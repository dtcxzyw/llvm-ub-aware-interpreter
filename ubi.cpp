// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include "ubi.h"
#include <llvm/Analysis/AssumeBundleQueries.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/InlineAsm.h>
#include <cassert>
#include <cstdlib>
#include <utility>

class ImmUBReporter final {
  raw_ostream &Out;
  UBAwareInterpreter &Interpreter;

public:
  ImmUBReporter(UBAwareInterpreter &Interpreter)
      : Out(errs()), Interpreter(Interpreter) {
    Out << "\nUB triggered: ";
  }
  [[noreturn]] ~ImmUBReporter() {
    Out << "\nExited with immediate UB.\n";
    Interpreter.dumpStackTrace();
    Out.flush();
    std::exit(EXIT_FAILURE);
  }
  template <typename Arg> ImmUBReporter &operator<<(Arg &&arg) {
    Out << std::forward<Arg>(arg);
    return *this;
  }
};

MemObject::~MemObject() { Manager.erase(Address.getZExtValue()); }
void MemObject::markPoison(size_t Offset, size_t Size, bool IsPoison) {
  for (size_t I = Offset; I != Offset + Size; ++I)
    Metadata[I].IsPoison = IsPoison;
}
void MemObject::verifyMemAccess(const APInt &Offset, const size_t AccessSize,
                                size_t Alignment) {
  if (!IsAlive)
    ImmUBReporter(Manager.Interpreter) << "Accessing dead object " << *this;
  auto NewAddr = Address + Offset;
  if (NewAddr.countr_zero() < Log2_64(Alignment))
    ImmUBReporter(Manager.Interpreter) << "Unaligned mem op";
  if ((Offset + AccessSize).ugt(Data.size()))
    ImmUBReporter(Manager.Interpreter)
        << "Out of bound mem op, bound = " << Data.size()
        << ", access range = [" << Offset << ", " << Offset + AccessSize << ')';
}
void MemObject::store(size_t Offset, const APInt &C) {
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = alignTo(C.getBitWidth(), 8) / 8;
  uint32_t WriteCnt = 0;
  std::byte *WritePos = Data.data() + Offset;
  for (uint32_t I = 0; I != C.getNumWords(); ++I) {
    auto Word = C.getRawData()[I];
    if (WriteCnt + Scale <= Size) {
      memcpy(&WritePos[WriteCnt], &Word, sizeof(Word));
      WriteCnt += Scale;
      if (WriteCnt == Size)
        return;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        WritePos[WriteCnt] = static_cast<std::byte>(Word & 255);
        Word >>= 8;
        if (++WriteCnt == Size)
          return;
      }
    }
  }
}
std::optional<APInt> MemObject::load(size_t Offset, size_t Bits) const {
  APInt Res = APInt::getZero(alignTo(Bits, 8));
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = Res.getBitWidth() / 8;
  uint32_t ReadCnt = 0;
  const std::byte *ReadPos = Data.data() + Offset;
  for (uint32_t I = 0; I != Res.getNumWords(); ++I) {
    auto &Word = const_cast<APInt::WordType &>(Res.getRawData()[I]);
    if (ReadCnt + Scale <= Size) {
      for (uint32_t J = 0; J != Scale; ++J) {
        if (Metadata[ReadPos + J - Data.data()].IsPoison)
          return std::nullopt;
      }
      memcpy(&Word, &ReadPos[ReadCnt], sizeof(Word));
      ReadPos += Scale;
      if (ReadCnt == Size)
        break;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        if (Metadata[ReadPos - Data.data()].IsPoison)
          return std::nullopt;
        Word |= static_cast<APInt::WordType>(ReadPos[ReadCnt]) << (J * 8);
        if (++ReadCnt == Size)
          break;
      }
      if (ReadCnt == Size)
        break;
    }
  }
  return Res.trunc(Bits);
}
void MemObject::dumpName(raw_ostream &Out) const {
  Out << (IsLocal ? '%' : '@') << Name;
  if (!IsAlive)
    Out << " (dead)";
}
void MemObject::dump(raw_ostream &Out) const {
  Out << (IsLocal ? '%' : '@') << Name << " (Addr = " << Address << ", "
      << "Size = " << Data.size() << (IsAlive ? "" : ", dead") << ')';
}
void PendingInitializeTask::write(uint64_t Offset, uint64_t Size) {
  if (Ranges.empty())
    return;

  uint64_t WriteLo = Offset, WriteHi = Offset + Size;
  SmallVector<std::pair<uint64_t, uint64_t>, 1> NewRanges;
  for (auto &[Lo, Hi] : Ranges) {
    uint64_t IntersectLo = std::max(Lo, WriteLo),
             IntersectHi = std::min(Hi, WriteHi);
    if (IntersectHi >= IntersectLo)
      continue;
    if (IntersectLo != Lo)
      NewRanges.emplace_back(Lo, IntersectLo);
    if (IntersectHi != Hi)
      NewRanges.emplace_back(IntersectHi, Hi);
  }

  Ranges.swap(NewRanges);
}
void MemObject::markWrite(size_t Offset, size_t Size) {
  for (auto &Task : PendingInitializeTasks)
    Task.write(Offset, Size);
}
PendingInitializeTask &MemObject::pushPendingInitializeTask(Frame *Ctx) {
  PendingInitializeTasks.push_back(PendingInitializeTask{Ctx});
  return PendingInitializeTasks.back();
}
void MemObject::popPendingInitializeTask(Frame *Ctx) {
  erase_if(PendingInitializeTasks,
           [this, Ctx](const PendingInitializeTask &Task) {
             if (Task.Context == Ctx) {
               if (!Task.Ranges.empty())
                 ImmUBReporter(Manager.Interpreter)
                     << "Uninitialized memory region " << *this
                     << " after function return.";
               return true;
             }
             return false;
           });
}

ContextSensitivePointerInfo
ContextSensitivePointerInfo::getDefault(Frame *FrameCtx) {
  return ContextSensitivePointerInfo{
      nullptr,           FrameCtx, true, true, true, true, IRMemLocation::Other,
      CaptureInfo::all()};
}
void ContextSensitivePointerInfo::push(Frame *Ctx) {
  if (Ctx != FrameCtx) {
    Parent = std::make_shared<ContextSensitivePointerInfo>(*this);
    FrameCtx = Ctx;
  }
}
void ContextSensitivePointerInfo::pop(Frame *Ctx) {
  if (FrameCtx == Ctx) {
    if (Parent)
      *this = *Parent;
    else
      *this = getDefault(nullptr);
  }
}

MemoryManager::MemoryManager(UBAwareInterpreter &Interpreter,
                             const DataLayout &DL, PointerType *Ty)
    : Interpreter(Interpreter), PtrBitWidth(DL.getTypeSizeInBits(Ty)) {
  assert(DL.getTypeSizeInBits(Ty) ==
         DL.getIndexSizeInBits(Ty->getAddressSpace()));
}
std::shared_ptr<MemObject> MemoryManager::create(std::string Name, bool IsLocal,
                                                 size_t Size,
                                                 size_t Alignment) {
  AllocatedMem = alignTo(AllocatedMem, Alignment);
  auto Address = APInt(PtrBitWidth, AllocatedMem);
  AllocatedMem += Size + Padding;
  auto Obj = std::make_shared<MemObject>(*this, std::move(Name), IsLocal,
                                         std::move(Address), Size);
  AddressMap.emplace(Address.getZExtValue(), Obj.get());
  return Obj;
}
SingleValue MemoryManager::lookupPointer(const APInt &Addr) const {
  if (auto Iter = AddressMap.upper_bound(Addr.getZExtValue());
      Iter != AddressMap.begin()) {
    auto *MO = std::prev(Iter)->second;
    if (MO->address().ule(Addr) && Addr.ule(MO->address() + MO->size())) {
      return SingleValue{
          Pointer{MO->shared_from_this(), Addr - MO->address(),
                  ContextSensitivePointerInfo::getDefault(nullptr)}};
    }
  }

  return SingleValue{Pointer{std::weak_ptr<MemObject>{},
                             APInt::getZero(Addr.getBitWidth()), Addr, 0,
                             ContextSensitivePointerInfo::getDefault(nullptr)}};
}

std::optional<APInt> addNoWrap(const APInt &LHS, const APInt &RHS, bool HasNSW,
                               bool HasNUW) {
  bool Overflow = false;
  auto Ret = LHS.sadd_ov(RHS, Overflow);
  if (HasNSW && Overflow)
    return std::nullopt;
  if (HasNUW) {
    (void)LHS.uadd_ov(RHS, Overflow);
    if (Overflow)
      return std::nullopt;
  }
  return Ret;
}
std::optional<APInt> subNoWrap(const APInt &LHS, const APInt &RHS, bool HasNSW,
                               bool HasNUW) {
  bool Overflow = false;
  auto Ret = LHS.ssub_ov(RHS, Overflow);
  if (HasNSW && Overflow)
    return std::nullopt;
  if (HasNUW) {
    (void)LHS.usub_ov(RHS, Overflow);
    if (Overflow)
      return std::nullopt;
  }
  return Ret;
}
std::optional<APInt> mulNoWrap(const APInt &LHS, const APInt &RHS, bool HasNSW,
                               bool HasNUW) {
  bool Overflow = false;
  auto Ret = LHS.smul_ov(RHS, Overflow);
  if (HasNSW && Overflow)
    return std::nullopt;
  if (HasNUW) {
    (void)LHS.umul_ov(RHS, Overflow);
    if (Overflow)
      return std::nullopt;
  }
  return Ret;
}
raw_ostream &operator<<(raw_ostream &Out, const SingleValue &Val) {
  if (auto *CI = std::get_if<APInt>(&Val)) {
    if (CI->getBitWidth() == 1)
      return Out << (CI->getBoolValue() ? "T" : "F");
    return Out << "i" << CI->getBitWidth() << ' ' << *CI;
  }
  if (auto *CFP = std::get_if<APFloat>(&Val))
    return Out << *CFP;
  if (auto *Ptr = std::get_if<Pointer>(&Val)) {
    Out << "Ptr " << Ptr->Address << '[';
    if (auto P = Ptr->Obj.lock())
      P->dumpName(Out);
    else
      Out << "dangling";
    if (!Ptr->Offset.isZero())
      Out << " + " << Ptr->Offset;
    Out << "] " << Ptr->Info.CI;
    if (Ptr->Info.Readable || Ptr->Info.Writable)
      Out << ' ' << (Ptr->Info.Readable ? "R" : "")
          << (Ptr->Info.Writable ? "W" : "");
    switch (Ptr->Info.Loc) {
    case IRMemLocation::ArgMem:
      Out << " ArgMem";
      break;
    default:
      break;
    }
    return Out;
  }
  return Out << "poison";
}

raw_ostream &operator<<(raw_ostream &Out, const AnyValue &Val) {
  if (const auto *SV = std::get_if<SingleValue>(&Val.Val))
    return Out << *SV;
  if (const auto *MV = std::get_if<std::vector<AnyValue>>(&Val.Val)) {
    Out << "{ ";
    bool First = true;
    for (auto &Sub : *MV) {
      if (First)
        First = false;
      else
        Out << ", ";
      Out << Sub;
    }
    return Out << " }";
  }
  return Out << "None";
}
bool refines(const SingleValue &LHS, const SingleValue &RHS) {
  if (isPoison(RHS))
    return true;
  if (isPoison(LHS))
    return false;
  if (auto *LCI = std::get_if<APInt>(&LHS))
    return *LCI == std::get<APInt>(RHS);
  if (auto *LFP = std::get_if<APFloat>(&LHS))
    return LFP->bitwiseIsEqual(std::get<APFloat>(RHS));
  if (auto *LPtr = std::get_if<Pointer>(&LHS))
    return LPtr->Address == std::get<Pointer>(RHS).Address;
  llvm_unreachable("Unknown SingleValue type");
}
bool AnyValue::refines(const AnyValue &RHS) const {
  if (isSingleValue())
    return ::refines(getSingleValue(), RHS.getSingleValue());
  auto &LHSArr = getValueArray();
  auto &RHSArr = RHS.getValueArray();
  assert(LHSArr.size() == RHSArr.size());
  for (uint32_t I = 0, E = LHSArr.size(); I != E; ++I) {
    if (!LHSArr[I].refines(RHSArr[I]))
      return false;
  }
  return true;
}

static void handleNoUndef(UBAwareInterpreter &Interpreter,
                          const SingleValue &V) {
  if (isPoison(V))
    ImmUBReporter(Interpreter) << "noundef on a poison value";
}
static APFloat handleDenormal(APFloat V,
                              DenormalMode::DenormalModeKind Denormal) {
  if (V.isDenormal()) {
    switch (Denormal) {
    case DenormalMode::PreserveSign:
      return APFloat::getZero(V.getSemantics(), V.isNegative());
    case DenormalMode::PositiveZero:
      return APFloat::getZero(V.getSemantics());
    case DenormalMode::Invalid:
    case DenormalMode::IEEE:
    case DenormalMode::Dynamic:
    default:
      break;
    }
  }
  return std::move(V);
}
static void handleFPVal(SingleValue &V, FastMathFlags FMF,
                        DenormalMode::DenormalModeKind Denormal) {
  if (isPoison(V))
    return;
  auto &AFP = std::get<APFloat>(V);
  if (isPoison(AFP, FMF)) {
    V = poison();
    return;
  }
  AFP = handleDenormal(AFP, Denormal);
}
static SingleValue handleFPVal(APFloat V, FastMathFlags FMF,
                               DenormalMode::DenormalModeKind Denormal) {
  if (isPoison(V, FMF))
    return poison();
  return handleDenormal(std::move(V), Denormal);
}
static void handleRange(SingleValue &V, const ConstantRange &CR) {
  if (auto *CI = std::get_if<APInt>(&V)) {
    if (!CR.contains(*CI))
      V = poison();
  }
}
static void handleAlign(SingleValue &V, size_t Align) {
  if (isPoison(V))
    return;
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address.countr_zero() < Log2_64(Align))
    V = poison();
}
static void handleNonNull(SingleValue &V) {
  if (isPoison(V))
    return;
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address == 0)
    V = poison();
}
static void handleNoFPClass(SingleValue &V, FPClassTest Mask) {
  if (isPoison(V))
    return;
  auto &AFP = std::get<APFloat>(V);
  if (AFP.classify() & Mask)
    V = poison();
}
static void handleDereferenceable(UBAwareInterpreter &Interpreter,
                                  SingleValue &V, uint64_t Size, bool OrNull) {
  if (isPoison(V))
    ImmUBReporter(Interpreter) << "dereferenceable on a poison value";
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address == 0) {
    if (OrNull)
      return;
    ImmUBReporter(Interpreter) << "dereferenceable on a null pointer";
  }
  if (Ptr.Offset.getSExtValue() + Size > Ptr.Bound) {
    ImmUBReporter(Interpreter)
        << "dereferenceable" << (OrNull ? "_or_null" : "") << "(" << Size
        << ") out of bound :" << V;
  }
  if (Ptr.Obj.expired())
    ImmUBReporter(Interpreter)
        << "dereferenceable" << (OrNull ? "_or_null" : "")
        << " on a dangling pointer";
}
static void postProcess(AnyValue &V,
                        const function_ref<void(SingleValue &)> &Fn) {
  if (V.isSingleValue()) {
    Fn(V.getSingleValue());
  } else {
    for (auto &Sub : V.getValueArray())
      postProcess(Sub, Fn);
  }
}
static AnyValue postProcessFPVal(AnyValue V, Instruction &FMFSource) {
  if (FMFSource.getType()->isFPOrFPVectorTy()) {
    FastMathFlags FMF = FMFSource.getFastMathFlags();
    postProcess(V, [FMF](SingleValue &SV) {
      handleFPVal(SV, FMF, DenormalMode::IEEE);
    });
  }
  return std::move(V);
}
static void postProcessAttr(UBAwareInterpreter &Interpreter, AnyValue &V,
                            const AttributeSet &AS) {
  if (AS.hasAttribute(Attribute::Range)) {
    auto CR = AS.getAttribute(Attribute::Range).getRange();
    postProcess(V, [CR](SingleValue &SV) { handleRange(SV, CR); });
  }
  if (AS.hasAttribute(Attribute::NoFPClass)) {
    auto Mask = AS.getAttribute(Attribute::NoFPClass).getNoFPClass();
    postProcess(V, [Mask](SingleValue &SV) { handleNoFPClass(SV, Mask); });
  }
  if (AS.hasAttribute(Attribute::Dereferenceable)) {
    auto Size = AS.getDereferenceableBytes();
    postProcess(V, [&](SingleValue &SV) {
      handleDereferenceable(Interpreter, SV, Size, false);
    });
  }
  if (AS.hasAttribute(Attribute::DereferenceableOrNull)) {
    auto Size = AS.getDereferenceableOrNullBytes();
    postProcess(V, [&](SingleValue &SV) {
      handleDereferenceable(Interpreter, SV, Size, true);
    });
  }
  if (AS.hasAttribute(Attribute::Alignment)) {
    auto Align = AS.getAlignment().valueOrOne().value();
    postProcess(V, [Align](SingleValue &SV) { handleAlign(SV, Align); });
  }
  if (AS.hasAttribute(Attribute::NonNull))
    postProcess(V, handleNonNull);
  if (AS.hasAttribute(Attribute::NoUndef))
    postProcess(V, [&](SingleValue &SV) { handleNoUndef(Interpreter, SV); });
  auto FrameCtx = Interpreter.getCurrentFrame();
  if (AS.hasAttribute(Attribute::Captures)) {
    auto CI = AS.getCaptureInfo();
    postProcess(V, [CI, FrameCtx](SingleValue &SV) {
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      Ptr.Info.pushCaptureInfo(FrameCtx, CI);
    });
  }
  if (AS.hasAttribute(Attribute::ReadNone)) {
    postProcess(V, [FrameCtx](SingleValue &SV) {
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      Ptr.Info.pushReadWrite(FrameCtx, false, false);
    });
  }
  if (AS.hasAttribute(Attribute::ReadOnly)) {
    postProcess(V, [FrameCtx](SingleValue &SV) {
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      if (!Ptr.Info.Readable) {
        SV = poison();
        return;
      }
      Ptr.Info.pushReadWrite(FrameCtx, true, false);
    });
  }
  if (AS.hasAttribute(Attribute::WriteOnly)) {
    postProcess(V, [FrameCtx](SingleValue &SV) {
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      if (!Ptr.Info.Writable) {
        SV = poison();
        return;
      }
      Ptr.Info.pushReadWrite(FrameCtx, false, true);
    });
  }
}
static bool anyOfScalar(const AnyValue &V,
                        function_ref<bool(const SingleValue &)> F) {
  if (V.isSingleValue()) {
    auto &SV = V.getSingleValue();
    return !isPoison(SV) && F(SV);
  }
  uint32_t E = V.getValueArray().size();
  for (uint32_t I = 0; I != E; ++I) {
    auto &SV = V.getSingleValueAt(I);
    if (isPoison(SV))
      continue;
    if (F(SV))
      return true;
  }
  return false;
}
static void foreachScalar(const AnyValue &V,
                          function_ref<void(const SingleValue &)> F) {
  if (V.isSingleValue()) {
    auto &SV = V.getSingleValue();
    if (!isPoison(SV))
      F(SV);
    return;
  }

  uint32_t E = V.getValueArray().size();
  for (uint32_t I = 0; I != E; ++I) {
    auto &SV = V.getSingleValueAt(I);
    if (isPoison(SV))
      continue;
    F(SV);
  }
}

uint32_t UBAwareInterpreter::getVectorLength(VectorType *Ty) const {
  auto EC = Ty->getElementCount();
  if (EC.isFixed())
    return EC.getFixedValue();
  return EC.getKnownMinValue() * Option.VScale;
}
AnyValue UBAwareInterpreter::getPoison(Type *Ty) const {
  if (Ty->isIntegerTy() || Ty->isFloatingPointTy() || Ty->isPointerTy())
    return poison();
  if (auto *VTy = dyn_cast<VectorType>(Ty))
    return std::vector<AnyValue>(getVectorLength(VTy), poison());
  if (auto *ATy = dyn_cast<ArrayType>(Ty))
    return std::vector<AnyValue>(ATy->getArrayNumElements(),
                                 getPoison(ATy->getArrayElementType()));
  if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    std::vector<AnyValue> Elts;
    Elts.reserve(StructTy->getStructNumElements());
    for (uint32_t I = 0, E = StructTy->getStructNumElements(); I != E; ++I)
      Elts.push_back(getPoison(StructTy->getStructElementType(I)));
    return std::move(Elts);
  }
  errs() << "Unsupported type " << *Ty << '\n';
  std::abort();
}
AnyValue UBAwareInterpreter::getZero(Type *Ty) const {
  if (Ty->isIntegerTy())
    return SingleValue{APInt::getZero(Ty->getIntegerBitWidth())};
  if (Ty->isFloatingPointTy())
    return SingleValue{APFloat::getZero(Ty->getFltSemantics())};
  if (Ty->isPointerTy())
    return SingleValue{*NullPtr};
  if (auto *VTy = dyn_cast<VectorType>(Ty))
    return std::vector<AnyValue>(getVectorLength(VTy),
                                 getZero(Ty->getScalarType()));
  if (auto *ATy = dyn_cast<ArrayType>(Ty))
    return std::vector<AnyValue>(ATy->getArrayNumElements(),
                                 getZero(ATy->getArrayElementType()));
  if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    std::vector<AnyValue> Elts;
    Elts.reserve(StructTy->getStructNumElements());
    for (uint32_t I = 0, E = StructTy->getStructNumElements(); I != E; ++I)
      Elts.push_back(getZero(StructTy->getStructElementType(I)));
    return std::move(Elts);
  }
  errs() << "Unsupported type " << *Ty << '\n';
  std::abort();
}
AnyValue UBAwareInterpreter::convertFromConstant(Constant *V) const {
  if (isa<PoisonValue>(V))
    return getPoison(V->getType());
  if (isa<UndefValue, ConstantAggregateZero>(V))
    return getZero(V->getType());
  if (auto *CI = dyn_cast<ConstantInt>(V))
    return SingleValue{CI->getValue()};
  if (auto *CFP = dyn_cast<ConstantFP>(V))
    return SingleValue{CFP->getValue()};
  if (isa<ConstantPointerNull>(V))
    return SingleValue{*NullPtr};
  if (auto *CDS = dyn_cast<ConstantDataSequential>(V)) {
    std::vector<AnyValue> Elts;
    Elts.reserve(CDS->getNumElements());
    for (uint32_t I = 0, E = CDS->getNumElements(); I != E; ++I)
      Elts.push_back(convertFromConstant(CDS->getElementAsConstant(I)));
    return std::move(Elts);
  }
  if (auto *CA = dyn_cast<ConstantAggregate>(V)) {
    std::vector<AnyValue> Elts;
    Elts.reserve(CA->getNumOperands());
    for (uint32_t I = 0, E = CA->getNumOperands(); I != E; ++I)
      Elts.push_back(convertFromConstant(CA->getOperand(I)));
    return std::move(Elts);
  }
  if (auto *GV = dyn_cast<GlobalValue>(V)) {
    auto Iter = GlobalValues.find(GV);
    if (Iter == GlobalValues.end())
      return AnyValue{*NullPtr};
    auto PointerInfo = ContextSensitivePointerInfo::getDefault(nullptr);
    PointerInfo.pushReadWrite(nullptr, true,
                              isa<GlobalVariable>(GV) &&
                                  !cast<GlobalVariable>(GV)->isConstant());
    return AnyValue{Pointer{Iter->second,
                            APInt::getZero(DL.getTypeSizeInBits(GV->getType())),
                            std::move(PointerInfo)}};
  }
  if (auto *CE = dyn_cast<ConstantExpr>(V)) {
    switch (CE->getOpcode()) {
    case Instruction::GetElementPtr: {
      auto *Inst = cast<GetElementPtrInst>(CE->getAsInstruction());
      auto Guard = make_scope_exit([Inst] { Inst->deleteValue(); });
      APInt Offset = APInt::getZero(DL.getIndexSizeInBits(0));
      SmallMapVector<Value *, APInt, 4> VarOffset;
      if (Inst->collectOffset(DL, Offset.getBitWidth(), VarOffset, Offset)) {
        assert(VarOffset.empty());
        return offsetPointer(
            std::get<Pointer>(
                convertFromConstant(cast<Constant>(Inst->getPointerOperand()))
                    .getSingleValue()),
            Offset, Inst->isInBounds());
      }
      break;
    }
    case Instruction::PtrToInt: {
      auto Ptr = std::get<Pointer>(
          convertFromConstant(cast<Constant>(CE->getOperand(0)))
              .getSingleValue());
      return SingleValue{
          Ptr.Address.zextOrTrunc(CE->getType()->getScalarSizeInBits())};
    }
    case Instruction::Sub: {
      auto LHS = convertFromConstant(cast<Constant>(CE->getOperand(0)));
      auto RHS = convertFromConstant(cast<Constant>(CE->getOperand(1)));
      return SingleValue{std::get<APInt>(LHS.getSingleValue()) -
                         std::get<APInt>(RHS.getSingleValue())};
    }
    case Instruction::Trunc: {
      auto V = convertFromConstant(cast<Constant>(CE->getOperand(0)));
      return SingleValue{std::get<APInt>(V.getSingleValue())
                             .trunc(CE->getType()->getScalarSizeInBits())};
    }
    default:
      break;
    }
  }
  if (auto *BA = dyn_cast<BlockAddress>(V))
    return SingleValue{
        Pointer{BlockTargets.at(BA->getBasicBlock()),
                APInt::getZero(DL.getTypeSizeInBits(V->getType())),
                ContextSensitivePointerInfo::getDefault(nullptr)}};
  errs() << "Unexpected constant " << *V << '\n';
  std::abort();
}
void UBAwareInterpreter::store(MemObject &MO, uint32_t Offset,
                               const AnyValue &V, Type *Ty) {
  if (Ty->isIntegerTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    MO.store(Offset, std::get<APInt>(SV));
  } else if (Ty->isFloatingPointTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    auto &C = std::get<APFloat>(SV);
    MO.store(Offset, C.bitcastToAPInt());
  } else if (Ty->isPointerTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    auto &Ptr = std::get<Pointer>(SV);
    MO.store(Offset, Ptr.Address);
  } else if (Ty->isVectorTy()) {
    Type *EltTy = Ty->getScalarType();
    auto Step = DL.getTypeStoreSize(EltTy);
    auto &MV = V.getValueArray();
    for (auto &Val : MV) {
      store(MO, Offset, Val, EltTy);
      Offset += Step;
    }
  } else if (auto *ArrTy = dyn_cast<ArrayType>(Ty)) {
    Type *EltTy = ArrTy->getElementType();
    auto Step = DL.getTypeStoreSize(EltTy);
    auto &MV = V.getValueArray();
    for (auto &Val : MV) {
      store(MO, Offset, Val, EltTy);
      Offset += Step;
    }
  } else if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    auto *Layout = DL.getStructLayout(StructTy);
    auto &MV = V.getValueArray();
    for (uint32_t I = 0, E = StructTy->getStructNumElements(); I != E; ++I) {
      auto NewOffset = Offset + Layout->getElementOffset(I).getFixedValue();
      store(MO, NewOffset, MV.at(I), StructTy->getStructElementType(I));
    }
  } else {
    errs() << "Unsupproted type: " << *Ty << '\n';
    std::abort();
  }
}
AnyValue UBAwareInterpreter::load(const MemObject &MO, uint32_t Offset,
                                  Type *Ty) {
  if (Ty->isIntegerTy()) {
    auto Val = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue());
    if (!Val.has_value())
      return poison();
    return SingleValue{Val->trunc(Ty->getScalarSizeInBits())};
  } else if (Ty->isFloatingPointTy()) {
    auto Val = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue());
    if (!Val.has_value())
      return poison();
    return SingleValue{APFloat(Ty->getFltSemantics(), *Val)};
  } else if (Ty->isPointerTy()) {
    auto Addr = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue());
    if (!Addr.has_value())
      return poison();
    return SingleValue{MemMgr.lookupPointer(*Addr)};
  } else if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    auto *Layout = DL.getStructLayout(StructTy);
    std::vector<AnyValue> Res;
    Res.reserve(StructTy->getNumElements());
    for (uint32_t I = 0, E = StructTy->getStructNumElements(); I != E; ++I) {
      auto NewOffset = Offset + Layout->getElementOffset(I).getFixedValue();
      Res.push_back(load(MO, NewOffset, StructTy->getStructElementType(I)));
    }
    return std::move(Res);
  } else if (auto *VTy = dyn_cast<VectorType>(Ty)) {
    uint32_t Len = getVectorLength(VTy);
    Type *EltTy = VTy->getElementType();
    size_t Step = DL.getTypeStoreSize(EltTy);
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      Res.push_back(load(MO, Offset, EltTy));
      Offset += Step;
    }
    return std::move(Res);
  } else {
    errs() << "Unsupproted type: " << *Ty << '\n';
    std::abort();
  }
}
void UBAwareInterpreter::store(const AnyValue &P, uint32_t Alignment,
                               const AnyValue &V, Type *Ty, bool IsVolatile) {
  // errs() << "Store " << P << ' ' << V << '\n';
  if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
    if (!PV->Info.Writable)
      ImmUBReporter(*this) << "store to a non-writable pointer " << *PV;
    if (auto MO = PV->Obj.lock()) {
      if (!MO->isStackObject(CurrentFrame) &&
          (CurrentFrame->MemEffects.getModRef(PV->Info.Loc) &
           ModRefInfo::Mod) != ModRefInfo::Mod)
        ImmUBReporter(*this) << "store in a writenone context";
      auto Size = DL.getTypeStoreSize(Ty).getFixedValue();
      if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
        volatileMemOpTy(Ty, /*IsStore=*/true);
      MO->verifyMemAccess(PV->Offset, Size, Alignment);
      if (!IsVolatile)
        MO->markWrite(PV->Offset.getZExtValue(), Size);
      return store(*MO, PV->Offset.getZExtValue(), V, Ty);
    }
    ImmUBReporter(*this) << "store to invalid pointer";
  }
  ImmUBReporter(*this) << "store to poison pointer";
}
AnyValue UBAwareInterpreter::load(const AnyValue &P, uint32_t Alignment,
                                  Type *Ty, bool IsVolatile) {
  if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
    if (!PV->Info.Readable)
      ImmUBReporter(*this) << "load from a non-readable pointer " << *PV;
    if (auto MO = PV->Obj.lock()) {
      if ((!MO->isConstant() && !MO->isStackObject(CurrentFrame)) &&
          (CurrentFrame->MemEffects.getModRef(PV->Info.Loc) &
           ModRefInfo::Ref) != ModRefInfo::Ref)
        ImmUBReporter(*this) << "load in a readnone context";
      auto Size = DL.getTypeStoreSize(Ty).getFixedValue();
      if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
        volatileMemOpTy(Ty, /*IsStore=*/false);
      MO->verifyMemAccess(PV->Offset, Size, Alignment);
      return load(*MO, PV->Offset.getZExtValue(), Ty);
    }
    ImmUBReporter(*this) << "load from invalid pointer";
  }
  ImmUBReporter(*this) << "load from poison pointer";
  llvm_unreachable("Unreachable code");
}
SingleValue UBAwareInterpreter::offsetPointer(const Pointer &Ptr,
                                              const APInt &Offset,
                                              GEPNoWrapFlags Flags) const {
  if (Offset.isZero())
    return Ptr;
  bool HasNSW = Flags.hasNoUnsignedSignedWrap();
  bool HasNUW = Flags.hasNoUnsignedWrap();
  auto NewOffset = addNoWrap(Ptr.Offset, Offset, HasNSW, HasNUW);
  if (!NewOffset)
    return poison();
  auto NewAddr = addNoWrap(Ptr.Address, Offset, HasNSW, HasNUW);
  if (!NewAddr)
    return poison();
  if (NewOffset->isNegative() || NewOffset->sgt(Ptr.Bound)) {
    if (Flags.isInBounds())
      return poison();
    return MemMgr.lookupPointer(*NewAddr);
  }

  return Pointer{Ptr.Obj, *NewOffset, *NewAddr, Ptr.Bound, Ptr.Info};
}

UBAwareInterpreter::UBAwareInterpreter(Module &M, InterpreterOption Option)
    : Ctx(M.getContext()), M(M), DL(M.getDataLayout()), Option(Option),
      TLI(Triple{M.getTargetTriple()}),
      MemMgr(*this, DL, PointerType::getUnqual(Ctx)) {
  assert(DL.isLittleEndian());
  static_assert(sys::IsLittleEndianHost);

  EMIInfo.Enabled = Option.EnableEMITracking;
  EMIInfo.EnablePGFTracking = EMIInfo.Enabled && Option.EnablePGFTracking;
  NullPtrStorage = MemMgr.create("null", false, 0U, 1U);
  NullPtr = Pointer{NullPtrStorage, APInt::getZero(DL.getPointerSizeInBits()),
                    ContextSensitivePointerInfo::getDefault(nullptr)};
  assert(NullPtr->Address.isZero());
  for (auto &GV : M.globals()) {
    if (!GV.hasExactDefinition())
      continue;
    GlobalValues.insert(
        {&GV, std::move(MemMgr.create(GV.getName().str(), false,
                                      DL.getTypeAllocSize(GV.getValueType()),
                                      DL.getPreferredAlign(&GV).value()))});
  }
  for (auto &GV : M.globals()) {
    if (!GV.hasExactDefinition())
      continue;
    if (GV.hasInitializer()) {
      auto &MO = GlobalValues.at(&GV);
      store(*MO, 0U, convertFromConstant(GV.getInitializer()),
            GV.getValueType());
      if (GV.isConstant())
        MO->markConstant();
    }
  }
  for (auto &F : M) {
    GlobalValues.insert(
        {&F, std::move(MemMgr.create(F.getName().str(), false, 0, 16))});
    ValidCallees.insert({GlobalValues.at(&F)->address().getZExtValue(), &F});
    for (auto &BB : F) {
      if (BB.isEntryBlock())
        continue;
      BlockTargets.insert({&BB, std::move(MemMgr.create(
                                    F.getName().str() + ":" + getValueName(&BB),
                                    true, 0, 16))});
      ValidBlockTargets.insert(
          {GlobalValues.at(&F)->address().getZExtValue(), &BB});
    }
  }
  // Expand constexprs
  while (true) {
    bool Changed = false;
    for (auto &F : M) {
      for (auto &BB : F) {
        for (auto &I : BB) {
          DenseMap<ConstantExpr *, DenseMap<BasicBlock *, Instruction *>> Cache;
          for (auto &U : I.operands()) {
            if (auto *CE = dyn_cast<ConstantExpr>(U.get())) {
              auto *Inst = CE->getAsInstruction();
              if (auto *PHI = dyn_cast<PHINode>(&I)) {
                auto &Table = Cache[CE];
                auto *PredBB = PHI->getIncomingBlock(U);
                if (auto It = Table.find(PredBB); It != Table.end()) {
                  Inst->deleteValue();
                  Inst = It->second;
                } else {
                  Inst->insertBefore(
                      PHI->getIncomingBlock(U)->getTerminator()->getIterator());
                  Table.insert({PredBB, Inst});
                }
              } else
                Inst->insertBefore(I.getIterator());
              U.set(Inst);
              Changed = true;
            }
          }
        }
      }
    }
    if (!Changed)
      break;
  }

  if (EMIInfo.Enabled && Option.EMIUseProb > 0.0) {
    Gen.seed(std::random_device{}());
    auto Sample = [&] {
      return std::generate_canonical<double,
                                     std::numeric_limits<size_t>::max()>(Gen) <
             Option.EMIUseProb;
    };
    for (auto &F : M) {
      for (auto &BB : F) {
        for (auto &I : BB) {
          if (isa<PHINode>(&I))
            continue;
          for (auto &Op : I.operands()) {
            if (!Op->getType()->isIntegerTy())
              continue;
            if (isa<Constant>(Op))
              continue;
            if (Sample())
              EMIInfo.InterestingUses[&I].push_back(&Op);
          }
        }
      }
    }
  }
  // if (verifyModule(M, &errs()))
  //   std::exit(EXIT_FAILURE);
}

bool UBAwareInterpreter::addValue(Instruction &I, AnyValue Val) {
  if (I.getType()->isVoidTy())
    return true;
  if (Option.Verbose)
    errs() << " -> " << Val;
  CurrentFrame->ValueMap[&I] = std::move(Val);
  return true;
}
bool UBAwareInterpreter::jumpTo(BasicBlock *To) {
  if (Option.Verbose) {
    errs() << " jump to ";
    To->printAsOperand(errs(), false);
  }
  BasicBlock *From = CurrentFrame->BB;
  CurrentFrame->BB = To;
  CurrentFrame->PC = To->begin();
  SmallVector<std::pair<PHINode *, AnyValue>> IncomingValues;
  while (true) {
    if (auto *PHI = dyn_cast<PHINode>(CurrentFrame->PC)) {
      IncomingValues.emplace_back(
          PHI, postProcessFPVal(getValue(PHI->getIncomingValueForBlock(From)),
                                *PHI));
      ++CurrentFrame->PC;
    } else
      break;
  }
  for (auto &[K, V] : IncomingValues) {
    if (Option.Verbose)
      K->printAsOperand(errs() << "\n    phi ");
    addValue(*K, std::move(V));
  }
  return false;
}
AnyValue UBAwareInterpreter::getValue(Value *V) {
  if (auto *C = dyn_cast<Constant>(V))
    return convertFromConstant(C);
  if (isa<MetadataAsValue>(V))
    return none();
  return CurrentFrame->ValueMap.at(V);
}
std::optional<APInt> UBAwareInterpreter::getInt(const SingleValue &SV) {
  if (auto *C = std::get_if<APInt>(&SV))
    return *C;
  return std::nullopt;
}
std::optional<APInt> UBAwareInterpreter::getInt(Value *V) {
  return getInt(getValue(V).getSingleValue());
}
APInt UBAwareInterpreter::getIntNonPoison(Value *V) {
  if (auto Res = getInt(getValue(V).getSingleValue()))
    return *Res;
  ImmUBReporter(*this) << "Expect a non-poison integer";
  llvm_unreachable("Unreachable code");
}
UBAwareInterpreter::BooleanVal
UBAwareInterpreter::getBoolean(const SingleValue &SV) {
  if (isPoison(SV))
    return BooleanVal::Poison;
  return std::get<APInt>(SV).getBoolValue() ? BooleanVal::True
                                            : BooleanVal::False;
}
bool UBAwareInterpreter::getBooleanNonPoison(const SingleValue &SV) {
  auto BV = getBoolean(SV);
  if (BV == BooleanVal::Poison)
    ImmUBReporter(*this) << "expect a poison value";
  return BV == BooleanVal::True;
}
UBAwareInterpreter::BooleanVal UBAwareInterpreter::getBoolean(Value *V) {
  return getBoolean(getValue(V).getSingleValue());
}
char *UBAwareInterpreter::getRawPtr(const SingleValue &SV) {
  auto Ptr = std::get<Pointer>(SV);
  if (auto MO = Ptr.Obj.lock()) {
    if (MO == NullPtrStorage)
      return nullptr;
    return MO->rawPointer() + Ptr.Offset.getSExtValue();
  }
  ImmUBReporter(*this) << "dangling pointer";
  llvm_unreachable("Unreachable code");
}
char *UBAwareInterpreter::getRawPtr(SingleValue SV, size_t Size,
                                    size_t Alignment, bool IsStore,
                                    bool IsVolatile) {
  auto &Ptr = std::get<Pointer>(SV);
  if (IsStore && !Ptr.Info.Writable)
    ImmUBReporter(*this) << "store to a non-writable pointer " << Ptr;
  if (!IsStore && !Ptr.Info.Readable)
    ImmUBReporter(*this) << "load from a non-readable pointer " << Ptr;
  if (auto MO = Ptr.Obj.lock()) {
    if (IsStore && !MO->isStackObject(CurrentFrame) &&
        (CurrentFrame->MemEffects.getModRef(Ptr.Info.Loc) & ModRefInfo::Mod) !=
            ModRefInfo::Mod)
      ImmUBReporter(*this) << "store in a writenone context";
    if (!IsStore && (!MO->isConstant() && !MO->isStackObject(CurrentFrame)) &&
        (CurrentFrame->MemEffects.getModRef(Ptr.Info.Loc) & ModRefInfo::Ref) !=
            ModRefInfo::Ref)
      ImmUBReporter(*this) << "load in a readnone context";
    if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
      volatileMemOp(Size, IsStore);
    MO->verifyMemAccess(Ptr.Offset, Size, Alignment);
    if (IsStore) {
      // FIXME: Approximation: assume all bytes to write are non-poison.
      MO->markPoison(Ptr.Offset.getSExtValue(), Size, false);
      if (!IsVolatile)
        MO->markWrite(Ptr.Offset.getSExtValue(), Size);
    }
    return MO->rawPointer() + Ptr.Offset.getSExtValue();
  }
  ImmUBReporter(*this) << "dangling pointer";
  llvm_unreachable("Unreachable code");
}
DenormalMode UBAwareInterpreter::getCurrentDenormalMode(Type *Ty) {
  if (Ty->isFPOrFPVectorTy() && CurrentFrame) {
    return CurrentFrame->BB->getParent()->getDenormalMode(
        Ty->getScalarType()->getFltSemantics());
  }
  return DenormalMode::getDefault();
}

void UBAwareInterpreter::volatileMemOp(size_t Size, bool IsStore) {
  // std::array<uint64_t, 3> Arr{VolatileMemHash, IsStore, Size};
  // VolatileMemHash = std::hash<std::string_view>{}(
  //     std::string_view{reinterpret_cast<const char *>(Arr.data()),
  //                      Arr.size() * sizeof(uint64_t)});
  // FIXME: Handle memcpy -> struct load/store
  if (IsStore)
    VolatileMemHash += Size;
  else
    VolatileMemHash += Size << 32;
}
void UBAwareInterpreter::volatileMemOpTy(Type *Ty, bool IsStore) {
  if (auto *ArrTy = dyn_cast<ArrayType>(Ty)) {
    size_t Size =
        DL.getTypeStoreSize(ArrTy->getArrayElementType()).getFixedValue();
    for (uint32_t I = 0, E = ArrTy->getArrayNumElements(); I != E; ++I)
      volatileMemOp(Size, IsStore);
  } else if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    for (uint32_t I = 0, E = StructTy->getNumElements(); I != E; ++I)
      volatileMemOpTy(StructTy->getElementType(I), IsStore);
  } else {
    size_t Size = DL.getTypeStoreSize(Ty).getFixedValue();
    volatileMemOp(Size, IsStore);
  }
}

bool UBAwareInterpreter::visitAllocaInst(AllocaInst &AI) {
  size_t AllocSize = DL.getTypeAllocSize(AI.getAllocatedType()).getFixedValue();
  if (AI.isArrayAllocation())
    AllocSize *= getIntNonPoison(AI.getArraySize()).getZExtValue();
  auto Obj = MemMgr.create(getValueName(&AI), true, AllocSize,
                           AI.getPointerAlignment(DL).value());
  Pointer Ptr{Obj, APInt::getZero(DL.getPointerSizeInBits()),
              ContextSensitivePointerInfo::getDefault(CurrentFrame)};
  Obj->setLiveness(true);
  Obj->setStackObjectInfo(CurrentFrame);
  for (auto *U : AI.users()) {
    if (isa<LifetimeIntrinsic>(U)) {
      // The returned object is initially dead if it is explicitly used by
      // lifetime intrinsics.
      Obj->setLiveness(false);
      break;
    }
  }
  CurrentFrame->Allocas.push_back(std::move(Obj));
  return addValue(AI, SingleValue{std::move(Ptr)});
}
AnyValue UBAwareInterpreter::visitBinOp(
    Type *RetTy, const AnyValue &LHS, const AnyValue &RHS,
    const function_ref<SingleValue(const SingleValue &, const SingleValue &)>
        &Fn) {
  auto FnPoison = [&Fn](const SingleValue &LHS,
                        const SingleValue &RHS) -> SingleValue {
    if (isPoison(LHS) || isPoison(RHS))
      return poison();
    return Fn(LHS, RHS);
  };
  if (auto *VTy = dyn_cast<VectorType>(RetTy)) {
    uint32_t Len = getVectorLength(VTy);
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I)
      Res.push_back(
          AnyValue{FnPoison(LHS.getSingleValueAt(I), RHS.getSingleValueAt(I))});
    return std::move(Res);
  }
  return AnyValue{FnPoison(LHS.getSingleValue(), RHS.getSingleValue())};
}
bool UBAwareInterpreter::visitBinOp(
    Instruction &I,
    const function_ref<SingleValue(const SingleValue &, const SingleValue &)>
        &Fn) {
  return addValue(I, visitBinOp(I.getType(), getValue(I.getOperand(0)),
                                getValue(I.getOperand(1)), Fn));
}
AnyValue UBAwareInterpreter::visitUnOp(
    Type *RetTy, const AnyValue &Val,
    const function_ref<SingleValue(const SingleValue &)> &Fn,
    bool PropagatesPoison) {
  auto FnPoison = [&Fn](const SingleValue &V) -> SingleValue {
    if (isPoison(V))
      return poison();
    return Fn(V);
  };
  auto &UsedFn = PropagatesPoison ? FnPoison : Fn;
  if (auto *VTy = dyn_cast<VectorType>(RetTy)) {
    uint32_t Len = getVectorLength(VTy);
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I)
      Res.push_back(AnyValue{UsedFn(Val.getSingleValueAt(I))});
    return std::move(Res);
  }
  return AnyValue{UsedFn(Val.getSingleValue())};
}
bool UBAwareInterpreter::visitUnOp(
    Instruction &I, const function_ref<SingleValue(const SingleValue &)> &Fn,
    bool PropagatesPoison) {
  return addValue(I, visitUnOp(I.getType(), getValue(I.getOperand(0)), Fn,
                               PropagatesPoison));
}
AnyValue UBAwareInterpreter::visitTriOp(
    Type *RetTy, const AnyValue &X, const AnyValue &Y, const AnyValue &Z,
    const function_ref<SingleValue(const SingleValue &, const SingleValue &,
                                   const SingleValue &)> &Fn) {
  auto FnPoison = [&Fn](const SingleValue &XV, const SingleValue &YV,
                        const SingleValue &ZV) -> SingleValue {
    if (isPoison(XV) || isPoison(YV) || isPoison(ZV))
      return poison();
    return Fn(XV, YV, ZV);
  };
  if (auto *VTy = dyn_cast<VectorType>(RetTy)) {
    uint32_t Len = getVectorLength(VTy);
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I)
      Res.push_back(
          AnyValue{FnPoison(X.getSingleValueAt(I), Y.getSingleValueAt(I),
                            Z.getSingleValueAt(I))});
    return std::move(Res);
  }
  return AnyValue{
      FnPoison(X.getSingleValue(), Y.getSingleValue(), Z.getSingleValue())};
}

bool UBAwareInterpreter::visitICmpInst(ICmpInst &I) {
  bool SameSign = true;
  auto ICmp = [&](const SingleValue &LHS,
                  const SingleValue &RHS) -> SingleValue {
    const auto &LHSC = std::get<APInt>(LHS);
    const auto &RHSC = std::get<APInt>(RHS);
    if (I.hasSameSign()) {
      if (LHSC.isNonNegative() != RHSC.isNonNegative())
        return poison();
    } else if (EMIInfo.EnablePGFTracking) {
      SameSign &= LHSC.isNonNegative() == RHSC.isNonNegative();
    }
    return boolean(ICmpInst::compare(LHSC, RHSC, I.getPredicate()));
  };
  auto ICmpPtr = [&](const SingleValue &LHS,
                     const SingleValue &RHS) -> SingleValue {
    if (std::holds_alternative<Pointer>(LHS)) {
      assert(std::holds_alternative<Pointer>(RHS));

      // Unfortunatly, we cannot track if the result is leaked out of
      // the function.
      auto IsCaptureInfoCorrect = [&I](const Pointer &LHS,
                                       const Pointer &RHS) -> bool {
        if (I.isEquality() && RHS.Address.isZero())
          return LHS.Info.ComparableWithNull;
        return LHS.Info.Comparable;
      };

      if (IsCaptureInfoCorrect(std::get<Pointer>(LHS),
                               std::get<Pointer>(RHS)) &&
          IsCaptureInfoCorrect(std::get<Pointer>(RHS), std::get<Pointer>(LHS)))
        return ICmp(std::get<Pointer>(LHS).Address,
                    std::get<Pointer>(RHS).Address);
      return poison();
    }
    return ICmp(LHS, RHS);
  };
  auto RetVal = visitBinOp(I, ICmpPtr);
  if (EMIInfo.EnablePGFTracking && !I.hasSameSign())
    EMIInfo.ICmpFlags[&I] |= !SameSign;
  return RetVal;
}
AnyValue UBAwareInterpreter::visitIntBinOp(
    Type *RetTy, const AnyValue &LHS, const AnyValue &RHS,
    const function_ref<std::optional<APInt>(const APInt &, const APInt &)>
        &Fn) {
  return visitBinOp(
      RetTy, LHS, RHS,
      [&Fn](const SingleValue &LHS, const SingleValue &RHS) -> SingleValue {
        auto &LHSC = std::get<APInt>(LHS);
        auto &RHSC = std::get<APInt>(RHS);
        if (auto Res = Fn(LHSC, RHSC))
          return SingleValue{*Res};
        return poison();
      });
}
AnyValue UBAwareInterpreter::visitFPBinOp(
    Type *RetTy, FastMathFlags FMF, const AnyValue &LHS, const AnyValue &RHS,
    const function_ref<std::optional<APFloat>(const APFloat &, const APFloat &)>
        &Fn) {
  auto Denormal = getCurrentDenormalMode(RetTy);
  return visitBinOp(
      RetTy, LHS, RHS,
      [&Fn, FMF, Denormal](const SingleValue &LHS,
                           const SingleValue &RHS) -> SingleValue {
        auto &LHSC = std::get<APFloat>(LHS);
        auto &RHSC = std::get<APFloat>(RHS);
        if (isPoison(LHSC, FMF) || isPoison(RHSC, FMF))
          return poison();
        if (auto Res = Fn(handleDenormal(LHSC, Denormal.Input),
                          handleDenormal(RHSC, Denormal.Input)))
          return handleFPVal(*Res, FMF, Denormal.Output);
        return poison();
      });
}
bool UBAwareInterpreter::visitIntBinOp(
    Instruction &I,
    const function_ref<std::optional<APInt>(const APInt &, const APInt &)>
        &Fn) {
  return addValue(I, visitIntBinOp(I.getType(), getValue(I.getOperand(0)),
                                   getValue(I.getOperand(1)), Fn));
}
bool UBAwareInterpreter::visitFPBinOp(
    Instruction &I,
    const function_ref<std::optional<APFloat>(const APFloat &, const APFloat &)>
        &Fn) {
  return addValue(I, visitFPBinOp(I.getType(), I.getFastMathFlags(),
                                  getValue(I.getOperand(0)),
                                  getValue(I.getOperand(1)), Fn));
}
AnyValue UBAwareInterpreter::visitIntTriOp(
    Type *RetTy, const AnyValue &X, const AnyValue &Y, const AnyValue &Z,
    const function_ref<std::optional<APInt>(const APInt &, const APInt &,
                                            const APInt &)> &Fn) {
  return visitTriOp(RetTy, X, Y, Z,
                    [&Fn](const SingleValue &X, const SingleValue &Y,
                          const SingleValue &Z) -> SingleValue {
                      auto &XC = std::get<APInt>(X);
                      auto &YC = std::get<APInt>(Y);
                      auto &ZC = std::get<APInt>(Z);
                      if (auto Res = Fn(XC, YC, ZC))
                        return SingleValue{*Res};
                      return poison();
                    });
}
AnyValue UBAwareInterpreter::visitFPTriOp(
    Type *RetTy, FastMathFlags FMF, const AnyValue &X, const AnyValue &Y,
    const AnyValue &Z,
    const function_ref<std::optional<APFloat>(const APFloat &, const APFloat &,
                                              const APFloat &)> &Fn) {
  auto Denormal = getCurrentDenormalMode(RetTy);
  return visitTriOp(
      RetTy, X, Y, Z,
      [&Fn, FMF, Denormal](const SingleValue &X, const SingleValue &Y,
                           const SingleValue &Z) -> SingleValue {
        auto &XC = std::get<APFloat>(X);
        auto &YC = std::get<APFloat>(Y);
        auto &ZC = std::get<APFloat>(Z);
        if (isPoison(XC, FMF) || isPoison(YC, FMF) || isPoison(ZC, FMF))
          return poison();
        if (auto Res = Fn(handleDenormal(XC, Denormal.Input),
                          handleDenormal(YC, Denormal.Input),
                          handleDenormal(ZC, Denormal.Input)))
          return handleFPVal(*Res, FMF, Denormal.Output);
        return poison();
      });
}
bool UBAwareInterpreter::visitAnd(BinaryOperator &I) {
  return visitIntBinOp(
      I, [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        return LHS & RHS;
      });
}
bool UBAwareInterpreter::visitXor(BinaryOperator &I) {
  return visitIntBinOp(
      I, [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        return LHS ^ RHS;
      });
}
bool UBAwareInterpreter::visitOr(BinaryOperator &I) {
  bool AllDisjoint = true;
  auto RetVal = visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (cast<PossiblyDisjointInst>(I).isDisjoint() && LHS.intersects(RHS))
          return std::nullopt;
        if (EMIInfo.EnablePGFTracking && AllDisjoint)
          AllDisjoint &= !LHS.intersects(RHS);
        return LHS | RHS;
      });
  if (EMIInfo.EnablePGFTracking && !cast<PossiblyDisjointInst>(I).isDisjoint())
    EMIInfo.DisjointFlags[cast<PossiblyDisjointInst>(&I)] |= !AllDisjoint;
  return RetVal;
}
bool UBAwareInterpreter::visitShl(BinaryOperator &I) {
  bool HasNSW = true, HasNUW = true;
  auto RetVal = visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.uge(LHS.getBitWidth()))
          return std::nullopt;
        if (EMIInfo.EnablePGFTracking) {
          if (HasNSW && RHS.uge(LHS.getNumSignBits()))
            HasNSW = false;
          if (HasNUW && RHS.ugt(LHS.countl_zero()))
            HasNUW = false;
        }
        if (I.hasNoSignedWrap() && RHS.uge(LHS.getNumSignBits()))
          return std::nullopt;
        if (I.hasNoUnsignedWrap() && RHS.ugt(LHS.countl_zero()))
          return std::nullopt;
        return LHS.shl(RHS);
      });
  if (EMIInfo.EnablePGFTracking &&
      !(I.hasNoSignedWrap() && I.hasNoUnsignedWrap()))
    EMIInfo.NoWrapFlags[&I] |= (!HasNSW ? 2 : 0) | (!HasNUW ? 1 : 0);
  return RetVal;
}
bool UBAwareInterpreter::visitLShr(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.uge(cast<PossiblyExactOperator>(I).isExact()
                        ? LHS.countr_zero() + 1
                        : LHS.getBitWidth()))
          return std::nullopt;
        return LHS.lshr(RHS);
      });
}
bool UBAwareInterpreter::visitAShr(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.uge(cast<PossiblyExactOperator>(I).isExact()
                        ? LHS.countr_zero() + 1
                        : LHS.getBitWidth()))
          return std::nullopt;
        return LHS.ashr(RHS);
      });
}
bool UBAwareInterpreter::visitAdd(BinaryOperator &I) {
  bool AllNSW = true, AllNUW = true;
  auto RetVal = visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        auto Res =
            addNoWrap(LHS, RHS, I.hasNoSignedWrap(), I.hasNoUnsignedWrap());
        if (EMIInfo.EnablePGFTracking && AllNSW) {
          bool Overflow = false;
          (void)LHS.sadd_ov(RHS, Overflow);
          AllNSW &= !Overflow;
        }
        if (EMIInfo.EnablePGFTracking && AllNUW) {
          bool Overflow = false;
          (void)LHS.uadd_ov(RHS, Overflow);
          AllNUW &= !Overflow;
        }
        return Res;
      });

  if (EMIInfo.EnablePGFTracking &&
      !(I.hasNoSignedWrap() && I.hasNoUnsignedWrap()))
    EMIInfo.NoWrapFlags[&I] |= (!AllNSW ? 2 : 0) | (!AllNUW ? 1 : 0);
  return RetVal;
}
bool UBAwareInterpreter::visitSub(BinaryOperator &I) {
  bool AllNSW = true, AllNUW = true;
  auto RetVal = visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        auto Res =
            subNoWrap(LHS, RHS, I.hasNoSignedWrap(), I.hasNoUnsignedWrap());
        if (EMIInfo.EnablePGFTracking && AllNSW) {
          bool Overflow = false;
          (void)LHS.ssub_ov(RHS, Overflow);
          AllNSW &= !Overflow;
        }
        if (EMIInfo.EnablePGFTracking && AllNUW) {
          bool Overflow = false;
          (void)LHS.usub_ov(RHS, Overflow);
          AllNUW &= !Overflow;
        }
        return Res;
      });
  if (EMIInfo.EnablePGFTracking &&
      !(I.hasNoSignedWrap() && I.hasNoUnsignedWrap()))
    EMIInfo.NoWrapFlags[&I] |= (!AllNSW ? 2 : 0) | (!AllNUW ? 1 : 0);
  return RetVal;
}
bool UBAwareInterpreter::visitMul(BinaryOperator &I) {
  bool AllNSW = true, AllNUW = true;
  auto RetVal = visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        auto Res =
            mulNoWrap(LHS, RHS, I.hasNoSignedWrap(), I.hasNoUnsignedWrap());
        if (EMIInfo.EnablePGFTracking && AllNSW) {
          bool Overflow = false;
          (void)LHS.smul_ov(RHS, Overflow);
          AllNSW &= !Overflow;
        }
        if (EMIInfo.EnablePGFTracking && AllNUW) {
          bool Overflow = false;
          (void)LHS.umul_ov(RHS, Overflow);
          AllNUW &= !Overflow;
        }
        return Res;
      });
  if (EMIInfo.EnablePGFTracking &&
      !(I.hasNoSignedWrap() && I.hasNoUnsignedWrap()))
    EMIInfo.NoWrapFlags[&I] |= (!AllNSW ? 2 : 0) | (!AllNUW ? 1 : 0);
  return RetVal;
}
bool UBAwareInterpreter::visitSDiv(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.isZero())
          ImmUBReporter(*this) << "division by zero";
        if (LHS.isMinSignedValue() && RHS.isAllOnes())
          ImmUBReporter(*this) << "signed division overflow";
        APInt Q, R;
        APInt::sdivrem(LHS, RHS, Q, R);
        if (I.isExact() && !R.isZero())
          return std::nullopt;
        return Q;
      });
}
bool UBAwareInterpreter::visitSRem(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.isZero())
          ImmUBReporter(*this) << "division by zero";
        return LHS.srem(RHS);
      });
}
bool UBAwareInterpreter::visitUDiv(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.isZero())
          ImmUBReporter(*this) << "division by zero";
        APInt Q, R;
        APInt::udivrem(LHS, RHS, Q, R);
        if (I.isExact() && !R.isZero())
          return std::nullopt;
        return Q;
      });
}
bool UBAwareInterpreter::visitURem(BinaryOperator &I) {
  return visitIntBinOp(
      I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
        if (RHS.isZero())
          ImmUBReporter(*this) << "division by zero";
        return LHS.urem(RHS);
      });
}
AnyValue UBAwareInterpreter::visitIntUnOp(
    Type *Ty, const AnyValue &Val,
    const function_ref<std::optional<APInt>(const APInt &)> &Fn) {
  return visitUnOp(Ty, Val, [&Fn](const SingleValue &V) -> SingleValue {
    auto &C = std::get<APInt>(V);
    if (auto Res = Fn(C))
      return SingleValue{*Res};
    return poison();
  });
}
bool UBAwareInterpreter::visitIntUnOp(
    Instruction &I,
    const function_ref<std::optional<APInt>(const APInt &)> &Fn) {
  return addValue(I, visitIntUnOp(I.getType(), getValue(I.getOperand(0)), Fn));
}
AnyValue UBAwareInterpreter::visitFPUnOp(
    Type *RetTy, FastMathFlags FMF, const AnyValue &Val,
    const function_ref<std::optional<APFloat>(const APFloat &)> &Fn) {
  auto Denormal = getCurrentDenormalMode(RetTy);
  return visitUnOp(RetTy, Val,
                   [&Fn, FMF, Denormal](const SingleValue &V) -> SingleValue {
                     auto &C = std::get<APFloat>(V);
                     if (isPoison(C, FMF))
                       return poison();
                     if (auto Res = Fn(handleDenormal(C, Denormal.Input)))
                       return handleFPVal(*Res, FMF, Denormal.Output);
                     return poison();
                   });
}
bool UBAwareInterpreter::visitFPUnOp(
    Instruction &I,
    const function_ref<std::optional<APFloat>(const APFloat &)> &Fn) {
  return addValue(I, visitFPUnOp(I.getType(),
                                 isa<FPMathOperator>(I) ? I.getFastMathFlags()
                                                        : FastMathFlags{},
                                 getValue(I.getOperand(0)), Fn));
}
bool UBAwareInterpreter::visitTruncInst(TruncInst &Trunc) {
  bool HasNSW = true, HasNUW = true;
  uint32_t DestBW = Trunc.getDestTy()->getScalarSizeInBits();
  auto RetVal =
      visitIntUnOp(Trunc, [&](const APInt &C) -> std::optional<APInt> {
        if (EMIInfo.EnablePGFTracking) {
          if (HasNSW && C.getSignificantBits() > DestBW)
            HasNSW = false;
          if (HasNUW && C.getActiveBits() > DestBW)
            HasNUW = false;
        }
        if (Trunc.hasNoSignedWrap() && C.getSignificantBits() > DestBW)
          return std::nullopt;
        if (Trunc.hasNoUnsignedWrap() && C.getActiveBits() > DestBW)
          return std::nullopt;
        return C.trunc(DestBW);
      });
  if (EMIInfo.EnablePGFTracking &&
      !(Trunc.hasNoSignedWrap() && Trunc.hasNoUnsignedWrap()))
    EMIInfo.TruncNoWrapFlags[&Trunc] |= (!HasNSW ? 2 : 0) | (!HasNUW ? 1 : 0);
  return RetVal;
}
bool UBAwareInterpreter::visitSExtInst(SExtInst &SExt) {
  uint32_t DestBW = SExt.getDestTy()->getScalarSizeInBits();
  return visitIntUnOp(SExt, [&](const APInt &C) -> std::optional<APInt> {
    return C.sext(DestBW);
  });
}
bool UBAwareInterpreter::visitZExtInst(ZExtInst &ZExt) {
  uint32_t DestBW = ZExt.getDestTy()->getScalarSizeInBits();
  bool IsNNeg = ZExt.hasNonNeg();
  bool HasNNeg = true;
  auto RetVal = visitIntUnOp(ZExt, [&](const APInt &C) -> std::optional<APInt> {
    if (IsNNeg && C.isNegative())
      return std::nullopt;
    if (EMIInfo.EnablePGFTracking)
      HasNNeg &= C.isNonNegative();
    return C.zext(DestBW);
  });
  if (EMIInfo.EnablePGFTracking && !ZExt.hasNonNeg())
    EMIInfo.NNegFlags[cast<PossiblyNonNegInst>(&ZExt)] |= !HasNNeg;
  return RetVal;
}
bool UBAwareInterpreter::fpCast(Instruction &I) {
  auto &DstSem = I.getType()->getScalarType()->getFltSemantics();
  return visitFPUnOp(I, [&](const APFloat &C) -> std::optional<APFloat> {
    auto V = C;
    bool LosesInfo;
    V.convert(DstSem, APFloat::rmNearestTiesToEven, &LosesInfo);
    return V;
  });
}
bool UBAwareInterpreter::visitFPExtInst(FPExtInst &FPExt) {
  return fpCast(FPExt);
}
bool UBAwareInterpreter::visitFPTruncInst(FPTruncInst &FPTrunc) {
  return fpCast(FPTrunc);
}
bool UBAwareInterpreter::visitIntToFPInst(Instruction &I, bool IsSigned) {
  auto &DstSem = I.getType()->getScalarType()->getFltSemantics();
  return visitUnOp(I, [&](const SingleValue &C) -> SingleValue {
    if (isPoison(C))
      return poison();
    auto &CI = std::get<APInt>(C);
    if (!IsSigned && I.hasNonNeg() && CI.isNegative())
      return poison();
    APFloat V(DstSem);
    V.convertFromAPInt(CI, IsSigned, APFloat::rmNearestTiesToEven);
    return V;
  });
}
bool UBAwareInterpreter::visitSIToFPInst(SIToFPInst &I) {
  return visitIntToFPInst(I, true);
}
bool UBAwareInterpreter::visitUIToFPInst(UIToFPInst &I) {
  return visitIntToFPInst(I, false);
}
bool UBAwareInterpreter::visitFPToIntInst(Instruction &I, bool IsSigned) {
  auto BitWidth = I.getType()->getScalarSizeInBits();
  return visitUnOp(I, [&](const SingleValue &C) -> SingleValue {
    if (isPoison(C))
      return poison();
    auto &CFP = std::get<APFloat>(C);
    APSInt V(BitWidth, !IsSigned);
    bool IsExact;
    auto Status = CFP.convertToInteger(V, APFloat::rmTowardZero, &IsExact);
    if (Status != APFloat::opInvalidOp)
      return V;
    (void)(IsExact);
    return poison();
  });
}
bool UBAwareInterpreter::visitFPToSIInst(FPToSIInst &I) {
  return visitFPToIntInst(I, true);
}
bool UBAwareInterpreter::visitFPToUIInst(FPToUIInst &I) {
  return visitFPToIntInst(I, false);
}
bool UBAwareInterpreter::visitFNeg(UnaryOperator &I) {
  return visitFPUnOp(I, [](const APFloat &X) { return -X; });
}
bool UBAwareInterpreter::visitFAdd(BinaryOperator &I) {
  return visitFPBinOp(I,
                      [](const APFloat &X, const APFloat &Y) { return X + Y; });
}
bool UBAwareInterpreter::visitFSub(BinaryOperator &I) {
  return visitFPBinOp(I,
                      [](const APFloat &X, const APFloat &Y) { return X - Y; });
}
bool UBAwareInterpreter::visitFMul(BinaryOperator &I) {
  return visitFPBinOp(I,
                      [](const APFloat &X, const APFloat &Y) { return X * Y; });
}
bool UBAwareInterpreter::visitFDiv(BinaryOperator &I) {
  return visitFPBinOp(I,
                      [](const APFloat &X, const APFloat &Y) { return X / Y; });
}
bool UBAwareInterpreter::visitFRem(BinaryOperator &I) {
  return visitFPBinOp(I, [](const APFloat &X, const APFloat &Y) {
    auto Z = X;
    Z.mod(Y);
    return Z;
  });
}
bool UBAwareInterpreter::visitFCmpInst(FCmpInst &FCmp) {
  auto FMF = FCmp.getFastMathFlags();
  return visitBinOp(
      FCmp, [&](const SingleValue &LHS, const SingleValue &RHS) -> SingleValue {
        if (isPoison(LHS) || isPoison(RHS))
          return poison();
        auto &LHSC = std::get<APFloat>(LHS);
        auto &RHSC = std::get<APFloat>(RHS);
        if (isPoison(LHSC, FMF) || isPoison(RHSC, FMF))
          return poison();
        return boolean(FCmpInst::compare(LHSC, RHSC, FCmp.getPredicate()));
      });
}
AnyValue UBAwareInterpreter::freezeValue(const AnyValue &Val, Type *Ty) {
  if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    uint32_t Len = StructTy->getStructNumElements();
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      auto *EltTy = StructTy->getStructElementType(I);
      Res.push_back(freezeValue(Val.getValueArray().at(I), EltTy));
    }
    return std::move(Res);
  }
  return visitUnOp(
      Ty, Val,
      [&](const SingleValue &C) -> SingleValue {
        if (isPoison(C))
          return getZero(Ty->getScalarType()).getSingleValue();
        return C;
      },
      /*PropagatesPoison=*/false);
}
bool UBAwareInterpreter::visitFreezeInst(FreezeInst &Freeze) {
  return addValue(
      Freeze, freezeValue(getValue(Freeze.getOperand(0)), Freeze.getType()));
}
bool UBAwareInterpreter::visitSelect(SelectInst &SI) {
  if (SI.getCondition()->getType()->isIntegerTy(1)) {
    switch (getBoolean(SI.getCondition())) {
    case BooleanVal::True:
      return addValue(SI, postProcessFPVal(getValue(SI.getTrueValue()), SI));
    case BooleanVal::False:
      return addValue(SI, postProcessFPVal(getValue(SI.getFalseValue()), SI));
    case BooleanVal::Poison:
      return addValue(SI, getPoison(SI.getType()));
    }
  }

  uint32_t Len = getVectorLength(cast<VectorType>(SI.getType()));
  auto Cond = getValue(SI.getCondition());
  auto TV = getValue(SI.getTrueValue());
  auto FV = getValue(SI.getFalseValue());
  std::vector<AnyValue> Res;
  Res.reserve(Len);
  for (uint32_t I = 0; I < Len; ++I) {
    switch (getBoolean(Cond.getSingleValueAt(I))) {
    case BooleanVal::True:
      Res.push_back(std::move(TV.getSingleValueAt(I)));
      break;
    case BooleanVal::False:
      Res.push_back(std::move(FV.getSingleValueAt(I)));
      break;
    case BooleanVal::Poison:
      Res.push_back(getPoison(SI.getType()->getScalarType()));
      break;
    }
  }
  return addValue(SI, postProcessFPVal(std::move(Res), SI));
}
bool UBAwareInterpreter::visitBranchInst(BranchInst &BI) {
  if (BI.isConditional()) {
    switch (getBoolean(BI.getCondition())) {
    case BooleanVal::True:
      return jumpTo(BI.getSuccessor(0));
    case BooleanVal::False:
      return jumpTo(BI.getSuccessor(1));
    case BooleanVal::Poison:
      ImmUBReporter(*this) << "Branch on poison";
    }
  }
  return jumpTo(BI.getSuccessor(0));
}
bool UBAwareInterpreter::visitIndirectBrInst(IndirectBrInst &IBI) {
  auto Ptr = getValue(IBI.getAddress()).getSingleValue();
  if (isPoison(Ptr))
    ImmUBReporter(*this) << "Indirect branch on poison";
  auto It =
      ValidBlockTargets.find(std::get<Pointer>(Ptr).Address.getZExtValue());
  if (It == ValidBlockTargets.end())
    ImmUBReporter(*this) << "Indirect branch on invalid target BB";
  auto DestBB = It->second;
  for (uint32_t I = 0, E = IBI.getNumDestinations(); I != E; ++I) {
    if (IBI.getDestination(I) == DestBB)
      return jumpTo(DestBB);
  }
  ImmUBReporter(*this) << "Indirect branch on unlisted target BB "
                       << *BlockAddress::get(DestBB);
  llvm_unreachable("Unreachable code");
}
SingleValue UBAwareInterpreter::computeGEP(const SingleValue &Base,
                                           const APInt &Offset,
                                           GEPNoWrapFlags Flags) {
  if (isPoison(Base))
    return Base;
  auto &Ptr = std::get<Pointer>(Base);
  return offsetPointer(Ptr, Offset, Flags);
}
bool UBAwareInterpreter::visitGetElementPtrInst(GetElementPtrInst &GEP) {
  // TODO: handle inrange
  uint32_t BitWidth = DL.getIndexSizeInBits(0);
  APInt Offset = APInt::getZero(BitWidth);
  SmallMapVector<Value *, APInt, 4> VarOffsets;
  if (!GEP.collectOffset(DL, BitWidth, VarOffsets, Offset)) {
    errs() << "Unsupported GEP " << GEP << '\n';
    std::abort();
  }
  auto Flags = GEP.getNoWrapFlags();
  auto CanonicalizeBitWidth = [&](APInt &Idx) {
    if (Idx.getBitWidth() == BitWidth)
      return true;
    if (Idx.getBitWidth() > BitWidth) {
      if (Flags.hasNoUnsignedSignedWrap() &&
          Idx.getSignificantBits() > BitWidth)
        return false;
      if (Flags.hasNoUnsignedWrap() && Idx.getActiveBits() > BitWidth)
        return false;
      Idx = Idx.trunc(BitWidth);
      return true;
    }
    Idx = Idx.sext(BitWidth);
    return true;
  };
  if (auto *VTy = dyn_cast<VectorType>(GEP.getType())) {
    uint32_t Len = getVectorLength(VTy);
    auto GetSplat = [Len](AnyValue V) -> AnyValue {
      if (V.isSingleValue())
        return std::vector<AnyValue>{Len, std::move(V)};
      return std::move(V);
    };
    AnyValue Res = GetSplat(getValue(GEP.getPointerOperand()));
    for (auto &[K, V] : VarOffsets) {
      auto KV = GetSplat(getValue(K));
      for (uint32_t I = 0; I != Len; ++I) {
        if (auto Idx = getInt(KV.getSingleValueAt(I))) {
          auto &IdxVal = *Idx;
          if (CanonicalizeBitWidth(IdxVal)) {
            if (auto Off = mulNoWrap(IdxVal, V, Flags.hasNoUnsignedSignedWrap(),
                                     Flags.hasNoUnsignedWrap())) {
              Res.getSingleValueAt(I) =
                  computeGEP(Res.getSingleValueAt(I), *Off, Flags);
              continue;
            }
          }
        }
        Res.getSingleValueAt(I) = poison();
      }
    }
    for (uint32_t I = 0; I != Len; ++I) {
      Res.getSingleValueAt(I) =
          computeGEP(Res.getSingleValueAt(I), Offset, Flags);
    }
    return addValue(GEP, std::move(Res));
  }

  SingleValue Res = getValue(GEP.getPointerOperand()).getSingleValue();
  if (isPoison(Res))
    return addValue(GEP, Res);
  for (auto &[K, V] : VarOffsets) {
    if (auto Idx = getInt(K)) {
      auto &IdxVal = *Idx;
      if (CanonicalizeBitWidth(IdxVal)) {
        if (auto Off = mulNoWrap(IdxVal, V, Flags.hasNoUnsignedSignedWrap(),
                                 Flags.hasNoUnsignedWrap())) {
          Res = computeGEP(Res, *Off, Flags);
          continue;
        }
      }
    }
    return addValue(GEP, poison());
  }
  return addValue(GEP, computeGEP(Res, Offset, Flags));
}
bool UBAwareInterpreter::visitExtractValueInst(ExtractValueInst &EVI) {
  AnyValue Res = getValue(EVI.getAggregateOperand());
  for (auto Idx : EVI.indices()) {
    auto Sub = std::move(Res.getValueArray().at(Idx));
    Res = std::move(Sub);
  }
  return addValue(EVI, std::move(Res));
}
bool UBAwareInterpreter::visitInsertValueInst(InsertValueInst &IVI) {
  auto Res = getValue(IVI.getAggregateOperand());
  auto Val = getValue(IVI.getInsertedValueOperand());
  AnyValue *Pos = &Res;
  for (auto Idx : IVI.indices())
    Pos = &Pos->getValueArray().at(Idx);
  *Pos = std::move(Val);
  return addValue(IVI, std::move(Res));
}
bool UBAwareInterpreter::visitInsertElementInst(InsertElementInst &IEI) {
  auto Res = getValue(IEI.getOperand(0));
  auto Insert = getValue(IEI.getOperand(1));
  auto Idx = getInt(IEI.getOperand(2));
  if (!Idx.has_value() || Idx->uge(Res.getValueArray().size()))
    return addValue(IEI, getPoison(IEI.getType()));
  Res.getValueArray().at(Idx->getZExtValue()) = std::move(Insert);
  return addValue(IEI, std::move(Res));
}
bool UBAwareInterpreter::visitExtractElementInst(ExtractElementInst &EEI) {
  auto Src = getValue(EEI.getOperand(0));
  auto Idx = getInt(EEI.getOperand(1));
  if (!Idx.has_value() || Idx->uge(Src.getValueArray().size()))
    return addValue(EEI, getPoison(EEI.getType()));
  return addValue(EEI, std::move(Src.getValueArray().at(Idx->getZExtValue())));
}
bool UBAwareInterpreter::visitShuffleVectorInst(ShuffleVectorInst &SVI) {
  assert(!SVI.getType()->isScalableTy() && "Not implemented");
  auto LHS = getValue(SVI.getOperand(0));
  uint32_t Size = LHS.getValueArray().size();
  bool RHSIsPoison = isa<PoisonValue>(SVI.getOperand(1));
  auto RHS = RHSIsPoison ? AnyValue{} : getValue(SVI.getOperand(1));
  std::vector<AnyValue> PickedValues;
  PickedValues.reserve(SVI.getShuffleMask().size());
  for (auto Idx : SVI.getShuffleMask()) {
    if (Idx == PoisonMaskElem)
      PickedValues.push_back(poison());
    else if (Idx < static_cast<int32_t>(Size))
      PickedValues.push_back(LHS.getSingleValueAt(Idx));
    else if (RHSIsPoison)
      PickedValues.push_back(getPoison(SVI.getType()->getScalarType()));
    else
      PickedValues.push_back(RHS.getSingleValueAt(Idx - Size));
  }
  return addValue(SVI, std::move(PickedValues));
}
bool UBAwareInterpreter::visitStoreInst(StoreInst &SI) {
  AnyValue StoreVal = getValue(SI.getValueOperand());
  if (SI.getAccessType()->isPtrOrPtrVectorTy()) {
    postProcess(StoreVal, [&](SingleValue &SV) {
      if (isPoison(SV))
        return;
      // FIXME: This is too strict.
      auto &Ptr = std::get<Pointer>(SV);
      CaptureComponents Usage = CaptureComponents::All;
      CaptureComponents Allowed = Ptr.Info.CI.getOtherComponents();
      if ((Usage & Allowed) != Usage)
        SV = poison();
    });
  }
  store(getValue(SI.getPointerOperand()), SI.getAlign().value(),
        std::move(StoreVal), SI.getValueOperand()->getType(), SI.isVolatile());
  return true;
}
void UBAwareInterpreter::handleRangeMetadata(AnyValue &V, Instruction &I) {
  if (auto *MD = I.getMetadata(LLVMContext::MD_range)) {
    auto CR = getConstantRangeFromMetadata(*MD);
    postProcess(V, [&](SingleValue &SV) { handleRange(SV, CR); });
  }
}
bool UBAwareInterpreter::visitLoadInst(LoadInst &LI) {
  auto RetVal = load(getValue(LI.getPointerOperand()), LI.getAlign().value(),
                     LI.getType(), LI.isVolatile());
  if (LI.getType()->isPointerTy()) {
    if (LI.hasMetadata(LLVMContext::MD_nonnull))
      postProcess(RetVal, handleNonNull);
    if (auto *MD = LI.getMetadata(LLVMContext::MD_dereferenceable)) {
      size_t Deref =
          mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
      postProcess(RetVal, [&](SingleValue &SV) {
        handleDereferenceable(*this, SV, Deref, false);
      });
    }
    if (auto *MD = LI.getMetadata(LLVMContext::MD_dereferenceable_or_null)) {
      size_t Deref =
          mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
      postProcess(RetVal, [&](SingleValue &SV) {
        handleDereferenceable(*this, SV, Deref, true);
      });
    }
    if (auto *MD = LI.getMetadata(LLVMContext::MD_align)) {
      size_t Align =
          mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
      postProcess(RetVal, [Align](SingleValue &SV) { handleAlign(SV, Align); });
    }
  }
  handleRangeMetadata(RetVal, LI);
  if (LI.hasMetadata(LLVMContext::MD_noundef))
    postProcess(RetVal,
                [&](SingleValue &SV) { return handleNoUndef(*this, SV); });
  else if (EMIInfo.EnablePGFTracking && RetVal.isSingleValue()) {
    EMIInfo.MayBeUndef[&LI] = isPoison(RetVal.getSingleValue());
    if (LI.getType()->isIntegerTy() && !isPoison(RetVal.getSingleValue()))
      EMIInfo.trackRange(&LI, std::get<APInt>(RetVal.getSingleValue()));
  }
  return addValue(LI, std::move(RetVal));
}
void UBAwareInterpreter::writeBits(APInt &Dst, uint32_t &Offset,
                                   const APInt &Src) {
  Dst.insertBits(Src, Offset);
  Offset += Src.getBitWidth();
}
void UBAwareInterpreter::toBits(APInt &Bits, APInt &PoisonBits,
                                uint32_t &Offset, const AnyValue &Val,
                                Type *Ty) {
  if (Val.isSingleValue() && isPoison(Val.getSingleValue())) {
    unsigned BW = DL.getTypeSizeInBits(Ty).getFixedValue();
    PoisonBits.setBits(Offset, Offset + BW);
    Offset += BW;
    return;
  }
  if (Ty->isIntegerTy()) {
    writeBits(Bits, Offset, std::get<APInt>(Val.getSingleValue()));
  } else if (Ty->isFloatingPointTy()) {
    writeBits(Bits, Offset,
              std::get<APFloat>(Val.getSingleValue()).bitcastToAPInt());
  } else if (Ty->isPointerTy()) {
    writeBits(Bits, Offset, std::get<Pointer>(Val.getSingleValue()).Address);
  } else if (auto *VTy = dyn_cast<VectorType>(Ty)) {
    Type *EltTy = VTy->getElementType();
    for (auto &Sub : Val.getValueArray())
      toBits(Bits, PoisonBits, Offset, Sub, EltTy);
  } else {
    errs() << "Unrecognized type " << *Ty << '\n';
    std::abort();
  }
}
bool UBAwareInterpreter::visitIntToPtr(IntToPtrInst &I) {
  return visitUnOp(I, [&](const SingleValue &V) -> SingleValue {
    if (isPoison(V))
      return poison();
    return MemMgr.lookupPointer(std::get<APInt>(V));
  });
}
bool UBAwareInterpreter::visitPtrToInt(PtrToIntInst &I) {
  return visitUnOp(I, [&](const SingleValue &V) -> SingleValue {
    if (isPoison(V))
      return poison();
    auto &Ptr = std::get<Pointer>(V);
    if (Ptr.Info.Comparable)
      return Ptr.Address;
    return poison();
  });
}
APInt UBAwareInterpreter::readBits(const APInt &Src, uint32_t &Offset,
                                   uint32_t Width) {
  auto Res = Src.extractBits(Width, Offset);
  Offset += Width;
  return Res;
}
AnyValue UBAwareInterpreter::fromBits(const APInt &Bits,
                                      const APInt &PoisonBits, uint32_t &Offset,
                                      Type *Ty) {
  if (Ty->isIntOrPtrTy() || Ty->isFloatingPointTy()) {
    if (APInt::getBitsSet(Bits.getBitWidth(), Offset,
                          Offset + Ty->getScalarSizeInBits())
            .intersects(PoisonBits)) {
      Offset += Ty->getScalarSizeInBits();
      return getPoison(Ty);
    }
  }
  if (Ty->isIntegerTy()) {
    return SingleValue{readBits(Bits, Offset, Ty->getIntegerBitWidth())};
  } else if (Ty->isFloatingPointTy()) {
    return SingleValue{
        APFloat(Ty->getFltSemantics(),
                readBits(Bits, Offset, Ty->getScalarSizeInBits()))};
  } else if (Ty->isPointerTy()) {
    return SingleValue{MemMgr.lookupPointer(
        readBits(Bits, Offset, DL.getPointerSizeInBits()))};
  } else if (auto *VTy = dyn_cast<VectorType>(Ty)) {
    Type *EltTy = VTy->getElementType();
    uint32_t Len = getVectorLength(VTy);
    std::vector<AnyValue> Elts;
    Elts.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      Elts.push_back(fromBits(Bits, PoisonBits, Offset, EltTy));
    }
    return std::move(Elts);
  } else {
    errs() << "Unrecognized type " << *Ty << '\n';
    std::abort();
  }
}
bool UBAwareInterpreter::visitBitCastInst(BitCastInst &BCI) {
  APInt Bits =
      APInt::getZero(DL.getTypeSizeInBits(BCI.getType()).getFixedValue());
  APInt PoisonBits = Bits;
  uint32_t Offset = 0;
  toBits(Bits, PoisonBits, Offset, getValue(BCI.getOperand(0)),
         BCI.getOperand(0)->getType());
  Offset = 0;
  return addValue(BCI, fromBits(Bits, PoisonBits, Offset, BCI.getType()));
}
std::string UBAwareInterpreter::getValueName(Value *V) {
  std::string Str;
  raw_string_ostream Out(Str);
  V->printAsOperand(Out);
  return Str;
}
AnyValue UBAwareInterpreter::handleCall(CallBase &CB) {
  SmallVector<AnyValue> Args;
  for (const auto &[Idx, Arg] : enumerate(CB.args()))
    Args.push_back(getValue(Arg));
  auto *CalledFunc = CB.getCalledOperand();
  Function *Callee = dyn_cast<Function>(CalledFunc);
  if (!Callee) {
    if (auto *Asm = dyn_cast<InlineAsm>(CalledFunc)) {
      // Handle empty asm string, which is used to implement black_box style
      // optimization blockers.
      if (Asm->getAsmString().empty() && CB.getType()->isVoidTy())
        return {};
      errs() << "Unsupported inline asm\n";
      std::abort();
    }
    auto Addr = getValue(CalledFunc).getSingleValue();
    if (isPoison(Addr))
      ImmUBReporter(*this) << "Call with poison callee";
    auto FuncAddr = std::get<Pointer>(Addr).Address.getZExtValue();
    if (auto It = ValidCallees.find(FuncAddr); It != ValidCallees.end())
      Callee = It->second;
    else
      ImmUBReporter(*this) << "Call with invalid callee";
  }
  auto RetVal = call(Callee, &CB, Args);
  handleRangeMetadata(RetVal, CB);
  postProcessAttr(*this, RetVal, CB.getRetAttributes());
  if (auto *Val = CB.getReturnedArgOperand()) {
    auto Expected = getValue(Val);
    if (!RetVal.refines(Expected))
      ImmUBReporter(*this) << "Return value mismatch";
  }
  return RetVal;
}
bool UBAwareInterpreter::visitCallInst(CallInst &CI) {
  auto RetVal = handleCall(CI);
  if (EMIInfo.EnablePGFTracking && RetVal.isSingleValue()) {
    EMIInfo.MayBeUndef[&CI] |= isPoison(RetVal.getSingleValue());
    if (CI.getType()->isIntegerTy() && !isPoison(RetVal.getSingleValue()))
      EMIInfo.trackRange(&CI, std::get<APInt>(RetVal.getSingleValue()));
  }
  return addValue(CI, std::move(RetVal));
}
bool UBAwareInterpreter::visitInvokeInst(InvokeInst &II) {
  auto RetVal = handleCall(II);
  if (EMIInfo.EnablePGFTracking && RetVal.isSingleValue()) {
    EMIInfo.MayBeUndef[&II] |= isPoison(RetVal.getSingleValue());
    if (II.getType()->isIntegerTy() && !isPoison(RetVal.getSingleValue()))
      EMIInfo.trackRange(&II, std::get<APInt>(RetVal.getSingleValue()));
  }
  addValue(II, std::move(RetVal));
  // TODO: handle exceptions
  return jumpTo(II.getNormalDest());
}
bool UBAwareInterpreter::visitReturnInst(ReturnInst &RI) {
  if (auto *RV = RI.getReturnValue()) {
    AnyValue RetVal = getValue(RV);
    if (RV->getType()->isPtrOrPtrVectorTy())
      postProcess(RetVal, [this](SingleValue &SV) {
        if (isPoison(SV))
          return;
        auto &Ptr = std::get<Pointer>(SV);
        auto CC = Ptr.Info.CI.getRetComponents();
        Ptr.Info.pop(CurrentFrame);
        if ((CC & CaptureComponents::Address) != CaptureComponents::Address)
          Ptr.Info.Comparable = false;
        if ((CC & CaptureComponents::AddressIsNull) !=
            CaptureComponents::AddressIsNull)
          Ptr.Info.ComparableWithNull = false;
        if ((CC & CaptureComponents::ReadProvenance) !=
            CaptureComponents::ReadProvenance)
          Ptr.Info.Readable = false;
        if ((CC & CaptureComponents::Provenance) !=
            CaptureComponents::Provenance)
          Ptr.Info.Writable = false;
      });
    CurrentFrame->RetVal = std::move(RetVal);
  } else
    CurrentFrame->RetVal = none();
  return false;
}
bool UBAwareInterpreter::visitUnreachableInst(UnreachableInst &) {
  ImmUBReporter(*this) << "Unreachable code";
  llvm_unreachable("Unreachable code");
}
bool UBAwareInterpreter::visitSwitchInst(SwitchInst &SI) {
  auto Cond = getInt(SI.getCondition());
  if (!Cond)
    ImmUBReporter(*this) << "Switch on poison condition";
  for (auto &Case : SI.cases()) {
    if (Case.getCaseValue()->getValue() == *Cond)
      return jumpTo(Case.getCaseSuccessor());
  }
  return jumpTo(SI.getDefaultDest());
}
bool UBAwareInterpreter::visitInstruction(Instruction &I) {
  errs() << "Unsupported inst " << I << '\n';
  std::abort();
}

AnyValue UBAwareInterpreter::handleWithOverflow(
    Type *OpTy, const AnyValue &LHS, const AnyValue &RHS,
    const function_ref<std::pair<APInt, bool>(const APInt &, const APInt &)>
        &Fn) {
  auto FnPoison =
      [&Fn](const SingleValue &LHS,
            const SingleValue &RHS) -> std::pair<SingleValue, SingleValue> {
    if (isPoison(LHS) || isPoison(RHS))
      return {poison(), poison()};
    auto [Val, Overflow] = Fn(std::get<APInt>(LHS), std::get<APInt>(RHS));
    return {Val, boolean(Overflow)};
  };
  if (auto *VTy = dyn_cast<VectorType>(OpTy)) {
    uint32_t Len = getVectorLength(VTy);
    std::vector<AnyValue> Res;
    std::vector<AnyValue> Overflow;
    Res.reserve(Len);
    Overflow.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      auto [K, V] = FnPoison(LHS.getSingleValueAt(I), RHS.getSingleValueAt(I));
      Res.push_back(std::move(K));
      Overflow.push_back(std::move(V));
    }
    return std::vector<AnyValue>{std::move(Res), std::move(Overflow)};
  }
  auto [K, V] = FnPoison(LHS.getSingleValue(), RHS.getSingleValue());
  return std::vector<AnyValue>{std::move(K), std::move(V)};
}

AnyValue UBAwareInterpreter::callIntrinsic(IntrinsicInst &II,
                                           SmallVectorImpl<AnyValue> &Args) {
  auto IID = II.getIntrinsicID();
  Type *RetTy = II.getType();
  FastMathFlags FMF =
      isa<FPMathOperator>(II) ? II.getFastMathFlags() : FastMathFlags();
  switch (IID) {
  case Intrinsic::ssa_copy:
    return Args[0];
  case Intrinsic::donothing:
    return none();
  case Intrinsic::vscale:
    return SingleValue{APInt(RetTy->getScalarSizeInBits(), Option.VScale)};
  case Intrinsic::lifetime_start:
  case Intrinsic::lifetime_end: {
    auto Size = getInt(Args[0].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "call lifetime intrinsic with poison size";
    auto &Ptr = Args[1].getSingleValue();
    if (auto *P = std::get_if<Pointer>(&Ptr)) {
      if (auto MO = P->Obj.lock()) {
        if (Size->isAllOnes())
          Size = APInt(Size->getBitWidth(), MO->size());
        // FIXME: What is the meaning of size?
        if (MO->isStackObject(CurrentFrame->LastFrame) && P->Offset.isZero()) {
          if (MO->isAlive() || IID == Intrinsic::lifetime_start)
            MO->markPoison(0, MO->size(), IID != Intrinsic::lifetime_start);
          MO->setLiveness(IID == Intrinsic::lifetime_start);
        } else {
          MO->markPoison(0, MO->size(), true);
        }
      } else
        ImmUBReporter(*this) << "call lifetime intrinsic with dangling pointer";
    } else {
      ImmUBReporter(*this) << "call lifetime intrinsic with poison pointer";
    }
    return none();
  }
  case Intrinsic::experimental_noalias_scope_decl:
    return none();
  case Intrinsic::umin:
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return APIntOps::umin(LHS, RHS);
        });
  case Intrinsic::umax:
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return APIntOps::umax(LHS, RHS);
        });
  case Intrinsic::smin:
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return APIntOps::smin(LHS, RHS);
        });
  case Intrinsic::smax:
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return APIntOps::smax(LHS, RHS);
        });
  case Intrinsic::memcpy:
  case Intrinsic::memcpy_inline:
  case Intrinsic::memmove: {
    auto Size = getInt(Args[2].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "memcpy with poison size";
    if (Size->isZero())
      return none();
    auto CopySize = Size->getZExtValue();
    bool IsVolatile = getBooleanNonPoison(Args[3].getSingleValue());
    auto Dst =
        getRawPtr(Args[0].getSingleValue(), CopySize, 1U, true, IsVolatile);
    auto Src =
        getRawPtr(Args[1].getSingleValue(), CopySize, 1U, false, IsVolatile);
    if (IID == Intrinsic::memmove)
      std::memmove(Dst, Src, CopySize);
    else
      std::memcpy(Dst, Src, CopySize);
    return none();
  }
  case Intrinsic::memset:
  case Intrinsic::memset_inline: {
    auto Size = getInt(Args[2].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "memcpy with poison size";
    if (Size->isZero())
      return none();
    auto WriteSize = Size->getZExtValue();
    bool IsVolatile = getBooleanNonPoison(Args[3].getSingleValue());
    auto Dst =
        getRawPtr(Args[0].getSingleValue(), WriteSize, 1U, true, IsVolatile);
    auto Val = getInt(Args[1].getSingleValue());
    if (!Val)
      ImmUBReporter(*this) << "memset with poison value";
    std::memset(Dst, Val->getZExtValue(), WriteSize);
    return none();
  }
  case Intrinsic::ctlz:
  case Intrinsic::cttz: {
    bool IsZeroPoison = getBooleanNonPoison(Args[1].getSingleValue());
    bool AllNonZero = true;
    auto RetVal = visitIntUnOp(
        RetTy, Args[0], [&](const APInt &V) -> std::optional<APInt> {
          if (IsZeroPoison && V.isZero())
            return std::nullopt;
          if (EMIInfo.EnablePGFTracking)
            AllNonZero &= !V.isZero();
          return APInt(V.getBitWidth(), IID == Intrinsic::ctlz
                                            ? V.countl_zero()
                                            : V.countr_zero());
        });
    if (EMIInfo.EnablePGFTracking && !IsZeroPoison)
      EMIInfo.IsPoisonFlags[cast<IntrinsicInst>(CurrentFrame->PC)] |=
          !AllNonZero;
    return RetVal;
  }
  case Intrinsic::abs: {
    bool IsIntMinPoison = getBooleanNonPoison(Args[1].getSingleValue());
    bool AllNonSMin = true;
    auto RetVal = visitIntUnOp(RetTy, Args[0],
                               [&](const APInt &V) -> std::optional<APInt> {
                                 if (IsIntMinPoison && V.isMinSignedValue())
                                   return std::nullopt;
                                 if (EMIInfo.EnablePGFTracking)
                                   AllNonSMin &= !V.isMinSignedValue();
                                 return V.abs();
                               });
    if (EMIInfo.EnablePGFTracking && !IsIntMinPoison)
      EMIInfo.IsPoisonFlags[cast<IntrinsicInst>(CurrentFrame->PC)] |=
          !AllNonSMin;
    return RetVal;
  }
  case Intrinsic::ctpop:
    return visitIntUnOp(RetTy, Args[0],
                        [&](const APInt &V) -> std::optional<APInt> {
                          return APInt(V.getBitWidth(), V.popcount());
                        });
  case Intrinsic::bitreverse:
    return visitIntUnOp(RetTy, Args[0],
                        [&](const APInt &V) -> std::optional<APInt> {
                          return V.reverseBits();
                        });
  case Intrinsic::bswap:
    return visitIntUnOp(
        RetTy, Args[0],
        [&](const APInt &V) -> std::optional<APInt> { return V.byteSwap(); });
  case Intrinsic::ucmp:
  case Intrinsic::scmp: {
    uint32_t BitWidth = RetTy->getScalarSizeInBits();
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (LHS == RHS)
            return APInt::getZero(BitWidth);
          return (IID == Intrinsic::ucmp ? LHS.ult(RHS) : LHS.slt(RHS))
                     ? APInt::getAllOnes(BitWidth)
                     : APInt(BitWidth, 1);
        });
  }
  case Intrinsic::assume: {
    switch (getBoolean(Args[0].getSingleValue())) {
    case BooleanVal::Poison:
      ImmUBReporter(*this) << "assumption violation (poison)";
    case BooleanVal::False:
      ImmUBReporter(*this) << "assumption violation (false)";
    case BooleanVal::True: {
      if (II.hasOperandBundles()) {
        for (auto &BOI : II.bundle_op_infos()) {
          RetainedKnowledge RK =
              llvm::getKnowledgeFromBundle(cast<AssumeInst>(II), BOI);
          if (RK.AttrKind == Attribute::Alignment ||
              RK.AttrKind == Attribute::NonNull ||
              RK.AttrKind == Attribute::Dereferenceable) {
            auto Val = getValue(RK.WasOn);
            postProcess(Val, [&](SingleValue &SV) {
              if (isPoison(SV))
                ImmUBReporter(*this) << "Assumption on poison pointer";
              switch (RK.AttrKind) {
              case Attribute::Alignment:
                handleAlign(SV, RK.ArgValue);
                break;
              case Attribute::NonNull:
                handleNonNull(SV);
                break;
              case Attribute::Dereferenceable:
                handleDereferenceable(*this, SV, RK.ArgValue, /*OrNull=*/false);
                break;
              default:
                llvm_unreachable("Unexpected attribute kind");
              }
              if (isPoison(SV))
                ImmUBReporter(*this) << "Assumption violated";
            });
          }
        }
      }

      return none();
    }
    }
  }
  case Intrinsic::sadd_with_overflow:
  case Intrinsic::ssub_with_overflow:
  case Intrinsic::smul_with_overflow:
  case Intrinsic::uadd_with_overflow:
  case Intrinsic::usub_with_overflow:
  case Intrinsic::umul_with_overflow:
    return handleWithOverflow(
        II.getArgOperand(0)->getType(), Args[0], Args[1],
        [IID](const APInt &LHS, const APInt &RHS) -> std::pair<APInt, bool> {
          APInt Res;
          bool Overflow = false;
          switch (IID) {
          case Intrinsic::sadd_with_overflow:
            Res = LHS.sadd_ov(RHS, Overflow);
            break;
          case Intrinsic::ssub_with_overflow:
            Res = LHS.ssub_ov(RHS, Overflow);
            break;
          case Intrinsic::smul_with_overflow:
            Res = LHS.smul_ov(RHS, Overflow);
            break;
          case Intrinsic::uadd_with_overflow:
            Res = LHS.uadd_ov(RHS, Overflow);
            break;
          case Intrinsic::usub_with_overflow:
            Res = LHS.usub_ov(RHS, Overflow);
            break;
          case Intrinsic::umul_with_overflow:
            Res = LHS.umul_ov(RHS, Overflow);
            break;
          default:
            llvm_unreachable("Unexpected intrinsic ID");
          }
          return {Res, Overflow};
        });
  case Intrinsic::sadd_sat:
  case Intrinsic::ssub_sat:
  case Intrinsic::sshl_sat:
  case Intrinsic::uadd_sat:
  case Intrinsic::usub_sat:
  case Intrinsic::ushl_sat:
    return visitIntBinOp(
        RetTy, Args[0], Args[1],
        [IID](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          switch (IID) {
          case Intrinsic::sadd_sat:
            return LHS.sadd_sat(RHS);
          case Intrinsic::ssub_sat:
            return LHS.ssub_sat(RHS);
          case Intrinsic::sshl_sat:
            return LHS.sshl_sat(RHS);
          case Intrinsic::uadd_sat:
            return LHS.uadd_sat(RHS);
          case Intrinsic::usub_sat:
            return LHS.usub_sat(RHS);
          case Intrinsic::ushl_sat:
            return LHS.ushl_sat(RHS);
          default:
            llvm_unreachable("Unexpected intrinsic ID");
          }
        });
  case Intrinsic::vector_reduce_add:
  case Intrinsic::vector_reduce_mul:
  case Intrinsic::vector_reduce_and:
  case Intrinsic::vector_reduce_or:
  case Intrinsic::vector_reduce_xor:
  case Intrinsic::vector_reduce_smax:
  case Intrinsic::vector_reduce_umax:
  case Intrinsic::vector_reduce_smin:
  case Intrinsic::vector_reduce_umin: {
    std::optional<APInt> Res;
    for (auto &V : Args[0].getValueArray()) {
      auto &SV = V.getSingleValue();
      if (isPoison(SV)) {
        Res.reset();
        break;
      }
      auto &Val = std::get<APInt>(SV);
      if (!Res)
        Res = Val;
      else {
        switch (IID) {
        case Intrinsic::vector_reduce_add:
          *Res += Val;
          break;
        case Intrinsic::vector_reduce_mul:
          *Res *= Val;
          break;
        case Intrinsic::vector_reduce_and:
          *Res &= Val;
          break;
        case Intrinsic::vector_reduce_or:
          *Res |= Val;
          break;
        case Intrinsic::vector_reduce_xor:
          *Res ^= Val;
          break;
        case Intrinsic::vector_reduce_smax:
          *Res = APIntOps::smax(*Res, Val);
          break;
        case Intrinsic::vector_reduce_smin:
          *Res = APIntOps::smin(*Res, Val);
          break;
        case Intrinsic::vector_reduce_umax:
          *Res = APIntOps::umax(*Res, Val);
          break;
        case Intrinsic::vector_reduce_umin:
          *Res = APIntOps::umin(*Res, Val);
          break;
        default:
          llvm_unreachable("Unexpected intrinsic ID");
        }
      }
    }
    return Res.has_value() ? SingleValue{*Res} : poison();
  }
  case Intrinsic::vector_reduce_fadd:
  case Intrinsic::vector_reduce_fmul:
  case Intrinsic::vector_reduce_fmax:
  case Intrinsic::vector_reduce_fmin:
  case Intrinsic::vector_reduce_fmaximum:
  case Intrinsic::vector_reduce_fminimum: {
    auto Denormal = getCurrentDenormalMode(RetTy);
    std::optional<APFloat> Res;
    for (auto &V : Args[0].getValueArray()) {
      auto &SV = V.getSingleValue();
      if (isPoison(SV)) {
        Res.reset();
        break;
      }
      auto &Val = std::get<APFloat>(SV);
      if (isPoison(Val, FMF)) {
        Res.reset();
        break;
      }
      Val = handleDenormal(std::move(Val), Denormal.Input);
      if (!Res)
        Res = Val;
      else {
        switch (IID) {
        case Intrinsic::vector_reduce_fadd:
          *Res = *Res + Val;
          break;
        case Intrinsic::vector_reduce_fmul:
          *Res = *Res * Val;
          break;
        case Intrinsic::vector_reduce_fmax:
          *Res = maxnum(*Res, Val);
          break;
        case Intrinsic::vector_reduce_fmin:
          *Res = minnum(*Res, Val);
          break;
        case Intrinsic::vector_reduce_fmaximum:
          *Res = maximum(*Res, Val);
          break;
        case Intrinsic::vector_reduce_fminimum:
          *Res = minimum(*Res, Val);
          break;
        default:
          llvm_unreachable("Unexpected intrinsic ID");
        }
      }
    }
    return Res.has_value() ? handleFPVal(std::move(*Res), FMF, Denormal.Output)
                           : poison();
  }
  case Intrinsic::fshl:
  case Intrinsic::fshr: {
    return visitIntTriOp(RetTy, Args[0], Args[1], Args[2],
                         [IID](const APInt &X, const APInt &Y,
                               const APInt &Z) -> std::optional<APInt> {
                           uint32_t BitWidth = X.getBitWidth();
                           uint32_t ShAmt = Z.urem(BitWidth);
                           bool IsFShr = IID == Intrinsic::fshr;
                           uint32_t LShrAmt = IsFShr ? ShAmt : BitWidth - ShAmt;
                           uint32_t ShlAmt = !IsFShr ? ShAmt : BitWidth - ShAmt;
                           return X.shl(ShlAmt) | Y.lshr(LShrAmt);
                         });
  }
  case Intrinsic::fabs: {
    return visitFPUnOp(RetTy, FMF, Args[0],
                       [](const APFloat &X) { return abs(X); });
  }
  case Intrinsic::fma: {
    return visitFPTriOp(RetTy, FMF, Args[0], Args[1], Args[2],
                        [](const APFloat &X, const APFloat &Y,
                           const APFloat &Z) -> std::optional<APFloat> {
                          auto Res = X;
                          Res.fusedMultiplyAdd(Y, Z,
                                               RoundingMode::NearestTiesToEven);
                          return Res;
                        });
  }
  case Intrinsic::fmuladd: {
    return visitFPTriOp(RetTy, FMF, Args[0], Args[1], Args[2],
                        [](const APFloat &X, const APFloat &Y, const APFloat &Z)
                            -> std::optional<APFloat> { return X * Y + Z; });
  }
  case Intrinsic::is_fpclass: {
    FPClassTest Mask = static_cast<FPClassTest>(
        getInt(Args[1].getSingleValue())->getZExtValue());
    return visitUnOp(RetTy, Args[0],
                     [Mask](const SingleValue &X) -> SingleValue {
                       if (isPoison(X))
                         return poison();
                       return boolean(std::get<APFloat>(X).classify() & Mask);
                     });
  }
  case Intrinsic::copysign:
  case Intrinsic::maxnum:
  case Intrinsic::minnum:
  case Intrinsic::maximum:
  case Intrinsic::minimum:
  case Intrinsic::maximumnum:
  case Intrinsic::minimumnum: {
    return visitFPBinOp(
        RetTy, FMF, Args[0], Args[1],
        [IID](const APFloat &X, const APFloat &Y) -> std::optional<APFloat> {
          switch (IID) {
          case Intrinsic::copysign:
            return APFloat::copySign(X, Y);
          case Intrinsic::maxnum:
            return maxnum(X, Y);
          case Intrinsic::maximum:
            return maximum(X, Y);
          case Intrinsic::maximumnum:
            return maximumnum(X, Y);
          case Intrinsic::minnum:
            return minnum(X, Y);
          case Intrinsic::minimum:
            return minimum(X, Y);
          case Intrinsic::minimumnum:
            return minimumnum(X, Y);
          default:
            llvm_unreachable("Unexpected intrinsic ID");
          }
        });
  }
  case Intrinsic::load_relative: {
    auto &Ptr = Args[0].getSingleValue();
    if (isPoison(Ptr))
      ImmUBReporter(*this) << "load_relative with poison ptr";
    auto &PtrVal = std::get<Pointer>(Ptr);
    auto Offset = getInt(Args[1].getSingleValue());
    if (!Offset)
      ImmUBReporter(*this) << "load_relative with poison offset";
    auto Addr = offsetPointer(PtrVal, *Offset, GEPNoWrapFlags::inBounds());
    if (isPoison(Addr))
      ImmUBReporter(*this) << "load_relative with invalid address";
    auto LoadedOffset =
        load(Addr, 4, IntegerType::getInt32Ty(Ctx), /*IsVolatile=*/false)
            .getSingleValue();
    if (isPoison(LoadedOffset))
      ImmUBReporter(*this) << "load_relative with poison loaded offset";
    return offsetPointer(
        PtrVal,
        std::get<APInt>(LoadedOffset).sextOrTrunc(DL.getIndexSizeInBits(0)),
        GEPNoWrapFlags::none());
  }
  case Intrinsic::objectsize: {
    auto &Ptr = Args[0].getSingleValue();
    if (!isPoison(Ptr)) {
      if (auto Obj = std::get<Pointer>(Ptr).Obj.lock())
        return SingleValue{APInt(RetTy->getScalarSizeInBits(), Obj->size())};
    }
    bool IsMin = getInt(Args[1].getSingleValue())->getBoolValue();
    return SingleValue{IsMin ? APInt::getZero(RetTy->getScalarSizeInBits())
                             : APInt::getAllOnes(RetTy->getScalarSizeInBits())};
  }
  case Intrinsic::vector_insert: {
    auto &Vec = Args[0].getValueArray();
    auto &SubVec = Args[1].getValueArray();
    auto Idx = getInt(Args[2].getSingleValue());
    if (!Idx)
      ImmUBReporter(*this) << "vector_insert with poison index";
    uint32_t Offset = Idx->getZExtValue();
    if (Offset + SubVec.size() > Vec.size())
      return getPoison(RetTy);
    std::vector<AnyValue> Res;
    Res.reserve(Vec.size());
    for (uint32_t I = 0; I != Vec.size(); ++I) {
      if (I >= Offset && I < Offset + SubVec.size())
        Res.push_back(SubVec[I - Offset]);
      else
        Res.push_back(Vec[I]);
    }
    return std::move(Res);
  }
  case Intrinsic::vector_extract: {
    auto &Vec = Args[0].getValueArray();
    auto Idx = getInt(Args[1].getSingleValue());
    // TODO: scalable vector
    uint32_t DstSize = cast<FixedVectorType>(RetTy)->getNumElements();
    if (!Idx)
      ImmUBReporter(*this) << "vector_insert with poison index";
    uint32_t Offset = Idx->getZExtValue();
    if (Offset + DstSize > Vec.size())
      return getPoison(RetTy);
    return std::vector<AnyValue>{Vec.begin() + Offset,
                                 Vec.begin() + Offset + DstSize};
  }
  default:
    break;
  }
  errs() << "Unsupported intrinsic: " << II.getCalledFunction()->getName()
         << '\n';
  std::abort();
}
SingleValue UBAwareInterpreter::alloc(const APInt &AllocSize,
                                      bool ZeroInitialize) {
  auto MemObj = MemMgr.create("alloc", false, AllocSize.getZExtValue(), 8);
  AllocatedMems.insert(MemObj);
  if (ZeroInitialize)
    std::memset(MemObj->rawPointer(), 0, MemObj->size());
  return SingleValue{
      Pointer{MemObj, APInt::getZero(DL.getPointerSizeInBits()),
              ContextSensitivePointerInfo::getDefault(CurrentFrame)}};
}
AnyValue UBAwareInterpreter::callLibFunc(LibFunc Func, Function *FuncDecl,
                                         SmallVectorImpl<AnyValue> &Args) {
  switch (Func) {
  case LibFunc_puts: {
    auto *Ptr = getRawPtr(Args[0].getSingleValue());
    if (!Ptr)
      ImmUBReporter(*this) << "puts with null ptr";
    puts(Ptr);
    return none();
  }
  case LibFunc_printf: {
    auto Format = getRawPtr(Args[0].getSingleValue());
    if (!Format)
      ImmUBReporter(*this) << "invalid printf format";
    if (Args.size() == 1) {
      if (Option.Verbose)
        errs() << "\n    Printf: ";
      int Ret = puts(getRawPtr(Args[0].getSingleValue()));
      if (Option.Verbose)
        errs() << "  ";
      return SingleValue{APInt(32, Ret)};
    }
    if (Args.size() == 2) {
      auto Val = getInt(Args[1].getSingleValue());
      if (!Val.has_value())
        ImmUBReporter(*this) << "print a poison value";
      if (Option.Verbose)
        errs() << "\n    Printf: ";
      int Ret =
          printf(getRawPtr(Args[0].getSingleValue()), Val->getSExtValue());
      if (Option.Verbose)
        errs() << "  ";
      return SingleValue{APInt(32, Ret)};
    }
    break;
  }
  case LibFunc_malloc:
  case LibFunc_Znam:
  case LibFunc_Znwm: {
    auto Size = getInt(Args[0].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "malloc with poison size";
    return alloc(*Size, /*ZeroInitialize=*/false);
  }
  case LibFunc_calloc: {
    auto Num = getInt(Args[0].getSingleValue());
    if (!Num)
      ImmUBReporter(*this) << "malloc with poison count";
    auto Size = getInt(Args[1].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "malloc with poison size";
    return alloc(*Num * *Size, /*ZeroInitialize=*/true);
  }
  case LibFunc_free:
  case LibFunc_ZdaPv:
  case LibFunc_ZdlPv: {
    auto &Ptr = Args[0].getSingleValue();
    if (isPoison(Ptr))
      ImmUBReporter(*this) << "free with poison ptr";
    auto &PtrVal = std::get<Pointer>(Ptr);
    if (!PtrVal.Offset.isZero())
      ImmUBReporter(*this) << "free with invalid ptr";
    if (auto MO = PtrVal.Obj.lock())
      AllocatedMems.erase(MO);
    else
      ImmUBReporter(*this) << "free with invalid ptr";
    return none();
  }
  case LibFunc_exit: {
    auto Code = getInt(Args[0].getSingleValue());
    if (!Code)
      ImmUBReporter(*this) << "exit with poison code";
    std::exit(Code->getSExtValue());
  }
  default:
    break;
  }
  errs() << "Unsupported libcall: " << FuncDecl->getName() << '\n';
  std::abort();
}
AnyValue UBAwareInterpreter::call(Function *Func, CallBase *CB,
                                  SmallVectorImpl<AnyValue> &Args) {
  auto FnAttrs = Func->getAttributes();

  SmallVector<std::shared_ptr<MemObject>> ByValTempObjects;
  SmallVector<MemObject *> InitializeMOs;
  auto PostProcessArgs = [&] {
    if (CB) {
      bool HandleParamAttr =
          !isa<IntrinsicInst>(CB) || !Option.IgnoreParamAttrsOnIntrinsic;
      for (const auto &[Idx, Arg] : enumerate(CB->args())) {
        auto &ArgVal = Args[Idx];

        MemObject *InitializeMO = nullptr;
        uint64_t InitializeOffset = 0;
        if (CB->isByValArgument(Idx)) {
          if (isPoison(ArgVal.getSingleValue()))
            ImmUBReporter(*this)
                << "Pass poison to an pointer argument with byval";
          auto *Ty = CB->getParamByValType(Idx);
          auto TmpMO = MemMgr.create(getValueName(Arg.get()), true,
                                     DL.getTypeAllocSize(Ty),
                                     DL.getPrefTypeAlign(Ty).value());
          TmpMO->setLiveness(true);
          TmpMO->setStackObjectInfo(CurrentFrame);
          memcpy(TmpMO->rawPointer(), getRawPtr(ArgVal.getSingleValue()),
                 DL.getTypeStoreSize(Ty));
          ArgVal = SingleValue{
              Pointer{TmpMO, APInt::getZero(DL.getPointerSizeInBits()),
                      ContextSensitivePointerInfo::getDefault(CurrentFrame)}};
          InitializeMO = TmpMO.get();
          ByValTempObjects.push_back(std::move(TmpMO));
        }

        if (HandleParamAttr)
          postProcessAttr(*this, ArgVal, CB->getParamAttributes(Idx));
        // Convert pointer loc to argmem
        if (CB->getArgOperand(Idx)->getType()->isPtrOrPtrVectorTy()) {
          postProcess(ArgVal, [&](SingleValue &SV) {
            if (isPoison(SV))
              return;
            auto &Ptr = std::get<Pointer>(SV);
            Ptr.Info.pushLoc(CurrentFrame, IRMemLocation::ArgMem);
          });

          if (HandleParamAttr &&
              CB->paramHasAttr(Idx, Attribute::Initializes)) {
            auto Initializes =
                CB->getParamAttr(Idx, Attribute::Initializes).getInitializes();
            if (!Initializes.empty()) {
              if (!InitializeMO) {
                if (isPoison(ArgVal.getSingleValue()))
                  ImmUBReporter(*this)
                      << "Pass poison to an pointer argument with initializes";
                auto &Ptr = std::get<Pointer>(ArgVal.getSingleValue());
                auto MO = Ptr.Obj.lock();
                if (!MO)
                  ImmUBReporter(*this)
                      << "Pass dangling pointer to an pointer argument with "
                         "initializes";
                InitializeMO = MO.get();
                InitializeOffset = Ptr.Offset.getZExtValue();
              }

              PendingInitializeTask &Task =
                  InitializeMO->pushPendingInitializeTask(CurrentFrame);
              for (auto &R : Initializes) {
                uint64_t Lo = InitializeOffset + R.getLower().getZExtValue();
                uint64_t Hi = InitializeOffset + R.getUpper().getZExtValue();
                Task.Ranges.push_back({Lo, Hi});
              }

              InitializeMOs.push_back(InitializeMO);
            }
          }
        }
      }
    }

    for (const auto &[Idx, Param] : enumerate(Func->args()))
      postProcessAttr(*this, Args[Idx], FnAttrs.getParamAttrs(Idx));
  };

  auto ExitFunc = [&](Frame *OldFrame) {
    for (auto &MO : InitializeMOs)
      MO->popPendingInitializeTask(CurrentFrame);
    CurrentFrame = OldFrame;
  };

  auto ME = CB ? CB->getMemoryEffects() : MemoryEffects::unknown();
  if (Func->isIntrinsic()) {
    Frame CallFrame{Func, nullptr, TLI, CurrentFrame, ME};
    auto Scope =
        llvm::make_scope_exit([&, Frame = CurrentFrame] { ExitFunc(Frame); });
    CurrentFrame = &CallFrame;
    PostProcessArgs();
    return callIntrinsic(*cast<IntrinsicInst>(CB), Args);
  } else {
    LibFunc F;
    if (TLI.getLibFunc(*Func, F)) {
      Frame CallFrame{Func, nullptr, TLI, CurrentFrame, ME};
      auto Scope =
          llvm::make_scope_exit([&, Frame = CurrentFrame] { ExitFunc(Frame); });
      CurrentFrame = &CallFrame;
      PostProcessArgs();
      return callLibFunc(F, Func, Args);
    }
  }

  if (!Func->hasExactDefinition()) {
    errs() << "Do not how to handle " << *Func << '\n';
    std::exit(EXIT_FAILURE);
  }

  FunctionAnalysisCache *FAC = nullptr;
  if (Option.VerifyValueTracking) {
    auto CacheIter = AnalysisCache.find(Func);
    if (CacheIter == AnalysisCache.end())
      CacheIter = AnalysisCache.emplace(Func, *Func).first;
    FAC = &CacheIter->second;
  }

  Frame CallFrame{Func, FAC, TLI, CurrentFrame, ME};
  auto Scope =
      llvm::make_scope_exit([&, Frame = CurrentFrame] { ExitFunc(Frame); });
  CurrentFrame = &CallFrame;
  PostProcessArgs();
  for (auto &Param : Func->args())
    CallFrame.ValueMap[&Param] = std::move(Args[Param.getArgNo()]);

  if (Option.Verbose) {
    errs() << "\n\nEntering function " << Func->getName() << '\n';
  }
  CallFrame.BB = &Func->getEntryBlock();
  CallFrame.PC = CallFrame.BB->begin();
  while (!CallFrame.RetVal.has_value()) {
    if (Option.Verbose)
      errs() << *CallFrame.PC;
    if (EMIInfo.Enabled) {
      EMIInfo.ReachableBlocks.insert(CallFrame.BB);
      auto Iter = EMIInfo.InterestingUses.find(&*CallFrame.PC);
      if (Iter != EMIInfo.InterestingUses.end()) {
        for (auto Op : Iter->second) {
          auto Val = getInt(*Op);
          if (auto Iter = EMIInfo.UseIntInfo.find(Op);
              Iter != EMIInfo.UseIntInfo.end())
            Iter->second.update(Val);
          else
            EMIInfo.UseIntInfo.insert({Op, IntConstraintInfo(Val)});
        }
      }
    }
    if (++Steps >= Option.MaxSteps) {
      errs() << "Exceed maximum steps\n";
      std::exit(EXIT_FAILURE);
    }
    // TODO: verify at-use analysis result
    if (visit(*CallFrame.PC)) {
      if (Option.VerifyValueTracking) {
        auto Iter = CallFrame.ValueMap.find(&*CallFrame.PC);
        if (Iter != CallFrame.ValueMap.end())
          verifyAnalysis(Iter->first, Iter->second, &*CallFrame.PC);
      }
      ++CallFrame.PC;
    }
    if (Option.Verbose)
      errs() << '\n';
  }

  auto RetVal = std::move(*CallFrame.RetVal);
  if (!Func->getReturnType()->isVoidTy())
    postProcessAttr(*this, RetVal, Func->getAttributes().getRetAttrs());

  if (Option.Verbose) {
    errs() << "Exiting function " << Func->getName() << '\n';
  }

  return RetVal;
}

int32_t UBAwareInterpreter::runMain() {
  auto *Entry = M.getFunction("main");
  if (!Entry) {
    errs() << "Cannot find entry function `main`\n";
    return EXIT_FAILURE;
  }

  SmallVector<AnyValue> Args;
  if (Option.ReduceMode) {
    for (auto &Arg : Entry->args())
      Args.push_back(getZero(Arg.getType()));
  } else {
    Args.push_back(SingleValue{APInt::getZero(32)});
    Args.push_back(SingleValue{*NullPtr});
  }
  auto RetVal = call(Entry, nullptr, Args);
  if (Entry->getReturnType()->isVoidTy())
    return EXIT_SUCCESS;
  if (isPoison(RetVal.getSingleValue()))
    ImmUBReporter(*this) << "Return a poison value";
  if (Option.TrackVolatileMem)
    outs() << "[llubi] Volatile mem hash: " << VolatileMemHash << '\n';
  return std::get<APInt>(RetVal.getSingleValue()).getSExtValue();
}

void UBAwareInterpreter::mutate() {
  assert(EMIInfo.Enabled);
  auto Sample = [&] {
    return std::generate_canonical<double, std::numeric_limits<size_t>::max()>(
               Gen) < Option.EMIProb;
  };

  for (auto [K, V] : EMIInfo.MayBeUndef) {
    if (V)
      continue;
    if (Option.EnableEMIDebugging)
      errs() << *K << '\n';
    if (Sample()) {
      if (auto *Call = dyn_cast<CallBase>(K)) {
        Call->addRetAttr(Attribute::NoUndef);
      } else if (auto *Load = dyn_cast<LoadInst>(K)) {
        Load->setMetadata(llvm::LLVMContext::MD_noundef,
                          llvm::MDNode::get(Ctx, {}));
      } else
        llvm_unreachable("Unreachable");
    }
  }

  for (auto &F : M)
    for (auto &BB : F) {
      if (EMIInfo.ReachableBlocks.contains(&BB))
        continue;
      if (Option.EnableEMIDebugging)
        errs() << "Unreachable BB: " << F.getName() << ":" << getValueName(&BB)
               << '\n';
      if (Sample()) {
        IRBuilder<> Builder(&BB, BB.getFirstNonPHIOrDbgOrAlloca());
        Builder.CreateStore(Constant::getNullValue(Builder.getInt8Ty()),
                            PoisonValue::get(Builder.getPtrTy()));
      }
    }

  for (auto &[K, V] : EMIInfo.Range) {
    if (V.isEmptySet() || V.isFullSet() || V.isSingleElement())
      continue;

    if (Option.EnableEMIDebugging)
      errs() << "Range of " << *K << " : " << V << '\n';
    if (Sample()) {
      if (auto *Call = dyn_cast<CallBase>(K)) {
        Call->addRangeRetAttr(V);
      } else if (auto *Load = dyn_cast<LoadInst>(K)) {
        MDBuilder MDHelper(Load->getContext());
        auto *MDNode = MDHelper.createRange(V.getLower(), V.getUpper());
        Load->setMetadata(LLVMContext::MD_range, MDNode);
      } else
        llvm_unreachable("Unreachable");
    }
  }

  for (auto &[K, V] : EMIInfo.ICmpFlags) {
    if (V)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << "samesign " << *K << '\n';
    if (Sample())
      K->setSameSign();
  }

  for (auto &[K, V] : EMIInfo.NNegFlags) {
    if (V)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << "nneg " << *K << '\n';
    if (Sample())
      K->setNonNeg();
  }

  for (auto &[K, V] : EMIInfo.IsPoisonFlags) {
    if (V)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << "is_val_poison " << *K << '\n';
    if (Sample())
      K->setArgOperand(1, ConstantInt::getTrue(K->getContext()));
  }
  for (auto &[K, V] : EMIInfo.DisjointFlags) {
    if (V)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << "disjoint " << *K << '\n';
    if (Sample())
      K->setIsDisjoint(true);
  }

  for (auto &[K, V] : EMIInfo.NoWrapFlags) {
    if (V == 3)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << *K << " " << (V & 2 ? "" : "nsw") << (V & 1 ? "" : "nuw")
             << '\n';

    if (!(V & 2) && !K->hasNoSignedWrap() && Sample())
      K->setHasNoSignedWrap();
    if (!(V & 1) && !K->hasNoUnsignedWrap() && Sample())
      K->setHasNoUnsignedWrap();
  }
  for (auto &[K, V] : EMIInfo.TruncNoWrapFlags) {
    if (V == 3)
      continue;

    if (Option.EnableEMIDebugging)
      errs() << *K << " " << (V & 2 ? "" : "nsw") << (V & 1 ? "" : "nuw")
             << '\n';

    if (!(V & 2) && !K->hasNoSignedWrap() && Sample())
      K->setHasNoSignedWrap(true);
    if (!(V & 1) && !K->hasNoUnsignedWrap() && Sample())
      K->setHasNoUnsignedWrap(true);
  }
  for (auto &[K, V] : EMIInfo.UseIntInfo) {
    if (V.HasPoison)
      continue;
    if (Option.EnableEMIDebugging)
      errs() << *K << " at " << *K->getUser() << ' ' << V.Bits << ' ' << V.Range
             << '\n';
    IRBuilder<> Builder(cast<Instruction>(K->getUser()));
    Type *Ty = K->get()->getType();
    bool RangeIsValid = !V.Range.isEmptySet() && !V.Range.isFullSet() &&
                        !V.Range.isSingleElement();
    bool BitIsValid =
        !V.Bits.hasConflict() && !V.Bits.isUnknown() && !V.Bits.isConstant();
    if (!RangeIsValid && !BitIsValid)
      continue;

    if (!BitIsValid || std::uniform_int_distribution<int>(0, 1)(Gen)) {
      // Use Range
      ICmpInst::Predicate Pred;
      APInt RHS, Offset;
      V.Range.getEquivalentICmp(Pred, RHS, Offset);
      Builder.CreateAssumption(Builder.CreateICmp(
          Pred,
          Offset.isZero() ? *K
                          : Builder.CreateAdd(*K, ConstantInt::get(Ty, Offset)),
          ConstantInt::get(Ty, RHS)));
    } else {
      // Use Knownbits
      const auto Mask = V.Bits.One | V.Bits.Zero;
      Builder.CreateAssumption(Builder.CreateICmpEQ(
          Builder.CreateAnd(*K, ConstantInt::get(Ty, Mask)),
          ConstantInt::get(Ty, V.Bits.One)));
    }
  }
}
bool UBAwareInterpreter::simplify() {
  auto Sample = [&] {
    return std::generate_canonical<double, std::numeric_limits<size_t>::max()>(
               Gen) < Option.EMIProb;
  };

  bool Changed = false;
  for (auto &[K, V] : EMIInfo.UseIntInfo) {
    if (V.HasPoison)
      continue;
    if (!Sample())
      continue;
    if (auto *C = V.Range.getSingleElement()) {
      if (Option.EnableEMIDebugging)
        errs() << "Simplify " << *K << " to " << *C << '\n';
      K->set(ConstantInt::get(K->get()->getType(), *C));
      Changed = true;
    }
  }
  return Changed;
}
void UBAwareInterpreter::dumpStackTrace() {
  if (!Option.DumpStackTrace)
    return;
  errs() << "Stacktrace:\n";
  auto Frame = CurrentFrame;
  while (Frame) {
    if (Frame->BB) {
      auto &Inst = *Frame->PC;
      errs() << "  " << Inst << " at ";
      Inst.getFunction()->printAsOperand(errs(), /*PrintType=*/false);
      errs() << '\n';
    }
    Frame = Frame->LastFrame;
  }
}
FunctionAnalysisCache::FunctionAnalysisCache(Function &F) : DT(F), AC(F) {
  for (auto &BB : F) {
    if (auto *Branch = dyn_cast<BranchInst>(BB.getTerminator())) {
      if (Branch->isUnconditional())
        continue;
      DC.registerBranch(Branch);
    }
  }
}
KnownBits FunctionAnalysisCache::queryKnownBits(Value *V,
                                                const SimplifyQuery &SQ) {
  auto Iter = KnownBitsCache.find(V);
  if (Iter != KnownBitsCache.end())
    return Iter->second;
  return KnownBitsCache[V] = computeKnownBits(V, /*Depth=*/0, SQ);
}
bool FunctionAnalysisCache::queryNonZero(Value *V, const SimplifyQuery &SQ) {
  auto Iter = NonZeroCache.find(V);
  if (Iter != NonZeroCache.end())
    return Iter->second;
  return NonZeroCache[V] = isKnownNonZero(V, SQ);
}
SimplifyQuery UBAwareInterpreter::getSQ(const Instruction *CxtI) const {
  return SimplifyQuery{DL,
                       &CurrentFrame->TLI,
                       &CurrentFrame->Cache->DT,
                       &CurrentFrame->Cache->AC,
                       CxtI,
                       /*UseInstrInfo=*/true,
                       /*CanUseUndef=*/true,
                       &CurrentFrame->Cache->DC};
}
Frame::Frame(Function *Func, FunctionAnalysisCache *Cache,
             TargetLibraryInfoImpl &TLI, Frame *LastFrame, MemoryEffects ME)
    : BB(nullptr), PC(), Cache(Cache), TLI(TLI, Func), LastFrame(LastFrame),
      MemEffects(ME) {}
void UBAwareInterpreter::verifyAnalysis(Value *V, const AnyValue &RV,
                                        const Instruction *CxtI) {
  auto *Ty = V->getType();
  SimplifyQuery SQ = getSQ(CxtI);

  if (Ty->isIntOrIntVectorTy() && Ty->getScalarSizeInBits() > 1) {
    KnownBits Known(Ty->getScalarSizeInBits());
    Known.Zero.setAllBits();
    Known.One.setAllBits();
    unsigned MinSignBits = Known.getBitWidth();
    foreachScalar(RV, [&](const SingleValue &SV) {
      Known.intersectWith(KnownBits::makeConstant(std::get<APInt>(SV)));
      MinSignBits = std::min(MinSignBits, std::get<APInt>(SV).getNumSignBits());
    });

    auto KnownAnalysis = CurrentFrame->Cache->queryKnownBits(V, SQ);
    if (!KnownAnalysis.Zero.isSubsetOf(Known.Zero) ||
        !KnownAnalysis.One.isSubsetOf(Known.One))
      ImmUBReporter(*this) << "knownbits of " << *V
                           << " is incorrect: analysis result = "
                           << KnownAnalysis << ", but sample result = " << Known
                           << '\n';

    if (!KnownAnalysis.isNonZero()) {
      if (anyOfScalar(RV,
                      [](const SingleValue &SV) {
                        return std::get<APInt>(SV).isZero();
                      }) &&
          CurrentFrame->Cache->queryNonZero(V, SQ))
        ImmUBReporter(*this) << *V << " may be zero\n";
    }
    if (MinSignBits != 1) {
      unsigned SignBits =
          ComputeNumSignBits(V, SQ.DL, /*Depth=*/0, SQ.AC, SQ.CxtI, SQ.DT);
      if (SignBits > MinSignBits)
        ImmUBReporter(*this)
            << "signbits of " << *V
            << " is incorrect: ComputeNumSignBits gives " << SignBits
            << ", but sample result = " << MinSignBits << '\n';
    }
  } else if (Ty->isPtrOrPtrVectorTy()) {
    if (anyOfScalar(RV,
                    [](const SingleValue &SV) {
                      return std::get<Pointer>(SV).Address.isZero();
                    }) &&
        CurrentFrame->Cache->queryNonZero(V, SQ))
      ImmUBReporter(*this) << *V << " may be null\n";
  }
  // TODO: known fpclass
}
