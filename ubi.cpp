// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include "ubi.h"
#include <llvm/Analysis/AssumeBundleQueries.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/InlineAsm.h>
#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <utility>
#include <variant>
#include <vector>

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
  for (size_t I = Offset; I != Offset + Size; ++I) {
    Metadata[I].IsPoison = IsPoison;
    Metadata[I].Readable = Metadata[I].Writable = Metadata[I].Comparable =
        Metadata[I].ComparableWithNull = IsPoison;
  }
}
void MemObject::verifyMemAccess(size_t Offset, size_t AccessSize,
                                size_t Alignment, bool IsStore) {
  if (!IsAlive)
    ImmUBReporter(Manager.Interpreter) << "Accessing dead object " << *this;
  if (((Address.getZExtValue() + Offset) & (Alignment - 1)) != 0)
    ImmUBReporter(Manager.Interpreter) << "Unaligned mem op";
  if (Offset + AccessSize > Data.size())
    ImmUBReporter(Manager.Interpreter)
        << "Out of bound mem op, bound = " << Data.size()
        << ", access range = [" << Offset << ", " << Offset + AccessSize << ')';
}
void MemObject::store(size_t Offset, const APInt &C) {
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = alignTo(C.getBitWidth(), 8) / 8;
  uint32_t WriteCnt = 0;
  std::byte *const WritePos = Data.data() + Offset;
  for (uint32_t I = 0; I != C.getNumWords(); ++I) {
    auto Word = C.getRawData()[I];
    if (WriteCnt + Scale <= Size) {
      for (uint32_t J = 0; J != Scale; ++J)
        Metadata[Offset + WriteCnt + J].IsPoison = false;
      memcpy(&WritePos[WriteCnt], &Word, sizeof(Word));
      WriteCnt += Scale;
      if (WriteCnt == Size)
        return;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        WritePos[WriteCnt] = static_cast<std::byte>(Word & 255);
        Metadata[Offset + WriteCnt].IsPoison = false;
        Word >>= 8;
        if (++WriteCnt == Size)
          return;
      }
    }
  }
}
std::optional<APInt> MemObject::load(size_t Offset, size_t Bits,
                                     bool FreezeBytes) const {
  APInt Res = APInt::getZero(alignTo(Bits, 8));
  constexpr uint32_t Scale = sizeof(APInt::WordType);
  const size_t Size = Res.getBitWidth() / 8;
  uint32_t ReadCnt = 0;
  const std::byte *const ReadPos = Data.data() + Offset;
  bool AllPoison = true;
  for (uint32_t I = 0; I != Res.getNumWords(); ++I) {
    auto &Word = const_cast<APInt::WordType &>(Res.getRawData()[I]);
    if (ReadCnt + Scale <= Size) {
      for (uint32_t J = 0; J != Scale; ++J) {
        if (Metadata[Offset + ReadCnt + J].IsPoison) {
          if (!FreezeBytes)
            return std::nullopt;
        } else
          AllPoison = false;
      }
      memcpy(&Word, &ReadPos[ReadCnt], sizeof(Word));
      ReadCnt += Scale;
      if (ReadCnt == Size)
        break;
    } else {
      for (auto J = 0; J != Scale; ++J) {
        if (Metadata[Offset + ReadCnt].IsPoison) {
          if (!FreezeBytes)
            return std::nullopt;
        } else
          AllPoison = false;
        Word |= static_cast<APInt::WordType>(ReadPos[ReadCnt]) << (J * 8);
        if (++ReadCnt == Size)
          break;
      }
      if (ReadCnt == Size)
        break;
    }
  }
  if (AllPoison)
    return std::nullopt;
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

ContextSensitivePointerInfo
ContextSensitivePointerInfo::getDefault(Frame *FrameCtx) {
  return ContextSensitivePointerInfo{
      nullptr,
      FrameCtx,
      true,
      true,
      true,
      true,
      static_cast<uint32_t>(IRMemLocation::Other),
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
          Pointer{MO->shared_from_this(),
                  static_cast<uint32_t>((Addr - MO->address()).getZExtValue()),
                  ContextSensitivePointerInfo::getDefault(nullptr)}};
    }
  }

  return SingleValue{Pointer{std::weak_ptr<MemObject>{}, 0, Addr, 0,
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
    if (Ptr->Offset != 0)
      Out << " + " << Ptr->Offset;
    Out << "] " << Ptr->Info.CI;
    if (Ptr->Info.Readable || Ptr->Info.Writable)
      Out << ' ' << (Ptr->Info.Readable ? "R" : "")
          << (Ptr->Info.Writable ? "W" : "");
    switch (Ptr->Info.getLoc()) {
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
  return V;
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
  if (Ptr.Offset + Size > Ptr.Bound) {
    ImmUBReporter(Interpreter)
        << "dereferenceable" << (OrNull ? "_or_null" : "") << "(" << Size
        << ") out of bound: " << V;
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
  return V;
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
      Ptr.Info.pushReadWrite(FrameCtx, Ptr.Info.Readable, false);
    });
  }
  if (AS.hasAttribute(Attribute::WriteOnly)) {
    postProcess(V, [FrameCtx](SingleValue &SV) {
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      Ptr.Info.pushReadWrite(FrameCtx, false, Ptr.Info.Writable);
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
uint32_t UBAwareInterpreter::getFixedSize(TypeSize Size) const {
  if (Size.isScalable())
    return Size.getKnownMinValue() * Option.VScale;
  return Size.getFixedValue();
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
    return AnyValue{Pointer{Iter->second, 0, std::move(PointerInfo)}};
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
    case Instruction::IntToPtr: {
      auto V = convertFromConstant(cast<Constant>(CE->getOperand(0)));
      assert(V.isSingleValue());
      if (isPoison(V.getSingleValue()))
        return poison();
      return SingleValue{
          MemMgr.lookupPointer(std::get<APInt>(V.getSingleValue()))};
    }
    default:
      break;
    }
  }
  if (auto *BA = dyn_cast<BlockAddress>(V))
    return SingleValue{
        Pointer{BlockTargets.at(BA->getBasicBlock()), 0,
                ContextSensitivePointerInfo::getDefault(nullptr)}};
  errs() << "Unexpected constant " << *V << '\n';
  std::abort();
}
void UBAwareInterpreter::store(MemObject &MO, uint32_t Offset,
                               const AnyValue &V, Type *Ty) {
  if (Ty->isIntegerTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (Option.StorePoisonIsImmUB && CurrentFrame)
        ImmUBReporter(*this) << "store poison value is UB";
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    MO.store(Offset, std::get<APInt>(SV));
  } else if (Ty->isFloatingPointTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (Option.StorePoisonIsImmUB && CurrentFrame)
        ImmUBReporter(*this) << "store poison value is UB";
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    auto &C = std::get<APFloat>(SV);
    MO.store(Offset, C.bitcastToAPInt());
  } else if (Ty->isPointerTy()) {
    auto &SV = V.getSingleValue();
    if (isPoison(SV)) {
      if (Option.StorePoisonIsImmUB && CurrentFrame)
        ImmUBReporter(*this) << "store poison value is UB";
      if (!Option.StorePoisonIsNoop)
        MO.markPoison(Offset, DL.getTypeStoreSize(Ty).getFixedValue(), true);
      return;
    }
    auto &Ptr = std::get<Pointer>(SV);
    MO.store(Offset, Ptr.Address);
    auto &PtrPermission = MO.getMetadata(Offset);
    PtrPermission.Comparable =
        Ptr.Info.Comparable &&
        (Ptr.Info.CI.getOtherComponents() & CaptureComponents::Address) ==
            CaptureComponents::Address;
    PtrPermission.ComparableWithNull =
        Ptr.Info.ComparableWithNull &&
        (Ptr.Info.CI.getOtherComponents() & CaptureComponents::AddressIsNull) ==
            CaptureComponents::AddressIsNull;
    PtrPermission.Readable =
        Ptr.Info.Readable && ((Ptr.Info.CI.getOtherComponents() &
                               CaptureComponents::ReadProvenance) ==
                              CaptureComponents::ReadProvenance);
    PtrPermission.Writable =
        Ptr.Info.Writable &&
        ((Ptr.Info.CI.getOtherComponents() & CaptureComponents::Provenance) ==
         CaptureComponents::Provenance);
  } else if (Ty->isVectorTy()) {
    Type *EltTy = Ty->getScalarType();
    if (EltTy->isIntegerTy() && EltTy->getIntegerBitWidth() % 8 != 0) {
      // Approximate the behavior with <n x i8> vector.
      uint32_t Len = getVectorLength(cast<VectorType>(Ty));
      uint32_t NumBits = Len * EltTy->getIntegerBitWidth();
      if (NumBits % 8 != 0)
        ImmUBReporter(*this) << "vector element type is not byte-sized";
      uint32_t NumBytes = NumBits / 8;
      auto *NewVTy = VectorType::get(IntegerType::getInt8Ty(Ty->getContext()),
                                     NumBytes, /*Scalable=*/false);
      // FIXME: poison elements may infect the whole byte.
      auto Converted =
          bitcast(V, VectorType::get(EltTy, Len, /*Scalable=*/false), NewVTy);
      store(MO, Offset, Converted, NewVTy);
    }
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
    auto Val = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue(),
                       Option.FreezeBytes);
    if (!Val.has_value())
      return poison();
    return SingleValue{Val->trunc(Ty->getScalarSizeInBits())};
  } else if (Ty->isFloatingPointTy()) {
    auto Val = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue(),
                       Option.FreezeBytes);
    if (!Val.has_value())
      return poison();
    return SingleValue{APFloat(Ty->getFltSemantics(), *Val)};
  } else if (Ty->isPointerTy()) {
    auto Addr = MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue(),
                        Option.FreezeBytes);
    if (!Addr.has_value())
      return poison();
    auto Ptr = MemMgr.lookupPointer(*Addr);
    if (isPoison(Ptr))
      return poison();
    // FIXME: Capture info should not be applied before the current function
    // returns.
    //
    // auto &Metadata = MO.getMetadata(Offset);
    // auto &PtrRef = std::get<Pointer>(Ptr);
    // PtrRef.Info.push(CurrentFrame);
    // PtrRef.Info.Readable = Metadata.Readable;
    // PtrRef.Info.Writable = Metadata.Writable;
    // PtrRef.Info.Comparable = Metadata.Comparable;
    // PtrRef.Info.ComparableWithNull = Metadata.ComparableWithNull;
    return std::move(Ptr);
  } else if (auto *StructTy = dyn_cast<StructType>(Ty)) {
    auto *Layout = DL.getStructLayout(StructTy);
    std::vector<AnyValue> Res;
    Res.reserve(StructTy->getNumElements());
    for (uint32_t I = 0, E = StructTy->getStructNumElements(); I != E; ++I) {
      auto NewOffset = Offset + Layout->getElementOffset(I).getFixedValue();
      Res.push_back(load(MO, NewOffset, StructTy->getStructElementType(I)));
    }
    return std::move(Res);
  } else if (auto *ArrTy = dyn_cast<ArrayType>(Ty)) {
    Type *EltTy = ArrTy->getArrayElementType();
    std::vector<AnyValue> Res;
    Res.reserve(ArrTy->getArrayNumElements());
    auto Step = DL.getTypeStoreSize(EltTy);
    for (uint32_t I = 0, E = ArrTy->getArrayNumElements(); I != E; ++I) {
      Res.push_back(load(MO, Offset, EltTy));
      Offset += Step;
    }
    return std::move(Res);
  } else if (auto *VTy = dyn_cast<VectorType>(Ty)) {
    uint32_t Len = getVectorLength(VTy);
    Type *EltTy = VTy->getElementType();
    if (EltTy->isIntegerTy() && EltTy->getIntegerBitWidth() % 8 != 0) {
      // Approximate the behavior with <n x i8> vector.
      uint32_t NumBits = Len * EltTy->getIntegerBitWidth();
      if (NumBits % 8 != 0)
        ImmUBReporter(*this) << "vector element type is not byte-sized";
      uint32_t NumBytes = NumBits / 8;
      auto *NewVTy = VectorType::get(IntegerType::getInt8Ty(VTy->getContext()),
                                     NumBytes, /*Scalable=*/false);
      auto LoadedValue = load(MO, Offset, NewVTy);
      return bitcast(LoadedValue, NewVTy,
                     VectorType::get(EltTy, Len, /*Scalable=*/false));
    }
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
          (CurrentFrame->MemEffects.getModRef(PV->Info.getLoc()) &
           ModRefInfo::Mod) != ModRefInfo::Mod) {
        // FIXME: If read is set, check  the case where the location is read
        // from and then the same value is written back.
        ImmUBReporter(*this) << "store in a writenone context";
      }
      auto Size = getFixedSize(DL.getTypeStoreSize(Ty));
      if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
        volatileMemOpTy(Ty, /*IsStore=*/true);
      MO->verifyMemAccess(PV->Offset, Size, Alignment, true);
      return store(*MO, PV->Offset, V, Ty);
    }
    ImmUBReporter(*this) << "store to invalid pointer";
  }
  ImmUBReporter(*this) << "store to poison pointer";
}
AnyValue UBAwareInterpreter::load(const AnyValue &P, uint32_t Alignment,
                                  Type *Ty, bool IsVolatile) {
  if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
    if (!PV->Info.Readable) {
      // However, the function may still internally read the location after
      // writing it, as this is not observable. Reading the location prior to
      // writing it results in a poison value.
      // We do not model the second behavior for now.
      if (IsVolatile || !PV->Info.Writable)
        ImmUBReporter(*this) << "load from a non-readable pointer " << *PV;
    }
    if (auto MO = PV->Obj.lock()) {
      if ((!MO->isConstant() && !MO->isStackObject(CurrentFrame)) &&
          (CurrentFrame->MemEffects.getModRef(PV->Info.getLoc()) &
           ModRefInfo::Ref) != ModRefInfo::Ref) {
        if (!IsVolatile ||
            (CurrentFrame->MemEffects.getModRef(PV->Info.getLoc()) &
             ModRefInfo::Mod) != ModRefInfo::Mod)
          ImmUBReporter(*this) << "load in a readnone context " << *MO;
      }
      auto Size = getFixedSize(DL.getTypeStoreSize(Ty));
      if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
        volatileMemOpTy(Ty, /*IsStore=*/false);
      MO->verifyMemAccess(PV->Offset, Size, Alignment, false);
      return load(*MO, PV->Offset, Ty);
    }
    ImmUBReporter(*this) << "load from invalid pointer " << *PV;
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
  auto NewAddr = addNoWrap(Ptr.Address, Offset, HasNSW, HasNUW);
  if (!NewAddr)
    return poison();
  int64_t NewOffset = static_cast<uint64_t>(Ptr.Offset) + Offset.getSExtValue();
  if (NewOffset < 0 || NewOffset > static_cast<int64_t>(Ptr.Bound)) {
    if (Flags.isInBounds())
      return poison();
    return MemMgr.lookupPointer(*NewAddr);
  }

  return Pointer{Ptr.Obj, static_cast<uint32_t>(NewOffset), *NewAddr, Ptr.Bound,
                 Ptr.Info};
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
  NullPtr = Pointer{NullPtrStorage, 0,
                    ContextSensitivePointerInfo::getDefault(nullptr)};
  assert(NullPtr->Address.isZero());
  if (Option.RustMode)
    patchRustLibFunc();
  for (auto &GV : M.globals()) {
    if (!GV.hasExactDefinition()) {
      if (Option.RustMode) {
        if (GV.getName() == "__rust_no_alloc_shim_is_unstable") {
          GlobalValues.insert(
              {&GV, MemMgr.create(GV.getName().str(), false, 1, 1)});
        }
      }
      continue;
    }
    GlobalValues.insert(
        {&GV, MemMgr.create(GV.getName().str(), false,
                            DL.getTypeAllocSize(GV.getValueType()),
                            DL.getPreferredAlign(&GV).value())});
  }
  for (auto &F : M) {
    GlobalValues.insert({&F, MemMgr.create(F.getName().str(), false, 0, 16)});
    ValidCallees.insert({GlobalValues.at(&F)->address().getZExtValue(), &F});
    for (auto &BB : F) {
      if (BB.isEntryBlock())
        continue;
      BlockTargets.insert(
          {&BB, MemMgr.create(F.getName().str() + ":" + getValueName(&BB), true,
                              0, 16)});
      ValidBlockTargets.insert(
          {GlobalValues.at(&F)->address().getZExtValue(), &BB});
    }
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
  if (Option.VerifySCEV) {
    auto &LI = CurrentFrame->Cache->LI;
    auto *L1 = LI.getLoopFor(To);

    if (L1 && L1->getHeader() == To) {
      auto *L0 = LI.getLoopFor(From);
      if (L0 == L1 || (L0 && L1->contains(L0)))
        ++CurrentFrame->Cache->BECount[L1];
      else
        CurrentFrame->Cache->BECount[L1] = 0;
    }
  }

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
static AnyValue None{std::monostate{}};
const AnyValue &none() { return None; }
const AnyValue &UBAwareInterpreter::getValue(Value *V) {
  if (auto *C = dyn_cast<Constant>(V)) {
    auto Iter = ConstantCache.find(C);
    if (Iter == ConstantCache.end())
      Iter =
          ConstantCache
              .insert({C, std::make_unique<AnyValue>(convertFromConstant(C))})
              .first;
    return *Iter->second;
  }
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
    return MO->rawPointer() + Ptr.Offset;
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
  if (!IsStore && !Ptr.Info.Readable) {
    // However, the function may still internally read the location after
    // writing it, as this is not observable. Reading the location prior to
    // writing it results in a poison value.
    // We do not model the second behavior for now.
    if (IsVolatile || !Ptr.Info.Writable)
      ImmUBReporter(*this) << "load from a non-readable pointer " << Ptr;
  }
  if (auto MO = Ptr.Obj.lock()) {
    if (IsStore && !MO->isStackObject(CurrentFrame) &&
        (CurrentFrame->MemEffects.getModRef(Ptr.Info.getLoc()) &
         ModRefInfo::Mod) != ModRefInfo::Mod)
      ImmUBReporter(*this) << "store in a writenone context";
    if (!IsStore && (!MO->isConstant() && !MO->isStackObject(CurrentFrame)) &&
        (CurrentFrame->MemEffects.getModRef(Ptr.Info.getLoc()) &
         ModRefInfo::Ref) != ModRefInfo::Ref) {
      if (IsVolatile || (CurrentFrame->MemEffects.getModRef(Ptr.Info.getLoc()) &
                         ModRefInfo::Mod) != ModRefInfo::Mod)
        ImmUBReporter(*this) << "load in a readnone context";
    }
    if (Option.TrackVolatileMem && IsVolatile && MO->isGlobal())
      volatileMemOp(Size, IsStore);
    MO->verifyMemAccess(Ptr.Offset, Size, Alignment, IsStore);
    if (IsStore) {
      // FIXME: Approximation: assume all bytes to write are non-poison.
      MO->markPoison(Ptr.Offset, Size, false);
    }
    return MO->rawPointer() + Ptr.Offset;
  }
  ImmUBReporter(*this) << "dangling pointer";
  llvm_unreachable("Unreachable code");
}
DenormalMode UBAwareInterpreter::getCurrentDenormalMode(Type *Ty) {
  if (Ty->isFPOrFPVectorTy() && CurrentFrame) {
    return CurrentFrame->Func->getDenormalMode(
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
  Pointer Ptr{Obj, 0, ContextSensitivePointerInfo::getDefault(CurrentFrame)};
  Obj->setLiveness(true);
  Obj->setStackObjectInfo(CurrentFrame);
  if (!Option.IgnoreExplicitLifetimeMarker) {
    for (auto *U : AI.users()) {
      if (isa<LifetimeIntrinsic>(U)) {
        // The returned object is initially dead if it is explicitly used by
        // lifetime intrinsics.
        Obj->setLiveness(false);
        break;
      }
    }
  }
  if (Option.FillUninitializedMemWithPoison)
    Obj->markPoison(0, AllocSize, true);
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
  if (auto *ArrTy = dyn_cast<ArrayType>(Ty)) {
    uint32_t Len = ArrTy->getArrayNumElements();
    auto *EltTy = ArrTy->getArrayElementType();
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I)
      Res.push_back(freezeValue(Val.getValueArray().at(I), EltTy));
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
      return V;
    };
    AnyValue Res = GetSplat(getValue(GEP.getPointerOperand()));
    for (auto &[K, V] : VarOffsets) {
      auto KV = GetSplat(getValue(K));
      for (uint32_t I = 0; I != Len; ++I) {
        auto &ResVal = Res.getSingleValueAt(I);
        if (auto Idx = getInt(KV.getSingleValueAt(I))) {
          auto &IdxVal = *Idx;
          if (CanonicalizeBitWidth(IdxVal)) {
            if (auto Off = mulNoWrap(IdxVal, V, Flags.hasNoUnsignedSignedWrap(),
                                     Flags.hasNoUnsignedWrap())) {
              ResVal = computeGEP(ResVal, *Off, Flags);
              continue;
            }
          }
        }
        ResVal = poison();
      }
    }
    for (uint32_t I = 0; I != Len; ++I) {
      auto &ResVal = Res.getSingleValueAt(I);
      ResVal = computeGEP(ResVal, Offset, Flags);
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
  auto LHS = getValue(SVI.getOperand(0));
  uint32_t Size = cast<VectorType>(SVI.getOperand(0)->getType())
                      ->getElementCount()
                      .getKnownMinValue();
  bool RHSIsPoison = isa<PoisonValue>(SVI.getOperand(1));
  auto RHS = RHSIsPoison ? AnyValue{} : getValue(SVI.getOperand(1));
  std::vector<AnyValue> PickedValues;
  uint32_t DstLen = getVectorLength(SVI.getType());
  PickedValues.reserve(DstLen);
  uint32_t Stride = SVI.getShuffleMask().size();
  for (uint32_t Off = 0; Off != DstLen; Off += Stride) {
    for (auto Idx : SVI.getShuffleMask()) {
      if (Idx == PoisonMaskElem)
        PickedValues.push_back(poison());
      else if (Idx < static_cast<int32_t>(Size))
        PickedValues.push_back(LHS.getSingleValueAt(Idx));
      else if (RHSIsPoison)
        PickedValues.push_back(poison());
      else
        PickedValues.push_back(RHS.getSingleValueAt(Idx - Size));
    }
  }
  return addValue(SVI, std::move(PickedValues));
}
bool UBAwareInterpreter::visitStoreInst(StoreInst &SI) {
  store(getValue(SI.getPointerOperand()), SI.getAlign().value(),
        getValue(SI.getValueOperand()), SI.getValueOperand()->getType(),
        SI.isVolatile());
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
                                   const APInt &Src) const {
  Dst.insertBits(Src, Offset);
  Offset += Src.getBitWidth();
}
void UBAwareInterpreter::toBits(APInt &Bits, APInt &PoisonBits,
                                uint32_t &Offset, const AnyValue &Val,
                                Type *Ty) const {
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
    return Ptr.Address;
  });
}
APInt UBAwareInterpreter::readBits(const APInt &Src, uint32_t &Offset,
                                   uint32_t Width) const {
  auto Res = Src.extractBits(Width, Offset);
  Offset += Width;
  return Res;
}
AnyValue UBAwareInterpreter::fromBits(const APInt &Bits,
                                      const APInt &PoisonBits, uint32_t &Offset,
                                      Type *Ty) const {
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
AnyValue UBAwareInterpreter::bitcast(const AnyValue &V, Type *SrcTy,
                                     Type *DstTy) const {
  APInt Bits = APInt::getZero(DL.getTypeSizeInBits(DstTy).getFixedValue());
  APInt PoisonBits = Bits;
  uint32_t Offset = 0;
  toBits(Bits, PoisonBits, Offset, V, SrcTy);
  Offset = 0;
  return fromBits(Bits, PoisonBits, Offset, DstTy);
}
bool UBAwareInterpreter::visitBitCastInst(BitCastInst &BCI) {
  return addValue(BCI, bitcast(getValue(BCI.getOperand(0)),
                               BCI.getOperand(0)->getType(), BCI.getType()));
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
  auto PadVPResult = [](std::vector<AnyValue> &Res, uint32_t Len) {
    Res.resize(Len, poison());
  };

  switch (IID) {
  case Intrinsic::ssa_copy:
  case Intrinsic::expect:
  case Intrinsic::expect_with_probability:
    return Args[0];
  case Intrinsic::donothing:
    return none();
  case Intrinsic::vscale:
    // TODO: check vscale_range
    return SingleValue{APInt(RetTy->getScalarSizeInBits(), Option.VScale)};
  case Intrinsic::lifetime_start:
  case Intrinsic::lifetime_end: {
    if (Option.IgnoreExplicitLifetimeMarker)
      return none();

    auto Size = getInt(Args[0].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "call lifetime intrinsic with poison size";
    auto &Ptr = Args[1].getSingleValue();
    if (auto *P = std::get_if<Pointer>(&Ptr)) {
      uint64_t PtrTag = P->Address.getZExtValue();
      if (Option.EnforceStackOrderLifetimeMarker) {
        auto &LifetimeStack = CurrentFrame->LastFrame->LifetimeStack;
        if (IID == Intrinsic::lifetime_start)
          LifetimeStack.push(PtrTag);
        else {
          if (LifetimeStack.empty() || LifetimeStack.top() != PtrTag)
            ImmUBReporter(*this)
                << "call lifetime end with unmatched lifetime start";
          else
            LifetimeStack.pop();
        }
      }

      if (auto MO = P->Obj.lock()) {
        // Do not reduce the pointer.
        if (Option.ReduceMode && P->Address.isZero())
          ImmUBReporter(*this) << "call lifetime intrinsic with null";
        if (!Option.ReduceMode && Size->isAllOnes())
          Size = APInt(Size->getBitWidth(), MO->size());
        // FIXME: What is the meaning of size?
        if (MO->isStackObject(CurrentFrame->LastFrame) && P->Offset == 0) {
          // Do not reduce the size.
          if (Option.ReduceMode && MO->size() != Size)
            ImmUBReporter(*this) << "call lifetime intrinsic with wrong size";
          if (MO->isAlive() || IID == Intrinsic::lifetime_start)
            MO->markPoison(0, MO->size(),
                           Option.FillUninitializedMemWithPoison ||
                               IID != Intrinsic::lifetime_start);
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
    auto Dst = Args[0].getSingleValue();
    auto Src = Args[1].getSingleValue();
    uint32_t DstIndexWidth =
        DL.getIndexTypeSizeInBits(II.getArgOperand(0)->getType());
    uint32_t SrcIndexWidth =
        DL.getIndexTypeSizeInBits(II.getArgOperand(1)->getType());
    Type *ByteTy = Type::getInt8Ty(II.getContext());
    auto ShouldCopyBackward = [](const SingleValue &A, const SingleValue &B) {
      if (isPoison(A) || isPoison(B))
        return false;
      return std::get<Pointer>(A).Address.ult(std::get<Pointer>(B).Address);
    };
    if (IID == Intrinsic::memmove && ShouldCopyBackward(Src, Dst)) {
      for (size_t I = 0; I != CopySize; ++I) {
        size_t Offset = CopySize - 1 - I;
        auto DstPtr =
            computeGEP(Dst, APInt(DstIndexWidth, Offset, false, true), {});
        auto SrcPtr =
            computeGEP(Src, APInt(SrcIndexWidth, Offset, false, true), {});
        auto Byte = load(SrcPtr, 1, ByteTy, IsVolatile);
        store(DstPtr, 1, Byte, ByteTy, IsVolatile);
      }
    } else {
      for (size_t I = 0; I != CopySize; ++I) {
        auto DstPtr = computeGEP(Dst, APInt(DstIndexWidth, I, false, true), {});
        auto SrcPtr = computeGEP(Src, APInt(SrcIndexWidth, I, false, true), {});
        auto Byte = load(SrcPtr, 1, ByteTy, IsVolatile);
        store(DstPtr, 1, Byte, ByteTy, IsVolatile);
      }
    }
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
                        [&](const APFloat &X, const APFloat &Y,
                            const APFloat &Z) -> std::optional<APFloat> {
                          if (Option.FuseFMulAdd) {
                            auto Res = X;
                            Res.fusedMultiplyAdd(
                                Y, Z, RoundingMode::NearestTiesToEven);
                            return Res;
                          }
                          return X * Y + Z;
                        });
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
  case Intrinsic::vector_reverse: {
    auto Vec = Args[0].getValueArray();
    std::reverse(Vec.begin(), Vec.end());
    return std::move(Vec);
  }
  case Intrinsic::fptosi_sat:
  case Intrinsic::fptoui_sat: {
    auto BitWidth = RetTy->getScalarSizeInBits();
    return visitUnOp(RetTy, Args[0], [&](const SingleValue &C) -> SingleValue {
      if (isPoison(C))
        return poison();
      auto &CFP = std::get<APFloat>(C);
      APSInt V(BitWidth, IID == Intrinsic::fptoui_sat);
      bool IsExact;
      CFP.convertToInteger(V, APFloat::rmTowardZero, &IsExact);
      (void)(IsExact);
      return V;
    });
  }
  case Intrinsic::stepvector: {
    std::vector<AnyValue> Res;
    uint32_t Len = getVectorLength(cast<VectorType>(RetTy));
    uint32_t BitWidth = RetTy->getScalarSizeInBits();
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I)
      Res.push_back(SingleValue{APInt(BitWidth, I, false, true)});
    return std::move(Res);
  }
  case Intrinsic::get_active_lane_mask: {
    auto Base = getInt(Args[0].getSingleValue());
    if (!Base)
      return getPoison(RetTy);
    auto N = getInt(Args[1].getSingleValue());
    if (!N || N->isZero())
      return getPoison(RetTy);
    std::vector<AnyValue> Res;
    uint32_t Len = getVectorLength(cast<VectorType>(RetTy));
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      bool Val = (*Base + I).ult(*N);
      Res.push_back(boolean(Val));
    }
    return std::move(Res);
  }
  case Intrinsic::masked_scatter: {
    auto &Values = Args[0].getValueArray();
    auto &Ptrs = Args[1].getValueArray();
    auto Align = getInt(Args[2].getSingleValue())->getZExtValue();
    auto &Mask = Args[3].getValueArray();
    auto *ValTy = cast<VectorType>(II.getArgOperand(0)->getType());
    auto *AccessTy = ValTy->getScalarType();
    uint32_t Len = getVectorLength(ValTy);
    for (uint32_t I = 0; I != Len; ++I) {
      auto &Value = Values[I];
      auto &Ptr = Ptrs[I];
      auto MaskVal = getInt(Mask[I].getSingleValue());
      if (getBooleanNonPoison(Mask[I].getSingleValue()))
        store(Ptr, Align, Value, AccessTy, false);
    }
    return none();
  }
  case Intrinsic::masked_gather: {
    auto &Ptrs = Args[0].getValueArray();
    auto Align = getInt(Args[1].getSingleValue())->getZExtValue();
    auto &Mask = Args[2].getValueArray();
    auto &PassThru = Args[3].getValueArray();
    auto *ValTy = cast<VectorType>(RetTy);
    auto *AccessTy = ValTy->getScalarType();
    uint32_t Len = getVectorLength(ValTy);
    std::vector<AnyValue> Values;
    Values.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      auto &Ptr = Ptrs[I];
      if (getBooleanNonPoison(Mask[I].getSingleValue()))
        Values.push_back(load(Ptr, Align, AccessTy, false));
      else
        Values.push_back(PassThru[I]);
    }
    return std::move(Values);
  }
  case Intrinsic::experimental_vp_strided_load: {
    auto Ptr = Args[0].getSingleValue();
    auto Stride = getInt(Args[1].getSingleValue());
    if (!Stride)
      ImmUBReporter(*this) << "llvm.vp.strided.load with poison stride";
    auto &Mask = Args[2].getValueArray();
    auto Evl = getInt(Args[3].getSingleValue());
    auto *EltTy = RetTy->getScalarType();
    uint32_t Len = getVectorLength(cast<VectorType>(RetTy));
    uint32_t Align = II.getParamAlign(0).valueOrOne().value();
    if (!Evl || Evl->ugt(Len))
      ImmUBReporter(*this) << "llvm.vp.strided.load with invalid evl " << Evl;
    std::vector<AnyValue> Values;
    Values.reserve(Len);
    for (uint32_t I = 0; I != Evl->getZExtValue(); ++I) {
      if (getBooleanNonPoison(Mask[I].getSingleValue()))
        Values.push_back(load(Ptr, Align, EltTy, false));
      else
        Values.push_back(poison());
      Ptr = computeGEP(Ptr, *Stride, GEPNoWrapFlags::none());
    }
    PadVPResult(Values, Len);
    return std::move(Values);
  }
  case Intrinsic::experimental_vp_strided_store: {
    auto &Val = Args[0].getValueArray();
    auto Ptr = Args[1].getSingleValue();
    auto Stride = getInt(Args[2].getSingleValue());
    if (!Stride)
      ImmUBReporter(*this) << "llvm.vp.strided.store with poison stride";
    auto &Mask = Args[3].getValueArray();
    auto Evl = getInt(Args[4].getSingleValue());
    auto *EltTy = RetTy->getScalarType();
    uint32_t Len = getVectorLength(cast<VectorType>(RetTy));
    uint32_t Align = II.getParamAlign(1).valueOrOne().value();
    if (!Evl || Evl->ugt(Len))
      ImmUBReporter(*this) << "llvm.vp.strided.load with invalid evl " << Evl;
    for (uint32_t I = 0; I != Evl->getZExtValue(); ++I) {
      if (getBooleanNonPoison(Mask[I].getSingleValue()))
        store(Ptr, Align, Val[I], EltTy, false);
      Ptr = computeGEP(Ptr, *Stride, GEPNoWrapFlags::none());
    }
    return none();
  }
  case Intrinsic::vector_splice: {
    auto &LHS = Args[0].getValueArray();
    auto &RHS = Args[1].getValueArray();
    auto Imm = getInt(Args[2].getSingleValue());
    if (!Imm)
      ImmUBReporter(*this) << "llvm.vector.splice with poison index";
    uint32_t Len = LHS.size();
    if (Imm->isNegative())
      *Imm += Len;
    if (Imm->uge(Len))
      ImmUBReporter(*this) << "llvm.vector.splice with invalid index "
                           << Args[2];
    uint32_t Off = Imm->getZExtValue();
    std::vector<AnyValue> Res;
    Res.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      uint32_t Pos = I + Off;
      Res.push_back(Pos < Len ? LHS[Pos] : RHS[Pos - Len]);
    }
    return std::move(Res);
  }
  case Intrinsic::masked_load: {
    auto Ptr = Args[0].getSingleValue();
    auto Align = getInt(Args[1].getSingleValue())->getZExtValue();
    auto &Mask = Args[2].getValueArray();
    auto &PassThru = Args[3].getValueArray();
    auto *ValTy = cast<VectorType>(RetTy);
    auto *AccessTy = ValTy->getScalarType();
    uint32_t Len = getVectorLength(ValTy);
    APInt Offset(DL.getIndexSizeInBits(0),
                 DL.getTypeStoreSize(AccessTy).getFixedValue(), false, true);
    std::vector<AnyValue> Values;
    Values.reserve(Len);
    for (uint32_t I = 0; I != Len; ++I) {
      Values.push_back(getBooleanNonPoison(Mask[I].getSingleValue())
                           ? load(Ptr, Align, AccessTy, false)
                           : PassThru[I]);
      Ptr = computeGEP(Ptr, Offset, GEPNoWrapFlags::none());
    }
    return std::move(Values);
  }
  case Intrinsic::masked_store: {
    auto &Values = Args[0].getValueArray();
    auto Ptr = Args[1].getSingleValue();
    auto Align = getInt(Args[2].getSingleValue())->getZExtValue();
    auto &Mask = Args[3].getValueArray();
    auto *ValTy = cast<VectorType>(II.getArgOperand(0)->getType());
    auto *AccessTy = ValTy->getScalarType();
    uint32_t Len = Values.size();
    APInt Offset(DL.getIndexSizeInBits(0),
                 DL.getTypeStoreSize(AccessTy).getFixedValue(), false, true);
    for (uint32_t I = 0; I != Len; ++I) {
      if (getBooleanNonPoison(Mask[I].getSingleValue()))
        store(Ptr, Align, Values[I], AccessTy, false);
      Ptr = computeGEP(Ptr, Offset, GEPNoWrapFlags::none());
    }
    return none();
  }
  case Intrinsic::experimental_cttz_elts: {
    auto &Vec = Args[0].getValueArray();
    bool IsZeroPoison = getBooleanNonPoison(Args[1].getSingleValue());
    uint32_t FirstNonZero = Vec.size();
    uint32_t Index = 0;
    for (auto &V : Vec) {
      if (isPoison(V.getSingleValue()))
        return poison();
      auto &Val = std::get<APInt>(V.getSingleValue());
      if (Val.isOne()) {
        FirstNonZero = Index;
        break;
      }
      ++Index;
    }

    if (IsZeroPoison && FirstNonZero == Vec.size())
      return poison();

    return SingleValue{APInt{RetTy->getScalarSizeInBits(), FirstNonZero}};
  }
  default:
    break;
  }
  errs() << "Unsupported intrinsic: " << II.getCalledFunction()->getName()
         << '\n';
  std::abort();
}

void UBAwareInterpreter::patchRustLibFunc() {
  for (auto &F : M) {
    if (!F.isDeclaration())
      continue;
    // std::io::stdio::_print
    if (F.getName().starts_with("_ZN3std2io5stdio6_print")) {
      // Only works for rustlantis
      auto *Entry = BasicBlock::Create(M.getContext(), "entry", &F);
      IRBuilder<> Builder{Entry};
      auto *P1 =
          Builder.CreateInBoundsPtrAdd(F.getArg(0), Builder.getInt64(16));
      auto *P2 = Builder.CreateLoad(Builder.getPtrTy(), P1);
      auto *P3 = Builder.CreateLoad(Builder.getPtrTy(), P2);
      Value *Val = Builder.CreateLoad(Builder.getInt64Ty(), P3);
      auto *FmtStr = Builder.CreateGlobalString("hash: %llu\n", "fmt");
      auto Callee = M.getOrInsertFunction(
          "printf",
          FunctionType::get(Type::getInt32Ty(M.getContext()),
                            {PointerType::getUnqual(M.getContext())}, true));
      Builder.CreateCall(Callee, {FmtStr, Val});
      Builder.CreateRetVoid();
    }

    // std::sys::sync::once::futex::Once::call
    // if (state_and_queued == INCOMPLETE) {
    //   f(OnceState{});
    //   state_and_queued = COMPLETE;
    // }
    if (F.getName().starts_with("_ZN3std3sys4sync4once5futex4Once4call")) {
      auto *Entry = BasicBlock::Create(M.getContext(), "entry", &F);
      IRBuilder<> Builder{Entry};
      auto *OnceState = Builder.CreateAlloca(Builder.getInt64Ty());
      auto *Status = Builder.CreateLoad(Builder.getInt32Ty(), F.getArg(0));
      // const INCOMPLETE: Primitive = 3;
      // See also
      // https://github.com/rust-lang/rust/commit/a2d41393365df0c0c9f728de7f79b8f0d4e14ef2
      auto *Test =
          Builder.CreateICmpEQ(Status, ConstantInt::get(Status->getType(), 3));
      auto *ThenBB = BasicBlock::Create(M.getContext(), "then", &F);
      auto *EndBB = BasicBlock::Create(M.getContext(), "end", &F);
      Builder.CreateCondBr(Test, ThenBB, EndBB);
      Builder.SetInsertPoint(ThenBB);
      Builder.CreateStore(Builder.getInt64(0), OnceState);
      auto *VTable = F.getArg(3);
      auto *FnPtr = Builder.CreatePtrAdd(VTable, Builder.getInt64(24));
      // core::ops::function::FnOnce::call_once{{vtable.shim}}
      auto *VTableShim = Builder.CreateLoad(Builder.getPtrTy(), FnPtr);
      Builder.CreateCall(
          FunctionType::get(Builder.getVoidTy(),
                            {Builder.getPtrTy(), Builder.getPtrTy()}, false),
          VTableShim, {F.getArg(2), OnceState});
      Builder.CreateStore(Builder.getInt32(3), F.getArg(0));
      Builder.CreateBr(EndBB);
      Builder.SetInsertPoint(EndBB);
      Builder.CreateRetVoid();
    }
  }
}

SingleValue UBAwareInterpreter::alloc(const APInt &AllocSize,
                                      bool ZeroInitialize) {
  auto MemObj = MemMgr.create("alloc", false, AllocSize.getZExtValue(), 8);
  AllocatedMems.insert(MemObj);
  if (ZeroInitialize)
    std::memset(MemObj->rawPointer(), 0, MemObj->size());
  return SingleValue{Pointer{
      MemObj, 0, ContextSensitivePointerInfo::getDefault(CurrentFrame)}};
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
      ImmUBReporter(*this) << "calloc with poison count";
    auto Size = getInt(Args[1].getSingleValue());
    if (!Size)
      ImmUBReporter(*this) << "calloc with poison size";
    return alloc(*Num * *Size, /*ZeroInitialize=*/true);
  }
  case LibFunc_free:
  case LibFunc_ZdaPv:
  case LibFunc_ZdlPv: {
    auto &Ptr = Args[0].getSingleValue();
    if (isPoison(Ptr))
      ImmUBReporter(*this) << "free with poison ptr";
    auto &PtrVal = std::get<Pointer>(Ptr);
    if (PtrVal.Offset != 0)
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
  case LibFunc_terminate:
    ImmUBReporter(*this) << "Terminated";
    break;
  case LibFunc_abort:
    ImmUBReporter(*this) << "Aborted";
    break;
  default:
    break;
  }
  errs() << "Unsupported libcall: " << FuncDecl->getName() << '\n';
  std::abort();
}
AnyValue UBAwareInterpreter::call(Function *Func, CallBase *CB,
                                  SmallVectorImpl<AnyValue> &Args) {
  assert(!Func->isPresplitCoroutine() &&
         "Do not support coroutine before it is split");
  auto FnAttrs = Func->getAttributes();

  SmallVector<std::shared_ptr<MemObject>> ByValTempObjects;
  auto AddNoAlias = [&](Value *Locker, AnyValue &Ptr) {
    // TODO: handle noalias
  };

  auto PostProcessArgs = [&] {
    if (CB) {
      bool HandleParamAttr =
          !isa<IntrinsicInst>(CB) || !Option.IgnoreParamAttrsOnIntrinsic;
      for (const auto &[Idx, Arg] : enumerate(CB->args())) {
        auto &ArgVal = Args[Idx];

        MemObject *InitializeMO = nullptr;
        int64_t InitializeOffset = 0;
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
          // FIXME: propagate poison
          memcpy(TmpMO->rawPointer(), getRawPtr(ArgVal.getSingleValue()),
                 DL.getTypeStoreSize(Ty));
          ArgVal = SingleValue{Pointer{
              TmpMO, 0, ContextSensitivePointerInfo::getDefault(CurrentFrame)}};
          InitializeMO = TmpMO.get();
          ByValTempObjects.push_back(std::move(TmpMO));
        }

        if (HandleParamAttr)
          postProcessAttr(*this, ArgVal, CB->getParamAttributes(Idx));
        if (CB->getArgOperand(Idx)->getType()->isPointerTy()) {
          if (CB->paramHasAttr(Idx, Attribute::NoAlias))
            AddNoAlias(Func->getArg(Idx), ArgVal);

          // Convert pointer loc to argmem
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
                  ImmUBReporter(*this) << "Pass poison to an pointer "
                                          "argument with initializes";
                auto &Ptr = std::get<Pointer>(ArgVal.getSingleValue());
                auto MO = Ptr.Obj.lock();
                if (!MO)
                  ImmUBReporter(*this) << "Pass dangling pointer to an "
                                          "pointer argument with "
                                          "initializes";
                InitializeMO = MO.get();
                InitializeOffset = Ptr.Offset;
              }

              for (auto &R : Initializes) {
                uint64_t Lo = static_cast<uint64_t>(
                    InitializeOffset + R.getLower().getSExtValue());
                uint64_t Hi = static_cast<uint64_t>(
                    InitializeOffset + R.getUpper().getSExtValue());
                // Approximation: initialize the region with undef
                InitializeMO->markPoison(Lo, Hi - Lo, false);
              }
            }
          }
        }
      }
    }

    // Skip if the function attr is known via CB.
    // FIXME: handle initializes
    if (!CB || !CB->getCalledFunction())
      for (const auto &[Idx, Param] : enumerate(Func->args()))
        postProcessAttr(*this, Args[Idx], FnAttrs.getParamAttrs(Idx));
  };

  auto ExitFunc = [&](Frame *OldFrame) { CurrentFrame = OldFrame; };

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

  if (Func->empty()) {
    // Handle Rust allocator API
    Frame CallFrame{Func, nullptr, TLI, CurrentFrame, ME};
    auto Scope =
        llvm::make_scope_exit([&, Frame = CurrentFrame] { ExitFunc(Frame); });
    CurrentFrame = &CallFrame;
    PostProcessArgs();
    auto Kind = Func->getAttributes().getAllocKind();
    if ((Kind & AllocFnKind::Alloc) == AllocFnKind::Alloc) {
      Attribute Attr = CB->getFnAttr(Attribute::AllocSize);
      if (Attr != Attribute()) {
        auto AllocArgs = Attr.getAllocSizeArgs();
        auto Size = getInt(Args[AllocArgs.first].getSingleValue());
        if (!Size)
          ImmUBReporter(*this) << "malloc with poison size";
        // TODO: handle allocalign
        bool ZeroInit =
            (Kind & AllocFnKind::Uninitialized) != AllocFnKind::Uninitialized;
        return alloc(*Size,
                     /*ZeroInitialize=*/ZeroInit);
      }
    } else if ((Kind & AllocFnKind::Free) == AllocFnKind::Free) {
      auto &Ptr = Args[0].getSingleValue();
      if (isPoison(Ptr))
        ImmUBReporter(*this) << "free with poison ptr";
      auto &PtrVal = std::get<Pointer>(Ptr);
      if (PtrVal.Offset != 0)
        ImmUBReporter(*this) << "free with invalid ptr " << Ptr;
      if (auto MO = PtrVal.Obj.lock())
        AllocatedMems.erase(MO);
      else
        ImmUBReporter(*this) << "free with invalid ptr " << Ptr;
      return none();
    }
    errs() << "Do not know how to handle " << *Func << '\n';
    std::exit(EXIT_FAILURE);
  }

  FunctionAnalysisCache *FAC = nullptr;
  if (Option.VerifyValueTracking || Option.VerifySCEV) {
    auto CacheIter = AnalysisCache.find(Func);
    if (CacheIter == AnalysisCache.end()) {
      CacheIter =
          AnalysisCache
              .emplace(Func,
                       std::make_unique<FunctionAnalysisCache>(*Func, TLI))
              .first;
    }
    FAC = CacheIter->second.get();
  }

  Frame CallFrame{Func, FAC, TLI, CurrentFrame, ME};
  auto Scope =
      llvm::make_scope_exit([&, Frame = CurrentFrame] { ExitFunc(Frame); });
  CurrentFrame = &CallFrame;
  PostProcessArgs();
  if (Option.Verbose) {
    errs() << "\n\nEntering function " << Func->getName() << '\n';
    for (auto &&[Idx, Arg] : enumerate(Func->args()))
      errs() << "  " << Arg << " = " << Args[Idx] << '\n';
  }
  for (auto &Param : Func->args())
    CallFrame.ValueMap[&Param] = std::move(Args[Param.getArgNo()]);

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
      if ((Option.VerifyValueTracking || Option.VerifySCEV)) {
        Type *Ty = (*CallFrame.PC).getType();
        if (Ty->isSingleValueType()) {
          auto Iter = CallFrame.ValueMap.find(&*CallFrame.PC);
          if (Iter != CallFrame.ValueMap.end()) {
            if (Option.VerifyValueTracking)
              verifyValueTracking(Iter->first, Iter->second, &*CallFrame.PC);
            if (Option.VerifySCEV && CallFrame.Cache->SE.isSCEVable(Ty))
              verifySCEV(Iter->first, Iter->second);
            if (Option.VerifyLazyValueInfo && Ty->isIntegerTy() &&
                !Ty->isIntegerTy(1)) {
              auto CR = CallFrame.Cache->LVI.getConstantRange(
                  Iter->first, cast<Instruction>(Iter->first), false);
              auto &Val = Iter->second.getSingleValue();
              if (!isPoison(Val) && !CR.contains(std::get<APInt>(Val)))
                Val = poison();
            }
          }
        }
      }
      auto *InnerCB = dyn_cast<CallBase>(CallFrame.PC);
      if (InnerCB && InnerCB->getType()->isPointerTy() &&
          InnerCB->returnDoesNotAlias())
        AddNoAlias(InnerCB, CurrentFrame->ValueMap.find(InnerCB)->second);
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
  Function *Entry = nullptr;
  if (Option.RustMode) {
    for (auto &F : M) {
      // xxx::main
      if (F.getName().contains("4main"))
        Entry = &F;
    }
  } else {
    Entry = M.getFunction("main");
  }
  if (!Entry) {
    errs() << "Cannot find entry function `main`\n";
    return EXIT_FAILURE;
  }

  SmallVector<AnyValue> Args;
  if (Option.ReduceMode) {
    for (auto &Arg : Entry->args())
      Args.push_back(getZero(Arg.getType()));
  } else if (!Option.RustMode) {
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
FunctionAnalysisCache::FunctionAnalysisCache(Function &F,
                                             TargetLibraryInfoImpl &TLIImpl)
    : DT(F), AC(F), TLI(TLIImpl, &F), LI(DT), SE(F, TLI, AC, DT, LI),
      LVI(&AC, &F.getDataLayout()) {
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
  return KnownBitsCache[V] = computeKnownBits(V, SQ);
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
    : Func(Func), BB(nullptr), PC(), Cache(Cache), TLI(TLI, Func),
      LastFrame(LastFrame), MemEffects(ME) {}
void UBAwareInterpreter::verifyValueTracking(Value *V, const AnyValue &RV,
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
      unsigned SignBits = ComputeNumSignBits(V, SQ.DL, SQ.AC, SQ.CxtI, SQ.DT);
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

using SCEVEvalRes = std::optional<APInt>;

static uint64_t GetBinomialCoefficient(uint64_t N, uint64_t M) {
  if (N < M)
    return 0;
  if (N == M || M == 0)
    return 1;
  if (N - M < M)
    M = N - M;
  if (M == 1)
    return N;
  if (M == 2 && N <= (1ULL << 32))
    return N * (N - 1) / 2;
  if (M == 3 && N <= (1ULL << 21))
    return N * (N - 1) * (N - 2) / 6;
  static std::vector<std::vector<uint32_t>> Coeff2D;
  if (Coeff2D.size() < M + 1)
    Coeff2D.resize(M + 1);
  for (uint64_t I = 0; I <= M; ++I) {
    auto &Coeffs = Coeff2D[I];
    if (I == 0) {
      if (Coeffs.size() < N + 1)
        Coeffs.resize(N + 1, 1);
    } else {
      auto &LastCoeffs = Coeff2D[I - 1];
      Coeffs.reserve(N + 1);
      if (Coeffs.empty())
        Coeffs.push_back(0);
      for (uint64_t J = Coeffs.size(); J <= N; ++J)
        Coeffs.push_back(Coeffs[J - 1] + LastCoeffs[J - 1]);
    }
  }
  return Coeff2D[M][N];
}

class SCEVEvaluator final : public SCEVVisitor<SCEVEvaluator, SCEVEvalRes> {
  const DataLayout &DL;
  function_ref<SCEVEvalRes(Value *)> EvalUnknown;
  function_ref<uint32_t(const Loop *)> GetLoopBECount;
  uint32_t VScale;

  uint32_t getSize(const SCEV *S) {
    auto *Ty = S->getType();
    if (Ty->isPointerTy())
      return DL.getPointerTypeSizeInBits(Ty);
    return Ty->getIntegerBitWidth();
  }

public:
  explicit SCEVEvaluator(const DataLayout &DL,
                         function_ref<SCEVEvalRes(Value *)> EvalUnknown,
                         function_ref<uint32_t(const Loop *)> GetLoopBECount,
                         uint32_t VScale)
      : DL(DL), EvalUnknown(EvalUnknown), GetLoopBECount(GetLoopBECount),
        VScale(VScale) {}

  SCEVEvalRes visitConstant(const SCEVConstant *SC) {
    return SC->getValue()->getValue();
  }

  SCEVEvalRes visitVScale(const SCEVVScale *S) {
    return APInt{getSize(S), VScale};
  }

  SCEVEvalRes visitPtrToIntExpr(const SCEVPtrToIntExpr *S) {
    auto *Ptr = S->getOperand();
    return visit(Ptr);
  }

  SCEVEvalRes visitTruncateExpr(const SCEVTruncateExpr *S) {
    auto *Op = S->getOperand();
    auto OpRes = visit(Op);
    if (!OpRes.has_value())
      return std::nullopt;
    return OpRes->trunc(getSize(S));
  }

  SCEVEvalRes visitZeroExtendExpr(const SCEVZeroExtendExpr *S) {
    auto *Op = S->getOperand();
    auto OpRes = visit(Op);
    if (!OpRes.has_value())
      return std::nullopt;
    return OpRes->zext(getSize(S));
  }

  SCEVEvalRes visitSignExtendExpr(const SCEVSignExtendExpr *S) {
    auto *Op = S->getOperand();
    auto OpRes = visit(Op);
    if (!OpRes.has_value())
      return std::nullopt;
    return OpRes->sext(getSize(S));
  }

  SCEVEvalRes visitAddExpr(const SCEVAddExpr *S) {
    // TODO: the nowrap flags must apply regardless of the order
    // (sum of positives) + (sum of negatives)
    APInt Res(getSize(S), 0);
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      auto BinOpRes =
          addNoWrap(Res, *OpRes, S->hasNoSignedWrap(), S->hasNoUnsignedWrap());
      if (!BinOpRes.has_value())
        return std::nullopt;
      Res = *BinOpRes;
    }
    return Res;
  }

  SCEVEvalRes visitMulExpr(const SCEVMulExpr *S) {
    APInt Res(getSize(S), 1);
    // TODO: the nowrap flags must apply regardless of the order
    // sort by the absolute value
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      auto BinOpRes =
          mulNoWrap(Res, *OpRes, S->hasNoSignedWrap(), S->hasNoUnsignedWrap());
      if (!BinOpRes.has_value())
        return std::nullopt;
      Res = *BinOpRes;
    }
    return Res;
  }

  SCEVEvalRes visitUDivExpr(const SCEVUDivExpr *S) {
    auto LHSRes = visit(S->getLHS());
    if (!LHSRes.has_value())
      return std::nullopt;
    auto RHSRes = visit(S->getRHS());
    if (!RHSRes.has_value())
      return std::nullopt;
    // For better diagnostics, convert division by zero from immediate UB to
    // poison.
    if (RHSRes->isZero())
      return std::nullopt;
    return LHSRes->udiv(*RHSRes);
  }

  SCEVEvalRes visitSMaxExpr(const SCEVSMaxExpr *S) {
    APInt Res = APInt::getSignedMinValue(getSize(S));
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      Res = APIntOps::smax(Res, *OpRes);
    }
    return Res;
  }

  SCEVEvalRes visitSMinExpr(const SCEVSMinExpr *S) {
    APInt Res = APInt::getSignedMaxValue(getSize(S));
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      Res = APIntOps::smin(Res, *OpRes);
    }
    return Res;
  }

  SCEVEvalRes visitUMaxExpr(const SCEVUMaxExpr *S) {
    APInt Res = APInt::getMinValue(getSize(S));
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      Res = APIntOps::umax(Res, *OpRes);
    }
    return Res;
  }

  SCEVEvalRes visitUMinExpr(const SCEVUMinExpr *S) {
    APInt Res = APInt::getMaxValue(getSize(S));
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      Res = APIntOps::umin(Res, *OpRes);
    }
    return Res;
  }

  SCEVEvalRes visitSequentialUMinExpr(const SCEVSequentialUMinExpr *S) {
    APInt Res = APInt::getMaxValue(getSize(S));
    for (auto *Op : S->operands()) {
      auto OpRes = visit(Op);
      if (!OpRes.has_value())
        return std::nullopt;
      // We reached the saturation point.
      if (OpRes->isMinValue())
        return *OpRes;
      Res = APIntOps::umin(Res, *OpRes);
    }
    return Res;
  }

  SCEVEvalRes visitAddRecExpr(const SCEVAddRecExpr *S) {
    auto Start = visit(S->getStart());
    if (!Start.has_value())
      return std::nullopt;
    auto BECount = GetLoopBECount(S->getLoop());
    if (BECount == 0)
      return Start;
    // We only check nw for affine addrec.
    if (S->isAffine()) {
      auto Step = visit(S->getOperand(1));
      if (!Step.has_value())
        return std::nullopt;
      APInt BECountC(Step->getBitWidth(), BECount, false, true);
      if (S->hasNoSelfWrap()) {
        auto AbsStep = Step->abs();
        bool Overflow = false;
        (void)AbsStep.umul_ov(BECountC, Overflow);
        if (Overflow)
          return std::nullopt;
      }
      return addNoWrap(*Start + *Step * (BECountC - 1), *Step,
                       S->hasNoSignedWrap(), S->hasNoUnsignedWrap());
    } else {
      APInt LastInc = APInt::getZero(getSize(S));
      APInt CurInc = APInt::getZero(getSize(S));
      uint32_t Idx = 1;
      for (auto *Op : drop_begin(S->operands())) {
        auto LastCoeff = GetBinomialCoefficient(BECount - 1, Idx);
        auto CurCoeff = GetBinomialCoefficient(BECount, Idx);
        ++Idx;
        if (CurCoeff == 0)
          continue;
        auto OpRes = visit(Op);
        if (!OpRes.has_value())
          return std::nullopt;
        LastInc += *OpRes * LastCoeff;
        CurInc += *OpRes * CurCoeff;
      }
      auto Diff = CurInc - LastInc;
      return addNoWrap(*Start + LastInc, Diff, S->hasNoSignedWrap(),
                       S->hasNoUnsignedWrap());
    }
  }

  SCEVEvalRes visitUnknown(const SCEVUnknown *S) {
    return EvalUnknown(S->getValue());
  }
};

void UBAwareInterpreter::verifySCEV(Value *V, const AnyValue &RV) {
  auto &SE = CurrentFrame->Cache->SE;
  auto *Expr = SE.getSCEV(V);

  if (isa<SCEVUnknown>(Expr))
    return;

  auto EvalUnknown = [&](Value *V) -> SCEVEvalRes {
    auto &Res = getValue(V).getSingleValue();
    if (isPoison(Res))
      return std::nullopt;
    if (auto *C = std::get_if<APInt>(&Res))
      return *C;
    if (auto *P = std::get_if<Pointer>(&Res))
      return P->Address;
    errs() << "Unknown value type: " << *V << '\n';
    llvm_unreachable("Unreachable");
  };
  auto GetLoopBECount = [&](const Loop *L) -> uint32_t {
    return CurrentFrame->Cache->BECount.at(L);
  };
  SCEVEvaluator Evaluator{DL, EvalUnknown, GetLoopBECount, Option.VScale};
  auto SCEVRes = Evaluator.visit(Expr);
  auto &SingleRV = getValue(V).getSingleValue();
  if (isPoison(SingleRV))
    return;
  auto DumpSubExprs = [&] {
    struct EvalAllSubExpr {
      SCEVEvaluator &Evaluator;
      function_ref<uint32_t(const Loop *)> GetLoopBECount;

      bool follow(const SCEV *S) {
        if (isa<SCEVConstant>(S))
          return false;
        auto Res = Evaluator.visit(S);
        if (!Res.has_value())
          errs() << "  " << *S << " = poison";
        else
          errs() << "  " << *S << " = " << *Res;
        if (auto *AddRec = dyn_cast<SCEVAddRecExpr>(S)) {
          auto BECount = GetLoopBECount(AddRec->getLoop());
          errs() << " (BE count = " << BECount << ")";
        }
        errs() << '\n';
        return true;
      }

      bool isDone() const { return false; }
    };

    EvalAllSubExpr E{Evaluator, GetLoopBECount};
    SCEVTraversal<EvalAllSubExpr> Traversal{E};
    Traversal.visitAll(Expr);
  };
  if (!SCEVRes.has_value()) {
    DumpSubExprs();
    ImmUBReporter(*this) << "SCEV result is more poisonous than real value\n"
                         << *V << " = " << RV << '\n'
                         << *Expr << " = poison" << '\n';
  }
  auto &SCEVIntRes = SCEVRes.value();
  auto &RealRes = std::holds_alternative<Pointer>(SingleRV)
                      ? std::get<Pointer>(SingleRV).Address
                      : std::get<APInt>(SingleRV);
  if (SCEVIntRes != RealRes) {
    DumpSubExprs();
    ImmUBReporter(*this) << "SCEV result is different from real value\n"
                         << *V << " = " << RV << '\n'
                         << *Expr << " = " << SCEVIntRes << '\n';
  }

  // Verify analysis result
  auto UCR = SE.getUnsignedRange(Expr);
  if (!UCR.contains(SCEVIntRes))
    ImmUBReporter(*this) << "Real value is out of the SCEV unsigned range\n"
                         << *V << " = " << RV << '\n'
                         << *Expr << " = " << UCR << '\n';

  auto SCR = SE.getSignedRange(Expr);
  if (!SCR.contains(SCEVIntRes))
    ImmUBReporter(*this) << "Real value is out of the SCEV signed range\n"
                         << *V << " = " << RV << '\n'
                         << *Expr << " = " << SCR << '\n';

  auto Fac = SE.getConstantMultiple(Expr);
  if (Fac.ugt(1) && !RealRes.urem(Fac).isZero()) {
    ImmUBReporter(*this)
        << "Real value is not a multiple of the SCEV constant\n"
        << *V << " = " << RV << '\n'
        << "MaxKnownFac(" << *Expr << ") = " << Fac << '\n';
  }
}
