// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/APSInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/FloatingPointMode.h>
#include <llvm/ADT/MapVector.h>
#include <llvm/ADT/STLFunctionalExtras.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constant.h>
#include <llvm/IR/ConstantRange.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/FMF.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/Alignment.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/SwapByteOrder.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/TypeSize.h>
#include <llvm/Support/raw_ostream.h>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <optional>
#include <variant>

using namespace llvm;
static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input>"),
                                      cl::Required,
                                      cl::value_desc("path to input IR"));
static cl::opt<uint32_t> VScaleValue(cl::desc("vscale"),
                                     cl::value_desc("value for llvm.vscale"),
                                     cl::init(4U));
static cl::opt<bool> IgnoreParamAttrsOnIntrinsic(
    "ignore-param-attrs-intrinsic",
    cl::desc("Ignore parameter attributes of intrinsic calls"),
    cl::init(false));
static cl::opt<bool> Verbose("verbose", cl::desc("Print step-by-step log"),
                             cl::init(false));

// TODO: handle llvm.lifetime.start/end and llvm.invariant.start.end/TBAA
size_t AllocatedMem = 0;
constexpr size_t Padding = 16U;

class ImmUBReporter final {
  raw_ostream &Out;

public:
  ImmUBReporter() : Out(errs()) { Out << "\nUB triggered: "; }
  [[noreturn]] ~ImmUBReporter() {
    Out << "\nExited with immediate UB.\n";
    Out.flush();
    std::exit(EXIT_FAILURE);
  }
  template <typename Arg> ImmUBReporter &operator<<(Arg &&arg) {
    Out << std::forward<Arg>(arg);
    return *this;
  }
};

class MemObject final : public std::enable_shared_from_this<MemObject> {
  std::string Name;
  bool IsLocal;
  size_t Address;
  SmallVector<std::byte, 16> Data;

public:
  static std::map<size_t, MemObject *> AddressMap;
  explicit MemObject(std::string Name, bool IsLocal, size_t Size,
                     size_t Alignment)
      : Name(std::move(Name)), IsLocal(IsLocal), Data(Size) {
    AllocatedMem = alignTo(AllocatedMem, Alignment);
    Address = AllocatedMem;
    AllocatedMem += Size + Padding;
    AddressMap.emplace(Address, this);
  }
  ~MemObject() { AddressMap.erase(Address); }
  void verifyMemAccess(intptr_t Offset, size_t AccessSize, size_t Alignment) {
    size_t NewAddr = Address + Offset;
    if (alignTo(NewAddr, Alignment) != NewAddr)
      ImmUBReporter() << "Unaligned mem op";
    if (Offset + AccessSize > Data.size())
      ImmUBReporter() << "Out of bound mem op, bound = " << Data.size()
                      << ", access range = [" << Offset << ", "
                      << Offset + AccessSize << ')';
  }
  static std::shared_ptr<MemObject> create(std::string Name, bool IsLocal,
                                           size_t Size, size_t Alignment) {
    return std::make_shared<MemObject>(std::move(Name), IsLocal, Size,
                                       Alignment);
  }
  void store(size_t Offset, const APInt &C) {
    //     errs() << Offset << ' ' << Data.size() << ' ' << C.getBitWidth() << '
    //     '<< C.getNumWords() << '\n';
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
  APInt load(size_t Offset, size_t Bits) const {
    APInt Res = APInt::getZero(alignTo(Bits, 8));
    constexpr uint32_t Scale = sizeof(APInt::WordType);
    const size_t Size = Res.getBitWidth() / 8;
    uint32_t ReadCnt = 0;
    const std::byte *ReadPos = Data.data() + Offset;
    for (uint32_t I = 0; I != Res.getNumWords(); ++I) {
      auto &Word = const_cast<APInt::WordType &>(Res.getRawData()[I]);
      if (ReadCnt + Scale <= Size) {
        memcpy(&Word, &ReadPos[ReadCnt], sizeof(Word));
        ReadPos += Scale;
        if (ReadCnt == Size)
          break;
      } else {
        for (auto J = 0; J != Scale; ++J) {
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
  size_t address() const { return Address; }
  size_t size() const { return Data.size(); }
  char *rawPointer() { return reinterpret_cast<char *>(Data.data()); }
  void dumpName(raw_ostream &Out) { Out << (IsLocal ? '%' : '@') << Name; }
  void dumpRef(raw_ostream &Out) {
    Out << '[' << (IsLocal ? '%' : '@') << Name << "(Addr = " << Address << ", "
        << "Size = " << Data.size() << ']';
  }
};
std::map<size_t, MemObject *> MemObject::AddressMap;

struct Pointer final {
  std::weak_ptr<MemObject> Obj;
  intptr_t Offset;
  size_t Address;
  intptr_t Bound;

  Pointer(const std::shared_ptr<MemObject> &Obj, intptr_t Offset)
      : Obj(Obj), Offset(Offset), Address(Obj->address() + Offset),
        Bound(Obj->size()) {}
  explicit Pointer(const std::weak_ptr<MemObject> &Obj, intptr_t NewOffset,
                   size_t NewAddress, intptr_t NewBound)
      : Obj(Obj), Offset(NewOffset), Address(NewAddress), Bound(NewBound) {}
};

using SingleValue = std::variant<APInt, APFloat, Pointer, std::monostate>;
bool isPoison(const SingleValue &SV) {
  return std::holds_alternative<std::monostate>(SV);
}
bool isPoison(const APFloat &AFP, FastMathFlags FMF) {
  if (FMF.noNaNs() && AFP.isNaN())
    return true;
  if (FMF.noInfs() && AFP.isInfinity())
    return true;
  return false;
}
SingleValue boolean(bool Val) { return SingleValue{APInt(1, Val)}; }
SingleValue poison() { return std::monostate{}; }
SingleValue lookupPointer(size_t Addr) {
  if (auto Iter = MemObject::AddressMap.upper_bound(Addr);
      Iter != MemObject::AddressMap.begin()) {
    auto *MO = std::prev(Iter)->second;
    if (MO->address() <= Addr && Addr <= MO->address() + MO->size()) {
      return SingleValue{Pointer{MO->shared_from_this(),
                                 static_cast<intptr_t>(Addr - MO->address())}};
    }
  }

  return SingleValue{Pointer{std::weak_ptr<MemObject>{}, 0, Addr, 0}};
}
SingleValue offsetPointer(const Pointer &Ptr, intptr_t Offset, bool InBound) {
  if (Offset == 0)
    return Ptr;
  intptr_t NewOffset = Ptr.Offset + Offset;
  if (NewOffset < 0 || NewOffset > Ptr.Bound) {
    if (InBound)
      return poison();
    return lookupPointer(Ptr.Address + NewOffset);
  }

  return Pointer{Ptr.Obj, NewOffset, Ptr.Address + Offset, Ptr.Bound};
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
    // Out << "Ptr { Obj = ";
    // if (auto P = Ptr->Obj.lock())
    //   P->dumpRef(Out);
    // else
    //   Out << "[dangling]";
    // Out << ", Offset = " << Ptr->Offset << ", Addr = " << Ptr->Address
    //     << ", Bound = " << Ptr->Bound << '}';
    // return Out;
    Out << "Ptr " << Ptr->Address << '[';
    if (auto P = Ptr->Obj.lock())
      P->dumpName(Out);
    else
      Out << "dangling";
    if (Ptr->Offset)
      Out << " + " << Ptr->Offset;
    return Out << ']';
  }
  return Out << "poison";
}

struct AnyValue final {
  std::variant<std::monostate, SingleValue, std::vector<AnyValue>> Val;

  AnyValue(SingleValue SV) : Val(std::move(SV)) {}
  AnyValue(std::vector<AnyValue> MV) : Val(std::move(MV)) {}
  AnyValue() = default;

  bool isSingleValue() const {
    return std::holds_alternative<SingleValue>(Val);
  }
  const SingleValue &getSingleValue() const {
    assert(isSingleValue());
    return std::get<SingleValue>(Val);
  }
  SingleValue &getSingleValue() {
    assert(isSingleValue());
    return std::get<SingleValue>(Val);
  }
  const std::vector<AnyValue> &getValueArray() const {
    assert(std::holds_alternative<std::vector<AnyValue>>(Val));
    return std::get<std::vector<AnyValue>>(Val);
  }
  std::vector<AnyValue> &getValueArray() {
    assert(std::holds_alternative<std::vector<AnyValue>>(Val));
    return std::get<std::vector<AnyValue>>(Val);
  }
  const SingleValue &getSingleValueAt(uint32_t Idx) const {
    return getValueArray().at(Idx).getSingleValue();
  }
  SingleValue &getSingleValueAt(uint32_t Idx) {
    return getValueArray().at(Idx).getSingleValue();
  }
};

AnyValue none() { return AnyValue{std::monostate{}}; }
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

void handleNoUndef(const SingleValue &V) {
  if (isPoison(V))
    ImmUBReporter() << "noundef on a poison value";
}
APFloat handleDenormal(APFloat V, DenormalMode::DenormalModeKind Denormal) {
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
void handleFPVal(SingleValue &V, FastMathFlags FMF,
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
SingleValue handleFPVal(APFloat V, FastMathFlags FMF,
                        DenormalMode::DenormalModeKind Denormal) {
  if (isPoison(V, FMF))
    return poison();
  return handleDenormal(std::move(V), Denormal);
}
void handleRange(SingleValue &V, const ConstantRange &CR) {
  if (auto *CI = std::get_if<APInt>(&V)) {
    if (!CR.contains(*CI))
      V = poison();
  }
}
void handleAlign(SingleValue &V, size_t Align) {
  if (isPoison(V))
    return;
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address & (Align - 1))
    V = poison();
}
void handleNonNull(SingleValue &V) {
  if (isPoison(V))
    return;
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address == 0)
    V = poison();
}
void handleNoFPClass(SingleValue &V, FPClassTest Mask) {
  if (isPoison(V))
    return;
  auto &AFP = std::get<APFloat>(V);
  if (AFP.classify() & Mask)
    V = poison();
}
void handleDereferenceable(SingleValue &V, uint64_t Size, bool OrNull) {
  if (isPoison(V))
    ImmUBReporter() << "dereferenceable on a poison value";
  auto &Ptr = std::get<Pointer>(V);
  if (Ptr.Address == 0) {
    if (OrNull)
      return;
    ImmUBReporter() << "dereferenceable on a null pointer";
  }
  if (Ptr.Offset + Size > Ptr.Bound) {
    ImmUBReporter() << "dereferenceable" << (OrNull ? "_or_null" : "") << "("
                    << Size << ") out of bound :" << V;
  }
  if (Ptr.Obj.expired())
    ImmUBReporter() << "dereferenceable" << (OrNull ? "_or_null" : "")
                    << " on a dangling pointer";
}
void postProcess(AnyValue &V, const function_ref<void(SingleValue &)> &Fn) {
  if (V.isSingleValue()) {
    Fn(V.getSingleValue());
  } else {
    for (auto &Sub : V.getValueArray())
      postProcess(Sub, Fn);
  }
}
AnyValue postProcessFPVal(AnyValue V, Instruction &FMFSource) {
  if (FMFSource.getType()->isFPOrFPVectorTy()) {
    FastMathFlags FMF = FMFSource.getFastMathFlags();
    postProcess(V, [FMF](SingleValue &SV) {
      handleFPVal(SV, FMF, DenormalMode::IEEE);
    });
  }
  return std::move(V);
}
void postProcessAttr(AnyValue &V, const AttributeSet &AS) {
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
    postProcess(
        V, [Size](SingleValue &SV) { handleDereferenceable(SV, Size, false); });
  }
  if (AS.hasAttribute(Attribute::DereferenceableOrNull)) {
    auto Size = AS.getDereferenceableOrNullBytes();
    postProcess(
        V, [Size](SingleValue &SV) { handleDereferenceable(SV, Size, true); });
  }
  if (AS.hasAttribute(Attribute::Alignment)) {
    auto Align = AS.getAlignment().valueOrOne().value();
    postProcess(V, [Align](SingleValue &SV) { handleAlign(SV, Align); });
  }
  if (AS.hasAttribute(Attribute::NonNull))
    postProcess(V, handleNonNull);
  if (AS.hasAttribute(Attribute::NoUndef))
    postProcess(V, handleNoUndef);
}

struct Frame final {
  BasicBlock *BB;
  BasicBlock::iterator PC;
  SmallVector<std::shared_ptr<MemObject>> Allocas;
  DenseMap<Value *, AnyValue> ValueMap;
  std::optional<AnyValue> RetVal;
};

class UBAwareInterpreter : public InstVisitor<UBAwareInterpreter, bool> {
  LLVMContext &Ctx;
  Module &M;
  const DataLayout &DL;
  TargetLibraryInfoImpl TLI;
  std::shared_ptr<MemObject> NullPtr;
  DenseMap<GlobalValue *, std::shared_ptr<MemObject>> GlobalValues;
  DenseMap<size_t, Function *> ValidCallees;
  DenseMap<size_t, BasicBlock *> ValidBlockTargets;
  DenseMap<BasicBlock *, std::shared_ptr<MemObject>> BlockTargets;
  Frame *CurrentFrame = nullptr;

  uint32_t getVectorLength(VectorType *Ty) const {
    auto EC = Ty->getElementCount();
    if (EC.isFixed())
      return EC.getFixedValue();
    return EC.getKnownMinValue() * VScaleValue;
  }
  AnyValue getPoison(Type *Ty) const {
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
    errs() << *Ty << '\n';
    llvm_unreachable("Unsupported type");
  }
  AnyValue getZero(Type *Ty) const {
    if (Ty->isIntegerTy())
      return SingleValue{APInt::getZero(Ty->getIntegerBitWidth())};
    if (Ty->isFloatingPointTy())
      return SingleValue{APFloat::getZero(Ty->getFltSemantics())};
    if (Ty->isPointerTy())
      return SingleValue{Pointer{NullPtr, 0U}};
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
    errs() << *Ty << '\n';
    llvm_unreachable("Unsupported type");
  }
  AnyValue convertFromConstant(Constant *V) const {
    if (isa<PoisonValue>(V))
      return getPoison(V->getType());
    if (isa<UndefValue, ConstantAggregateZero>(V))
      return getZero(V->getType());
    if (auto *CI = dyn_cast<ConstantInt>(V))
      return SingleValue{CI->getValue()};
    if (auto *CFP = dyn_cast<ConstantFP>(V))
      return SingleValue{CFP->getValue()};
    if (isa<ConstantPointerNull>(V))
      return SingleValue{Pointer{NullPtr, 0U}};
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
      return AnyValue{Pointer{GlobalValues.at(GV), 0}};
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
              Offset.getSExtValue(), Inst->isInBounds());
        }
        break;
      }
      default:
        break;
      }
    }
    if (auto *BA = dyn_cast<BlockAddress>(V))
      return SingleValue{Pointer{BlockTargets.at(BA->getBasicBlock()), 0}};
    errs() << *V << '\n';
    llvm_unreachable("Unexpected constant");
  }
  void store(MemObject &MO, uint32_t Offset, const AnyValue &V, Type *Ty) {
    if (Ty->isIntegerTy()) {
      auto &SV = V.getSingleValue();
      if (isPoison(SV))
        return;
      MO.store(Offset, std::get<APInt>(SV));
    } else if (Ty->isFloatingPointTy()) {
      auto &SV = V.getSingleValue();
      if (isPoison(SV))
        return;
      auto &C = std::get<APFloat>(SV);
      MO.store(Offset, C.bitcastToAPInt());
    } else if (Ty->isPointerTy()) {
      auto &SV = V.getSingleValue();
      if (isPoison(SV))
        return;
      auto &Ptr = std::get<Pointer>(SV);
      MO.store(Offset, APInt(DL.getPointerSizeInBits(), Ptr.Address));
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
      llvm_unreachable("Unsupported mem store");
    }
  }
  AnyValue load(const MemObject &MO, uint32_t Offset, Type *Ty) {
    if (Ty->isIntegerTy()) {
      return SingleValue{
          MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue())
              .trunc(Ty->getScalarSizeInBits())};
    } else if (Ty->isFloatingPointTy()) {
      return SingleValue{APFloat(
          Ty->getFltSemantics(),
          MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue()))};
    } else if (Ty->isPointerTy()) {
      auto Addr =
          MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue());
      return SingleValue{lookupPointer(Addr.getZExtValue())};
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
      llvm_unreachable("Unsupported mem store");
    }
  }
  void store(const AnyValue &P, uint32_t Alignment, const AnyValue &V, Type *Ty,
             bool IsVolatile) {
    // errs() << "Store " << P << ' ' << V << '\n';
    if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
      if (auto MO = PV->Obj.lock()) {
        auto Size = DL.getTypeStoreSize(Ty).getFixedValue();
        if (IsVolatile)
          volatileStore(PV->Address, Size, Alignment);
        MO->verifyMemAccess(PV->Offset, Size, Alignment);
        return store(*MO, PV->Offset, V, Ty);
      }
      ImmUBReporter() << "load from invalid pointer";
    }
    ImmUBReporter() << "store to poison pointer";
  }
  AnyValue load(const AnyValue &P, uint32_t Alignment, Type *Ty,
                bool IsVolatile) {
    if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
      if (auto MO = PV->Obj.lock()) {
        auto Size = DL.getTypeStoreSize(Ty).getFixedValue();
        if (IsVolatile)
          volatileLoad(PV->Address, Size, Alignment);
        MO->verifyMemAccess(PV->Offset, Size, Alignment);
        return load(*MO, PV->Offset, Ty);
      }
      ImmUBReporter() << "load from invalid pointer";
    }
    ImmUBReporter() << "load from poison pointer";
  }

public:
  explicit UBAwareInterpreter(Module &M)
      : Ctx(M.getContext()), M(M), DL(M.getDataLayout()),
        TLI(Triple{M.getTargetTriple()}) {
    assert(DL.isLittleEndian());
    static_assert(sys::IsLittleEndianHost);
    NullPtr = MemObject::create("null", false, 0U, 1U);
    assert(NullPtr->address() == 0);
    for (auto &GV : M.globals()) {
      if (!GV.hasExactDefinition())
        continue;
      GlobalValues.insert({&GV, std::move(MemObject::create(
                                    GV.getName().str(), false,
                                    DL.getTypeAllocSize(GV.getValueType()),
                                    DL.getPreferredAlign(&GV).value()))});
    }
    for (auto &GV : M.globals()) {
      if (!GV.hasExactDefinition())
        continue;
      if (GV.hasInitializer())
        store(*GlobalValues.at(&GV), 0U,
              convertFromConstant(GV.getInitializer()), GV.getValueType());
    }
    for (auto &F : M) {
      GlobalValues.insert(
          {&F, std::move(MemObject::create(F.getName().str(), false, 0, 16))});
      ValidCallees.insert({GlobalValues.at(&F)->address(), &F});
      for (auto &BB : F) {
        if (BB.isEntryBlock())
          continue;
        BlockTargets.insert(
            {&BB,
             std::move(MemObject::create(
                 F.getName().str() + ":" + getValueName(&BB), true, 0, 16))});
        ValidBlockTargets.insert({GlobalValues.at(&F)->address(), &BB});
      }
    }
    // Expand constexprs
    while (true) {
      bool Changed = false;
      for (auto &F : M) {
        for (auto &BB : F) {
          for (auto &I : BB) {
            for (auto &U : I.operands()) {
              if (auto *CE = dyn_cast<ConstantExpr>(U.get())) {
                auto *Inst = CE->getAsInstruction();
                if (auto *PHI = dyn_cast<PHINode>(&I))
                  Inst->insertBefore(PHI->getIncomingBlock(U)->getTerminator());
                else
                  Inst->insertBefore(&I);
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
  }

  bool addValue(Instruction &I, AnyValue Val) {
    if (I.getType()->isVoidTy())
      return true;
    if (Verbose)
      errs() << " -> " << Val;
    CurrentFrame->ValueMap[&I] = std::move(Val);
    return true;
  }
  bool jumpTo(BasicBlock *To) {
    if (Verbose) {
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
      if (Verbose)
        K->printAsOperand(errs() << "\n    phi ");
      addValue(*K, std::move(V));
    }
    return false;
  }
  AnyValue getValue(Value *V) {
    if (auto *C = dyn_cast<Constant>(V))
      return convertFromConstant(C);
    if (isa<MetadataAsValue>(V))
      return none();
    return CurrentFrame->ValueMap.at(V);
  }
  std::optional<APInt> getInt(const SingleValue &SV) {
    if (auto *C = std::get_if<APInt>(&SV))
      return *C;
    return std::nullopt;
  }
  std::optional<APInt> getInt(Value *V) {
    return getInt(getValue(V).getSingleValue());
  }
  APInt getIntNonPoison(Value *V) {
    if (auto Res = getInt(getValue(V).getSingleValue()))
      return *Res;
    ImmUBReporter() << "Expect a non-poison integer";
  }
  enum class BooleanVal { Poison, False, True };
  BooleanVal getBoolean(const SingleValue &SV) {
    if (isPoison(SV))
      return BooleanVal::Poison;
    return std::get<APInt>(SV).getBoolValue() ? BooleanVal::True
                                              : BooleanVal::False;
  }
  bool getBooleanNonPoison(const SingleValue &SV) {
    auto BV = getBoolean(SV);
    if (BV == BooleanVal::Poison)
      ImmUBReporter() << "expect a poison value";
    return BV == BooleanVal::True;
  }
  BooleanVal getBoolean(Value *V) {
    return getBoolean(getValue(V).getSingleValue());
  }
  char *getRawPtr(const SingleValue &SV) {
    auto Ptr = std::get<Pointer>(SV);
    if (auto MO = Ptr.Obj.lock())
      return MO->rawPointer() + Ptr.Offset;
    ImmUBReporter() << "dangling pointer";
  }
  char *getRawPtr(const SingleValue &SV, size_t Size, size_t Alignment,
                  bool IsStore, bool IsVolatile) {
    auto Ptr = std::get<Pointer>(SV);
    if (auto MO = Ptr.Obj.lock()) {
      if (IsVolatile) {
        if (IsStore)
          volatileStore(Ptr.Address, Size, Alignment);
        else
          volatileLoad(Ptr.Address, Size, Alignment);
      }
      MO->verifyMemAccess(Ptr.Offset, Size, Alignment);
      return MO->rawPointer() + Ptr.Offset;
    }
    ImmUBReporter() << "dangling pointer";
  }
  DenormalMode getCurrentDenormalMode(Type *Ty) {
    if (Ty->isFPOrFPVectorTy() && CurrentFrame) {
      return CurrentFrame->BB->getParent()->getDenormalMode(
          Ty->getScalarType()->getFltSemantics());
    }
    return DenormalMode::getDefault();
  }

  // TODO: checksum for volatile ops
  void volatileLoad(size_t Addr, size_t Size, size_t Alignment) {}
  void volatileStore(size_t Addr, size_t Size, size_t Alignment) {}

  bool visitAllocaInst(AllocaInst &AI) {
    assert(!AI.isArrayAllocation() && "VLA is not implemented yet.");
    auto Obj = MemObject::create(getValueName(&AI), true,
                                 DL.getTypeAllocSize(AI.getAllocatedType()),
                                 AI.getPointerAlignment(DL).value());
    Pointer Ptr{Obj, 0U};
    CurrentFrame->Allocas.push_back(std::move(Obj));
    return addValue(AI, SingleValue{std::move(Ptr)});
  }
  AnyValue visitBinOp(
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
        Res.push_back(AnyValue{
            FnPoison(LHS.getSingleValueAt(I), RHS.getSingleValueAt(I))});
      return std::move(Res);
    }
    return AnyValue{FnPoison(LHS.getSingleValue(), RHS.getSingleValue())};
  }
  bool visitBinOp(Instruction &I,
                  const function_ref<SingleValue(const SingleValue &,
                                                 const SingleValue &)> &Fn) {
    return addValue(I, visitBinOp(I.getType(), getValue(I.getOperand(0)),
                                  getValue(I.getOperand(1)), Fn));
  }
  AnyValue visitUnOp(Type *RetTy, const AnyValue &Val,
                     const function_ref<SingleValue(const SingleValue &)> &Fn,
                     bool PropagatesPoison = true) {
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
  bool visitUnOp(Instruction &I,
                 const function_ref<SingleValue(const SingleValue &)> &Fn,
                 bool PropagatesPoison = true) {
    return addValue(I, visitUnOp(I.getType(), getValue(I.getOperand(0)), Fn,
                                 PropagatesPoison));
  }
  AnyValue visitTriOp(
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

  bool visitICmpInst(ICmpInst &I) {
    auto ICmp = [&I](const SingleValue &LHS,
                     const SingleValue &RHS) -> SingleValue {
      const auto &LHSC = std::get<APInt>(LHS);
      const auto &RHSC = std::get<APInt>(RHS);
      if (I.hasSameSign()) {
        if (LHSC.isNonNegative() != RHSC.isNonNegative())
          return poison();
      }
      return boolean(ICmpInst::compare(LHSC, RHSC, I.getPredicate()));
    };
    auto ICmpPtr = [&](const SingleValue &LHS,
                       const SingleValue &RHS) -> SingleValue {
      if (std::holds_alternative<Pointer>(LHS)) {
        assert(std::holds_alternative<Pointer>(RHS));
        uint32_t BitWidth = DL.getPointerSizeInBits();
        return ICmp(APInt(BitWidth, std::get<Pointer>(LHS).Address),
                    APInt(BitWidth, std::get<Pointer>(RHS).Address));
      }
      return ICmp(LHS, RHS);
    };
    return visitBinOp(I, ICmpPtr);
  }
  AnyValue visitIntBinOp(
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
  AnyValue visitFPBinOp(Type *RetTy, FastMathFlags FMF, const AnyValue &LHS,
                        const AnyValue &RHS,
                        const function_ref<std::optional<APFloat>(
                            const APFloat &, const APFloat &)> &Fn) {
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
  bool visitIntBinOp(Instruction &I, const function_ref<std::optional<APInt>(
                                         const APInt &, const APInt &)> &Fn) {
    return addValue(I, visitIntBinOp(I.getType(), getValue(I.getOperand(0)),
                                     getValue(I.getOperand(1)), Fn));
  }
  bool visitFPBinOp(Instruction &I,
                    const function_ref<std::optional<APFloat>(
                        const APFloat &, const APFloat &)> &Fn) {
    return addValue(I, visitFPBinOp(I.getType(), I.getFastMathFlags(),
                                    getValue(I.getOperand(0)),
                                    getValue(I.getOperand(1)), Fn));
  }
  AnyValue visitIntTriOp(
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
  AnyValue
  visitFPTriOp(Type *RetTy, FastMathFlags FMF, const AnyValue &X,
               const AnyValue &Y, const AnyValue &Z,
               const function_ref<std::optional<APFloat>(
                   const APFloat &, const APFloat &, const APFloat &)> &Fn) {
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
  bool visitAnd(BinaryOperator &I) {
    return visitIntBinOp(
        I, [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return LHS & RHS;
        });
  }
  bool visitXor(BinaryOperator &I) {
    return visitIntBinOp(
        I, [](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          return LHS ^ RHS;
        });
  }
  bool visitOr(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (cast<PossiblyDisjointInst>(I).isDisjoint() && LHS.intersects(RHS))
            return std::nullopt;
          return LHS | RHS;
        });
  }
  bool visitShl(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.uge(LHS.getBitWidth()))
            return std::nullopt;
          if (I.hasNoSignedWrap() && RHS.uge(LHS.getNumSignBits()))
            return std::nullopt;
          if (I.hasNoUnsignedWrap() && RHS.ugt(LHS.countl_zero()))
            return std::nullopt;
          return LHS.shl(RHS);
        });
  }
  bool visitLShr(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.uge(cast<PossiblyExactOperator>(I).isExact()
                          ? LHS.countr_zero() + 1
                          : LHS.getBitWidth()))
            return std::nullopt;
          return LHS.lshr(RHS);
        });
  }
  bool visitAShr(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.uge(cast<PossiblyExactOperator>(I).isExact()
                          ? LHS.countr_zero() + 1
                          : LHS.getBitWidth()))
            return std::nullopt;
          return LHS.ashr(RHS);
        });
  }
  bool visitAdd(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          bool Overflow = false;
          auto Ret = LHS.uadd_ov(RHS, Overflow);
          if (I.hasNoUnsignedWrap() && Overflow)
            return std::nullopt;
          if (I.hasNoSignedWrap()) {
            (void)LHS.sadd_ov(RHS, Overflow);
            if (Overflow)
              return std::nullopt;
          }
          return Ret;
        });
  }
  bool visitSub(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          bool Overflow = false;
          auto Ret = LHS.usub_ov(RHS, Overflow);
          if (I.hasNoUnsignedWrap() && Overflow)
            return std::nullopt;
          if (I.hasNoSignedWrap()) {
            (void)LHS.ssub_ov(RHS, Overflow);
            if (Overflow)
              return std::nullopt;
          }
          return Ret;
        });
  }
  bool visitMul(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          bool Overflow = false;
          auto Ret = LHS.umul_ov(RHS, Overflow);
          if (I.hasNoUnsignedWrap() && Overflow)
            return std::nullopt;
          if (I.hasNoSignedWrap()) {
            (void)LHS.smul_ov(RHS, Overflow);
            if (Overflow)
              return std::nullopt;
          }
          return Ret;
        });
  }
  bool visitSDiv(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.isZero() || (LHS.isMinSignedValue() && RHS.isAllOnes()))
            return std::nullopt;
          APInt Q, R;
          APInt::sdivrem(LHS, RHS, Q, R);
          if (I.isExact() && !R.isZero())
            return std::nullopt;
          return Q;
        });
  }
  bool visitSRem(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.isZero())
            return std::nullopt;
          return LHS.srem(RHS);
        });
  }
  bool visitUDiv(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.isZero())
            return std::nullopt;
          APInt Q, R;
          APInt::udivrem(LHS, RHS, Q, R);
          if (I.isExact() && !R.isZero())
            return std::nullopt;
          return Q;
        });
  }
  bool visitURem(BinaryOperator &I) {
    return visitIntBinOp(
        I, [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
          if (RHS.isZero())
            return std::nullopt;
          return LHS.urem(RHS);
        });
  }
  AnyValue
  visitIntUnOp(Type *Ty, const AnyValue &Val,
               const function_ref<std::optional<APInt>(const APInt &)> &Fn) {
    return visitUnOp(Ty, Val, [&Fn](const SingleValue &V) -> SingleValue {
      auto &C = std::get<APInt>(V);
      if (auto Res = Fn(C))
        return SingleValue{*Res};
      return poison();
    });
  }
  bool
  visitIntUnOp(Instruction &I,
               const function_ref<std::optional<APInt>(const APInt &)> &Fn) {
    return addValue(I,
                    visitIntUnOp(I.getType(), getValue(I.getOperand(0)), Fn));
  }
  AnyValue
  visitFPUnOp(Type *RetTy, FastMathFlags FMF, const AnyValue &Val,
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
  bool
  visitFPUnOp(Instruction &I,
              const function_ref<std::optional<APFloat>(const APFloat &)> &Fn) {
    return addValue(I, visitFPUnOp(I.getType(), I.getFastMathFlags(),
                                   getValue(I.getOperand(0)), Fn));
  }
  bool visitTruncInst(TruncInst &Trunc) {
    uint32_t DestBW = Trunc.getDestTy()->getScalarSizeInBits();
    return visitIntUnOp(Trunc, [&](const APInt &C) -> std::optional<APInt> {
      if (Trunc.hasNoSignedWrap() && C.getSignificantBits() > DestBW)
        return std::nullopt;
      if (Trunc.hasNoUnsignedWrap() && C.getActiveBits() > DestBW)
        return std::nullopt;
      return C.trunc(DestBW);
    });
  }
  bool visitSExtInst(SExtInst &SExt) {
    uint32_t DestBW = SExt.getDestTy()->getScalarSizeInBits();
    return visitIntUnOp(SExt, [&](const APInt &C) -> std::optional<APInt> {
      return C.sext(DestBW);
    });
  }
  bool visitZExtInst(ZExtInst &ZExt) {
    uint32_t DestBW = ZExt.getDestTy()->getScalarSizeInBits();
    bool IsNNeg = ZExt.hasNonNeg();
    return visitIntUnOp(ZExt, [&](const APInt &C) -> std::optional<APInt> {
      if (IsNNeg && C.isNegative())
        return std::nullopt;
      return C.zext(DestBW);
    });
  }
  bool fpCast(Instruction &I) {
    auto &DstSem = I.getType()->getScalarType()->getFltSemantics();
    return visitFPUnOp(I, [&](const APFloat &C) -> std::optional<APFloat> {
      auto V = C;
      bool LosesInfo;
      V.convert(DstSem, APFloat::rmNearestTiesToEven, &LosesInfo);
      return V;
    });
  }
  bool visitFPExtInst(FPExtInst &FPExt) { return fpCast(FPExt); }
  bool visitFPTruncInst(FPTruncInst &FPTrunc) { return fpCast(FPTrunc); }
  bool visitIntToFPInst(Instruction &I, bool IsSigned) {
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
  bool visitSIToFPInst(SIToFPInst &I) { return visitIntToFPInst(I, true); }
  bool visitUIToFPInst(UIToFPInst &I) { return visitIntToFPInst(I, false); }
  bool visitFPToIntInst(Instruction &I, bool IsSigned) {
    auto BitWidth = I.getType()->getScalarSizeInBits();
    return visitUnOp(I, [&](const SingleValue &C) -> SingleValue {
      if (isPoison(C))
        return poison();
      auto &CFP = std::get<APFloat>(C);
      APSInt V(BitWidth, !IsSigned);
      bool IsExact;
      auto Status =
          CFP.convertToInteger(V, APFloat::rmNearestTiesToEven, &IsExact);
      if (Status == APFloat::opOK || Status == APFloat::opInexact)
        return V;
      return poison();
    });
  }
  bool visitFPToSIInst(FPToSIInst &I) { return visitFPToIntInst(I, true); }
  bool visitFPToUIInst(FPToUIInst &I) { return visitFPToIntInst(I, false); }
  bool visitFNeg(UnaryOperator &I) {
    return visitFPUnOp(I, [](const APFloat &X) { return -X; });
  }
  bool visitFAdd(BinaryOperator &I) {
    return visitFPBinOp(
        I, [](const APFloat &X, const APFloat &Y) { return X + Y; });
  }
  bool visitFSub(BinaryOperator &I) {
    return visitFPBinOp(
        I, [](const APFloat &X, const APFloat &Y) { return X - Y; });
  }
  bool visitFMul(BinaryOperator &I) {
    return visitFPBinOp(
        I, [](const APFloat &X, const APFloat &Y) { return X * Y; });
  }
  bool visitFDiv(BinaryOperator &I) {
    return visitFPBinOp(
        I, [](const APFloat &X, const APFloat &Y) { return X / Y; });
  }
  bool visitFRem(BinaryOperator &I) {
    return visitFPBinOp(I, [](const APFloat &X, const APFloat &Y) {
      auto Z = X;
      Z.mod(Y);
      return Z;
    });
  }
  bool visitFCmpInst(FCmpInst &FCmp) {
    auto FMF = FCmp.getFastMathFlags();
    return visitBinOp(
        FCmp,
        [&](const SingleValue &LHS, const SingleValue &RHS) -> SingleValue {
          if (isPoison(LHS) || isPoison(RHS))
            return poison();
          auto &LHSC = std::get<APFloat>(LHS);
          auto &RHSC = std::get<APFloat>(RHS);
          if (isPoison(LHSC, FMF) || isPoison(RHSC, FMF))
            return poison();
          return boolean(FCmpInst::compare(LHSC, RHSC, FCmp.getPredicate()));
        });
  }
  AnyValue freezeValue(const AnyValue &Val, Type *Ty) {
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
  bool visitFreezeInst(FreezeInst &Freeze) {
    return addValue(
        Freeze, freezeValue(getValue(Freeze.getOperand(0)), Freeze.getType()));
  }
  bool visitSelect(SelectInst &SI) {
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
  bool visitBranchInst(BranchInst &BI) {
    if (BI.isConditional()) {
      switch (getBoolean(BI.getCondition())) {
      case BooleanVal::True:
        return jumpTo(BI.getSuccessor(0));
      case BooleanVal::False:
        return jumpTo(BI.getSuccessor(1));
      case BooleanVal::Poison:
        ImmUBReporter() << "Branch on poison";
      }
    }
    return jumpTo(BI.getSuccessor(0));
  }
  bool visitIndirectBrInst(IndirectBrInst &IBI) {
    auto Ptr = getValue(IBI.getAddress()).getSingleValue();
    if (isPoison(Ptr))
      ImmUBReporter() << "Indirect branch on poison";
    auto It = ValidBlockTargets.find(std::get<Pointer>(Ptr).Address);
    if (It == ValidBlockTargets.end())
      ImmUBReporter() << "Indirect branch on invalid target BB";
    auto DestBB = It->second;
    for (uint32_t I = 0, E = IBI.getNumDestinations(); I != E; ++I) {
      if (IBI.getDestination(I) == DestBB)
        return jumpTo(DestBB);
    }
    ImmUBReporter() << "Indirect branch on unlisted target BB "
                    << *BlockAddress::get(DestBB);
  }
  SingleValue computeGEP(const SingleValue &Base, const APInt &Offset,
                         bool InBounds) {
    if (isPoison(Base))
      return Base;
    auto &Ptr = std::get<Pointer>(Base);
    return offsetPointer(Ptr, Offset.getSExtValue(), InBounds);
  }
  bool visitGetElementPtrInst(GetElementPtrInst &GEP) {
    // TODO: handle nuw/nusw/inrange
    uint32_t BitWidth = DL.getIndexSizeInBits(0);
    APInt Offset = APInt::getZero(BitWidth);
    SmallMapVector<Value *, APInt, 4> VarOffsets;
    if (!GEP.collectOffset(DL, BitWidth, VarOffsets, Offset))
      llvm_unreachable("Unsupported GEP");
    bool InBounds = GEP.isInBounds();
    if (auto *VTy = dyn_cast<VectorType>(GEP.getType())) {
      uint32_t Len = getVectorLength(VTy);
      AnyValue Res = getValue(GEP.getPointerOperand());
      for (auto &[K, V] : VarOffsets) {
        auto KV = getValue(K);
        for (uint32_t I = 0; I != Len; ++I) {
          if (auto Idx = getInt(KV.getSingleValueAt(I)))
            Res.getSingleValueAt(I) =
                computeGEP(Res.getSingleValueAt(I), *Idx * V, InBounds);
          else
            Res.getSingleValueAt(I) = poison();
        }
      }
      for (uint32_t I = 0; I != Len; ++I) {
        Res.getSingleValueAt(I) =
            computeGEP(Res.getSingleValueAt(I), Offset, InBounds);
      }
      return addValue(GEP, std::move(Res));
    }

    SingleValue Res = getValue(GEP.getPointerOperand()).getSingleValue();
    if (isPoison(Res))
      return addValue(GEP, Res);
    for (auto &[K, V] : VarOffsets) {
      if (auto Idx = getInt(K))
        Res = computeGEP(Res, *Idx * V, InBounds);
      else
        return addValue(GEP, poison());
    }
    return addValue(GEP, computeGEP(Res, Offset, InBounds));
  }
  bool visitExtractValueInst(ExtractValueInst &EVI) {
    AnyValue Res = getValue(EVI.getAggregateOperand());
    for (auto Idx : EVI.indices()) {
      auto Sub = std::move(Res.getValueArray().at(Idx));
      Res = std::move(Sub);
    }
    return addValue(EVI, std::move(Res));
  }
  bool visitInsertValueInst(InsertValueInst &IVI) {
    auto Res = getValue(IVI.getAggregateOperand());
    auto Val = getValue(IVI.getInsertedValueOperand());
    AnyValue *Pos = &Res;
    for (auto Idx : IVI.indices())
      Pos = &Pos->getValueArray().at(Idx);
    *Pos = std::move(Val);
    return addValue(IVI, std::move(Res));
  }
  bool visitInsertElementInst(InsertElementInst &IEI) {
    auto Res = getValue(IEI.getOperand(0));
    auto Insert = getValue(IEI.getOperand(1));
    auto Idx = getInt(IEI.getOperand(2));
    if (!Idx.has_value() || Idx->uge(Res.getValueArray().size()))
      return addValue(IEI, getPoison(IEI.getType()));
    Res.getValueArray().at(Idx->getZExtValue()) = std::move(Insert);
    return addValue(IEI, std::move(Res));
  }
  bool visitExtractElementInst(ExtractElementInst &EEI) {
    auto Src = getValue(EEI.getOperand(0));
    auto Idx = getInt(EEI.getOperand(1));
    if (!Idx.has_value() || Idx->uge(Src.getValueArray().size()))
      return addValue(EEI, getPoison(EEI.getType()));
    return addValue(EEI,
                    std::move(Src.getValueArray().at(Idx->getZExtValue())));
  }
  bool visitShuffleVectorInst(ShuffleVectorInst &SVI) {
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
      else if (Idx < Size)
        PickedValues.push_back(LHS.getSingleValueAt(Idx));
      else if (RHSIsPoison)
        PickedValues.push_back(getPoison(SVI.getType()->getScalarType()));
      else
        PickedValues.push_back(RHS.getSingleValueAt(Idx - Size));
    }
    return addValue(SVI, std::move(PickedValues));
  }
  bool visitStoreInst(StoreInst &SI) {
    store(getValue(SI.getPointerOperand()), SI.getAlign().value(),
          getValue(SI.getValueOperand()), SI.getValueOperand()->getType(),
          SI.isVolatile());
    return true;
  }
  void handleRangeMetadata(AnyValue &V, Instruction &I) {
    if (auto *MD = I.getMetadata(LLVMContext::MD_range)) {
      auto CR = getConstantRangeFromMetadata(*MD);
      postProcess(V, [&](SingleValue &SV) { handleRange(SV, CR); });
    }
  }
  bool visitLoadInst(LoadInst &LI) {
    auto RetVal = load(getValue(LI.getPointerOperand()), LI.getAlign().value(),
                       LI.getType(), LI.isVolatile());
    if (LI.getType()->isPointerTy()) {
      if (LI.hasMetadata(LLVMContext::MD_nonnull))
        postProcess(RetVal, handleNonNull);
      if (auto *MD = LI.getMetadata(LLVMContext::MD_dereferenceable)) {
        size_t Deref =
            mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
        postProcess(RetVal, [Deref](SingleValue &SV) {
          handleDereferenceable(SV, Deref, false);
        });
      }
      if (auto *MD = LI.getMetadata(LLVMContext::MD_dereferenceable_or_null)) {
        size_t Deref =
            mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
        postProcess(RetVal, [Deref](SingleValue &SV) {
          handleDereferenceable(SV, Deref, true);
        });
      }
      if (auto *MD = LI.getMetadata(LLVMContext::MD_align)) {
        size_t Align =
            mdconst::extract<ConstantInt>(MD->getOperand(0))->getLimitedValue();
        postProcess(RetVal,
                    [Align](SingleValue &SV) { handleAlign(SV, Align); });
      }
    }
    handleRangeMetadata(RetVal, LI);
    if (LI.hasMetadata(LLVMContext::MD_noundef))
      postProcess(RetVal, handleNoUndef);
    return addValue(LI, std::move(RetVal));
  }
  void writeBits(APInt &Dst, uint32_t &Offset, const APInt &Src) {
    Dst.insertBits(Src, Offset);
    Offset += Src.getBitWidth();
  }
  void toBits(APInt &Bits, APInt &PoisonBits, uint32_t &Offset,
              const AnyValue &Val, Type *Ty) {
    if (Val.isSingleValue() && isPoison(Val.getSingleValue())) {
      unsigned BW = DL.getTypeSizeInBits(Ty).getFixedValue();
      PoisonBits.setBits(Offset, Offset + BW);
      return;
    }
    if (Ty->isIntegerTy()) {
      writeBits(Bits, Offset, std::get<APInt>(Val.getSingleValue()));
    } else if (Ty->isFloatingPointTy()) {
      writeBits(Bits, Offset,
                std::get<APFloat>(Val.getSingleValue()).bitcastToAPInt());
    } else if (Ty->isPointerTy()) {
      writeBits(Bits, Offset,
                APInt(DL.getPointerSizeInBits(),
                      std::get<Pointer>(Val.getSingleValue()).Address));
    } else if (auto *VTy = dyn_cast<VectorType>(Ty)) {
      Type *EltTy = VTy->getElementType();
      for (auto &Sub : Val.getValueArray())
        toBits(Bits, PoisonBits, Offset, Sub, EltTy);
    } else {
      errs() << "Unrecognized type " << *Ty << '\n';
      llvm_unreachable("Not implemented");
    }
  }
  bool visitIntToPtr(IntToPtrInst &I) {
    return visitUnOp(I, [](const SingleValue &V) -> SingleValue {
      if (isPoison(V))
        return poison();
      return lookupPointer(std::get<APInt>(V).getZExtValue());
    });
  }
  bool visitPtrToInt(PtrToIntInst &I) {
    return visitUnOp(I, [&](const SingleValue &V) -> SingleValue {
      if (isPoison(V))
        return poison();
      return APInt(I.getType()->getScalarSizeInBits(),
                   std::get<Pointer>(V).Address);
    });
  }
  APInt readBits(const APInt &Src, uint32_t &Offset, uint32_t Width) {
    auto Res = Src.extractBits(Width, Offset);
    Offset += Width;
    return Res;
  }
  AnyValue fromBits(const APInt &Bits, const APInt &PoisonBits,
                    uint32_t &Offset, Type *Ty) {
    if (Ty->isIntOrPtrTy() || Ty->isFloatingPointTy()) {
      if (APInt::getBitsSet(Bits.getBitWidth(), Offset,
                            Offset + Ty->getScalarSizeInBits())
              .intersects(PoisonBits))
        return getPoison(Ty);
    }
    if (Ty->isIntegerTy()) {
      return SingleValue{readBits(Bits, Offset, Ty->getIntegerBitWidth())};
    } else if (Ty->isFloatingPointTy()) {
      return SingleValue{
          APFloat(Ty->getFltSemantics(),
                  readBits(Bits, Offset, Ty->getScalarSizeInBits()))};
    } else if (Ty->isPointerTy()) {
      return SingleValue{lookupPointer(
          readBits(Bits, Offset, DL.getPointerSizeInBits()).getZExtValue())};
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
      llvm_unreachable("Not implemented");
    }
  }
  bool visitBitCastInst(BitCastInst &BCI) {
    APInt Bits =
        APInt::getZero(DL.getTypeSizeInBits(BCI.getType()).getFixedValue());
    APInt PoisonBits = Bits;
    uint32_t Offset = 0;
    toBits(Bits, PoisonBits, Offset, getValue(BCI.getOperand(0)),
           BCI.getOperand(0)->getType());
    Offset = 0;
    return addValue(BCI, fromBits(Bits, PoisonBits, Offset, BCI.getType()));
  }
  std::string getValueName(Value *V) {
    std::string Str;
    raw_string_ostream Out(Str);
    V->printAsOperand(Out);
    return Str;
  }
  AnyValue handleCall(CallBase &CB) {
    SmallVector<AnyValue> Args;
    SmallVector<std::shared_ptr<MemObject>> ByValTempObjects;
    bool HandleParamAttr =
        !isa<IntrinsicInst>(CB) || !IgnoreParamAttrsOnIntrinsic;
    for (const auto &[Idx, Arg] : enumerate(CB.args())) {
      auto ArgVal = getValue(Arg);

      if (CB.isByValArgument(Idx)) {
        auto *Ty = CB.getParamByValType(Idx);
        auto TmpMO = MemObject::create(getValueName(Arg.get()), true,
                                       DL.getTypeAllocSize(Ty),
                                       DL.getPrefTypeAlign(Ty).value());
        memcpy(TmpMO->rawPointer(), getRawPtr(ArgVal.getSingleValue()),
               DL.getTypeStoreSize(Ty));
        ArgVal = SingleValue{Pointer{TmpMO, 0}};
        ByValTempObjects.push_back(std::move(TmpMO));
      }

      if (HandleParamAttr)
        postProcessAttr(ArgVal, CB.getParamAttributes(Idx));
      Args.push_back(std::move(ArgVal));
    }
    FastMathFlags FMF;
    if (auto *FPOp = dyn_cast<FPMathOperator>(&CB))
      FMF = FPOp->getFastMathFlags();
    auto *CalledFunc = CB.getCalledOperand();
    Function *Callee = dyn_cast<Function>(CalledFunc);
    if (!Callee) {
      auto Addr = getValue(CalledFunc).getSingleValue();
      if (isPoison(Addr))
        ImmUBReporter() << "Call with poison callee";
      auto FuncAddr = std::get<Pointer>(Addr).Address;
      if (auto It = ValidCallees.find(FuncAddr); It != ValidCallees.end())
        Callee = It->second;
      else
        ImmUBReporter() << "Call with invalid callee";
    }
    auto RetVal = call(Callee, FMF, Args);
    handleRangeMetadata(RetVal, CB);
    postProcessAttr(RetVal, CB.getRetAttributes());
    return std::move(RetVal);
  }
  bool visitCallInst(CallInst &CI) { return addValue(CI, handleCall(CI)); }
  bool visitReturnInst(ReturnInst &RI) {
    if (auto *RV = RI.getReturnValue())
      CurrentFrame->RetVal = getValue(RV);
    else
      CurrentFrame->RetVal = none();
    return false;
  }
  bool visitUnreachableInst(UnreachableInst &) {
    ImmUBReporter() << "Unreachable code";
  }
  bool visitSwitchInst(SwitchInst &SI) {
    auto Cond = getInt(SI.getCondition());
    if (!Cond)
      ImmUBReporter() << "Switch on poison condition";
    for (auto &Case : SI.cases()) {
      if (Case.getCaseValue()->getValue() == *Cond)
        return jumpTo(Case.getCaseSuccessor());
    }
    return jumpTo(SI.getDefaultDest());
  }
  bool visitInstruction(Instruction &I) {
    errs() << I << '\n';
    llvm_unreachable("Unsupported inst");
  }

  AnyValue handleWithOverflow(
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
        auto [K, V] =
            FnPoison(LHS.getSingleValueAt(I), RHS.getSingleValueAt(I));
        Res.push_back(std::move(K));
        Overflow.push_back(std::move(V));
      }
      return std::vector<AnyValue>{std::move(Res), std::move(Overflow)};
    }
    auto [K, V] = FnPoison(LHS.getSingleValue(), RHS.getSingleValue());
    return std::vector<AnyValue>{std::move(K), std::move(V)};
  }

  AnyValue callIntrinsic(Function *Func, FastMathFlags FMF,
                         SmallVectorImpl<AnyValue> &Args) {
    auto IID = Func->getIntrinsicID();
    Type *RetTy = Func->getReturnType();
    switch (IID) {
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
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
        ImmUBReporter() << "memcpy with poison size";
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
        ImmUBReporter() << "memcpy with poison size";
      if (Size->isZero())
        return none();
      auto WriteSize = Size->getZExtValue();
      bool IsVolatile = getBooleanNonPoison(Args[3].getSingleValue());
      auto Dst =
          getRawPtr(Args[0].getSingleValue(), WriteSize, 1U, true, IsVolatile);
      auto Val = getInt(Args[1].getSingleValue());
      if (!Val)
        ImmUBReporter() << "memset with poison value";
      std::memset(Dst, Val->getZExtValue(), WriteSize);
      return none();
    }
    case Intrinsic::ctlz:
    case Intrinsic::cttz: {
      bool IsZeroPoison = getBooleanNonPoison(Args[1].getSingleValue());
      return visitIntUnOp(
          RetTy, Args[0], [&](const APInt &V) -> std::optional<APInt> {
            if (IsZeroPoison && V.isZero())
              return std::nullopt;
            return APInt(V.getBitWidth(), IID == Intrinsic::ctlz
                                              ? V.countl_zero()
                                              : V.countr_zero());
          });
    }
    case Intrinsic::abs: {
      bool IsIntMinPoison = getBooleanNonPoison(Args[1].getSingleValue());
      return visitIntUnOp(RetTy, Args[0],
                          [&](const APInt &V) -> std::optional<APInt> {
                            if (IsIntMinPoison && V.isMinSignedValue())
                              return std::nullopt;
                            return V.abs();
                          });
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
    case Intrinsic::scmp:
      return visitIntBinOp(
          RetTy, Args[0], Args[1],
          [&](const APInt &LHS, const APInt &RHS) -> std::optional<APInt> {
            uint32_t BitWidth = LHS.getBitWidth();
            if (LHS == RHS)
              return APInt::getZero(BitWidth);
            return (IID == Intrinsic::ucmp ? LHS.ult(RHS) : LHS.slt(RHS))
                       ? APInt::getAllOnes(BitWidth)
                       : APInt(BitWidth, 1);
          });
    case Intrinsic::assume: {
      // TODO: handle operand bundles
      switch (getBoolean(Args[0].getSingleValue())) {
      case BooleanVal::Poison:
        ImmUBReporter() << "assumption violation (poison)";
      case BooleanVal::False:
        ImmUBReporter() << "assumption violation (false)";
      case BooleanVal::True:
        return none();
      }
    }
    case Intrinsic::sadd_with_overflow:
    case Intrinsic::ssub_with_overflow:
    case Intrinsic::smul_with_overflow:
    case Intrinsic::uadd_with_overflow:
    case Intrinsic::usub_with_overflow:
    case Intrinsic::umul_with_overflow:
      return handleWithOverflow(
          Func->getArg(0)->getType(), Args[0], Args[1],
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
      return Res.has_value()
                 ? handleFPVal(std::move(*Res), FMF, Denormal.Output)
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
                             uint32_t LShrAmt =
                                 IsFShr ? ShAmt : BitWidth - ShAmt;
                             uint32_t ShlAmt =
                                 !IsFShr ? ShAmt : BitWidth - ShAmt;
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
                            Res.fusedMultiplyAdd(
                                Y, Z, RoundingMode::NearestTiesToEven);
                            return Res;
                          });
    }
    case Intrinsic::fmuladd: {
      return visitFPTriOp(
          RetTy, FMF, Args[0], Args[1], Args[2],
          [](const APFloat &X, const APFloat &Y,
             const APFloat &Z) -> std::optional<APFloat> { return X * Y + Z; });
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

    default:
      break;
    }
    errs() << "Intrinsic: " << Func->getName() << '\n';
    llvm_unreachable("Unsupported intrinsic");
  }
  AnyValue callLibFunc(LibFunc Func, Function *FuncDecl,
                       SmallVectorImpl<AnyValue> &Args) {
    switch (Func) {
    case LibFunc_printf: {
      if (Args.size() == 2) {
        auto Val = getInt(Args[1].getSingleValue());
        if (!Val.has_value())
          ImmUBReporter() << "print a poison value";
        if (Verbose)
          errs() << "\n    Printf: ";
        int Ret =
            printf(getRawPtr(Args[0].getSingleValue()), Val->getSExtValue());
        if (Verbose)
          errs() << "  ";
        return SingleValue{APInt(32, Ret)};
      }
      break;
    }
    default:
      break;
    }
    errs() << "Libcall: " << FuncDecl->getName() << '\n';
    llvm_unreachable("Unsupported libcall");
  }
  AnyValue call(Function *Func, FastMathFlags FMF,
                SmallVectorImpl<AnyValue> &Args) {
    auto FnAttrs = Func->getAttributes();
    for (const auto &[Idx, Param] : enumerate(Func->args()))
      postProcessAttr(Args[Idx], FnAttrs.getParamAttrs(Idx));

    if (Func->isIntrinsic()) {
      return callIntrinsic(Func, FMF, Args);
    } else {
      LibFunc F;
      if (TLI.getLibFunc(*Func, F))
        return callLibFunc(F, Func, Args);
    }

    if (!Func->hasExactDefinition()) {
      errs() << "Do not how to handle " << *Func << '\n';
      std::exit(EXIT_FAILURE);
    }

    Frame CallFrame;
    auto Scope = llvm::make_scope_exit(
        [this, Frame = CurrentFrame] { CurrentFrame = Frame; });
    CurrentFrame = &CallFrame;
    for (auto &Param : Func->args())
      CallFrame.ValueMap[&Param] = std::move(Args[Param.getArgNo()]);

    if (Verbose) {
      errs() << "\n\nEntering function " << Func->getName() << '\n';
    }
    CallFrame.BB = &Func->getEntryBlock();
    CallFrame.PC = CallFrame.BB->begin();
    while (!CallFrame.RetVal.has_value()) {
      if (Verbose)
        errs() << *CallFrame.PC;
      if (visit(*CallFrame.PC))
        ++CallFrame.PC;
      if (Verbose)
        errs() << '\n';
    }

    auto RetVal = std::move(*CallFrame.RetVal);
    if (!Func->getReturnType()->isVoidTy())
      postProcessAttr(RetVal, Func->getAttributes().getRetAttrs());

    if (Verbose) {
      errs() << "Exiting function " << Func->getName() << '\n';
    }

    return RetVal;
  }

  int32_t runMain() {
    auto *Entry = M.getFunction("main");
    if (!Entry) {
      errs() << "Cannot find entry function `main`\n";
      return EXIT_FAILURE;
    }

    SmallVector<AnyValue> Args;
    Args.push_back(SingleValue{APInt::getZero(32)});
    Args.push_back(SingleValue{Pointer{NullPtr, 0U}});
    auto RetVal = call(Entry, FastMathFlags{}, Args);
    if (Entry->getReturnType()->isVoidTy())
      return EXIT_SUCCESS;
    if (isPoison(RetVal.getSingleValue()))
      ImmUBReporter() << "Return a poison value";
    return std::get<APInt>(RetVal.getSingleValue()).getSExtValue();
  }
};

int main(int argc, char **argv) {
  InitLLVM Init{argc, argv};
  cl::ParseCommandLineOptions(argc, argv, "llubi\n");

  LLVMContext Ctx;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(InputFile, Err, Ctx);
  if (!M) {
    Err.print(argv[0], errs());
    return EXIT_FAILURE;
  }

  UBAwareInterpreter Executor(*M);
  return Executor.runMain();
}
