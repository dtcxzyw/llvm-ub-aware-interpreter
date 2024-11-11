// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include <llvm-20/llvm/ADT/StringRef.h>
#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/MapVector.h>
#include <llvm/ADT/STLFunctionalExtras.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Dominators.h>
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

// TODO: handle llvm.lifetime.start/end and llvm.invariant.start.end
size_t AllocatedMem = 0;
constexpr size_t Padding = 16U;

class ImmUBReporter final {
  raw_ostream &Out;

public:
  ImmUBReporter() : Out(errs()) { Out << "UB triggered: "; }
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

class MemObject final {
  StringRef Name;
  bool IsLocal;
  size_t Address;
  SmallVector<std::byte, 16> Data;
  static std::map<size_t, MemObject *> AddressMap;

public:
  explicit MemObject(StringRef Name, bool IsLocal, size_t Size,
                     size_t Alignment)
      : Name(Name), IsLocal(IsLocal), Data(Size) {
    AllocatedMem = alignTo(AllocatedMem, Alignment);
    Address = AllocatedMem;
    AllocatedMem += Size + Padding;
    AddressMap.emplace(Address, this);
  }
  ~MemObject() { AddressMap.erase(Address); }
  void verifyMemAccess(size_t Offset, size_t AccessSize, size_t Alignment) {
    size_t NewAddr = Address + Offset;
    if (alignTo(NewAddr, Alignment) != NewAddr)
      ImmUBReporter() << "Unaligned mem op";
    if (Offset + AccessSize >= Data.size())
      ImmUBReporter() << "Out of bound mem op";
  }
  static std::shared_ptr<MemObject> create(StringRef Name, bool IsLocal,
                                           size_t Size, size_t Alignment) {
    return std::make_shared<MemObject>(Name, IsLocal, Size, Alignment);
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
          Word = (Word << 8) | static_cast<APInt::WordType>(ReadPos[ReadCnt]);
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
SingleValue boolean(bool Val) { return SingleValue{APInt(1, Val)}; }
SingleValue poison() { return std::monostate{}; }
SingleValue lookupPointer(size_t Addr) {
  // TODO
  return poison();
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
    Out << "Ptr { Obj = ";
    if (auto P = Ptr->Obj.lock())
      P->dumpRef(Out);
    else
      Out << "[dangling]";
    Out << ", Offset = " << Ptr->Offset << ", Addr = " << Ptr->Address
        << ", Bound = " << Ptr->Bound << '}';
    return Out;
  }
  return Out << "poison";
}

struct AnyValue final {
  std::variant<SingleValue, std::vector<AnyValue>, std::monostate> Val;

  AnyValue(SingleValue SV) : Val(std::move(SV)) {}
  AnyValue(std::vector<AnyValue> MV) : Val(std::move(MV)) {}
  AnyValue() = default;

  const SingleValue &getSingleValue() const {
    assert(std::holds_alternative<SingleValue>(Val));
    return std::get<SingleValue>(Val);
  }
  SingleValue &getSingleValue() {
    assert(std::holds_alternative<SingleValue>(Val));
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
  DenseMap<GlobalVariable *, std::shared_ptr<MemObject>> GlobalVariables;
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
      return std::vector<AnyValue>(getVectorLength(VTy));
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
    if (auto *GV = dyn_cast<GlobalVariable>(V)) {
      return AnyValue{Pointer{GlobalVariables.at(GV), 0}};
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
      llvm_unreachable("Not Implemented");
    } else if (auto *ArrTy = dyn_cast<ArrayType>(Ty)) {
      Type *EltTy = ArrTy->getElementType();
      auto Step = DL.getTypeStoreSize(EltTy);
      auto &MV = V.getValueArray();
      for (uint32_t I = 0, E = ArrTy->getNumElements(); I != E; ++I) {
        store(MO, Offset, MV[I], EltTy);
        Offset += Step;
      }
    } else {
      errs() << "Unsupproted type: " << *Ty << '\n';
      llvm_unreachable("Unsupported mem store");
    }
  }
  AnyValue load(const MemObject &MO, uint32_t Offset, Type *Ty) {
    if (Ty->isIntegerTy()) {
      return SingleValue{
          MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue())};
    } else if (Ty->isFloatingPointTy()) {
      return SingleValue{APFloat(
          Ty->getFltSemantics(),
          MO.load(Offset, DL.getTypeStoreSizeInBits(Ty).getFixedValue()))};
    } else if (Ty->isVectorTy()) {
      llvm_unreachable("Not Implemented");
    } else {
      errs() << "Unsupproted type: " << *Ty << '\n';
      llvm_unreachable("Unsupported mem store");
    }
  }
  void store(const AnyValue &P, uint32_t Alignment, const AnyValue &V,
             Type *Ty) {
    if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
      if (auto MO = PV->Obj.lock()) {
        MO->verifyMemAccess(PV->Offset, DL.getTypeStoreSize(Ty).getFixedValue(),
                            Alignment);
        return store(*MO, PV->Offset, V, Ty);
      }
      ImmUBReporter() << "load from invalid pointer";
    }
    ImmUBReporter() << "store to poison pointer";
  }
  AnyValue load(const AnyValue &P, uint32_t Alignment, Type *Ty) {
    if (auto *PV = std::get_if<Pointer>(&P.getSingleValue())) {
      if (auto MO = PV->Obj.lock()) {
        MO->verifyMemAccess(PV->Offset, DL.getTypeStoreSize(Ty).getFixedValue(),
                            Alignment);
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
      GlobalVariables.insert(
          {&GV, std::move(MemObject::create(
                    GV.getName(), false, DL.getTypeAllocSize(GV.getValueType()),
                    DL.getPreferredAlign(&GV).value()))});
    }
    for (auto &GV : M.globals()) {
      if (!GV.hasExactDefinition())
        continue;
      if (GV.hasInitializer())
        store(*GlobalVariables.at(&GV), 0U,
              convertFromConstant(GV.getInitializer()), GV.getValueType());
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
    errs() << I << " -> " << Val << '\n';
    CurrentFrame->ValueMap[&I] = std::move(Val);
    return true;
  }
  bool jumpTo(BasicBlock *To) {
    BasicBlock *From = CurrentFrame->BB;
    CurrentFrame->BB = To;
    CurrentFrame->PC = To->begin();
    SmallVector<std::pair<PHINode *, AnyValue>> IncomingValues;
    while (true) {
      if (auto *PHI = dyn_cast<PHINode>(CurrentFrame->PC)) {
        IncomingValues.emplace_back(
            PHI, getValue(PHI->getIncomingValueForBlock(From)));
        ++CurrentFrame->PC;
      } else
        break;
    }
    for (auto &[K, V] : IncomingValues)
      addValue(*K, std::move(V));
    return false;
  }
  AnyValue getValue(Value *V) {
    if (auto *C = dyn_cast<Constant>(V)) {
      errs() << "    Constant " << *C << " -> " << convertFromConstant(C)
             << '\n';
      return convertFromConstant(C);
    }
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
  enum class BooleanVal { Poison, False, True };
  BooleanVal getBoolean(const SingleValue &SV) {
    if (isPoison(SV))
      return BooleanVal::Poison;
    return std::get<APInt>(SV).getBoolValue() ? BooleanVal::True
                                              : BooleanVal::False;
  }
  BooleanVal getBoolean(Value *V) {
    return getBoolean(getValue(V).getSingleValue());
  }

  bool visitAllocaInst(AllocaInst &AI) {
    assert(!AI.isArrayAllocation() && "VLA is not implemented yet.");
    auto Obj = MemObject::create(AI.getName(), true,
                                 DL.getTypeAllocSize(AI.getAllocatedType()),
                                 AI.getPointerAlignment(DL).value());
    Pointer Ptr{Obj, 0U};
    CurrentFrame->Allocas.push_back(std::move(Obj));
    return addValue(AI, SingleValue{std::move(Ptr)});
  }
  bool visitBinOp(Instruction &I,
                  const function_ref<SingleValue(const SingleValue &,
                                                 const SingleValue &)> &Fn) {
    auto FnPoison = [&Fn](const SingleValue &LHS,
                          const SingleValue &RHS) -> SingleValue {
      if (isPoison(LHS) || isPoison(RHS))
        return poison();
      return Fn(LHS, RHS);
    };
    if (auto *VTy = dyn_cast<VectorType>(I.getType())) {
      uint32_t Len = getVectorLength(VTy);
      auto LHS = getValue(I.getOperand(0));
      auto RHS = getValue(I.getOperand(1));
      std::vector<AnyValue> Res;
      Res.reserve(Len);
      for (uint32_t I = 0; I != Len; ++I)
        Res.push_back(AnyValue{
            FnPoison(LHS.getSingleValueAt(I), RHS.getSingleValueAt(I))});
      return addValue(I, std::move(Res));
    }
    return addValue(
        I, AnyValue{FnPoison(getValue(I.getOperand(0)).getSingleValue(),
                             getValue(I.getOperand(1)).getSingleValue())});
  }
  bool visitUnOp(Instruction &I,
                 const function_ref<SingleValue(const SingleValue &)> &Fn) {
    auto FnPoison = [&Fn](const SingleValue &V) -> SingleValue {
      if (isPoison(V))
        return poison();
      return Fn(V);
    };
    if (auto *VTy = dyn_cast<VectorType>(I.getType())) {
      uint32_t Len = getVectorLength(VTy);
      auto V = getValue(I.getOperand(0));
      std::vector<AnyValue> Res;
      Res.reserve(Len);
      for (uint32_t I = 0; I != Len; ++I)
        Res.push_back(AnyValue{FnPoison(V.getSingleValueAt(I))});
      return addValue(I, std::move(Res));
    }
    return addValue(
        I, AnyValue{FnPoison(getValue(I.getOperand(0)).getSingleValue())});
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
  bool visitIntBinOp(Instruction &I, const function_ref<std::optional<APInt>(
                                         const APInt &, const APInt &)> &Fn) {
    return visitBinOp(
        I,
        [&Fn](const SingleValue &LHS, const SingleValue &RHS) -> SingleValue {
          auto &LHSC = std::get<APInt>(LHS);
          auto &RHSC = std::get<APInt>(RHS);
          if (auto Res = Fn(LHSC, RHSC))
            return SingleValue{*Res};
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
  bool
  visitIntUnOp(Instruction &I,
               const function_ref<std::optional<APInt>(const APInt &)> &Fn) {
    return visitUnOp(I, [&Fn](const SingleValue &V) -> SingleValue {
      auto &C = std::get<APInt>(V);
      if (auto Res = Fn(C))
        return SingleValue{*Res};
      return poison();
    });
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
  bool visitSelect(SelectInst &SI) {
    if (SI.getCondition()->getType()->isIntegerTy(1)) {
      switch (getBoolean(SI.getCondition())) {
      case BooleanVal::True:
        return addValue(SI, getValue(SI.getTrueValue()));
      case BooleanVal::False:
        return addValue(SI, getValue(SI.getFalseValue()));
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
    return addValue(SI, std::move(Res));
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
  bool visitStoreInst(StoreInst &SI) {
    store(getValue(SI.getPointerOperand()), SI.getAlign().value(),
          getValue(SI.getValueOperand()), SI.getValueOperand()->getType());
    return true;
  }
  bool visitInstruction(Instruction &I) {
    errs() << I << '\n';
    llvm_unreachable("Unsupported inst");
  }

  AnyValue callIntrinsic(Function *Func, SmallVectorImpl<AnyValue> &Args) {
    llvm_unreachable("Unsupported intrinsic");
  }
  AnyValue callLibFunc(LibFunc Func, Function *FuncDecl,
                       SmallVectorImpl<AnyValue> &Args) {
    llvm_unreachable("Unsupported libcall");
  }
  AnyValue call(Function *Func, SmallVectorImpl<AnyValue> &Args) {
    // TODO: handle param attrs
    for (auto &Param : Func->args()) {
    }

    if (Func->isIntrinsic()) {
      return callIntrinsic(Func, Args);
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

    CallFrame.BB = &Func->getEntryBlock();
    CallFrame.PC = CallFrame.BB->begin();
    while (!CallFrame.RetVal.has_value()) {
      if (visit(*CallFrame.PC))
        ++CallFrame.PC;
    }

    // TODO: handle retval attrs
    auto RetVal = std::move(*CallFrame.RetVal);
    if (!Func->getReturnType()->isVoidTy()) {
    }

    return RetVal;
  }

  int32_t runMain() {
    auto *Entry = M.getFunction("main");
    if (!Entry) {
      errs() << "Cannot find entry function `main`\n";
      return EXIT_FAILURE;
    }
    auto *FTy = Entry->getFunctionType();
    if (!FTy->getReturnType()->isIntegerTy(32) || FTy->isFunctionVarArg() ||
        FTy->getNumParams() != 2 || !FTy->getParamType(0)->isIntegerTy(32) ||
        !FTy->getParamType(1)->isPointerTy()) {
      errs() << "Unrecognized func";
      return EXIT_FAILURE;
    }

    SmallVector<AnyValue> Args;
    Args.push_back(SingleValue{APInt::getZero(32)});
    Args.push_back(SingleValue{Pointer{NullPtr, 0U}});
    return std::get<APInt>(call(Entry, Args).getSingleValue()).getSExtValue();
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
