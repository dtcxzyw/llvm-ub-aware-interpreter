// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/ScopeExit.h>
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
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
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
    Out << "Exited with immediate UB.\n";
    std::exit(EXIT_FAILURE);
  }
  template <typename Arg> ImmUBReporter &operator<<(Arg &&arg) {
    Out << std::forward<Arg>(arg);
    return *this;
  }
};

class MemObject final {
  size_t Address;
  SmallVector<std::byte, 16> Data;
  static std::map<size_t, MemObject *> AddressMap;

public:
  explicit MemObject(size_t Size, size_t Alignment) : Data(Size) {
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
  static std::shared_ptr<MemObject> create(size_t Size, size_t Alignment) {
    return std::make_shared<MemObject>(Size, Alignment);
  }
  void store(size_t Offset, const APInt &C) {
    constexpr uint32_t Scale = APInt::APINT_BITS_PER_WORD / 8;
    const size_t Size = alignTo(C.getBitWidth(), 8);
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
    constexpr uint32_t Scale = APInt::APINT_BITS_PER_WORD / 8;
    const size_t Size = Res.getBitWidth();
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
};
std::map<size_t, MemObject *> MemObject::AddressMap;

struct Pointer final {
  std::weak_ptr<MemObject> Obj;
  size_t Offset;
  size_t Address;

  Pointer(const std::shared_ptr<MemObject> &Obj, size_t Offset)
      : Obj(Obj), Offset(Offset), Address(Obj->address() + Offset) {}
};

using SingleValue = std::variant<APInt, APFloat, Pointer, std::monostate>;
bool isPoison(const SingleValue &SV) {
  return std::holds_alternative<std::monostate>(SV);
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
};

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
      return SingleValue{};
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
    llvm_unreachable("Unsupported type");
  }
  AnyValue convertFromConstant(Constant *V) const {
    if (isa<PoisonValue>(V))
      return getPoison(V->getType());
    if (isa<UndefValue>(V))
      return getZero(V->getType());
    if (auto *CI = dyn_cast<ConstantInt>(V))
      return SingleValue{CI->getValue()};
    if (auto *CFP = dyn_cast<ConstantFP>(V))
      return SingleValue{CFP->getValue()};
    if (isa<ConstantAggregateZero>(V))
      return getZero(V->getType());
    if (isa<ConstantPointerNull>(V))
      return SingleValue{Pointer{NullPtr, 0U}};
    if (auto *CDS = dyn_cast<ConstantDataSequential>(V)) {
      std::vector<AnyValue> Elts;
      for (uint32_t I = 0, E = CDS->getNumElements(); I != E; ++I)
        Elts.push_back(convertFromConstant(CDS->getElementAsConstant(I)));
      return std::move(Elts);
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
    NullPtr = MemObject::create(0U, 1U);
    assert(NullPtr->address() == 0);
    for (auto &GV : M.globals()) {
      if (!GV.hasExactDefinition())
        continue;
      auto MemObj = MemObject::create(DL.getTypeAllocSize(GV.getType()),
                                      DL.getPreferredAlign(&GV).value());
      if (GV.hasInitializer())
        store(*MemObj, 0U, convertFromConstant(GV.getInitializer()),
              GV.getValueType());
      GlobalVariables.insert({&GV, std::move(MemObj)});
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
  bool visitInstruction(Instruction &I) {
    errs() << I << '\n';
    llvm_unreachable("Unsupported inst");
  }

  AnyValue callIntrinsic(Function *Func, ArrayRef<AnyValue> &Args) {
    llvm_unreachable("Unsupported intrinsic");
  }
  AnyValue callLibFunc(LibFunc Func, Function *FuncDecl,
                       ArrayRef<AnyValue> &Args) {
    llvm_unreachable("Unsupported libcall");
  }
  AnyValue call(Function *Func, ArrayRef<AnyValue> &Args) {
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
        FTy->getNumParams() != 0) {
      errs() << "Unrecognized func";
      return EXIT_FAILURE;
    }

    ArrayRef<AnyValue> Empty;
    return std::get<APInt>(call(Entry, Empty).getSingleValue()).getSExtValue();
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
