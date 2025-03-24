// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#pragma once

#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/APSInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/FloatingPointMode.h>
#include <llvm/ADT/MapVector.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/STLFunctionalExtras.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/DomConditionCache.h>
#include <llvm/Analysis/SimplifyQuery.h>
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
#include <llvm/IR/GEPNoWrapFlags.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/MDBuilder.h>
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
#include <llvm/Support/KnownBits.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/ModRef.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/SwapByteOrder.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/TypeSize.h>
#include <limits>
#include <map>
#include <random>
#include <unordered_set>
#include <variant>

using namespace llvm;

class MemoryManager;
struct Frame;

struct MemByteMetadata {
  bool IsPoison = false;
};

struct PendingInitializeTask {
  Frame *Context;
  SmallVector<std::pair<uint64_t, uint64_t>, 1> Ranges;

  void write(uint64_t Offset, uint64_t Size);
};

class MemObject final : public std::enable_shared_from_this<MemObject> {
  MemoryManager &Manager;
  std::string Name;
  bool IsLocal;
  Frame *StackObjectInfo;
  APInt Address;
  SmallVector<std::byte, 16> Data;
  SmallVector<MemByteMetadata, 16> Metadata;
  SmallVector<PendingInitializeTask, 1> PendingInitializeTasks;
  bool IsAlive;
  bool IsConstant;

public:
  explicit MemObject(MemoryManager &Manager, std::string Name, bool IsLocal,
                     APInt PtrAddress, size_t Size)
      : Manager(Manager), Name(std::move(Name)), IsLocal(IsLocal),
        StackObjectInfo(nullptr), Address(std::move(PtrAddress)), Data(Size),
        Metadata(Size), IsAlive(true), IsConstant(false) {}
  ~MemObject();
  void setStackObjectInfo(Frame *FrameCtx) { StackObjectInfo = FrameCtx; }
  void markConstant() { IsConstant = true; }
  void setLiveness(bool Alive) { IsAlive = Alive; }
  void markPoison(size_t Offset, size_t Size, bool IsPoison);
  void verifyMemAccess(const APInt &Offset, const size_t AccessSize,
                       size_t Alignment);
  void store(size_t Offset, const APInt &C);
  void markWrite(size_t Offset, size_t Size);
  PendingInitializeTask &pushPendingInitializeTask(Frame *Ctx);
  void popPendingInitializeTask(Frame *Ctx);
  std::optional<APInt> load(size_t Offset, size_t Bits) const;
  APInt address() const { return Address; }
  size_t size() const { return Data.size(); }
  char *rawPointer() { return reinterpret_cast<char *>(Data.data()); }
  void dumpName(raw_ostream &Out) const;
  void dump(raw_ostream &Out) const;
  bool isGlobal() const noexcept { return !IsLocal; }
  bool isStackObject(Frame *Ctx) const noexcept {
    return StackObjectInfo == Ctx;
  }
  bool isAlive() const noexcept { return IsAlive; }
  bool isConstant() const noexcept { return IsConstant; }
};

inline raw_ostream &operator<<(raw_ostream &Out, const MemObject &MO) {
  MO.dump(Out);
  return Out;
}

struct ContextSensitivePointerInfo {
  std::shared_ptr<const ContextSensitivePointerInfo> Parent;
  Frame *FrameCtx;
  bool Readable : 1;
  bool Writable : 1;
  bool Comparable : 1;
  bool ComparableWithNull : 1;
  IRMemLocation Loc;
  CaptureInfo CI;

  static ContextSensitivePointerInfo getDefault(Frame *FrameCtx);
  void push(Frame *Ctx);
  void pushReadWrite(Frame *Ctx, bool Readable, bool Writable) {
    push(Ctx);
    this->Readable = Readable;
    this->Writable = Writable;
  }
  void pushLoc(Frame *Ctx, IRMemLocation Loc) {
    push(Ctx);
    this->Loc = Loc;
  }
  void pushCaptureInfo(Frame *Ctx, CaptureInfo CI) {
    push(Ctx);
    this->CI &= CI;
  }
  void pushComparable(Frame *Ctx, bool Comparable) {
    push(Ctx);
    this->Comparable = Comparable;
  }
  void pushComparableWithNull(Frame *Ctx, bool ComparableWithNull) {
    push(Ctx);
    this->ComparableWithNull = ComparableWithNull;
  }
  void pop(Frame *Ctx);
};

struct Pointer final {
  std::weak_ptr<MemObject> Obj;
  APInt Offset;
  APInt Address;
  size_t Bound;
  ContextSensitivePointerInfo Info;

  explicit Pointer(const std::shared_ptr<MemObject> &Obj, const APInt &Offset,
                   ContextSensitivePointerInfo Info)
      : Obj(Obj), Offset(Offset), Address(Obj->address() + Offset),
        Bound(Obj->size()), Info(std::move(Info)) {}
  explicit Pointer(const std::weak_ptr<MemObject> &Obj, APInt NewOffset,
                   APInt NewAddress, size_t NewBound,
                   ContextSensitivePointerInfo Info)
      : Obj(Obj), Offset(std::move(NewOffset)), Address(std::move(NewAddress)),
        Bound(NewBound), Info(std::move(Info)) {}
};

using SingleValue = std::variant<APInt, APFloat, Pointer, std::monostate>;
inline bool isPoison(const SingleValue &SV) {
  return std::holds_alternative<std::monostate>(SV);
}
inline bool isPoison(const APFloat &AFP, FastMathFlags FMF) {
  if (FMF.noNaNs() && AFP.isNaN())
    return true;
  if (FMF.noInfs() && AFP.isInfinity())
    return true;
  return false;
}
inline SingleValue boolean(bool Val) { return SingleValue{APInt(1, Val)}; }
inline SingleValue poison() { return std::monostate{}; }
bool refines(const SingleValue &LHS, const SingleValue &RHS);

class UBAwareInterpreter;

class MemoryManager final {
  UBAwareInterpreter &Interpreter;
  uint32_t PtrBitWidth;
  size_t AllocatedMem = 0;
  static constexpr size_t Padding = 16U;
  std::map<size_t, MemObject *> AddressMap;

  friend class MemObject;
  void erase(const size_t Address) { AddressMap.erase(Address); }

public:
  explicit MemoryManager(UBAwareInterpreter &Interpreter, const DataLayout &DL,
                         PointerType *Ty);
  std::shared_ptr<MemObject> create(std::string Name, bool IsLocal, size_t Size,
                                    size_t Alignment);
  SingleValue lookupPointer(const APInt &Addr) const;
};
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
  bool refines(const AnyValue &RHS) const;
};
inline AnyValue none() { return AnyValue{std::monostate{}}; }
raw_ostream &operator<<(raw_ostream &Out, const AnyValue &Val);

struct FunctionAnalysisCache final {
  DominatorTree DT;
  AssumptionCache AC;
  DomConditionCache DC;
  DenseMap<Value *, bool> NonZeroCache;
  DenseMap<Value *, KnownBits> KnownBitsCache;

  FunctionAnalysisCache(Function &F);
  FunctionAnalysisCache(const FunctionAnalysisCache &) = delete;
  KnownBits queryKnownBits(Value *V, const SimplifyQuery &SQ);
  bool queryNonZero(Value *V, const SimplifyQuery &SQ);
};

struct Frame final {
  BasicBlock *BB;
  BasicBlock::iterator PC;
  SmallVector<std::shared_ptr<MemObject>> Allocas;
  DenseMap<Value *, AnyValue> ValueMap;
  std::optional<AnyValue> RetVal;
  FunctionAnalysisCache *Cache;
  TargetLibraryInfo TLI;
  Frame *LastFrame;
  MemoryEffects MemEffects;

  explicit Frame(Function *Func, FunctionAnalysisCache *Cache,
                 TargetLibraryInfoImpl &TLI, Frame *LastFrame,
                 MemoryEffects ME);
};

struct IntConstraintInfo final {
  ConstantRange Range;
  KnownBits Bits;
  bool HasPoison;

  explicit IntConstraintInfo(const std::optional<APInt> &InitV)
      : Range(InitV.has_value() ? *InitV : APInt::getZero(32)),
        Bits(KnownBits::makeConstant(InitV.has_value() ? *InitV
                                                       : APInt::getZero(32))),
        HasPoison(!InitV.has_value()) {}
  void update(const std::optional<APInt> &V) {
    if (HasPoison)
      return;
    if (!V.has_value()) {
      HasPoison = true;
      return;
    }
    Range = Range.unionWith(*V);
    Bits = Bits.intersectWith(KnownBits::makeConstant(*V));
  }
};

struct EMITrackingInfo final {
  bool Enabled;
  bool EnablePGFTracking;
  DenseMap<Value *, bool> MayBeUndef;
  DenseMap<Value *, ConstantRange> Range;
  DenseMap<BinaryOperator *, uint32_t> NoWrapFlags;
  DenseMap<TruncInst *, uint32_t> TruncNoWrapFlags;
  DenseMap<PossiblyNonNegInst *, bool> NNegFlags;
  DenseMap<ICmpInst *, bool> ICmpFlags;
  DenseMap<IntrinsicInst *, bool> IsPoisonFlags;
  DenseMap<PossiblyDisjointInst *, bool> DisjointFlags;

  DenseMap<Instruction *, SmallVector<Use *>> InterestingUses;
  DenseMap<Use *, IntConstraintInfo> UseIntInfo;

  // TODO: nonnull
  // TODO: align
  // TODO: Use -> attributes mapping for arguments
  DenseSet<BasicBlock *> ReachableBlocks;

  void trackRange(Value *K, const APInt &V) {
    if (V.getBitWidth() <= 1)
      return;
    if (!Range.contains(K))
      Range.insert({K, V});
    else {
      auto &Ref = Range.find(K)->second;
      Ref = Ref.unionWith(V);
    }
  }
};

struct InterpreterOption {
  uint32_t VScale = 4;
  uint32_t MaxSteps = std::numeric_limits<uint32_t>::max();
  bool Verbose = false;
  bool DumpStackTrace = false;

  bool EnableEMITracking = false;
  bool EnablePGFTracking = true;
  bool EnableEMIDebugging = false;
  double EMIProb = 0.1;
  double EMIUseProb = 0.001;

  bool TrackVolatileMem = false;
  bool VerifyValueTracking = false;
  bool IgnoreParamAttrsOnIntrinsic = false;
  bool StorePoisonIsNoop = false;
  bool ReduceMode = false;
};

class UBAwareInterpreter : public InstVisitor<UBAwareInterpreter, bool> {
  LLVMContext &Ctx;
  Module &M;
  const DataLayout &DL;
  InterpreterOption Option;
  TargetLibraryInfoImpl TLI;
  MemoryManager MemMgr;
  std::shared_ptr<MemObject> NullPtrStorage;
  std::optional<Pointer> NullPtr;
  DenseMap<GlobalValue *, std::shared_ptr<MemObject>> GlobalValues;
  std::unordered_set<std::shared_ptr<MemObject>> AllocatedMems;
  DenseMap<size_t, Function *> ValidCallees;
  DenseMap<size_t, BasicBlock *> ValidBlockTargets;
  DenseMap<BasicBlock *, std::shared_ptr<MemObject>> BlockTargets;
  std::unordered_map<Function *, FunctionAnalysisCache> AnalysisCache;
  EMITrackingInfo EMIInfo;
  std::mt19937_64 Gen;
  Frame *CurrentFrame = nullptr;
  uint32_t Steps = 0;
  uint64_t VolatileMemHash = 0;

  SimplifyQuery getSQ(const Instruction *CxtI) const;
  void verifyAnalysis(Value *V, const AnyValue &RV, const Instruction *CxtI);
  uint32_t getVectorLength(VectorType *Ty) const;
  AnyValue getPoison(Type *Ty) const;
  AnyValue getZero(Type *Ty) const;
  AnyValue convertFromConstant(Constant *V) const;
  void store(MemObject &MO, uint32_t Offset, const AnyValue &V, Type *Ty);
  AnyValue load(const MemObject &MO, uint32_t Offset, Type *Ty);
  void store(const AnyValue &P, uint32_t Alignment, const AnyValue &V, Type *Ty,
             bool IsVolatile);
  AnyValue load(const AnyValue &P, uint32_t Alignment, Type *Ty,
                bool IsVolatile);
  SingleValue offsetPointer(const Pointer &Ptr, const APInt &Offset,
                            GEPNoWrapFlags Flags) const;
  SingleValue alloc(const APInt &AllocSize, bool ZeroInitialize);

public:
  explicit UBAwareInterpreter(Module &M, InterpreterOption Option);

  Frame *getCurrentFrame() const { return CurrentFrame; }
  bool addValue(Instruction &I, AnyValue Val);
  bool jumpTo(BasicBlock *To);
  AnyValue getValue(Value *V);
  std::optional<APInt> getInt(const SingleValue &SV);
  std::optional<APInt> getInt(Value *V);
  APInt getIntNonPoison(Value *V);
  enum class BooleanVal { Poison, False, True };
  BooleanVal getBoolean(const SingleValue &SV);
  bool getBooleanNonPoison(const SingleValue &SV);
  BooleanVal getBoolean(Value *V);
  char *getRawPtr(const SingleValue &SV);
  char *getRawPtr(SingleValue SV, size_t Size, size_t Alignment, bool IsStore,
                  bool IsVolatile);
  DenormalMode getCurrentDenormalMode(Type *Ty);

  void volatileMemOpTy(Type *Ty, bool IsStore);
  void volatileMemOp(size_t Size, bool IsStore);

  bool visitAllocaInst(AllocaInst &AI);
  AnyValue visitBinOp(Type *RetTy, const AnyValue &LHS, const AnyValue &RHS,
                      const function_ref<SingleValue(const SingleValue &,
                                                     const SingleValue &)> &Fn);
  bool visitBinOp(Instruction &I,
                  const function_ref<SingleValue(const SingleValue &,
                                                 const SingleValue &)> &Fn);
  AnyValue visitUnOp(Type *RetTy, const AnyValue &Val,
                     const function_ref<SingleValue(const SingleValue &)> &Fn,
                     bool PropagatesPoison = true);
  bool visitUnOp(Instruction &I,
                 const function_ref<SingleValue(const SingleValue &)> &Fn,
                 bool PropagatesPoison = true);
  AnyValue visitTriOp(
      Type *RetTy, const AnyValue &X, const AnyValue &Y, const AnyValue &Z,
      const function_ref<SingleValue(const SingleValue &, const SingleValue &,
                                     const SingleValue &)> &Fn);

  bool visitICmpInst(ICmpInst &I);
  AnyValue visitIntBinOp(
      Type *RetTy, const AnyValue &LHS, const AnyValue &RHS,
      const function_ref<std::optional<APInt>(const APInt &, const APInt &)>
          &Fn);
  AnyValue
  visitFPBinOp(Type *RetTy, FastMathFlags FMF, const AnyValue &LHS,
               const AnyValue &RHS,
               const function_ref<std::optional<APFloat>(const APFloat &,
                                                         const APFloat &)> &Fn);
  bool visitIntBinOp(Instruction &I, const function_ref<std::optional<APInt>(
                                         const APInt &, const APInt &)> &Fn);
  bool visitFPBinOp(Instruction &I, const function_ref<std::optional<APFloat>(
                                        const APFloat &, const APFloat &)> &Fn);
  AnyValue visitIntTriOp(Type *RetTy, const AnyValue &X, const AnyValue &Y,
                         const AnyValue &Z,
                         const function_ref<std::optional<APInt>(
                             const APInt &, const APInt &, const APInt &)> &Fn);
  AnyValue
  visitFPTriOp(Type *RetTy, FastMathFlags FMF, const AnyValue &X,
               const AnyValue &Y, const AnyValue &Z,
               const function_ref<std::optional<APFloat>(
                   const APFloat &, const APFloat &, const APFloat &)> &Fn);
  bool visitAnd(BinaryOperator &I);
  bool visitXor(BinaryOperator &I);
  bool visitOr(BinaryOperator &I);
  bool visitShl(BinaryOperator &I);
  bool visitLShr(BinaryOperator &I);
  bool visitAShr(BinaryOperator &I);
  bool visitAdd(BinaryOperator &I);
  bool visitSub(BinaryOperator &I);
  bool visitMul(BinaryOperator &I);
  bool visitSDiv(BinaryOperator &I);
  bool visitSRem(BinaryOperator &I);
  bool visitUDiv(BinaryOperator &I);
  bool visitURem(BinaryOperator &I);
  AnyValue
  visitIntUnOp(Type *Ty, const AnyValue &Val,
               const function_ref<std::optional<APInt>(const APInt &)> &Fn);
  bool
  visitIntUnOp(Instruction &I,
               const function_ref<std::optional<APInt>(const APInt &)> &Fn);
  AnyValue
  visitFPUnOp(Type *RetTy, FastMathFlags FMF, const AnyValue &Val,
              const function_ref<std::optional<APFloat>(const APFloat &)> &Fn);
  bool
  visitFPUnOp(Instruction &I,
              const function_ref<std::optional<APFloat>(const APFloat &)> &Fn);
  bool visitTruncInst(TruncInst &Trunc);
  bool visitSExtInst(SExtInst &SExt);
  bool visitZExtInst(ZExtInst &ZExt);
  bool fpCast(Instruction &I);
  bool visitFPExtInst(FPExtInst &FPExt);
  bool visitFPTruncInst(FPTruncInst &FPTrunc);
  bool visitIntToFPInst(Instruction &I, bool IsSigned);
  bool visitSIToFPInst(SIToFPInst &I);
  bool visitUIToFPInst(UIToFPInst &I);
  bool visitFPToIntInst(Instruction &I, bool IsSigned);
  bool visitFPToSIInst(FPToSIInst &I);
  bool visitFPToUIInst(FPToUIInst &I);
  bool visitFNeg(UnaryOperator &I);
  bool visitFAdd(BinaryOperator &I);
  bool visitFSub(BinaryOperator &I);
  bool visitFMul(BinaryOperator &I);
  bool visitFDiv(BinaryOperator &I);
  bool visitFRem(BinaryOperator &I);
  bool visitFCmpInst(FCmpInst &FCmp);
  AnyValue freezeValue(const AnyValue &Val, Type *Ty);
  bool visitFreezeInst(FreezeInst &Freeze);
  bool visitSelect(SelectInst &SI);
  bool visitBranchInst(BranchInst &BI);
  bool visitIndirectBrInst(IndirectBrInst &IBI);
  SingleValue computeGEP(const SingleValue &Base, const APInt &Offset,
                         GEPNoWrapFlags Flags);
  bool visitGetElementPtrInst(GetElementPtrInst &GEP);
  bool visitExtractValueInst(ExtractValueInst &EVI);
  bool visitInsertValueInst(InsertValueInst &IVI);
  bool visitInsertElementInst(InsertElementInst &IEI);
  bool visitExtractElementInst(ExtractElementInst &EEI);
  bool visitShuffleVectorInst(ShuffleVectorInst &SVI);
  bool visitStoreInst(StoreInst &SI);
  void handleRangeMetadata(AnyValue &V, Instruction &I);
  bool visitLoadInst(LoadInst &LI);
  void writeBits(APInt &Dst, uint32_t &Offset, const APInt &Src);
  void toBits(APInt &Bits, APInt &PoisonBits, uint32_t &Offset,
              const AnyValue &Val, Type *Ty);
  bool visitIntToPtr(IntToPtrInst &I);
  bool visitPtrToInt(PtrToIntInst &I);
  APInt readBits(const APInt &Src, uint32_t &Offset, uint32_t Width);
  AnyValue fromBits(const APInt &Bits, const APInt &PoisonBits,
                    uint32_t &Offset, Type *Ty);
  bool visitBitCastInst(BitCastInst &BCI);
  std::string getValueName(Value *V);
  AnyValue handleCall(CallBase &CB);
  bool visitCallInst(CallInst &CI);
  bool visitInvokeInst(InvokeInst &II);
  bool visitReturnInst(ReturnInst &RI);
  bool visitUnreachableInst(UnreachableInst &);
  bool visitSwitchInst(SwitchInst &SI);
  bool visitInstruction(Instruction &I);
  AnyValue handleWithOverflow(
      Type *OpTy, const AnyValue &LHS, const AnyValue &RHS,
      const function_ref<std::pair<APInt, bool>(const APInt &, const APInt &)>
          &Fn);

  AnyValue callIntrinsic(IntrinsicInst &II, SmallVectorImpl<AnyValue> &Args);
  AnyValue callLibFunc(LibFunc Func, Function *FuncDecl,
                       SmallVectorImpl<AnyValue> &Args);
  AnyValue call(Function *Func, CallBase *CB, SmallVectorImpl<AnyValue> &Args);
  void dumpStackTrace();
  int32_t runMain();
  void mutate();
  bool simplify();
};
