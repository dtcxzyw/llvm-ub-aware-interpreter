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
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/SwapByteOrder.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/TypeSize.h>
#include <map>
#include <variant>

using namespace llvm;

class ImmUBReporter final {
  raw_ostream &Out;

public:
  ImmUBReporter();
  [[noreturn]] ~ImmUBReporter();
  template <typename Arg> ImmUBReporter &operator<<(Arg &&arg) {
    Out << std::forward<Arg>(arg);
    return *this;
  }
};

class MemoryManager;
class MemObject final : public std::enable_shared_from_this<MemObject> {
  MemoryManager &Manager;
  std::string Name;
  bool IsLocal;
  APInt Address;
  SmallVector<std::byte, 16> Data;

public:
  explicit MemObject(MemoryManager &Manager, std::string Name, bool IsLocal,
                     APInt PtrAddress, size_t Size)
      : Manager(Manager), Name(std::move(Name)), IsLocal(IsLocal),
        Address(std::move(PtrAddress)), Data(Size) {}
  ~MemObject();
  void verifyMemAccess(const APInt &Offset, const size_t AccessSize,
                       size_t Alignment);
  void store(size_t Offset, const APInt &C);
  APInt load(size_t Offset, size_t Bits) const;
  APInt address() const { return Address; }
  size_t size() const { return Data.size(); }
  char *rawPointer() { return reinterpret_cast<char *>(Data.data()); }
  void dumpName(raw_ostream &Out);
  void dumpRef(raw_ostream &Out);
};

struct Pointer final {
  std::weak_ptr<MemObject> Obj;
  APInt Offset;
  APInt Address;
  size_t Bound;

  Pointer(const std::shared_ptr<MemObject> &Obj, const APInt &Offset)
      : Obj(Obj), Offset(Offset), Address(Obj->address() + Offset),
        Bound(Obj->size()) {}
  explicit Pointer(const std::weak_ptr<MemObject> &Obj, APInt NewOffset,
                   APInt NewAddress, size_t NewBound)
      : Obj(Obj), Offset(std::move(NewOffset)), Address(std::move(NewAddress)),
        Bound(NewBound) {}
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

class MemoryManager final {
  // TODO: handle llvm.lifetime.start/end and llvm.invariant.start.end/TBAA
  uint32_t PtrBitWidth;
  size_t AllocatedMem = 0;
  static constexpr size_t Padding = 16U;
  std::map<size_t, MemObject *> AddressMap;

  friend class MemObject;
  void erase(const size_t Address) { AddressMap.erase(Address); }

public:
  explicit MemoryManager(const DataLayout &DL, PointerType *Ty);
  std::shared_ptr<MemObject> create(std::string Name, bool IsLocal, size_t Size,
                                    size_t Alignment);
  SingleValue lookupPointer(const APInt &Addr) const;
};
