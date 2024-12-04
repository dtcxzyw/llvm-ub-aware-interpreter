// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include <llvm/ADT/STLExtras.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/ConstantFold.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/Local.h>
#include "ubi.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <system_error>

using namespace llvm;
using namespace PatternMatch;
static cl::OptionCategory Category("EMIReduce Options");
static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input>"),
                                      cl::Required,
                                      cl::value_desc("path to input IR"),
                                      cl::cat(Category));
static cl::opt<uint32_t> VScaleValue("vscale",
                                     cl::value_desc("value for llvm.vscale"),
                                     cl::init(4U), cl::cat(Category));
static cl::opt<std::string> OutputFile(cl::Positional, cl::desc("<output>"),
                                       cl::Required,
                                       cl::value_desc("path to output IR"),
                                       cl::cat(Category));

static Constant *constantFoldInst(Instruction *I) {
  if (auto *BO = dyn_cast<BinaryOperator>(I)) {
    if (auto *LHS = dyn_cast<Constant>(BO->getOperand(0)))
      if (auto *RHS = dyn_cast<Constant>(BO->getOperand(1)))
        return ConstantFoldBinaryInstruction(BO->getOpcode(), LHS, RHS);
  }
  if (auto *UI = dyn_cast<UnaryOperator>(I)) {
    if (auto *V = dyn_cast<Constant>(UI->getOperand(0)))
      return ConstantFoldUnaryInstruction(UI->getOpcode(), V);
  }
  if (auto *CI = dyn_cast<CastInst>(I)) {
    if (auto *V = dyn_cast<Constant>(CI->getOperand(0)))
      return ConstantFoldCastInstruction(CI->getOpcode(), V, CI->getType());
  }
  if (auto *SI = dyn_cast<SelectInst>(I)) {
    if (auto *Cond = dyn_cast<Constant>(SI->getCondition()))
      if (auto *V1 = dyn_cast<Constant>(SI->getTrueValue()))
        if (auto *V2 = dyn_cast<Constant>(SI->getFalseValue()))
          return ConstantFoldSelectInstruction(Cond, V1, V2);
  }
  if (auto *EI = dyn_cast<ExtractElementInst>(I)) {
    if (auto *Val = dyn_cast<Constant>(EI->getVectorOperand()))
      if (auto *Idx = dyn_cast<Constant>(EI->getIndexOperand()))
        return ConstantFoldExtractElementInstruction(Val, Idx);
  }
  if (auto *II = dyn_cast<InsertElementInst>(I)) {
    if (auto *Val = dyn_cast<Constant>(II->getOperand(0)))
      if (auto *Elt = dyn_cast<Constant>(II->getOperand(1)))
        if (auto *Idx = dyn_cast<Constant>(II->getOperand(2)))
          return ConstantFoldInsertElementInstruction(Val, Elt, Idx);
  }
  if (auto *SVI = dyn_cast<ShuffleVectorInst>(I)) {
    if (auto *V1 = dyn_cast<Constant>(SVI->getOperand(0)))
      if (auto *V2 = dyn_cast<Constant>(SVI->getOperand(1)))
        return ConstantFoldShuffleVectorInstruction(V1, V2,
                                                    SVI->getShuffleMask());
  }
  if (auto *EVI = dyn_cast<ExtractValueInst>(I)) {
    if (auto *Agg = dyn_cast<Constant>(EVI->getAggregateOperand()))
      return ConstantFoldExtractValueInstruction(Agg, EVI->getIndices());
  }
  if (auto *IVI = dyn_cast<InsertValueInst>(I)) {
    if (auto *Agg = dyn_cast<Constant>(IVI->getAggregateOperand()))
      if (auto *Val = dyn_cast<Constant>(IVI->getInsertedValueOperand()))
        return ConstantFoldInsertValueInstruction(Agg, Val, IVI->getIndices());
  }
  if (auto *CI = dyn_cast<CmpInst>(I)) {
    if (auto *C1 = dyn_cast<Constant>(CI->getOperand(0)))
      if (auto *C2 = dyn_cast<Constant>(CI->getOperand(1)))
        return ConstantFoldCompareInstruction(CI->getPredicate(), C1, C2);
  }

  return nullptr;
}

static bool simplifyFunction(Function &F) {
  if (F.isDeclaration())
    return false;
  bool Changed = false;
  for (auto &BB : F) {
    for (auto &I : make_early_inc_range(BB)) {
      if (isInstructionTriviallyDead(&I)) {
        I.eraseFromParent();
        Changed = true;
        continue;
      }
      if (auto *V = constantFoldInst(&I)) {
        I.replaceAllUsesWith(V);
        I.eraseFromParent();
        Changed = true;
        continue;
      }
    }

    Changed |= ConstantFoldTerminator(&BB, /*DeleteDeadConditions=*/true);
  }
  Changed |= removeUnreachableBlocks(F);
  return Changed;
}
static bool simplifyModule(Module &M) {
  bool Changed = false;
  for (auto &F : make_early_inc_range(M)) {
    Changed |= simplifyFunction(F);
    if (F.getName() != "main" && F.user_empty()) {
      F.eraseFromParent();
      Changed = true;
    }
  }
  for (auto &GV : make_early_inc_range(M.globals())) {
    if (GV.user_empty()) {
      GV.eraseFromParent();
      Changed = true;
    }
  }

  if (verifyModule(M, &errs())) {
    errs() << "Error: verification failed\n";
    std::abort();
  }
  return Changed;
}

int main(int argc, char **argv) {
  InitLLVM Init{argc, argv};
  cl::HideUnrelatedOptions(Category);
  cl::ParseCommandLineOptions(
      argc, argv,
      "emireduce -- EMI-based semantic-preserving LLVM IR reducer\n");

  LLVMContext Ctx;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(InputFile, Err, Ctx);
  if (!M) {
    Err.print(argv[0], errs());
    return EXIT_FAILURE;
  }

  InterpreterOption Option;
  Option.VScale = VScaleValue;
  Option.EnableEMITracking = true;
  Option.EnablePGFTracking = false;
  Option.EMIProb = 0.1;
  Option.EMIUseProb = 1.01;
  UBAwareInterpreter Executor(*M, Option);
  int32_t Ret = Executor.runMain();
  if (!Executor.simplify()) {
    outs() << "No changes\n";
    return EXIT_SUCCESS;
  }
  simplifyModule(*M);
  std::error_code EC;
  raw_fd_ostream Out{OutputFile.getValue(), EC, sys::fs::OF_Text};
  if (EC) {
    errs() << "Error: " << EC.message() << '\n';
    return EXIT_FAILURE;
  }
  Out << *M;
  Out.flush();
  return Ret;
}
