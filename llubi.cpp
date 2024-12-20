// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2024 Yingwei Zheng
// This file is licensed under the Apache-2.0 License.
// See the LICENSE file for more information.

#include "ubi.h"
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <memory>
#include <system_error>

using namespace llvm;
static cl::OptionCategory Category("LLUBI Options");
static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input>"),
                                      cl::Required,
                                      cl::value_desc("path to input IR"),
                                      cl::cat(Category));
static cl::opt<uint32_t> VScaleValue("vscale",
                                     cl::value_desc("value for llvm.vscale"),
                                     cl::init(4U), cl::cat(Category));
static cl::opt<uint32_t>
    MaxSteps("max-steps", cl::value_desc("Max steps to run"),
             cl::init(std::numeric_limits<uint32_t>::max()), cl::cat(Category));
static cl::opt<bool> IgnoreParamAttrsOnIntrinsic(
    "ignore-param-attrs-intrinsic",
    cl::desc("Ignore parameter attributes of intrinsic calls"), cl::init(false),
    cl::cat(Category));
static cl::opt<bool> ReduceMode("reduce-mode",
                                cl::desc("Reduce mode (allow invalid IR)"),
                                cl::init(false), cl::cat(Category));
static cl::opt<bool> Verbose("verbose", cl::desc("Print step-by-step log"),
                             cl::init(false), cl::cat(Category));
static cl::opt<std::string> EMIMutate("emi",
                                      cl::desc("Enable EMI-based mutation"),
                                      cl::value_desc("Path to output IR file"),
                                      cl::cat(Category));
static cl::opt<bool> DumpEMI("dump-emi",
                             cl::desc("Dump EMI-based mutation scheme"),
                             cl::init(false), cl::cat(Category));
static cl::opt<bool>
    DumpStackTrace("dump-stack-trace",
                   cl::desc("Dump stack trace when immediate UB occurs"),
                   cl::init(true), cl::cat(Category));

int main(int argc, char **argv) {
  InitLLVM Init{argc, argv};
  cl::HideUnrelatedOptions(Category);
  cl::ParseCommandLineOptions(argc, argv,
                              "llubi -- LLVM ub-aware interpreter\n");

  LLVMContext Ctx;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(InputFile, Err, Ctx);
  if (!M) {
    Err.print(argv[0], errs());
    return EXIT_FAILURE;
  }

  InterpreterOption Option;

  Option.ReduceMode = ReduceMode;
  Option.VScale = VScaleValue;
  Option.MaxSteps = MaxSteps;
  Option.Verbose = Verbose;
  Option.EnableEMITracking = !EMIMutate.empty();
  Option.EnableEMIDebugging = DumpEMI;
  Option.IgnoreParamAttrsOnIntrinsic = IgnoreParamAttrsOnIntrinsic;
  Option.DumpStackTrace = DumpStackTrace;

  UBAwareInterpreter Executor(*M, Option);
  int32_t Ret = Executor.runMain();
  if (!EMIMutate.empty()) {
    Executor.mutate();
    std::error_code EC;
    raw_fd_ostream Out{EMIMutate.getValue(), EC, sys::fs::OF_Text};
    if (EC) {
      errs() << "Error: " << EC.message() << '\n';
      return EXIT_FAILURE;
    }
    Out << *M;
    Out.flush();
  }
  return Ret;
}
