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
static cl::opt<bool>
    TrackVolatileMem("track-volatile-mem",
                     cl::desc("Track volatile memory accesses"),
                     cl::init(false), cl::cat(Category));
static cl::opt<bool>
    VerifyValueTracking("verify-value-tracking",
                        cl::desc("Verify analysis results of value tracking"),
                        cl::init(false), cl::cat(Category));
static cl::opt<bool>
    StorePoisonIsNoop("store-poison-is-noop",
                      cl::desc("Treat store poison as a no-op"),
                      cl::init(false), cl::cat(Category));
static cl::opt<bool> RustMode("rust", cl::desc("Run rust programs"),
                              cl::init(false), cl::cat(Category));
static cl::opt<bool>
    IgnoreExplicitLifetimeMarker("ignore-explicit-lifetime-marker",
                                 cl::desc("Ignore explicit lifetime markers"),
                                 cl::init(false), cl::cat(Category));
static cl::opt<bool> FillUninitializedMemWithPoison(
    "fill-uninitialized-mem-with-poison",
    cl::desc("Fill uninitialized memory with poison to sync with alive2"),
    cl::init(false), cl::cat(Category));
static cl::opt<bool> FuseFMulAdd("fuse-fmuladd",
                                 cl::desc("Treat fmuladd as fma"),
                                 cl::init(false), cl::cat(Category));

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
  Option.TrackVolatileMem = TrackVolatileMem;
  Option.VerifyValueTracking = VerifyValueTracking;
  Option.IgnoreParamAttrsOnIntrinsic = IgnoreParamAttrsOnIntrinsic;
  Option.DumpStackTrace = DumpStackTrace;
  Option.StorePoisonIsNoop = StorePoisonIsNoop;
  Option.RustMode = RustMode;
  Option.IgnoreExplicitLifetimeMarker = IgnoreExplicitLifetimeMarker;
  Option.FillUninitializedMemWithPoison = FillUninitializedMemWithPoison;
  Option.FuseFMulAdd = FuseFMulAdd;

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
