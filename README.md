# llvm-ub-aware-interpreter (llubi)
UB-aware interpreter for LLVM debugging

## Introduction

This tool is developed to save my life when debugging LLVM. Unlike lli, this interpreter is UB-aware, which means it will check immediate undefined behaviors during the execution and handle poison values properly. It is designed to be a debugging tool, so it is not optimized for performance. [alive-exec](https://github.com/AliveToolkit/alive2) should be a drop-in replacement of this tool. But it is slow and easy to get stuck in my experience. So this tool is designed to be more friendly to csmith and creduce.

## Motivation

We have suffered from incorrect poison-generating/UB-implying annotations in LLVM for a long time. The most common mistake is that we forget to drop annotations after replacing one of its operands in place. In most cases, this kind of bugs will not be caught by end-to-end tests or real-world applications. But they will finally emerge when we do some aggressive optimizations with these incorrect annotations. With this interpreter, we can easily find out the incorrect annotations handling and fix them.

Here is an incomplete list of this kind of bugs:
+ https://github.com/llvm/llvm-project/issues/115976
+ https://github.com/llvm/llvm-project/issues/115890
+ https://github.com/llvm/llvm-project/issues/114879
+ https://github.com/llvm/llvm-project/issues/113997
+ https://github.com/llvm/llvm-project/issues/112666
+ https://github.com/llvm/llvm-project/issues/112476
+ https://github.com/llvm/llvm-project/issues/112356
+ https://github.com/llvm/llvm-project/issues/112350
+ https://github.com/llvm/llvm-project/issues/112078
+ https://github.com/llvm/llvm-project/issues/112076
+ https://github.com/llvm/llvm-project/issues/112068
+ https://github.com/llvm/llvm-project/issues/111934
+ https://github.com/llvm/llvm-project/issues/99436
+ https://github.com/llvm/llvm-project/issues/91691
+ https://github.com/llvm/llvm-project/issues/91178
+ https://github.com/llvm/llvm-project/issues/91127
+ https://github.com/llvm/llvm-project/issues/90380
+ https://github.com/llvm/llvm-project/issues/87042
+ https://github.com/llvm/llvm-project/issues/85536
+ https://github.com/llvm/llvm-project/issues/78621

## Getting Started

```
git clone https://github.com/dtcxzyw/llvm-ub-aware-interpreter
cd llvm-ub-aware-interpreter
mkdir -p build && cd build
cmake .. -GNinja -DCMAKE_BUILD_TYPE=Release -DLLVM_DIR=/path/to/llvm/lib/cmake/llvm
cmake --build . -j
./llubi test.ll [--verbose]
```

## Notes
+ Undef values are not supported as we will eventually remove undef from LLVM in the future. In llubi, they are treated as zero values.
+ FFI is not supported. Currently it only supports ```printf("%d", x)``` for csmith.

## Roadmap
- [ ] TBAA support
- [ ] lifetime/invariant support
- [ ] Fine-grained UB check control
- [ ] Turn it into a library
- [ ] Per-pass UB-aware testing
- [ ] EMI-based fuzzing
