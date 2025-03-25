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

## Automatic UB-Free Test Case Reduction for Middle-End Miscompilation Bugs

test.sh:
```
#!/usr/bin/bash

MAX_STEPS=1000000
a=$(<path to llubi> --max-steps $MAX_STEPS --reduce-mode $1)
if [ $? -ne 0 ]; then
    exit 1
fi
<path to opt> <options> $1 -o $1.tmp
if [ $? -ne 0 ]; then
    exit 1
fi
b=$(<path to llubi> --max-steps $MAX_STEPS --reduce-mode $1.tmp)
if [ $? -ne 0 ]; then
    rm $1.tmp
    exit 0
fi
if [[ $a == $b ]]; then
    rm $1.tmp
    exit 1
fi
rm $1.tmp
exit 0
```

Usage:
```
clang -O3 -Xclang -disable-llvm-passes -emit-llvm -S test.c -o test.ll
llvm-reduce --test=test.sh --ir-passes="function(sroa,instcombine<no-verify-fixpoint>,gvn,simplifycfg,infer-address-spaces),inline" test.ll
```

Please refer to [this example](https://github.com/llvm/llvm-project/issues/131465#issuecomment-2727536818) if you find it hard to get a valid reproducer.
BTW, an automatic reproducer reduction pipeline will be available soon :)  

## Fuzzing with Csmith
```
python3 csmith.py <llvm install dir> <csmith install dir> <path to llubi> <test count> [emi]
```
If `emi` is set, it will enable the EMI-based mutation. For more details, please refer to [Compiler validation via equivalence modulo inputs, PLDI'21](https://dl.acm.org/doi/10.1145/2594291.2594334).

## Fuzzing with Rustlantis
[Rustlantis](https://github.com/dtcxzyw/rustlantis) has been adapted to support llubi.

```
git clone https://github.com/dtcxzyw/rustlantis.git
cp rustlantis/config.toml.example ./config.toml
echo "llubi_path=$(pwd)/build/llubi" >>config.toml
python3 rustlantis.py ./rustlantis <test count>
```

## Limitations
We did some refinements on the LLVM LangRef to make the implementation practical and efficient:

+ Undef values are not supported as we will eventually remove undef from LLVM in the future. In llubi, they are treated as zero values.
+ FFI is not supported. Currently it only supports ```printf("%d", x)``` for csmith. Some rust standard library functions are patched to support rustlantis.
+ Addresses of allocations are unique. That is, we cannot model the behavior of stack coloring in llubi.
+ Pointer aliasing has not been supported yet.
+ Pointer provenance and capture tracking support is limited. We do not track the capabilities of pointers if it is stored into memory or converted to an integer.
+ We do not maintain the precise poison semantics in memory when ```memcpy/memmove/memset``` is called.
+ We do not check ```externally observable sideeffects``` strictly as required by ```memory(read)/readonly```. The current implementation just works for these two fuzzers.
+ Volatile memory accesses are partially supported. We only record total number of bytes that are loaded/stored via volatile memory ops.

## License

This repository is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.

## Citation

Please cite this work with the following BibTex entry:

```
@misc{llubi,
  title = {LLVM UB-Aware Interpreter},
  url = {https://github.com/dtcxzyw/llvm-ub-aware-interpreter},
  author = {Yingwei Zheng},
  year = {2024},
}
```
