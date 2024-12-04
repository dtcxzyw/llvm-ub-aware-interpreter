#!/usr/bin/env python3

import os
import sys
import subprocess
import shutil

# python3 emireduce.py <path to opt> <llbui build dir> <src ir> <reduced ir>

# TODO: pass sequence reduction
opt_bin = sys.argv[1]
ubi_path = sys.argv[2]
llubi_bin = os.path.join(ubi_path, "llubi")
if not os.path.exists(llubi_bin):
    print("llubi not found")
    sys.exit(1)
emireduce_bin = os.path.join(ubi_path, "emireduce")
if not os.path.exists(emireduce_bin):
    print("emireduce not found")
    sys.exit(1)
src_ir = sys.argv[3]
reduced_ir = sys.argv[4]
reduced_tmp_ir = reduced_ir.removesuffix(".ll") + ".tmp.ll"
reduced_opt_ir = reduced_ir.removesuffix(".ll") + ".opt.ll"
max_retrial = 100

def exec_ir(path):
    try:
        return subprocess.check_output([llubi_bin, path, "--max-steps", "100000000"], stderr=subprocess.DEVNULL).decode("utf-8")
    except Exception:
        return None

def reduce_ir(path, output_path):
    try:
        out = subprocess.check_output([emireduce_bin, path, output_path]).decode("utf-8")
        if "No changes" in out:
            return None
        return out
    except Exception:
        print("Internal bug")
        exit(-1)

def opt_ir(path, output_path):
    try:
        subprocess.check_output([opt_bin, "-S", "-O3", path, "-o", output_path])
        return True
    except Exception:
        return False

shutil.copyfile(src_ir, reduced_ir)
ref_output = exec_ir(reduced_ir)
orig_size = os.path.getsize(reduced_ir)
if not opt_ir(reduced_ir, reduced_opt_ir):
    print("Failed to optimize")
    sys.exit(1)
wrong_output = exec_ir(reduced_opt_ir)
if ref_output == wrong_output:
    print("Test case is not interesting")
    sys.exit(0)

def reduce_once():
    ref_output = reduce_ir(reduced_ir, reduced_tmp_ir)
    if ref_output is None:
        return False
    if not opt_ir(reduced_tmp_ir, reduced_opt_ir):
        os.remove(reduced_tmp_ir)
        return False
    cur_output = exec_ir(reduced_opt_ir)
    if cur_output == ref_output:
        os.remove(reduced_tmp_ir)
        os.remove(reduced_opt_ir)
        return False
    shutil.move(reduced_tmp_ir, reduced_ir)
    os.remove(reduced_opt_ir)
    return True

reduce_iter = 0
reduce_fail_count = 0
while True:
    reduce_iter += 1
    current_size = os.path.getsize(reduced_ir)
    print(f"Iteration {reduce_iter} {current_size} bytes ({current_size/orig_size*100:.2f}%) fail count {reduce_fail_count}")
    if reduce_once():
        reduce_fail_count = 0
    else:
        reduce_fail_count += 1
        if reduce_fail_count >= max_retrial:
            break
opt_ir(reduced_ir, reduced_opt_ir)

print(f"Final size {os.path.getsize(reduced_ir)} bytes ({os.path.getsize(reduced_ir)/orig_size*100:.2f}%)")
