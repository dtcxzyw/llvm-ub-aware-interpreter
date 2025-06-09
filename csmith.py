#!/usr/bin/env python3

from multiprocessing import Pool
from tqdm import tqdm
import os
import sys
import subprocess
import shutil
import tqdm
import datetime
import random

# python3 ../csmith.py /usr ../../csmith/install/ ./llubi 1

llvm_dir = sys.argv[1]
csmith_dir = sys.argv[2]
llubi_bin = sys.argv[3]
test_count = int(sys.argv[4])
emi = len(sys.argv) >= 6 and sys.argv[5] == "emi"
inconsistent = len(sys.argv) >= 6 and sys.argv[5] == "inconsistency"
stepbystep = len(sys.argv) >= 6 and sys.argv[5] == "stepbystep"
if emi:
    print("EMI-based mutation is enabled")
if inconsistent:
    print("Inconsistency check is enabled")
if stepbystep:
    print("Step-by-step check is enabled")
csmith_command = (
    csmith_dir
    + "/bin/csmith --max-funcs 3 --max-block-depth 5 --quiet --builtins --no-packed-struct --no-unions --no-bitfields --output "
)
compile_command = llvm_dir + "/bin/clang -DNDEBUG -g0 -w -I" + csmith_dir + "/include "
comp_timeout = 10.0
exec_timeout = 1.0
llubi_workarounds = [
    # https://github.com/llvm/llvm-project/issues/115890
    "--ignore-param-attrs-intrinsic",
    "--non-global-value-max-name-size=4096",
]
if not inconsistent:
    # llubi_workarounds.append('--track-volatile-mem')
    pass

cwd = "csmith" + datetime.datetime.now().strftime("%Y-%m-%d@%H:%M")
os.makedirs(cwd)

no_report_env = {
    "LLVM_DISABLE_CRASH_REPORT": "1",
    "LLVM_DISABLE_SYMBOLIZATION": "1",
}


def check_step_by_step(file_c, basename):
    file_o0_output = basename + ".O0.ll"
    try:
        comp_command = (
            compile_command
            + " -o "
            + file_o0_output
            + " "
            + file_c
            + " -O3 -Xclang -disable-llvm-passes -emit-llvm -S"
        )
        subprocess.check_call(
            comp_command.split(" "),
            timeout=comp_timeout,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        os.remove(file_c)
        return None

    try:
        ref_out = subprocess.check_output(
            [llubi_bin, file_o0_output] + llubi_workarounds,
            timeout=exec_timeout * 5,
            env=no_report_env,
        )
    except subprocess.TimeoutExpired:
        # Ignore timeout
        os.remove(file_c)
        os.remove(file_o0_output)
        return True
    except Exception:
        return False

    idx = 1
    while True:
        file_i_output = basename + "." + str(idx) + ".ll"
        try:
            comp_command = (
                compile_command
                + " -o "
                + file_i_output
                + " "
                + file_c
                + " -O3 -emit-llvm -S"
                + " -mllvm -opt-bisect-limit="
                + str(idx)
            )
            ret = subprocess.run(
                comp_command.split(" "),
                timeout=comp_timeout,
                check=True,
                capture_output=True,
            )
            if f"({idx})" not in ret.stderr.decode():
                os.remove(file_c)
                os.remove(file_i_output)
                os.remove(file_o0_output)
                return True
        except Exception:
            os.remove(file_c)
            os.remove(file_o0_output)
            return None

        try:
            out = subprocess.check_output(
                [llubi_bin, file_i_output] + llubi_workarounds,
                timeout=exec_timeout * 5,
                env=no_report_env,
            )
        except subprocess.TimeoutExpired:
            # Ignore timeout
            os.remove(file_c)
            os.remove(file_i_output)
            return True
        except Exception:
            return False

        if out != ref_out:
            return False
        os.remove(file_i_output)
        idx += 1


def csmith_test(i):
    basename = cwd + "/test" + str(i)
    file_c = basename + ".c"
    try:
        subprocess.check_call((csmith_command + file_c).split(" "))
    except subprocess.SubprocessError:
        return None

    if stepbystep:
        return check_step_by_step(file_c, basename)

    file_out = basename + ".ll"
    try:
        comp_command = compile_command + " -o " + file_out + " " + file_c
        subprocess.check_call(comp_command.split(" "), timeout=comp_timeout)
    except subprocess.TimeoutExpired:
        os.remove(file_c)
        if os.path.exists(file_out):
            os.remove(file_out)
        return None
    except subprocess.CalledProcessError:
        return False

    try:
        subprocess.check_call(
            [file_out],
            timeout=exec_timeout,
            stderr=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
        )
        subprocess.check_call(
            (
                comp_command
                + " -O3 -emit-llvm -S"
                + (
                    " -mllvm -opt-bisect-limit=" + str(random.randint(0, 1000))
                    if emi
                    else ""
                )
            ).split(" "),
            timeout=comp_timeout,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        if os.path.exists(file_out):
            os.remove(file_out)
        os.remove(file_c)
        return None

    if emi:
        file_emi_out = basename + ".emi.ll"
        try:
            ref_out = subprocess.check_output(
                [llubi_bin, file_out, "--emi", file_emi_out] + llubi_workarounds,
                timeout=exec_timeout,
                env=no_report_env,
            )
        except subprocess.TimeoutExpired:
            # Ignore timeout
            os.remove(file_c)
            os.remove(file_out)
            if os.path.exists(file_emi_out):
                os.remove(file_emi_out)
            return None
        except Exception:
            return False

        file_emi_opt_out = basename + ".emiopt.ll"
        try:
            subprocess.check_call(
                [
                    llvm_dir + "/bin/opt",
                    "-O3",
                    file_emi_out,
                    "-S",
                    "-o",
                    file_emi_opt_out,
                ],
                timeout=comp_timeout,
                stderr=subprocess.DEVNULL,
            )
        except subprocess.TimeoutExpired:
            # Ignore timeout
            os.remove(file_c)
            os.remove(file_out)
            os.remove(file_emi_out)
            return None
        except Exception:
            return False

        try:
            out = subprocess.check_output(
                [llubi_bin, file_emi_opt_out] + llubi_workarounds,
                timeout=exec_timeout * 5,
                env=no_report_env,
            )
        except subprocess.TimeoutExpired:
            # Ignore timeout
            os.remove(file_c)
            os.remove(file_out)
            os.remove(file_emi_out)
            os.remove(file_emi_opt_out)
            return True
        except Exception:
            return False

        if out == ref_out:
            os.remove(file_c)
            os.remove(file_out)
            os.remove(file_emi_out)
            os.remove(file_emi_opt_out)
            return True

    else:
        if inconsistent:
            try:
                ref_out = subprocess.check_output(
                    [llvm_dir + "/bin/lli", file_out],
                    timeout=exec_timeout,
                    stderr=subprocess.DEVNULL,
                )
            except Exception:
                os.remove(file_c)
                os.remove(file_out)
                return None
        else:
            file_o0_output = basename + ".O0.ll"
            try:
                comp_command = (
                    compile_command
                    + " -o "
                    + file_o0_output
                    + " "
                    + file_c
                    + " -O3 -Xclang -disable-llvm-passes -emit-llvm -S"
                )
                subprocess.check_call(
                    comp_command.split(" "),
                    timeout=comp_timeout,
                    stderr=subprocess.DEVNULL,
                )
            except Exception:
                os.remove(file_out)
                os.remove(file_c)
                return None

            try:
                ref_out = subprocess.check_output(
                    [llubi_bin, file_o0_output] + llubi_workarounds,
                    timeout=exec_timeout * 5,
                    env=no_report_env,
                )
            except subprocess.TimeoutExpired:
                # Ignore timeout
                os.remove(file_c)
                os.remove(file_out)
                os.remove(file_o0_output)
                return None
            except Exception:
                return False

        try:
            out = subprocess.check_output(
                [llubi_bin, file_out]
                + llubi_workarounds
                + ["--verify-value-tracking", "--verify-scev-res", "--verify-lvi"],
                timeout=exec_timeout * 5,
                env=no_report_env,
            )
        except subprocess.TimeoutExpired:
            # Ignore timeout
            os.remove(file_c)
            os.remove(file_out)
            if not inconsistent:
                os.remove(file_o0_output)
            return None
        except Exception:
            return False

        if out == ref_out:
            os.remove(file_c)
            os.remove(file_out)
            if not inconsistent:
                os.remove(file_o0_output)
            return True
    return False


L = list(range(test_count))
pbar = tqdm.tqdm(L)
error_count = 0
skipped_count = 0
pool = Pool(os.cpu_count())

for res in pool.imap_unordered(csmith_test, L):
    if res is not None:
        error_count += 0 if res else 1
    else:
        skipped_count += 1

    pbar.set_description(
        "Failed: {} Skipped: {}".format(error_count, skipped_count), refresh=False
    )
    pbar.update(1)
pbar.close()

if error_count == 0:
    shutil.rmtree(cwd)
