#!/usr/bin/env python3

from multiprocessing import Pool
from tqdm import tqdm
import os
import sys
import subprocess
import shutil
import tqdm
import datetime
import secrets

# python3 ../rustlantis.py ../../LLVM/rustlantis 1

rustlantis_dir = sys.argv[1]
subprocess.check_call(["cargo", "build", "--release"], cwd=rustlantis_dir)
test_count = int(sys.argv[2])
generate = os.path.join(rustlantis_dir, "target/release/generate")
difftest = os.path.join(rustlantis_dir, "target/release/difftest")
timeout = 30.0

cwd = "rustlantis" + datetime.datetime.now().strftime("%Y-%m-%d@%H:%M")
os.makedirs(cwd)


def rustlantis_test(i):
    seed = secrets.randbelow(2**64)
    basename = cwd + "/test" + str(i) + "_" + hex(seed)[2:]
    file_rs = basename + ".rs"
    try:
        with open(file_rs, "w") as f:
            subprocess.check_call(
                [generate, str(seed)],
                timeout=timeout,
                stdout=f,
                stderr=subprocess.DEVNULL,
            )
    except subprocess.SubprocessError:
        if os.path.exists(file_rs):
            os.remove(file_rs)
        return None

    try:
        subprocess.check_call(
            [difftest, file_rs],
            timeout=timeout,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.SubprocessError:
        return False
    os.remove(file_rs)
    return True


L = list(range(test_count))
pbar = tqdm.tqdm(L)
error_count = 0
skipped_count = 0
pool = Pool(os.cpu_count())

for res in pool.imap_unordered(rustlantis_test, L):
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
