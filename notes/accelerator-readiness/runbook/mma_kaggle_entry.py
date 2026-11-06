"""Kaggle T4 dry run of the paid-box script itself (initiative 17, workload 3): bash mma.sh --shrink.
Runs from the unpacked bundle (cwd = bundle root holding mma.sh, common.sh, src/).  Needs internet for the
pinned toolkit and CUTLASS downloads.  Copies results.json to ACCEL_RESULTS and a log tail to stdout."""
import os
import pathlib
import shutil
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
out = pathlib.Path("/tmp/accel/mma-sh-out")
env = dict(os.environ, ACCEL_OUT=str(out), ACCEL_CACHE="/tmp/accel/cache")
PRESETS = {"nocutlass": ["--no-cutlass"]}   # bare words: the Kaggle harness cannot pass dashed arguments
args = ["--shrink", "--sku", "T4", "--toolkit", "conda"] + [x for w in sys.argv[1:] for x in PRESETS.get(w, [w])]
cmd = ["bash", str(here / "mma.sh")] + args
print("RUN", " ".join(cmd), flush=True)
rc = subprocess.call(cmd, env=env)
res = out / "results.json"
if res.exists() and os.environ.get("ACCEL_RESULTS"):
    shutil.copy(res, os.environ["ACCEL_RESULTS"])
print("mma.sh rc", rc, flush=True)
sys.exit(rc)
