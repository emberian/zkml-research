"""Kaggle T4 dry run of the paid-box script itself: runs `bash runbook/bfv.sh --shrink --sku T4 --no-venv`
from the bundled repo layout and copies its results.json to $ACCEL_RESULTS (lane w1-bfv, initiative 17)."""
import os, pathlib, shutil, subprocess, sys
root = pathlib.Path.cwd()
out = pathlib.Path("/tmp/accel/bfv-out")
env = dict(os.environ, ACCEL_OUT=str(out))
rc = subprocess.call(["bash", str(root / "notes/accelerator-readiness/runbook/bfv.sh"), "--shrink", "--sku", "T4",
                      "--no-venv"], env=env)
for name in ("results.json", "env.txt", "box.json"):
    if (out / name).exists():
        dst = pathlib.Path(os.environ["ACCEL_RESULTS"]) if name == "results.json" else \
            pathlib.Path(os.environ["ACCEL_RESULTS"]).with_name(name)
        shutil.copy(out / name, dst)
sha = out / "src" / "SHA256SUMS"
if sha.exists():
    print(sha.read_text())
sys.exit(rc)
