"""Kaggle entry for the workload-2 dry run: runs the paid-box script itself, shrunk and offline."""
import json
import os
import shutil
import subprocess
import sys

out = "/tmp/tower256-out"
os.chmod("bin/tower256_fri_fast_bench", 0o755)
env = dict(os.environ, ACCEL_OUT=out)
cmd = ["bash", "tower256.sh", "--shrink", "--offline", "--sku", "T4",
       "--rust-bin", os.path.abspath("bin/tower256_fri_fast_bench")] + sys.argv[1:]
rc = subprocess.call(cmd, env=env)
dst = os.environ.get("ACCEL_RESULTS", "results.json")
src = os.path.join(out, "results.json")
if os.path.exists(src):
    res = json.load(open(src))
else:
    res = {}
res["script_rc"] = rc
json.dump(res, open(dst, "w"), indent=1)
print("ENTRY_DONE rc", rc, "all_bit_exact", res.get("all_bit_exact"), flush=True)
sys.exit(rc)
