"""Kaggle T4 entry (redesign lane, migration step 1): the GPU host's receipt with Python openings and with
native openings (tower256_openings.c), every receipt checked against the CPU prover's expected bytes
(expect_ell*.json) and, in the --openings-check run, the native bytes against the Python bytes every round."""
import json, os, subprocess, sys
def sh(c, t=1500):
    r = subprocess.run(c, shell=True, capture_output=True, text=True, timeout=t); print("$", c, "\n", (r.stdout + r.stderr)[-3000:], flush=True); return r
res = {"runs": {}}
out = os.environ.get("ACCEL_RESULTS", "results.json")
cc = sh("nvidia-smi --query-gpu=compute_cap --format=csv,noheader").stdout.split()[0].replace(".", "")
ok = sh(f"nvcc -arch=sm_{cc} -O3 -cubin -o t.cubin tower256_fri.cu").returncode == 0
ok &= sh("cc -O2 -shared -fPIC -o tower256_openings.so tower256_openings.c").returncode == 0
os.environ["T256_OPENINGS_LIB"] = os.path.abspath("tower256_openings.so")
for name, extra in (("native_checked", "--native-openings --openings-check"), ("native", "--native-openings")):
    r = sh(f"{sys.executable} tower256_gpu.py --data data --cubin {os.path.abspath('t.cubin')} --ells 14,18,20 --reps 3 --out r_{name}.json {extra}")
    try:
        res["runs"][name] = json.load(open(f"r_{name}.json"))
    except Exception as e:
        res["runs"][name] = {"error": repr(e)}
    ok &= r.returncode == 0
res["ok"] = bool(ok)
json.dump(res, open(out, "w"), indent=1)
sys.exit(0 if ok else 1)
