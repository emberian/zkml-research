"""Kaggle T4 entry (redesign lane): packed-binary encode on the Xeon core and the T4, bit-exact across both
and against check_encode.py's Lagrange reference; Keccak-f/s on the same core. Writes ACCEL_RESULTS."""
import json, os, subprocess, sys

def sh(cmd, t=900):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=t)
    print("$", cmd, "\n", (r.stdout + r.stderr)[-4000:], flush=True)
    return r

res = {"checks": [], "cpu": [], "gpu": [], "ok": True}
out = os.environ.get("ACCEL_RESULTS", "results.json")
try:
    res["cpu_model"] = sh("grep -m1 'model name' /proc/cpuinfo").stdout.strip()
    assert sh("gcc -O3 -march=native -o encode encode.c").returncode == 0
    for a in ("3 3", "4 17", "5 36"):
        r = sh(f"{sys.executable} -I check_encode.py ./encode {a}")
        res["checks"].append(json.loads(r.stdout.strip().splitlines()[-1])); res["ok"] &= r.returncode == 0
    res["keccak"] = json.loads(sh("./encode keccak 2000000").stdout.splitlines()[0])
    shapes = [(8, 16), (10, 64), (10, 256), (12, 256), (12, 1024), (14, 256)]
    for e, R in ([] if os.environ.get("SKIP_CPU") else shapes):
        res["cpu"].append(json.loads(sh(f"./encode bench {e} {R} 5").stdout))
    # packed-binary PIOP on this Xeon core (piop_ref.py verifies transcripts; bench reports ns/row, mults/row)
    if sh("gcc -O3 -march=native -o piop piop.c -lpthread").returncode == 0:
        res["piop_checks"] = []
        for a in ("5", "8", "8 77", "9 300"):
            r = sh(f"{sys.executable} -I piop_ref.py ./piop {a}")
            res["piop_checks"].append(json.loads(r.stdout.strip().splitlines()[-1])); res["ok"] &= r.returncode == 0
        res["piop"] = [json.loads(sh(f"./piop bench {e} {rp} {t}").stdout) for e, rp, t in ((12, 30, 1), (14, 30, 1), (18, 5, 1), (14, 30, 4))]
    r = sh("nvcc -O3 -arch=sm_75 -o encode_gpu encode_gpu.cu")
    sh("nvcc -O3 -arch=sm_75 -DTABLE_GATHER -o encode_gpu_gather encode_gpu.cu")
    sh("nvcc -O3 -arch=sm_75 -DS_MAX=5 -DRWT=64 -o encode_gpu_s5 encode_gpu.cu")
    res["nvcc_rc"] = r.returncode
    if r.returncode == 0:
        res["nvidia_smi"] = sh("nvidia-smi --query-gpu=name,clocks.sm,clocks.max.sm,power.limit --format=csv,noheader").stdout.strip()
        for e, R in shapes + [(14, 1024)]:
            g = json.loads(sh(f"./encode_gpu {e} {R} 10").stdout)
            cpu = [c for c in res["cpu"] if c["ell"] == e and c["R"] == R]
            if cpu:
                g["digest_equals_cpu"] = g.get("cw_lo_digest") == cpu[0]["cw_lo_digest"]; res["ok"] &= g["digest_equals_cpu"]
            res["gpu"].append(g)
        res["gpu_fused"] = []
        for exe in ("./encode_gpu_gather", "./encode_gpu", "./encode_gpu_s5"):
            for e, R in [(10, 256), (12, 256), (12, 1024), (14, 256), (14, 1024)]:
                g = json.loads(sh(f"{exe} {e} {R} 10 fused").stdout)
                g["variant"] = exe
                ref = [x for x in res["gpu"] if x["ell"] == e and x["R"] == R]
                g["digest_equals_per_layer"] = bool(ref) and g.get("cw_lo_digest") == ref[0]["cw_lo_digest"]
                res["ok"] &= g["digest_equals_per_layer"]; res["gpu_fused"].append(g)
        res["nvidia_smi_after"] = sh("nvidia-smi --query-gpu=clocks.sm --format=csv,noheader").stdout.strip()
except Exception as ex:
    res["ok"] = False; res["error"] = repr(ex)
json.dump(res, open(out, "w"), indent=1)
print(json.dumps({"ok": res["ok"]}))
sys.exit(0 if res["ok"] else 1)
