"""Kaggle T4, one session (initiative 14's ROTATION free probe): the Tower256 fixed-r multiply as an INT8 (and FP16)
0/1 dense GEMM with parity repack (degg-research rotation_probe.cu `towermul`, through mma.sh --sections towermul,
checked against Rust binary_tower_256.rs products) against the log/exp table multiply (minidregg
lane/accel-tower256-gpu tower256_fri.cu, through tower256.sh --shrink with --bitslice-bench, which times the table
kernel beside the bit-sliced one). Both from the paid-box bundles, built the way the box builds them.
Ratio = table ns per multiply / tensor ns per element (> 1: the tensor route wins)."""
import json, os, pathlib, shlex, subprocess, tarfile, time
HERE = pathlib.Path.cwd(); w = pathlib.Path("/tmp/accel/tmul")
R = {}
for name, sub in (("mma-bundle.tar.gz", "m"), ("tower256-bundle.tar.gz", "t")):
    (w / sub).mkdir(parents=True, exist_ok=True)
    with tarfile.open(HERE / name) as t:
        t.extractall(w / sub, filter="data")
def run(tag, cwd, cmd, env=None):
    t = time.time()
    p = subprocess.run(["bash", "-c", cmd], cwd=cwd, env=dict(os.environ, ACCEL_OUT=str(cwd / "out"), **(env or {})),
                       capture_output=True, text=True, timeout=1500)
    R[tag + "_rc"] = p.returncode; R[tag + "_s"] = round(time.time() - t, 1)
    print(tag, "rc", p.returncode, R[tag + "_s"], "s", flush=True); print((p.stdout + p.stderr)[-2500:], flush=True)
run("mma", w / "m", "bash mma/mma.sh --shrink --sections compile,towermul")
run("tower", w / "t", "bash tower256/tower256.sh --shrink", {"TOWER256_GPU_ARGS": "--bitslice-bench"})
m = json.loads((w / "m/out/results.json").read_text()) if (w / "m/out/results.json").exists() else {}
t = json.loads((w / "t/out/results.json").read_text()) if (w / "t/out/results.json").exists() else {}
R["towermul"] = m.get("towermul"); R["mma_checks"] = {k: v for k, v in m.get("checks", {}).items() if k.startswith("towermul")}
R["bitslice_bench"] = t.get("bitslice_bench") or {k: v for k, v in t.items() if "mul" in k.lower()}
R["tower_all_bit_exact"] = t.get("all_bit_exact")
pathlib.Path(os.environ["ACCEL_RESULTS"]).write_text(json.dumps(R, indent=1, default=str))
ok = R["mma_rc"] == 0 and R["tower_rc"] == 0
print("DONE ok", ok, flush=True)
raise SystemExit(0 if ok else 1)
