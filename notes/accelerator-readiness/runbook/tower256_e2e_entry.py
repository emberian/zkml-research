"""Kaggle T4, accel-tower-e2e-01: the whole Tower256 leaf prover end to end on the GPU, from the
paid-box bundle built the way the box builds it (tower256-bundle.sh; tower256.sh --shrink --e2e,
online: accel_venv + pinned pip, rustup 1.89.0 and cargo build --locked of the bundle's prover).
Every receipt is checked byte for byte against the CPU prover's on the same box."""
import json, os, pathlib, subprocess, tarfile, time
HERE = pathlib.Path.cwd(); w = pathlib.Path("/tmp/accel/e2e")
w.mkdir(parents=True, exist_ok=True)
with tarfile.open(HERE / "tower256-bundle.tar.gz") as t:
    t.extractall(w, filter="data")
t0 = time.time()
p = subprocess.run(["bash", "tower256/tower256.sh", "--shrink", "--e2e", "--sku", "T4"], cwd=w,
                   env=dict(os.environ, ACCEL_OUT=str(w / "out")), timeout=2900)
res_p = w / "out/results.json"
R = json.loads(res_p.read_text()) if res_p.exists() else {}
R["script_rc"] = p.returncode
R["script_s"] = round(time.time() - t0, 1)
pathlib.Path(os.environ["ACCEL_RESULTS"]).write_text(json.dumps(R, indent=1, default=str))
print("DONE rc", p.returncode, "all_bit_exact", R.get("all_bit_exact"), flush=True)
raise SystemExit(0 if p.returncode == 0 else 1)
