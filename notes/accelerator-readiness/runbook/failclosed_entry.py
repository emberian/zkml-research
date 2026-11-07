"""Kaggle T4 check that the paid-box scripts fail CLOSED and that the dry run builds the way the box does
(initiative 17, after accel-h100-all-02 printed rc 0 for three failed steps). Runs, from the same bundles the
box gets, under the same `bash -c` composite the box runner launches:
  good   tower256.sh --shrink   built from the bundle (rustup + cargo --locked + venv + pip), expect rc 0
  good   bfv.sh --shrink        venv + pinned cupy wheels (the box path, not --no-venv),     expect rc 0
  good   mma.sh --shrink        the box path,                                            expect rc 0
  broken tower256: one prover source file truncated                                 expect rc != 0
  broken bfv:      accel_rns_ntt.cu truncated (nvcc/NVRTC compile fails)            expect rc != 0
  broken mma:      probe_sm75.cu truncated, MANIFEST left as shipped (sha check)    expect rc != 0
  broken mma:      probe_sm75.cu truncated, MANIFEST regenerated (nvcc fails)       expect rc != 0
Writes ACCEL_RESULTS; exits 1 unless every expectation holds."""
import json, os, pathlib, shlex, subprocess, tarfile, time
HERE = pathlib.Path.cwd()
R = {"cases": {}}
def untar(name, dest):
    dest.mkdir(parents=True, exist_ok=True)
    with tarfile.open(HERE / name) as t:
        t.extractall(dest, filter="data")
def run(case, cwd, cmd, expect_zero, wall):
    # the box runner's composite: bash -c '<cmd>; echo X_RC=$?' (shlex-quoted, as vast_box.py now does)
    composite = f"{cmd}; echo X_RC=$?"
    t = time.time()
    p = subprocess.run(["bash", "-c", f"bash -c {shlex.quote(composite)}"], cwd=cwd, capture_output=True,
                       text=True, timeout=wall, env=dict(os.environ, ACCEL_OUT=str(cwd / ("out-" + case))))
    out = p.stdout + p.stderr
    rc_line = [l for l in out.splitlines() if l.startswith("X_RC=")]
    rc = int(rc_line[-1].split("=")[1]) if rc_line else None
    ok = (rc == 0) if expect_zero else (rc not in (0, None))
    R["cases"][case] = dict(rc=rc, expect_zero=expect_zero, ok=ok, seconds=round(time.time() - t, 1), tail=out[-1500:])
    print(case, "rc", rc, "ok", ok, round(time.time() - t, 1), "s", flush=True)
def truncate(p):
    b = p.read_bytes(); p.write_bytes(b[: len(b) // 2])
w = pathlib.Path("/tmp/accel/fc"); 
for name, sub in (("tower256-bundle.tar.gz", "good"), ("bfv-bundle.tar.gz", "bgood"), ("mma-bundle.tar.gz", "mgood"), ("tower256-bundle.tar.gz", "tbad"), ("bfv-bundle.tar.gz", "bbad"),
                  ("mma-bundle.tar.gz", "mbad1"), ("mma-bundle.tar.gz", "mbad2")):
    untar(name, w / sub)
run("tower256_good", w / "good", "bash tower256/tower256.sh --shrink", True, 1500)
run("bfv_good", w / "bgood", "bash bfv/notes/accelerator-readiness/runbook/bfv.sh --sku T4 --shrink", True, 1200)
run("mma_good", w / "mgood", "bash mma/mma.sh --shrink", True, 900)
srcs = sorted((w / "tbad/tower256/prover/src").rglob("tower256_fri_fast*.rs")) or sorted((w / "tbad/tower256/prover/src").rglob("*.rs"))
truncate(srcs[0]); R["tower256_broken_file"] = srcs[0].name
run("tower256_broken_build", w / "tbad", "bash tower256/tower256.sh --shrink", False, 900)
truncate(w / "bbad/bfv/research/dark_learning_2026_11_06/accel_rns_ntt.cu")
run("bfv_broken_build", w / "bbad", "bash bfv/notes/accelerator-readiness/runbook/bfv.sh --sku T4 --shrink", False, 900)
truncate(w / "mbad1/mma/src/probe_sm75.cu")
run("mma_broken_manifest", w / "mbad1", "bash mma/mma.sh --shrink", False, 600)
truncate(w / "mbad2/mma/src/probe_sm75.cu")
subprocess.run("cd mma/src && sha256sum probe.cu probe_fixed.cu probe_sm75.cu probe_sm80.cu gemm_probe.cu rotation_probe.cu mma_run.py t256_vectors.jsonl > MANIFEST",
               shell=True, cwd=w / "mbad2", check=True)
run("mma_broken_build", w / "mbad2", "bash mma/mma.sh --shrink", False, 900)
R["all_ok"] = all(c["ok"] for c in R["cases"].values())
good = w / "good" / "out-tower256_good" / "results.json"
if good.exists():
    g = json.loads(good.read_text())
    R["tower256_good_all_bit_exact"] = g.get("all_bit_exact")
pathlib.Path(os.environ["ACCEL_RESULTS"]).write_text(json.dumps(R, indent=1))
print("ALL_OK", R["all_ok"], flush=True)
raise SystemExit(0 if R["all_ok"] else 1)
