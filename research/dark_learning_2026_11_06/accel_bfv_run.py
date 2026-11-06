"""One entry for the BFV device measurement (Kaggle T4 dry run and the paid H100/B200 box alike):
NTT tuning sweep (accel_bench_cuda) -> best exact shape per (N, L) -> return pipeline check + bench +
per-step extrapolation (accel_he_bench). 2026-11-06, accelerator readiness (initiative 17), lane w1-bfv.

    python3 accel_bfv_run.py --shrink     # exactly the Kaggle T4 dry run
    python3 accel_bfv_run.py              # full: N in {8192, 16384}, L in {3, 4}, full sweep, larger batches
Results: $ACCEL_RESULTS (JSON), progress on stdout.
"""
import json
import os
import pathlib
import shlex
import subprocess
import sys
import time

import accel_bench_cuda as B
import accel_he_bench as H

def main():
    argv = shlex.split(" ".join(sys.argv[1:]))
    shrink = "--shrink" in argv
    import cupy as cp
    dev = cp.cuda.runtime.getDeviceProperties(0)
    out = pathlib.Path(os.environ.get("ACCEL_RESULTS", "accel_bfv_run.json"))
    res = dict(device=dev["name"].decode(), sm=f"{dev['major']}{dev['minor']}", n_devices=cp.cuda.runtime.getDeviceCount(),
               smi=subprocess.run("nvidia-smi --query-gpu=name,memory.total,clocks.max.sm,clocks.max.memory --format=csv,noheader",
                                  shell=True, capture_output=True, text=True).stdout.strip(),
               cupy=cp.__version__, shrink=shrink, sweeps={}, he={})
    log = lambda s: print(s, flush=True)
    log("device %s sm %s x%d shrink=%s" % (res["device"], res["sm"], res["n_devices"], shrink))
    t0 = time.time()
    configs = [(8192, 3), (16384, 3), (8192, 4), (16384, 4)]
    ok = True
    for N, L in configs:
        key = f"N{N}_L{L}"
        rows = (384 if shrink else 1536) * L // 3
        recs = B.sweep(N, L, rows, shrink, lambda s: log(key + " " + s))
        good = [r for r in recs if "error" not in r and r["same_words_as_first"] and r["roundtrip_ok"]]
        ref = recs[0].get("ref_check", {})
        exact = bool(ref.get("fwd_ok") and ref.get("roundtrip_ok")) and len(good) == len(recs)
        best = min(good, key=lambda r: r["fwd_us_per_ntt"] + r["inv_us_per_ntt"]) if good else None
        res["sweeps"][key] = dict(records=recs, best=best, ref_check=ref, all_exact=exact)
        ok &= exact
        log("%s sweep exact=%s best=%s" % (key, exact, json.dumps(best)))
        out.write_text(json.dumps(res, indent=1))
        if best is None:
            continue
        mode = 0 if best["mode"] == "shoup" else 1
        ctx = B.Ctx(N, L, mode, best["logE"], best["logC"], best["threads"], best["G"])
        run = dict(shape=best, clocks_before=B.clocks())
        run["us_per_ntt_after_sweep"] = H.ntt_rate(ctx, rows, 10)
        run["check"] = H.check(ctx, 2 if shrink else 3, log)
        ok &= run["check"]["ok"]
        nret = (128 if shrink else 512) * 8192 * 3 // (N * L)
        reps = 3 if shrink else 10
        run["us_per_ntt"] = H.ntt_rate(ctx, nret * L, reps)
        run["clocks_after_check"] = B.clocks()
        run["outer"] = H.bench(ctx, nret, 1, reps, log)
        nr = max(16, nret // 4)
        Kbig = 64 if N == 8192 else 64
        run["matvec_K1"] = H.bench(ctx, nr, 1, reps, log)
        run["matvec_Kbig"] = H.bench(ctx, nr, Kbig, reps, log)
        run["step"] = H.extrapolate(N, L, run["outer"]["us_per_return"]["return_total"],
                                    run["matvec_K1"]["us_per_return"]["return_total"],
                                    (Kbig, run["matvec_Kbig"]["us_per_return"]["return_total"]), run["us_per_ntt"])
        run["clocks_after_bench"] = B.clocks()
        log(key + " step " + json.dumps(run["step"]) + " clocks " + run["clocks_after_bench"])
        res["he"][key] = run
        res["elapsed_s"] = time.time() - t0
        out.write_text(json.dumps(res, indent=1))
        del ctx
        cp.get_default_memory_pool().free_all_blocks()
    res["compile_s"] = getattr(B.Ctx, "compile_s", None)
    res["all_exact"] = ok
    res["elapsed_s"] = time.time() - t0
    out.write_text(json.dumps(res, indent=1))
    log("ALL EXACT" if ok else "EXACTNESS FAILURE")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
