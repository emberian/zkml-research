"""cupy host harness for accel_rns_ntt.cu: device context (tables, kernels), bit-exact checks against
accel_rns_ref, and the NTT tuning sweep. 2026-11-06, accelerator readiness (initiative 17), lane w1-bfv.

    python3 accel_bench_cuda.py [--N 8192 16384] [--L 3 4] [--rows 768] [--quick]

Writes JSON to $ACCEL_RESULTS (or ./accel_bench_cuda.json). accel_he_bench.py imports Ctx from here.
Timing: cupy events around warm, synchronized launches; compile and transfers excluded and reported apart.
"""
import argparse
import json
import math
import os
import pathlib
import random
import shlex
import sys
import time

import numpy as np

import accel_rns_ref as R

HERE = pathlib.Path(__file__).resolve().parent
M64 = (1 << 64) - 1

def shoup_q(w, p):
    return (w << 64) // p

class Ctx:
    """Tables and kernels for one (N, L, MODE). MODE 0 = Shoup, 1 = Montgomery (see accel_rns_ntt.cu)."""
    _mod = None

    def __init__(self, N, L, mode=0, logE=None, logC=4, threads=256, G=1):
        import cupy as cp
        self.cp = cp
        self.N, self.L, self.mode = N, L, mode
        self.logN = N.bit_length() - 1
        self.Qp, self.t = R.primes(N, L)
        self.Q = math.prod(self.Qp)
        self.T = [R.Tables(q, N) for q in self.Qp]
        self.set_shape(logE if logE is not None else min(self.logN, 11), logC, threads, G)
        if Ctx._mod is None:
            src = (HERE / "accel_rns_ntt.cu").read_text()
            names = [f"{k}<{m}>" for k in ("fwdA", "fwdB", "invA", "invB", "ret_mac", "pmul_fixed") for m in (0, 1)]
            names += [f"{k}<{m}, {g}>" for k in ("fwdAr", "fwdBr", "invAr", "invBr") for m in (0, 1) for g in (2, 3, 4)]
            names += ["ret_finalize", "hps_decrypt", "gen_random", "shoup_quot", "to_mont"]
            t0 = time.perf_counter()
            mod = cp.RawModule(code=src, options=("-std=c++17",), name_expressions=names)
            for n in names:
                mod.get_function(n)
            Ctx.compile_s = time.perf_counter() - t0
            Ctx._mod = mod
        self.k = {n: Ctx._mod.get_function(f"{n}<{mode}>") for n in ("fwdA", "fwdB", "invA", "invB", "ret_mac", "pmul_fixed")}
        for n in ("ret_finalize", "hps_decrypt", "gen_random", "shoup_quot", "to_mont"):
            self.k[n] = Ctx._mod.get_function(n)
        self.mode = mode
        for g in (2, 3, 4):
            for n in ("fwdAr", "fwdBr", "invAr", "invBr"):
                self.k[f"{n}{g}"] = Ctx._mod.get_function(f"{n}<{mode}, {g}>")   # e.g. "fwdAr3"
        self.smem_max = cp.cuda.runtime.deviceGetAttribute(97, 0)   # cudaDevAttrMaxSharedMemoryPerBlockOptin
        for n, f in self.k.items():
            if n[:4] in ("fwdA", "fwdB", "invA", "invB"):
                f.max_dynamic_shared_size_bytes = self.smem_max
        tw, twq, itw, itwq, mc = [], [], [], [], []
        Rm = 1 << 64
        for q, T in zip(self.Qp, self.T):
            pn = (-pow(q, -1, Rm)) % Rm
            last = T.ipsi_brv[1] * T.ninv % q
            if mode == 0:
                tw.append(T.psi_brv); twq.append([shoup_q(w, q) for w in T.psi_brv])
                itw.append(T.ipsi_brv); itwq.append([shoup_q(w, q) for w in T.ipsi_brv])
                mc.append([q, pn, T.ninv, shoup_q(T.ninv, q), last, shoup_q(last, q), Rm * Rm % q, Rm % q])
            else:
                tw.append([w * Rm % q for w in T.psi_brv]); twq.append([0] * N)
                itw.append([w * Rm % q for w in T.ipsi_brv]); itwq.append([0] * N)
                mc.append([q, pn, T.ninv * Rm % q, 0, last * Rm % q, 0, Rm * Rm % q, Rm % q])
        u = lambda x: cp.asarray(np.array(x, dtype=np.uint64))
        self.tw, self.twq, self.itw, self.itwq, self.mc = u(tw), u(twq), u(itw), u(itwq), u(mc)
        self.mc_host = mc

    def set_shape(self, logE, logC, threads, G=1):
        self.logE = min(logE, self.logN)
        self.logR = self.logN - self.logE
        self.logC = min(logC, self.logE)
        self.threads = threads
        self.G = G
        if G == 1:
            self.kn = {n: n for n in ("fwdA", "fwdB", "invA", "invB")}
        else:
            self.kn = {n: f"{n}r{G}" for n in ("fwdA", "fwdB", "invA", "invB")}

    # ---- transforms on a [rows][N] uint64 buffer; row r uses prime r % L
    def fwd(self, buf, rows):
        cp, i32 = self.cp, np.int32
        if self.logR > 0:
            self.k[self.kn["fwdA"]](((self.N >> self.logR) >> self.logC, rows), (self.threads,),
                           (buf, self.tw, self.twq, self.mc, i32(self.logN), i32(self.logR), i32(self.logC), i32(self.L)),
                           shared_mem=8 << (self.logR + self.logC))
        self.k[self.kn["fwdB"]]((self.N >> self.logE, rows), (self.threads,),
                       (buf, self.tw, self.twq, self.mc, i32(self.logN), i32(self.logE), i32(self.L)),
                       shared_mem=8 << self.logE)

    def inv(self, buf, rows):
        i32 = np.int32
        self.k[self.kn["invB"]]((self.N >> self.logE, rows), (self.threads,),
                       (buf, self.itw, self.itwq, self.mc, i32(self.logN), i32(self.logE), i32(self.L)),
                       shared_mem=8 << self.logE)
        if self.logR > 0:
            self.k[self.kn["invA"]](((self.N >> self.logR) >> self.logC, rows), (self.threads,),
                           (buf, self.itw, self.itwq, self.mc, i32(self.logN), i32(self.logR), i32(self.logC), i32(self.L)),
                           shared_mem=8 << (self.logR + self.logC))

    def fixed(self, spec, rows):
        """A fixed operand (spectrum, [rows][N], row r prime r % L) in this MODE's form: (w, q)."""
        cp = self.cp
        w = spec.copy()
        q = cp.zeros_like(w)
        n = rows * self.N
        kern = self.k["shoup_quot"] if self.mode == 0 else self.k["to_mont"]
        kern(((n + 255) // 256,), (256,), (w, q, self.mc, np.int32(self.logN), np.int32(self.L), np.int64(n)))
        return w, q

    def timed(self, fn, reps=10, warm_s=0.2):
        """Warm the clocks (>= warm_s of back-to-back calls: GPUs drop P-state while the host runs Python
        checks; dry run accel-bfv-dry-t4-03 measured 2x slower NTTs without this), then time reps calls."""
        cp = self.cp
        t0 = time.perf_counter()
        while True:
            fn()
            cp.cuda.Device().synchronize()
            if time.perf_counter() - t0 >= warm_s:
                break
        e0, e1 = cp.cuda.Event(), cp.cuda.Event()
        e0.record()
        for _ in range(reps):
            fn()
        e1.record()
        e1.synchronize()
        return cp.cuda.get_elapsed_time(e0, e1) / 1e3 / reps

    def passes(self):
        return 1 if self.logR == 0 else 2

def ref_rows(host, ctx, rows_idx):
    """accel_rns_ref forward spectra for sampled rows of a host [rows][N] array."""
    return {r: [int(x) for x in R.fwd([int(v) for v in host[r]], ctx.T[r % ctx.L])] for r in rows_idx}

def clocks():
    """SM clock, power, temperature now (T4 throttles under sustained load; recorded beside timings)."""
    import subprocess
    return subprocess.run("nvidia-smi -i 0 --query-gpu=clocks.sm,power.draw,temperature.gpu --format=csv,noheader",
                          shell=True, capture_output=True, text=True).stdout.strip()

def ntt_check(ctx, rows, rng):
    """Device forward == reference on sampled rows (every word), inverse(forward) == input on every row."""
    cp = ctx.cp
    host = np.empty((rows, ctx.N), dtype=np.uint64)
    for r in range(rows):
        q = ctx.Qp[r % ctx.L]
        host[r] = np.array([rng.randrange(q) for _ in range(ctx.N)], dtype=np.uint64) if r < 2 * ctx.L else \
            (np.random.default_rng(r).integers(0, q, ctx.N, dtype=np.uint64))
    buf = cp.asarray(host)
    ctx.fwd(buf, rows)
    spec = cp.asnumpy(buf)
    sample = sorted({0, 1, rows - 1} | set(range(ctx.L)))
    ref = ref_rows(host, ctx, sample)
    fwd_ok = all(list(map(int, spec[r])) == ref[r] for r in sample)
    ctx.inv(buf, rows)
    round_ok = bool(np.array_equal(cp.asnumpy(buf), host))
    return dict(fwd_ref_rows=len(sample), fwd_ok=fwd_ok, roundtrip_rows=rows, roundtrip_ok=round_ok), spec

def sweep(N, L, rows, quick, log):
    """Every shape: forward words identical to the FIRST shape's on a fixed input (the first shape is checked
    word for word against accel_rns_ref on sampled rows, and inverse(forward) == input on all rows)."""
    import cupy as cp
    rng = random.Random(N * 10 + L)
    logN = N.bit_length() - 1
    shapes = []
    for mode in (0, 1):
        smem = cp.cuda.runtime.deviceGetAttribute(97, 0)
        for logE in (9, 10, 11, 12, 13, 14):
            if logE > logN or (8 << logE) > smem:
                continue
            for G in (1, 2, 3, 4):
                for th in (64, 128, 256, 512, 1024):
                    if th > ((1 << logE) >> G) or th < ((1 << logE) >> G) // 16:
                        continue
                    shapes.append((mode, logE, 4, th, G))
    if quick:
        shapes = [s for s in shapes if s[1] in (10, 11, 13) and s[4] in (1, 3) and s[3] in (128, 256)]
    ctxs, out, first = {}, [], None
    x = cp.asarray(np.random.default_rng(11).integers(0, min(R.primes(N, L)[0]), (rows, N), dtype=np.uint64))
    buf = x.copy()
    for mode, logE, logC, th, G in shapes:
        try:
            if mode not in ctxs:
                ctxs[mode] = Ctx(N, L, mode)
            ctx = ctxs[mode]
            ctx.set_shape(logE, logC, th, G)
            rec = dict(mode=["shoup", "mont"][mode], logE=logE, logC=logC, threads=th, G=G, passes=ctx.passes())
            if first is None:
                rec["ref_check"], _ = ntt_check(ctx, min(rows, 4 * L), rng)
            y = x.copy()
            ctx.fwd(y, rows)
            yw = cp.asnumpy(y)
            if first is None:
                first = yw
            rec["same_words_as_first"] = bool(np.array_equal(yw, first))
            ctx.inv(y, rows)
            rec["roundtrip_ok"] = bool(cp.array_equal(x, y))
            tf = ctx.timed(lambda: ctx.fwd(buf, rows))
            ti = ctx.timed(lambda: ctx.inv(buf, rows))
            byts = 2 * 8 * N * ctx.passes()
            rec.update(fwd_us_per_ntt=tf / rows * 1e6, inv_us_per_ntt=ti / rows * 1e6,
                       fwd_GBps=byts * rows / tf / 1e9, inv_GBps=byts * rows / ti / 1e9)
        except Exception as e:
            rec = dict(mode=mode, logE=logE, logC=logC, threads=th, G=G, error=repr(e)[:400])
        log(json.dumps(rec))
        out.append(rec)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="*", default=[8192, 16384])
    ap.add_argument("--L", type=int, nargs="*", default=[3, 4])
    ap.add_argument("--rows", type=int, default=768)
    ap.add_argument("--quick", action="store_true")
    a = ap.parse_args(shlex.split(" ".join(sys.argv[1:])))   # the Kaggle harness passes one quoted string
    import cupy as cp
    dev = cp.cuda.runtime.getDeviceProperties(0)
    res = dict(device=dev["name"].decode(), sm=f"{dev['major']}{dev['minor']}", n_devices=cp.cuda.runtime.getDeviceCount(),
               cupy=cp.__version__, sweeps={})
    print("device", res["device"], "sm", res["sm"], flush=True)
    out_path = os.environ.get("ACCEL_RESULTS", "accel_bench_cuda.json")
    for N in a.N:
        for L in a.L:
            key = f"N{N}_L{L}"
            recs = sweep(N, L, a.rows * L // 3, a.quick, lambda s: print(key, s, flush=True))
            good = [r for r in recs if "error" not in r and r["same_words_as_first"] and r["roundtrip_ok"]]
            best = min(good, key=lambda r: r["fwd_us_per_ntt"] + r["inv_us_per_ntt"]) if good else None
            ref = recs[0].get("ref_check", {})
            res["sweeps"][key] = dict(records=recs, best=best, ref_check=ref,
                                      all_exact=bool(ref.get("fwd_ok") and ref.get("roundtrip_ok")) and all(
                                          "error" not in r and r["same_words_as_first"] and r["roundtrip_ok"] for r in recs))
            res["compile_s"] = Ctx.compile_s
            pathlib.Path(out_path).write_text(json.dumps(res, indent=1))
            print(key, "BEST", best, flush=True)
    return 0

if __name__ == "__main__":
    sys.exit(main())
