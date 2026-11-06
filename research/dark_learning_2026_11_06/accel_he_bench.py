"""The he_outer / he_matvec return pipeline on CUDA at d = 4096: bit-exact check against the owning lane's
code, measured throughput per return, and the per-step time extrapolated with he_outer.counts /
he_matvec.counts. 2026-11-06, accelerator readiness (initiative 17), lane w1-bfv.

    python3 accel_he_bench.py [--N 8192 16384] [--L 3 4] [--nret 512] [--check 2] [--mode 0|1]
                              [--logE 11 --logC 4 --threads 256] [--K 1 64]

One return (accel_rns_ref.return_rns; he_outer.HEOuter._return then bfv decrypt), per prime, on device:
  sender i:   gen randomness (u, e0, e1, M, flood)  ->  U^ = NTT(u)  ->  acc_c = sum_b P^ C^_c + K_c U^
              ->  INTT(acc_0, acc_1)  ->  c0 += e0 + round(Q M / t) + flood,  c1 += e1
  receiver j: X = INTT(NTT(c1) S^)  ->  dec = HPS(c0 + X)
NTT count per return: 5 L (1 + 2 sender, 2 receiver). Amortized per step and counted separately: the
receiver-side NTT of every sent ciphertext (2 L each) and the plaintext spectra (L each).

Check (--check k > 0): k returns drawn by accel_rns_ref.draw_return (the owning lane's he_matvec.OwnKey and
he_outer.HEOuter._return, with bfv_ref.decrypt), all sharing one key. Device NTT-domain words of P and ct0
== accel_rns_ref.fwd; device c0, c1 residues == bfv_ref's ciphertext mod each prime, every coefficient;
device decryption == bfv_ref.decrypt, every coefficient; HPS ambiguity count == 0.
What is measured vs extrapolated: a batch of --nret returns is timed (warm, synchronized, events); the step
time is that per-return time times the counts' return totals plus the amortized NTTs at the measured NTT rate.
"""
import argparse
import json
import math
import os
import pathlib
import shlex
import sys
import time

import numpy as np

import accel_rns_ref as R
from accel_bench_cuda import Ctx

D = 4096
N_PARTIES = 3

class Pipe:
    def __init__(self, ctx, nret, K=1):
        cp = self.cp = ctx.cp
        self.ctx, self.nret, self.K = ctx, nret, K
        N, L = ctx.N, ctx.L
        self.LN = L * N
        z = lambda *s: cp.zeros(s, dtype=cp.uint64)
        self.U, self.E0, self.E1 = z(nret, L, N), z(nret, L, N), z(nret, L, N)
        self.M = z(nret, N)
        self.Acc = z(nret, 2, L, N)
        self.X = z(nret, L, N)
        self.out = z(nret, N)
        self.amb = cp.zeros(1, dtype=cp.uint32)
        t, Q, Rm = ctx.t, ctx.Q, 1 << 64
        sq = lambda w, m: (w << 64) // m
        inv2t = [pow(2 * t, -1, q) for q in ctx.Qp]
        hp = R.HPS(ctx.Qp, t)
        u = lambda x: cp.asarray(np.array(x, dtype=np.uint64))
        self.inv2t, self.inv2tq = u(inv2t), u([sq(w, q) for w, q in zip(inv2t, ctx.Qp)])
        self.qmt = Q % t
        self.qmtq = sq(self.qmt, t)
        self.hw, self.hwq = u(hp.w), u([sq(w, t) for w in hp.w])
        self.thh, self.thl = u(hp.thh), u(hp.thl)
        self.F_bits = ((N * (t // 2) * 16 * 2).bit_length() + 40) + 1

    def set_operands(self, Ph, Ch, K0, K1, S, pidx, cidx):
        """Spectra (device, coefficient words already transformed): Ph [nP*K][L][N], Ch [nC*K][2][L][N],
        K0/K1/S [L][N]. Converts the fixed operands to this MODE's form."""
        ctx = self.ctx
        self.Pw, self.Pq = ctx.fixed(Ph, Ph.shape[0] * ctx.L)
        self.Ch = Ch
        self.K0w, self.K0q = ctx.fixed(K0, ctx.L)
        self.K1w, self.K1q = ctx.fixed(K1, ctx.L)
        self.Sw, self.Sq = ctx.fixed(S, ctx.L)
        self.pidx = self.cp.asarray(np.array(pidx, dtype=np.int32))
        self.cidx = self.cp.asarray(np.array(cidx, dtype=np.int32))

    def ew(self, n):
        return ((n + 255) // 256,), (256,)

    # ---- stages
    def s_gen(self, seed=1):
        c = self.ctx
        g, b = self.ew(self.nret * c.N)
        c.k["gen_random"](g, b, (self.U, self.E0, self.E1, self.M, c.mc, np.uint64(c.t), np.uint64(seed),
                                 np.int32(self.F_bits), np.int32(c.logN), np.int32(c.L), np.int32(self.nret)))

    def s_fwd_u(self):
        self.ctx.fwd(self.U, self.nret * self.ctx.L)

    def s_mac(self):
        c = self.ctx
        g, b = self.ew(self.nret * self.LN)
        c.k["ret_mac"](g, b, (self.Acc, self.Pw, self.Pq, self.Ch, self.K0w, self.K0q, self.K1w, self.K1q, self.U,
                              self.pidx, self.cidx, np.int32(self.K), c.mc, np.int32(c.logN), np.int32(c.L),
                              np.int32(self.nret)))

    def s_inv_acc(self):
        self.ctx.inv(self.Acc, 2 * self.nret * self.ctx.L)

    def s_finalize(self):
        c = self.ctx
        g, b = self.ew(self.nret * self.LN)
        c.k["ret_finalize"](g, b, (self.Acc, self.E0, self.E1, self.M, c.mc, self.inv2t, self.inv2tq, np.uint64(c.t),
                                   np.uint64(self.qmt), np.uint64(self.qmtq), np.int32(c.logN), np.int32(c.L),
                                   np.int32(self.nret)))

    def s_decrypt(self):
        c = self.ctx
        self.X[...] = self.Acc[:, 1]
        c.fwd(self.X, self.nret * c.L)
        g, b = self.ew(self.nret * self.LN)
        c.k["pmul_fixed"](g, b, (self.X, self.Sw, self.Sq, c.mc, np.int32(c.logN), np.int32(c.L),
                                 np.int32(self.nret * c.L)))
        c.inv(self.X, self.nret * c.L)
        g, b = self.ew(self.nret * c.N)
        c.k["hps_decrypt"](g, b, (self.out, self.amb, self.Acc, np.int32(2 * self.LN), self.X, c.mc, self.hw, self.hwq,
                                  self.thh, self.thl, np.uint64(c.t), np.int32(c.logN), np.int32(c.L),
                                  np.int32(self.nret)))

    def sender(self, gen=True):
        if gen:
            self.s_gen()
        self.s_fwd_u()
        self.s_mac()
        self.s_inv_acc()
        self.s_finalize()

def rns_rows(polys, Qp):
    """[n][N] signed/unsigned Python ints -> [n][L][N] uint64 residues."""
    return np.array([[[int(x) % q for x in p] for q in Qp] for p in polys], dtype=np.uint64)

def check(ctx, k, log):
    """k returns from the owning lane's code; every word compared."""
    cp, N, L, Qp, t = ctx.cp, ctx.N, ctx.L, ctx.Qp, ctx.t
    t0 = time.perf_counter()
    kj = R.own_key(N, Qp, t)
    dr = [R.draw_return(N, Qp, t, seed=s, kj=kj) for s in range(k)]
    log("check: drew %d returns from he_outer._return in %.1f s" % (k, time.perf_counter() - t0))
    pipe = Pipe(ctx, k, K=1)
    Ph = cp.asarray(rns_rows([d["P"] for d in dr], Qp))
    Ch = cp.asarray(rns_rows([c for d in dr for c in d["ct"]], Qp).reshape(k, 2, L, N))
    K0, K1 = (cp.asarray(rns_rows([kj.pk[i]], Qp)[0]) for i in (0, 1))
    S = cp.asarray(rns_rows([kj.sch.s], Qp)[0])
    for buf, rows in ((Ph, k * L), (Ch, 2 * k * L), (K0, L), (K1, L), (S, L)):
        ctx.fwd(buf, rows)
    # NTT-domain words vs the reference, return 0, every prime
    ph, ch = cp.asnumpy(Ph), cp.asnumpy(Ch)
    spec_ok = all(list(map(int, ph[0, l])) == list(R.fwd(dr[0]["P"], ctx.T[l])) and
                  list(map(int, ch[0, 0, l])) == list(R.fwd(dr[0]["ct"][0], ctx.T[l])) for l in range(L))
    pipe.set_operands(Ph, Ch, K0, K1, S, list(range(k)), list(range(k)))
    pipe.U[...] = cp.asarray(rns_rows([d["u"] for d in dr], Qp))
    pipe.E0[...] = cp.asarray(rns_rows([[a + b for a, b in zip(d["e0"], d["flood"])] for d in dr], Qp))
    pipe.E1[...] = cp.asarray(rns_rows([d["e1"] for d in dr], Qp))
    pipe.M[...] = cp.asarray(np.array([d["M"] for d in dr], dtype=np.uint64))
    pipe.sender(gen=False)
    pipe.s_decrypt()
    acc, dec, amb = cp.asnumpy(pipe.Acc), cp.asnumpy(pipe.out), int(pipe.amb.get()[0])
    ct_ok = all(list(map(int, acc[r, c, l])) == [x % q for x in dr[r]["c1" if c else "c0"]]
                for r in range(k) for c in (0, 1) for l, q in enumerate(Qp))
    dec_ok = all(list(map(int, dec[r])) == dr[r]["dec"] for r in range(k))
    res = dict(returns=k, spectra_P_ct0_equal_ref=spec_ok, c0_c1_residues_equal_bfv_ref=ct_ok,
               decrypt_equal_bfv_ref=dec_ok, hps_ambiguous=amb, ok=bool(spec_ok and ct_ok and dec_ok and amb == 0))
    log("check " + json.dumps(res))
    return res

def bench(ctx, nret, K, reps, log):
    """Random operands, device randomness; per-stage times over a warm batch of nret returns."""
    cp, N, L = ctx.cp, ctx.N, ctx.L
    nP, nC = 32, 2
    pipe = Pipe(ctx, nret, K=K)
    rnd = lambda *s: cp.asarray(np.random.default_rng(sum(s)).integers(0, min(ctx.Qp), s, dtype=np.uint64))
    Ph, Ch = rnd(nP * K, L, N), rnd(nC * K, 2, L, N)
    pipe.set_operands(Ph, Ch, rnd(L, N), rnd(L, N), rnd(L, N), [r % nP for r in range(nret)],
                      [(r // nP) % nC for r in range(nret)])
    pipe.s_gen()
    st = dict(gen=pipe.s_gen, fwd_u=pipe.s_fwd_u, mac=pipe.s_mac, inv_acc=pipe.s_inv_acc, finalize=pipe.s_finalize,
              decrypt=pipe.s_decrypt)
    times = {k: ctx.timed(f, reps) / nret * 1e6 for k, f in st.items()}
    full = lambda: (pipe.sender(), pipe.s_decrypt())
    times["return_total"] = ctx.timed(full, reps) / nret * 1e6
    times["sender"] = sum(times[k] for k in ("gen", "fwd_u", "mac", "inv_acc", "finalize"))
    rec = dict(nret=nret, K=K, us_per_return=times)
    log("bench " + json.dumps(rec))
    return rec

def ntt_rate(ctx, rows, reps):
    buf = ctx.cp.asarray(np.random.default_rng(3).integers(0, min(ctx.Qp), (rows, ctx.N), dtype=np.uint64))
    return (ctx.timed(lambda: ctx.fwd(buf, rows), reps) + ctx.timed(lambda: ctx.inv(buf, rows), reps)) / 2 / rows * 1e6

def extrapolate(N, L, outer, mv1, mv64, us_ntt):
    """Per-step device seconds at d = 4096, n = 3 (sum over all parties), from the measured per-return
    times and the owning lane's counts."""
    import he_matvec as HM
    import he_outer as HO
    co, cm = HO.counts(D, N=N, L=L, n=N_PARTIES), HM.counts(D, N=N, L=L, n=N_PARTIES)
    dc, dr = HO.layout(D, D, N)
    ntt = us_ntt * 1e-6
    # he_outer: returns measured with K = 1; amortized: 2L NTTs per sent ct, L per plaintext D_a / D'_a
    plain_o = 2 * N_PARTIES * (D // dr) * 2               # outers x parties x row blocks x (value, MAC)
    outer_s = co["cts_returned"] * outer * 1e-6 + (co["cts_sent"] * 2 * L + plain_o * L) * ntt
    # he_matvec: per return, sum over K blocks (forward K = d/dc, transpose K = d/dr); MAC cost per block
    # from the K = 1 vs K = Kbig difference, measured
    mdc, mdr = HM.layout(D, N)
    per_block = (mv64[1] - mv1) / (mv64[0] - 1)
    ret_fwd = 2 * N_PARTIES * (N_PARTIES - 1) * (D // mdr)     # two forward matvecs per step
    ret_tr = N_PARTIES * (N_PARTIES - 1) * (D // mdc)
    assert ret_fwd + ret_tr == cm["cts_returned"]
    mv_s = (ret_fwd * (mv1 + (D // mdc - 1) * per_block) + ret_tr * (mv1 + (D // mdr - 1) * per_block)) * 1e-6
    plain_m = 3 * N_PARTIES * (D // mdr) * (D // mdc)         # every W block, each matvec, each party, once
    mv_s += (cm["cts_sent"] * 2 * L + plain_m * L) * ntt
    return dict(outer_returns=co["cts_returned"], outer_sent=co["cts_sent"], outer_plaintexts=plain_o,
                matvec_returns=cm["cts_returned"], matvec_sent=cm["cts_sent"], matvec_plaintexts=plain_m,
                outer_s=outer_s, matvec_s=mv_s, step_s=outer_s + mv_s, per_party_step_s=(outer_s + mv_s) / N_PARTIES,
                model="returns x measured us/return + amortized NTTs x measured us/NTT; matvec block MAC cost "
                      "linear in K from the K=1 and K=%d runs" % mv64[0])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="*", default=[8192, 16384])
    ap.add_argument("--L", type=int, nargs="*", default=[3, 4])
    ap.add_argument("--nret", type=int, default=512)
    ap.add_argument("--Kbig", type=int, default=64)
    ap.add_argument("--check", type=int, default=2)
    ap.add_argument("--mode", type=int, default=0)
    ap.add_argument("--logE", type=int, default=11)
    ap.add_argument("--logC", type=int, default=4)
    ap.add_argument("--threads", type=int, default=256)
    ap.add_argument("--G", type=int, default=1)
    ap.add_argument("--reps", type=int, default=5)
    a = ap.parse_args(shlex.split(" ".join(sys.argv[1:])))
    import cupy as cp
    dev = cp.cuda.runtime.getDeviceProperties(0)
    res = dict(device=dev["name"].decode(), sm=f"{dev['major']}{dev['minor']}", n_devices=cp.cuda.runtime.getDeviceCount(),
               args=vars(a), runs={})
    log = lambda s: print(s, flush=True)
    log("device %s sm %s" % (res["device"], res["sm"]))
    out_path = os.environ.get("ACCEL_RESULTS", "accel_he_bench.json")
    ok = True
    for N in a.N:
        for L in a.L:
            key = f"N{N}_L{L}"
            ctx = Ctx(N, L, a.mode, a.logE, a.logC, a.threads, a.G)
            run = dict(shape=dict(mode=a.mode, logE=ctx.logE, logC=ctx.logC, threads=a.threads), compile_s=Ctx.compile_s)
            if a.check:
                run["check"] = check(ctx, a.check, log)
                ok &= run["check"]["ok"]
            nret = max(64, a.nret * 8192 * 3 // (N * L))
            run["us_per_ntt"] = ntt_rate(ctx, nret * L, a.reps)
            run["outer"] = bench(ctx, nret, 1, a.reps, log)
            nr = max(16, nret // 4)
            run["matvec_K1"] = bench(ctx, nr, 1, a.reps, log)
            run["matvec_Kbig"] = bench(ctx, nr, a.Kbig, a.reps, log)
            run["step"] = extrapolate(N, L, run["outer"]["us_per_return"]["return_total"],
                                      run["matvec_K1"]["us_per_return"]["return_total"],
                                      (a.Kbig, run["matvec_Kbig"]["us_per_return"]["return_total"]), run["us_per_ntt"])
            log(key + " step " + json.dumps(run["step"]))
            res["runs"][key] = run
            pathlib.Path(out_path).write_text(json.dumps(res, indent=1))
            del ctx
            cp.get_default_memory_pool().free_all_blocks()
    res["all_checks_ok"] = ok
    pathlib.Path(out_path).write_text(json.dumps(res, indent=1))
    log("ALL CHECKS OK" if ok else "CHECK FAILURE")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
