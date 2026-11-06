#!/usr/bin/env python3
"""Independent reference for piop.c: regenerates the instance from the same SplitMix64 stream, recomputes every
prover message with Python integers (GF(2^256) mod x^256+x^10+x^5+x^2+1, checked irreducible below), compares
with the C transcript byte for byte, then RUNS THE VERIFIER: each zerocheck/lookup round's consistency, and the
final claims against multilinear evaluations computed directly from the trace (not from the prover's folds).
With the `bad` argument (one violated row) the honest-prover transcript must FAIL the zerocheck.
    piop_ref.py <piop binary> ELL [bad]"""
import json, subprocess, sys

F = (1 << 256) | (1 << 10) | (1 << 5) | (1 << 2) | 1
M64 = (1 << 64) - 1

def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 256: a ^= F
    return r

def irreducible():
    def mm(a, b): return gmul(a, b)
    y = 2
    for i in range(256):
        y = mm(y, y)
        if i == 127: y128 = y
    def gcd(a, b):
        while b:
            while a and a.bit_length() >= b.bit_length(): a ^= b << (a.bit_length() - b.bit_length())
            a, b = b, a
        return a
    return y == 2 and gcd(F, y128 ^ 2) == 1

class Rng:
    def __init__(s, seed): s.s = seed
    def next(s):
        s.s = (s.s + 0x9e3779b97f4a7c15) & M64; z = s.s
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & M64; z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & M64
        return z ^ (z >> 31)
    def g(s):
        w = [s.next() for _ in range(4)]
        return w[0] | w[1] << 64 | w[2] << 128 | w[3] << 192

def eq(t, x): return 1 ^ t ^ x

def mle(vals, pt):  # vals indexed LSB-first by pt[0]
    v = list(vals)
    for r in pt:
        v = [v[2 * j] ^ gmul(r, v[2 * j] ^ v[2 * j + 1]) for j in range(len(v) // 2)]
    return v[0]

def main():
    exe, ell = sys.argv[1], int(sys.argv[2]); bad = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    n = 1 << ell; R = Rng(0x5eed + ell); W = (n + 63) // 64
    aw, bw, cw = [], [], []
    for _ in range(W):
        a = R.next(); b = R.next(); aw.append(a); bw.append(b); cw.append(a & b)
    if n < 64:
        m = (1 << n) - 1; aw[0] &= m; bw[0] &= m; cw[0] &= m
    if bad: cw[(bad % n) >> 6] ^= 1 << ((bad % n) & 63)
    bit = lambda v, i: v[i >> 6] >> (i & 63) & 1
    A = [bit(aw, i) for i in range(n)]; B = [bit(bw, i) for i in range(n)]; C = [bit(cw, i) for i in range(n)]
    addr = [R.next() & 15 for _ in range(n)]
    val = [R.g() for _ in range(16)]
    tau = [R.g() for _ in range(ell)]; rz = [R.g() for _ in range(ell)]; rl = [R.g() for _ in range(ell)]; rlk = [R.g() for _ in range(ell)]
    out = json.loads(subprocess.run([exe, "check", str(ell)] + ([str(bad)] if bad else []), capture_output=True, text=True, check=True).stdout)
    h = lambda s: int(s, 16)
    zq = [h(x) for x in out["zq"]]; zf = [h(x) for x in out["zfinal"]]; lq = [h(x) for x in out["lq"]]
    lclaim = h(out["lclaim"]); lfinal = h(out["lfinal"]); ra = [h(x) for x in out["ra"]]

    # ---- recompute the prover's messages independently (plain, unfactored sums) ----
    mism = 0
    a, b, c = A[:], B[:], C[:]
    for i in range(ell):
        rest = tau[i + 1:]
        m = len(a) // 2
        Etab = []  # eq over the remaining variables, built point by point
        for j in range(m):
            e = 1
            for k, t in enumerate(rest):
                e = gmul(e, eq(t, j >> k & 1))
            Etab.append(e)
        q0 = q1 = qi = 0
        for j in range(m):
            p0 = gmul(a[2*j], b[2*j]) ^ c[2*j]; p1 = gmul(a[2*j+1], b[2*j+1]) ^ c[2*j+1]
            pi = gmul(a[2*j] ^ a[2*j+1], b[2*j] ^ b[2*j+1])
            q0 ^= gmul(Etab[j], p0); q1 ^= gmul(Etab[j], p1); qi ^= gmul(Etab[j], pi)
        mism += (q0, q1, qi) != tuple(zq[3*i:3*i+3])
        r = rz[i]
        a = [a[2*j] ^ gmul(r, a[2*j] ^ a[2*j+1]) for j in range(m)]
        b = [b[2*j] ^ gmul(r, b[2*j] ^ b[2*j+1]) for j in range(m)]
        c = [c[2*j] ^ gmul(r, c[2*j] ^ c[2*j+1]) for j in range(m)]
    mism += [a[0], b[0], c[0]] != zf
    # ---- zerocheck verifier ----
    claim, pre, zok = 0, 1, True
    for i in range(ell):
        q0, q1, qi = zq[3*i:3*i+3]; t = tau[i]; r = rz[i]
        if gmul(pre, gmul(eq(t, 0), q0) ^ gmul(eq(t, 1), q1)) != claim: zok = False
        qr = q0 ^ gmul(q0 ^ q1 ^ qi, r) ^ gmul(qi, gmul(r, r))
        pre = gmul(pre, eq(t, r)); claim = gmul(pre, qr)
    # final: against MLEs of the trace computed directly at the challenge point
    ar, br, cr = mle(A, rz), mle(B, rz), mle(C, rz)
    if claim != gmul(pre, gmul(ar, br) ^ cr): zok = False
    if [ar, br, cr] != zf: zok = False
    # ---- lookup verifier ----
    g = [val[x] for x in addr]
    rv_direct = 0
    for x in range(n):
        e = 1
        for k in range(ell): e = gmul(e, eq(rl[k], x >> k & 1))
        rv_direct ^= gmul(e, g[x])
    lok = lclaim == rv_direct
    claim, pre = lclaim, 1
    for i in range(ell):
        q0, q1 = lq[2*i], lq[2*i+1]; t = rl[i]; r = rlk[i]
        if gmul(pre, gmul(eq(t, 0), q0) ^ gmul(eq(t, 1), q1)) != claim: lok = False
        qr = q0 ^ gmul(q0 ^ q1, r)
        pre = gmul(pre, eq(t, r)); claim = gmul(pre, qr)
    gr = mle(g, rlk)
    if claim != gmul(pre, gr) or gr != lfinal: lok = False
    # one-hot openings: ra~(rho, v) = MLE of [addr(x) == v] at rho; and sum_v val[v] ra~ = g~(rho)
    ra_direct = [mle([1 if addr[x] == v else 0 for x in range(n)], rlk) for v in range(16)]
    tot = 0
    for v in range(16): tot ^= gmul(val[v], ra_direct[v])
    rok = ra_direct == ra and tot == gr
    res = {"ell": ell, "bad": bad, "irreducible": irreducible(), "transcript_mismatches": mism,
           "zerocheck_accepts": zok, "lookup_accepts": lok, "onehot_openings_ok": rok, "c_mults": out["mults"]}
    ok = res["irreducible"] and mism == 0 and lok and rok and (zok if not bad else not zok)
    res["pass"] = ok
    print(json.dumps(res)); sys.exit(0 if ok else 1)

main()
