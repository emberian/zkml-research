"""61-bit negacyclic RNS NTT in JAX for TPU (CPU-checkable): three paths, all bit-exact against accel_rns_ref.
2026-11-06, accelerator readiness (initiative 17), lane w1-bfv. Design and derivations: notes/accelerator-
readiness/BFV.md section "TPU". Residues are canonical, held as u32 pairs (lo, hi), hi < 2^29.

(a) VPU   `vpu_fwd/vpu_inv`: the reference transform itself (CT forward with psi_brv, GS inverse, bit-reversed
          spectrum, word for word), with a radix-2^16 four-limb Montgomery product (R = 2^64) in u32 lanes
          (the breadstuffs bfv_ntt.wgsl technique, one more limb). Twiddles in Montgomery form, so outputs stay
          canonical. Column-sum form: every partial product is split into 16-bit halves added into 9 column
          accumulators (< 2^22 each), so no u32 add overflows; carries are passed column to column.
(x) X64   `x64_fwd/x64_inv`: the same transform on jnp.uint64 (jax_enable_x64; emulated on TPU), Montgomery
          with mulhi built from 32-bit halves. Baseline for what u64 emulation costs.
(b) MXU   `mxu_fwd/mxu_inv`: four-step N = N1 N2, j = j1 + N1 j2, k = N2 k1 + k2, cyclic in w = psi^2 after
          the psi twist. All twiddles fold into matrices: the forward is
              B[j1, k2] = sum_j2 a[j] psi^(j (1 + 2 k2))          (one N2 x N2 matrix per j1)
              X[N2 k1 + k2] = sum_j1 psi^(2 N2 j1 k1) B[j1, k2]  (one shared N1 x N1 matrix)
          so X[k] = a(psi^(2k + 1)), natural order; the reference's A[k] = a(psi^(2 brv(k) + 1)) = X[brv(k)].
          The inverse mirrors it with psi^-1 and N^-1 folded into the per-row matrices.
          Each modular matmul Y = Z W mod p is int8 x int8 -> int32 on the MXU: Z (canonical, < 2^61) is cut
          into 8 balanced signed bytes z_i in [-128, 127]; for each i the matrix W 2^(8i) mod p is cut into 8
          balanced bytes; byte planes go into K (i) and the output dimension (l):
              Y_l = sum_(i, j) z_i[j] byte_l(W[j] 2^(8i) mod p),   sum_l Y_l 2^(8l) = Z W (mod p).
          int32 bound: K = 8 n2 <= 1024 terms, each |z_i w| <= 128 * 128 = 2^14, so |Y_l| <= 2^24 < 2^31.
          Reduce (VPU): carry-normalize Y_l into bytes d_l in [0, 256) and a signed carry c (|c| < 2^17), so
          V = D + c 2^64 with D < 2^64; with p = 2^61 - delta (delta < 2^22 for every prime used, asserted),
          D = h 2^61 + r gives V = r + (h + 8 c) delta (mod p), |(h + 8c) delta| < 2^43; one conditional add
          or subtract of p lands in [0, p).
    python3 accel_rns_jax.py [--check] [--bench] [--N ...] [--P 64]
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

U32 = np.uint32
M16 = 0xFFFF

def split(x):
    x = np.asarray(x, dtype=np.uint64)
    return (x & np.uint64(0xFFFFFFFF)).astype(U32), (x >> np.uint64(32)).astype(U32)

def join(lo, hi):
    return np.asarray(lo).astype(np.uint64) | (np.asarray(hi).astype(np.uint64) << np.uint64(32))

def bitrev_perm(N):
    bits = N.bit_length() - 1
    return np.array([R.brv(k, bits) for k in range(N)], dtype=np.int64)

# ===================================================================== (a) VPU: u32 pairs, 16-bit limbs
def _jnp():
    import jax.numpy as jnp
    return jnp

def add64(a, b):
    jnp = _jnp()
    lo = a[0] + b[0]
    return lo, a[1] + b[1] + (lo < a[0]).astype(jnp.uint32)

def sub64(a, b):
    jnp = _jnp()
    return a[0] - b[0], a[1] - b[1] - (a[0] < b[0]).astype(jnp.uint32)

def ge64(a, b):
    return (a[1] > b[1]) | ((a[1] == b[1]) & (a[0] >= b[0]))

def sel(c, a, b):
    jnp = _jnp()
    return jnp.where(c, a[0], b[0]), jnp.where(c, a[1], b[1])

def addmod(a, b, p):
    s = add64(a, b)
    return sel(ge64(s, p), sub64(s, p), s)

def submod(a, b, p):
    return sel(ge64(a, b), sub64(a, b), sub64(add64(a, p), b))

def limbs(x):
    return [x[0] & M16, x[0] >> 16, x[1] & M16, x[1] >> 16]

def mont_mul(a, wl, pl, pinv16, p):
    """REDC(a w) with R = 2^64, radix 2^16, 4 limbs. a: (lo, hi) canonical; wl: 4 limbs of w (Montgomery form),
    pl: 4 limbs of p; returns a w mod p canonical. Column sums stay < 2^22 (16 products' halves + 8 reduction
    halves + carries), so no u32 add overflows; each product is < 2^32."""
    jnp = _jnp()
    al = limbs(a)
    col = [None] * 10
    def acc(k, v):
        col[k] = v if col[k] is None else col[k] + v
    for i in range(4):
        for j in range(4):
            pr = al[i] * wl[j]
            acc(i + j, pr & M16)
            acc(i + j + 1, pr >> 16)
    for k in range(10):
        if col[k] is None:
            col[k] = jnp.zeros_like(al[0])
    for i in range(4):
        m = ((col[i] & M16) * pinv16) & M16
        for j in range(4):
            pr = m * pl[j]
            col[i + j] = col[i + j] + (pr & M16)
            col[i + j + 1] = col[i + j + 1] + (pr >> 16)
        col[i + 1] = col[i + 1] + (col[i] >> 16)
    for k in range(4, 9):
        col[k + 1] = col[k + 1] + (col[k] >> 16)
        col[k] = col[k] & M16
    r = (col[4] | (col[5] << 16), col[6] | (col[7] << 16))
    # col[8] is 0: REDC < 2p < 2^62 fits in 4 limbs
    return sel(ge64(r, p), sub64(r, p), r)

class VPUTables:
    def __init__(self, q, N):
        T = R.Tables(q, N)
        Rm = 1 << 64
        self.N, self.q = N, q
        fw = np.array([w * Rm % q for w in T.psi_brv], dtype=np.uint64)
        iw = np.array([w * Rm % q for w in T.ipsi_brv], dtype=np.uint64)
        self.fw = [np.array(l, dtype=U32) for l in limbs(split(fw))]
        self.iw = [np.array(l, dtype=U32) for l in limbs(split(iw))]
        self.ninv = [np.array(l, dtype=U32) for l in limbs(split(np.uint64(T.ninv * Rm % q)))]
        self.last = [np.array(l, dtype=U32) for l in limbs(split(np.uint64(T.ipsi_brv[1] * T.ninv % q * Rm % q)))]
        self.p = tuple(np.array(v, dtype=U32) for v in split(np.uint64(q)))
        self.pl = [np.array(l, dtype=U32) for l in limbs(self.p)]
        self.pinv16 = U32((-pow(q, -1, 1 << 16)) % (1 << 16))

def vpu_fwd(a, tb):
    """a: (lo, hi) arrays (..., N) for ONE prime; reference forward, word for word."""
    jnp = _jnp()
    N = tb.N
    lo, hi = a
    sh = lo.shape[:-1]
    m = 1
    while m < N:
        t = N // (2 * m)
        L = lo.reshape(sh + (m, 2, t))
        H = hi.reshape(sh + (m, 2, t))
        w = [jnp.asarray(x[m:2 * m]).reshape(m, 1) for x in tb.fw]
        U = (L[..., 0, :], H[..., 0, :])
        V = mont_mul((L[..., 1, :], H[..., 1, :]), w, tb.pl, tb.pinv16, tb.p)
        x, y = addmod(U, V, tb.p), submod(U, V, tb.p)
        lo = jnp.stack([x[0], y[0]], axis=-2).reshape(sh + (N,))
        hi = jnp.stack([x[1], y[1]], axis=-2).reshape(sh + (N,))
        m *= 2
    return lo, hi

def vpu_inv(a, tb):
    jnp = _jnp()
    N = tb.N
    lo, hi = a
    sh = lo.shape[:-1]
    h = N // 2
    while h >= 1:
        t = N // (2 * h)
        L = lo.reshape(sh + (h, 2, t))
        H = hi.reshape(sh + (h, 2, t))
        U = (L[..., 0, :], H[..., 0, :])
        V = (L[..., 1, :], H[..., 1, :])
        s, d = addmod(U, V, tb.p), submod(U, V, tb.p)
        if h > 1:
            w = [jnp.asarray(x[h:2 * h]).reshape(h, 1) for x in tb.iw]
            x, y = s, mont_mul(d, w, tb.pl, tb.pinv16, tb.p)
        else:
            x = mont_mul(s, tb.ninv, tb.pl, tb.pinv16, tb.p)
            y = mont_mul(d, tb.last, tb.pl, tb.pinv16, tb.p)
        lo = jnp.stack([x[0], y[0]], axis=-2).reshape(sh + (N,))
        hi = jnp.stack([x[1], y[1]], axis=-2).reshape(sh + (N,))
        h //= 2
    return lo, hi

# ===================================================================== (x) X64 baseline
def _mulhi64(a, b):
    jnp = _jnp()
    m32 = jnp.uint64(0xFFFFFFFF)
    a0, a1, b0, b1 = a & m32, a >> 32, b & m32, b >> 32
    p00, p01, p10, p11 = a0 * b0, a0 * b1, a1 * b0, a1 * b1
    mid = (p00 >> 32) + (p01 & m32) + (p10 & m32)
    return p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32)

def x64_mont(a, w, p, pn):
    jnp = _jnp()
    lo = a * w
    hi = _mulhi64(a, w)
    m = lo * pn
    t = hi + _mulhi64(m, p) + (lo != 0).astype(jnp.uint64)
    return jnp.where(t >= p, t - p, t)

class X64Tables:
    def __init__(self, q, N):
        T = R.Tables(q, N)
        Rm = 1 << 64
        self.N, self.q = N, q
        self.fw = np.array([w * Rm % q for w in T.psi_brv], dtype=np.uint64)
        self.iw = np.array([w * Rm % q for w in T.ipsi_brv], dtype=np.uint64)
        self.ninv = np.uint64(T.ninv * Rm % q)
        self.last = np.uint64(T.ipsi_brv[1] * T.ninv % q * Rm % q)
        self.p = np.uint64(q)
        self.pn = np.uint64((-pow(q, -1, Rm)) % Rm)

def x64_fwd(a, tb):
    jnp = _jnp()
    N, p = tb.N, jnp.uint64(tb.p)
    sh = a.shape[:-1]
    m = 1
    while m < N:
        t = N // (2 * m)
        A = a.reshape(sh + (m, 2, t))
        w = jnp.asarray(tb.fw[m:2 * m]).reshape(m, 1)
        U, V = A[..., 0, :], x64_mont(A[..., 1, :], w, p, jnp.uint64(tb.pn))
        s = U + V
        x = jnp.where(s >= p, s - p, s)
        y = jnp.where(U >= V, U - V, U + p - V)
        a = jnp.stack([x, y], axis=-2).reshape(sh + (N,))
        m *= 2
    return a

def x64_inv(a, tb):
    jnp = _jnp()
    N, p, pn = tb.N, jnp.uint64(tb.p), jnp.uint64(tb.pn)
    sh = a.shape[:-1]
    h = N // 2
    while h >= 1:
        t = N // (2 * h)
        A = a.reshape(sh + (h, 2, t))
        U, V = A[..., 0, :], A[..., 1, :]
        s = U + V
        s = jnp.where(s >= p, s - p, s)
        d = jnp.where(U >= V, U - V, U + p - V)
        if h > 1:
            w = jnp.asarray(tb.iw[h:2 * h]).reshape(h, 1)
            x, y = s, x64_mont(d, w, p, pn)
        else:
            x, y = x64_mont(s, jnp.uint64(tb.ninv), p, pn), x64_mont(d, jnp.uint64(tb.last), p, pn)
        a = jnp.stack([x, y], axis=-2).reshape(sh + (N,))
        h //= 2
    return a

# ===================================================================== (b) MXU four-step
def bal_bytes_np(v):
    """Canonical values (< 2^61, uint64 numpy) -> 8 balanced signed bytes (int8), sum b_i 2^(8i) = v."""
    v = np.asarray(v, dtype=np.uint64)
    out = np.empty((8,) + v.shape, dtype=np.int8)
    c = np.zeros(v.shape, dtype=np.int64)
    for i in range(8):
        b = ((v >> np.uint64(8 * i)) & np.uint64(0xFF)).astype(np.int64) + c
        c = (b >= 128).astype(np.int64)
        out[i] = (b - 256 * c).astype(np.int8)
    assert not c.any()
    return out

def mat_planes(E, pw_i):
    """E: exponent array (any shape S) into the power table; pw_i[i] = table of psi^e 2^(8i) mod p (uint64).
    Returns int8 (8 [i], 8 [l], *S): byte l of (W 2^(8i) mod p)."""
    return np.stack([bal_bytes_np(pw[E]) for pw in pw_i])

class MXUTables:
    """Folded four-step matrices for one prime: F1 (N1, 8 N2, 8 N2), F2 (8 N1, 8 N1), I1 (8 N1, 8 N1),
    I2 (N1, 8 N2, 8 N2), rows/cols ordered (byte, index) as in the module docstring."""
    def __init__(self, q, N, N1=None):
        T = R.Tables(q, N)
        self.N, self.q = N, q
        logN = N.bit_length() - 1
        self.N1 = N1 or (1 << (logN // 2))
        self.N2 = N // self.N1
        N1, N2 = self.N1, self.N2
        self.delta = (1 << 61) - q
        assert 0 < self.delta < (1 << 22), "reduce step needs p = 2^61 - delta, delta < 2^22"
        twoN = 2 * N
        pw = [T.psi]
        x = 1
        tab = []
        for e in range(twoN):
            tab.append(x)
            x = x * T.psi % q
        ipsi = pow(T.psi, -1, q)
        itab = []
        x = T.ninv
        for e in range(twoN):
            itab.append(x)            # N^-1 psi^-e
            x = x * ipsi % q
        ftab = [np.array([v * (1 << (8 * i)) % q for v in tab], dtype=np.uint64) for i in range(8)]
        itabs = [np.array([v * (1 << (8 * i)) % q for v in itab], dtype=np.uint64) for i in range(8)]
        ntab = [np.array([v * (1 << (8 * i)) % q for v in [pow(T.psi, -e, q) for e in range(twoN)]], dtype=np.uint64)
                for i in range(8)]
        j1 = np.arange(N1).reshape(N1, 1, 1)
        j2 = np.arange(N2).reshape(1, N2, 1)
        k2 = np.arange(N2).reshape(1, 1, N2)
        E1 = ((j1 + N1 * j2) * (1 + 2 * k2)) % twoN                    # (N1, N2 [j2], N2 [k2])
        P1 = mat_planes(E1, ftab)                                       # (8 i, 8 l, N1, N2, N2)
        self.F1 = np.ascontiguousarray(P1.transpose(2, 0, 3, 1, 4)).reshape(N1, 8 * N2, 8 * N2)
        P1i = mat_planes(E1, itabs)                                     # I2: [j1][(i, k2), (l, j2)]
        self.I2 = np.ascontiguousarray(P1i.transpose(2, 0, 4, 1, 3)).reshape(N1, 8 * N2, 8 * N2)
        a1 = np.arange(N1).reshape(N1, 1)
        b1 = np.arange(N1).reshape(1, N1)
        E2 = (2 * N2 * a1 * b1) % twoN                                  # (k1 or j1, j1 or k1)
        P2 = mat_planes(E2, ftab)                                       # (8 i, 8 l, N1 [k1], N1 [j1])
        self.F2 = np.ascontiguousarray(P2.transpose(1, 2, 0, 3)).reshape(8 * N1, 8 * N1)   # [(l,k1), (i,j1)]
        P2i = mat_planes(E2, ntab)                                      # (8 i, 8 l, N1 [j1], N1 [k1])
        self.I1 = np.ascontiguousarray(P2i.transpose(1, 2, 0, 3)).reshape(8 * N1, 8 * N1)  # [(l,j1), (i,k1)]

    def bytes_total(self):
        return self.F1.nbytes + self.F2.nbytes + self.I1.nbytes + self.I2.nbytes

def jbytes(x):
    """(lo, hi) canonical -> int8 planes (8, ...) balanced (jnp)."""
    jnp = _jnp()
    lo, hi = x
    raw = [(lo >> (8 * i)) & 0xFF for i in range(4)] + [(hi >> (8 * i)) & 0xFF for i in range(4)]
    out = []
    c = jnp.zeros(lo.shape, jnp.int32)
    for b in raw:
        v = b.astype(jnp.int32) + c
        c = (v >= 128).astype(jnp.int32)
        out.append((v - 256 * c).astype(jnp.int8))
    return jnp.stack(out)

def jreduce(Y, delta, p):
    """Y: int32 planes (8, ...) with sum_l Y_l 2^(8l) = V (mod p) -> (lo, hi) canonical (see docstring)."""
    jnp = _jnp()
    c = jnp.zeros(Y.shape[1:], jnp.int32)
    d = []
    for l in range(8):
        s = Y[l] + c
        d.append((s & 0xFF).astype(jnp.uint32))
        c = s >> 8                                     # arithmetic shift: floor division by 256
    lo = d[0] | (d[1] << 8) | (d[2] << 16) | (d[3] << 24)
    hi = d[4] | (d[5] << 8) | (d[6] << 16) | (d[7] << 24)
    e = (hi >> 29).astype(jnp.int32) + 8 * c          # V = r + e delta (mod p), r = D mod 2^61
    hi = hi & jnp.uint32((1 << 29) - 1)
    ea = jnp.abs(e).astype(jnp.uint32)                 # |e| < 2^21
    d0, d1 = jnp.uint32(delta & M16), jnp.uint32(delta >> 16)
    e0, e1 = ea & M16, ea >> 16
    p00, p01, p10, p11 = e0 * d0, e0 * d1, e1 * d0, e1 * d1
    mid = p01 + p10                                    # < 2^28
    plo = p00 + (mid << 16)
    phi = (mid >> 16) + p11 + (plo < p00).astype(jnp.uint32)
    pos = add64((lo, hi), (plo, phi))
    neg = sub64((lo, hi), (plo, phi))
    negative = ge64((plo, phi), (lo, hi)) & ~((plo == lo) & (phi == hi))
    neg = sel(negative, add64(neg, p), neg)            # r - |e| delta in (-2^43, 2^61): + p once
    v = sel(e >= 0, pos, neg)
    return sel(ge64(v, p), sub64(v, p), v)             # r + e delta < 2^61 + 2^43 < 2p

def mxu_fwd(a, mt, F1, F2):
    """a: (lo, hi) (P, N) one prime -> natural-order spectrum X (P, N), X[k] = a(psi^(2k+1))."""
    jnp = _jnp()
    import jax
    N1, N2 = mt.N1, mt.N2
    p = tuple(jnp.uint32(v) for v in split(np.uint64(mt.q)))
    Pn = a[0].shape[0]
    A = tuple(x.reshape(Pn, N2, N1).transpose(2, 0, 1) for x in a)          # [j1, p, j2]
    Z = jbytes(A)                                                          # (8 i, N1, P, N2)
    Z = Z.transpose(1, 2, 0, 3).reshape(N1, Pn, 8 * N2)                     # [j1, p, (i, j2)]
    Y = jax.lax.dot_general(Z, F1, (((2,), (1,)), ((0,), (0,))), preferred_element_type=jnp.int32)  # [j1, p, (l,k2)]
    Y = Y.reshape(N1, Pn, 8, N2).transpose(2, 0, 1, 3)                      # (8 l, j1, p, k2)
    B = jreduce(Y, mt.delta, p)                                             # [j1, p, k2]
    Z = jbytes(B).reshape(8 * N1, Pn * N2)                                  # [(i, j1), (p, k2)]
    Y = jnp.dot(F2, Z, preferred_element_type=jnp.int32).reshape(8, N1, Pn, N2)   # (8 l, k1, p, k2)
    C = jreduce(Y, mt.delta, p)                                             # [k1, p, k2]
    return tuple(x.transpose(1, 0, 2).reshape(Pn, N1 * N2) for x in C)

def mxu_inv(X, mt, I1, I2):
    jnp = _jnp()
    import jax
    N1, N2 = mt.N1, mt.N2
    p = tuple(jnp.uint32(v) for v in split(np.uint64(mt.q)))
    Pn = X[0].shape[0]
    Xm = tuple(x.reshape(Pn, N1, N2).transpose(1, 0, 2) for x in X)        # [k1, p, k2]
    Z = jbytes(Xm).reshape(8 * N1, Pn * N2)                                 # [(i, k1), (p, k2)]
    Y = jnp.dot(I1, Z, preferred_element_type=jnp.int32).reshape(8, N1, Pn, N2)   # (8 l, j1, p, k2)
    G = jreduce(Y, mt.delta, p)                                             # [j1, p, k2]
    Z = jbytes(G).transpose(1, 2, 0, 3).reshape(N1, Pn, 8 * N2)             # [j1, p, (i, k2)]
    Y = jax.lax.dot_general(Z, I2, (((2,), (1,)), ((0,), (0,))), preferred_element_type=jnp.int32)  # [j1, p, (l, j2)]
    Y = Y.reshape(N1, Pn, 8, N2).transpose(2, 0, 1, 3)                      # (8 l, j1, p, j2)
    A = jreduce(Y, mt.delta, p)                                             # [j1, p, j2]
    return tuple(x.transpose(1, 2, 0).reshape(Pn, N1 * N2) for x in A)

# ===================================================================== checks and bench
def check(N, Ls=(3, 4), P=4, log=print):
    """Each path, each prime: forward words == accel_rns_ref.fwd (MXU: after the brv permutation) on P random
    rows, inverse(forward) == input; MXU products == bfv_ref.negacyclic_mul mod p on one row pair."""
    import jax
    import jax.numpy as jnp
    import bfv_ref as bfv
    out = {}
    rng = np.random.default_rng(N)
    perm = bitrev_perm(N)
    for L in Ls:
        Qp, _ = R.primes(N, L)
        for q in Qp:
            if (str(q)) in out:
                continue
            T = R.Tables(q, N)
            x = rng.integers(0, q, (P, N), dtype=np.uint64)
            ref = np.array([[int(v) for v in R.fwd([int(c) for c in row], T)] for row in x], dtype=np.uint64)
            vt = VPUTables(q, N)
            xs = tuple(jnp.asarray(v) for v in split(x))
            f = jax.jit(lambda a: vpu_fwd(a, vt))
            g = jax.jit(lambda a: vpu_inv(a, vt))
            yv = f(xs)
            vpu_ok = bool(np.array_equal(join(*yv), ref)) and bool(np.array_equal(join(*g(yv)), x))
            mt = MXUTables(q, N)
            F1, F2, I1, I2 = (jnp.asarray(m) for m in (mt.F1, mt.F2, mt.I1, mt.I2))
            fm = jax.jit(lambda a: mxu_fwd(a, mt, F1, F2))
            gm = jax.jit(lambda a: mxu_inv(a, mt, I1, I2))
            ym = fm(xs)
            Xn = join(*ym)
            mxu_ok = bool(np.array_equal(Xn[:, perm], ref)) and bool(np.array_equal(join(*gm(ym)), x))
            # product through the MXU path vs Kronecker
            z = join(*gm(tuple(v for v in split(np.array(
                [[int(u) * int(w) % q for u, w in zip(Xn[0], Xn[1])]], dtype=np.uint64)))))
            zz, _ = bfv.negacyclic_mul([int(c) for c in x[0]], [int(c) for c in x[1]])
            prod_ok = [int(c) for c in z[0]] == [c % q for c in zz]
            res = dict(vpu=vpu_ok, mxu=mxu_ok, mxu_product_vs_kronecker=prod_ok)
            try:
                jax.config.update("jax_enable_x64", True)
                xt = X64Tables(q, N)
                f6 = jax.jit(lambda a: x64_fwd(a, xt))
                g6 = jax.jit(lambda a: x64_inv(a, xt))
                y6 = f6(jnp.asarray(x, dtype=jnp.uint64))
                res["x64"] = bool(np.array_equal(np.asarray(y6), ref)) and bool(np.array_equal(np.asarray(g6(y6)), x))
            finally:
                jax.config.update("jax_enable_x64", False)
            out[str(q)] = res
            log("check N%d q=%d %s" % (N, q, json.dumps(res)))
    return out

def timeit(f, a, reps):
    import jax
    t0 = time.perf_counter()
    r = f(a)
    jax.block_until_ready(r)
    comp = time.perf_counter() - t0
    t0 = time.perf_counter()
    for _ in range(reps):
        r = f(a)
    jax.block_until_ready(r)
    return (time.perf_counter() - t0) / reps, comp

def bench(N, P, reps=5, paths=("vpu", "mxu", "x64"), log=print, N1=None):
    """Per path: warm us per NTT (forward, inverse) on P polys of one prime, one device."""
    import jax
    import jax.numpy as jnp
    q = R.primes(N, 3)[0][0]
    x = np.random.default_rng(1).integers(0, q, (P, N), dtype=np.uint64)
    xs = tuple(jax.device_put(jnp.asarray(v)) for v in split(x))
    res = {}
    if "vpu" in paths:
        vt = VPUTables(q, N)
        f, g = jax.jit(lambda a: vpu_fwd(a, vt)), jax.jit(lambda a: vpu_inv(a, vt))
        tf, cf = timeit(f, xs, reps)
        ti, ci = timeit(g, f(xs), reps)
        res["vpu"] = dict(fwd_us=tf / P * 1e6, inv_us=ti / P * 1e6, compile_s=cf + ci)
        log("bench N%d P%d vpu %s" % (N, P, json.dumps(res["vpu"])))
    if "mxu" in paths:
        mt = MXUTables(q, N, N1)
        F1, F2, I1, I2 = (jax.device_put(jnp.asarray(m)) for m in (mt.F1, mt.F2, mt.I1, mt.I2))
        f, g = jax.jit(lambda a: mxu_fwd(a, mt, F1, F2)), jax.jit(lambda a: mxu_inv(a, mt, I1, I2))
        tf, cf = timeit(f, xs, reps)
        ti, ci = timeit(g, f(xs), reps)
        macs = mt.N1 * (8 * mt.N2) ** 2 + (8 * mt.N1) ** 2 * mt.N2
        res["mxu"] = dict(fwd_us=tf / P * 1e6, inv_us=ti / P * 1e6, compile_s=cf + ci, N1=mt.N1, N2=mt.N2,
                          int8_macs_per_ntt=macs, matrix_bytes=mt.bytes_total(),
                          int8_TOPS_achieved=2 * macs * P / tf / 1e12)
        log("bench N%d P%d mxu %s" % (N, P, json.dumps(res["mxu"])))
    if "x64" in paths:
        jax.config.update("jax_enable_x64", True)
        try:
            xt = X64Tables(q, N)
            x6 = jax.device_put(jnp.asarray(x, dtype=jnp.uint64))
            f, g = jax.jit(lambda a: x64_fwd(a, xt)), jax.jit(lambda a: x64_inv(a, xt))
            tf, cf = timeit(f, x6, reps)
            ti, ci = timeit(g, f(x6), reps)
            res["x64"] = dict(fwd_us=tf / P * 1e6, inv_us=ti / P * 1e6, compile_s=cf + ci)
            log("bench N%d P%d x64 %s" % (N, P, json.dumps(res["x64"])))
        finally:
            jax.config.update("jax_enable_x64", False)
    return res

def bench_pointwise(N, P, reps=5, log=print):
    """VPU Montgomery product of a (P, N) batch by a fixed (N,) operand: the return pipeline's pointwise step."""
    import jax
    import jax.numpy as jnp
    q = R.primes(N, 3)[0][0]
    vt = VPUTables(q, N)
    rng = np.random.default_rng(2)
    x = tuple(jax.device_put(jnp.asarray(v)) for v in split(rng.integers(0, q, (P, N), dtype=np.uint64)))
    w = [jnp.asarray(l) for l in limbs(split(rng.integers(0, q, N, dtype=np.uint64)))]
    f = jax.jit(lambda a: mont_mul(a, w, vt.pl, vt.pinv16, vt.p))
    t, c = timeit(f, x, reps)
    res = dict(us_per_poly=t / P * 1e6, ns_per_modmul=t / (P * N) * 1e9, compile_s=c)
    log("pointwise N%d P%d %s" % (N, P, json.dumps(res)))
    return res

def bench_multi(N, P, reps=5, log=print, N1=None):
    """MXU forward + inverse on all local devices (pmap over a leading device axis, matrices replicated);
    P polys PER DEVICE. Throughput in NTTs/s for the whole host."""
    import jax
    import jax.numpy as jnp
    nd = jax.local_device_count()
    q = R.primes(N, 3)[0][0]
    mt = MXUTables(q, N, N1)
    x = np.random.default_rng(1).integers(0, q, (nd, P, N), dtype=np.uint64)
    xs = tuple(jnp.asarray(v) for v in split(x))
    F1, F2, I1, I2 = (jnp.asarray(m) for m in (mt.F1, mt.F2, mt.I1, mt.I2))
    f = jax.pmap(lambda a, A, B: mxu_fwd(a, mt, A, B), in_axes=(0, None, None))
    g = jax.pmap(lambda a, A, B: mxu_inv(a, mt, A, B), in_axes=(0, None, None))
    tf, cf = timeit(lambda a: f(a, F1, F2), xs, reps)
    y = f(xs, F1, F2)
    ti, ci = timeit(lambda a: g(a, I1, I2), y, reps)
    ok = bool(np.array_equal(join(*g(y, I1, I2)), x))
    res = dict(devices=nd, P_per_device=P, fwd_us_per_ntt_host=tf / (nd * P) * 1e6, inv_us_per_ntt_host=ti / (nd * P) * 1e6,
               compile_s=cf + ci, roundtrip_ok=ok, N1=mt.N1)
    log("multi N%d P%d %s" % (N, P, json.dumps(res)))
    return res

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--bench", action="store_true")
    ap.add_argument("--N", type=int, nargs="*", default=[8192, 16384])
    ap.add_argument("--P", type=int, nargs="*", default=[64])
    ap.add_argument("--paths", nargs="*", default=["vpu", "mxu", "x64"])
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--checkL", type=int, nargs="*", default=[3, 4])
    ap.add_argument("--N1", type=int, nargs="*", default=[0])
    ap.add_argument("--pointwise", action="store_true")
    ap.add_argument("--multi", type=int, nargs="*", default=[])
    a = ap.parse_args(shlex.split(" ".join(sys.argv[1:])))
    import jax
    res = dict(jax=jax.__version__, backend=jax.default_backend(), devices=[str(d) for d in jax.devices()],
               device_kind=jax.devices()[0].device_kind, n_devices=jax.device_count(), check={}, bench={})
    print("jax", res["jax"], res["backend"], res["device_kind"], "x%d" % res["n_devices"], flush=True)
    if os.environ.get("ACCEL_DEVICE") == "tpu":
        assert res["backend"] == "tpu", res
    out = pathlib.Path(os.environ.get("ACCEL_RESULTS", "accel_rns_jax.json"))
    ok = True
    for N in a.N:
        if a.check:
            c = check(N, tuple(a.checkL))
            res["check"]["N%d" % N] = c
            ok &= all(all(v.values()) for v in c.values())
            out.write_text(json.dumps(res, indent=1))
        if a.bench:
            for P in a.P:
                for n1 in a.N1:
                    paths = tuple(a.paths) if n1 == a.N1[0] else ("mxu",)
                    key = "N%d_P%d" % (N, P) + ("_N1_%d" % n1 if n1 else "")
                    try:
                        res["bench"][key] = bench(N, P, a.reps, paths, N1=n1 or None)
                    except Exception as e:
                        res["bench"][key] = dict(error=repr(e)[:500])
                        print(key, "error", repr(e)[:500], flush=True)
                    out.write_text(json.dumps(res, indent=1))
                if a.pointwise:
                    res["bench"]["pointwise_N%d_P%d" % (N, P)] = bench_pointwise(N, P, a.reps)
        for P in a.multi:
            try:
                res["bench"]["multi_N%d_P%d" % (N, P)] = bench_multi(N, P, a.reps)
            except Exception as e:
                res["bench"]["multi_N%d_P%d" % (N, P)] = dict(error=repr(e)[:500])
                print("multi error", repr(e)[:500], flush=True)
            out.write_text(json.dumps(res, indent=1))
    res["all_exact"] = ok
    out.write_text(json.dumps(res, indent=1))
    print("ALL EXACT" if ok else "EXACTNESS FAILURE", flush=True)
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
