"""Reference negacyclic RNS NTT for the dark-learning BFV kernels (accelerator readiness, initiative 17).

2026-11-06. Exact arithmetic on Python ints (numpy object arrays, vectorized per stage). Every device kernel
(CUDA accel_rns_ntt.cu, JAX accel_rns_jax.py) matches THIS module word for word, on the NTT-domain values
as well as on the final products. This module is itself checked against bfv_ref.negacyclic_mul (Kronecker
substitution over Z) and against direct polynomial evaluation (`python3 accel_rns_ref.py`).

Convention (fixed once, used everywhere):
  primes   Qp(N, L): L = 3 -> ntt_primes(61, 3, 2N); L = 4 -> the first five of ntt_primes(61, 5, 2N) minus t.
           t = ntt_primes(61, 4, 2N)[3] in both cases (the SPDZ field, as in run_he_outer / fhe_fork).
  psi      the SMALLEST primitive 2N-th root of unity mod p (canonical: no generator search convention).
  tables   psi_brv[k] = psi^brv(k), ipsi_brv[k] = psi^-brv(k), brv = bit reversal on log2 N bits; ninv = N^-1.
  forward  Cooley-Tukey, psi merged into the twiddles (Longa-Naehrig / SEAL): natural-order input,
           bit-reversed output. Stage m = 1, 2, .., N/2 (t = N / 2m): view a as (m, 2, t); for group i,
           U = a[i,0,:], V = a[i,1,:] * psi_brv[m + i]; a[i,0,:] = U + V, a[i,1,:] = U - V (mod p).
           Output: A[k] = a(psi^(2 brv(k) + 1)), checked by evaluation below.
  inverse  Gentleman-Sande, bit-reversed input, natural-order output. Stage h = N/2, .., 1 (t = N / 2h): view
           a as (h, 2, t); U, V as above; a[i,0,:] = U + V, a[i,1,:] = (U - V) * ipsi_brv[h + i]; then * ninv.
           (Devices fold ninv into the last stage; values are canonical residues, so the words are identical.)
  pointwise C[k] = A[k] B[k] mod p in the bit-reversed domain. All stored values are canonical, in [0, p).
"""
import math
import random
import sys

import numpy as np

import bfv_ref as bfv

def primes(N, L):
    t = bfv.ntt_primes(61, 4, 2 * N)[3]
    if L == 3:
        Qp = bfv.ntt_primes(61, 3, 2 * N)
    elif L == 4:
        Qp = [q for q in bfv.ntt_primes(61, 5, 2 * N) if q != t]
    else:
        raise ValueError(L)
    assert len(Qp) == L and t not in Qp
    return Qp, t

def brv(k, bits):
    return int(format(k, "0%db" % bits)[::-1], 2)

def min_psi(p, N):
    g = 2
    while True:
        psi = pow(g, (p - 1) // (2 * N), p)
        if pow(psi, N, p) == p - 1:
            break
        g += 1
    sq, best, x = psi * psi % p, p, psi
    for _ in range(N):
        best = min(best, x)
        x = x * sq % p
    assert pow(best, N, p) == p - 1
    return best

class Tables:
    """Per-prime twiddle tables (Python ints)."""
    _cache = {}

    def __new__(cls, p, N):
        key = (p, N)
        if key not in cls._cache:
            self = super().__new__(cls)
            bits = N.bit_length() - 1
            self.p, self.N, self.bits = p, N, bits
            self.psi = min_psi(p, N)
            ipsi = pow(self.psi, -1, p)
            pw = [1] * N
            ipw = [1] * N
            for i in range(1, N):
                pw[i] = pw[i - 1] * self.psi % p
                ipw[i] = ipw[i - 1] * ipsi % p
            self.psi_brv = [pw[brv(k, bits)] for k in range(N)]
            self.ipsi_brv = [ipw[brv(k, bits)] for k in range(N)]
            self.ninv = pow(N, -1, p)
            cls._cache[key] = self
        return cls._cache[key]

def fwd(a, T):
    p, N = T.p, T.N
    a = np.array([int(x) % p for x in a], dtype=object)
    tw = np.array(T.psi_brv, dtype=object)
    m = 1
    while m < N:
        t = N // (2 * m)
        A = a.reshape(m, 2, t)
        S = tw[m:2 * m].reshape(m, 1)
        U, V = A[:, 0, :], (A[:, 1, :] * S) % p
        a = np.stack([(U + V) % p, (U - V) % p], axis=1).reshape(N)
        m *= 2
    return a

def inv(a, T):
    p, N = T.p, T.N
    a = np.array([int(x) % p for x in a], dtype=object)
    tw = np.array(T.ipsi_brv, dtype=object)
    h = N // 2
    while h >= 1:
        t = N // (2 * h)
        A = a.reshape(h, 2, t)
        S = tw[h:2 * h].reshape(h, 1)
        U, V = A[:, 0, :], A[:, 1, :]
        a = np.stack([(U + V) % p, ((U - V) * S) % p], axis=1).reshape(N)
        h //= 2
    return (a * T.ninv) % p

def pmul(A, B, p):
    return (np.asarray(A, dtype=object) * np.asarray(B, dtype=object)) % p

def padd(A, B, p):
    return (np.asarray(A, dtype=object) + np.asarray(B, dtype=object)) % p

def to_rns(a, Qp):
    return [np.array([int(x) % q for x in a], dtype=object) for q in Qp]

def crt(res, Qp):
    Q = math.prod(Qp)
    out = np.zeros(len(res[0]), dtype=object)
    for r, q in zip(res, Qp):
        qh = Q // q
        out = out + ((np.asarray(r, dtype=object) * pow(qh, -1, q)) % q) * qh
    return out % Q

def rns_negacyclic(a, b, Qp, N):
    """a * b in Z_Q[X]/(X^N + 1) through the per-prime NTTs; returns residues and the forward spectra."""
    outs, specs = [], []
    for q in Qp:
        T = Tables(q, N)
        A, B = fwd(a, T), fwd(b, T)
        outs.append(inv(pmul(A, B, q), T))
        specs.append((A, B))
    return outs, specs

# ---------------------------------------------------------------- BFV return pipeline in RNS form
def mask_encode(M, Q, t, q):
    """round(Q centered(M, t) / t) mod q for q | Q, from M alone (no big ints): with x = Q mc and
    r = (2 x + t) mod 2t = (2 ((Q mod t) M mod t) + t) mod 2t, the value is (t - r) (2t)^-1 mod q."""
    M = np.asarray(M, dtype=object)
    r = (2 * (((Q % t) * M) % t) + t) % (2 * t)
    return ((t - r) * pow(2 * t, -1, q)) % q

class HPS:
    """Exact BFV decryption scaling round(t x / Q) mod t from RNS residues x_i (Halevi-Polyakov-Shoup with
    128-bit fixed-point fractions). With qhat_i = Q / p_i, w_i + theta_i = t (qhat_i^-1 mod p_i) / p_i:
        t x / Q = sum_i x_i w_i + sum_i x_i theta_i - v t.
    theta_i is stored as th_i = floor(theta_i 2^128) = (thh_i, thl_i) 64-bit words; per term
        x thh = hi 2^64 + lo (exact), frac_i = lo + floor(x thl / 2^64)  (64-bit fraction, may carry),
    and the rounded value is (sum (x_i w_i mod t) + sum hi_i + floor((sum frac_i + 2^63) / 2^64)) mod t.
    Truncation error < (2L) 2^-64 per coefficient; `ambiguous` flags a fraction that close to 1/2."""
    def __init__(self, Qp, t):
        self.Qp, self.t = Qp, t
        Q = math.prod(Qp)
        self.w, self.thh, self.thl = [], [], []
        for q in Qp:
            num = t * pow(Q // q, -1, q)
            self.w.append((num // q) % t)
            th = ((num % q) << 128) // q
            self.thh.append(th >> 64)
            self.thl.append(th & ((1 << 64) - 1))

    def scale(self, xs):
        t, L = self.t, len(self.Qp)
        out, amb = [], 0
        for k in range(len(xs[0])):
            ip, fr = 0, 0
            for i in range(L):
                x = int(xs[i][k])
                ip += x * self.w[i] % t
                pr = x * self.thh[i]
                ip += pr >> 64
                fr += (pr & ((1 << 64) - 1)) + ((x * self.thl[i]) >> 64)
            ip += (fr + (1 << 63)) >> 64
            d = (fr & ((1 << 64) - 1)) - (1 << 63)
            if abs(d) < 2 * L + 2:
                amb += 1
            out.append(ip % t)
        return out, amb

def return_rns(P, ct, pk, u, e0, e1, M, flood, s, Qp, t, N):
    """One he_outer return and its decryption, in RNS/NTT form, exactly as the device pipeline does it:
      c0 = INTT(P^ ct0^ + pk0^ u^) + e0 + mask_encode(M) + flood,  c1 = INTT(P^ ct1^ + pk1^ u^) + e1,
      dec = HPS(c0 + INTT(c1^ s^)).  Returns (c0 residues, c1 residues, dec, spectra of P and ct0)."""
    Q = math.prod(Qp)
    c0s, c1s, xs, spec = [], [], [], []
    for q in Qp:
        T = Tables(q, N)
        Ph, c0h, c1h, k0h, k1h, uh, sh = (fwd(v, T) for v in (P, ct[0], ct[1], pk[0], pk[1], u, s))
        a0 = inv(padd(pmul(Ph, c0h, q), pmul(k0h, uh, q), q), T)
        a1 = inv(padd(pmul(Ph, c1h, q), pmul(k1h, uh, q), q), T)
        e0q = np.array([int(x) % q for x in e0], dtype=object)
        e1q = np.array([int(x) % q for x in e1], dtype=object)
        fq = np.array([int(x) % q for x in flood], dtype=object)
        c0 = (a0 + e0q + mask_encode(M, Q, t, q) + fq) % q
        c1 = (a1 + e1q) % q
        x = (c0 + inv(pmul(fwd(c1, T), sh, q), T)) % q
        c0s.append(c0)
        c1s.append(c1)
        xs.append(x)
        spec.append((Ph, c0h))
    dec, amb = HPS(Qp, t).scale(xs)
    return c0s, c1s, dec, amb, spec

# ---------------------------------------------------------------- checks against bfv_ref / he_outer
def own_key(N, Qp, t, seed=100):
    import he_matvec as HM
    return HM.OwnKey(N, math.prod(Qp), t, seed=seed)

def draw_return(N, Qp, t, seed, kj=None):
    """Run the owning lane's code (he_matvec.OwnKey, he_outer.HEOuter._return) on one return and replay
    its rng to recover the randomness it drew. Returns the inputs, bfv_ref's ciphertext and decryption."""
    import he_outer as HO
    Q = math.prod(Qp)
    kj = kj or own_key(N, Qp, t, 100 + seed)
    rng = random.Random(seed)
    m = [0] * N
    for c in range(64):
        m[c] = rng.randrange(t)
    ct = kj.sch.encrypt_exact(m)
    cen = lambda v: v - t if v > t // 2 else v
    a = [cen(rng.randrange(t)) for _ in range(N // 64)]
    P = [0] * N
    for r, v in enumerate(a):
        P[64 * r] = v
    ho = HO.HEOuter.__new__(HO.HEOuter)
    ho.Q, ho.N, ho.p, ho.flood_bits = Q, N, t, 40
    ho.rng = random.Random(seed + 7)
    ho.wire = {"he_return": 0}
    ho.cts_returned = 0
    (c0, c1), M = ho._return(kj, P, ct, None)
    dec = kj.sch.decrypt((c0, c1))
    # replay ho.rng: M, then enc_zero_pk (u, then e0 for c0, then e1 for c1), then the flood
    rr = random.Random(seed + 7)
    M2 = [rr.randrange(t) for _ in range(N)]
    u = [rr.choice((-1, 0, 1)) for _ in range(N)]
    e0 = [rr.randint(-8, 8) for _ in range(N)]
    e1 = [rr.randint(-8, 8) for _ in range(N)]
    F = 1 << ((N * (t // 2) * 16 * 2).bit_length() + 40)
    flood = [rr.randint(-F, F) for _ in range(N)]
    assert M2 == M
    return dict(P=P, ct=ct, pk=kj.pk, u=u, e0=e0, e1=e1, M=M, flood=flood, s=kj.sch.s, c0=c0, c1=c1,
                dec=dec, m=m, a=a)

def check_eval(N, Qp, rng, samples=6):
    for q in Qp:
        T = Tables(q, N)
        a = [rng.randrange(q) for _ in range(N)]
        A = fwd(a, T)
        for k in rng.sample(range(N), samples):
            x = pow(T.psi, 2 * brv(k, T.bits) + 1, q)
            assert A[k] == sum(c * pow(x, j, q) for j, c in enumerate(a)) % q, (N, q, k)
        assert list(inv(A, T)) == a
    return True

def check_product(N, Qp, a, b):
    Q = math.prod(Qp)
    z, _ = bfv.negacyclic_mul(bfv.poly_centered(a, Q), bfv.poly_centered(b, Q))
    want = [x % Q for x in z]
    outs, _ = rns_negacyclic(a, b, Qp, N)
    got = crt(outs, Qp)
    for r, q in zip(outs, Qp):
        assert list(r) == [x % q for x in want]
    return list(got) == want

def main():
    rng = random.Random(20261106)
    res = {}
    for N in (8192, 16384):
        for L in (3, 4):
            Qp, t = primes(N, L)
            Q = math.prod(Qp)
            key = "N%d_L%d" % (N, L)
            ok_eval = check_eval(N, Qp, rng)
            a = [rng.randrange(Q) for _ in range(N)]
            b = [rng.randrange(Q) for _ in range(N)]
            ok_full = check_product(N, Qp, a, b)
            # he_outer shape: sparse D_a (coefficients 64 r, centered mod t) times a uniform ciphertext component
            D = [0] * N
            for r in range(N // 64):
                D[64 * r] = rng.randrange(t) - t // 2
            ok_sparse = check_product(N, Qp, [x % Q for x in D], b)
            res[key] = dict(eval=ok_eval, full=ok_full, sparse=ok_sparse, psi=[Tables(q, N).psi for q in Qp], t=t)
            print(key, res[key], flush=True)
            assert ok_eval and ok_full and ok_sparse
    for N, L in ((8192, 3), (16384, 3), (8192, 4), (16384, 4)):
        Qp, t = primes(N, L)
        R = draw_return(N, Qp, t, seed=1)
        c0s, c1s, dec, amb, _ = return_rns(R["P"], R["ct"], R["pk"], R["u"], R["e0"], R["e1"], R["M"], R["flood"],
                                           R["s"], Qp, t, N)
        ok_ct = list(crt(c0s, Qp)) == R["c0"] and list(crt(c1s, Qp)) == R["c1"]
        ok_dec = dec == R["dec"]
        print("return N%d L%d: ciphertext equal %s, decryption equal %s, ambiguous %d" % (N, L, ok_ct, ok_dec, amb))
        assert ok_ct and ok_dec and amb == 0
    print("ALL REFERENCE CHECKS PASS")

if __name__ == "__main__":
    sys.exit(main())
