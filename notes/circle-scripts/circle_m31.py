#!/usr/bin/env python3
"""circle_m31.py -- the circle-aligned vFHE candidate: algebra check + NTT/limb counts.

No dependencies.  python3 circle_m31.py   (~10 s; the N=8192 half-NTT verification dominates)

Part 1  The algebra over p = 2^31 - 1 (M31):
        p = 3 mod 4, v2(p+1) = 31, v2(p-1) = 1, p = -1 mod 2N for N = 4096, 8192.
        F_{p^2} = F_p[i]/(i^2+1); the circle group C(F_p) = norm-1 subgroup, order p+1 = 2^31.
        omega of order 2N lives in F_{p^2} (on the circle), never in F_p.
        X^N + 1 = prod_{j < N/2} (X^2 - c_j X + 1),  c_j = omega^{2j+1} + omega^{-(2j+1)} = 2 x_j,
        each quadratic irreducible (disc = -4 y_j^2, -1 a non-residue).  No linear factor.
        The N odd powers of omega ARE the standard-position coset Q.G_N of 2024/278 (Q = omega).
        Verified by: every c_j distinct, X^N = -1 mod each quadratic, each irreducible; N/2 distinct
        monic irreducible quadratics dividing a degree-N monic polynomial => product equals it.
Part 2  Counts, base-field multiplications only (counts are the instrument; the clock is a guest):
        (a) fully split 31-bit limb (BabyBear/KoalaBear, p = 1 mod 2N): negacyclic NTT = (N/2) log2 N.
        (b) M31 half-split: the transform F_p[X]/(X^N+1) -> (F_{p^2})^{N/2} implemented by the
            conjugate-symmetric recursion  f(w^k) = f0(w^{2k}) + w^k f1(w^{2k}),  k odd in [1, N-1],
            paired k <-> N-k so only N/4 twiddle products per level; leaf N=2 is free (omega = i).
            Base mults COUNTED by an instrumented run and checked against the closed form
            (m/4) N (log2 N - 1), m in {3 (Karatsuba/Gauss), 4 (schoolbook)}; correctness checked
            against Horner evaluation at random points.
        (c) pointwise product: full split N mults; half split N/2 F_{p^2}-mults = (m/2) N.
        (d) Kyber n=256, q=3329 for calibration of the same accounting (7 vs 8 layers, basemul 5).
        (e) limb count to log2 Q ~ 109 with a 31-bit native limb; FRI height ceilings.
"""
import random
from math import log2

p = 2**31 - 1

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k

# ---------- F_{p^2} = F_p[i], i^2 = -1 ----------
def fmul(a, b):
    (a0, a1), (b0, b1) = a, b
    return ((a0*b0 - a1*b1) % p, (a0*b1 + a1*b0) % p)

def fpow(a, e):
    r = (1, 0)
    while e:
        if e & 1:
            r = fmul(r, a)
        a = fmul(a, a); e >>= 1
    return r

def conj(a):
    return (a[0], (-a[1]) % p)

def is_residue(c):
    """Euler criterion in F_p (c != 0)."""
    return pow(c % p, (p - 1) // 2, p) == 1

# ---------- Part 1 ----------
print("=" * 88)
print("PART 1  the algebra over M31 = 2^31 - 1")
print("=" * 88)
assert p % 4 == 3
print(f"p = {p}; p mod 4 = {p % 4}; v2(p+1) = {v2(p+1)}; v2(p-1) = {v2(p-1)}; "
      f"p-1 = 2 * {(p-1)//2} (odd cofactor {(p-1)//2 % 2 == 1})")
print(f"-1 is a quadratic residue mod p: {is_residue(p-1)}  (so no i in F_p; F_p[i] is a field)")
print(f"gcd checks for Poseidon2 S-box: gcd(3,p-1)={__import__('math').gcd(3,p-1)} "
      f"gcd(5,p-1)={__import__('math').gcd(5,p-1)} gcd(7,p-1)={__import__('math').gcd(7,p-1)}")

# generator of the circle group: 2024/278 uses (2, 1268011823); verify it and its order
g = (2, 1268011823)
assert (g[0]**2 + g[1]**2) % p == 1, "not on the circle"
assert fpow(g, 2**31) == (1, 0) and fpow(g, 2**30) != (1, 0)
print(f"circle generator g = {g}: g^(2^31) = 1, g^(2^30) = {fpow(g, 2**30)} != 1  => C(F_p) cyclic of order 2^31")

def check_N(N):
    n = int(log2(N))
    assert 2**(n+1) | (p+1), "CFFT-friendly domain size (Def. 1 of 2024/278 needs 2^{n+1} | p+1)"
    assert (p + 1) % (2*N) == 0, "p = -1 mod 2N"
    w = fpow(g, 2**31 // (2*N))          # order exactly 2N
    assert fpow(w, N) == (p-1, 0) and fpow(w, 2*N) == (1, 0)
    assert fpow(w, p) == conj(w) == fpow(w, 2*N - 1), "Frobenius = inversion = conjugation"
    # X^N + 1 has no root in F_p: a root x would give x^N = -1, but x^N is a square (N even)
    # and -1 is a non-square (p = 3 mod 4).  So no linear factor.  Now the quadratics:
    cs = set()
    ok_div = ok_irr = 0
    wk = w                                 # omega^1
    w2 = fmul(w, w)
    for j in range(N // 2):
        # wk = omega^{2j+1}; c_j = wk + conj(wk) = 2*Re(wk)
        c = (2 * wk[0]) % p
        cs.add(c)
        # X^N mod (X^2 - cX + 1): represent X^e as (u + vX), square-and-multiply
        def qmul(a, b):
            (a0, a1), (b0, b1) = a, b
            t = a1 * b1 % p                 # X^2 = cX - 1
            return ((a0*b0 - t) % p, (a0*b1 + a1*b0 + c*t) % p)
        r, base, e = (1, 0), (0, 1), N
        while e:
            if e & 1:
                r = qmul(r, base)
            base = qmul(base, base); e >>= 1
        ok_div += (r == (p - 1, 0))
        disc = (c*c - 4) % p
        ok_irr += (not is_residue(disc))    # disc = -4 y^2 with y != 0: non-residue
        wk = fmul(wk, w2)
    assert len(cs) == N // 2 and ok_div == N // 2 and ok_irr == N // 2
    # Kyber round-3 spec Sect. 4.4 criterion: no factor of X^N+1 mod q of "small degree and small norm".
    # Our quadratics are X^2 - c_j X + 1; their integer norm is governed by the centred |c_j|.
    small = min(min(c, p - c) for c in cs)
    print(f"          smallest centred |c_j| over all {N//2} quadratic factors: {small} = 2^{log2(small):.2f} "
          f"(Kyber's small-norm-factor criterion: none small; sqrt(p) = 2^15.5)")
    print(f"N = {N:5d}: omega = g^(2^31/2N) has order 2N = {2*N}; omega in F_p? {w[1] == 0}; "
          f"omega^N = -1; omega^p = omega^-1")
    print(f"          X^N + 1 = prod of {N//2} DISTINCT irreducible quadratics X^2 - c_j X + 1 "
          f"(divisibility {ok_div}/{N//2}, irreducibility {ok_irr}/{N//2}); linear factors: 0")
    print(f"          CRT: F_p[X]/(X^N+1) ~= (F_{{p^2}})^{N//2}; the N odd powers of omega = the standard-position "
          f"coset Q.G_{N} (Q = omega of order 2N) of 2024/278 Sect. 3.1; c_j = 2 x_j (x-coordinate of the circle point)")
    return w

W = {N: check_N(N) for N in (4096, 8192)}

# ---------- Part 2 ----------
print()
print("=" * 88)
print("PART 2  counts (base-field multiplications)")
print("=" * 88)

class Counter:
    def __init__(self, m):
        self.m = m       # base mults per F_{p^2} x F_{p^2} product
        self.n = 0
    def mul(self, a, b):
        self.n += self.m
        return fmul(a, b)

def half_ntt(f, w, ctr):
    """Evaluate f in F_p[X] (len N, monomial coefficients) at omega^k for k odd in [1, N-1]
    (one representative per conjugate pair; the other N/2 values are the conjugates).
    Returns dict k -> f(omega^k) in F_{p^2}.  omega has order 2N."""
    N = len(f)
    if N == 1:
        return {0: (f[0] % p, 0)}          # not reached for N >= 2 in the odd-k system
    if N == 2:
        # omega has order 4 => omega = +-i; f(omega) = f0 + f1*omega: no multiplication
        a, b = f
        return {1: ((a) % p, (b * w[1]) % p) if w[0] == 0 else None}
    f0, f1 = f[0::2], f[1::2]
    w2 = fmul(w, w)                        # order N
    E0 = half_ntt(f0, w2, ctr)             # values at zeta^k, k odd in [1, N/2 - 1]
    E1 = half_ntt(f1, w2, ctr)
    out = {}
    wk = w
    wsq = fmul(w, w)
    for k in range(1, N // 2, 2):
        A = E0[k]; B = ctr.mul(wk, E1[k])  # ONE F_{p^2} product per pair (k, N-k)
        out[k] = ((A[0] + B[0]) % p, (A[1] + B[1]) % p)
        D = ((A[0] - B[0]) % p, (A[1] - B[1]) % p)   # f(omega^{k+N}) = conj(f(omega^{N-k}))
        out[N - k] = conj(D)
        wk = fmul(wk, wsq)
    return out

def horner(f, x):
    r = (0, 0)
    for c in reversed(f):
        r = fmul(r, x); r = ((r[0] + c) % p, r[1])
    return r

rng = random.Random(278)
print(f"{'N':>6} {'full-split NTT':>16} {'half-split m=3':>16} {'half-split m=4':>16} {'closed form m=3/4':>20} {'ratio m=3':>10} {'ratio m=4':>10}")
for N in (4096, 8192):
    f = [rng.randrange(p) for _ in range(N)]
    w = W[N]
    res = {}
    for m in (3, 4):
        ctr = Counter(m)
        vals = half_ntt(f, w, ctr)
        res[m] = ctr.n
        # correctness at 8 random odd k
        for k in rng.sample(range(1, N, 2), 8):
            assert vals[k] == horner(f, fpow(w, k)), "half-NTT wrong"
        assert len(vals) == N // 2
    full = (N // 2) * int(log2(N))
    cf3 = 3 * N * (int(log2(N)) - 1) // 4
    cf4 = N * (int(log2(N)) - 1)
    assert res[3] == cf3 and res[4] == cf4
    print(f"{N:6d} {full:16d} {res[3]:16d} {res[4]:16d} {str(cf3)+'/'+str(cf4):>20} {res[3]/full:10.3f} {res[4]/full:10.3f}")
print("  (half-split count verified by instrumented run == closed form (m/4).N.(log2 N - 1); values checked vs Horner)")
print("  pointwise product in the transform domain, per ring multiplication:")
for N in (4096, 8192):
    print(f"    N={N}: full split {N} base mults; half split {N//2} F_p2-mults = {3*N//2} (m=3) / {2*N} (m=4)  "
          f"=> x{3*N//2/N:.1f} / x{2*N/N:.1f}")
print("  one ring product from coefficient form (2 fwd + 1 inv transform + pointwise), N=4096:")
N = 4096
full_total = 3 * (N//2) * 12 + N
for m in (3, 4):
    half_total = 3 * (m * N * 11 // 4) + m * N // 2
    print(f"    m={m}: full {full_total}  half {half_total}  ratio x{half_total/full_total:.2f}")

print()
print("Kyber calibration (round-3 spec Sect. 1.1 / FIPS 203 Sect. 4.3): n=256, q=3329, q = 1 mod 256, not mod 512")
print(f"  full-split NTT would be 8 layers x 128 = {8*128} mults; Kyber's 7-layer NTT = {7*128}; "
      f"basemul 5 mults/pair x 128 = {5*128} vs 256 pointwise  => transform x{7/8:.3f}, pointwise x{640/256:.1f}")
print(f"  one product from coefficient form: full {3*1024+256}, Kyber {3*896+640}  (equal -- one saved layer pays for the basemul)")
print("  M31 differs from Kyber: Kyber's quadratics are X^2 - zeta (an F_q-rational CT tree exists, one layer short);")
print("  M31's are X^2 - c_j X + 1 with NO F_p-rational intermediate factor (X^{N/2} -/+ i needs i), so every")
print("  butterfly above the leaf is an F_{p^2} product: the half-split transform COSTS MORE, not less.")

print()
print("Limbs to log2 Q ~ 109 with a 31-bit native limb (M31 = 2^31-1, log2 = %.6f):" % log2(p))
print(f"  ceil(109/31) = {-(-109//31)} limbs of 31 bits = {4*31} bits; 3 x 31 = 93 bits (16 bits short);")
print(f"  M31 + two 39-bit primes (KB-limb-verdict recipe shape) = {log2(p)+39+39:.3f} bits; only ONE limb can be the prover field:")
print(f"  there is exactly one 31-bit Mersenne prime, and any other limb is a foreign prime (bridged at 2 felts/residue).")
print(f"FRI height ceilings at log_blowup 6: circle domain max 2^30 (Def. 1: 2^(n+1) | p+1 => n <= 30) -> height 2^{30-6};")
print(f"  BabyBear 2^{27-6}; KoalaBear 2^{24-6}.  The 98,304-equation family: 2^20 rows (RNS), 2^19 per limb (h2-verdict).")
print()
print("Algebra obstruction (the pointwise/ring mismatch): F_p-algebra homs to F_p --")
print(f"  from F_p^D (D = circle coset of size N): N of them; from F_p[X]/(X^N+1) over M31: 0 (no F_p-root of X^N+1).")
print("  => no F_p-algebra isomorphism; the STARK's pointwise product over the coset is NOT the FHE ring product,")
print("     whatever basis or twiddle table is chosen.  The ring product IS pointwise over (F_{p^2})^{N/2}: pairs of cells.")
print()
print("QM31 = F_{p^4}: log2 |QM31| = %.6f (BabyBear^4 = %.6f, KoalaBear^4 = %.6f)" % (
    4*log2(p), 4*log2(2013265921), 4*log2(2130706433)))
K, H, R = 1, 2**21, 97
for name, F in (("QM31", p**4), ("BabyBear^4", 2013265921**4), ("M31^5", p**5)):
    err = K*H*R / F
    print(f"  LogUp cell at deployed cap K=1,H=2^21,R=97: {name}: 2^{log2(err):.2f}  -> clears 100? {err <= 2**-100}; "
          f"K.H.R budget for 100 bits = 2^{log2(F)-100:.2f} (K.R <= {int((F/2**100)//H)} at H=2^21)")
print("ALL CHECKS PASSED")
