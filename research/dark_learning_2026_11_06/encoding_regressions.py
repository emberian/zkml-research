"""Regression falsifiers for the two large-t BFV encoding fixes (VERDICTS §9). Counts nothing; exits 1 on
any regression. Runs in about a minute at N = 8192, the d = 64 build's parameters (at N = 1024 the primes give Q mod t ~ 2^49 and both broken encodings survive one product, so the falsifier needs the deployed N).

With t a ~61-bit prime (t = the SPDZ field, so encryption-to-shares lands in the MPC field), r = Q mod t
is ~2^58. Textbook BFV encodes Delta m with Delta = floor(Q/t), which differs from the exact (Q/t) m by
r m / t. A ct x ct multiplies that error by about t N |s|. With centered encoding of a small message,
r m / t is a few units, which is harmless. It is fatal when the integer being encoded is NOT small:
  F1  textbook Delta m with m's NON-centered representative (a negative m stored as t - |m|);
  F2  Delta (m + k t), the value that additive shares reconstruct to before reduction mod t
      (shares-to-encryption with Delta M_i per party, or a mask pair Enc(R) + (m - R)).
Each falsifier must FAIL under the broken encoding and PASS under the fix:
  fix F1: centered representative (bfv_ref.BFV.encrypt);
  fix F2: exact scaling round(Q (m + k t) / t) = round(Q m / t) + k Q (bfv_ref.BFV.encrypt_exact).
"""
import random
import sys

import bfv_ref as bfv
import fhe_fork as FF

def encrypt_with(sch, rep, scale):
    """rep: the integer representative per coefficient; scale(x) -> its encoding in Z_Q."""
    a = sch.uniform()
    e = sch.small_error()
    as_, _ = bfv.negacyclic_mul(bfv.poly_centered(a, sch.Q), sch.s)
    return ([(scale(x) - y - ee) % sch.Q for x, y, ee in zip(rep, as_, e)], a)

def product(sch, c1, c2):
    d, _, _ = sch.tensor_lifted(c1, c2)
    return tuple([y % sch.Q for y in sch.scale(dk)[0]] for dk in d)

def run(N=8192, seed=5):
    sch, Qp, Bp, t = FF.setup(N=N)
    sch.keygen()
    Q = sch.Q
    rng = random.Random(seed)
    m1 = [rng.randint(-7, 7) for _ in range(N)]
    m2 = [rng.randint(-7, 7) for _ in range(N)]
    want, _ = bfv.negacyclic_mul(m1, m2)
    want = [x % t for x in want]
    textbook = lambda x: sch.delta * x
    exact = lambda x: (2 * Q * x + t) // (2 * t)
    noncentered = [x % t for x in m1]                      # -3 stored as t - 3
    k = [rng.choice((-1, 1, 2)) for _ in range(N)]
    shares_sum = [x + kk * t for x, kk in zip(m1, k)]      # what three additive shares reconstruct to
    c2 = encrypt_with(sch, m2, exact)
    cases = [
        ("F1 textbook, non-centered representative", noncentered, textbook, False),
        ("F1 fix: textbook, centered representative", m1, textbook, True),
        ("F2 textbook Delta (m + k t)", shares_sum, textbook, False),
        ("F2 fix: exact round(Q (m + k t) / t)", shares_sum, exact, True),
    ]
    ok = True
    print(f"N = {N}, log Q = {Q.bit_length()}, t = {t.bit_length()}-bit, Q mod t = {(Q % t).bit_length()}-bit")
    for name, rep, scale, should_pass in cases:
        c1 = encrypt_with(sch, rep, scale)
        fresh_ok = sch.decrypt(c1) == [x % t for x in m1]
        prod_ok = sch.decrypt(product(sch, c1, c2)) == want
        good = fresh_ok and (prod_ok == should_pass)
        ok &= good
        print(f"  {name:45s} fresh decrypts: {fresh_ok}  after ct x ct: {prod_ok}  "
              f"(expected {should_pass})  {'ok' if good else 'REGRESSION'}")
    # the library entry points used by the build
    for name, enc in (("bfv_ref.encrypt (centered)", lambda: sch.encrypt([x % t for x in m1])),
                      ("bfv_ref.encrypt_exact on shares sum", lambda: sch.encrypt_exact([x % t for x in shares_sum]))):
        good = sch.decrypt(product(sch, enc(), c2)) == want
        ok &= good
        print(f"  {name:45s} after ct x ct: {good}  {'ok' if good else 'REGRESSION'}")
    print("ENCODING REGRESSIONS", "PASS" if ok else "FAIL")
    return ok

if __name__ == "__main__":
    sys.exit(0 if run() else 1)
