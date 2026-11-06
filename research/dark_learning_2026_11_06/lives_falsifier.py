"""Regression falsifier for review3's ZK BREAK (2026-11-06): a hiding commitment opened in a THIRD proof reveals its
data (3 x 64 distinct columns exceed the 128 tails; interpolation recovers W). Fixed: the custodians keep a
per-commitment life counter and refuse a third opening (cosnark.LifeExhausted). The script checks both: the honest
counter refuses, and a forced third opening (colluders bypassing their own counter) does leak, which is why the
counter matters. Exits 1 unless both hold. The interpolation is review3/lives_leak.py's."""
import random
import sys

import bfv_ref as bfv
import cosnark as CS
import cosnark_zk as ZK

CS.HIDE, CS.NMASK = CS.LIVES * CS.T_COLS, CS.LIVES        # the pinned ZK parameters (proofwire.PARAMS)

def interp_coeffs(xs, ys, p):
    n = len(xs); c = list(ys)
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            c[i] = (c[i] - c[i - 1]) * pow(xs[i] - xs[i - j], -1, p) % p
    poly = [0] * n
    for i in range(n - 1, -1, -1):
        new = [0] * n
        for k in range(n - 1):
            new[k + 1] = (new[k + 1] + poly[k]) % p
            new[k] = (new[k] - xs[i] * poly[k]) % p
        new[0] = (new[0] + c[i]) % p
        poly = new
    return poly

def openings(com, n_proofs, p, force=False):
    pts = {}
    if force:
        com.max_lives = 99
    for life in range(n_proofs):
        com.base = 0 if life == 0 else com.block
        tr = CS.Transcript(f"proof-{life}")
        _, _, cols = CS.pcs_prove({"W1n": com}, [], tr, 3, p)
        J, per = cols["W1n"]
        for jj, j in enumerate(J):
            pts[com.pts[j]] = [sum(per[i][jj][0][r] for i in range(3)) % p for r in range(com.Rd)]
    return pts

def main():
    p = bfv.ntt_primes(61, 4, 16384)[3]
    rng = random.Random(7)
    d = 4
    secret = [rng.randrange(-7, 8) % p for _ in range(d * d)]
    sh = [[rng.randrange(p) for _ in secret] for _ in range(2)]
    sh.append([(v - a - b) % p for v, a, b in zip(secret, *sh)])
    com = ZK.ZKPCS(p, sh, "W1n")
    try:
        openings(com, 3, p)
        refused = False
    except CS.LifeExhausted as e:
        refused = True
        print("honest third opening:", "REFUSED", e)
    com2 = ZK.ZKPCS(p, sh, "W1n")
    pts = openings(com2, 3, p, force=True)
    xs = sorted(pts)[:com2.W]
    rec = []
    for r in range(com2.Rd):
        rec += interp_coeffs(xs, [pts[x][r] for x in xs], p)[:com2.C]
    leaks = rec == secret
    print("forced third opening:", len(pts), "distinct points for rows of degree <", com2.W, "; data recovered:", leaks)
    ok = refused and leaks
    print("FALSIFIER", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
