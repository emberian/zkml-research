"""Falsifier: layer-1 hiding with PUBLICLY seeded tails does not hide (found 2026-11-06 while building ZK layers
2-3). SharePCS used to seed every custodian's tail coefficients and mask rows from (label, party, hide, nmask),
all public. A verifier that recomputes the tails subtracts them from an opened column and reads the DATA part of
each row's codeword at that point, a linear functional of the committed vector.
With secret seeds (the fix), the same computation gives an unrelated value.

    python3 zk_seed_falsifier.py      # exits 1 unless legacy LEAKS and fixed HIDES
"""
import random
import sys

import cosnark as CS
from cosnark import H

def attack(com, label, p, n, j):
    """The verifier's computation: tails from the public seed, subtracted from party i's opened column j."""
    x = com.pts[j]
    recovered = []
    for r in range(com.Rd):
        tot = 0
        for i in range(n):
            col, _ = com.open_col(i, j)
            rng = random.Random(H("mask", label, i, com.hide, com.nmask))
            tails = None
            for rr in range(com.Rd):
                t = [rng.randrange(p) for _ in range(com.W - com.C)]
                if rr == r:
                    tails = t
            tail_val = sum(c * pow(x, com.C + k, p) for k, c in enumerate(tails)) % p
            tot = (tot + col[r] - tail_val) % p
        recovered.append(tot)
    return recovered

def main():
    p, n, C = 2305843009212399617, 3, 8
    rng = random.Random(7)
    secret = [rng.randrange(1000) for _ in range(64)]               # the committed vector (e.g. weights)
    shares = [[rng.randrange(p) for _ in secret] for _ in range(n - 1)]
    shares.append([(v - sum(c)) % p for v, c in zip(secret, zip(*shares))])
    out = {}
    for name, legacy in (("legacy_public_seed", True), ("secret_seed", False)):
        com = CS.SharePCS(p, shares, "W1", hide=128, nmask=2, legacy_public_seed=legacy)
        j = 5
        got = attack(com, "W1", p, n, j)
        x = com.pts[j]
        truth = [sum(secret[r * com.C + c] * pow(x, c, p) for c in range(com.C)) % p for r in range(com.Rd)]
        out[name] = got == truth
        print(name, "verifier recovers the data part of every row at the opened column:", got == truth)
    ok = out["legacy_public_seed"] and not out["secret_seed"]
    print("FALSIFIER", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
