"""Falsifier: UNSALTED Merkle leaves turn the opened columns into a guess-confirmation oracle (gen 4, 2026-11-06).

A committed row is f of degree < k + t: its k message values plus t hiding values. Opening T = t columns fixes
the hiding part once the message is known. A verifier holding a GUESS of the message (or a coalition of n - 1
custodians holding their own shares and a guess of the secret, which gives the last custodian's share) interpolates
f from the k guessed values and the T opened values, evaluates it at an UNOPENED column, and compares
H("leaf", column) with the sibling leaf hash that every authentication path reveals. A right guess matches and a
wrong one does not. Salted leaves (H("leaf", salt, column), with a secret 256-bit salt opened only with its own
column) remove the oracle.

Run against the real commitment code (cozk.Prover.add_row / commit / path), with the leaves unsalted
(cosnark.SALT_LEAVES = False) and then salted:

    python3 leaf_salt_falsifier.py      # exits 1 unless unsalted CONFIRMS the guess and salted does not
"""
import random
import sys

import cosnark as CS
import cozk as Z
from cosnark import H


def interp_eval(nodes, vals, x, p):
    tot = 0
    for i, (xi, yi) in enumerate(zip(nodes, vals)):
        num = den = 1
        for j, xj in enumerate(nodes):
            if j != i:
                num = num * (x - xj) % p
                den = den * (xi - xj) % p
        tot = (tot + yi * num * pow(den, -1, p)) % p
    return tot


def oracle(salted, guess_right):
    CS.SALT_LEAVES = salted
    p = 2305843009212399617
    P = Z.Params(p, k=8, t=8, T=8)
    rng = random.Random(3)
    secret = [rng.randint(-7, 7) % p for _ in range(P.k)]            # e.g. a row of small weights
    sh0 = [rng.randrange(p) for _ in secret]
    sh1 = [rng.randrange(p) for _ in secret]
    sh2 = [(v - a - b) % p for v, a, b in zip(secret, sh0, sh1)]
    prv = Z.Prover(P, 3, ("falsifier", 0))
    prv.add_row([sh0, sh1, sh2])
    prv.commit()                                                     # one group = this row; per-party trees
    g = prv.groups[0]
    J = [2 * i for i in range(P.T)]                                   # opened columns (even); their siblings are not
    opened = [([c[j] for c in g["codes"][2]], Z.path(g["trees"][2], j)) for j in J]
    # the coalition (custodians 0 and 1) and a guess of the secret: custodian 2's share
    guess = list(secret) if guess_right else [(secret[0] + 1) % p] + secret[1:]
    g2 = [(v - a - b) % p for v, a, b in zip(guess, sh0, sh1)]
    nodes = P.zeta + [j + 1 for j in J]
    vals = g2 + [col[0] for col, _ in opened]
    jj = J[0]
    sib = jj ^ 1
    predicted = interp_eval(nodes, vals, sib + 1, p)
    leaf_seen = opened[0][1][1]                                      # path = [salt, sibling leaf, ...]
    salt_guess = ""                                                  # the verifier does not know the sibling's salt
    return H("leaf", salt_guess, [predicted]) == leaf_seen


def main():
    res = {(s, r): oracle(s, r) for s in (False, True) for r in (True, False)}
    for (s, r), v in res.items():
        print(f"leaves {'salted  ' if s else 'UNSALTED'}  guess {'right' if r else 'wrong'}: "
              f"{'CONFIRMED' if v else 'not confirmed'}")
    ok = res[(False, True)] and not res[(False, False)] and not res[(True, True)] and not res[(True, False)]
    CS.SALT_LEAVES = True
    print("FALSIFIER PASS" if ok else "FALSIFIER FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
