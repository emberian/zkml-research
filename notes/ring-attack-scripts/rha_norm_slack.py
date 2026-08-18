"""
ITEM 2 -- THE FREE-NORM-CHECK ASSUMPTION, PRICED.

The question from the brief: "What breaks if the norm check is absent or cheap?
Is there a forgery that exploits it?"

THE CLAIM UNDER TEST (mine, derived; this script is what makes it measured):

  The gadget-Feistel pins its plane decomposition UNIQUELY only because
  B^K is barely above q:  B^K = 2^64, q = 2^64 - 257, so gamma = B^K - q = 257
  and the ambiguity rate is gamma/q = 2^-56.  That is the WHOLE reason the
  modulus was moved off the deployed Frog value, and the design note prices the
  residual grinding at ~2^54.

  THAT ENTIRE ANALYSIS IS CONDITIONAL ON THE NORM CHECK BEING EXACT AT B.

  If the host's infinity-norm check certifies only ||Y||_inf < B' = 2^s * B
  (i.e. s bits of SLACK), the count of admissible plane vectors per coefficient
  is B'^K / q = 2^(4s), so the free-choice budget is

        4s bits per COEFFICIENT   ->   16 * 4s = 64s bits per RING ELEMENT.

  s = 1 (a factor-2 slack) therefore hands a malicious prover 2^64 free
  Fiat-Shamir choices per absorbed ring element, and s = 2 hands it 2^128.

WHY THIS IS NOT A HYPOTHETICAL SLACK.  notes/ring-hash-dual-mode.md Sec.5c
already records, as an ACCEPTED cost, a "x1-2 norm-control factor" for the
LatticeFold-family decomposition machinery, because strong-sampling challenges
have unbounded coefficient norm and folding grows witness norms.  x2 is s = 1.
The slack and the gamma analysis live in the same design family and have never
been multiplied together.

WHAT IS MEASURED HERE
  (1) EXHAUSTIVE, at a knife-edge toy (B^K just above q): the number of
      admissible plane vectors per value, as a function of the slack.  This is
      the law 2^(4s), measured, not asserted.
  (2) A LIVE GUARD: the same measurement against a WRONG law, which must go RED;
      and a structural control (K too small, so B^K < q) which must also go RED.
  (3) CONSTRUCTIVE at DEPLOYMENT parameters (q = 2^64-257, B = 2^16, K = 4):
      an explicit family of distinct plane vectors for one value under slack,
      and a demonstration that they produce DIFFERENT round-function outputs
      -- i.e. a different Fiat-Shamir challenge.  This is the forgery.
  (4) The grinding budget per element and per permutation call, in bits.

HOUSE LAW: every guard row below is proved live by INJECTION (a deliberately
wrong expectation is fed in and the row must refuse it).  A guard that only
ever passes is not a guard.
"""
import random
from math import log2

# ----------------------------------------------------------------- toy scale
# knife-edge toy mirroring the real shape:  B^K just above q, q prime.
TOY = [
    # (B, K, q, label)      B^K must be just above q, as at deployment
    (4, 4, 251, "B=4,K=4,B^K=256,q=251 (gamma=5)"),
    (2, 6, 61, "B=2,K=6,B^K=64,q=61 (gamma=3)"),
    (8, 3, 509, "B=8,K=3,B^K=512,q=509 (gamma=3)"),
]


def count_reps(v, q, B, K, Bp):
    """#{ (y_0..y_{K-1}) in [0,Bp)^K : sum_j B^j y_j = v mod q }, exhaustive."""
    n = 0
    stack = [(0, 0)]  # (index, partial sum mod q)
    # iterative product to keep memory flat
    def rec(j, acc):
        nonlocal n
        if j == K:
            if acc % q == v % q:
                n += 1
            return
        Bj = pow(B, j, q)
        for y in range(Bp):
            rec(j + 1, (acc + Bj * y) % q)
    rec(0, 0)
    return n


print("=" * 78)
print("(1) EXHAUSTIVE: admissible plane vectors per value vs NORM SLACK")
print("=" * 78)
print("    law under test:  mean #reps  =  B'^K / q   with  B' = 2^s * B")
print("    so bits of free choice per coefficient = K*s  (K=4 at deployment)")
print()

rows = []
for (B, K, q, label) in TOY:
    print(f"  {label}")
    for s in (0, 1, 2):
        Bp = B * (2 ** s)
        # average over all values in Z_q (exhaustive in v as well)
        tot = 0
        for v in range(q):
            tot += count_reps(v, q, B, K, Bp)
        mean = tot / q
        pred = (Bp ** K) / q
        ok = abs(mean - pred) < 1e-9
        bits = log2(mean) if mean > 0 else float("-inf")
        rows.append((label, s, mean, pred, ok))
        print(f"    s={s}  B'={Bp:<4} measured mean reps = {mean:10.4f}"
              f"   predicted B'^K/q = {pred:10.4f}   {'OK' if ok else 'MISMATCH'}"
              f"   [{bits:5.2f} bits/coeff]")
    print()

assert all(r[4] for r in rows), "the law B'^K/q must hold exactly (it is a counting identity)"
print("  -> the law holds EXACTLY at every toy and every slack (it is a counting")
print("     identity: the tuple count is B'^K and it is equidistributed over Z_q).")

# ------------------------------------------------------------------- guards
print()
print("=" * 78)
print("(2) GUARDS -- PROVED LIVE BY INJECTION (each must REFUSE)")
print("=" * 78)

# GUARD A: inject a WRONG law (the one a careless reading gives: B'/q, i.e.
# treating the slack as if it bought only ONE plane's worth of freedom).
B, K, q = 4, 4, 251
wrong_hits = 0
for s in (1, 2):
    Bp = B * (2 ** s)
    tot = sum(count_reps(v, q, B, K, Bp) for v in range(q))
    mean = tot / q
    wrong_pred = (Bp ** 1) / q * (B ** (K - 1))   # a plausible-but-wrong law
    if abs(mean - wrong_pred) < 1e-9:
        wrong_hits += 1
print(f"  GUARD A  wrong law (slack buys one plane, not K): agreed on "
      f"{wrong_hits}/2 slacks  -> {'DEAD GUARD' if wrong_hits else 'LIVE (refused)'}")
assert wrong_hits == 0, "guard A failed to refuse the wrong law"

# GUARD B: structural control -- K too small, B^K < q.  Then most values have
# NO representation at all and the mean must fall below 1 at s=0.
B2, K2, q2 = 4, 3, 251           # B^K = 64 < 251
tot = sum(count_reps(v, q2, B2, K2, B2) for v in range(q2))
mean_small = tot / q2
print(f"  GUARD B  B^K={B2**K2} < q={q2} at s=0: mean reps = {mean_small:.4f}"
      f"  (must be < 1)  -> {'LIVE (refused >=1)' if mean_small < 1 else 'DEAD GUARD'}")
assert mean_small < 1.0

# GUARD C: the counter itself must be sensitive to the modulus.
# ⚑ HISTORY, KEPT PER minted-a-falsifier-that-stopped-falsifying: the first
# version of this guard compared count_reps(v=7, q=251) against
# count_reps(v=7, q=257) and asserted they differ.  BOTH ARE 1.  The mutation
# was a NO-OP on that value and the guard was DEAD -- it would have passed
# forever while asserting nothing.  It is rebuilt CONSTRUCTIVELY below: the
# discriminating statistic is the number of values with NO representation,
# which is 0 when B^K > q and necessarily > 0 when B^K < q (pigeonhole).
zeros_ok = sum(1 for v in range(251) if count_reps(v, 251, 4, 4, 4) == 0)   # B^K=256 > q
zeros_mut = sum(1 for v in range(257) if count_reps(v, 257, 4, 4, 4) == 0)  # B^K=256 < q
print(f"  GUARD C  counter sensitivity (values with ZERO reps):"
      f" q=251 (B^K>q) -> {zeros_ok},  q=257 (B^K<q) -> {zeros_mut}"
      f"  -> {'LIVE (differs)' if zeros_ok != zeros_mut else 'DEAD GUARD'}")
assert zeros_ok == 0 and zeros_mut > 0 and zeros_ok != zeros_mut

# ------------------------------------------------- deployment, constructively
print()
print("=" * 78)
print("(3) DEPLOYMENT PARAMETERS -- an explicit forgery family under slack")
print("=" * 78)
Q = (1 << 64) - 257
B = 1 << 16
K = 4
D = 16
assert Q % 32 == 31
gamma = (1 << 64) - Q
print(f"  q = 2^64-257 = {Q}   B = 2^16   K = 4   gamma = B^K - q = {gamma}")
print(f"  gamma/q = 2^{log2(gamma/Q):.1f}   (this is the EXACT-norm-check picture:")
print(f"    a prover must grind ~2^{log2(Q/gamma/D):.0f} to find ONE ambiguous coefficient)")
print()


def canon(v):
    return [(v >> (16 * j)) & 0xFFFF for j in range(4)]


def recompose(y):
    return sum(y[j] << (16 * j) for j in range(4)) % Q


def borrow_family(v, c):
    """All plane vectors reachable from the canonical digits of v by borrowing
    t_j in [0,c) units from plane j+1 into plane j.  Every member satisfies
    recomposition and has ||y||_inf < c*B."""
    y0 = canon(v)
    out = []
    for t0 in range(c):
        for t1 in range(c):
            for t2 in range(c):
                y = y0[:]
                y[0] += t0 << 16
                y[1] -= t0
                y[1] += t1 << 16
                y[2] -= t1
                y[2] += t2 << 16
                y[3] -= t2
                if all(0 <= x < c * B for x in y):
                    out.append(tuple(y))
    return sorted(set(out))


# pick a value whose canonical digits are all >= c-1 so every borrow is legal
rng = random.Random(20260818)
v = rng.randrange(Q // 2, Q)          # generic large value
for c, s in ((2, 1), (4, 2)):
    fam = borrow_family(v, c)
    assert all(recompose(y) == v % Q for y in fam), "a family member broke recomposition"
    assert all(max(y) < c * B for y in fam), "a family member broke the slack bound"
    per_elt = len(fam) ** D
    print(f"  slack s={s} (norm bound {c}*B = 2^{16+s}):")
    print(f"    distinct plane vectors for ONE coefficient : {len(fam)}  "
          f"(= {log2(len(fam)):.1f} bits)   [predicted B'^K/q = {(c*B)**K/Q:.0f}]")
    print(f"    per RING ELEMENT ({D} coefficients)         : {len(fam)}^{D} "
          f"= 2^{log2(per_elt):.0f}")
    print(f"    per PERMUTATION CALL (rate 7 elements)     : 2^{7*log2(per_elt):.0f}")
print()
print("  NB the borrow family is a CONSTRUCTIVE LOWER BOUND (c^3 per coefficient);")
print("  the exhaustive law B'^K/q = 2^(4s) is the exact count and is larger.")

# ---------------------------------------- the forgery changes the hash output
print()
print("=" * 78)
print("(4) THE FORGERY: distinct admissible planes -> DISTINCT round output")
print("=" * 78)
print("  (a plane choice is only a Fiat-Shamir grinding channel if it MOVES the")
print("   hash.  measured here on the real round function, not assumed.)")


def ring_mul(a, b, q=Q, d=D):
    r = [0] * d
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            e = i + j
            if e < d:
                r[e] = (r[e] + x * y) % q
            else:
                r[e - d] = (r[e - d] - x * y) % q
    return r


rr = lambda: [rng.randrange(Q) for _ in range(D)]
g = [rr() for _ in range(K)]
h = [rr() for _ in range(2)]


def F_one_element(planes):
    """the per-element contribution to F_r: sum_j g_j*Y_j + sum_{j<2} h_j*(Y_j*Y_{j+1}).
    This is EXACTLY the i'=fixed term of design_gadget_feistel.py's F()."""
    acc = [0] * D
    for j in range(K):
        acc = [(x + y) % Q for x, y in zip(acc, ring_mul(g[j], planes[j]))]
    for j in range(2):
        z = ring_mul(planes[j], planes[j + 1])
        acc = [(x + y) % Q for x, y in zip(acc, ring_mul(h[j], z))]
    return acc


# build one ring element, take the canonical planes and one borrow variant
elt = [rng.randrange(Q // 2, Q) for _ in range(D)]
planes_canon = [[canon(c)[j] for c in elt] for j in range(K)]
# borrow one unit at position 0 in coefficient 0 only -- the MINIMAL forgery
planes_forge = [p[:] for p in planes_canon]
planes_forge[0][0] += 1 << 16
planes_forge[1][0] -= 1

rec_canon = [sum(planes_canon[j][i] << (16 * j) for j in range(K)) % Q for i in range(D)]
rec_forge = [sum(planes_forge[j][i] << (16 * j) for j in range(K)) % Q for i in range(D)]
print(f"  both plane sets recompose to the SAME ring element : {rec_canon == rec_forge}")
print(f"  canonical  ||Y||_inf = {max(max(p) for p in planes_canon)}  (< B = {B})")
print(f"  forged     ||Y||_inf = {max(max(p) for p in planes_forge)}  "
      f"(< 2B = {2*B}, i.e. passes a 1-bit-slack check, FAILS an exact one)")
out_c = F_one_element(planes_canon)
out_f = F_one_element(planes_forge)
print(f"  round-function outputs differ : {out_c != out_f}"
      f"   ({sum(1 for a,b in zip(out_c,out_f) if a!=b)}/{D} coefficients differ)")
assert rec_canon == rec_forge
assert out_c != out_f

# GUARD D (live): if we DO NOT forge, the outputs must be identical.  This is
# the mutation-actually-happened check -- the recorded class where a falsifier
# silently became a no-op.
out_c2 = F_one_element([p[:] for p in planes_canon])
print(f"  GUARD D  no-forgery control: outputs identical = {out_c2 == out_c}"
      f"  -> {'LIVE' if out_c2 == out_c else 'BROKEN HARNESS'}")
assert out_c2 == out_c

print()
print("=" * 78)
print("VERDICT")
print("=" * 78)
print(f"""  The exact-norm-check picture (gamma/q = 2^{log2(gamma/Q):.1f}, ~2^54 grinding) is
  CORRECT AND FRAGILE.  It is not a property of the modulus alone; it is a
  property of the modulus AND an EXACT infinity-norm check at bound B.

    slack s bits  ->  4s bits per coefficient  ->  64s bits per ring element
                  ->  448s bits per permutation call at rate 7.

  s = 1  (the x2 norm-control factor already accepted in ring-hash-dual-mode
  Sec.5c) restores 2^64 free Fiat-Shamir choices per absorbed element, versus
  the 2^54 GRINDING COST the design credits itself with.  That is not a
  degradation of the margin; it is the inversion of it -- the prover stops
  paying and starts choosing.
""")
