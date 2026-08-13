#!/usr/bin/env python3
"""
The commitment exchange rate, and the matmul interior/boundary ratio.

Companion to notes/boundary-statements.md.  Exists because SELVAGE.md quoted
"5,461x at n=4096" and notes/prover-floor.md quoted "Ratio = 4n/3" with NO
derivation artifact behind either -- `rg '5,461'` found three prose mentions and
zero scripts.  This is that script.

Every constant is IMPORTED IN SPIRIT from prover_floor.py (which cites its own
measurements in-line); nothing new is measured here.  The only new content is
the EXCHANGE RATE: how many field multiplications one committed base felt is
worth, which turns "commit the boundary, not the interior" from a slogan into a
threshold rule.

Currency: base-field multiplications.
"""
from math import log2

# --- constants, identical to paper/scripts/prover_floor.py -------------------
# breadstuffs/docs/deos/GPU-PROVER-PROTOTYPE.md:632 (counted from p3 82cfad7)
P2_MULS_BB, P2_ADDS_BB, P2_RATE = 655, 1309, 8
BB_OPEQ = P2_MULS_BB + P2_ADDS_BB / 3      # mult-equiv per Poseidon2 permutation


def per_element(b, w, log_h, d=3, k=2, perm=BB_OPEQ):
    """(hash, encode, sumcheck) mult-equiv per committed base felt.

    hash      leaves h*2^b of width w -> ceil(w/8) sponge perms; tree compress;
              FRI batches all w columns into ONE codeword before folding
    encode    iNTT size h once + 2^b forward NTTs
    sumcheck  linear-time folding, INDEPENDENT of the blowup -- this is also the
              per-value cost of VIRTUALIZING rather than committing
    """
    hash_perms = (2 ** b) * (1 / P2_RATE + 2 / w)
    return hash_perms * perm, (2 ** b + 1) * log_h / 2, (d - 1) * k * 10


W, LOG_H = 48, 20

print("=" * 79)
print("1.  THE EXCHANGE RATE -- mult-equiv per COMMITTED base felt")
print(f"    (w={W}, h=2^{LOG_H}, d=3, k=2)")
print("=" * 79)
print(f"  {'lb':>3} {'hash':>10} {'encode':>8} {'sumck':>6} {'TOTAL':>10} {'vs virtualize':>15}")
VIRT = per_element(4, W, LOG_H)[2]           # the folding term, per value per layer
for b in (1, 2, 3, 4, 5, 6):
    hm, en, sc = per_element(b, W, LOG_H)
    t = hm + en + sc
    print(f"  {b:>3} {hm:>10.0f} {en:>8.0f} {sc:>6.0f} {t:>10.0f} {t/VIRT:>14.0f}x")

print(f"""
  Virtualizing a value costs the FOLDING term alone: {VIRT:.0f} mult-equiv per
  value per sumcheck layer it participates in.

  ** ONE COMMITTED BASE FELT IS WORTH ~{sum(per_element(4,W,LOG_H)):.0f} FIELD MULTIPLICATIONS AT lb=4,
     ~{sum(per_element(6,W,LOG_H)):.0f} AT THE DEPLOYED lb=6.  Virtualizing one costs ~{VIRT:.0f}. **

  DECISION RULE: virtualize a value iff the number of sumcheck layers it
  participates in is below {sum(per_element(4,W,LOG_H))/VIRT:.0f} (lb=4) / {sum(per_element(6,W,LOG_H))/VIRT:.0f} (lb=6).

  This LOCATES the sweet spot Thaler asserts in eprint 2025/2041 Sec 1
  ("commit to as little data as possible.  Not zero -- there's a sweet spot").
  The survey states the tension; nobody prices it.

  ** SUNSET CONDITION.  The rule is an empirical claim about alpha/beta, not a
  theorem.  At lb=1 the ratio is {sum(per_element(1,W,LOG_H))/VIRT:.0f}x, not {sum(per_element(6,W,LOG_H))/VIRT:.0f}x -- a 28x swing across the
  blowup knob.  Cheaper commitment moves the optimal cut TOWARD materializing. **
""")

print("=" * 79)
print("2.  MATMUL -- the marquee figure, priced under the full cost function")
print("=" * 79)
print("""
  MATERIALIZED (an AIR with one row per multiply-accumulate): committed cells
  per row are a_ik, b_kj, the product, and the running accumulator = 4.
  -> 4n^3 committed felts.   <- this is where the "4" in "4n/3" comes from
  VIRTUALIZED (Thaler CRYPTO'13 Thm 3 / the relation sumcheck): commit A, B, C.
  -> 3n^2 committed felts, and the prover's proof overhead is ADDITIVE O(n^2)
     over ANY unverifiable matmul algorithm (so the route is omega-agnostic).
""")
print(f"  {'n':>6} {'AIR felts':>15} {'virt felts':>11} {'AIR cost':>11} {'virt cost':>11} {'ratio':>8} {'4n/3':>8}")
LB = 4
for n in (256, 1024, 4096):
    air_rows = n ** 3
    air_felts = 4 * air_rows
    virt_felts = 3 * n * n
    air_cost = air_felts * sum(per_element(LB, W, int(log2(air_rows)) + 1))
    # the n^3 field work to COMPUTE C is not proof overhead; the sumcheck folding
    # over the n^2-sized MLEs is
    virt_cost = virt_felts * sum(per_element(LB, W, int(log2(n * n)) + 1)) + 2 * (n ** 2) * VIRT
    print(f"  {n:>6} {air_felts:>15,} {virt_felts:>11,} {air_cost:>11.3e} "
          f"{virt_cost:>11.3e} {air_cost/virt_cost:>7.0f}x {4*n/3:>7.0f}x")

print("""
  The full cost function and the naive 4n/3 element count agree to 2.4%.
  So SELVAGE's "5,461x at n=4096" CHECKS OUT -- it was still an unscripted
  number in a marquee position, which is why this file exists.

  NAMED INADEQUACIES
  - The AIR row model (4 committed cells/MAC, ignoring selectors) is a shape
    estimate, not a census of an emitted object.  A real AIR is wider.
  - per_element over-predicts below lb=4 (query work dominates there) -- same
    named inadequacy as prover_floor.py.
  - "virt cost" prices the COMMITMENT and the FOLDING.  It does not price proof
    size or recursion, which is the third axis of the trade and the one that
    stops "commit one element and prove everything" from being correct.
""")
