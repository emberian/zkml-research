#!/usr/bin/env python3
"""
C3, resolved: the Poseidon2 permutation, committed vs virtualized.

Companion to notes/poseidon2-virtualization.md.  Where boundary_exchange_rate.py
prices the exchange rate in COUNTED FIELD MULTIPLICATIONS, this one prices it in
MEASURED NANOSECONDS on the deployed prover, because the two disagree by ~10x and
the threshold rule hangs entirely on the conversion nobody had taken.

MEASURED INPUTS (breadstuffs @ 2026-08-13, macOS/arm64, laptop under swarm load):

  breadstuffs/circuit/tests/poseidon2_virtualization_measure.rs
    arm A (deployed 352-col)  2^16 perms: 1434.9 ms, 24,117,248 trace cells
    arm B (narrow  157-col)   2^16 perms:  678.8 ms, 10,289,152 trace cells
    => marginal committed felt = (1434.9-678.8) ms / 13,828,096 cells = 54.7 ns

  breadstuffs/sumcheck-toy/tests/folding_price.rs
    complete p3-sumcheck fold, degree 2, packed, 2^20 values: 11.506 ms
    => 10.97 ns per value per layer   (39.3 ns at 2^16 -- it is still amortizing)

NAMED INADEQUACIES, up front:
  - 54.7 ns is an UPPER bound on the pure commitment price: arm A also carries 211
    more constraints, so the delta bundles quotient work with commitment work.
    Every conclusion below is in the direction that a LOWER commit price makes
    virtualizing look WORSE, so the verdict is robust to this confound.
  - the degree scaling from d=2 to d=alpha+1 is MODELLED, not measured:
    p3-sumcheck's ProductPolynomial is degree-2 only.  Two bracketing models are
    carried through rather than one flattering one.
  - one box, one field, one blowup (lb=3).  boundary_exchange_rate.py's own sunset
    condition -- a 28x swing across the blowup knob -- applies here unchanged.
"""

# --- MEASURED ---------------------------------------------------------------
COMMIT_NS = (1434.9 - 678.8) * 1e6 / (24_117_248 - 10_289_152)   # ns / committed felt
FOLD_NS_D2 = 11.506e6 / 2 ** 20                                   # ns / value / layer, d=2

# --- geometries (p3, pinned rev 82cfad73) -----------------------------------
#   (name, width, full rounds, partial rounds, alpha)
GEOMS = [
    ("BabyBear  w16 a=7 (DEPLOYED)", 16, 8, 13, 7),
    ("KoalaBear w16 a=3", 16, 8, 20, 3),
    ("KoalaBear w24 a=3", 24, 8, 23, 3),
    ("BabyBear  w24 a=7", 24, 8, 21, 7),
]


def committed(w, rf, rp, all_rounds):
    """Committed base felts per permutation.

    all_rounds=True  -> arm A: every round's full state (the deployed shape).
    all_rounds=False -> arm B: inputs, each full round's post-state, and ONE
                        column per partial round (the S-box output).  Lanes
                        1..w-1 of a partial round are affine in already-committed
                        values, so an expression carries them at degree 1.
    """
    if all_rounds:
        return (1 + rf + rp) * w
    return w + rf * w + rp


def sbox_mults(alpha):
    """Multiplications to evaluate x^alpha by the addition chain p3 uses."""
    return {3: 2, 5: 3, 7: 4, 11: 5}[alpha]


def fold_ns(alpha, model):
    """ns per value per sumcheck layer for a degree-(alpha+1) round polynomial.

    LOW   cost scales with the number of round-message evaluations beyond the two
          free ends: (D-1)/(d-1), d=2.
    HIGH  cost scales with the evaluation count AND with the work per evaluation:
          ((D+1)/(d+1)) * (sbox_mults(alpha) / 1).
    """
    D = alpha + 1
    if model == "LOW":
        return FOLD_NS_D2 * (D - 1) / 1
    return FOLD_NS_D2 * ((D + 1) / 3) * sbox_mults(alpha)


print("=" * 78)
print("MEASURED EXCHANGE RATE (this box, lb=3), against the counted-mult one")
print("=" * 78)
print(f"  commit one base felt        {COMMIT_NS:8.2f} ns   (measured, upper bound)")
print(f"  fold one value, one layer   {FOLD_NS_D2:8.2f} ns   (measured, degree 2)")
print(f"  => EXCHANGE RATE            {COMMIT_NS / FOLD_NS_D2:8.2f} layers")
print("""
  boundary_exchange_rate.py says 78x (lb=4) / 308x (lb=6) in COUNTED FIELD
  MULTIPLICATIONS; at lb=3 its own model gives ~40x.  Measured in wall-clock at
  lb=3 it is ~5x.  ⚑ The gap is the mult-equiv -> nanosecond conversion, which
  was never taken: hashing SIMD-vectorizes harder than sumcheck folding does, so
  a scalar multiplication count over-prices commitment by ~8x.  The threshold
  rule is only as good as that conversion, and the conversion decides C3.
""")

print("=" * 78)
print("1.  ARM A vs ARM B -- virtualize the degree-1 lanes, INSIDE the AIR")
print("=" * 78)
print(f"  {'geometry':<30} {'arm A':>8} {'arm B':>8} {'ratio':>7} {'deg-1 felts':>12}")
for name, w, rf, rp, a in GEOMS:
    ca, cb = committed(w, rf, rp, True), committed(w, rf, rp, False)
    print(f"  {name:<30} {ca:>8} {cb:>8} {ca / cb:>6.2f}x {rp * (w - 1) + w:>12}")
print("""
  No sumcheck, no degree increase (max_constraint_degree stays alpha), fewer
  constraints, and FEWER field ops per row.  Arm B is Pareto-dominant, and the
  win GROWS as alpha falls, because a smaller alpha buys its security with MORE
  partial rounds -- which is exactly where the 16:1 saving lives.
""")

print("=" * 78)
print("2.  ARM C -- GKR: commit only the input layer, sumcheck the round chain")
print("=" * 78)
print("  Per permutation the values needing a sumcheck are exactly the S-box")
print("  inputs (linear layers fold into the claim): rf*w + rp -- which is arm B's")
print("  committed count minus the inputs.  So the question is per-value and crisp:")
print("  is folding one value once cheaper than committing it?\n")
print(f"  {'geometry':<30} {'commit ns':>10} {'fold LOW':>9} {'fold HIGH':>10} {'verdict':>22}")
for name, w, rf, rp, a in GEOMS:
    lo, hi = fold_ns(a, "LOW"), fold_ns(a, "HIGH")
    if hi < COMMIT_NS:
        verdict = f"VIRTUALIZE {COMMIT_NS / hi:.1f}-{COMMIT_NS / lo:.1f}x"
    elif lo > COMMIT_NS:
        verdict = f"COMMIT {hi / COMMIT_NS:.1f}-{lo / COMMIT_NS:.1f}x"
    else:
        verdict = "STRADDLES"
    print(f"  {name:<30} {COMMIT_NS:>10.1f} {lo:>9.1f} {hi:>10.1f} {verdict:>22}")

print("""
  ⚑ THE CROSSOVER IN alpha.  Folding beats committing while""")
for model in ("LOW", "HIGH"):
    best = [a for a in (3, 5, 7, 11) if fold_ns(a, model) < COMMIT_NS]
    print(f"    {model:<5} model: alpha <= {max(best) if best else '(none)'}"
          f"   [d=alpha+1 <= {max(best) + 1 if best else '-'}]")
print("""
  So the deployed alpha=7 is on the WRONG side of the measured crossover and
  KoalaBear's alpha=3 is on the right side -- but by 1.5-2.5x, not 4-15x.

  ⚑ THE CROSSOVER IN LAYERS.  The threshold rule reads: virtualize a value while
  the number of sumcheck layers it participates in is below""")
for name, w, rf, rp, a in GEOMS:
    lo, hi = fold_ns(a, "LOW"), fold_ns(a, "HIGH")
    print(f"    {name:<30} {COMMIT_NS / hi:>5.2f} - {COMMIT_NS / lo:>5.2f} layers")
print("""
  A Poseidon2 round-chain value participates in ONE layer, so at alpha=7 the
  budget (0.4-0.8 layers) is spent before the first one.  This is the same rule
  the verdict note states; what moved is the exchange rate it is evaluated at.
""")

print("=" * 78)
print("3.  WHAT LANDS")
print("=" * 78)
print(f"""
  Arm B, in Lean, at the deployed geometry:
     chip aux span  352 -> {8 * 16 + 13}      (CHIP_WIDTH 386 -> {33 + 8 * 16 + 13 + 1})
     constraints    352 -> {8 * 16 + 13}
     field ops/row  2,316 -> 2,105 (Rust arm currency)
     MEASURED prover 2.11x at 2^16 permutations, verifier 1.28x, proof 1.25x
  Arm C is not indicated at alpha=7 on this box.  Revisit it at alpha=3, at a
  higher blowup, or on hardware where hashing does not vectorize as well.
""")
