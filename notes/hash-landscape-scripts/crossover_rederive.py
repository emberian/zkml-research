#!/usr/bin/env python3
"""E5 RE-DERIVED at current shares (2026-08-18).

Re-runs `crossover.py`'s model with f_circ swept over the four SHARE POINTS that
`docs/VERDICTS.md` Sec.5e names, instead of only the 0.3645 the original was
computed at.

THE MODEL IS UNCHANGED. Only f_circ moves. Every other input is the same committed
measurement crossover.py cites.

  m_leaf = (1 - f_nat) + f_nat/rho_nat          [leaf prove multiplier on the swap]
  c      = (1 - f_circ) + f_circ*R              [wrap CELL multiplier on the swap]
  R*     = (1/m_leaf - 1 + f_circ) / f_circ     [break-even: net win iff R < R*]

Rewrite R* to see the dependence on f_circ directly:

  R* = 1 + (1/m_leaf - 1) / f_circ

=> R* is strictly DECREASING in f_circ, and asymptotes DOWN to 1 as f_circ -> 1.
   Raising the in-circuit hash share LOWERS the bar a candidate hash must beat.
   (The numerator 1/m_leaf - 1 is the NATIVE-side gain, untouched by f_circ; the
   denominator f_circ is the IN-CIRCUIT penalty exposure, which is what grew.)

And the free-hash (Amdahl, R=0) value is 1/(1-f_circ), which RISES.

BOTH ARE THE SAME ARITHMETIC. Raising f_circ raises the payoff of a FREE hash and
raises the penalty of an EXPENSIVE one. It is a LEVERAGE increase, not a direction.
"""

RHO_NAT = 100.9 / 36.3  # 2.7796  notes/fast-systems-recon.md

# f_nat estimators -- IDENTICAL to crossover.py, unchanged by this lane.
X = {3: 177.7, 4: 149.4, 5: 135.0, 6: 127.7, 7: 124.0}  # field-op-counts.md Sec.5
Y_FLOOR = 890.0
work_share = {b: Y_FLOOR / (Y_FLOOR + x) for b, x in X.items()}
clock_b6_hash = 43.71
clock_b6_arith = 7.710 + 12.925 + 3.545 + 1.283 + 0.246
clock_share_b6 = clock_b6_hash / (clock_b6_hash + clock_b6_arith)
clock_share_b3_post = 1.224 / (1.0 + 1.224)

ESTIMATORS = [
    ("work b=3", work_share[3]),
    ("work b=6", work_share[6]),
    ("work b=7", work_share[7]),
    ("clock b=6 pow=0", clock_share_b6),
    ("clock b=3 post-LDE", clock_share_b3_post),
]

# THE SHARE POINTS -- each with its PROVENANCE and DEPLOYMENT STATE.
SHARE_POINTS = [
    (0.3645, "pre-split leaf wrap",
     "MEASURED, recursion-tower-profile.md Sec.3c -- the point E5 was decided at. "
     "SUPERSEDED: the reduced-opening split is in the deployed pin."),
    (0.5236, "a4/K2 + reduced-opening split == DEPLOYED TODAY",
     "MEASURED. plonky3-recursion 834a3f7 'group matrices and reverse-horner chain' "
     "is an ancestor of the pinned rev fc3c6df (breadstuffs Cargo.toml:370-373). "
     "Grid row 'a4/K2 (deployed)' reads 52.4%."),
    (0.733, "a4/K16/rec4 packing",
     "MEASURED + PROVEN (k16_wrap_proves..., breadstuffs a8e8842a5/44d0dea45), "
     "NOT DEPLOYED -- VK rotation pending (73f8dc7d -> 6fdd7b64)."),
    (0.81, "dedicated chain table",
     "DERIVED ONLY (galois-levers.md Sec.3d). Requires a NEW AIR that does not exist "
     "and must be Lean-authored per house law."),
]

# R measured, from hash-landscape.md Sec.1a (prime) and Sec.1d (binary, eprint 2025/1893 Table 4).
R_CANDIDATES = [
    ("Blake3", "BabyBear prime", 30.6),
    ("Keccak-f", "BabyBear prime", 210.6),
    ("Keccak-f", "binary (verify proxy)", 12.7),
    ("Grostl-P", "binary (verify proxy)", 24.7),
    ("lookup-arithmetized", "either", 3.2),
]


def m_leaf(f_nat):
    return (1.0 - f_nat) + f_nat / RHO_NAT


def R_star(f_nat, f_circ):
    return (1.0 / m_leaf(f_nat) - 1.0 + f_circ) / f_circ


def free_hash(f_circ):
    """Amdahl value of a FREE in-circuit hash (R=0) on wrap CELLS."""
    return 1.0 / (1.0 - f_circ)


print("=" * 96)
print("E5 RE-DERIVED -- R* as a function of the in-circuit hash share f_circ")
print(f"rho_nat = {RHO_NAT:.4f}   (model and every other input UNCHANGED from crossover.py)")
print("=" * 96)

print(f"\n{'f_circ':>8}  {'free-hash (R=0)':>16}  {'R* band (leaf wrap)':>24}   provenance")
print("-" * 96)
bands = {}
for fc, label, prov in SHARE_POINTS:
    rs = [R_star(f, fc) for _, f in ESTIMATORS]
    bands[fc] = (min(rs), max(rs))
    print(f"{fc:>8.4f}  {free_hash(fc):>15.2f}x  {min(rs):>10.2f}x - {max(rs):<10.2f}x   {label}")

print("\n" + "=" * 96)
print("PER-ESTIMATOR DETAIL")
print("=" * 96)
hdr = f"{'estimator':<20}{'m_leaf':>9}{'leaf spd':>10}"
for fc, _, _ in SHARE_POINTS:
    hdr += f"{'R*@' + format(fc, '.3f'):>12}"
print(hdr)
for name, f in ESTIMATORS:
    row = f"{name:<20}{m_leaf(f):>9.4f}{1/m_leaf(f):>9.2f}x"
    for fc, _, _ in SHARE_POINTS:
        row += f"{R_star(f, fc):>11.2f}x"
    print(row)

print("\n" + "=" * 96)
print("WHERE REALITY SITS -- margin ABOVE R* (>1 means the swap LOSES)")
print("=" * 96)
hdr = f"{'candidate':<34}{'R':>8}"
for fc, _, _ in SHARE_POINTS:
    hdr += f"{'@' + format(fc, '.3f'):>16}"
print(hdr)
for nm, fld, R in R_CANDIDATES:
    row = f"{nm + ' (' + fld + ')':<34}{R:>8.1f}"
    for fc, _, _ in SHARE_POINTS:
        lo, hi = bands[fc]
        row += f"{format(R/hi, '.1f') + '-' + format(R/lo, '.1f') + 'x':>16}"
    print(row)

print("\n" + "=" * 96)
print("THE WRAP MULTIPLIER c*m_leaf -- what the swap ACTUALLY does to a wrap (>1 = worse)")
print("(work b=6 estimator; c = (1-f_circ) + f_circ*R)")
print("=" * 96)
f6 = work_share[6]
ml6 = m_leaf(f6)
hdr = f"{'candidate':<34}{'R':>8}"
for fc, _, _ in SHARE_POINTS:
    hdr += f"{'@' + format(fc, '.3f'):>13}"
print(hdr)
for nm, fld, R in R_CANDIDATES:
    row = f"{nm + ' (' + fld + ')':<34}{R:>8.1f}"
    for fc, _, _ in SHARE_POINTS:
        c = (1 - fc) + fc * R
        row += f"{c * ml6:>12.2f}x"
    print(row)

print("\n" + "=" * 96)
print("SANITY: reproduce the COMMITTED figures crossover.py / LEAF-VS-RECURSION printed")
print("=" * 96)
checks = [
    ("R* work b=6 @0.3645 == 4.49", R_star(work_share[6], 0.3645), 4.49),
    ("R* work b=3 @0.3645 == 4.14", R_star(work_share[3], 0.3645), 4.14),
    ("R* clock b=6 @0.3645 == 2.85", R_star(clock_share_b6, 0.3645), 2.85),
    ("R* clock b=3 @0.3645 == 2.49", R_star(clock_share_b3_post, 0.3645), 2.49),
    ("free hash @0.3645 == 1.57", free_hash(0.3645), 1.57),
    ("free hash @0.5236 == 2.10", free_hash(0.5236), 2.10),
]
ok = True
for label, got, want in checks:
    good = abs(got - want) < 0.006
    ok &= good
    print(f"  [{'OK ' if good else 'RED'}] {label:<36} got {got:.4f}")
print(f"\n{'ALL CONTROLS REPRODUCE' if ok else 'A CONTROL FAILED -- DO NOT TRUST THE TABLE ABOVE'}")

print("\n" + "=" * 96)
print("FREE-HASH CEILING vs the SHARE it was quoted at")
print("=" * 96)
for fc, label, _ in SHARE_POINTS:
    print(f"  f_circ={fc:.4f} ({label:<44}) -> free hash worth {free_hash(fc):.2f}x")
print("\nVERDICTS.md Sec.5e quotes '~x5'. That is the 0.81 DERIVED row.")
print("The MEASURED-and-proven row (0.733) gives x3.75. The DEPLOYED row (0.5236) gives x2.10.")

print("\n" + "=" * 96)
print("ABSOLUTE CELLS -- the mechanism, with no shares at all")
print("(grid rows, galois-levers.md Sec.3c; p2 cells = wrap_cells * p2_share)")
print("=" * 96)
GRID = [("a4/K2 DEPLOYED", 40_554_496, 0.524), ("a4/K16/rec4", 28_971_008, 0.733)]
for nm, cells, sh in GRID:
    print(f"  {nm:<16} wrap {cells:>12,}  p2 {int(cells*sh):>12,}  non-p2 {int(cells*(1-sh)):>12,}")
print("\n  => the p2 half is CONSTANT (~21.2M): the retune deleted ARITHMETIC, not hashing.")
print("     So swapping in a traditional hash adds the SAME absolute cells either way,")
print("     while the baseline it is measured against shrank. Hence R* falls.\n")
hdr = f"  {'candidate':<30}{'R':>7}{'pre-retune':>15}{'post-retune':>14}{'retune worth':>14}"
print(hdr)
for nm, fld, R in R_CANDIDATES:
    tot = []
    for _, cells, sh in GRID:
        p2, other = cells * sh, cells * (1 - sh)
        tot.append(other + p2 * R)
    print(f"  {nm + ' ' + fld[:9]:<30}{R:>7.1f}{tot[0]/1e6:>13.1f}M{tot[1]/1e6:>13.1f}M{tot[0]/tot[1]:>13.3f}x")
b = [GRID[0][1], GRID[1][1]]
print(f"  {'Poseidon2 (i.e. no swap)':<30}{1.0:>7.1f}{b[0]/1e6:>13.1f}M{b[1]/1e6:>13.1f}M{b[0]/b[1]:>13.3f}x")
print("\n  ==> THE PACKING RETUNE IS WORTH x1.400 WITH POSEIDON2 AND ~x1.0 WITH A TRADITIONAL HASH.")
print("      The optimization and the hash swap are MUTUALLY CANNIBALIZING: each one's")
print("      value is the other's absence. We already took the better of the two.")
