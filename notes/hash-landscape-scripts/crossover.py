#!/usr/bin/env python3
"""Hash-swap crossover for the dregg/zkml tower, computed from OUR OWN measurements.

Every input is cited to a committed note. No literature numbers enter the crossover;
literature only supplies the value of R that we then compare against R*.

INPUTS (all ours, all committed)
--------------------------------
rho_nat  = 2.78   Poseidon2/Blake3 native cost, same Merkle commit of 2^15 x 135 BabyBear
                  (Poseidon2 100.9 ms = 22.8 ns/elt; Blake3 36.3 ms = 8.2 ns/elt)
                  -- notes/fast-systems-recon.md
f_nat    = native-hash share of a LEAF prove.  TWO ESTIMATORS, reported as a band:
             work model  : Y/(Y+X), X exact from op counts, Y=890 measured
                           -- notes/field-op-counts.md Sec.5
             clock model : measured per-phase ms, contended box
                           -- docs/COST-MODEL.md Sec.A / Sec.6
f_circ   = in-circuit-hash share of committed cells in a WRAP
             0.3645 leaf wrap, 0.5398 apex/shrink -- notes/recursion-tower-profile.md Sec.3c
R        = (in-circuit cost of candidate hash) / (in-circuit cost of Poseidon2), same workload.
           THIS is the unknown the literature must supply.

MODEL
-----
Swapping Poseidon2 -> H multiplies:
  a LEAF prove by     m_leaf = (1 - f_nat) + f_nat / rho_nat
  a WRAP's cells by   c      = (1 - f_circ) + f_circ * R
  and the WRAP's time by     m_wrap = c * m_leaf
    (a wrap is itself a STARK: its cost tracks its committed cells, and it hashes
     those cells with the SAME native hash, so it collects m_leaf too.)

Net win on a wrap iff c * m_leaf < 1, i.e.

  R  <  R*  =  ( 1/m_leaf - 1 + f_circ ) / f_circ

STATED INADEQUACIES (labelled, not hidden)
  - wrap arithmetic is taken proportional to cells; the DFT is cells*log h, so R* is
    mildly optimistic for the swap at large R. Low-resolution by intent.
  - rho_nat is a contended-box clock ratio; both sides equally contended, and it is a
    RATIO of two hash workloads, the pair least corrupted by contention.
  - table heights are padded to powers of two, so real in-circuit cost is a STAIRCASE
    in R, not a line. See headroom() below.
"""

RHO_NAT = 100.9 / 36.3          # 2.7796...  notes/fast-systems-recon.md

# --- f_nat, work model: hash-bound iff Y > X; hash share = Y/(Y+X) ---
X = {3: 177.7, 4: 149.4, 5: 135.0, 6: 127.7, 7: 124.0}   # field-op-counts.md Sec.5
Y_FLOOR = 890.0                                           # 16 MB working set, the conservative end
work_share = {b: Y_FLOOR / (Y_FLOOR + x) for b, x in X.items()}

# --- f_nat, clock model ---
# b=6, q=19, pow=0, per-phase minima, docs/COST-MODEL.md Sec.A + field-op-counts Sec.6
clock_b6_hash  = 43.71                                   # Merkle-commit + FRI-fold Merkle
clock_b6_arith = 7.710 + 12.925 + 3.545 + 1.283 + 0.246  # LDE commit, LDE q-eval, open, q-eval, lookup
clock_share_b6 = clock_b6_hash / (clock_b6_hash + clock_b6_arith)
# b=3, AFTER the landed LDE-layout fix: COST-MODEL.md records hash/arith 0.902 -> 1.224
clock_share_b3_post = 1.224 / (1.0 + 1.224)

F_CIRC = {"leaf wrap": 0.3645, "apex / shrink": 0.5398}

def m_leaf(f_nat, rho=RHO_NAT):
    return (1.0 - f_nat) + f_nat / rho

def R_star(f_nat, f_circ, rho=RHO_NAT):
    return (1.0 / m_leaf(f_nat, rho) - 1.0 + f_circ) / f_circ

def show(label, f_nat):
    ml = m_leaf(f_nat)
    print(f"\n{label}")
    print(f"  f_nat = {f_nat:.4f}   -> leaf prove multiplier m_leaf = {ml:.4f}"
          f"   (leaf gets {1/ml:.2f}x FASTER on the swap alone)")
    for name, fc in F_CIRC.items():
        rs = R_star(f_nat, fc)
        print(f"  {name:16s} f_circ={fc:.4f}  ->  R* = {rs:.2f}x")

print("=" * 78)
print("CROSSOVER R*: the in-circuit cost ratio at which swapping Poseidon2 -> Blake3")
print("stops paying for itself, computed from our own measurements.")
print(f"rho_nat (Poseidon2 native / Blake3 native) = {RHO_NAT:.4f}")
print("=" * 78)

print("\n--- WORK MODEL (op counts x measured Y; contention-immune counts) ---")
for b in (3, 6, 7):
    show(f"b = {b}   [work model, X={X[b]}, Y={Y_FLOOR:.0f}]", work_share[b])

print("\n--- CLOCK MODEL (measured per-phase ms, contended box; the conservative end) ---")
show("b = 6, pow=0  [clock, pre-LDE-fix phase table]", clock_share_b6)
show("b = 3, post-LDE-layout-fix  [clock, hash/arith = 1.224]", clock_share_b3_post)

# --- the full band ---
alls = []
for f in list(work_share.values()) + [clock_share_b6, clock_share_b3_post]:
    for fc in F_CIRC.values():
        alls.append(R_star(f, fc))
print("\n" + "=" * 78)
print(f"R* BAND ACROSS EVERY ESTIMATOR AND LAYER:  {min(alls):.2f}x  ..  {max(alls):.2f}x")
print("=" * 78)

# --- leaf-only (no recursion) case: no f_circ at all ---
print("\nLEAF-ONLY / TOP-OF-TOWER (nothing wraps it, so R is irrelevant):")
for lbl, f in (("work, b=6", work_share[6]), ("work, b=3", work_share[3]),
               ("clock, b=6", clock_share_b6), ("clock, b=3 post-fix", clock_share_b3_post)):
    print(f"  {lbl:22s} speedup = {1/m_leaf(f):.2f}x   (free: no in-circuit cost at all)")

# --- power-of-two staircase ---
print("\nSTAIRCASE (rows are padded to powers of two, so small R is FREE):")
perms_leaf, perms_apex = 38168, 22626
for nm, p in (("leaf wrap", perms_leaf), ("apex/shrink", perms_apex)):
    import math
    pad = 1 << math.ceil(math.log2(p))
    print(f"  {nm:12s} {p:,} rows -> padded 2^{int(math.log2(pad))} = {pad:,}"
          f"   headroom {pad/p:.3f}x in ROWS before the table costs one more rung")


# ============================================================================
# R, MEASURED -- from our OWN pinned Plonky3 (rev 82cfad7), not quoted.
# Widths are `size_of::<*Cols<u8>>()` read out of the pinned crates; rows per
# invocation read from each crate's generation.rs.
#   blake3-air : num_rows = inputs.len()                -> 1 row / compression
#   keccak-air : num_rows = inputs.len() * NUM_ROUNDS   -> 24 rows / permutation
# Poseidon2 side is OUR deployed tower table, notes/recursion-tower-profile.md 3a.
# ALL THREE ARE AIR MAIN CELLS OVER A 31-BIT PRIME FIELD -- one unit, no conversion.
# ============================================================================
P2_MAIN_COLS = 300          # poseidon2_perm/baby_bear_d4_w16, main width, 1 row/perm
BLAKE3_COLS  = 9168         # NUM_BLAKE3_COLS, 1 row/compression
KECCAK_COLS  = 2633         # NUM_KECCAK_COLS
KECCAK_ROWS  = 24           # NUM_ROUNDS

print("\n" + "=" * 78)
print("R, MEASURED IN A PRIME FIELD (AIR main cells per invocation, pinned p3 82cfad7)")
print("=" * 78)
cands = {
    "Poseidon2-w16 (ours, deployed)": P2_MAIN_COLS,
    "Blake3 (p3-blake3-air)": BLAKE3_COLS,
    "Keccak-f (p3-keccak-air)": KECCAK_COLS * KECCAK_ROWS,
}
for nm, c in cands.items():
    print(f"  {nm:34s} {c:>8,} cells/invocation   R = {c/P2_MAIN_COLS:7.1f}x")

print("\n  Merkle NODE ratio is 1:1 in invocations (a 2-to-1 node is one Poseidon2-w16")
print("  perm OR one Blake3 compression at a 256-bit digest), so the cell ratio IS R")
print("  for the recursion column, which is Merkle-path dominated.")
print("  Bulk ABSORB credits Blake3 2x (64 B/compression vs a rate-8 ~31 B), so an")
print("  absorb-heavy workload sees R/2.")

print("\n" + "=" * 78)
print("VERDICT: measured R against the crossover band")
print("=" * 78)
band_lo, band_hi = min(alls), max(alls)
for nm, c in cands.items():
    if nm.startswith("Poseidon2"):
        continue
    R = c / P2_MAIN_COLS
    print(f"\n  {nm}:  R = {R:.1f}x   vs  R* = {band_lo:.2f}x..{band_hi:.2f}x")
    print(f"    margin above crossover: {R/band_hi:.1f}x (best case for the swap)"
          f" .. {R/band_lo:.1f}x (worst case)")
    print(f"    -> Poseidon2 WINS" if R > band_hi else "    -> candidate wins")

print("\n" + "=" * 78)
print("BINARY FIELD: the same ratio, from the only same-system head-to-head")
print("eprint 2025/1893 Table 4 (Binius v0, Ryzen 9 7900X, per ~1 MB hashed)")
print("VERIFY time is the in-circuit/recursion proxy: recursion cost IS verifier cost.")
print("=" * 78)
bin_verify_ms = {
    "Grostl-P (standard)": 114.97,
    "Keccak-f (standard)": 45.70,
    "Vision-32b (algebraic)": 10.12,
    "Anemoi (algebraic)": 12.28,
    "Poseidon-b pi (algebraic)": 4.66,
    "Poseidon-b pi n=64 (algebraic)": 3.61,
}
base = bin_verify_ms["Poseidon-b pi n=64 (algebraic)"]
for nm, v in bin_verify_ms.items():
    print(f"  {nm:32s} verify {v:7.2f} ms   R_proxy = {v/base:6.1f}x")
print(f"\n  Grostl / Poseidon-b(n=32) = {114.97/4.66:.1f}x ;"
      f"  Keccak / Poseidon-b(n=64) = {45.70/3.61:.1f}x")
print(f"  -> R_proxy in a BINARY field is ~12.7x..24.7x, STILL ABOVE R* = {band_hi:.1f}x.")
print("  The binary field shrinks R by ~2x (from ~30x for Blake3), it does NOT close it.")
