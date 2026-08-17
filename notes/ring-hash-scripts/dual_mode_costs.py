# ring-hash-dual-mode.md section 4 arithmetic. Pure counts on stated protocol shapes;
# currency = R_q constraint rows per the ring-hash cost table (Feistel 27.4/absorbed ring
# element, sigma-Poseidon tau=2 107.8, tau=4 89.8, baseline 716.8). Counts, not clocks.
from math import log2

base_total, per_elt_base = 2417127, 716.8
ring_elts = base_total / per_elt_base
print(f"transcript ring elements/step = {ring_elts:.1f}")
for name, per in [("sigma-P tau=2", 107.8), ("sigma-P tau=4", 89.8), ("Feistel", 27.4)]:
    print(f"  FS bill {name}: {ring_elts*per:,.0f} rows")

# Shape F: folding-style opening (LatticeFold/1127-native), verifier in-circuit.
kappa, K = 24, 4    # kappa: MSIS-rank SKETCH (root-Hermite, NOT an estimator run); K planes
for nu in (17, 19, 20):
    arith = 3*nu + kappa*nu + 2*nu + kappa*K   # sumcheck checks + C folds + value folds + terminal
    absorb = nu*(kappa+3)                       # per round: kappa fresh commit elts + 3 sumcheck coeffs
    for hname, per in [("Feistel", 27.4), ("sigma-P t2", 107.8)]:
        print(f"ShapeF nu={nu} {hname}: arith={arith}  absorb={absorb} elts  "
              f"total {arith+absorb*per:,.0f} .. {arith+2*absorb*per:,.0f} rows (norm-control x1..x2)")

# Shape G: Greyhound+LaBRADOR — proof absorption term (50KB proof, ring elt = 16*8 bytes).
elts = 50*1024/(16*8)
print(f"ShapeG proof absorb: {elts:,.0f} ring elts -> Feistel {elts*27.4:,.0f} rows, "
      f"sigma-P t2 {elts*107.8:,.0f} rows (+ tensor/IP ~0.9k + LaBRADOR arith c_L*O(sqrt N), c_L unmeasured)")

# Cross-substrate refusal-with-arithmetic vs the wrap's Horner chains.
horner = 216330
print(f"Horner: {horner:,} ext4 MACs x ~10 base mults = {horner*10:,.0f} BabyBear-mult-equiv")
for rows in (15000, 28000):
    for bm, tag in [(100, "CRT-slot best case"), (1024, "schoolbook worst case")]:
        print(f"  ShapeF {rows:,} rows x {bm}/row = {rows*bm:,.0f} ({tag}): ratio {rows*bm/(horner*10):.1f}x")

# Commit-instead-of-absorb break-evens (Feistel).
for O in (14000, 28000):
    t = kappa + O/27.4
    print(f"one-shot break-even: n_r > {t:,.0f} ring elts = {t*16:,.0f} Z_q values (opening {O:,} rows)")
print(f"amortized break-even: n_r > kappa = {kappa} ring elts = {kappa*16} Z_q values")

q = 2**64 - 257
print(f"q=2^64-257: gamma/q = 2^{log2(257/q):.1f}; per-element ambiguity ~16*gamma/q = 2^{log2(16*257/q):.1f}")
