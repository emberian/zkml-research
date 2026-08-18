"""
ITEM 3 -- DIRECT GROBNER/CICO ON sigma-POSEIDON, UNDER PERRIN'S RULE.

PERRIN'S RULE, CORRECTED AT SOURCE.  The brief relayed it as: "argue from the
elimination step, not from computing the Grobner basis -- the latter is
'sometimes literally non-existent.'"  ⚑ THE PARAPHRASE IS WRONG in the way that
matters.  Read at source (2024/605, Abstract):

  "For algebraic attack relying on the computation and exploitation of a Grobner
   basis, our survey of the literature suggests to base a security argument on
   the complexity of the variable elimination step rather than that of the
   computation of the Grobner basis itself.  Indeed, it turns out that the
   latter complexity is hard to estimate---and is sometimes litteraly
   non-existent."

The antecedent of "the latter" is THE COMPLEXITY, not the basis.  Every ideal
has a Grobner basis.  What can be non-existent is its COST: for a suitable
weighted monomial order the natural modelling ALREADY IS a Grobner basis, so
the GrobFind step costs ZERO (the FreeLunch phenomenon).  The rule therefore
says: NEVER price security on an F4/F5 estimate, because it can evaporate to
nothing.  Price it on the change-of-order / elimination step, whose cost is
governed by the IDEAL DEGREE D_I.

THE COST MODEL, from CheapLunch 2025/2040 (which supplies the formulas Perrin
does not):
    D_I  <=  delta^(k*R_F) * d^(R_P)          [Table 1, Poseidon row; conjectured tight]
    round skipping: D_I /= d^s,  s = floor(t/k) - 2        [Sec.4.2]
    designer-conservative cost (Eq.10, omega=2):  D_I^2 * wt(x_m)/deg(Q_m)
                                                  ~ D_I^2 / d^(R_F)
  d = S-box degree, delta = degree of a full round (= d for Poseidon),
  k = number of FIXED OUTPUT coordinates = CICO-k, t = number of branches,
  R_F/R_P = full/partial rounds.

⚑ THE LIVE GUARD IS THE WHOLE POINT OF THIS SCRIPT.  The formula is reproduced
against ALL FOUR published rows of CheapLunch Table 2 before it is pointed at
anything of ours.  A cost model that cannot reproduce its own source's numbers
is not evidence, and this repo has shipped a guard row asserting a number its
source paper did not contain.  Every row below is checked, and the check is
then fed a deliberately wrong exponent to prove it can go red.
"""
from math import log2

OMEGA_DESIGNER = 2.0


def ideal_degree_log2(d, k, R_F, R_P, t, skip=True):
    """log2 D_I for a Poseidon-shaped permutation, CheapLunch Table 1 + Sec.4.2."""
    e = k * R_F + R_P
    if skip:
        s = max(t // k - 2, 0)
        e -= s
    return e * log2(d)


def designer_cost_log2(d, k, R_F, R_P, t, skip=True):
    """CheapLunch Eq.(10) with omega=2: D_I^2 * wt/deg ~ D_I^2 / d^{R_F}."""
    return OMEGA_DESIGNER * ideal_degree_log2(d, k, R_F, R_P, t, skip) - R_F * log2(d)


# ---------------------------------------------------------------- calibration
# CheapLunch 2025/2040 Table 2, "Comparison with [3] on high security level
# instances".  Column FGLM(10) is the designer-conservative estimate.
TABLE2 = [
    # lambda, d, t, k, R_F, R_P, published FGLM via Eq.(10)
    (1024, 3, 24, 8, 8, 85, 456.47),
    (512, 5, 12, 4, 8, 57, 390.08),
    (384, 7, 9, 3, 8, 47, 370.57),
    (256, 3, 49, 7, 6, 46, 253.59),
]

print("=" * 78)
print("CALIBRATION -- reproduce CheapLunch Table 2 before pointing this anywhere")
print("=" * 78)
print(f"  {'lambda':>6} {'d':>2} {'t':>3} {'k':>2} {'R_F':>4} {'R_P':>4} "
      f"{'published':>10} {'computed':>9} {'delta':>7}")
worst = 0.0
for lam, d, t, k, RF, RP, pub in TABLE2:
    got = designer_cost_log2(d, k, RF, RP, t)
    worst = max(worst, abs(got - pub))
    print(f"  {lam:>6} {d:>2} {t:>3} {k:>2} {RF:>4} {RP:>4} "
          f"{pub:>10.2f} {got:>9.2f} {got-pub:>+7.2f}")
print(f"\n  worst absolute disagreement = {worst:.3f} bits over 4/4 rows")
assert worst < 0.1, "the cost model does not reproduce its own source -- STOP"
print("  -> 4/4 rows reproduced to better than 0.1 bit.  The model is the paper's.")

print()
print("=" * 78)
print("GUARDS -- PROVED LIVE BY INJECTION")
print("=" * 78)


def wrong_no_skip(d, k, RF, RP, t):
    return designer_cost_log2(d, k, RF, RP, t, skip=False)


hits = sum(1 for lam, d, t, k, RF, RP, pub in TABLE2
           if abs(wrong_no_skip(d, k, RF, RP, t) - pub) < 0.1)
print(f"  GUARD A  drop the round-skipping term: rows still matching = {hits}/4"
      f"  -> {'LIVE (refused)' if hits == 0 else 'DEAD GUARD'}")
assert hits == 0

hits2 = sum(1 for lam, d, t, k, RF, RP, pub in TABLE2
            if abs(OMEGA_DESIGNER * ideal_degree_log2(d, k, RF, RP, t) - pub) < 0.1)
print(f"  GUARD B  drop the /d^{{R_F}} factor: rows still matching = {hits2}/4"
      f"  -> {'LIVE (refused)' if hits2 == 0 else 'DEAD GUARD'}")
assert hits2 == 0

# GUARD C: the model must NOT report a break on an instance the same paper
# declares unbroken.  CheapLunch: "we found no attacks on full Poseidon with its
# security margin for realistic security levels (80 <= lambda <= 256)."
SAFE = [("Poseidon-128 t=3 d=5", 5, 3, 1, 8, 56, 128),
        ("Poseidon-128 t=9 d=5", 5, 9, 1, 8, 35, 128)]
false_alarms = 0
for name, d, t, k, RF, RP, lam in SAFE:
    c = designer_cost_log2(d, k, RF, RP, t)
    broke = c < lam
    false_alarms += broke
    print(f"  GUARD C  {name:<22} cost 2^{c:7.1f} vs lambda {lam}"
          f"  -> {'FALSE ALARM' if broke else 'no break, as published'}")
assert false_alarms == 0, "the model reports a break on an instance published as safe"

print()
print("=" * 78)
print("sigma-POSEIDON -- and the answer depends entirely on GRANULARITY")
print("=" * 78)
print("""  Spec of record: /Users/ember/src/ring-ro-hash/sigma_poseidon.py, frog_like()
    q ~ 2^64, d_ring = 16, t = 9 RING ELEMENTS, rate 8, capacity 1 element,
    alpha = 7, R_F = 8, R_P = 22  (the borrowed 30-round budget)
    tau = 2  =>  R_q = (F_{q^2})^8, so 1 ring element = 8 slots = 16 F_q coords

  A Grobner attack is a system OVER A FIELD.  R_q is NOT a field, so the
  granularity is not a modelling taste -- it is a correctness question.""")

ALPHA, RF, RP = 7, 8, 22
LAMBDA = 128

readings = [
    ("(A) ring-element  [INVALID]", 9, 1, 1,
     "t=9 'branches', capacity 1 -> CICO-1.  ILLEGITIMATE: R_q is a product "
     "ring, not a field; one R_q S-box is 8 field equations, not one."),
    ("(B) CRT slot, F_{q^2}", 72, 8, 8,
     "9 elts x 8 slots = 72 branches; capacity 1 elt = 8 slots -> CICO-8; "
     "the partial round S-boxes ONE RING ELEMENT = 8 slots, so n_S = 8."),
    ("(C) F_q coordinate", 144, 16, 8,
     "144 F_q coords; capacity 16 coords -> CICO-16.  This is the granularity "
     "at which the sigma layer (which carries a Frobenius twist at tau=2) is "
     "LINEAR; over F_{q^2} it is only semi-linear."),
]

print(f"  {'reading':<28} {'t':>4} {'k':>3} {'n_S':>4} {'log2 D_I':>9} "
      f"{'cost':>10} {'verdict':>10}")
for label, t, k, nS, why in readings:
    # partial rounds carry n_S S-boxes each, so they contribute d^(n_S*R_P)
    e = k * RF + nS * RP
    s = max(t // k - 2, 0)
    e -= s
    lDI = e * log2(ALPHA)
    cost = OMEGA_DESIGNER * lDI - RF * log2(ALPHA)
    print(f"  {label:<28} {t:>4} {k:>3} {nS:>4} {lDI:>9.1f} "
          f"2^{cost:<9.1f} {'BREAK' if cost < LAMBDA else 'safe':>10}")

print("""
  ⚑ READING (A) IS THE ONLY ONE THAT PRODUCES A SCARY NUMBER, AND IT IS THE
  ONE THAT IS WRONG.  Recorded here precisely because a careless modeller lands
  on it first: it treats the state as 9 branches and the S-box as one degree-7
  equation, when x^7 over R_q is 8 independent degree-7 maps over F_{q^2}.
  Undercounting the S-boxes 8x is what manufactures the break.

  At either legitimate granularity the elimination step is hundreds of bits
  above the bar.""")

print()
print("=" * 78)
print("THE ROUND REQUIREMENT FROM THIS LEG")
print("=" * 78)
t, k, nS = 72, 8, 8
s = max(t // k - 2, 0)
print(f"  at reading (B): how many rounds are needed for cost >= 2^{LAMBDA}?")
found = None
for R in range(1, 40):
    # scale the schedule: R total rounds, all FULL (the attacker-friendly case,
    # since a full round costs the attacker k S-box-degrees and a partial one nS)
    e = max(k * R - s, 1)
    cost = OMEGA_DESIGNER * e * log2(ALPHA) - R * log2(ALPHA)
    if cost >= LAMBDA:
        found = (R, cost)
        break
print(f"    all-full-round schedule : {found[0]} rounds  (cost 2^{found[1]:.1f})")
found2 = None
for R in range(1, 60):
    e = max(nS * R - s, 1)
    cost = OMEGA_DESIGNER * e * log2(ALPHA) - 0
    if cost >= LAMBDA:
        found2 = (R, cost)
        break
print(f"    all-partial-round schedule: {found2[0]} rounds  (cost 2^{found2[1]:.1f})")

INTEGRAL_FLOOR = 24
BUDGET = 30
print(f"""
  ⚑ THE COMPARISON THE BRIEF ASKED FOR:
      Grobner / CICO leg (this script)  :  {max(found[0], found2[0])} rounds
      char-p INTEGRAL floor (measured)  : {INTEGRAL_FLOOR} rounds
      borrowed budget                   : {BUDGET} rounds

  Grobner does NOT reach further than integral.  It is satisfied an order of
  magnitude earlier.  The integral property remains the BINDING algebraic
  constraint on sigma-Poseidon, and the ~{BUDGET - INTEGRAL_FLOOR}-round margin
  over the budget is unchanged by this leg.  The candidate is NOT in the
  trouble the brief flagged as possible.""")

print("""
  ⚠ RESIDUALS, named, because this is a bound and not a proof:
   - D_I <= delta^(k*R_F) * d^(R_P) is CONJECTURED TIGHT by CheapLunch, not
     proven; Perrin's MIDC is likewise a conjecture (CheapLunch Sec.4.1
     validates it in their setting).  A LOWER bound on D_I is what a defence
     needs and neither of these is one.
   - the n_S = 8 extension of the R_P term is MINE, not CheapLunch's; their
     Poseidon row assumes ONE S-box per partial round.  It is the natural
     reading of their XHash8 case (D_I <= alpha^((n_S + 2k)*R)) but it is not
     stated for Poseidon, and it is the single largest lever in the table.
   - ⚑ CheapLunch's whole cost model assumes p is large enough that a single
     coordinate cannot be guessed.  Ours is q ~ 2^64.  Perrin flags exactly
     this for Goldilocks, and FreeLunch ABANDONED its XHash8 attack for it:
     "since the size of one branch is roughly 64 bits, this CICO problem could
     simply be solved by making 2^64 queries."  Any future attack that reduces
     to guessing a SMALL NUMBER of F_q coordinates is cheap for us in a way it
     is not for a 256-bit-prime design.  Live residual, NOT priced above.
   - neither CheapLunch nor FreeLunch says anything about extension fields or
     product-of-fields rings; the nearest precedent (XHash8's F_(p^3) S-box) is
     handled by flattening it back to the prime field, which is reading (C).""")
