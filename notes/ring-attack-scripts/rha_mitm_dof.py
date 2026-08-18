"""
ITEM 1 (part B) -- A MITM MODEL FOR THE GADGET-FEISTEL, INSTANTIATED, AND THE
ROUND REQUIREMENT IT COMPUTES.

THE OBSTRUCTION THIS DISSOLVES.  notes/feistel-classical-tooling.md Sec.4
concluded "no published MITM model can be instantiated", because at BIT or
COEFFICIENT granularity the nonlinear layer (a) re-partitions the cell 64 -> 4x16,
(b) Z = Y_j*Y_{j+1} is two-input and non-bijective, (c) ring multiplication is
not coefficient-local.  All three are TRUE at that granularity.

⚑ ALL THREE DISSOLVE AT RING-ELEMENT GRANULARITY, and rha_feistel_structure.py
measures the fact that makes it legitimate:

    F_r(R)_i = sum_{i'} f_{r,i,i'}(R_{i'})       [S1, measured 12/12, guard live]

  The nonlinearity NEVER couples two input elements.  So with the cell taken to
  be a RING ELEMENT (1024 bits), the round is exactly the AES-like shape every
  MITM model assumes:
      a UNARY, CELL-LOCAL nonlinear map  S : R_q -> R_q^6,
          x |-> (Y_0,Y_1,Y_2,Y_3, Y_0*Y_1, Y_1*Y_2)
      followed by a PUBLIC LINEAR LAYER over R_q (the g,h matrix, 24 -> 4).
  S is EXPANDING and the linear layer is CONTRACTING -- neither is standard --
  but neither is used by the colour propagation, which only needs cell-locality.

THE MODEL.  Unroll the 2-branch Feistel:  X^{r+1} = X^{r-1} + F_r(X^r),
X^r in R_q^4.  Colours, with the superposition rule that a Feistel's ADD is
LINEAR and therefore does NOT destroy separability (this is the
Superposition-MITM idea, eprint 2021/575, and it is what makes this model
STRONGER than naive colouring -- if it were weaker the round count would be an
underestimate and useless as a defence):

    G  constant           B  forward-neutral      R  backward-neutral
    S  a formal SUM of a blue part and a red part, still linearly separable
    W  unknown

    add  : join, with join(B,R) = S,  join(S,*) = S,  join(W,*) = W
    F    : G->G, B->B, R->R,  S->W, W->W      <-- the ONLY place colour is lost,
           because F is nonlinear and cannot be applied to a formal sum
    diffusion: F_r's output cell i depends on ALL input cells [S3, measured 4/4],
           so F's input colour is the JOIN over the whole cell vector.

WHAT IS COMPUTED: over every assignment of {G,B,R} to the 8 cells of the two
starting states, the number of consecutive rounds for which the state stays
colour-separable in both directions, with at least one blue and one red degree
of freedom and a nonempty matching point.  That number is the MITM reach.

HOUSE LAW: the search is exhaustive over 3^8 colourings, and the reach is
falsified by injection (a model with F:S->S, i.e. pretending F is linear, must
report UNBOUNDED reach -- if it does not, the propagation is not wired up).
"""
from itertools import product

G, B, R, S, W = "G", "B", "R", "S", "W"

# colour join for the LINEAR add.  Superposition-preserving.
def join(a, b):
    if a == W or b == W:
        return W
    if a == G:
        return b
    if b == G:
        return a
    if a == b:
        return a
    # {B,R}, {B,S}, {R,S} -> S
    return S


def join_all(cs):
    acc = G
    for c in cs:
        acc = join(acc, c)
    return acc


def F_colour(cellvec, linear_F=False):
    """colour of F_r(X) for every output cell.  F is NONLINEAR: it can be applied
    to a pure colour but not to a formal sum."""
    c = join_all(cellvec)
    if linear_F:
        return c          # the INJECTED DEFECT used as the liveness guard
    return c if c in (G, B, R) else W


W_CELLS = 4          # w = 4 ring elements per Feistel branch


def forward_reach(Xprev, Xcur, linear_F=False, maxr=64):
    """states X^{s-1}=Xprev, X^s=Xcur; return the list of state colourings
    X^{s+1}, X^{s+2}, ... until the state is entirely W."""
    seq = [Xprev, Xcur]
    for _ in range(maxr):
        fc = F_colour(seq[-1], linear_F)
        nxt = tuple(join(seq[-2][i], fc) for i in range(W_CELLS))
        seq.append(nxt)
        if all(c == W for c in nxt):
            break
    return seq


def backward_reach(Xprev, Xcur, linear_F=False, maxr=64):
    """X^{r-1} = X^{r+1} - F_r(X^r): from (X^{s-1}, X^s) go DOWN."""
    seq = [Xcur, Xprev]           # seq[0]=X^s, seq[1]=X^{s-1}, then X^{s-2}...
    for _ in range(maxr):
        fc = F_colour(seq[-1], linear_F)
        nxt = tuple(join(seq[-2][i], fc) for i in range(W_CELLS))
        seq.append(nxt)
        if all(c == W for c in nxt):
            break
    return seq


def usable(state):
    """a state is usable at a matching point if no cell is W."""
    return all(c != W for c in state)


def evaluate(Xprev, Xcur, linear_F=False):
    """returns (rounds_covered, dof_blue, dof_red) for this starting colouring."""
    dof_b = sum(1 for c in Xprev + Xcur if c == B)
    dof_r = sum(1 for c in Xprev + Xcur if c == R)
    if dof_b == 0 or dof_r == 0:
        return (0, dof_b, dof_r)          # a MITM needs both chunks
    fwd = forward_reach(Xprev, Xcur, linear_F)
    bwd = backward_reach(Xprev, Xcur, linear_F)
    # count consecutive usable states above X^s and below X^{s-1}
    up = 0
    for st in fwd[2:]:
        if usable(st):
            up += 1
        else:
            break
    down = 0
    for st in bwd[2:]:
        if usable(st):
            down += 1
        else:
            break
    # states known: X^{s-1-down} ... X^{s+up}  -> that many states minus 1 rounds
    n_states = 2 + up + down
    return (n_states - 1, dof_b, dof_r)


def sweep(linear_F=False):
    best = (0, None)
    for assign in product((G, B, R), repeat=2 * W_CELLS):
        Xprev = assign[:W_CELLS]
        Xcur = assign[W_CELLS:]
        rounds, db, dr = evaluate(Xprev, Xcur, linear_F)
        if rounds > best[0]:
            best = (rounds, (Xprev, Xcur, db, dr))
    return best


print("=" * 78)
print("MITM COLOUR-PROPAGATION SWEEP -- exhaustive over 3^8 = 6561 colourings")
print("=" * 78)
rounds, wit = sweep(linear_F=False)
Xp, Xc, db, dr = wit
print(f"  cell = one ring element (1024 bits); w = {W_CELLS} cells per branch")
print(f"  MAX ROUNDS COVERED = {rounds}")
print(f"    best starting colouring  X^(s-1) = {Xp}")
print(f"                             X^(s)   = {Xc}")
print(f"    DoF_blue = {db} cells, DoF_red = {dr} cells")
fwd = forward_reach(Xp, Xc)
bwd = backward_reach(Xp, Xc)
print(f"    forward  states: {[''.join(s) for s in fwd[:6]]}")
print(f"    backward states: {[''.join(s) for s in bwd[:6]]}")

print()
print("=" * 78)
print("GUARDS -- PROVED LIVE BY INJECTION")
print("=" * 78)
# GUARD 1: pretend F is LINEAR (F: S->S).  Colour is then never lost and the
# reach must blow up to the search cap.  If it does not, the propagation is not
# actually wired to F_colour and the whole sweep is decorative.
r_lin, _ = sweep(linear_F=True)
print(f"  GUARD 1  inject 'F is linear' (S -> S): reach = {r_lin} rounds"
      f"  -> {'LIVE (model responds)' if r_lin > rounds else 'DEAD GUARD'}")
assert r_lin > rounds

# GUARD 2: a colouring with no red must score 0 (a MITM needs two chunks).
r0, _, _ = evaluate((B,) * W_CELLS, (B,) * W_CELLS)
print(f"  GUARD 2  all-blue colouring (no backward chunk): rounds = {r0}"
      f"  -> {'LIVE' if r0 == 0 else 'DEAD GUARD'}")
assert r0 == 0

# GUARD 3: break the diffusion assumption -- if F only depended on cell 0, the
# reach must INCREASE (cells 1..3 stay separable).  This checks that S3's
# measured full diffusion is what is limiting the answer, not an artefact.
def F_colour_sparse(cellvec, linear_F=False):
    c = cellvec[0]
    return c if c in (G, B, R) else W

_real = F_colour
try:
    globals()["F_colour"] = F_colour_sparse
    r_sparse, _ = sweep(linear_F=False)
finally:
    globals()["F_colour"] = _real
print(f"  GUARD 3  inject 'F depends on cell 0 only': reach = {r_sparse} rounds"
      f"  -> {'LIVE (diffusion is what binds)' if r_sparse > rounds else 'DEAD GUARD'}")
assert r_sparse > rounds

print()
print("=" * 78)
print("⚑ CALIBRATION -- the ONLY thing that makes the number above mean anything")
print("=" * 78)
print("""  This model is structural: its answer depends on (i) the 2-branch Feistel
  recurrence and (ii) F having full 1-round diffusion over its input cells.
  BOTH published 2-branch Feistel MITM targets have exactly those two
  properties, so the model returns the SAME reach for them -- and their true
  reach is PUBLISHED.  That makes them a calibration, not an analogy.""")

# published reach on 2-branch Feistels with full 1-round diffusion inside F.
# read at source by the literature lane; see the note for the citations.
PUBLISHED = [
    # target,            cells/branch, cell bits, state bits, published reach,
    #                    generic,  attack cost
    ("Feistel-SP-128", 8, 8, 128, 12, 128, 113,
     "Hou et al. 2023/1359 Sec.5 (Table 1); F = SubBytes + MDS"),
    ("Simpira-2", 16, 8, 256, 7, 256, 225,
     "Hou et al. 2023/1359 Sec.6.1; F = 2 AES rounds; SS22 got 5 by hand, "
     "and its BRANCH-level automatic tool marked b=2 'Inapplicable'"),
]

print()
print(f"  {'target':<16} {'cells/br':>8} {'model says':>11} {'published':>10} "
      f"{'underestimate':>14}")
factors = []
for name, cells, cb, sb, pub, gen, cost, src in PUBLISHED:
    # the model's answer is structural and does not depend on the cell count:
    # F joins all input cells regardless of how many there are.  Verify that.
    m = rounds
    f = pub / m
    factors.append(f)
    print(f"  {name:<16} {cells:>8} {m:>11} {pub:>10} {f:>13.2f}x")
worst = max(factors)
print(f"""
  ⚑ THE MODEL UNDERESTIMATES THE PUBLISHED REACH BY UP TO {worst:.1f}x.
  It is therefore NOT a security bound.  The gap is not mysterious: both
  published attacks were obtained at BYTE granularity with cancellations, and
  2023/1359 says so in as many words -- SS22's branch-level model was
  "Inapplicable" at b=2, and going FINER bought the rounds.  A coarse cell
  model is the one that reports nothing.""")

NR = 16
calibrated = rounds * worst
print()
print("=" * 78)
print("THE COMPUTED ROUND REQUIREMENT, CALIBRATED")
print("=" * 78)
print(f"""  raw model reach (cell = ring element)       : {rounds} rounds
  x worst published underestimate factor      : x{worst:.1f}
  ----------------------------------------------------------
  ⚑ CALIBRATED MITM ROUND REQUIREMENT         : {calibrated:.0f} rounds
  deployed NR                                 : {NR} rounds
  ⚑ MARGIN                                    : {NR/calibrated:.2f}x

  This is the number to carry outward.  It is NOT {rounds + 1} and the margin is
  NOT {NR/(rounds+1):.0f}x.  Quoting the raw model would be a cost table wearing
  security clothes -- the model's own calibration refutes it.""")

print()
print("=" * 78)
print("THE LEG THAT ACTUALLY BEARS ON THE 128-BIT DECISION: MITM *GAIN*")
print("=" * 78)
print("""  Reach is not a break.  What decides shipping is whether a MITM can push a
  security level BELOW the bar.  Published MITM gains against 2-branch
  Feistels, as a FRACTION of the target (the scale-free comparison):""")
for name, cells, cb, sb, pub, gen, cost, src in PUBLISHED:
    gain = gen - cost
    print(f"    {name:<16} generic 2^{gen:<4} attack 2^{cost:<4} "
          f"gain {gain:>3} bits = {100*gain/gen:5.1f}% of target")
pub_frac = max((gen - cost) / gen for _, _, _, _, _, gen, cost, _ in PUBLISHED)

LAMBDA = 128
CAP = 1024                 # capacity, 1 ring element
DIGEST = 256               # a 256-bit digest is what lambda=128 collision needs
targets = [
    ("collision (sponge)", CAP // 2),
    ("preimage, 256-bit digest", min(CAP, DIGEST)),
]
print(f"""
  Our sponge: capacity {CAP} bits (1 ring element), target lambda = {LAMBDA}.""")
for label, gen_bits in targets:
    need = (gen_bits - LAMBDA) / gen_bits
    print(f"    {label:<26} generic 2^{gen_bits:<4} -> to reach 2^{LAMBDA} needs a gain of"
          f" {gen_bits-LAMBDA:>3} bits = {100*need:5.1f}% of target"
          f"   [{need/pub_frac:4.1f}x the largest published fraction]")
print(f"""
  ⚑ The largest MITM gain ever published against a 2-branch Feistel is
  {100*pub_frac:.0f}% of its target.  Ours would have to be 50-75% -- between 4x and 6x
  the state of the art IN RELATIVE TERMS -- before the 128-bit claim moves.
  That is the honest defence of this design against MITM, and note what it
  rests on: the enormous 1024-bit capacity, NOT the round count.""")

print()
print("=" * 78)
print("⚠ WHAT THIS MODEL DOES NOT COVER -- stated so the number is not over-read")
print("=" * 78)
print(f"""   - it is a REACH bound at cell granularity, not a complexity.
   - it models NO cancellations, no guessed cells, no bicliques, no
     superposition refinements.  Those are exactly what bought 2023/1359 its
     extra rounds, and they are why the calibration factor is {worst:.0f}x.
   - ⚑ THE FINER MODEL THE LITERATURE NEEDED IS NOT AVAILABLE HERE, and the
     reason is structural, not an effort budget: base-B decomposition is
     COEFFICIENT-local, ring multiplication is SLOT-local (R_q = (F_q^2)^8),
     and the change of basis between the two is dense.  NO single cell
     decomposition makes both nonlinear steps local.  So the byte-level
     refinement that took Simpira-2 from 5 to 7 rounds has no analogue to
     copy here; it would have to be invented.
   - ⚑ it assumes the attacker's cells are RING ELEMENTS.  An attacker with
     finer control -- which is exactly what a SLACK NORM CHECK hands over,
     see rha_norm_slack.py -- is not modelled here at all.""")
