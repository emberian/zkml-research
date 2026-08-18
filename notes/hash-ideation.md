# Hash ideation — eight constructions from first principles, two gated

2026-08-18. IDEATION lane. Charter: **generate genuinely distinct compression/permutation
designs for our setting** — not iterate Weft (see `notes/weft-coset-repair.md`, referenced
not re-derived), not react to a paper. Five or more constructions, honest obstructions,
cheap gate on the top two. A candidate killed in an hour by an exact computation is a
success for this lane.

**Setting, taken as given from the briefs (not re-derived here):** the leaf sponge is
92.03% of Merkle-tree permutations and Merkle-commit ~51% of prove; arity is a null knob
and leaf RATE is the live one (w24 rate-16 = ×0.777 native); BCS makes the tree hash the
random oracle itself, so algebraic/linear tree nodes are CLOSED and "collision resistance
suffices" is refuted — design for RO-likeness; in-circuit baseline Poseidon2 ≈ 300
cells/compression (BabyBear; 164 at KoalaBear per `hash-verdict.md` §5), native it loses
5.82× to Keccak; crossover R\* = 1.74–2.75×; FRI floors every trace at 128 rows, so cell
wins compound at the wrap/tower layer, not at small leaves. Gate order: structure /
quotient / subfield / minpoly, **branch fifth**.

Labels: `[MEASURED]` = script + log in this lane; `[DERIVED]` = pencil derivation shown or
cited; `[READ]` = file/paper at source; `[ASSUMED]` = mine, unverified — every round-count
and cost figure in §2's sketches is an *estimate for ranking*, not a measurement, and is
labeled so.

---

## 0. THE THROUGH-LINE FOUND WHILE IDEATING — three claims the eight sketches keep hitting

1. **Cells-per-S-box and the attacker's model degree are the same object.** The
   in-circuit price of an S-box *is* the degree of its cheapest implicit representation
   (x⁷ → a deg-7 chain of committed cells; 1/x → the deg-2 relation xy = 1). But the
   attacker's Gröbner model is built from exactly that cheapest implicit representation.
   Jarvis/Friday died of this precisely (`[READ]` Albrecht et al. 2019: inversion +
   sparse affine, modeled by its own quadric constraints). **Every cell you save hands
   the algebraic attacker a lower-degree model.** The counterweight cannot be "more
   rounds by feel"; it has to be a computed property of the *solving* cost, which is
   claim 3.
2. **Margin is the price of non-computability — and margin is the only currency that
   clears the fixed-cost floor.** Given FRI's 128-row floor, a hash win compounds at the
   wrap/tower, where the unit is *rounds in the verifier's constraint set*. Deployed
   designs carry round margin sized to their UNCOMPUTED legs (Poseidon2's margins are
   sized against attack families nobody can enumerate). A design whose bounds are exact
   computations can ship at bound + small margin. **"Computable security" monetizes as
   round-count, and round-count is the one currency the floor does not eat.**
3. **A concrete new gate item falls out of direction 1** (proposed, not yet built): the
   **regular-sequence check**. For a candidate's CICO system, take the top-degree
   homogeneous parts of the round equations and *compute* whether they form a regular
   sequence (equivalently: the top-parts share only the trivial projective zero — a
   rank/elimination computation at our sizes). If YES, the Hilbert series is the
   complete-intersection one, the Macaulay bound is exact, and **the F5 cost is a
   computed number, not a hope**. If NO, the failure certificate *is* the freelunch
   surface — you have computed where the dedicated attack enters. Either answer is
   information; today's gate has no item that touches the Gröbner leg at all.

---

## 1. THE EIGHT, IN ONE TABLE

Weaving names, per house convention (Weft, Twill, Selvage are taken by siblings).

| # | name | one line | attacks which cost | win lands where | expected killer |
|---|---|---|---|---|---|
| 1 | **WARP** | capacity moves into the key schedule: MMO/MD leaf chaining over a width-16 AO cipher | datapath width of the 92% leaf bucket | native (51% Merkle-commit) AND per-query circuit | related-key security of AO ciphers: unstudied |
| 2 | **JACQUARD** | 3×3×3 cube SPN; axis-rotating 3-lane MDS; wide-trail THEOREM | round-count certainty; rate 18 | wrap layer (cells) | its own tensor structure = the 2026/306 shape — gate decides |
| 3 | **BOBBIN** | full-width inversion S-layer, Montgomery-batched natively | S-box cells (cheapest possible: deg-2 relation) | both, if it survives | the Jarvis precedent; the 0-point |
| 4 | **HEDDLE** | companion-matrix linear layer, irreducible charpoly: every gate item a THEOREM; exact trail DP | margin (claim 2) | wrap only | diffusion latency × full-S-box cost |
| 5 | **TWINE** | χ over F_p: quadratic, whole-width, exact DDT/Fourier by rank computation | native shape (SIMD/GPU) + exact statistical ledger | native leaf side | the p-ary degree wall: deg-2 rounds pay ×log₂p rounds |
| 6 | **CLEAVE** | two primitives by ROLE: grind vs per-query tree | the profile mismatch (dir. 4) | grind: native, now; leaf: blocked | leaf half killed by the BCS-extraction theorem itself |
| 7 | **FULLING** | SPN with PROVEN k-wise-independence ε(R), computed from DDT + branch | statistical margin → zero | wrap (rounds) | closes the leg that was already cheap at 31 bits |
| 8 | **BROADLOOM** | wide-and-shallow α⁻¹ (Rescue-shape, w48, R≈4) | circuit cells per absorbed lane | wrap only | native α-th-root cost lands on the 51% — inverted profile |

---

## 2. THE CONSTRUCTIONS

### 2.1 WARP — capacity in the key schedule ⭐ (directions 3 + 5)

**The accounting observation this rides.** A sponge pays its capacity in DATAPATH WIDTH
on every call, forever: w24 = rate 16 + capacity 8, so every permutation is 50% wider
than the data it absorbs. A block-cipher compression in MMO shape,
`h' = E_h(m) + m`, moves the chaining/capacity into the **key port**: the datapath is
only as wide as the message block. Nothing about the sponge theorem requires the
capacity to ride in the permuted state — that is a *mode* decision we inherited.

**Construction sketch.**
- **Cipher**: width-16 AO SPN over the deployed field (Poseidon2-like rounds; S-box and
  round counts to be set by the gate + classical tooling), keyed by an 8-lane key
  through a **linear** schedule: round key `k_r = W^r·h` for a fixed 8×8 invertible `W`
  (companion of an irreducible octic, so the schedule itself has no invariant
  subspaces), injected via a fixed 16×8 expansion `E`.
- **Leaf absorber** (the 92% bucket): MD/HAIFA chain `h_{i+1} = E_{h_i}(m_i) + m_i`,
  16-lane message blocks, 8-lane chaining value. Absorbs 16 lanes per **width-16** call
  where the sponge absorbs 16 per width-24 call.
- **Node compression** (the ~8%): `h = E_{left}(right) + right` at 8-lane block width,
  or Hirose double-block if the single-block bound is too thin.
- **Tree mode**: standard Merkle with domain separation; leaf finalization includes
  length + position.

**Cost attacked, and where the win lands.** Same absorbed lanes per call, ~2/3 the
width. `[ASSUMED]` if AO round cost scales ~linearly in t at fixed round count, a
width-16 call + linear schedule ≈ 0.7–0.8× a width-24 call in BOTH currencies → a
1.25–1.4× win on the 92% bucket. Native half lands directly on Merkle-commit (51% of
prove, real time, not floored); circuit half lands on the per-query leaf re-execution at
the wrap, where wins compound. This is the only idea on the page that attacks the leaf
bucket's *width* rather than its round count — and it **stacks with** the already-banked
×0.777 rate lever instead of replacing it.

**Security rests on**: PGV/MMO collision-preimage bounds in the ideal-cipher model; tree
indifferentiability results for 2-to-1 compressions (Dodis et al. line); BCS extraction
still runs on oracle *queries* — an ideal-cipher query is a query, so the extractor
story plausibly survives, **but that is `[ASSUMED]` and must be checked against the
actual BCS extractor, and `hash-verdict.md` §6's "mode is free" explicitly does NOT
cover this** — `SpongeIndiff` is parametric over the permutation, not over the mode. A
new mode proof in Lean is real work and is priced in, per the greenfield doctrine.

**Gate: computable vs assertable.** Computable: all five items on the datapath layer;
all five on the **compound** [datapath | schedule] map — and see §3.2: the gate fires on
the compound *by construction*, and the firing is the related-key surface rendered in
our own vocabulary. Computable-with-effort: related-key trail bounds (MILP over the
compound — the sibling Feistel-tooling lane's CLAASP encoding reaches this shape).
Assertable only: the ideal-cipher gap; chosen-key/known-key distinguishers.

**Expected killer, named.** The key input is ADVERSARIAL twice over (chaining values are
attacker-influenced; at the first block the key is the IV but every later key is derived
from attacker data). So the cipher needs related-key and chosen-key resistance — and
**no AO design has a related-key analysis**; they are all analyzed as fixed-constant
permutations. A linear key schedule is exactly the shape classical related-key
differentials eat. This is a real research mortgage, but it is a *classical, computable*
one — the best-tooled open question on this page, not the worst.

### 2.2 JACQUARD — the 3×3×3 cube, a wide-trail THEOREM, and an enumerable invariant lattice (directions 1 + 2 + 6)

**Construction sketch.** t = 27 lanes indexed by (i,j,k) ∈ {0,1,2}³. Round: lane-wise
power S-box (x⁷ BabyBear / x³ KoalaBear); MixColumns by a fixed 3×3 MDS `A` along one
axis; **axis rotation** ρ: (i,j,k) → (j,k,i) — a pure wiring permutation, 0 cells, 0
native ops (this is the `packEquiv` cube-reindex borrow: a proven bijection used as the
diffusion permutation). One round's linear layer is `M = P_ρ·(I₉ ⊗ A)`; the rotation
makes consecutive rounds mix along different axes, AES-style. All rounds full;
`[ASSUMED]` R ≈ 6–8.

**Cost attacked.** Round-count *certainty* (claim 2) plus rate: c = 9 lanes (≥ 2·128
bits at 31-bit lanes), rate 18 vs 16. Cells `[ASSUMED]`: 27 S-boxes × ~2 cells (deg-7,
committed intermediate) × 8 rounds ≈ 432 → cells/absorbed-lane 24 vs Poseidon2-BB's
18.75 — **loses at 8 rounds, parity at 6**; at KoalaBear deg-3 inline, 27×8 = 216 vs
164 — same story. Jacquard does not win on raw cells; its case is that its statistical
round count is a THEOREM (below), so its margin can be thin where Poseidon2's must be
fat — the claim-2 currency. Native `[ASSUMED]`: ~parity (structured 3×3 mixing ≈ 2
mults/lane/round).

**Security rests on**: the AES 4-round propagation theorem transplanted to the cube —
any 4-round trail has ≥ B² = 16 active S-boxes, **a theorem consuming only branch(A) =
4**, not a search; at DDT(x⁷) ≤ 6/p `[DERIVED]` that is ~2^{-454} per 4 rounds.
Algebraic legs: degree 7^R, standard — assertable beyond symbolic round 3.

**Gate: computable vs assertable.** Everything in the gate is computable here, and
cheaply — M is explicit and 27-wide. Extra, direction-1 credit: the invariant-subspace
lattice of the *linear* layer is finite and enumerable (the algebra generated by M is
small; its isotypic decomposition is a computation). **And the same enumeration is the
expected killer**: `I₉ ⊗ A` composed with a lane permutation is literally the
`P_{t/4} ⊗ M₄` shape 2026/306 attacked, and `weft-coset-repair.md` §1c's lesson is that
fiber/coset-aligned point structure yields block-constant invariant flags that branch
numbers cannot see. Prediction registered before running: **with an equal-rowsum
(circulant) A the fiber-constant dim-9 spaces form a ρ-cycled invariant family and the
trail scan stalls; with an unequal-rowsum (Cauchy) A the hull should escape — whether
anything ELSE stalls is what the run is for.** Outcome (§3.1): the circ form died
HARDER than predicted (a dim-2 collapse, minpoly 10 — root cause `A = I + J`, the
cheapest possible MDS); the Cauchy form passed the trail scan clean but carries a
**robust minpoly 24/27 defect the attempted repair did not fix**.

### 2.3 BOBBIN — the batched-inversion layer, priced honestly against its own precedent (direction 5 + claim 1)

**Construction sketch.** t = 24; S-layer: lane-wise `x ↦ x^{p−2}` (inversion with
0 ↦ 0); dense MDS; full rounds only; `[ASSUMED]` R ≈ 6–8 (inversion reaches maximal
degree in one round, both directions, so interpolation dies immediately; statistical:
DDT(1/x) ≤ 4/p).

**The native trick nobody prices.** A full LAYER of 24 inversions Montgomery-batches:
3(t−1) mults + ONE inversion ≈ 69 + ~30 ≈ 100 mults/layer ≈ **4.2 mults/lane — the same
as x⁷'s 4** `[DERIVED]`. The classical objection to inversion S-boxes (native
exponentiation) evaporates *for full layers* — batching needs many independent
inversions per call, which is exactly what a full-width layer provides. In-circuit it is
the cheapest S-box that exists: `y·x² = x ∧ x·y² = y` (two deg-3 constraints handling
the 0-point) ≈ 1–2 cells vs x⁷'s ~2.

**Cost attacked**: S-box cells AND native S-box cost simultaneously — the only S-box on
the page that is simultaneously optimal in both currencies. `[ASSUMED]` 6 rounds × 24 ×
1.5 ≈ 216 cells; native 6×(100 + MDS) ≈ parity or better.

**Security rests on**: claim 1, adversely — this is the construction the Jarvis
precedent is ABOUT. The deg-2 implicit form that makes it cheap is the attacker's model.
The repair hypothesis (dense MDS + enough rounds defeats the equation-chaining that
killed Jarvis's sparse affine layer) is exactly an asserted-not-computed Gröbner claim —
**unless the §0 claim-3 regular-sequence check is built**: Bobbin's CICO ideal is
generated by QUADRICS, the single best-understood case in commutative algebra; if the
top-parts are a regular sequence, the Hilbert series and the F5 cost are exact numbers.
**Bobbin is the natural first customer of the proposed gate item, and should not be
built before it.**

**Gate: computable vs assertable.** Standard five: computable (dense MDS: expected
clean, hence uninformative — the action is all in the algebraic leg the gate does not
yet have). The 0-point: `[ASSUMED]` capacity-lane domain arguments are exactly the kind
of unproven reachability claim our instruments exist to refuse; the two-constraint
encoding above removes the assumption at ~2× S-box cell cost, and THAT price must be
quoted, not the 1-cell fantasy.

### 2.4 HEDDLE — every gate item a theorem: the ledger testbed (direction 1, taken literally)

**Construction sketch.** t = 24; linear layer `M = C_f`, the companion matrix of a
monic irreducible degree-24 `f` over F_p with all coefficients nonzero; full S-box layer
(x⁷); constants. Native: the layer is 23 moves + one dense row = 24 mults/round.

**Why: the gate becomes a theorem list.** `f` irreducible ⇒ F_p^24 is a simple
F_p[M]-module ⇒ **M has NO invariant subspaces at all** — not just coordinate ones, ALL
of them (structure item: 0, by theorem); M^T likewise (quotient item: 0, by theorem —
plus the support digraph is strongly connected since the last column is full); minpoly =
f, degree 24, and **every nonzero vector is cyclic**, so per-lane observability is 24/24
(minpoly item: by theorem); no block-constant trail can stall FOREVER (an infinite
stall is a proper invariant subspace, which does not exist) — ⚠ but see §3.3: at the
scan's default 6-round horizon Heddle shows 206/372 "stalls" anyway, because a
horizon-bounded scan cannot tell *invariant* from *not yet arrived*, and Heddle's
diffusion diameter is 24. At horizon 26 the count is 0/372, as the theorem requires.
That mismatch is a genuine tooling finding, minted in §3.5. Branch(M) = 2 — last, per
the amended gate, and here is a design that leans on that amendment completely: its
statistical story is not branch but the **exact trail ledger** — the companion's
sparsity makes difference propagation nearly deterministic (a difference not touching
the feedback tap simply shifts), so min-active-S-boxes(R) is exact rather than bounded
by ⌊R/2⌋·B: min-active(R) = R for R ≤ 24 `[DERIVED: ≥ R since the S-layer is bijective
so a nonzero difference stays nonzero every round; ≤ R by the lone-lane shift]`,
`[MEASURED]` §3.3: `M^r·e₀ = e_r` for r ≤ 23 confirmed on the concrete instance, and
the tap then detonates weight 1 → 24 in one round (full-support feedback column).

**What the ledger honestly shows, and the named killer.** The exact ledger says the
statistical legs close at ~5 rounds (R actives × 2^{-28.4}) — consistent with the
charter's "statistical is nearly free at 31 bits" — and thereby shows the binding
constraint is DIFFUSION: a lone difference takes up to 23 rounds to reach the tap, so
R ≥ ~26–30 with full S-box layers ≈ 1250–1450 cells `[ASSUMED]` — **4–5× Poseidon2.
Dead as a deployable leaf hash.** A block-companion variant (companion over 4×4 MDS
blocks: 6-round diffusion, block-activity DP still exact at 2⁶ states) is the repair
direction and lands ~500–600 cells — still 1.7–2× over baseline. Heddle's value is as
the **method testbed**: the design whose entire gate is theorems + one exact DP, i.e.
the existence proof that "the security argument is a computation" is achievable — at a
cost the claim-2 margin thesis must then beat, and at these numbers does not.

### 2.5 TWINE — χ over F_p: the exact-spectrum quadratic (directions 1 + 2)

**Construction sketch.** t = 24; nonlinear layer `y_i = x_i + x_{i+1}·x_{i+2}` (Keccak's
χ transplanted to F_p); a NON-circulant dense linear layer; asymmetric constants.
Whole-width nonlinearity at 1 mult/lane/round, algebraic degree exactly 2 per round.

**Direction-1 credit — the strongest exact ledger on the page.** For quadratic maps,
EVERY differential transition probability is exactly `p^{−rank}` of an affine system —
the DDT is a rank function, computed not sampled; linear correlations are Gauss sums
with `|corr| = p^{−rank/2}` exactly. Trail weights are integers from linear algebra; a
transfer-matrix trail count is in principle exact.

**Costs and the named killer.** Deg-2 rounds must commit every round: 24 cells/round.
The p-ary degree wall: total degree 2^R needs R ≥ ~32 just to saturate one lane's
univariate degree, `[ASSUMED]` R ≈ 40+ with margin → ~960 cells, R ≈ 3.2× Poseidon2 —
**outside R\* = 1.74–2.75, so the circuit side loses outright**. Native: ~960 mults but
in a perfectly SIMD/GPU shape (uniform local ops — the same shape that makes Keccak
5.82× us), so the native side might approach parity-or-better on vector hardware —
the win, if any, lands on Merkle-commit native time only. Second obstruction:
**invertibility of χ_p is not inherited from char 2** (χ is bijective on F₂ⁿ iff n odd;
over F_p this must be checked) — `[MEASURED]` §3.4: **χ_p is NOT a bijection for ANY
tested (p, t)** — brute force at t ∈ {3,4,5}, p ∈ {3,5,7,11,13}, 15/15 non-bijective,
odd t included. That kills the permutation-sponge instantiation
outright; a Feistel/MMO wrapping could rescue the χ idea (feed-forward tolerates
non-bijectivity) at mode cost — at which point it competes inside WARP's frame, not as a
sponge. Third: shift-invariance gives rotation-symmetric structure (the constant-vector
diagonal is a nonlinear invariant of χ∘circulant) — constants and a non-circulant layer
must carry the symmetry-breaking, and that is checkable but adds nothing to the cost
case. **Ranked low; the exact-spectrum idea survives as a tool** (quadratic layers are
where exact trail ledgers are easiest) even though this instantiation dies.

### 2.6 CLEAVE — split by role: grind vs per-query (direction 4)

**The observation.** The tree hash is verified in-circuit PER QUERY; grinding is
verified ONCE. One primitive currently serves both profiles. Splitting by role:

- **CLEAVE-grind, actionable now, zero cryptanalytic novelty**: move proof-of-work
  grinding to Blake3. Native 5.82× on the grind loop; in-circuit the grind check is
  verified once per proof (~9,168 cells once — noise at wrap scale). No RO-tree
  implication: grinding is not the BCS tree. `[ASSUMED: that our grind hash is currently
  the algebraic one — VERIFY in code before acting; if it already is Blake3/Keccak this
  row is a no-op.]`
- **CLEAVE-leaf, and its kill, stated honestly**: the tempting half is to stop
  re-executing the leaf sponge in-circuit (the dominant per-query term) by binding
  opened leaf values to already-committed columns with LogUp — our proved machinery —
  leaving only path nodes algebraic. **This dies by the charter's own theorem**: BCS
  straightline extraction runs off oracle QUERIES, and a LogUp binding generates none —
  the same line that closed linear tree nodes closes argument-bound leaves. Reviving it
  means replacing BCS extraction itself — a protocol-layer change, out of scope, and
  the kill is recorded so the next ideation lane does not re-derive it.

### 2.7 FULLING — proven k-wise independence over F_p (direction 1, proof-artifact flavor)

**Construction sketch.** t = 24 SPN (x³ at KoalaBear + MDS), rounds set by a PROVEN
pairwise/t-wise-independence bound in the Liu–Tessaro–Vaikuntanathan line (Crypto'21,
AES-shaped; `[READ]`-level familiarity, not re-verified here), transplanted to F_p: the
amplification lemma consumes exactly two computed quantities — S-box max differential
probability (2/p for x³, exact) and branch (theorem for MDS) — and outputs ε(R), a
computed curve dominating EVERY statistical attack at once.

**Why it fits our shop and why it is ranked low anyway.** We are the differentiator that
computes what designers assert, and a mechanized LTV-style bound in Lean over the
deployed field would be a first — the permutation-level companion to `SpongeIndiff`.
But: (a) known amplification constants are brutal (AES-shape needed ~3× production
rounds for the proven 2^{-128}) → outside R\*; (b) pairwise independence bounds the
STATISTICAL legs, which at 31-bit lanes were already the cheap ones; the algebraic legs
— the ones that actually bind AO designs — are untouched. Fulling polishes the cheap
half. Its residual value is claim-2: an exact statistical theorem lets that margin go to
zero and be re-spent on algebraic margin.

### 2.8 BROADLOOM — wide-and-shallow α⁻¹, and why its profile is inverted (direction 2)

**Construction sketch.** w = 48 (rate 39, c = 9), Rescue-Prime shape: x³ layer, MDS,
x^{1/3} layer, R ≈ 4. The α⁻¹ trick kills interpolation in 2 rounds; wide state buys
few rounds; every constraint deg-3 via the inverse-witness encoding.

**Cells** `[ASSUMED]`: 2×48×4 = 384 cells / 39 lanes ≈ 9.8 cells/absorbed-lane vs
Poseidon2-KB's 10.25 — parity, and better if R = 3 clears. **Native, and the kill**: the
x^{1/3} layer is a fixed-exponent ~45-mult exponentiation per lane with NO batching
trick (Montgomery batching inverts, it does not take cube roots), ≈ 2.9× native LOSS
landing on the 51% Merkle-commit share — the measured Rescue disaster (1660 ms vs 100.9,
`fast-systems-recon.md`) is this, and width does not fix it. Broadloom's honest slot is
as the PER-QUERY-ONLY primitive inside a CLEAVE-style split — and CLEAVE-leaf is dead
(§2.6), so Broadloom has no host. Recorded as: right shape for a cost profile our
protocol does not currently expose. Also: at w48 a dense MDS is native-expensive, and
the structured (⊗-form) alternatives are the 2026/306 shape again — the gate would have
to clear whatever layer is chosen.

---

## 3. THE CHEAP GATE, RUN — top two (WARP §3.2, JACQUARD §3.1), plus two free riders

Script: `~/src/ring-ro-hash/ideation_gate.py` (new, this lane; mirrors
`weft_coset_repair.py`'s gate semantics — closed-set structure/quotient enumeration,
block-constant hull trails, minpoly/observability, exact small-weight branch — ported to
F_p = BabyBear 2013265921). Log: `ideation-gate-run.log` beside it (main run 367 s +
two follow-up blocks). Everything in this section is `[MEASURED]` unless labeled.

### 3.1 JACQUARD — the circ instantiation KILLED in 3.5 minutes; the Cauchy one flagged

Prediction registered in §2.2 before the run; outcome sharper than the prediction.

| gate item (amended order) | A = circ(2,1,1) | A = Cauchy(0,1,2;3,4,5) | Cauchy #2 (0,1,2;4,7,9) |
|---|---|---|---|
| 1 structure (closed sets) | NONE | NONE | — |
| 2 quotient (autonomous) | NONE | NONE | — |
| **2b bc-trails** (457 starts incl. all 27 fibers) | ⚑ **457/457 STALL at dim 2** — held at horizon 12 | **0/457** | 0/457 |
| 3 subfield | vacuous over prime F_p (analogue: entry mult-orders, nothing small) | same | — |
| **4 minpoly / observability** | ⚑ **10/27; 27/27 lanes defective, worst 8** | ⚑ **24/27; 27/27 defective, worst 24** | ⚑ **24/27 — ROBUST across instances** |
| 5 branch | 4 exact | 4 exact | 4 |

**The circ kill, diagnosed to root cause.** `circ(2,1,1) = I + J` (J = all-ones) — the
*cheapest possible* 3×3 MDS (adds only). `A·v = v + (Σv)·1`, so signatures coarsen
instead of separating: every low-weight and every fiber start collapses into a **dim-2
block-constant invariant structure** (`M·1 = 4·1` confirmed), inside which every
lane-wise S-box and the whole linear layer commute for any number of rounds — round
constants are the only escape, the exact 2026/306 posture. And `deg(minpoly) = 10` with
every lane defective. **Branch (4, exact, item 5) and the closed-set items (clean) were
completely blind to all of it** — the amended gate's ordering earns its keep again.
⚑ **Minted: the cheapest MDS is the most structured.** Cost-optimizing the local mixer
walked directly into the attacked shape; anyone picking the "obvious" adds-only 3×3
would ship this.

**The Cauchy escape, and its flag.** Distinct rowsums kill the fiber family: 0/457
stalls, branch 4 exact, closed sets none. But `deg(minpoly) = 24 < 27` with all lanes'
observability capped at 24 — and it is **structural, not instance luck**: a second
Cauchy (different points) gives the identical 24/27, and a **fixed-point-free twisted
rotation ρ′: (i,j,k) → (j,k,i+1)** — the natural repair, killing the cube diagonal's 3
fixed lanes — **changes nothing** (24/27, all defective). So the 3-dim spectral deficit
is baked into the `P·(I₉ ⊗ A)` architecture itself, not into the choice of A or ρ. This
is `weft-coset-repair.md` §1c's law surfacing in a prime field: **the tensor structure
that makes the layer cheap forces a spectral degeneracy its MDS-ness cannot see.**
Diagnosis of the exact 3-dim factor: NOT done here — named as `[JACQ-minpoly]`, the
obligation any adoption must discharge first.

### 3.2 WARP — the gate fires by construction, and the firing IS the related-key surface

Compound `C = [[M16, M16·E],[0, W]]` (dense random invertible M16 as MDS stand-in; W =
companion of an irreducible octic; E = lane-doubling injection):

| item | result | translation |
|---|---|---|
| 1 structure | ⚑ proper closed set, size **16** | the datapath block is an invariant subspace of the compound |
| 2 quotient | ⚑ autonomous quotient, size **8** | **the key schedule runs itself — the definition of a cipher, rendered as a gate flag** |
| 2b bc-trails | ⚑ 206/372 stall at dim 16 (every state-side start; infinite stall, block-triangular by construction) | state-side differences never touch the schedule |
| 4 minpoly | 24/24, but 8 lanes defective at dim 8 | the schedule lanes observe only themselves |
| 5 branch | 17 at the compound (dense stand-in; uninformative) | branch is blind to all of the above, as usual |

**The reading, and it is the honest structural price of the whole idea.** These flags
are not defects to fix — *fixing* the autonomous quotient means feeding state back into
the key register, which rebuilds a width-24 permutation, i.e. the sponge we were
leaving. ⚑ **Conservation law, minted: the capacity you evict from the datapath
reappears as an autonomous quotient in the compound.** A sponge pays capacity in WIDTH
on every call; a cipher-mode compression pays it in a STRUCTURAL flag that the
ideal-cipher model — and a related-key analysis nobody has done for AO designs — must
answer for. The gate cannot certify Warp the way it certifies a permutation; what it
CAN do is name exactly what must be argued by other means (related-key trails over this
exact compound — a shape the sibling Feistel lane's CLAASP encoding reaches). That is
the correct division of labor, computed rather than asserted.

### 3.3 HEDDLE — theorems confirmed, ledger confirmed, and the scan's blind spot found

All four theorem items confirmed by computation on a concrete irreducible f (found by
search, all coefficients nonzero): structure NONE, quotient NONE, minpoly 24/24,
observability 24/24 at every lane, branch 2. Ledger: `M^r·e₀ = e_r` for r ≤ 23
confirmed; the tap detonates weight 1 → 24 in one round. So min-active(R) = R exactly
for R ≤ 24 (§2.4), the statistical legs close at ~5 rounds — and the ledger thereby
*proves* the binding constraint is diffusion (R ≥ ~26 with full S-layers ≈ 4–5×
Poseidon2 cells). Heddle is cost-dead and method-alive, as §2.4 already concluded.

**The blind spot** (promoted to §3.5): at the default 6-round horizon the trail scan
reported **206/372 stalls** on a design that PROVABLY has no invariant subspace of any
kind. They were lone-lane shifts that had not yet reached the tap. Horizon 26 — past
the diffusion diameter — gives **0/372**.

### 3.4 TWINE — the sponge instantiation killed by brute force

χ_p (`y_i = x_i + x_{i+1}x_{i+2}`, cyclic): **non-bijective for all 15 tested (p, t)**,
t ∈ {3,4,5} × p ∈ {3,5,7,11,13}, odd t included — the char-2 "bijective iff n odd"
theorem does NOT transplant. No permutation, no sponge. The exact-spectrum idea (§2.5)
survives only as a component inside feed-forward modes, where it competes under WARP's
frame and WARP's obstructions.

### 3.5 ⚑ Tooling amendment, paid for by this run: THE TRAIL SCAN'S VERDICT IS HORIZON-RELATIVE

A horizon-R hull trail cannot distinguish *invariant* from *not yet arrived*: it
reports both as "stall". Dense layers (Weft coset, Jacquard) reach full dim in ≤ 2
rounds, so horizon 6 was always silently sufficient — until the first SPARSE candidate
(Heddle, diffusion diameter 24) produced 206 false stalls, on a design where the true
count is 0 **by theorem**. Rule for the gate, from here on: **run the scan at horizon ≥
the layer's diffusion diameter (support-digraph eccentricity bound, itself computable),
or the report is unlabeled noise** — and symmetrically, a *true* stall claim quoted
from a short-horizon run (Jacquard-circ) should be re-held at a doubled horizon, as
done in §3.1. `weft_coset_repair.py`'s 6-round default is CORRECT for the dense layers
it was built for and must not be silently reused on sparse ones.

---

## 4. RANKED SHORTLIST — with obstructions named

1. **WARP** (§2.1, gated §3.2). The only candidate attacking the 92% leaf bucket's
   WIDTH; stacks with the banked rate lever; wins land native (51% Merkle-commit) AND
   per-query at the wrap. Obstructions, in order: **related-key security of AO ciphers
   — unstudied anywhere** (but classical and computable-with-effort: MILP over the
   §3.2 compound); the mode-indifferentiability proof is real new Lean work
   (`SpongeIndiff` does not cover it); BCS-extractor compatibility of ideal-cipher
   queries `[ASSUMED, must be checked at source]`. Next cheap step: a related-key
   trail bound on a toy-width instance via the Feistel lane's CLAASP tooling.
2. **JACQUARD-Cauchy** (§2.2, gated §3.1). Passed structure/quotient/trails/branch;
   wide-trail THEOREM for its statistical legs; rate 18. Obstructions: ⚑
   `[JACQ-minpoly]` — a robust 3-dim spectral deficit that survived the
   fixed-point-free repair, undiagnosed; cost parity-at-best vs Poseidon2 (its case is
   claim-2 margin-thinning, not raw cells); all-full-rounds. The circ variant is DEAD
   and banked as a gate demonstration.
3. **BOBBIN** (§2.3). Cheapest S-box in both currencies (batched inversion ≈ 4.2
   native mults/lane + a deg-2/3 relation in-circuit). Obstructions: the Jarvis
   precedent IS this design's threat model (claim 1); the 0-point costs the honest 2×
   encoding; **blocked-by-design on building §0 claim 3's regular-sequence gate item
   first** — Bobbin is its first customer, not before.
4. **CLEAVE-grind** (§2.6). Not a primitive — a systems split; actionable now at zero
   cryptanalytic risk IF the grind hash is currently algebraic (`[ASSUMED]` — verify
   in code first). CLEAVE-leaf is dead by the charter's own BCS-extraction theorem,
   recorded so nobody re-derives it.
5. **HEDDLE** (§2.4, gated §3.3). Cost-dead (4–5× cells), method-alive: the existence
   proof that a design's ENTIRE gate can be theorems + one exact ledger, and the run
   that found the scan's horizon blind spot. Keep as the direction-1 testbed.
6. **FULLING** (§2.7). A mechanized k-wise-independence bound would be a first and
   fits our differentiator, but it closes the legs that were already cheap at 31 bits;
   value is margin-reallocation only.
7. **TWINE** (§2.5, killed §3.4). χ_p is not a permutation — measured, 15/15. The
   exact-quadratic-spectrum LEDGER idea outlives the instantiation.
8. **BROADLOOM** (§2.8). Inverted cost profile (native α-root on the 51%); its only
   host (a per-query-only slot) died with CLEAVE-leaf. Recorded, shelved.

**What this lane hands the gate itself** — arguably worth more than any candidate:
(a) the §3.5 horizon rule; (b) the §0 claim-3 **regular-sequence check** as a proposed
sixth item — the first gate item that would touch the Gröbner leg, with Bobbin as its
first customer; (c) two minted one-liners with measurements behind them: *the cheapest
MDS is the most structured* (§3.1) and *evicted capacity reappears as an autonomous
quotient* (§3.2).

## 5. Reproduce

```bash
cd ~/src/ring-ro-hash && python3 ideation_gate.py   # ~6 min, BabyBear, seed fixed
# follow-up blocks (horizons, Cauchy#2, fixed-point-free rho') appended in
# ideation-gate-run.log by the same lane; see the log for exact invocations
```
