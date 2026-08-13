# The compositions — best outcome, regardless of origin

2026-08-13. Written after being corrected three times for sorting findings by
provenance. **The question is not what is ours. The question is what is the
best system that can exist, and which combinations get there.** Owning the
full stack — FHE engine, proof system, kernel semantics, Lean emission, and
the machine-checked justification — means we can *join* things that were built
apart. That is the whole advantage, and it is an advantage about combination,
not ownership.

Each entry: the pieces, why joining them beats either half, and what it costs.

---

## C1. Essentially-optimal linear-algebra certificates, made non-interactive and proved

**Pieces**: Dumas–Kaltofen–Villard's certificate catalogue — rank, determinant,
characteristic and minimal polynomial, Frobenius form, PSD, rank profiles, all
with verification linear in input size — **compiled with Fiat–Shamir as a
heuristic**. Plus a machine-checked RBR→FS compiler theorem over an inhabited
oracle. Plus Lean-authored emission.

**Why joining beats either half**: their catalogue is unusable as a deployed
non-interactive argument without an FS transform whose soundness is actually
established; an FS transform with nothing to transform is a lemma. Together:
**a library of essentially-optimal certificates for linear algebra that are
non-interactive with a proved transform and emitted as the object proved
about.** Every one of those primitives is an ML operation.

**Cost**: a port. Their protocols are two-round Σ-protocols; the transform
exists; the emission pipeline exists. **The near-term item.**

---

## C2. Abstraction choice with a cost model and a Lean obligation

**Pieces**: Distiller's provably-safe refinement chain `T_I ≤ T_E ≤ T_S` over
transition systems (obligations to SMT, mechanization explicitly free). Plus
the **measured exchange rate** — 3,120 field mults per committed felt at lb=4,
12,331 at lb=6, ~40 to virtualize one per layer. Plus Lean emission.

**Why joining beats either half**: Distiller can *prove* an abstraction safe
but has no idea which abstraction is *cheap* — its 1.3–50× is found, not
chosen. The exchange rate says which, and the threshold rule says when to stop
(the sweet spot is not zero). Lean makes the obligation a theorem about the
emitted object rather than an SMT query about a model.

**And the joining technology is named**: not e-graphs — they preserve
functional equality, and Freivalds is a *soundness-preserving reduction*, not
an equality. **A rewrite system over relations, ordered by soundness-preserving
reduction, scheduled against measured commitment price.**

**Cost**: real design work, and Allspice (S&P'13) tried protocol selection by
static analysis and the field dropped it — that has to be understood before
claiming a path.

---

## C3. Virtualize the permutation (a live prediction, cheap to test)

**Pieces**: the threshold rule (virtualize while layer count < the 78–308×
exchange rate). Plus Poseidon2 at ~21 layers. Plus a corroborating measurement
already in our tree (`map_write_chip` 227 ms vs `umem_write_read_nochip`
14.9 ms).

**Why it matters**: the permutation is **the most-committed object in the
prover**, and the rule predicts virtualizing beats committing by **4–15×**.

**Cost**: a measurement, not a campaign. **Do this first — it is the cheapest
large number on the board.**

---

## C4. Emit over ℤ, valuate per ring

**Pieces**: semiring provenance (transport commutes with a value-ring change
**iff the map is a homomorphism**; semantics in any K **factors through the
free object**). Plus Kovach–Kjolstad's semiring-parametric compiler proved in
Lean 4 in ~540 lines. Plus Campanelli–Hall-Andersen's author-over-ℤ-reduce-mod-p.
Plus the measured ~3× base→extension cliff.

**Why joining beats either half**: the cliff says the constraint object must be
ring-polymorphic; provenance says *what shape that has* (a syntactic expression
over ℤ-coefficients, each concrete ring a valuation — **not** a
`BabyBear → BabyBear` function); and the Lean-4 precedent says it is ~540
lines, not a research programme. **This settles a design question we were
about to answer by taste.**

**Cost**: a refactor of the emission layer, checkable against
Hierarchy-Builder-style retrofit precedent — a check, not a deadline.

---

## C5. One change that is simultaneously an FHE speedup and a proof simplification

**Pieces**: `fold_add` is linear ⇒ MLE linearity ⇒ **one common-point opening,
zero sumcheck rounds, zero range checks** (ratio = B, 690× at B=512). Plus the
side condition (no reduction during accumulation) being met by **lazy
accumulation, measured at 0.88× — i.e. faster on the FHE side too.**

**Why joining beats either half**: the change the prover wants and the change
the FHE engine wants **are the same change**. That almost never happens.

**Cost**: the multilinear commitment seam, which is C6.

---

## C6. A multilinear opening built on proximity results we already hold

**Pieces**: RS proximity with attained bounds, correlated agreement
(CA ⟹ MCA, domain-general), the BCS alphabet, FS transport. Plus a multilinear
PCS whose soundness composes from those rather than needing a new proximity
result.

**Why it matters**: **this is the gap.** Everything downstream — Jagged, GKR,
zkML matmul, the vFHE vector relations, C5 — waits on it. And the right choice
is the one whose *proof* is closest to a composition of what exists, not the
one that is fastest.

**Cost**: a campaign. The landscape lane is establishing which candidate is
nearest.

---

## C7. Jagged, in Lean

**Pieces**: one commitment for arbitrarily many tables of different heights, no
extra oracles, verifier cost depending only on total log-area — **reducing to a
degree-2 sumcheck (which our engine already proves) plus a width-4,
two-bit-state read-once branching program.** Plus the monotonicity check and
dimension-binding hash, without which it is unsound. Plus the 2^30 area
ceiling, which is our field's, not their design's.

**Why it matters**: it kills the one-recursion-circuit-per-proof-shape
explosion, and the BP is decidable per layer with an induction on top — **the
most tractable large formalization available.** Ceno independently made it
their default.

---

## C8. The economics half of the audit theorem

**Pieces**: `AuditSampling.lean` (detection, `E[Λ] ≤ b/q`). Plus the **rational
proofs** literature — *sitting in our paperbin, cited zero times.* Plus
Randomized Partial Checking as the named instantiation hazard (a deployed
commit-then-audit protocol whose published bound was wrong **because privacy
forced dependent sampling**).

**Why joining beats either half**: detection without economics does not tell
you the sampling rate; economics without a machine-checked detection bound is
an argument. And RPC shows the failure mode is *real and deployed*.

---

## The order

**C3** (a measurement, cheapest large number) → **C4** (settles a design
question before more constraints are written) → **C1** (a port with immediate
ML surface) → **C6** (the gap) → **C7**, **C5** (both wait on C6) → **C2**,
**C8** (research-shaped).
