/-
# Selvage.Accumulator — the WARP-shape accumulated claim and its γ-fold.

THE HEART of Selvage (docs/SELVAGE-RECOMPOSITION.md §1): the accumulated object
`acc.𝕩 = (rt, α, μ, β, η)` — one word commitment `rt`, one multilinear
evaluation constraint `û(α) = μ`, one bundled circuit constraint
`P̂(β, C⁻¹(f)) = η` — read abstractly as a CONSTRAINED-CODEWORD claim: a word
`f` in ONE fixed linear code `C` together with a channel of (functional,
target) constraints, γ-linear in both slots (WARP 2025/753 Def 5.6/5.7 and
Constr. 10.4; WHIR 2024/1586 multi-constrained CRS — LOOM §6: the same shape,
convergent from two papers). This is the object OB-3's receipt Q becomes
(docs/OB3-RECEIPT-ENCODING.md §1; `Assurance/ReceiptClaim.lean`'s
`[OB3-d-fold]` residual points here) and the ONE object the light client
checks: the accumulator replaces the PCS opening at every chain link, and the
folding PCS appears once, compressing the final accumulator.

The two fold rules, verbatim from the construction reads:

* **Same-word batching (WHIR Constr. 5.5).** `r` constraints `(ŵᵢ, σᵢ)` on ONE
  word fold to one by γ-powers: `ŵ := ∑ᵢ γ^(i-1)·ŵᵢ`, `σ := ∑ᵢ γ^(i-1)·σᵢ`.
  Here: `batch`, with `batchFunctional` and the closed γ-power target sum;
  the batched functional is again a linear functional — a TERM of the
  `LinearMap` module, with `batchFunctional_apply` its evaluation identity.
  Completeness is `batch_satisfies`. The RBR soundness error `(t−1)·ℓ/|F|` is
  `[ACC-sound]` below; its SHAPE is exhibited concretely in the keystones.

* **Cross-word fold (WHIR Constr. 7.4 / WARP's accumulation step).** Words
  combine `g := ∑ γ_{i,j}·f_{i,j}`; targets combine γ-linearly. Here:
  `foldClaims A B γ` — one link's claim meets the running accumulator, the
  folded word is `f + γ • g`, the targets fold `σ + γ·τ`, the recommitment is
  prover-supplied data (`foldRoot`, opaque — WARP recommits the folded word
  every step). Closure `foldClaims_satisfies`: CRS-claim × CRS-claim →
  CRS-claim, with the folded word as the witness — what makes the chain ONE
  accumulated object. Pairwise folds at γ-powers compose to the flat
  γ-combination (`foldClaims_assoc`, `foldClaims_chain_target`), so the
  doubly-indexed `γ_{i,j}` form is reachable by iterating this one operation.

**Transcription notes (read before auditing):**

* **Linearity scope — the channel is the POST-REDUCTION interface.** The
  evaluation constraint `û(α) = μ` IS linear in the word (a multilinear
  extension is linear in the values it extends), and every constraint in
  OB-3's receipt encoding (binding evaluation, per-asset conservation, seam
  equality) is in this Z-linear / linear-Σ-IOP class
  (docs/OB3-RECEIPT-ENCODING.md §1). The bundled circuit constraint
  `P̂(β, C⁻¹(f)) = η` as first stated is NOT linear in the word; WARP's
  per-step sumchecks (the "two sumchecks" of LOOM §1) reduce it to evaluation
  claims BEFORE any fold — what the γ-fold ever touches is a linear channel.
  The sumcheck front lives in `Selvage/Sumcheck.lean`; this file fixes the
  algebra at the interface where the fold actually operates.

* **`σ before γ`** (DeepBrake's message-order law, LOOM §6): the fold
  challenge is a function ARGUMENT here, applied to claims whose targets are
  already fixed — the type discipline mirrors the message order, and no
  separate evaluation-binding obligation accrues.

* **Cross-word completeness needs a shared functional channel** (`hshare` in
  `foldClaims_satisfies`): a functional evaluated on `f + γ • g` splits
  γ-linearly only against ITS OWN values on both words. This is not a model
  weakness but the construction itself: WARP aligns both inputs to a fresh
  common point (in-domain queries re-read as boolean multilinear claims,
  LOOM §1) before folding; same-functional-different-targets is exactly the
  post-alignment state. Same-word batching (`batch`) has no such hypothesis.

* **The root is opaque.** `Root` is an arbitrary type; that `rt` binds the
  word is the commitment layer's obligation, consumed by extraction
  (`[ACC-extract]` below), never by the fold algebra. Consequently
  associativity of `foldClaims` is stated on the channel (where it is a
  theorem) — the root component tracks the prover's recommitment schedule,
  on which the algebra imposes nothing.

* **The proximity ledger** (δ, regime tag, additive RBR error budget — LOOM
  §6's third carried datum) is NOT yet a field of `AccClaim`: its fold rule
  IS the soundness bound `(t−1)ℓ/|F|`, so carrying it before `[ACC-sound]`
  lands would be a number with no theorem attached. It joins the structure
  with `[ACC-sound]`.

* **Sibling reconciliation.** `Selvage/ConstrainedCode.lean` (landed
  concurrently) presents the same channel as weight vectors on List spines —
  the CRS-code side. The bridge section here PROVES the two presentations are
  one algebra (`dotWtL`, `ofConstraints_satisfies_iff`,
  `batch_ofConstraints`); nothing is duplicated, and the exact-word
  Schwartz–Zippel soundness count for Constr 5.5 lives there
  (`card_batch_satisfying_le`), transported by the bridge.
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Selvage.ReedSolomon
import Selvage.ConstrainedCode

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r r₁ r₂ : ℕ}

/-! ## The accumulated claim -/

/-- **The accumulated claim** — WARP's `acc.𝕩 = (rt, α, μ, β, η)`, abstracted
to its constrained-codeword content: an opaque word commitment `rt` plus a
constraint channel of `r` pairs (linear functional, target), γ-linear in both
slots. WARP's shape is the `r = 2` instance (`AccClaim.warp`): the evaluation
constraint `(û(α), μ)` and the bundled circuit constraint `(P̂(β,·), η)`, each
a functional-target pair once the sumcheck front has linearized it (see the
module header's linearity note). The word itself is NOT a field: the claim is
what the light client holds; words are witnesses (`AccClaim.Satisfies`). -/
structure AccClaim (Root : Type*) (F : Type*) [Field F] (ι : Type*) (r : ℕ) where
  /-- The word commitment (Merkle root in WARP; opaque here — binding is the
  commitment layer's obligation, consumed by `[ACC-extract]`). -/
  rt : Root
  /-- The constraint channel: `r` pairs of a linear functional over the code's
  ambient space and a target scalar. -/
  channel : Fin r → ((ι → F) →ₗ[F] F) × F

namespace AccClaim

/-- The functional half of the channel. -/
def weights (A : AccClaim Root F ι r) : Fin r → (ι → F) →ₗ[F] F :=
  fun i => (A.channel i).1

/-- The target half of the channel. -/
def targets (A : AccClaim Root F ι r) : Fin r → F :=
  fun i => (A.channel i).2

@[simp] theorem weights_apply (A : AccClaim Root F ι r) (i : Fin r) :
    A.weights i = (A.channel i).1 := rfl

@[simp] theorem targets_apply (A : AccClaim Root F ι r) (i : Fin r) :
    A.targets i = (A.channel i).2 := rfl

end AccClaim

/-- **Satisfaction** — the strict (honest-decider) relation of LOOM §1's
promise-split: `f` is a word of the fixed code `C` meeting every constraint of
the channel exactly. The δ-slack relaxation lives only in extraction
(`[ACC-extract]`), never here — the strict/relaxed interface is fixed day one
(LOOM §1, [OB-3 restated]). (Namespaced: the sibling `Selvage/ConstrainedCode`
owns the word-level `Satisfies`; this is the claim-level relation, and
`AccClaim.ofConstraints_satisfies_iff` below proves they present the same
content over the RS code.) -/
def AccClaim.Satisfies (C : Submodule F (ι → F)) (A : AccClaim Root F ι r)
    (f : ι → F) : Prop :=
  f ∈ C ∧ ∀ i, A.weights i f = A.targets i

theorem AccClaim.Satisfies.mem {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {f : ι → F} (h : Satisfies C A f) : f ∈ C := h.1

/-! ## The WARP shape: `(rt, α, μ, β, η)` as the two-constraint instance -/

/-- WARP's accumulated claim: commitment `rt`, evaluation constraint
`ev = (û(α)-functional, μ)`, bundled circuit constraint
`circ = (P̂(β,·)-functional, η)` — the `(rt, α, μ, β, η)` tuple with the two
points α, β absorbed into their (post-reduction, linear) functionals. -/
def AccClaim.warp (rt : Root) (ev circ : ((ι → F) →ₗ[F] F) × F) :
    AccClaim Root F ι 2 :=
  ⟨rt, ![ev, circ]⟩

/-- Satisfaction of the WARP shape, unfolded: code membership, `û(α) = μ`,
`P̂(β,·) = η`. -/
theorem AccClaim.warp_satisfies_iff {C : Submodule F (ι → F)} {rt : Root}
    {wα wβ : (ι → F) →ₗ[F] F} {μ η : F} {f : ι → F} :
    AccClaim.Satisfies C (AccClaim.warp rt (wα, μ) (wβ, η)) f ↔
      f ∈ C ∧ wα f = μ ∧ wβ f = η := by
  simp [AccClaim.Satisfies, AccClaim.warp, Fin.forall_fin_two]

/-! ## seqDescr-style constraint accumulation: channels append

A new same-word constraint joining the running claim (a uniqueness pin, a
receipt constraint — "a pin is itself a CRS constraint and folds along",
LOOM §6) is channel concatenation. Satisfaction distributes exactly. -/

/-- Append the constraint channels of two claims about the SAME committed word
(the root is the first claim's — sequential description accumulates onto the
running object). -/
def AccClaim.append (A : AccClaim Root F ι r₁) (B : AccClaim Root F ι r₂) :
    AccClaim Root F ι (r₁ + r₂) :=
  ⟨A.rt, Fin.append A.channel B.channel⟩

/-- Appending channels is exact for satisfaction: a word witnesses the
concatenation iff it witnesses both constituents. -/
theorem AccClaim.append_satisfies_iff {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r₁} {B : AccClaim Root F ι r₂} {f : ι → F} :
    AccClaim.Satisfies C (A.append B) f ↔ AccClaim.Satisfies C A f ∧ AccClaim.Satisfies C B f := by
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨⟨hf, fun i => ?_⟩, hf, fun j => ?_⟩
    · simpa [AccClaim.append, AccClaim.weights, AccClaim.targets,
        Fin.append_left] using hc (Fin.castAdd r₂ i)
    · simpa [AccClaim.append, AccClaim.weights, AccClaim.targets,
        Fin.append_right] using hc (Fin.natAdd r₁ j)
  · rintro ⟨⟨hf, hA⟩, ⟨-, hB⟩⟩
    refine ⟨hf, fun k => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [AccClaim.append, AccClaim.weights, AccClaim.targets,
        Fin.append_left] using hA i
    · simpa [AccClaim.append, AccClaim.weights, AccClaim.targets,
        Fin.append_right] using hB j

/-! ## Same-word γ-batching (WHIR Constr. 5.5) -/

/-- The γ-power combination of `r` functionals, `∑ᵢ γ^i • ŵᵢ` — a TERM of the
`LinearMap` module: the batch of linear functionals is again a linear
functional, by construction in the module structure of `(ι → F) →ₗ[F] F`
(this is the "batching is a linear functional" claim, discharged by the type
plus `batchFunctional_apply`). Index convention: `Fin r` is 0-based, so the
paper's `γ^(i-1)` is `γ^i` here. -/
def batchFunctional (γ : F) (ws : Fin r → (ι → F) →ₗ[F] F) :
    (ι → F) →ₗ[F] F :=
  ∑ i : Fin r, γ ^ i.val • ws i

/-- Evaluation of the batched functional: `(∑ᵢ γ^i • ŵᵢ) f = ∑ᵢ γ^i · ŵᵢ f`. -/
@[simp] theorem batchFunctional_apply (γ : F) (ws : Fin r → (ι → F) →ₗ[F] F)
    (f : ι → F) :
    batchFunctional γ ws f = ∑ i : Fin r, γ ^ i.val * ws i f := by
  simp [batchFunctional, smul_eq_mul]

/-- **WHIR Constr. 5.5** — same-word constraint batching: the `r` constraints
of one claim fold to ONE by γ-powers, `ŵ := ∑ᵢ γ^i·ŵᵢ`, `σ := ∑ᵢ γ^i·σᵢ`.
Word and commitment unchanged. The target sum is the closed γ-power form of
the sibling's Horner-spine `batchTarget` (`Selvage/ConstrainedCode.lean`,
`batchTarget_eq_sum`) — the bridge section proves the correspondence
(`AccClaim.batch_ofConstraints`). RBR soundness error `(t−1)·ℓ/|F|`:
`[ACC-sound]`. -/
def AccClaim.batch (A : AccClaim Root F ι r) (γ : F) : AccClaim Root F ι 1 :=
  ⟨A.rt, fun _ =>
    (batchFunctional γ A.weights, ∑ i : Fin r, γ ^ i.val * A.targets i)⟩

/-- Completeness of same-word batching: a word satisfying every constraint of
the channel satisfies the γ-batch, for EVERY γ. (The converse fails on a small
challenge set — that failure probability is the `(t−1)ℓ/|F|` of `[ACC-sound]`,
and its shape is exhibited in the keystones below.) -/
theorem AccClaim.batch_satisfies {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {f : ι → F} (γ : F) (h : AccClaim.Satisfies C A f) :
    AccClaim.Satisfies C (A.batch γ) f := by
  refine ⟨h.1, fun _ => ?_⟩
  show batchFunctional γ A.weights f = ∑ i : Fin r, γ ^ i.val * A.targets i
  rw [batchFunctional_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [h.2 i]

/-! ## The cross-word γ-fold (WHIR Constr. 7.4 / the accumulation step) -/

section Fold

/- The prover's recommitment schedule: the commitment to the folded word
`f + γ • g` given the constituents' roots and the challenge. Opaque — in WARP
the accumulation prover recommits the folded word each step; binding is the
commitment layer's obligation (`[ACC-extract]`). -/
variable (foldRoot : Root → F → Root → Root)

/-- **The γ-fold at challenge γ** — one accumulation step: the link claim `B`
folds into the running accumulator `A`. The folded claim is about the folded
word `f + γ • g`; its channel keeps `A`'s functionals (the shared,
post-alignment channel — module header note) and combines targets γ-linearly:
`σᵢ + γ·τᵢ`. The recommitment is `foldRoot A.rt γ B.rt`. -/
def foldClaims (A B : AccClaim Root F ι r) (γ : F) : AccClaim Root F ι r :=
  ⟨foldRoot A.rt γ B.rt,
    fun i => ((A.channel i).1, (A.channel i).2 + γ * (B.channel i).2)⟩

/-- The docstring identity, verbatim: the folded channel is `A`'s functionals
with γ-linearly combined targets. -/
@[simp] theorem foldClaims_channel (A B : AccClaim Root F ι r) (γ : F)
    (i : Fin r) :
    (foldClaims foldRoot A B γ).channel i
      = ((A.channel i).1, (A.channel i).2 + γ * (B.channel i).2) := rfl

@[simp] theorem foldClaims_rt (A B : AccClaim Root F ι r) (γ : F) :
    (foldClaims foldRoot A B γ).rt = foldRoot A.rt γ B.rt := rfl

/-- **Closure: CRS-claim × CRS-claim → CRS-claim.** If `f` witnesses `A` and
`g` witnesses `B`, and the two channels share functionals (`hshare` — the
post-alignment state; module header note), then the folded word `f + γ • g`
witnesses the folded claim: it is in the code (linearity of `C`) and meets
every γ-combined constraint (γ-linearity of the channel in both slots). This
is what makes the chain ONE accumulated object. -/
theorem foldClaims_satisfies {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {f g : ι → F} (γ : F)
    (hshare : ∀ i, B.weights i = A.weights i)
    (hA : AccClaim.Satisfies C A f) (hB : AccClaim.Satisfies C B g) :
    AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g) := by
  refine ⟨C.add_mem hA.1 (C.smul_mem γ hB.1), fun i => ?_⟩
  have hBg : A.weights i g = B.targets i := by rw [← hshare i]; exact hB.2 i
  show (A.channel i).1 (f + γ • g) = (A.channel i).2 + γ * (B.channel i).2
  rw [map_add, map_smul, smul_eq_mul]
  have hAf : (A.channel i).1 f = (A.channel i).2 := hA.2 i
  simp only [AccClaim.weights, AccClaim.targets] at hBg
  rw [hAf, hBg]

/-- The batching identity at the word: pairwise γ-power folds flatten to the
γ-power combination `f + γ • g + γ² • h`. -/
theorem foldWord_assoc (f g h : ι → F) (γ : F) :
    (f + γ • g) + γ ^ 2 • h = f + γ • (g + γ • h) := by
  rw [smul_add, smul_smul, ← add_assoc, pow_two]

/-- **Associativity of the γ-fold on the channel** (γ-power form): folding the
pairwise-folded `A, B` with `C'` at `γ²` equals folding `A` with the
pairwise-folded `B, C'` at `γ` — both are the flat γ-power combination
`σ + γ·τ + γ²·υ` on shared functionals. Stated on the channel: the root
component tracks the prover's opaque recommitment schedule, on which the
algebra imposes nothing (module header note). -/
theorem foldClaims_assoc (A B C' : AccClaim Root F ι r) (γ : F) :
    (foldClaims foldRoot (foldClaims foldRoot A B γ) C' (γ ^ 2)).channel
      = (foldClaims foldRoot A (foldClaims foldRoot B C' γ) γ).channel := by
  funext i
  refine Prod.ext rfl ?_
  show ((A.channel i).2 + γ * (B.channel i).2) + γ ^ 2 * (C'.channel i).2
      = (A.channel i).2 + γ * ((B.channel i).2 + γ * (C'.channel i).2)
  ring

/-- The flat form of a length-3 chain: targets are the γ-power combination
`σ + γ·τ + γ²·υ` — WHIR's `∑ γ^(i-1)·σᵢ`, reached by iterating the ONE
pairwise fold. -/
theorem foldClaims_chain_target (A B C' : AccClaim Root F ι r) (γ : F)
    (i : Fin r) :
    ((foldClaims foldRoot (foldClaims foldRoot A B γ) C' (γ ^ 2)).channel i).2
      = (A.channel i).2 + γ * (B.channel i).2 + γ ^ 2 * (C'.channel i).2 := by
  simp

end Fold

/-! ## Bridge to `Selvage/ConstrainedCode.lean` — one algebra, two presentations

The sibling file (landed concurrently) presents the SAME constraint channel as
weight VECTORS on List spines: `LinearConstraint` entries `⟨wt, target⟩` with
satisfaction `dotWt wt f = target`, the constrained code `constrainedRS` (WHIR
Def 4.5), and γ-batching in Horner form (`batchConstraint`), including the
exact-word Schwartz–Zippel soundness count (`card_batch_satisfying_le`). This
file is the CLAIM level: `Fin r` spines of linear functionals plus the opaque
root and the cross-word fold. The two presentations are provably the same
content — `exists_dotWt_eq` there gives one direction in the abstract; here
the working correspondence is BUILT:

* `dotWtL` — the pairing as a bilinear map, so a weight vector IS a channel
  functional;
* `AccClaim.ofConstraints` — a constraint list transported into a claim;
* `AccClaim.ofConstraints_satisfies_iff` — claim satisfaction over the RS code
  is EXACTLY membership in `constrainedRS`;
* `AccClaim.batch_ofConstraints` — claim-level γ-batching commutes with the
  list-level `batchConstraint`, on the nose.

Nothing is duplicated across the seam: Constr 5.5's exact-word soundness
lives THERE; the WARP shape, the cross-word fold, and closure live HERE. -/

section Bridge

variable [Fintype ι]

/-- The `dotWt` pairing of `Selvage/ConstrainedCode.lean` as a bilinear map: in
particular `dotWtL a : (ι → F) →ₗ[F] F` is a channel functional, and `dotWtL`
itself is linear in the weight vector — the fact the batch bridge runs on. -/
def dotWtL : (ι → F) →ₗ[F] (ι → F) →ₗ[F] F :=
  LinearMap.mk₂ F dotWt dotWt_add_left dotWt_smul_left
    (fun a f g => by simp [dotWt, mul_add, Finset.sum_add_distrib])
    (fun γ a f => by simp [dotWt, Finset.mul_sum, mul_left_comm])

@[simp] theorem dotWtL_apply (a f : ι → F) : dotWtL a f = dotWt a f := rfl

/-- A `LinearConstraint` list (the sibling channel) transported into an
accumulated claim: functionals via `dotWtL`, targets carried. -/
def AccClaim.ofConstraints (rt : Root) (cs : List (LinearConstraint ι F)) :
    AccClaim Root F ι cs.length :=
  ⟨rt, fun k => (dotWtL (cs[(k : ℕ)]).wt, (cs[(k : ℕ)]).target)⟩

/-- **The satisfaction bridge**: over the RS code, claim-level satisfaction of
a transported constraint list is EXACTLY membership in the sibling's
constrained code `CRS[F, dom, d, cs]` — the accumulated claim and the
constrained-codeword claim are one object. -/
theorem AccClaim.ofConstraints_satisfies_iff [DecidableEq ι] [DecidableEq F]
    {dom : ι ↪ F} {d : ℕ} {rt : Root} {cs : List (LinearConstraint ι F)}
    {f : ι → F} :
    AccClaim.Satisfies (reedSolomonCode dom d) (AccClaim.ofConstraints rt cs) f
      ↔ f ∈ constrainedRS dom d cs := by
  rw [mem_constrainedRS_iff]
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨hf, fun c hcmem => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hcmem
    exact hc ⟨k, hk⟩
  · rintro ⟨hf, hc⟩
    exact ⟨hf, fun k => hc (cs[(k : ℕ)]) (List.getElem_mem _)⟩

/-- The functional half of the batch bridge: the `LinearMap`-module γ-power
combination of transported weights is the transport of the sibling's Horner
`batchWt`. -/
theorem batchFunctional_dotWtL (γ : F) (cs : List (LinearConstraint ι F)) :
    batchFunctional γ (fun k : Fin cs.length => dotWtL (cs[(k : ℕ)]).wt)
      = dotWtL (batchWt γ cs) := by
  rw [batchWt_eq_sum, map_sum, batchFunctional]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul]

/-- **The batch bridge**: claim-level γ-batching of a transported list IS the
transport of the sibling's `batchConstraint` — the two Constr 5.5
implementations agree on the nose (weights via `batchWt_eq_sum`, targets via
`batchTarget_eq_sum`). -/
theorem AccClaim.batch_ofConstraints (rt : Root) (γ : F)
    (cs : List (LinearConstraint ι F)) :
    (AccClaim.ofConstraints rt cs).batch γ
      = AccClaim.ofConstraints rt [batchConstraint γ cs] := by
  unfold AccClaim.batch AccClaim.ofConstraints
  congr 1
  funext k
  obtain rfl := Fin.fin_one_eq_zero k
  exact Prod.ext (batchFunctional_dotWtL γ cs) ((batchTarget_eq_sum γ cs).symm)

end Bridge

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, all computing, over the tiny code `RS[F₅, {0,1,2,3}, 2]` of
`Selvage/ReedSolomon.lean`'s `RSExample` (lines over F₅ on 4 points) with the
word `xWord = (0,1,2,3)` (evaluations of `X`, a genuine codeword):

* **satisfiable** — `goodClaim_satisfiable`: a WARP-shape claim (an in-domain
  query constraint and a conservation-functional constraint — the two channel
  kinds of OB-3's receipt encoding) genuinely satisfied by `xWord`, by
  `decide`.
* **teeth** — `batch_badPair_iff`: a doctored pair of constraints (both
  FALSE on `xWord`, rigged with residuals −1 and +1 so the batch residual is
  `γ − 1`) is satisfied by the γ-batch IFF `γ = 1`. So `teeth_badChallenge`
  exhibits the soundness-error event at the ONE bad challenge, and
  `teeth_separates` shows every other γ catches the false pair — the fold
  separates. `teeth_bad_card` counts the bad set: EXACTLY 1 = (t−1)·ℓ
  challenges of |F| = 5, with t = 2 constraints and list size ℓ = 1 — the
  `(t−1)·ℓ/|F|` shape of `[ACC-sound]`, witnessed with its exact constant.
* **cross-word teeth** — `fold_teeth`: a link claim with a FALSE target
  folded into an honest accumulator is caught at every γ ≠ 0.
* **premise inhabitation** — `fold_honest` / `fold_honest_nonzero`: the
  closure theorem `foldClaims_satisfies` FIRES non-vacuously (every
  hypothesis discharged by concrete witnesses, for every γ — including a
  fold of two genuinely nonzero distinct codewords). -/

namespace AccExample

open RSExample

/-- The in-domain query functional at coordinate 2 — an evaluation-channel
constraint (LOOM §1: in-domain queries re-read as boolean multilinear
claims). -/
def q2 : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5 := LinearMap.proj 2

/-- The conservation functional `f ↦ ∑ᵢ f i` — OB-3's per-asset conservation
shape (`⟨f, a_conservation⟩`), a sum of coordinate projections in the
`LinearMap` module. -/
def consv : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5 := ∑ i : Fin 4, LinearMap.proj i

@[simp] theorem q2_apply (f : Fin 4 → ZMod 5) : q2 f = f 2 := rfl

@[simp] theorem consv_apply (f : Fin 4 → ZMod 5) : consv f = ∑ i : Fin 4, f i := by
  simp [consv]

@[simp] theorem xWord_two : xWord 2 = 2 := by decide

@[simp] theorem sum_xWord : (∑ i : Fin 4, xWord i) = 1 := by decide

theorem q2_xWord : q2 xWord = 2 := by decide

theorem consv_xWord : consv xWord = 1 := by
  rw [consv_apply]; exact sum_xWord

/-- A WARP-shape claim `(rt, α, μ, β, η) = ((), q2, 2, consv, 1)` that `xWord`
genuinely satisfies. -/
def goodClaim : AccClaim Unit (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp () (q2, 2) (consv, 1)

/-- **Satisfiable**: the keystone claim is inhabited by a real codeword — all
three conjuncts computed. -/
theorem goodClaim_satisfiable :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) goodClaim xWord :=
  AccClaim.warp_satisfies_iff.mpr ⟨xWord_mem, q2_xWord, consv_xWord⟩

/-- The doctored pair: both constraints FALSE on `xWord` (`q2 xWord = 2 ≠ 3`,
`consv xWord = 1 ≠ 0`), with residuals `actual − target = (−1, +1)` so the
γ-batch residual is `−1 + γ·1 = γ − 1` — a degree-`(t−1)` polynomial in γ
with exactly one root. -/
def badPair : AccClaim Unit (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp () (q2, 3) (consv, 0)

theorem badPair_not_satisfied :
    ¬ AccClaim.Satisfies (reedSolomonCode dom₅ 2) badPair xWord := by
  rintro ⟨-, hc⟩
  have h0 := hc 0
  simp [badPair, AccClaim.warp, AccClaim.weights, AccClaim.targets] at h0
  exact absurd h0 (by decide)

/-- **Teeth, exact**: the γ-batch of the false pair is satisfied by `xWord`
IFF `γ = 1` — the batch residual `γ − 1` vanishes only there. Every other
challenge separates the false pair from the honest claim. -/
theorem batch_badPair_iff (γ : ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord ↔ γ = 1 := by
  constructor
  · rintro ⟨-, hc⟩
    have h0 := hc 0
    simp [badPair, AccClaim.warp, AccClaim.batch, AccClaim.weights,
      AccClaim.targets, Fin.sum_univ_two] at h0
    linear_combination h0
  · rintro rfl
    refine ⟨xWord_mem, fun i => ?_⟩
    simp [badPair, AccClaim.warp, AccClaim.batch, AccClaim.weights,
      AccClaim.targets, Fin.sum_univ_two]
    decide

/-- The soundness-error EVENT, exhibited: at the one bad challenge `γ = 1`
the batch of a false pair is satisfied — this is the event whose probability
`[ACC-sound]` bounds by `(t−1)ℓ/|F|`. -/
theorem teeth_badChallenge :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch 1) xWord :=
  (batch_badPair_iff 1).mpr rfl

/-- Every challenge but the bad one catches the false pair: the fold has
teeth at generic γ. -/
theorem teeth_separates (γ : ZMod 5) (hγ : γ ≠ 1) :
    ¬ AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord :=
  fun h => hγ ((batch_badPair_iff γ).mp h)

open Classical in
/-- The `(t−1)·ℓ/|F|` SHAPE with its exact constant: the bad-challenge set of
the false pair has cardinality 1 = (t−1)·ℓ (t = 2 constraints, list size
ℓ = 1 in the unique-decoding regime) out of |F| = 5 — soundness error 1/5,
witnessed as a set count, not just an inequality. -/
theorem teeth_bad_card :
    (Finset.univ.filter fun γ : ZMod 5 =>
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord).card = 1 := by
  have h : (Finset.univ.filter fun γ : ZMod 5 =>
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord) = {1} := by
    ext γ
    simp [batch_badPair_iff]
  rw [h, Finset.card_singleton]

/-! ### Cross-word fold keystones -/

/-- The trivial recommitment schedule for the keystone's opaque `Unit` root. -/
def trivialRoot : Unit → ZMod 5 → Unit → Unit := fun _ _ _ => ()

/-- The running accumulator: one evaluation constraint, true on `xWord`. -/
def evalA : AccClaim Unit (ZMod 5) (Fin 4) 1 := ⟨(), fun _ => (q2, 2)⟩

/-- A link claim with target 0 — honest for the zero word (`q2 0 = 0`). -/
def evalB0 : AccClaim Unit (ZMod 5) (Fin 4) 1 := ⟨(), fun _ => (q2, 0)⟩

/-- A link claim with target 1 — honest for `oneWord` below (`q2 oneWord = 1`)
and FALSE for the zero word (`q2 0 = 0 ≠ 1`): satisfaction is a relation
between claim and word, and the fold keystones exercise both sides. -/
def evalB1 : AccClaim Unit (ZMod 5) (Fin 4) 1 := ⟨(), fun _ => (q2, 1)⟩

/-- The constant-1 word — evaluations of `C 1`, a genuine nonzero codeword. -/
def oneWord : Fin 4 → ZMod 5 := fun _ => 1

theorem oneWord_mem : oneWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 1, by rw [Polynomial.degree_C one_ne_zero]; decide,
      fun _ => by simp [oneWord]⟩

/-- **Premise inhabitation**: the closure theorem `foldClaims_satisfies`
fires non-vacuously — honest accumulator × honest link fold to a satisfied
claim on the folded word, for EVERY challenge. -/
theorem fold_honest (γ : ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (foldClaims trivialRoot evalA evalB0 γ) (xWord + γ • 0) :=
  foldClaims_satisfies trivialRoot γ (fun _ => rfl)
    ⟨xWord_mem, fun _ => q2_xWord⟩
    ⟨Submodule.zero_mem _, fun _ => rfl⟩

/-- The closure exercised on two genuinely NONZERO distinct codewords:
`xWord + γ • oneWord` witnesses the fold of the honest pair, for every γ. -/
theorem fold_honest_nonzero (γ : ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • oneWord) :=
  foldClaims_satisfies trivialRoot γ (fun _ => rfl)
    ⟨xWord_mem, fun _ => q2_xWord⟩
    ⟨oneWord_mem, fun _ => rfl⟩

/-- **Cross-word teeth**: folding a link claim that is FALSE for its word
(`evalB1` against the zero word) into an honest accumulator is caught by the
folded claim at every `γ ≠ 0` — the folded word `xWord + γ • 0 = xWord`
evaluates to `2`, but the folded target is `2 + γ`. -/
theorem fold_teeth (γ : ZMod 5) (hγ : γ ≠ 0) :
    ¬ AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0) := by
  rintro ⟨-, hc⟩
  have h0 := hc 0
  simp [foldClaims, evalA, evalB1, AccClaim.weights, AccClaim.targets] at h0
  exact hγ (by linear_combination h0)

end AccExample

/-! ## Residual obligations — prose, not stubs

Named residuals with their WARP/WHIR realizers; each becomes a real theorem,
never a `def : Prop := True` (the vacuous-obligation sin — see
`Assurance/ReceiptClaim.lean`'s residual note and the audit discipline).

**[ACC-sound]** — RBR soundness of the γ-fold. If the batched/folded claim is
δ-close-satisfiable, then except with probability `(t−1)·ℓ/|F|` over the
challenge γ (t = number of constraints folded, ℓ = the list size at radius δ;
WHIR Constr. 5.5 for same-word, `err★ + (s−1)·ℓ/|F|` via mutual correlated
agreement for cross-word, Constr. 7.4), every constituent constraint was
δ-close-satisfiable — round-by-round, so Fiat–Shamir in the ROM preserves
straightline extraction (LOOM §2's law). The load-bearing ingredient is
mutual correlated agreement, PROVED at the unique-decoding regime for every
linear code in `Selvage/CorrelatedAgreement.lean`
(`hasMutualCorrelatedAgreement_of_isProximityGenerator`, WHIR Lemma 4.10) and
instantiated for RS in `Selvage/ReedSolomon.lean`; the EXACT-WORD kernel of the
same-word case is already a theorem — `card_batch_satisfying_le` in
`Selvage/ConstrainedCode.lean` (the defect-polynomial root count, `≤ t−1`
challenges pass a violated batch), transported to this file's claims by the
bridge — so what remains is precisely the lift from exact membership to
δ-proximity (the sibling's `[CRS-batch-sound]`, one residual shared by both
files, stated once each side of the bridge) plus the cross-word case. The
keystones above pin the bound's shape: `teeth_bad_card` computes the
bad-challenge set of a t = 2, ℓ = 1 instance to EXACTLY (t−1)·ℓ = 1 of
|F| = 5. Also in this
residual's scope: the proximity ledger (δ, regime tag, additive error budget
— LOOM §6) joins `AccClaim` as a carried field once its fold rule (this
bound) is a theorem, and the pre-reduction nonlinear circuit claim
`P̂(β, C⁻¹(f)) = η` enters via the sumcheck front (`Selvage/Sumcheck.lean`), not
via this file's linear channel.
⟲ STATUS (`Selvage/AccSound.lean`): the probability bounds are now THEOREMS —
exact-word for BOTH fold rules (`accSound_batch_exact` /
`AccClaim.batch_sound_exact` at `(t−1)/|F|`; `foldClaims_sound_exact` at
`(s−1)/|F|`), δ-proximity same-word at `(t−1)·ℓ/|F|` with the list size as
hypothesis (`accSound_batch_proximity`, ℓ = 1 discharged at unique decoding),
and the cross-word accumulation step at UD with mutual CA consumed
(`foldClaims_sound_proximity_UD`, `err⋆ + (s−1)·ℓ/|F|` at s = 2, ℓ = 1).
What remains of this residual: the beyond-UD list regimes
`[ACC-sound-list]` and the RBR-game packaging + proximity-ledger field
`[ACC-sound-rbr]` — see that file's header.

**[ACC-extract]** — the straightline erasure extractor. WARP's relaxed
round-by-round knowledge soundness (WARP §4 + App. B): the extractor works
BACKWARDS — each round's extractor consumes the *next* round's witness — and
uses erasure correction ONLY (available for every linear code, O(n³) generic,
Õ(n) for RS; no unique/list decoder is ever run), recovering the accumulated
word from the `t` opened columns plus the mutual-agreement set. Depth
composition of the per-link extractors is loss-free,
`ε_sr ≤ (t+k)·ε_rbr` (WARP Thm B.4) — the tower PROVED in `Selvage/Depth.lean`
modulo the named seam `[OB-2a]`. Root binding (that `rt` commits the word the
extractor recovers — Merkle/BCS binding) is consumed here, which is why the
fold algebra above never inspects `Root`. -/

end Minidregg.Selvage
