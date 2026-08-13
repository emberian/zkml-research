/-
# Selvage.AccSound — [ACC-sound]: the γ-fold's soundness bound.

Closes the probability half of `Selvage/Accumulator.lean`'s `[ACC-sound]` residual:
for a fold at a uniformly random challenge γ, a word (pair) that does not
satisfy the individual claims satisfies the fold with probability at most the
WHIR bounds — `(t−1)·ℓ/|F|` for same-word batching (Constr. 5.5), and
`err⋆(δ) + (s−1)·ℓ/|F|` for the cross-word accumulation step (Constr. 7.4),
both instantiated here with everything the landed tree can realize. This lane
WIRES landed pieces; it re-derives neither root counting nor mutual CA:

* the EXACT-WORD kernel is `card_batch_satisfying_le`
  (`Selvage/ConstrainedCode.lean` — the defect-polynomial root count);
* the δ-proximity realizer is mutual correlated agreement at unique decoding
  (`Selvage/CorrelatedAgreement.lean` — WHIR Lemma 4.10, proved for every linear
  code) plus its unique-decoding mechanism `codeword_eq_of_close_of_close`;
* the claim algebra is `Selvage/Accumulator.lean`'s (`AccClaim.batch`,
  `foldClaims`).

## The statement map (what is PROVED here, no sorry, no axioms)

Same-word batching (WHIR Constr. 5.5), t = number of constraints:
* `accSound_batch_exact` — exact-word, list level: a word violating some
  constraint passes the γ-batch with probability ≤ (t−1)/|F| (the ℓ = 1 /
  full-membership regime). Direct division of the landed kernel.
* `AccClaim.batch_sound_exact` / `AccClaim.batch_sound_exact'` — the same
  bound at the accumulated-claim level (`A.batch γ`), transported through
  `exists_dotWt_eq`.
* `accSound_batch_proximity` — the δ-PROXIMITY bound `(t−1)·ℓ/|F|`: if no
  codeword δ-close to the word satisfies all constraints, then the probability
  that SOME δ-close codeword satisfies the γ-batch is ≤ (t−1)·ℓ/|F|, where ℓ
  bounds the number of codewords in the δ-ball (the list size — a hypothesis
  here; supplying it per-regime is the parameter ladder's job, LOOM §5).
  Union bound over the list, each list element priced by the landed kernel.
* `accSound_batch_proximity_UD` — the unique-decoding instantiation: at
  δ < dC/2 the list hypothesis is DISCHARGED with ℓ = 1 by
  `codeword_eq_of_close_of_close`, giving the unconditional (t−1)/|F|.

Cross-word fold (WHIR Constr. 7.4 / the accumulation step, s = 2 words):
* `card_fold_pair_satisfying_le` — the cross-word exact-word kernel, obtained
  by REUSE of `card_batch_satisfying_le` through a sum-domain encoding (the
  pair (u, v) on ι ⊕ ι; the cross-word fold IS same-word batching over the
  disjoint union — no new root counting).
* `foldClaims_sound_exact` — exact-word: a pair violating some individual
  claim satisfies the folded claim (on the folded word f + γ•g) with
  probability ≤ 1/|F| = (s−1)/|F|.
* `foldClaims_sound_proximity_UD` — THE HEADLINE: the accumulation step's
  δ-proximity soundness at unique decoding, with mutual correlated agreement
  genuinely consumed. If no pair of δ-close codewords satisfies the individual
  claims, then the probability (uniform γ) that the folded word f + γ•g is
  δ-close to SOME codeword satisfying the folded claim is
  ≤ err⋆(δ) + 1/|F| — Constr. 7.4's `err⋆ + (s−1)·ℓ/|F|` at s = 2, ℓ = 1.
  This is exactly where plain proximity gaps fail and mutual CA is
  load-bearing (WARP fn. 6, LOOM §1): `HasMutualCorrelatedAgreement` supplies
  the decomposition w = u + γ•v of the nearby codeword; unique decoding pins
  (u, v) challenge-independently; the exact-word cross kernel prices the one
  bad challenge.
* `foldClaims_sound_proximity_UD'` — end-to-end corollary: hypotheses reduced
  to `IsProximityGenerator` (+ the landed Lemma 4.10 realizer), bound
  err(δ) + 1/|F| with the SAME err (mutual CA is free at UD).

## Transcription notes (read before auditing)

* **`uniformProb` comes from `Selvage/Rbr.lean`** — one import beyond this lane's
  nominal three (Accumulator, ConstrainedCode, CorrelatedAgreement).
  Justification: the toolkit was specified for reuse but lives in Rbr (landed,
  stable, already an aggregate import of `Selvage.lean`); a local twin under this
  namespace would collide or duplicate (house law: nothing lands beside what
  it supersedes). `Selvage/OutOfDomain.lean` is the precedent — it imports Rbr
  for `uniformProb` alone and keeps its counting lemmas `private` to avoid
  clashing with `Selvage/Depth.lean`'s toolkit (NOT imported here: sibling lanes
  may have it dirty). Same discipline: every counting lemma below is
  `private`.
* **The challenge field lives in `Type`, not `Type*`** — `uniformProb`'s `C :
  Type` fixes the universe (Rbr's choice, matching every deployed challenge
  space). The index/domain `ι` stays universe-polymorphic.
* **List size ℓ enters as `Nat.card` of the δ-ball's codeword set** — the
  instance-free cardinality, matching `uniformProb`'s own `Nat.card` style.
  The (δ, ℓ)-list-decodability of the code is a HYPOTHESIS of the general
  proximity statements (as in WHIR, where ℓ is the list size the regime
  supplies); the UD theorems discharge it with ℓ = 1, which is why the v0 rung
  is unconditional (LOOM §5).
* **Strict fold events.** Every event bounded here is about the honest fold
  interface: the folded word is `f + γ • g` (the prover's recommitment is
  bound separately — `[ACC-extract]`'s obligation, not touched here), and
  "satisfies the fold" is `AccClaim.Satisfies` of the folded claim, exact or
  through a δ-close codeword. The δ-slack sits in the events, never in the
  satisfaction relation (LOOM §1's strict/relaxed split).

## What REMAINS of [ACC-sound] after this file (honest residuals, prose)

* **[ACC-sound-list]** — the beyond-UD regimes: supplying the list hypothesis
  `ℓ > 1` (Johnson: unconditional for RS since 2025/2051 + 2025/2110; the
  Guruswami–Sudan count is not in this tree) and the cross-word statement at
  ℓ > 1, where the fixed-pair uniqueness argument below must be replaced by
  the correlated-list enumeration (the (s−1)·ℓ — not ℓ² — count needs the
  agreement sets of the ℓ candidates correlated, WHIR §7). Realizer:
  `HasMutualCorrelatedAgreement` at the Johnson rung + a list-decoding count.
* **[ACC-sound-rbr]** — packaging these per-step challenge bounds as the
  round function of the RBR game (`Selvage/Rbr.lean`'s vocabulary) so the
  FS/BCS compilation (`Selvage/FiatShamir.lean`) consumes them; the bounds here
  are the per-round error masses that ledger carries. The proximity-ledger
  field joining `AccClaim` (module note in Accumulator.lean) lands with it.
* The `IsProximityGenerator` hypothesis for RS at concrete parameters is WHIR
  Thm 4.8 — a named hypothesis in this tree by the `Selvage/ReedSolomon.lean`
  precedent, inherited (not created) by the corollaries here.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Selvage.Accumulator
import Selvage.ConstrainedCode
import Selvage.CorrelatedAgreement
import Selvage.Rbr

namespace Minidregg.Selvage

variable {Root : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]
variable {r : ℕ}

/-! ## Counting plumbing for `uniformProb` (private — Depth owns the public
toolkit; these are the four facts this file needs, kept `private` so the
aggregate `Selvage.lean` build never sees two copies). -/

private theorem uniformProb_eq_card_filter (F : Type) [Fintype F] (p : F → Prop)
    [DecidablePred p] :
    uniformProb F p = ((Finset.univ.filter p).card : ℝ) / (Fintype.card F : ℝ) := by
  unfold uniformProb
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem uniformProb_le_of_card_le {F : Type} [Fintype F] [Nonempty F]
    {p : F → Prop} [DecidablePred p] {m : ℕ}
    (h : (Finset.univ.filter p).card ≤ m) :
    uniformProb F p ≤ (m : ℝ) / (Fintype.card F : ℝ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniformProb_eq_card_filter, div_le_div_iff_of_pos_right hF]
  exact_mod_cast h

private theorem uniformProb_nonneg' (F : Type) [Fintype F] (p : F → Prop) :
    0 ≤ uniformProb F p := by
  unfold uniformProb
  positivity

private theorem uniformProb_mono' {F : Type} [Fintype F] [Nonempty F]
    {p q : F → Prop} (h : ∀ c, p c → q c) :
    uniformProb F p ≤ uniformProb F q := by
  classical
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniformProb_eq_card_filter F p, uniformProb_eq_card_filter F q,
    div_le_div_iff_of_pos_right hF]
  exact_mod_cast
    Finset.card_le_card (Finset.monotone_filter_right _ fun c _ => h c)

private theorem uniformProb_or_le' (F : Type) [Fintype F] [Nonempty F]
    (p q : F → Prop) :
    uniformProb F (fun c => p c ∨ q c) ≤ uniformProb F p + uniformProb F q := by
  classical
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniformProb_eq_card_filter F p, uniformProb_eq_card_filter F q,
    uniformProb_eq_card_filter F (fun c => p c ∨ q c), ← add_div,
    div_le_div_iff_of_pos_right hF]
  calc ((Finset.univ.filter fun c => p c ∨ q c).card : ℝ)
      = ((Finset.univ.filter p ∪ Finset.univ.filter q).card : ℝ) := by
        rw [Finset.filter_or]
    _ ≤ ((Finset.univ.filter p).card : ℝ) + ((Finset.univ.filter q).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _

/-- The probability bridge: for the affine generator (seed = a uniform field
element), `ProximityGenerator.pr` IS `uniformProb` of the seed event — the
mutual-CA error bound of `Selvage/CorrelatedAgreement.lean` and the challenge
counting of this file are the same measure. -/
theorem affineGenerator_pr_eq_uniformProb [Fintype F] (E : (Fin 2 → F) → Prop) :
    (affineGenerator F).pr E
      = uniformProb F (fun γ => E ((affineGenerator F).gen γ)) := by
  classical
  unfold ProximityGenerator.pr
  rw [uniformProb_eq_card_filter]
  have hw : ∀ ω : (affineGenerator F).Seed,
      (affineGenerator F).weight ω = ((Fintype.card F : ℝ))⁻¹ := fun _ => rfl
  rw [Finset.sum_congr rfl fun ω _ => hw ω, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  congr 2

/-! ## Distance-side plumbing: agreement sets from δ-closeness, quantization -/

omit [DecidableEq ι] [Field F] in
/-- Converse of `relDist_le_of_agreesOn`: δ-closeness yields an agreement set
of at least `(1−δ)·n` coordinates (the pointwise-equality set). -/
private theorem le_card_agreeSet_of_relDist_le [Nonempty ι] {f u : ι → F} {δ : ℝ}
    (h : relDist f u ≤ δ) :
    (1 - δ) * (Fintype.card ι : ℝ)
      ≤ ((Finset.univ.filter fun x => f x = u x).card : ℝ) := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdist : (hammingDist f u : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
    rw [relDist, div_le_iff₀ hn] at h
    exact h
  have hcard : hammingDist f u = (Finset.univ.filter fun x => ¬f x = u x).card := by
    simp [hammingDist]
  have hsplit : (Finset.univ.filter fun x => f x = u x).card
      + (Finset.univ.filter fun x => ¬f x = u x).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hsplit' : ((Finset.univ.filter fun x => f x = u x).card : ℝ)
      + (hammingDist f u : ℝ) = (Fintype.card ι : ℝ) := by
    rw [hcard]
    exact_mod_cast congrArg Nat.cast hsplit
  linarith

omit [DecidableEq ι] [Field F] in
/-- Below the quantization floor `1/n`, δ-closeness is equality — the
mechanism that pins the δ-ball to a point in the tight keystones. Contrapositive
of `one_div_card_le_relDist`. -/
private theorem eq_of_relDist_le_of_lt_inv_card [Nonempty ι] {f u : ι → F}
    {δ : ℝ} (h : relDist f u ≤ δ) (hδ : δ < 1 / (Fintype.card ι : ℝ)) :
    f = u := by
  by_contra hne
  exact absurd (le_trans (one_div_card_le_relDist hne) h) (not_le.mpr hδ)

/-! ## Same-word batching (WHIR Constr. 5.5): the exact-word bound, ℓ = 1

The full-membership regime: the word is held EXACTLY (no δ-slack), so the list
size is 1 and the bound is `(t−1)/|F|`. The counting is entirely the landed
kernel `card_batch_satisfying_le`; this section only divides by `|F|`. -/

omit [DecidableEq ι] in
/-- **[ACC-sound], exact-word case, list level.** A word violating some
constraint of the list satisfies the γ-batch (WHIR Constr. 5.5) with
probability at most `(t−1)/|F|` over a uniform challenge — the landed
Schwartz–Zippel count `card_batch_satisfying_le`, read as `uniformProb`. -/
theorem accSound_batch_exact [Fintype F] {fw : ι → F}
    {cs : List (LinearConstraint ι F)} (h : ∃ c ∈ cs, ¬Satisfies fw c) :
    uniformProb F (fun γ => Satisfies fw (batchConstraint γ cs))
      ≤ ((cs.length : ℝ) - 1) / (Fintype.card F : ℝ) := by
  classical
  have hlen : 1 ≤ cs.length := by
    obtain ⟨c, hc, -⟩ := h
    exact List.length_pos_of_mem hc
  have hcast : ((cs.length - 1 : ℕ) : ℝ) = (cs.length : ℝ) - 1 := by
    rw [Nat.cast_sub hlen, Nat.cast_one]
  rw [← hcast]
  exact uniformProb_le_of_card_le (card_batch_satisfying_le h)

omit [DecidableEq ι] in
/-- **[ACC-sound], exact-word case, claim level.** A word violating some
constraint of an accumulated claim's channel satisfies the γ-batched claim
`A.batch γ` with probability at most `(r−1)/|F|`. Transport of the list-level
kernel through `exists_dotWt_eq`: every channel functional is a `dotWt`, so the
claim's channel is a constraint list and the batched events coincide. -/
theorem AccClaim.batch_sound_exact [Fintype F] {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {fw : ι → F}
    (h : ∃ i, A.weights i fw ≠ A.targets i) :
    uniformProb F (fun γ => AccClaim.Satisfies C (A.batch γ) fw)
      ≤ ((r : ℝ) - 1) / (Fintype.card F : ℝ) := by
  classical
  -- the channel as a constraint list, functional-by-functional
  choose a ha using fun i => exists_dotWt_eq (A.weights i)
  set cs : List (LinearConstraint ι F) :=
    List.ofFn (fun i : Fin r => ⟨a i, A.targets i⟩) with hcs
  have hlen : cs.length = r := List.length_ofFn ..
  have hwt : ∀ k : Fin cs.length,
      (cs[(k : ℕ)]).wt = a (Fin.cast hlen k) := by
    intro k
    simp [hcs, List.getElem_ofFn, Fin.cast]
  have htg : ∀ k : Fin cs.length,
      (cs[(k : ℕ)]).target = A.targets (Fin.cast hlen k) := by
    intro k
    simp [hcs, List.getElem_ofFn, Fin.cast]
  -- the two batch events coincide pointwise
  have hbatch : ∀ γ : F, Minidregg.Selvage.Satisfies fw (batchConstraint γ cs) ↔
      batchFunctional γ A.weights fw = ∑ i : Fin r, γ ^ (i : ℕ) * A.targets i := by
    intro γ
    have hwtsum : dotWt (batchWt γ cs) fw
        = ∑ i : Fin r, γ ^ (i : ℕ) * A.weights i fw := by
      have h1 : dotWt (batchWt γ cs) fw
          = batchFunctional γ (fun k : Fin cs.length => dotWtL (cs[(k : ℕ)]).wt) fw := by
        rw [batchFunctional_dotWtL]
        rfl
      rw [h1, batchFunctional_apply]
      rw [← Fin.sum_congr' (fun i : Fin r => γ ^ (i : ℕ) * A.weights i fw) hlen]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dotWtL_apply, hwt k, ha]
      rfl
    have htgsum : batchTarget γ cs = ∑ i : Fin r, γ ^ (i : ℕ) * A.targets i := by
      rw [batchTarget_eq_sum]
      rw [← Fin.sum_congr' (fun i : Fin r => γ ^ (i : ℕ) * A.targets i) hlen]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [htg k]
      rfl
    rw [Minidregg.Selvage.Satisfies, batchConstraint, hwtsum, htgsum,
      batchFunctional_apply]
  -- event inclusion: the batched claim implies the batched list constraint
  have hsub : ∀ γ : F, AccClaim.Satisfies C (A.batch γ) fw →
      Minidregg.Selvage.Satisfies fw (batchConstraint γ cs) := by
    rintro γ ⟨-, hc⟩
    have h0 := hc 0
    rw [hbatch]
    exact h0
  -- the violation transports to the list
  have hviol : ∃ c ∈ cs, ¬Minidregg.Selvage.Satisfies fw c := by
    obtain ⟨i, hi⟩ := h
    refine ⟨cs[(Fin.cast hlen.symm i : ℕ)], List.getElem_mem _, ?_⟩
    rw [Minidregg.Selvage.Satisfies, hwt (Fin.cast hlen.symm i),
      htg (Fin.cast hlen.symm i), ha]
    simpa using hi
  -- count and divide
  have hr : 1 ≤ r := by
    obtain ⟨i, -⟩ := h
    exact i.pos
  have hcast : ((cs.length - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [hlen, Nat.cast_sub hr, Nat.cast_one]
  rw [← hcast]
  exact le_trans (uniformProb_mono' hsub)
    (uniformProb_le_of_card_le (card_batch_satisfying_le hviol))

omit [DecidableEq ι] in
/-- The honest-phrasing corollary: a codeword that does NOT satisfy the claim
satisfies its γ-batch with probability at most `(r−1)/|F|`. (Membership plus
claim failure classically yields a violated channel index; `r ≥ 1` because an
unsatisfied claim has a constraint to violate.) -/
theorem AccClaim.batch_sound_exact' [Fintype F] {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {fw : ι → F} (hfC : fw ∈ C)
    (h : ¬AccClaim.Satisfies C A fw) :
    uniformProb F (fun γ => AccClaim.Satisfies C (A.batch γ) fw)
      ≤ ((r : ℝ) - 1) / (Fintype.card F : ℝ) := by
  refine AccClaim.batch_sound_exact ?_
  by_contra hall
  push Not at hall
  exact h ⟨hfC, hall⟩

/-! ## Same-word batching: the δ-proximity bound `(t−1)·ℓ/|F|`

The lift from exact membership to δ-proximity — the sibling files'
`[CRS-batch-sound]` shape. The event is now "SOME codeword δ-close to the word
satisfies the γ-batch"; the list size ℓ (number of codewords in the δ-ball)
prices the union bound, and each list element is priced by the SAME landed
kernel. At unique decoding the list hypothesis is discharged with ℓ = 1
(`accSound_batch_proximity_UD`) — the v0 rung, unconditional. -/

/-- **[ACC-sound], δ-proximity, same-word (WHIR Constr. 5.5's `(t−1)·ℓ/|F|`).**
If every codeword δ-close to the word violates some constraint of the list
(`hfar` — the word is not δ-close to the multi-constrained code), and the
δ-ball around the word contains at most ℓ codewords (`hlist` — the
(δ, ℓ)-list-decodability of the code, the regime's job to supply), then a
uniform challenge lets some δ-close codeword satisfy the γ-batch with
probability at most `(t−1)·ℓ/|F|`: a union bound over the list, the landed
exact-word kernel pricing each list element at `t−1` challenges. -/
theorem accSound_batch_proximity [Fintype F] {C : Submodule F (ι → F)}
    {δ : ℝ} {fw : ι → F} {cs : List (LinearConstraint ι F)} {ℓ : ℕ}
    (hne : cs ≠ [])
    (hlist : Nat.card {u : ι → F // u ∈ C ∧ relDist fw u ≤ δ} ≤ ℓ)
    (hfar : ∀ u ∈ C, relDist fw u ≤ δ → ∃ c ∈ cs, ¬Satisfies u c) :
    uniformProb F
        (fun γ => ∃ u ∈ C, relDist fw u ≤ δ ∧ Satisfies u (batchConstraint γ cs))
      ≤ ((cs.length : ℝ) - 1) * (ℓ : ℝ) / (Fintype.card F : ℝ) := by
  classical
  set L : Finset (ι → F) :=
    Finset.univ.filter (fun u => u ∈ C ∧ relDist fw u ≤ δ) with hLdef
  have hLcard : L.card ≤ ℓ := by
    calc L.card = Fintype.card {u : ι → F // u ∈ C ∧ relDist fw u ≤ δ} :=
          (Fintype.card_subtype _).symm
      _ = Nat.card {u : ι → F // u ∈ C ∧ relDist fw u ≤ δ} :=
          Nat.card_eq_fintype_card.symm
      _ ≤ ℓ := hlist
  -- union bound at the counting level
  have hsub : (Finset.univ.filter fun γ : F =>
        ∃ u ∈ C, relDist fw u ≤ δ ∧ Satisfies u (batchConstraint γ cs))
      ⊆ L.biUnion (fun u =>
        Finset.univ.filter fun γ : F => Satisfies u (batchConstraint γ cs)) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨-, u, huC, hclose, hsat⟩ := hγ
    exact Finset.mem_biUnion.mpr
      ⟨u, by simp [hLdef, huC, hclose],
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsat⟩⟩
  have hcount : ∀ u ∈ L,
      (Finset.univ.filter fun γ : F => Satisfies u (batchConstraint γ cs)).card
        ≤ cs.length - 1 := by
    intro u hu
    rw [hLdef, Finset.mem_filter] at hu
    exact card_batch_satisfying_le (hfar u hu.2.1 hu.2.2)
  have hcard : (Finset.univ.filter fun γ : F =>
        ∃ u ∈ C, relDist fw u ≤ δ ∧ Satisfies u (batchConstraint γ cs)).card
      ≤ ℓ * (cs.length - 1) :=
    calc (Finset.univ.filter fun γ : F =>
          ∃ u ∈ C, relDist fw u ≤ δ ∧ Satisfies u (batchConstraint γ cs)).card
        ≤ (L.biUnion (fun u => Finset.univ.filter fun γ : F =>
            Satisfies u (batchConstraint γ cs))).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ L, (Finset.univ.filter fun γ : F =>
            Satisfies u (batchConstraint γ cs)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ L, (cs.length - 1) := Finset.sum_le_sum hcount
      _ = L.card * (cs.length - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ℓ * (cs.length - 1) := Nat.mul_le_mul_right _ hLcard
  have hlen : 1 ≤ cs.length := by
    have := List.length_pos_iff.mpr hne
    omega
  have hcast : ((ℓ * (cs.length - 1) : ℕ) : ℝ) = ((cs.length : ℝ) - 1) * (ℓ : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hlen, Nat.cast_one]
    ring
  rw [← hcast]
  exact uniformProb_le_of_card_le hcard

/-- **[ACC-sound], δ-proximity at UNIQUE DECODING — the v0 rung,
unconditional.** At radius `δ < dC/2` the δ-ball contains at most one codeword
(`codeword_eq_of_close_of_close` — `Selvage/CorrelatedAgreement.lean`'s
unique-decoding mechanism), so the list hypothesis is discharged with ℓ = 1
and the bound is the exact-word `(t−1)/|F|`. -/
theorem accSound_batch_proximity_UD [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} {δ dC : ℝ} {fw : ι → F}
    {cs : List (LinearConstraint ι F)}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v) (hδC : δ < dC / 2)
    (hne : cs ≠ [])
    (hfar : ∀ u ∈ C, relDist fw u ≤ δ → ∃ c ∈ cs, ¬Satisfies u c) :
    uniformProb F
        (fun γ => ∃ u ∈ C, relDist fw u ≤ δ ∧ Satisfies u (batchConstraint γ cs))
      ≤ ((cs.length : ℝ) - 1) / (Fintype.card F : ℝ) := by
  have hlist : Nat.card {u : ι → F // u ∈ C ∧ relDist fw u ≤ δ} ≤ 1 := by
    classical
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff.mpr fun ⟨u, huC, hu⟩ ⟨v, hvC, hv⟩ =>
      Subtype.ext (codeword_eq_of_close_of_close hdC huC hvC hδC hu hv)
  have := accSound_batch_proximity (F := F) hne hlist hfar
  rwa [Nat.cast_one, mul_one] at this

/-! ## The cross-word fold (WHIR Constr. 7.4 / the accumulation step)

The kernel first: the cross-word residual `(φu − σ) + γ·(φv − τ)` is the
defect polynomial of a SAME-word batch over the disjoint-sum domain `ι ⊕ ι` —
the pair `(u, v)` is one word there, and each side's constraint reads through
one summand. So the cross-word count is a REUSE of `card_batch_satisfying_le`,
not new root counting. -/

omit [DecidableEq ι] in
/-- **The cross-word exact-word kernel** (s = 2): if the pair `(u, v)` violates
the claim pair `(σ, τ)` under the functional `φ`, at most `1 = s − 1` challenges
γ satisfy the γ-combined constraint `φu + γ·φv = σ + γ·τ`. Proof by sum-domain
encoding into the landed same-word kernel. -/
theorem card_fold_pair_satisfying_le [Fintype F] {φ : (ι → F) →ₗ[F] F} {σ τ : F}
    {u v : ι → F} (h : ¬(φ u = σ ∧ φ v = τ)) :
    (Finset.univ.filter fun γ : F => φ u + γ * φ v = σ + γ * τ).card ≤ 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_dotWt_eq φ
  -- the pair as ONE word over ι ⊕ ι; each constraint reads one summand
  set w2 : ι ⊕ ι → F := Sum.elim u v with hw2
  set c₀ : LinearConstraint (ι ⊕ ι) F := ⟨Sum.elim a 0, σ⟩ with hc₀
  set c₁ : LinearConstraint (ι ⊕ ι) F := ⟨Sum.elim 0 a, τ⟩ with hc₁
  have h₀ : dotWt c₀.wt w2 = φ u := by
    rw [← ha u]
    simp [dotWt, hc₀, hw2, Fintype.sum_sum_type]
  have h₁ : dotWt c₁.wt w2 = φ v := by
    rw [← ha v]
    simp [dotWt, hc₁, hw2, Fintype.sum_sum_type]
  have hbatch : ∀ γ : F,
      Satisfies w2 (batchConstraint γ [c₀, c₁]) ↔ φ u + γ * φ v = σ + γ * τ := by
    intro γ
    show dotWt (batchWt γ [c₀, c₁]) w2 = batchTarget γ [c₀, c₁] ↔ _
    rw [show batchWt γ [c₀, c₁] = c₀.wt + γ • (c₁.wt + γ • 0) from rfl,
      show batchTarget γ [c₀, c₁] = c₀.target + γ * (c₁.target + γ * 0) from rfl,
      smul_zero, add_zero, mul_zero, add_zero, dotWt_add_left, dotWt_smul_left,
      h₀, h₁]
  have hviol : ∃ c ∈ [c₀, c₁], ¬Satisfies w2 c := by
    rcases not_and_or.mp h with h' | h'
    · exact ⟨c₀, List.mem_cons_self .., by rwa [Satisfies, h₀]⟩
    · exact ⟨c₁, by simp, by rwa [Satisfies, h₁]⟩
  calc (Finset.univ.filter fun γ : F => φ u + γ * φ v = σ + γ * τ).card
      = (Finset.univ.filter fun γ : F =>
          Satisfies w2 (batchConstraint γ [c₀, c₁])).card := by
        exact congrArg Finset.card
          (Finset.filter_congr fun γ _ => (hbatch γ).symm)
    _ ≤ 1 := card_batch_satisfying_le hviol

omit [DecidableEq ι] in
/-- **[ACC-sound], exact-word case, cross-word fold.** A pair of words
violating some individual claim of the (shared-channel) pair `(A, B)`
satisfies the folded claim `foldClaims A B γ` — on the honest folded word
`f + γ • g` — with probability at most `1/|F| = (s−1)/|F|` (s = 2 words). The
violated index's γ-combined constraint prices the event through the sum-domain
kernel. -/
theorem foldClaims_sound_exact [Fintype F] {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A B : AccClaim Root F ι r}
    {f g : ι → F}
    (hviol : ∃ i, ¬(A.weights i f = A.targets i ∧ A.weights i g = B.targets i)) :
    uniformProb F (fun γ =>
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g))
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hviol
  have hsub : ∀ γ : F,
      AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g) →
      A.weights i₀ f + γ * A.weights i₀ g = A.targets i₀ + γ * B.targets i₀ := by
    rintro γ ⟨-, hc⟩
    have h0 := hc i₀
    simp only [AccClaim.weights, AccClaim.targets, foldClaims_channel] at h0
    rw [map_add, map_smul, smul_eq_mul] at h0
    exact h0
  have hcard := card_fold_pair_satisfying_le (φ := A.weights i₀) hi₀
  have := uniformProb_le_of_card_le (F := F) hcard
  rw [Nat.cast_one] at this
  exact le_trans (uniformProb_mono' hsub) this

omit [DecidableEq ι] in
/-- The honest-phrasing corollary of the cross-word exact bound: two codewords
that do NOT jointly witness the (shared-channel) claim pair satisfy the fold
with probability at most `1/|F|`. -/
theorem foldClaims_sound_exact' [Fintype F] {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A B : AccClaim Root F ι r}
    {f g : ι → F} (hshare : ∀ i, B.weights i = A.weights i)
    (hf : f ∈ C) (hg : g ∈ C)
    (h : ¬(AccClaim.Satisfies C A f ∧ AccClaim.Satisfies C B g)) :
    uniformProb F (fun γ =>
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g))
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  refine foldClaims_sound_exact foldRoot ?_
  by_contra hall
  push Not at hall
  exact h ⟨⟨hf, fun i => (hall i).1⟩, ⟨hg, fun i => by
    show B.weights i g = B.targets i
    rw [hshare i]
    exact (hall i).2⟩⟩

/-! ## The headline: cross-word fold soundness at unique decoding, δ-proximity

WHIR Constr. 7.4's bound `err⋆(δ) + (s−1)·ℓ/|F|` at s = 2 words, ℓ = 1 (the
unique-decoding regime — v0's rung, LOOM §5). This is THE place mutual
correlated agreement is load-bearing (WARP fn. 6): a plain proximity gap says
the folded word is close to SOME codeword, but only mutual CA relates that
codeword's agreement set to the constituents', yielding the decomposition
`w = u + γ•v` with u, v δ-close to the input words. Unique decoding then pins
(u, v) challenge-independently, and the exact-word cross kernel prices the one
bad challenge for the pinned pair. -/

/-- **[ACC-sound], δ-proximity, cross-word fold at UNIQUE DECODING.** Fix
words `f, g` (the prover's committed words — arbitrary, not assumed codewords)
and a shared-channel claim pair `(A, B)`. Suppose no pair of codewords
δ-close to `f, g` respectively satisfies the individual claims (`hfar`). Then,
over a uniform challenge γ, the folded word `f + γ • g` is δ-close to some
codeword satisfying the folded claim `foldClaims A B γ` with probability at
most `err⋆(δ) + 1/|F|`, where `err⋆` is the mutual-correlated-agreement error
of the affine generator (WHIR Def 4.9, realized at UD by the landed
Lemma 4.10). Regime: `0 < δ`, `δ < 1 − B⋆` (mutual CA's interval),
`δ < dC/2` (unique decoding). -/
theorem foldClaims_sound_proximity_UD [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} {δ dC Bstar : ℝ}
    {errstar : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (hfar : ∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) :
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ errstar δ + 1 / (Fintype.card F : ℝ) := by
  classical
  set fv : Fin 2 → ι → F := ![f, g] with hfv
  have hcomb : ∀ γ : F, comb ((affineGenerator F).gen γ) fv = f + γ • g := by
    intro γ
    funext x
    simp [hfv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- the pinned-pair event: some pair of δ-close codewords satisfies the
  -- γ-combined claims
  set R : F → Prop := fun γ => ∃ u ∈ C, ∃ v ∈ C,
      relDist f u ≤ δ ∧ relDist g v ≤ δ ∧
      ∀ i, A.weights i u + γ * A.weights i v
        = A.targets i + γ * B.targets i with hR
  -- Step 1 (mutual CA consumed): the fold event splits into the mutual-CA
  -- failure event and the pinned-pair event.
  have hkey : ∀ γ : F, (∃ w, relDist (f + γ • g) w ≤ δ ∧
      AccClaim.Satisfies C (foldClaims foldRoot A B γ) w) →
      MutualCAFailure C δ fv ((affineGenerator F).gen γ) ∨ R γ := by
    rintro γ ⟨w, hwclose, hwC, hwsat⟩
    by_cases hFail : MutualCAFailure C δ fv ((affineGenerator F).gen γ)
    · exact Or.inl hFail
    · right
      -- the agreement set of the folded word with its nearby codeword
      set S : Finset ι := Finset.univ.filter (fun x => (f + γ • g) x = w x)
        with hS
      have hScard : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) :=
        le_card_agreeSet_of_relDist_le hwclose
      have hAgS : AgreesOn S (f + γ • g) w := fun x hx =>
        (Finset.mem_filter.mp hx).2
      have hAgComb : AgreesOn S (comb ((affineGenerator F).gen γ) fv) w := by
        rw [hcomb]
        exact hAgS
      -- ¬failure at S: each input agrees with SOME codeword on S — the
      -- agreement-set relation only mutual CA provides
      have hgood : ∀ i, ∃ u' ∈ C, AgreesOn S (fv i) u' := by
        by_contra hbad
        push Not at hbad
        obtain ⟨i, hi⟩ := hbad
        exact hFail ⟨S, hScard, ⟨w, hwC, hAgComb⟩, i, fun u' hu' =>
          hi u' hu'⟩
      obtain ⟨u, huC, huAg⟩ := hgood 0
      obtain ⟨v, hvC, hvAg⟩ := hgood 1
      have hfu : AgreesOn S f u := by simpa [hfv] using huAg
      have hgv : AgreesOn S g v := by simpa [hfv] using hvAg
      -- the decomposition: w = u + γ•v, by unique decoding
      have huvC : u + γ • v ∈ C := C.add_mem huC (C.smul_mem γ hvC)
      have hAg2 : AgreesOn S (f + γ • g) (u + γ • v) := by
        intro x hx
        have h1 := hfu x hx
        have h2 := hgv x hx
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
      have hclose2 : relDist (f + γ • g) (u + γ • v) ≤ δ :=
        relDist_le_of_agreesOn hAg2 hScard
      have hweq : w = u + γ • v :=
        codeword_eq_of_close_of_close hdC hwC huvC hδC hwclose hclose2
      have hfuδ : relDist f u ≤ δ := relDist_le_of_agreesOn hfu hScard
      have hgvδ : relDist g v ≤ δ := relDist_le_of_agreesOn hgv hScard
      refine ⟨u, huC, v, hvC, hfuδ, hgvδ, fun i => ?_⟩
      have h0 := hwsat i
      simp only [AccClaim.weights, AccClaim.targets, foldClaims_channel] at h0
      rw [hweq, map_add, map_smul, smul_eq_mul] at h0
      exact h0
  -- Step 2: the mutual-CA error prices the failure event.
  have hFailBound : uniformProb F
      (fun γ => MutualCAFailure C δ fv ((affineGenerator F).gen γ))
        ≤ errstar δ := by
    rw [← affineGenerator_pr_eq_uniformProb]
    exact hMCA fv δ hδ0 hδB
  -- Step 3: unique decoding pins the pair challenge-independently; the
  -- exact-word cross kernel prices the pinned pair at one challenge.
  have hRBound : uniformProb F R ≤ 1 / (Fintype.card F : ℝ) := by
    by_cases hex : ∃ γ₀, R γ₀
    · obtain ⟨γ₀, u₀, hu₀C, v₀, hv₀C, hfu₀, hgv₀, -⟩ := hex
      obtain ⟨i₀, hi₀⟩ := hfar u₀ hu₀C v₀ hv₀C hfu₀ hgv₀
      have hsub : ∀ γ, R γ →
          A.weights i₀ u₀ + γ * A.weights i₀ v₀
            = A.targets i₀ + γ * B.targets i₀ := by
        rintro γ ⟨u, huC, v, hvC, hfu, hgv, hall⟩
        have hu_eq : u = u₀ :=
          codeword_eq_of_close_of_close hdC huC hu₀C hδC hfu hfu₀
        have hv_eq : v = v₀ :=
          codeword_eq_of_close_of_close hdC hvC hv₀C hδC hgv hgv₀
        rw [← hu_eq, ← hv_eq]
        exact hall i₀
      have hcard := card_fold_pair_satisfying_le (φ := A.weights i₀) hi₀
      have hdiv := uniformProb_le_of_card_le (F := F) hcard
      rw [Nat.cast_one] at hdiv
      exact le_trans (uniformProb_mono' hsub) hdiv
    · push Not at hex
      have h0 : uniformProb F R = 0 := by
        rw [uniformProb_eq_card_filter,
          Finset.filter_false_of_mem (fun γ _ => hex γ)]
        simp
      rw [h0]
      positivity
  -- assemble
  calc uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
          AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ uniformProb F (fun γ =>
          MutualCAFailure C δ fv ((affineGenerator F).gen γ) ∨ R γ) :=
        uniformProb_mono' hkey
    _ ≤ uniformProb F
          (fun γ => MutualCAFailure C δ fv ((affineGenerator F).gen γ))
        + uniformProb F R := uniformProb_or_le' F _ _
    _ ≤ errstar δ + 1 / (Fintype.card F : ℝ) := add_le_add hFailBound hRBound

/-- **End-to-end corollary**: hypotheses reduced to the proximity-generator
property (WHIR Def 4.7 — for RS this is Thm 4.8, the one analytic import this
tree carries as a named hypothesis, `Selvage/ReedSolomon.lean` precedent). The
landed Lemma 4.10 (`affineGenerator_hasMutualCorrelatedAgreement`) turns it
into mutual CA at UD with the SAME error, so the accumulation step's soundness
is `err(δ) + 1/|F|` — Constr. 7.4's `err⋆ + (s−1)·ℓ/|F|` at s = 2, ℓ = 1,
with err⋆ = err free of charge in the unique-decoding regime. -/
theorem foldClaims_sound_proximity_UD' [Fintype F] [Nonempty ι]
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A B : AccClaim Root F ι r} {f g : ι → F} {δ dC B' : ℝ} {err : ℝ → ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hPG : IsProximityGenerator (affineGenerator F) C B' err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B' → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B' → 0 ≤ err δ)
    (hδ0 : 0 < δ) (hδB : δ < 1 - B') (hδC : δ < dC / 2)
    (hfar : ∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) :
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ err δ + 1 / (Fintype.card F : ℝ) := by
  refine foldClaims_sound_proximity_UD foldRoot hdC
    (affineGenerator_hasMutualCorrelatedAgreement C hdC hPG
      (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2))
    hδ0 ?_ hδC hfar
  -- δ < 1 − max (1 − dC/2) B': both regime facts feed the packed bound
  rcases le_total (1 - dC / 2) B' with h | h
  · rw [max_eq_right h]
    exact hδB
  · rw [max_eq_left h]
    linarith

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, all computing, over the landed F₅ instances (`RSExample`'s
`RS[F₅, {0,1,2,3}, 2]`, `AccExample`'s claims). Each general theorem above is
FIRED on concrete data, and each bound is ATTAINED — computed as an equality,
so the theorems are tight, not slack:

* same-word exact: `badPair` (t = 2, both constraints false on `xWord`) passes
  the batch at EXACTLY 1 = (t−1)·ℓ of 5 challenges — probability `1/5`,
  equal to the theorem's bound `(2−1)/5`;
* cross-word exact: the false link `evalB1` folded into the honest `evalA`
  survives at exactly the challenge γ = 0 — probability `1/5 = (s−1)/5`;
* cross-word δ-PROXIMITY (the headline): over `C = ⊤` (where
  `hasMutualCorrelatedAgreement_top_affine` supplies mutual CA with err⋆ = 0)
  at δ = 1/16 inside the UD interval, the fold event probability is EXACTLY
  `1/5 = err⋆ + (s−1)·ℓ/|F|` — the headline bound attained with every
  hypothesis discharged by landed witnesses (premise inhabitation: the
  theorem fires non-vacuously end to end);
* same-word δ-proximity: the zero word against `[evalC, evalC₂]` over the RS
  code at δ = 1/16 — event probability exactly `1/5 = (t−1)·ℓ/|F|`, ℓ = 1
  discharged by unique decoding. -/

namespace AccSoundExample

open RSExample AccExample CRSExample

open Classical in
/-- The bad-challenge set of the same-word keystone, as a set: `{1}` (the one
challenge where the doctored pair's batch residual `γ − 1` vanishes). -/
theorem batch_badSet :
    (Finset.univ.filter fun γ : ZMod 5 =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord)
      = {1} := by
  classical
  ext γ
  simp [batch_badPair_iff]

open Classical in
/-- **Same-word bound ATTAINED**: the probability that `xWord` survives the
batch of the false pair is EXACTLY `1/5` — equal to `(t−1)·ℓ/|F|` at t = 2,
ℓ = 1, |F| = 5. -/
theorem batch_prob_eq :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord)
      = 1 / 5 := by
  classical
  rw [uniformProb_eq_card_filter, batch_badSet]
  norm_num [ZMod.card]

/-- The general claim-level theorem FIRED on the keystone (premise
inhabitation: the violation witness is computed), giving the same `1/5` from
the other side — bound met with equality. -/
theorem batch_bound_fired :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) (badPair.batch γ) xWord)
      ≤ ((2 : ℝ) - 1) / 5 := by
  have h := AccClaim.batch_sound_exact (C := reedSolomonCode dom₅ 2)
    (A := badPair) (fw := xWord) ⟨0, by decide⟩
  simpa [ZMod.card] using h

open Classical in
/-- **Cross-word bound ATTAINED**: the surviving-challenge set of the
exact-word fold keystone (false link `evalB1` into honest `evalA`, on the
folded word) is exactly `{0}`. -/
theorem fold_badSet :
    (Finset.univ.filter fun γ : ZMod 5 =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      = {0} := by
  classical
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hγ
    exact fold_teeth γ hγ h
  · rintro rfl
    refine ⟨by simpa using xWord_mem, fun i => ?_⟩
    show q2 (xWord + (0 : ZMod 5) • 0) = 2 + 0 * 1
    simp


open Classical in
/-- Cross-word exact-word probability: exactly `1/5 = (s−1)/|F|`. -/
theorem fold_prob_eq :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      = 1 / 5 := by
  classical
  rw [uniformProb_eq_card_filter, fold_badSet]
  norm_num [ZMod.card]

/-- The general cross-word theorem FIRED on the keystone: `≤ 1/5`, met with
equality by `fold_prob_eq`. The violation witness: the link claims `q2 = 1`
of the zero word, but `q2 0 = 0`. -/
theorem fold_bound_fired :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      ≤ 1 / 5 := by
  have h := foldClaims_sound_exact (C := reedSolomonCode dom₅ 2) trivialRoot
    (A := evalA) (B := evalB1) (f := xWord) (g := 0) ⟨0, by decide⟩
  simpa [ZMod.card] using h

/-! ### δ-proximity keystones — the proximity theorems fired and attained

Radius δ = 1/16, below the quantization floor 1/4 of the 4-point domain, so
the δ-balls are points and every closeness hypothesis is discharged by
computation. The UD hypotheses use `minDistLB_inhabited`'s `dC = 1/n` (the
landed satisfiability witness for the distance bound). -/

/-- The pinned batch set of the zero word against `[evalC, evalC₂]`: exactly
`{2}` (where the batch residual `1 + 2γ` of the violated pair vanishes —
the γ the sibling's `batch_teeth_card_eq` counts). Computed. -/
theorem batch_pinned_iff : ∀ γ : ZMod 5,
    Satisfies (0 : Fin 4 → ZMod 5) (batchConstraint γ [evalC, evalC₂]) ↔
      γ = 2 := by decide

/-- **Same-word δ-proximity theorem FIRED** (premise inhabitation for
`accSound_batch_proximity_UD`): over the RS code at δ = 1/16 < dC/2, the zero
word — which violates `evalC` — has some δ-close codeword satisfying the
γ-batch with probability ≤ (t−1)·ℓ/|F| = 1/5, every hypothesis discharged by
landed witnesses. -/
theorem batch_proximity_fired :
    uniformProb (ZMod 5) (fun γ => ∃ u ∈ reedSolomonCode dom₅ 2,
        relDist (0 : Fin 4 → ZMod 5) u ≤ 1 / 16 ∧
        Satisfies u (batchConstraint γ [evalC, evalC₂]))
      ≤ ((2 : ℝ) - 1) / 5 := by
  have h := accSound_batch_proximity_UD (F := ZMod 5)
    (C := reedSolomonCode dom₅ 2) (δ := 1 / 16)
    (dC := 1 / (Fintype.card (Fin 4) : ℝ)) (fw := (0 : Fin 4 → ZMod 5))
    (cs := [evalC, evalC₂]) (minDistLB_inhabited _)
    (by norm_num [Fintype.card_fin]) (by simp)
    (fun u huC hclose => by
      have h0u : (0 : Fin 4 → ZMod 5) = u :=
        eq_of_relDist_le_of_lt_inv_card hclose (by norm_num [Fintype.card_fin])
      exact ⟨evalC, by simp, by rw [← h0u]; exact zero_not_satisfies⟩)
  simpa [ZMod.card] using h

open Classical in
/-- **Same-word δ-proximity bound ATTAINED**: the event probability is EXACTLY
`1/5 = (t−1)·ℓ/|F|` (t = 2, ℓ = 1, |F| = 5). The δ-ball around the zero word
is `{0}` (quantization), so the event is precisely the pinned batch set `{2}`
of `batch_pinned_iff`. -/
theorem batch_proximity_prob_eq :
    uniformProb (ZMod 5) (fun γ => ∃ u ∈ reedSolomonCode dom₅ 2,
        relDist (0 : Fin 4 → ZMod 5) u ≤ 1 / 16 ∧
        Satisfies u (batchConstraint γ [evalC, evalC₂]))
      = 1 / 5 := by
  classical
  have h00 : relDist (0 : Fin 4 → ZMod 5) 0 ≤ 1 / 16 := by
    simp [relDist]
  have hev : ∀ γ : ZMod 5, (∃ u ∈ reedSolomonCode dom₅ 2,
      relDist (0 : Fin 4 → ZMod 5) u ≤ 1 / 16 ∧
      Satisfies u (batchConstraint γ [evalC, evalC₂])) ↔ γ = 2 := by
    intro γ
    constructor
    · rintro ⟨u, -, hclose, hsat⟩
      have h0u : (0 : Fin 4 → ZMod 5) = u :=
        eq_of_relDist_le_of_lt_inv_card hclose (by norm_num [Fintype.card_fin])
      rw [← h0u] at hsat
      exact (batch_pinned_iff γ).mp hsat
    · rintro rfl
      exact ⟨0, Submodule.zero_mem _, h00, (batch_pinned_iff 2).mpr rfl⟩
  rw [uniformProb_eq_card_filter]
  have hset : (Finset.univ.filter fun γ : ZMod 5 =>
      ∃ u ∈ reedSolomonCode dom₅ 2, relDist (0 : Fin 4 → ZMod 5) u ≤ 1 / 16 ∧
        Satisfies u (batchConstraint γ [evalC, evalC₂])) = {2} := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hev γ
  rw [hset]
  norm_num [ZMod.card]

/-- **THE HEADLINE FIRED** (premise inhabitation for
`foldClaims_sound_proximity_UD`): over `C = ⊤`, where the landed
`hasMutualCorrelatedAgreement_top_affine` supplies mutual CA with err⋆ = 0 and
`minDistLB_inhabited` supplies dC = 1/4, the fold of the false link `evalB1`
into the honest `evalA` on words (xWord, 0) at δ = 1/16 is δ-close-satisfied
with probability ≤ err⋆ + (s−1)·ℓ/|F| = 0 + 1/5. Every hypothesis of the
headline theorem discharged by landed witnesses — the theorem is
non-vacuous end to end. -/
theorem fold_proximity_fired :
    uniformProb (ZMod 5) (fun γ =>
        ∃ w, relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (foldClaims trivialRoot evalA evalB1 γ) w)
      ≤ 1 / 5 := by
  have hmax : max (1 - 1 / (Fintype.card (Fin 4) : ℝ) / 2) 0 = 7 / 8 := by
    rw [Fintype.card_fin]
    rw [max_eq_left (by norm_num)]
    norm_num
  have h := foldClaims_sound_proximity_UD (F := ZMod 5)
    (C := (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))) trivialRoot
    (A := evalA) (B := evalB1) (f := xWord) (g := 0) (δ := 1 / 16)
    (dC := 1 / (Fintype.card (Fin 4) : ℝ))
    (minDistLB_inhabited _) hasMutualCorrelatedAgreement_top_affine
    (by norm_num) (by rw [hmax]; norm_num) (by norm_num [Fintype.card_fin])
    (fun u _ v _ hcu hcv => by
      have h1 : xWord = u :=
        eq_of_relDist_le_of_lt_inv_card hcu (by norm_num [Fintype.card_fin])
      have h2 : (0 : Fin 4 → ZMod 5) = v :=
        eq_of_relDist_le_of_lt_inv_card hcv (by norm_num [Fintype.card_fin])
      refine ⟨0, fun hpair => ?_⟩
      rw [← h2] at hpair
      exact absurd hpair.2 (by decide))
  simpa [ZMod.card] using h

open Classical in
/-- **THE HEADLINE ATTAINED**: the fold-proximity event probability is EXACTLY
`1/5 = err⋆ + (s−1)·ℓ/|F|` (err⋆ = 0 at ⊤, s = 2, ℓ = 1, |F| = 5) — the
headline bound is tight including its mutual-CA term. The event pins to
γ = 0: the δ-ball around the folded word `xWord` is `{xWord}` (quantization),
and `q2 xWord = 2 = 2 + γ·1` forces γ = 0. -/
theorem fold_proximity_prob_eq :
    uniformProb (ZMod 5) (fun γ =>
        ∃ w, relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (foldClaims trivialRoot evalA evalB1 γ) w)
      = 1 / 5 := by
  classical
  have hev : ∀ γ : ZMod 5, (∃ w,
      relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
      AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (foldClaims trivialRoot evalA evalB1 γ) w) ↔ γ = 0 := by
    intro γ
    have hxg : xWord + γ • (0 : Fin 4 → ZMod 5) = xWord := by simp
    constructor
    · rintro ⟨w, hclose, -, hsat⟩
      rw [hxg] at hclose
      have hxw : xWord = w :=
        eq_of_relDist_le_of_lt_inv_card hclose (by norm_num [Fintype.card_fin])
      have h0 := hsat 0
      simp only [AccClaim.weights, AccClaim.targets, foldClaims_channel] at h0
      rw [← hxw] at h0
      have h2 : (2 : ZMod 5) = 2 + γ * 1 := by
        rw [← q2_xWord]
        exact h0
      linear_combination -h2
    · rintro rfl
      refine ⟨xWord, ?_, Submodule.mem_top, fun i => ?_⟩
      · rw [hxg]
        simp [relDist]
      · show q2 (xWord + (0 : ZMod 5) • (0 : Fin 4 → ZMod 5)) = 2 + 0 * 1
        simp
  rw [uniformProb_eq_card_filter]
  have hset : (Finset.univ.filter fun γ : ZMod 5 => ∃ w,
      relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
      AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (foldClaims trivialRoot evalA evalB1 γ) w) = {0} := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hev γ
  rw [hset]
  norm_num [ZMod.card]

end AccSoundExample

end Minidregg.Selvage
