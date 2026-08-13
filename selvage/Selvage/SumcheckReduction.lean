/-
# Selvage.SumcheckReduction — the sumcheck front retires the constraint channel.

LOOM §6: the accumulated object is a multi-constrained CRS claim; the decider's
SINGLE sumcheck absorbs the whole constraint list. This file is the bridge that
makes that sentence a theorem: a `ConstrainedCode` linear constraint
`⟨wt, f⟩ = σ` (`Satisfies`/`dotWt`) IS a sumcheck sum-claim
`Σ_i wt(i)·f(i) = σ` over the evaluation domain — the exact object
`Selvage/Sumcheck.lean`'s proved soundness reduces — so a word VIOLATING the
constraint survives the sumcheck's random challenges only with the
round-by-round probability `v·d/|F|`.

**What is proved here (no `sorry`, no new soundness derivation — pure wiring of
the two landed layers):**

* `constraint_as_sumcheck` — **the bridge, definitional**: `Satisfies f c` ↔ the
  sum-claim `Σ_i constraintSummand c f i = c.target` holds (`Iff.rfl`; the
  summand is `i ↦ c.wt i · f i`, the claimed total is the constraint target, the
  TRUE total `trueSum c f` is the actual pairing `dotWt`).
* `constraint_as_hypercube_sum` — the claim-OBJECT half of the reshaping: along
  any index equivalence `ι ≃ ({0,1}^v)` the constraint's sum becomes literally a
  sum over the boolean hypercube, the domain sumcheck walks.
* `sumcheck_retires_constraint` — **the retirement theorem (fixed round
  polynomials)**: run the sumcheck front on the constraint's sum-claim (claimed
  total `c.target`, honest truth chain anchored at `trueSum c f`); if the word
  violates the constraint, the verifier accepts with probability `≤ v·d/|F|`.
  Direct reuse of `sumcheck_soundness` — the violation `¬ Satisfies f c` IS the
  `H ≠ S` clause of `AcceptsFalse`.
* `satisfies_not_acceptsFalse` — the honest side: a word SATISFYING the
  constraint has no lie to launder (`AcceptsFalse` is impossible outright).
* `adaptive_sumcheck_soundness` / `adaptive_sumcheck_retires_constraint` — the
  **adaptive packaging** Sumcheck.lean names as its one unbuilt piece, assembled
  here (no soundness re-derived): round polynomials may depend on the challenge
  PREFIX (`PrefixMeasurable`); the per-transcript reduction
  (`sumcheck_reduction`) lands each accepted-false transcript in a
  prefix-measurable laundering set (`launderSet`, `≤ d` elements by the reused
  root count `card_agreeFinset_lt`), and the DISCHARGED
  `adaptiveUnionBound_holds` gives `≤ v·d/|F|`. This matters because the fixed
  theorem's honest hypothesis forces near-constant truth chains at `v ≥ 2`; the
  adaptive form is the one a real multi-round honest prover (the MLE round
  polynomials) inhabits.
* **§6 absorption of the list**: `list_as_single_sumcheck` — a word satisfying a
  WHOLE constraint list satisfies the single γ-batched sum-claim (reuse of
  `satisfies_batch_of_forall`); `batch_survives_prob_le` — stage 1 of the
  soundness pipeline in probability form: a list-violating word's γ-batch stays
  TRUE for `≤ (t−1)/|F|` of uniform γ (reuse of `card_batch_satisfying_le`
  through `uniformProb_mem_finset`); `sumcheck_retires_batch` — stage 2: for
  every γ where the batch stays violated, ONE sumcheck on the batched claim
  catches the word except with probability `v·d/|F|`. Round-by-round reading:
  the γ-round contributes `(t−1)/|F|` and the sumcheck rounds `v·d/|F|` to the
  additive RBR error ledger — the whole linear (ℤ-linear, γ-linear) part of the
  accumulated constraint list is retired by one sumcheck.

**Keystones (ATLAS: satisfiable + teeth, BUILT, over F₅ — reusing
`CRSExample`'s constraint `f(1) = 1` and words):** `SCRExample.xWord_sumClaim` —
the honest codeword's constraint rendered AS the sum-claim, computed;
`xWord_hypercube_sumClaim` — the same claim transported to `{0,1}²` along an
explicit `Fin 4 ≃ (Fin 2 → Bool)`, computed; `xWord_never_caught` — the honest
word is never falsely convicted. Teeth: the zero word violates the constraint
(claimed `1`, true total `0` — `zero_trueSum`); `zero_word_caught` instantiates
the retirement theorem CONCRETELY (one round, cheating prover `g̃ = X` passing
the round check), every hypothesis discharged, bound `1/5`; and
`zero_word_accept_witness` exhibits the challenge `r = 0` on which the cheat IS
accepted — the caught-event is nonempty, so the bound constrains a real event,
not a vacuum. `adaptive_bound_fires` runs the adaptive packaging on the same
data.

**Residual — `[SC-reshape]` (prose, per the `[CRS-batch-sound]` precedent: no
placeholder Prop).** What remains between this file and a turnkey decider
sumcheck is the HONEST-PROVER REALIZER: exhibiting the multilinear-extension
round polynomials — WHIR Def 4.5's `f̂` (and the weight's `â`), with
`gᵢ(X) = Σ_{b ∈ {0,1}^{v−i−1}} â·f̂(r₁,…,rᵢ₋₁, X, b)` — as the `honest` family,
discharging `hHonest` (boolean-sum consistency, degree `≤ deg(â·f̂)` per round)
and realizing the final oracle check as the evaluation `â(r)·f̂(r)`. The claim
OBJECT is already reshaped (`constraint_as_hypercube_sum`); the adaptive
protocol shape the MLE prover needs is packaged (`adaptive_sumcheck_soundness`);
only the MLE construction itself is future vocabulary. Everything above is
stated so that realizer plugs in as a hypothesis instantiation, not a
restatement.
-/
import Selvage.Sumcheck
import Selvage.ConstrainedCode

namespace Minidregg.Selvage

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The bridge: a linear constraint presents as a sumcheck sum-claim -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The summand of the sum-claim a linear constraint presents: `i ↦ wt(i)·f(i)`.
The sumcheck's domain function — `Satisfies f c` claims its total is
`c.target`. -/
def constraintSummand (c : LinearConstraint ι F) (f : ι → F) : ι → F :=
  fun i => c.wt i * f i

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The TRUE total of the presented sum — what the summand actually adds to. -/
def trueSum (c : LinearConstraint ι F) (f : ι → F) : F :=
  ∑ i, constraintSummand c f i

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The true total is the constraint pairing itself. -/
theorem trueSum_eq_dotWt (c : LinearConstraint ι F) (f : ι → F) :
    trueSum c f = dotWt c.wt f := rfl

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **The bridge (definitional).** A constrained-code linear constraint IS a
sumcheck sum-claim: `Satisfies f c` holds iff the claim
`Σ_i constraintSummand c f i = c.target` does. `ConstrainedCode`'s `dotWt` and
the sumcheck's sum-over-the-domain are the same object; this `Iff.rfl` is the
interface both layers meet at. -/
theorem constraint_as_sumcheck (f : ι → F) (c : LinearConstraint ι F) :
    Satisfies f c ↔ ∑ i, constraintSummand c f i = c.target :=
  Iff.rfl

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Reindexing a domain sum along an equivalence with the boolean hypercube. -/
theorem sum_reindex_hypercube {v : ℕ} (e : ι ≃ (Fin v → Bool)) (w : ι → F) :
    ∑ b : Fin v → Bool, w (e.symm b) = ∑ i, w i :=
  Fintype.sum_equiv e.symm (fun b => w (e.symm b)) w fun _ => rfl

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **The claim-object half of `[SC-reshape]`, closed.** Along any index
equivalence `ι ≃ {0,1}^v`, the constraint's sum-claim becomes literally a sum
over the boolean hypercube — the domain the sumcheck walks. (What is NOT closed
here is the honest MLE round-polynomial realizer; see the module docstring.) -/
theorem constraint_as_hypercube_sum {v : ℕ} (e : ι ≃ (Fin v → Bool))
    (f : ι → F) (c : LinearConstraint ι F) :
    Satisfies f c ↔
      ∑ b : Fin v → Bool, constraintSummand c f (e.symm b) = c.target := by
  rw [constraint_as_sumcheck, sum_reindex_hypercube e (constraintSummand c f)]

/-! ## The acceptance event, and violation as the false-claim clause -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The sumcheck verifier's acceptance event on claimed total `H` against the
honest truth chain anchored at `S`: every round's boolean check passes and the
final folded claim matches the truth (the verifier's terminal oracle check).
`AcceptsFalse` is exactly this conjoined with `H ≠ S`
(`acceptsFalse_iff_accepts`). -/
def SumcheckAccepts {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F)
    (r : Fin v → F) : Prop :=
  (∀ i, i < v → (prover i).eval 0 + (prover i).eval 1
      = scChain H prover (chalOf r) i)
    ∧ scChain H prover (chalOf r) v = scChain S honest (chalOf r) v

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
theorem acceptsFalse_iff_accepts {v : ℕ} {prover honest : ℕ → Polynomial F}
    {H S : F} {r : Fin v → F} :
    AcceptsFalse prover honest H S r
      ↔ SumcheckAccepts prover honest H S r ∧ H ≠ S := by
  unfold AcceptsFalse SumcheckAccepts
  tauto

/-! ## The retirement theorem (fixed round polynomials) -/

omit [DecidableEq ι] in
/-- **The sumcheck retires the linear constraint.** Run the sumcheck front on
the constraint's sum-claim: claimed total `c.target`, honest truth chain
anchored at the ACTUAL pairing `trueSum c f`. If the word VIOLATES the
constraint, the verifier accepts with probability at most `v·d/|F|` over the
uniform challenge vector — `Selvage/Sumcheck.lean`'s `sumcheck_soundness` applied
verbatim, because the violation `¬ Satisfies f c` IS the false-claim clause
`c.target ≠ trueSum c f`. Fixed (challenge-independent) round polynomials, as in
`sumcheck_soundness`; the adaptive form a real multi-round honest prover
inhabits is `adaptive_sumcheck_retires_constraint` below. -/
theorem sumcheck_retires_constraint {v d : ℕ}
    {prover honest : ℕ → Polynomial F} {f : ι → F} {c : LinearConstraint ι F}
    (hviol : ¬ Satisfies f c)
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1
        = scChain (trueSum c f) honest (chalOf r) i) :
    uniformProb (Fin v → F)
      (SumcheckAccepts prover honest c.target (trueSum c f))
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  have hne : c.target ≠ trueSum c f := by
    intro h
    apply hviol
    show dotWt c.wt f = c.target
    rw [← trueSum_eq_dotWt, h]
  have hconv : uniformProb (Fin v → F)
      (SumcheckAccepts prover honest c.target (trueSum c f))
      = uniformProb (Fin v → F)
          (AcceptsFalse prover honest c.target (trueSum c f)) :=
    uniformProb_congr fun r =>
      ⟨fun h => acceptsFalse_iff_accepts.mpr ⟨h, hne⟩,
       fun h => (acceptsFalse_iff_accepts.mp h).1⟩
  rw [hconv]
  exact sumcheck_soundness hProverDeg hHonestDeg hHonest

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The honest side: a word SATISFYING the constraint has no lie to launder —
`AcceptsFalse` at the constraint's claim is impossible outright (its false-claim
clause is refuted by `Satisfies`). -/
theorem satisfies_not_acceptsFalse {v : ℕ}
    {prover honest : ℕ → Polynomial F} {f : ι → F} {c : LinearConstraint ι F}
    (hsat : Satisfies f c) (r : Fin v → F) :
    ¬ AcceptsFalse prover honest c.target (trueSum c f) r := by
  intro h
  have hsat' : trueSum c f = c.target := hsat
  exact h.2.2 hsat'.symm

/-! ## The adaptive packaging (prefix-dependent round polynomials)

`sumcheck_soundness` fixes the round polynomials up front; its honest
boolean-sum hypothesis then forces near-constant truth chains for `v ≥ 2`, so
the fixed theorem is really the one-round engine iterated. A real multi-round
prover — honest (the MLE round polynomials) or cheating — chooses round `i`'s
polynomial from the challenge prefix. Sumcheck.lean proved both halves of the
adaptive statement (`sumcheck_reduction` per transcript,
`adaptiveUnionBound_holds` for prefix-measurable bad sets) and named the
packaging as its one unbuilt piece; this section builds exactly that packaging,
re-deriving no soundness content. -/

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Prefix-measurability: the round-`i` message depends on the challenge stream
only through coordinates `< i` — the information a round-`i` prover actually
has. -/
def PrefixMeasurable (P : (ℕ → F) → ℕ → Polynomial F) : Prop :=
  ∀ (χ χ' : ℕ → F) (i : ℕ), (∀ j, j < i → χ j = χ' j) → P χ i = P χ' i

open Classical in
omit [Fintype ι] [DecidableEq ι] in
/-- Round `i`'s laundering set for prefix-dependent messages: empty when the
round message is honest (an honest round cannot launder a lie — see
`adaptive_sumcheck_soundness`), the agreement finset of the two round
polynomials otherwise. -/
noncomputable def launderSet {v : ℕ}
    (prover honest : (ℕ → F) → ℕ → Polynomial F)
    (r : Fin v → F) (i : Fin v) : Finset F :=
  if prover (chalOf r) i.val = honest (chalOf r) i.val then ∅
  else agreeFinset (prover (chalOf r) i.val) (honest (chalOf r) i.val)

omit [Fintype ι] [DecidableEq ι] in
/-- The laundering set counts: `≤ d` elements, by the reused root count
`card_agreeFinset_lt` (degree `≤ d` round polynomials). -/
theorem launderSet_card_le {v d : ℕ}
    {prover honest : (ℕ → F) → ℕ → Polynomial F}
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (r : Fin v → F) (i : Fin v) :
    (launderSet prover honest r i).card ≤ d := by
  unfold launderSet
  by_cases hpe : prover (chalOf r) i.val = honest (chalOf r) i.val
  · rw [if_pos hpe]
    simp
  · rw [if_neg hpe]
    have h := card_agreeFinset_lt (hProverDeg _ _ i.isLt) (hHonestDeg _ _ i.isLt) hpe
    omega

omit [Fintype ι] [DecidableEq ι] in
/-- The laundering set is prefix-measurable: it reads the challenges only
through the prefix `r|_{<i}` — exactly the measurability
`adaptiveUnionBound_holds` consumes. -/
theorem launderSet_prefixMeas {v : ℕ}
    {prover honest : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover) (hhm : PrefixMeasurable honest)
    (i : Fin v) (r r' : Fin v → F)
    (hpre : ∀ j : Fin v, (j : ℕ) < (i : ℕ) → r j = r' j) :
    launderSet prover honest r i = launderSet prover honest r' i := by
  have hchal : ∀ j, j < (i : ℕ) → chalOf r j = chalOf r' j := by
    intro j hj
    have hjv : j < v := lt_trans hj i.isLt
    rw [chalOf, dif_pos hjv, chalOf, dif_pos hjv]
    exact hpre ⟨j, hjv⟩ hj
  unfold launderSet
  simp only [hpm (chalOf r) (chalOf r') i.val hchal,
    hhm (chalOf r) (chalOf r') i.val hchal]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The adaptive verifier accepts a false claim: `AcceptsFalse` with each
round's polynomials drawn from the challenge prefix. -/
def AdaptiveAcceptsFalse {v : ℕ}
    (prover honest : (ℕ → F) → ℕ → Polynomial F) (H S : F)
    (r : Fin v → F) : Prop :=
  AcceptsFalse (prover (chalOf r)) (honest (chalOf r)) H S r

omit [Fintype ι] [DecidableEq ι] in
/-- **Adaptive sumcheck soundness — the packaging, assembled.** Round
polynomials may depend on the challenge prefix (`PrefixMeasurable`, degrees
`≤ d`, honest boolean-sum consistency along the truth chain); a false claim
(`H ≠ S` inside `AdaptiveAcceptsFalse`) is accepted with probability
`≤ v·d/|F|`. Per transcript, `sumcheck_reduction` forces the lie to launder at
some round; an honest round cannot launder (check passed + honest consistency
collapse claim onto truth), so the challenge lands in that round's
`launderSet` — prefix-measurable with `≤ d` elements — and the DISCHARGED
`adaptiveUnionBound_holds` closes the union bound. -/
theorem adaptive_sumcheck_soundness {v d : ℕ}
    {prover honest : (ℕ → F) → ℕ → Polynomial F} {H S : F}
    (hpm : PrefixMeasurable prover) (hhm : PrefixMeasurable honest)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ r : Fin v → F, ∀ i, i < v →
      (honest (chalOf r) i).eval 0 + (honest (chalOf r) i).eval 1
        = scChain S (honest (chalOf r)) (chalOf r) i) :
    uniformProb (Fin v → F) (AdaptiveAcceptsFalse prover honest H S)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  have hstep : ∀ r : Fin v → F, AdaptiveAcceptsFalse prover honest H S r →
      ∃ i : Fin v, r i ∈ launderSet prover honest r i := by
    rintro r ⟨hchecks, hfinal, hfalse⟩
    obtain ⟨j, hj, hne, hag⟩ :=
      sumcheck_reduction (v := v) (prover := prover (chalOf r))
        (honest := honest (chalOf r)) (chal := chalOf r)
        (claimF := scChain H (prover (chalOf r)) (chalOf r))
        (truF := scChain S (honest (chalOf r)) (chalOf r))
        (fun i _ => rfl) (fun i _ => rfl) hfalse hfinal
    refine ⟨⟨j, hj⟩, ?_⟩
    have hpe : prover (chalOf r) (⟨j, hj⟩ : Fin v).val
        ≠ honest (chalOf r) (⟨j, hj⟩ : Fin v).val := by
      intro heq
      have hchk := hchecks j hj
      rw [show prover (chalOf r) j = honest (chalOf r) j from heq] at hchk
      exact hne (hchk.symm.trans (hHonest r j hj))
    unfold launderSet
    rw [if_neg hpe, mem_agreeFinset, ← chalOf_coe r ⟨j, hj⟩]
    exact hag
  calc uniformProb (Fin v → F) (AdaptiveAcceptsFalse prover honest H S)
      ≤ uniformProb (Fin v → F)
          (fun r => ∃ i : Fin v, r i ∈ launderSet prover honest r i) :=
        uniformProb_mono hstep
    _ ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
        adaptiveUnionBound_holds (fun r i => launderSet prover honest r i)
          (fun i r r' hpre => launderSet_prefixMeas hpm hhm i r r' hpre)
          (fun r i => launderSet_card_le hProverDeg hHonestDeg r i)

omit [DecidableEq ι] in
/-- **Adaptive retirement.** The retirement theorem in the shape a real
multi-round honest prover (the MLE round polynomials of `[SC-reshape]`)
inhabits: prefix-dependent round polynomials, truth chain anchored at the
constraint's actual pairing, violation caught except with probability
`v·d/|F|`. -/
theorem adaptive_sumcheck_retires_constraint {v d : ℕ}
    {prover honest : (ℕ → F) → ℕ → Polynomial F}
    {f : ι → F} {c : LinearConstraint ι F}
    (hviol : ¬ Satisfies f c)
    (hpm : PrefixMeasurable prover) (hhm : PrefixMeasurable honest)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ (χ : ℕ → F) (i : ℕ), i < v →
      (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ r : Fin v → F, ∀ i, i < v →
      (honest (chalOf r) i).eval 0 + (honest (chalOf r) i).eval 1
        = scChain (trueSum c f) (honest (chalOf r)) (chalOf r) i) :
    uniformProb (Fin v → F)
      (fun r => SumcheckAccepts (prover (chalOf r)) (honest (chalOf r))
        c.target (trueSum c f) r)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  have hne : c.target ≠ trueSum c f := by
    intro h
    apply hviol
    show dotWt c.wt f = c.target
    rw [← trueSum_eq_dotWt, h]
  have hconv : uniformProb (Fin v → F)
      (fun r => SumcheckAccepts (prover (chalOf r)) (honest (chalOf r))
        c.target (trueSum c f) r)
      = uniformProb (Fin v → F)
          (AdaptiveAcceptsFalse prover honest c.target (trueSum c f)) :=
    uniformProb_congr fun r => by
      unfold AdaptiveAcceptsFalse
      rw [acceptsFalse_iff_accepts]
      exact (and_iff_left hne).symm
  rw [hconv]
  exact adaptive_sumcheck_soundness hpm hhm hProverDeg hHonestDeg hHonest

/-! ## §6: the single sumcheck absorbs the whole constraint list

The accumulator carries a LIST of linear constraints on one word; the γ-batch
(`ConstrainedCode`, WHIR Constr. 5.5) collapses the list to ONE
`LinearConstraint`, hence — through the bridge — to ONE sum-claim. Stage 1 (the
γ round): a list-violating word's batch stays true for at most `(t−1)/|F|` of
uniform γ. Stage 2 (the sumcheck rounds): wherever the batch stays violated,
one sumcheck catches the word except with probability `v·d/|F|`. The two stages
are exactly the additive contributions to the RBR error ledger of §6. -/

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Completeness composition: a word satisfying the WHOLE list satisfies the
single γ-batched sum-claim, for every γ (reuse: `satisfies_batch_of_forall`
through the bridge). One sum-claim now carries the entire list. -/
theorem list_as_single_sumcheck (γ : F) {f : ι → F}
    {cs : List (LinearConstraint ι F)} (h : ∀ c ∈ cs, Satisfies f c) :
    ∑ i, constraintSummand (batchConstraint γ cs) f i
      = (batchConstraint γ cs).target :=
  (constraint_as_sumcheck f (batchConstraint γ cs)).mp
    (satisfies_batch_of_forall γ h)

omit [DecidableEq ι] in
/-- **Stage 1 (the γ round), probability form.** If the word violates SOME
constraint of the list, a uniform γ leaves the batched sum-claim TRUE with
probability `≤ (t−1)/|F|` — `card_batch_satisfying_le`'s root count rendered
through `uniformProb_mem_finset`. -/
theorem batch_survives_prob_le {f : ι → F} {cs : List (LinearConstraint ι F)}
    (h : ∃ c ∈ cs, ¬ Satisfies f c) :
    uniformProb F (fun γ => Satisfies f (batchConstraint γ cs))
      ≤ ((cs.length - 1 : ℕ) : ℝ) / Fintype.card F := by
  have hconv : uniformProb F (fun γ => Satisfies f (batchConstraint γ cs))
      = uniformProb F (fun γ =>
          γ ∈ Finset.univ.filter fun γ' : F =>
            Satisfies f (batchConstraint γ' cs)) :=
    uniformProb_congr fun γ => by simp
  rw [hconv, uniformProb_mem_finset]
  gcongr
  exact_mod_cast card_batch_satisfying_le h

omit [DecidableEq ι] in
/-- **Stage 2: one sumcheck retires the batched list.** For any γ at which the
batch stays violated (all but `≤ t−1` of them, by stage 1), the single sumcheck
on the batched sum-claim catches the word except with probability `v·d/|F|` —
§6's "the decider's single sumcheck absorbs the whole constraint list", with
the γ round and the sumcheck rounds contributing additively to the RBR
ledger. -/
theorem sumcheck_retires_batch {v d : ℕ} {prover honest : ℕ → Polynomial F}
    {f : ι → F} {cs : List (LinearConstraint ι F)} {γ : F}
    (hγ : ¬ Satisfies f (batchConstraint γ cs))
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1
        = scChain (trueSum (batchConstraint γ cs) f) honest (chalOf r) i) :
    uniformProb (Fin v → F)
      (SumcheckAccepts prover honest (batchConstraint γ cs).target
        (trueSum (batchConstraint γ cs) f))
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  sumcheck_retires_constraint hγ hProverDeg hHonestDeg hHonest

/-! ## Keystones over F₅ (ATLAS: satisfiable + teeth, BUILT)

`CRSExample`'s constraint `f(1) = 1` on the 4-point domain, its honest codeword
`xWord = (0,1,2,3)` and the violating zero word — now driven through the
sumcheck front. Everything computes on the actual data. -/

namespace SCRExample

open RSExample CRSExample

/-- **SATISFIABLE — the bridge computes.** The honest codeword's constraint
`f(1) = 1`, rendered AS the sumcheck sum-claim `Σ_i wt(i)·xWord(i) = 1`. -/
theorem xWord_sumClaim :
    ∑ i, constraintSummand evalC xWord i = evalC.target := by decide

/-- Round-trip through the bridge: the sum-claim IS the satisfaction. -/
example : Satisfies xWord evalC :=
  (constraint_as_sumcheck xWord evalC).mpr xWord_sumClaim

/-- The 4-point domain as the boolean square `{0,1}²`, explicitly: index `i`
maps to its bits. -/
def hyperIdx : Fin 4 ≃ (Fin 2 → Bool) where
  toFun i j := Nat.testBit i.val j.val
  invFun b := (if b 0 then 1 else 0) + if b 1 then 2 else 0
  left_inv i := by fin_cases i <;> decide
  right_inv b := by
    cases hb0 : b 0 <;> cases hb1 : b 1 <;> funext j <;> fin_cases j <;>
      simp [hb0, hb1] <;> decide

/-- **The claim object in hypercube shape, computed**: the same constraint as a
sum over `{0,1}²` — the domain the decider's sumcheck walks. -/
theorem xWord_hypercube_sumClaim :
    ∑ b : Fin 2 → Bool, constraintSummand evalC xWord (hyperIdx.symm b)
      = evalC.target := by decide

/-- The general reshaping lemma exercised on the concrete data. -/
example : Satisfies xWord evalC ↔
    ∑ b : Fin 2 → Bool, constraintSummand evalC xWord (hyperIdx.symm b)
      = evalC.target :=
  constraint_as_hypercube_sum hyperIdx xWord evalC

/-- The honest word is never falsely convicted: no sumcheck run on its claim
can be an `AcceptsFalse` event. -/
theorem xWord_never_caught {v : ℕ}
    (prover honest : ℕ → Polynomial (ZMod 5)) (r : Fin v → ZMod 5) :
    ¬ AcceptsFalse prover honest evalC.target (trueSum evalC xWord) r :=
  satisfies_not_acceptsFalse (by decide) r

/-- The violating word's TRUE total: the zero word sums to `0` against the
constraint's weight — while the constraint claims `1`. -/
theorem zero_trueSum : trueSum evalC (0 : Fin 4 → ZMod 5) = 0 := by decide

/-- **TEETH — the retirement bound FIRES.** One-round sumcheck on the zero
word's claim (claimed total `1`, true total `0`): the cheating prover sends
`g̃ = X`, which passes the round check `g̃(0) + g̃(1) = 1`; the retirement theorem
delivers `Pr[accept] ≤ 1/5` with every hypothesis discharged concretely. -/
theorem zero_word_caught :
    uniformProb (Fin 1 → ZMod 5)
      (SumcheckAccepts (fun _ => (X : Polynomial (ZMod 5))) (fun _ => 0)
        evalC.target (trueSum evalC (0 : Fin 4 → ZMod 5)))
      ≤ 1 / 5 := by
  have h := sumcheck_retires_constraint (v := 1) (d := 1)
    (prover := fun _ => (X : Polynomial (ZMod 5))) (honest := fun _ => 0)
    zero_not_satisfies
    (fun i _ => by rw [Polynomial.degree_X]; decide)
    (fun i _ => by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (fun r i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      simp [scChain, zero_trueSum])
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- The caught-event is NONEMPTY: at challenge `r = 0` the cheating run is
accepted (`g̃(0) = 0` matches the truth — the lie is laundered at the root), so
the `1/5` bound constrains a real event, not a vacuum. -/
theorem zero_word_accept_witness :
    SumcheckAccepts (v := 1) (fun _ => (X : Polynomial (ZMod 5))) (fun _ => 0)
      evalC.target (trueSum evalC (0 : Fin 4 → ZMod 5)) (fun _ => 0) := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp [scChain, evalC, evalConstraint]
  · simp [scChain, chalOf]

/-- The adaptive packaging fires on the same data (constant-in-prefix
messages are trivially prefix-measurable). -/
theorem adaptive_bound_fires :
    uniformProb (Fin 1 → ZMod 5)
      (AdaptiveAcceptsFalse (fun _ _ => (X : Polynomial (ZMod 5)))
        (fun _ _ => 0) evalC.target (trueSum evalC (0 : Fin 4 → ZMod 5)))
      ≤ 1 / 5 := by
  have h := adaptive_sumcheck_soundness (v := 1) (d := 1)
    (prover := fun _ _ => (X : Polynomial (ZMod 5))) (honest := fun _ _ => 0)
    (H := evalC.target) (S := trueSum evalC (0 : Fin 4 → ZMod 5))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun χ i _ => by rw [Polynomial.degree_X]; decide)
    (fun χ i _ => by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (fun r i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      simp [scChain, zero_trueSum])
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- The adaptive event is inhabited by the SAME witness (`r = 0` launders the
same lie), so `adaptive_bound_fires` also constrains a nonempty event. -/
example : AdaptiveAcceptsFalse (v := 1) (fun _ _ => (X : Polynomial (ZMod 5)))
    (fun _ _ => 0) evalC.target (trueSum evalC (0 : Fin 4 → ZMod 5))
    (fun _ => 0) :=
  ⟨zero_word_accept_witness.1, zero_word_accept_witness.2, by decide⟩

end SCRExample

end Minidregg.Selvage
