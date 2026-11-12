/-
# Selvage.LogupStar -- the characteristic-independent algebraic core of LogUp*

This module formalizes the exact pushforward identity used by LogUp* lookup
arguments (Soukhanov, ePrint 2025/946) and by the current Binius64 design.  It
is a **committed-pushforward integrity kernel, not a complete lookup-soundness
theorem**.  The protocol order that makes its random challenges load-bearing
is:

1. bind the trace and the looker addresses;
2. sample the fresh MLE evaluation point `r`, which fixes the equality weights
   `X` and tests the pulled-table relation;
3. sample `gamma` only to batch the resulting looker claims;
4. commit the resulting table-side pushforward `Y`;
5. only then sample the logarithmic-derivative challenge `c`.

Batching is deliberately not modeled here.  Once `X`, `I`, and the committed
`Y` are fixed, the algebra below is characteristic-independent: it applies to
prime fields, extension fields, and binary tower fields without modification.

The integrity theorem is honest about its algebraic premise.  A `Y` different
from the pushforward of the already-fixed `I,X` makes the cross-multiplied
rational identity a nonzero polynomial; root counting then prices the fresh
`c`.  Denominator poles are counted separately rather than silently excluded
from the sample space.

Two lookup obligations are intentionally outside this API and should remain
separate.  `[LOGUP-ADDRESS-LINK]` proves that `I` is the canonical, authorized
index decoded from the committed address expression.  The ordinary upstream
`[LOGUP-PULLBACK-SOUND]` MLE argument proves that a false pulled-table relation
is detected at the fresh evaluation point `r`; `gamma` merely batches multiple
looker claims and receives the usual batching root bound.  This module begins
after those bridges: it conditions on the resulting fixed `I,X`, proves the
committed `Y` is their exact pushforward except for the priced `c` roots, and
makes no standalone claim about address decoding or MLE evaluation soundness.

In particular, an indexed lookup specified by `I : κ → ι` does **not** need a
separate Eagen--Haböck-style count argument after `I` has been linked.  The
characteristic-two parity trap belongs to a different primitive: unindexed
multiset membership encoded by plain per-row multiplicities, where two unit
hits satisfy `1 + 1 = 0`.  If that alternative primitive is added, it needs
per-row algebraic units (or another noncancelling multiplicity encoding).  That
requirement is not part of this indexed pushforward theorem.
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Selvage.Sumcheck

namespace Minidregg.Selvage

open Polynomial

section Pushforward

variable {F : Type*} [Field F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

/-- Push looker weights through their table indices. -/
noncomputable def logupPushforward (I : κ → ι) (X : κ → F) : ι → F :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => I i = j), X i

/-- The finite dot product spelling used by the lookup relation. -/
noncomputable def logupDot {α : Type*} [Fintype α]
    (a b : α → F) : F :=
  ∑ i, a i * b i

/-- Pullback/pushforward duality: querying the table after `I` against looker
weights is exactly querying the table against the pushed-forward weights. -/
theorem logup_pullback_pushforward (I : κ → ι) (X : κ → F) (T : ι → F) :
    logupDot (fun i => T (I i)) X =
      logupDot T (logupPushforward I X) := by
  classical
  unfold logupDot logupPushforward
  rw [← Finset.sum_fiberwise (s := Finset.univ) I
    (fun i => T (I i) * X i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Fixed-challenge logarithmic derivative.  The denominator side condition is
not baked into the definition; every theorem that divides states it. -/
noncomputable def logupLogDerivative (J : ι → F) (W : ι → F) (c : F) : F :=
  ∑ j, W j / (c - J j)

/-- **Completeness at a fixed challenge.** The looker-side logarithmic
derivative is exactly the table-side logarithmic derivative of the
pushforward.  The proof is just pullback/pushforward duality; it uses no
characteristic assumption. -/
theorem logup_logDerivative_complete (J : ι → F) (I : κ → ι)
    (X : κ → F) (c : F) (_hc : ∀ j, c - J j ≠ 0) :
    (∑ i, X i / (c - J (I i))) =
      logupLogDerivative J (logupPushforward I X) c := by
  classical
  have h := logup_pullback_pushforward (I := I) (X := X)
    (T := fun j => (c - J j)⁻¹)
  simpa [logupDot, logupLogDerivative, div_eq_mul_inv, mul_comm] using h

end Pushforward

section DefectPolynomial

variable {F : Type} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of every logarithmic-derivative denominator. -/
noncomputable def logupDenominator (J : ι → F) : F[X] :=
  ∏ j, (Polynomial.X - Polynomial.C (J j))

/-- The Lagrange numerator factor obtained by removing table row `j`. -/
noncomputable def logupCofactor (J : ι → F) (j : ι) : F[X] :=
  ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (J k))

/-- The cross-multiplied polynomial for a claimed table multiplicity `claimed`
against the correct one `expected`. -/
noncomputable def logupDefect (J : ι → F)
    (expected claimed : ι → F) : F[X] :=
  ∑ j, Polynomial.C (claimed j - expected j) * logupCofactor J j

omit [DecidableEq ι] in
@[simp] theorem logupDenominator_eval (J : ι → F) (c : F) :
    (logupDenominator J).eval c = ∏ j, (c - J j) := by
  classical
  simp only [logupDenominator, eval_prod, eval_sub, eval_X, eval_C]

@[simp] theorem logupCofactor_eval (J : ι → F) (j : ι) (c : F) :
    (logupCofactor J j).eval c =
      ∏ k ∈ Finset.univ.erase j, (c - J k) := by
  classical
  simp only [logupCofactor, eval_prod, eval_sub, eval_X, eval_C]

@[simp] theorem logupDefect_eval (J : ι → F)
    (expected claimed : ι → F) (c : F) :
    (logupDefect J expected claimed).eval c =
      ∑ j, (claimed j - expected j) *
        ∏ k ∈ Finset.univ.erase j, (c - J k) := by
  classical
  rw [logupDefect, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_C, logupCofactor_eval]

/-- Clearing all denominators turns the rational discrepancy into evaluation
of `logupDefect`. -/
theorem logupDenominator_mul_rational_sub (J : ι → F)
    (expected claimed : ι → F) (c : F) (hc : ∀ j, c - J j ≠ 0) :
    (logupDenominator J).eval c *
        (logupLogDerivative J claimed c - logupLogDerivative J expected c) =
      (logupDefect J expected claimed).eval c := by
  classical
  rw [logupDenominator_eval, logupDefect_eval]
  simp only [logupLogDerivative, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sub_div]
  have hsplit : (∏ k, (c - J k)) =
      (c - J j) * ∏ k ∈ Finset.univ.erase j, (c - J k) := by
    simpa [mul_comm] using
      (Finset.mul_prod_erase (Finset.univ : Finset ι)
        (fun k => c - J k) (Finset.mem_univ j)).symm
  rw [hsplit]
  field_simp [hc j]

/-- Away from poles, the rational equality is exactly the polynomial root
test. -/
theorem logup_rational_eq_iff_defect_eval_eq_zero (J : ι → F)
    (expected claimed : ι → F) (c : F) (hc : ∀ j, c - J j ≠ 0) :
    logupLogDerivative J claimed c = logupLogDerivative J expected c ↔
      (logupDefect J expected claimed).eval c = 0 := by
  rw [← logupDenominator_mul_rational_sub J expected claimed c hc]
  have hden : (logupDenominator J).eval c ≠ 0 := by
    rw [logupDenominator_eval]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hc j
  rw [mul_eq_zero, or_iff_right hden, sub_eq_zero]

/-- Evaluating a cofactor at its own injective table point is nonzero. -/
theorem logupCofactor_eval_self_ne_zero (J : ι → F)
    (hJ : Function.Injective J) (j : ι) :
    (logupCofactor J j).eval (J j) ≠ 0 := by
  classical
  rw [logupCofactor_eval]
  exact Finset.prod_ne_zero_iff.mpr fun k hk => by
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact sub_ne_zero.mpr (hJ.ne hkj.symm)

/-- Every other cofactor vanishes at `J j`. -/
theorem logupCofactor_eval_other (J : ι → F) {j k : ι} (hjk : j ≠ k) :
    (logupCofactor J k).eval (J j) = 0 := by
  classical
  rw [logupCofactor_eval]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)
  simp

/-- **Wrong pushforward gives a nonzero polynomial.** Injectivity of the table
embedding is the only structural premise: evaluate at a row where the claimed
and expected multiplicities differ. -/
theorem logupDefect_ne_zero_of_ne (J : ι → F) (hJ : Function.Injective J)
    {expected claimed : ι → F} (hne : claimed ≠ expected) :
    logupDefect J expected claimed ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, claimed j ≠ expected j := by
    by_contra h
    push Not at h
    exact hne (funext h)
  intro hzero
  have heval : (logupDefect J expected claimed).eval (J j) = 0 := by rw [hzero]; simp
  rw [logupDefect_eval] at heval
  have hsingle :
      (∑ k, (claimed k - expected k) *
        ∏ l ∈ Finset.univ.erase k, (J j - J l)) =
      (claimed j - expected j) *
        ∏ l ∈ Finset.univ.erase j, (J j - J l) := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := j) (s := Finset.univ.erase k)
        (Finset.mem_erase.mpr ⟨hkj.symm, Finset.mem_univ j⟩)
      simp
    · simp
  rw [hsingle] at heval
  have hcself := logupCofactor_eval_self_ne_zero J hJ j
  rw [logupCofactor_eval] at hcself
  exact mul_ne_zero (sub_ne_zero.mpr hj) hcself heval

/-- The defect degree is at most `|ι|-1`.  For an empty table the sum is zero
and the truncated subtraction gives the correct bound `0`. -/
theorem logupDefect_natDegree_le (J : ι → F)
    (expected claimed : ι → F) :
    (logupDefect J expected claimed).natDegree ≤ Fintype.card ι - 1 := by
  classical
  unfold logupDefect logupCofactor
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, Nat.zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hfactor : ∀ k ∈ Finset.univ.erase j,
      (Polynomial.X - Polynomial.C (J k)).natDegree ≤ 1 := by
    intro k hk
    rw [Polynomial.natDegree_X_sub_C]
  calc
    ∑ k ∈ Finset.univ.erase j,
        (Polynomial.X - Polynomial.C (J k)).natDegree
        ≤ ∑ k ∈ Finset.univ.erase j, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hfactor k hk
    _ = (Finset.univ.erase j).card := by simp
    _ = Fintype.card ι - 1 := by simp

/-- A nonzero degree-`d` polynomial vanishes on at most `d` uniform field
challenges. -/
theorem uniformProb_poly_eval_eq_zero_le [Fintype F] (p : F[X])
    (hp : p ≠ 0) {d : ℕ} (hdeg : p.natDegree ≤ d) :
    uniformProb F (fun c => p.eval c = 0) ≤
      (d : ℝ) / Fintype.card F := by
  classical
  unfold uniformProb
  have hsub : (Finset.univ.filter fun c : F => p.eval c = 0).val ⊆ p.roots := by
    intro c hc
    rw [Finset.mem_val, Finset.mem_filter] at hc
    rw [Polynomial.mem_roots hp]
    exact hc.2
  have hcard : (Finset.univ.filter fun c : F => p.eval c = 0).card ≤ d :=
    le_trans (Polynomial.card_le_degree_of_subset_roots hsub) hdeg
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  gcongr

/-- A wrong committed pushforward passes the fresh non-pole challenge with
probability at most `(|ι|-1)/|F|`. -/
theorem logup_wrong_rational_accept_prob_le [Fintype F]
    (J : ι → F) (hJ : Function.Injective J)
    {expected claimed : ι → F} (hne : claimed ≠ expected) :
    uniformProb F (fun c =>
      (∀ j, c - J j ≠ 0) ∧
      logupLogDerivative J claimed c = logupLogDerivative J expected c) ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) / Fintype.card F := by
  refine le_trans (uniformProb_mono fun c hc =>
    (logup_rational_eq_iff_defect_eval_eq_zero J expected claimed c hc.1).mp hc.2) ?_
  exact uniformProb_poly_eval_eq_zero_le _
    (logupDefect_ne_zero_of_ne J hJ hne)
    (logupDefect_natDegree_le J expected claimed)

omit [DecidableEq ι] in
/-- Denominator poles are exactly table points, hence contribute at most
`|ι|/|F|` even before using injectivity. -/
theorem logup_denominator_zero_prob_le [Fintype F] (J : ι → F) :
    uniformProb F (fun c => ∃ j, c - J j = 0) ≤
      (Fintype.card ι : ℝ) / Fintype.card F := by
  classical
  calc
    uniformProb F (fun c => ∃ j, c - J j = 0)
        ≤ uniformProb F (fun c => c ∈ Finset.univ.image J) :=
          uniformProb_mono fun c hc => by
            obtain ⟨j, hj⟩ := hc
            rw [sub_eq_zero] at hj
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
    _ = ((Finset.univ.image J).card : ℝ) / Fintype.card F :=
      uniformProb_mem_finset _
    _ ≤ (Fintype.card ι : ℝ) / Fintype.card F := by
      gcongr
      exact_mod_cast Finset.card_image_le

/-- Conservative total bad-challenge price: poles plus roots of the wrong
cross-multiplied identity. -/
theorem logup_wrong_or_pole_prob_le [Fintype F]
    (J : ι → F) (hJ : Function.Injective J)
    {expected claimed : ι → F} (hne : claimed ≠ expected) :
    uniformProb F (fun c =>
      (∃ j, c - J j = 0) ∨
      (logupDefect J expected claimed).eval c = 0) ≤
      ((Fintype.card ι : ℕ) : ℝ) / Fintype.card F +
      ((Fintype.card ι - 1 : ℕ) : ℝ) / Fintype.card F := by
  refine le_trans (uniformProb_or_le _ _) ?_
  gcongr
  · exact logup_denominator_zero_prob_le J
  · exact uniformProb_poly_eval_eq_zero_le _
      (logupDefect_ne_zero_of_ne J hJ hne)
      (logupDefect_natDegree_le J expected claimed)

end DefectPolynomial

/-! ## A concrete F5 tooth -/

namespace LogupStarExample

/-- Three lookers hit table rows `0,1,0` with weights `1,2,3`. -/
def I : Fin 3 → Fin 2 := ![0, 1, 0]
def X : Fin 3 → ZMod 5 := ![1, 2, 3]
def J : Fin 2 → ZMod 5 := ![0, 1]
def correctY : Fin 2 → ZMod 5 := ![4, 2]
def wrongY : Fin 2 → ZMod 5 := ![0, 2]

theorem pushforward_is_correct :
    logupPushforward I X = correctY := by
  funext j
  fin_cases j <;> rw [logupPushforward] <;> decide

theorem complete_at_two :
    (∑ i, X i / ((2 : ZMod 5) - J (I i))) =
      logupLogDerivative J correctY 2 := by
  rw [← pushforward_is_correct]
  apply logup_logDerivative_complete
  intro j
  fin_cases j <;> decide

/-- **TEETH:** changing the multiplicity of row zero is rejected at the
non-pole challenge `c=2`. -/
theorem wrong_rejected_at_two :
    logupLogDerivative J wrongY 2 ≠ logupLogDerivative J correctY 2 := by
  norm_num [logupLogDerivative, J, wrongY, correctY]
  decide

theorem wrong_defect_nonzero :
    logupDefect J correctY wrongY ≠ 0 := by
  apply logupDefect_ne_zero_of_ne J
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [J]
  · decide

end LogupStarExample

/-- info: 'Minidregg.Selvage.logup_pullback_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logup_pullback_pushforward
/-- info: 'Minidregg.Selvage.logup_logDerivative_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logup_logDerivative_complete
/-- info: 'Minidregg.Selvage.logupDefect_ne_zero_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logupDefect_ne_zero_of_ne
/-- info: 'Minidregg.Selvage.logup_wrong_rational_accept_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logup_wrong_rational_accept_prob_le
/-- info: 'Minidregg.Selvage.LogupStarExample.wrong_rejected_at_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LogupStarExample.wrong_rejected_at_two

end Minidregg.Selvage
