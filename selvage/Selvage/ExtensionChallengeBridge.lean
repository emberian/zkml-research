/-
# Selvage.ExtensionChallengeBridge — base commitments, extension challenges

`SmallField` already proves that base-field Reed--Solomon words lift to an
extension field without changing their degree.  This file closes the analogous
constraint seam needed by the runtime: lift each base-field weight and target,
then batch the resulting constraints with an extension-field γ.

The key executable identity is `lifted_constraint_residual`: materializing a
gate residual in the base field and embedding that scalar is exactly the same
as evaluating the lifted constraint on the lifted word.  Consequently the
existing root-counting theorem applies over the extension cardinality without
rewriting the batching or sumcheck theory.
-/

import Selvage.ConstrainedCode
import Selvage.SmallField

namespace Minidregg.Selvage

variable {ι Fq K : Type*} [Fintype ι]
variable [Field Fq] [Field K] [Algebra Fq K]

/-- Lift one linear constraint coefficientwise into the challenge field. -/
def liftConstraint (c : LinearConstraint ι Fq) : LinearConstraint ι K where
  wt := liftWord c.wt
  target := algebraMap Fq K c.target

omit [Fintype ι] in
@[simp] theorem liftConstraint_wt (c : LinearConstraint ι Fq) :
    (liftConstraint (K := K) c).wt = liftWord c.wt := rfl

omit [Fintype ι] in
@[simp] theorem liftConstraint_target (c : LinearConstraint ι Fq) :
    (liftConstraint (K := K) c).target = algebraMap Fq K c.target := rfl

/-- Pairing two lifted base vectors commutes with the base-field embedding. -/
theorem dotWt_liftWord (a f : ι → Fq) :
    dotWt (liftWord (K := K) a) (liftWord (K := K) f) =
      algebraMap Fq K (dotWt a f) := by
  simp [dotWt, liftWord, map_sum]

/-- A base word satisfies a constraint exactly when its lift satisfies the
lifted constraint. -/
theorem satisfies_liftConstraint_iff (f : ι → Fq) (c : LinearConstraint ι Fq) :
    Satisfies (liftWord (K := K) f) (liftConstraint (K := K) c) ↔
      Satisfies f c := by
  unfold Satisfies
  rw [liftConstraint_wt, liftConstraint_target, dotWt_liftWord]
  exact (algebraMap Fq K).injective.eq_iff

/-- **Runtime bridge:** computing a residual in BabyBear and then embedding it
is identical to evaluating the lifted constraint over the extension. -/
theorem lifted_constraint_residual (f : ι → Fq) (c : LinearConstraint ι Fq) :
    dotWt (liftConstraint (K := K) c).wt (liftWord (K := K) f) -
        (liftConstraint (K := K) c).target =
      algebraMap Fq K (dotWt c.wt f - c.target) := by
  rw [liftConstraint_wt, liftConstraint_target, dotWt_liftWord, map_sub]

/-- Violating one base constraint produces a violation in the mapped list. -/
theorem exists_lifted_violation {f : ι → Fq} {cs : List (LinearConstraint ι Fq)}
    (h : ∃ c ∈ cs, ¬Satisfies f c) :
    ∃ c ∈ cs.map (liftConstraint (K := K)),
      ¬Satisfies (liftWord (K := K) f) c := by
  obtain ⟨c, hc, hviol⟩ := h
  refine ⟨liftConstraint (K := K) c, List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
  simpa [satisfies_liftConstraint_iff] using hviol

/-- **Extension-field γ-batching soundness.**  If a base word violates some
base constraint, at most `t-1` of the `|K|` extension challenges make the
coefficientwise-lifted batch pass.  This is the existing root-count theorem,
instantiated after the exact base-to-extension bridge above. -/
theorem card_lifted_batch_satisfying_le [Fintype K] [DecidableEq K]
    {f : ι → Fq} {cs : List (LinearConstraint ι Fq)}
    (h : ∃ c ∈ cs, ¬Satisfies f c) :
    (Finset.univ.filter fun γ : K =>
      Satisfies (liftWord (K := K) f)
        (batchConstraint γ (cs.map (liftConstraint (K := K))))).card ≤
      cs.length - 1 := by
  simpa using card_batch_satisfying_le (exists_lifted_violation (K := K) h)

#check @dotWt_liftWord
#check @satisfies_liftConstraint_iff
#check @lifted_constraint_residual
#check @card_lifted_batch_satisfying_le

/-- info: 'Minidregg.Selvage.card_lifted_batch_satisfying_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_lifted_batch_satisfying_le

end Minidregg.Selvage
