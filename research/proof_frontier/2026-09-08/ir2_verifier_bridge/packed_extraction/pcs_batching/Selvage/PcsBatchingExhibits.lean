/- Small nonzero premise inhabitation and orthogonal degree/denominator controls.
The full-UD theorem fires here; no large actual-field polynomial is enumerated. -/
import Selvage.PcsBatchingFullUD

namespace Minidregg.Selvage.PcsBatching.Exhibits
open Polynomial
open scoped Classical
noncomputable section
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

abbrev F := ZMod 101
abbrev dom := CurveFullUDWitness.dom

def constantData : Data F (Fin 5) (Fin 1) 2 where
  column _ := 0
  source _ _ := 3
  point _ := 10
  claim _ := 3

def wrongData : Data F (Fin 5) (Fin 1) 2 := {constantData with claim := fun _ => 4}

def NonzeroAccepted : Prop :=
  constantData.OffDomain dom 1 ∧
  constantData.source 0 0 ≠ 0 ∧
  constantData.JointCard dom 1 2 1

theorem constant_offDomain : constantData.OffDomain dom 1 := by
  intro j i
  fin_cases i <;> norm_num [constantData,dom,CurveFullUDWitness.dom,F] <;> decide

theorem nonzeroAccepted : NonzeroAccepted := by
  refine ⟨constant_offDomain,by decide,?_⟩
  apply jointCard_of_many_close constantData dom 1 one_ne_zero (by decide) (by decide)
    (by decide) (by decide) constant_offDomain Finset.univ
  · intro α _
    refine ⟨0,(reedSolomonCode dom 2).zero_mem,?_⟩
    have hzero : curveWord (constantData.quotientWord dom 1) α=0 := by
      funext i
      simp [curveWord,comb,Data.quotientWord,constantData]
    rw [hzero]
    simp
  · decide

/-- The counted false-claim theorem fires over101 alphas with a nonzero
constant source; its10-element upper bound is strictly below the field size. -/
theorem wrong_claim_bad_alpha :
    (Finset.univ.filter (fun α : F => close (1/5:ℝ) (reedSolomonCode dom 2)
      (curveWord (wrongData.quotientWord dom 1) α))).card ≤ 10 := by
  have h := bad_alpha_card_of_wrong_claim wrongData dom 1 one_ne_zero
    (by decide) (by decide) (by norm_num : (0:ℝ)<1/5)
    (by norm_num : (2:ℝ)<(1-2*(1/5:ℝ))*(Fintype.card (Fin 5) : ℝ))
    constant_offDomain (fun _ => (C 3 : F[X]))
    (by intro k; simp) (by intro k i; simp [wrongData,constantData]) 0 (by norm_num [wrongData,constantData,F]; decide)
  exact h

/-- Quotient degree0 really reconstructs degree1. Replacing ≤d by <d
without a further source argument would be false, even for this one term. -/
def DegreeLossFalsifier : Prop :=
  (liftQuotient (1 : F) 0 0 1).natDegree=1 ∧
  ¬(liftQuotient (1 : F) 0 0 1).degree < (1 : WithBot ℕ)

theorem degreeLossFalsifier : DegreeLossFalsifier := by
  norm_num [DegreeLossFalsifier,liftQuotient]

/-- At an on-domain opening point, field division by zero erases a false
claim. The off-domain hypothesis has an independent, necessary role. -/
def ZeroDenominatorFalsifier : Prop :=
  ((1-0)/(0-0) : F)=0 ∧ (1 : F) ≠ 0

theorem zeroDenominatorFalsifier : ZeroDenominatorFalsifier := by
  norm_num [ZeroDenominatorFalsifier]

/- Exact dependencies of every theorem in this module. -/

/-- info: 'Minidregg.Selvage.PcsBatching.Exhibits.constant_offDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.Exhibits.constant_offDomain

/-- info: 'Minidregg.Selvage.PcsBatching.Exhibits.nonzeroAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.Exhibits.nonzeroAccepted

/-- info: 'Minidregg.Selvage.PcsBatching.Exhibits.wrong_claim_bad_alpha' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.Exhibits.wrong_claim_bad_alpha

/-- info: 'Minidregg.Selvage.PcsBatching.Exhibits.degreeLossFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.Exhibits.degreeLossFalsifier

/-- info: 'Minidregg.Selvage.PcsBatching.Exhibits.zeroDenominatorFalsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PcsBatching.Exhibits.zeroDenominatorFalsifier

end
end Minidregg.Selvage.PcsBatching.Exhibits
