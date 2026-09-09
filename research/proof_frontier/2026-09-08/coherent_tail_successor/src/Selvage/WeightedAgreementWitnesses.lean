/- Nonconstant real weights, genuinely far coefficients and real good
scalars. Existing finite curve teeth are reused; no enumeration campaign. -/
import Selvage.CurveWeightedAgreement
import Selvage.CurveFullUDTeeth

namespace Minidregg.Selvage.WeightedAgreementWitnesses
open CurveDegreeTeeth
open scoped BigOperators Classical

/-- Both coordinates carry positive but unequal consistency weights. -/
noncomputable def weight : Fin 2 → ℝ := ![1,4/5]

theorem weight_bounds : (∀ i, 0 ≤ weight i) ∧ (∀ i, weight i ≤ 1) := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [weight]

theorem weight_nonconstant : weight 0 ≠ weight 1 := by norm_num [weight]

theorem weight_mass : consistencyMass weight Finset.univ = 9/5 := by
  norm_num [consistencyMass,weight,Fin.sum_univ_succ]

/-- The existing non-codeword coefficient family remains weighted-far. -/
theorem weighted_far : ¬WeightedCorrelatedAgreement (reedSolomonCode dom 1) (1/5:ℝ) weight words := by
  intro h
  exact no_correlated_agreement (weightedCA_to_CA _ _ weight weight_bounds.2 words h)

/-- Three actual scalars have weighted codeword agreement despite the far family. -/
theorem three_weighted_good (z : ZMod 17) (hz : z ∈ ({0,1,2}:Finset (ZMod 17))) :
    WeightedClose (reedSolomonCode dom 1) (1/5:ℝ) weight (curveWord words z) := by
  rw [curve_at_three_roots z hz]
  exact ⟨Finset.univ,by norm_num [weight_mass],0,(reedSolomonCode dom 1).zero_mem,fun _ _ => rfl⟩

/-- All field/radius/weight/farness premises fire on this genuine nonempty bad event. -/
theorem weighted_bound_fires :
    uniformProb (ZMod 17) (fun z => WeightedClose (reedSolomonCode dom 1) (1/5:ℝ)
      weight (curveWord words z)) ≤ 14/17 := by
  have h := curve_weighted_uniform_sound 7 (by decide) dom (d := 1) (by decide)
    (θ := 1/5) (by norm_num) (by norm_num) weight weight_bounds.2 words weighted_far
  norm_num at h ⊢
  exact h

/-- Legal zero coefficients have a weighted common agreement set at this threshold. -/
theorem zero_common (M : ℕ) :
    WeightedCorrelatedAgreement (reedSolomonCode dom 1) (1/5:ℝ) weight
      (fun _ : Fin (M+1) => (0 : Fin 2 → ZMod 17)) :=
  ⟨Finset.univ,by norm_num [weight_mass],fun _ =>
    ⟨0,(reedSolomonCode dom 1).zero_mem,fun _ _ => rfl⟩⟩

/-- Values above one break the density domination used by the reduction. -/
theorem overweight_density_falsifier :
    (1:ℝ) < consistencyMass (fun _ : Fin 2 => (2:ℝ)) {0} ∧
    (consistencyMass (fun _ : Fin 2 => (2:ℝ)) {0}) > (({0}:Finset (Fin 2)).card:ℝ) := by
  norm_num [consistencyMass]

/-- Coherent round disagreements may be the SAME set. Summing their
marginal rejection probabilities would double-count it. -/
theorem overlapping_marginals_falsifier :
    (({0}:Finset (Fin 2)) ∪ {0}).card < ({0}:Finset (Fin 2)).card+({0}:Finset (Fin 2)).card := by decide

end Minidregg.Selvage.WeightedAgreementWitnesses

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.weight_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.weight_bounds

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.weight_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.weight_nonconstant

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.weight_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.weight_mass

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.weighted_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.weighted_far

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.three_weighted_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.three_weighted_good

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.weighted_bound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.weighted_bound_fires

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.zero_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.zero_common

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.overweight_density_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.overweight_density_falsifier

/-- info: 'Minidregg.Selvage.WeightedAgreementWitnesses.overlapping_marginals_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.WeightedAgreementWitnesses.overlapping_marginals_falsifier
