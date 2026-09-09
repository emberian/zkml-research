/- Real-weight correlated agreement, derived from the existing mutual-CA
full-UD theorem. Source orientation: S-two2026/532 Thm29 and Remark30.
No new matrix/gluing argument or Reed–Solomon semantics are introduced. -/
import Selvage.CurveProximityGapFullUD
import Selvage.Depth

namespace Minidregg.Selvage
open scoped BigOperators Classical
variable {ι F : Type} [Fintype ι] [Field F] [DecidableEq F] {M : ℕ}

/-- Unnormalized consistency mass. Dividing by card ι gives the paper's measure. -/
def consistencyMass (weight : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, weight i

/-- Weighted agreement with some codeword; caller-selected sets are retained. -/
def WeightedClose (C : Submodule F (ι → F)) (θ : ℝ) (weight : ι → ℝ) (f : ι → F) : Prop :=
  ∃ S : Finset ι, (1-θ)*(Fintype.card ι:ℝ) ≤ consistencyMass weight S ∧
    ∃ v ∈ C, AgreesOn S f v

def WeightedCorrelatedAgreement {ℓ : ℕ} (C : Submodule F (ι → F)) (θ : ℝ)
    (weight : ι → ℝ) (u : Fin ℓ → ι → F) : Prop :=
  ∃ S : Finset ι, (1-θ)*(Fintype.card ι:ℝ) ≤ consistencyMass weight S ∧
    ∀ j, ∃ v ∈ C, AgreesOn S (u j) v

omit [Fintype ι] [Field F] [DecidableEq F] in
/-- Subprobability weights are dominated by ordinary set cardinality. -/
theorem consistencyMass_le_card (weight : ι → ℝ) (hle : ∀ i, weight i ≤ 1) (S : Finset ι) :
    consistencyMass weight S ≤ (S.card:ℝ) := by
  calc
    _ ≤ ∑ _i ∈ S, (1:ℝ) := Finset.sum_le_sum (fun i _ => hle i)
    _ = _ := by simp

omit [Fintype ι] [Field F] [DecidableEq F] in
theorem consistencyMass_nonneg (weight : ι → ℝ) (h0 : ∀ i, 0 ≤ weight i) (S : Finset ι) :
    0 ≤ consistencyMass weight S := Finset.sum_nonneg (fun i _ => h0 i)

omit [Fintype ι] [Field F] [DecidableEq F] in
theorem consistencyMass_mono (weight : ι → ℝ) (h0 : ∀ i, 0 ≤ weight i)
    {S T : Finset ι} (hST : S ⊆ T) : consistencyMass weight S ≤ consistencyMass weight T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => h0 i)

omit [DecidableEq F] in
/-- Negating weighted CA turns a weighted close point into the EXISTING
mutual-CA failure event on the SAME agreement set. -/
theorem weightedClose_mutualFailure (C : Submodule F (ι → F)) (θ : ℝ)
    (weight : ι → ℝ) (hle : ∀ i, weight i ≤ 1) (u : Fin (M+1) → ι → F)
    (hfar : ¬WeightedCorrelatedAgreement C θ weight u) (r : Fin (M+1) → F)
    (hc : WeightedClose C θ weight (comb r u)) : MutualCAFailure C θ u r := by
  obtain ⟨S,hS,hc⟩ := hc
  refine ⟨S,hS.trans (consistencyMass_le_card weight hle S),hc,?_⟩
  by_contra hn
  push Not at hn
  exact hfar ⟨S,hS,hn⟩

omit [DecidableEq F] in
/-- Uniform scalar coins exactly realize the geometric generator for any event. -/
theorem geometric_pr_uniform [Fintype F] (M : ℕ) (E : (Fin (M+1) → F) → Prop) :
    (geometricGenerator F M).pr E = uniformProb F (fun z => E (fun j => z^j.val)) := by
  unfold ProximityGenerator.pr
  change (∑ _z ∈ Finset.univ.filter (fun z : F => E (fun j => z^j.val)),
    (Fintype.card F:ℝ)⁻¹) = _
  rw [Finset.sum_const,nsmul_eq_mul]
  unfold uniformProb
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,div_eq_mul_inv]


omit [DecidableEq F] in
/-- Weighted agreement also supplies ordinary agreement whenever weights≤1. -/
theorem weightedCA_to_CA {ℓ : ℕ} (C : Submodule F (ι → F)) (θ : ℝ)
    (weight : ι → ℝ) (hle : ∀ i, weight i ≤ 1) (u : Fin ℓ → ι → F)
    (h : WeightedCorrelatedAgreement C θ weight u) : CorrelatedAgreement C θ u := by
  obtain ⟨S,hS,hw⟩ := h
  exact ⟨S,hS.trans (consistencyMass_le_card weight hle S),hw⟩

/-- Existing full UD supplies real-weight curve soundness at the SAME M*n/|F|
error, for weights fixed before the one scalar challenge. -/
theorem curve_weighted_uniform_sound [Nonempty ι] [Fintype F]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {θ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι:ℝ))
    (weight : ι → ℝ) (hle : ∀ i, weight i ≤ 1) (u : Fin (M+1) → ι → F)
    (hfar : ¬WeightedCorrelatedAgreement (reedSolomonCode dom d) θ weight u) :
    uniformProb F (fun z => WeightedClose (reedSolomonCode dom d) θ weight (curveWord u z)) ≤
      ((M*Fintype.card ι:ℕ):ℝ)/Fintype.card F := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hθB : θ < 1-(1+(d:ℝ)/(Fintype.card ι:ℝ))/2 := by
    have hdiv := (div_lt_iff₀ hn).mpr hrate
    linarith
  have h := hasGeometricMutualCorrelatedAgreement_fullUD M hM dom hd u θ hθ hθB
  rw [geometric_pr_uniform] at h
  exact le_trans (uniformProb_mono fun z hz =>
    weightedClose_mutualFailure _ θ weight hle u hfar (fun j => z^j.val) hz) h

/-- A direct weighted cardinality interface, useful before probability composition. -/
theorem curve_weighted_bad_card [Nonempty ι] [Fintype F]
    (M : ℕ) (hM : 1 ≤ M) (dom : ι ↪ F) {d : ℕ} (hd : 1 ≤ d) {θ : ℝ}
    (hθ : 0 < θ) (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι:ℝ))
    (weight : ι → ℝ) (hle : ∀ i, weight i ≤ 1) (u : Fin (M+1) → ι → F)
    (hfar : ¬WeightedCorrelatedAgreement (reedSolomonCode dom d) θ weight u) :
    (Finset.univ.filter fun z => WeightedClose (reedSolomonCode dom d) θ weight (curveWord u z)).card ≤
      M*Fintype.card ι := by
  have h := curve_weighted_uniform_sound M hM dom hd hθ hrate weight hle u hfar
  unfold uniformProb at h
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
  have hF : (0:ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  exact_mod_cast (div_le_div_iff_of_pos_right hF).mp h

end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.consistencyMass_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.consistencyMass_le_card

/-- info: 'Minidregg.Selvage.consistencyMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.consistencyMass_nonneg

/-- info: 'Minidregg.Selvage.consistencyMass_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.consistencyMass_mono

/-- info: 'Minidregg.Selvage.weightedClose_mutualFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.weightedClose_mutualFailure

/-- info: 'Minidregg.Selvage.geometric_pr_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.geometric_pr_uniform

/-- info: 'Minidregg.Selvage.weightedCA_to_CA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.weightedCA_to_CA

/-- info: 'Minidregg.Selvage.curve_weighted_uniform_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_weighted_uniform_sound

/-- info: 'Minidregg.Selvage.curve_weighted_bad_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_weighted_bad_card
