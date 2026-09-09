/- Masking consistency weights by an actual fold equation retains the
weighted-agreement invariant at the same threshold. -/
import Selvage.CurveWeightedAgreement

namespace Minidregg.Selvage
open scoped BigOperators Classical
variable {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]

noncomputable def maskConsistency (weight : ι → ℝ) (f g : ι → F) (i : ι) : ℝ :=
  if f i = g i then weight i else 0

omit [Fintype ι] [Field F] in
theorem maskConsistency_nonneg (weight : ι → ℝ) (h0 : ∀ i, 0 ≤ weight i) (f g : ι → F) (i : ι) :
    0 ≤ maskConsistency weight f g i := by
  unfold maskConsistency
  split_ifs
  · exact h0 i
  · norm_num

omit [Fintype ι] [Field F] in
theorem maskConsistency_le_one (weight : ι → ℝ) (h1 : ∀ i, weight i ≤ 1) (f g : ι → F) (i : ι) :
    maskConsistency weight f g i ≤ 1 := by unfold maskConsistency; split_ifs <;> simp_all

omit [Fintype ι] [Field F] in
/-- Removing zero-weight mismatches leaves exactly the same mass. -/
theorem maskConsistency_mass (weight : ι → ℝ) (f g : ι → F) (S : Finset ι) :
    consistencyMass (maskConsistency weight f g) S =
      consistencyMass weight (S.filter fun i => f i = g i) := by
  simp [consistencyMass,maskConsistency,Finset.sum_filter]

/-- Weighted closeness after the equality mask transfers to the literal
fold under the previous projected weights, with no subtraction of θ. -/
theorem weightedClose_mask_transfer (C : Submodule F (ι → F)) (θ : ℝ)
    (weight : ι → ℝ) (next literal : ι → F)
    (h : WeightedClose C θ (maskConsistency weight next literal) next) :
    WeightedClose C θ weight literal := by
  obtain ⟨S,hS,v,hv,ha⟩ := h
  refine ⟨S.filter (fun i => next i = literal i),?_,v,hv,?_⟩
  · simpa only [maskConsistency_mass] using hS
  · intro i hi
    have hs := Finset.mem_filter.mp hi
    exact hs.2.symm.trans (ha i hs.1)

/-- Initial all-one consistency weights recover ordinary proximity. -/
theorem weightedClose_one_to_close [Nonempty ι] (C : Submodule F (ι → F)) (θ : ℝ) (f : ι → F)
    (h : WeightedClose C θ (fun _ => 1) f) : close θ C f := by
  obtain ⟨S,hS,v,hv,ha⟩ := h
  refine ⟨v,hv,relDist_le_of_agreesOn ha ?_⟩
  simpa [consistencyMass] using hS

omit [DecidableEq F] in
/-- A legal terminal codeword with enough total consistency mass is
weighted-close to itself. This is the terminal invariant's contradiction. -/
theorem weightedClose_self_of_mass (C : Submodule F (ι → F)) (θ : ℝ)
    (weight : ι → ℝ) (f : ι → F) (hf : f ∈ C)
    (hm : (1-θ)*(Fintype.card ι:ℝ) ≤ consistencyMass weight Finset.univ) :
    WeightedClose C θ weight f := ⟨Finset.univ,hm,f,hf,fun _ _ => rfl⟩

end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.maskConsistency_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.maskConsistency_nonneg

/-- info: 'Minidregg.Selvage.maskConsistency_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.maskConsistency_le_one

/-- info: 'Minidregg.Selvage.maskConsistency_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.maskConsistency_mass

/-- info: 'Minidregg.Selvage.weightedClose_mask_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.weightedClose_mask_transfer

/-- info: 'Minidregg.Selvage.weightedClose_one_to_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.weightedClose_one_to_close

/-- info: 'Minidregg.Selvage.weightedClose_self_of_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.weightedClose_self_of_mass
