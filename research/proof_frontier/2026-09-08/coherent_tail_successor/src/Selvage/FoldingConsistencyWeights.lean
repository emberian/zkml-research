/- Consistency weights transported through the EXISTING FoldingData squaring
fibres. Weighted source agreement is reconstructed without a radius gap. -/
import Selvage.CurveWeightedAgreement
import Selvage.ArityEightFold

namespace Minidregg.Selvage.ArityEight
open scoped BigOperators Classical
variable {F ι κ : Type} [Field F] [DecidableEq F] [Fintype ι] [Fintype κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

noncomputable def projectConsistency (D : FoldingData F dom domSq) (weight : ι → ℝ) (k : κ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => D.sq i = k), weight i)/2

omit [DecidableEq F] [Fintype κ] in
/-- The projected mass equals half the mass on the actual squaring preimage. -/
theorem projectConsistency_mass (D : FoldingData F dom domSq) (weight : ι → ℝ) (S : Finset κ) :
    consistencyMass (projectConsistency D weight) S =
      consistencyMass weight (Finset.univ.filter fun i => D.sq i ∈ S)/2 := by
  unfold consistencyMass projectConsistency
  rw [←Finset.sum_div]
  exact congrArg (fun x : ℝ => x/2) (Finset.sum_fiberwise_eq_sum_filter Finset.univ S D.sq weight)

omit [DecidableEq F] [Fintype κ] in
theorem projectConsistency_nonneg (D : FoldingData F dom domSq) (weight : ι → ℝ)
    (h0 : ∀ i, 0 ≤ weight i) (k : κ) : 0 ≤ projectConsistency D weight k := by
  exact div_nonneg (Finset.sum_nonneg fun i _ => h0 i) (by norm_num)

omit [DecidableEq F] [Fintype κ] in
theorem projectConsistency_le_one (D : FoldingData F dom domSq) (weight : ι → ℝ)
    (h1 : ∀ i, weight i ≤ 1) (k : κ) : projectConsistency D weight k ≤ 1 := by
  have hc : (Finset.univ.filter (fun i => D.sq i = k)).card = 2 := by
    simpa using card_sq_preimage D {k}
  have h := consistencyMass_le_card weight h1 (Finset.univ.filter fun i => D.sq i = k)
  rw [hc] at h
  norm_num at h
  change consistencyMass weight _ / 2 ≤ 1
  linarith

omit [DecidableEq F] in
/-- All family members reconstruct on the same weighted squaring preimage. -/
theorem weighted_recompose_family (D : FoldingData F dom domSq)
    {n d : ℕ} {θ : ℝ} (weight : ι → ℝ) (u : Fin n → ι → F)
    (h : WeightedCorrelatedAgreement (reedSolomonCode domSq d) θ
      (projectConsistency D weight) (parityFamily D u)) :
    WeightedCorrelatedAgreement (reedSolomonCode dom (2*d)) θ weight u := by
  obtain ⟨S,hSmass,hgood⟩ := h
  refine ⟨Finset.univ.filter (fun i => D.sq i ∈ S),?_,?_⟩
  · rw [card_eq_two_mul_card D]
    rw [projectConsistency_mass] at hSmass
    push_cast
    linarith
  · intro j
    obtain ⟨vE,hvE,hE⟩ := hgood (j.castAdd n)
    obtain ⟨vO,hvO,hO⟩ := hgood (j.natAdd n)
    simp only [parityFamily,Fin.append_left,Fin.append_right] at hE hO
    obtain ⟨pE,hpEd,hpE⟩ := mem_reedSolomonCode_iff.mp hvE
    obtain ⟨pO,hpOd,hpO⟩ := mem_reedSolomonCode_iff.mp hvO
    refine ⟨fun i => (recompose pE pO).eval (dom i),mem_reedSolomonCode_iff.mpr
      ⟨recompose pE pO,degree_recompose_lt hpEd hpOd,fun _ => rfl⟩,?_⟩
    intro i hi
    have hik := (Finset.mem_filter.mp hi).2
    exact eq_recompose_of_agree D i ((hE _ hik).trans (hpE _)) ((hO _ hik).trans (hpO _))

variable {ι₀ ι₁ ι₂ ι₃ : Type}
variable [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable {dom₀ : ι₀ ↪ F} {dom₁ : ι₁ ↪ F} {dom₂ : ι₂ ↪ F} {dom₃ : ι₃ ↪ F}

noncomputable def projectConsistency8 (D₀ : FoldingData F dom₀ dom₁)
    (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃) (weight : ι₀ → ℝ) : ι₃ → ℝ :=
  projectConsistency D₂ (projectConsistency D₁ (projectConsistency D₀ weight))

omit [DecidableEq F] [Fintype ι₃] in
theorem projectConsistency8_nonneg (D₀ : FoldingData F dom₀ dom₁)
    (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃) (weight : ι₀ → ℝ)
    (h0 : ∀ i, 0 ≤ weight i) : ∀ i, 0 ≤ projectConsistency8 D₀ D₁ D₂ weight i :=
  projectConsistency_nonneg D₂ _ (projectConsistency_nonneg D₁ _ (projectConsistency_nonneg D₀ _ h0))

omit [DecidableEq F] [Fintype ι₃] in
theorem projectConsistency8_le_one (D₀ : FoldingData F dom₀ dom₁)
    (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃) (weight : ι₀ → ℝ)
    (h1 : ∀ i, weight i ≤ 1) : ∀ i, projectConsistency8 D₀ D₁ D₂ weight i ≤ 1 :=
  projectConsistency_le_one D₂ _ (projectConsistency_le_one D₁ _ (projectConsistency_le_one D₀ _ h1))

omit [DecidableEq F] in
/-- Weighted agreement reconstructs the source at unchanged θ, on eightfold fibres. -/
theorem weighted_reconstruction (D₀ : FoldingData F dom₀ dom₁)
    (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (d : ℕ) (θ : ℝ) (weight : ι₀ → ℝ) (f : ι₀ → F)
    (h : WeightedCorrelatedAgreement (reedSolomonCode dom₃ d) θ
      (projectConsistency8 D₀ D₁ D₂ weight) (components D₀ D₁ D₂ f)) :
    WeightedClose (reedSolomonCode dom₀ (8*d)) θ weight f := by
  have h₂ := weighted_recompose_family D₂ _ _ h
  have h₁ := weighted_recompose_family D₁ _ _ h₂
  have h₀ := weighted_recompose_family D₀ _ _ h₁
  obtain ⟨S,hS,hw⟩ := h₀
  obtain ⟨w,hwC,hwAg⟩ := hw 0
  refine ⟨S,hS,w,?_,hwAg⟩
  simpa only [show 2*(2*(2*d)) = 8*d by omega] using hwC

/-- Direct one-scalar, fixed-input arity-eight preservation of weighted
nonagreement. This is the per-round invariant needed for cumulative query soundness. -/
theorem fold8_injected_weighted_sound [Fintype F] [Nonempty ι₃]
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ)
    (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (weight : ι₀ → ℝ) (h1 : ∀ i, weight i ≤ 1) (f : ι₀ → F) (g : ι₃ → F)
    (hfar : ¬WeightedClose (reedSolomonCode dom₀ (8*d)) θ weight f) :
    uniformProb F (fun β => WeightedClose (reedSolomonCode dom₃ d) θ
      (projectConsistency8 D₀ D₁ D₂ weight) (fun i => fold8 D₀ D₁ D₂ f β i+β^8*g i)) ≤
      ((8*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F := by
  have hf : ¬WeightedCorrelatedAgreement (reedSolomonCode dom₃ d) θ
      (projectConsistency8 D₀ D₁ D₂ weight) (Fin.snoc (components D₀ D₁ D₂ f) g) := by
    rintro ⟨S,hS,hw⟩
    apply hfar
    apply weighted_reconstruction D₀ D₁ D₂ d θ weight f
    exact ⟨S,hS,fun j => by simpa using hw j.castSucc⟩
  simpa only [curveWord_snoc,←fold8_eq_curve] using
    curve_weighted_uniform_sound 8 (by decide) dom₃ hd hθ hrate
      (projectConsistency8 D₀ D₁ D₂ weight) (projectConsistency8_le_one D₀ D₁ D₂ weight h1)
      (Fin.snoc (components D₀ D₁ D₂ f) g) hf

end Minidregg.Selvage.ArityEight



/-- info: 'Minidregg.Selvage.ArityEight.projectConsistency_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.projectConsistency_mass

/-- info: 'Minidregg.Selvage.ArityEight.projectConsistency_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.projectConsistency_nonneg

/-- info: 'Minidregg.Selvage.ArityEight.projectConsistency_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.projectConsistency_le_one

/-- info: 'Minidregg.Selvage.ArityEight.weighted_recompose_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.weighted_recompose_family

/-- info: 'Minidregg.Selvage.ArityEight.projectConsistency8_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.projectConsistency8_nonneg

/-- info: 'Minidregg.Selvage.ArityEight.projectConsistency8_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.projectConsistency8_le_one

/-- info: 'Minidregg.Selvage.ArityEight.weighted_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.weighted_reconstruction

/-- info: 'Minidregg.Selvage.ArityEight.fold8_injected_weighted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_injected_weighted_sound
