/- Direct native barycentric-row to the existing binary folding semantics.
The four-value final round and eight-value rounds use correlated powers of one
scalar. Concrete node/fibre facts are explicit; no fold equality is assumed. -/
import Theory.P3BarycentricInterpolation
import Selvage.FoldingConsistencyWeights
import Mathlib.Algebra.Polynomial.OfFn

namespace Minidregg.Selvage.ArityEight
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] [DecidableEq F]
variable {ι₀ ι₁ ι₂ ι₃ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable {dom₀ : ι₀ ↪ F} {dom₁ : ι₁ ↪ F} {dom₂ : ι₂ ↪ F} {dom₃ : ι₃ ↪ F}

/-- The actual final native round uses arity four, hence beta then beta squared. -/
def fold4 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (f : ι₀ → F) (β : F) : ι₂ → F := fold D₁ (fold D₀ f β) (β^2)

def components4 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (f : ι₀ → F) : Fin 4 → ι₂ → F := parityFamily D₁ (parityFamily D₀ (fun _ : Fin 1 => f))

omit [DecidableEq F] [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
theorem fold4_eq_curve (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (f : ι₀ → F) (β : F) : fold4 D₀ D₁ f β = curveWord (components4 D₀ D₁ f) β := by
  ext i
  simp [fold4,components4,parityFamily,curveWord,comb,Fin.sum_univ_succ,
    Fin.append,Fin.addCases,Fin.castLT,fold,foldEven,foldOdd,div_eq_mul_inv]
  ring

omit [DecidableEq F] [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
theorem fold_selects_source (D : FoldingData F dom₀ dom₁) (f : ι₀ → F) (i : ι₀) :
    fold D f (dom₀ i) (D.sq i) = f i := foldEven_add_mul_foldOdd D f i

omit [DecidableEq F] [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
theorem fold4_selects_source (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (f : ι₀ → F) (i : ι₀) :
    fold4 D₀ D₁ f (dom₀ i) (D₁.sq (D₀.sq i)) = f i := by
  unfold fold4
  rw [←D₀.domSq_sq,fold_selects_source,fold_selects_source]

omit [DecidableEq F] [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
theorem fold8_selects_source (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (f : ι₀ → F) (i : ι₀) :
    fold8 D₀ D₁ D₂ f (dom₀ i) (D₂.sq (D₁.sq (D₀.sq i))) = f i := by
  have hx : (dom₀ i)^4 = dom₂ (D₁.sq (D₀.sq i)) := by
    rw [D₁.domSq_sq,D₀.domSq_sq]
    ring
  unfold fold8
  rw [hx,fold_selects_source]
  exact fold4_selects_source D₀ D₁ f i

omit [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
lemma coefficient_poly_eval {n : ℕ} (u : Fin (n+1) → F) (β : F) :
    (ofFn (n+1) u).eval β = ∑ j, β^j.val*u j := by
  rw [ofFn_eq_sum_monomial]
  simp only [eval_finsetSum,eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
/-- Native four-value coset interpolation is exactly the existing two-fold
operator when the source indices are the actual four-element square fibre. -/
theorem native_eq_fold4 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (xs : P3Barycentric.CosetNodes F 4) (idx : Fin 4 → ι₀) (k : ι₂)
    (hnode : ∀ j, xs.nodes j = dom₀ (idx j))
    (hfibre : ∀ j, D₁.sq (D₀.sq (idx j)) = k) (f : ι₀ → F) (β : F) :
    P3Barycentric.native xs (fun j => f (idx j)) β = fold4 D₀ D₁ f β k := by
  let p := ofFn 4 (fun j => components4 D₀ D₁ f j k)
  have he : ∀ z, p.eval z = fold4 D₀ D₁ f z k := by
    intro z
    rw [fold4_eq_curve]
    exact coefficient_poly_eval _ _
  have hv : (fun j => f (idx j)) = fun j => p.eval (xs.nodes j) := by
    funext j
    rw [he,hnode,←hfibre j]
    exact (fold4_selects_source D₀ D₁ f (idx j)).symm
  rw [hv,P3Barycentric.native_of_polynomial xs p (ofFn_degree_lt _) β,he]

omit [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
/-- Native eight-value interpolation matches all three existing folds with
beta,beta²,beta⁴, including the native early return at any fibre point. -/
theorem native_eq_fold8 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (xs : P3Barycentric.CosetNodes F 8)
    (idx : Fin 8 → ι₀) (k : ι₃) (hnode : ∀ j, xs.nodes j = dom₀ (idx j))
    (hfibre : ∀ j, D₂.sq (D₁.sq (D₀.sq (idx j))) = k) (f : ι₀ → F) (β : F) :
    P3Barycentric.native xs (fun j => f (idx j)) β = fold8 D₀ D₁ D₂ f β k := by
  let p := ofFn 8 (fun j => components D₀ D₁ D₂ f j k)
  have he : ∀ z, p.eval z = fold8 D₀ D₁ D₂ f z k := by
    intro z
    rw [fold8_eq_curve]
    exact coefficient_poly_eval _ _
  have hv : (fun j => f (idx j)) = fun j => p.eval (xs.nodes j) := by
    funext j
    rw [he,hnode,←hfibre j]
    exact (fold8_selects_source D₀ D₁ D₂ f (idx j)).symm
  rw [hv,P3Barycentric.native_of_polynomial xs p (ofFn_degree_lt _) β,he]

omit [DecidableEq F] in
theorem weighted_reconstruction4 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (d : ℕ) (θ : ℝ) (weight : ι₀ → ℝ) (f : ι₀ → F)
    (h : WeightedCorrelatedAgreement (reedSolomonCode dom₂ d) θ
      (projectConsistency D₁ (projectConsistency D₀ weight)) (components4 D₀ D₁ f)) :
    WeightedClose (reedSolomonCode dom₀ (4*d)) θ weight f := by
  have h₁ := weighted_recompose_family D₁ _ _ h
  have h₀ := weighted_recompose_family D₀ _ _ h₁
  obtain ⟨S,hS,hw⟩ := h₀
  obtain ⟨w,hwC,hwAg⟩ := hw 0
  exact ⟨S,hS,w,by simpa only [show 2*(2*d)=4*d by omega] using hwC,hwAg⟩

/-- The actual last arity-four/no-injection transition has curve degree three. -/
theorem fold4_weighted_sound [Fintype F] [Nonempty ι₂]
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ)
    (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₂:ℝ))
    (weight : ι₀ → ℝ) (h1 : ∀ i, weight i ≤ 1) (f : ι₀ → F)
    (hfar : ¬WeightedClose (reedSolomonCode dom₀ (4*d)) θ weight f) :
    uniformProb F (fun β => WeightedClose (reedSolomonCode dom₂ d) θ
      (projectConsistency D₁ (projectConsistency D₀ weight)) (fold4 D₀ D₁ f β)) ≤
      ((3*Fintype.card ι₂:ℕ):ℝ)/Fintype.card F := by
  have hf : ¬WeightedCorrelatedAgreement (reedSolomonCode dom₂ d) θ
      (projectConsistency D₁ (projectConsistency D₀ weight)) (components4 D₀ D₁ f) :=
    fun h => hfar (weighted_reconstruction4 D₀ D₁ d θ weight f h)
  simpa only [←fold4_eq_curve] using curve_weighted_uniform_sound 3 (by decide) dom₂ hd hθ hrate
    (projectConsistency D₁ (projectConsistency D₀ weight))
    (projectConsistency_le_one D₁ _ (projectConsistency_le_one D₀ weight h1)) (components4 D₀ D₁ f) hf

/-- The actual no-injection eight-value transition has curve degree seven. -/
theorem fold8_weighted_sound [Fintype F] [Nonempty ι₃]
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    {d : ℕ} (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ)
    (hrate : (d:ℝ) < (1-2*θ)*(Fintype.card ι₃:ℝ))
    (weight : ι₀ → ℝ) (h1 : ∀ i, weight i ≤ 1) (f : ι₀ → F)
    (hfar : ¬WeightedClose (reedSolomonCode dom₀ (8*d)) θ weight f) :
    uniformProb F (fun β => WeightedClose (reedSolomonCode dom₃ d) θ
      (projectConsistency8 D₀ D₁ D₂ weight) (fold8 D₀ D₁ D₂ f β)) ≤
      ((7*Fintype.card ι₃:ℕ):ℝ)/Fintype.card F := by
  have hf : ¬WeightedCorrelatedAgreement (reedSolomonCode dom₃ d) θ
      (projectConsistency8 D₀ D₁ D₂ weight) (components D₀ D₁ D₂ f) :=
    fun h => hfar (weighted_reconstruction D₀ D₁ D₂ d θ weight f h)
  simpa only [←fold8_eq_curve] using curve_weighted_uniform_sound 7 (by decide) dom₃ hd hθ hrate
    (projectConsistency8 D₀ D₁ D₂ weight) (projectConsistency8_le_one D₀ D₁ D₂ weight h1)
    (components D₀ D₁ D₂ f) hf

end
end Minidregg.Selvage.ArityEight

/-- info: 'Minidregg.Selvage.ArityEight.fold4_eq_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold4_eq_curve

/-- info: 'Minidregg.Selvage.ArityEight.fold_selects_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold_selects_source

/-- info: 'Minidregg.Selvage.ArityEight.fold4_selects_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold4_selects_source

/-- info: 'Minidregg.Selvage.ArityEight.fold8_selects_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_selects_source

/-- info: 'Minidregg.Selvage.ArityEight.coefficient_poly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.coefficient_poly_eval

/-- info: 'Minidregg.Selvage.ArityEight.native_eq_fold4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.native_eq_fold4

/-- info: 'Minidregg.Selvage.ArityEight.native_eq_fold8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.native_eq_fold8

/-- info: 'Minidregg.Selvage.ArityEight.weighted_reconstruction4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.weighted_reconstruction4

/-- info: 'Minidregg.Selvage.ArityEight.fold4_weighted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold4_weighted_sound

/-- info: 'Minidregg.Selvage.ArityEight.fold8_weighted_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_weighted_sound

