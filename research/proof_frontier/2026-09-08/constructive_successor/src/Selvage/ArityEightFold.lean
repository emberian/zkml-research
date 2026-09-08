/- One arity-eight fold from three existing binary FoldingData objects.
The same scalar supplies beta, beta^2, beta^4. No independence premise.
The agreement reconstruction uses existing RS codes and existing squaring fibres. -/
import Selvage.Proximity
import Selvage.CurveFriChallenge

namespace Minidregg.Selvage.ArityEight
open scoped BigOperators Classical

variable {F : Type*} [Field F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- Even components precede odd components, in coefficient order. -/
def parityFamily (D : FoldingData F dom domSq) {n : ℕ} (u : Fin n → ι → F) :
    Fin (n+n) → κ → F :=
  Fin.append (fun j => foldEven D (u j)) (fun j => foldOdd D (u j))

/-- One common agreement set lifts through the actual squaring map for every
member of the family, preserving its relative size. -/
theorem correlatedAgreement_recompose_family [DecidableEq F] [DecidableEq ι]
    (D : FoldingData F dom domSq) {n d : ℕ} {δ : ℝ} (u : Fin n → ι → F)
    (h : CorrelatedAgreement (reedSolomonCode domSq d) δ (parityFamily D u)) :
    CorrelatedAgreement (reedSolomonCode dom (2*d)) δ u := by
  classical
  obtain ⟨S, hScard, hgood⟩ := h
  refine ⟨Finset.univ.filter (fun i => D.sq i ∈ S), ?_, ?_⟩
  · rw [card_sq_preimage D S, card_eq_two_mul_card D]
    push_cast
    linarith
  · intro j
    obtain ⟨vE, hvE, hE⟩ := hgood (j.castAdd n)
    obtain ⟨vO, hvO, hO⟩ := hgood (j.natAdd n)
    simp only [parityFamily, Fin.append_left, Fin.append_right] at hE hO
    obtain ⟨pE, hpEd, hpE⟩ := mem_reedSolomonCode_iff.mp hvE
    obtain ⟨pO, hpOd, hpO⟩ := mem_reedSolomonCode_iff.mp hvO
    refine ⟨fun i => (recompose pE pO).eval (dom i),
      mem_reedSolomonCode_iff.mpr
        ⟨recompose pE pO, degree_recompose_lt hpEd hpOd, fun _ => rfl⟩, ?_⟩
    intro i hi
    have hik := (Finset.mem_filter.mp hi).2
    exact eq_recompose_of_agree D i
      ((hE _ hik).trans (hpE _)) ((hO _ hik).trans (hpO _))

variable {ι₀ ι₁ ι₂ ι₃ : Type*}
variable [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable {dom₀ : ι₀ ↪ F} {dom₁ : ι₁ ↪ F} {dom₂ : ι₂ ↪ F} {dom₃ : ι₃ ↪ F}

/-- Eight beta-independent coefficient words. -/
def components (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (f : ι₀ → F) : Fin 8 → ι₃ → F :=
  parityFamily D₂ (parityFamily D₁ (parityFamily D₀ (fun _ : Fin 1 => f)))

/-- One width-eight challenge, implemented by the existing three binary folds. -/
def fold8 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (f : ι₀ → F) (β : F) : ι₃ → F :=
  fold D₂ (fold D₁ (fold D₀ f β) (β^2)) (β^4)

/-- Statement-first source-farness contract. -/
def Reconstruction [DecidableEq F] (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) : Prop :=
  ∀ (d : ℕ) (δ : ℝ) (f : ι₀ → F),
    CorrelatedAgreement (reedSolomonCode dom₃ d) δ (components D₀ D₁ D₂ f) →
    close δ (reedSolomonCode dom₀ (8*d)) f

/-- The source agreement is reconstructed on the eightfold squaring preimage. -/
theorem reconstruction [DecidableEq F] [Nonempty ι₀]
    (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) : Reconstruction D₀ D₁ D₂ := by
  classical
  intro d δ f h
  have h₂ := correlatedAgreement_recompose_family D₂ _ h
  have h₁ := correlatedAgreement_recompose_family D₁ _ h₂
  have h₀ := correlatedAgreement_recompose_family D₀ _ h₁
  obtain ⟨S, hS, hw⟩ := h₀
  obtain ⟨w, hwC, hwAg⟩ := hw 0
  refine ⟨w, ?_, relDist_le_of_agreesOn hwAg hS⟩
  simpa only [show 2*(2*(2*d)) = 8*d by omega] using hwC

omit [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
/-- Exact coefficient-curve identity for the correlated internal challenges. -/
theorem fold8_eq_curve (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (f : ι₀ → F) (β : F) :
    fold8 D₀ D₁ D₂ f β = curveWord (components D₀ D₁ D₂ f) β := by
  ext i
  simp [fold8, components, parityFamily, curveWord, comb, Fin.sum_univ_succ,
    Fin.append, Fin.addCases, Fin.castLT, fold, foldEven, foldOdd, div_eq_mul_inv]
  ring

/-- The two actual indices in an existing binary fibre. -/
def branch (D : FoldingData F dom domSq) (i : κ) (b : Bool) : ι :=
  if b then D.neg (D.sec i) else D.sec i

/-- The eight source indices needed for a three-pass fold. -/
def rowPoint (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (i : ι₃) (c b a : Bool) : ι₀ :=
  branch D₀ (branch D₁ (branch D₂ i c) b) a

/-- Literal arithmetic on two supplied values. -/
def pairFold (x a b β : F) : F := (a+b)/2 + β*((a-b)/(2*x))

/-- The executable eight-value fold; the source word is not an input. -/
def foldRow8 (D₀ : FoldingData F dom₀ dom₁) (D₁ : FoldingData F dom₁ dom₂)
    (D₂ : FoldingData F dom₂ dom₃) (i : ι₃) (v : Bool → Bool → Bool → F) (β : F) : F :=
  let v₁ := fun c b => pairFold (dom₀ (D₀.sec (branch D₁ (branch D₂ i c) b)))
    (v c b false) (v c b true) β
  let v₂ := fun c => pairFold (dom₁ (D₁.sec (branch D₂ i c)))
    (v₁ c false) (v₁ c true) (β^2)
  pairFold (dom₂ (D₂.sec i)) (v₂ false) (v₂ true) (β^4)

omit [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] in
/-- Eight true source values make the supplied-value computation the actual fold. -/
theorem foldRow8_eq_fold8 (D₀ : FoldingData F dom₀ dom₁)
    (D₁ : FoldingData F dom₁ dom₂) (D₂ : FoldingData F dom₂ dom₃)
    (i : ι₃) (f : ι₀ → F) (β : F) :
    foldRow8 D₀ D₁ D₂ i (fun c b a => f (rowPoint D₀ D₁ D₂ i c b a)) β =
      fold8 D₀ D₁ D₂ f β i := by
  simp only [foldRow8, fold8, rowPoint, branch, Bool.false_eq_true, ↓reduceIte,
    fold, foldEven, foldOdd, pairFold]

end Minidregg.Selvage.ArityEight


/-- info: 'Minidregg.Selvage.ArityEight.correlatedAgreement_recompose_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.correlatedAgreement_recompose_family

/-- info: 'Minidregg.Selvage.ArityEight.reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.reconstruction

/-- info: 'Minidregg.Selvage.ArityEight.fold8_eq_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.fold8_eq_curve

/-- info: 'Minidregg.Selvage.ArityEight.foldRow8_eq_fold8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.foldRow8_eq_fold8

