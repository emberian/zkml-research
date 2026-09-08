import Theory.PolynomialBivariate

/-!
Statement-first contract for corrected Polishchuk–Spielman gluing.
The quotient degree conditions are premises, not inferred from divisibility.
The all-one instance inhabits every premise; the zero-specialization tooth
exhibits a nondivisible pair rejected by the conclusion.
-/

open Polynomial.Bivariate Polynomial

structure PolynomialGluingData (F : Type) [Field F] where
  ax : ℕ
  ay : ℕ
  bx : ℕ
  by_ : ℕ
  nx : ℕ+
  ny : ℕ+
  A : F[X][Y]
  B : F[X][Y]
  Px : Finset F
  Py : Finset F
  quotX : F → F[X]
  quotY : F → F[X]

namespace PolynomialGluingData

def Admissible {F : Type} [Field F] (d : PolynomialGluingData F) : Prop :=
  d.ax ≤ d.bx ∧ d.ay ≤ d.by_ ∧ d.A ≠ 0 ∧
  degreeX d.A ≤ d.ax ∧ degreeX d.B ≤ d.bx ∧
  natDegreeY d.A ≤ d.ay ∧ natDegreeY d.B ≤ d.by_ ∧
  (d.nx : ℕ) ≤ d.Px.card ∧ (d.ny : ℕ) ≤ d.Py.card ∧
  (∀ y ∈ d.Py, (d.quotX y).natDegree ≤ d.bx - d.ax ∧
    evalY y d.B = d.quotX y * evalY y d.A) ∧
  (∀ x ∈ d.Px, (d.quotY x).natDegree ≤ d.by_ - d.ay ∧
    evalX x d.B = d.quotY x * evalX x d.A) ∧
  (d.bx : ℚ) / (d.nx : ℚ) + (d.by_ : ℚ) / (d.ny : ℚ) < 1

def Glues {F : Type} [Field F] (d : PolynomialGluingData F) : Prop :=
  ∃ P : F[X][Y], d.B = P * d.A ∧
    degreeX P ≤ d.bx - d.ax ∧ natDegreeY P ≤ d.by_ - d.ay ∧
    (∃ Qx : Finset F, (d.nx : ℕ) - d.ax ≤ Qx.card ∧ Qx ⊆ d.Px ∧
      ∀ x ∈ Qx, evalX x P = d.quotY x) ∧
    (∃ Qy : Finset F, (d.ny : ℕ) - d.ay ≤ Qy.card ∧ Qy ⊆ d.Py ∧
      ∀ y ∈ Qy, evalY y P = d.quotX y)

end PolynomialGluingData

/-- Every admissible local quotient grid has a global quotient with the stated bounds. -/
def PolynomialGluing (F : Type) [Field F] : Prop :=
  ∀ d : PolynomialGluingData F, d.Admissible → d.Glues

noncomputable def polynomialGluingWitness : PolynomialGluingData ℚ where
  ax := 0
  ay := 0
  bx := 0
  by_ := 0
  nx := 1
  ny := 1
  A := 1
  B := 1
  Px := {0}
  Py := {0}
  quotX := fun _ => 1
  quotY := fun _ => 1

theorem polynomialGluing_premise_inhabited :
    polynomialGluingWitness.Admissible := by
  simp [PolynomialGluingData.Admissible, polynomialGluingWitness,
    natDegreeY, evalX_eq_map, evalY, ← natDegreeY_swap]

theorem polynomialGluing_satisfiable : polynomialGluingWitness.Glues := by
  refine ⟨1, ?_⟩
  simp [polynomialGluingWitness, natDegreeY, evalX_eq_map, evalY, ← natDegreeY_swap]
  exact ⟨{0}, by simp⟩

noncomputable def polynomialGluingBroken : PolynomialGluingData ℚ :=
  { polynomialGluingWitness with A := Y, ay := 1, by_ := 1 }

theorem polynomialGluing_teeth : ¬ polynomialGluingBroken.Glues := by
  rintro ⟨P, h, _⟩
  have h0 := congrArg (fun f : ℚ[X][Y] => evalY 0 f) h
  simpa [polynomialGluingBroken, polynomialGluingWitness, evalY] using h0

/-- info: 'polynomialGluing_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polynomialGluing_premise_inhabited
/-- info: 'polynomialGluing_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polynomialGluing_satisfiable
/-- info: 'polynomialGluing_teeth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polynomialGluing_teeth
