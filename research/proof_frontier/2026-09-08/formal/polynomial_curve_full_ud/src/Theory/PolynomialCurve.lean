/- A finite coefficient vector represented by its ordinary Mathlib polynomial. -/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

namespace Minidregg.PolynomialCurve
open Polynomial Finset
open scoped BigOperators
variable {F : Type*} [Field F]

noncomputable def poly {M : ℕ} (u : Fin (M+1) → F) : F[X] :=
  ∑ j, Polynomial.monomial j.val (u j)

theorem eval_poly {M : ℕ} (u : Fin (M+1) → F) (z : F) :
    (poly u).eval z = ∑ j, z ^ j.val * u j := by
  simp [poly, Polynomial.eval_finsetSum, mul_comm]

theorem coeff_poly {M : ℕ} (u : Fin (M+1) → F) (j : Fin (M+1)) :
    (poly u).coeff j.val = u j := by
  simp [poly, Polynomial.coeff_monomial, ← Fin.ext_iff]

theorem natDegree_poly {M : ℕ} (u : Fin (M+1) → F) :
    (poly u).natDegree ≤ M := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

end Minidregg.PolynomialCurve

/-- info: 'Minidregg.PolynomialCurve.eval_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.PolynomialCurve.eval_poly

/-- info: 'Minidregg.PolynomialCurve.coeff_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.PolynomialCurve.coeff_poly

/-- info: 'Minidregg.PolynomialCurve.natDegree_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.PolynomialCurve.natDegree_poly

