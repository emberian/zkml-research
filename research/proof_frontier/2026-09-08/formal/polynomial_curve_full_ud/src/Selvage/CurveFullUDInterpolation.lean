/- Degree-M full-UD interpolation over the existing RS definition.
Reuses the already checked affine error-locator theorem at the single word
(curveWord u z,0), with scalar0. All polynomial-matrix degree work is generic. -/
import Selvage.CurveFullUDStatement
import Selvage.FullUDInterpolation
import Theory.CurveRSInterpolationKernel

namespace Minidregg.Selvage
open Polynomial Matrix Finset RSInterpolation
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

noncomputable def curvePolynomial {M : ℕ} (u : Fin (M+1) → ι → F) (i : ι) : F[X] :=
  PolynomialCurve.poly (fun j => u j i)

omit [DecidableEq F] [Fintype ι] in
theorem curvePolynomial_eval {M : ℕ} (u : Fin (M+1) → ι → F) (z : F) (i : ι) :
    (curvePolynomial u i).eval z = curveWord u z i := by
  exact PolynomialCurve.eval_poly _ z

omit [DecidableEq F] [Fintype ι] in
theorem curvePolynomial_coeff {M : ℕ} (u : Fin (M+1) → ι → F)
    (i : ι) (j : Fin (M+1)) : (curvePolynomial u i).coeff j.val = u j i :=
  PolynomialCurve.coeff_poly _ j

omit [DecidableEq F] [Fintype ι] in
theorem curvePolynomial_natDegree {M : ℕ} (u : Fin (M+1) → ι → F) (i : ι) :
    (curvePolynomial u i).natDegree ≤ M := PolynomialCurve.natDegree_poly _

theorem curve_bw_bounded_kernel_of_many_close
    (M e d : ℕ) (dom : ι ↪ F) (u : Fin (M+1) → ι → F) (A : Finset F)
    (_hM : 1 ≤ M) (hd : 1 ≤ d) (hradius : 2*e+d ≤ Fintype.card ι)
    (hcard : M*Fintype.card ι < A.card)
    (hclose : ∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (curveWord u z) w ≤ e) :
    ∃ a : Fin (e+1) → F[X], ∃ b : Fin (e+d) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ M*e) ∧
      (∀ s, (b s).natDegree ≤ M*(e+1)) ∧
      (BW_homMatrix e d (fun i => Polynomial.C (dom i))
        (curvePolynomial u)).mulVec (Fin.append a b) = 0 := by
  apply curve_bounded_kernel_of_specializations M e d dom (curvePolynomial u) A
    (curvePolynomial_natDegree u) hd hradius
  · exact lt_of_le_of_lt (Nat.mul_le_mul_left M (by omega)) hcard
  · intro z hz
    have hclose' : ∃ w ∈ reedSolomonCode dom d,
        hammingDist ((![(curveWord u z), (0 : ι → F)] : Fin 2 → ι → F) 0 +
          (0 : F) • (![(curveWord u z), (0 : ι → F)] : Fin 2 → ι → F) 1) w ≤ e := by
      simpa using hclose z hz
    have h := bw_specialization_of_close hd ![curveWord u z, (0 : ι → F)] 0 hclose'
    simpa [curvePolynomial_eval] using h

end Minidregg.Selvage

/-- info: 'Minidregg.Selvage.curvePolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curvePolynomial_eval

/-- info: 'Minidregg.Selvage.curvePolynomial_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curvePolynomial_coeff

/-- info: 'Minidregg.Selvage.curvePolynomial_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curvePolynomial_natDegree

/-- info: 'Minidregg.Selvage.curve_bw_bounded_kernel_of_many_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_bw_bounded_kernel_of_many_close

