/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/- Adapted 2026-09-08 for minidregg, Lean 4.30.0. Retains only the ordinary
Mathlib nested-polynomial degree/evaluation surface; no CompPoly representation.
Source: CompPoly revision a09455a22fea4623a2a1c5b363cf6efc61486a83,
CompPoly/ToMathlib/Polynomial/BivariateDegree.lean. evalX is backported to the
Lean 4.30 constructor, and degreeX_mul is derived from Mathlib swap. -/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate
namespace Polynomial.Bivariate
noncomputable section
variable {F : Type*}
section Semiring
variable [Semiring F]
/-- `(i, j)`-coefficient of a polynomial, i.e. the coefficient of `X^i Y^j`. -/
def coeff (f : F[X][Y]) (i j : ℕ) : F :=
  (f.coeff j).coeff i

/-- The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] :=
  f.coeff (natDegree f)

/-- The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial. -/
@[simp, grind =]
theorem leadingCoeffY_eq_zero (f : F[X][Y]) : leadingCoeffY f = 0 ↔ f = 0 := by
  simp [leadingCoeffY]

/-- The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero. -/
@[simp, grind =]
lemma leadingCoeffY_ne_zero (f : F[X][Y]) : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  exact not_congr (leadingCoeffY_eq_zero (f := f))

/-- The `Y`-degree of a bivariate polynomial, as a natural number. -/
def natDegreeY (f : F[X][Y]) : ℕ :=
  Polynomial.natDegree f

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ :=
  f.support.sup (fun n => (f.coeff n).natDegree)


/-- Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    natDegreeY (f * g) = natDegreeY f + natDegreeY g := by
  simpa [natDegreeY] using (Polynomial.natDegree_mul hf hg)

theorem coeff_natDegree_le_degreeX (f : F[X][Y]) (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  classical
  unfold degreeX
  by_cases hn : n ∈ f.support
  · exact Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree) hn
  · have hcoeff : f.coeff n = 0 := by
      exact Polynomial.notMem_support_iff.mp hn
    simp [hcoeff]


/-- The evaluation at a point of a bivariate polynomial in the first variable `X`. -/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  Polynomial.ofFinsupp (Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp.coeff)

/-- The evaluation at a point of a bivariate polynomial in the second variable `Y`. -/
def evalY (a : F) (f : F[X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

end Semiring

section CommSemiring

variable [CommSemiring F]

lemma evalX_eq_map (x : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
  classical
  ext n
  simp only [Polynomial.Bivariate.evalX, Polynomial.coeff_ofFinsupp,
    Finsupp.mapRange_apply, Polynomial.coeff_map]
  rfl

end CommSemiring

section CommRing

variable [CommRing F]

lemma degreeX_swap (f : F[X][Y]) :
    Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.natDegreeY f := by
  classical
  have hcoeff :
      ∀ (g : F[X][Y]) (i j : ℕ),
        Polynomial.Bivariate.coeff (Polynomial.Bivariate.swap g) i j =
          Polynomial.Bivariate.coeff g j i := by
    intro g i j
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
        have hp' : ((Polynomial.Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
          exact hp
        have hq' : ((Polynomial.Bivariate.swap q).coeff j).coeff i = (q.coeff i).coeff j := by
          exact hq
        simp [Polynomial.Bivariate.coeff, hp', hq']
    | monomial n a =>
        induction a using Polynomial.induction_on' with
        | add p q hp hq =>
            have hp' : ((Polynomial.Bivariate.swap ((monomial n) p)).coeff j).coeff i =
                (((monomial n) p).coeff i).coeff j := by exact hp
            have hq' : ((Polynomial.Bivariate.swap ((monomial n) q)).coeff j).coeff i =
                (((monomial n) q).coeff i).coeff j := by exact hq
            simp [Polynomial.Bivariate.coeff, map_add, hp', hq']
        | monomial m r =>
            by_cases hi : n = i
            · subst hi
              by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, hj]
            · by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, hi]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, hi, hj]

  unfold Polynomial.Bivariate.degreeX Polynomial.Bivariate.natDegreeY
  by_cases hf : f = 0
  · subst hf
    simp
  · apply le_antisymm
    · refine Finset.sup_le_iff.2 ?_
      intro n hn
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hfm : f.coeff m = 0 := coeff_eq_zero_of_natDegree_lt hm
      have hmn : ((Polynomial.Bivariate.swap f).coeff n).coeff m = (f.coeff m).coeff n := by
        exact hcoeff f m n
      rw [hmn]
      simp [hfm]
    · have hNmem : natDegree f ∈ f.support :=
        Polynomial.natDegree_mem_support_of_nonzero hf
      have hcoeffN0 : f.coeff (natDegree f) ≠ 0 := by
        exact mem_support_iff.mp hNmem
      let n : ℕ := (f.coeff (natDegree f)).natDegree
      have hnmem : n ∈ (f.coeff (natDegree f)).support := by
        exact natDegree_mem_support_of_nonzero hcoeffN0
      have hcoeffn : (f.coeff (natDegree f)).coeff n ≠ 0 := by
        exact mem_support_iff.mp hnmem
      have hEq : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) =
          (f.coeff (natDegree f)).coeff n := by
        exact hcoeff f f.natDegree n
      have hswapCoeff : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) ≠ 0 := by
        simpa [hEq] using hcoeffn
      have hNle_natDeg : natDegree f ≤ ((Polynomial.Bivariate.swap f).coeff n).natDegree := by
        exact le_natDegree_of_ne_zero hswapCoeff
      have hcoeff_nonzero : (Polynomial.Bivariate.swap f).coeff n ≠ 0 := by
        intro hzero
        apply hswapCoeff
        rw [hzero]
        simp
      have hn_support : n ∈ (Polynomial.Bivariate.swap f).support := by
        exact mem_support_iff.mpr hcoeff_nonzero
      have hn_le_degX :
          ((Polynomial.Bivariate.swap f).coeff n).natDegree ≤
            (Polynomial.Bivariate.swap f).support.sup
              (fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) :=
        Finset.le_sup (f := fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) hn_support
      exact le_trans hNle_natDeg hn_le_degX

lemma evalY_eq_evalX_swap (y : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalY y f =
      Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
  classical
  let : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)
  have eval_eq_aeval : Polynomial.eval (Polynomial.C y) f = aeval (Polynomial.C y) f := by
    simp [Polynomial.aeval_def]
  have mapAlgHom_eq_map :
      Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f)
        = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
    exact rfl
  calc
    Polynomial.Bivariate.evalY y f
        = Polynomial.eval (Polynomial.C y) f := by
            rfl
    _ = aeval (Polynomial.C y) f := by
      exact eval_eq_aeval
    _ = Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f) := by
      exact aveal_eq_map_swap y f
    _ = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
      exact mapAlgHom_eq_map
    _ = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
      exact (evalX_eq_map y (Polynomial.Bivariate.swap f)).symm

lemma natDegreeY_swap (f : F[X][Y]) :
    Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.degreeX f := by
  classical
  have h := degreeX_swap (F := F) (f := Polynomial.Bivariate.swap f)
  have hs : Polynomial.Bivariate.swap (R := F) (Polynomial.Bivariate.swap f) = f := by
    simpa using (Polynomial.Bivariate.swap (R := F)).left_inv f
  have h' :
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
        Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) := by
    simpa using h.symm
  have hdeg :
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) =
        Polynomial.Bivariate.degreeX f := by
    simpa using congrArg Polynomial.Bivariate.degreeX hs
  exact h'.trans hdeg

end CommRing


lemma degreeX_mul {F : Type*} [CommRing F] [IsDomain F]
    (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX (f * g) = degreeX f + degreeX g := by
  rw [← natDegreeY_swap, map_mul, degreeY_mul]
  · rw [natDegreeY_swap, natDegreeY_swap]
  · exact fun h => hf (swap.injective (by simpa using h))
  · exact fun h => hg (swap.injective (by simpa using h))

lemma evalX_mul {F : Type*} [CommSemiring F] (x : F) (f g : F[X][Y]) :
    evalX x (f * g) = evalX x f * evalX x g := by
  simp [evalX_eq_map]

end
end Polynomial.Bivariate

/-! Complete declaration axiom census, pinned for integration. -/

/-- info: 'Polynomial.Bivariate.leadingCoeffY_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.leadingCoeffY_eq_zero

/-- info: 'Polynomial.Bivariate.leadingCoeffY_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.leadingCoeffY_ne_zero

/-- info: 'Polynomial.Bivariate.degreeY_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.degreeY_mul

/-- info: 'Polynomial.Bivariate.coeff_natDegree_le_degreeX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.coeff_natDegree_le_degreeX

/-- info: 'Polynomial.Bivariate.evalX_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.evalX_eq_map

/-- info: 'Polynomial.Bivariate.degreeX_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.degreeX_swap

/-- info: 'Polynomial.Bivariate.evalY_eq_evalX_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.evalY_eq_evalX_swap

/-- info: 'Polynomial.Bivariate.natDegreeY_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.natDegreeY_swap

/-- info: 'Polynomial.Bivariate.degreeX_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.degreeX_mul

/-- info: 'Polynomial.Bivariate.evalX_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polynomial.Bivariate.evalX_mul
