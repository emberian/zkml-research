/- Native eight-coset quotient reconstruction as ordinary polynomials.
The native verifier uses coset Lagrange weights, not coefficient chunks. -/
import Compiler.AirPolynomialOod

namespace Minidregg.Compiler.Ir2QuotientRecomposition
open Polynomial Minidregg.Selvage BabyBearExt4 AirPolynomialOod
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

/-- Z_{shift*H_n}(X)=(X/shift)^n-1. -/
def cosetZero (n : ℕ) (shift : Ext4) : Ext4[X] := C ((shift^n)⁻¹)*X^n-1

def weight (n : ℕ) (shift : Fin 8 → Ext4) (j : Fin 8) : Ext4[X] :=
  ∏ l ∈ Finset.univ.erase j,cosetZero n (shift l)*C (((cosetZero n (shift l)).eval (shift j))⁻¹)

def coordinateChunk (u : Ext4) (q : Fin 8 → Fin 4 → Ext4[X]) (j : Fin 8) : Ext4[X] :=
  ∑ k,C (u^k.val)*q j k

def recompose (n : ℕ) (shift : Fin 8 → Ext4) (u : Ext4)
    (q : Fin 8 → Fin 4 → Ext4[X]) : Ext4[X] :=
  ∑ j,weight n shift j*coordinateChunk u q j

/-- This is literally the native weighted sum of four-coordinate chunk openings. -/
theorem recompose_eval (n : ℕ) (shift : Fin 8 → Ext4) (u ζ : Ext4)
    (q : Fin 8 → Fin 4 → Ext4[X]) :
    (recompose n shift u q).eval ζ=
      ∑ j,(∏ l ∈ Finset.univ.erase j,
        ((cosetZero n (shift l)).eval ζ)/((cosetZero n (shift l)).eval (shift j)))*
          (∑ k,u^k.val*(q j k).eval ζ) := by
  simp [recompose,weight,coordinateChunk,Polynomial.eval_finsetSum,Polynomial.eval_prod,div_eq_mul_inv]

theorem cosetZero_degree (n : ℕ) (shift : Ext4) : (cosetZero n shift).natDegree ≤ n := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · simp

theorem weight_degree (n : ℕ) (shift : Fin 8 → Ext4) (j : Fin 8) :
    (weight n shift j).natDegree ≤ 7*n := by
  unfold weight
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ l ∈ Finset.univ.erase j,(cosetZero n (shift l)*C (((cosetZero n (shift l)).eval (shift j))⁻¹)).natDegree
      ≤ ∑ l ∈ Finset.univ.erase j,n := by
        apply Finset.sum_le_sum
        intro l hl
        exact (Polynomial.natDegree_mul_C_le _ _).trans (cosetZero_degree _ _)
    _ = 7*n := by simp

theorem coordinate_degree (d : ℕ) (u : Ext4) (q : Fin 8 → Fin 4 → Ext4[X])
    (hq : ∀ j k,(q j k).natDegree ≤ d) (j : Fin 8) :
    (coordinateChunk u q j).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hq j k)

theorem recompose_degree (n d : ℕ) (shift : Fin 8 → Ext4) (u : Ext4)
    (q : Fin 8 → Fin 4 → Ext4[X]) (hq : ∀ j k,(q j k).natDegree ≤ d) :
    (recompose n shift u q).natDegree ≤ 7*n+d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_mul_le).trans
    (Nat.add_le_add (weight_degree _ _ _) (coordinate_degree d u q hq j))

/-- At the actual H13 size and the PCS explanation's inclusive degree cap,
recomposed quotient degree is at most73728. Multiplication by Z_H gives81920. -/
theorem actual_quotient_degree (shift : Fin 8 → Ext4) (u : Ext4)
    (q : Fin 8 → Fin 4 → Ext4[X]) (hq : ∀ j k,(q j k).natDegree ≤ 16384) :
    (recompose 8192 shift u q).natDegree ≤ 73728 ∧
    ((X^8192-1)*recompose 8192 shift u q).natDegree ≤ 81920 := by
  have hd := recompose_degree 8192 16384 shift u q hq
  constructor
  · exact hd
  · apply (Polynomial.natDegree_mul_le).trans
    have hz : ((X:Ext4[X])^8192-1).natDegree ≤ 8192 := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      simp
    exact Nat.add_le_add hz hd

end
end Minidregg.Compiler.Ir2QuotientRecomposition

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.recompose_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.recompose_eval

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.cosetZero_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.cosetZero_degree

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.weight_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.weight_degree

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.coordinate_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.coordinate_degree

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.recompose_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.recompose_degree

/-- info: 'Minidregg.Compiler.Ir2QuotientRecomposition.actual_quotient_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Compiler.Ir2QuotientRecomposition.actual_quotient_degree

