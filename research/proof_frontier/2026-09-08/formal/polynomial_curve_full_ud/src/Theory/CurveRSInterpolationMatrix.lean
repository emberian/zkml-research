/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Degree-parameterized extension of the existing BW matrix lemmas, following
BCIKS20 §6.1. The matrix itself is the existing BW_homMatrix; no second matrix
or coding definition is introduced. The affine input is no longer hardcoded.
-/
import Theory.RSInterpolationMatrix
import Theory.PolynomialCurve

namespace Minidregg.RSInterpolation
open Polynomial Matrix Finset
open scoped BigOperators
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

theorem BW_entry_natDegree_zero (e d : ℕ) (dom : ι → F) (f : ι → F[X])
    (i : ι) (j : Fin ((e+1)+(e+d))) (hj : e+1 ≤ j.val) :
    (BW_homMatrix e d (fun i => Polynomial.C (dom i)) f i j).natDegree = 0 := by
  have hj' : ¬ j.val ≤ e := by omega
  simp [BW_homMatrix, hj']

theorem BW_entry_natDegree_le (M e d : ℕ) (dom : ι → F) (f : ι → F[X])
    (hdeg : ∀ i, (f i).natDegree ≤ M) (i : ι) (j : Fin ((e+1)+(e+d))) :
    (BW_homMatrix e d (fun i => Polynomial.C (dom i)) f i j).natDegree ≤ M := by
  by_cases hj : j.val ≤ e
  · simpa [BW_homMatrix, hj] using
      (Polynomial.natDegree_mul_le (p := f i)
        (q := (Polynomial.C (dom i)) ^ j.val)).trans (by simpa using hdeg i)
  · simp [BW_homMatrix, hj]

theorem BW_map_eval (e d : ℕ) (dom : ι → F) (f : ι → F[X]) (z : F) :
    (BW_homMatrix e d (fun i => Polynomial.C (dom i)) f).map
      (Polynomial.evalRingHom z) =
    BW_homMatrix e d dom (fun i => (f i).eval z) := by
  ext i j
  by_cases hj : j.val ≤ e <;> simp [BW_homMatrix, hj]

theorem BW_det_natDegree_le (M e d : ℕ) (dom : ι → F) (f : ι → F[X])
    (hdeg : ∀ i, (f i).natDegree ≤ M)
    (r : Fin ((e+1)+(e+d)) → ι) :
    (Matrix.det ((BW_homMatrix e d (fun i => Polynomial.C (dom i)) f).submatrix r id)).natDegree
      ≤ M*(e+1) := by
  classical
  let A := (BW_homMatrix e d (fun i => Polynomial.C (dom i)) f).submatrix r id
  change A.det.natDegree ≤ M*(e+1)
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  have hsign : (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤
      (∏ i, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  have hprod : (∏ i, A (σ i) i).natDegree ≤ ∑ i, (A (σ i) i).natDegree :=
    Polynomial.natDegree_prod_le Finset.univ (fun i => A (σ i) i)
  refine hsign.trans (hprod.trans ?_)
  rw [Fin.sum_univ_add]
  have hleft : (∑ j : Fin (e+1),
      (A (σ (Fin.castAdd (e+d) j)) (Fin.castAdd (e+d) j)).natDegree) ≤ (e+1)*M := by
    calc
      _ ≤ ∑ _j : Fin (e+1), M := Finset.sum_le_sum fun j _ =>
        BW_entry_natDegree_le M e d dom f hdeg _ _
      _ = _ := by simp
  have hright : (∑ j : Fin (e+d),
      (A (σ (Fin.natAdd (e+1) j)) (Fin.natAdd (e+1) j)).natDegree) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact BW_entry_natDegree_zero e d dom f _ _ (by simp)
  rw [hright, add_zero]
  simpa [Nat.mul_comm] using hleft

end Minidregg.RSInterpolation

/-- info: 'Minidregg.RSInterpolation.BW_entry_natDegree_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.RSInterpolation.BW_entry_natDegree_zero

/-- info: 'Minidregg.RSInterpolation.BW_entry_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.RSInterpolation.BW_entry_natDegree_le

/-- info: 'Minidregg.RSInterpolation.BW_map_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.RSInterpolation.BW_map_eval

/-- info: 'Minidregg.RSInterpolation.BW_det_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.RSInterpolation.BW_det_natDegree_le

