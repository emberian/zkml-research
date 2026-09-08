/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Adapted from ArkLib at 22dbd4e836c15a21f68889afa69b7130da04abbb,
Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/BWMatrix.lean.
Only polynomial-matrix algebra is retained; no parallel RS/probability model.
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace Minidregg.RSInterpolation

open Polynomial Matrix Finset
open scoped BigOperators

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι]

def BW_homMatrix {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (e k : ℕ) (ωs : ι → R) (f : ι → R) :
    Matrix ι (Fin ((e + 1) + (e + k))) R :=
  Matrix.of fun i j =>
    if j.1 < e + 1 then
      f i * (ωs i) ^ j.1
    else
      - (ωs i) ^ (j.1 - (e + 1))


theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree = 0 := by
  classical
  have hle : ¬ (j.1 ≤ e) := by
    have hgt : e < j.1 := by
      exact lt_of_lt_of_le (Nat.lt_succ_self e) hj
    exact not_le_of_gt hgt
  -- reduce to the second branch
  simp [BW_homMatrix, hle]


theorem BW_homMatrix_entry_natDegree_le_one {F : Type*} [Field F] {ι : Type*} [Fintype ι] (e k : ℕ)
    (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree ≤ 1 := by
  classical
  by_cases hjle : (j.1 ≤ e)
  · -- j.1 ≤ e
    simp only [BW_homMatrix, Order.lt_add_one_iff, X_mul_C, Matrix.of_apply, hjle, ↓reduceIte]
    have hlin :
        (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
      have hadd :
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤
            max (Polynomial.C (f0 i) : F[X]).natDegree
              (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        exact
          (Polynomial.natDegree_add_le (Polynomial.C (f0 i) : F[X])
            (Polynomial.C (f1 i) * Polynomial.X : F[X]))
      have hC : (Polynomial.C (f0 i) : F[X]).natDegree ≤ 1 := by
        simp
      have hX : (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
        simpa using Polynomial.natDegree_mul_le
          (p := (Polynomial.C (f1 i) : F[X])) (q := (Polynomial.X : F[X]))
      exact le_trans hadd (max_le hC hX)
    have hq : ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree = 0 := by
      simp
    calc
      ((Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]) *
            (Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree ≤
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree +
            ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree :=
        Polynomial.natDegree_mul_le
          (p := (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]))
          (q := (Polynomial.C (ωs i) : F[X]) ^ j.1)
      _ = (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        simp [hq]
      _ ≤ 1 := hlin
  · -- ¬ j.1 ≤ e
    simp [BW_homMatrix, hjle]


theorem BW_homMatrix_map_evalRingHom {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (e k : ℕ) (ωs f0 f1 : ι → F) (z : F) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
          (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))).map
        (Polynomial.evalRingHom z)
      =
      BW_homMatrix (ι := ι) e k ωs (fun i => f0 i + z * f1 i) := by
  ext i j
  by_cases hje : (j.1 ≤ e)
  · have hcomm : f1 i * z = z * f1 i := mul_comm (f1 i) z
    have : f1 i * z = z * f1 i ∨ ωs i = 0 ∧ ¬j = 0 := Or.inl hcomm
    simpa [BW_homMatrix, Nat.lt_succ_iff, hje, mul_add, add_mul] using this
  · simp [BW_homMatrix, hje]


theorem BW_homMatrix_mulVec_eq_zero_iff {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (e k : ℕ)
    (ωs : ι → R) (f : ι → R)
    (a : Fin (e + 1) → R) (b : Fin (e + k) → R) :
    Matrix.mulVec (BW_homMatrix (ι := ι) e k ωs f) (Fin.append a b) = 0 ↔
      (∀ i : ι,
        (∑ t : Fin (e + 1), a t * (ωs i) ^ t.1) * (f i)
          = ∑ s : Fin (e + k), b s * (ωs i) ^ s.1) := by
  classical
  -- helper facts to simplify the `if` guards coming from `BW_homMatrix`
  have hx : ∀ x : Fin (e + 1), (x.1 ≤ e) := fun x => Nat.le_of_lt_succ x.isLt
  have hy : ∀ x : Fin (e + k), ¬ (e + 1 + x.1 ≤ e) := by
    intro x hle
    have : e + 1 ≤ e := le_trans (Nat.le_add_right (e + 1) x.1) hle
    exact Nat.not_succ_le_self e this
  constructor
  · intro h i
    have hi := congrArg (fun v => v i) h
    have hi' :
        (∑ j : Fin ((e + 1) + (e + k)),
            BW_homMatrix (ι := ι) e k ωs f i j * Fin.append a b j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hi
    have hi'' := hi'
    rw [Fin.sum_univ_add] at hi''
    simp only [BW_homMatrix, Order.lt_add_one_iff, Matrix.of_apply, Fin.val_castAdd, hx,
      ↓reduceIte, Fin.append_left, Fin.val_natAdd, hy, add_tsub_cancel_left, Fin.append_right,
      neg_mul, sum_neg_distrib] at hi''
    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      have := eq_neg_of_add_eq_zero_left hi''
      simpa using this
    -- Convert `hAC` into the desired coefficientwise identity.
    calc
      (∑ t : Fin (e + 1), a t * ωs i ^ t.1) * f i
          = f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) := by
              simp [mul_comm]
      _ = ∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1) := by
              simp [Finset.mul_sum]
      _ = ∑ t : Fin (e + 1), f i * ωs i ^ t.1 * a t := by
              simp [mul_left_comm, mul_comm]
      _ = ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
              simpa using hAC
      _ = ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
              simp [mul_comm]
  · intro h
    ext i
    -- expand the matrix-vector multiplication at coordinate `i`
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Fin.sum_univ_add]
    simp only [BW_homMatrix, Order.lt_add_one_iff, Matrix.of_apply, Fin.val_castAdd, hx,
      ↓reduceIte, Fin.append_left, Fin.val_natAdd, hy, add_tsub_cancel_left, Fin.append_right,
      neg_mul, sum_neg_distrib]
    -- turn the hypothesis `h i` into the same normal form
    have hEq0 : f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [mul_comm] using h i
    have hEq1 : (∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1)) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [Finset.mul_sum] using hEq0
    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      -- rearrange products in `hEq1`
      simpa [mul_assoc, mul_left_comm, mul_comm]
    -- use `hAC` to close the goal
    simp [hAC]


theorem Fin_sum_ite_lt_e_add_one (e k : ℕ) :
    (Finset.univ.filter (fun i : Fin ((e + 1) + (e + k)) => i.1 ≤ e)).card = e + 1 := by
  classical
  have hle : e + 1 ≤ (e + 1) + (e + k) := Nat.le_add_right (e + 1) (e + k)
  have hcard_lt0 :
      Fintype.card {i : Fin ((e + 1) + (e + k)) // i.1 < e + 1} = e + 1 :=
    Fintype.card_fin_lt_of_le (m := e + 1) (n := (e + 1) + (e + k)) hle
  have hcard_lt : (Finset.univ.filter (fun i : Fin ((e + 1) + (e + k)) => i.1 < e + 1)).card = e + 1 := by
    simpa [Fintype.card_subtype] using hcard_lt0
  simpa [Nat.lt_succ_iff] using hcard_lt


theorem BW_homMatrix_det_submatrix_natDegree_le_e_add_one {F : Type*} [Field F] {ι : Type*}
    [Fintype ι] (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι) :
    (Matrix.det
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) e k
            (fun i => (Polynomial.C (ωs i) : F[X]))
            (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
          r id)).natDegree ≤ e + 1 := by
  classical
  -- Name the matrices to keep subsequent expressions manageable.
  let M : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let A : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix M r id
  change (Matrix.det A).natDegree ≤ e + 1
  -- Expand determinant as a sum over permutations.
  rw [Matrix.det_apply]
  refine
    (Polynomial.natDegree_sum_le_of_forall_le
        (s :=
          (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i)
        (n := e + 1) ?_)
  intro σ hσ
  -- The permutation sign is a unit (±1), so it does not increase natDegree.
  have hsign :
      (Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  -- Degree of a product is bounded by the sum of degrees.
  have hprod :
      (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        ∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree := by
    simpa using
      (Polynomial.natDegree_prod_le
        (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
        (f := fun i : Fin ((e + 1) + (e + k)) => A (σ i) i))
  -- Only the first `e+1` columns can contribute degree (and each contributes at most 1).
  have hsum :
      (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree) ≤ e + 1 := by
    have hpoint :
        ∀ i : Fin ((e + 1) + (e + k)),
          (A (σ i) i).natDegree ≤ ite (i.1 < e + 1) (1 : ℕ) 0 := by
      intro i
      by_cases hi : i.1 < e + 1
      · -- In the first `e+1` columns, each entry has natDegree ≤ 1.
        have hle1 :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree ≤ 1 :=
          BW_homMatrix_entry_natDegree_le_one (ι := ι) (F := F) e k ωs f0 f1
            (r (σ i)) i
        simpa [A, M, Matrix.submatrix, hi] using hle1
      · -- After column `e+1`, the entry is constant in `X`, hence natDegree = 0.
        have hi' : e + 1 ≤ i.1 := Nat.le_of_not_gt hi
        have hzero :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree = 0 :=
          BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs
            f0 f1 (r (σ i)) i hi'
        have hzero' :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree = 0 := by
          -- For these columns, the definition of `BW_homMatrix` ignores the input `f`.
          simpa [BW_homMatrix, Nat.not_lt_of_ge hi'] using hzero
        have hA : (A (σ i) i).natDegree = 0 := by
          simpa [A, M, Matrix.submatrix] using hzero'
        simp [hi, hA]
    have hle :
        (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree)
          ≤
          ∑ i : Fin ((e + 1) + (e + k)), ite (i.1 < e + 1) (1 : ℕ) 0 := by
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (fun i _ => hpoint i))
    -- `simp` rewrites this indicator sum into a cardinality, so rewrite the axiom the same way.
    have hcard :
        ((Finset.univ.filter (fun x : Fin ((e + 1) + (e + k)) => (x.1 : ℕ) ≤ e)).card : ℕ) = e + 1 := by
      simpa [Nat.lt_succ_iff] using Fin_sum_ite_lt_e_add_one e k
    -- Conclude.
    simpa [hcard] using hle
  -- Assemble the inequalities.
  exact le_trans hsign (le_trans hprod hsum)



theorem RS_isUnit_det_vandermonde_C_of_injective (n : ℕ) (v : Fin n → F)
    (hv : Function.Injective v) :
    IsUnit (Matrix.det (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])))) := by
  classical
  -- The Vandermonde matrix over `F[X]` with constant entries is the entrywise image of the
  -- Vandermonde matrix over `F` under the ring hom `Polynomial.C`.
  have hdet :
      (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X]))).det =
        (Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det) := by
    have hvand :
        (Polynomial.C : F →+* F[X]).mapMatrix (Matrix.vandermonde v) =
          Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])) := by
      ext i j
      simp [Matrix.vandermonde]
    -- Map the determinant through `Polynomial.C` and rewrite the mapped matrix as a Vandermonde.
    simpa [hvand] using
      (RingHom.map_det (f := (Polynomial.C : F →+* F[X])) (M := Matrix.vandermonde v)).symm
  -- Over a field, the Vandermonde determinant is nonzero iff the entries are distinct.
  have hne : (Matrix.vandermonde v).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  -- In a field, nonzero elements are units.
  have hunit : IsUnit ((Matrix.vandermonde v).det) := (isUnit_iff_ne_zero).2 hne
  -- Constant polynomials are units iff their coefficients are units.
  have hunitC : IsUnit ((Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det)) :=
    (Polynomial.isUnit_C (x := (Matrix.vandermonde v).det)).2 hunit
  -- Conclude by rewriting the determinant as a constant polynomial.
  simpa [hdet] using hunitC


theorem RS_mulVec_append_castAdd_natAdd {R : Type*} [NonUnitalNonAssocSemiring R] {ι : Type*}
    (m n : ℕ) (M : Matrix ι (Fin (m + n)) R) (a : Fin m → R) (b : Fin n → R) :
    Matrix.mulVec M (Fin.append a b) =
      Matrix.mulVec (M.submatrix id (Fin.castAdd n)) a +
        Matrix.mulVec (M.submatrix id (Fin.natAdd m)) b := by
  classical
  -- check names
  have _ := (dotProduct : (Fin (m + n) → R) → (Fin (m + n) → R) → R)
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append, Matrix.submatrix]


theorem RS_natDegree_inv_neg_vandermonde_C_eq_zero (n : ℕ) (v : Fin n → F)
    (hv : Function.Injective v) :
    ∀ i j : Fin n,
      ((-Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X])))⁻¹ i j).natDegree =
        0 := by
  classical
  intro i j
  let f : F →+* F[X] := Polynomial.C
  let D0 : Matrix (Fin n) (Fin n) F := -Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) F[X] :=
    -Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X]))
  change ((D⁻¹ i j).natDegree = 0)
  have hDmap : D = D0.map f := by
    ext i j
    simp [D, D0, Matrix.vandermonde, Matrix.map_apply, f, map_pow]
  have hdetV : (Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
    simpa using (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hdetD0 : (Matrix.det D0) ≠ 0 := by
    have h : ((-1 : F) ^ (Fintype.card (Fin n)) * Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (by simp)) hdetV
    simpa [D0, Matrix.det_neg] using h
  have hunit0 : IsUnit (Matrix.det D0) := (isUnit_iff_ne_zero).2 hdetD0
  have hmul0 : D0 * D0⁻¹ = 1 := Matrix.mul_nonsing_inv D0 hunit0
  have hmul : (D0.map f) * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [Matrix.map_mul] using congrArg (fun A : Matrix (Fin n) (Fin n) F => A.map f) hmul0
  have hmul' : D * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [hDmap] using hmul
  have hinv : D⁻¹ = (D0⁻¹).map f := by
    exact Matrix.inv_eq_right_inv (A := D) (B := (D0⁻¹).map f) hmul'
  simp [hinv, Matrix.map_apply, f]



/-- info: 'Minidregg.RSInterpolation.BW_homMatrix_entry_natDegree_eq_zero_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BW_homMatrix_entry_natDegree_eq_zero_of_ge

/-- info: 'Minidregg.RSInterpolation.BW_homMatrix_entry_natDegree_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BW_homMatrix_entry_natDegree_le_one

/-- info: 'Minidregg.RSInterpolation.BW_homMatrix_map_evalRingHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BW_homMatrix_map_evalRingHom

/-- info: 'Minidregg.RSInterpolation.BW_homMatrix_mulVec_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BW_homMatrix_mulVec_eq_zero_iff

/-- info: 'Minidregg.RSInterpolation.Fin_sum_ite_lt_e_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fin_sum_ite_lt_e_add_one

/-- info: 'Minidregg.RSInterpolation.BW_homMatrix_det_submatrix_natDegree_le_e_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BW_homMatrix_det_submatrix_natDegree_le_e_add_one

/-- info: 'Minidregg.RSInterpolation.RS_isUnit_det_vandermonde_C_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RS_isUnit_det_vandermonde_C_of_injective

/-- info: 'Minidregg.RSInterpolation.RS_mulVec_append_castAdd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RS_mulVec_append_castAdd_natAdd

/-- info: 'Minidregg.RSInterpolation.RS_natDegree_inv_neg_vandermonde_C_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RS_natDegree_inv_neg_vandermonde_C_eq_zero

end Minidregg.RSInterpolation
