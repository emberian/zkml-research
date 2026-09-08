/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases

/-!
# Degree-bounded polynomial matrix kernel

Adapted from ArkLib's BWMatrix.lean at commit
22dbd4e836c15a21f68889afa69b7130da04abbb, declarations at lines
606, 618, 630, 742, 760, 789, 937, 944 and 1175.
Changes: standalone Mathlib-only module; unnecessary section assumptions removed;
universe-polymorphic interface, correctness statement and nonvacuity/falsifier
witnesses added; Lean 4.30 port.
This is candidate-independent algebra, not a Reed–Solomon or proximity theorem.
-/

namespace PolynomialMatrixKernel

open Polynomial Matrix
open scoped BigOperators

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- The conclusion is actual nonzero polynomial annihilation with a degree bound. -/
def BoundedKernel (e : ℕ) (K : Matrix ι (Fin (e + 1)) F[X]) : Prop :=
  ∃ a : Fin (e + 1) → F[X],
    a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0

/-- Source matrix hypotheses, kept separate from the desired kernel conclusion. -/
def Premises (e : ℕ) (K : Matrix ι (Fin (e + 1)) F[X]) : Prop :=
  e + 1 ≤ Fintype.card ι ∧
  (∀ i j, (K i j).natDegree ≤ 1) ∧
  ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0

/-- Every sufficiently tall matrix of linear polynomials with vanishing full
row minors has a nonzero kernel vector whose coordinates have degree ≤ e. -/
def Correctness : Prop :=
  ∀ (e : ℕ) (K : Matrix ι (Fin (e + 1)) F[X]), Premises e K → BoundedKernel e K

namespace Source

open Matrix in
open Polynomial in
theorem RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F))
    (t : Fin (n + 1)) :
    B.adjugate t (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (t : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
  simpa [Fin.succAbove_last] using
    (Matrix.adjugate_fin_succ_eq_det_submatrix (A := B) (i := t) (j := Fin.last n))

open Matrix in
open Polynomial in
theorem RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F)) :
    B.adjugate (Fin.last n) (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
  -- apply the provided adjugate formula with t = Fin.last n
  simpa using
    (RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := n) (B := B) (t := Fin.last n))

open Matrix in
open Polynomial in
theorem RS_det_submatrix_eq_zero_of_det_eq_zero (n : ℕ)
    (K : Matrix (Fin n) (Fin n) (Polynomial F))
    (hdet : Matrix.det K = 0)
    (I J : Fin n ↪ Fin n) :
    Matrix.det (K.submatrix I J) = 0 := by
  classical
  let eI : Fin n ≃ Fin n := I.equivOfFiniteSelfEmbedding
  let eJ : Fin n ≃ Fin n := J.equivOfFiniteSelfEmbedding
  have hI : (eI.toEmbedding : Fin n ↪ Fin n) = I := by
    simp [eI]
  have hJ : (eJ.toEmbedding : Fin n ↪ Fin n) = J := by
    simp [eJ]
  have hsub : K.submatrix I J = K.submatrix eI eJ := by
    ext i j
    have hIi : eI i = I i := by
      have := congrArg (fun f : Fin n ↪ Fin n => f i) hI
      simpa [Equiv.toEmbedding_apply] using this
    have hJj : eJ j = J j := by
      have := congrArg (fun f : Fin n ↪ Fin n => f j) hJ
      simpa [Equiv.toEmbedding_apply] using this
    simp [Matrix.submatrix_apply, hIi, hJj]
  calc
    Matrix.det (K.submatrix I J) = Matrix.det (K.submatrix eI eJ) := by
      simp [hsub]
    _ = Matrix.det (K.reindex eI.symm eJ.symm) := by
      simp [Matrix.reindex_apply]
    _ = Equiv.Perm.sign (eJ.symm.trans eI) * Matrix.det K := by
      simpa [eI, eJ] using (Matrix.det_reindex (e := eI.symm) (e' := eJ.symm) K)
    _ = 0 := by
      simp [hdet]

open Matrix in
open Polynomial in
theorem RS_mulVec_adjugate_col_eq_det (n : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial F))
    (j : Fin n) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) =
      (fun i : Fin n => if i = j then Matrix.det A else 0) := by
  classical
  funext i
  calc
    Matrix.mulVec A (fun k : Fin n => A.adjugate k j) i = (A * A.adjugate) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    _ = (A.det • (1 : Matrix (Fin n) (Fin n) (Polynomial F))) i j := by
      simpa using
        congrArg (fun M : Matrix (Fin n) (Fin n) (Polynomial F) => M i j) (Matrix.mul_adjugate A)
    _ = (if i = j then Matrix.det A else 0) := by
      simp [Matrix.one_apply]

open Matrix in
open Polynomial in
theorem RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) (j : Fin n) (hdet : Matrix.det A = 0) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) = 0 := by
  classical
  -- Rewrite using the adjugate column identity
  rw [RS_mulVec_adjugate_col_eq_det n A j]
  -- Now simplify using det A = 0
  ext i
  by_cases h : i = j
  · simp [h, hdet]
  · simp [h]


open Polynomial in
open Matrix in
theorem RS_natDegree_det_le_of_entry_natDegree_le_one (n : ℕ) (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ 1) :
    (Matrix.det A).natDegree ≤ n := by
  classical
  rw [Matrix.det_apply]
  -- bound degree of the determinant by bounding each Leibniz summand
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)) ?_
  intro σ hσ
  -- ignore the scalar `sign σ` (it is ±1)
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)).natDegree
        ≤ (∏ i : Fin n, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  -- bound the product by summing the bounds on the factors
  have hprod : (∏ i : Fin n, A (σ i) i).natDegree ≤ n := by
    have h1 : (∏ i : Fin n, A (σ i) i).natDegree ≤ ∑ i : Fin n, (A (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => A (σ i) i))
    have h2 : (∑ i : Fin n, (A (σ i) i).natDegree) ≤ n := by
      -- each summand is ≤ 1 by hypothesis
      have hle1 : ∀ i : Fin n, (A (σ i) i).natDegree ≤ 1 := by
        intro i
        simpa using hdeg (σ i) i
      -- sum of `n` terms each ≤ 1
      have hsum' : (∑ i ∈ (Finset.univ : Finset (Fin n)), (A (σ i) i).natDegree)
          ≤ (Finset.univ : Finset (Fin n)).card • (1 : ℕ) := by
        refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (A (σ i) i).natDegree) (n := (1 : ℕ)) ?_
        intro i hi
        simpa using hle1 i
      -- rewrite sums/cards
      simpa [Finset.card_univ, Fintype.card_fin] using hsum'
    exact le_trans h1 h2
  exact le_trans hsign hprod

open Matrix in
theorem adjugate_updateRow_same_col {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i j : n) (b : n → R) :
    (A.updateRow i b).adjugate j i = A.adjugate j i := by
  simp [Matrix.adjugate_apply]

open scoped BigOperators in
open Matrix in
theorem det_updateRow_eq_sum_mul_adjugate_col {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (i : n) (b : n → R) :
    (A.updateRow i b).det = ∑ j : n, b j * A.adjugate j i := by
  classical
  -- Laplace expansion of the determinant along the updated row
  simpa [Matrix.updateRow_apply, adjugate_updateRow_same_col, mul_assoc] using
    (Matrix.det_eq_sum_mul_adjugate_row (A := A.updateRow i b) (i := i))

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix ι (Fin (e + 1)) F[X])
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ (0 : F[X])
  let : DecidablePred P := Classical.decPred _
  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simp
  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := by
    simpa [r] using
      (Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0)
  rcases Pr with ⟨I, J, hdetIJ⟩
  have hnotPn : ¬ P n := by
    intro hPn
    rcases hPn with ⟨I0, J0, hdet0⟩
    let A : Matrix (Fin n) (Fin n) F[X] := K.submatrix I0 id
    have hdetA : Matrix.det A = 0 := by
      simpa [A] using hdet I0
    have hdet_sub : Matrix.det (A.submatrix (Function.Embedding.refl _) J0) = 0 :=
      RS_det_submatrix_eq_zero_of_det_eq_zero n A hdetA (Function.Embedding.refl _) J0
    have hdetK : Matrix.det (K.submatrix I0 J0) = 0 := by
      have hmatrix : K.submatrix I0 J0 = A.submatrix (Function.Embedding.refl _) J0 := by
        ext i j
        rfl
      rw [hmatrix]
      exact hdet_sub
    exact hdet0 hdetK
  have hrle : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)
  have hrne : r ≠ n := by
    intro hre
    have hEq : Nat.findGreatest P n = n := by
      simpa [r] using hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hEq |>.2.1
    have hn0 : n ≠ 0 := by
      simp [n]
    exact hnotPn (hcond hn0)
  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hrlt
    exact Nat.lt_succ_iff.mp this
  have hcard' : n ≤ Fintype.card ι := by
    simpa [n] using hcard
  have hrltcardι : r < Fintype.card ι := lt_of_lt_of_le hrlt hcard'
  -- pick i0 ∉ range I
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    simpa [sI] using hrltcardι
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    apply hi0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨i, by simp, rfl⟩
  -- pick j0 ∉ range J
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    simpa [sJ] using hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    apply hj0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨j, by simp, rfl⟩
  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := by
      simp [r]
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb
  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    have : P (r + 1) := ⟨I', J', by simpa [B] using hne⟩
    exact hnotPr1 this
  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i
    funext j
    simp [B, I', J']
  have hu_last : u (Fin.last r) =
      (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
    simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
  have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
    have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) := by
      have hminus1 : (-1 : F[X]) ≠ (0 : F[X]) := by simp
      exact pow_ne_zero _ hminus1
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
      simpa [hsub_cast] using hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor
  -- degree bound on u
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ r := by
    intro t
    have hu_t : u t =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      apply RS_natDegree_det_le_of_entry_natDegree_le_one (n := r)
        (A := B.submatrix Fin.castSucc t.succAbove)
      intro i j
      -- entries come from K
      simpa [B] using hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdeg_sign : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      simp
    have hmul_le :
        (u t).natDegree ≤
          ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
      simpa [hu_t] using
        (Polynomial.natDegree_mul_le
          (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
          (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))
    have hdeg_rhs :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      simpa [hdeg_sign] using hdeg_det
    exact le_trans hmul_le hdeg_rhs
  -- extend u to all columns
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hval : a (J' (Fin.last r)) = 0 := by
      simpa using congrArg (fun f : Fin n → F[X] => f (J' (Fin.last r))) ha0
    have : u (Fin.last r) = 0 := by
      simpa [ha_on (Fin.last r)] using hval
    exact hu_last_ne this
  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      exact le_trans (by simpa [ha_on t] using hdeg_u t) hrle_e
    · have haj : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj)
      simp [haj]
  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by
          simpa [Set.mem_range] using hj
        have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
              (b := j) hb)
        simp [haj]
      · intro t
        simp [ha_on t]
    change (∑ j, K i j * a j) = ∑ t, K i (J' t) * u t
    exact hsum.symm
  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc t)) hBu
        simpa using this
      have hrow' : (∑ x : Fin (r + 1), K (I t) (J' x) * u x) = 0 := by
        change (∑ x, B (Fin.castSucc t) x * u x) = 0 at hrow
        simpa [B, I', J'] using hrow
      rw [hmul_formula (i := I t)]
      simpa using hrow'
    · -- i ∉ range I
      have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        have : P (r + 1) := ⟨Ii, J', by simpa using hne⟩
        exact hnotPr1 this
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x
        funext y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · -- x = last
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
        · intro x
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi
      have hdet_expr : Matrix.det (B.updateRow (Fin.last r) b) =
          ∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r) := by
        simpa using
          det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 := by
        simpa [hdet_expr] using hdet_update
      have hsum0' : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [b, u] using hsum0
      rw [hmul_formula (i := i)]
      simpa using hsum0'
  refine ⟨a, ha_ne, ?_, hmulVec⟩
  intro t
  simpa using hdeg_a t

end Source

/-- The degree-bounded kernel theorem, with all source hypotheses explicit. -/
theorem correctness : Correctness (F := F) (ι := ι) := by
  intro e K h
  exact Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one
    e K h.1 h.2.1 h.2.2

/-- A nonzero singular matrix of linear polynomials over the same arbitrary field. -/
noncomputable def witnessMatrix : Matrix (Fin 2) (Fin 2) F[X] := fun _ => ![X, 1]

/-- Its nonzero kernel vector has a coordinate of degree exactly one. -/
noncomputable def witnessVector : Fin 2 → F[X] := ![1, -X]

theorem witnessMatrix_premises : Premises 1 (witnessMatrix (F := F)) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro i j
    fin_cases j <;> simp [witnessMatrix]
  · intro r
    simp [Matrix.det_fin_two, witnessMatrix]

theorem witnessVector_valid :
    witnessVector (F := F) ≠ 0 ∧
    (∀ t, (witnessVector (F := F) t).natDegree ≤ 1) ∧
    Matrix.mulVec (witnessMatrix (F := F)) witnessVector = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [witnessVector] at this
  · intro t
    fin_cases t <;> simp [witnessVector]
  · ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, witnessMatrix, witnessVector]

/-- Premise inhabitation uses a nonzero matrix, uniformly over every field. -/
theorem premises_inhabited :
    ∃ K : Matrix (Fin 2) (Fin 2) F[X], K ≠ 0 ∧ Premises 1 K := by
  refine ⟨witnessMatrix, ?_, witnessMatrix_premises⟩
  intro h
  have := congrFun (congrFun h 0) 1
  simp [witnessMatrix] at this

/-- Both the input premises and the concrete conclusion are satisfied. -/
theorem satisfiable :
    ∃ K : Matrix (Fin 2) (Fin 2) F[X], Premises 1 K ∧ BoundedKernel 1 K :=
  ⟨witnessMatrix, witnessMatrix_premises, witnessVector, witnessVector_valid⟩

/-- Falsifier: a linear identity matrix satisfies size/degree requirements but
has no nonzero kernel. The vanishing-minor hypothesis cannot be dropped. -/
theorem determinant_hypothesis_teeth (e : ℕ) :
    e + 1 ≤ Fintype.card (Fin (e + 1)) ∧
    (∀ i j, ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) F[X]) i j).natDegree ≤ 1) ∧
    ¬ BoundedKernel e (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) F[X]) := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rintro ⟨a, ha, _, hmul⟩
    exact ha (by simpa using hmul)

/-- The degree bound is substantive: the singular witness matrix has no
nonzero kernel vector consisting entirely of constant polynomials. -/
theorem degree_bound_teeth :
    ¬ ∃ a : Fin 2 → F[X], a ≠ 0 ∧
      (∀ t, (a t).natDegree ≤ 0) ∧ Matrix.mulVec (witnessMatrix (F := F)) a = 0 := by
  rintro ⟨a, ha, hdeg, hmul⟩
  have ha0 : a 0 = C ((a 0).coeff 0) := eq_C_of_natDegree_le_zero (hdeg 0)
  have ha1 : a 1 = C ((a 1).coeff 0) := eq_C_of_natDegree_le_zero (hdeg 1)
  have heq : X * a 0 + a 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, witnessMatrix]
      using congrFun hmul 0
  have hc0 : (a 0).coeff 0 = 0 := by
    have h := congrArg (fun p : F[X] => p.coeff 1) heq
    have hzero : (a 1).coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (hdeg 1) Nat.zero_lt_one)
    simpa only [coeff_add, coeff_X_mul, hzero, add_zero, coeff_zero] using h
  have hc1 : (a 1).coeff 0 = 0 := by
    have h := congrArg (fun p : F[X] => p.coeff 0) heq
    simpa using h
  apply ha
  funext t
  fin_cases t
  · simpa [hc0] using ha0
  · simpa [hc1] using ha1

end PolynomialMatrixKernel

/-- info: 'PolynomialMatrixKernel.Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one

/-- info: 'PolynomialMatrixKernel.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.correctness

/-- info: 'PolynomialMatrixKernel.witnessMatrix_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.witnessMatrix_premises

/-- info: 'PolynomialMatrixKernel.witnessVector_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.witnessVector_valid

/-- info: 'PolynomialMatrixKernel.premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.premises_inhabited

/-- info: 'PolynomialMatrixKernel.satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.satisfiable

/-- info: 'PolynomialMatrixKernel.determinant_hypothesis_teeth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.determinant_hypothesis_teeth

/-- info: 'PolynomialMatrixKernel.degree_bound_teeth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolynomialMatrixKernel.degree_bound_teeth
