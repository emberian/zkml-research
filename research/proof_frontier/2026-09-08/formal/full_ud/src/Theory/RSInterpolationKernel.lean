/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Adapted from ArkLib 22dbd4e836c15a21f68889afa69b7130da04abbb,
AffineLines/GoodCoeffs.lean:212,464. Direct polynomial-matrix interface;
all coding hypotheses are supplied by the existing Selvage RS layer.
-/
import Theory.RSInterpolationMatrix
import Theory.PolynomialMatrixKernel

namespace Minidregg.RSInterpolation
open Polynomial Matrix Finset
open scoped BigOperators
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- At each scalar, an actual nonzero error-locator block is required. -/
def SpecializationKernels (e d : ℕ) (ωs f0 f1 : ι → F) (S : Finset F) : Prop :=
  ∀ z ∈ S, ∃ a : Fin (e+1) → F, ∃ b : Fin (e+d) → F,
    a ≠ 0 ∧ (BW_homMatrix e d ωs (fun i => f0 i + z * f1 i)).mulVec
      (Fin.append a b) = 0

/-- More specializations than the determinant degree force every maximal
minor to vanish; arbitrary row maps are allowed. -/
theorem det_eq_zero_of_specializations
    (e deg : ℕ) (domain : ι ↪ F) (u : Fin 2 → ι → F) (S : Finset F)
    (hS : e+1 < S.card)
    (hgood : SpecializationKernels e deg domain (u 0) (u 1) S)
    (r : Fin ((e+1)+(e+deg)) → ι) :
    Matrix.det ((BW_homMatrix e deg (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))).submatrix r id) = 0 := by
  classical
  let N : ℕ := (e + 1) + (e + deg)
  -- Polynomial matrix and its square submatrix
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg
      (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
  let A : Matrix (Fin N) (Fin N) F[X] :=
    Matrix.submatrix M (r : Fin N → ι) (id : Fin N → Fin N)
  -- Degree bound on det(A)
  have hdeg_det : (Matrix.det A).natDegree ≤ e + 1 := by
    simpa [A, M, N] using
      (BW_homMatrix_det_submatrix_natDegree_le_e_add_one (ι := ι) (F := F) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i)
        (r := (r : Fin N → ι)))
  have he1_lt : e + 1 < S.card := hS
  have hdeg_lt : (Matrix.det A).natDegree < S.card := lt_of_le_of_lt hdeg_det he1_lt
  -- det(A) vanishes on all points of S
  have heval : ∀ z ∈ S, (Matrix.det A).eval z = 0 := by
    intro z hz
    obtain ⟨a,b,ha0,hmul⟩ := hgood z hz
    let v : Fin N → F := Fin.append a b
    have hv_ne : v ≠ 0 := by
      intro hv
      apply ha0
      ext i
      have hvi : v (Fin.castAdd (e + deg) i) = (0 : Fin N → F) (Fin.castAdd (e + deg) i) :=
        congrArg (fun f => f (Fin.castAdd (e + deg) i)) hv
      simpa [v, N] using hvi
    let Mz : Matrix ι (Fin N) F :=
      BW_homMatrix (ι := ι) e deg (fun i => domain i) (fun i => u 0 i + z * u 1 i)
    have hmulMz : Mz *ᵥ v = 0 := by
      simpa [Mz, v, N] using hmul
    have hmulSub :
        (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v = 0 := by
      ext i
      have hi : (Mz *ᵥ v) (r i) = 0 := by
        simpa using congrArg (fun f => f (r i)) hmulMz
      simpa [Matrix.mulVec, Matrix.submatrix] using hi
    have hdetMz :
        Matrix.det (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) = 0 := by
      have hex : ∃ v' : Fin N → F, v' ≠ 0 ∧
          (Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N)) *ᵥ v' = 0 :=
        ⟨v, hv_ne, hmulSub⟩
      exact (Matrix.exists_mulVec_eq_zero_iff
        (M := Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N))).1 hex
    -- Relate evaluation of det(A) to determinant of the evaluated matrix
    have hdet_eval : (Matrix.det A).eval z = Matrix.det (A.map (Polynomial.eval z)) := by
      simpa [Polynomial.coe_evalRingHom] using (RingHom.map_det (Polynomial.evalRingHom z) A)
    -- Identify the mapped matrix with the evaluated BW matrix
    have hAmap : A.map (Polynomial.eval z) =
        Matrix.submatrix Mz (r : Fin N → ι) (id : Fin N → Fin N) := by
      have hMmap : M.map (Polynomial.eval z) = Mz := by
        simpa [M, Mz, N, Polynomial.coe_evalRingHom] using
          (BW_homMatrix_map_evalRingHom (ι := ι) (F := F) e deg (fun i => domain i)
            (fun i => u 0 i) (fun i => u 1 i) z)
      ext i j
      change (M.map (Polynomial.eval z)) (r i) j = Mz (r i) j
      rw [hMmap]
    -- conclude evaluation is zero
    rw [hdet_eval]
    simpa [hAmap] using hdetMz
  -- Root counting: det(A) has too many roots, hence is zero
  have hdetA0 : Matrix.det A = 0 := by
    exact
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p := Matrix.det A) (s := S) heval
        (by simpa using hdeg_lt)
  -- Finish: unfold A and M
  simpa [A, M, N] using hdetA0

/-- Bounded polynomial interpolation certificate. The dimension/radius
hypotheses are integer arithmetic, and specialization certificates are
checked at every element of the explicitly supplied good set. -/
theorem bounded_kernel_of_specializations
    (e deg : ℕ) (domain : ι ↪ F) (u : Fin 2 → ι → F) (S : Finset F)
    (hdegpos : 1 ≤ deg) (hradius : 2*e+deg ≤ Fintype.card ι)
    (hScard : e+1 < S.card)
    (hgood : SpecializationKernels e deg domain (u 0) (u 1) S) :
    ∃ a : Fin (e+1) → F[X], ∃ b : Fin (e+deg) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧
      (∀ s, (b s).natDegree ≤ e+1) ∧
      (BW_homMatrix e deg (fun i => (Polynomial.C (domain i) : F[X]))
        (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))).mulVec
        (Fin.append a b) = 0 := by
  classical
  let m : ℕ := e + 1
  let n : ℕ := e + deg
  let N : ℕ := m + n
  let M : Matrix ι (Fin N) F[X] :=
    BW_homMatrix (ι := ι) e deg (fun i => (Polynomial.C (domain i) : F[X]))
      (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
  have hdetM : ∀ r : Fin N → ι, Matrix.det (Matrix.submatrix M r id) = 0 := by
    intro r
    simpa [M, N, m, n] using
      det_eq_zero_of_specializations e deg domain u S hScard hgood r
  have hcard_n : n ≤ Fintype.card ι := by
    dsimp [n]
    omega
  obtain ⟨rB⟩ : Nonempty (Fin n ↪ ι) := by
    classical
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard_n
  let cL : Fin m → Fin N := fun j => Fin.castAdd n j
  let cR : Fin n → Fin N := fun j => Fin.natAdd m j
  let L : Matrix ι (Fin m) F[X] := Matrix.submatrix M id cL
  let R : Matrix ι (Fin n) F[X] := Matrix.submatrix M id cR
  let A21 : Matrix (Fin n) (Fin m) F[X] := Matrix.submatrix M rB cL
  let D : Matrix (Fin n) (Fin n) F[X] := Matrix.submatrix M rB cR
  have hD : D = -Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])) := by
    funext i j
    have hj' : ¬ e + 1 + (j : ℕ) ≤ e := by
      omega
    simp [D, M, BW_homMatrix, cR, Matrix.vandermonde, m, hj']
  have hvB : Function.Injective (fun i : Fin n => domain (rB i)) := by
    intro i1 i2 h
    apply rB.injective
    apply domain.injective
    exact h
  have hdetV : IsUnit
      (Matrix.det
        (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X])))) := by
    simpa using
      (RS_isUnit_det_vandermonde_C_of_injective (F := F) n (fun i : Fin n => domain (rB i)) hvB)
  have hdetD : IsUnit (Matrix.det D) := by
    have hunitNeg : IsUnit ((-1 : F[X]) ^ Fintype.card (Fin n)) := by
      simpa using (isUnit_neg_one (α := F[X])).pow (Fintype.card (Fin n))
    have hdetD' :
        Matrix.det D =
          (-1 : F[X]) ^ Fintype.card (Fin n) *
            Matrix.det
              (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (domain (rB i)) : F[X]))) := by
      simp [hD, Matrix.det_neg]
    refine hdetD'.symm ▸ (hunitNeg.mul hdetV)
  let : Invertible D := Matrix.invertibleOfIsUnitDet D hdetD
  let K0 : Matrix ι (Fin m) F[X] := L - R * (⅟D * A21)
  have hdetK0 : ∀ rA : Fin m → ι, Matrix.det (K0.submatrix rA id) = 0 := by
    intro rA
    let r : Fin N → ι := Fin.append rA rB
    have hdetA : Matrix.det (M.submatrix r id) = 0 := hdetM r
    let eSum : (Fin m ⊕ Fin n) ≃ Fin N := finSumFinEquiv (m := m) (n := n)
    let Ablocks : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) F[X] :=
      (M.submatrix r id).submatrix eSum eSum
    have hdetAblocks : Matrix.det Ablocks = 0 := by
      have hdetEq : Matrix.det Ablocks = Matrix.det (M.submatrix r id) := by
        simpa [Ablocks] using (Matrix.det_submatrix_equiv_self (e := eSum) (M.submatrix r id))
      simpa [hdetEq] using hdetA
    have hAblocks_eq :
        Ablocks = Matrix.fromBlocks (L.submatrix rA id) (R.submatrix rA id) A21 D := by
      funext i j
      cases i <;> cases j <;>
        simp (config := { zeta := true })
          [Ablocks, eSum, L, R, A21, D, r, cL, cR, Matrix.fromBlocks, N, m, n]
    have hmul :
        Matrix.det D *
            Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) =
          0 := by
      have hformula :=
        (Matrix.det_fromBlocks₂₂ (A := L.submatrix rA id) (B := R.submatrix rA id)
          (C := A21) (D := D))
      simpa [hAblocks_eq, hformula, Matrix.mul_assoc] using hdetAblocks
    have hdetSchur :
        Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21) = 0 := by
      exact (IsUnit.mul_right_eq_zero (a := Matrix.det D)
        (b := Matrix.det ((L.submatrix rA id) - (R.submatrix rA id) * ⅟D * A21)) hdetD).1 hmul
    change ((L - R * (⅟D * A21)).submatrix rA id).det = 0
    have hmatrix : (L - R * (⅟D * A21)).submatrix rA id =
        L.submatrix rA id - R.submatrix rA id * (⅟D * A21) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hmatrix]
    simpa only [Matrix.mul_assoc] using hdetSchur
  have hdegL : ∀ i j, (L i j).natDegree ≤ 1 := by
    intro i j
    simpa [L, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cL j))
  have hdegA21 : ∀ i j, (A21 i j).natDegree ≤ 1 := by
    intro i j
    simpa [A21, cL, M] using
      (BW_homMatrix_entry_natDegree_le_one (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) (rB i) (cL j))
  have hdegR0 : ∀ i j, (R i j).natDegree = 0 := by
    intro i j
    have hj : e + 1 ≤ (cR j).1 := by
      simp [cR, m]
    simpa [R, cR, M] using
      (BW_homMatrix_entry_natDegree_eq_zero_of_ge (F := F) (ι := ι) e deg
        (ωs := fun i => domain i) (f0 := fun i => u 0 i) (f1 := fun i => u 1 i) i (cR j) hj)
  have hdegInvD0 : ∀ i j : Fin n, (D⁻¹ i j).natDegree = 0 := by
    intro i j
    simpa [hD] using
      (RS_natDegree_inv_neg_vandermonde_C_eq_zero
        (F := F) n (fun t : Fin n => domain (rB t)) hvB i j)
  have hdegInvDA21 : ∀ i j, ((⅟D * A21) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ((⅟D i k) * (A21 k j)).natDegree ≤ 1 := by
      intro k hk
      have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
      calc
        ((⅟D i k) * (A21 k j)).natDegree ≤ (⅟D i k).natDegree + (A21 k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + (A21 k j).natDegree := by
          simp [Matrix.invOf_eq_nonsing_inv, hInv']
        _ = (A21 k j).natDegree := by simp
        _ ≤ 1 := hdegA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => (⅟D i k) * (A21 k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegRInvDA21 : ∀ i j, ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
    intro i j
    classical
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (R i k * ((⅟D * A21) k j)).natDegree ≤ 1 := by
      intro k hk
      have hR : (R i k).natDegree = 0 := hdegR0 i k
      calc
        (R i k * ((⅟D * A21) k j)).natDegree ≤ (R i k).natDegree + ((⅟D * A21) k j).natDegree :=
          Polynomial.natDegree_mul_le
        _ = 0 + ((⅟D * A21) k j).natDegree := by simp [hR]
        _ = ((⅟D * A21) k j).natDegree := by simp
        _ ≤ 1 := hdegInvDA21 k j
    have hsum :=
      Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
        (n := 1) (f := fun k : Fin n => R i k * ((⅟D * A21) k j)) hterm
    simpa [Matrix.mul_apply] using hsum
  have hdegK0 : ∀ i j, (K0 i j).natDegree ≤ 1 := by
    intro i j
    have hsub : (L i j - (R * (⅟D * A21)) i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree :=
      Polynomial.natDegree_sub_le (L i j) ((R * (⅟D * A21)) i j)
    have hmax :
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree ≤ 1 := by
      exact max_le_iff.mpr ⟨hdegL i j, hdegRInvDA21 i j⟩
    have : (K0 i j).natDegree ≤
        max (L i j).natDegree ((R * (⅟D * A21)) i j).natDegree := by
      simpa [K0] using hsub
    exact le_trans this hmax
  have hcard_m : m ≤ Fintype.card ι := by
    dsimp [m]
    omega
  obtain ⟨a, ha0, ha_deg, haKer⟩ :=
    PolynomialMatrixKernel.Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (ι := ι) (F := F) e K0
      (by simpa [m] using hcard_m) hdegK0 (by
        intro rA
        simpa [m, K0] using hdetK0 rA)
  let b : Fin n → F[X] := -(⅟D).mulVec (A21.mulVec a)
  refine ⟨a, b, ha0, ha_deg, ?_, ?_⟩
  · intro s
    classical
    have hdegA21mulVec : ∀ i : Fin n, ((A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ t ∈ (Finset.univ : Finset (Fin m)),
          (A21 i t * a t).natDegree ≤ e + 1 := by
        intro t ht
        have hA : (A21 i t).natDegree ≤ 1 := hdegA21 i t
        have ha : (a t).natDegree ≤ e := ha_deg t
        have hmul : (A21 i t * a t).natDegree ≤ (A21 i t).natDegree + (a t).natDegree :=
          Polynomial.natDegree_mul_le
        have hadd : (A21 i t).natDegree + (a t).natDegree ≤ 1 + e := Nat.add_le_add hA ha
        have : (A21 i t * a t).natDegree ≤ 1 + e := le_trans hmul hadd
        simpa [Nat.add_comm] using this
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin m)))
          (n := e + 1) (f := fun t : Fin m => A21 i t * a t) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    have hdegInvDmulVec : ∀ i : Fin n, ((⅟D).mulVec (A21.mulVec a) i).natDegree ≤ e + 1 := by
      intro i
      have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤ e + 1 := by
        intro k hk
        have hInv' : (D⁻¹ i k).natDegree = 0 := hdegInvD0 i k
        have hA : ((A21.mulVec a) k).natDegree ≤ e + 1 := hdegA21mulVec k
        calc
          ((⅟D i k) * (A21.mulVec a k)).natDegree ≤
              (⅟D i k).natDegree + (A21.mulVec a k).natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + (A21.mulVec a k).natDegree := by
            simp [Matrix.invOf_eq_nonsing_inv, hInv']
          _ = (A21.mulVec a k).natDegree := by simp
          _ ≤ e + 1 := hA
      have hsum :=
        Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin n)))
          (n := e + 1) (f := fun k : Fin n => (⅟D i k) * (A21.mulVec a k)) hterm
      simpa [Matrix.mulVec, dotProduct] using hsum
    simpa [b] using hdegInvDmulVec s
  · -- kernel equation
    have hRb : Matrix.mulVec R b = -Matrix.mulVec (R * (⅟D * A21)) a := by
      ext i
      simp [b, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
    have hLR : Matrix.mulVec L a + Matrix.mulVec R b = 0 := by
      have haKer' : Matrix.mulVec (L - R * (⅟D * A21)) a = 0 := by
        simpa [K0] using haKer
      have haKer'' : Matrix.mulVec L a - Matrix.mulVec (R * (⅟D * A21)) a = 0 := by
        simpa [Matrix.sub_mulVec] using haKer'
      simpa [sub_eq_add_neg, hRb] using haKer''
    have hsplit : Matrix.mulVec M (Fin.append a b) = Matrix.mulVec L a + Matrix.mulVec R b := by
      simpa [L, R, cL, cR, N] using
        (RS_mulVec_append_castAdd_natAdd (ι := ι) (R := F[X]) m n M a b)
    change Matrix.mulVec M (Fin.append a b) = 0
    rw [hsplit]
    exact hLR
/-- info: 'Minidregg.RSInterpolation.det_eq_zero_of_specializations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms det_eq_zero_of_specializations

/-- info: 'Minidregg.RSInterpolation.bounded_kernel_of_specializations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bounded_kernel_of_specializations

end Minidregg.RSInterpolation
