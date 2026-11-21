/-
# `Theory/ZkmlDeltaNet.lean` — `Qwen3.8-Next` Gated DeltaNet Erase-and-Write & Chunkwise WY Bilinear Reduction

**Substrate, said out loud: this is Lean-authored denotational and algebraic metatheory.**
Mathlib-only imports (`scripts/check-import-boundary.sh`: `Theory/` tier only). Zero `sorry`,
zero custom `axiom`, zero `native_decide`, zero `#guard`.

## What this module proves (and why it unlocks both `zkML` and constant-state `vFHEML`)

`Qwen3.8-Next` (`arXiv:2608.30320` §2.1.1, Eqs. 1–5; Yang et al., 2024) replaces 3 of every 4
softmax self-attention layers with **Gated DeltaNet (`GDN`)**, maintaining a fixed-size per-head
fast-weight matrix state `S_t ∈ R^{d_k × d_v}` across arbitrary sequence lengths `T` (`256K–1M`):

1. **Part A — Residual Erase-and-Write ↔ Decayed Householder Recurrence (`Eqs. 1–5`)**:
   - `gdnStep α β k v S` computes `S̃ = α • S` (`Eq. 1`), residual error `e = v - S̃ᵀ k` (`Eq. 2`),
     and rank-1 update `S' = S̃ + β • (k ⊗ e)` (`Eq. 3`) over **any commutative ring `R`**.
   - `gdnStep_eq_householder_update` proves `Eq. 5` identically over any `CommRing R`:
       `gdnStep α β k v S = α • ((1 - β • (k ⊗ k)) * S) + β • (k ⊗ v)`.
   - `gdnStep_targeted_erase` & `gdnStep_preserves_orthogonal`: at `α = 1, β = 1` with unit key
     `k · k = 1`, writing `(k, v)` erases the prior association along `k` and reads back `v`
     **exactly** (`(gdnStep 1 1 k v S)ᵀ k = v`), while leaving any orthogonal key `q ⊥ k`
     identically unchanged. `gdnStep_unnormalized_erase_fails` exhibits the falsifier tooth when
     `k · k ≠ 1`.

2. **Part B — Chunkwise WY Unit-Lower-Triangular Inversion-to-Bilinear Equivalence**:
   In chunkwise parallel prefill/transcript proving (`C = 64`), sequential `GDN` steps collapse
   into matrix contractions plus solving a unit-lower-triangular system `(I + L) U = V` where `L`
   is strictly lower triangular (`L_{i,j} = 0` for `i ≤ j`). Naively proving `U = (I + L)⁻¹ V`
   would require either `C` sequential GKR layers of forward substitution or matrix inversion
   (which doesn't even exist over non-field rings until nilpotency is proved!).
   - `strictLowerTri_pow_zero_above` & `strictLowerTri_pow_card_eq_zero`: for any strictly lower
     triangular `C × C` matrix `L` over **any `CommRing R`**, `(L ^ m)_{i,j} = 0` whenever
     `i < j + m`, hence **`L ^ C = 0`**.
   - `neumannInv L := ∑_{k < C} (-L)^k`: proves `(1 + L) * neumannInv L = 1` and
     `neumannInv L * (1 + L) = 1` **division-free over any `CommRing R`** — including non-fields
     with zero divisors such as `ZMod (2^k)` / `ZMod t` in BFV and SPDZ2k!
   - `wyChunk_bilinear_iff_recurrence`: proves the three-way equivalence
       `(1 + L) * U = V  ↔  U = neumannInv L * V  ↔  ∀ i col, U i col = V i col - ∑_{j < i} L i j * U j col`
     so a ZK or vFHE verifier checks `(1 + L) * U = V` (`U + L * U = V`) via **ONE flat degree-2
     bilinear `EinSumcheck`** with **zero** sequential GKR depth and **zero** field inversions!
   - **Witnesses + Falsifier Tooth**: concrete `C = 3` witnesses over both `ℤ` and non-field
     `ZMod 16` (`L ^ 2 ≠ 0 ∧ L ^ 3 = 0`), plus falsifier `L = -1` (violating strict lower
     triangularity on the diagonal `i = j`, where `(1 + L) * U₁ = (1 + L) * U₂` holds for
     distinct `U₁ ≠ U₂`).
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Minidregg.Theory.ZkmlDeltaNet

open Matrix

/-! ## Part A. Gated DeltaNet (`arXiv:2608.30320` Eqs. 1–5) Erase-and-Write Equivalence -/

section GatedDeltaNet

variable {R : Type*} [CommRing R] {dk dv : ℕ}

/-- **Eq. (2) Residual Prediction Error (`gdnResidual`)**: `e_t = v_t - (α_t S_{t-1})ᵀ k_t`. -/
def gdnResidual (α : R) (k : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R) : Fin dv → R :=
  v - (α • S)ᵀ.mulVec k

/-- **Eqs. (1–3) Gated DeltaNet State Update (`gdnStep`)**:
`S̃_{t-1} = α_t S_{t-1}`, `e_t = v_t - S̃_{t-1}ᵀ k_t`, `S_t = S̃_{t-1} + β_t k_t e_tᵀ`.
Requires only `O(d_k d_v)` state — independent of sequence length `T`! -/
def gdnStep (α β : R) (k : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin dk) (Fin dv) R :=
  α • S + β • Matrix.vecMulVec k (gdnResidual α k v S)

/-- **Eq. (4) Gated DeltaNet State Readout (`gdnReadout`)**: `y_t = S_tᵀ q_t`. -/
def gdnReadout (q : Fin dk → R) (S : Matrix (Fin dk) (Fin dv) R) : Fin dv → R :=
  Sᵀ.mulVec q

/-- **Theorem (`gdnStep_eq_householder_update`, `arXiv:2608.30320` Eq. 5):**
Over ANY commutative ring `R`, the two-stage residual delta rule (`Eqs. 1–3`) equals the decayed
generalized Householder transition `α • ((1 - β • (k ⊗ k)) * S) + β • (k ⊗ v)`. -/
theorem gdnStep_eq_householder_update (α β : R) (k : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnStep α β k v S =
      α • ((1 - β • Matrix.vecMulVec k k) * S) + β • Matrix.vecMulVec k v := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  ext i j
  have hL :
      β * (k i * (v j - ∑ x : Fin dk, α * S x j * k x)) =
        β * (k i * v j) - α * ∑ x : Fin dk, β * (k i * k x) * S x j := by
    rw [mul_sub (k i), mul_sub β, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  change α * S i j + β * (k i * (v j - ∑ x : Fin dk, α * S x j * k x)) =
    α * (S i j - ∑ x : Fin dk, β * (k i * k x) * S x j) + β * (k i * v j)
  rw [hL]
  ring

/-- **Targeted Erase-and-Write (`gdnStep_targeted_erase`):**
When `α = 1`, `β = 1`, and `k` has unit norm (`dotProduct k k = 1`), writing `(k, v)` completely
erases whatever value `S` previously stored along `k` and reads back `v` **on the nose**:
`(gdnStep 1 1 k v S)ᵀ k = v`. -/
theorem gdnStep_targeted_erase (k : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R) (hk : dotProduct k k = 1) :
    (gdnStep 1 1 k v S)ᵀ.mulVec k = v := by
  ext j
  have hkk : ∑ i : Fin dk, k i * k i = 1 := hk
  simp only [gdnStep, gdnResidual, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply, Pi.sub_apply, one_smul]
  have hexp :
      (∑ i : Fin dk, (S i j + k i * (v j - ∑ x : Fin dk, S x j * k x)) * k i) =
        (∑ i : Fin dk, S i j * k i)
          + (∑ i : Fin dk, k i * k i) * (v j - ∑ x : Fin dk, S x j * k x) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hkk, one_mul]
  ring

/-- **Orthogonal Key Preservation (`gdnStep_preserves_orthogonal`):**
At `α = 1`, writing `(k, v)` with ANY write gate `β` leaves associations along every orthogonal
query `q` (`dotProduct k q = 0`) identically untouched. -/
theorem gdnStep_preserves_orthogonal (β : R) (k q : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R) (horth : dotProduct k q = 0) :
    (gdnStep 1 β k v S)ᵀ.mulVec q = Sᵀ.mulVec q := by
  ext j
  have hkq : ∑ i : Fin dk, k i * q i = 0 := horth
  simp only [gdnStep, gdnResidual, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.sub_apply,
    one_smul, smul_eq_mul]
  have hexp :
      (∑ i : Fin dk, (S i j + β * (k i * (v j - ∑ x : Fin dk, S x j * k x))) * q i) =
        (∑ i : Fin dk, S i j * q i)
          + β * (v j - ∑ x : Fin dk, S x j * k x) * (∑ i : Fin dk, k i * q i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hkq, mul_zero, add_zero]

/-- **Satisfying Witness (`gdnStep_erase_witness`):** concrete 2D unit key `k = ![1, 0]` over `ℤ`
erases non-zero prior state `S = ![![99, -42], ![7, 13]]`, reads back `v = ![5, 8]` along `k`, and
preserves orthogonal readout `![7, 13]` along `q = ![0, 1]`. -/
theorem gdnStep_erase_witness :
    let k : Fin 2 → ℤ := ![1, 0]
    let q : Fin 2 → ℤ := ![0, 1]
    let v : Fin 2 → ℤ := ![5, 8]
    let S : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![99, -42], ![7, 13]]
    dotProduct k k = 1 ∧
    dotProduct k q = 0 ∧
    (gdnStep 1 1 k v S)ᵀ.mulVec k = v ∧
    (gdnStep 1 1 k v S)ᵀ.mulVec q = ![7, 13] := by
  decide

/-- **Falsifier Tooth (`gdnStep_unnormalized_erase_fails`):** dropping `dotProduct k k = 1`
(`Eq. 7`'s `L2Norm` premise, e.g. `k = ![2]` with `k · k = 4 ≠ 1`) breaks targeted erase-and-write:
writing `v = ![1]` into `S = 0` reads back `![4] ≠ ![1]`! -/
theorem gdnStep_unnormalized_erase_fails :
    let k : Fin 1 → ℤ := ![2]
    let v : Fin 1 → ℤ := ![1]
    let S : Matrix (Fin 1) (Fin 1) ℤ := 0
    dotProduct k k ≠ 1 ∧ (gdnStep 1 1 k v S)ᵀ.mulVec k ≠ v := by
  decide

end GatedDeltaNet

/-! ## Part B. Chunkwise WY Unit-Lower-Triangular Inversion-to-Bilinear Equivalence -/

section ChunkwiseWY

/-- Strict lower triangularity of a `C × C` chunk coupling matrix `L`: all entries on and above
the main diagonal vanish (`i ≤ j → L i j = 0`). -/
def IsStrictLowerTri {R : Type*} [Zero R] {C : ℕ} (L : Matrix (Fin C) (Fin C) R) : Prop :=
  ∀ i j : Fin C, i ≤ j → L i j = 0

/-- Negating a strictly lower triangular matrix preserves strict lower triangularity. -/
theorem IsStrictLowerTri.neg {R : Type*} [Ring R] {C : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L) :
    IsStrictLowerTri (-L) := by
  intro i j hij
  simp [hL i j hij]

/-- **Band-Shift Nilpotency Lemma (`strictLowerTri_pow_zero_above`):**
For any strictly lower triangular `L`, `(L ^ m) i j = 0` whenever `i.val < j.val + m`. Each
multiplication shifts the nonzero subdiagonal band strictly downward by one step. -/
theorem strictLowerTri_pow_zero_above {R : Type*} [CommRing R] {C : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L) :
    ∀ (m : ℕ) (i j : Fin C), i.val < j.val + m → (L ^ m) i j = 0
  | 0, i, j, hij => by
      have hne : i ≠ j := by
        intro h
        subst h
        omega
      rw [pow_zero]
      exact Matrix.one_apply_ne hne
  | m + 1, i, j, hij => by
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hkj : k ≤ j
      · rw [hL k j hkj, mul_zero]
      · have hlt : j.val < k.val := lt_of_not_ge hkj
        have hik : i.val < k.val + m := by omega
        rw [strictLowerTri_pow_zero_above hL m i k hik, zero_mul]

/-- **Exact Nilpotency (`strictLowerTri_pow_card_eq_zero`):**
Every strictly lower triangular `C × C` matrix `L` over ANY `CommRing R` satisfies `L ^ C = 0`. -/
theorem strictLowerTri_pow_card_eq_zero {R : Type*} [CommRing R] {C : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L) :
    L ^ C = 0 := by
  ext i j
  exact strictLowerTri_pow_zero_above hL C i j (by omega)

/-- **Division-Free Neumann Inverse (`neumannInv`)**:
`neumannInv L = ∑_{k=0}^{C-1} (-L)^k`. Defined using ONLY ring additions and multiplications, so
`(1 + L)⁻¹` exists constructively over non-field rings (`ℤ`, `ZMod t`, `ZMod (2^64)`). -/
def neumannInv {R : Type*} [CommRing R] {C : ℕ} (L : Matrix (Fin C) (Fin C) R) :
    Matrix (Fin C) (Fin C) R :=
  (Finset.range C).sum (fun k => (-L) ^ k)

/-- Generic ring telescoping identity `(1 - X) * ∑_{k<n} X^k = 1 - X^n` and its right-hand twin. -/
theorem one_sub_mul_geom_sum {A : Type*} [Ring A] (X : A) :
    ∀ n : ℕ,
      (1 - X) * (Finset.range n).sum (fun k => X ^ k) = 1 - X ^ n ∧
      (Finset.range n).sum (fun k => X ^ k) * (1 - X) = 1 - X ^ n
  | 0 => by simp
  | n + 1 => by
      obtain ⟨ihL, ihR⟩ := one_sub_mul_geom_sum X n
      rw [Finset.sum_range_succ]
      constructor
      · calc (1 - X) * ((Finset.range n).sum (fun k => X ^ k) + X ^ n)
            = (1 - X) * (Finset.range n).sum (fun k => X ^ k) + (1 - X) * X ^ n := mul_add _ _ _
          _ = (1 - X ^ n) + (X ^ n - X * X ^ n) := by rw [ihL, sub_mul, one_mul]
          _ = (1 - X ^ n) + (X ^ n - X ^ (n + 1)) := by rw [← pow_succ']
          _ = 1 - X ^ (n + 1) := sub_add_sub_cancel 1 (X ^ n) (X ^ (n + 1))
      · calc ((Finset.range n).sum (fun k => X ^ k) + X ^ n) * (1 - X)
            = (Finset.range n).sum (fun k => X ^ k) * (1 - X) + X ^ n * (1 - X) := add_mul _ _ _
          _ = (1 - X ^ n) + (X ^ n - X ^ n * X) := by rw [ihR, mul_sub, mul_one]
          _ = (1 - X ^ n) + (X ^ n - X ^ (n + 1)) := by rw [← pow_succ]
          _ = 1 - X ^ (n + 1) := sub_add_sub_cancel 1 (X ^ n) (X ^ (n + 1))

/-- **Right-Inverse Theorem (`mul_neumannInv_eq_one`):** `(1 + L) * neumannInv L = 1` over ANY
`CommRing R` whenever `IsStrictLowerTri L`. -/
theorem mul_neumannInv_eq_one {R : Type*} [CommRing R] {C : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L) :
    (1 + L) * neumannInv L = 1 := by
  have htel := (one_sub_mul_geom_sum (-L) C).1
  have h1 : (1 : Matrix (Fin C) (Fin C) R) - (-L) = 1 + L := sub_neg_eq_add _ _
  have hpow : (-L) ^ C = 0 := strictLowerTri_pow_card_eq_zero hL.neg
  unfold neumannInv
  rw [h1, hpow, sub_zero] at htel
  exact htel

/-- **Left-Inverse Theorem (`neumannInv_mul_eq_one`):** `neumannInv L * (1 + L) = 1` over ANY
`CommRing R` whenever `IsStrictLowerTri L`. -/
theorem neumannInv_mul_eq_one {R : Type*} [CommRing R] {C : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L) :
    neumannInv L * (1 + L) = 1 := by
  have htel := (one_sub_mul_geom_sum (-L) C).2
  have h1 : (1 : Matrix (Fin C) (Fin C) R) - (-L) = 1 + L := sub_neg_eq_add _ _
  have hpow : (-L) ^ C = 0 := strictLowerTri_pow_card_eq_zero hL.neg
  unfold neumannInv
  rw [h1, hpow, sub_zero] at htel
  exact htel

/-- **Main ZK / vFHE WY Chunk Reduction (`wyChunk_bilinear_iff_recurrence`):**
For any strictly lower triangular `C × C` matrix `L` and `C × d` matrices `U, V` over ANY
`CommRing R`, the flat bilinear relation `(1 + L) * U = V` (`U + L * U = V`) is **equivalent**
BOTH to the unique closed-form inverse solution `U = neumannInv L * V` AND to the sequential
causal forward-substitution recurrence
`∀ i col, U i col = V i col - ∑_{j < i} L i j * U j col`.

Consequently, a ZK prover commits `U` as untrusted advice and proves `U + L * U = V` in **one
flat degree-2 `EinSumcheck`** (zero sequential `C`-step GKR circuit, zero matrix inversions). -/
theorem wyChunk_bilinear_iff_recurrence {R : Type*} [CommRing R] {C d : ℕ}
    {L : Matrix (Fin C) (Fin C) R} (hL : IsStrictLowerTri L)
    (U V : Matrix (Fin C) (Fin d) R) :
    ((1 + L) * U = V ↔ U = neumannInv L * V) ∧
    (U = neumannInv L * V ↔
      ∀ i : Fin C, ∀ col : Fin d,
        U i col = V i col - ∑ j ∈ Finset.univ.filter (· < i), L i j * U j col) := by
  have h_neumann : (1 + L) * U = V ↔ U = neumannInv L * V := by
    constructor
    · intro h
      calc U = 1 * U := (Matrix.one_mul U).symm
        _ = (neumannInv L * (1 + L)) * U := by rw [neumannInv_mul_eq_one hL]
        _ = neumannInv L * ((1 + L) * U) := Matrix.mul_assoc _ _ _
        _ = neumannInv L * V := by rw [h]
    · intro h
      rw [h, ← Matrix.mul_assoc, mul_neumannInv_eq_one hL, Matrix.one_mul]
  have h_rec : (1 + L) * U = V ↔
      ∀ i : Fin C, ∀ col : Fin d,
        U i col = V i col - ∑ j ∈ Finset.univ.filter (· < i), L i j * U j col := by
    constructor
    · intro h i col
      have hi := congrArg (fun M => M i col) h
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply] at hi
      have hsplit :
          (∑ j : Fin C, L i j * U j col) =
            ∑ j ∈ Finset.univ.filter (· < i), L i j * U j col := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hij : i ≤ j := le_of_not_gt (by simpa using hj)
        rw [hL i j hij, zero_mul]
      rw [hsplit] at hi
      exact eq_sub_of_add_eq hi
    · intro h
      ext i col
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
      have hsplit :
          (∑ j : Fin C, L i j * U j col) =
            ∑ j ∈ Finset.univ.filter (· < i), L i j * U j col := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hij : i ≤ j := le_of_not_gt (by simpa using hj)
        rw [hL i j hij, zero_mul]
      rw [hsplit]
      exact add_eq_of_eq_sub (h i col)
  exact ⟨h_neumann, h_neumann.symm.trans h_rec⟩

/-! ### Satisfying Witnesses (`C = 3` over `ℤ` and Non-Field `ZMod 16`) & Falsifier Tooth -/

/-- Concrete `3 × 3` strictly lower triangular coupling matrix with nonzero subdiagonal product
(`L ^ 2 ≠ 0`, `L ^ 3 = 0`, showing nilpotency index `C = 3` is tight). -/
def wyWitnessLInt : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![0, 0, 0], ![2, 0, 0], ![-3, 4, 0]]

/-- **Satisfying Witness over `ℤ` (`wyChunk_witness_C3_int`):**
Exhibits `IsStrictLowerTri wyWitnessLInt`, tight nilpotency (`L^2 ≠ 0 ∧ L^3 = 0`), and exact
agreement between `(1 + L) * U = V`, `U = neumannInv L * V`, and causal forward substitution. -/
theorem wyChunk_witness_C3_int :
    let L := wyWitnessLInt
    let V : Matrix (Fin 3) (Fin 2) ℤ := Matrix.of ![![1, 2], ![5, -1], ![3, 4]]
    let U : Matrix (Fin 3) (Fin 2) ℤ := Matrix.of ![![1, 2], ![3, -5], ![-6, 30]]
    IsStrictLowerTri L ∧
    L ^ 2 ≠ 0 ∧
    L ^ 3 = 0 ∧
    (1 + L) * U = V ∧
    U = neumannInv L * V := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [wyWitnessLInt] at hij ⊢

/-- **Satisfying Witness over Non-Field Ring `ZMod 16` (`wyChunk_witness_C3_zmod16`):**
`ZMod 16` has zero divisors (`(4 : ZMod 16) * 4 = 0`, not a field — modeling SPDZ2k / BFV power-of-2
plaintext rings), yet `IsStrictLowerTri` still guarantees two-sided `neumannInv` and unique `U`. -/
theorem wyChunk_witness_C3_zmod16 :
    let L : Matrix (Fin 3) (Fin 3) (ZMod 16) := Matrix.of ![![0, 0, 0], ![2, 0, 0], ![13, 4, 0]]
    let V : Matrix (Fin 3) (Fin 2) (ZMod 16) := Matrix.of ![![1, 2], ![5, 15], ![3, 4]]
    let U : Matrix (Fin 3) (Fin 2) (ZMod 16) := Matrix.of ![![1, 2], ![3, 11], ![10, 14]]
    ((4 : ZMod 16) ≠ 0 ∧ (4 : ZMod 16) * 4 = 0) ∧
    IsStrictLowerTri L ∧
    (1 + L) * neumannInv L = 1 ∧
    (1 + L) * U = V ∧
    U = neumannInv L * V := by
  refine ⟨by decide, ?_, by decide, by decide, by decide⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

/-- **Falsifier Tooth (`wyChunk_nonStrictLower_falsifier`):**
Drop `IsStrictLowerTri L` by setting `L = -1` (violating `L i i = 0` on the diagonal): then
`1 + L = 0`, and two **distinct** solution matrices `U₁ = 0 ≠ 1 = U₂` BOTH satisfy the bilinear
check `(1 + L) * U₁ = V` and `(1 + L) * U₂ = V` (`V = 0`), refuting soundness of the bilinear
check without strict lower triangularity! -/
theorem wyChunk_nonStrictLower_falsifier :
    let L : Matrix (Fin 3) (Fin 3) ℤ := -1
    let U₁ : Matrix (Fin 3) (Fin 3) ℤ := 0
    let U₂ : Matrix (Fin 3) (Fin 3) ℤ := 1
    ¬ IsStrictLowerTri L ∧
    U₁ ≠ U₂ ∧
    (1 + L) * U₁ = 0 ∧
    (1 + L) * U₂ = 0 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro hL
  have h00 : (-1 : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 0 := hL 0 0 (le_refl 0)
  revert h00
  decide

end ChunkwiseWY

/-! ## Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Theory.ZkmlDeltaNet.gdnStep_eq_householder_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnStep_eq_householder_update
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.gdnStep_targeted_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnStep_targeted_erase
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.gdnStep_preserves_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnStep_preserves_orthogonal
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.gdnStep_erase_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnStep_erase_witness
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.gdnStep_unnormalized_erase_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnStep_unnormalized_erase_fails
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.strictLowerTri_pow_zero_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strictLowerTri_pow_zero_above
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.strictLowerTri_pow_card_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strictLowerTri_pow_card_eq_zero
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.mul_neumannInv_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mul_neumannInv_eq_one
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.neumannInv_mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms neumannInv_mul_eq_one
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.wyChunk_bilinear_iff_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyChunk_bilinear_iff_recurrence
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.wyChunk_witness_C3_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyChunk_witness_C3_int
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.wyChunk_witness_C3_zmod16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyChunk_witness_C3_zmod16
/-- info: 'Minidregg.Theory.ZkmlDeltaNet.wyChunk_nonStrictLower_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyChunk_nonStrictLower_falsifier

end Minidregg.Theory.ZkmlDeltaNet
