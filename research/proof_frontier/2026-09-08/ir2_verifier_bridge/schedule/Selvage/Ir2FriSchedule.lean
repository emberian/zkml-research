/- The concrete IR2 replay schedule: logheight 17, four arity-eight rounds,
then arity four, ending at logheight three. -/
import Selvage.BabyBearModuloSampling
import Theory.BitReverseFriTransport

namespace Minidregg.Selvage.Ir2FriSchedule
open scoped BigOperators Classical
open Minidregg.Theory.BitReverseFriTransport

/-- Total source exponent bits removed after each committed round. -/
def stage (n : ℕ) : ℕ := min (3*n) 14

/-- Existing natural exponent indices for the replay's exact domain sizes. -/
abbrev Index (n : ℕ) : Type := Fin (2^(17-stage n))

/-- Actual number of source entries combined by each of the five rounds. -/
def radix (n : Fin 5) : ℕ := 2^(stage (n+1)-stage n)

/-- The actual coherent projection reduces the natural exponent modulo the next size. -/
def project (n : Fin 5) (i : Index n) : Index (n+1) :=
  ⟨i.val % 2^(17-stage (n+1)),Nat.mod_lt _ (by positivity)⟩

/-- Project a full seventeen-bit natural source exponent to any stage. -/
def naturalIndex (n : ℕ) (i : Index 0) : Index n :=
  ⟨i.val % 2^(17-stage n),Nat.mod_lt _ (by positivity)⟩

/-- The runtime source order is the reverse of all seventeen raw index bits. -/
def sourceIndex (raw : Fin (2^17)) : Index 0 :=
  ⟨reverseIndex 17 raw.val,reverseIndex_lt 17 raw.val⟩

/-- Runtime dropping of low query bits followed by reversing the remaining bits. -/
def runtimeIndex (n : ℕ) (raw : Fin (2^17)) : Index n :=
  ⟨reverseIndex (17-stage n) (raw.val / 2^(stage n)),reverseIndex_lt _ _⟩

/-- Exact replay dimensions and final domain cardinality. -/
theorem dimensions : [stage 0,stage 1,stage 2,stage 3,stage 4,stage 5] =
    [0,3,6,9,12,14] ∧ Fintype.card (Index 5) = 8 := by decide

theorem stage_le (n : ℕ) : stage n ≤ 14 := Nat.min_le_right _ _

theorem stage_monotone {n m : ℕ} (h : n ≤ m) : stage n ≤ stage m := by
  unfold stage
  omega

theorem radix_positive (n : Fin 5) : 0 < radix n := by unfold radix; positivity

/-- The final round has four entries; the other four have eight. -/
theorem radix_exact (n : Fin 5) : radix n = if n.val < 4 then 8 else 4 := by
  fin_cases n <;> decide

/-- Exact source/target factorization, derived from the actual stage exponents. -/
theorem size_factor (n : Fin 5) :
    2^(17-stage n) = radix n * 2^(17-stage (n+1)) := by
  unfold radix
  rw [←pow_add]
  congr 1
  have h := stage_monotone (show n.val ≤ n.val+1 by omega)
  have h' := stage_le (n+1)
  omega

/-- The initial source is factored by exactly the bits removed at stage n. -/
theorem source_size_factor (n : ℕ) : 2^17 = 2^(stage n)*2^(17-stage n) := by
  rw [←pow_add]
  congr 1
  have h := stage_le n
  omega

theorem naturalIndex_zero (i : Index 0) : naturalIndex 0 i = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

/-- Successive actual projections have the same endpoint as the full source projection. -/
theorem project_naturalIndex (n : Fin 5) (i : Index 0) :
    project n (naturalIndex n i) = naturalIndex (n+1) i := by
  apply Fin.ext
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by
    have h := stage_monotone (show n.val ≤ n.val+1 by omega)
    omega))

/-- Coherent runtime rows are exactly the projected natural exponents of the full source. -/
theorem runtimeIndex_eq_naturalIndex (n : ℕ) (raw : Fin (2^17)) :
    runtimeIndex n raw = naturalIndex n (sourceIndex raw) := by
  apply Fin.ext
  exact query_transport 17 (stage n) raw.val (by have h := stage_le n; omega) raw.isLt

/-- No initial pair-index convention is used: stage zero reverses all seventeen bits. -/
theorem runtimeIndex_zero (raw : Fin (2^17)) : runtimeIndex 0 raw = sourceIndex raw := by
  rw [runtimeIndex_eq_naturalIndex,naturalIndex_zero]

/-- Full-source bit reversal is an involution, hence a uniform-source equivalence. -/
def sourceEquiv : Fin (2^17) ≃ Index 0 where
  toFun := sourceIndex
  invFun i := ⟨reverseIndex 17 i.val,reverseIndex_lt _ _⟩
  left_inv raw := by
    apply Fin.ext
    change reverseIndex 17 (reverseIndex 17 raw.val) = raw.val
    simp [reverseIndex,BitVec.reverse_reverse_eq]
  right_inv i := by
    apply Fin.ext
    change reverseIndex 17 (reverseIndex 17 i.val) = i.val
    simp [reverseIndex,BitVec.reverse_reverse_eq]

/-- Quotient and remainder split an actual round index into its radix fibre and next row. -/
def projectSplitEquiv (n : Fin 5) : Index n ≃ Fin (radix n) × Index (n+1) :=
  (finCongr (size_factor n)).trans finProdFinEquiv.symm

theorem projectSplitEquiv_snd (n : Fin 5) (i : Index n) :
    (projectSplitEquiv n i).2 = project n i := by
  apply Fin.ext
  simp [projectSplitEquiv,finProdFinEquiv,project]

/-- The exact fibre over every actual next-row index has the round's proved radix. -/
def projectFiberEquiv (n : Fin 5) (k : Index (n+1)) :
    {i : Index n // project n i = k} ≃ Fin (radix n) where
  toFun i := (projectSplitEquiv n i.val).1
  invFun a := ⟨(projectSplitEquiv n).symm (a,k),by
    rw [←projectSplitEquiv_snd,Equiv.apply_symm_apply]⟩
  left_inv i := by
    apply Subtype.ext
    apply (projectSplitEquiv n).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl (by simpa only [projectSplitEquiv_snd] using i.property.symm)
  right_inv a := by simp

/-- Balanced fibre cardinality is derived from the concrete modulus, not assumed. -/
theorem project_fiber_card (n : Fin 5) (k : Index (n+1)) :
    (Finset.univ.filter fun i => project n i = k).card = radix n := by
  have h := Fintype.card_congr (projectFiberEquiv n k)
  simpa only [Fintype.card_subtype,Fintype.card_fin] using h

/-- Radix multiplication removes exactly the new stage bits. -/
theorem stage_factor (n : Fin 5) : 2^(stage (n+1)) = radix n * 2^(stage n) := by
  unfold radix
  rw [←pow_add]
  congr 1
  have h := stage_monotone (show n.val ≤ n.val+1 by omega)
  omega

/-- The observed final round cannot be replaced by a fifth arity-eight step. -/
theorem final_round_arity_falsifier : radix ⟨4,by decide⟩ = 4 ∧ radix ⟨4,by decide⟩ ≠ 8 := by
  decide

/-- Full-source reversal keeps the low raw bit as the high natural exponent bit. -/
theorem full_source_bit_witness :
    (sourceIndex (⟨1,by decide⟩ : Fin (2^17))).val = 2^16 := by
  decide

end Minidregg.Selvage.Ir2FriSchedule

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.dimensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.dimensions

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.stage_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.stage_le

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.stage_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.stage_monotone

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.radix_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.radix_positive

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.radix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.radix_exact

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.size_factor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.size_factor

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.source_size_factor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.source_size_factor

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.naturalIndex_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.naturalIndex_zero

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.project_naturalIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.project_naturalIndex

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.runtimeIndex_eq_naturalIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.runtimeIndex_eq_naturalIndex

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.runtimeIndex_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.runtimeIndex_zero

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.projectSplitEquiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.projectSplitEquiv_snd

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.project_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.project_fiber_card

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.stage_factor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.stage_factor

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.final_round_arity_falsifier' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.final_round_arity_falsifier

/-- info: 'Minidregg.Selvage.Ir2FriSchedule.full_source_bit_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2FriSchedule.full_source_bit_witness

