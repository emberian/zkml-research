/- Exact packed-leaf indexing for the five actual IR2 FRI rounds. -/
import Selvage.Ir2FriNativeEvent

namespace Minidregg.Selvage.Ir2Fri
open Ir2FriSchedule
open Minidregg.Theory.BitReverseFriTransport
noncomputable section

/-- Statement-first contract: every natural source position has one packed row and column. -/
def PackedIndexContract : Prop := ∀ j : Fin 5,
  ∃ e : Index j ≃ (Index (j+1) × Fin (radix j)),
    ∀ row col, e.symm (row,col) = nativeRowSourceIndex j row col

/-- Reversing a packed row/column concatenation gives the existing natural exponent formula. -/
theorem reverseIndex_packed (h a : ℕ) (row : Fin (2^h)) (col : Fin (2^a)) :
    reverseIndex (h+a) (col.val + 2^a*row.val) =
      reverseIndex h row.val + 2^h*reverseIndex a col.val := by
  have hv : (BitVec.ofNat h row.val ++ BitVec.ofNat a col.val).toNat =
      col.val + 2^a*row.val := by
    rw [BitVec.toNat_append,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt row.isLt,Nat.mod_eq_of_lt col.isLt,
      ←Nat.shiftLeft_add_eq_or_of_lt col.isLt,Nat.shiftLeft_eq]
    ac_rfl
  have he : BitVec.ofNat (h+a) (col.val + 2^a*row.val) =
      BitVec.ofNat h row.val ++ BitVec.ofNat a col.val := by
    apply BitVec.eq_of_toNat_eq
    rw [←hv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (BitVec.ofNat h row.val ++ BitVec.ofNat a col.val).isLt]
  unfold reverseIndex
  rw [he,BitVec.reverse_append,BitVec.toNat_cast,BitVec.toNat_append,
    ←Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat h row.val).reverse.isLt,
    Nat.shiftLeft_eq]
  ac_rfl

/-- Reverse the current natural exponent, then divide into its native packed row and column. -/
def packedIndexEquiv (j : Fin 5) : Index j ≃ (Index (j+1) × Fin (radix j)) :=
  ((reverseFin (17-stage j)).trans
    (finCongr ((size_factor j).trans (Nat.mul_comm _ _)))).trans finProdFinEquiv.symm

/-- The forward row number is the actual quotient after reversing the current height. -/
theorem packedIndexEquiv_row (j : Fin 5) (i : Index j) :
    (packedIndexEquiv j i).1.val = reverseIndex (17-stage j) i.val / radix j := by
  change (reverseFin (17-stage j) i).val / radix j = _
  rw [reverseFin_value]

/-- The forward column number is the actual remainder after reversing the current height. -/
theorem packedIndexEquiv_col (j : Fin 5) (i : Index j) :
    (packedIndexEquiv j i).2.val = reverseIndex (17-stage j) i.val % radix j := by
  change (reverseFin (17-stage j) i).val % radix j = _
  rw [reverseFin_value]

/-- The inverse is the existing actual row-source index, with no extracted-word premise. -/
theorem packedIndexEquiv_symm (j : Fin 5) (row : Index (j+1)) (col : Fin (radix j)) :
    (packedIndexEquiv j).symm (row,col) = nativeRowSourceIndex j row col := by
  apply Fin.ext
  change (reverseFin (17-stage j) _).val = _
  rw [reverseFin_value]
  change reverseIndex (17-stage j) (col.val+radix j*row.val) =
    reverseIndex (nativeRowHeight j) row.val +
      2^(nativeRowHeight j)*reverseIndex (nativeLogArity j) col.val
  rw [←native_height_add j]
  exact reverseIndex_packed (nativeRowHeight j) (nativeLogArity j) row col

/-- Packing an actual native row source returns that exact row and column. -/
theorem packedIndexEquiv_nativeRowSourceIndex (j : Fin 5) (row : Index (j+1))
    (col : Fin (radix j)) :
    packedIndexEquiv j (nativeRowSourceIndex j row col) = (row,col) := by
  rw [←packedIndexEquiv_symm,Equiv.apply_symm_apply]

/-- Every actual round inhabits the packed-index contract. -/
theorem packed_index_contract : PackedIndexContract :=
  fun j => ⟨packedIndexEquiv j,packedIndexEquiv_symm j⟩

/-- The native verifier keeps the next low radix bits as the selected column. -/
def rawColumn (j : Fin 5) (raw : Fin (2^17)) : Fin (radix j) :=
  ⟨(raw.val / 2^(stage j)) % radix j,Nat.mod_lt _ (radix_positive j)⟩

/-- Reversing a coherent runtime exponent recovers its remaining raw query bits. -/
theorem reverse_runtimeIndex (j : Fin 5) (raw : Fin (2^17)) :
    reverseIndex (17-stage j) (runtimeIndex j raw).val = raw.val / 2^(stage j) := by
  have hb : raw.val / 2^(stage j) < 2^(17-stage j) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(stage j))).mpr
    rw [Nat.mul_comm,←source_size_factor]
    exact raw.isLt
  change reverseIndex (17-stage j) (reverseIndex (17-stage j) _) = _
  simp [reverseIndex,BitVec.reverse_reverse_eq,Nat.mod_eq_of_lt hb]

/-- The actual query decomposes into precisely the raw parent row and selected column. -/
theorem packedIndexEquiv_runtimeIndex (j : Fin 5) (raw : Fin (2^17)) :
    packedIndexEquiv j (runtimeIndex j raw) = (rawParentRow j raw,rawColumn j raw) := by
  apply Prod.ext
  · apply Fin.ext
    rw [packedIndexEquiv_row,reverse_runtimeIndex]
    change raw.val / 2^(stage j) / radix j = raw.val / 2^(stage (j+1))
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm,←stage_factor]
  · apply Fin.ext
    rw [packedIndexEquiv_col,reverse_runtimeIndex]
    rfl

/-- The selected packed source is the coherent runtime exponent at every actual round. -/
theorem nativeRowSourceIndex_raw (j : Fin 5) (raw : Fin (2^17)) :
    nativeRowSourceIndex j (rawParentRow j raw) (rawColumn j raw) = runtimeIndex j raw := by
  apply (packedIndexEquiv j).injective
  rw [packedIndexEquiv_nativeRowSourceIndex,packedIndexEquiv_runtimeIndex]

/-- At the initial packed root the selector reverses all seventeen source bits. -/
theorem nativeRowSourceIndex_raw_zero (raw : Fin (2^17)) :
    nativeRowSourceIndex 0 (rawParentRow 0 raw) (rawColumn 0 raw) = sourceIndex raw := by
  rw [nativeRowSourceIndex_raw]
  exact runtimeIndex_zero raw

/-- Nonzero final-round row and column select natural exponent twenty. -/
theorem packed_index_witness :
    (nativeRowSourceIndex 4 1 ⟨1,by decide⟩).val = 20 ∧
      packedIndexEquiv 4 (nativeRowSourceIndex 4 1 ⟨1,by decide⟩) = (1,⟨1,by decide⟩) := by
  exact ⟨by decide,packedIndexEquiv_nativeRowSourceIndex 4 1 ⟨1,by decide⟩⟩

/-- Teeth: using raw concatenation as the natural exponent loses the required bit reversal. -/
theorem packed_index_unreversed_falsifier : (nativeRowSourceIndex 4 1 ⟨1,by decide⟩).val ≠ 5 := by
  decide

/-- The contract and a nonzero source selector are simultaneously inhabited. -/
theorem packed_index_premises_inhabited : PackedIndexContract ∧
    ∃ raw : Fin (2^17), raw.val ≠ 0 ∧
      nativeRowSourceIndex 0 (rawParentRow 0 raw) (rawColumn 0 raw) = sourceIndex raw :=
  ⟨packed_index_contract,1,by decide,nativeRowSourceIndex_raw_zero 1⟩

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.reverseIndex_packed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.reverseIndex_packed

/-- info: 'Minidregg.Selvage.Ir2Fri.packedIndexEquiv_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packedIndexEquiv_row

/-- info: 'Minidregg.Selvage.Ir2Fri.packedIndexEquiv_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packedIndexEquiv_col

/-- info: 'Minidregg.Selvage.Ir2Fri.packedIndexEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packedIndexEquiv_symm

/-- info: 'Minidregg.Selvage.Ir2Fri.packedIndexEquiv_nativeRowSourceIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packedIndexEquiv_nativeRowSourceIndex

/-- info: 'Minidregg.Selvage.Ir2Fri.packed_index_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packed_index_contract

/-- info: 'Minidregg.Selvage.Ir2Fri.reverse_runtimeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.reverse_runtimeIndex

/-- info: 'Minidregg.Selvage.Ir2Fri.packedIndexEquiv_runtimeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packedIndexEquiv_runtimeIndex

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_raw

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_raw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeRowSourceIndex_raw_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.packed_index_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packed_index_witness

/-- info: 'Minidregg.Selvage.Ir2Fri.packed_index_unreversed_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packed_index_unreversed_falsifier

/-- info: 'Minidregg.Selvage.Ir2Fri.packed_index_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.packed_index_premises_inhabited
