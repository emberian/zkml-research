/- Fixed-shape packed MMCS leaf projections. Extension coefficients use the
existing BabyBear X^4-11 power-basis equivalence. P3 extension_mmcs flattens each
extension value first; hiding_mmcs appends four base-field salts to each matrix
row; same-height Merkle hashing concatenates those salted rows in matrix order.
The canonical adapter's exact shape gate is a separate premise: native hiding
MMCS itself does not check supplied salt length. No hash/ROM claim is made here. -/
import Selvage.BabyBearExt4
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic
namespace Minidregg.Selvage.PackedLeafEncoding
open Minidregg.Selvage.BabyBearExt4
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- Offset in a concatenation, derived only from preceding block lengths. -/
def prefixLength {α : Type*} (blocks : List (List α)) (i : Nat) : Nat :=
  ((blocks.take i).map List.length).sum

def ext4Encode (x : Ext4) : List BabyBear := List.ofFn (coefficients x)
def ext4Decode (xs : List BabyBear) : Ext4 :=
  coefficients.symm (fun i => xs.getD i.val 0)

def friLeafEncode {n : Nat} (values : Fin n → Ext4) (salts : Fin 4 → BabyBear) : List BabyBear :=
  (List.ofFn (fun i => ext4Encode (values i))).flatten ++ List.ofFn salts
def friProject {n : Nat} (i : Fin n) (leaf : List BabyBear) : Ext4 :=
  ext4Decode ((leaf.drop (4*i.val)).take 4)

def FriRoundTrip : Prop := ∀ (n : Nat) (values : Fin n → Ext4) (salts : Fin 4 → BabyBear) (i : Fin n),
  friProject i (friLeafEncode values salts)=values i

def rowOffset {m : Nat} (width : Fin m → Nat) (i : Fin m) : Nat :=
  ((List.ofFn (fun j => width j+4)).take i.val).sum
def rowsEncode {m : Nat} (width : Fin m → Nat) (rows : (i : Fin m) → Fin (width i) → BabyBear)
    (salts : Fin m → Fin 4 → BabyBear) : List BabyBear :=
  (List.ofFn (fun i => List.ofFn (rows i) ++ List.ofFn (salts i))).flatten

def rowSlice {m : Nat} (width : Fin m → Nat) (i : Fin m) (leaf : List BabyBear) : List BabyBear :=
  (leaf.drop (rowOffset width i)).take (width i)
def rowProject {m : Nat} (width : Fin m → Nat) (i : Fin m) (leaf : List BabyBear) : Fin (width i) → BabyBear :=
  fun j => (rowSlice width i leaf).getD j.val 0

def RowsRoundTrip : Prop := ∀ (m : Nat) (width : Fin m → Nat)
    (rows : (i : Fin m) → Fin (width i) → BabyBear) (salts : Fin m → Fin 4 → BabyBear) (i : Fin m),
  rowProject width i (rowsEncode width rows salts)=rows i

/-- Arbitrary-size blocks and suffix. Neither their widths nor values are
expanded by this induction; salts may therefore be treated as any suffix. -/
theorem slice_block_append {α : Type*} (blocks : List (List α)) (tail : List α)
    (i : Nat) (hi : i<blocks.length) :
    ((blocks.flatten++tail).drop (prefixLength blocks i)).take (blocks[i].length)=blocks[i] := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons head rest ih =>
    cases i with
    | zero => simp [prefixLength,List.append_assoc]
    | succ i =>
      have hi' : i<rest.length := by simpa using hi
      have ht := ih i hi'
      simpa only [prefixLength,List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons,
        List.getElem_cons_succ,List.append_assoc,←List.drop_drop,List.drop_left] using ht

theorem getD_ofFn {α : Type*} (default : α) {n : Nat} (f : Fin n → α) (i : Fin n) :
    (List.ofFn f).getD i.val default=f i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

theorem ext4Encode_length (x : Ext4) : (ext4Encode x).length=4 := by
  simp [ext4Encode,extensionPolynomial_natDegree]

theorem friLeafEncode_length {n : Nat} (values : Fin n → Ext4) (salts : Fin 4 → BabyBear) :
    (friLeafEncode values salts).length=4*n+4 := by
  simp [friLeafEncode,List.length_flatten,List.map_ofFn,Function.comp_def,ext4Encode_length,Nat.mul_comm]

theorem rowsEncode_length {m : Nat} (width : Fin m → Nat)
    (rows : (i : Fin m) → Fin (width i) → BabyBear) (salts : Fin m → Fin 4 → BabyBear) :
    (rowsEncode width rows salts).length=(List.ofFn (fun i => width i+4)).sum := by
  simp [rowsEncode,List.length_flatten,List.map_ofFn,Function.comp_def]

theorem ext4Decode_encode (x : Ext4) : ext4Decode (ext4Encode x)=x := by
  unfold ext4Decode ext4Encode
  simp only [getD_ofFn]
  exact coefficients.symm_apply_apply x

theorem ext4Encode_injective : Function.Injective ext4Encode := by
  intro x y h
  have hh := congrArg ext4Decode h
  simpa only [ext4Decode_encode] using hh

theorem prefixLength_ofFn {α : Type*} {n : Nat} (blocks : Fin n → List α)
    (width : Fin n → Nat) (hlen : ∀ i,(blocks i).length=width i) (i : Fin n) :
    prefixLength (List.ofFn blocks) i.val=((List.ofFn width).take i.val).sum := by
  simp only [prefixLength,List.map_take,List.map_ofFn]
  have hw : List.length ∘ blocks=width := funext hlen
  rw [hw]

theorem prefixLength_const {α : Type*} {n : Nat} (blocks : Fin n → List α)
    (width : Nat) (hlen : ∀ i,(blocks i).length=width) (i : Fin n) :
    prefixLength (List.ofFn blocks) i.val=width*i.val := by
  rw [prefixLength_ofFn blocks (fun _ => width) hlen i,List.ofFn_const,List.take_replicate]
  simp [Nat.mul_comm]

theorem friRoundTrip : FriRoundTrip := by
  intro n values salts i
  have h := slice_block_append (List.ofFn (fun j => ext4Encode (values j))) (List.ofFn salts) i.val (by simp)
  rw [prefixLength_const _ 4 (fun j => ext4Encode_length (values j)) i] at h
  simp only [List.getElem_ofFn,ext4Encode_length] at h
  unfold friProject friLeafEncode
  rw [h,ext4Decode_encode]

theorem fri_values_injective {n : Nat} (values other : Fin n → Ext4) (salts otherSalts : Fin 4 → BabyBear)
    (h : friLeafEncode values salts=friLeafEncode other otherSalts) : values=other := by
  funext i
  have hh := congrArg (friProject i) h
  simpa only [friRoundTrip n] using hh

theorem friLeaf_injective {n : Nat} (values other : Fin n → Ext4) (salts otherSalts : Fin 4 → BabyBear)
    (h : friLeafEncode values salts=friLeafEncode other otherSalts) : values=other ∧ salts=otherSalts := by
  have hv := fri_values_injective values other salts otherSalts h
  refine ⟨hv,?_⟩
  subst other
  apply List.ofFn_injective
  exact List.append_cancel_left h

/-- Recover a whole salted row, including its four salt coordinates. -/
theorem rowBlock_encode {m : Nat} (width : Fin m → Nat)
    (rows : (i : Fin m) → Fin (width i) → BabyBear) (salts : Fin m → Fin 4 → BabyBear) (i : Fin m) :
    ((rowsEncode width rows salts).drop (rowOffset width i)).take (width i+4)=
      List.ofFn (rows i) ++ List.ofFn (salts i) := by
  have h := slice_block_append
    (List.ofFn (fun j => List.ofFn (rows j) ++ List.ofFn (salts j))) [] i.val (by simp)
  rw [prefixLength_ofFn _ (fun j => width j+4) (by intro j; simp) i] at h
  simpa only [List.append_nil,List.getElem_ofFn,List.length_append,List.length_ofFn,
    rowsEncode,rowOffset] using h

theorem rowSlice_encode {m : Nat} (width : Fin m → Nat)
    (rows : (i : Fin m) → Fin (width i) → BabyBear) (salts : Fin m → Fin 4 → BabyBear) (i : Fin m) :
    rowSlice width i (rowsEncode width rows salts)=List.ofFn (rows i) := by
  have h := congrArg (List.take (width i)) (rowBlock_encode width rows salts i)
  simpa [rowSlice,List.take_take,List.take_append_of_le_length] using h

theorem rowsRoundTrip : RowsRoundTrip := by
  intro m width rows salts i
  funext j
  unfold rowProject
  rw [rowSlice_encode,getD_ofFn]

theorem rows_values_injective {m : Nat} (width : Fin m → Nat)
    (rows other : (i : Fin m) → Fin (width i) → BabyBear)
    (salts otherSalts : Fin m → Fin 4 → BabyBear)
    (h : rowsEncode width rows salts=rowsEncode width other otherSalts) : rows=other := by
  funext i
  have hh := congrArg (rowProject width i) h
  simpa only [rowsRoundTrip m] using hh

theorem rowsEncode_injective {m : Nat} (width : Fin m → Nat)
    (rows other : (i : Fin m) → Fin (width i) → BabyBear)
    (salts otherSalts : Fin m → Fin 4 → BabyBear)
    (h : rowsEncode width rows salts=rowsEncode width other otherSalts) :
    rows=other ∧ salts=otherSalts := by
  have hv := rows_values_injective width rows other salts otherSalts h
  refine ⟨hv,?_⟩
  subst other
  funext i
  apply List.ofFn_injective
  have hh := congrArg (fun xs : List BabyBear =>
    (xs.drop (rowOffset width i)).take (width i+4)) h
  dsimp only at hh
  rw [rowBlock_encode,rowBlock_encode] at hh
  exact List.append_cancel_left hh

/-- Canonical input-batch widths, grouped in the verifier's same-height matrix order.
The generic theorem above consumes these as dimensions without expanding their rows. -/
def actualInputWidths : List (List Nat) :=
  [[8,8],[2513,5],List.replicate 16 8,[59],[8,8]]
def widthsOfList (ws : List Nat) : Fin ws.length → Nat := fun i => ws[i]

/-- Fixed-shape acceptance has a nonzero value and arbitrary salts. -/
def NonzeroFriWitness : Prop :=
  ∀ salts : Fin 4 → BabyBear,
    friProject (0 : Fin 1) (friLeafEncode (fun _ : Fin 1 => (1 : Ext4)) salts)=1

theorem nonzeroFriWitness : NonzeroFriWitness := by
  intro salts
  exact friRoundTrip 1 (fun _ => 1) salts 0

/-- Changing any extension coordinate cannot be hidden by changing salts. -/
theorem fri_changed_coordinate_refused {n : Nat} (values other : Fin n → Ext4)
    (salts otherSalts : Fin 4 → BabyBear) (i : Fin n) (hne : values i ≠ other i) :
    friLeafEncode values salts ≠ friLeafEncode other otherSalts := by
  intro h
  exact hne (congrFun (fri_values_injective values other salts otherSalts h) i)

/-- A missing per-row salt offset reads a salt instead of the next matrix row. -/
def MissingSaltOffsetFalsifier : Prop :=
  (rowsEncode (fun _ : Fin 2 => 1) (fun _ _ => 1) (fun _ _ => 0)).getD 1 0 ≠ (1 : BabyBear)

theorem missingSaltOffsetFalsifier : MissingSaltOffsetFalsifier := by
  norm_num [MissingSaltOffsetFalsifier,rowsEncode,List.ofFn_succ]

/-- The matrix premise is inhabited even with different widths; no content or
salt constraint is required by the lossless fixed-shape encoding. -/
theorem rows_premise_inhabited (ws : List Nat)
    (rows : (i : Fin ws.length) → Fin (widthsOfList ws i) → BabyBear)
    (salts : Fin ws.length → Fin 4 → BabyBear) :
    ∀ i, rowProject (widthsOfList ws) i (rowsEncode (widthsOfList ws) rows salts)=rows i := by
  exact rowsRoundTrip ws.length (widthsOfList ws) rows salts

/- Every exported theorem is pinned to its exact kernel axiom dependencies. -/

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.slice_block_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.slice_block_append

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.getD_ofFn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.getD_ofFn

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.ext4Encode_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.ext4Encode_length

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.friLeafEncode_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.friLeafEncode_length

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rowsEncode_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rowsEncode_length

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.ext4Decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.ext4Decode_encode

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.ext4Encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.ext4Encode_injective

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.prefixLength_ofFn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.prefixLength_ofFn

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.prefixLength_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.prefixLength_const

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.friRoundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.friRoundTrip

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.fri_values_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.fri_values_injective

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.friLeaf_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.friLeaf_injective

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rowBlock_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rowBlock_encode

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rowSlice_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rowSlice_encode

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rowsRoundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rowsRoundTrip

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rows_values_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rows_values_injective

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rowsEncode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rowsEncode_injective

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.nonzeroFriWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.nonzeroFriWitness

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.fri_changed_coordinate_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.fri_changed_coordinate_refused

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.missingSaltOffsetFalsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.missingSaltOffsetFalsifier

/-- info: 'Minidregg.Selvage.PackedLeafEncoding.rows_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Selvage.PackedLeafEncoding.rows_premise_inhabited

end
end Minidregg.Selvage.PackedLeafEncoding
