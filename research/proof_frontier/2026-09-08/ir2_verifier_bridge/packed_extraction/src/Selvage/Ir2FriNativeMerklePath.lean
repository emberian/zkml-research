/- Actual low-bit-first bottom-up MMCS paths transported to BinaryMerkle's top-down interface. -/
import Selvage.BinaryMerkle
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fin.Rev

namespace Minidregg.Selvage.Ir2Fri

/-- The existing binary address decoder exposes the actual raw integer test bit. -/
theorem binaryAddressBits_testBit (k : ℕ) (raw : Fin (2^k)) (i : Fin k) :
    binaryAddressBits k raw i = Nat.testBit raw.val i.val := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change ((⟨raw.val / 2^i.val % 2, _⟩ : Fin 2) == 1) = _
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff]

variable {Value Digest : Type*}

/-- One native MMCS compression step, with false selecting the left child. -/
def nativeNode (H : BinaryMerkle.HashSuite Value Digest) (bit : Bool) (child sibling : Digest) : Digest :=
  if bit then H.node sibling child else H.node child sibling

/-- Literal bottom-up path traversal: low address bit and first supplied sibling are consumed first. -/
def bottomUpRecompute (H : BinaryMerkle.HashSuite Value Digest) : {k : ℕ} →
    Digest → (Fin k → Bool) → List Digest → Option Digest
  | 0, leaf, _, [] => some leaf
  | 0, _, _, _::_ => none
  | _+1, _, _, [] => none
  | k+1, leaf, address, sibling::rest =>
      bottomUpRecompute H (nativeNode H (address 0) leaf sibling)
        (fun i : Fin k => address i.succ) rest

/-- Statement-first exact path-order transport, including malformed sibling counts. -/
def NativeMerklePathContract (H : BinaryMerkle.HashSuite Value Digest) : Prop :=
  ∀ (k : ℕ) (leaf : Digest) (bits : Fin k → Bool) (siblings : List Digest),
    bottomUpRecompute H leaf bits siblings =
      BinaryMerkle.recompute H leaf (fun i => bits i.rev) siblings.reverse

/-- The final top-down sibling is precisely the first compression at the leaf. -/
theorem recompute_append_singleton (H : BinaryMerkle.HashSuite Value Digest) :
    ∀ (k : ℕ) (leaf sibling : Digest) (address : Fin (k+1) → Bool) (path : List Digest),
    BinaryMerkle.recompute H leaf address (path++[sibling]) =
      BinaryMerkle.recompute H (nativeNode H (address (Fin.last k)) leaf sibling)
        (fun i => address i.castSucc) path := by
  intro k
  induction k with
  | zero =>
    intro leaf sibling address path
    cases path with
    | nil => cases hb : address 0 <;> simp [BinaryMerkle.recompute,nativeNode,hb]
    | cons s rest =>
      cases rest <;> simp [BinaryMerkle.recompute]
  | succ k ih =>
    intro leaf sibling address path
    cases path with
    | nil => simp [BinaryMerkle.recompute]
    | cons s rest =>
      simp only [List.cons_append,BinaryMerkle.recompute]
      rw [ih]
      rfl

/-- Actual bottom-up traversal equals top-down recomputation with both orders reversed. -/
theorem bottomUpRecompute_eq_recompute (H : BinaryMerkle.HashSuite Value Digest) :
    NativeMerklePathContract H := by
  intro k
  induction k with
  | zero =>
    intro leaf bits siblings
    cases siblings with
    | nil => rfl
    | cons sibling rest =>
      simp only [List.reverse_cons]
      cases rest.reverse <;> rfl
  | succ k ih =>
    intro leaf bits siblings
    cases siblings with
    | nil => rfl
    | cons sibling rest =>
      simp only [bottomUpRecompute,ih,List.reverse_cons,recompute_append_singleton,
        Fin.rev_last,Fin.rev_castSucc]

/-- The raw-integer spelling used by the native verifier. -/
theorem bottomUpRecompute_raw (H : BinaryMerkle.HashSuite Value Digest) (k : ℕ)
    (leaf : Digest) (raw : Fin (2^k)) (siblings : List Digest) :
    bottomUpRecompute H leaf (fun i : Fin k => Nat.testBit raw.val i.val) siblings =
      BinaryMerkle.recompute H leaf (fun i => binaryAddressBits k raw i.rev) siblings.reverse := by
  have hbits : (fun i : Fin k => Nat.testBit raw.val i.val) = binaryAddressBits k raw := by
    funext i
    exact (binaryAddressBits_testBit k raw i).symm
  rw [hbits]
  exact bottomUpRecompute_eq_recompute H k leaf _ siblings

/-- An ordered arithmetic node makes the two path orientations distinguishable. -/
def pathOrderWitnessSuite : BinaryMerkle.HashSuite ℕ ℕ where
  leaf := id
  node left right := 100*left+right

/-- A nonzero raw index and two actual bottom-up sibling steps inhabit the transport contract. -/
theorem native_path_premises_inhabited : NativeMerklePathContract pathOrderWitnessSuite ∧
    bottomUpRecompute pathOrderWitnessSuite 2 (binaryAddressBits 2 1) [3,4] = some 30204 := by
  exact ⟨bottomUpRecompute_eq_recompute _,by decide⟩

/-- Teeth: keeping the LSB-first decoded address in the root-first interface changes the result. -/
theorem native_path_unreversed_falsifier :
    bottomUpRecompute pathOrderWitnessSuite 2 (binaryAddressBits 2 1) [3,4] ≠
      BinaryMerkle.recompute pathOrderWitnessSuite 2 (binaryAddressBits 2 1) [3,4].reverse := by
  decide

end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.binaryAddressBits_testBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.binaryAddressBits_testBit

/-- info: 'Minidregg.Selvage.Ir2Fri.recompute_append_singleton' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.recompute_append_singleton

/-- info: 'Minidregg.Selvage.Ir2Fri.bottomUpRecompute_eq_recompute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.bottomUpRecompute_eq_recompute

/-- info: 'Minidregg.Selvage.Ir2Fri.bottomUpRecompute_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.bottomUpRecompute_raw

/-- info: 'Minidregg.Selvage.Ir2Fri.native_path_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_path_premises_inhabited

/-- info: 'Minidregg.Selvage.Ir2Fri.native_path_unreversed_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_path_unreversed_falsifier
