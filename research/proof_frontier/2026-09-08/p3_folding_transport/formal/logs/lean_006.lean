/-
[DERIVED statement-first] Fixed-width bit reversal transports removal of low
runtime index bits to the natural exponent modulo the remaining domain size.
The subject is the existing BitVec.reverse/extractLsb' operations, not a new
bit-reversal implementation or a FRI probability model.
-/
import Mathlib.Data.Nat.Bitwise

namespace Minidregg.Theory.BitReverseFriTransport

set_option autoImplicit false

def ProjectionTransport : Prop :=
  ∀ (a b : Nat) (x : BitVec (b + a)),
    (x.extractLsb' a b).reverse.toNat = x.reverse.toNat % 2 ^ b

/-- A natural-number view of the existing fixed-width reversal operation. -/
def reverseIndex (bits index : Nat) : Nat := (BitVec.ofNat bits index).reverse.toNat

def QueryTransport : Prop :=
  ∀ (bits dropped index : Nat), dropped ≤ bits → index < 2 ^ bits →
    reverseIndex (bits - dropped) (index / 2 ^ dropped) =
      reverseIndex bits index % 2 ^ (bits - dropped)

theorem reverse_high_eq_low_reverse (a b : Nat) (x : BitVec (b + a)) :
    (x.extractLsb' a b).reverse = x.reverse.extractLsb' 0 b := by
  ext i hi
  simp only [BitVec.getElem_reverse, BitVec.getElem_extractLsb', Nat.zero_add,
    BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_extractLsb', BitVec.getLsbD_reverse]
  simp only [hi, show b - 1 - i < b by omega, show i < b + a by omega,
    decide_true, Bool.true_and]
  congr 1
  omega

theorem projection_transport : ProjectionTransport := by
  intro a b x
  rw [reverse_high_eq_low_reverse]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem bounded_extract (a b index : Nat) (hi : index < 2 ^ (b + a)) :
    (BitVec.ofNat (b + a) index).extractLsb' a b = BitVec.ofNat b (index / 2 ^ a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.shiftRight_eq_div_pow]

theorem query_transport : QueryTransport := by
  intro bits dropped index hd hi
  have he : bits - dropped + dropped = bits := Nat.sub_add_cancel hd
  have h := projection_transport dropped (bits - dropped)
    (BitVec.ofNat (bits - dropped + dropped) index)
  rw [bounded_extract dropped (bits - dropped) index (by simpa only [he] using hi)] at h
  exact h.trans (congrArg
    (fun width => (BitVec.ofNat width index).reverse.toNat % 2 ^ (bits - dropped)) he)

theorem query_transport_composition (bits first total index : Nat)
    (hf : first ≤ total) (ht : total ≤ bits) (hi : index < 2 ^ bits) :
    reverseIndex (bits - first) (index / 2 ^ first) % 2 ^ (bits - total) =
      reverseIndex (bits - total) (index / 2 ^ total) := by
  rw [query_transport bits first index (hf.trans ht) hi,
    query_transport bits total index ht hi]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))

theorem binary_coherent_index (bits round index : Nat)
    (hr : round + 1 ≤ bits) (hi : index < 2 ^ bits) :
    reverseIndex (bits - 1) (index / 2) % 2 ^ (bits - (round + 1)) =
      reverseIndex (bits - (round + 1)) (index / 2 ^ (round + 1)) := by
  simpa only [Nat.pow_one] using
    query_transport_composition bits 1 (round + 1) index (by omega) hr hi

theorem reverse_involution (b : Nat) (x : BitVec b) : x.reverse.reverse = x :=
  BitVec.reverse_reverse_eq

theorem reverseIndex_lt (bits index : Nat) : reverseIndex bits index < 2 ^ bits :=
  (BitVec.ofNat bits index).reverse.isLt

def reverseEquiv (b : Nat) : BitVec b ≃ BitVec b where
  toFun := BitVec.reverse
  invFun := BitVec.reverse
  left_inv := reverse_involution b
  right_inv := reverse_involution b

theorem source_premises_inhabited : 3 ≤ 8 ∧ 181 < 2 ^ 8 := by decide +kernel

theorem source_index_subject :
    ((BitVec.ofNat 8 181).extractLsb' 3 5).reverse.toNat = 13 ∧
    (BitVec.ofNat 8 181).reverse.toNat % 2 ^ 5 = 13 := by
  decide +kernel

theorem wrong_projection_refused :
    ((BitVec.ofNat 8 181).extractLsb' 3 5).reverse.toNat ≠ 181 % 2 ^ 5 := by
  decide +kernel

end Minidregg.Theory.BitReverseFriTransport
