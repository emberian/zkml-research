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

theorem reverse_involution (b : Nat) (x : BitVec b) : x.reverse.reverse = x :=
  BitVec.reverse_reverse_eq

theorem source_index_subject :
    ((BitVec.ofNat 8 181).extractLsb' 3 5).reverse.toNat = 13 ∧
    (BitVec.ofNat 8 181).reverse.toNat % 2 ^ 5 = 13 := by
  decide +kernel

theorem wrong_projection_refused :
    ((BitVec.ofNat 8 181).extractLsb' 3 5).reverse.toNat ≠ 181 % 2 ^ 5 := by
  decide +kernel

end Minidregg.Theory.BitReverseFriTransport
