/- The deployed IR2 FRI row points use the certified BabyBear roots, natural
powers on the subgroup, and bit reversal within each packed row. The input
PCS's separate multiplicative coset shift31 is not inserted into FRI nodes. -/
import Selvage.P3NativeFoldRows
import Selvage.BabyBearFoldingTower
import Theory.BitReverseFriTransport
import Mathlib.Data.BitVec

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4
open Minidregg.Theory.BitReverseFriTransport
open scoped Classical
noncomputable section

/-- The actual bit-reversal permutation of row column indices. -/
def reverseFin (a : ℕ) : Fin (2^a) ≃ Fin (2^a) :=
  (BitVec.equivFin.toEquiv.symm.trans (reverseEquiv a)).trans BitVec.equivFin.toEquiv

lemma reverseFin_value (a : ℕ) (i : Fin (2^a)) :
    (reverseFin a i).val = reverseIndex a i.val := by
  change (BitVec.ofFin i).reverse.toNat = (BitVec.ofNat a i.val).reverse.toNat
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

/-- Dropping h root bits has the exact certified repeated-squaring convention. -/
theorem omega_power_drop (h a : ℕ) (ha : h+a ≤ 27) :
    TwoAdic.omega (h+a)^(2^h) = TwoAdic.omega a := by
  unfold TwoAdic.omega
  rw [←pow_mul,←pow_add]
  congr 2
  omega

/-- Exact native packed-row coset, for supported height and any log arity. -/
def rowNodes (h a : ℕ) (ha : h+a ≤ 27) (row : Fin (2^h)) :
    P3Barycentric.CosetNodes Ext4 (2^a) :=
  P3Barycentric.reindex
    (P3Barycentric.fromPrimitive (TwoAdic.omega a) (TwoAdic.omega_primitive a (by omega))
      (by positivity) ((TwoAdic.omega (h+a))^(reverseIndex h row.val))
      (pow_ne_zero _ (TwoAdic.omega_ne_zero (h+a) ha))
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using pow_ne_zero a MultiplicativeTower.two_ne_zero))
    (reverseFin a)

/-- This is the formula executed by two_adic_pcs.rs:243–250. -/
theorem rowNodes_source (h a : ℕ) (ha : h+a ≤ 27) (row : Fin (2^h)) (j : Fin (2^a)) :
    (rowNodes h a ha row).nodes j =
      TwoAdic.omega (h+a)^(reverseIndex h row.val) *
      TwoAdic.omega a^(reverseIndex a j.val) := by
  change TwoAdic.omega (h+a)^(reverseIndex h row.val) * TwoAdic.omega a^(reverseFin a j).val = _
  rw [reverseFin_value]

/-- Native row columns are actual source-domain natural exponents. -/
def rowSourceIndex (h a : ℕ) (row : Fin (2^h)) (j : Fin (2^a)) : Fin (2^(h+a)) :=
  ⟨reverseIndex h row.val+2^h*reverseIndex a j.val,by
    have hr := reverseIndex_lt h row.val
    have hj := reverseIndex_lt a j.val
    have hp : 0 < 2^h := by positivity
    rw [pow_add]
    nlinarith⟩

/-- Source-domain membership is proved from roots; it is not a claim about
numeric field labels or an arbitrary row-point convention. -/
theorem rowNodes_sourceIndex (h a : ℕ) (ha : h+a ≤ 27)
    (row : Fin (2^h)) (j : Fin (2^a)) :
    (rowNodes h a ha row).nodes j = TwoAdic.omega (h+a)^(rowSourceIndex h a row j).val := by
  rw [rowNodes_source,←omega_power_drop h a ha]
  simp only [rowSourceIndex,pow_add,pow_mul]

/-- The entire packed row projects onto the same actual parent exponent. -/
theorem rowSourceIndex_parent (h a : ℕ) (row : Fin (2^h)) (j : Fin (2^a)) :
    (rowSourceIndex h a row j).val % 2^h = reverseIndex h row.val := by
  simp only [rowSourceIndex,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (reverseIndex_lt h row.val)

/-- Source native folding is interpolation on these certified actual field
nodes, with the explicit beta=node branch already proved. -/
theorem row_native_correct (h a : ℕ) (ha : h+a ≤ 27) (row : Fin (2^h)) :
    P3Barycentric.Correctness (rowNodes h a ha row) := P3Barycentric.correctness _

/-- The input PCS uses the coset31 coordinate while FRI uses subgroup t.
This function records that actual source substitution without conflating them. -/
def inputPoint (h : ℕ) (index : Fin (2^h)) : Ext4 :=
  (31:Ext4)*TwoAdic.omega h^(reverseIndex h index.val)

/-- Exact evaluation substitution for an honest input polynomial on the
subgroup coordinate used by FRI. -/
theorem input_coset_substitution (h : ℕ) (index : Fin (2^h)) (p : Polynomial Ext4) :
    p.eval (inputPoint h index) =
      (p.comp (Polynomial.C (31:Ext4)*Polynomial.X)).eval
        (TwoAdic.omega h^(reverseIndex h index.val)) := by
  simp [inputPoint,Polynomial.eval_comp]

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.reverseFin_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.reverseFin_value

/-- info: 'Minidregg.Selvage.Ir2Fri.omega_power_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.omega_power_drop

/-- info: 'Minidregg.Selvage.Ir2Fri.rowNodes_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.rowNodes_source

/-- info: 'Minidregg.Selvage.Ir2Fri.rowNodes_sourceIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.rowNodes_sourceIndex

/-- info: 'Minidregg.Selvage.Ir2Fri.rowSourceIndex_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.rowSourceIndex_parent

/-- info: 'Minidregg.Selvage.Ir2Fri.row_native_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.row_native_correct

/-- info: 'Minidregg.Selvage.Ir2Fri.input_coset_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.input_coset_substitution

