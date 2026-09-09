import Compiler.ProfiledBounds

namespace Minidregg.Compiler.ProfiledMatrix
open Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false

/-- Every shifted coefficient fits inside the same unsigned mass used to select
the automatic result width; this removes per-instance coefficient assumptions. -/
theorem coefficient_le_mass (p : Layout) (c : Nat) (matrix : Fin p.groups → Nat)
    (hb : 1<p.base) (j : Fin p.scalars) : digitCoefficient p matrix j≤sideMassBound p c matrix := by
  let gd := (groupDigit p).symm j
  have hd : p.base^gd.2.val≤p.base^p.digits-1 := by
    have h := Nat.pow_lt_pow_right hb gd.2.isLt
    omega
  have hm : matrix gd.1≤∑ g,matrix g :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (matrix g)) (Finset.mem_univ gd.1)
  change matrix gd.1*p.base^gd.2.val≤_
  calc
    matrix gd.1*p.base^gd.2.val≤matrix gd.1*(p.base^p.digits-1) := Nat.mul_le_mul_left _ hd
    _ ≤ (∑ g,matrix g)*(p.base^p.digits-1) := Nat.mul_le_mul_right _ hm
    _ ≤ sideMassBound p c matrix := by dsimp [sideMassBound]; rw [mul_comm]; omega

theorem auto_constants (p : Layout) (rows : Fin p.rows → Row p.groups) (hb : 0<p.limbBits) :
    ∀ i,leftConstant (rows i)<p.base^((autoLayout p rows).width i) ∧
      rightConstant (rows i)<p.base^((autoLayout p rows).width i) := by
  intro i
  have hw := auto_width_sufficient p rows hb i
  exact ⟨lt_of_le_of_lt (Nat.le_add_right _ _) hw.1,lt_of_le_of_lt (Nat.le_add_right _ _) hw.2⟩

theorem auto_coefficients (p : Layout) (rows : Fin p.rows → Row p.groups) (hb : 0<p.limbBits) :
    ∀ i j,digitCoefficient p (leftCoefficient (rows i)) j<p.base^((autoLayout p rows).width i) ∧
      digitCoefficient p (rightCoefficient (rows i)) j<p.base^((autoLayout p rows).width i) := by
  have hbase : 1<p.base := by
    change 1<2^p.limbBits
    exact Nat.one_lt_two_pow (by omega)
  intro i j
  have hw := auto_width_sufficient p rows hb i
  exact ⟨lt_of_le_of_lt (coefficient_le_mass p _ _ hbase j) hw.1,
    lt_of_le_of_lt (coefficient_le_mass p _ _ hbase j) hw.2⟩

/-- info: 'Minidregg.Compiler.ProfiledMatrix.coefficient_le_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.coefficient_le_mass

/-- info: 'Minidregg.Compiler.ProfiledMatrix.auto_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.auto_constants

/-- info: 'Minidregg.Compiler.ProfiledMatrix.auto_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.auto_coefficients

end Minidregg.Compiler.ProfiledMatrix
