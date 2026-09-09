import Compiler.ProfiledMatrix

namespace Minidregg.Compiler.ProfiledMatrix
open Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false

def UnsignedMassBound : Prop := ∀ (p : Layout) c matrix (x : Fin p.groups → Nat),
  (∀ g,x g < p.base^p.digits) → c+∑ g,matrix g*x g ≤ sideMassBound p c matrix

theorem unsignedMassBound : UnsignedMassBound := by
  intro p c matrix x hx
  apply Nat.add_le_add_left
  calc
    ∑ g,matrix g*x g ≤ ∑ g,matrix g*(p.base^p.digits-1) := by
      apply Finset.sum_le_sum
      intro g _
      exact Nat.mul_le_mul_left _ (by have := hx g; omega)
    _ = (p.base^p.digits-1)*∑ g,matrix g := by rw [← Finset.sum_mul,mul_comm]

def WidthSufficient : Prop := ∀ bits mass : Nat,0<bits → mass < (2^bits)^(1+Nat.log2 mass/bits)

theorem widthSufficient : WidthSufficient := by
  intro bits mass hb
  have he : Nat.log2 mass+1 ≤ bits*(1+Nat.log2 mass/bits) := by
    have hr := Nat.mod_lt (Nat.log2 mass) hb
    have hd := Nat.div_add_mod (Nat.log2 mass) bits
    nlinarith
  calc
    mass < 2^(Nat.log2 mass+1) := Nat.lt_log2_self
    _ ≤ 2^(bits*(1+Nat.log2 mass/bits)) := Nat.pow_le_pow_right (by decide) he
    _ = (2^bits)^(1+Nat.log2 mass/bits) := by rw [pow_mul]

/-- The unsigned mass, not a sampled trace, determines every automatic result width. -/
theorem auto_width_sufficient (p : Layout) (rows : Fin p.rows → Row p.groups) (hb : 0<p.limbBits) (i : Fin p.rows) :
    sideMassBound p (leftConstant (rows i)) (leftCoefficient (rows i)) < p.base^((autoLayout p rows).width i) ∧
    sideMassBound p (rightConstant (rows i)) (rightCoefficient (rows i)) < p.base^((autoLayout p rows).width i) := by
  have h := widthSufficient p.limbBits
    (max (sideMassBound p (leftConstant (rows i)) (leftCoefficient (rows i)))
      (sideMassBound p (rightConstant (rows i)) (rightCoefficient (rows i)))) hb
  exact ⟨lt_of_le_of_lt (le_max_left _ _) h,lt_of_le_of_lt (le_max_right _ _) h⟩

/-- A conventional column recurrence invariant; callers supply a static column
mass budget, never an assertion that a sampled carry happened to fit. -/
theorem carry_step_bound (base cap column carry : Nat) (hb : 0<base)
    (hcarry : carry≤cap) (hcolumn : column≤(base-1)*cap) : (column+carry)/base≤cap := by
  apply (Nat.div_le_iff_le_mul_add_pred hb).mpr
  have h : column+carry≤base*cap := by
    calc
      column+carry ≤ (base-1)*cap+cap := Nat.add_le_add hcolumn hcarry
      _ = base*cap := by rw [← add_one_mul]; congr 1; omega
  omega

/-- info: 'Minidregg.Compiler.ProfiledMatrix.unsignedMassBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.unsignedMassBound

/-- info: 'Minidregg.Compiler.ProfiledMatrix.widthSufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.widthSufficient

/-- info: 'Minidregg.Compiler.ProfiledMatrix.auto_width_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.auto_width_sufficient

/-- info: 'Minidregg.Compiler.ProfiledMatrix.carry_step_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.carry_step_bound

end Minidregg.Compiler.ProfiledMatrix
