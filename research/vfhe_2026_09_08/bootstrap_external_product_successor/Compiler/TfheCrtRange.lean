import Compiler.TfheCmuxDecomposition
import Mathlib.Data.Int.ModEq

namespace Minidregg.Compiler.TfheCrtRange
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Two residues uniquely determine every admissible exact signed external-product
coefficient. This is a reconstruction bound, not a theorem about a floating FFT. -/
def CrtUnique : Prop := ∀ x y : Int,
  |x| ≤ 4503599627370496 → |y| ≤ 4503599627370496 →
  x%2013265921 = y%2013265921 → x%998244353 = y%998244353 → x = y

theorem product_bound (d k : Int) (hd : |d| ≤ 512) (hk : |k| ≤ 2147483648) :
    |d*k| ≤ 1099511627776 := by
  rw [abs_mul]
  exact mul_le_mul hd hk (abs_nonneg k) (by norm_num)


theorem list_bound (terms : List Int) (h : ∀ t ∈ terms, |t| ≤ 1099511627776) :
    |terms.sum| ≤ (terms.length : Int)*1099511627776 := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
    have ht := h t (by simp)
    have hh := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [abs_le] at ht hh ⊢
    constructor <;> omega


theorem coefficient_bound (terms : List Int) (hn : terms.length ≤ 4096)
    (h : ∀ t ∈ terms, |t| ≤ 1099511627776) : |terms.sum| ≤ 4503599627370496 := by
  have hh := list_bound terms h
  have hl : (terms.length : Int) ≤ 4096 := by exact_mod_cast hn
  omega


theorem crtUnique : CrtUnique := by
  intro x y hx hy h1 h2
  have hm : Int.ModEq (2013265921*998244353) x y :=
    (Int.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨h1,h2⟩
  change x%2009731336725594113 = y%2009731336725594113 at hm
  rw [abs_le] at hx hy
  omega

/-- Interpreting the raw unsigned torus coefficient as signed32 changes no residue. -/

theorem centered_u32 (x : Int) (hx : 0 ≤ x ∧ x < 4294967296) :
    (if x < 2147483648 then x else x-4294967296)%4294967296 = x := by
  split_ifs <;> omega


theorem scale_low24 (x : Int) : (256*x)%4294967296 = 256*(x%16777216) := by
  omega

def signedCrt (u : Int) := if u > 2009731336725594113/2 then u-2009731336725594113 else u


theorem negative_one_witness : signedCrt 2009731336725594112 = -1 ∧
    (-1 : Int)%2013265921 = 2013265920 ∧ (-1 : Int)%998244353 = 998244352 := by decide +kernel


theorem changed_zero_refused (x : Int) (hx : |x| ≤ 4503599627370496)
    (h1 : x%2013265921 = 0) (h2 : x%998244353 = 0) : x ≠ 1 := by
  have hz : x = 0 := crtUnique x 0 hx (by norm_num) h1 h2
  omega

/-- info: 'Minidregg.Compiler.TfheCrtRange.product_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms product_bound
/-- info: 'Minidregg.Compiler.TfheCrtRange.list_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms list_bound
/-- info: 'Minidregg.Compiler.TfheCrtRange.coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coefficient_bound
/-- info: 'Minidregg.Compiler.TfheCrtRange.crtUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms crtUnique
/-- info: 'Minidregg.Compiler.TfheCrtRange.centered_u32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms centered_u32
/-- info: 'Minidregg.Compiler.TfheCrtRange.scale_low24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scale_low24
/-- info: 'Minidregg.Compiler.TfheCrtRange.negative_one_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms negative_one_witness
/-- info: 'Minidregg.Compiler.TfheCrtRange.changed_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms changed_zero_refused
end Minidregg.Compiler.TfheCrtRange
