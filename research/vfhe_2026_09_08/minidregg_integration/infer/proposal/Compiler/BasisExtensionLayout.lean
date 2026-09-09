import Compiler.ActualBasisExtension

namespace Minidregg.Compiler.ActualBasisExtension
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.ExactBasisExtension Minidregg.Compiler.SignedMatrix
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

def rowLayout : ProfiledMatrix.RowLayout profile.rows where
  width := ![23,23,23,23,37,23,45,23,45,23,45,23,45,23,45,23,22,22,22,22]
  carryBits := ![2,2,2,2,14,2,15,2,15,2,15,2,15,2,15,2,2,2,2,2]

def ProfileDerived : Prop := rowLayout=ProfiledMatrix.autoLayout profile rows
theorem profileDerived : ProfileDerived := by
  apply congrArg₂ (@ProfiledMatrix.RowLayout.mk 20)
  · funext i; fin_cases i <;> decide
  · funext i; fin_cases i <;> decide

theorem paramsValid : Valid params := by constructor <;> decide

theorem capacity : ProfiledMatrix.Capacity profile rowLayout rows := by
  constructor
  · decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · rw [profileDerived]
    exact ProfiledMatrix.auto_constants profile rows (by decide)
  · rw [profileDerived]
    exact ProfiledMatrix.auto_coefficients profile rows (by decide)

def source := ProfiledMatrix.system profile rowLayout rows
def SourceSound : Prop := ∀ asg,systemAccepts asg source → Semantics params (decoded profile asg)

theorem source_balanced (asg : Nat → BabyBear) (hs : systemAccepts asg source) :
    Balanced params (decoded profile asg) := by
  intro row hm
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  have h := ProfiledMatrix.sourceSound profile rowLayout rows capacity asg hs
    ⟨i.val,by change i.val<20 at *;exact i.isLt⟩
  simpa only [rows,hi] using h

theorem sourceSound : SourceSound := by
  intro asg hs
  exact ExactBasisExtension.matrixSound params paramsValid _ (source_balanced asg hs)

/-- info: 'Minidregg.Compiler.ActualBasisExtension.profileDerived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.profileDerived

/-- info: 'Minidregg.Compiler.ActualBasisExtension.paramsValid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.paramsValid

/-- info: 'Minidregg.Compiler.ActualBasisExtension.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.capacity

/-- info: 'Minidregg.Compiler.ActualBasisExtension.source_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.source_balanced

/-- info: 'Minidregg.Compiler.ActualBasisExtension.sourceSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.sourceSound

end Minidregg.Compiler.ActualBasisExtension
