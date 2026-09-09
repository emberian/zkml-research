import Compiler.RangeProfiledExhibits
namespace Minidregg.Compiler.RangeProfiledCompactExhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.ProfiledMatrix
open Minidregg.Compiler.RangeProfiledCompact
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

def tinyCompact : Profile := ⟨tiny,tinyProfile,tinyRows,1,fun j => 2+j⟩
def good (j : Nat) : BabyBear := if j=2 ∨ j=3 then 1 else 0
def wrong (j : Nat) : BabyBear := if j=3 then 1 else 0
def InhabitedCompact : Prop := ProfiledMatrix.Capacity tiny tinyProfile tinyRows ∧
  systemAccepts good (RangeProfiledCompact.system tinyCompact) ∧
  RangeHolds tinyCompact good ∧
  decoded tiny (good ∘ indexMap tinyCompact ∘ tinyCompact.oldMap) ⟨0,by decide⟩=1
theorem inhabitedCompact : InhabitedCompact := by
  refine ⟨ProfiledMatrix.inhabitedCompiler.1,?_,?_,by decide⟩
  · unfold systemAccepts;decide
  · unfold RangeHolds;decide

/-- Same admitted shape and range values, with one scalar changed: the generated
arithmetic refuses the missing value. -/
def ChangedScalarRefused : Prop := RangeHolds tinyCompact wrong ∧
  ¬ systemAccepts wrong (RangeProfiledCompact.system tinyCompact)
theorem changedScalarRefused : ChangedScalarRefused := by
  constructor
  · unfold RangeHolds;decide
  · unfold systemAccepts;decide
end Minidregg.Compiler.RangeProfiledCompactExhibits

/-- info: 'Minidregg.Compiler.RangeProfiledCompactExhibits.inhabitedCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompactExhibits.inhabitedCompact

/-- info: 'Minidregg.Compiler.RangeProfiledCompactExhibits.changedScalarRefused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledCompactExhibits.changedScalarRefused
