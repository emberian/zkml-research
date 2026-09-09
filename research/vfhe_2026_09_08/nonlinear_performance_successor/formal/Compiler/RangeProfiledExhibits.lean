import Compiler.RangeProfiledCompact
import Compiler.ProfiledExhibits
namespace Minidregg.Compiler.RangeProfiledExhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.ProfiledMatrix
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

/-- A nonzero signed relation with all new premises inhabited. -/
def InhabitedCompiler : Prop := Capacity tiny tinyProfile tinyRows ∧
  systemAccepts tinyAssignment (RangeProfiledMatrix.gates tiny tinyProfile tinyRows) ∧
  RangeProfiledMatrix.Bounds tiny tinyProfile tinyAssignment ∧
  decoded tiny tinyAssignment ⟨0,by decide⟩=1
theorem inhabitedCompiler : InhabitedCompiler := by
  refine ⟨ProfiledMatrix.inhabitedCompiler.1,?_,?_,by decide⟩
  · unfold systemAccepts;decide
  · unfold RangeProfiledMatrix.Bounds;decide

/-- Range evidence cannot be omitted: a scalar equal to the field modulus minus
one can satisfy a one-bit truncated equation while its integer value is large. -/
def falseAssignment (j : Nat) : BabyBear := if j=0 then babyBearP-1 else 0
def falseRows : Fin tiny.rows → Row tiny.groups := fun _ =>
  SignedMatrix.add (SignedMatrix.var ⟨0,by decide⟩) (SignedMatrix.cst 1)
def MissingRangeFalsifier : Prop :=
  Capacity tiny tinyProfile falseRows ∧
  systemAccepts falseAssignment (RangeProfiledMatrix.gates tiny tinyProfile falseRows) ∧
  ¬ RangeProfiledMatrix.Bounds tiny tinyProfile falseAssignment ∧
  SignedMatrix.eval (falseRows ⟨0,by decide⟩) (decoded tiny falseAssignment)≠0
theorem missingRangeFalsifier : MissingRangeFalsifier := by
  refine ⟨by constructor <;> decide,?_,?_,by decide⟩
  · unfold systemAccepts;decide
  · intro h
    have hh := h.1 ⟨0,by decide⟩
    have hf : ¬ (falseAssignment (scalarWire tiny ⟨0,by decide⟩)).val<2^tiny.limbBits := by decide
    exact hf hh

def MissingCapacityFalsifier : Prop :=
  systemAccepts (fun _ : Nat => (0 : BabyBear))
    (RangeProfiledMatrix.gates tiny tinyProfile (fun _ => SignedMatrix.cst 2)) ∧
  RangeProfiledMatrix.Bounds tiny tinyProfile (fun _ => 0) ∧
  ¬ Capacity tiny tinyProfile (fun _ => SignedMatrix.cst 2)
theorem missingCapacityFalsifier : MissingCapacityFalsifier := by
  refine ⟨?_,?_,ProfiledMatrix.missingCapacityFalsifier.2.1⟩
  · unfold systemAccepts;decide
  · unfold RangeProfiledMatrix.Bounds;decide
end Minidregg.Compiler.RangeProfiledExhibits

/-- info: 'Minidregg.Compiler.RangeProfiledExhibits.inhabitedCompiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledExhibits.inhabitedCompiler

/-- info: 'Minidregg.Compiler.RangeProfiledExhibits.missingRangeFalsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledExhibits.missingRangeFalsifier

/-- info: 'Minidregg.Compiler.RangeProfiledExhibits.missingCapacityFalsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeProfiledExhibits.missingCapacityFalsifier
