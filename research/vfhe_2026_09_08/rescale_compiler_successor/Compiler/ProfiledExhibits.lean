import Compiler.ProfiledMatrix

namespace Minidregg.Compiler.ProfiledMatrix
open Minidregg.Compiler Minidregg.Compiler.SignedMatrix Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

def tiny : Layout := ⟨1,1,1,1,1,1⟩
def tinyRows : Fin tiny.rows → Row tiny.groups := fun _ => SignedMatrix.sub (SignedMatrix.var ⟨0,by decide⟩) (SignedMatrix.cst 1)
def tinyProfile : RowLayout tiny.rows := ⟨fun _ => 1,fun _ => 1⟩
def tinyAssignment (j : Nat) : BabyBear := if j<4 then 1 else 0

def InhabitedCompiler : Prop := Capacity tiny tinyProfile tinyRows ∧
  systemAccepts tinyAssignment (system tiny tinyProfile tinyRows) ∧ decoded tiny tinyAssignment ⟨0,by decide⟩=1

theorem inhabitedCompiler : InhabitedCompiler := by
  refine ⟨?_,?_,by decide⟩
  · constructor <;> decide
  · unfold systemAccepts
    decide

/-- Omitting the exact constant-capacity premise admits a real truncated relation:
constant2 becomes a zero one-bit digit although the integer equation is false. -/
def MissingCapacityFalsifier : Prop :=
  systemAccepts (fun _ : Nat => (0 : BabyBear)) (system tiny tinyProfile (fun _ => SignedMatrix.cst 2)) ∧
  (¬ Capacity tiny tinyProfile (fun _ => SignedMatrix.cst 2)) ∧
  SignedMatrix.eval (SignedMatrix.cst 2 : Row 1) (fun _ => 0)≠0

theorem missingCapacityFalsifier : MissingCapacityFalsifier := by
  refine ⟨?_,?_,by decide⟩
  · unfold systemAccepts
    decide
  · intro h
    have hh := (h.constants ⟨0,by decide⟩).1
    norm_num [leftConstant,SignedMatrix.cst,Minidregg.Theory.CompressedLinearEquation.posPart,tiny,Layout.base,tinyProfile] at hh

/-- info: 'Minidregg.Compiler.ProfiledMatrix.inhabitedCompiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.inhabitedCompiler

/-- info: 'Minidregg.Compiler.ProfiledMatrix.missingCapacityFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ProfiledMatrix.missingCapacityFalsifier

end Minidregg.Compiler.ProfiledMatrix
