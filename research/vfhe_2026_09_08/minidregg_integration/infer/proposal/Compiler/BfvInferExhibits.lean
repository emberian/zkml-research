import Compiler.BfvInferComposition
import Compiler.BfvKeyswitchExhibits
namespace Minidregg.Compiler.BfvInferComposition.Exhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open BfvKeyswitchCore
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

def sample : Operands where
  d := ![1,2,3,4]
  key := fun h _ => if h.val=0 then 2 else 3
  addend := ![7,5]

def RowPremiseInhabited : Prop := ∃ w : Wires BabyBear,
  systemAccepts id (BfvKeyswitchCore.system 37 w) ∧ Bound w id sample ![27,35]

theorem good_bound : Bound BfvKeyswitchCore.Exhibits.good id sample ![27,35] := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; rw [BfvKeyswitchCore.Exhibits.good_values]
    fin_cases i <;> rfl
  · intro h i; rw [BfvKeyswitchCore.Exhibits.good_values]
    fin_cases h <;> fin_cases i <;> rfl
  · intro h; rw [BfvKeyswitchCore.Exhibits.good_values]
    fin_cases h <;> rfl
  · intro h; rw [BfvKeyswitchCore.Exhibits.good_values]
    fin_cases h <;> rfl

theorem rowPremiseInhabited : RowPremiseInhabited :=
  ⟨BfvKeyswitchCore.Exhibits.good,BfvKeyswitchCore.Exhibits.nonzero_premise.1,good_bound⟩

def ChangedOutputRefused : Prop := ∀ (J : Type) (w : Wires J) (asg : J → BabyBear)
  (out : Fin 2 → Nat),systemAccepts asg (BfvKeyswitchCore.system 37 w) →
  Bound w asg sample out → out 0≠19

theorem changedOutputRefused : ChangedOutputRefused := by
  intro J w asg out hs hb
  have heq := boundRowSound J 37 (by decide) (by decide) w asg sample out hs hb 0
  have hvalue : output 37 sample 0=27 := by decide
  omega

def sampleStep (_n x : Nat) : Nat := (x+2)%37
def sampleTrace : Nat → Nat := iterate sampleStep 7

def PrefixPremiseInhabited : Prop := ∃ trace : Nat → Nat,
  trace 0=7 ∧ (∀ i,i<10 → trace (i+1)=sampleStep i (trace i)) ∧ trace 10=27

theorem prefixPremiseInhabited : PrefixPremiseInhabited := by
  exact ⟨sampleTrace,rfl,fun _ _ => rfl,by decide⟩

/-- Dropping the last accumulated stage gives a different value even when the
same modular arithmetic is used. This tests stage coverage, not row arithmetic. -/
def MissingStageChangesOutput : Prop := iterate sampleStep 7 9≠iterate sampleStep 7 10

theorem missingStageChangesOutput : MissingStageChangesOutput := by
  unfold MissingStageChangesOutput
  decide
end Minidregg.Compiler.BfvInferComposition.Exhibits

/-- info: 'Minidregg.Compiler.BfvInferComposition.Exhibits.good_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.Exhibits.good_bound

/-- info: 'Minidregg.Compiler.BfvInferComposition.Exhibits.rowPremiseInhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.Exhibits.rowPremiseInhabited

/-- info: 'Minidregg.Compiler.BfvInferComposition.Exhibits.changedOutputRefused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.Exhibits.changedOutputRefused

/-- info: 'Minidregg.Compiler.BfvInferComposition.Exhibits.prefixPremiseInhabited' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.Exhibits.prefixPremiseInhabited

/-- info: 'Minidregg.Compiler.BfvInferComposition.Exhibits.missingStageChangesOutput' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.Exhibits.missingStageChangesOutput
