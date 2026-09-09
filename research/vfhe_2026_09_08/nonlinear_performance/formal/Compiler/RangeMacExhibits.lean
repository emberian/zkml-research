/- Nonzero premise and canonical omitted-product refusal for the generic source
used by the actual compact layout. No large closed trace is kernel evaluated. -/
import Compiler.RangeCompletedMac
import Compiler.BfvKeyswitchExhibits
namespace Minidregg.Compiler.RangeMacExhibits
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.BfvKeyswitchCore
open Minidregg.Compiler.BfvKeyswitchCore.Exhibits
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

def NonzeroPremise : Prop :=
  systemAccepts id (RangeCompletedMac.gates 37 good) ∧
  RangeCompletedMac.Bounds id good ∧ value id good 0=1 ∧ value id good 14=27

def MissingProductFalsifier : Prop :=
  ¬(systemAccepts id (RangeCompletedMac.gates 37 wrong) ∧ RangeCompletedMac.Bounds id wrong)

theorem nonzeroPremise : NonzeroPremise := by
  refine ⟨RangeCompletedMac.source_reduction 37 good id nonzero_premise.1,?_,good_values 0,good_values 14⟩
  refine ⟨?_,?_,?_⟩
  · intro g i
    fin_cases g <;> fin_cases i <;> norm_num [good,vals,lo] <;> decide
  · intro h i
    norm_num [good]
  · intro h i
    norm_num [good]
    decide

theorem missingProductFalsifier : MissingProductFalsifier := by
  intro h
  have hh := (RangeCompletedMac.sound 37 (by decide) (by decide) wrong id h.1 h.2).2 0
  norm_num [wrong_values,vals,oIndex,aIndex,dIndex,kIndex,Fin.sum_univ_succ] at hh

theorem premiseInhabited : ∃ w : Wires BabyBear,
    systemAccepts id (RangeCompletedMac.gates 37 w) ∧ RangeCompletedMac.Bounds id w ∧
    value id w 0≠0 ∧ value id w 14≠0 := by
  refine ⟨good,nonzeroPremise.1,nonzeroPremise.2.1,?_,?_⟩
  · rw [good_values]; decide
  · rw [good_values]; decide
end Minidregg.Compiler.RangeMacExhibits

/-- info: 'Minidregg.Compiler.RangeMacExhibits.nonzeroPremise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeMacExhibits.nonzeroPremise

/-- info: 'Minidregg.Compiler.RangeMacExhibits.missingProductFalsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeMacExhibits.missingProductFalsifier

/-- info: 'Minidregg.Compiler.RangeMacExhibits.premiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeMacExhibits.premiseInhabited

