import Compiler.DirectedRnsWitness

namespace Minidregg.Compiler.DirectedRnsScaler
open Minidregg.Compiler.SignedMatrix
set_option autoImplicit false

def small : Params 1 1 where
  sourceBase := fun _ => 31
  targetBase := fun _ => 31
  Q := 31
  thetaG := fun _ => 0
  thetaF := fun _ => 1
  omega := fun _ => 2
  gamma := 0
  dG := 1
  dF := 2
  wOffset := 8
  uOffset := 8

def smallValues : Fin (groups 1 1) → Nat := ![3,27,0,1,0,10,0,3,8,22,8,8,0,22]

def Nonvacuous : Prop := Valid small ∧ Balanced small smallValues ∧
  output small (fun _ => 3)=8

def WrongRoundingRefused : Prop := ∀ c,¬ Accepts small (fun _ => 3) (fun _ => 7) c

theorem nonvacuous : Nonvacuous := by
  refine ⟨⟨by decide,by decide,by decide,by decide,by decide,by decide⟩,?_,by decide⟩
  unfold Balanced
  decide

theorem wrongRoundingRefused : WrongRoundingRefused := by
  intro c h
  have hh := certificateSound small nonvacuous.1 _ _ c h 0
  norm_num [output,v,w,roundDiv,small,Fin.sum_univ_succ] at hh

end Minidregg.Compiler.DirectedRnsScaler

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.nonvacuous

/-- info: 'Minidregg.Compiler.DirectedRnsScaler.wrongRoundingRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.DirectedRnsScaler.wrongRoundingRefused
