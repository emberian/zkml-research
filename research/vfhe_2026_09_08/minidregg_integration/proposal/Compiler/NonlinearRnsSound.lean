import Compiler.NonlinearRnsInstance
namespace Minidregg.Compiler.NonlinearRnsInstance
open Minidregg.Compiler.DirectedRnsScaler Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false
set_option maxRecDepth 20000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 3000000
/-- Small finite constant fact. No trace or accepted assignment is normalized. -/
theorem parameter_capacities : ∀ row ∈ forms params,
    leftConstant row < 2^300 ∧ rightConstant row < 2^300 ∧
    ∀ g,leftCoefficient row g < 2^201 ∧ rightCoefficient row g < 2^201 := by
  intro row hr
  rcases List.mem_append.mp hr with hr|hr
  · rcases List.mem_append.mp hr with hr|hr
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      fin_cases i <;> norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]
      all_goals intro g; fin_cases g <;> norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]
      all_goals intro g; fin_cases g <;> norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]
  · obtain ⟨i,_,hr⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> fin_cases i <;> norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]
    all_goals intro g; fin_cases g <;> norm_num [inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,params,leftConstant,rightConstant,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,Fin.ext_iff]

theorem capacity : Capacity profile rows := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro i
    have h := parameter_capacities (rows i) (List.get_mem _ _)
    exact ⟨lt_trans h.1 (by decide),lt_trans h.2.1 (by decide)⟩
  · intro i j
    have h := (parameter_capacities (rows i) (List.get_mem _ _)).2.2 (groupDigit profile|>.symm j).1
    have hp : profile.base^(groupDigit profile|>.symm j).2.val ≤ 512^22 :=
      Nat.pow_le_pow_right (by decide) (by have := (groupDigit profile|>.symm j).2.isLt; change _<23 at this; omega)
    exact ⟨lt_of_le_of_lt (Nat.mul_le_mul h.1.le hp) (by decide),
      lt_of_le_of_lt (Nat.mul_le_mul h.2.le hp) (by decide)⟩


def InstanceSound : Prop := ∀ asg,systemAccepts asg source → ∀ i,
  (decoded profile asg (target (L:=9) (K:=4) i 0) : Int)=output params (fun j => decoded profile asg (residue (L:=9) (K:=4) j))%(params.targetBase i : Int)

theorem source_balanced (asg : Nat → BabyBear) (hs : systemAccepts asg source) :
    Balanced params (decoded profile asg) := by
  intro row hm
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  have h := SignedMatrix.sourceSound profile rows capacity asg hs ⟨i.val,by change i.val<23 at *; exact i.isLt⟩
  simpa only [rows,hi] using h

theorem sourceSound : InstanceSound := by
  intro asg hs
  exact matrixSound params paramsValid _ (source_balanced asg hs)

end Minidregg.Compiler.NonlinearRnsInstance

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.parameter_capacities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.parameter_capacities

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.capacity

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.source_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.source_balanced

/-- info: 'Minidregg.Compiler.NonlinearRnsInstance.sourceSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsInstance.sourceSound
