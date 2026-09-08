import Compiler.ProfiledMatrix
import Compiler.NonlinearRnsPublicSound

namespace Minidregg.Compiler.NonlinearRnsProfiled
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.DirectedRnsScaler
open Minidregg.Compiler.NonlinearRnsInstance
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1000

/-- Compile-time profile emitted by autoLayout, not fitted to runtime witnesses. -/
def rowLayout : ProfiledMatrix.RowLayout profile.rows where
  width := ![24,24,24,24,24,24,24,24,24,38,24,38,24,46,24,29,24,29,24,29,24,29,24]
  carryBits := ![2,2,2,2,2,2,2,2,2,15,2,14,2,16,2,11,2,11,2,11,2,11,2]

def ProfileDerived : Prop := rowLayout=ProfiledMatrix.autoLayout profile rows

theorem profileDerived : ProfileDerived := by
  apply congrArg₂ (@ProfiledMatrix.RowLayout.mk 23)
  · funext i; fin_cases i <;> decide
  · funext i; fin_cases i <;> decide

/-- Only row coefficient capacities are computed; no accepted trace is reduced. -/
theorem coefficients_fit : ∀ i g,
    leftCoefficient (rows i) g < 512^(rowLayout.width i-22) ∧
    rightCoefficient (rows i) g < 512^(rowLayout.width i-22) := by
  intro i
  fin_cases i <;>
    norm_num [rows,forms,profile,rowLayout,inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,
      params,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,
      SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,
      Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,List.finRange_succ,Fin.ext_iff,Matrix.cons_val]
  all_goals intro g; fin_cases g <;>
    norm_num [rows,forms,profile,rowLayout,inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,
      params,leftCoefficient,rightCoefficient,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,
      SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,
      Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,List.finRange_succ,Fin.ext_iff,Matrix.cons_val]
  all_goals decide

theorem constants_fit : ∀ i,leftConstant (rows i) < 512^(rowLayout.width i) ∧
    rightConstant (rows i) < 512^(rowLayout.width i) := by
  intro i
  fin_cases i <;>
    norm_num [rows,forms,profile,rowLayout,inputRow,gRow,gBound,fRow,fBound,yRow,yBound,targetRow,targetBound,
      params,leftConstant,rightConstant,linear,SignedMatrix.sum,SignedMatrix.sub,SignedMatrix.add,SignedMatrix.scale,
      SignedMatrix.var,SignedMatrix.cst,Fin.sum_univ_succ,Minidregg.Theory.CompressedLinearEquation.posPart,
      Minidregg.Theory.CompressedLinearEquation.negPart,residue,inputSlack,extra,target,List.finRange_succ,Fin.ext_iff,Matrix.cons_val]
  all_goals decide

theorem capacity : ProfiledMatrix.Capacity profile rowLayout rows := by
  constructor
  · decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · exact constants_fit
  · intro i j
    have h := coefficients_fit i (groupDigit profile|>.symm j).1
    have hp : profile.base^(groupDigit profile|>.symm j).2.val ≤ 512^22 :=
      Nat.pow_le_pow_right (by decide) (by have := (groupDigit profile|>.symm j).2.isLt; change _<23 at this; omega)
    have hw : 22 ≤ rowLayout.width i := by fin_cases i <;> decide
    have he : 512^(rowLayout.width i-22)*512^22=profile.base^(rowLayout.width i) := by
      rw [← pow_add,Nat.sub_add_cancel hw]; rfl
    constructor
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hp) (he ▸ Nat.mul_lt_mul_of_pos_right h.1 (by positivity))
    · exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hp) (he ▸ Nat.mul_lt_mul_of_pos_right h.2 (by positivity))

def source := ProfiledMatrix.system profile rowLayout rows
def system : ConstraintSystem BabyBear Nat := [vr 88] ++ renameS NonlinearRnsPublic.wireMap source
def nVars := 89+ProfiledMatrix.nVars profile rowLayout

def RowSound : Prop := ∀ asg,systemAccepts asg system → ∀ i,
  (NonlinearRnsPublic.publicOutput asg i : Int)=nativeProjectedOutput (NonlinearRnsPublic.publicResidues asg) i

theorem source_balanced (asg : Nat → BabyBear) (hs : systemAccepts asg source) : Balanced params (decoded profile asg) := by
  intro row hm
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  have h := ProfiledMatrix.sourceSound profile rowLayout rows capacity asg hs ⟨i.val,by change i.val<23 at *; exact i.isLt⟩
  simpa only [rows,hi] using h

theorem rowSound : RowSound := by
  intro asg hs i
  obtain ⟨hz,hs⟩ := (systemAccepts_append asg _ _).mp hs
  have hz' : asg 88=0 := by simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using hz
  have ha := (systemAccepts_renameS asg NonlinearRnsPublic.wireMap source).mp hs
  have hb := source_balanced (asg ∘ NonlinearRnsPublic.wireMap) ha
  have hc := balanced_accepts params paramsValid _ hb
  have hw := nativeWordRefinement _ hc.1
  have hout := matrixSound params paramsValid _ hb i
  rw [← hw,NonlinearRnsPublic.input_public asg hz',congrFun (NonlinearRnsPublic.output_public asg hz') i,
    canonical_lift_preserves_native] at hout
  exact hout

theorem simplifiedSource_sound (asg : Nat → BabyBear) (h : systemAccepts asg (AirSimplify.simplifySystem system)) :
    ∀ i,(NonlinearRnsPublic.publicOutput asg i : Int)=nativeProjectedOutput (NonlinearRnsPublic.publicResidues asg) i :=
  rowSound asg ((AirSimplify.simplifySystem_accepts_iff asg system).mp h)

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.profileDerived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.profileDerived

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.coefficients_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.coefficients_fit

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.constants_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.constants_fit

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.capacity

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.source_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.source_balanced

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.rowSound

/-- info: 'Minidregg.Compiler.NonlinearRnsProfiled.simplifiedSource_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsProfiled.simplifiedSource_sound

end Minidregg.Compiler.NonlinearRnsProfiled
