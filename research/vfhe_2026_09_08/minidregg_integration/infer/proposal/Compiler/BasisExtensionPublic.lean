import Compiler.BasisExtensionNative
import Compiler.AirSimplify
import Compiler.PredCompile

namespace Minidregg.Compiler.ActualBasisExtension
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.ExactBasisExtension Minidregg.Compiler.SignedMatrix
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

def nVars := 85+ProfiledMatrix.nVars profile rowLayout
def wireMap (j : Nat) : Nat :=
  if j<profile.scalars then
    let g := j/22
    let d := j%22
    if g<4 then if d<6 then 1+6*g+d else 84
    else if 26≤g ∧ g<30 then if d<6 then 25+6*(g-26)+d else 84
    else if 11≤g ∧ g<26 ∧ (g-11)%3=0 then
      if d<7 then 49+7*((g-11)/3)+d else 84
    else 85+j
  else 85+j
def system : ConstraintSystem BabyBear Nat := [vr 84] ++ renameS wireMap source

def publicInput (asg : Nat → BabyBear) (i : Fin 4) : Nat :=
  ∑ d : Fin 6,512^d.val*(asg (1+6*i.val+d.val)).val
def publicCopy (asg : Nat → BabyBear) (i : Fin 4) : Nat :=
  ∑ d : Fin 6,512^d.val*(asg (25+6*i.val+d.val)).val
def publicNew (asg : Nat → BabyBear) (i : Fin 5) : Nat :=
  ∑ d : Fin 7,512^d.val*(asg (49+7*i.val+d.val)).val

theorem input_wire (i : Fin 4) (d : Fin 22) :
    wireMap (scalarWire profile (groupDigit profile (residue (K:=5) i,d)))=
      if d.val<6 then 1+6*i.val+d.val else 84 := by
  change wireMap (d.val+22*i.val)=_
  have hi := i.isLt; have hd := d.isLt
  have hdiv : (d.val+22*i.val)/22=i.val := by omega
  have hmod : (d.val+22*i.val)%22=d.val := by omega
  simp only [wireMap,profile,Layout.scalars,hdiv,hmod,
    show d.val+22*i.val<30*22 by omega,if_true,hi]

theorem copy_wire (i : Fin 4) (d : Fin 22) :
    wireMap (scalarWire profile (groupDigit profile (copied (K:=5) i,d)))=
      if d.val<6 then 25+6*i.val+d.val else 84 := by
  change wireMap (d.val+22*(26+i.val))=_
  have hi := i.isLt; have hd := d.isLt
  have hdiv : (d.val+22*(26+i.val))/22=26+i.val := by omega
  have hmod : (d.val+22*(26+i.val))%22=d.val := by omega
  simp only [wireMap,profile,Layout.scalars,hdiv,hmod,
    show d.val+22*(26+i.val)<30*22 by omega,if_true,
    show ¬26+i.val<4 by omega,if_false,show 26≤26+i.val by omega,
    show 26+i.val<30 by omega,and_self,show 26+i.val-26=i.val by omega]

theorem new_wire (i : Fin 5) (d : Fin 22) :
    wireMap (scalarWire profile (groupDigit profile (target (L:=4) i 0,d)))=
      if d.val<7 then 49+7*i.val+d.val else 84 := by
  change wireMap (d.val+22*(11+3*i.val+0))=_
  rw [Nat.add_zero]
  have hi := i.isLt; have hd := d.isLt
  have hdiv : (d.val+22*(11+3*i.val))/22=11+3*i.val := by omega
  have hmod : (d.val+22*(11+3*i.val))%22=d.val := by omega
  simp only [wireMap,profile,Layout.scalars,hdiv,hmod,
    show d.val+22*(11+3*i.val)<30*22 by omega,if_true,
    show ¬11+3*i.val<4 by omega,if_false,
    show ¬(26≤11+3*i.val ∧ 11+3*i.val<30) by omega,
    show 11≤11+3*i.val by omega,show 11+3*i.val<26 by omega,
    show (11+3*i.val-11)%3=0 by omega,and_self,
    show (11+3*i.val-11)/3=i.val by omega]

theorem input_public (asg : Nat → BabyBear) (hz : asg 84=0) :
    (fun i : Fin 4 => decoded profile (asg ∘ wireMap) (residue (K:=5) i))=publicInput asg := by
  funext i
  unfold decoded publicInput
  simp_rw [Function.comp_apply,input_wire]
  simp only [profile,Layout.base]
  change (∑ d : Fin (6+16),512^d.val*(asg (if d.val<6 then 1+6*i.val+d.val else 84)).val)=_
  rw [Fin.sum_univ_add]
  have hh : ∀ d : Fin 16,¬(d.natAdd 6).val<6 := by intro d;simp
  simp only [hh,if_false,hz,ZMod.val_zero,mul_zero,Finset.sum_const_zero,add_zero,Fin.val_castAdd]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.isLt,if_true]

theorem copy_public (asg : Nat → BabyBear) (hz : asg 84=0) :
    (fun i : Fin 4 => decoded profile (asg ∘ wireMap) (copied (K:=5) i))=publicCopy asg := by
  funext i
  unfold decoded publicCopy
  simp_rw [Function.comp_apply,copy_wire]
  simp only [profile,Layout.base]
  change (∑ d : Fin (6+16),512^d.val*(asg (if d.val<6 then 25+6*i.val+d.val else 84)).val)=_
  rw [Fin.sum_univ_add]
  have hh : ∀ d : Fin 16,¬(d.natAdd 6).val<6 := by intro d;simp
  simp only [hh,if_false,hz,ZMod.val_zero,mul_zero,Finset.sum_const_zero,add_zero,Fin.val_castAdd]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.isLt,if_true]

theorem new_public (asg : Nat → BabyBear) (hz : asg 84=0) :
    (fun i : Fin 5 => decoded profile (asg ∘ wireMap) (target (L:=4) i 0))=publicNew asg := by
  funext i
  unfold decoded publicNew
  simp_rw [Function.comp_apply,new_wire]
  simp only [profile,Layout.base]
  change (∑ d : Fin (7+15),512^d.val*(asg (if d.val<7 then 49+7*i.val+d.val else 84)).val)=_
  rw [Fin.sum_univ_add]
  have hh : ∀ d : Fin 15,¬(d.natAdd 7).val<7 := by intro d;simp
  simp only [hh,if_false,hz,ZMod.val_zero,mul_zero,Finset.sum_const_zero,add_zero,Fin.val_castAdd]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.isLt,if_true]

def PublicRowSound : Prop := ∀ asg,systemAccepts asg system →
  (∀ i,publicInput asg i<params.source i) ∧
  (∀ i,publicCopy asg i=publicInput asg i) ∧
  ∀ i,(publicNew asg i : Int)=nativeOutput (fun j => publicInput asg j) i

theorem publicRowSound : PublicRowSound := by
  intro asg hs
  obtain ⟨hz,hs⟩ := (systemAccepts_append asg _ _).mp hs
  have hz' : asg 84=0 := by simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using hz
  have ha := (systemAccepts_renameS asg wireMap source).mp hs
  obtain ⟨hin,hcopy,hout⟩ := sourceSound (asg ∘ wireMap) ha
  have hi := input_public asg hz'
  have hc := copy_public asg hz'
  have hn := new_public asg hz'
  have hin' : ∀ i,publicInput asg i<params.source i := by
    intro i;rw [← congrFun hi i];exact hin i
  refine ⟨hin',?_,?_⟩
  · intro i;rw [← congrFun hc i,← congrFun hi i];exact hcopy i
  · intro i
    have h := hout i
    have hzinput := congrArg (fun f : Fin 4 → Nat => fun j => (f j : Int)) hi
    dsimp only at hzinput
    rw [congrFun hn i,hzinput] at h
    exact h.trans (nativeAgreement _ (fun j => ⟨by positivity,by exact_mod_cast hin' j⟩) i)

theorem simplifiedSource_sound (asg : Nat → BabyBear)
    (hs : systemAccepts asg (AirSimplify.simplifySystem system)) :
    (∀ i,publicInput asg i<params.source i) ∧
    (∀ i,publicCopy asg i=publicInput asg i) ∧
    ∀ i,(publicNew asg i : Int)=nativeOutput (fun j => publicInput asg j) i :=
  publicRowSound asg ((AirSimplify.simplifySystem_accepts_iff asg system).mp hs)

/-- info: 'Minidregg.Compiler.ActualBasisExtension.input_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.input_wire

/-- info: 'Minidregg.Compiler.ActualBasisExtension.copy_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.copy_wire

/-- info: 'Minidregg.Compiler.ActualBasisExtension.new_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.new_wire

/-- info: 'Minidregg.Compiler.ActualBasisExtension.input_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.input_public

/-- info: 'Minidregg.Compiler.ActualBasisExtension.copy_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.copy_public

/-- info: 'Minidregg.Compiler.ActualBasisExtension.new_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.new_public

/-- info: 'Minidregg.Compiler.ActualBasisExtension.publicRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.publicRowSound

/-- info: 'Minidregg.Compiler.ActualBasisExtension.simplifiedSource_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.ActualBasisExtension.simplifiedSource_sound

end Minidregg.Compiler.ActualBasisExtension
