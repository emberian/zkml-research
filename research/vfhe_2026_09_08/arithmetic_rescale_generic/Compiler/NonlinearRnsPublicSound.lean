import Compiler.NonlinearRnsPublic
import Compiler.NonlinearRnsSound
import Compiler.NonlinearRnsNative

namespace Minidregg.Compiler.NonlinearRnsPublic
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DirectedRnsScaler Minidregg.Compiler.SignedMatrix
open Minidregg.Compiler.NonlinearRnsInstance Minidregg.Compiler.AirSimplify
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 200000

def publicResidues (asg : Nat → BabyBear) (i : Fin 9) : Int := (∑ d : Fin 7,512^d.val*(asg (1+7*i.val+d.val)).val : Nat)
def publicOutput (asg : Nat → BabyBear) (i : Fin 4) : Nat := ∑ d : Fin 6,512^d.val*(asg (64+6*i.val+d.val)).val

def PublicRowSound : Prop := ∀ asg,systemAccepts asg system → ∀ i,
  (publicOutput asg i : Int)=wordOutput (publicResidues asg)%(params.targetBase i : Int)

theorem input_wire (i : Fin 9) (d : Fin 23) :
    wireMap (scalarWire profile (groupDigit profile (residue (K:=4) i,d)))=
      if d.val<7 then 1+7*i.val+d.val else 88 := by
  change wireMap (d.val+23*i.val)=_
  have hi := i.isLt
  have hd := d.isLt
  have hdiv : (d.val+23*i.val)/23=i.val := by omega
  have hmod : (d.val+23*i.val)%23=d.val := by omega
  simp only [wireMap,profile,Layout.scalars,hdiv,hmod,show d.val+23*i.val<39*23 by omega,if_true,hi]

theorem output_wire (i : Fin 4) (d : Fin 23) :
    wireMap (scalarWire profile (groupDigit profile (target (L:=9) i 0,d)))=
      if d.val<6 then 64+6*i.val+d.val else 88 := by
  change wireMap (d.val+23*(27+3*i.val+0))=_
  rw [Nat.add_zero]
  have hi := i.isLt
  have hd := d.isLt
  have hdiv : (d.val+23*(27+3*i.val))/23=27+3*i.val := by omega
  have hmod : (d.val+23*(27+3*i.val))%23=d.val := by omega
  simp only [wireMap,profile,Layout.scalars,hdiv,hmod,
    show d.val+23*(27+3*i.val)<39*23 by omega,if_true,
    show ¬27+3*i.val<9 by omega,if_false,show 27≤27+3*i.val by omega,
    show 27+3*i.val<39 by omega,show (27+3*i.val-27)%3=0 by omega,
    and_self,show (27+3*i.val-27)/3=i.val by omega]

theorem input_public (asg : Nat → BabyBear) (hz : asg 88=0) :
    (fun i : Fin 9 => (decoded profile (asg ∘ wireMap) (residue (K:=4) i) : Int))=publicResidues asg := by
  funext i
  unfold decoded publicResidues
  simp_rw [Function.comp_apply,input_wire]
  simp only [profile,Layout.base]
  apply congrArg (fun n : Nat => (n : Int))
  change (∑ d : Fin (7+16),512^d.val*(asg (if d.val<7 then 1+7*i.val+d.val else 88)).val)=_
  rw [Fin.sum_univ_add]
  have hh : ∀ d : Fin 16,¬(d.natAdd 7).val<7 := by intro d; simp
  simp only [hh,if_false,hz,ZMod.val_zero,mul_zero,Finset.sum_const_zero,add_zero,Fin.val_castAdd]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.isLt,if_true]

theorem output_public (asg : Nat → BabyBear) (hz : asg 88=0) :
    (fun i : Fin 4 => decoded profile (asg ∘ wireMap) (target (L:=9) i 0))=publicOutput asg := by
  funext i
  unfold decoded publicOutput
  simp_rw [Function.comp_apply,output_wire]
  simp only [profile,Layout.base]
  change (∑ d : Fin (6+17),512^d.val*(asg (if d.val<6 then 64+6*i.val+d.val else 88)).val)=_
  rw [Fin.sum_univ_add]
  have hh : ∀ d : Fin 17,¬(d.natAdd 6).val<6 := by intro d; simp
  simp only [hh,if_false,hz,ZMod.val_zero,mul_zero,Finset.sum_const_zero,add_zero,Fin.val_castAdd]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.isLt,if_true]

theorem publicRowSound : PublicRowSound := by
  intro asg hs i
  obtain ⟨hz,hs⟩ := (systemAccepts_append asg _ _).mp hs
  have hz' : asg 88=0 := by simpa [systemAccepts_cons,systemAccepts_nil,accepts,eval_vr] using hz
  have ha := (systemAccepts_renameS asg wireMap source).mp hs
  have hb := source_balanced (asg ∘ wireMap) ha
  have hc := balanced_accepts params paramsValid _ hb
  have hw := nativeWordRefinement _ hc.1
  have hout := NonlinearRnsInstance.sourceSound (asg ∘ wireMap) ha i
  rw [← hw] at hout
  rw [input_public asg hz',congrFun (output_public asg hz') i] at hout
  exact hout

theorem nativeProjectedRow_sound (asg : Nat → BabyBear) (h : systemAccepts asg system) :
    ∀ i,(publicOutput asg i : Int)=nativeProjectedOutput (publicResidues asg) i := by
  intro i
  rw [publicRowSound asg h i,canonical_lift_preserves_native]

theorem simplifiedSource_sound (asg : Nat → BabyBear) (h : systemAccepts asg (simplifySystem system)) :
    ∀ i,(publicOutput asg i : Int)=wordOutput (publicResidues asg)%(params.targetBase i : Int) :=
  publicRowSound asg ((simplifySystem_accepts_iff asg system).mp h)

end Minidregg.Compiler.NonlinearRnsPublic

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.input_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.input_wire

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.output_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.output_wire

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.input_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.input_public

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.output_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.output_public

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.publicRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.publicRowSound

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.nativeProjectedRow_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.nativeProjectedRow_sound

/-- info: 'Minidregg.Compiler.NonlinearRnsPublic.simplifiedSource_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.NonlinearRnsPublic.simplifiedSource_sound
