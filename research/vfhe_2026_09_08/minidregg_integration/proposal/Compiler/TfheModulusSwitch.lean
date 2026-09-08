import Compiler.BfvLinearCombinationLayout

namespace Minidregg.Compiler.TfheModulusSwitch
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/- Exact native-u32 PBS entry for TFHE's N=512 preset.
Public columns: row ID, input low16, input high16, rotation exponent.
The remaining columns are range/decomposition witnesses, not supplied results. -/
def nVars : Nat := 55
abbrev W := Fin nVars
def lo : W := ⟨1,by decide⟩
def hi : W := ⟨2,by decide⟩
def out : W := ⟨3,by decide⟩
def rem : W := ⟨4,by decide⟩
def wrap : W := ⟨5,by decide⟩
def loBit (i : Fin 16) : W := ⟨6+i.val,by dsimp [nVars]; omega⟩
def hiBit (i : Fin 16) : W := ⟨22+i.val,by dsimp [nVars]; omega⟩
def outBit (i : Fin 10) : W := ⟨38+i.val,by dsimp [nVars]; omega⟩
def remBit (i : Fin 6) : W := ⟨48+i.val,by dsimp [nVars]; omega⟩
def wrapBit (_ : Fin 1) : W := ⟨54,by decide⟩

def balance : Term (AirSig BabyBear W) :=
  add' (add' (vr hi) (cst 32))
    (mul' (cst (-1)) (add' (add' (mul' (cst 64) (vr out)) (vr rem))
      (mul' (cst 65536) (vr wrap))))

def system : ConstraintSystem BabyBear W :=
  rangeGadget lo loBit ++ rangeGadget hi hiBit ++ rangeGadget out outBit ++
  rangeGadget rem remBit ++ rangeGadget wrap wrapBit ++ [balance]

def input (asg : W → BabyBear) : Nat := (asg lo).val+65536*(asg hi).val

/-- Statement first: acceptance fixes every full u32 input's native rounded,
wrapped exponent in Z/(2N), rather than only a prime-field congruence. -/
def RowSound : Prop := ∀ asg : W → BabyBear, systemAccepts asg system →
  input asg < 4294967296 ∧ (asg out).val < 1024 ∧
  (asg out).val = ((input asg+2097152)/4194304)%1024

theorem balance_correct (asg : W → BabyBear) : accepts asg balance ↔
    asg hi+32 = 64*asg out+asg rem+65536*asg wrap := by
  simp only [accepts,balance,eval_add',eval_mul',eval_vr,eval_cst]
  constructor <;> intro h <;> linear_combination h

theorem rowSound : RowSound := by
  intro asg hs
  simp only [system,systemAccepts_append,systemAccepts_cons,systemAccepts_nil,and_true] at hs
  obtain ⟨⟨⟨⟨⟨hl,hh⟩,ho⟩,hr⟩,hw⟩,he⟩ := hs
  have hlv : (asg lo).val < 65536 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^16 ≤ babyBearP) asg lo loBit hl
  have hhv : (asg hi).val < 65536 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^16 ≤ babyBearP) asg hi hiBit hh
  have hov : (asg out).val < 1024 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^10 ≤ babyBearP) asg out outBit ho
  have hrv : (asg rem).val < 64 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^6 ≤ babyBearP) asg rem remBit hr
  have hwv : (asg wrap).val < 2 := rangeGadget_val_lt
    (by norm_num [babyBearP] : 2^1 ≤ babyBearP) asg wrap wrapBit hw
  have hf := (balance_correct asg).mp he
  have hleft : (asg hi).val+32 < babyBearP := by norm_num [babyBearP]; omega
  have hright : 64*(asg out).val+(asg rem).val+65536*(asg wrap).val < babyBearP := by
    norm_num [babyBearP]; omega
  have hc : (((asg hi).val+32 : Nat) : BabyBear) =
      ((64*(asg out).val+(asg rem).val+65536*(asg wrap).val : Nat) : BabyBear) := by
    simpa using hf
  have heq := congrArg ZMod.val hc
  simp only [ZMod.val_cast_of_lt hleft,ZMod.val_cast_of_lt hright] at heq
  dsimp [input]
  refine ⟨by omega,hov,?_⟩
  omega

theorem simplifiedSource_sound (asg : W → BabyBear)
    (h : systemAccepts asg (simplifySystem system)) :
    input asg < 4294967296 ∧ (asg out).val < 1024 ∧
    (asg out).val = ((input asg+2097152)/4194304)%1024 :=
  rowSound asg ((simplifySystem_accepts_iff asg system).mp h)

def setBits (a : Array BabyBear) (offset count value : Nat) : Array BabyBear := Id.run do
  let mut a := a
  for j in [:count] do a := a.set! (offset+j) ((value/2^j%2 : Nat) : BabyBear)
  return a

def variableArray (row : Array Nat) : Array BabyBear := Id.run do
  let mut a := Array.replicate nVars (0 : BabyBear)
  for i in [:4] do a := a.set! i (row[i]! : BabyBear)
  let h := row[2]!
  let r := (h+32)%64
  let w := (h+32)/65536
  a := a.set! 4 (r : BabyBear)
  a := a.set! 5 (w : BabyBear)
  a := setBits a 6 16 row[1]!
  a := setBits a 22 16 h
  a := setBits a 38 10 row[3]!
  a := setBits a 48 6 r
  a := setBits a 54 1 w
  return a

def zeroAsg : W → BabyBear := fun i => (variableArray #[0,0,0,0])[i.val]!

/-- A kernel-computed satisfying assignment inhabits the actual relation. -/
theorem zero_witness : systemAccepts zeroAsg system := by decide +kernel

/-- No auxiliary assignment can turn zero into exponent one. -/
theorem changed_zero_refused (asg : W → BabyBear) (hl : asg lo = 0)
    (hh : asg hi = 0) (ho : asg out = 1) : ¬ systemAccepts asg system := by
  intro hs
  have h := (rowSound asg hs).2.2
  simp [input,hl,hh,ho] at h

def sourceCheck (row : Array Nat) : Bool :=
  let a := variableArray row
  system.all (fun t => eval (fun i => a[i.val]!) t == 0)

/- Each final theorem report is an exact build assertion. -/
/-- info: 'Minidregg.Compiler.TfheModulusSwitch.balance_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms balance_correct
/-- info: 'Minidregg.Compiler.TfheModulusSwitch.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSound
/-- info: 'Minidregg.Compiler.TfheModulusSwitch.simplifiedSource_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplifiedSource_sound
/-- info: 'Minidregg.Compiler.TfheModulusSwitch.zero_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_witness
/-- info: 'Minidregg.Compiler.TfheModulusSwitch.changed_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms changed_zero_refused
end Minidregg.Compiler.TfheModulusSwitch
