import Compiler.TfheSignedDecomposition

namespace Minidregg.Compiler.TfheCmuxDecomposition
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/- The old rotation and new decomposition systems are reused by the existing
compiler variable-renaming fold. This file adds only bounded exponent/subtraction
relations; both complete input reads are tied to exact-public tables by emission. -/
def nVars : Nat := 301
abbrev W := Fin nVars
def rot (i : TfheInitialRotation.W) : W := ⟨i.val,by have h := i.isLt; dsimp [nVars,TfheInitialRotation.nVars] at *; omega⟩
def dec (i : TfheSignedDecomposition.W) : W := ⟨111+i.val,by have h := i.isLt; dsimp [nVars,TfheSignedDecomposition.nVars] at *; omega⟩
def widths : Fin 6 → Nat := ![10,16,16,1,1,1]
def offsets : Fin 6 → Nat := ![256,266,282,298,299,300]
def value (k : Fin 6) : W := ⟨250+k.val,by dsimp [nVars]; omega⟩
def bits (k : Fin 6) (j : Fin (widths k)) : W :=
  ⟨offsets k+j.val,by
    have cap : offsets k+widths k ≤ nVars := by fin_cases k <;> decide
    have hj := j.isLt; omega⟩
def v (k : Fin 6) : Term (AirSig BabyBear W) := vr (value k)
def val (asg : W → BabyBear) (k : Fin 6) := (asg (value k)).val
def r (k : Fin 12) : Term (AirSig BabyBear W) := vr (rot (TfheInitialRotation.value k))
def d (k : Fin 22) : Term (AirSig BabyBear W) := vr (dec (TfheSignedDecomposition.value k))
def rv (asg : W → BabyBear) (k : Fin 12) := TfheInitialRotation.val (asg ∘ rot) k
def dv (asg : W → BabyBear) (k : Fin 22) := TfheSignedDecomposition.val (asg ∘ dec) k
def base (asg : W → BabyBear) := val asg 1+65536*val asg 2
def delta (asg : W → BabyBear) := dv asg 0+65536*dv asg 1
def rotated (asg : W → BabyBear) := rv asg 3+65536*rv asg 4
def ranges : ConstraintSystem BabyBear W :=
  (List.finRange 6).flatMap fun k => rangeGadget (value k) (bits k)
def sub (a b : Term (AirSig BabyBear W)) := add' a (mul' (cst (-1)) b)
def exponentTerm := sub (add' (v 0) (r 2)) (mul' (cst 1024) (v 5))
def loTerm := sub (add' (d 0) (v 1))
  (add' (r 3) (mul' (cst 65536) (v 3)))
def hiTerm := sub (add' (add' (d 1) (v 2)) (v 3))
  (add' (r 4) (mul' (cst 65536) (v 4)))
def extras := ranges ++ [exponentTerm,loTerm,hiTerm]
def system : ConstraintSystem BabyBear W :=
  renameS rot TfheInitialRotation.system ++ renameS dec TfheSignedDecomposition.system ++ extras

/-- Complete component soundness: both reused component systems remain accepted,
and the new relations force the positive monomial source/sign and native wrapped
subtraction. The accepted decomposition is governed by its universal rowSound. -/
def RowSound : Prop := ∀ asg : W → BabyBear, systemAccepts asg system →
  systemAccepts (asg ∘ rot) TfheInitialRotation.system ∧
  systemAccepts (asg ∘ dec) TfheSignedDecomposition.system ∧
  val asg 0 < 1024 ∧ rv asg 1 < 512 ∧
  rv asg 5 = (rv asg 1+1024-val asg 0)%512 ∧
  rv asg 8 = ((rv asg 1+1024-val asg 0)/512)%2 ∧
  base asg < 4294967296 ∧ delta asg < 4294967296 ∧
  delta asg = (rotated asg+4294967296-base asg)%4294967296

theorem range_bounds (asg : W → BabyBear) (h : systemAccepts asg ranges) (k : Fin 6) :
    val asg k < 2^(widths k) := by
  have hp : 2^(widths k) ≤ babyBearP := by fin_cases k <;> decide
  exact rangeGadget_val_lt hp asg (value k) (bits k)
    (fun t ht => h t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩))

theorem field_equations (asg : W → BabyBear) (h : systemAccepts asg [exponentTerm,loTerm,hiTerm]) :
    asg (value 0)+asg (rot (TfheInitialRotation.value 2)) = 1024*asg (value 5) ∧
    asg (dec (TfheSignedDecomposition.value 0))+asg (value 1) = asg (rot (TfheInitialRotation.value 3))+65536*asg (value 3) ∧
    asg (dec (TfheSignedDecomposition.value 1))+asg (value 2)+asg (value 3) = asg (rot (TfheInitialRotation.value 4))+65536*asg (value 4) := by
  simp only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,exponentTerm,loTerm,hiTerm,
    sub,v,r,d,eval_add',eval_mul',eval_vr,eval_cst] at h
  rcases h with ⟨h1,h2,h3⟩
  refine ⟨?_,?_,?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3

theorem rowSound : RowSound := by
  intro asg hs
  obtain ⟨hc,he⟩ := (systemAccepts_append asg _ extras).mp hs
  obtain ⟨hr,hd⟩ := (systemAccepts_append asg _ _).mp hc
  have hr := (systemAccepts_renameS asg rot TfheInitialRotation.system).mp hr
  have hd := (systemAccepts_renameS asg dec TfheSignedDecomposition.system).mp hd
  obtain ⟨hb,he⟩ := (systemAccepts_append asg ranges _).mp he
  have hrot := TfheInitialRotation.rowSound (asg ∘ rot) hr
  have hdec := TfheSignedDecomposition.rowSound (asg ∘ dec) hd
  obtain ⟨hrr,-⟩ := (systemAccepts_append _ TfheInitialRotation.ranges _).mp hr
  obtain ⟨hdr,-⟩ := (systemAccepts_append _ (TfheSignedDecomposition.ranges ++ TfheSignedDecomposition.zeros) _).mp hd
  obtain ⟨hdr,-⟩ := (systemAccepts_append _ TfheSignedDecomposition.ranges _).mp hdr
  have bounds := range_bounds asg hb
  have b0 := bounds 0; have b1 := bounds 1; have b2 := bounds 2
  have b3 := bounds 3; have b4 := bounds 4; have b5 := bounds 5
  change val asg 0 < 1024 at b0
  change val asg 1 < 65536 at b1
  change val asg 2 < 65536 at b2
  change val asg 3 < 2 at b3
  change val asg 4 < 2 at b4
  change val asg 5 < 2 at b5
  have r3 := TfheInitialRotation.range_bounds _ hrr 3
  have r4 := TfheInitialRotation.range_bounds _ hrr 4
  have d0 := TfheSignedDecomposition.range_bounds _ hdr 0
  have d1 := TfheSignedDecomposition.range_bounds _ hdr 1
  change rv asg 3 < 65536 at r3
  change rv asg 4 < 65536 at r4
  change dv asg 0 < 65536 at d0
  change dv asg 1 < 65536 at d1
  have r1 : rv asg 1 < 512 := hrot.2.1
  have r2 : rv asg 2 < 1024 := hrot.2.2.1
  have rs : rv asg 5 = (rv asg 1+rv asg 2)%512 := hrot.2.2.2.1
  have rp : rv asg 8 = ((rv asg 1+rv asg 2)/512)%2 := hrot.2.2.2.2.1
  obtain ⟨f0,f1,f2⟩ := field_equations asg he
  have e0 : val asg 0+rv asg 2 = 1024*val asg 5 := by
    apply TfheInitialRotation.small_eq (by norm_num [babyBearP]; omega) (by norm_num [babyBearP]; omega)
    simpa [val,rv,TfheInitialRotation.val,Function.comp_def] using f0
  have e1 : dv asg 0+val asg 1 = rv asg 3+65536*val asg 3 := by
    apply TfheInitialRotation.small_eq (by norm_num [babyBearP]; omega) (by norm_num [babyBearP]; omega)
    simpa [val,rv,dv,TfheInitialRotation.val,TfheSignedDecomposition.val,Function.comp_def] using f1
  have e2 : dv asg 1+val asg 2+val asg 3 = rv asg 4+65536*val asg 4 := by
    apply TfheInitialRotation.small_eq (by norm_num [babyBearP]; omega) (by norm_num [babyBearP]; omega)
    simpa [val,rv,dv,TfheInitialRotation.val,TfheSignedDecomposition.val,Function.comp_def] using f2
  refine ⟨hr,hd,b0,r1,?_,?_,by dsimp [base]; omega,by dsimp [delta]; omega,?_⟩
  · omega
  · omega
  · dsimp [delta,rotated,base]; omega

/-- Full source map is a permutation, so every coefficient of each input polynomial
is bound by the exact-public source table once, in addition to its base read. -/
theorem source_injective (a j k : Nat) (ha : a < 1024) (hj : j < 512) (hk : k < 512)
    (h : (j+1024-a)%512 = (k+1024-a)%512) : j = k := by omega

def variableArray (row : Array Nat) (inputs : Array (Array Nat)) : Array BabyBear := Id.run do
  let a := row[3]!
  let negA := (1024-a)%1024
  let source := (row[2]!+negA)%512
  let inp := inputs[512*row[1]!+source]!
  let x := inp[2]!+65536*inp[3]!
  let y := if (row[2]!+negA)/512%2 == 0 then x else (4294967296-x)%4294967296
  let rr := #[row[0]!,row[1]!,row[2]!,negA,y%65536,y/65536]
  let ra := TfheInitialRotation.variableArray rr inputs
  let da := TfheSignedDecomposition.variableArray (row[4]!+65536*row[5]!) row[6]! row[7]! row[8]! row[9]!
  let orig := inputs[512*row[1]!+row[2]!]!
  let cl := (row[4]!+orig[2]!)/65536
  let ch := (row[5]!+orig[3]!+cl)/65536
  let vals := #[a,orig[2]!,orig[3]!,cl,ch,(a+negA)/1024]
  let mut out := Array.replicate nVars (0 : BabyBear)
  for i in [:111] do out := out.set! i ra[i]!
  for i in [:139] do out := out.set! (111+i) da[i]!
  for k in [:6] do out := out.set! (250+k) (vals[k]! : BabyBear)
  for k in List.finRange 6 do out := TfheModulusSwitch.setBits out (offsets k) (widths k) vals[k.val]!
  return out

def asgOf (a : Array BabyBear) : W → BabyBear := fun i => a[i.val]!
def sourceCheck (a : Array BabyBear) : Bool := system.all (fun t => eval (asgOf a) t == 0)
def zeroArray := variableArray #[0,0,0,0,0,0,0,0,512,512] #[#[0,0,0,0]]
theorem zero_witness : systemAccepts (asgOf zeroArray) system := by decide +kernel

theorem changed_zero_refused (asg : W → BabyBear) (hx : delta asg = 0)
    (hd : dv asg 4 = 513) : ¬ systemAccepts asg system := by
  intro h
  exact TfheSignedDecomposition.changed_zero_refused (asg ∘ dec) hx hd (rowSound asg h).2.1

/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.range_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms range_bounds
/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.field_equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms field_equations
/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSound
/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.source_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_injective
/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.zero_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_witness
/-- info: 'Minidregg.Compiler.TfheCmuxDecomposition.changed_zero_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms changed_zero_refused
end Minidregg.Compiler.TfheCmuxDecomposition
