import Compiler.TfheModulusSwitch

namespace Minidregg.Compiler.TfheInitialRotation
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/- Public output row: id, component, destination, exponent, outLo, outHi.
The input exact-public table binds (component, source, inLo, inHi).
All arithmetic and witness construction live in this compiler source. -/
def nVars : Nat := 111
abbrev W := Fin nVars
def widths : Fin 12 → Nat := ![2,9,10,16,16,9,16,16,1,1,1,1]
def offsets : Fin 12 → Nat := ![13,15,24,34,50,66,75,91,107,108,109,110]
def value (k : Fin 12) : W := ⟨k.val+1,by dsimp [nVars]; omega⟩
def bits (k : Fin 12) (j : Fin (widths k)) : W :=
  ⟨offsets k+j.val,by
    have cap : offsets k+widths k ≤ nVars := by fin_cases k <;> decide
    have hj := j.isLt
    omega⟩
def v (k : Fin 12) : Term (AirSig BabyBear W) := vr (value k)
def val (asg : W → BabyBear) (k : Fin 12) : Nat := (asg (value k)).val
def wordIn (asg : W → BabyBear) : Nat := val asg 6+65536*val asg 7
def wordOut (asg : W → BabyBear) : Nat := val asg 3+65536*val asg 4
def ranges : ConstraintSystem BabyBear W :=
  (List.finRange 12).flatMap fun k => rangeGadget (value k) (bits k)
def sub (a b : Term (AirSig BabyBear W)) := add' a (mul' (cst (-1)) b)
def indexTerm := sub (add' (v 1) (v 2))
  (add' (add' (v 5) (mul' (cst 512) (v 8))) (mul' (cst 1024) (v 9)))
def loTerm := sub (add' (v 3) (mul' (mul' (cst 2) (v 8)) (v 6)))
  (add' (v 6) (mul' (cst 65536) (v 10)))
def hiTerm := sub (add' (add' (v 4) (mul' (mul' (cst 2) (v 8)) (v 7))) (v 10))
  (add' (v 7) (mul' (cst 65536) (v 11)))
def system : ConstraintSystem BabyBear W := ranges ++ [indexTerm,loTerm,hiTerm]

/-- Complete row law, with the source index and negacyclic sign forced rather
than supplied as unchecked permutation witnesses. -/
def RowSound : Prop := ∀ asg : W → BabyBear, systemAccepts asg system →
  val asg 0 < 4 ∧ val asg 1 < 512 ∧ val asg 2 < 1024 ∧
  val asg 5 = (val asg 1+val asg 2)%512 ∧
  val asg 8 = ((val asg 1+val asg 2)/512)%2 ∧
  wordIn asg < 4294967296 ∧ wordOut asg < 4294967296 ∧
  wordOut asg = if ((val asg 1+val asg 2)/512)%2 = 0 then wordIn asg
    else (4294967296-wordIn asg)%4294967296

theorem small_eq {a b : Nat} (ha : a < babyBearP) (hb : b < babyBearP)
    (h : (a : BabyBear) = (b : BabyBear)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_cast_of_lt ha,ZMod.val_cast_of_lt hb] using hv

theorem range_bounds (asg : W → BabyBear) (h : systemAccepts asg ranges) (k : Fin 12) :
    val asg k < 2^(widths k) := by
  have hp : 2^(widths k) ≤ babyBearP := by fin_cases k <;> decide
  exact rangeGadget_val_lt hp asg (value k) (bits k)
    (fun t ht => h t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩))

theorem equations (asg : W → BabyBear) (h : systemAccepts asg [indexTerm,loTerm,hiTerm]) :
    asg (value 1)+asg (value 2) = asg (value 5)+512*asg (value 8)+1024*asg (value 9) ∧
    asg (value 3)+2*asg (value 8)*asg (value 6) = asg (value 6)+65536*asg (value 10) ∧
    asg (value 4)+2*asg (value 8)*asg (value 7)+asg (value 10) = asg (value 7)+65536*asg (value 11) := by
  simp only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,indexTerm,loTerm,hiTerm,
    sub,v,eval_add',eval_mul',eval_vr,eval_cst] at h
  rcases h with ⟨h1,h2,h3⟩
  refine ⟨?_,?_,?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3

theorem rowSound : RowSound := by
  intro asg hs
  obtain ⟨hr,he⟩ := (systemAccepts_append asg ranges _).mp hs
  have hb := range_bounds asg hr
  have h0 := hb 0; have hj := hb 1; have he := equations asg he
  have ha := hb 2; have hzl := hb 3; have hzh := hb 4
  have hi := hb 5; have hxl := hb 6; have hxh := hb 7
  have hs := hb 8; have ht := hb 9; have hc := hb 10; have hd := hb 11
  change val asg 0 < 4 at h0
  change val asg 1 < 512 at hj
  change val asg 2 < 1024 at ha
  change val asg 3 < 65536 at hzl
  change val asg 4 < 65536 at hzh
  change val asg 5 < 512 at hi
  change val asg 6 < 65536 at hxl
  change val asg 7 < 65536 at hxh
  change val asg 8 < 2 at hs
  change val asg 9 < 2 at ht
  change val asg 10 < 2 at hc
  change val asg 11 < 2 at hd
  have hp1 := Nat.mul_le_mul (show val asg 8 ≤ 1 by omega) (show val asg 6 ≤ 65535 by omega)
  have hp2 := Nat.mul_le_mul (show val asg 8 ≤ 1 by omega) (show val asg 7 ≤ 65535 by omega)
  have hindex : val asg 1+val asg 2 = val asg 5+512*val asg 8+1024*val asg 9 := by
    apply small_eq (by norm_num [babyBearP]; omega) (by norm_num [babyBearP]; omega)
    simpa [val] using he.1
  have hlo : val asg 3+2*val asg 8*val asg 6 = val asg 6+65536*val asg 10 := by
    apply small_eq (by norm_num [babyBearP]; nlinarith) (by norm_num [babyBearP]; omega)
    simpa [val] using he.2.1
  have hhi : val asg 4+2*val asg 8*val asg 7+val asg 10 = val asg 7+65536*val asg 11 := by
    apply small_eq (by norm_num [babyBearP]; nlinarith) (by norm_num [babyBearP]; omega)
    simpa [val] using he.2.2
  have hsource : val asg 5 = (val asg 1+val asg 2)%512 := by omega
  have hsign : val asg 8 = ((val asg 1+val asg 2)/512)%2 := by omega
  refine ⟨h0,hj,ha,hsource,hsign,by dsimp [wordIn]; omega,by dsimp [wordOut]; omega,?_⟩
  rw [← hsign]
  have cases : val asg 8 = 0 ∨ val asg 8 = 1 := by omega
  rcases cases with hzero | hone
  · rw [hzero] at hlo hhi ⊢
    simp only [mul_zero,zero_mul,add_zero,ite_true] at hlo hhi ⊢
    dsimp [wordOut,wordIn]; omega
  · rw [hone] at hlo hhi ⊢
    simp only [mul_one,one_ne_zero,ite_false] at hlo hhi ⊢
    have total : wordIn asg+wordOut asg = 4294967296*val asg 11 := by
      dsimp [wordIn,wordOut]; nlinarith
    dsimp [wordIn,wordOut] at total ⊢
    omega

theorem simplifiedSource_sound (asg : W → BabyBear)
    (h : systemAccepts asg (simplifySystem system)) :
    val asg 5 = (val asg 1+val asg 2)%512 ∧
    wordOut asg = if ((val asg 1+val asg 2)/512)%2 = 0 then wordIn asg
      else (4294967296-wordIn asg)%4294967296 := by
  have h := rowSound asg ((simplifySystem_accepts_iff asg system).mp h)
  exact ⟨h.2.2.2.1,h.2.2.2.2.2.2.2⟩

/-- The actual library splits at N-(b mod N) and toggles the sign for odd full
cycles. This is the same sign as the generated destination-plus-exponent law. -/
theorem library_sign (j b : Nat) (hj : j < 512) :
    ((j+b)/512)%2 = (b/512+(if j < 512-b%512 then 0 else 1))%2 := by
  split_ifs <;> omega

/-- The generated source map is a permutation on all N coefficient positions. -/
theorem source_injective (b j k : Nat) (hj : j < 512) (hk : k < 512)
    (h : (j+b)%512 = (k+b)%512) : j = k := by omega

theorem source_surjective (b k : Nat) (hk : k < 512) :
    ∃ j : Nat, j < 512 ∧ (j+b)%512 = k := by
  refine ⟨(k+512-b%512)%512,Nat.mod_lt _ (by omega),?_⟩
  omega

def variableArray (row : Array Nat) (inputRows : Array (Array Nat)) : Array BabyBear := Id.run do
  let mut a := Array.replicate nVars (0 : BabyBear)
  for i in [:6] do a := a.set! i (row[i]! : BabyBear)
  let sum := row[2]!+row[3]!
  let source := sum%512
  let sourceRow := inputRows[512*row[1]!+source]!
  let xl := sourceRow[2]!
  let xh := sourceRow[3]!
  let sign := sum/512%2
  let cl := if sign == 0 then 0 else (xl+row[4]!)/65536
  let ch := if sign == 0 then 0 else (xh+row[5]!+cl)/65536
  for (i,x) in [(6,source),(7,xl),(8,xh),(9,sign),(10,sum/1024),(11,cl),(12,ch)] do
    a := a.set! i (x : BabyBear)
  for k in List.finRange 12 do
    a := TfheModulusSwitch.setBits a (offsets k) (widths k) a[k.val+1]!.val
  return a

def zeroAsg : W → BabyBear := fun _ => 0
theorem zero_witness : systemAccepts zeroAsg system := by decide +kernel
def negOneAsg : W → BabyBear := fun i =>
  (variableArray #[0,0,0,512,65535,65535] #[#[0,0,1,0]])[i.val]!
theorem negated_one_witness : systemAccepts negOneAsg system := by decide +kernel

theorem changed_zero_refused (asg : W → BabyBear) (hx : wordIn asg = 0)
    (hz : wordOut asg = 1) : ¬ systemAccepts asg system := by
  intro h
  have h := (rowSound asg h).2.2.2.2.2.2.2
  rw [hx,hz] at h
  by_cases hp : ((val asg 1+val asg 2)/512)%2 = 0
  · simp [hp] at h
  · simp [hp] at h
def sourceCheck (a : Array BabyBear) : Bool := system.all (fun t => eval (fun i => a[i.val]!) t == 0)

/-- info: 'Minidregg.Compiler.TfheInitialRotation.small_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms small_eq
/-- info: 'Minidregg.Compiler.TfheInitialRotation.range_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms range_bounds
/-- info: 'Minidregg.Compiler.TfheInitialRotation.equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equations
/-- info: 'Minidregg.Compiler.TfheInitialRotation.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSound
/-- info: 'Minidregg.Compiler.TfheInitialRotation.simplifiedSource_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms simplifiedSource_sound
/-- info: 'Minidregg.Compiler.TfheInitialRotation.library_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms library_sign
/-- info: 'Minidregg.Compiler.TfheInitialRotation.source_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_injective
/-- info: 'Minidregg.Compiler.TfheInitialRotation.source_surjective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_surjective
/-- info: 'Minidregg.Compiler.TfheInitialRotation.zero_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_witness
/-- info: 'Minidregg.Compiler.TfheInitialRotation.negated_one_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negated_one_witness
/-- info: 'Minidregg.Compiler.TfheInitialRotation.changed_zero_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms changed_zero_refused
end Minidregg.Compiler.TfheInitialRotation
