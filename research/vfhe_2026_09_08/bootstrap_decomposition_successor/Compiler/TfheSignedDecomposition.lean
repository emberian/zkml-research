import Compiler.TfheInitialRotation
import Compiler.PredCompile

namespace Minidregg.Compiler.TfheSignedDecomposition
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.AirSimplify
open Minidregg.Theory
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def nVars : Nat := 139
abbrev W := Fin nVars
def widths (k : Fin 20) : Nat := #[16,16,10,10,11,11,11,1,4,1,9,1,9,1,1,1,1,1,1,1][k.val]!
def offsets (k : Fin 20) : Nat := #[22,38,54,64,74,85,96,107,108,112,113,122,123,132,133,134,135,136,137,138][k.val]!
def value (k : Fin 22) : W := ⟨k.val,by dsimp [nVars]; omega⟩
def bits (k : Fin 20) (j : Fin (widths k)) : W :=
  ⟨offsets k+j.val,by
    have cap : offsets k+widths k ≤ nVars := by fin_cases k <;> decide
    have hj := j.isLt; omega⟩
def v (k : Fin 22) : Term (AirSig BabyBear W) := vr (value k)
def val (asg : W → BabyBear) (k : Fin 22) : Nat := (asg (value k)).val
def word (asg : W → BabyBear) := val asg 0+65536*val asg 1
def rounded (x : Nat) := ((x+2048)/4096)%1048576
def initCarry (r rb : Nat) : Nat := if r > 524288 ∨ (r = 524288 ∧ rb = 1) then 1 else 0
def digitCarry (l h : Nat) : Nat := if l > 512 ∨ (l = 512 ∧ h ≥ 512) then 1 else 0
def ranges : ConstraintSystem BabyBear W :=
  (List.finRange 20).flatMap fun k => rangeGadget (value ⟨k.val,by omega⟩) (bits k)
def sub (a b : Term (AirSig BabyBear W)) := add' a (mul' (cst (-1)) b)
def zeros : ConstraintSystem BabyBear W :=
  Minidregg.Compiler.isZero (add' (v 2) (mul' (cst 1024) (v 10))) (value 14) (value 20) ++
  Minidregg.Compiler.isZero (v 12) (value 15) (value 21)
def eq0 := sub (v 0) (add' (add' (v 6) (mul' (cst 2048) (v 7))) (mul' (cst 4096) (v 8)))
def eq1 := sub (add' (add' (mul' (cst 16) (v 1)) (v 8)) (v 7)) (add' (add' (v 2) (mul' (cst 1024) (v 3))) (mul' (cst 1048576) (v 9)))
def eq2 := sub (v 3) (add' (v 10) (mul' (cst 512) (v 11)))
def eq3 := sub (v 2) (add' (v 12) (mul' (cst 512) (v 13)))
def eq4 := sub (add' (v 16) (mul' (v 14) (v 7))) (v 14)
def eq5 := sub (add' (v 17) (mul' (v 11) (v 16))) (v 11)
def eq6 := sub (add' (v 18) (mul' (v 15) (v 11))) (v 15)
def eq7 := sub (add' (v 19) (mul' (v 13) (v 18))) (v 13)
def eq8 := sub (add' (v 4) (mul' (cst 1024) (v 19))) (add' (v 2) (cst 512))
def eq9 := sub (add' (v 5) (mul' (cst 1024) (v 17))) (add' (add' (v 3) (v 19)) (cst 512))
def equations := [eq0,eq1,eq2,eq3,eq4,eq5,eq6,eq7,eq8,eq9]
def system : ConstraintSystem BabyBear W := ranges ++ zeros ++ equations

/-- All auxiliary assignments are quantified: exact native rounded word and the two
balanced digit offsets are forced, including both deployed midpoint conventions. -/
def RowSound : Prop := ∀ asg : W → BabyBear, systemAccepts asg system →
  word asg < 4294967296 ∧ val asg 2+1024*val asg 3 = rounded (word asg) ∧
  val asg 7 = (word asg/2048)%2 ∧
  val asg 17 = initCarry (rounded (word asg)) ((word asg/2048)%2) ∧
  val asg 19 = digitCarry (val asg 2) (val asg 3) ∧
  val asg 4+1024*val asg 19 = val asg 2+512 ∧
  val asg 5+1024*val asg 17 = val asg 3+val asg 19+512

theorem range_bounds (asg : W → BabyBear) (h : systemAccepts asg ranges) (k : Fin 20) :
    val asg ⟨k.val,by omega⟩ < 2^(widths k) := by
  have hp : 2^(widths k) ≤ babyBearP := by fin_cases k <;> decide
  exact rangeGadget_val_lt hp asg _ (bits k)
    (fun t ht => h t (List.mem_flatMap.mpr ⟨k,List.mem_finRange k,ht⟩))

theorem field_equations (asg : W → BabyBear) (h : systemAccepts asg equations) :
    asg (value 0) = ((asg (value 6)+(2048*asg (value 7)))+(4096*asg (value 8))) ∧
    (((16*asg (value 1))+asg (value 8))+asg (value 7)) = ((asg (value 2)+(1024*asg (value 3)))+(1048576*asg (value 9))) ∧
    asg (value 3) = (asg (value 10)+(512*asg (value 11))) ∧
    asg (value 2) = (asg (value 12)+(512*asg (value 13))) ∧
    (asg (value 16)+(asg (value 14)*asg (value 7))) = asg (value 14) ∧
    (asg (value 17)+(asg (value 11)*asg (value 16))) = asg (value 11) ∧
    (asg (value 18)+(asg (value 15)*asg (value 11))) = asg (value 15) ∧
    (asg (value 19)+(asg (value 13)*asg (value 18))) = asg (value 13) ∧
    (asg (value 4)+(1024*asg (value 19))) = (asg (value 2)+512) ∧
    (asg (value 5)+(1024*asg (value 17))) = ((asg (value 3)+asg (value 19))+512) := by
  simp only [equations,systemAccepts_cons,systemAccepts_nil,and_true,accepts,
    eq0,eq1,eq2,eq3,eq4,eq5,eq6,eq7,eq8,eq9,sub,v,eval_add',eval_mul',eval_vr,eval_cst] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4
  · linear_combination h5
  · linear_combination h6
  · linear_combination h7
  · linear_combination h8
  · linear_combination h9

theorem zero_nat (asg : W → BabyBear) (d : Term (AirSig BabyBear W))
    (b w : W) (n : Nat) (hn : n < babyBearP) (hd : eval asg d = (n : BabyBear))
    (h : systemAccepts asg (Minidregg.Compiler.isZero d b w)) :
    (asg b).val = if n = 0 then 1 else 0 := by
  have hh := Minidregg.Compiler.isZero_forced h
  have hz : (n : BabyBear) = 0 ↔ n = 0 := by
    constructor
    · intro h; exact TfheInitialRotation.small_eq hn (by decide) h
    · intro h; simp [h]
  rw [hd] at hh
  by_cases he : n = 0
  · simp [he] at hh ⊢; rw [hh]; decide
  · simp [hz,he] at hh ⊢; rw [hh]

theorem rowSound : RowSound := by
  intro asg hs
  obtain ⟨hrz,he⟩ := (systemAccepts_append asg (ranges ++ zeros) equations).mp hs
  obtain ⟨hr,hz⟩ := (systemAccepts_append asg ranges zeros).mp hrz
  obtain ⟨hz0,hz1⟩ := (systemAccepts_append asg _ _).mp hz
  have hb := range_bounds asg hr
  have b0 := hb 0
  change val asg 0 < 65536 at b0
  have b1 := hb 1
  change val asg 1 < 65536 at b1
  have b2 := hb 2
  change val asg 2 < 1024 at b2
  have b3 := hb 3
  change val asg 3 < 1024 at b3
  have b4 := hb 4
  change val asg 4 < 2048 at b4
  have b5 := hb 5
  change val asg 5 < 2048 at b5
  have b6 := hb 6
  change val asg 6 < 2048 at b6
  have b7 := hb 7
  change val asg 7 < 2 at b7
  have b8 := hb 8
  change val asg 8 < 16 at b8
  have b9 := hb 9
  change val asg 9 < 2 at b9
  have b10 := hb 10
  change val asg 10 < 512 at b10
  have b11 := hb 11
  change val asg 11 < 2 at b11
  have b12 := hb 12
  change val asg 12 < 512 at b12
  have b13 := hb 13
  change val asg 13 < 2 at b13
  have b14 := hb 14
  change val asg 14 < 2 at b14
  have b15 := hb 15
  change val asg 15 < 2 at b15
  have b16 := hb 16
  change val asg 16 < 2 at b16
  have b17 := hb 17
  change val asg 17 < 2 at b17
  have b18 := hb 18
  change val asg 18 < 2 at b18
  have b19 := hb 19
  change val asg 19 < 2 at b19
  rcases field_equations asg he with ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,f9⟩
  have e0 : val asg 0 = ((val asg 6+(2048*val asg 7))+(4096*val asg 8)) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f0
  have e1 : (((16*val asg 1)+val asg 8)+val asg 7) = ((val asg 2+(1024*val asg 3))+(1048576*val asg 9)) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f1
  have e2 : val asg 3 = (val asg 10+(512*val asg 11)) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f2
  have e3 : val asg 2 = (val asg 12+(512*val asg 13)) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f3
  have e4 : (val asg 16+(val asg 14*val asg 7)) = val asg 14 := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 14 ≤ 1 by omega) (show val asg 7 ≤ 1 by omega)
      omega
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 14 ≤ 1 by omega) (show val asg 7 ≤ 1 by omega)
      omega
    · simpa [val] using f4
  have e5 : (val asg 17+(val asg 11*val asg 16)) = val asg 11 := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 11 ≤ 1 by omega) (show val asg 16 ≤ 1 by omega)
      omega
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 11 ≤ 1 by omega) (show val asg 16 ≤ 1 by omega)
      omega
    · simpa [val] using f5
  have e6 : (val asg 18+(val asg 15*val asg 11)) = val asg 15 := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 15 ≤ 1 by omega) (show val asg 11 ≤ 1 by omega)
      omega
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 15 ≤ 1 by omega) (show val asg 11 ≤ 1 by omega)
      omega
    · simpa [val] using f6
  have e7 : (val asg 19+(val asg 13*val asg 18)) = val asg 13 := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 13 ≤ 1 by omega) (show val asg 18 ≤ 1 by omega)
      omega
    · norm_num [babyBearP]
      have pp := Nat.mul_le_mul (show val asg 13 ≤ 1 by omega) (show val asg 18 ≤ 1 by omega)
      omega
    · simpa [val] using f7
  have e8 : (val asg 4+(1024*val asg 19)) = (val asg 2+512) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f8
  have e9 : (val asg 5+(1024*val asg 17)) = ((val asg 3+val asg 19)+512) := by
    apply TfheInitialRotation.small_eq
    · norm_num [babyBearP]
      omega
    · norm_num [babyBearP]
      omega
    · simpa [val] using f9
  have z0 : val asg 14 = if val asg 2+1024*val asg 10 = 0 then 1 else 0 := by
    apply zero_nat asg _ _ _ _ (by norm_num [babyBearP]; omega) _ hz0
    simp [v,val]
  have z1 : val asg 15 = if val asg 12 = 0 then 1 else 0 := by
    apply zero_nat asg _ _ _ _ (by norm_num [babyBearP]; omega) _ hz1
    simp [v,val]
  have hrnd : val asg 2+1024*val asg 3 = rounded (word asg) := by
    dsimp [rounded,word]; omega
  have hrb : val asg 7 = (word asg/2048)%2 := by dsimp [word]; omega
  have hi : val asg 17 = initCarry (val asg 2+1024*val asg 3) (val asg 7) := by
    have bt : val asg 11 = 0 ∨ val asg 11 = 1 := by omega
    rcases bt with bt | bt
    · rw [bt] at e2 e5; simp only [zero_mul] at e5
      simp only [initCarry]; split_ifs <;> omega
    · rw [bt] at e2 e5; simp only [one_mul] at e5
      by_cases zz : val asg 2+1024*val asg 10 = 0
      · simp only [zz,ite_true] at z0
        rw [z0] at e4; simp only [one_mul] at e4
        simp only [initCarry]; split_ifs <;> omega
      · simp only [zz,ite_false] at z0
        rw [z0] at e4; simp only [zero_mul] at e4
        simp only [initCarry]; split_ifs <;> omega
  have hc : val asg 19 = digitCarry (val asg 2) (val asg 3) := by
    have bt : val asg 13 = 0 ∨ val asg 13 = 1 := by omega
    rcases bt with bt | bt
    · rw [bt] at e3 e7; simp only [zero_mul] at e7
      simp only [digitCarry]; split_ifs <;> omega
    · rw [bt] at e3 e7; simp only [one_mul] at e7
      by_cases zz : val asg 12 = 0
      · simp only [zz,ite_true] at z1
        rw [z1] at e6; simp only [one_mul] at e6
        simp only [digitCarry]; split_ifs <;> omega
      · simp only [zz,ite_false] at z1
        rw [z1] at e6; simp only [zero_mul] at e6
        simp only [digitCarry]; split_ifs <;> omega
  exact ⟨by dsimp [word]; omega,hrnd,hrb,by simpa [hrnd,hrb] using hi,hc,e8,e9⟩

/-- Native last decomposition step on its balanced next state preserves the state,
including the negative and positive half-base ties. -/
theorem final_step (t : Int) (ht : -512 ≤ t ∧ t ≤ 512) :
    t%1024-1024*(if t%1024 > 512 ∨ (t%1024 = 512 ∧ (t/1024)%1024 ≥ 512) then 1 else 0) = t := by
  split_ifs <;> omega

/-- Arithmetic right shift and mask for the balanced 20-bit state have exactly
these quotient/remainder values; the first carry therefore reads H modulo1024. -/
theorem initial_state (l h i : Int) (hl : 0 ≤ l ∧ l < 1024) (hh : 0 ≤ h ∧ h < 1024) :
    (l+1024*h-1048576*i)%1024 = l ∧
    (l+1024*h-1048576*i)/1024 = h-1024*i ∧
    ((l+1024*h-1048576*i)/1024)%1024 = h := by omega

/-- Exact source carry choices leave the next signed state in the closed balanced
range, including both endpoints; final_step therefore applies to its last digit. -/
theorem next_state_range (l h rb : Nat) (hl : l < 1024) (hh : h < 1024) (hb : rb < 2) :
    -512 ≤ (h : Int)+(digitCarry l h : Int)-1024*(initCarry (l+1024*h) rb : Int) ∧
    (h : Int)+(digitCarry l h : Int)-1024*(initCarry (l+1024*h) rb : Int) ≤ 512 := by
  simp only [initCarry,digitCarry]
  split_ifs <;> norm_num <;> omega

def variableArray (x l h e2 e1 : Nat) : Array BabyBear := Id.run do
  let xl := x%65536
  let rb := x/2048%2
  let i := initCarry (l+1024*h) rb
  let c := digitCarry l h
  let low := l+1024*(h%512)
  let z0 := if low == 0 then 1 else 0
  let z1 := if l%512 == 0 then 1 else 0
  let vals : Array Nat := #[xl,x/65536,l,h,e2,e1,x%2048,rb,xl/4096,(x+2048)/4294967296,
    h%512,h/512,l%512,l/512,z0,z1,z0*(1-rb),i,z1*(1-h/512),c]
  let mut a := Array.replicate nVars (0 : BabyBear)
  for k in [:20] do a := a.set! k (vals[k]! : BabyBear)
  a := a.set! 20 (if low == 0 then 0 else (low : BabyBear)⁻¹)
  a := a.set! 21 (if l%512 == 0 then 0 else ((l%512 : Nat) : BabyBear)⁻¹)
  for k in List.finRange 20 do a := TfheModulusSwitch.setBits a (offsets k) (widths k) vals[k.val]!
  return a

def canonical (x : Nat) : Array BabyBear :=
  let r := rounded x; let l := r%1024; let h := r/1024
  variableArray x l h (l+512-1024*digitCarry l h)
    (h+digitCarry l h+512-1024*initCarry r (x/2048%2))
def asgOf (a : Array BabyBear) : W → BabyBear := fun i => a[i.val]!
def sourceCheck (a : Array BabyBear) : Bool := system.all (fun t => eval (asgOf a) t == 0)
theorem zero_witness : systemAccepts (asgOf (canonical 0)) system := by decide +kernel
theorem negative_midpoint_witness : systemAccepts (asgOf (canonical 2147481600)) system := by decide +kernel
theorem low_digit_tie_witness : systemAccepts (asgOf (canonical 2149580800)) system := by decide +kernel

theorem changed_zero_refused (asg : W → BabyBear) (hx : word asg = 0)
    (hd : val asg 4 = 513) : ¬ systemAccepts asg system := by
  intro hs
  have h := rowSound asg hs
  have hr := h.2.1
  have hc := h.2.2.2.2.1
  have he := h.2.2.2.2.2.1
  rw [hx] at hr
  norm_num [rounded] at hr
  have hl : val asg 2 = 0 := by omega
  have hh : val asg 3 = 0 := by omega
  simp [hl,hh,digitCarry] at hc
  omega
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.initial_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_state
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.next_state_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_state_range
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.range_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms range_bounds
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.field_equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms field_equations
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.zero_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_nat
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.rowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rowSound
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.final_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_step
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.zero_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_witness
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.negative_midpoint_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms negative_midpoint_witness
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.low_digit_tie_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms low_digit_tie_witness
/-- info: 'Minidregg.Compiler.TfheSignedDecomposition.changed_zero_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms changed_zero_refused
end Minidregg.Compiler.TfheSignedDecomposition
