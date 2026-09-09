import Compiler.TfheSparseCertificate
namespace Minidregg.Compiler.TfheSparseTeeth
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.TfheSparseRow Minidregg.Compiler.TfheSparseWrap
open Minidregg.Compiler.TfheSparseCertificate
open Minidregg.Theory
set_option autoImplicit false
local instance : Hashable BabyBear where hash x := hash x.val
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

def zeroAssignment (f : Fin 5 → BabyBear) (i : Fin nVars) : BabyBear :=
  if i.val=3 then f 0 else if i.val=4 then f 1 else if i.val=5 then f 2 else
  if i.val=6 then f 3 else if i.val=7 then f 4 else
  if (238 ≤ i.val ∧ i.val < 243) ∨ (258 ≤ i.val ∧ i.val < 263) then 4 else
  if (243 ≤ i.val ∧ i.val < 258 ∧ (i.val-243)%3=2) ∨
    (263 ≤ i.val ∧ i.val < 278 ∧ (i.val-263)%3=2) then 1 else 0

def ZeroPremise : Prop := ∃ a : Fin nVars → BabyBear,
  systemAccepts a system ∧ fval a 0=1 ∧ ∀ g,value a g=0

theorem zero_low (f : Fin 5 → BabyBear) (i : Fin nVars) (hi : i.val < 238)
    (hflag : i.val < 3 ∨ 7 < i.val) : zeroAssignment f i=0 := by
  simp [zeroAssignment,show ¬i.val=3 by omega,show ¬i.val=4 by omega,show ¬i.val=5 by omega,
    show ¬i.val=6 by omega,show ¬i.val=7 by omega,show ¬238 ≤ i.val by omega,
    show ¬258 ≤ i.val by omega,show ¬243 ≤ i.val by omega,show ¬263 ≤ i.val by omega]

theorem zero_readings (f : Fin 5 → BabyBear) :
    (∀ g i,zeroAssignment f (w g i)=0) ∧
    (∀ g i j,zeroAssignment f (wb g i j)=0) ∧
    (∀ i,zeroAssignment f (flag i)=f i) ∧
    (∀ k i,zeroAssignment f (carry k i)=4) ∧
    (∀ k i j,zeroAssignment f (carryBit k i j)=(if j.val=2 then 1 else 0)) ∧
    zeroAssignment f zeroWire=0 ∧ (∀ i,zeroAssignment f (raw i)=0) ∧
    (∀ i j,zeroAssignment f (rawBit i j)=0) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro g i; apply zero_low <;> dsimp [w] <;> omega
  · intro g i j; apply zero_low <;> dsimp [wb] <;> omega
  · intro i; fin_cases i <;> simp [zeroAssignment,flag]
  · intro k i; fin_cases k <;> fin_cases i <;> norm_num [zeroAssignment,carry]
  · intro k i j; fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [zeroAssignment,carryBit]
  · simp [zeroAssignment,zeroWire]
  · intro i; apply zero_low <;> dsimp [raw] <;> omega
  · intro i j
    unfold rawBit
    dsimp only
    split
    · apply zero_low <;> dsimp <;> omega
    · simp [zeroAssignment,zeroWire]

theorem zero_accepts (f : Fin 5 → BabyBear) (hf : ∀ i,f i=0 ∨ f i=1) :
    systemAccepts (zeroAssignment f) system := by
  obtain ⟨hw,hb,hf',hc,hcb,hz,hr,hrb⟩ := zero_readings f
  simp only [system,systemAccepts_append]
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩
  · intro t ht
    obtain ⟨g,_,ht⟩ := List.mem_flatMap.mp ht
    have hh : systemAccepts (zeroAssignment f) (AirBignum.limbRangeSystem (w g) (wb g)) := by
      rw [AirBignum.limbRangeSystem_correct]
      intro i
      simp [rangeGadget_correct,hw,hb]
    exact hh t ht
  · intro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    rw [boolGadget_correct,hf']
    exact hf i
  · intro t ht
    obtain ⟨k,_,ht⟩ := List.mem_flatMap.mp ht
    have hh : systemAccepts (zeroAssignment f) (wrapSystem (leftTerm k) (rightTerm k) (carry k) (carryBit k)) := by
      simp only [wrapSystem,systemAccepts_append]
      refine ⟨⟨?_,?_⟩,?_⟩
      · rw [AirBignum.limbRangeSystem_correct]
        intro i
        norm_num [rangeGadget_correct,hc,hcb,Fin.forall_fin_succ,Fin.sum_univ_succ]
      · simp only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_add',eval_vr,eval_cst,hc]
        ring
      · intro t ht
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
        rw [wrapColumn_correct]
        fin_cases k <;> norm_num [leftTerm,rightTerm,eval_add',eval_mul',eval_cst,eval_vr,hw,hc]
    exact hh t ht
  · intro t ht
    obtain ⟨i,_,ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> simp [accepts,eval_mul',eval_add',eval_vr,eval_cst,hw]
  · simpa only [systemAccepts_cons,systemAccepts_nil,and_true,accepts,eval_vr] using hz
  · rw [AirBignum.limbRangeSystem_correct]
    intro i
    simp [rangeGadget_correct,hr,hrb]

theorem zero_values (f : Fin 5 → BabyBear) (g : Fin 8) : value (zeroAssignment f) g=0 := by
  simp [value,AirBignum.limbVals,(zero_readings f).1]

theorem zero_premise : ZeroPremise := by
  refine ⟨zeroAssignment (fun _ => 1),zero_accepts _ (fun _ => Or.inr rfl),?_,zero_values _⟩
  dsimp [fval]
  rw [(zero_readings _).2.2.1]
  decide +kernel

theorem wrong_scale_refused (a : Fin nVars → BabyBear)
    (h : rawValue a≠256*value a 3) : ¬systemAccepts a emittedSystem := by
  intro hs
  exact h (emitted_sound a hs).2.2.2.2.2

theorem wrong_anchor_refused (a : Fin nVars → BabyBear)
    (hf : fval a 0=1) (ha : value a 3≠value a 7) : ¬systemAccepts a emittedSystem := by
  intro hs
  exact ha ((emitted_sound a hs).2.2.2.2.1 hf).2

def flagValues (j : Fin 512) : Fin 5 → ℕ := ![if j.val=0 then 1 else 0,
  if j.val < 44 then 1 else 0,if j.val < 162 then 1 else 0,
  if j.val < 351 then 1 else 0,if 469 ≤ j.val then 1 else 0]
def zeroRows (j : Fin 512) : Fin nVars → BabyBear := zeroAssignment (fun i => (flagValues j i : BabyBear))

def WholePremise : Prop := ∃ rows : Fin 512 → Fin nVars → BabyBear,
  Linked (fun _ => 0) (fun _ => 0) (fun _ => 0) rows ∧
  ∀ j,systemAccepts (rows j) emittedSystem

theorem flagValues_bool (j : Fin 512) (i : Fin 5) : flagValues j i=0 ∨ flagValues j i=1 := by
  fin_cases i <;> dsimp [flagValues]
  all_goals split <;> simp

theorem whole_premise : WholePremise := by
  have hfv (j : Fin 512) (i : Fin 5) : fval (zeroRows j) i=flagValues j i := by
    dsimp [fval,zeroRows]
    rw [(zero_readings _).2.2.1]
    apply ZMod.val_cast_of_lt
    rcases flagValues_bool j i with h|h <;> rw [h] <;> decide
  refine ⟨zeroRows,?_,?_⟩
  · intro j
    have hz (g : Fin 8) : read zeroRows j g=0 := by
      dsimp [TfheSparseCertificate.read,zeroRows]
      rw [zero_values]
      simp
    simp only [hz,hfv,neg_zero,ite_self]
    simp [flagValues]
  · intro j
    apply (AirAssertionShare.optimize_preserves (zeroRows j) system).mpr
    apply zero_accepts
    intro i
    rcases flagValues_bool j i with h|h <;> simp [h]
end Minidregg.Compiler.TfheSparseTeeth

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.zero_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.zero_low

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.zero_readings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.zero_readings

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.zero_accepts

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.zero_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.zero_values

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.zero_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.zero_premise

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.wrong_scale_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.wrong_scale_refused

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.wrong_anchor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.wrong_anchor_refused

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.flagValues_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.flagValues_bool

/-- info: 'Minidregg.Compiler.TfheSparseTeeth.whole_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.TfheSparseTeeth.whole_premise
