/- Direct target-residue rows, joined to the existing eleven-stage BFV program.
Public staging identifies operands, not the truth of an arithmetic result.
PCS/Fiat-Shamir and Rust IO reconstruction are separate from this source theorem. -/
import Compiler.MatchedFieldMac
namespace Minidregg.Compiler.MatchedFieldProgram
open Minidregg.Compiler Minidregg.Compiler.BfvInferComposition
open Minidregg.Compiler.BfvInferLinear (Slot primes)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000

def Checked (l : Fin 4) (a : Operands) (out : Fin 2 → Nat) : Prop :=
  ∃ r : MatchedFieldMac.Row,MatchedFieldMac.Canonical (primes l) r ∧
    MatchedFieldMac.WholeRow (primes l) r 0 ∧ MatchedFieldMac.operands r=a ∧
    MatchedFieldMac.outputs r=out
def Initial (model : Ciphertext) (query : Plaintext) (out : Ciphertext) : Prop :=
  ∀ l j,Checked l (initialOperands model query l j) (fun h => out h l j)
def Rotation (op : Transforms) (key : EvaluationKey) (s : Fin 10)
    (before after : Ciphertext) : Prop :=
  ∀ l j,Checked l (rotationOperands op key before s l j) (fun h => after h l j)

def LinearSound : Prop := ∀ op key model query (trace : Nat → Ciphertext),
  Initial model query (trace 0) →
  (∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) →
  trace 10=inferDot op key model query

def updateOperands (q : Nat) (acc fresh old : Fin 2 → Nat) : Operands where
  d := ![fresh 0,fresh 1,old 0,old 1]
  key := ![![1,0,q-1,0],![0,1,0,q-1]]
  addend := acc
def updateValue (q : Nat) (acc fresh old : Fin 2 → Nat) (h : Fin 2) : Nat :=
  (acc h+fresh h+q-old h)%q
def Update (acc fresh old out : Ciphertext) : Prop :=
  ∀ l j,Checked l (updateOperands (primes l) (fun h => acc h l j)
    (fun h => fresh h l j) (fun h => old h l j)) (fun h => out h l j)

def UpdateSound : Prop := ∀ acc fresh old out : Ciphertext,
  Update acc fresh old out →
  ∀ h l j,out h l j=(acc h l j+fresh h l j+primes l-old h l j)%primes l

def updated (acc fresh old : Ciphertext) : Ciphertext := fun h l j =>
  updateValue (primes l) (fun h => acc h l j) (fun h => fresh h l j)
    (fun h => old h l j) h

theorem checked_sound (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (h : Checked l a out) : ∀ c,out c=output (primes l) a c := by
  obtain ⟨r,hc,he,ha,ho⟩ := h
  have hs := MatchedFieldMac.sound (primes l) (MatchedFieldMac.prime_positive l) r hc he.2
  simpa only [ha,ho] using hs

theorem checked_complete (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (hd : ∀ i,a.d i<primes l) (hk : ∀ h i,a.key h i<primes l)
    (ha : ∀ h,a.addend h<primes l) (ho : ∀ h,out h=output (primes l) a h) :
    Checked l a out := by
  have he : out=output (primes l) a := funext ho
  subst out
  obtain ⟨hc,hg⟩ := MatchedFieldMac.complete (primes l) (MatchedFieldMac.prime_positive l) a hd hk ha
  exact ⟨MatchedFieldMac.pack a (output (primes l) a),hc,hg,
    MatchedFieldMac.pack_operands _ _,MatchedFieldMac.pack_outputs _ _⟩

/-- The same prefix induction and exact public BFV program used before the
backend replacement, now with target-field row acceptance. -/
theorem linearSound : LinearSound := by
  intro op key model query trace hi hr
  apply prefixSound Ciphertext (stepAt op key) (initialProduct model query) trace 10
  · funext h l j
    exact (checked_sound l _ _ (hi l j) h).trans (initialOperands_output model query h l j)
  · intro i hi
    have hh : trace (i+1)=rotationStep op key ⟨i,hi⟩ (trace i) := by
      funext h l j
      exact checked_sound l _ _ (hr ⟨i,hi⟩ l j) h
    simpa [stepAt,hi] using hh

theorem output_canonical (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (hc : Checked l a out) (h : Fin 2) : out h<primes l := by
  rw [checked_sound l a out hc h]
  exact Nat.mod_lt _ (MatchedFieldMac.prime_positive l)

theorem checked_d_canonical (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (hc : Checked l a out) (i : Fin 4) : a.d i<primes l := by
  obtain ⟨r,hc,_,ha,_⟩ := hc
  have hd := hc (MatchedFieldMac.dIndex i)
  change (MatchedFieldMac.operands r).d i<primes l at hd
  rwa [ha] at hd

theorem updateOperands_output (q : Nat) (hq : 0<q)
    (acc fresh old : Fin 2 → Nat) (hold : ∀ h,old h<q) (h : Fin 2) :
    output q (updateOperands q acc fresh old) h=updateValue q acc fresh old h := by
  have hm : ((q-1 : Nat) : ZMod q)=-1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hcast (h : Fin 2) : ((acc h+fresh h+q-old h : Nat) : ZMod q)=
      (acc h : ZMod q)+(fresh h : ZMod q)-(old h : ZMod q) := by
    rw [Nat.cast_sub (by have := hold h; omega)]
    simp
  have he : ((acc h+∑ i : Fin 4,(updateOperands q acc fresh old).d i*
      (updateOperands q acc fresh old).key h i : Nat) : ZMod q)=
      ((acc h+fresh h+q-old h : Nat) : ZMod q) := by
    rw [hcast]
    fin_cases h <;> simp [updateOperands,Fin.sum_univ_succ,hm] <;> ring
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,output,updateValue,updateOperands] using hv

theorem updateSound : UpdateSound := by
  intro acc fresh old out hc h l j
  have hold : ∀ c,old c l j<primes l := by
    intro c
    fin_cases c
    · exact checked_d_canonical l _ _ (hc l j) 2
    · exact checked_d_canonical l _ _ (hc l j) 3
  exact (checked_sound l _ _ (hc l j) h).trans
    (updateOperands_output (primes l) (MatchedFieldMac.prime_positive l)
      _ _ _ hold h)

/-- A complete accepted FIFO update followed by all eleven accepted linear
stages computes the authorized inference on exactly the updated model. -/
theorem updateThenLinearSound (op : Transforms) (key : EvaluationKey)
    (acc fresh old model : Ciphertext) (query : Plaintext) (trace : Nat → Ciphertext)
    (hu : Update acc fresh old model) (hi : Initial model query (trace 0))
    (hr : ∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) :
    model=updated acc fresh old ∧
    trace 10=inferDot op key (updated acc fresh old) query := by
  have hm : model=updated acc fresh old := by
    funext h l j
    exact updateSound acc fresh old model hu h l j
  exact ⟨hm,by simpa only [hm] using linearSound op key model query trace hi hr⟩

theorem wrongLinearRefused (op : Transforms) (key : EvaluationKey) (model : Ciphertext)
    (query : Plaintext) (trace : Nat → Ciphertext)
    (hw : trace 10≠inferDot op key model query) :
    ¬(Initial model query (trace 0) ∧
      ∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) := by
  rintro ⟨hi,hr⟩
  exact hw (linearSound op key model query trace hi hr)

def demoModel : Ciphertext := fun _ _ _ => 3
def demoQuery : Plaintext := fun _ _ => 2
def demoKey : EvaluationKey := fun _ _ _ _ _ => 0
def demoTransforms : Transforms := ⟨fun _ _ _ => 0,fun _ _ _ => 0⟩
def demoTrace (n : Nat) : Ciphertext := fun h _ _ => if h.val=0 then 6*2^n else 6
def zeroSlot : Slot := ⟨0,by decide⟩

theorem demoInitial : Initial demoModel demoQuery (demoTrace 0) := by
  intro l j
  apply checked_complete
  · intro i; fin_cases l <;> fin_cases i <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h i; fin_cases l <;> fin_cases h <;> fin_cases i <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h; exact MatchedFieldMac.prime_positive l
  · intro h; fin_cases l <;> fin_cases h <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]

theorem demoRotations : ∀ s : Fin 10,Rotation demoTransforms demoKey s
    (demoTrace s.val) (demoTrace (s.val+1)) := by
  intro s l j
  apply checked_complete
  · intro i; exact MatchedFieldMac.prime_positive l
  · intro h i; exact MatchedFieldMac.prime_positive l
  · intro h
    fin_cases h
    · exact Nat.mod_lt _ (MatchedFieldMac.prime_positive l)
    · fin_cases l <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h
    fin_cases s <;> fin_cases l <;> fin_cases h <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]

/-- All eleven stages are jointly inhabited at the four actual primes, with
nonzero changing state; the old program and prefix compiler are reused. -/
theorem linearPremiseInhabited : ∃ (op : Transforms) (key : EvaluationKey)
    (model : Ciphertext) (query : Plaintext) (trace : Nat → Ciphertext),
    Initial model query (trace 0) ∧
    (∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) ∧
    trace 10 0 0 zeroSlot=6144 ∧ trace 10 1 0 zeroSlot=6 :=
  ⟨demoTransforms,demoKey,demoModel,demoQuery,demoTrace,demoInitial,demoRotations,rfl,rfl⟩

theorem updateWitness : Update (fun _ _ _ => 5) (fun _ _ _ => 7)
    (fun _ _ _ => 3) (fun _ _ _ => 9) := by
  intro l j
  apply checked_complete
  · intro i; fin_cases l <;> fin_cases i <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h i; fin_cases l <;> fin_cases h <;> fin_cases i <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h; fin_cases l <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]
  · intro h; fin_cases l <;> fin_cases h <;> norm_num [initialOperands,demoModel,demoQuery,demoTrace,rotationOperands,lifted,demoTransforms,demoKey,rotated,BfvInferLinear.substitute,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]

theorem demoUpdate : Update (fun _ _ _ => 1) (fun _ _ _ => 5)
    (fun _ _ _ => 3) demoModel := by
  intro l j
  apply checked_complete
  · intro i; fin_cases l <;> fin_cases i <;> norm_num [updateOperands,primes,BfvKeyswitchRow.primes]
  · intro h i; fin_cases l <;> fin_cases h <;> fin_cases i <;> norm_num [updateOperands,primes,BfvKeyswitchRow.primes]
  · intro h; fin_cases l <;> norm_num [updateOperands,primes,BfvKeyswitchRow.primes]
  · intro h; fin_cases l <;> fin_cases h <;> norm_num [demoModel,output,updateOperands,primes,BfvKeyswitchRow.primes,Fin.sum_univ_succ]

/-- Joint inhabitation of the complete update-and-eleven-stage head. The
abstract transform witness is zero; it makes no claim to be the native NTT. -/
theorem updateLinearPremiseInhabited : ∃ (op : Transforms) (key : EvaluationKey)
    (acc fresh old model : Ciphertext) (query : Plaintext) (trace : Nat → Ciphertext),
    Update acc fresh old model ∧ Initial model query (trace 0) ∧
    (∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) ∧
    model 0 0 zeroSlot=3 ∧ trace 10 0 0 zeroSlot=6144 :=
  ⟨demoTransforms,demoKey,fun _ _ _ => 1,fun _ _ _ => 5,fun _ _ _ => 3,
    demoModel,demoQuery,demoTrace,demoUpdate,demoInitial,demoRotations,rfl,rfl⟩

theorem omittedExpiryRefused : ¬Update (fun _ _ _ => 5) (fun _ _ _ => 7)
    (fun _ _ _ => 3) (fun _ _ _ => 12) := by
  intro hc
  have hh := updateSound _ _ _ _ hc 0 0 zeroSlot
  norm_num [primes,BfvKeyswitchRow.primes] at hh

/-- info: 'Minidregg.Compiler.MatchedFieldProgram.checked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_sound
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.checked_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_complete
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.linearSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linearSound
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.output_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms output_canonical
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.checked_d_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_d_canonical
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.updateOperands_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms updateOperands_output
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.updateSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms updateSound
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.updateThenLinearSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms updateThenLinearSound
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.wrongLinearRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrongLinearRefused
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.demoInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoInitial
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.demoRotations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoRotations
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.linearPremiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linearPremiseInhabited
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.updateWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms updateWitness
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.demoUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms demoUpdate
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.updateLinearPremiseInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms updateLinearPremiseInhabited
/-- info: 'Minidregg.Compiler.MatchedFieldProgram.omittedExpiryRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omittedExpiryRefused

end Minidregg.Compiler.MatchedFieldProgram
