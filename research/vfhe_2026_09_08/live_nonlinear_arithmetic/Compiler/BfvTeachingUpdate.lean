/- Teaching uses the existing emitted paired-MAC source: no new arithmetic
circuit, witness executor, or idealized update replaces the native addition/subtraction path. -/
import Compiler.BfvInferContract
namespace Minidregg.Compiler.BfvTeachingUpdate
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open Minidregg.Compiler.BfvInferComposition (Operands Ciphertext Plaintext EvaluationKey)
open Minidregg.Compiler.BfvInferLinear (primes)
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

abbrev Pair := Fin 2 → Nat

def operands (q : Nat) (acc fresh old : Pair) : Operands where
  d := ![fresh 0,fresh 1,old 0,old 1]
  key := ![![1,0,q-1,0],![0,1,0,q-1]]
  addend := acc

def updateValue (q acc fresh old : Nat) : Nat :=
  (((acc : Int)+(fresh : Int)-(old : Int))%(q : Int)).toNat

def OperandSound : Prop := ∀ q : Nat,0<q → ∀ acc fresh old : Pair,∀ h,
  BfvInferComposition.output q (operands q acc fresh old) h=
    updateValue q (acc h) (fresh h) (old h)

theorem signedReduction (q a f o : Nat) (hq : 0<q) :
    (a+f+o*(q-1))%q=updateValue q a f o := by
  have hc : ((a+f+o*(q-1) : Nat) : Int)=
      (a : Int)+(f : Int)-(o : Int)+(o : Int)*(q : Int) := by
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,Int.ofNat_sub (by omega)]
    push_cast
    ring
  have hm := congrArg Int.toNat (Int.natCast_emod (a+f+o*(q-1)) q)
  simp only [Int.toNat_natCast] at hm
  rw [hm,hc]
  simp [updateValue,Int.add_emod]

theorem operandSound : OperandSound := by
  intro q hq acc fresh old h
  have hval : BfvInferComposition.output q (operands q acc fresh old) h=
      (acc h+fresh h+old h*(q-1))%q := by
    fin_cases h <;> simp [BfvInferComposition.output,operands,Fin.sum_univ_succ,Nat.add_assoc]
  exact hval.trans (signedReduction q _ _ _ hq)

def UpdateRowChecked (l : Fin 4) (acc fresh old out : Pair) : Prop :=
  BfvInferComposition.EmittedChecked l (operands (primes l) acc fresh old) out

theorem updateRow_sound (l : Fin 4) (acc fresh old out : Pair)
    (hc : UpdateRowChecked l acc fresh old out) : ∀ h,
    out h=updateValue (primes l) (acc h) (fresh h) (old h) := by
  intro h
  exact (BfvInferComposition.emittedChecked_sound l _ _ hc h).trans
    (operandSound (primes l) (BfvKeyswitchRow.prime_capacity l).1 acc fresh old h)

def update (acc fresh old : Ciphertext) : Ciphertext :=
  fun h l j => updateValue (primes l) (acc h l j) (fresh h l j) (old h l j)

def UpdateChecked (acc fresh old out : Ciphertext) : Prop :=
  ∀ l j,UpdateRowChecked l (fun h => acc h l j) (fun h => fresh h l j)
    (fun h => old h l j) (fun h => out h l j)

def UpdateSound : Prop := ∀ acc fresh old out,
  UpdateChecked acc fresh old out → out=update acc fresh old

theorem updateSound : UpdateSound := by
  intro acc fresh old out hc
  funext h l j
  exact updateRow_sound l _ _ _ _ (hc l j) h

/-- Complete update history over public ciphertext arithmetic. Which issued
ciphertext/lane is fresh or expired remains an explicit service binding. -/
def history (initial : Ciphertext) (fresh old : Nat → Ciphertext) : Nat → Ciphertext
  | 0 => initial
  | n+1 => update (history initial fresh old n) (fresh n) (old n)

def HistorySound : Prop := ∀ (initial : Ciphertext) (fresh old trace : Nat → Ciphertext)
  (n : Nat),trace 0=initial →
  (∀ i,i<n → UpdateChecked (trace i) (fresh i) (old i) (trace (i+1))) →
  trace n=history initial fresh old n

theorem historySound : HistorySound := by
  intro initial fresh old trace n h0 hs
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hn := updateSound (trace n) (fresh n) (old n) (trace (n+1)) (hs n (by omega))
    rw [hn,history,ih (fun i hi => hs i (by omega))]

/-- The completed Infer contract already quantifies over its caller-selected
model. Substituting the forced updated model needs no old-data specialization. -/
def LearnThenInferSound : Prop := ∀ (op : BfvInferContract.PublicTransforms)
  (key : EvaluationKey) (query : Plaintext) (acc fresh old next : Ciphertext)
  (kernel : BfvSquareComposition.KernelCiphertext),UpdateChecked acc fresh old next →
  BfvInferContract.AcceptedInfer op key next query kernel →
  kernel=BfvInferContract.result op key (update acc fresh old) query

theorem learnThenInferSound : LearnThenInferSound := by
  intro op key query acc fresh old next kernel hu hi
  have hk := BfvInferContract.inferSound op key next query kernel hi
  simpa only [updateSound acc fresh old next hu] using hk

/-- Zero means exact zero coefficient words, not a fresh encryption of zero. -/
def zero : Ciphertext := fun _ _ _ => 0

theorem noExpiry (acc fresh : Ciphertext) : update acc fresh zero=
    fun h l j => (acc h l j+fresh h l j)%primes l := by
  funext h l j
  change updateValue (primes l) (acc h l j) (fresh h l j) 0=_
  simpa only [Nat.zero_mul,Nat.add_zero] using
    (signedReduction (primes l) (acc h l j) (fresh h l j) 0 (BfvKeyswitchRow.prime_capacity l).1).symm

/-- A still-canonical incorrect result cannot pass the existing MAC source,
regardless of the auxiliary witness assignment. -/
def WrongUpdateRefused : Prop := ∀ acc fresh old out,
  out≠update acc fresh old → ¬UpdateChecked acc fresh old out

theorem wrongUpdateRefused : WrongUpdateRefused := by
  intro acc fresh old out hwrong hc
  exact hwrong (updateSound acc fresh old out hc)
end Minidregg.Compiler.BfvTeachingUpdate

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.signedReduction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.signedReduction

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.operandSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.operandSound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.updateRow_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.updateRow_sound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.updateSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.updateSound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.historySound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.historySound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.learnThenInferSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.learnThenInferSound

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.noExpiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.noExpiry

/-- info: 'Minidregg.Compiler.BfvTeachingUpdate.wrongUpdateRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvTeachingUpdate.wrongUpdateRefused
