/- Whole Infer's dot stage, composed from the accepted compiler-owned MAC rows
and the public linear plan. The NTT callbacks remain a stated runtime boundary. -/
import Compiler.BfvInferLinear
namespace Minidregg.Compiler.BfvInferComposition
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan Minidregg.Theory
open BfvInferLinear
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

structure Operands where
  d : Fin 4 → Nat
  key : Fin 2 → Fin 4 → Nat
  addend : Fin 2 → Nat

def output (q : Nat) (a : Operands) (h : Fin 2) : Nat :=
  (a.addend h+∑ i : Fin 4,a.d i*a.key h i)%q

/-- Public binding carries no output arithmetic premise. Only the public words
are identified with their roles; accepted source equations supply arithmetic. -/
def Bound {J : Type} (w : BfvKeyswitchCore.Wires J) (asg : J → BabyBear)
    (a : Operands) (out : Fin 2 → Nat) : Prop :=
  (∀ i,BfvKeyswitchCore.value asg w (BfvKeyswitchCore.dIndex i)=a.d i) ∧
  (∀ h i,BfvKeyswitchCore.value asg w (BfvKeyswitchCore.kIndex h i)=a.key h i) ∧
  (∀ h,BfvKeyswitchCore.value asg w (BfvKeyswitchCore.aIndex h)=a.addend h) ∧
  (∀ h,BfvKeyswitchCore.value asg w (BfvKeyswitchCore.oIndex h)=out h)

def BoundRowSound : Prop := ∀ (J : Type) (q : Nat), 0<q → q<512^6 →
  ∀ (w : BfvKeyswitchCore.Wires J) (asg : J → BabyBear) (a : Operands) (out : Fin 2 → Nat),
  systemAccepts asg (BfvKeyswitchCore.system q w) → Bound w asg a out →
  ∀ h,out h=output q a h

theorem boundRowSound : BoundRowSound := by
  intro J q hq hcap w asg a out hs hb h
  have hh := (BfvKeyswitchCore.sound q hq hcap w asg hs).2 h
  simpa only [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,output] using hh

def EmittedChecked (l : Fin 4) (a : Operands) (out : Fin 2 → Nat) : Prop :=
  ∃ asg : Fin BfvKeyswitchRow.nVars → BabyBear,
    systemAccepts asg (BfvKeyswitchRow.emittedSystem (primes l)) ∧
    Bound BfvKeyswitchRow.wires asg a out

theorem emittedChecked_sound (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (hc : EmittedChecked l a out) : ∀ h,out h=output (primes l) a h := by
  obtain ⟨asg,hs,hb⟩ := hc
  intro h
  have hh := (BfvKeyswitchRow.emittedSystem_sound l asg hs).2 h
  change BfvKeyswitchCore.value asg BfvKeyswitchRow.wires (BfvKeyswitchCore.oIndex h)=
    (BfvKeyswitchCore.value asg BfvKeyswitchRow.wires (BfvKeyswitchCore.aIndex h)+
      ∑ i : Fin 4,BfvKeyswitchCore.value asg BfvKeyswitchRow.wires (BfvKeyswitchCore.dIndex i)*
      BfvKeyswitchCore.value asg BfvKeyswitchRow.wires (BfvKeyswitchCore.kIndex h i))%primes l at hh
  simpa only [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,output] using hh

abbrev Ciphertext := Fin 2 → Fin 4 → Slot → Nat
abbrev Plaintext := Fin 4 → Slot → Nat
abbrev EvaluationKey := Fin 10 → Fin 2 → Fin 4 → Fin 4 → Slot → Nat
/-- These supplied public transforms name the exact representation boundary.
No inverse/linearity claim about a Rust NTT implementation is assumed or proved. -/
structure Transforms where
  forward : Fin 4 → (Slot → Nat) → Slot → Nat
  inverse : Fin 4 → (Slot → Nat) → Slot → Nat

def initialOperands (model : Ciphertext) (query : Plaintext) (l : Fin 4) (j : Slot) : Operands where
  d := fun i => if i.val=0 then query l j else 0
  key := fun h i => if i.val=0 then model h l j else 0
  addend := fun _ => 0

def initialProduct (model : Ciphertext) (query : Plaintext) : Ciphertext :=
  fun h l j => model h l j*query l j%primes l

theorem initialOperands_output (model : Ciphertext) (query : Plaintext) (h : Fin 2)
    (l : Fin 4) (j : Slot) :
    output (primes l) (initialOperands model query l j) h=initialProduct model query h l j := by
  fin_cases h <;> simp [output,initialOperands,initialProduct,Nat.mul_comm]

def rotated (p : Ciphertext) (s : Fin 10) : Ciphertext :=
  fun h l => substitute (exponents s) (p h l)

def lifted (op : Transforms) (p : Ciphertext) (s : Fin 10)
    (target source : Fin 4) : Slot → Nat :=
  op.forward target (fun j => canonicalLift (primes target)
    (op.inverse source (rotated p s 1 source) j))


/-- Exactly the input-specific NTT congruence needed to replace native lazy
coefficients with the verifier's canonical target-prime coefficients. -/
def NativeLiftCorrespondence : Prop := ∀ (op : Transforms) (p : Ciphertext) (s : Fin 10)
  (source target : Fin 4),
  (∀ j,op.inverse source (rotated p s 1 source) j<primes source) →
  op.forward target (fun j => canonicalLift (primes target)
    (op.inverse source (rotated p s 1 source) j))=
    op.forward target (op.inverse source (rotated p s 1 source)) →
  lifted op p s target source=op.forward target (fun j => lazyLiftWord (primes target)
    (op.inverse source (rotated p s 1 source) j))

theorem nativeLiftCorrespondence : NativeLiftCorrespondence := by
  intro op p s source target hcanonical hcongruence
  have hword : (fun j => lazyLiftWord (primes target)
      (op.inverse source (rotated p s 1 source) j))=
      op.inverse source (rotated p s 1 source) := by
    funext j
    exact (liftCorrect source target _ (hcanonical j)).2.1
  rw [hword]
  exact hcongruence

def rotationOperands (op : Transforms) (key : EvaluationKey) (p : Ciphertext)
    (s : Fin 10) (l : Fin 4) (j : Slot) : Operands where
  d := fun i => lifted op p s l i j
  key := fun h i => key s h l i j
  addend := fun h => if h.val=0 then (p 0 l j+rotated p s 0 l j)%primes l else p 1 l j

def rotationStep (op : Transforms) (key : EvaluationKey) (s : Fin 10)
    (p : Ciphertext) : Ciphertext :=
  fun h l j => output (primes l) (rotationOperands op key p s l j) h

def InitialChecked (model : Ciphertext) (query : Plaintext) (out : Ciphertext) : Prop :=
  ∀ l j, EmittedChecked l (initialOperands model query l j) (fun h => out h l j)
def RotationChecked (op : Transforms) (key : EvaluationKey) (s : Fin 10)
    (before after : Ciphertext) : Prop :=
  ∀ l j, EmittedChecked l (rotationOperands op key before s l j) (fun h => after h l j)

theorem initialChecked_sound (model : Ciphertext) (query : Plaintext) (out : Ciphertext)
    (hc : InitialChecked model query out) : out=initialProduct model query := by
  funext h l j
  exact (emittedChecked_sound l _ _ (hc l j) h).trans (initialOperands_output model query h l j)

theorem rotationChecked_sound (op : Transforms) (key : EvaluationKey) (s : Fin 10)
    (before after : Ciphertext) (hc : RotationChecked op key s before after) :
    after=rotationStep op key s before := by
  funext h l j
  exact emittedChecked_sound l _ _ (hc l j) h

/-- Generic prefix composition, reused at every length through the final stage. -/
def iterate {S : Type} (step : Nat → S → S) (start : S) : Nat → S
  | 0 => start
  | n+1 => step n (iterate step start n)

def PrefixSound : Prop := ∀ (S : Type) (step : Nat → S → S) (start : S)
  (trace : Nat → S) (n : Nat),trace 0=start →
  (∀ i,i<n → trace (i+1)=step i (trace i)) → trace n=iterate step start n

theorem prefixSound : PrefixSound := by
  intro S step start trace n h0 hs
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hs n (by omega),iterate,ih (fun i hi => hs i (by omega))]

def stepAt (op : Transforms) (key : EvaluationKey) (n : Nat) (p : Ciphertext) : Ciphertext :=
  if h : n<10 then rotationStep op key ⟨n,h⟩ p else p

def inferDot (op : Transforms) (key : EvaluationKey) (model : Ciphertext)
    (query : Plaintext) : Ciphertext := iterate (stepAt op key) (initialProduct model query) 10

def InferDotSound : Prop := ∀ (op : Transforms) (key : EvaluationKey) (model : Ciphertext)
  (query : Plaintext) (trace : Nat → Ciphertext),
  InitialChecked model query (trace 0) →
  (∀ s : Fin 10,RotationChecked op key s (trace s.val) (trace (s.val+1))) →
  trace 10=inferDot op key model query

theorem inferDotSound : InferDotSound := by
  intro op key model query trace hi hr
  apply prefixSound Ciphertext (stepAt op key) (initialProduct model query) trace 10
  · exact initialChecked_sound model query (trace 0) hi
  · intro i hi
    have hs := rotationChecked_sound op key ⟨i,hi⟩ (trace i) (trace (i+1)) (hr ⟨i,hi⟩)
    simpa [stepAt,hi] using hs

end Minidregg.Compiler.BfvInferComposition

/-- info: 'Minidregg.Compiler.BfvInferComposition.boundRowSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.boundRowSound

/-- info: 'Minidregg.Compiler.BfvInferComposition.emittedChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.emittedChecked_sound

/-- info: 'Minidregg.Compiler.BfvInferComposition.initialOperands_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.initialOperands_output

/-- info: 'Minidregg.Compiler.BfvInferComposition.initialChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.initialChecked_sound

/-- info: 'Minidregg.Compiler.BfvInferComposition.rotationChecked_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.rotationChecked_sound

/-- info: 'Minidregg.Compiler.BfvInferComposition.prefixSound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.prefixSound

/-- info: 'Minidregg.Compiler.BfvInferComposition.inferDotSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.inferDotSound

/-- info: 'Minidregg.Compiler.BfvInferComposition.nativeLiftCorrespondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferComposition.nativeLiftCorrespondence
