/- Replacement accepted-row type, composed through the previous exact Infer
functions and prefix/square theorems. No second evaluator or square AIR. -/
import Compiler.RangeKeyswitchRow
import Compiler.BfvInferContract
namespace Minidregg.Compiler.RangeKeyswitchInfer
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.BfvInferComposition
open Minidregg.Compiler.BfvInferLinear (primes)
open Minidregg.Compiler.BfvSquareComposition (KernelCiphertext)
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

def Checked (l : Fin 4) (a : Operands) (out : Fin 2 → Nat) : Prop :=
  ∃ asg : RangeKeyswitchRow.Idx → BabyBear,
    systemAccepts asg (RangeKeyswitchRow.system (primes l)) ∧
    RangeKeyswitchRow.RangeHolds asg ∧ Bound RangeKeyswitchRow.wires asg a out

theorem checked_sound (l : Fin 4) (a : Operands) (out : Fin 2 → Nat)
    (hc : Checked l a out) : ∀ h,out h=output (primes l) a h := by
  obtain ⟨asg,hs,hr,hb⟩ := hc
  intro h
  have hh := (RangeKeyswitchRow.actualRowSound l asg hs hr).2 h
  change BfvKeyswitchCore.value asg RangeKeyswitchRow.wires (BfvKeyswitchCore.oIndex h)=
    (BfvKeyswitchCore.value asg RangeKeyswitchRow.wires (BfvKeyswitchCore.aIndex h)+
      ∑ i : Fin 4,BfvKeyswitchCore.value asg RangeKeyswitchRow.wires (BfvKeyswitchCore.dIndex i)*
      BfvKeyswitchCore.value asg RangeKeyswitchRow.wires (BfvKeyswitchCore.kIndex h i))%primes l at hh
  simpa only [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,output] using hh

def Initial (model : Ciphertext) (query : Plaintext) (out : Ciphertext) : Prop :=
  ∀ l j,Checked l (initialOperands model query l j) (fun h => out h l j)
def Rotation (op : Transforms) (key : EvaluationKey) (s : Fin 10)
    (before after : Ciphertext) : Prop :=
  ∀ l j,Checked l (rotationOperands op key before s l j) (fun h => after h l j)

def DotSound : Prop := ∀ op key model query (trace : Nat → Ciphertext),
  Initial model query (trace 0) →
  (∀ s : Fin 10,Rotation op key s (trace s.val) (trace (s.val+1))) →
  trace 10=inferDot op key model query

theorem dotSound : DotSound := by
  intro op key model query trace hi hr
  apply prefixSound Ciphertext (stepAt op key) (initialProduct model query) trace 10
  · funext h l j
    exact (checked_sound l _ _ (hi l j) h).trans (initialOperands_output model query h l j)
  · intro i hi
    have hh : trace (i+1)=rotationStep op key ⟨i,hi⟩ (trace i) := by
      funext h l j
      exact checked_sound l _ _ (hr ⟨i,hi⟩ l j) h
    simpa [stepAt,hi] using hh

def AcceptedInfer (op : BfvInferContract.PublicTransforms) (key : EvaluationKey)
    (model : Ciphertext) (query : Plaintext) (kernel : KernelCiphertext) : Prop :=
  ∃ trace : Nat → Ciphertext, Initial model query (trace 0) ∧
    (∀ s : Fin 10,Rotation op.base key s (trace s.val) (trace (s.val+1))) ∧
    BfvSquareComposition.BaseRoundTrip (BfvInferContract.squareTransforms op) (trace 10) ∧
    BfvSquareComposition.SquareChecked (BfvInferContract.squareTransforms op) (trace 10) kernel

def InferSound : Prop := ∀ op key model query kernel,
  AcceptedInfer op key model query kernel → kernel=BfvInferContract.result op key model query

theorem inferSound : InferSound := by
  intro op key model query kernel hc
  obtain ⟨trace,hi,hr,hrt,hs⟩ := hc
  have hd := dotSound op.base key model query trace hi hr
  have hk := BfvSquareComposition.squareChecked_sound (BfvInferContract.squareTransforms op)
    (trace 10) kernel hrt hs
  simpa only [hd,BfvInferContract.result] using hk

theorem wrongOutputRefused (op : BfvInferContract.PublicTransforms) (key : EvaluationKey)
    (model : Ciphertext) (query : Plaintext) (kernel : KernelCiphertext)
    (hw : kernel≠BfvInferContract.result op key model query) :
    ¬AcceptedInfer op key model query kernel := fun hc => hw (inferSound op key model query kernel hc)
end Minidregg.Compiler.RangeKeyswitchInfer

/-- info: 'Minidregg.Compiler.RangeKeyswitchInfer.checked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchInfer.checked_sound

/-- info: 'Minidregg.Compiler.RangeKeyswitchInfer.dotSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchInfer.dotSound

/-- info: 'Minidregg.Compiler.RangeKeyswitchInfer.inferSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchInfer.inferSound

/-- info: 'Minidregg.Compiler.RangeKeyswitchInfer.wrongOutputRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.RangeKeyswitchInfer.wrongOutputRefused

