/- One contract for the chosen Infer: compiler-accepted initial product, ten
rotation/add stages, basis extension, tensor square and directed rescale. -/
import Compiler.BfvInferComposition
import Compiler.BfvSquareComposition
namespace Minidregg.Compiler.BfvInferContract
open Minidregg.Compiler
open Minidregg.Compiler.BfvInferLinear (Slot)
open Minidregg.Compiler.BfvInferComposition (Ciphertext Plaintext EvaluationKey)
open Minidregg.Compiler.BfvSquareComposition (KernelCiphertext)
set_option autoImplicit false

/-- One shared pair of base-prime transform callbacks is used throughout Infer;
the extension-prime callbacks occur only in its final square. -/
structure PublicTransforms where
  base : BfvInferComposition.Transforms
  forwardExtended : Fin 9 → (Slot → Nat) → Slot → Nat
  inverseExtended : Fin 9 → (Slot → Nat) → Slot → Nat

def squareTransforms (op : PublicTransforms) : BfvSquareComposition.SquareTransforms where
  inverseBase := op.base.inverse
  forwardExtended := op.forwardExtended
  inverseExtended := op.inverseExtended
  forwardBase := op.base.forward

def result (op : PublicTransforms) (key : EvaluationKey) (model : Ciphertext)
    (query : Plaintext) : KernelCiphertext :=
  BfvSquareComposition.exactDirectedSquare (squareTransforms op)
    (BfvInferComposition.inferDot op.base key model query)

/-- All source acceptance and bindings refer to the same intermediate dot.
The only transform law is the input-specific common-modulus roundtrip, not
an arithmetic-output equality. Byte commitments/decoding remain outside Lean. -/
def AcceptedInfer (op : PublicTransforms) (key : EvaluationKey) (model : Ciphertext)
    (query : Plaintext) (kernel : KernelCiphertext) : Prop :=
  ∃ trace : Nat → Ciphertext,
    BfvInferComposition.InitialChecked model query (trace 0) ∧
    (∀ s : Fin 10,BfvInferComposition.RotationChecked op.base key s
      (trace s.val) (trace (s.val+1))) ∧
    BfvSquareComposition.BaseRoundTrip (squareTransforms op) (trace 10) ∧
    BfvSquareComposition.SquareChecked (squareTransforms op) (trace 10) kernel

def InferSound : Prop := ∀ op key model query kernel,
  AcceptedInfer op key model query kernel → kernel=result op key model query

def UniqueOutput : Prop := ∀ op key model query left right,
  AcceptedInfer op key model query left → AcceptedInfer op key model query right → left=right

def WrongOutputRefused : Prop := ∀ op key model query kernel,
  kernel≠result op key model query → ¬AcceptedInfer op key model query kernel

theorem inferSound : InferSound := by
  intro op key model query kernel hc
  obtain ⟨trace,hi,hr,hrt,hs⟩ := hc
  have hd := BfvInferComposition.inferDotSound op.base key model query trace hi hr
  have hk := BfvSquareComposition.squareChecked_sound (squareTransforms op) (trace 10) kernel hrt hs
  simpa only [hd,result] using hk

theorem uniqueOutput : UniqueOutput := by
  intro op key model query left right hl hr
  exact (inferSound op key model query left hl).trans (inferSound op key model query right hr).symm

theorem wrongOutputRefused : WrongOutputRefused := by
  intro op key model query kernel hwrong hc
  exact hwrong (inferSound op key model query kernel hc)
end Minidregg.Compiler.BfvInferContract

/-- info: 'Minidregg.Compiler.BfvInferContract.inferSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferContract.inferSound

/-- info: 'Minidregg.Compiler.BfvInferContract.uniqueOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferContract.uniqueOutput

/-- info: 'Minidregg.Compiler.BfvInferContract.wrongOutputRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvInferContract.wrongOutputRefused
