/-
[DERIVED independent review tooth; EXECUTED after compilation]
The actual canonical captured row has deterministic source output 172481.
Replacing that deterministic formula by the diagnostic nearest-or-nearest+1
envelope admits 172480, including as a canonical target residue. This is a
refutation only of that weakened certificate relation, not of the checked
source decomposition, Rust encryption, or decryption correctness.
ATLAS positive pole: the source instance's actual inhabited canonical row.
Negative pole: the other integer inside its own one-unit envelope.
-/
import Compiler.FheRnsScaleDecomposition

namespace Minidregg.Compiler.BFVEnvelopeSeamReview
open Minidregg.Compiler.FheRnsScale
set_option autoImplicit false

def envelopeAdmits (r : Fin 6 → ℤ) (y : ℤ) : Prop :=
  roundDiv (deployedT * selectedLift deployedP r deployedGarner (deployedV r)) deployedQ ≤ y ∧
  y ≤ roundDiv (deployedT * selectedLift deployedP r deployedGarner (deployedV r)) deployedQ + 1

def exactSourceResidue (r : Fin 6 → ℤ) (y : ℤ) : Prop :=
  y = deployedOutput r % deployedQ

theorem same_row_envelope_admits_wrong_source_residue :
    (∀ i : Fin 6, 0 ≤ capturedResidues i ∧ capturedResidues i < deployedBase i) ∧
    envelopeAdmits capturedResidues 172480 ∧
    (0 : ℤ) ≤ 172480 ∧ (172480 : ℤ) < deployedQ ∧
    ¬ exactSourceResidue capturedResidues 172480 ∧
    exactSourceResidue capturedResidues 172481 := by
  obtain ⟨canonical, _, computed, nearest⟩ := deployed_witness_inhabited
  refine ⟨canonical, ?_, by decide, by decide, ?_, ?_⟩
  · unfold envelopeAdmits
    rw [nearest]
    constructor <;> decide
  · unfold exactSourceResidue
    rw [computed]
    decide
  · unfold exactSourceResidue
    rw [computed]
    decide

/-- info: 'Minidregg.Compiler.BFVEnvelopeSeamReview.same_row_envelope_admits_wrong_source_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms same_row_envelope_admits_wrong_source_residue

end Minidregg.Compiler.BFVEnvelopeSeamReview
