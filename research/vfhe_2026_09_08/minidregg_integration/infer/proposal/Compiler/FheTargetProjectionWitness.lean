/- Side-effect-free matrix witnesses. Full emitted assignment acceptance is
executed by the separate runner, not claimed by these kernel proofs. -/
import Compiler.FheTargetProjectionVerifier

namespace Minidregg.Compiler.FheTargetProjection
open Minidregg.Compiler.FheRnsScale
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def targetValues (y : ℕ) : Fin 10 → ℕ := fun j => match j.val with
  | 0 => y
  | 1 => y%68719403009
  | 2 => y/68719403009
  | 3 => 68719403008-y%68719403009
  | 4 => y%68719230977
  | 5 => y/68719230977
  | 6 => 68719230976-y%68719230977
  | 7 => y%137438822401
  | 8 => y/137438822401
  | _ => 137438822400-y%137438822401

/-- Nonzero matrix witness with all nineteen-digit group capacities inhabited. -/
theorem captured_matrix_inhabited :
    Balanced (targetValues 172481) ∧
    (∀ i,targetValues 172481 i<64^19) ∧
    (∀ i,readLimbs (targetValues 172481) i=172481) := by
  unfold Balanced
  decide +kernel

/-- The largest canonical source output also inhabits the finite matrix layout. -/
theorem maximum_matrix_inhabited :
    Balanced (targetValues (deployedQ.toNat-1)) ∧
    (∀ i,targetValues (deployedQ.toNat-1) i<64^19) ∧
    (∀ i,readLimbs (targetValues (deployedQ.toNat-1)) i=targetPrime i-1) := by
  unfold Balanced
  decide +kernel

end Minidregg.Compiler.FheTargetProjection

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheTargetProjection.captured_matrix_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.captured_matrix_inhabited

/-- info: 'Minidregg.Compiler.FheTargetProjection.maximum_matrix_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheTargetProjection.maximum_matrix_inhabited
