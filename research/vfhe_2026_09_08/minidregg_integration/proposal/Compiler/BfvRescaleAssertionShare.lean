/- Actual rescale source consumes the generic pass, retaining its existing
integer row theorem and all public input/output coordinates. -/
import Compiler.AirAssertionShare
import Compiler.BfvRescaleRow

namespace Minidregg.Compiler.BfvRescaleAssertionShare
open Minidregg.Compiler
open Minidregg.Compiler.BfvRescaleRow
open Minidregg.Compiler.NativeKernelPlan
set_option autoImplicit false

def sharedSystem : ConstraintSystem BabyBear (Fin nVars) :=
  AirAssertionShare.optimize system

def PreservesRescale : Prop := ∀ asg : Fin nVars → BabyBear,
  systemAccepts asg sharedSystem ↔ systemAccepts asg system

theorem sharedSystem_accepts_iff : PreservesRescale := by
  intro asg
  exact AirAssertionShare.optimize_preserves asg system

theorem sharedSystem_sound (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg sharedSystem) : ∀ i,
    (output asg i : Int) = FheRnsScale.deployedOutput (residues asg) %
      (FheTargetProjection.targetPrime i : Int) :=
  rowSound asg ((sharedSystem_accepts_iff asg).mp h)

end Minidregg.Compiler.BfvRescaleAssertionShare

-- Exact axiom outputs from the checked declarations.

/-- info: 'Minidregg.Compiler.BfvRescaleAssertionShare.sharedSystem_accepts_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvRescaleAssertionShare.sharedSystem_accepts_iff

/-- info: 'Minidregg.Compiler.BfvRescaleAssertionShare.sharedSystem_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.BfvRescaleAssertionShare.sharedSystem_sound
