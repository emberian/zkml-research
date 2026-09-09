import Compiler.BfvRescaleRow

namespace Minidregg.Compiler.BfvRescaleRow
open Minidregg.Compiler
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.AirSimplify
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

/-- A cheap semantic premise witness for the exact two joined matrices. The
large source assignment is exercised by the executable producer, not kernel-normalized. -/
def JoinedMatrices (s : Fin 21 → Nat) (t : Fin 10 → Nat) : Prop :=
  FheSourceCertificate.Balanced s ∧ FheTargetProjection.Balanced t ∧ s 18 = t 0

def JoinedMatricesSound : Prop := ∀ s t,JoinedMatrices s t →
  ∀ i,(FheTargetProjection.readLimbs t i : Int) = FheRnsScale.deployedOutput (FheSourceCertificate.readResidues s) % (FheTargetProjection.targetPrime i : Int)

def WrongNearestExcluded : Prop := ∀ (asg : Fin nVars → BabyBear),
  residues asg = FheRnsScale.capturedResidues → output asg 0 = 172480 →
  ¬ systemAccepts asg system

theorem joinedMatricesSound : JoinedMatricesSound := by
  intro s t h
  obtain ⟨hs,ht,hy⟩ := h
  have hc := FheSourceCertificate.balanced_output_forced s hs
  rw [hy] at hc
  exact FheTargetProjection.projection_source _ _ _ _ _ hc (FheTargetProjection.balanced_projection t ht)

theorem joinedMatricesInhabited : ∃ s t,JoinedMatrices s t ∧
    s 18 = 172481 ∧ ∀ i,FheTargetProjection.readLimbs t i = 172481 := by
  refine ⟨FheSourceCertificate.sourceValues FheRnsScale.capturedResidues,FheTargetProjection.targetValues 172481,?_,
    FheSourceCertificate.captured_balance_inhabited.2.2,FheTargetProjection.captured_matrix_inhabited.2.2⟩
  exact ⟨FheSourceCertificate.captured_balance_inhabited.1,FheTargetProjection.captured_matrix_inhabited.1,
    FheSourceCertificate.captured_balance_inhabited.2.2⟩

theorem wrongNearestExcluded : WrongNearestExcluded := by
  intro asg hr ho hs
  have h := rowSound asg hs 0
  rw [hr,ho,FheRnsScale.deployed_witness_inhabited.2.2.1] at h
  norm_num [FheTargetProjection.targetPrime] at h

theorem simplifiedSource_sound (asg : Fin nVars → BabyBear)
    (h : systemAccepts asg (simplifySystem system)) :
    ∀ i,(output asg i : Int) = FheRnsScale.deployedOutput (residues asg) % (FheTargetProjection.targetPrime i : Int) :=
  rowSound asg ((simplifySystem_accepts_iff asg system).mp h)

/-- info: 'Minidregg.Compiler.BfvRescaleRow.joinedMatricesSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms joinedMatricesSound
/-- info: 'Minidregg.Compiler.BfvRescaleRow.joinedMatricesInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms joinedMatricesInhabited
/-- info: 'Minidregg.Compiler.BfvRescaleRow.wrongNearestExcluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrongNearestExcluded
/-- info: 'Minidregg.Compiler.BfvRescaleRow.simplifiedSource_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simplifiedSource_sound

end Minidregg.Compiler.BfvRescaleRow
