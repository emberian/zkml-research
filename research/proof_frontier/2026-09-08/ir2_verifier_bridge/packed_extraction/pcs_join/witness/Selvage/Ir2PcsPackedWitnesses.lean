/- Actual PCS join premises on fixed zero input rows and false opening claims.
This instantiates the PCS/packed probability head; it makes no deployed sponge claim. -/
import Selvage.Ir2PcsPackedSoundness
import Selvage.Ir2PackedWitnesses

namespace Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses
open BabyBearExt4 Ir2FriSchedule Packed Polynomial
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Actual fixed input checkpoints, zero off-domain points and false one-valued claims. -/
def plan : CommitmentPlan ℕ where
  input := Packed.Witnesses.checkpoints.input
  points _ _ _ := 0
  claims _ _ _ _ := 1
  fri _ := Packed.Witnesses.checkpoints.fri
  final _ := Packed.Witnesses.checkpoints.final

def supplied (_ : ChallengeSpace) : Openings ℕ 38 := Packed.Witnesses.openings 38
def retained (_ : ChallengeSpace) : Packed.Log ℕ := Packed.Witnesses.checkpointLog

/-- Statement-first inhabitation of all concrete premises of the actual PCS join. -/
def JoinPremises : Prop :=
  (∀ x,CheckpointsLogged (plan.atAlpha x.1) x.2.1 (retained x)) ∧
  (data plan.rows plan.points plan.claims).OffDomain (domain 0) 31 ∧
  ¬JointColumnsNear plan.rows plan.points plan.claims (degree 0) (2/5)

/-- Every source row is the zero row pinned by the actual salted input-leaf paths. -/
theorem rows_zero (i : Index 0) : plan.rows i = fun _ _ _ => 0 := by
  have hg : ¬Failure Packed.Witnesses.checkpoints (fun _ => 0) Packed.Witnesses.checkpointLog := by
    have h := Packed.Witnesses.no_failure 0 (fun _ => 0) (fun a => a.elim0)
    simpa [verificationLog,List.ofFn_zero] using h
  have hp := input_rows_pin Packed.Witnesses.hash Packed.Witnesses.checkpoints
    Packed.Witnesses.checkpointLog (fun _ => 0) (sourceEquiv.symm i) Packed.Witnesses.queryOpening
    (Packed.Witnesses.checkpoints_logged _) hg
    (fun b e he => Packed.Witnesses.path_log_mem 17 (sourceEquiv.symm i) _
      (Packed.Witnesses.input_leaf_mem b) e he)
    (Packed.Witnesses.paths_accept _ (sourceEquiv.symm i))
  exact hp

/-- Zero points are outside the actual multiplicative coset31 domain. -/
theorem off_domain : (data plan.rows plan.points plan.claims).OffDomain (domain 0) 31 := by
  intro j i
  change (0:Ext4) ≠ 31*domain 0 i
  have hd : domain 0 i ≠ 0 := by
    rw [native_domain_source]
    exact pow_ne_zero _ (TwoAdic.omega_ne_zero _ (by decide))
  exact (mul_ne_zero coset31_ne_zero hd).symm

/-- The original physical input polynomial is zero in every actual input column. -/
theorem originals_exact (k : Column) (i : Index 0) :
    (0 : Ext4[X]).eval (31*domain 0 i) =
      algebraMap BabyBear Ext4 (plan.rows i k.1 k.2.1 k.2.2) := by
  rw [rows_zero]
  simp

/-- One exact-source claim is false, excluding every common nearby-column explanation. -/
theorem wrong_claims_not_joint :
    ¬JointColumnsNear plan.rows plan.points plan.claims (degree 0) (2/5) := by
  apply not_joint_columns_of_wrong_claim plan.rows plan.points plan.claims
    (fun _ => (0 : Ext4[X])) (by intro k; simp) originals_exact
    (⟨0,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩⟩ : Term)
  change (1:Ext4) ≠ (0 : Ext4[X]).eval 0
  simp

/-- Fixed actual input and FRI checkpoint logs are retained at every alpha/beta prefix. -/
theorem checkpoints_logged (x : ChallengeSpace) :
    CheckpointsLogged (plan.atAlpha x.1) x.2.1 (retained x) :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

/-- All three actual-join premises are simultaneously inhabited. -/
theorem join_premises_inhabited : JoinPremises :=
  ⟨checkpoints_logged,off_domain,wrong_claims_not_joint⟩

/-- Teeth: correcting the claims to zero restores the joint explanation on the entire domain. -/
theorem zero_claims_joint : JointColumnsNear plan.rows plan.points
    (fun _ _ _ _ => 0) (degree 0) (2/5) := by
  refine ⟨Finset.univ,?_,(fun _ => (0 : Ext4[X])),?_,?_⟩
  · norm_num [Index,stage]
  · intro k
    exact ⟨by simp,fun i _ => originals_exact k i⟩
  · intro t
    simp

/-- The actual PCS/packed soundness head fires on these fixed logged commitments and false claims. -/
theorem sound_fires :
    uniformProb ChallengeSpace (Accepted Packed.Witnesses.hash plan supplied) ≤
      (690880504:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38+
      uniformProb ChallengeSpace (ObservedFailure Packed.Witnesses.hash plan supplied retained) :=
  packed_pcs_soundness Packed.Witnesses.hash plan supplied retained
    checkpoints_logged off_domain wrong_claims_not_joint

end
end Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.rows_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.rows_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.off_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.off_domain

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.originals_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.originals_exact

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.wrong_claims_not_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.wrong_claims_not_joint

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.checkpoints_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.checkpoints_logged

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.join_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.join_premises_inhabited

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.zero_claims_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.zero_claims_joint

/-- info: 'Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Pcs.PackedWitnesses.sound_fires
