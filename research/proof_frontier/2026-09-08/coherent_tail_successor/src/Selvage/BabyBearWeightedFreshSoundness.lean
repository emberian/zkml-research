/- Weighted coherent-query soundness composed with the frozen causal fresh-query
execution certificates. Classical hash coins remain separate from FRI coins. -/
import Selvage.BabyBearWeightedSoundness
import Selvage.CommitmentFailureSoundness
import Selvage.CommitmentExecutionWitness

namespace Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted
open BabyBearExt4 ArityEight.Schedule ArityEight.Schedule.BabyBear
open SuppliedOpeningTrace
open scoped Classical
noncomputable section
variable {Q N q : ℕ} [NeZero N]

set_option maxHeartbeats 2500000 in
/-- Full composed five-round soundness. Initial extraction farness is part
of the event: it is not incorrectly required on every colliding hash tape.
The weighted invariant supplies the stronger FRI tail; the prior fresh-query reduction prices the residual. -/
theorem sound (E : Execution Q N q) (default : Ext4) :
    uniformProb (Coins Q N × External q)
      (fun y => InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2) ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^q+((3*(Q:ℝ)^2+Q)/2+11*Q)/N := by
  let ideal : Coins Q N × External q → Prop := fun y => InitiallyFar E default y.1 ∧
    ArityEight.Schedule.Accepts firstFifteen (extracted (E.checkpoints y.1) default)
      degree q (by decide) y.2.1 y.2.2
  let bad : Coins Q N × External q → Prop := fun y => Failure (E.checkpoints y.1)
    (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2) y.2.1
  have hi : uniformProb (Coins Q N × External q) ideal ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^q := by
    apply uniformProb_prod_le (by positivity)
    intro c
    by_cases hf : InitiallyFar E default c
    · have h := ArityEight.Schedule.BabyBear.Weighted.sound (extracted (E.checkpoints c) default) q hf
      exact le_trans (uniformProb_mono fun _ hx => hx.2) h
    · rw [uniformProb_false (fun _ hx => hf hx.1)]
      positivity
  have hc : ∀ y : Coins Q N × External q,
      InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2 → ideal y ∨ bad y := by
    intro y hy
    let H := cachedSuite (E.strategy y.2) y.1 0
    have hs : CheckpointsLogged (E.checkpoints y.1)
        (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2) y.2.1 := by
      simpa only [executionLog] using checkpointsLogged_append (E.checkpoints y.1) y.2.1 (E.proverLog y.1 y.2)
        (verificationLog H firstFifteen (E.checkpoints y.1) q (by decide) y.2.1 y.2.2
          (E.openings y.1 y.2)) (E.checkpoints_logged y.1 y.2)
    have hl : OpeningsLogged H firstFifteen
        (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2)
        q (by decide) y.2.2 (E.openings y.1 y.2) := by
      simpa only [executionLog] using verificationLog_append_logged H firstFifteen (E.checkpoints y.1) q (by decide)
        y.2.1 y.2.2 (E.openings y.1 y.2) (E.proverLog y.1 y.2)
    have h := supplied_cover (ell := 20) (m := 5) H firstFifteen
      (E.checkpoints y.1) default degree q (by decide) y.2.1 y.2.2 (E.openings y.1 y.2)
      (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2) hs hl (by
        simpa only [Accepts] using hy.2)
    exact h.elim (fun h => Or.inl ⟨hy.1,h⟩) Or.inr
  exact le_trans (le_trans (uniformProb_mono hc) (uniformProb_or_le ideal bad))
    (add_le_add hi (failure_probability E))

/-- If the fixed fresh-query budget is covered by actual retained calls,
the composed bound can be expressed using prover calls plus 720 per query seed. -/
theorem sound_call_budget (E : Execution Q N q) (default : Ext4) (B : ℕ)
    (hP : ∀ c x, (E.proverLog c x).length ≤ B)
    (hcache : ∀ c x e, e ∈ entries (E.strategy x) c →
      e ∈ executionLog E.strategy E.checkpoints E.proverLog E.openings c x) :
    uniformProb (Coins Q N × External q)
      (fun y => InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2) ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^q+
      ((3*((B+720*q:ℕ):ℝ)^2+(B+720*q:ℕ))/2+11*(B+720*q:ℕ))/N := by
  let c : Coins Q N := fun _ => 0
  let x : External q := (fun _ => 0, fun _ => 0)
  have hQ : Q ≤ B+720*q := SuppliedOpeningTrace.BabyBear.fresh_count_le_total
    (E.strategy x) (E.fresh x) c (cachedSuite (E.strategy x) c 0) (E.checkpoints c) q x.1 x.2
    (E.openings c x) (E.proverLog c x) (hP c x) (hcache c x)
  apply le_trans (sound E default)
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Q:ℝ) ≤ (B+720*q:ℕ) := by exact_mod_cast hQ
  have hs : (Q:ℝ)^2 ≤ ((B+720*q:ℕ):ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hc
  linarith

/-- At 312 queries the complete ideal FRI contribution is at most 2^-100;
the finite classical hash residual is still explicitly added. -/
theorem sound_312 (E : Execution Q N 312) (default : Ext4) :
    uniformProb (Coins Q N × External 312)
      (fun y => InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2) ≤
      (1/2^100:ℝ)+((3*(Q:ℝ)^2+Q)/2+11*Q)/N :=
  (sound E default).trans (add_le_add ArityEight.Schedule.BabyBear.Weighted.candidate_312_arithmetic le_rfl)

/-- The existing concrete finite-digest causal execution certificate inhabits
the new composition for every positive digest cardinality. -/
theorem execution_inhabited (N : ℕ) [NeZero N] :
    ∃ E : Execution 1 N 312, ∀ default,
      uniformProb (Coins 1 N × External 312)
        (fun y => InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2) ≤
        (1/2^100:ℝ)+((3*(1:ℝ)^2+1)/2+11)/N := by
  refine ⟨Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution N 312, fun default => ?_⟩
  simpa only [Nat.cast_one,mul_one] using sound_312 (Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution N 312) default

end
end Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound_call_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound_call_budget

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound_312' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.sound_312

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.execution_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Weighted.execution_inhabited

