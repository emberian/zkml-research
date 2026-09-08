/- Composition of the actual five-round supplied verifier with finite classical
fresh hash coins. Hash coins and FRI challenge/query coins are distinct factors.
No Fiat–Shamir or quantum-oracle reduction is asserted. -/
import Selvage.SuppliedScheduleTrace

namespace Minidregg.Selvage.CommitmentFreshTrace.BabyBear
open BabyBearExt4 ArityEight.Schedule ArityEight.Schedule.BabyBear
open SuppliedOpeningTrace
open scoped Classical
noncomputable section

abbrev External (q : ℕ) := (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)
abbrev Coins (Q N : ℕ) := Fin Q → Fin N

def executionLog {Q N q : ℕ} [NeZero N]
    (A : External q → Strategy Ext4 Q N 11)
    (st : Coins Q N → Checkpoints Ext4 (Fin N))
    (P : Coins Q N → External q → EfficientRootOpening.Log Ext4 (Fin N))
    (o : Coins Q N → External q → Openings Ext4 (Fin N) 5 q)
    (c : Coins Q N) (x : External q) :=
  P c x ++ verificationLog (cachedSuite (A x) c 0) firstFifteen (st c) q (by decide) x.1 x.2 (o c x)

/-- Causal execution certificates, all stated as concrete query/log facts.
Fixing the hash tape leaves the checkpoints FRI-prefix adaptive. Fixing the FRI
coins leaves the hash strategy adaptive only in earlier hash answers. -/
structure Execution (Q N q : ℕ) [NeZero N] where
  strategy : External q → Strategy Ext4 Q N 11
  fresh : ∀ x, Fresh (strategy x)
  checkpoints : Coins Q N → Checkpoints Ext4 (Fin N)
  proverLog : Coins Q N → External q → EfficientRootOpening.Log Ext4 (Fin N)
  openings : Coins Q N → External q → Openings Ext4 (Fin N) 5 q
  origins : ∀ c x, Origins (strategy x) c (checkpoints c) x.1
  checkpoints_logged : ∀ c x, CheckpointsLogged (checkpoints c) (proverLog c x) x.1
  covered : ∀ c x e, e ∈ executionLog strategy checkpoints proverLog openings c x →
    e ∈ oracleLog (strategy x) c

variable {Q N q : ℕ} [NeZero N]

def InitiallyFar (E : Execution Q N q) (default : Ext4) (c : Coins Q N) : Prop :=
  EfficientRootOpening.Far_E (2/5:ℝ) 20
    (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
    (E.checkpoints c |>.word 0 (fun i => i.elim0)).1 default
    (E.checkpoints c |>.word 0 (fun i => i.elim0)).2

def Accepts (E : Execution Q N q) (default : Ext4) (c : Coins Q N) (x : External q) : Prop :=
  SuppliedAccepts (cachedSuite (E.strategy x) c 0) firstFifteen (E.checkpoints c) default degree
    q (by decide) x.1 x.2 (E.openings c x)

/-- The observed residual is priced by a derived fresh-query bound, after
conditioning on the separate external challenge/query coins. -/
theorem failure_probability (E : Execution Q N q) :
    uniformProb (Coins Q N × External q) (fun y => Failure (E.checkpoints y.1)
      (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2) y.2.1) ≤
      ((3*(Q:ℝ)^2+Q)/2+11*Q)/N := by
  have h := uniformProb_equiv (Equiv.prodComm (Coins Q N) (External q))
    (fun y => Failure (E.checkpoints y.2)
      (executionLog E.strategy E.checkpoints E.proverLog E.openings y.2 y.1) y.1.1)
  simp only [Equiv.prodComm_apply,Prod.swap] at h
  rw [h]
  apply uniformProb_prod_le (by positivity)
  intro x
  exact oracle_schedule_failure_probability (E.strategy x) (E.fresh x) E.checkpoints
    (fun _ => x.1) (fun c => executionLog E.strategy E.checkpoints E.proverLog E.openings c x)
    (fun c => E.origins c x) (fun c => E.covered c x)

set_option maxHeartbeats 2500000 in
/-- Full composed five-round soundness. Initial extraction farness is part
of the event: it is not incorrectly required on every colliding hash tape.
The FRI term is inherited unchanged; the observed residual is now discharged. -/
theorem sound (E : Execution Q N q) (default : Ext4) :
    uniformProb (Coins Q N × External q)
      (fun y => InitiallyFar E default y.1 ∧ Accepts E default y.1 y.2) ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q+((3*(Q:ℝ)^2+Q)/2+11*Q)/N := by
  let ideal : Coins Q N × External q → Prop := fun y => InitiallyFar E default y.1 ∧
    ArityEight.Schedule.Accepts firstFifteen (extracted (E.checkpoints y.1) default)
      degree q (by decide) y.2.1 y.2.2
  let bad : Coins Q N × External q → Prop := fun y => Failure (E.checkpoints y.1)
    (executionLog E.strategy E.checkpoints E.proverLog E.openings y.1 y.2) y.2.1
  have hi : uniformProb (Coins Q N × External q) ideal ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q := by
    apply uniformProb_prod_le (by positivity)
    intro c
    by_cases hf : InitiallyFar E default c
    · have h := terminal_sound (extracted (E.checkpoints c) default) q hf
      norm_num at h
      exact le_trans (uniformProb_mono fun _ hx => hx.2) (by simpa only [Nat.cast_pow] using h)
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
      (1198336:ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q+
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

end
end Minidregg.Selvage.CommitmentFreshTrace.BabyBear

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.failure_probability

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.sound

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.sound_call_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.sound_call_budget
