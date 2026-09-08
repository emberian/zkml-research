/- A finite-digest execution inhabits every causal/log certificate, for any
number of supplied queries. Missing paths are rejected by the actual checker. -/
import Selvage.CommitmentFailureSoundness

namespace Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness
open BabyBearExt4 ArityEight ArityEight.Schedule ArityEight.Schedule.BabyBear
open SuppliedOpeningTrace
open scoped Classical
noncomputable section

variable (N : ℕ) [NeZero N]

def one : Strategy Ext4 1 N 11 where
  query _ _ := .leaf 0
  roots _ _ := []
  roots_le _ _ := by simp

omit [NeZero N] in
theorem one_fresh : Fresh (one N) := fun _ _ _ _ => Subsingleton.elim _ _

def checkpoints (c : Coins 1 N) : Checkpoints Ext4 (Fin N) where
  word _ _ := (entries (one N) c,c 0)
  input _ _ := (entries (one N) c,c 0)

def emptyRow : RowOpening Ext4 (Fin N) := ⟨fun _ _ _ => ⟨0,[]⟩,⟨0,[]⟩,⟨0,[]⟩⟩

omit [NeZero N] in
theorem all_origin (c : Coins 1 N) :
    CheckpointOrigin (one N) c (entries (one N) c) (c 0) := by
  refine ⟨1,le_rfl,?_,?_⟩
  · intro e
    rw [mem_entries_iff,mem_prefixLog_iff]
    constructor
    · rintro ⟨t,ht⟩; exact ⟨t,t.isLt,ht⟩
    · rintro ⟨t,_,ht⟩; exact ⟨t,ht⟩
  · intro t ht
    omega

omit [NeZero N] in
theorem pathLog_nil {Value Digest : Type} (H : BinaryMerkle.HashSuite Value Digest)
    (v : Digest) {k : ℕ} (a : Fin k → Bool) : EfficientRootOpening.pathLog H v a [] = [] := by
  cases k <;> rfl

omit [NeZero N] in
/-- A malformed empty path still records its supplied leaf hash, exactly once. -/
theorem empty_row_log {k₀ k₁ k₂ k₃ : ℕ}
    {d₀ : Fin (2^k₀) ↪ Ext4} {d₁ : Fin (2^k₁) ↪ Ext4}
    {d₂ : Fin (2^k₂) ↪ Ext4} {d₃ : Fin (2^k₃) ↪ Ext4}
    (H : BinaryMerkle.HashSuite Ext4 (Fin N))
    (D₀ : FoldingData Ext4 d₀ d₁) (D₁ : FoldingData Ext4 d₁ d₂) (D₂ : FoldingData Ext4 d₂ d₃)
    (rs rg rn : Fin N) (β : Ext4) (i : Fin (2^k₃)) (e : EfficientRootOpening.Query Ext4 (Fin N) × Fin N) :
    e ∈ (rowRun H D₀ D₁ D₂ rs rg rn β i (emptyRow N)).2 ↔ e = (.leaf 0,H.leaf 0) := by
  simp [rowRun,sourceRuns,emptyRow,pointRun,openingRun_eq,EfficientRootOpening.openingLog,pathLog_nil]

theorem leaf_answer (c : Coins 1 N) : (cachedSuite (one N) c 0).leaf 0 = c 0 :=
  cachedSuite_entry (one N) (one_fresh N) c 0 0

/-- Every generated verifier record is a replay of the sole counted leaf query. -/
theorem verification_covered (q : ℕ) (c : Coins 1 N) (x : External q) :
    LogCovered (one N) c (verificationLog (cachedSuite (one N) c 0) firstFifteen
      (checkpoints N c) q (by decide) x.1 x.2 (fun _ _ => emptyRow N)) := by
  intro e he
  obtain ⟨L,hL,he⟩ := List.mem_flatten.mp he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hL
  obtain ⟨L,hL,he⟩ := List.mem_flatten.mp he
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hL
  have hh := (empty_row_log N _ _ _ _ _ _ _ _ _ e).mp he
  rw [leaf_answer] at hh
  rw [hh]
  exact List.mem_ofFn.mpr ⟨0,rfl⟩

/-- All concrete execution premises are inhabited over a finite digest alphabet.
The supplied empty paths are deliberately invalid; this is a rejection control. -/
def execution (q : ℕ) : Execution 1 N q where
  strategy _ := one N
  fresh _ := one_fresh N
  checkpoints := checkpoints N
  proverLog c _ := entries (one N) c
  openings _ _ _ _ := emptyRow N
  origins c _ := ⟨fun _ _ => all_origin N c,fun _ => all_origin N c⟩
  checkpoints_logged _ _ := ⟨fun _ _ _ he => he,fun _ _ he => he⟩
  covered c x e he := by
    rw [oracleLog_eq_entries (one N) (one_fresh N) c]
    rcases List.mem_append.mp he with hp | hv
    · exact hp
    · exact verification_covered N q c x e hv

/-- The prover log has one call; all counted cache entries occur in it. -/
theorem execution_call_premises (q : ℕ) :
    (∀ c x, ((execution N q).proverLog c x).length ≤ 1) ∧
    (∀ c x e, e ∈ entries ((execution N q).strategy x) c →
      e ∈ executionLog (execution N q).strategy (execution N q).checkpoints
        (execution N q).proverLog (execution N q).openings c x) := by
  constructor
  · intro c x
    simp [execution,entries]
  · intro c x e he
    exact List.mem_append.mpr (Or.inl he)

/-- An actually supplied positive query count fails on the absent source path. -/
theorem execution_rejects {q : ℕ} (hq : 0 < q) (default : Ext4)
    (c : Coins 1 N) (x : External q) : ¬Accepts (execution N q) default c x := by
  intro ha
  have h := ha.2 (0 : Fin 5) (⟨0,hq⟩ : Fin q)
  have hp := h.1 false false false
  change BinaryMerkle.recompute _ _ _ [] = some _ at hp
  simp [BinaryMerkle.recompute] at hp

end
end Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.one_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.one_fresh

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.all_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.all_origin

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.pathLog_nil' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.pathLog_nil

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.empty_row_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.empty_row_log

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.leaf_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.leaf_answer

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.verification_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.verification_covered

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution_call_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution_call_premises

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.BabyBear.Witness.execution_rejects
