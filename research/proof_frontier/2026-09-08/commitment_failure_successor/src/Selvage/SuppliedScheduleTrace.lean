/- Constructed supplied-path verification logs and finite-schedule accounting.
This discharges opening-log inclusion from actual instrumented verifier runs. -/
import Selvage.SuppliedOpeningTrace

namespace Minidregg.Selvage.SuppliedOpeningTrace
open ArityEight.Schedule
open scoped Classical
variable {F Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest] {ell m : ℕ}

/-- Run every actually supplied row once and retain its emitted records. -/
def verificationLog (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) : EfficientRootOpening.Log F Digest :=
  (List.ofFn fun j : Fin m => (List.ofFn fun a : Fin q =>
    (rowRun H (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
      (T.data (3*j.val+2) (by omega))
      (st.word j (friPrefix r j (by omega))).2 (st.input j (friPrefix r j (by omega))).2
      (st.word (j+1) (friPrefix r (j+1) (by omega))).2
      (r j) (roundQueries hell j seed a) (o j a)).2).flatten).flatten

theorem verificationLog_contains (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) (j : Fin m) (a : Fin q)
    (e : EfficientRootOpening.Query F Digest × Digest)
    (he : e ∈ (rowRun H (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
      (T.data (3*j.val+2) (by omega))
      (st.word j (friPrefix r j (by omega))).2 (st.input j (friPrefix r j (by omega))).2
      (st.word (j+1) (friPrefix r (j+1) (by omega))).2
      (r j) (roundQueries hell j seed a) (o j a)).2) :
    e ∈ verificationLog H T st q hell r seed o :=
  List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,
    List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨a,rfl⟩,he⟩⟩

/-- Existing OpeningsLogged is now a theorem of the constructed verifier log. -/
theorem verificationLog_logged (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) :
    OpeningsLogged H T (verificationLog H T st q hell r seed o) q hell seed o := by
  intro j a
  have h := rowRun_logged H (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
    (T.data (3*j.val+2) (by omega))
    (st.word j (friPrefix r j (by omega))).2 (st.input j (friPrefix r j (by omega))).2
    (st.word (j+1) (friPrefix r (j+1) (by omega))).2
    (r j) (roundQueries hell j seed a) (o j a)
  exact ⟨fun c b d e he => verificationLog_contains H T st q hell r seed o j a e (h.1 c b d e he),
    fun e he => verificationLog_contains H T st q hell r seed o j a e (h.2.1 e he),
    fun e he => verificationLog_contains H T st q hell r seed o j a e (h.2.2 e he)⟩

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
/-- Finite concatenation preserves the sum of the per-entry record bounds. -/
theorem flatten_ofFn_length_le {α : Type} {n : ℕ} (L : Fin n → List α) (b : Fin n → ℕ)
    (hb : ∀ i, (L i).length ≤ b i) : (List.ofFn L).flatten.length ≤ ∑ i, b i := by
  simp only [List.length_flatten,List.map_ofFn,List.sum_ofFn]
  exact Finset.sum_le_sum fun i _ => hb i

/-- The bound includes every supplied source, input and next-word path. -/
theorem verificationLog_length_le (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) :
    (verificationLog H T st q hell r seed o).length ≤
      ∑ j : Fin m, q*(8*(ell-3*j.val+1)+2*(ell-3*(j.val+1)+1)) := by
  apply flatten_ofFn_length_le
  intro j
  calc
    _ ≤ ∑ _a : Fin q, (8*(ell-3*j.val+1)+2*(ell-3*(j.val+1)+1)) := by
      apply flatten_ofFn_length_le
      intro a
      exact rowRun_length_le H (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
        (T.data (3*j.val+2) (by omega)) _ _ _ (r j) (roundQueries hell j seed a) (o j a)
    _ = _ := by simp

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
/-- All checkpoint roots used by m rounds: m+1 words and m injected inputs.
This list alone is not a causal declaration schedule; Origins still enforces timing. -/
def checkpointRoots (st : Checkpoints F Digest) (r : Fin m → F) : List Digest :=
  (List.ofFn fun n : Fin (m+1) => (st.word n (friPrefix r n (by omega))).2) ++
    (List.ofFn fun j : Fin m => (st.input j (friPrefix r j (by omega))).2)

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
theorem checkpointRoots_length (st : Checkpoints F Digest) (r : Fin m → F) :
    (checkpointRoots st r).length = 2*m+1 := by simp [checkpointRoots]; omega

/-- Appending constructed verification records discharges the existing path-log premise. -/
theorem verificationLog_append_logged (H : BinaryMerkle.HashSuite F Digest)
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m)) (st : Checkpoints F Digest)
    (q : ℕ) (hell : 3*m ≤ ell) (r : Fin m → F) (seed : Fin q → PowerTwoFriLevels ell 1)
    (o : Openings F Digest m q) (P : EfficientRootOpening.Log F Digest) :
    OpeningsLogged H T (P++verificationLog H T st q hell r seed o) q hell seed o := by
  intro j a
  have h := verificationLog_logged H T st q hell r seed o j a
  exact ⟨fun c b d e he => List.mem_append.mpr (Or.inr (h.1 c b d e he)),
    fun e he => List.mem_append.mpr (Or.inr (h.2.1 e he)),
    fun e he => List.mem_append.mpr (Or.inr (h.2.2 e he))⟩

omit [Field F] [DecidableEq F] [DecidableEq Digest] in
theorem checkpointsLogged_append (st : Checkpoints F Digest) (r : Fin m → F)
    (P L : EfficientRootOpening.Log F Digest) (h : CheckpointsLogged st P r) :
    CheckpointsLogged st (P++L) r :=
  ⟨fun n hn e he => List.mem_append.mpr (Or.inl (h.1 n hn e he)),
    fun j e he => List.mem_append.mpr (Or.inl (h.2 j e he))⟩

end Minidregg.Selvage.SuppliedOpeningTrace

namespace Minidregg.Selvage.SuppliedOpeningTrace.BabyBear
open ArityEight.Schedule ArityEight.Schedule.BabyBear BabyBearExt4
variable {Digest : Type} [DecidableEq Digest]

/-- Actual five-round scalar verifier records: 204+174+144+114+84 = 720 per seed. -/
theorem verificationLog_length_le (H : BinaryMerkle.HashSuite Ext4 Digest) (st : Checkpoints Ext4 Digest)
    (q : ℕ) (r : Fin 5 → Ext4) (seed : Fin q → PowerTwoFriLevels 20 1) (o : Openings Ext4 Digest 5 q) :
    (verificationLog H firstFifteen st q (by decide) r seed o).length ≤ 720*q := by
  have h := SuppliedOpeningTrace.verificationLog_length_le H firstFifteen st q (by decide) r seed o
  have hb : (∑ j : Fin 5, q*(8*(20-3*j.val+1)+2*(20-3*(j.val+1)+1))) = 720*q := by
    simp only [Fin.sum_univ_succ]
    norm_num
    ring
  rw [hb] at h
  exact h

/-- All fresh cache entries are charged either to the prover/preprocessing
call log or to the actual five-round supplied verifier log. -/
theorem fresh_count_le_total {Q N R B : ℕ} (A : CommitmentFreshTrace.Strategy Ext4 Q N R)
    (hf : CommitmentFreshTrace.Fresh A) (c : Fin Q → Fin N)
    (H : BinaryMerkle.HashSuite Ext4 (Fin N)) (st : Checkpoints Ext4 (Fin N))
    (q : ℕ) (r : Fin 5 → Ext4) (seed : Fin q → PowerTwoFriLevels 20 1) (o : Openings Ext4 (Fin N) 5 q)
    (P : EfficientRootOpening.Log Ext4 (Fin N)) (hP : P.length ≤ B)
    (hcover : ∀ e ∈ CommitmentFreshTrace.entries A c,
      e ∈ P++verificationLog H firstFifteen st q (by decide) r seed o) : Q ≤ B+720*q := by
  have h := CommitmentFreshTrace.fresh_count_le_calls A hf c _ hcover
  have hv := verificationLog_length_le H st q r seed o
  rw [List.length_append] at h
  omega

end Minidregg.Selvage.SuppliedOpeningTrace.BabyBear

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_contains

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_logged

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.flatten_ofFn_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.flatten_ofFn_length_le

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_length_le

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.checkpointRoots_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.checkpointRoots_length

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_append_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.verificationLog_append_logged

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.checkpointsLogged_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.checkpointsLogged_append

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.BabyBear.verificationLog_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.BabyBear.verificationLog_length_le

/-- info: 'Minidregg.Selvage.SuppliedOpeningTrace.BabyBear.fresh_count_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.SuppliedOpeningTrace.BabyBear.fresh_count_le_total
