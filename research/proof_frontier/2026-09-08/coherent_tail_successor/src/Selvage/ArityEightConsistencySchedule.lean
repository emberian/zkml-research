/- Prefix-adaptive consistency weights and a threshold-preserving finite
challenge invariant, on the existing arity-eight schedule APIs. -/
import Selvage.FoldingConsistencyWeights
import Selvage.ConsistencyMask
import Selvage.ArityEightSchedule

namespace Minidregg.Selvage.ArityEight.Schedule
open scoped BigOperators Classical
variable {F : Type} [Field F] [DecidableEq F] {ell m : ℕ}

/-- Weights depend only on the same prior scalar prefix as their source word. -/
noncomputable def prefixConsistency (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) :
    (n : ℕ) → n ≤ m → (Fin n → F) → PowerTwoFriLevels ell (3*n) → ℝ
  | 0, _, _ => fun _ => 1
  | n+1, hn, p =>
    let j : Fin m := ⟨n,by omega⟩
    let prior : Fin n → F := fun i => p i.castSucc
    maskConsistency (projectConsistency8 (T.data (3*n) (by omega))
      (T.data (3*n+1) (by omega)) (T.data (3*n+2) (by omega))
      (prefixConsistency T s n (by omega) prior))
      (s.word (n+1) p) (literal T s j prior (p (Fin.last n)))

noncomputable def consistencyAt (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) (n : ℕ) (hn : n ≤ m) :=
  prefixConsistency T s n hn (friPrefix r n hn)

theorem prefixConsistency_nonneg (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (n : ℕ) (hn : n ≤ m) (p : Fin n → F) :
    ∀ i, 0 ≤ prefixConsistency T s n hn p i := by
  induction n with
  | zero => intro i; simp [prefixConsistency]
  | succ n ih =>
    exact maskConsistency_nonneg _ (projectConsistency8_nonneg _ _ _ _ (ih (by omega) _)) _ _

theorem prefixConsistency_le_one (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (n : ℕ) (hn : n ≤ m) (p : Fin n → F) :
    ∀ i, prefixConsistency T s n hn p i ≤ 1 := by
  induction n with
  | zero => intro i; simp [prefixConsistency]
  | succ n ih =>
    exact maskConsistency_le_one _ (projectConsistency8_le_one _ _ _ _ (ih (by omega) _)) _ _

/-- Exact recurrence on a completed challenge vector, with no future-query argument. -/
theorem consistencyAt_succ (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (r : Fin m → F) (j : Fin m) :
    consistencyAt T s r (j.val+1) (by omega) =
      maskConsistency (projectConsistency8 (T.data (3*j.val) (by omega))
        (T.data (3*j.val+1) (by omega)) (T.data (3*j.val+2) (by omega))
        (consistencyAt T s r j (by omega)))
        (s.wordAt r (j+1) (by omega)) (blockAt T s j r) := rfl

/-- This bad event changes the weighted threshold across one fresh scalar. -/
def WeightedBadRound (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (θ : ℝ) (j : Fin m) (r : Fin m → F) : Prop :=
  ¬WeightedClose (reedSolomonCode (T.dom (3*j.val)) (deg j)) θ
      (consistencyAt T s r j (by omega)) (s.wordAt r j (by omega)) ∧
  WeightedClose (reedSolomonCode (T.dom (3*(j.val+1))) (deg (j+1))) θ
    (projectConsistency8 (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
      (T.data (3*j.val+2) (by omega)) (consistencyAt T s r j (by omega))) (blockAt T s j r)

theorem weighted_bad_round_bound [Fintype F]
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (θ : ℝ)
    (j : Fin m) (hd : 1 ≤ deg (j+1)) (hdeg : deg j = 8*deg (j+1)) (hθ : 0 < θ)
    (hrate : (deg (j+1):ℝ) < (1-2*θ)*(Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ)) :
    uniformProb (Fin m → F) (WeightedBadRound T s deg θ j) ≤
      ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F := by
  apply prefix_challenge_bound j (fun p β =>
    ¬WeightedClose (reedSolomonCode (T.dom (3*j.val)) (deg j)) θ
      (prefixConsistency T s j (by omega) p) (s.word j p) ∧
    WeightedClose (reedSolomonCode (T.dom (3*(j.val+1))) (deg (j+1))) θ
      (projectConsistency8 (T.data (3*j.val) (by omega)) (T.data (3*j.val+1) (by omega))
        (T.data (3*j.val+2) (by omega)) (prefixConsistency T s j (by omega) p))
      (literal T s j p β)) (by positivity)
  intro p
  by_cases hf : WeightedClose (reedSolomonCode (T.dom (3*j.val)) (deg j)) θ
      (prefixConsistency T s j (by omega) p) (s.word j p)
  · rw [uniformProb_false (fun _ h => h.1 hf)]
    positivity
  · have hf' : ¬WeightedClose (reedSolomonCode (T.dom (3*j.val)) (8*deg (j+1))) θ
        (prefixConsistency T s j (by omega) p) (s.word j p) := by simpa only [←hdeg] using hf
    exact le_trans (uniformProb_mono fun _ h => h.2)
      (fold8_injected_weighted_sound (T.data (3*j.val) (by omega))
        (T.data (3*j.val+1) (by omega)) (T.data (3*j.val+2) (by omega)) hd hθ hrate
        (prefixConsistency T s j (by omega) p) (prefixConsistency_le_one T s j (by omega) p)
        (s.word j p) (s.input j p) hf')

theorem weighted_bad_schedule_bound [Fintype F]
    (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (θ : ℝ)
    (hd : ∀ j : Fin m, 1 ≤ deg (j+1)) (hdeg : ∀ j : Fin m, deg j = 8*deg (j+1)) (hθ : 0 < θ)
    (hrate : ∀ j : Fin m, (deg (j+1):ℝ) <
      (1-2*θ)*(Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℝ)) :
    uniformProb (Fin m → F) (fun r => ∃ j, WeightedBadRound T s deg θ j r) ≤
      ∑ j : Fin m, ((8*Fintype.card (PowerTwoFriLevels ell (3*(j.val+1))):ℕ):ℝ)/Fintype.card F := by
  exact le_trans (uniformProb_exists_le _)
    (Finset.sum_le_sum fun j _ => weighted_bad_round_bound T s deg θ j (hd j) (hdeg j) hθ (hrate j))

/-- No radius is spent per transition: absence of the proved bad events
preserves weighted nonagreement from the initial word to every prefix. -/
theorem weighted_invariant (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (θ : ℝ)
    (hfar : ¬close θ (reedSolomonCode (T.dom 0) (deg 0)) (s.word 0 (fun i => i.elim0)))
    (r : Fin m → F) (hgood : ¬∃ j, WeightedBadRound T s deg θ j r) (n : ℕ) (hn : n ≤ m) :
    ¬WeightedClose (reedSolomonCode (T.dom (3*n)) (deg n)) θ
      (consistencyAt T s r n hn) (s.wordAt r n hn) := by
  induction n with
  | zero =>
    intro h
    apply hfar
    have hp : friPrefix r 0 hn = (fun i => i.elim0) := Subsingleton.elim _ _
    simpa only [Words.wordAt,hp] using weightedClose_one_to_close _ θ _ h
  | succ n ih =>
    intro h
    let j : Fin m := ⟨n,by omega⟩
    apply hgood
    refine ⟨j,ih (by omega),?_⟩
    rw [consistencyAt_succ T s r j] at h
    exact weightedClose_mask_transfer _ θ _ _ _ h

/-- A legal terminal word has strictly less than (1−θ) total consistency
mass off the derived challenge bad event. Query transport is a separate theorem. -/
theorem terminal_consistency_mass_lt (T : FoldingTower F (PowerTwoFriLevels ell) (3*m))
    (s : Words F (PowerTwoFriLevels ell)) (deg : ℕ → ℕ) (θ : ℝ)
    (hfar : ¬close θ (reedSolomonCode (T.dom 0) (deg 0)) (s.word 0 (fun i => i.elim0)))
    (r : Fin m → F) (hgood : ¬∃ j, WeightedBadRound T s deg θ j r)
    (hterminal : s.wordAt r m le_rfl ∈ reedSolomonCode (T.dom (3*m)) (deg m)) :
    consistencyMass (consistencyAt T s r m le_rfl) Finset.univ <
      (1-θ)*(Fintype.card (PowerTwoFriLevels ell (3*m)):ℝ) := by
  by_contra hn
  exact weighted_invariant T s deg θ hfar r hgood m le_rfl
    (weightedClose_self_of_mass _ θ _ _ hterminal (le_of_not_gt hn))

end Minidregg.Selvage.ArityEight.Schedule

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.prefixConsistency_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.prefixConsistency_nonneg

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.prefixConsistency_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.prefixConsistency_le_one

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.consistencyAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.consistencyAt_succ

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.weighted_bad_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.weighted_bad_round_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.weighted_bad_schedule_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.weighted_bad_schedule_bound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.weighted_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.weighted_invariant

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.terminal_consistency_mass_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.terminal_consistency_mass_lt
