/- Actual BabyBear tower/degree/rate specialization of the cumulative
weighted invariant. The single threshold is 1/5 at all five rounds. -/
import Selvage.ArityEightConsistencySchedule
import Selvage.ArityEightScheduleBabyBear

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted
open BabyBearExt4
noncomputable section

theorem rate_fixed (j : Fin 5) : (degree (j+1):ℝ) <
    (1-2*(1/5:ℝ))*(Fintype.card (PowerTwoFriLevels 20 (3*(j.val+1))):ℝ) := by
  fin_cases j <;> norm_num [degree,PowerTwoFriLevels]

theorem initial_far (s : Words Ext4 (PowerTwoFriLevels 20))
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (s.word 0 (fun i => i.elim0))) :
    ¬close (1/5:ℝ) (reedSolomonCode (firstFifteen.dom 0) (degree 0))
      (s.word 0 (fun i => i.elim0)) := by
  rintro ⟨w,hw,hc⟩
  apply hfar
  refine ⟨w,hw,?_⟩
  linarith

/-- The full existing degree-eight challenge sum, at one unchanged weighted threshold. -/
theorem bad_probability (s : Words Ext4 (PowerTwoFriLevels 20)) :
    uniformProb (Fin 5 → Ext4) (fun r => ∃ j, WeightedBadRound firstFifteen s degree (1/5:ℝ) j r) ≤
      (1198336:ℝ)/(modulus^4:ℕ) := by
  have h := weighted_bad_schedule_bound firstFifteen s degree (1/5:ℝ) degree_positive degree_step
    (by norm_num) rate_fixed
  rw [ext4_card] at h
  norm_num [PowerTwoFriLevels,Fin.sum_univ_succ] at h ⊢
  convert h using 1
  ring

/-- Off the derived challenge event, a legal terminal word has normalized
consistency mass below 4/5. The query-side equality is proved separately. -/
theorem terminal_mass (s : Words Ext4 (PowerTwoFriLevels 20))
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (s.word 0 (fun i => i.elim0))) (r : Fin 5 → Ext4)
    (hgood : ¬∃ j, WeightedBadRound firstFifteen s degree (1/5:ℝ) j r)
    (ht : s.wordAt r 5 le_rfl ∈ reedSolomonCode (firstFifteen.dom 15) (degree 5)) :
    consistencyMass (consistencyAt firstFifteen s r 5 le_rfl) Finset.univ /
      (Fintype.card (PowerTwoFriLevels 20 15):ℝ) < 4/5 := by
  have h := terminal_consistency_mass_lt (ell := 20) (m := 5) firstFifteen s degree (1/5:ℝ)
    (initial_far s hfar) r hgood ht
  norm_num [PowerTwoFriLevels] at h ⊢
  linarith

set_option exponentiation.threshold 1000 in
/-- The ideal error budget arithmetic, including the field challenge term. -/
theorem candidate_312_arithmetic :
    (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^312 ≤ 1/2^100 := by norm_num [modulus]

set_option exponentiation.threshold 1000 in
/-- A one-query reduction would miss this same numerical threshold. -/
theorem candidate_311_fails :
    (1/2^100:ℝ) < (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^311 := by norm_num [modulus]

end
end Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.rate_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.rate_fixed

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.initial_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.initial_far

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.bad_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.bad_probability

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.terminal_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.terminal_mass

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.candidate_312_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.candidate_312_arithmetic

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.candidate_311_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.candidate_311_fails
