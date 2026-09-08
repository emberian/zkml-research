/- Five external arity-eight rounds on the existing certified BabyBearExt4
binary tower. Degree/rate/radius arithmetic is discharged, not assumed. -/
import Selvage.ArityEightScheduleSupplied
import Selvage.BabyBearFoldingTower

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear
open BabyBearExt4
noncomputable section

def firstFifteen : FoldingTower Ext4 (PowerTwoFriLevels 20) 15 where
  dom := MultiplicativeTower.tower.dom
  data j hj := MultiplicativeTower.tower.data j (by omega)

theorem firstFifteen_domains (n : ℕ) : firstFifteen.dom n = MultiplicativeTower.tower.dom n := rfl

theorem firstFifteen_transitions (j : ℕ) (hj : j < 15) :
    firstFifteen.data j hj = MultiplicativeTower.tower.data j (by omega) := rfl

def degree (n : ℕ) : ℕ := 2^(19-3*n)
def radius (n : ℕ) : ℝ := (5-n:ℕ)/25

theorem degree_positive (j : Fin 5) : 1 ≤ degree (j+1) := by
  fin_cases j <;> norm_num [degree]

theorem degree_step (j : Fin 5) : degree j = 8*degree (j+1) := by
  fin_cases j <;> norm_num [degree]

theorem radius_positive (j : Fin 5) : 0 < radius j := by
  fin_cases j <;> norm_num [radius]

theorem radius_gap (j : Fin 5) : radius (j+1)+(1/25:ℝ) ≤ radius j := by
  fin_cases j <;> norm_num [radius]

theorem rate (j : Fin 5) : (degree (j+1):ℝ) <
    (1-2*radius j)*(Fintype.card (PowerTwoFriLevels 20 (3*(j.val+1))):ℝ) := by
  fin_cases j <;> norm_num [degree,radius,PowerTwoFriLevels]

/-- Five real external rounds, with one shared query vector. The terminal
word has degree below 16; realizing its RS-membership check is a caller boundary. -/
theorem terminal_sound (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (hfar : ¬close (2/5:ℝ)
      (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19)) (s.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen s degree q (by decide) x.1 x.2) ≤
      ((2^20+2^17+2^14+2^11+2^8:ℕ):ℝ)/(modulus^4:ℕ) + (24/25:ℝ)^q := by
  have hf : ¬close (radius 0) (reedSolomonCode (firstFifteen.dom 0) (degree 0))
      (s.word 0 (fun i => i.elim0)) := by
    rintro ⟨w,hw,hc⟩
    apply hfar
    refine ⟨w,hw,?_⟩
    norm_num [radius] at hc
    linarith
  have h := sound firstFifteen s degree radius q (by decide) (τ := (1/25:ℝ))
    degree_positive degree_step radius_positive (by norm_num) (by norm_num [radius]) radius_gap rate hf
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels,Fin.sum_univ_succ] at h ⊢
  convert h using 1
  ring

set_option maxHeartbeats 800000 in
/-- Actual-field finite supplied-path soundness, with the observed log union
kept explicit and unpriced. Prefix-selected checkpoint roots may be malicious. -/
theorem supplied_terminal_sound {Digest : Type} [DecidableEq Digest]
    (H : BinaryMerkle.HashSuite Ext4 Digest) (st : Checkpoints Ext4 Digest) (default : Ext4) (q : ℕ)
    (openings : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1) → Openings Ext4 Digest 5 q)
    (logs : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1) → EfficientRootOpening.Log Ext4 Digest)
    (hsub : ∀ x, CheckpointsLogged st (logs x) x.1)
    (hlog : ∀ x, OpeningsLogged H firstFifteen (logs x) q (by decide) x.2 (openings x))
    (hfar : EfficientRootOpening.Far_E (2/5:ℝ) 20
      (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (st.word 0 (fun i => i.elim0)).1 default (st.word 0 (fun i => i.elim0)).2) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => SuppliedAccepts H firstFifteen st default degree q (by decide) x.1 x.2 (openings x)) ≤
      ((2^20+2^17+2^14+2^11+2^8:ℕ):ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q+
      uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
        (fun x => Failure st (logs x) x.1) := by
  have hf : EfficientRootOpening.Far_E (radius 0) 20
      (reedSolomonCode (firstFifteen.dom 0) (degree 0))
      (st.word 0 (fun i => i.elim0)).1 default (st.word 0 (fun i => i.elim0)).2 := by
    rintro ⟨w,hw,hc⟩
    apply hfar
    refine ⟨w,hw,?_⟩
    norm_num [radius] at hc
    linarith
  have h := supplied_sound H firstFifteen st default degree radius q (by decide) (τ := (1/25:ℝ))
    degree_positive degree_step radius_positive (by norm_num) (by norm_num [radius]) radius_gap rate
    openings logs hsub hlog hf
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels,Fin.sum_univ_succ] at h ⊢
  convert h using 1
  ring

end
end Minidregg.Selvage.ArityEight.Schedule.BabyBear

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_domains

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_transitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_transitions

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.degree_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.degree_positive

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.degree_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.degree_step

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.radius_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.radius_positive

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.radius_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.radius_gap

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.rate

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.terminal_sound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.supplied_terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.supplied_terminal_sound
