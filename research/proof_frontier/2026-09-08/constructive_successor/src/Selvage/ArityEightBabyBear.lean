/- Actual BabyBearExt4 first arity-eight transition, on the existing certified
tower. Single-round uniform challenges and sampled checks, with fixed input
injection; no new whole-protocol security-bit claim. -/
import Selvage.ArityEightSampling
import Selvage.BabyBearFoldingTower

namespace Minidregg.Selvage.ArityEight.BabyBear
open BabyBearExt4 BabyBearExt4.MultiplicativeTower

/-- The next word is committed after beta, before the query vector; g is a
fixed-prefix input. Source 2/5-farness implies the 1/5-farness needed for this
arity-eight block. All carrier, domain and rate premises are discharged. -/
theorem first_injected_crossing (f : Fin (2^20) → Ext4) (g : Fin (2^17) → Ext4)
    (next : Ext4 → Fin (2^17) → Ext4) (q : ℕ)
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (tower.dom 0) (2^19)) f) :
    uniformProb (Ext4 × (Fin q → Fin (2^17)))
      (Crossing (reedSolomonCode (tower.dom 3) (2^16)) (1/10:ℝ)
        (fun β i => fold8 (tower.data 0 (by decide)) (tower.data 1 (by decide))
          (tower.data 2 (by decide)) f β i + β^8*g i) next q) ≤
      (2^20:ℝ)/(modulus^4:ℕ) + (9/10:ℝ)^q := by
  have hf : ¬close (1/5:ℝ) (reedSolomonCode (tower.dom 0) (8*2^16)) f := by
    rintro ⟨w,hw,hclose⟩
    apply hfar
    refine ⟨w,?_,?_⟩
    · convert hw using 1
    · linarith
  have h := fold8_injected_sampled_crossing (tower.data 0 (by decide))
    (tower.data 1 (by decide)) (tower.data 2 (by decide)) (d := 2^16) (by norm_num)
    (θ := (1/5:ℝ)) (δ := (1/10:ℝ)) (τ := (1/10:ℝ)) (by norm_num)
    (by norm_num [PowerTwoFriLevels]) (by norm_num) (by norm_num) f g next q hf
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels] at h ⊢
  exact h

/-- The actual high-degree witness inhabits the source-farness premise of
the newly composed width-eight statement for any fixed injected input. -/
theorem actual_far_source_fires (g : Fin (2^17) → Ext4)
    (next : Ext4 → Fin (2^17) → Ext4) (q : ℕ) :
    uniformProb (Ext4 × (Fin q → Fin (2^17)))
      (Crossing (reedSolomonCode (tower.dom 3) (2^16)) (1/10:ℝ)
        (fun β i => fold8 (tower.data 0 (by decide)) (tower.data 1 (by decide))
          (tower.data 2 (by decide)) farWord β i + β^8*g i) next q) ≤
      (2^20:ℝ)/(modulus^4:ℕ) + (9/10:ℝ)^q :=
  first_injected_crossing farWord g next q farWord_far

end Minidregg.Selvage.ArityEight.BabyBear

/-- info: 'Minidregg.Selvage.ArityEight.BabyBear.first_injected_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.BabyBear.first_injected_crossing

/-- info: 'Minidregg.Selvage.ArityEight.BabyBear.actual_far_source_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.BabyBear.actual_far_source_fires

