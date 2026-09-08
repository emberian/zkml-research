/- Actual BabyBearExt4 specialization of two external arity-eight rounds.
The tower is a projection of the existing certified tower, with unchanged
root, domain, squaring, negation and section objects. -/
import Selvage.ArityEightTwoRoundSupplied
import Selvage.BabyBearFoldingTower

namespace Minidregg.Selvage.ArityEight.TwoRound.BabyBear
open BabyBearExt4
noncomputable section

/-- Exactly the first six transition objects of the existing tower. -/
def firstSix : FoldingTower Ext4 (PowerTwoFriLevels 20) 6 where
  dom := MultiplicativeTower.tower.dom
  data j hj := MultiplicativeTower.tower.data j (by omega)

theorem firstSix_domains (n : ℕ) : firstSix.dom n = MultiplicativeTower.tower.dom n := rfl

theorem firstSix_transitions (j : ℕ) (hj : j < 6) :
    firstSix.data j hj = MultiplicativeTower.tower.data j (by omega) := rfl

/-- All rate, degree, radius and carrier arithmetic is discharged. The five
word functions retain their explicit prefix dependence. -/
theorem terminal_sound (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (hfar : ¬close (2/5:ℝ)
      (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19)) s.source) :
    uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstSix s (2^13) q (by decide) x.1 x.2) ≤
      ((2^20+2^17:ℕ):ℝ)/(modulus^4:ℕ) + (9/10:ℝ)^q := by
  have hf : ¬close (1/5:ℝ) (reedSolomonCode (firstSix.dom 0) (64*2^13)) s.source := by
    rintro ⟨w,hw,hclose⟩
    apply hfar
    refine ⟨w,?_,?_⟩
    · convert hw using 1
    · linarith
  have h := sound firstSix s (d := 2^13) (by norm_num) q (by decide)
    (ρ₀ := (1/5:ℝ)) (ρ₁ := (1/10:ℝ)) (τ := (1/10:ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [PowerTwoFriLevels])
    (by norm_num [PowerTwoFriLevels]) hf
  have hc : Fintype.card Ext4 = modulus^4 := ext4_card
  rw [hc] at h
  norm_num [PowerTwoFriLevels] at h ⊢
  convert h using 1
  ring

/-- Actual-field supplied-opening theorem with summed transition failures
and a single coherent-query tail. The observed log term is not assigned bits. -/
theorem supplied_terminal_sound {Digest : Type} [DecidableEq Digest]
    (H : BinaryMerkle.HashSuite Ext4 Digest) (st : Checkpoints Ext4 Digest) (default : Ext4) (q : ℕ)
    (openings : (Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1) → Openings Ext4 Digest q)
    (logs : (Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1) → EfficientRootOpening.Log Ext4 Digest)
    (hsub : ∀ x, CheckpointsLogged st (logs x) x.1)
    (hlog : ∀ x, OpeningsLogged H firstSix (logs x) q (by decide) x.2 (openings x))
    (hfar : EfficientRootOpening.Far_E (2/5:ℝ) 20
      (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19)) st.source.1 default st.source.2) :
    uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => SuppliedAccepts H firstSix st default (2^13) q (by decide) x.1 x.2 (openings x)) ≤
      ((2^20+2^17:ℕ):ℝ)/(modulus^4:ℕ) + (9/10:ℝ)^q +
      uniformProb ((Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1))
        (fun x => Failure st (logs x) x.1) := by
  let Ω := (Ext4 × Ext4) × (Fin q → PowerTwoFriLevels 20 1)
  let ideal : Ω → Prop := fun x => Accepts firstSix (extracted st default) (2^13) q (by decide) x.1 x.2
  let raw : Ω → Prop := fun x => SuppliedAccepts H firstSix st default (2^13) q (by decide) x.1 x.2 (openings x)
  let bad : Ω → Prop := fun x => Failure st (logs x) x.1
  have h : uniformProb Ω ideal ≤ ((2^20+2^17:ℕ):ℝ)/(modulus^4:ℕ)+(9/10:ℝ)^q :=
    terminal_sound (extracted st default) q hfar
  have hcover : ∀ x : Ω, raw x → ideal x ∨ bad x := by
    intro x hx
    exact supplied_cover H firstSix st default (2^13) q (by decide) x.1 x.2
      (openings x) (logs x) (hsub x) (hlog x) hx
  have hsplit : uniformProb Ω raw ≤ uniformProb Ω ideal + uniformProb Ω bad :=
    le_trans (uniformProb_mono hcover) (uniformProb_or_le ideal bad)
  change uniformProb Ω raw ≤ _
  linarith

end
end Minidregg.Selvage.ArityEight.TwoRound.BabyBear

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.BabyBear.firstSix_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.BabyBear.firstSix_domains

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.BabyBear.firstSix_transitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.BabyBear.firstSix_transitions

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.BabyBear.terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.BabyBear.terminal_sound

/-- info: 'Minidregg.Selvage.ArityEight.TwoRound.BabyBear.supplied_terminal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.TwoRound.BabyBear.supplied_terminal_sound
