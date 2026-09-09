/- Cumulative weighted FRI soundness for five actual BabyBear arity-eight
rounds and the existing shared coherent-query sampler. -/
import Selvage.BabyBearConsistencyInvariant
import Selvage.ConsistencyCoherentTransport
import Selvage.ArityEightScheduleWitnesses

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted
open BabyBearExt4
open scoped Classical
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2500000

/-- One threshold survives the entire schedule. The exact coherent-query
identity converts terminal consistency mass to the q-fold survival tail. -/
theorem coherent_tail (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (s.word 0 (fun i => i.elim0))) (r : Fin 5 → Ext4)
    (hgood : ¬∃ j, WeightedBadRound firstFifteen s degree (1/5:ℝ) j r) :
    uniformProb (Fin q → PowerTwoFriLevels 20 1) (Accepts firstFifteen s degree q (by decide) r) ≤
      (4/5:ℝ)^q := by
  by_cases ht : s.wordAt r 5 le_rfl ∈ reedSolomonCode (firstFifteen.dom 15) (degree 5)
  · rw [consistency_query_exact s q r ht]
    have hn := uniformProb_nonneg (seedChecks s r)
    rw [seed_probability_mass] at hn
    exact pow_le_pow_left₀ hn (le_of_lt (terminal_mass s hfar r hgood ht)) q
  · rw [uniformProb_false (fun _ h => ht h.1)]
    positivity

/-- Actual five-round ideal FRI soundness with no radius loss per round.
Challenge errors are summed; query coordinates are independent but the rounds
within each query remain coherent. -/
theorem sound (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (s.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen s degree q (by decide) x.1 x.2) ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^q := by
  let bad : (Fin 5 → Ext4) → Prop := fun r => ∃ j : Fin 5, WeightedBadRound (ell := 20) (m := 5) firstFifteen s degree (1/5:ℝ) j r
  have hb := bad_probability s
  have hq : uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => ¬bad x.1 ∧ Accepts firstFifteen s degree q (by decide) x.1 x.2) ≤ (4/5:ℝ)^q := by
    apply uniformProb_prod_le (by positivity)
    intro r
    by_cases hbad : bad r
    · rw [uniformProb_false (fun _ h => h.1 hbad)]
      positivity
    · exact le_trans (uniformProb_mono fun _ h => h.2) (coherent_tail s q hfar r hbad)
  have hsplit : uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen s degree q (by decide) x.1 x.2) ≤
      uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)) (fun x => bad x.1)+
      uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
        (fun x => ¬bad x.1 ∧ Accepts firstFifteen s degree q (by decide) x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_) (uniformProb_or_le _ _)
    by_cases hbad : bad x.1
    · exact Or.inl hbad
    · exact Or.inr ⟨hbad,hx⟩
  rw [TwoRound.uniform_fst (B := Fin q → PowerTwoFriLevels 20 1) bad] at hsplit
  change uniformProb (Fin 5 → Ext4) bad ≤ _ at hb
  linarith

/-- 312 shared queries suffice for the complete IDEAL FRI event at 2^-100,
including the unchanged degree-eight field-challenge term. -/
theorem ideal_100 (s : Words Ext4 (PowerTwoFriLevels 20))
    (hfar : ¬close (2/5:ℝ) (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (s.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin 5 → Ext4) × (Fin 312 → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen s degree 312 (by decide) x.1 x.2) ≤ 1/2^100 :=
  (sound s 312 hfar).trans candidate_312_arithmetic

/-- The same new tail feeds the actual supplied scalar-path verifier;
observed hash/log failure remains an explicit residual at this interface. -/
theorem supplied_sound {Digest : Type} [DecidableEq Digest]
    (H : BinaryMerkle.HashSuite Ext4 Digest) (st : Checkpoints Ext4 Digest) (default : Ext4) (q : ℕ)
    (openings : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1) → Openings Ext4 Digest 5 q)
    (logs : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1) → EfficientRootOpening.Log Ext4 Digest)
    (hsub : ∀ x, CheckpointsLogged st (logs x) x.1)
    (hlog : ∀ x, OpeningsLogged (ell := 20) (m := 5) H firstFifteen (logs x) q (by decide) x.2 (openings x))
    (hfar : EfficientRootOpening.Far_E (2/5:ℝ) 20
      (reedSolomonCode (MultiplicativeTower.tower.dom 0) (2^19))
      (st.word 0 (fun i => i.elim0)).1 default (st.word 0 (fun i => i.elim0)).2) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => SuppliedAccepts (ell := 20) (m := 5) H firstFifteen st default degree q (by decide) x.1 x.2 (openings x)) ≤
      (1198336:ℝ)/(modulus^4:ℕ)+(4/5:ℝ)^q+
      uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)) (fun x => Failure st (logs x) x.1) := by
  have hi := sound (extracted st default) q hfar
  have hc := uniformProb_mono (fun (x : (Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1)) hx => supplied_cover (ell := 20) (m := 5)
    H firstFifteen st default degree q (by decide) x.1 x.2 (openings x) (logs x) (hsub x) (hlog x) hx)
  exact le_trans (le_trans hc (uniformProb_or_le _ _)) (add_le_add hi le_rfl)

/-- The actual full-size far monomial strategy inhabits the new ideal theorem;
its all-zero accepted queries and seed-one rejection are inherited unchanged. -/
theorem witness_sound :
    uniformProb ((Fin 5 → Ext4) × (Fin 312 → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen Witnesses.words degree 312 (by decide) x.1 x.2) ≤ 1/2^100 :=
  ideal_100 Witnesses.words Witnesses.source_far

end
end Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.coherent_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.coherent_tail

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.sound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.ideal_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.ideal_100

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.supplied_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.supplied_sound

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.witness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Weighted.witness_sound

