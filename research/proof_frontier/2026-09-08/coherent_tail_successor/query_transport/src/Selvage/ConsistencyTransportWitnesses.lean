/- Premise inhabitation and live teeth for exact consistency/coherent transport. -/
import Selvage.ConsistencyCoherentTransport
import Selvage.ArityEightScheduleWitnesses

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses
open scoped Classical
open BabyBearExt4

/-- The transport premises have an actual-field witness with both acceptance poles. -/
def PremisesInhabited : Prop :=
  ∃ s : Words Ext4 (PowerTwoFriLevels 20), ∀ r : Fin 5 → Ext4,
    s.wordAt r 5 le_rfl ∈ reedSolomonCode (firstFifteen.dom 15) (degree 5) ∧
    Accepts firstFifteen s degree 1 (by decide) r (fun _ => 0) ∧
    ¬Accepts firstFifteen s degree 1 (by decide) r (fun _ => 1)

/-- The existing far monomial schedule realizes every premise and both poles. -/
theorem premises_inhabited : PremisesInhabited :=
  ⟨Witnesses.words,fun r => ⟨Witnesses.terminal_mem r,
    Witnesses.zero_seed_accepts r 1,Witnesses.one_seed_rejects r⟩⟩

/-- The generic source-mass contract is realized on the same certified tower and schedule. -/
theorem source_mass_satisfiable (r : Fin 5 → Ext4) :
    SourceMassContract firstFifteen Witnesses.words r :=
  consistency_mass_source firstFifteen Witnesses.words r

/-- The exact probability contract fires on an actually inhabited legal-terminal premise. -/
theorem query_exact_satisfiable (r : Fin 5 → Ext4) (q : ℕ) :
    Witnesses.words.wordAt r 5 le_rfl ∈ reedSolomonCode (firstFifteen.dom 15) (degree 5) ∧
    ConsistencyQueryContract Witnesses.words q r :=
  ⟨Witnesses.terminal_mem r,consistency_query_exact Witnesses.words q r⟩

/-- The zero coherent index survives all five actual equations. -/
theorem zero_seed_checks (r : Fin 5 → Ext4) : seedChecks Witnesses.words r 0 := by
  intro j
  exact (Witnesses.zero_seed_accepts r 1).2 j 0

/-- The one coherent index fails the last actual equation. -/
theorem one_seed_fails_checks (r : Fin 5 → Ext4) : ¬seedChecks Witnesses.words r 1 := by
  intro h
  apply Witnesses.one_seed_rejects r
  refine ⟨Witnesses.terminal_mem r,fun j _ => h j⟩

/-- A witnessed finite event has positive probability and a witnessed failure
makes that probability strictly below one. -/
theorem probability_two_poles {I : Type} [Fintype I] [Nonempty I]
    (p : I → Prop) (a b : I) (ha : p a) (hb : ¬p b) :
    0 < uniformProb I p ∧ uniformProb I p < 1 := by
  have hcard : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (Finset.univ.filter p).card :=
    Finset.card_pos.mpr ⟨a,by simp [ha]⟩
  have hlt : (Finset.univ.filter p).card < Fintype.card I := by
    simpa using Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨b,Finset.mem_univ b,hb⟩)
  unfold uniformProb
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact ⟨div_pos (by exact_mod_cast hpos) hcard,
    (div_lt_one hcard).mpr (by exact_mod_cast hlt)⟩

/-- Teeth: normalized consistency mass is neither empty nor universally accepting.
Replacing the masks by all-one weights would falsely assign this schedule mass one. -/
theorem mask_omission_falsifier (r : Fin 5 → Ext4) :
    0 < consistencyMass (consistencyAt firstFifteen Witnesses.words r 5 le_rfl) Finset.univ /
        (Fintype.card (PowerTwoFriLevels 20 15):ℝ) ∧
    consistencyMass (consistencyAt firstFifteen Witnesses.words r 5 le_rfl) Finset.univ /
        (Fintype.card (PowerTwoFriLevels 20 15):ℝ) < 1 := by
  rw [←seed_probability_mass]
  exact probability_two_poles (seedChecks Witnesses.words r) 0 1
    (zero_seed_checks r) (one_seed_fails_checks r)

end Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.premises_inhabited

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.source_mass_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.source_mass_satisfiable

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.query_exact_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.query_exact_satisfiable

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.zero_seed_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.zero_seed_checks

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.one_seed_fails_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.one_seed_fails_checks

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.probability_two_poles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.probability_two_poles

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.mask_omission_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.QueryWitnesses.mask_omission_falsifier

