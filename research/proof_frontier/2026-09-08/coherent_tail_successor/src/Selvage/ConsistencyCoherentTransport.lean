/- Recursive consistency mass for the actual certified BabyBear coherent sampler. -/
import Selvage.ConsistencyQueryMass
import Selvage.ArityEightScheduleBabyBear

namespace Minidregg.Selvage.ArityEight.Schedule
set_option maxHeartbeats 800000
open scoped BigOperators Classical

/-- Repeated independent coordinates exponentiate any single-index event. -/
theorem uniformProb_all_coordinates {I : Type} [Fintype I] (q : ℕ) (p : I → Prop) :
    uniformProb (Fin q → I) (fun seed => ∀ a, p (seed a)) = (uniformProb I p)^q := by
  have hset : (Finset.univ.filter fun seed : Fin q → I => ∀ a, p (seed a)) =
      Fintype.piFinset (fun _ : Fin q => Finset.univ.filter p) := by
    ext seed
    simp [Fintype.mem_piFinset]
  unfold uniformProb
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hset,Fintype.card_piFinset_const,Fintype.card_fun,Fintype.card_fin]
  push_cast
  exact (div_pow _ _ q).symm

/-- The actual binary squaring map preserves uniform probability. Its two-element
fibres are proved from FoldingData; no balanced-map premise is assumed. -/
theorem uniformProb_square {F I K : Type} [Field F] [Fintype I] [Fintype K]
    {dom : I ↪ F} {domSq : K ↪ F} (D : FoldingData F dom domSq) (p : K → Prop) :
    uniformProb I (fun i => p (D.sq i)) = uniformProb K p := by
  have hc := card_sq_preimage D (Finset.univ.filter p)
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc
  unfold uniformProb
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hc,card_eq_two_mul_card D]
  push_cast
  ring

namespace BabyBear
open BabyBearExt4

/-- The certified tower's exact projection, retained by firstFifteen. -/
theorem firstFifteen_sq_val (n : ℕ) (hn : n < 15) (i : PowerTwoFriLevels 20 n) :
    ((firstFifteen.data n hn).sq i).val = i.val % 2^(20-(n+1)) :=
  MultiplicativeTower.correctness.2 n (by omega) i

/-- Three actual square maps coincide with the existing sampler's block modulus. -/
theorem blockSquare_val (n : ℕ) (hn : n < 5) (i : PowerTwoFriLevels 20 (3*n)) :
    (blockSquare firstFifteen n hn i).val = i.val % 2^(20-3*(n+1)) := by
  simp only [blockSquare,firstFifteen_sq_val]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  congr 2

/-- Iterated actual maps retain precisely the low bits used by coherent queries. -/
theorem sourcePoint_val (n : ℕ) (hn : n ≤ 5) (i : PowerTwoFriLevels 20 0) :
    (sourcePoint firstFifteen n hn i).val = i.val % 2^(20-3*n) := by
  induction n with
  | zero => exact (Nat.mod_eq_of_lt i.isLt).symm
  | succ n ih =>
    rw [sourcePoint,blockSquare_val,ih (by omega),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- Actual source trajectories and the existing seed sampler select identical indices. -/
theorem sourcePoint_eq_coherent (j : Fin 5) (i : PowerTwoFriLevels 20 0) :
    sourcePoint (m := 5) firstFifteen (j+1) (by omega) i =
      powerTwoRoundIndex (show 15 ≤ 20 by decide) (⟨3*j.val+2,by omega⟩ : Fin 15)
        ((firstFifteen.data 0 (by decide)).sq i) := by
  apply Fin.ext
  rw [sourcePoint_val]
  change i.val % 2^(20-3*(j.val+1)) =
    ((firstFifteen.data 0 (by decide)).sq i).val % 2^(20-(3*j.val+2+1))
  rw [firstFifteen_sq_val,Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rfl

/-- One coordinate of the existing coherent query schedule passes every fold equation. -/
def seedChecks (s : Words Ext4 (PowerTwoFriLevels 20)) (r : Fin 5 → Ext4)
    (seed : PowerTwoFriLevels 20 1) : Prop :=
  ∀ j : Fin 5, s.wordAt r (j+1) (by omega)
      (powerTwoRoundIndex (show 15 ≤ 20 by decide) (⟨3*j.val+2,by omega⟩ : Fin 15) seed) =
    blockAt firstFifteen s j r
      (powerTwoRoundIndex (show 15 ≤ 20 by decide) (⟨3*j.val+2,by omega⟩ : Fin 15) seed)

/-- This exact transport uses firstFifteen's certified square maps. Cardinalities
alone would not identify the cross-round coherent event. -/
theorem sourceChecks_iff_seedChecks (s : Words Ext4 (PowerTwoFriLevels 20))
    (r : Fin 5 → Ext4) (i : PowerTwoFriLevels 20 0) :
    sourceChecks firstFifteen s r 5 le_rfl i ↔
      seedChecks s r ((firstFifteen.data 0 (by decide)).sq i) := by
  rw [sourceChecks_iff_all]
  simp only [sourcePoint_eq_coherent,seedChecks]

/-- Statement-first contract for the exact fixed-scalar coherent query probability. -/
def ConsistencyQueryContract (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (r : Fin 5 → Ext4) : Prop :=
  s.wordAt r 5 le_rfl ∈ reedSolomonCode (firstFifteen.dom 15) (degree 5) →
    uniformProb (Fin q → PowerTwoFriLevels 20 1)
      (Accepts firstFifteen s degree q (by decide) r) =
      (consistencyMass (consistencyAt firstFifteen s r 5 le_rfl) Finset.univ /
        (Fintype.card (PowerTwoFriLevels 20 15):ℝ))^q

/-- The normalized terminal mass is exactly one existing coherent seed's survival probability. -/
theorem seed_probability_mass (s : Words Ext4 (PowerTwoFriLevels 20)) (r : Fin 5 → Ext4) :
    uniformProb (PowerTwoFriLevels 20 1) (seedChecks s r) =
      consistencyMass (consistencyAt firstFifteen s r 5 le_rfl) Finset.univ /
        (Fintype.card (PowerTwoFriLevels 20 15):ℝ) := by
  rw [←uniformProb_square (firstFifteen.data 0 (by decide)) (seedChecks s r)]
  rw [←uniformProb_congr (sourceChecks_iff_seedChecks s r)]
  exact source_probability_mass (ell := 20) (m := 5) firstFifteen s r (by decide) 5 le_rfl

/-- Every scalar-fixed acceptance event has the exact coherent query tail. All
rounds use the same seed vector; independence is only across its q coordinates. -/
theorem consistency_query_exact (s : Words Ext4 (PowerTwoFriLevels 20)) (q : ℕ)
    (r : Fin 5 → Ext4) : ConsistencyQueryContract s q r := by
  intro hterminal
  change uniformProb (Fin q → PowerTwoFriLevels 20 1)
    (Accepts firstFifteen s degree q (by decide) r) = _
  calc
    _ = uniformProb (Fin q → PowerTwoFriLevels 20 1)
        (fun seed => ∀ a, seedChecks s r (seed a)) := by
      apply uniformProb_congr
      intro seed
      simp only [Accepts,hterminal,true_and,seedChecks,roundQueries,powerTwoCoherentRound]
      exact forall_comm
    _ = (uniformProb (PowerTwoFriLevels 20 1) (seedChecks s r))^q :=
      uniformProb_all_coordinates q _
    _ = _ := by rw [seed_probability_mass]

end BabyBear
end Minidregg.Selvage.ArityEight.Schedule

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.uniformProb_all_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.uniformProb_all_coordinates

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.uniformProb_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.uniformProb_square

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_sq_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.firstFifteen_sq_val

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.blockSquare_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.blockSquare_val

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourcePoint_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourcePoint_val

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourcePoint_eq_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourcePoint_eq_coherent

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourceChecks_iff_seedChecks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.sourceChecks_iff_seedChecks

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.seed_probability_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.seed_probability_mass

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.consistency_query_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.consistency_query_exact

