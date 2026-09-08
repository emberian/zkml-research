/- Inhabited five-round actual BabyBear schedule. A monomial source is far;
four exact transitions lead to one terminal substitution. Query zero accepts,
while query one detects that substitution. No field enumeration is used. -/
import Selvage.ArityEightScheduleBabyBear
import Selvage.ArityEightTwoRoundWitnesses

namespace Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses
open BabyBearExt4 Polynomial
noncomputable section

def monomial (n : ℕ) : PowerTwoFriLevels 20 (3*n) → Ext4 :=
  fun i => (firstFifteen.dom (3*n) i)^(degree n)

def words : Words Ext4 (PowerTwoFriLevels 20) where
  word n _ := if n < 5 then monomial n else fun _ => 1
  input _ _ := fun _ => 0

theorem source_eq : words.word 0 (fun i => i.elim0) = MultiplicativeTower.farWord := rfl

theorem source_far : ¬close (2/5:ℝ) (reedSolomonCode (firstFifteen.dom 0) (2^19))
    (words.word 0 (fun i => i.elim0)) :=
  MultiplicativeTower.farWord_far

theorem source_not_mem : words.word 0 (fun i => i.elim0) ∉
    reedSolomonCode (firstFifteen.dom 0) (2^19) := MultiplicativeTower.farWord_not_mem

/-- Each literal arity-eight fold divides the monomial exponent by eight. -/
theorem literal_exact (j : Fin 5) (p : Fin j.val → Ext4) (β : Ext4) :
    literal firstFifteen words j p β = monomial (j+1) := by
  have hj : j.val < 5 := j.isLt
  unfold literal words
  simp only [hj,if_pos,mul_zero,add_zero]
  unfold monomial
  rw [degree_step j]
  exact TwoRound.fold8_power (firstFifteen.data (3*j.val) (by omega))
    (firstFifteen.data (3*j.val+1) (by omega)) (firstFifteen.data (3*j.val+2) (by omega))
    (degree (j+1)) β

theorem terminal_mem (r : Fin 5 → Ext4) : words.wordAt r 5 le_rfl ∈
    reedSolomonCode (firstFifteen.dom 15) (degree 5) := by
  refine mem_reedSolomonCode_iff.mpr ⟨C 1,?_,?_⟩
  · norm_num [degree]
  · intro i
    simp [Words.wordAt,words]

theorem domain_zero (n : ℕ) : firstFifteen.dom n (0 : PowerTwoFriLevels 20 n) = 1 := by
  change (PowerTwoRootFolding.levelRoot MultiplicativeTower.initialRoot n)^0 = 1
  simp

theorem terminal_monomial_one : monomial 5 (1 : PowerTwoFriLevels 20 15) = -1 := by
  have h := PowerTwoRootFolding.levelRoot_half_turn MultiplicativeTower.initialRoot_primitive 15 (by decide)
  simpa [monomial,degree,firstFifteen,MultiplicativeTower.tower,PowerTwoRootFolding.tower,
    PowerTwoRootFolding.domain] using h

/-- Every challenge vector accepts the all-zero shared query vector. -/
theorem zero_seed_accepts (r : Fin 5 → Ext4) (q : ℕ) :
    Accepts firstFifteen words degree q (by decide) r (fun _ => 0) := by
  refine ⟨terminal_mem r,?_⟩
  intro j a
  change words.wordAt r (j+1) _ _ = literal firstFifteen words j _ _ _
  rw [literal_exact]
  have hz : roundQueries (show 3*5 ≤ 20 by decide) j
      (fun _ : Fin q => (0 : PowerTwoFriLevels 20 1)) a = 0 := by
    apply Fin.ext
    simp [roundQueries,powerTwoCoherentRound,powerTwoRoundIndex]
  rw [hz]
  simp only [Words.wordAt,words]
  split_ifs
  · rfl
  · simp [monomial,domain_zero]

set_option maxHeartbeats 800000 in
/-- The same legal terminal word rejects at seed one in the fifth transition. -/
theorem one_seed_rejects (r : Fin 5 → Ext4) :
    ¬Accepts firstFifteen words degree 1 (by decide) r (fun _ => 1) := by
  intro h
  let j : Fin 5 := ⟨4,by decide⟩
  let seed : Fin 1 → PowerTwoFriLevels 20 1 := fun _ => 1
  have heq := h.2 j 0
  have hl : blockAt firstFifteen words j r (roundQueries (by decide) j seed 0) =
      monomial (j+1) (roundQueries (by decide) j seed 0) :=
    congrFun (literal_exact j (friPrefix r j (by omega)) (r j)) _
  have hx := heq.trans hl
  have hi : roundQueries (show 3*5 ≤ 20 by decide) j seed 0 = 1 := by
    apply Fin.ext
    norm_num [j,seed,roundQueries,powerTwoCoherentRound,powerTwoRoundIndex]
  rw [hi] at hx
  change 1 = monomial 5 1 at hx
  rw [terminal_monomial_one] at hx
  have ht : (2:Ext4)=0 := by linear_combination hx
  exact MultiplicativeTower.two_ne_zero ht

/-- All finite-schedule source, degree, rate, radius, timing and terminal
premises are inhabited by the actual five-round schedule. -/
theorem sound_fires (q : ℕ) :
    uniformProb ((Fin 5 → Ext4) × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Accepts firstFifteen words degree q (by decide) x.1 x.2) ≤
      ((2^20+2^17+2^14+2^11+2^8:ℕ):ℝ)/(modulus^4:ℕ)+(24/25:ℝ)^q :=
  terminal_sound words q source_far

end
end Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_eq

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_far

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.source_not_mem

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.literal_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.literal_exact

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.terminal_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.terminal_mem

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.domain_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.domain_zero

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.terminal_monomial_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.terminal_monomial_one

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.zero_seed_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.zero_seed_accepts

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.one_seed_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.one_seed_rejects

/-- info: 'Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.Schedule.BabyBear.Witnesses.sound_fires
