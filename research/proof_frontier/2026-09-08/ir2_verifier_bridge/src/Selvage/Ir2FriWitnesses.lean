/- Actual-carrier nonvacuity and initial-equality teeth for the IR2 profile. -/
import Selvage.Ir2FriSoundness
import Selvage.ArityEightTwoRoundWitnesses

namespace Minidregg.Selvage.Ir2Fri.Witnesses
open BabyBearExt4 Ir2FriSchedule Polynomial ArityEight
open scoped Classical
noncomputable section
set_option maxRecDepth 100000

/-- A source of degree exactly 16384, outside the actual degree-below-16384 code. -/
def farWord : Index 0 → Ext4 := fun i => (domain 0 i)^16384

theorem farWord_not_mem : farWord ∉ reedSolomonCode (domain 0) 16384 := by
  intro hw
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hne : (X^16384 : Polynomial Ext4) ≠ p := by
    intro heq
    rw [←heq] at hp
    norm_num at hp
  have hcard := card_agreeSet_lt_of_ne (domain 0) (d := 16385)
    (p := (X^16384 : Polynomial Ext4)) (by norm_num) (q := p) (hp.trans (by norm_num)) hne
  have hall : (Finset.univ.filter fun i =>
      (X^16384 : Polynomial Ext4).eval (domain 0 i) = p.eval (domain 0 i)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    simpa [farWord] using heval i
  rw [hall,Finset.card_univ] at hcard
  norm_num [Index,stage] at hcard

/-- The minimum-distance argument yields actual positive 2/5 source farness. -/
theorem farWord_far : ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) farWord := by
  rintro ⟨w,hw,hclose⟩
  have hmem : farWord ∈ reedSolomonCode (domain 0) 16385 :=
    mem_reedSolomonCode_iff.mpr ⟨X^16384,by norm_num,fun i => by simp [farWord]⟩
  have hw' : w ∈ reedSolomonCode (domain 0) 16385 := by
    obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
    exact mem_reedSolomonCode_iff.mpr ⟨p,hp.trans (by norm_num [degree,stage]),heval⟩
  have h := reedSolomonCode_minDist (domain 0) 16385 farWord hmem w hw'
    (fun heq => farWord_not_mem (heq ▸ hw))
  norm_num [Index,stage] at h
  linarith

/-- The separately committed FRI words are constant one. This is deliberately
different from the far input; the initial native query check is the detector. -/
def words : Words where
  input := farWord
  word _ _ := fun _ => 1

theorem fold_one {F ι κ : Type*} [Field F] {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (β : F) : fold D (fun _ => 1) β = fun _ => 1 := by
  simpa using TwoRound.fold_even_power D 0 β

theorem block_one (r : Fin 5 → Ext4) (j : Fin 5) : blockAt words j r = fun _ => 1 := by
  fin_cases j
  · simpa using TwoRound.fold8_power (Ir2Fri.tower.data 0 (by decide))
      (Ir2Fri.tower.data 1 (by decide)) (Ir2Fri.tower.data 2 (by decide)) 0 (r 0)
  · simpa using TwoRound.fold8_power (Ir2Fri.tower.data 3 (by decide))
      (Ir2Fri.tower.data 4 (by decide)) (Ir2Fri.tower.data 5 (by decide)) 0 (r 1)
  · simpa using TwoRound.fold8_power (Ir2Fri.tower.data 6 (by decide))
      (Ir2Fri.tower.data 7 (by decide)) (Ir2Fri.tower.data 8 (by decide)) 0 (r 2)
  · simpa using TwoRound.fold8_power (Ir2Fri.tower.data 9 (by decide))
      (Ir2Fri.tower.data 10 (by decide)) (Ir2Fri.tower.data 11 (by decide)) 0 (r 3)
  · change fold (Ir2Fri.tower.data 13 (by decide))
      (fold (Ir2Fri.tower.data 12 (by decide)) (fun _ => 1) (r 4)) ((r 4)^2) = _
    rw [fold_one (Ir2Fri.tower.data 12 (by decide)) (r 4)]
    exact fold_one (Ir2Fri.tower.data 13 (by decide)) _

/-- The terminal constant polynomial and all five native consistency transitions are inhabited. -/
theorem terminal_and_steps (r : Fin 5 → Ext4) :
    Terminal words r ∧ ∀ j k, stepMasks words r j k := by
  refine ⟨⟨1,fun _ => rfl⟩,?_⟩
  intro j k
  unfold stepMasks
  rw [block_one]
  rfl

theorem input_zero : farWord 0 = 1 := by
  change ((PowerTwoRootFolding.levelRoot (TwoAdic.omega 17) 0)^0)^16384 = 1
  simp

theorem input_one : farWord 1 ≠ 1 := by
  change ((PowerTwoRootFolding.levelRoot (TwoAdic.omega 17) 0)^1)^16384 ≠ 1
  simpa [PowerTwoRootFolding.levelRoot] using
    (TwoAdic.omega_primitive 17 (by decide)).pow_ne_one_of_pos_of_lt
      (by decide : 16384 ≠ 0) (by decide : 16384 < 2^17)

/-- This far-input strategy really accepts the all-zero 38-query sample. -/
theorem zero_accepts (r : Fin 5 → Ext4) : FreshAccepts words 38 r (fun _ => 0) := by
  refine ⟨(terminal_and_steps r).1,?_,fun j a => (terminal_and_steps r).2 j _⟩
  intro a
  have hz : sourceIndex (BabyBearModuloSampling.sampleBits 17 (0:BabyBear)) = 0 := by
    apply Fin.ext
    decide
  rw [hz]
  exact input_zero.symm

/-- Raw bit16 is natural input coordinate one: the initial equality rejects it,
even though every later fold and terminal equality passes. -/
theorem initial_rejects (r : Fin 5 → Ext4) :
    ¬FreshAccepts words 38 r (fun _ => (65536:BabyBear)) := by
  intro h
  have he := h.2.1 0
  have ho : sourceIndex (BabyBearModuloSampling.sampleBits 17 (65536:BabyBear)) = 1 := by
    apply Fin.ext
    decide
  rw [ho] at he
  exact input_one he.symm

/-- All proximity theorem premises are inhabited together with genuine
accepting and rejecting native query vectors on the actual field and schedule. -/
theorem premises_inhabited : ∃ s : Words,
    ¬close (2/5:ℝ) (reedSolomonCode (domain 0) (degree 0)) s.input ∧
    (∀ r, FreshAccepts s 38 r (fun _ => 0)) ∧
    (∀ r, ¬FreshAccepts s 38 r (fun _ => (65536:BabyBear))) :=
  ⟨words,farWord_far,zero_accepts,initial_rejects⟩

/-- The actual 38-query theorem applies to the concrete far-input witness. -/
theorem sound_fires :
    uniformProb ((Fin 5 → Ext4) × (Fin 38 → BabyBear))
      (fun x => FreshAccepts words 38 x.1 x.2) ≤
      (131064:ℝ)/(modulus^4:ℕ)+
        ((((modulus-1:ℕ):ℝ)/(modulus:ℝ))*(3/5:ℝ)+1/(modulus:ℝ))^38 :=
  fresh_38 words farWord_far

end
end Minidregg.Selvage.Ir2Fri.Witnesses

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.farWord_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.farWord_not_mem

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.farWord_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.farWord_far

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.fold_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.fold_one

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.block_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.block_one

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.terminal_and_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.terminal_and_steps

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.input_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.input_zero

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.input_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.input_one

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.zero_accepts

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.initial_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.initial_rejects

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.premises_inhabited

/-- info: 'Minidregg.Selvage.Ir2Fri.Witnesses.sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.Witnesses.sound_fires

