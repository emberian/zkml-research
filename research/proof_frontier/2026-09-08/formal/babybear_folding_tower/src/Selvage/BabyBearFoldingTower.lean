/-
# An actual 2^20 → ... → 2 BabyBearExt4 FoldingTower

Domains use natural powers of the certified scalar 2^20 root inside the
existing X^4-11 extension. All embeddings, squaring/negation fibres and index
maps are derived; the sampled consumer's tower premise is discharged.
-/
import Selvage.BabyBearTwoAdic
import Selvage.PowerTwoRootFolding
import Selvage.FullUDSamplingBudget

namespace Minidregg.Selvage.BabyBearExt4
namespace MultiplicativeTower

noncomputable section
open Polynomial

/-- The actual 20-bit source root in the actual extension carrier. -/
def initialRoot : Ext4 := TwoAdic.omega 20

/-- Statement-first domain/tower contract at the sampled consumer's dimensions. -/
def Correctness (T : FoldingTower Ext4 (PowerTwoFriLevels 20) 19) : Prop :=
  PowerTwoRootFolding.TowerContract initialRoot T

theorem initialRoot_primitive : IsPrimitiveRoot initialRoot (2^20) :=
  TwoAdic.omega_primitive 20 (by decide)

/-- Characteristic-two exclusion is proved through the actual base-field embedding. -/
theorem two_ne_zero : (2 : Ext4) ≠ 0 := by
  have h : (2 : BabyBear) ≠ 0 := by decide
  have hinj := (algebraMap BabyBear Ext4).injective
  simpa only [map_ofNat, map_zero] using fun hz => h (hinj hz)

/-- All 19 transition objects and their shared domain embeddings are realized. -/
def tower : FoldingTower Ext4 (PowerTwoFriLevels 20) 19 :=
  PowerTwoRootFolding.tower initialRoot_primitive two_ne_zero (by decide)

/-- The actual tower satisfies its exact natural-power/modulo contract. -/
theorem correctness : Correctness tower :=
  PowerTwoRootFolding.tower_contract initialRoot_primitive two_ne_zero (by decide)

/-- No empty-type or hypothetical-field premise is used to inhabit the tower. -/
theorem tower_premise_inhabited :
    ∃ T : FoldingTower Ext4 (PowerTwoFriLevels 20) 19, Correctness T :=
  ⟨tower, correctness⟩

/-- Source-root convention at every supported level: the runtime's repeated squaring. -/
theorem levelRoot_source (n : ℕ) (hn : n ≤ 20) :
    PowerTwoRootFolding.levelRoot initialRoot n = TwoAdic.omega (20-n) := by
  unfold PowerTwoRootFolding.levelRoot initialRoot TwoAdic.omega
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

/-- The concrete embeddings use the exact source root for that level size. -/
theorem domain_source (n : ℕ) (hn : n ≤ 20) (i : PowerTwoFriLevels 20 n) :
    tower.dom n i = (TwoAdic.omega (20-n))^i.val := by
  change (PowerTwoRootFolding.levelRoot initialRoot n)^i.val = _
  rw [levelRoot_source n hn]

/-- Every index in every tower domain is nonzero, including the first index. -/
theorem domain_ne_zero (n : ℕ) (i : PowerTwoFriLevels 20 n) : tower.dom n i ≠ 0 := by
  exact pow_ne_zero _ (pow_ne_zero _ (initialRoot_primitive.ne_zero (by norm_num)))

/-- The initial domain is the multiplicative subgroup, beginning at 1. -/
theorem initial_domain_zero_index : tower.dom 0 (0 : Fin (2^20)) = 1 := by
  change (PowerTwoRootFolding.levelRoot initialRoot 0)^0 = 1
  simp

/-- The original consecutive-subfield domain's zero point cannot identify this tower. -/
theorem consecutive_domain_falsifier :
    tower.dom 0 (0 : Fin (2^20)) ≠
      FullUDInstantiation.domain (0 : Fin (2^20)) := by
  rw [initial_domain_zero_index]
  change (1 : Ext4) ≠ algebraMap BabyBear Ext4 0
  simp

/-- The actual initial evaluation embedding, with no parallel RS definition. -/
abbrev initialDomain : Fin (2^20) ↪ Ext4 := tower.dom 0

/-- A degree-exactly-2^19 polynomial evaluated on the actual multiplicative domain. -/
def farWord : Fin (2^20) → Ext4 := fun i => (initialDomain i)^(2^19)

/-- The source degree really lies outside the degree-below-2^19 code. -/
theorem farWord_not_mem : farWord ∉ reedSolomonCode initialDomain (2^19) := by
  classical
  intro hw
  obtain ⟨p, hp, heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hne : (X^(2^19) : Polynomial Ext4) ≠ p := by
    intro heq
    rw [← heq] at hp
    norm_num at hp
  have hcard := card_agreeSet_lt_of_ne initialDomain (d := 2^19+1)
    (p := (X^(2^19) : Polynomial Ext4)) (by norm_num)
    (q := p) (hp.trans (by norm_num)) hne
  have hfull : (Finset.univ.filter fun i =>
      (X^(2^19) : Polynomial Ext4).eval (initialDomain i) = p.eval (initialDomain i)) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    simpa [farWord] using heval i
  rw [hfull, Finset.card_univ, Fintype.card_fin] at hcard
  norm_num at hcard

/-- The same word lies in the immediately larger degree window. -/
theorem farWord_mem_successor : farWord ∈ reedSolomonCode initialDomain (2^19+1) := by
  exact mem_reedSolomonCode_iff.mpr
    ⟨X^(2^19), by norm_num, fun i => by simp [farWord]⟩

/-- Existing RS minimum distance gives a 1/2 lower bound against every legal source word. -/
theorem farWord_relDist (w : Fin (2^20) → Ext4)
    (hw : w ∈ reedSolomonCode initialDomain (2^19)) : (1/2 : ℝ) ≤ relDist farWord w := by
  have hw' : w ∈ reedSolomonCode initialDomain (2^19+1) := by
    obtain ⟨p, hp, heval⟩ := mem_reedSolomonCode_iff.mp hw
    exact mem_reedSolomonCode_iff.mpr ⟨p, hp.trans (by norm_num), heval⟩
  have hne : farWord ≠ w := fun h => farWord_not_mem (h ▸ hw)
  have h := reedSolomonCode_minDist initialDomain (2^19+1)
    farWord farWord_mem_successor w hw' hne
  norm_num at h ⊢
  exact h

/-- The actual sampled theorem's 2/5 initial-farness premise is inhabited. -/
theorem farWord_far : ¬ close (2/5 : ℝ)
    (reedSolomonCode (tower.dom 0) (fullUDSamplingDegree 0)) farWord := by
  rintro ⟨w, hw, hclose⟩
  have hdist := farWord_relDist w hw
  linarith

/-- Increasing the degree window invalidates this claimed farness. -/
theorem source_degree_falsifier :
    close (2/5 : ℝ) (reedSolomonCode initialDomain (2^19+1)) farWord := by
  exact ⟨farWord, farWord_mem_successor, by norm_num [relDist, hammingDist]⟩

/-- Actual field, actual 19-round tower and actual source farness are inhabited together. -/
theorem tower_and_farness_inhabited :
    ∃ T : FoldingTower Ext4 (PowerTwoFriLevels 20) 19,
      ∃ w : PowerTwoFriLevels 20 0 → Ext4,
        Correctness T ∧ ¬ close (2/5 : ℝ)
          (reedSolomonCode (T.dom 0) (fullUDSamplingDegree 0)) w :=
  ⟨tower, farWord, correctness, farWord_far⟩

/-- The existing BabyBear coherent head now has an actual tower; transcript,
exact binding and initial farness remain explicit at this interface. -/
theorem coherent_sound {Root Op : ℕ → Type}
    (S : ∀ n, BindingCommitment (Root n) Ext4 (PowerTwoFriLevels 20 n) (Op n))
    (st : FriAdaptiveTranscript S)
    (hfar0 : ¬ close (2/5 : ℝ)
      (reedSolomonCode (tower.dom 0) (fullUDSamplingDegree 0))
      (st.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin 19 → Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1))
      (fun x => FriAdaptiveCoherentAccepts S tower fullUDSamplingDegree st
        (by decide) 3603 x.1 x.2) ≤ 1/(2^55 : ℝ) :=
  fullUDSampling_babyBear_55 S tower st hfar0

end
end MultiplicativeTower
end Minidregg.Selvage.BabyBearExt4

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.initialRoot_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.initialRoot_primitive
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.two_ne_zero
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.correctness
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.tower_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.tower_premise_inhabited
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.levelRoot_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.levelRoot_source
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.domain_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.domain_source
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.domain_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.domain_ne_zero
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.initial_domain_zero_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.initial_domain_zero_index
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.consecutive_domain_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.consecutive_domain_falsifier
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_not_mem
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_mem_successor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_mem_successor
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_relDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_relDist
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.farWord_far
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.source_degree_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.source_degree_falsifier
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.tower_and_farness_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.tower_and_farness_inhabited
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.coherent_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.coherent_sound
