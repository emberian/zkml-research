/-
# Full unique-decoding target over Selvage's existing Reed–Solomon code

Statement-first contract for the theorem in FullUDCore. This module states
the integer cardinality core and pins a nonempty premise. The radius-premise
falsifier is in FullUDTeeth; the existing consumer is in FullUDFriConsumer.
-/
import Selvage.Proximity

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The proposed full-UD cardinality core, stated in existing code/distance
language. Its theorem will require `1 ≤ d` and `2*e+d ≤ card ι`. -/
def FullUDCardCore (dom : ι ↪ F) (d e : ℕ) : Prop :=
  ∀ (f : Fin 2 → ι → F) (A : Finset F),
    (∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (f 0 + z • f 1) w ≤ e) →
    Fintype.card ι < A.card →
    ∃ S : Finset ι, Fintype.card ι - e ≤ S.card ∧
      ∀ j, ∃ w ∈ reedSolomonCode dom d, AgreesOn S (f j) w

/-- Concrete admissibility and good-slope data. The cardinality condition
rules out an empty/all-impossible source premise. -/
def FullUDPremise (dom : ι ↪ F) (d e : ℕ)
    (f : Fin 2 → ι → F) (A : Finset F) : Prop :=
  1 ≤ d ∧ 2 * e + d ≤ Fintype.card ι ∧
    Fintype.card ι < A.card ∧
    ∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (f 0 + z • f 1) w ≤ e

namespace FullUDWitness

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def dom : Fin 8 ↪ ZMod 11 where
  toFun i := i.val
  inj' := by
    intro a b hab
    have ha : a.val < 11 := lt_trans a.isLt (by decide)
    have hb : b.val < 11 := lt_trans b.isLt (by decide)
    apply Fin.ext
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

def xWord : Fin 8 → ZMod 11 := fun i => dom i
def oneWord : Fin 8 → ZMod 11 := fun _ => 1
def pair : Fin 2 → Fin 8 → ZMod 11 := ![xWord, oneWord]

theorem x_mem : xWord ∈ reedSolomonCode dom 4 := by
  apply mem_reedSolomonCode_iff.mpr
  exact ⟨Polynomial.X, by norm_num, fun i => by simp [xWord]⟩

theorem one_mem : oneWord ∈ reedSolomonCode dom 4 := by
  apply mem_reedSolomonCode_iff.mpr
  exact ⟨1, by norm_num, fun i => by simp [oneWord]⟩

/-- The full-UD source premise fires at rate one half, eight positions and
one-error-pair radius `e=2`. In particular it is not a full-rate/top code. -/
theorem premise_inhabited : FullUDPremise dom 4 2 pair Finset.univ := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro z hz
  refine ⟨xWord + z • oneWord,
    (reedSolomonCode dom 4).add_mem x_mem ((reedSolomonCode dom 4).smul_mem z one_mem), ?_⟩
  simp [pair]

/-- The same witness has all eight jointly explained positions. -/
theorem conclusion_inhabited :
    ∃ S : Finset (Fin 8), 8 - 2 ≤ S.card ∧
      ∀ j, ∃ w ∈ reedSolomonCode dom 4, AgreesOn S (pair j) w := by
  refine ⟨Finset.univ, by simp, ?_⟩
  intro j
  fin_cases j
  · exact ⟨xWord, x_mem, fun _ _ => rfl⟩
  · exact ⟨oneWord, one_mem, fun _ _ => rfl⟩

/-- info: 'Minidregg.Selvage.FullUDWitness.x_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x_mem

/-- info: 'Minidregg.Selvage.FullUDWitness.one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem

end FullUDWitness

/-- info: 'Minidregg.Selvage.FullUDWitness.premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDWitness.premise_inhabited
/-- info: 'Minidregg.Selvage.FullUDWitness.conclusion_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FullUDWitness.conclusion_inhabited

end Minidregg.Selvage
