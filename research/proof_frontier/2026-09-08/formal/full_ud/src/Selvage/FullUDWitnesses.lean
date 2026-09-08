/-
# A realizer firing beyond the previous radius band

Toy witness, type-distinct from deployment parameters: eight evaluation
points over ZMod11, degree bound four, relative radius one fifth.
-/
import Selvage.ProximityGapFullUD

namespace Minidregg.Selvage.FullUDWitness
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The actual good line has probability one at the wider radius. -/
theorem line_pr_one_fullUD :
    (affineGenerator (ZMod 11)).pr (fun r =>
      close (1/5 : ℝ) (reedSolomonCode dom 4) (comb r pair)) = 1 := by
  classical
  have hall : ∀ z : ZMod 11,
      close (1/5 : ℝ) (reedSolomonCode dom 4)
        (comb ((affineGenerator (ZMod 11)).gen z) pair) := by
    intro z
    have heq : comb ((affineGenerator (ZMod 11)).gen z) pair = xWord + z • oneWord :=
      funext fun i => by rw [comb_affineGenerator]; rfl
    rw [heq]
    exact close_of_mem ((reedSolomonCode dom 4).add_mem x_mem
      ((reedSolomonCode dom 4).smul_mem z one_mem)) (by norm_num)
  unfold ProximityGenerator.pr
  simp only [hall, Finset.filter_true]
  exact (affineGenerator (ZMod 11)).weight_sum_one

/-- The new theorem, rather than a hand-supplied conclusion, produces the
correlated agreement at radius one fifth. -/
theorem good_line_CA_fullUD :
    CorrelatedAgreement (reedSolomonCode dom 4) (1/5 : ℝ) pair := by
  refine reedSolomonCode_isProximityGenerator_fullUD dom 4 (by norm_num)
    pair (1/5 : ℝ) (by norm_num) ?_ ?_
  · norm_num
  · rw [line_pr_one_fullUD]
    norm_num [ZMod.card]

/-- The former radius condition fails on precisely this firing site. -/
theorem old_band_rejects_fullUD_witness :
    ¬ (1/5 : ℝ) < 1-(2+(4 : ℝ)/(Fintype.card (Fin 8) : ℝ))/3 := by
  norm_num

/-- All source premises of the new hPG head are inhabited together, with a
strictly positive rate and a probability strictly above the error bound. -/
theorem fullUD_generator_premise_inhabited :
    ∃ f : Fin 2 → Fin 8 → ZMod 11,
      (0 : ℝ) < 1/5 ∧
      (1/5 : ℝ) < 1-(1+(4 : ℝ)/(Fintype.card (Fin 8) : ℝ))/2 ∧
      (Fintype.card (Fin 8) : ℝ)/(Fintype.card (ZMod 11) : ℝ) <
        (affineGenerator (ZMod 11)).pr (fun r =>
          close (1/5 : ℝ) (reedSolomonCode dom 4) (comb r f)) := by
  refine ⟨pair,by norm_num,by norm_num,?_⟩
  rw [line_pr_one_fullUD]
  norm_num [ZMod.card]

/-- info: 'Minidregg.Selvage.FullUDWitness.line_pr_one_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms line_pr_one_fullUD
/-- info: 'Minidregg.Selvage.FullUDWitness.good_line_CA_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms good_line_CA_fullUD
/-- info: 'Minidregg.Selvage.FullUDWitness.old_band_rejects_fullUD_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms old_band_rejects_fullUD_witness
/-- info: 'Minidregg.Selvage.FullUDWitness.fullUD_generator_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullUD_generator_premise_inhabited

end Minidregg.Selvage.FullUDWitness
