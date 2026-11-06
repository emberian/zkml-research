/-! Small exact counterexamples; no imported package or proof placeholder. -/
namespace Astra.DarkLearningCounterexamples

theorem public_linear_expiry_counterexample :
    (2 * (2 * (0 : Int) + 1) + 0) - 1 ≠ 2 * 0 + 0 := by decide

theorem cancelling_corrupt_steps :
    (0 : Int) + 1 - 1 = 0 ∧ (0 : Int) + 1 ≠ 0 := by decide

theorem negative_contraction_substitution :
    (0 : Int) ≤ 1 ∧ ¬ ((-1 : Int) * 0 ≤ (-1 : Int) * 1) := by decide

theorem unsigned_is_not_signed :
    (-1 : Int) % 7 = 6 ∧ (-1 : Int) % 7 ≠ -1 := by decide

/-- info: 'Astra.DarkLearningCounterexamples.public_linear_expiry_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms public_linear_expiry_counterexample
/-- info: 'Astra.DarkLearningCounterexamples.cancelling_corrupt_steps' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cancelling_corrupt_steps
/-- info: 'Astra.DarkLearningCounterexamples.negative_contraction_substitution' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms negative_contraction_substitution
/-- info: 'Astra.DarkLearningCounterexamples.unsigned_is_not_signed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms unsigned_is_not_signed
end Astra.DarkLearningCounterexamples
