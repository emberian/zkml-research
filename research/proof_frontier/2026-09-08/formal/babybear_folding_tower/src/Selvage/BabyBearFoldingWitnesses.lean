/-
# Nonvacuous actual-carrier sampled FRI instance

The initial word is provably 2/5-far on the actual 2^20 multiplicative domain.
The strategy chooses constant 1 after its first commitment. All-zero query
seeds accept, while query index 1 rejects the first round. Thus the concrete
probability head has inhabited premises and an inhabited acceptance event.
-/
import Selvage.BabyBearFoldingTower

namespace Minidregg.Selvage.BabyBearExt4.MultiplicativeTower
namespace Witnesses

noncomputable section

abbrev schemes (n : ℕ) := idealCommitment Ext4 (PowerTwoFriLevels 20 n)

/-- Statement-first nonvacuity target for the actual sampled consumer. -/
def ConsumerInhabitation : Prop :=
  ∃ st : FriAdaptiveTranscript schemes,
    (¬ close (2/5 : ℝ) (reedSolomonCode (tower.dom 0) (fullUDSamplingDegree 0))
      (st.word 0 (fun i => i.elim0))) ∧
    ∃ r seed, FriAdaptiveCoherentAccepts schemes tower fullUDSamplingDegree st
      (by decide) 3603 r seed

/-- The initial high-degree word followed by constant-1 commitments. -/
def selectedWord : ∀ n, (Fin n → Ext4) → PowerTwoFriLevels 20 n → Ext4
  | 0, _ => farWord
  | _+1, _ => fun _ => 1

def transcript : FriAdaptiveTranscript schemes where
  word := selectedWord
  root := selectedWord
  root_eq_commit _ _ := rfl

/-- The source polynomial has even degree, so its first fold is independent
of the challenge. This uses the actual derived negation fibre. -/
theorem first_fold (a : Ext4) (k : PowerTwoFriLevels 20 1) :
    fold (tower.data 0 (by decide)) farWord a k =
      (tower.dom 0 ((tower.data 0 (by decide)).sec k))^(2^19) := by
  let D := tower.data 0 (by decide)
  have heven : Even (2^19) := ⟨2^18, by norm_num⟩
  change ((tower.dom 0 (D.sec k))^(2^19) +
      (tower.dom 0 (D.neg (D.sec k)))^(2^19))/2 +
    a*(((tower.dom 0 (D.sec k))^(2^19) -
      (tower.dom 0 (D.neg (D.sec k)))^(2^19))/(2*tower.dom 0 (D.sec k))) = _
  rw [D.dom_neg, heven.neg_pow]
  field_simp [two_ne_zero]
  ring

/-- Query zero's first fold is exactly the strategy's claimed constant 1. -/
theorem first_fold_zero (a : Ext4) :
    fold (tower.data 0 (by decide)) farWord a (0 : PowerTwoFriLevels 20 1) = 1 := by
  rw [first_fold]
  change ((PowerTwoRootFolding.levelRoot initialRoot 0)^0)^(2^19) = 1
  simp

/-- Query one's first fold is -1, providing a concrete rejected query. -/
theorem first_fold_one (a : Ext4) :
    fold (tower.data 0 (by decide)) farWord a (1 : PowerTwoFriLevels 20 1) = -1 := by
  rw [first_fold]
  change ((PowerTwoRootFolding.levelRoot initialRoot 0)^1)^(2^19) = -1
  simp only [PowerTwoRootFolding.levelRoot, pow_zero, pow_one]
  exact TwoAdic.omega_half_turn 19 (by decide)

/-- Farness is proved for this actual strategy's actual initial word. -/
theorem initial_farness :
    ¬ close (2/5 : ℝ) (reedSolomonCode (tower.dom 0) (fullUDSamplingDegree 0))
      (transcript.word 0 (fun i => i.elim0)) := farWord_far

/-- Every round is consistent at the zero query along the selected strategy. -/
theorem zero_fold_equation (r : Fin 19 → Ext4) (j : Fin 19) :
    transcript.wordAt r (j+1) (Nat.succ_le_iff.mpr j.isLt) 0 =
      fold (tower.data j j.isLt)
        (transcript.wordAt r j (Nat.le_of_lt j.isLt)) (r j) 0 := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => exact (first_fold_zero (r 0)).symm
  | succ j =>
    change (1 : Ext4) = fold (tower.data (j+1) hj) (fun _ => 1) (r ⟨j+1,hj⟩) 0
    simp only [fold, foldEven, foldOdd, sub_self, zero_div, mul_zero, add_zero]
    rw [show (1 : Ext4)+1 = 2 by ring, div_self two_ne_zero]

/-- Concrete accepting executions exist for all challenge vectors and query counts. -/
theorem zero_queries_accept (r : Fin 19 → Ext4) (qCount : ℕ) :
    FriAdaptiveCoherentAccepts schemes tower fullUDSamplingDegree transcript
      (by decide) qCount r (fun _ => 0) := by
  have hQ : powerTwoCoherentSchedule (show 19 ≤ 20 by decide)
      (fun _ : Fin qCount => (0 : PowerTwoFriLevels 20 1)) = fun _ _ => 0 := by
    funext j a
    apply Fin.ext
    simp [powerTwoCoherentSchedule, powerTwoCoherentRound, powerTwoRoundIndex]
  unfold FriAdaptiveCoherentAccepts
  rw [hQ]
  constructor
  · intro j
    let w := transcript.wordAt r j (Nat.le_of_lt j.isLt)
    let w' := transcript.wordAt r (j+1) (Nat.succ_le_iff.mpr j.isLt)
    let D := tower.data j j.isLt
    refine ⟨fun _ => {
      left := w (D.sec 0)
      right := w (D.neg (D.sec 0))
      next := w' 0
      leftPath := ()
      rightPath := ()
      nextPath := () }, fun _ => ?_⟩
    exact ⟨rfl, rfl, rfl, zero_fold_equation r j⟩
  · change (fun _ => (1 : Ext4)) ∈ reedSolomonCode (tower.dom 19) 1
    exact mem_reedSolomonCode_one_iff.mpr (fun _ _ => rfl)

/-- The complete actual-carrier consumer premise and acceptance event are inhabited. -/
theorem consumer_inhabited : ConsumerInhabitation :=
  ⟨transcript, initial_farness, (fun _ => 0), (fun _ => 0),
    zero_queries_accept (fun _ => 0) 3603⟩

/-- The query verifier has teeth on the same far strategy: index 1 rejects. -/
theorem query_one_falsifier (r : Fin 19 → Ext4) :
    ¬ FriAdaptiveRoundQueriesAccept schemes tower transcript r (0 : Fin 19)
      (fun _ : Fin 1 => (1 : PowerTwoFriLevels 20 1)) := by
  intro h
  have heq := friAdaptiveRoundQueries_pins schemes tower transcript r (0 : Fin 19) h (0 : Fin 1)
  change (1 : Ext4) = fold (tower.data 0 (by decide)) farWord (r 0) 1 at heq
  rw [first_fold_one] at heq
  have htwo : (2 : Ext4) = 0 := by linear_combination heq
  exact two_ne_zero htwo

/-- Inhabited acceptance has strictly positive mass in this actual finite experiment. -/
theorem witnessed_probability_positive :
    0 < uniformProb ((Fin 19 → Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1))
      (fun x => FriAdaptiveCoherentAccepts schemes tower fullUDSamplingDegree
        transcript (by decide) 3603 x.1 x.2) := by
  classical
  let A := {x : (Fin 19 → Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1) //
    FriAdaptiveCoherentAccepts schemes tower fullUDSamplingDegree transcript
      (by decide) 3603 x.1 x.2}
  haveI : Nonempty A := ⟨⟨((fun _ => 0), (fun _ => 0)),
    zero_queries_accept (fun _ => 0) 3603⟩⟩
  unfold uniformProb
  apply div_pos
  · exact_mod_cast (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩ : 0 < Nat.card A)
  · exact_mod_cast Fintype.card_pos

/-- The actual tower, binding interface, far strategy and probability head
are all instantiated; no deployment transcript realization is claimed. -/
theorem witnessed_sound :
    uniformProb ((Fin 19 → Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1))
      (fun x => FriAdaptiveCoherentAccepts schemes tower fullUDSamplingDegree
        transcript (by decide) 3603 x.1 x.2) ≤ 1/(2^55 : ℝ) :=
  coherent_sound schemes transcript initial_farness

end
end Witnesses
end Minidregg.Selvage.BabyBearExt4.MultiplicativeTower

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold_zero
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.first_fold_one
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.initial_farness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.initial_farness
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.zero_fold_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.zero_fold_equation
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.zero_queries_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.zero_queries_accept
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.consumer_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.consumer_inhabited
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.query_one_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.query_one_falsifier
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.witnessed_probability_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.witnessed_probability_positive
/-- info: 'Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.witnessed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BabyBearExt4.MultiplicativeTower.Witnesses.witnessed_sound
