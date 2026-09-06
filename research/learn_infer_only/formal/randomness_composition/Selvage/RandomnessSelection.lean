/-
Statement-first: a selection rule cannot keep a pointwise probability bound
after seeing the sampled world. It can retain a sum over all possible selected
contexts; a selector fixed before an independent fresh coin retains the fibre
bound. Coin-blind delivery preserves a paired Boolean output distribution.

ATLAS: SelectionTransfer and BlindSelection are named Props before the proofs.
The Boolean diagonal is the failed-premise sibling for a pointwise-to-adaptive
claim. An independent fresh coin and a nonconstant selector inhabit the positive
premise. Delivery based on an independent history bit inhabits nonempty balanced
selection; delivery based on the result is the explicit bias tooth.

This is finite probability on the existing uniformProb carrier, not an FS
multi-context reduction, cryptographic entropy source, or liveness theorem.
It adds no hypothesis declaring honest sampling of an exposed secret.
-/
import Selvage.Depth

namespace Minidregg.Selvage.RandomnessSelection

open scoped BigOperators

/-- The only unconditional transfer from arbitrary world-dependent selection. -/
def SelectionTransfer : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {n : Nat} (bad : Fin n → Ω → Prop)
    (select : Ω → Fin n),
    uniformProb Ω (fun w => bad (select w) w) ≤
      ∑ i : Fin n, uniformProb Ω (bad i)

/-- Delivery does not distinguish the paired hidden-coin worlds. -/
def BlindSelection {Ω : Type} (flip : Ω ≃ Ω) (deliver : Ω → Prop) : Prop :=
  ∀ w, deliver (flip w) ↔ deliver w

/-- Exact Boolean balance, with no conditional-probability denominator hidden. -/
def ReleaseBalanced {Ω : Type} [Fintype Ω]
    (deliver : Ω → Prop) (out : Ω → Bool) : Prop :=
  uniformProb Ω (fun w => deliver w ∧ out w = false) =
    uniformProb Ω (fun w => deliver w ∧ out w = true)

theorem selection_transfer : SelectionTransfer := by
  intro Ω _ n bad select
  exact le_trans (uniformProb_mono (fun w h => ⟨select w, h⟩))
    (uniformProb_exists_le bad)

theorem selection_transfer_uniform {Ω : Type} [Fintype Ω] {n : Nat}
    (bad : Fin n → Ω → Prop) (select : Ω → Fin n) {ε : ℝ}
    (h : ∀ i, uniformProb Ω (bad i) ≤ ε) :
    uniformProb Ω (fun w => bad (select w) w) ≤ (n : ℝ) * ε := by
  calc
    _ ≤ ∑ i : Fin n, uniformProb Ω (bad i) := selection_transfer bad select
    _ ≤ ∑ _i : Fin n, ε := Finset.sum_le_sum (fun i _ => h i)
    _ = (n : ℝ) * ε := by simp

/-- The selector reads only history; the probability premise holds after EVERY
history and for EVERY context. Marginal fixed-context bounds do not imply it. -/
theorem fresh_after_selection {H R C : Type} [Fintype H] [Fintype R]
    (bad : H → C → R → Prop) (select : H → C) {ε : ℝ} (hε : 0 ≤ ε)
    (hfibre : ∀ h c, uniformProb R (bad h c) ≤ ε) :
    uniformProb (H × R) (fun hr => bad hr.1 (select hr.1) hr.2) ≤ ε :=
  uniformProb_prod_le hε (fun h => hfibre h (select h))

theorem coinblind_release_balanced {Ω : Type} [Fintype Ω]
    (flip : Ω ≃ Ω) (deliver : Ω → Prop) (out : Ω → Bool)
    (blind : BlindSelection flip deliver)
    (opposite : ∀ w, out (flip w) = !out w) :
    ReleaseBalanced deliver out := by
  unfold ReleaseBalanced
  calc
    _ = uniformProb Ω (fun w => deliver (flip w) ∧ out (flip w) = false) :=
      (uniformProb_equiv flip (fun w => deliver w ∧ out w = false)).symm
    _ = uniformProb Ω (fun w => deliver w ∧ out w = true) := by
      apply uniformProb_congr
      intro w
      rw [blind w, opposite w]
      cases out w <;> simp

/-- Dividing both masses by the same positive delivery probability preserves
balance. Positivity is a functionality premise, not supplied by blindness. -/
theorem conditional_balance {Ω : Type} [Fintype Ω]
    (deliver : Ω → Prop) (out : Ω → Bool)
    (balanced : ReleaseBalanced deliver out)
    (available : 0 < uniformProb Ω deliver) :
    0 < uniformProb Ω deliver ∧
      uniformProb Ω (fun w => deliver w ∧ out w = false) / uniformProb Ω deliver =
        uniformProb Ω (fun w => deliver w ∧ out w = true) / uniformProb Ω deliver :=
  ⟨available, congrArg (fun p => p / uniformProb Ω deliver) balanced⟩

namespace Witness

theorem bool_single (b : Bool) :
    uniformProb Bool (fun r => r = b) = (1 / 2 : ℝ) := by
  cases b <;> norm_num [uniformProb, Nat.card_eq_fintype_card]

theorem fixed_diagonal_bound (c : Bool) :
    uniformProb Bool (fun w => c = w) = (1 / 2 : ℝ) := by
  simpa only [eq_comm] using bool_single c

theorem adaptive_diagonal_is_one :
    uniformProb Bool (fun w => w = w) = 1 := by
  norm_num [uniformProb, Nat.card_eq_fintype_card]

/-- Two contexts, both meeting their half bound; selecting after the world is
revealed violates that bound. This is not a counterexample to an FS theorem. -/
theorem pointwise_bound_not_adaptive :
    (∀ c : Bool, uniformProb Bool (fun w => c = w) ≤ (1 / 2 : ℝ)) ∧
    ¬ uniformProb Bool (fun w => w = w) ≤ (1 / 2 : ℝ) := by
  constructor
  · intro c
    exact le_of_eq (fixed_diagonal_bound c)
  · rw [adaptive_diagonal_is_one]
    norm_num

theorem fresh_premise_inhabited :
    ∃ (bad : Bool → Bool → Bool → Prop) (select : Bool → Bool),
      select false ≠ select true ∧
      (∀ h c, uniformProb Bool (bad h c) ≤ (1 / 2 : ℝ)) ∧
      uniformProb (Bool × Bool) (fun hr => bad hr.1 (select hr.1) hr.2) ≤
        (1 / 2 : ℝ) := by
  refine ⟨fun _ c r => r = c, id, by decide, ?_, ?_⟩
  · intro _ c
    exact le_of_eq (bool_single c)
  · exact fresh_after_selection (fun _ c r => r = c) id (by norm_num)
      (fun _ c => le_of_eq (bool_single c))

def flipCoin : (Bool × Bool) ≃ (Bool × Bool) where
  toFun := fun w => (!w.1, w.2)
  invFun := fun w => (!w.1, w.2)
  left_inv := by intro w; simp
  right_inv := by intro w; simp

def independentDelivery (w : Bool × Bool) : Prop := w.2 = true

theorem blind_delivery_inhabited :
    BlindSelection flipCoin independentDelivery ∧
    (∃ w, independentDelivery w) ∧ (∃ w, ¬ independentDelivery w) ∧
    ReleaseBalanced independentDelivery Prod.fst := by
  have hb : BlindSelection flipCoin independentDelivery := fun _ => Iff.rfl
  refine ⟨hb, ⟨(false, true), rfl⟩, ⟨(false, false), by simp [independentDelivery]⟩, ?_⟩
  exact coinblind_release_balanced flipCoin independentDelivery Prod.fst hb (fun _ => rfl)

theorem result_filter_not_blind :
    ¬ BlindSelection flipCoin (fun w => w.1 = true) := by
  intro h
  have hx := h (false, false)
  simp [flipCoin] at hx

theorem result_filter_biased :
    ¬ ReleaseBalanced (fun r : Bool => r = true) id := by
  unfold ReleaseBalanced
  have hz : uniformProb Bool (fun r => r = true ∧ id r = false) = 0 :=
    uniformProb_false (by intro r; cases r <;> simp)
  have ho : uniformProb Bool (fun r => r = true ∧ id r = true) = (1 / 2 : ℝ) := by
    simpa using bool_single true
  rw [hz, ho]
  norm_num

end Witness
end Minidregg.Selvage.RandomnessSelection

/-- info: 'Minidregg.Selvage.RandomnessSelection.selection_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.selection_transfer

/-- info: 'Minidregg.Selvage.RandomnessSelection.selection_transfer_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.selection_transfer_uniform

/-- info: 'Minidregg.Selvage.RandomnessSelection.fresh_after_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.fresh_after_selection

/-- info: 'Minidregg.Selvage.RandomnessSelection.coinblind_release_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.coinblind_release_balanced

/-- info: 'Minidregg.Selvage.RandomnessSelection.conditional_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.conditional_balance

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.bool_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.bool_single

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.fixed_diagonal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.fixed_diagonal_bound

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.adaptive_diagonal_is_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.adaptive_diagonal_is_one

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.pointwise_bound_not_adaptive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.pointwise_bound_not_adaptive

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.fresh_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.fresh_premise_inhabited

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.blind_delivery_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.blind_delivery_inhabited

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.result_filter_not_blind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.result_filter_not_blind

/-- info: 'Minidregg.Selvage.RandomnessSelection.Witness.result_filter_biased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.RandomnessSelection.Witness.result_filter_biased

