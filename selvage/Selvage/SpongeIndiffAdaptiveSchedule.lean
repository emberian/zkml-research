/-
# Selvage.SpongeIndiffAdaptiveSchedule — prefix causality and conditional bad price

This module joins the two preceding pieces of the sponge-indifferentiability
run argument:

* `SpongeIndiffRunInvariant` threads the exact off-bad premise through the
  actual adaptive `idealStep` transition;
* `AdaptiveFiniteSampling` prices prefix-dependent finite bad sets; and
* `SpongeIndiffCapacityBudget` exposes the branch-specific avoid set and its
  deterministic size.

Here the ideal state before coordinate `i` is computed from precisely those
steps whose indices are `< i`.  It is proved insensitive to all later capacity
coins.  Consequently the evolving simulator avoid set is prefix-measurable,
has size at most `2q+2`, and its conditional failure probability for every
fixed rate/block-rate schedule is at most `q(2q+2)/|Cap|`.

The bound is intentionally the first honest run-level price, not the final
headline constant: it uses the global `q` log-length ceiling at every round.
Sharpening the per-round sizes and transporting this conditional result through
the full `(rate, block-rate, capacity)` product coin space are separate,
straightforward refinements.  The random-permutation/function switching hop is
still outside this module.
-/
import Selvage.SpongeIndiffCapacityBudget

namespace Minidregg.Selvage

section AdaptiveSchedule

variable {Rate Cap : Type} [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
  [DecidableEq Rate] [DecidableEq Cap] [Nonempty Cap]

/-- Replace only the capacity coordinate of a fixed ideal-game coin schedule. -/
def withCapacity {q : Nat} (base : Fin q → Rate × Rate)
    (capacity : Fin q → Cap) : Fin q → Rate × (Rate × Cap) :=
  fun j => ((base j).1, ((base j).2, capacity j))

/-- The actual step indices strictly preceding numeric round `n`. -/
def idealPrefixSteps (q n : Nat) : List (Fin q) :=
  (List.finRange q).filter fun j => (j : Nat) < n

@[simp] theorem mem_idealPrefixSteps {q n : Nat} (j : Fin q) :
    j ∈ idealPrefixSteps q n ↔ (j : Nat) < n := by
  simp [idealPrefixSteps]

/-- The ideal state after exactly the rounds whose indices are `< n`. -/
noncomputable def idealPrefixState {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (n : Nat) :
    IdealState Rate Cap :=
  (idealPrefixSteps q n).foldl (idealStep D iv coins)
    ⟨Oracle.empty, Oracle.empty, []⟩

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
lemma idealStep_eq_of_coin_eq {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q) (h : coins j = coins' j) :
    idealStep D iv coins st j = idealStep D iv coins' st j := by
  unfold idealStep
  rw [h]

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- Two ideal folds agree when their coin schedules agree at every listed
step, from any common intermediate state. -/
theorem foldl_idealStep_congr {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → Rate × (Rate × Cap))
    (steps : List (Fin q)) (st : IdealState Rate Cap)
    (hlisted : ∀ j ∈ steps, coins j = coins' j) :
    steps.foldl (idealStep D iv coins) st =
      steps.foldl (idealStep D iv coins') st := by
  induction steps generalizing st with
  | nil => rfl
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [idealStep_eq_of_coin_eq D iv coins coins' st j
        (hlisted j (by simp))]
      apply ih (st := idealStep D iv coins' st j)
      intro k hk
      exact hlisted k (by simp [hk])

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- A prefix state depends only on the coins of the listed earlier steps. -/
theorem idealPrefixState_congr {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → Rate × (Rate × Cap)) (n : Nat)
    (hcoins : ∀ j : Fin q, (j : Nat) < n → coins j = coins' j) :
    idealPrefixState D iv coins n = idealPrefixState D iv coins' n := by
  unfold idealPrefixState
  apply foldl_idealStep_congr
  intro j hj
  exact hcoins j (mem_idealPrefixSteps j |>.mp hj)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- Folding `n` ideal steps grows the shared simulator log by at most `n`. -/
theorem foldl_idealStep_log_length_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap))
    (steps : List (Fin q)) (st : IdealState Rate Cap) :
    (steps.foldl (idealStep D iv coins) st).sim.log.length
      ≤ st.sim.log.length + steps.length := by
  induction steps generalizing st with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hone := idealStep_sim_log_length_le D iv coins st j
      have htail := ih (idealStep D iv coins st j)
      omega

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- Every prefix state of a `q`-query run has at most `q` simulator entries. -/
theorem idealPrefixState_log_length_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (n : Nat) :
    (idealPrefixState D iv coins n).sim.log.length ≤ q := by
  have hfold := foldl_idealStep_log_length_le D iv coins
    (idealPrefixSteps q n) ⟨Oracle.empty, Oracle.empty, []⟩
  have hfilter : (idealPrefixSteps q n).length ≤ q := by
    calc
      (idealPrefixSteps q n).length ≤ (List.finRange q).length := by
        exact List.length_filter_le _ _
      _ = q := List.length_finRange
  have hfold' :
      (idealPrefixState D iv coins n).sim.log.length ≤
        (idealPrefixSteps q n).length := by
    change
      ((idealPrefixSteps q n).foldl (idealStep D iv coins)
        ⟨Oracle.empty, Oracle.empty, []⟩).sim.log.length ≤
          (idealPrefixSteps q n).length
    simpa only [Oracle.empty, List.length_nil, Nat.zero_add] using hfold
  exact hfold'.trans hfilter

/-- The evolving avoid set presented as a function of the capacity vector. -/
noncomputable def adaptiveCapacityAvoid {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (base : Fin q → Rate × Rate) (capacity : Fin q → Cap)
    (i : Fin q) : Finset Cap :=
  idealCapacityAvoid D iv
    (idealPrefixState D iv (withCapacity base capacity) i)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- Prefix causality: changing the current or any later capacity coin cannot
change the current round's avoid set. -/
theorem adaptiveCapacityAvoid_prefix {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (base : Fin q → Rate × Rate) (i : Fin q)
    (capacity capacity' : Fin q → Cap)
    (hprefix : ∀ j : Fin q, (j : Nat) < (i : Nat) →
      capacity j = capacity' j) :
    adaptiveCapacityAvoid D iv base capacity i =
      adaptiveCapacityAvoid D iv base capacity' i := by
  unfold adaptiveCapacityAvoid
  congr 1
  apply idealPrefixState_congr
  intro j hj
  simp only [withCapacity]
  rw [hprefix j hj]

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- Uniform global cardinality ceiling for every adaptive round. -/
theorem adaptiveCapacityAvoid_card_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (base : Fin q → Rate × Rate) (capacity : Fin q → Cap)
    (i : Fin q) :
    (adaptiveCapacityAvoid D iv base capacity i).card ≤ 2 * q + 2 := by
  unfold adaptiveCapacityAvoid
  refine (idealCapacityAvoid_card_le D iv _).trans ?_
  have hlog := idealPrefixState_log_length_le D iv
    (withCapacity base capacity) i
  omega

omit [Fintype Rate] [DecidableEq Rate] in
/-- **The first whole-run adaptive capacity price.**  For every fixed schedule
of rate coins and block-rate coins, the probability that some capacity coin
hits the simulator avoid set chosen from its earlier prefix is at most
`q(2q+2)/|Cap|`. -/
theorem adaptiveCapacityFailure_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (base : Fin q → Rate × Rate) :
    uniformProb (Fin q → Cap) (fun capacity =>
      ∃ i : Fin q, capacity i ∈ adaptiveCapacityAvoid D iv base capacity i)
      ≤ (q : Real) * (((2 * q + 2 : Nat) : Real) / Fintype.card Cap) := by
  exact adaptiveFiniteUnionBound
    (fun capacity i => adaptiveCapacityAvoid D iv base capacity i)
    (fun i r r' h => adaptiveCapacityAvoid_prefix D iv base i r r' h)
    (fun r i => adaptiveCapacityAvoid_card_le D iv base r i)

/-- Lossless separation of the actual ideal-game coin schedule into its fixed
rate/block-rate schedule and its sampled capacity schedule. -/
def splitIdealCoins (q : Nat) :
    (Fin q → Rate × (Rate × Cap)) ≃
      ((Fin q → Rate × Rate) × (Fin q → Cap)) where
  toFun coins :=
    (fun j => ((coins j).1, (coins j).2.1), fun j => (coins j).2.2)
  invFun parts := withCapacity parts.1 parts.2
  left_inv coins := by
    funext j
    exact Prod.ext rfl (Prod.ext rfl rfl)
  right_inv parts := by
    rcases parts with ⟨base, capacity⟩
    apply Prod.ext <;> funext j <;> rfl

/-- The adaptive capacity-failure event directly on the actual ideal-game coin
space. -/
noncomputable def IdealAdaptiveCapacityFailure {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) : Prop :=
  ∃ i : Fin q, (coins i).2.2 ∈
    adaptiveCapacityAvoid D iv
      (fun j => ((coins j).1, (coins j).2.1))
      (fun j => (coins j).2.2) i

omit [DecidableEq Rate] in
/-- **Full ideal-coin transport.**  The conditional adaptive capacity price
holds on the exact coin space consumed by `idealRun`, not merely after fixing
the other two coin coordinates by hand. -/
theorem idealAdaptiveCapacityFailure_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) :
    uniformProb (Fin q → Rate × (Rate × Cap))
      (IdealAdaptiveCapacityFailure D iv)
      ≤ (q : Real) * (((2 * q + 2 : Nat) : Real) / Fintype.card Cap) := by
  have htransport :
      uniformProb (Fin q → Rate × (Rate × Cap))
          (IdealAdaptiveCapacityFailure D iv)
        = uniformProb ((Fin q → Rate × Rate) × (Fin q → Cap))
          (fun parts => ∃ i : Fin q,
            parts.2 i ∈ adaptiveCapacityAvoid D iv parts.1 parts.2 i) := by
    rw [← uniformProb_equiv (splitIdealCoins (Rate := Rate) (Cap := Cap) q)
      (fun parts => ∃ i : Fin q,
        parts.2 i ∈ adaptiveCapacityAvoid D iv parts.1 parts.2 i)]
    apply uniformProb_congr
    intro coins
    rfl
  rw [htransport]
  refine uniformProb_prod_le (by positivity) fun base => ?_
  simpa using adaptiveCapacityFailure_le D iv base

end AdaptiveSchedule

/-! ## A changing two-round simulator schedule -/

namespace SpongeAdaptiveScheduleExample

def iv : ZMod 2 × Fin 5 := (0, 0)

def twoForward : Distinguisher (ZMod 2) (Fin 5) 2 where
  move ans := if ans.isEmpty then .fwd (1, 0) else .fwd (1, 1)
  out _ := true

def base : Fin 2 → ZMod 2 × ZMod 2 := fun _ => (0, 0)

def capsA : Fin 2 → Fin 5 := fun _ => 2
def capsB : Fin 2 → Fin 5 := fun j => if j = 0 then 3 else 4

/-- Round zero's avoid set ignores every capacity coin. -/
theorem round0_same :
    adaptiveCapacityAvoid twoForward iv base capsA 0 =
      adaptiveCapacityAvoid twoForward iv base capsB 0 := by
  apply adaptiveCapacityAvoid_prefix
  intro j hj
  omega

/-- The generic adaptive probability theorem fires on the concrete two-step
schedule; no assertion that the avoid set is fixed is needed. -/
theorem failure_le :
    uniformProb (Fin 2 → Fin 5) (fun capacity =>
      ∃ i : Fin 2,
        capacity i ∈ adaptiveCapacityAvoid twoForward iv base capacity i)
      ≤ (2 : Real) * (((6 : Nat) : Real) / 5) := by
  simpa using adaptiveCapacityFailure_le twoForward iv base

end SpongeAdaptiveScheduleExample

/-- info: 'Minidregg.Selvage.adaptiveCapacityAvoid_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adaptiveCapacityAvoid_prefix
/-- info: 'Minidregg.Selvage.adaptiveCapacityFailure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adaptiveCapacityFailure_le
/-- info: 'Minidregg.Selvage.idealAdaptiveCapacityFailure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealAdaptiveCapacityFailure_le

end Minidregg.Selvage
