/-
# Selvage.SpongeIndiffOffBadRun — priced capacity failure or a consistent run

This is the deterministic/probabilistic join for the simulator-log invariant.
It presents the adaptive ideal run recursively by numeric round, proves that
round `n` depends only on coins `< n`, prices the resulting prefix-dependent
capacity failure on the exact ideal-game coin space, and proves that outside
that failure the final simulator log has unique rooted paths.

The recursive state is proved equal to `idealRun`, so the conclusion is about
the landed game rather than a parallel model.  This closes the capacity/run
bookkeeping component of `[SPONGE-indiff-game]`.  It does not compare the ideal
transcript with a random permutation transcript; identical-until-bad and the
random-permutation/random-function switching term remain explicit.
-/
import Selvage.SpongeIndiffAdaptiveSchedule

namespace Minidregg.Selvage

section OffBadRun

variable {Rate Cap : Type} [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
  [DecidableEq Rate] [DecidableEq Cap] [Nonempty Cap]

/-- The ideal state after the first `n` rounds, written recursively so the
current prefix dependency is definitionally visible. -/
noncomputable def idealStateNat {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) :
    (n : Nat) → n ≤ q → IdealState Rate Cap
  | 0, _ => ⟨Oracle.empty, Oracle.empty, []⟩
  | n + 1, hn =>
      idealStep D iv coins
        (idealStateNat D iv coins n (Nat.le_trans (Nat.le_succ n) hn))
        ⟨n, Nat.lt_of_succ_le hn⟩

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- Prefix causality for the recursive actual run. -/
theorem idealStateNat_congr {q n : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → Rate × (Rate × Cap)) (hn : n ≤ q)
    (hcoins : ∀ j : Fin q, (j : Nat) < n → coins j = coins' j) :
    idealStateNat D iv coins n hn = idealStateNat D iv coins' n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold idealStateNat
      rw [ih (Nat.le_trans (Nat.le_succ n) hn)
        (fun j hj => hcoins j (Nat.lt_trans hj (Nat.lt_succ_self n)))]
      apply idealStep_eq_of_coin_eq
      exact hcoins ⟨n, Nat.lt_of_succ_le hn⟩ (by simp)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- The recursive presentation is exactly the finite fold over the first `n`
indices. -/
theorem idealStateNat_eq_foldl {q n : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (hn : n ≤ q) :
    idealStateNat D iv coins n hn =
      Fin.foldl n
        (fun st j => idealStep D iv coins st
          ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩)
        ⟨Oracle.empty, Oracle.empty, []⟩ := by
  induction n with
  | zero => simp [idealStateNat]
  | succ n ih =>
      rw [Fin.foldl_succ_last]
      unfold idealStateNat
      rw [ih (Nat.le_trans (Nat.le_succ n) hn)]
      congr

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- At the full query count, the recursive state is the landed `idealRun`. -/
theorem idealStateNat_full_eq_idealRun {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) :
    idealStateNat D iv coins q (Nat.le_refl q) = idealRun D iv coins := by
  rw [idealStateNat_eq_foldl, Fin.foldl_eq_finRange_foldl]
  unfold idealRun
  congr 1

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    [Nonempty Cap] in
/-- After `n` rounds the shared simulator log has at most `n` entries. -/
theorem idealStateNat_log_length_le {q n : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (hn : n ≤ q) :
    (idealStateNat D iv coins n hn).sim.log.length ≤ n := by
  induction n with
  | zero =>
      change 0 ≤ 0
      exact Nat.le_refl 0
  | succ n ih =>
      unfold idealStateNat
      have hstep := idealStep_sim_log_length_le D iv coins
        (idealStateNat D iv coins n (Nat.le_trans (Nat.le_succ n) hn))
        ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev := ih (Nat.le_trans (Nat.le_succ n) hn)
      omega

/-- Exact avoid set before round `i` in the recursive run. -/
noncomputable def recursiveCapacityAvoid {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (i : Fin q) : Finset Cap :=
  idealCapacityAvoid D iv
    (idealStateNat D iv coins i (Nat.le_of_lt i.isLt))

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- Recursive avoid sets are prefix-measurable. -/
theorem recursiveCapacityAvoid_prefix {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins coins' : Fin q → Rate × (Rate × Cap)) (i : Fin q)
    (hcoins : ∀ j : Fin q, (j : Nat) < (i : Nat) → coins j = coins' j) :
    recursiveCapacityAvoid D iv coins i =
      recursiveCapacityAvoid D iv coins' i := by
  unfold recursiveCapacityAvoid
  rw [idealStateNat_congr D iv coins coins'
    (Nat.le_of_lt i.isLt) hcoins]

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- Every recursive round avoid set has the same global `2q+2` ceiling. -/
theorem recursiveCapacityAvoid_card_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (i : Fin q) :
    (recursiveCapacityAvoid D iv coins i).card ≤ 2 * q + 2 := by
  unfold recursiveCapacityAvoid
  refine (idealCapacityAvoid_card_le D iv _).trans ?_
  have hlog := idealStateNat_log_length_le D iv coins
    (Nat.le_of_lt i.isLt)
  omega

/-- Capacity failure on the exact recursive/landed ideal run. -/
noncomputable def RecursiveCapacityFailure {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) : Prop :=
  ∃ i : Fin q, (coins i).2.2 ∈ recursiveCapacityAvoid D iv coins i

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- Outside the recursive capacity failure, every round preserves unique
rooted paths. -/
theorem idealStateNat_uniquePaths_of_good {q n : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) (hn : n ≤ q)
    (hgood : ∀ i : Fin q, (i : Nat) < n →
      (coins i).2.2 ∉ recursiveCapacityAvoid D iv coins i) :
    UniquePaths (idealStateNat D iv coins n hn).sim iv := by
  induction n with
  | zero => simpa [idealStateNat] using uniquePaths_empty iv
  | succ n ih =>
      unfold idealStateNat
      have hprev := ih (Nat.le_trans (Nat.le_succ n) hn)
        (fun i hi => hgood i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      let j : Fin q := ⟨n, Nat.lt_of_succ_le hn⟩
      have havoid : (coins j).2.2 ∉
          idealCapacityAvoid D iv
            (idealStateNat D iv coins n (Nat.le_trans (Nat.le_succ n) hn)) := by
        exact hgood j (by change n < n + 1; omega)
      exact idealStep_uniquePaths D iv coins
        (idealStateNat D iv coins n (Nat.le_trans (Nat.le_succ n) hn)) j
        hprev (idealFreshAt_of_not_mem_avoid D iv coins _ j havoid)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [Nonempty Cap] in
/-- **Priced consistency alternative.**  Every exact ideal coin schedule either
hits the named adaptive capacity-failure event or the actual final `idealRun`
simulator log has unique rooted paths. -/
theorem capacityFailure_or_idealRun_uniquePaths {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin q → Rate × (Rate × Cap)) :
    RecursiveCapacityFailure D iv coins ∨
      UniquePaths (idealRun D iv coins).sim iv := by
  by_cases hbad : RecursiveCapacityFailure D iv coins
  · exact Or.inl hbad
  · right
    rw [← idealStateNat_full_eq_idealRun D iv coins]
    exact idealStateNat_uniquePaths_of_good D iv coins (Nat.le_refl q)
      (fun i _ hi => hbad ⟨i, hi⟩)

omit [Fintype Rate] [DecidableEq Rate] in
/-- Conditional recursive-run price for each fixed rate/block-rate schedule. -/
theorem recursiveCapacityFailure_conditional_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (base : Fin q → Rate × Rate) :
    uniformProb (Fin q → Cap) (fun capacity =>
      RecursiveCapacityFailure D iv (withCapacity base capacity))
      ≤ (q : Real) * (((2 * q + 2 : Nat) : Real) / Fintype.card Cap) := by
  unfold RecursiveCapacityFailure
  apply adaptiveFiniteUnionBound
  · intro i capacity capacity' hprefix
    apply recursiveCapacityAvoid_prefix
    intro j hj
    simp only [withCapacity]
    rw [hprefix j hj]
  · intro capacity i
    exact recursiveCapacityAvoid_card_le D iv (withCapacity base capacity) i

omit [DecidableEq Rate] in
/-- **Numeric price on the exact ideal coin space.**  The pointwise failure
event in `capacityFailure_or_idealRun_uniquePaths` costs at most
`q(2q+2)/|Cap|`. -/
theorem recursiveCapacityFailure_le {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) :
    uniformProb (Fin q → Rate × (Rate × Cap))
      (RecursiveCapacityFailure D iv)
      ≤ (q : Real) * (((2 * q + 2 : Nat) : Real) / Fintype.card Cap) := by
  have htransport :
      uniformProb (Fin q → Rate × (Rate × Cap))
          (RecursiveCapacityFailure D iv)
        = uniformProb ((Fin q → Rate × Rate) × (Fin q → Cap))
          (fun parts =>
            RecursiveCapacityFailure D iv (withCapacity parts.1 parts.2)) := by
    rw [← uniformProb_equiv (splitIdealCoins (Rate := Rate) (Cap := Cap) q)
      (fun parts =>
        RecursiveCapacityFailure D iv (withCapacity parts.1 parts.2))]
    apply uniformProb_congr
    intro coins
    have hrebuild :=
      (splitIdealCoins (Rate := Rate) (Cap := Cap) q).left_inv coins
    change withCapacity
      ((splitIdealCoins (Rate := Rate) (Cap := Cap) q) coins).1
      ((splitIdealCoins (Rate := Rate) (Cap := Cap) q) coins).2 = coins at hrebuild
    rw [hrebuild]
  rw [htransport]
  refine uniformProb_prod_le (by positivity) fun base => ?_
  exact recursiveCapacityFailure_conditional_le D iv base

end OffBadRun

/-! The pointwise classifier is the deterministic half.  Its event will be
priced by the prefix/product theorem in the next small transport lemma; no
probability premise appears in the classifier itself. -/

/-- info: 'Minidregg.Selvage.idealStateNat_full_eq_idealRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealStateNat_full_eq_idealRun
/-- info: 'Minidregg.Selvage.capacityFailure_or_idealRun_uniquePaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacityFailure_or_idealRun_uniquePaths
/-- info: 'Minidregg.Selvage.recursiveCapacityFailure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveCapacityFailure_le

end Minidregg.Selvage
