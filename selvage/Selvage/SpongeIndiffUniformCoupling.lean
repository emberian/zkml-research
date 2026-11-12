/-
# Selvage.SpongeIndiffUniformCoupling — probability transport for work coins

The deterministic oracle lemmas permit eager prefix samples to move past
distinct lazy samples.  A probability proof must additionally show that the
resulting transformation is a bijection of the *whole fixed work coin space*.
This module states that boundary exactly and proves the counting transport.

A `UniformWorkCoupling` contains an actual equivalence of
`Fin work → Rate × Cap`, not merely matching marginals, and a pointwise
equivalence of the two events under that map.  Uniform probabilities are then
equal.  Coordinate permutations provide concrete nontrivial examples.  The
full adaptive sponge hop must still build a coupling whose reindexing follows
the construction/reveal schedule; it is not asserted here.
-/
import Selvage.SpongeIndiffOracleReordering

namespace Minidregg.Selvage

section UniformCoupling

variable {Rate Cap : Type} [Fintype Rate] [Fintype Cap]

/-- Reindex a fixed work vector by a permutation of its coordinates. -/
def permuteWorkCoins {work : Nat} (permutation : Equiv.Perm (Fin work)) :
    (Fin work → Rate × Cap) ≃ (Fin work → Rate × Cap) where
  toFun coins index := coins (permutation index)
  invFun coins index := coins (permutation.symm index)
  left_inv coins := by
    funext index
    simp
  right_inv coins := by
    funext index
    simp

/-- Uniform probability is invariant under any coordinate permutation. -/
theorem uniformProb_permuteWorkCoins {work : Nat}
    (permutation : Equiv.Perm (Fin work))
    (event : (Fin work → Rate × Cap) → Prop) :
    uniformProb (Fin work → Rate × Cap)
        (fun coins => event (permuteWorkCoins permutation coins)) =
      uniformProb (Fin work → Rate × Cap) event :=
  uniformProb_equiv (permuteWorkCoins permutation) event

/-- Exact same-space coupling between two work-indexed events. -/
structure UniformWorkCoupling {work : Nat}
    (left right : (Fin work → Rate × Cap) → Prop) where
  reindex : (Fin work → Rate × Cap) ≃ (Fin work → Rate × Cap)
  event_iff : ∀ coins, left coins ↔ right (reindex coins)

/-- A same-space bijection plus pointwise event equivalence gives exact
probability equality. -/
theorem uniformProb_eq_of_coupling {work : Nat}
    {left right : (Fin work → Rate × Cap) → Prop}
    (coupling : UniformWorkCoupling left right) :
    uniformProb (Fin work → Rate × Cap) left =
      uniformProb (Fin work → Rate × Cap) right := by
  calc
    uniformProb (Fin work → Rate × Cap) left =
        uniformProb (Fin work → Rate × Cap)
          (fun coins => right (coupling.reindex coins)) := by
      apply uniformProb_congr
      exact coupling.event_iff
    _ = uniformProb (Fin work → Rate × Cap) right :=
      uniformProb_equiv coupling.reindex right

variable [AddCommGroup Rate] [DecidableEq Rate]

/-- The precise remaining eager/deferred bridge for one distinguisher.  The
left event is the work-stream prefix hybrid.  The right event is intentionally
parameterized by a corrected work-indexed deferred simulator rather than the
old one-pair-per-public-round sample space. -/
def PrefixDeferredCoupling {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (deferredAccept : (Fin work → Rate × Cap) → Prop) : Type :=
  UniformWorkCoupling
    (workHybridAccept Rate Cap D iv)
    deferredAccept

end UniformCoupling

/-! ## A nontrivial coordinate swap is an exact coupling -/

namespace SpongeUniformCouplingExample

def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def firstIsTrue (coins : Fin 3 → Bool × Bool) : Prop := (coins 0).1 = true
def secondIsTrue (coins : Fin 3 → Bool × Bool) : Prop := (coins 1).1 = true

def coupling : UniformWorkCoupling firstIsTrue secondIsTrue where
  reindex := permuteWorkCoins swap01
  event_iff coins := by
    simp [firstIsTrue, secondIsTrue, permuteWorkCoins, swap01]

theorem swapped_coordinate_probability :
    uniformProb (Fin 3 → Bool × Bool) firstIsTrue =
      uniformProb (Fin 3 → Bool × Bool) secondIsTrue :=
  uniformProb_eq_of_coupling coupling

end SpongeUniformCouplingExample

/-- info: 'Minidregg.Selvage.uniformProb_eq_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniformProb_eq_of_coupling
/-- info: 'Minidregg.Selvage.SpongeUniformCouplingExample.swapped_coordinate_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeUniformCouplingExample.swapped_coordinate_probability

end Minidregg.Selvage
