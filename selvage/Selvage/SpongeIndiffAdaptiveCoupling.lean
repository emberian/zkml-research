/-
# Selvage.SpongeIndiffAdaptiveCoupling — prefix-measurable coin reindexing

The eager/deferred sponge hop cannot use a fixed coordinate permutation: the
coordinates to move are selected by the public transcript produced so far.
Nor is matching each coordinate marginal enough.  The required map must be a
bijection of the *whole* fixed work-vector space.

This module supplies the adaptive construction kernel.  A guarded involution
may apply a coin reindexing based on a predicate of the current vector, but the
predicate must be invariant under that reindexing.  Applying the guarded map
twice is therefore the identity, so it is an exact equivalence and preserves
uniform probability.  The work specialization permits a prefix-measurable
decision to swap later coordinates.  Finite programs of these guarded moves
are composed into one equivalence of the whole work-vector space, and hence
into the exact `UniformWorkCoupling` expected by the eager/deferred boundary.
A concrete three-coordinate theorem straightens an adaptively selected later
coin into one fixed coordinate.

The remaining run theorem must synthesize the program from the actual public
transcript and prove the corresponding off-bad semantic agreement.
-/
import Selvage.SpongeIndiffDeferredWork

namespace Minidregg.Selvage

section GuardedInvolution

/-- An involution selected by a guard which it cannot change.  Guard
invariance is the load-bearing causality condition: the inverse makes the same
decision after the forward move. -/
structure GuardedInvolution (α : Type) where
  step : α → α
  step_involutive : Function.Involutive step
  guard : α → Prop
  guardDecidable : DecidablePred guard
  guard_stable : ∀ value, guard (step value) ↔ guard value

def GuardedInvolution.apply {α : Type} (move : GuardedInvolution α)
    (value : α) : α :=
  letI : Decidable (move.guard value) := move.guardDecidable value
  if move.guard value then move.step value else value

/-- A guarded involution is a genuine self-equivalence, not a coupling by
matching marginals. -/
def GuardedInvolution.reindex {α : Type} (move : GuardedInvolution α) : α ≃ α where
  toFun := move.apply
  invFun := move.apply
  left_inv value := by
    by_cases hguard : move.guard value
    · have hstep : move.guard (move.step value) :=
        (move.guard_stable value).2 hguard
      simp only [GuardedInvolution.apply, hguard, hstep, if_pos]
      exact move.step_involutive value
    · have hstep : ¬ move.guard (move.step value) := by
        intro h
        exact hguard ((move.guard_stable value).1 h)
      simp only [GuardedInvolution.apply, hguard, hstep, if_neg]
  right_inv value := by
    by_cases hguard : move.guard value
    · have hstep : move.guard (move.step value) :=
        (move.guard_stable value).2 hguard
      simp only [GuardedInvolution.apply, hguard, hstep, if_pos]
      exact move.step_involutive value
    · have hstep : ¬ move.guard (move.step value) := by
        intro h
        exact hguard ((move.guard_stable value).1 h)
      simp only [GuardedInvolution.apply, hguard, hstep, if_neg]

/-- Uniform counting measure is invariant under a prefix-measurable guarded
move because that move is an equivalence of the complete sample space. -/
theorem uniformProb_guarded_reindex {α : Type} [Fintype α]
    (move : GuardedInvolution α) (event : α → Prop) :
    uniformProb α (fun value => event (move.reindex value)) =
      uniformProb α event :=
  uniformProb_equiv move.reindex event

end GuardedInvolution

section WorkReindexing

variable {Rate Cap : Type}

/-- Lift an involutive coordinate permutation to a guarded involution of the
whole sponge work vector.  The guard-stability premise is the exact statement
that the adaptive decision only observed information outside the coordinates
being moved (or otherwise cannot distinguish their order). -/
def guardedWorkReindex {work : Nat}
    (permutation : Equiv.Perm (Fin work))
    (permutation_involutive : Function.Involutive permutation)
    (guard : (Fin work → Rate × Cap) → Prop)
    (guardDecidable : DecidablePred guard)
    (guard_stable : ∀ coins,
      guard (permuteWorkCoins permutation coins) ↔ guard coins) :
    GuardedInvolution (Fin work → Rate × Cap) where
  step := permuteWorkCoins permutation
  step_involutive coins := by
    change (fun index => coins (permutation (permutation index))) = coins
    funext index
    rw [permutation_involutive index]
  guard := guard
  guardDecidable := guardDecidable
  guard_stable := guard_stable

end WorkReindexing

/-! ## Prefix guards and finite online programs -/

section PrefixGuards

variable {Rate Cap : Type}

/-- A work-vector predicate is prefix-measurable at `boundary` when it depends
only on coordinates with numeric index strictly below that boundary. -/
def WorkPrefixMeasurable {work : Nat} (boundary : Nat)
    (guard : (Fin work → Rate × Cap) → Prop) : Prop :=
  ∀ left right,
    (∀ k : Fin work, (k : Nat) < boundary → left k = right k) →
      (guard left ↔ guard right)

/-- Swapping two coordinates at or after the observation boundary cannot
change a prefix-measurable decision.  This is the causality fact needed by an
online coin scheduler, stated directly on the complete work-vector space. -/
theorem prefixMeasurable_swap_stable {work boundary : Nat}
    {guard : (Fin work → Rate × Cap) → Prop}
    (prefix : WorkPrefixMeasurable boundary guard)
    (i j : Fin work) (hi : boundary ≤ (i : Nat))
    (hj : boundary ≤ (j : Nat)) (coins : Fin work → Rate × Cap) :
    guard (permuteWorkCoins (Equiv.swap i j) coins) ↔ guard coins := by
  apply prefix
  intro k hk
  unfold permuteWorkCoins
  have hki : k ≠ i := by
    intro equal
    subst i
    omega
  have hkj : k ≠ j := by
    intro equal
    subst j
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- A prefix decision may therefore guard a swap wholly in the unobserved
suffix, producing a genuine involutive whole-space reindexing. -/
def prefixGuardedSwap {work boundary : Nat}
    (i j : Fin work) (guard : (Fin work → Rate × Cap) → Prop)
    (guardDecidable : DecidablePred guard)
    (prefix : WorkPrefixMeasurable boundary guard)
    (hi : boundary ≤ (i : Nat)) (hj : boundary ≤ (j : Nat)) :
    GuardedInvolution (Fin work → Rate × Cap) :=
  guardedWorkReindex (Equiv.swap i j)
    (by intro index; simp)
    guard guardDecidable
    (prefixMeasurable_swap_stable prefix i j hi hj)

end PrefixGuards

section GuardedPrograms

/-- Compose a finite sequence of adaptive guarded moves.  Every move observes
the vector produced by the preceding moves; nevertheless the composite is one
equivalence of the complete original sample space. -/
def guardedProgramReindex {α : Type} : List (GuardedInvolution α) → α ≃ α
  | [] => Equiv.refl α
  | move :: moves => move.reindex |>.trans (guardedProgramReindex moves)

@[simp] theorem guardedProgramReindex_nil {α : Type} :
    guardedProgramReindex ([] : List (GuardedInvolution α)) = Equiv.refl α :=
  rfl

@[simp] theorem guardedProgramReindex_cons {α : Type}
    (move : GuardedInvolution α) (moves : List (GuardedInvolution α)) :
    guardedProgramReindex (move :: moves) =
      move.reindex.trans (guardedProgramReindex moves) := rfl

/-- Any finite online program of stable guarded moves preserves the exact
uniform counting measure. -/
theorem uniformProb_guardedProgram {α : Type} [Fintype α]
    (moves : List (GuardedInvolution α)) (event : α → Prop) :
    uniformProb α (fun value => event (guardedProgramReindex moves value)) =
      uniformProb α event :=
  uniformProb_equiv (guardedProgramReindex moves) event

/-- Package a pointwise eager/deferred agreement under a finite guarded
program as the exact same-space coupling required by the work-stream game. -/
def guardedProgramCoupling {Rate Cap : Type}
    [Fintype Rate] [Fintype Cap] {work : Nat}
    {left right : (Fin work → Rate × Cap) → Prop}
    (moves : List (GuardedInvolution (Fin work → Rate × Cap)))
    (event_iff : ∀ coins,
      left coins ↔ right (guardedProgramReindex moves coins)) :
    UniformWorkCoupling left right where
  reindex := guardedProgramReindex moves
  event_iff := event_iff

/-- Once the run-level semantic agreement supplies the pointwise premise, the
entire adaptive program transports probability in one theorem application. -/
theorem uniformProb_eq_of_guardedProgram {Rate Cap : Type}
    [Fintype Rate] [Fintype Cap] {work : Nat}
    {left right : (Fin work → Rate × Cap) → Prop}
    (moves : List (GuardedInvolution (Fin work → Rate × Cap)))
    (event_iff : ∀ coins,
      left coins ↔ right (guardedProgramReindex moves coins)) :
    uniformProb (Fin work → Rate × Cap) left =
      uniformProb (Fin work → Rate × Cap) right :=
  uniformProb_eq_of_coupling (guardedProgramCoupling moves event_iff)

end GuardedPrograms

/-! ## A transcript-selected later coordinate is still exactly uniform -/

namespace SpongeAdaptiveCouplingExample

def tailSwapIndex : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

theorem tailSwapIndex_involutive : Function.Involutive tailSwapIndex := by
  intro index
  fin_cases index <;> rfl

def tailSwapPermutation : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective tailSwapIndex tailSwapIndex_involutive.bijective

def earlyGuard (coins : Fin 3 → Bool × Bool) : Prop :=
  (coins 0).1 = true

def tailSwap : GuardedInvolution (Fin 3 → Bool × Bool) :=
  guardedWorkReindex tailSwapPermutation
    (by
      intro index
      fin_cases index <;> rfl)
    earlyGuard (fun coins => inferInstance)
    (by
      intro coins
      rfl)

/-- The later coordinate selected after observing coordinate zero. -/
def adaptiveTailEvent (coins : Fin 3 → Bool × Bool) : Prop :=
  (if (coins 0).1 then (coins 1).1 else (coins 2).1) = true

/-- One fixed later coordinate, independent of the observed prefix. -/
def fixedTailEvent (coins : Fin 3 → Bool × Bool) : Prop :=
  (coins 2).1 = true

/-- The guarded swap straightens adaptive selection pointwise. -/
theorem adaptiveTailEvent_reindex (coins : Fin 3 → Bool × Bool) :
    adaptiveTailEvent (tailSwap.reindex coins) ↔ fixedTailEvent coins := by
  by_cases hguard : earlyGuard coins
  · simp [GuardedInvolution.reindex, GuardedInvolution.apply, tailSwap,
      guardedWorkReindex, hguard, earlyGuard, adaptiveTailEvent,
      fixedTailEvent, permuteWorkCoins, tailSwapPermutation, tailSwapIndex]
  · simp [GuardedInvolution.reindex, GuardedInvolution.apply, tailSwap,
      guardedWorkReindex, hguard, earlyGuard, adaptiveTailEvent,
      fixedTailEvent]

/-- A prefix-dependent choice of which later coin to reveal has exactly the
same probability as reading a fixed later coordinate.  The proof is a global
sample-space equivalence, not a matching-marginals argument. -/
theorem adaptiveTailEvent_probability :
    uniformProb (Fin 3 → Bool × Bool) adaptiveTailEvent =
      uniformProb (Fin 3 → Bool × Bool) fixedTailEvent := by
  calc
    uniformProb (Fin 3 → Bool × Bool) adaptiveTailEvent =
        uniformProb (Fin 3 → Bool × Bool)
          (fun coins => adaptiveTailEvent (tailSwap.reindex coins)) :=
      (uniformProb_guarded_reindex tailSwap adaptiveTailEvent).symm
    _ = uniformProb (Fin 3 → Bool × Bool) fixedTailEvent := by
      apply uniformProb_congr
      exact adaptiveTailEvent_reindex

end SpongeAdaptiveCouplingExample

/-- info: 'Minidregg.Selvage.uniformProb_guarded_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniformProb_guarded_reindex
#print axioms prefixMeasurable_swap_stable
#print axioms uniformProb_eq_of_guardedProgram
/-- info: 'Minidregg.Selvage.SpongeAdaptiveCouplingExample.adaptiveTailEvent_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeAdaptiveCouplingExample.adaptiveTailEvent_probability

end Minidregg.Selvage
