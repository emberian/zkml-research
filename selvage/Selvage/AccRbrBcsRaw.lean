/-
# Selvage.AccRbrBcsRaw -- the executable BCS reduction before binding

`accReductionBcs` uses only commitment, opening, and opening verification in
its verifier, but its carrier is parameterized by `BindingCommitment`.  This
module exposes the strictly weaker reduction that the verifier actually runs:
an `OpeningScheme`.  It proves only verifier reflection.  Knowledge soundness,
binding, collision resistance, and random-oracle claims remain outside this
module.
-/

import Selvage.AccRbrBcs

namespace Minidregg.Selvage

set_option autoImplicit false

noncomputable section

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : Nat}

open Classical in
/-- The literal deployed BCS verifier over a binding-free opening scheme. -/
@[reducible] noncomputable def accReductionBcsRaw
    (C : Submodule F (Fin m -> F))
    (foldRoot : Root -> F -> Root -> Root)
    (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar <= 1)
    (E : OpeningScheme Root' F (Fin m) Op)
    (domain : Fin m ↪ F) (degree : Nat) (queries : Fin t -> Fin m) :
    Reduction where
  Idx := Unit
  X := AccClaim Root F (Fin m) r
  A := F
  X' := AccClaim Root F (Fin m) r
  A' := F
  W := Fin ch.length -> Fin m -> F
  n := m
  n' := m
  n_pos := hm
  n'_pos := hm
  R := fun _ genesis initial witness =>
    AccClaim.Satisfies C genesis initial ∧
      ∀ k : Fin ch.length, LinkAligned C genesis ch k (witness k)
  R' := fun _ aggregate folded _ => AccClaim.Satisfies C aggregate folded
  k := ch.length
  k_pos := hch
  PMsg := BcsMsg Root' F Op t
  Chal := F
  pmsgNonempty :=
    ⟨⟨E.commit 0, fun _ => 0, fun j => E.openAt 0 (queries j)⟩⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := deltaStar
  δstar_pos := deltaStarPositive
  δstar_le_one := deltaStarLeOne
  verify := fun _ genesis initial messages challenges =>
    if ∀ i, ColsOpen E queries (messages i) then
      some
        (aggregate foldRoot (padSched challenges) genesis ch,
          foldWords (padSched challenges) initial
            (List.ofFn fun i => bcsWord domain degree queries (messages i)))
    else none

namespace accReductionBcsRaw

/-- Exact reflection of the raw verifier.  This theorem exposes the accepted
opening checks and both deterministic output components without invoking a
binding property. -/
theorem verify_eq_some_iff
    (C : Submodule F (Fin m -> F))
    (foldRoot : Root -> F -> Root -> Root)
    (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar <= 1)
    (E : OpeningScheme Root' F (Fin m) Op)
    (domain : Fin m ↪ F) (degree : Nat) (queries : Fin t -> Fin m)
    (genesis : AccClaim Root F (Fin m) r) (initial : Fin m -> F)
    (messages : Fin ch.length -> BcsMsg Root' F Op t)
    (challenges : Fin ch.length -> F)
    (outputClaim : AccClaim Root F (Fin m) r)
    (outputWord : Fin m -> F) :
    (accReductionBcsRaw C foldRoot ch hm hch deltaStar deltaStarPositive
      deltaStarLeOne E domain degree queries).verify () genesis initial
        messages challenges = some (outputClaim, outputWord) ↔
      (∀ i, ColsOpen E queries (messages i)) ∧
      outputClaim = aggregate foldRoot (padSched challenges) genesis ch ∧
      outputWord = foldWords (padSched challenges) initial
        (List.ofFn fun i => bcsWord domain degree queries (messages i)) := by
  classical
  change
    (if ∀ i, ColsOpen E queries (messages i) then
      some
        (aggregate foldRoot (padSched challenges) genesis ch,
          foldWords (padSched challenges) initial
            (List.ofFn fun i => bcsWord domain degree queries (messages i)))
    else none) = some (outputClaim, outputWord) ↔ _
  split
  next accepted =>
    constructor
    · intro outputExact
      have pairExact := Option.some.inj outputExact
      exact ⟨accepted,
        (congrArg Prod.fst pairExact).symm,
        (congrArg Prod.snd pairExact).symm⟩
    · rintro ⟨_, claimExact, wordExact⟩
      subst outputClaim
      subst outputWord
      rfl
  next rejected => simp [rejected]

end accReductionBcsRaw

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.accReductionBcsRaw.verify_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms accReductionBcsRaw.verify_eq_some_iff

end

end Minidregg.Selvage
