/-
# Selvage.BaseFoldBcsDeferredIdeal — the deferred work-space acceptance IS
# the landed ideal acceptance, and the off-bad witness is built

`BaseFoldBcsCrossings` named `[DEFERRED-ideal-exact]`: the deferred ideal
run's acceptance probability on the padded work space equals `idealProb` of
the landed game on its own coin space.  This module proves it and closes
that name.

Both sides read only one rate coin per public round.  The deferred run reads
the segment-head rate (`paddedDeferredWorkRun_head_semantics`); the landed
`idealRun`, on a construction-only schedule whose messages are pairwise
prefix-free, reads exactly the round's rate coin (`paddedIdealRun_ans`, the
same induction on the recursive `idealStateNat`).  The two probabilities are
then the same marginal: the segment-head map is injective
(`paddedSegmentHead_injective`), so `uniformProb_comp_injective` pulls the
work space back to one pair per round, and the capacity/block coordinates
are discarded by the exact product marginal (`uniformProb_prod_snd`).

With this, the tree's own interface `PrefixHybridIdealOffBadWitness` — the
honest target `SpongeIndiffWorkStream` states for the hybrid-to-ideal
identification — is inhabited for every padded receipt distinguisher
(`paddedOffBadWitness`): bad event = item 1's `PaddedCapacityCollisionRun`,
deferred acceptance = the reindexed deferred run, agreement off bad = item
1's bridge, and `deferred_probability_exact` = this module.

Covered scope: the fixed padded receipt schedule under the proved routing
premise.  Not covered: any distinguisher issuing primitive queries.
-/

import Selvage.BaseFoldBcsCrossings
import Selvage.SpongeIndiffOffBadRun
import Selvage.LightClientGrinding

namespace Minidregg.Selvage.BaseFoldBcsDeferredIdeal

open Minidregg.Selvage
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsPadding
open Minidregg.Selvage.BaseFoldBcsRunSchedule
open Minidregg.Selvage.BaseFoldBcsCapacityEvent
open Minidregg.Selvage.BaseFoldBcsCrossings

set_option autoImplicit false

noncomputable section

variable {m queryCount : Nat}

/-! ## The construction-only ideal run reads one rate coin per round -/

/-- The public answer the ideal world gives at each round of a fresh,
construction-only schedule: the round's rate coin. -/
def idealRateTrace (coins : Fin (m + queryCount) → Rate × (Rate × Cap)) :
    Fin (m + queryCount) → SpAnswer Rate Cap :=
  fun round => .rate (coins round).1

/-- Recursive ideal invariant for the padded schedule: the transcript is the
rate-coin trace so far, the simulator log is untouched, and every later
public message is still fresh in the RO. -/
theorem paddedIdealStateNat_semantics (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (m + queryCount) → Rate × (Rate × Cap))
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    ∀ (round : Nat) (hround : round ≤ m + queryCount),
      (idealStateNat (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins round hround).ans =
          (List.ofFn (idealRateTrace coins)).take round ∧
        (idealStateNat (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins round hround).sim = Oracle.empty ∧
        ∀ future : Fin (m + queryCount), round ≤ future →
          (idealStateNat (paddedConstructionDistinguisher statement receipt
            verdict) (0, 0) coins round hround).ro.lookup
              (paddedPublicMessageSchedule statement receipt future) = none := by
  intro round
  induction round with
  | zero =>
      intro hround
      exact ⟨by simp [idealStateNat], rfl, fun future _ => Oracle.lookup_empty _⟩
  | succ round ih =>
      intro hround
      have hprev : round ≤ m + queryCount :=
        Nat.le_trans (Nat.le_succ round) hround
      obtain ⟨hans, hsim, hfuture⟩ := ih hprev
      have hroundLt : round < m + queryCount := Nat.lt_of_succ_le hround
      set D := paddedConstructionDistinguisher statement receipt verdict with hD
      set state := idealStateNat D (0, 0) coins round hprev with hstate
      let current : Fin (m + queryCount) := ⟨round, hroundLt⟩
      have hansLength : state.ans.length = round := by
        rw [hans, List.length_take, List.length_ofFn]
        omega
      obtain ⟨x, xs, hquery, hmessage⟩ :=
        paddedConstructionQuerySchedule_is_constr statement receipt current
      have hmove : D.move state.ans = .constr x xs := by
        rw [hD, paddedConstructionDistinguisher_move_at_length statement receipt
          verdict state.ans (by rw [hansLength]; exact hroundLt), ← hquery]
        congr 1
        exact Fin.ext hansLength
      have hfresh : state.ro.lookup (x :: xs) = none := by
        rw [← hmessage]
        exact hfuture current (le_refl _)
      have hstep :
          idealStateNat D (0, 0) coins (round + 1) hround =
            ⟨(state.ro.respond (x :: xs) (coins ⟨round, hroundLt⟩).1).2, state.sim,
              state.ans ++
                [.rate (state.ro.respond (x :: xs) (coins ⟨round, hroundLt⟩).1).1]⟩ := by
        rw [idealStateNat]
        show idealStep D (0, 0) coins state ⟨round, hroundLt⟩ = _
        simp only [idealStep, hmove]
      rw [hstep]
      refine ⟨?_, hsim, ?_⟩
      · show state.ans ++
            [SpAnswer.rate (state.ro.respond (x :: xs) (coins ⟨round, hroundLt⟩).1).1] =
          (List.ofFn (idealRateTrace coins)).take (round + 1)
        rw [Oracle.respond_fresh_fst hfresh]
        have hindex : round < (List.ofFn (idealRateTrace coins)).length := by
          simpa using hroundLt
        rw [List.take_add_one, List.getElem?_eq_getElem hindex, List.getElem_ofFn,
          hans]
        rfl
      · intro future hfutureIndex
        have hne : current ≠ future := by
          intro equal
          have hval := congrArg Fin.val equal
          simp [current] at hval
          omega
        have hnotPrefix := hsafe current future hne
        have hmessageNe :
            paddedPublicMessageSchedule statement receipt future ≠ x :: xs := by
          intro equal
          apply hnotPrefix
          rw [hmessage, equal]
        show (state.ro.respond (x :: xs) (coins ⟨round, hroundLt⟩).1).2.lookup
            (paddedPublicMessageSchedule statement receipt future) = none
        rw [Oracle.lookup_respond_ne _ hmessageNe]
        exact hfuture future (by omega)

/-- ⭐ The landed ideal run of the padded distinguisher answers exactly the
rate-coin trace. -/
theorem paddedIdealRun_ans (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : Fin (m + queryCount) → Rate × (Rate × Cap))
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    (idealRun (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) coins).ans = List.ofFn (idealRateTrace coins) := by
  rw [← idealStateNat_full_eq_idealRun]
  rw [(paddedIdealStateNat_semantics statement receipt verdict coins hsafe
    (m + queryCount) (Nat.le_refl _)).1]
  exact (List.take_eq_self_iff _).2 (by simp)

/-! ## Both acceptance probabilities are the same rate marginal -/

/-- The verdict read on one rate per round. -/
def rateVerdict (verdict : List (SpAnswer Rate Cap) → Bool)
    (rates : Fin (m + queryCount) → Rate) : Prop :=
  verdict (List.ofFn fun round => SpAnswer.rate (rates round)) = true

/-- Discarding the second coordinate of every round is an exact marginal. -/
theorem rate_marginal (verdict : List (SpAnswer Rate Cap) → Bool) (γ : Type)
    [Fintype γ] [Nonempty γ] :
    uniformProb (Fin (m + queryCount) → Rate × γ)
        (fun pairs => rateVerdict verdict fun round => (pairs round).1) =
      uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict) := by
  haveI : Nonempty (Fin (m + queryCount) → γ) := ⟨fun _ => Classical.arbitrary γ⟩
  calc
    uniformProb (Fin (m + queryCount) → Rate × γ)
        (fun pairs => rateVerdict verdict fun round => (pairs round).1)
      = uniformProb ((Fin (m + queryCount) → Rate) × (Fin (m + queryCount) → γ))
          (fun parts => rateVerdict verdict parts.1) :=
        uniformProb_equiv (splitWorkCoins (m + queryCount))
          (fun parts => rateVerdict verdict parts.1)
    _ = uniformProb ((Fin (m + queryCount) → γ) × (Fin (m + queryCount) → Rate))
          (fun parts => rateVerdict verdict parts.2) :=
        uniformProb_equiv (Equiv.prodComm _ _)
          (fun parts => rateVerdict verdict parts.2)
    _ = uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict) :=
        uniformProb_prod_snd (rateVerdict verdict)

theorem paddedIdealAccept_iff (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (coins : Fin (m + queryCount) → Rate × (Rate × Cap)) :
    ((paddedConstructionDistinguisher statement receipt verdict).out
        (idealRun (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) coins).ans = true) ↔
      rateVerdict verdict fun round => (coins round).1 := by
  rw [paddedIdealRun_ans statement receipt verdict coins hsafe]
  exact Iff.rfl

theorem paddedIdealProb_eq (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    idealProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) =
      uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict) := by
  unfold idealProb
  rw [uniformProb_congr (paddedIdealAccept_iff statement receipt verdict hsafe)]
  exact rate_marginal verdict (Rate × Cap)

/-- Static segments are disjoint and ordered, so their heads are distinct. -/
theorem paddedSegmentHead_injective (statement : Statement m)
    (receipt : Receipt m queryCount) :
    Function.Injective (paddedSegmentHead statement receipt) := by
  intro left right hequal
  have hval : (paddedSegmentHead statement receipt left : Nat) =
      paddedSegmentHead statement receipt right := congrArg Fin.val hequal
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := paddedSegmentLast_lt_head_of_lt statement receipt left right hlt
    have h2 := paddedSegmentHead_le_last statement receipt left
    omega
  · have h1 := paddedSegmentLast_lt_head_of_lt statement receipt right left hgt
    have h2 := paddedSegmentHead_le_last statement receipt right
    omega

/-- Reading a uniform work vector only at the segment heads is exactly the
uniform one-pair-per-round space. -/
theorem head_marginal (statement : Statement m) (receipt : Receipt m queryCount)
    (p : (Fin (m + queryCount) → Rate × Cap) → Prop) :
    uniformProb (WorkCoins statement receipt)
        (fun coins => p fun round => coins (paddedSegmentHead statement receipt round)) =
      uniformProb (Fin (m + queryCount) → Rate × Cap) p :=
  uniformProb_comp_injective (paddedSegmentHead_injective statement receipt) p

theorem paddedDeferredAccept_iff (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (coins : WorkCoins statement receipt) :
    deferredAccept statement receipt verdict coins ↔
      rateVerdict verdict fun round =>
        (coins (paddedSegmentHead statement receipt round)).1 := by
  obtain ⟨state, hrun, hans, _, _, _⟩ :=
    paddedDeferredWorkRun_head_semantics statement receipt verdict coins hsafe
  unfold deferredAccept deferredWorkAccept
  rw [hrun]
  show (paddedConstructionDistinguisher statement receipt verdict).out
      state.core.ans = true ↔ _
  rw [hans]
  exact Iff.rfl

theorem paddedDeferredProb_eq (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    deferredProb statement receipt verdict =
      uniformProb (Fin (m + queryCount) → Rate) (rateVerdict verdict) := by
  unfold deferredProb
  rw [uniformProb_congr (paddedDeferredAccept_iff statement receipt verdict hsafe),
    head_marginal statement receipt
      (fun pairs => rateVerdict verdict fun round => (pairs round).1)]
  exact rate_marginal verdict Cap

/-- ⭐ **`[DEFERRED-ideal-exact]`, closed.**  For every padded receipt under
the proved routing premise, the deferred work-space acceptance probability
is the landed `idealProb`. -/
theorem paddedDeferredIdealExact (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    PaddedDeferredIdealExact statement receipt verdict := by
  unfold PaddedDeferredIdealExact
  rw [paddedDeferredProb_eq statement receipt verdict hsafe,
    paddedIdealProb_eq statement receipt verdict hsafe]

/-! ## The tree's off-bad interface, inhabited for the padded class -/

/-- ⭐ The landed `PrefixHybridIdealOffBadWitness` for every padded receipt
distinguisher: item 1's exact event as `bad`, the reindexed deferred run as
the deferred acceptance, item 1's bridge for agreement off bad, and this
module's exact probability identity. -/
def paddedOffBadWitness (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    PrefixHybridIdealOffBadWitness Rate Cap
      (work := paddedTranscriptPrimitiveWork statement receipt)
      (paddedConstructionDistinguisher statement receipt verdict) (0, 0) where
  bad := PaddedCapacityCollisionRun statement receipt verdict
  deferredAccept coins :=
    deferredAccept statement receipt verdict
      (paddedSegmentReindex statement receipt coins)
  agree_off_bad coins hnocol :=
    eagerAccept_iff_deferredAccept_reindex statement receipt verdict hsafe coins
      hnocol
  deferred_probability_exact := by
    rw [← deferredProb_eq_reindexed]
    exact paddedDeferredIdealExact statement receipt verdict hsafe

/-- Under the routing premise, `paddedRomBound_of_crossings` needs only the
three remaining named hops. -/
theorem paddedRomBound_of_three_crossings (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hswitch : PaddedRpRfSwitch statement receipt verdict)
    (hsampling : PaddedLazyFunctionSampling statement receipt verdict)
    (hagree : PaddedLazyEagerAgreeOffCollision statement receipt verdict) :
    |realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)|
      ≤ BaseFoldPoseidon2Rom.romError
          (paddedTranscriptPrimitiveWork statement receipt) :=
  paddedRomBound_of_crossings statement receipt verdict hsafe hswitch hsampling
    hagree (paddedDeferredIdealExact statement receipt verdict hsafe)

#check @paddedIdealRun_ans
#check @paddedIdealProb_eq
#check @paddedSegmentHead_injective
#check @paddedDeferredProb_eq
#check @paddedDeferredIdealExact
#check @paddedOffBadWitness
#check @paddedRomBound_of_three_crossings

/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedIdealRun_ans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedIdealRun_ans
/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedIdealProb_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedIdealProb_eq
/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedDeferredProb_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedDeferredProb_eq
/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedDeferredIdealExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedDeferredIdealExact
/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedOffBadWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedOffBadWitness
/-- info: 'Minidregg.Selvage.BaseFoldBcsDeferredIdeal.paddedRomBound_of_three_crossings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedRomBound_of_three_crossings

end

end Minidregg.Selvage.BaseFoldBcsDeferredIdeal
