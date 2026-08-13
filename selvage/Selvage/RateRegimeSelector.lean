/-
# Selvage.RateRegimeSelector -- one honest API for the proved rate regimes

This module does not turn the different rate regimes into one fictitious
radius theorem.  It selects a typed certificate for the event each landed
theorem actually controls:

* sub-quantization: exact membership plus the ordinary FRI acceptance mass;
* one-third UD: the unconditional fixed-radius FRI acceptance mass;
* half then UD: one threshold-halving round followed by the unconditional
  fixed-radius tail;
* Johnson: affine-line mutual-CA failure, only after receiving the explicit
  `HaboeckTheorem2` seam and the matching proximity-generator premise.

Every request and every result carries a strict plain-RS capacity guard.
Consequently the selector has no constructor at `delta = 1 - rate`.
-/
import Selvage.DeciderProximity
import Selvage.HalfThresholdFriTower
import Selvage.JohnsonMcaBridge

namespace Minidregg.Selvage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {m : ℕ}

/-! ## The explicit plain-RS capacity boundary -/

/-- A selected radius is for a proper RS code and is strictly below the
plain-RS capacity radius `1 - d/n`.  The half-threshold theorem itself does
not imply this fact, so it is deliberately an input to every selector branch. -/
structure PlainRSCapacityGuard (n d : ℕ) (delta : ℝ) : Prop where
  properDegree : d < n
  belowCapacity : delta < 1 - (d : ℝ) / (n : ℝ)

/-- The strict guard has no inhabitant at the plain-RS capacity boundary. -/
theorem no_plain_rs_capacity_guard_at_capacity (n d : ℕ) :
    ¬ PlainRSCapacityGuard n d (1 - (d : ℝ) / (n : ℝ)) := by
  intro h
  exact (lt_irrefl _ h.belowCapacity)

/-! ## A common result shape without erasing branch semantics -/

/-- The four proof-producing regimes exposed by the selector. -/
inductive RateRegime where
  | exactSubquant
  | oneThirdUD
  | halfThenUD
  | haboeckJohnson
  deriving DecidableEq, Repr

/-- The exact Haboeck/Johnson bad-slope probability selected at the finite
multiplicity `max 3 d`. -/
noncomputable def haboeckJohnsonBadMass
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) : ℝ :=
  haboeckBadCount
      (haboeckReducedRate (deg 0) (Fintype.card (ι 0) : ℝ))
      (Fintype.card (ι 0) : ℝ) (max 3 (deg 0)) /
    (Fintype.card F : ℝ)

/-- Branch-indexed evidence.  The first three constructors bound the
uniform FRI challenge tuple.  The Johnson constructor bounds the affine
generator's mutual-CA failure event and retains both the published-theorem
seam and its derived `WHIRConjecture412` instance. -/
inductive RateRegimeEvidence
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (delta : ℝ) :
    RateRegime → ℝ → Prop
  | exactSubquant
      (collapse : ∀ f : ι 0 → F,
        close delta (reedSolomonCode (T.dom 0) (deg 0)) f ↔
          f ∈ reedSolomonCode (T.dom 0) (deg 0))
      (sound : ∀ f : ι 0 → F,
        ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) f →
          ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤
            (m : ℝ) / (Fintype.card F : ℝ)) :
      RateRegimeEvidence T deg delta .exactSubquant
        ((m : ℝ) / (Fintype.card F : ℝ))
  | oneThirdUD
      (sound : ∀ f : ι 0 → F,
        ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) f →
          ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤
            (m : ℝ) * (Fintype.card (ι 0) : ℝ) /
              (Fintype.card F : ℝ)) :
      RateRegimeEvidence T deg delta .oneThirdUD
        ((m : ℝ) * (Fintype.card (ι 0) : ℝ) /
          (Fintype.card F : ℝ))
  | halfThenUD
      (sound : ∀ f : ι 0 → F,
        ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) f →
          ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤
            (m : ℝ) * (Fintype.card (ι 0) : ℝ) /
              (Fintype.card F : ℝ)) :
      RateRegimeEvidence T deg delta .halfThenUD
        ((m : ℝ) * (Fintype.card (ι 0) : ℝ) /
          (Fintype.card F : ℝ))
  | haboeckJohnson
      (seam : HaboeckTheorem2 (T.dom 0) (deg 0))
      (conjecture :
        WHIRConjecture412 (affineGenerator F)
          (reedSolomonCode (T.dom 0) (deg 0))
          (Real.sqrt ((deg 0 : ℝ) / (Fintype.card (ι 0) : ℝ)))
          (fun _ => haboeckJohnsonBadMass T deg))
      (sound : ∀ f : Fin 2 → ι 0 → F,
        (affineGenerator F).pr
            (MutualCAFailure
              (reedSolomonCode (T.dom 0) (deg 0)) delta f) ≤
          haboeckJohnsonBadMass T deg) :
      RateRegimeEvidence T deg delta .haboeckJohnson
        (haboeckJohnsonBadMass T deg)

/-- The public result: a named regime, its normalized challenge bad mass,
the capacity guard, and the theorem witnessing that mass. -/
structure SelectedRateRegime
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (delta : ℝ) where
  regime : RateRegime
  badMass : ℝ
  capacityGuard : PlainRSCapacityGuard
    (Fintype.card (ι 0)) (deg 0) delta
  evidence : RateRegimeEvidence T deg delta regime badMass

/-! ## Explicit selector requests -/

/-- A request contains exactly the hypotheses needed by its selected landed
theorem.  In particular the unconditional branches contain no proximity-gap
or literature seam, whereas the Johnson branch cannot be constructed without
`HaboeckTheorem2`. -/
inductive RateRegimeRequest
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (delta : ℝ) : Type
  | exactSubquant
      (hdelta : 0 ≤ delta)
      (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
      (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
      (hquant : ∀ n, n ≤ m →
        delta < 1 / (Fintype.card (ι n) : ℝ))
      (hguard : PlainRSCapacityGuard
        (Fintype.card (ι 0)) (deg 0) delta)
  | oneThirdUD
      (hdelta : 0 < delta)
      (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
      (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
      (hband : ∀ j, j < m →
        delta < 1 - (2 + (deg (j + 1) : ℝ) /
          (Fintype.card (ι (j + 1)) : ℝ)) / 3)
      (hguard : PlainRSCapacityGuard
        (Fintype.card (ι 0)) (deg 0) delta)
  | halfThenUD
      (hm : 0 < m)
      (hdelta : 0 < delta)
      (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
      (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
      (hband : ∀ j, j < m → 0 < j →
        delta / 2 < 1 - (2 + (deg (j + 1) : ℝ) /
          (Fintype.card (ι (j + 1)) : ℝ)) / 3)
      (hguard : PlainRSCapacityGuard
        (Fintype.card (ι 0)) (deg 0) delta)
  | haboeckJohnson
      (hHab : HaboeckTheorem2 (T.dom 0) (deg 0))
      (hPG : IsProximityGenerator (affineGenerator F)
        (reedSolomonCode (T.dom 0) (deg 0))
        (Real.sqrt ((deg 0 : ℝ) / (Fintype.card (ι 0) : ℝ)))
        (fun _ => haboeckJohnsonBadMass T deg))
      (hdelta : 0 < delta)
      (hjohnson : delta <
        johnsonRadius ((deg 0 : ℝ) / (Fintype.card (ι 0) : ℝ)))
      (hguard : PlainRSCapacityGuard
        (Fintype.card (ι 0)) (deg 0) delta)

/-! ## Selection theorem -/

private theorem accept_probability_le_of_count
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) {f : ι 0 → F} {b : ℕ}
    (hcount : (acceptSet T deg f).card ≤
      m * (b * Fintype.card F ^ (m - 1))) :
    ((acceptSet T deg f).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤
      (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hzero : (acceptSet T deg f).card = 0 :=
      Nat.le_zero.mp (by simpa using hcount)
    rw [hzero]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
      ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
    have hpow : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by positivity
    have hcast : ((acceptSet T deg f).card : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * (b : ℝ) * (Fintype.card F : ℝ) ^ k := by
      calc
        ((acceptSet T deg f).card : ℝ)
            ≤ (((k + 1) * (b * Fintype.card F ^ k) : ℕ) : ℝ) := by
              exact_mod_cast (by simpa using hcount)
        _ = ((k + 1 : ℕ) : ℝ) * (b : ℝ) *
              (Fintype.card F : ℝ) ^ k := by
              push_cast
              ring
    rw [pow_succ]
    have hstep : ((acceptSet T deg f).card : ℝ) /
          ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ))
        ≤ (((k + 1 : ℕ) : ℝ) * (b : ℝ) *
            (Fintype.card F : ℝ) ^ k) /
          ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ)) := by
      gcongr
    refine le_trans hstep (le_of_eq ?_)
    have hpowne : ((Fintype.card F : ℝ) ^ k) ≠ 0 := ne_of_gt hpow
    have hFne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hF
    field_simp

/-- Select the requested proved regime and return its precise bad-mass
certificate.  This is a theorem-producing dispatch, not a numerical heuristic. -/
noncomputable def selectRateRegime
    {T : FoldingTower F ι m} {deg : ℕ → ℕ} {delta : ℝ}
    (request : RateRegimeRequest T deg delta) :
    SelectedRateRegime T deg delta := by
  cases request with
  | exactSubquant hdelta hnonempty hdeg hquant hguard =>
      refine
        { regime := .exactSubquant
          badMass := (m : ℝ) / (Fintype.card F : ℝ)
          capacityGuard := hguard
          evidence := ?_ }
      apply RateRegimeEvidence.exactSubquant
      · intro f
        letI : Nonempty (ι 0) := hnonempty 0 (Nat.zero_le m)
        exact close_iff_mem_of_lt_inv_card hdelta
          (hquant 0 (Nat.zero_le m))
      · intro f hfar
        have hfold : ∀ j (hj : j < m),
            FoldDistancePreserving (T.data j hj) (deg j) (deg (j + 1))
              delta 1 := by
          intro j hj
          letI : Nonempty (ι (j + 1)) :=
            hnonempty (j + 1) (Nat.succ_le_iff.mpr hj)
          have h := foldDistancePreserving_of_lt_inv_card
            (T.data j hj) (deg (j + 1)) hdelta
            (hquant (j + 1) (Nat.succ_le_iff.mpr hj))
          simpa [hdeg j hj] using h
        simpa using
          (proximity_sound_prob T deg hdelta (b := 1) hfold hfar)
  | oneThirdUD hdelta hnonempty hdeg hband hguard =>
      refine
        { regime := .oneThirdUD
          badMass := (m : ℝ) * (Fintype.card (ι 0) : ℝ) /
            (Fintype.card F : ℝ)
          capacityGuard := hguard
          evidence := ?_ }
      apply RateRegimeEvidence.oneThirdUD
      intro f hfar
      apply proximity_sound_prob T deg hdelta.le
        (b := Fintype.card (ι 0)) ?_ hfar
      intro j hj
      letI : Nonempty (ι j) := hnonempty j (Nat.le_of_lt hj)
      letI : Nonempty (ι (j + 1)) :=
        hnonempty (j + 1) (Nat.succ_le_iff.mpr hj)
      have hsmall := foldDistancePreserving_UD
        (T.data j hj) (deg (j + 1)) hdelta (hband j hj)
      have hround : FoldDistancePreserving (T.data j hj)
          (deg j) (deg (j + 1)) delta (Fintype.card (ι (j + 1))) := by
        simpa [hdeg j hj] using hsmall
      intro w hw
      obtain ⟨bad, hbad, hspec⟩ := hround w hw
      exact ⟨bad, hbad.trans
        (T.card_level_le_zero (j + 1) (Nat.succ_le_iff.mpr hj)), hspec⟩
  | halfThenUD hm hdelta hnonempty hdeg hband hguard =>
      refine
        { regime := .halfThenUD
          badMass := (m : ℝ) * (Fintype.card (ι 0) : ℝ) /
            (Fintype.card F : ℝ)
          capacityGuard := hguard
          evidence := ?_ }
      apply RateRegimeEvidence.halfThenUD
      intro f hfar
      apply accept_probability_le_of_count T deg
      exact proximity_sound_halfThen_UD T deg hm hdelta hnonempty hdeg hband hfar
  | haboeckJohnson hHab hPG hdelta hjohnson hguard =>
      have hdegreePos : 0 < deg 0 :=
        lt_trans Nat.zero_lt_one hHab.1
      have hcardPos : 0 < Fintype.card (ι 0) :=
        lt_of_lt_of_le hdegreePos hHab.2.1
      letI : Nonempty (ι 0) := Fintype.card_pos_iff.mp hcardPos
      have hconjecture :
          WHIRConjecture412 (affineGenerator F)
            (reedSolomonCode (T.dom 0) (deg 0))
            (Real.sqrt ((deg 0 : ℝ) / (Fintype.card (ι 0) : ℝ)))
            (fun _ => haboeckJohnsonBadMass T deg) := by
        simpa [haboeckJohnsonBadMass] using
          (whirConjecture412_rs_of_haboeck_max_three_degree
            (T.dom 0) (deg 0) hHab)
      refine
        { regime := .haboeckJohnson
          badMass := haboeckJohnsonBadMass T deg
          capacityGuard := hguard
          evidence := ?_ }
      apply RateRegimeEvidence.haboeckJohnson hHab hconjecture
      intro f
      exact mutualCA_johnson (T.dom 0) (deg 0) hconjecture hPG f
        hdelta hjohnson

/-! ## A small firing site: F5, one round, rate one half -/

namespace RateRegimeSelectorExample

open ProximityExample

/-- The F5 line code has source rate `2/4 = 1/2`.  At `delta = 1/5` the
sub-quantization selector fires, so its proximity event is exact membership
and its one-round challenge mass is `1/5`. -/
noncomputable def f5HalfRateSelection :
    SelectedRateRegime ldtTower degSched (1 / 5 : ℝ) :=
  selectRateRegime (.exactSubquant
    (by norm_num)
    (by
      intro n hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · change Nonempty (Fin 4)
        exact ⟨0⟩
      · change Nonempty (Fin 2)
        exact ⟨0⟩)
    degSched_halving
    (by
      intro n hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;>
        norm_num [levels, Fintype.card_fin])
    (by
      constructor <;> norm_num [degSched, levels, Fintype.card_fin]))

theorem f5_half_rate_selector_fires :
    (degSched 0 : ℝ) / (Fintype.card (levels 0) : ℝ) = 1 / 2 ∧
      f5HalfRateSelection.regime = .exactSubquant ∧
      f5HalfRateSelection.badMass = 1 / 5 := by
  constructor
  · norm_num [degSched, levels, Fintype.card_fin]
  constructor
  · rfl
  · norm_num [f5HalfRateSelection, selectRateRegime, ZMod.card]

end RateRegimeSelectorExample

end Minidregg.Selvage
