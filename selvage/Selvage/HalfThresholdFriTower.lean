/-
# Selvage.HalfThresholdFriTower -- one halving, then a fixed-radius FRI tail

`Selvage.HalfThresholdFri` closes the first multiplicative FRI round:
`delta`-farness becomes `delta/2`-farness outside one challenge.  The original
`proximity_far_covering` theorem fixes one radius at every tower level, so it
cannot consume that result without pretending the threshold never changed.

This file adds the minimal radius-scheduled tower theorem.  Its induction is
the landed `proximity_far_covering` proof with `radius n` in place of a global
`delta`; the adaptive counting engine is reused unchanged.  The resulting
challenge-only error numerator is the existing common-bound form

  `m * b * |F|^(m-1)`,

where `b` bounds every round's bad set.  For the half-threshold route we take
`b = |L_0|`: the first round costs `1 <= |L_0|`, and every later landed UD
round costs at most its next-level domain size, which is at most `|L_0|`.

Two heads are provided:

* `proximity_sound_halfThen` consumes arbitrary same-`delta/2` tail
  transitions;
* `proximity_sound_halfThen_UD` supplies those transitions unconditionally
  from `foldDistancePreserving_UD`, on the currently proved one-third-UD
  band `delta/2 < (1-rate)/3`.

This is soundness for Selvage's whole-word `proximityTest`.  A maliciously
recommitted oracle can deviate from the derived fold tower; detecting that
deviation with `q` openings and adding `(1-delta/2)^q` is the separate
`[DEC-prox-query]` commitment/transcript layer.  It is not assumed here.
-/
import Selvage.HalfThresholdFri

namespace Minidregg.Selvage

variable {F : Type*} [Field F]

/-! ## Radius-scheduled round reduction -/

section ScheduledCovering

variable [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {m : ℕ}

/-- The FRI round-reduction with a possibly different radius at every level.
Far-persistence uses `radius n -> radius (n+1)` transitions; only the final
radius needs to be nonnegative so base-code membership implies closeness. -/
theorem proximity_far_covering_schedule
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (hfinal : 0 ≤ radius m) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistanceTransition (T.data j hj) (deg j) (deg (j + 1))
        (radius j) (radius (j + 1)) b)
    {f : ι 0 → F}
    (hfar : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) f) :
    ∃ bad : (Fin m → F) → Fin m → Finset F,
      (∀ (i : Fin m) (r r' : Fin m → F),
        (∀ j : Fin m, (j : ℕ) < (i : ℕ) → r j = r' j) → bad r i = bad r' i)
      ∧ (∀ r i, (bad r i).card ≤ b)
      ∧ ∀ r : Fin m → F,
        proximityTest T deg f (chalExt r) → ∃ i, r i ∈ bad r i := by
  classical
  have hbadAt : ∀ (j : ℕ) (hj : j < m) (w : ι j → F),
      ∃ bad : Finset F, bad.card ≤ b ∧
        (¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) w →
          ∀ alpha, alpha ∉ bad →
            ¬ close (radius (j + 1))
              (reedSolomonCode (T.dom (j + 1)) (deg (j + 1)))
              (fold (T.data j hj) w alpha)) := by
    intro j hj w
    by_cases hw : ¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) w
    · obtain ⟨bad, hcard, hspec⟩ := hfold j hj w hw
      exact ⟨bad, hcard, fun _ => hspec⟩
    · exact ⟨∅, Nat.zero_le b, fun hw' => absurd (not_not.mp hw) hw'⟩
  choose badAt hbadCard hbadSpec using hbadAt
  refine ⟨fun r i => badAt i i.isLt
      (T.word f (chalExt r) i (le_of_lt i.isLt)), ?_, ?_, ?_⟩
  · intro i r r' hagree
    exact congrArg (badAt i i.isLt)
      (T.word_congr f i (le_of_lt i.isLt) fun j hj => by
        have hjm : j < m := lt_trans hj i.isLt
        rw [chalExt, dif_pos hjm, chalExt, dif_pos hjm]
        exact hagree ⟨j, hjm⟩ hj)
  · exact fun r i => hbadCard i i.isLt _
  · intro r hacc
    by_contra hmiss
    have hmiss' : ∀ i : Fin m,
        r i ∉ badAt i i.isLt
          (T.word f (chalExt r) i (le_of_lt i.isLt)) :=
      fun i hi => hmiss ⟨i, hi⟩
    have hfarAll : ∀ (n : ℕ) (hn : n ≤ m),
        ¬ close (radius n) (reedSolomonCode (T.dom n) (deg n))
          (T.word f (chalExt r) n hn) := by
      intro n
      induction n with
      | zero => intro _; exact hfar
      | succ k ih =>
          intro hn
          have hk : k < m := hn
          rw [T.word_succ]
          have hkfar := ih (Nat.le_of_succ_le hn)
          have halpha : chalExt r k ∉ badAt k hk
              (T.word f (chalExt r) k (Nat.le_of_succ_le hn)) := by
            have h := hmiss' ⟨k, hk⟩
            rw [chalExt, dif_pos hk]
            exact h
          exact hbadSpec k hk _ hkfar _ halpha
    exact hfarAll m le_rfl (close_of_mem hacc hfinal)

end ScheduledCovering

/-! ## Scheduled counting head -/

section ScheduledSoundness

variable [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {m : ℕ}

/-- Challenge-only soundness for a radius schedule.  The adaptive union bound
is exactly the landed counting engine; changing radii does not change its
measurability or cardinality argument. -/
theorem proximity_sound_schedule
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (radius : ℕ → ℝ)
    (hfinal : 0 ≤ radius m) {b : ℕ}
    (hfold : ∀ j (hj : j < m),
      FoldDistanceTransition (T.data j hj) (deg j) (deg (j + 1))
        (radius j) (radius (j + 1)) b)
    {f : ι 0 → F}
    (hfar : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) := by
  classical
  obtain ⟨bad, hmeas, hcard, hcover⟩ :=
    proximity_far_covering_schedule T deg radius hfinal hfold hfar
  refine le_trans (Finset.card_le_card fun r hr => ?_)
    (card_filter_exists_coord_mem_le bad hmeas hcard)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ r, hcover r (mem_acceptSet.mp hr)⟩

end ScheduledSoundness

/-! ## One halving followed by a fixed-radius tail -/

/-- Radius `delta` at level zero and `delta/2` at every later level. -/
noncomputable def halfThenRadius (delta : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then delta else delta / 2

@[simp] theorem halfThenRadius_zero (delta : ℝ) :
    halfThenRadius delta 0 = delta := rfl

@[simp] theorem halfThenRadius_succ (delta : ℝ) (n : ℕ) :
    halfThenRadius delta (n + 1) = delta / 2 := by
  simp [halfThenRadius]

section HalfThenTail

variable [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
variable [∀ n, DecidableEq (ι n)] [Nonempty (ι 0)] [Nonempty (ι 1)]
variable {m : ℕ}

/-- **One half-threshold round, then a same-radius tail.**  Round zero is
supplied by `foldDistanceTransition_halfThreshold`; every positive round is
an explicit `delta/2 -> delta/2` transition with common bad-set bound `b`.
The resulting challenge numerator is `m*b*|F|^(m-1)`. -/
theorem proximity_sound_halfThen
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) {delta : ℝ} {b : ℕ}
    (hm : 0 < m) (hdelta : 0 ≤ delta) (hb : 1 ≤ b)
    (hdeg0 : deg 0 = 2 * deg 1)
    (htail : ∀ j (hj : j < m), 0 < j →
      FoldDistanceTransition (T.data j hj) (deg j) (deg (j + 1))
        (delta / 2) (delta / 2) b)
    {f : ι 0 → F}
    (hfar : ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤ m * (b * Fintype.card F ^ (m - 1)) := by
  apply proximity_sound_schedule T deg (halfThenRadius delta)
    (by simp [halfThenRadius]; positivity) (b := b) ?_ (by simpa using hfar)
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    have hfirst := foldDistanceTransition_halfThreshold
      (T.data 0 hm) (deg 1) delta
    have hfirst' : FoldDistanceTransition (T.data 0 hm)
        (deg 0) (deg 1) delta (delta / 2) 1 := by
      simpa [hdeg0] using hfirst
    simpa using hfirst'.mono_bad hb
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    simpa [halfThenRadius, hj0] using htail j hj hjpos

end HalfThenTail

/-! ### Domain-size bookkeeping -/

section DomainCardinality

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {m : ℕ}

/-- Every level of a folding tower has cardinality at most level zero: each
`FoldingData` halves cardinality exactly. -/
theorem FoldingTower.card_level_le_zero (T : FoldingTower F ι m) :
    ∀ n, n ≤ m → Fintype.card (ι n) ≤ Fintype.card (ι 0) := by
  intro n
  induction n with
  | zero => intro _; exact le_rfl
  | succ k ih =>
      intro hn
      have hprev := ih (Nat.le_of_succ_le hn)
      have hhalve := card_eq_two_mul_card (T.data k hn)
      omega

end DomainCardinality

section HalfThenUD

variable [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
variable [∀ n, DecidableEq (ι n)]
variable {m : ℕ}

/-- **Unconditional half-threshold FRI challenge soundness on the landed
one-third-UD tail band.**  The first round costs at most one challenge.  Every
later round uses `foldDistancePreserving_UD` at radius `delta/2`, with bad
set size `|L_(j+1)| <= |L_0|`.  Hence the common-bound numerator is

`m * |L_0| * |F|^(m-1)`.

For rate `1/2`, `delta = 3/10` is already beyond Johnson while
`delta/2 = 3/20 < 1/6`; `HalfThresholdFriExample` proves those inequalities
and fires the tail realizer concretely. -/
theorem proximity_sound_halfThen_UD
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) {delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hband : ∀ j, j < m → 0 < j →
      delta / 2 <
        1 - (2 + (deg (j + 1) : ℝ) /
          (Fintype.card (ι (j + 1)) : ℝ)) / 3)
    {f : ι 0 → F}
    (hfar : ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤
      m * (Fintype.card (ι 0) * Fintype.card F ^ (m - 1)) := by
  letI : Nonempty (ι 0) := hnonempty 0 (Nat.zero_le m)
  letI : Nonempty (ι 1) := hnonempty 1 hm
  apply proximity_sound_halfThen T deg hm hdelta.le
    (by exact_mod_cast Fintype.card_pos) (hdeg 0 hm) ?_ hfar
  intro j hj hjpos
  letI : Nonempty (ι j) := hnonempty j (Nat.le_of_lt hj)
  letI : Nonempty (ι (j + 1)) :=
    hnonempty (j + 1) (Nat.succ_le_iff.mpr hj)
  have hpres := foldDistancePreserving_UD (T.data j hj) (deg (j + 1))
    (by positivity) (hband j hj hjpos)
  have hpres' : FoldDistancePreserving (T.data j hj)
      (deg j) (deg (j + 1)) (delta / 2) (Fintype.card (ι (j + 1))) := by
    simpa [hdeg j hj] using hpres
  exact (foldDistanceTransition_of_preserving hpres').mono_bad
    (T.card_level_le_zero (j + 1) (Nat.succ_le_iff.mpr hj))

/-- **A concrete post-Johnson rate regime.**  On any tower whose positive
tail rounds have folded rate exactly `1/2`, an initial word `3/10`-far from
the level-zero code has challenge-only acceptance numerator bounded by
`m*|L_0|*|F|^(m-1)`.  The accompanying first conjunct records that `3/10`
is strictly beyond the rate-half Johnson radius; after the one-time halving,
`3/20 < 1/6` discharges every unconditional one-third-UD tail hypothesis. -/
theorem proximity_sound_rateHalf_postJohnson
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (hm : 0 < m)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hrate : ∀ j, j < m → 0 < j →
      (deg (j + 1) : ℝ) / (Fintype.card (ι (j + 1)) : ℝ) = 1 / 2)
    {f : ι 0 → F}
    (hfar : ¬ close (3 / 10 : ℝ)
      (reedSolomonCode (T.dom 0) (deg 0)) f) :
    johnsonRadius (1 / 2 : ℝ) < 3 / 10
      ∧ (acceptSet T deg f).card ≤
        m * (Fintype.card (ι 0) * Fintype.card F ^ (m - 1)) := by
  constructor
  · exact HalfThresholdFriExample.postJohnson_half_lands_in_unconditional_UD.1
  · apply proximity_sound_halfThen_UD T deg hm (by norm_num) hnonempty hdeg ?_ hfar
    intro j hj hjpos
    rw [hrate j hj hjpos]
    norm_num

end HalfThenUD

/-! ## A concrete attained one-round tower keystone -/

namespace HalfThresholdFriTowerExample

open ProximityExample

/-- The scheduled tower theorem fires on the landed F5 spike.  The tail is
empty (`m = 1`), the sole first-round bad set has size one, and the theorem's
numerator is exactly one. -/
theorem spike_scheduled_bound :
    (acceptSet ldtTower degSched spikeWord).card
      ≤ 1 * (1 * Fintype.card (ZMod 5) ^ (1 - 1)) := by
  letI : Nonempty (levels 0) := ⟨(0 : Fin 4)⟩
  letI : Nonempty (levels 1) := ⟨(0 : Fin 2)⟩
  apply proximity_sound_halfThen ldtTower degSched (delta := (1 / 5 : ℝ))
    (b := 1) (by omega) (by norm_num) (by omega)
    (by norm_num [degSched]) ?_ spikeWord_far
  intro j hj hjpos
  omega

/-- The scheduled challenge bound is attained: the acceptance set is the
single laundering challenge, exactly as the half-threshold bad set is `{3}`. -/
theorem spike_scheduled_bound_attained :
    (acceptSet ldtTower degSched spikeWord).card
      = 1 * (1 * Fintype.card (ZMod 5) ^ (1 - 1)) := by
  rw [ProximityExample.acceptSet_spike]
  norm_num

end HalfThresholdFriTowerExample

/-! ## Honest boundary -/

/-
Closed here: radius-scheduled far-persistence, adaptive challenge counting,
the one-halving/fixed-tail composition, and its unconditional one-third-UD
instantiation.  The full unique-decoding tail can replace
`foldDistancePreserving_UD` with `foldDistancePreserving_UD_full` once the
named `PolishchukSpielman` lemma is supplied.

Not modeled: prover-committed intermediate words, Merkle openings, the query
miss event, or Fiat--Shamir.  Consequently no `(1-delta/2)^q` term appears in
these theorem statements.
-/

/-- info: 'Minidregg.Selvage.proximity_far_covering_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms proximity_far_covering_schedule
/-- info: 'Minidregg.Selvage.proximity_sound_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms proximity_sound_schedule
/-- info: 'Minidregg.Selvage.proximity_sound_halfThen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms proximity_sound_halfThen
/-- info: 'Minidregg.Selvage.FoldingTower.card_level_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldingTower.card_level_le_zero
/-- info: 'Minidregg.Selvage.proximity_sound_halfThen_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms proximity_sound_halfThen_UD
/-- info: 'Minidregg.Selvage.proximity_sound_rateHalf_postJohnson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms proximity_sound_rateHalf_postJohnson
/-- info: 'Minidregg.Selvage.HalfThresholdFriTowerExample.spike_scheduled_bound_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriTowerExample.spike_scheduled_bound_attained

end Minidregg.Selvage
