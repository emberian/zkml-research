/-
# Full unique-decoding tail in the existing half-threshold FRI chain

The first fold still halves the target distance. Each positive tail round
uses the proved full-UD realizer. The challenge numerator is unchanged.
-/
import Selvage.ProximityGapFullUD
import Selvage.HalfThresholdFriTranscript

namespace Minidregg.Selvage
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {m : ℕ}

/-- The existing half-threshold tower bound with the full-UD tail radius. -/
theorem proximity_sound_halfThen_fullUD
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) {delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hdegpos : ∀ j, j < m → 0 < j → 1 ≤ deg (j+1))
    (hband : ∀ j, j < m → 0 < j →
      delta / 2 <
        1 - (1 + (deg (j + 1) : ℝ) /
          (Fintype.card (ι (j + 1)) : ℝ)) / 2)
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
  have hpres := foldDistancePreserving_fullUD (T.data j hj) (deg (j + 1)) (hdegpos j hj hjpos)
    (by positivity) (hband j hj hjpos)
  have hpres' : FoldDistancePreserving (T.data j hj)
      (deg j) (deg (j + 1)) (delta / 2) (Fintype.card (ι (j + 1))) := by
    simpa [hdeg j hj] using hpres
  exact (foldDistanceTransition_of_preserving hpres').mono_bad
    (T.card_level_le_zero (j + 1) (Nat.succ_le_iff.mpr hj))

/-- At rate one half, an initial distance two fifths has tail radius one
fifth. This lies in the newly proved band and outside the former one-third
UD tail band. The same tower acceptance numerator follows. -/
theorem proximity_sound_rateHalf_twoFifths_fullUD
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (hm : 0 < m)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2*deg (j+1))
    (hrate : ∀ j, j < m → 0 < j →
      (deg (j+1) : ℝ)/(Fintype.card (ι (j+1)) : ℝ) = 1/2)
    {f : ι 0 → F}
    (hfar : ¬ close (2/5 : ℝ) (reedSolomonCode (T.dom 0) (deg 0)) f) :
    (acceptSet T deg f).card ≤
      m * (Fintype.card (ι 0) * Fintype.card F ^ (m-1)) := by
  apply proximity_sound_halfThen_fullUD T deg hm (by norm_num)
    hnonempty hdeg ?_ ?_ hfar
  · intro j hj hjpos
    have hr := hrate j hj hjpos
    by_contra h
    have hz : deg (j+1) = 0 := by omega
    norm_num [hz] at hr
  · intro j hj hjpos
    rw [hrate j hj hjpos]
    norm_num

/-- Arithmetic tooth: the new rate-half tail radius cannot satisfy the
old theorem's radius hypothesis. -/
theorem rateHalf_twoFifths_new_band :
    (0 : ℝ) < (2/5)/2 ∧
    (2/5)/2 < 1-(1+(1/2 : ℝ))/2 ∧
    ¬ (2/5)/2 < 1-(2+(1/2 : ℝ))/3 := by
  norm_num

/-- All-position committed-oracle soundness inherits the wider tail band,
using the existing binding reduction. No Fiat–Shamir random-oracle or
sampled-opening claim is added here. -/
theorem committedFri_sound_halfThen_fullUD
    {Root Op : ℕ → Type*}
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriCommittedStatement S) {delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2*deg (j+1))
    (hdegpos : ∀ j, j < m → 0 < j → 1 ≤ deg (j+1))
    (hband : ∀ j, j < m → 0 < j →
      delta/2 < 1-(1+(deg (j+1) : ℝ)/(Fintype.card (ι (j+1)) : ℝ))/2)
    (hfar : ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) (st.word 0)) :
    (friCommittedAcceptSet S T deg st).card ≤
      m * (Fintype.card (ι 0) * Fintype.card F ^ (m-1)) := by
  exact (Finset.card_le_card (friCommittedAcceptSet_subset S T deg st)).trans
    (proximity_sound_halfThen_fullUD T deg hm hdelta hnonempty hdeg hdegpos hband hfar)

/-- info: 'Minidregg.Selvage.proximity_sound_halfThen_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proximity_sound_halfThen_fullUD

/-- info: 'Minidregg.Selvage.committedFri_sound_halfThen_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms committedFri_sound_halfThen_fullUD

/-- info: 'Minidregg.Selvage.proximity_sound_rateHalf_twoFifths_fullUD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proximity_sound_rateHalf_twoFifths_fullUD

/-- info: 'Minidregg.Selvage.rateHalf_twoFifths_new_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rateHalf_twoFifths_new_band

end Minidregg.Selvage
