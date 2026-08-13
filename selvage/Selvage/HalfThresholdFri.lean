/-
# Selvage.HalfThresholdFri -- the first FRI round at one halved threshold

`Selvage.HalfThresholdRegime` proves the characteristic-independent algebraic
core: unless a pair of words has correlated agreement at radius `delta`, at
most one scalar makes its affine combination `delta/2`-close to a linear
code.  This file connects that statement to Selvage's concrete multiplicative
FRI fold.

The connection is exact:

* `fold_eq_foldFamily` identifies the FRI fold with the affine family of its
  even and odd components;
* `foldComponents_not_correlated_of_far` is the contrapositive of the landed
  two-for-two FRI coupling `close_of_correlatedAgreement`; and
* `foldDistanceTransition_halfThreshold` says that a `delta`-far source word
  folds to a `delta/2`-far word outside a set of at most one challenge.

The ordinary `FoldDistancePreserving` interface has one radius on both sides
and therefore cannot state this theorem.  `FoldDistanceTransition` is the
smallest honest extension: it records separate input and output radii while
retaining the existing finite bad-set contract.

This is the commit-challenge part of the Chai--Fan threshold-halving route,
not its oracle-query protocol.  In particular this file does not claim the
query miss term `(1 - delta/2)^q`, Merkle attribution, or Fiat--Shamir
composition; those remain `[DEC-prox-query]` and transcript-layer work.
-/
import Selvage.HalfThresholdRegime

namespace Minidregg.Selvage

variable {F : Type*} [Field F]
variable {ι κ : Type*}

/-! ## A mixed-threshold one-round interface -/

/-- One round of folding takes `deltaIn`-farness to `deltaOut`-farness off a
finite bad set of at most `b` challenges.  This is the two-radius analogue of
`FoldDistancePreserving`. -/
def FoldDistanceTransition [DecidableEq F] [Fintype ι] [Fintype κ]
    {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (dbig dsmall : ℕ)
    (deltaIn deltaOut : ℝ) (b : ℕ) : Prop :=
  ∀ f : ι → F, ¬ close deltaIn (reedSolomonCode dom dbig) f →
    ∃ bad : Finset F, bad.card ≤ b ∧
      ∀ alpha, alpha ∉ bad →
        ¬ close deltaOut (reedSolomonCode domSq dsmall) (fold D f alpha)

/-- A same-radius distance-preservation theorem is, in particular, a
mixed-threshold transition whose two radii coincide. -/
theorem foldDistanceTransition_of_preserving [DecidableEq F]
    [Fintype ι] [Fintype κ]
    {dom : ι ↪ F} {domSq : κ ↪ F}
    {D : FoldingData F dom domSq} {dbig dsmall b : ℕ} {delta : ℝ}
    (h : FoldDistancePreserving D dbig dsmall delta b) :
    FoldDistanceTransition D dbig dsmall delta delta b :=
  h

/-- Bad-set bounds weaken monotonically. -/
theorem FoldDistanceTransition.mono_bad [DecidableEq F]
    [Fintype ι] [Fintype κ]
    {dom : ι ↪ F} {domSq : κ ↪ F}
    {D : FoldingData F dom domSq} {dbig dsmall b b' : ℕ}
    {deltaIn deltaOut : ℝ}
    (h : FoldDistanceTransition D dbig dsmall deltaIn deltaOut b)
    (hbb : b ≤ b') :
    FoldDistanceTransition D dbig dsmall deltaIn deltaOut b' := by
  intro f hfar
  obtain ⟨bad, hbad, hspec⟩ := h f hfar
  exact ⟨bad, hbad.trans hbb, hspec⟩

/-! ## Exact coupling to the multiplicative FRI fold -/

section MultiplicativeFold

variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- The concrete multiplicative FRI fold is exactly the affine fold family of
its even and odd component words. -/
theorem fold_eq_foldFamily (D : FoldingData F dom domSq)
    (f : ι → F) (alpha : F) :
    fold D f alpha = foldFamily (foldEven D f) (foldOdd D f) alpha := by
  funext x
  rfl

/-- A source word that is `delta`-far from the degree-`< 2d` code has no
radius-`delta` correlated explanation for its even/odd component pair.

This is precisely the contrapositive of the landed multiplicative FRI
coupling `close_of_correlatedAgreement`. -/
theorem foldComponents_not_correlated_of_far [Nonempty ι]
    [DecidableEq F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (D : FoldingData F dom domSq) (d : ℕ) {delta : ℝ} {f : ι → F}
    (hfar : ¬ close delta (reedSolomonCode dom (2 * d)) f) :
    ¬ CorrelatedAgreement (reedSolomonCode domSq d) delta
      ![foldEven D f, foldOdd D f] := by
  intro hCA
  exact hfar (close_of_correlatedAgreement D hCA)

/-- **The first-round half-threshold transition.** If the source word is
`delta`-far from `RS[dom, 2d]`, then outside at most ONE field challenge its
FRI fold is `delta/2`-far from `RS[domSq, d]`.

No Johnson bound, rate inequality, characteristic assumption, or proximity
gap theorem is used. -/
theorem foldDistanceTransition_halfThreshold [Fintype F] [Nonempty ι]
    [Nonempty κ] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (D : FoldingData F dom domSq) (d : ℕ) (delta : ℝ) :
    FoldDistanceTransition D (2 * d) d delta (delta / 2) 1 := by
  intro f hfar
  have hpair := foldComponents_not_correlated_of_far D d hfar
  let bad : Finset F := halfThresholdBadScalars
    (reedSolomonCode domSq d) (foldEven D f) (foldOdd D f) delta
  refine ⟨bad, ?_, ?_⟩
  · simpa [bad] using halfThreshold_bad_card_le_one
      (reedSolomonCode domSq d) (foldEven D f) (foldOdd D f) delta hpair
  · intro alpha halpha hclose
    apply halpha
    simp only [bad, halfThresholdBadScalars, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [← fold_eq_foldFamily D f alpha]
    exact hclose

/-- The concrete bad-challenge set for the multiplicative first fold. -/
noncomputable def foldHalfThresholdBadScalars [Fintype F]
    [DecidableEq F] [Fintype ι] [Fintype κ]
    (D : FoldingData F dom domSq) (d : ℕ) (delta : ℝ) (f : ι → F) : Finset F :=
  @Finset.filter F
    (fun alpha : F =>
      close (delta / 2) (reedSolomonCode domSq d) (fold D f alpha))
    (Classical.decPred _) Finset.univ

/-- Counting form of the first-round theorem: at most one challenge makes a
`delta`-far source fold `delta/2`-close. -/
theorem fold_halfThreshold_bad_card_le_one [Fintype F] [Nonempty ι]
    [Nonempty κ] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (D : FoldingData F dom domSq) (d : ℕ) {delta : ℝ} {f : ι → F}
    (hfar : ¬ close delta (reedSolomonCode dom (2 * d)) f) :
    (foldHalfThresholdBadScalars D d delta f).card ≤ 1 := by
  classical
  obtain ⟨bad, hbad, hspec⟩ :=
    foldDistanceTransition_halfThreshold D d delta f hfar
  refine le_trans (Finset.card_le_card (s := foldHalfThresholdBadScalars D d delta f) ?_)
    hbad
  intro alpha halpha
  have hclose : close (delta / 2) (reedSolomonCode domSq d) (fold D f alpha) := by
    exact (Finset.mem_filter.mp halpha).2
  by_contra hnot
  exact hspec alpha hnot hclose

/-- Uniform-probability rendering of the first-round theorem. -/
theorem fold_halfThreshold_pr_le [Fintype F] [Nonempty ι] [Nonempty κ]
    [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (D : FoldingData F dom domSq) (d : ℕ) {delta : ℝ} {f : ι → F}
    (hfar : ¬ close delta (reedSolomonCode dom (2 * d)) f) :
    ((foldHalfThresholdBadScalars D d delta f).card : ℝ)
        / (Fintype.card F : ℝ)
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hF]
  exact_mod_cast fold_halfThreshold_bad_card_le_one D d hfar

end MultiplicativeFold

/-! ## Keystones: the bad challenge is real, and the post-Johnson band exists -/

namespace HalfThresholdFriExample

open ProximityExample

/-- At the landed F5 folding domain, the spike's half-threshold bad set is
EXACTLY the singleton `{3}`.  Thus the one-challenge bound is attained, not
merely an upper bound.

The source is `1/5`-far (`spikeWord_far`); challenge `3` folds it to a
degree-`< 1` word, while every other challenge remains outside even the
`1/10`-ball. -/
theorem spike_halfThreshold_bad_exact :
    foldHalfThresholdBadScalars data0 1 (1 / 5 : ℝ) spikeWord = {3} := by
  classical
  ext alpha
  simp only [foldHalfThresholdBadScalars, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨u, huC, hrel⟩
    have heq : fold data0 spikeWord alpha = u := by
      by_contra hne
      have hfloor := one_div_card_le_relDist (F := ZMod 5) hne
      norm_num [Fintype.card_fin] at hfloor
      linarith
    apply (spike_accept_iff alpha).mp
    change fold data0 spikeWord alpha ∈ reedSolomonCode dom1 1
    exact heq ▸ huC
  · intro halpha
    subst alpha
    have hacc := (spike_accept_iff (3 : ZMod 5)).mpr rfl
    change fold data0 spikeWord 3 ∈ reedSolomonCode dom1 1 at hacc
    exact close_of_mem hacc (by norm_num)

/-- The first-round half-threshold theorem fires at the concrete spike and
its bound is attained with equality. -/
theorem spike_halfThreshold_bound_attained :
    (foldHalfThresholdBadScalars data0 1 (1 / 5 : ℝ) spikeWord).card = 1 := by
  rw [spike_halfThreshold_bad_exact]
  simp

/-- At rate `rho = 1/2`, `delta = 3/10` is strictly beyond Johnson, while
its once-halved threshold `3/20` lies inside Selvage's UNCONDITIONAL
one-third-UD proximity band `(0, 1/6)`.  This is the concrete nonempty
post-Johnson interval available without `PolishchukSpielman`. -/
theorem postJohnson_half_lands_in_unconditional_UD :
    johnsonRadius (1 / 2 : ℝ) < 3 / 10
      ∧ (3 / 10 : ℝ) / 2 < 1 - (2 + (1 / 2 : ℝ)) / 3 := by
  constructor
  · have h := JohnsonRegimeExample.johnson_win_at_rate_half.2.2
    norm_num at h ⊢
    exact h
  · norm_num

/-- The landed unconditional UD realizer accepts the once-halved
post-Johnson radius at the concrete rate-half folding data. -/
theorem half_postJohnson_tail_transition :
    FoldDistanceTransition data0 2 1 (3 / 20 : ℝ) (3 / 20 : ℝ) 2 := by
  apply foldDistanceTransition_of_preserving
  exact foldDistancePreserving_UD data0 1 (by norm_num) (by
    norm_num [Fintype.card_fin])

end HalfThresholdFriExample

/-! ## Honest boundary -/

/-
The theorem above is the complete first-round multiplicative coupling.  A
multi-round theorem needs a radius-indexed version of `proximity_far_covering`:
round zero uses `delta -> delta/2`, while every later round preserves
`delta/2`.  The existing tower soundness API fixes one radius globally, so
that assembly is intentionally not disguised as a `FoldDistancePreserving`
claim here.

For later rounds Selvage currently offers two genuine choices:

* `foldDistancePreserving_UD` is unconditional on
  `delta/2 < (1 - rate)/3`; this already gives a post-Johnson interval when
  `rate > 1/4`.
* `foldDistancePreserving_UD_full` covers the full
  `delta/2 < (1 - rate)/2` band, conditional on the one named classical
  `PolishchukSpielman` divisibility lemma.

The query-miss factor is separately available as the fixed-word counting
kernel `column_sampling_bridge_pr`; composing it with committed per-round
oracles remains the explicitly named `[DEC-prox-query]` residual.
-/

/-- info: 'Minidregg.Selvage.fold_eq_foldFamily' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_eq_foldFamily
/-- info: 'Minidregg.Selvage.foldComponents_not_correlated_of_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldComponents_not_correlated_of_far
/-- info: 'Minidregg.Selvage.foldDistanceTransition_halfThreshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldDistanceTransition_halfThreshold
/-- info: 'Minidregg.Selvage.fold_halfThreshold_pr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_halfThreshold_pr_le
/-- info: 'Minidregg.Selvage.HalfThresholdFriExample.spike_halfThreshold_bad_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriExample.spike_halfThreshold_bad_exact
/-- info: 'Minidregg.Selvage.HalfThresholdFriExample.half_postJohnson_tail_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriExample.half_postJohnson_tail_transition

end Minidregg.Selvage
