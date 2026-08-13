/-
# Selvage.AdditiveProximity — the additive image is an ordinary RS domain.

The additive fold developed in `Theory/AdditiveNTT{,Transform}` indexes its
half-size word by a transversal `R`, while Selvage's proximity machinery indexes
Reed--Solomon words by an abstract finite type equipped with an embedding into
the field.  This file proves that these are the same representation:

* `additiveImageDomain` embeds `r : R` at `q_beta(r) = r^2 + beta*r`;
  transversality makes this injective.
* `closeToDeg_iff_close` and `foldedCloseToDeg_iff_close` identify Theory's
  counting predicates with Selvage's relative-Hamming `close` predicate.
* `additiveProximityGap_of_isProximityGenerator` transports ANY Selvage PG(2)
  realizer to Theory's named `AdditiveProximityGap`.
* `additiveProximityGap_UD` feeds the landed, hypothesis-free RS proximity
  theorem into that bridge on its proved macroscopic band
  `delta < (1-rho)/3`.
* `additiveFold_distance_UD` closes one additive-FRI round on that band.

The stronger full-UD, Johnson, and post-Johnson regimes need no new additive
algebra: they can feed their stronger `IsProximityGenerator` realizers through
the same generic bridge.  Their assumptions and parameter ranges remain where
they belong, in the corresponding Selvage rate-regime modules.

No Theory file imports Selvage; the candidate-independent boundary remains one-way.
-/
import Theory.AdditiveNTTTransform
import Selvage.ProximityGapUD

namespace Minidregg.Selvage

open Polynomial
open Minidregg.Theory

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Representation: a finite additive image as an RS domain -/

/-- Restrict a field-indexed word to a finite set of coordinates. -/
def wordOn (D : Finset F) (f : F → F) : D → F := fun x => f x

/-- The subtype inclusion `D ↪ F`, packaged as the RS domain embedding. -/
def finsetDomain (D : Finset F) : D ↪ F :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The additive image domain `r ↦ q_beta(r)` indexed by the transversal itself.
The only two points in a fold fiber are `r` and `r + beta`; transversality
therefore makes this an embedding. -/
def additiveImageDomain [CharP F 2] (R : Finset F) (beta : F)
    (hR : ∀ r ∈ R, r + beta ∉ R) : R ↪ F where
  toFun r := foldMap beta r
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact foldMap_injOn_transversal hR x.property y.property hxy

omit [Field F] in
/-- Hamming distance on a finite-set subtype is exactly the cardinality of the
corresponding filter on the original `Finset`. -/
theorem hammingDist_wordOn (D : Finset F) (f g : F → F) :
    hammingDist (wordOn D f) (wordOn D g) =
      (D.filter fun x => f x ≠ g x).card := by
  classical
  unfold hammingDist wordOn
  rw [Finset.univ_eq_attach]
  simpa using congrArg Finset.card
    (Finset.filter_attach (fun x => f x ≠ g x) D)

/-- Convert Theory's `natDegree < d` convention to Selvage's polynomial
`degree < d` convention.  The `0 < d` guard is necessary exactly for the zero
polynomial: `degree 0 = bot`, while `natDegree 0 = 0`. -/
theorem natDegree_lt_iff_degree_lt {p : F[X]} {d : ℕ} (hd : 0 < d) :
    p.natDegree < d ↔ p.degree < (d : WithBot ℕ) := by
  constructor
  · intro hp
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp)
  · intro hp
    by_cases hp0 : p = 0
    · subst p
      simpa using hd
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp

/-- Theory's full-domain counting predicate is exactly Selvage closeness to the
RS code on the subtype domain. -/
theorem closeToDeg_iff_close (D : Finset F) (hD : D.Nonempty) {d : ℕ}
    (hd : 0 < d) (delta : ℝ) (f : F → F) :
    closeToDeg D d delta f ↔
      close delta (reedSolomonCode (finsetDomain D) d) (wordOn D f) := by
  classical
  letI : Nonempty D := Finset.nonempty_coe_sort.mpr hD
  have hn : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  constructor
  · rintro ⟨p, hp, hdist⟩
    let u : D → F := fun x => p.eval x
    refine ⟨u, mem_reedSolomonCode_iff.mpr ⟨p,
      (natDegree_lt_iff_degree_lt hd).mp hp, fun _ => rfl⟩, ?_⟩
    rw [relDist, show hammingDist (wordOn D f) u =
      (D.filter fun x => f x ≠ p.eval x).card by
        simpa [u] using hammingDist_wordOn D f (fun x => p.eval x),
      Fintype.card_coe]
    exact (div_le_iff₀ hn).mpr (by simpa using hdist)
  · rintro ⟨u, hu, hdist⟩
    obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
    refine ⟨p, (natDegree_lt_iff_degree_lt hd).mpr hp, ?_⟩
    rw [relDist] at hdist
    have hham : hammingDist (wordOn D f) u =
        (D.filter fun x => f x ≠ p.eval x).card := by
      calc hammingDist (wordOn D f) u
          = hammingDist (wordOn D f) (fun x : D => p.eval x) := by
              congr 1
              funext x
              exact hpu x
        _ = (D.filter fun x => f x ≠ p.eval x).card := by
              simpa using hammingDist_wordOn D f (fun x => p.eval x)
    rw [hham, Fintype.card_coe] at hdist
    exact (div_le_iff₀ hn).mp hdist

/-- The additive folded-word predicate is Selvage closeness to the RS code whose
evaluation embedding is `r ↦ q_beta(r)`.  This is the central representation
seam: no domain-specific proximity theorem is needed after this point. -/
theorem foldedCloseToDeg_iff_close [CharP F 2] (R : Finset F) (hRn : R.Nonempty)
    (beta : F) (hR : ∀ r ∈ R, r + beta ∉ R) {d : ℕ} (hd : 0 < d)
    (delta : ℝ) (g : F → F) :
    foldedCloseToDeg R beta d delta g ↔
      close delta (reedSolomonCode (additiveImageDomain R beta hR) d) (wordOn R g) := by
  classical
  letI : Nonempty R := Finset.nonempty_coe_sort.mpr hRn
  have hn : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast hRn.card_pos
  constructor
  · rintro ⟨p, hp, hdist⟩
    let u : R → F := fun r => p.eval (foldMap beta r)
    refine ⟨u, mem_reedSolomonCode_iff.mpr ⟨p,
      (natDegree_lt_iff_degree_lt hd).mp hp, fun _ => rfl⟩, ?_⟩
    rw [relDist, show hammingDist (wordOn R g) u =
      (R.filter fun r => g r ≠ p.eval (foldMap beta r)).card by
        simpa [u] using hammingDist_wordOn R g
          (fun r => p.eval (foldMap beta r)),
      Fintype.card_coe]
    exact (div_le_iff₀ hn).mpr (by simpa using hdist)
  · rintro ⟨u, hu, hdist⟩
    obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
    refine ⟨p, (natDegree_lt_iff_degree_lt hd).mpr hp, ?_⟩
    rw [relDist] at hdist
    have hham : hammingDist (wordOn R g) u =
        (R.filter fun r => g r ≠ p.eval (foldMap beta r)).card := by
      calc hammingDist (wordOn R g) u
          = hammingDist (wordOn R g)
              (fun r : R => p.eval (foldMap beta r)) := by
                congr 1
                funext r
                exact hpu r
        _ = (R.filter fun r => g r ≠ p.eval (foldMap beta r)).card := by
              simpa using hammingDist_wordOn R g
                (fun r => p.eval (foldMap beta r))
    rw [hham, Fintype.card_coe] at hdist
    exact (div_le_iff₀ hn).mp hdist

/-! ## Any Selvage proximity generator yields the additive gap -/

/-- **The domain-agnostic bridge.** Any PG(2) realizer for RS on the additive
image domain discharges Theory's `AdditiveProximityGap`, with the usual
conversion `err(delta) * |F| ≤ b` from probability to bad-set cardinality. -/
theorem additiveProximityGap_of_isProximityGenerator [Fintype F] [CharP F 2]
    {R : Finset F} (hRn : R.Nonempty) {beta : F}
    (hR : ∀ r ∈ R, r + beta ∉ R) {d : ℕ} (hd : 0 < d)
    {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator (affineGenerator F)
      (reedSolomonCode (additiveImageDomain R beta hR) d) B err)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaB : delta < 1 - B)
    {b : ℕ} (hb : err delta * (Fintype.card F : ℝ) ≤ (b : ℝ)) :
    AdditiveProximityGap R beta d delta b := by
  classical
  letI : Nonempty R := Finset.nonempty_coe_sort.mpr hRn
  intro u v hno
  let f : Fin 2 → R → F := ![wordOn R u, wordOn R v]
  let C := reedSolomonCode (additiveImageDomain R beta hR) d
  have hnotCA : ¬ CorrelatedAgreement C delta f := by
    rintro ⟨S, hScard, hall⟩
    obtain ⟨u₀, hu₀C, hu₀⟩ := hall 0
    obtain ⟨u₁, hu₁C, hu₁⟩ := hall 1
    obtain ⟨p₀, hp₀, hp₀u⟩ := mem_reedSolomonCode_iff.mp hu₀C
    obtain ⟨p₁, hp₁, hp₁u⟩ := mem_reedSolomonCode_iff.mp hu₁C
    have hn₀ : p₀.natDegree < d := (natDegree_lt_iff_degree_lt hd).mpr hp₀
    have hn₁ : p₁.natDegree < d := (natDegree_lt_iff_degree_lt hd).mpr hp₁
    let valEmb : R ↪ F := ⟨Subtype.val, Subtype.val_injective⟩
    let T : Finset F := S.map valEmb
    have hTsub : T ⊆ R.filter (fun r =>
        u r = p₀.eval (foldMap beta r) ∧ v r = p₁.eval (foldMap beta r)) := by
      intro x hx
      obtain ⟨r, hrS, rfl⟩ := Finset.mem_map.mp hx
      refine Finset.mem_filter.mpr ⟨r.property, ?_⟩
      constructor
      · have h := hu₀ r hrS
        change u r = u₀ r at h
        exact h.trans (hp₀u r)
      · have h := hu₁ r hrS
        change v r = u₁ r at h
        exact h.trans (hp₁u r)
    have hTcard : T.card = S.card := Finset.card_map _
    have hlarge : (1 - delta) * (R.card : ℝ) ≤
        ((R.filter fun r => u r = p₀.eval (foldMap beta r) ∧
          v r = p₁.eval (foldMap beta r)).card : ℝ) := by
      have hSreal : (1 - delta) * (R.card : ℝ) ≤ (S.card : ℝ) := by
        simpa using hScard
      have hmap : (S.card : ℝ) ≤
          ((R.filter fun r => u r = p₀.eval (foldMap beta r) ∧
            v r = p₁.eval (foldMap beta r)).card : ℝ) := by
        rw [← hTcard]
        exact_mod_cast Finset.card_le_card hTsub
      exact hSreal.trans hmap
    exact (not_lt_of_ge hlarge) (hno p₀ p₁ hn₀ hn₁)
  have hpr : (affineGenerator F).pr
      (fun r => close delta C (comb r f)) ≤ err delta := by
    by_contra hgt
    exact hnotCA (hPG f delta hdelta0 hdeltaB (not_le.mp hgt))
  let bad : Finset F := Finset.univ.filter (fun gamma =>
    foldedCloseToDeg R beta d delta (fun r => u r + gamma * v r))
  have hcomb (gamma : F) :
      comb ((affineGenerator F).gen gamma) f =
        wordOn R (fun r => u r + gamma * v r) := by
    funext r
    rw [comb_affineGenerator]
    rfl
  have hpr_eq : (affineGenerator F).pr
      (fun r => close delta C (comb r f)) =
        (bad.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    simp only [affineGenerator]
    have hfilter :
        (Finset.univ.filter fun gamma : F =>
          close delta C (comb ![1, gamma] f)) = bad := by
      unfold bad
      refine Finset.filter_congr fun gamma _ => ?_
      have hc : comb ![1, gamma] f =
          wordOn R (fun r => u r + gamma * v r) := by
        simpa only [affineGenerator] using hcomb gamma
      rw [hc]
      exact (foldedCloseToDeg_iff_close R hRn beta hR hd delta
        (fun r => u r + gamma * v r)).symm
    change (∑ gamma ∈ (Finset.univ.filter fun gamma : F =>
      close delta C (comb ![1, gamma] f)),
        ((Fintype.card F : ℝ))⁻¹) =
      (bad.card : ℝ) / (Fintype.card F : ℝ)
    rw [hfilter]
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hbad : bad.card ≤ b := by
    have hfrac : (bad.card : ℝ) / (Fintype.card F : ℝ) ≤ err delta := by
      rw [← hpr_eq]
      exact hpr
    have hreal : (bad.card : ℝ) ≤ (b : ℝ) :=
      le_trans ((div_le_iff₀ hF).mp hfrac) hb
    exact_mod_cast hreal
  refine ⟨bad, hbad, ?_⟩
  intro gamma hgamma hclose
  apply hgamma
  unfold bad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose⟩

/-! ## Hypothesis-free macroscopic band and one-round soundness -/

/-- **The additive proximity gap, unconditionally on the proved one-third-UD
band.** This is the first macroscopic realization of `[ANTT-proximity]`:
`delta < (1-rho)/3`, error `|R|/|F|`, hence at most `|R|` bad challenges. -/
theorem additiveProximityGap_UD [Fintype F] [CharP F 2]
    {R : Finset F} (hRn : R.Nonempty) {beta : F}
    (hR : ∀ r ∈ R, r + beta ∉ R) {d : ℕ} (hd : 0 < d)
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaB : delta < 1 - (2 + (d : ℝ) / (R.card : ℝ)) / 3) :
    AdditiveProximityGap R beta d delta R.card := by
  letI : Nonempty R := Finset.nonempty_coe_sort.mpr hRn
  have hB : delta <
      1 - (2 + (d : ℝ) / (Fintype.card R : ℝ)) / 3 := by
    simpa using hdeltaB
  have hF : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  apply additiveProximityGap_of_isProximityGenerator hRn hR hd
    (reedSolomonCode_isProximityGenerator_UD (additiveImageDomain R beta hR) d)
    hdelta0 hB
  rw [Fintype.card_coe, div_mul_cancel₀ _ hF]

/-- **One additive-FRI round is sound on the proved macroscopic band.** A word
`delta`-far from degree `< 2d` on `R ∪ (R+beta)` folds, outside at most `|R|`
challenges, to a word still `delta`-far from degree `< d` on the additive
image domain. -/
theorem additiveFold_distance_UD [Fintype F] [CharP F 2]
    {R : Finset F} (hRn : R.Nonempty) {beta : F} (hbeta : beta ≠ 0)
    (hR : ∀ r ∈ R, r + beta ∉ R) {d : ℕ} (hd : 0 < d)
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaB : delta < 1 - (2 + (d : ℝ) / (R.card : ℝ)) / 3)
    {f : F → F} (hfar : ¬ closeToDeg (pairDomain R beta) (2 * d) delta f) :
    ∃ bad : Finset F, bad.card ≤ R.card ∧ ∀ gamma ∉ bad,
      ¬ foldedCloseToDeg R beta d delta (friFold beta gamma f) :=
  additiveFold_distance hbeta hR
    (additiveProximityGap_UD hRn hR hd hdelta0 hdeltaB) hfar

/-! ## Concrete keystone: GF(16), four points, delta = 1/8 -/

open scoped Classical in
/-- At the concrete additive domain `R={0,1}`, `beta=x₁` in GF(16), the
macroscopic gap fires at `d=1`, `delta=1/8`, with at most two bad challenges.
This is strictly positive distance, not the already-proved exact regime. -/
theorem keystone_additiveProximityGap :
    AdditiveProximityGap ({0, 1} : Finset (binaryTower 2)) (fpGen 1) 1 (1 / 8) 2 := by
  letI : Fintype (binaryTower 2) := Fintype.ofFinite _
  simpa using additiveProximityGap_UD
    (R := ({0, 1} : Finset (binaryTower 2))) (beta := fpGen 1)
    (d := 1) (delta := (1 / 8 : ℝ))
    (by simp) keystone_transversal (by norm_num) (by norm_num) (by norm_num)

open scoped Classical in
/-- **Premise inhabitation at positive distance.** The far-word witness already
constructed for the GF(16) additive domain is not merely non-codeword-exact:
it is `1/8`-far.  A four-point word with at most `(1/8)·4 = 1/2`
disagreements has zero disagreements, so `1/8`-closeness would contradict the
landed exact-regime tooth. -/
theorem keystone_far_word_eighth :
    ∃ f : binaryTower 2 → binaryTower 2,
      ¬ closeToDeg (pairDomain {0, 1} (fpGen 1)) 2 (1 / 8) f := by
  obtain ⟨f, hfar⟩ := keystone_far_word_exists
  refine ⟨f, fun hclose => hfar ?_⟩
  obtain ⟨p, hp, hcount⟩ := hclose
  refine ⟨p, hp, ?_⟩
  have hcard : (pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).card = 4 := by
    rw [pairDomain_card keystone_transversal]
    norm_num
  have hlt : (((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
      fun x => f x ≠ p.eval x).card : ℝ) < 1 := by
    rw [hcard] at hcount
    norm_num at hcount
    calc
      (((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
          fun x => f x ≠ p.eval x).card : ℝ) ≤ 1 / 2 := hcount
      _ < 1 := by norm_num
  have hzero : ((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
      fun x => f x ≠ p.eval x).card = 0 := by
    have : ((pairDomain ({0, 1} : Finset (binaryTower 2)) (fpGen 1)).filter
        fun x => f x ≠ p.eval x).card < 1 := by exact_mod_cast hlt
    omega
  rw [hzero]
  norm_num

open scoped Classical in
/-- **The new macroscopic theorem fires end-to-end.** On the concrete GF(16)
four-point domain there is a `1/8`-far word whose additive fold remains
`1/8`-far outside a bad set of at most two challenges. -/
theorem keystone_additiveFold_distance_fires :
    ∃ f : binaryTower 2 → binaryTower 2,
      ¬ closeToDeg (pairDomain {0, 1} (fpGen 1)) 2 (1 / 8) f ∧
      ∃ bad : Finset (binaryTower 2), bad.card ≤ 2 ∧ ∀ gamma ∉ bad,
        ¬ foldedCloseToDeg {0, 1} (fpGen 1) 1 (1 / 8)
          (friFold (fpGen 1) gamma f) := by
  letI : Fintype (binaryTower 2) := Fintype.ofFinite _
  obtain ⟨f, hfar⟩ := keystone_far_word_eighth
  refine ⟨f, hfar, ?_⟩
  simpa using additiveFold_distance_UD
    (R := ({0, 1} : Finset (binaryTower 2))) (beta := fpGen 1)
    (d := 1) (delta := (1 / 8 : ℝ)) (f := f)
    (by simp) (fpGen_ne_zero 1) keystone_transversal
    (by norm_num) (by norm_num) (by norm_num) hfar

/-- info: 'Minidregg.Selvage.additiveProximityGap_of_isProximityGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveProximityGap_of_isProximityGenerator
/-- info: 'Minidregg.Selvage.additiveProximityGap_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveProximityGap_UD
/-- info: 'Minidregg.Selvage.additiveFold_distance_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveFold_distance_UD
/-- info: 'Minidregg.Selvage.keystone_additiveProximityGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keystone_additiveProximityGap
/-- info: 'Minidregg.Selvage.keystone_far_word_eighth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keystone_far_word_eighth
/-- info: 'Minidregg.Selvage.keystone_additiveFold_distance_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keystone_additiveFold_distance_fires

end Minidregg.Selvage
