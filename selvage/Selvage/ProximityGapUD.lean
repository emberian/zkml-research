/-
# Selvage.ProximityGapUD — the RS proximity gap PROVED in the unique-decoding
regime (one-third radius): hPG moves from ASSUMED to PROVED on a macroscopic
interval, and both standing consumers are discharged there.

**What this file is.** Every rate<1 theorem in the landed stack rides ONE
hypothesis: `IsProximityGenerator (affineGenerator F) (RS[dom, d]) B err` —
WHIR Thm 4.8 / BCIKS 2020/654, carried honestly as `hPG` by
`Selvage/ReedSolomon.lean` (Cor 4.11), `Selvage/Proximity.lean`
(`foldDistancePreserving_of_isProximityGenerator`), and `Selvage/SubUdSeam.lean`
(the whole family ladder; its residual `[SUBUD-johnson]`(i) named the UD-case
realizer as the near-term target). This file BUILDS that realizer:
`rs_proximityGap_UD` proves the two-case gap — an affine line
`{f₀ + γ·f₁ : γ ∈ F}` in the function space either has full CORRELATED
AGREEMENT at radius δ (in particular is entirely δ-close to the code), or at
most an `n/|F|` fraction of challenges lands δ-close — and
`reedSolomonCode_isProximityGenerator_UD` / `hasMutualCorrelatedAgreement_UD`
/ `foldDistancePreserving_UD` slot it into the landed consumers with zero
re-derivation.

**The radius, stated plainly (the honest number).** The gap is proved for

  `δ ∈ (0, (1 − ρ)/3)`,  `ρ = d/n`  —  i.e.  `d < (1 − 3δ)·n`,

ONE-THIRD of the way to the unique-decoding radius `(1 − ρ)/2` of BCIKS
Thm 1.2's UD case, with the SAME `err = n/|F|` error shape. The covered scope
in the same sentence as the claim: hPG is now PROVED for every rate ρ < 1 at
radii up to `(1 − ρ)/3`, and remains a hypothesis on `[(1 − ρ)/3, (1 − ρ)/2)`
(and in the Johnson regime beyond). The interval is macroscopic — at the
deployed-shape rate ρ = 1/2 it is `(0, 1/6)` — so this genuinely covers a
rate<1 regime, not only exact membership; it is NOT the full UD interval.
The gap to `(1 − ρ)/2` is the named residual `[PROXGAP-tight]` (prose at the
bottom): the elementary transfer argument below pays a `2δ` start cost (the
first codeword pair is pinned from TWO close challenges, hence on a
`(1 − 2δ)`-set only), and closing the last factor is exactly BCIKS Thm 4.1's
Berlekamp–Welch-over-`F(Z)` argument — real future work, not attempted here,
never assumed.

**The proof (all of it, no sorry).**

1. *Two close points pin an affine codeword line* (`line_pair_agreement`):
   if `f₀ + γᵢ·f₁` agrees with codewords `wᵢ` on `Tᵢ` at two distinct
   challenges, then on `T₀ ∩ T₁` the pair `(f₀, f₁)` agrees with the codeword
   pair `u := w₀ − γ₀·v`, `v := (γ₀ − γ₁)⁻¹·(w₀ − w₁)`, and `wᵢ = u + γᵢ·v`.
   This is the correlated-agreement CORE — the line `u + γ·v` is then
   `2δ`-close to `f₀ + γ·f₁` at EVERY challenge, not just the sampled ones.
2. *Transfer* (inside `correlatedAgreement_of_close_card`): for every close
   challenge `γ`, its codeword `w_γ` EQUALS `u + γ·v` — both agree with
   `f₀ + γ·f₁` on `T_γ ∩ Dᶜ` (`D` the pair's disagreement set, `|D| ≤ 2δn`),
   a set of more than `d` points, and RS codewords agreeing on ≥ d points
   coincide (`reedSolomonCode_eq_of_agreesOn`, read off the landed
   `reedSolomonCode_minDist` — cited, not re-derived). This is the step that
   prices the one-third radius: `(1 − δ)n − 2δn > d`.
3. *The coincidence count boosts `2δ` back to EXACTLY δ*: off `D`, the line
   reproduces `f₀ + γ·f₁` everywhere; on `D`, each coordinate can coincide
   with the line at AT MOST ONE challenge (an affine equation in γ with a
   nonzero coefficient pair — `x ∈ D`!). So per close challenge
   `|D| ≤ ⌊δn⌋ + |K_γ|` with the `K_γ ⊆ D` pairwise disjoint: pigeonhole
   over `≥ ⌊δn⌋ + 2` close challenges forces `|D| ≤ ⌊δn⌋ ≤ δn` — the common
   agreement set `Dᶜ` has ≥ `(1 − δ)n` coordinates ON THE NOSE, no
   quantization loss, no radius loss. (This integer endgame is why the count
   hypothesis is `⌊δn⌋ + 2` — sharper than the `n + 1` that `err = n/|F|`
   supplies.)

**What is DISCHARGED downstream** (the floor-shrink, itemized):

* `reedSolomonCode_isProximityGenerator_UD` — the standing `hPG` of
  `Selvage/ReedSolomon.lean` (Cor 4.11 hypothesis), PROVED at
  `B = (2 + ρ)/3`, `err = n/|F|`.
* `hasMutualCorrelatedAgreement_UD` — mutual correlated agreement for the
  affine generator on `RS[dom, d]` with NO hypothesis beyond `d ≤ n`: the
  landed WHIR Lemma 4.10 machinery
  (`reedSolomonCode_hasMutualCorrelatedAgreement`) fed the proved realizer;
  `B⋆ = max(1 − dC/2, B)` collapses to `B` since `B` already dominates the
  half-distance point. Consumers that assumed `hPG` (SubUdSeam's
  `foldFamily_correlatedAgreement`/`foldFamily_mutualCA`/
  `subUdRecover_of_foldFamily`, DeciderProximity's macroscopic regime) now
  have it PROVED on `δ ∈ (0, (1 − ρ)/3)`.
* `foldDistancePreserving_UD` — `[PROX-fold-distance]` at macroscopic δ
  (`Selvage/Proximity.lean`'s reduction fed the realizer): one FRI fold round
  preserves δ-farness with bad-set bound `b = |κ|` on the same interval —
  the LDT's `proximity_sound` chain now runs hypothesis-free there.

**Honest scope limits.** (i) The radius is `(1 − ρ)/3`, not `(1 − ρ)/2` —
`[PROXGAP-tight]`(a). (ii) `err = n/|F|` has content only when `|F| > n`
(true at deployment; at the F₅ keystone it is 4/5, barely nontrivial — said
plainly there). (iii) The generator covered is PG(2) — the pair/affine-line
case `ℓ = 2`, which is what every landed consumer invokes; the ℓ-tuple
geometric generator is a separate (easier, iterated) extension, named in the
residual. (iv) Probability is rendered through the landed
`ProximityGenerator.pr` (finitely-supported weights), not
`Selvage/Sumcheck.lean`'s `uniformProb` — that import chain is lane-blocked;
the two renderings' unification stays the flagged integration debt.
-/
import Mathlib.Tactic.LinearCombination
import Selvage.CorrelatedAgreement
import Selvage.ReedSolomon
import Selvage.Proximity

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Bridges: δ-closeness ↔ agreement sets, agreement count ↔ equality -/

omit [DecidableEq ι] in
/-- From δ-closeness to an explicit agreement set: the canonical set
`{x | g x = w x}` carries at least `(1 − δ)·n` coordinates. Converse of the
landed `relDist_le_of_agreesOn`. -/
theorem exists_agreesOn_of_close [Nonempty ι] {C : Submodule F (ι → F)}
    {δ : ℝ} {g : ι → F} (h : close δ C g) :
    ∃ w ∈ C, ∃ T : Finset ι,
      (1 - δ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) ∧ AgreesOn T g w := by
  obtain ⟨w, hwC, hrel⟩ := h
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨w, hwC, Finset.univ.filter (fun x => g x = w x),
    ?_, fun x hx => (Finset.mem_filter.mp hx).2⟩
  have hsplit : (Finset.univ.filter fun x => g x = w x).card
      + (Finset.univ.filter fun x => ¬ g x = w x).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hh : hammingDist g w = (Finset.univ.filter fun x => ¬ g x = w x).card := by
    simp [hammingDist, ne_eq]
  have hd : (hammingDist g w : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
    rw [relDist, div_le_iff₀ hn] at hrel
    linarith
  have hcast : ((Finset.univ.filter fun x => g x = w x).card : ℝ)
      + (hammingDist g w : ℝ) = (Fintype.card ι : ℝ) := by
    rw [hh]; exact_mod_cast hsplit
  nlinarith

/-- Two RS codewords agreeing on at least `d` domain points are EQUAL — the
landed minimum distance `reedSolomonCode_minDist` (CITED, not re-derived)
read at agreement-set resolution: distinct codewords agree on ≤ d − 1
points. -/
theorem reedSolomonCode_eq_of_agreesOn [Nonempty ι] (dom : ι ↪ F) {d : ℕ}
    {u v : ι → F} (hu : u ∈ reedSolomonCode dom d)
    (hv : v ∈ reedSolomonCode dom d) {S : Finset ι}
    (hS : (d : ℝ) ≤ (S.card : ℝ)) (hAg : AgreesOn S u v) : u = v := by
  by_contra hne
  have hmd := reedSolomonCode_minDist dom d u hu v hv hne
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdc : (hammingDist u v : ℝ) + (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hammingDist_add_card_le_of_agreesOn hAg
  rw [relDist, le_div_iff₀ hn] at hmd
  have hexp : (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) - ((d : ℝ) - 1) := by
    field_simp
  rw [hexp] at hmd
  linarith

private theorem card_sdiff_univ_cast (S : Finset ι) :
    (((Finset.univ \ S).card : ℝ))
      = (Fintype.card ι : ℝ) - (S.card : ℝ) := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ S)]

/-! ## The correlated-agreement core -/

omit [Fintype ι] [DecidableEq F] in
/-- **Two close points on the line pin an affine codeword line.** From
agreement of `f₀ + γᵢ • f₁` with codewords `wᵢ` on `Tᵢ` at two DISTINCT
challenges, the pair `(f₀, f₁)` agrees on `T₀ ∩ T₁` with a codeword pair
`(u, v)` interpolating both: `wᵢ = u + γᵢ • v`. In particular the whole line
`{u + γ • v}` then reproduces `{f₀ + γ • f₁}` on `T₀ ∩ T₁` at EVERY
challenge — the correlated-agreement direction of the gap. -/
theorem line_pair_agreement {C : Submodule F (ι → F)} {γ₀ γ₁ : F}
    (hne : γ₀ ≠ γ₁) {f₀ f₁ w₀ w₁ : ι → F} (hw₀ : w₀ ∈ C) (hw₁ : w₁ ∈ C)
    {T₀ T₁ : Finset ι} (h₀ : AgreesOn T₀ (f₀ + γ₀ • f₁) w₀)
    (h₁ : AgreesOn T₁ (f₀ + γ₁ • f₁) w₁) :
    ∃ u ∈ C, ∃ v ∈ C,
      AgreesOn (T₀ ∩ T₁) f₀ u ∧ AgreesOn (T₀ ∩ T₁) f₁ v ∧
      w₀ = u + γ₀ • v ∧ w₁ = u + γ₁ • v := by
  have hγ : γ₀ - γ₁ ≠ 0 := sub_ne_zero.mpr hne
  set v : ι → F := (γ₀ - γ₁)⁻¹ • (w₀ - w₁) with hv
  set u : ι → F := w₀ - γ₀ • v with hu
  have hvC : v ∈ C := Submodule.smul_mem C _ (Submodule.sub_mem C hw₀ hw₁)
  have huC : u ∈ C := Submodule.sub_mem C hw₀ (Submodule.smul_mem C _ hvC)
  have hvx : ∀ x ∈ T₀ ∩ T₁, f₁ x = v x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := Finset.mem_inter.mp hx
    have e0 : f₀ x + γ₀ * f₁ x = w₀ x := h₀ x hx0
    have e1 : f₀ x + γ₁ * f₁ x = w₁ x := h₁ x hx1
    show f₁ x = (γ₀ - γ₁)⁻¹ * (w₀ x - w₁ x)
    rw [← e0, ← e1]
    field_simp
    ring
  have hux : ∀ x ∈ T₀ ∩ T₁, f₀ x = u x := by
    intro x hx
    have e0 : f₀ x + γ₀ * f₁ x = w₀ x := h₀ x (Finset.mem_inter.mp hx).1
    show f₀ x = w₀ x - γ₀ * v x
    rw [← hvx x hx, ← e0]
    ring
  refine ⟨u, huC, v, hvC, hux, hvx, ?_, ?_⟩
  · funext x
    show w₀ x = (w₀ x - γ₀ * v x) + γ₀ * v x
    ring
  · funext x
    show w₁ x = (w₀ x - γ₀ * ((γ₀ - γ₁)⁻¹ * (w₀ x - w₁ x)))
      + γ₁ * ((γ₀ - γ₁)⁻¹ * (w₀ x - w₁ x))
    field_simp
    ring

/-- **The UD-regime correlated-agreement core, counting form (field-size
free).** If the line `f 0 + γ • f 1` is δ-close to `RS[dom, d]` for at least
`⌊δn⌋ + 2` challenges, with `d < (1 − 3δ)·n` (one-third of the
unique-decoding radius), then the pair has correlated agreement at radius δ
EXACTLY: one common agreement set of ≥ `(1 − δ)·n` coordinates — no radius
loss, no quantization loss. Two close challenges pin the codeword line
(`line_pair_agreement`, a `(1 − 2δ)`-set); every close challenge's codeword
transfers onto that line (`reedSolomonCode_eq_of_agreesOn` — the step that
prices the one-third radius); and the per-coordinate ≤ 1 coincidence
challenge plus pigeonhole over `⌊δn⌋ + 2` challenges crushes the
disagreement set back to `⌊δn⌋`. -/
theorem correlatedAgreement_of_close_card [Nonempty ι] (dom : ι ↪ F) {d : ℕ}
    {δ : ℝ} (hδ0 : 0 < δ)
    (hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ))
    {f : Fin 2 → ι → F} {A : Finset F}
    (hAclose : ∀ γ ∈ A, close δ (reedSolomonCode dom d) (f 0 + γ • f 1))
    (hAcard : Nat.floor (δ * (Fintype.card ι : ℝ)) + 2 ≤ A.card) :
    CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  classical
  set C := reedSolomonCode dom d with hC
  set n : ℕ := Fintype.card ι with hn'
  have hn : (0 : ℝ) < (n : ℝ) := by
    rw [hn']; exact_mod_cast Fintype.card_pos
  set e : ℕ := Nat.floor (δ * (n : ℝ)) with he'
  have heδ : (e : ℝ) ≤ δ * (n : ℝ) := Nat.floor_le (by positivity)
  -- per-challenge witnesses
  have hex : ∀ γ ∈ A, ∃ w ∈ C, ∃ T : Finset ι,
      (1 - δ) * (n : ℝ) ≤ (T.card : ℝ) ∧ AgreesOn T (f 0 + γ • f 1) w :=
    fun γ hγ => exists_agreesOn_of_close (hAclose γ hγ)
  choose! w hwC T hTcard hTag using hex
  -- a distinct close pair
  have hA2 : 1 < A.card := by omega
  obtain ⟨γ₀, hγ₀, γ₁, hγ₁, hγne⟩ := Finset.one_lt_card.mp hA2
  -- the pinned codeword pair (u, v)
  obtain ⟨u, huC, v, hvC, hagf₀, hagf₁, hw₀, hw₁⟩ :=
    line_pair_agreement hγne (hwC γ₀ hγ₀) (hwC γ₁ hγ₁)
      (hTag γ₀ hγ₀) (hTag γ₁ hγ₁)
  -- the disagreement set of the pair against (u, v)
  set D : Finset ι := Finset.univ.filter
    (fun x => ¬ (f 0 x = u x ∧ f 1 x = v x)) with hD'
  have hnotD : ∀ x, x ∉ D → f 0 x = u x ∧ f 1 x = v x := by
    intro x hx
    by_contra hcon
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcon⟩)
  have hinD : ∀ x ∈ D, ¬ (f 0 x = u x ∧ f 1 x = v x) :=
    fun x hx => (Finset.mem_filter.mp hx).2
  -- |D| ≤ 2δn: D avoids T γ₀ ∩ T γ₁, which has ≥ (1 − 2δ)n coordinates
  have hDsub : D ⊆ Finset.univ \ (T γ₀ ∩ T γ₁) := by
    intro x hx
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ x, fun hxT => hinD x hx ⟨hagf₀ x hxT, hagf₁ x hxT⟩⟩
  have hTT : (1 - 2 * δ) * (n : ℝ) ≤ ((T γ₀ ∩ T γ₁).card : ℝ) := by
    have hkey : ((T γ₀ ∪ T γ₁).card : ℝ) + ((T γ₀ ∩ T γ₁).card : ℝ)
        = ((T γ₀).card : ℝ) + ((T γ₁).card : ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter (T γ₀) (T γ₁)
    have hun : ((T γ₀ ∪ T γ₁).card : ℝ) ≤ (n : ℝ) := by
      rw [hn']; exact_mod_cast Finset.card_le_univ (T γ₀ ∪ T γ₁)
    have h0 := hTcard γ₀ hγ₀
    have h1 := hTcard γ₁ hγ₁
    linarith
  have hDcard : (D.card : ℝ) ≤ 2 * δ * (n : ℝ) := by
    have h1 : (D.card : ℝ) ≤ ((Finset.univ \ (T γ₀ ∩ T γ₁)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hDsub
    rw [card_sdiff_univ_cast, ← hn'] at h1
    linarith
  -- off D, the pinned line reproduces the observed line at EVERY challenge
  have hlineD : ∀ (γ : F) (x : ι), x ∉ D →
      (f 0 + γ • f 1) x = (u + γ • v) x := by
    intro γ x hx
    obtain ⟨h0, h1⟩ := hnotD x hx
    show f 0 x + γ * f 1 x = u x + γ * v x
    rw [h0, h1]
  -- TRANSFER: every close challenge's codeword IS on the pinned line
  have htrans : ∀ γ ∈ A, w γ = u + γ • v := by
    intro γ hγ
    have hlineC : u + γ • v ∈ C :=
      Submodule.add_mem C huC (Submodule.smul_mem C γ hvC)
    refine reedSolomonCode_eq_of_agreesOn dom (hwC γ hγ) hlineC
      (S := T γ ∩ (Finset.univ \ D)) ?_ ?_
    · -- card ≥ (1 − δ)n + (n − |D|) − n ≥ (1 − 3δ)n > d
      have hkey : ((T γ ∪ (Finset.univ \ D)).card : ℝ)
          + ((T γ ∩ (Finset.univ \ D)).card : ℝ)
          = ((T γ).card : ℝ) + (((Finset.univ \ D)).card : ℝ) := by
        exact_mod_cast Finset.card_union_add_card_inter (T γ) (Finset.univ \ D)
      have hun : ((T γ ∪ (Finset.univ \ D)).card : ℝ) ≤ (n : ℝ) := by
        rw [hn']; exact_mod_cast Finset.card_le_univ (T γ ∪ (Finset.univ \ D))
      have hDc := card_sdiff_univ_cast D
      rw [← hn'] at hDc
      have hTγ := hTcard γ hγ
      linarith
    · intro x hx
      obtain ⟨hxT, hxD⟩ := Finset.mem_inter.mp hx
      have hxD' : x ∉ D := (Finset.mem_sdiff.mp hxD).2
      rw [← hTag γ hγ x hxT, hlineD γ x hxD']
  -- the endgame split: either D is already small, or count coincidences
  by_cases hDδ : (D.card : ℝ) ≤ δ * (n : ℝ)
  · -- correlated agreement delivered on S := univ \ D
    refine ⟨Finset.univ \ D, ?_, ?_⟩
    · rw [card_sdiff_univ_cast, ← hn']
      linarith
    · intro i
      induction i using Fin.cases with
      | zero =>
          exact ⟨u, huC, fun x hx => (hnotD x (Finset.mem_sdiff.mp hx).2).1⟩
      | succ j =>
          have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
          rw [hj]
          exact ⟨v, hvC, fun x hx => (hnotD x (Finset.mem_sdiff.mp hx).2).2⟩
  · -- coincidence sets: on D, each coordinate coincides with the line at
    -- AT MOST ONE challenge — pigeonhole over ⌊δn⌋ + 2 challenges
    exfalso
    have hDe : e + 1 ≤ D.card := by
      have hlt : δ * (n : ℝ) < (D.card : ℝ) := not_le.mp hDδ
      have : (e : ℝ) < (D.card : ℝ) := lt_of_le_of_lt heδ hlt
      exact_mod_cast this
    set K : F → Finset ι := fun γ =>
      D.filter (fun x => f 0 x + γ * f 1 x = u x + γ * v x) with hK'
    have hKsub : ∀ γ, K γ ⊆ D := fun γ => Finset.filter_subset _ _
    -- pairwise disjoint: two coincidences at one x ∈ D force f = (u,v) at x
    have hKdisj : ∀ γ γ' : F, γ ≠ γ' → Disjoint (K γ) (K γ') := by
      intro γ γ' hne'
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨hxD, hcoin⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, hcoin'⟩ := Finset.mem_filter.mp hx'
      have hsub' : (γ - γ') * (f 1 x - v x) = 0 := by
        linear_combination hcoin - hcoin'
      have h1 : f 1 x = v x := by
        rcases mul_eq_zero.mp hsub' with h | h
        · exact absurd (sub_eq_zero.mp h) hne'
        · exact sub_eq_zero.mp h
      have h0 : f 0 x = u x := by linear_combination hcoin - γ * h1
      exact hinD x hxD ⟨h0, h1⟩
    -- per close challenge: |D| ≤ e + |K γ|
    have hperγ : ∀ γ ∈ A, D.card ≤ e + (K γ).card := by
      intro γ hγ
      have hsub : D \ K γ ⊆ Finset.univ \ T γ := by
        intro x hx
        obtain ⟨hxD, hxK⟩ := Finset.mem_sdiff.mp hx
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ x, fun hxT => hxK ?_⟩
        refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
        have h1 : f 0 x + γ * f 1 x = w γ x := hTag γ hγ x hxT
        have h2 : w γ x = u x + γ * v x := by rw [htrans γ hγ]; rfl
        rw [h1, h2]
      have hcompl : (Finset.univ \ T γ).card ≤ e := by
        apply Nat.le_floor
        rw [card_sdiff_univ_cast, ← hn']
        have := hTcard γ hγ
        linarith
      have hDsplit : (D ∩ K γ).card + (D \ K γ).card = D.card :=
        Finset.card_inter_add_card_sdiff D (K γ)
      have hDK : (D ∩ K γ).card ≤ (K γ).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h3 : (D \ K γ).card ≤ e :=
        le_trans (Finset.card_le_card hsub) hcompl
      omega
    -- pigeonhole: the disjoint K γ ⊆ D can each miss ≤ e of D's mass
    have hsum : ∑ γ ∈ A, (K γ).card ≤ D.card := by
      rw [← Finset.card_biUnion (fun γ _ γ' _ h => hKdisj γ γ' h)]
      exact Finset.card_le_card (Finset.biUnion_subset.mpr fun γ _ => hKsub γ)
    have hlow : ∀ γ ∈ A, D.card - e ≤ (K γ).card := by
      intro γ hγ
      have := hperγ γ hγ
      omega
    have hcount : A.card * (D.card - e) ≤ D.card := by
      have h := Finset.card_nsmul_le_sum A (fun γ => (K γ).card)
        (D.card - e) hlow
      rw [smul_eq_mul] at h
      exact le_trans h hsum
    -- numeric contradiction: (e + 2)·s ≤ e + s with s ≥ 1 is absurd
    have h1 : e * (D.card - e) + 2 * (D.card - e) ≤ D.card := by
      calc e * (D.card - e) + 2 * (D.card - e)
          = (e + 2) * (D.card - e) := by ring
        _ ≤ A.card * (D.card - e) := Nat.mul_le_mul_right _ hAcard
        _ ≤ D.card := hcount
    have h2 : e ≤ e * (D.card - e) := Nat.le_mul_of_pos_right e (by omega)
    generalize hm : e * (D.card - e) = m at h1 h2
    omega

/-! ## The gap heads: `rs_proximityGap_UD` and the hPG discharge -/

/-- Correlated agreement makes the WHOLE line δ-close: at every challenge the
interpolated codeword `u + γ • v` sits within δ — the "entirely close" half
of the gap's good case. -/
theorem line_close_of_correlatedAgreement [Nonempty ι]
    {C : Submodule F (ι → F)} {δ : ℝ} {f : Fin 2 → ι → F}
    (h : CorrelatedAgreement C δ f) (γ : F) :
    close δ C (f 0 + γ • f 1) := by
  obtain ⟨S, hS, hall⟩ := h
  obtain ⟨u, huC, hu⟩ := hall 0
  obtain ⟨v, hvC, hv⟩ := hall 1
  refine ⟨u + γ • v, Submodule.add_mem C huC (Submodule.smul_mem C γ hvC),
    relDist_le_of_agreesOn (S := S) (fun x hx => ?_) hS⟩
  show f 0 x + γ * f 1 x = u x + γ * v x
  rw [hu x hx, hv x hx]

/-- **`rs_proximityGap_UD` — the Reed–Solomon proximity gap at the
one-third-UD radius, two-case form (BCIKS Thm 1.2's UD shape, provable
regime, `err = n/|F|`).** For `d < (1 − 3δ)·n`: either at most an `n/|F|`
fraction of challenges lands the affine line `f 0 + γ • f 1` δ-close to the
code, or the pair has FULL correlated agreement at radius δ — whence the line
is ENTIRELY δ-close (`line_close_of_correlatedAgreement`). The gap: the
closeness probability never sits strictly between `n/|F|` and the
all-challenges regime. -/
theorem rs_proximityGap_UD [Nonempty ι] [Fintype F] (dom : ι ↪ F) {d : ℕ}
    {δ : ℝ} (hδ0 : 0 < δ)
    (hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ))
    (f : Fin 2 → ι → F) :
    (affineGenerator F).pr
        (fun r => close δ (reedSolomonCode dom d) (comb r f))
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
    ∨ CorrelatedAgreement (reedSolomonCode dom d) δ f := by
  classical
  set C := reedSolomonCode dom d with hC
  by_cases hpr : (affineGenerator F).pr (fun r => close δ C (comb r f))
      ≤ (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
  · exact Or.inl hpr
  right
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set A : Finset F := Finset.univ.filter
    (fun γ => close δ C (f 0 + γ • f 1)) with hA
  -- the closeness probability is the bad-challenge fraction
  have hpr_eq : (affineGenerator F).pr (fun r => close δ C (comb r f))
      = (A.card : ℝ) / (Fintype.card F : ℝ) := by
    unfold ProximityGenerator.pr
    have hcomb : ∀ γ : F, comb ((affineGenerator F).gen γ) f = f 0 + γ • f 1 :=
      fun γ => funext fun x => by rw [comb_affineGenerator]; rfl
    have hfilter : (Finset.univ.filter fun ω : (affineGenerator F).Seed =>
        close δ C (comb ((affineGenerator F).gen ω) f)) = A := by
      rw [hA]
      refine Finset.filter_congr fun γ _ => ?_
      rw [hcomb γ]
    rw [hfilter]
    calc ∑ ω ∈ A, (affineGenerator F).weight ω
        = ∑ _ω ∈ A, ((Fintype.card F : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun ω _ => rfl
      _ = (A.card : ℝ) * ((Fintype.card F : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (A.card : ℝ) / (Fintype.card F : ℝ) := (div_eq_mul_inv _ _).symm
  -- more than n close challenges
  have hAn : (Fintype.card ι : ℝ) < (A.card : ℝ) := by
    rw [hpr_eq] at hpr
    have h := not_le.mp hpr
    rw [div_lt_div_iff_of_pos_right hF] at h
    exact h
  -- n + 1 ≥ ⌊δn⌋ + 2, since δ < 1/3
  have hAcard : Nat.floor (δ * (Fintype.card ι : ℝ)) + 2 ≤ A.card := by
    have hδ3' : (0 : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ) :=
      lt_of_le_of_lt (Nat.cast_nonneg d) hδ3
    have heδ : (Nat.floor (δ * (Fintype.card ι : ℝ)) : ℝ)
        ≤ δ * (Fintype.card ι : ℝ) := Nat.floor_le (by positivity)
    have hδn0 : (0 : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by positivity
    have hen : (Nat.floor (δ * (Fintype.card ι : ℝ)) : ℝ)
        < (Fintype.card ι : ℝ) := by nlinarith
    have hen' : Nat.floor (δ * (Fintype.card ι : ℝ)) + 1 ≤ Fintype.card ι := by
      exact_mod_cast hen
    have hAn' : Fintype.card ι + 1 ≤ A.card := by exact_mod_cast hAn
    omega
  exact correlatedAgreement_of_close_card dom hδ0 hδ3
    (fun γ hγ => (Finset.mem_filter.mp hγ).2) hAcard

/-- **The hPG DISCHARGE — the standing proximity-gap hypothesis PROVED at the
one-third-UD radius.** The affine generator PG(2) IS a proximity generator
for `RS[dom, d]` with bound `B = (2 + ρ)/3` (admissible radii
`δ ∈ (0, (1 − ρ)/3)`) and error `err = n/|F|`. This is the hypothesis that
`Selvage/ReedSolomon.lean` (Cor 4.11), `Selvage/Proximity.lean`
(`foldDistancePreserving_of_isProximityGenerator`) and `Selvage/SubUdSeam.lean`
(the family ladder; residual `[SUBUD-johnson]`(i)) carried as `hPG` —
realized here, hypothesis-free, on that interval. -/
theorem reedSolomonCode_isProximityGenerator_UD [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) (d : ℕ) :
    IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      ((2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  intro f δ hδ0 hδB hpr
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδ3 : (d : ℝ) < (1 - 3 * δ) * (Fintype.card ι : ℝ) := by
    -- δ < 1 − (2 + ρ)/3 = (1 − ρ)/3  ⟺  ρ < 1 − 3δ  ⟺  d < (1 − 3δ)n
    have hρ : (d : ℝ) / (Fintype.card ι : ℝ) < 1 - 3 * δ := by linarith
    calc (d : ℝ) = (d : ℝ) / (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) := by
          field_simp
      _ < (1 - 3 * δ) * (Fintype.card ι : ℝ) :=
          mul_lt_mul_of_pos_right hρ hn
  rcases rs_proximityGap_UD dom hδ0 hδ3 f with h | h
  · exact absurd hpr (not_lt.mpr h)
  · exact h

/-- **`hasMutualCorrelatedAgreement_UD` — mutual correlated agreement for the
affine generator on RS, NO proximity-gap hypothesis left.** The landed WHIR
Lemma 4.10 / Corollary 4.11 machinery
(`reedSolomonCode_hasMutualCorrelatedAgreement`, CITED) fed the proved
realizer: `B⋆ = max(1 − dC/2, (2 + ρ)/3)` collapses to `(2 + ρ)/3` (which
already dominates the half-distance point for `d ≤ n`), with the same error
`n/|F|`. Every consumer that assumed `hPG` now has mutual CA PROVED on
`δ ∈ (0, (1 − ρ)/3)`. -/
theorem hasMutualCorrelatedAgreement_UD [Nonempty ι] [Fintype F]
    (dom : ι ↪ F) {d : ℕ} (hdn : d ≤ Fintype.card ι) :
    HasMutualCorrelatedAgreement (affineGenerator F) (reedSolomonCode dom d)
      ((2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3)
      (fun _ => (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F)
    dom d (reedSolomonCode_isProximityGenerator_UD dom d)
    (fun _ _ _ => le_refl _)
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hle : 1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2
      ≤ (2 + (d : ℝ) / (Fintype.card ι : ℝ)) / 3 := by
    -- (1 + ρ − 1/n)/2 ≤ (2 + ρ)/3 ⟺ ρ ≤ 1 + 3/n, and ρ ≤ 1
    have hsub : ((d : ℝ) - 1) / (Fintype.card ι : ℝ)
        = (d : ℝ) / (Fintype.card ι : ℝ) - 1 / (Fintype.card ι : ℝ) :=
      sub_div _ _ _
    have hρ1 : (d : ℝ) / (Fintype.card ι : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      exact_mod_cast hdn
    have h1n : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
    rw [hsub]
    linarith
  rwa [max_eq_right hle] at h

/-! ## The LDT consumer: `[PROX-fold-distance]` discharged at macroscopic δ -/

/-- **`[PROX-fold-distance]` PROVED at the one-third-UD radius** — the
macroscopic-δ regime of `Selvage/Proximity.lean`, previously REDUCED to `hPG`
(`foldDistancePreserving_of_isProximityGenerator`, CITED), now fed the proved
realizer: one FRI fold round preserves δ-farness off at most `|κ|` challenges
(`err δ · |F| = |κ|`), for every `δ ∈ (0, (1 − ρ_κ)/3)` at the folded rate
`ρ_κ = d/|κ|`. The `proximity_sound` chain runs hypothesis-free on this
interval. -/
theorem foldDistancePreserving_UD {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype F] [Nonempty ι] [Nonempty κ] {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδB : δ < 1 - (2 + (d : ℝ) / (Fintype.card κ : ℝ)) / 3) :
    FoldDistancePreserving D (2 * d) d δ (Fintype.card κ) := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact foldDistancePreserving_of_isProximityGenerator D d
    (reedSolomonCode_isProximityGenerator_UD domSq d) hδ0 hδB
    (le_of_eq (div_mul_cancel₀ _ (ne_of_gt hF)))

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The landed `RS[F₅, {0,1,2,3}, 2]` (rate ρ = 1/2, so `B = 5/6`,
δ-interval `(0, 1/6)`, `err = n/|F| = 4/5`). Plainly said: at this toy size
the error bound `4/5` is barely below 1 — the gap has real content here only
because an all-codeword line has probability exactly 1; at deployed field
sizes `n/|F|` is tiny. What the keystones exhibit:

* **satisfiable / the hypothesis FIRES at rate < 1**: the all-codeword line
  `xWord + γ · oneWord` has closeness probability 1 > 4/5, and the PROVED
  generator delivers correlated agreement — the first hPG firing at a
  macroscopic-rate code (every landed firing site was the full-rate ⊤).
* **teeth / the gap is real**: the line `badWord + γ · (−badWord)` through
  the non-codeword spike `(0,1,0,0)` is NOT entirely close, its bad set is
  EXACTLY `{1}` — nonempty (some challenge genuinely launders the far pair)
  and of measure `1/5 ≤ 4/5` — and the pair has NO correlated agreement at
  δ = 1/8: the gap's left case fires with a computed, nonvacuous bad set.
* **interval nonempty**: δ = 1/8 ∈ (0, 1/6) with all hypotheses discharged
  numerically. -/

namespace ProximityGapUDExample

open RSExample

/-- The constant-1 word — evaluations of the constant polynomial `1`. -/
def oneWord : Fin 4 → ZMod 5 := fun _ => 1

theorem oneWord_mem : oneWord ∈ reedSolomonCode dom₅ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 1,
      by rw [Polynomial.degree_C (by decide : (1 : ZMod 5) ≠ 0)]; decide,
      fun i => by simp [oneWord]⟩

/-- The good line is codewords through and through. -/
theorem line_mem (γ : ZMod 5) :
    xWord + γ • oneWord ∈ reedSolomonCode dom₅ 2 :=
  Submodule.add_mem _ xWord_mem (Submodule.smul_mem _ _ oneWord_mem)

/-- The good line's closeness probability is exactly 1. -/
theorem line_pr_one :
    (affineGenerator (ZMod 5)).pr (fun r =>
      close (1/8 : ℝ) (reedSolomonCode dom₅ 2) (comb r ![xWord, oneWord]))
      = 1 := by
  classical
  have heq : ∀ γ : ZMod 5,
      comb ((affineGenerator (ZMod 5)).gen γ) ![xWord, oneWord]
        = xWord + γ • oneWord :=
    fun γ => funext fun x => by rw [comb_affineGenerator]; rfl
  have hall : ∀ ω : (affineGenerator (ZMod 5)).Seed,
      close (1/8 : ℝ) (reedSolomonCode dom₅ 2)
        (comb ((affineGenerator (ZMod 5)).gen ω) ![xWord, oneWord]) := by
    intro γ
    rw [heq γ]
    exact close_of_mem (line_mem γ) (by norm_num)
  unfold ProximityGenerator.pr
  rw [Finset.filter_true_of_mem fun ω _ => hall ω]
  exact (affineGenerator (ZMod 5)).weight_sum_one

/-- **The PROVED generator FIRES at rate 1/2** — probability 1 exceeds the
error 4/5 and the theorem (not a by-hand witness) delivers correlated
agreement. Compare the landed firing sites, which were all full-rate ⊤. -/
theorem good_line_CA :
    CorrelatedAgreement (reedSolomonCode dom₅ 2) (1/8 : ℝ)
      ![xWord, oneWord] := by
  refine reedSolomonCode_isProximityGenerator_UD (F := ZMod 5) dom₅ 2
    ![xWord, oneWord] (1/8 : ℝ) (by norm_num) ?_ ?_
  · -- 1/8 < 1 − (2 + 2/4)/3 = 1/6
    norm_num [Fintype.card_fin]
  · rw [line_pr_one]
    have h5 : (Fintype.card (ZMod 5) : ℝ) = 5 := by
      rw [ZMod.card]; norm_num
    rw [Fintype.card_fin, h5]
    norm_num

/-- ...and the good case of the gap in its "entirely close" reading: every
point of the line is δ-close (here: is a codeword). -/
example (γ : ZMod 5) :
    close (1/8 : ℝ) (reedSolomonCode dom₅ 2)
      (![xWord, oneWord] 0 + γ • ![xWord, oneWord] 1) :=
  line_close_of_correlatedAgreement good_line_CA γ

/-! ### Teeth: a far pair, its bad set computed exactly -/

/-- The spike `(0, 1, 0, 0)` on the `{0,1,2,3}` domain. -/
def badWord : Fin 4 → ZMod 5 := ![0, 1, 0, 0]

/-- Its negation `(0, 4, 0, 0)` — the pair `(badWord, negBadWord)` spans the
line `(1 − γ) • badWord`. -/
def negBadWord : Fin 4 → ZMod 5 := ![0, 4, 0, 0]

/-- The spike is NOT a line codeword: it vanishes at the two domain points
`0` and `2` yet is nonzero — root counting via the landed
`card_agreeSet_lt_of_ne` (mirrors `ProximityExample.spikeWord_notMem`, which
lives on the other domain `{1,2,3,4}`). -/
theorem badWord_notMem : badWord ∉ reedSolomonCode dom₅ 2 := by
  intro hmem
  obtain ⟨p, hdeg, hp⟩ := mem_reedSolomonCode_iff.mp hmem
  have hpne : p ≠ 0 := by
    intro h0
    have h1 := hp 1
    rw [h0, Polynomial.eval_zero] at h1
    exact absurd h1 (by decide)
  have hcard := card_agreeSet_lt_of_ne dom₅ (d := 2) hdeg
    (q := 0) (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _) hpne
  have hsub : ({0, 2} : Finset (Fin 4))
      ⊆ Finset.univ.filter fun i =>
        p.eval (dom₅ i) = (0 : Polynomial (ZMod 5)).eval (dom₅ i) := by
    intro i hi
    have h0 := hp 0
    have h2 := hp 2
    fin_cases hi <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Polynomial.eval_zero] <;>
      [rw [← h0]; rw [← h2]] <;> decide
  have h2le : 2 ≤ (Finset.univ.filter fun i =>
      p.eval (dom₅ i) = (0 : Polynomial (ZMod 5)).eval (dom₅ i)).card :=
    le_trans (by decide) (Finset.card_le_card hsub)
  omega

/-- The bad line collapses to a scalar multiple of the spike. -/
theorem bad_line_eq (γ : ZMod 5) :
    badWord + γ • negBadWord = (1 - γ) • badWord := by
  revert γ
  decide

/-- Below the quantization floor `1/4`, δ-closeness IS membership. -/
theorem close_iff_mem {g : Fin 4 → ZMod 5} :
    close (1/8 : ℝ) (reedSolomonCode dom₅ 2) g
      ↔ g ∈ reedSolomonCode dom₅ 2 := by
  constructor
  · rintro ⟨u, huC, hrel⟩
    have heq : g = u := by
      by_contra hne
      have hfloor := one_div_card_le_relDist (F := ZMod 5) hne
      rw [Fintype.card_fin] at hfloor
      linarith
    rwa [heq]
  · intro h
    exact close_of_mem h (by norm_num)

/-- The bad-challenge set of the far pair — the challenges landing the line
δ-close (classically measurable, the landed `acceptSet` idiom). -/
noncomputable def badSet : Finset (ZMod 5) :=
  letI : DecidablePred fun γ : ZMod 5 =>
      close (1/8 : ℝ) (reedSolomonCode dom₅ 2) (badWord + γ • negBadWord) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter fun γ : ZMod 5 =>
    close (1/8 : ℝ) (reedSolomonCode dom₅ 2) (badWord + γ • negBadWord)

theorem mem_badSet {γ : ZMod 5} :
    γ ∈ badSet
      ↔ close (1/8 : ℝ) (reedSolomonCode dom₅ 2)
          (badWord + γ • negBadWord) := by
  simp [badSet]

/-- **The bad set computed EXACTLY: `{1}`.** One challenge launders the far
pair (at `γ = 1` the line degenerates to the zero codeword); every other
challenge sees a non-codeword at distance ≥ 1/4. -/
theorem badSet_eq : badSet = {1} := by
  ext γ
  rw [mem_badSet, Finset.mem_singleton]
  constructor
  · intro hclose
    have hmem := close_iff_mem.mp hclose
    rw [bad_line_eq γ] at hmem
    by_contra hne
    have h1γ : (1 : ZMod 5) - γ ≠ 0 := by
      intro h
      exact hne (sub_eq_zero.mp h).symm
    have hbad : badWord ∈ reedSolomonCode dom₅ 2 := by
      have h := Submodule.smul_mem _ ((1 : ZMod 5) - γ)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ h1γ, one_smul] at h
    exact badWord_notMem hbad
  · rintro rfl
    rw [close_iff_mem, bad_line_eq]
    have hz : ((1 : ZMod 5) - 1) • badWord = 0 := by decide
    rw [hz]
    exact Submodule.zero_mem _

/-- The far pair has NO correlated agreement at δ = 1/8: an agreement set of
≥ 3.5 coordinates out of 4 is everything, and everywhere-agreement would put
the spike in the code. -/
theorem bad_pair_no_CA :
    ¬ CorrelatedAgreement (reedSolomonCode dom₅ 2) (1/8 : ℝ)
      ![badWord, negBadWord] := by
  rintro ⟨S, hcard, hall⟩
  have hS4 : S.card = 4 := by
    have h3 : (3 : ℝ) < (S.card : ℝ) := by
      rw [Fintype.card_fin] at hcard
      norm_num at hcard
      linarith
    have h3' : 3 < S.card := by exact_mod_cast h3
    have hle : S.card ≤ 4 := by
      have h := Finset.card_le_univ S
      rwa [Fintype.card_fin] at h
    omega
  have hSuniv : S = Finset.univ :=
    Finset.eq_univ_of_card S (by rw [hS4, Fintype.card_fin])
  obtain ⟨u, huC, hu⟩ := hall 0
  have hbadeq : badWord = u := by
    funext x
    exact hu x (by rw [hSuniv]; exact Finset.mem_univ x)
  exact badWord_notMem (hbadeq ▸ huC)

/-- **The gap's teeth, assembled**: the bad line is NOT entirely close
(γ = 0 misses), it IS deceptively close somewhere (γ = 1 — the bad set is
nonempty, the error bound guards a real event), the bad set has size
`1 ≤ n = 4` (measure `1/5 ≤ 4/5 = n/|F|`), and correlated agreement FAILS —
the left disjunct of `rs_proximityGap_UD` is the live one, with slack. -/
theorem bad_line_teeth :
    ¬ close (1/8 : ℝ) (reedSolomonCode dom₅ 2)
        (badWord + (0 : ZMod 5) • negBadWord)
    ∧ close (1/8 : ℝ) (reedSolomonCode dom₅ 2)
        (badWord + (1 : ZMod 5) • negBadWord)
    ∧ badSet.card = 1
    ∧ ¬ CorrelatedAgreement (reedSolomonCode dom₅ 2) (1/8 : ℝ)
        ![badWord, negBadWord] := by
  refine ⟨?_, ?_, ?_, bad_pair_no_CA⟩
  · intro hclose
    have h : (0 : ZMod 5) ∈ badSet := mem_badSet.mpr hclose
    rw [badSet_eq, Finset.mem_singleton] at h
    exact absurd h (by decide)
  · have h : (1 : ZMod 5) ∈ ({1} : Finset (ZMod 5)) := Finset.mem_singleton_self 1
    rw [← badSet_eq, mem_badSet] at h
    exact h
  · rw [badSet_eq, Finset.card_singleton]

/-- The δ-interval of the discharged theorems is NONEMPTY at the tiny code:
`1/8 ∈ (0, 1 − B)` with `B = (2 + 2/4)/3 = 5/6`. -/
example : (0 : ℝ) < 1/8 ∧
    (1/8 : ℝ) < 1 - (2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3 := by
  constructor
  · norm_num
  · norm_num [Fintype.card_fin]

/-- The discharged mutual-CA head, instantiated end-to-end at the tiny code
(every hypothesis numeric: `d = 2 ≤ 4 = n`). -/
theorem mutualCA_F5 :
    HasMutualCorrelatedAgreement (affineGenerator (ZMod 5))
      (reedSolomonCode dom₅ 2)
      ((2 + (2 : ℝ) / (Fintype.card (Fin 4) : ℝ)) / 3)
      (fun _ => (Fintype.card (Fin 4) : ℝ) / (Fintype.card (ZMod 5) : ℝ)) :=
  hasMutualCorrelatedAgreement_UD dom₅ (by rw [Fintype.card_fin]; omega)

end ProximityGapUDExample

/-! ## Residual obligation — `[PROXGAP-tight]`, prose not stub

What CLOSED here: the UD correlated-agreement CORE (two close points pin the
codeword line; every close challenge's codeword transfers onto it; the
per-coordinate single-coincidence count restores the EXACT radius δ with no
quantization loss), the two-case gap `rs_proximityGap_UD` with the BCIKS
`err = n/|F|` shape, and the hypothesis-free discharge of all three standing
consumers (`IsProximityGenerator`, mutual CA, `[PROX-fold-distance]`) — on
`δ ∈ (0, (1 − ρ)/3)`.

What REMAINS, named precisely:

* **(a) The radius: `(1 − ρ)/3 → (1 − ρ)/2`** (BCIKS 2020/654 Thm 1.2 /
  Thm 4.1, the full UD case). The elementary argument here cannot cross
  one-third: the starting pair is pinned on a `(1 − 2δ)`-set only, and the
  transfer needs `(1 − δ)n − 2δn > d`. BCIKS close the gap by solving the
  Berlekamp–Welch system over the rational function field `F(Z)` (a nonzero
  maximal minor is a degree-≤ `⌊δn⌋ + 1` polynomial in the challenge —
  THAT is where their bad-challenge count comes from — and the generic
  solution specializes to every close challenge). Formalizable, genuinely
  heavier: linear systems over `F(Z)`, rank under specialization, division
  in `F(Z)[X]`. Nothing downstream consumes the missing band today: every
  landed invocation prices its radius through a hypothesis that this file's
  realizer either already discharges or leaves untouched.
* **(b) The error constant.** The core needs only `⌊δn⌋ + 2` close
  challenges — the heads round up to `err = n/|F|` (the literature label)
  because `pr > n/|F|` gives `n + 1 ≥ ⌊δn⌋ + 2` for free. A sharper head at
  `err = (⌊δn⌋ + 1)/|F|` is available from the same core; not stated, to
  keep the consumer-facing constant the recognizable one.
* **(c) ℓ > 2.** PG(2) — the affine pair, the only generator any landed
  consumer invokes — is what is realized. The geometric ℓ-tuple generator
  `(1, α, …, α^{ℓ−1})` follows by iterating the pair case (fold the tuple
  associatively) or by the same argument with an ℓ-variate coincidence
  count; neither is done here.
* **(d) The Johnson regime** (`B = √ρ`, WHIR Thm 4.8 / BCIKS Thm 1.2
  proper) is untouched and stays exactly where the landed files keep it: a
  hypothesis, never an instance — inherited unchanged as
  `Selvage/ReedSolomon.lean`'s keystone TODO and `[SUBUD-johnson]`(i)'s hard
  half.

## Ledger

* `exists_agreesOn_of_close` / `reedSolomonCode_eq_of_agreesOn` — PROVED:
  the two bridges (closeness → explicit `(1 − δ)n` agreement set; ≥ d-point
  agreement → codeword equality, via the CITED `reedSolomonCode_minDist`).
* `line_pair_agreement` — PROVED: two close points pin the affine codeword
  line — the correlated-agreement core.
* `correlatedAgreement_of_close_card` — PROVED: `⌊δn⌋ + 2` close challenges
  at `d < (1 − 3δ)n` force correlated agreement at radius EXACTLY δ
  (transfer + disjoint coincidence sets + integer pigeonhole).
* `line_close_of_correlatedAgreement` — PROVED: the good case's "entirely
  δ-close line" reading.
* `rs_proximityGap_UD` — PROVED: the two-case gap, `err = n/|F|`.
* `reedSolomonCode_isProximityGenerator_UD` — PROVED: **hPG discharged** at
  `B = (2 + ρ)/3`, `err = n/|F|`.
* `hasMutualCorrelatedAgreement_UD` — PROVED: mutual CA hypothesis-free on
  `δ ∈ (0, (1 − ρ)/3)` (landed Lemma 4.10 machinery CITED, `max` collapsed).
* `foldDistancePreserving_UD` — PROVED: `[PROX-fold-distance]` macroscopic
  regime discharged (landed reduction CITED), bad-set bound `|κ|`.
* Keystones — `good_line_CA` (the proved generator FIRES at rate 1/2 — the
  first non-⊤ firing site in the tree), `line_pr_one`, `badWord_notMem`,
  `badSet_eq` (bad set EXACTLY `{1}`), `bad_pair_no_CA`, `bad_line_teeth`
  (gap two-sided on concrete instances), `mutualCA_F5`, interval-nonempty
  `example`s.
* Residual — `[PROXGAP-tight]` (prose above): (a) radius `(1−ρ)/3 → (1−ρ)/2`
  (BW over `F(Z)`), (b) the sharper `(⌊δn⌋+1)/|F|` constant, (c) ℓ > 2,
  (d) Johnson (inherited, untouched).

`#print axioms` on `rs_proximityGap_UD`,
`reedSolomonCode_isProximityGenerator_UD`, `hasMutualCorrelatedAgreement_UD`,
`foldDistancePreserving_UD`, `ProximityGapUDExample.good_line_CA`,
`ProximityGapUDExample.bad_line_teeth`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
