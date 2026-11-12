/-
# Selvage.SubUdSeam — [ZK-RBR-extract] open lemma A attacked: the SUB-UNIQUE-
DECODING seam. The lemma as POSED (extend `recoverFromColumns` to `t < d`)
is REFUTED in its column form and REALIZED in its mutual-CA form; the
remainder sharpens to `[SUBUD-johnson]`.

`Selvage/ZkExtraction.lean` named lemma A exactly: the seam recovers each round
increment from `t ≥ d` opened columns (`recoverFromColumns_sound`), but that
regime is INCOMPATIBLE with constrained-mask hiding (`t + r ≤ d`,
`not_constrainedMask_hiding_of_recoverable`) — the two demands never share a
`t`. The deployed constrained-mask protocol therefore needs the increment
recovered from `t < d` columns per round, "via erasure correction inside the
MUTUAL AGREEMENT SET across the fold family (WARP App. B's actual route),
not per-word unique decoding". This file builds that route. The finding:

**The `t`-window conflict was an artifact of the COLUMN-resolution decoder,
and it DISSOLVES at word resolution — the recovery never counts columns.**

* **The recovery ladder, each rung proved.** The seam's data is the
  correlated fold family `foldFamily f₀ g ρ = f₀ + ρ • g` (successive
  recommitted partial folds ARE this shape — `partialFold_foldFamily`,
  citing `partialFold_succ`):
  1. ONE fold word pins NOTHING about the increment: every candidate `g'`
     is consistent with any observed single fold
     (`single_fold_word_ambiguous`).
  2. TWO exact fold words pin the increment COMPLETELY — this is the landed
     two-point extractor, cited not re-derived (`extractPair_foldFamily`,
     via `extractPair_snd`).
  3. `t < d` COLUMNS of the family — even at EVERY challenge at once — pin
     NOTHING: two distinct codeword increments produce IDENTICAL column
     tables for the whole family, so NO extractor consuming column data
     alone can recover both (`foldFamily_columns_ambiguous`,
     `no_column_extractor` — quantified over ALL recovery functions). The
     posed "extend `recoverFromColumns` to `t < d`" is impossible AS A
     FUNCTION OF COLUMNS; more challenges at the same `t` positions never
     escape `recoverFromColumns_teeth`'s ambiguity.
  4. The δ-CLOSE family plus correlated agreement pins the increment's
     CODEWORD: if the fold at a random challenge is δ-close to the code
     often enough (`err δ < Pr`), the pair `(f₀, g)` agrees with codewords
     `(u₀, u_g)` on ONE common set of ≥ `(1−δ)n` coordinates
     (`foldFamily_correlatedAgreement`, firing the `IsProximityGenerator`
     hypothesis on the tuple `![f₀, g]` — the fold family IS the affine
     generator's combination, `foldFamily_eq_comb`), and below the
     unique-decoding radius `δ < dC/2` that codeword is UNIQUE
     (`subUdRecover_sound`, via the landed `codeword_eq_of_close_of_close`
     + `reedSolomonCode_minDist`, cited). The mutual-CA refinement is the
     landed WHIR Lemma 4.10/Corollary 4.11 cited verbatim
     (`foldFamily_mutualCA` = `reedSolomonCode_hasMutualCorrelatedAgreement`
     at `![f₀, g]`), and per NON-FAILING seed the observed fold's OWN
     agreement set becomes the recovery's (`subUdRecover_of_seed` — this is
     where mutual, not plain, CA is load-bearing).

* **`subUdRecover` — the sub-UD decoder.** Word-resolution list decoding at
  radius δ: pick any codeword with a `(1−δ)`-fraction agreement set (`dif`
  idiom, junk `0` outside — `recoverFromColumns`'s honesty discipline).
  PROVED: always a codeword (`subUdRecover_mem`); pins UNIQUELY below
  `dC/2` (`subUdRecover_sound`); exact on genuine codewords
  (`subUdRecover_codeword`); and — the adversarial content — the increment
  of two committed folds that only δ-AGREE with the honest successive
  partial folds is recovered EXACTLY at radius `2δ`
  (`subUdRecover_increment`, via `card_inter_agreement` +
  `increment_agreesOn`: the two agreement sets intersect in a
  `(1−2δ)`-fraction set that still pins). The composed headline is
  `subUdRecover_of_foldFamily`: family closeness event ⇒ the recovery
  agrees with the committed increment on a mutual agreement set carrying a
  SIMULTANEOUS correction of the previous fold, and the recovered family
  reproduces the committed family on that set at EVERY challenge — the
  opened columns that land in it are exactly reproduced.

* **The seam, re-proved with NO `t ≥ d` anywhere.**
  `subUdSeamCounterfactual` mirrors `seamCounterfactual` field for field
  with ONE change visible in the type: it consumes the recommitted fold
  WORDS (`folds : ℕ → ι → F` — what the roots bind) where the old seam
  consumed opened COLUMNS (`cols : ℕ → Fin t → F`), and routes the
  increment `γ⁻¹ • (folds (k+1) − folds k)` (`seam_increment`) through
  `subUdRecover` instead of `recoverFromColumns`. `extractChain_subUdSeam`
  then inverts the whole chain — `extractChain_flatFold` cited, the shapes
  regime-independent exactly as `[ZK-RBR-extract]` predicted — with no
  column count, no query injectivity, no `d ≤ t` hypothesis in the entire
  composition. Consequence, computed on F₅: at `t = 1 < d = 2` (inside the
  constrained-mask hiding window `t + r ≤ d`) hiding HOLDS while the
  increment is recovered (`subud_hiding_coexist_F5`, citing the landed
  `window_F5`) — the regime `not_constrainedMask_hiding_of_recoverable`
  proved impossible for the COLUMN seam is inhabited by the WORD seam.

* **Honest scope — what "recovery" consumes here.** The sub-UD route reads
  the fold words at ROOT resolution (in the ideal binding model the root
  determines the word — `Selvage/Commitment.lean`'s discipline), not at column
  resolution; rung 3 proves this is NOT a convenience but a necessity. The
  δ-closeness EVENT (`hobs`) enters as a premise: bridging it from the
  deployed `t`-column spot checks is the sampling bound, part (iv) of the
  residual — `t` enters the sub-UD seam ONLY as soundness amplification
  (a fold δ-far from its checked shape survives one uniformly-opened column
  with probability ≤ `1 − δ`; `card_compl_le_of_agreement` is the mass
  bound it composes with), never as an interpolation count. And every CA
  theorem rides the standing `hPG` hypothesis (WHIR Thm 4.8 / BCIKS
  2020/654) exactly as the landed `Selvage/ReedSolomon.lean` corollaries do —
  hypothesis, never instance or axiom.

**Keystones** (F₅ at the landed `RS[F₅, {0,1,2,3}, 2]` + a fresh
`RS[F₁₁, {0..7}, 2]` corruption site + the full-rate `hPG`-inhabited site):
recovery fires at `t`-free `d = 2` (`subud_recover_xWord`); the family
theorem fires END TO END with every hypothesis discharged at the full-rate
code (`subud_family_fires` — genuine `IsProximityGenerator`, nonzero
closeness probability, `B⋆`-interval inhabited); the seam extraction fires
at depth 2 on the landed masked family `msEx` with NO column hypothesis
(`subud_seam_extraction_F5` — compare `seam_extraction_F5`'s `t = d`);
teeth: identical family column tables for `xWord` vs `twoXWord` at
`t = 1 < d` defeat EVERY column extractor while `subUdRecover` returns both
exactly (`family_pins_where_columns_cannot`, `single_fold_ambiguous_F5`);
the old decoder is junk at `t < d` and confidently WRONG on corrupted
columns where the new one CORRECTS (`old_route_junk_new_route_recovers`,
`old_route_decodes_wrong_on_corruption` vs `corrupted_increment_recovered`
— a genuinely non-codeword committed increment, `corrupted_increment_not_code`,
decoded to the true codeword); the UD-radius premise is load-bearing:
beyond `dC/2` two codewords qualify at once (`beyond_ud_list_ambiguous` —
the `[SUBUD-johnson]` frontier, computed). No `sorry`, no vacuous
`Prop := True`.
-/
import Selvage.ZkExtraction
import Selvage.CorrelatedAgreement
import Selvage.Erasure
import Selvage.ReedSolomon

namespace Minidregg.Selvage

namespace ProximityGenerator

/-- The certain event has probability 1 — the completeness companion of the
landed `pr_eq_zero`; consumed by the keystone that fires the family theorem
end to end. -/
theorem pr_one {F : Type*} {ℓ : ℕ} (G : ProximityGenerator F ℓ)
    {E : (Fin ℓ → F) → Prop} (h : ∀ r, E r) : G.pr E = 1 := by
  classical
  unfold pr
  rw [Finset.filter_true_of_mem fun ω _ => h _]
  exact G.weight_sum_one

end ProximityGenerator

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The correlated fold family: the seam's object -/

/-- **The correlated fold family**: the recommitted word at challenge `ρ` —
previous fold plus `ρ`-weighted increment. Successive recommitted partial
folds are EXACTLY this shape (`partialFold_foldFamily` below), and the family
over the challenge draw is EXACTLY the affine proximity generator's
combination (`foldFamily_eq_comb` below): the seam's correlation is not an
analogy to the CA machinery, it IS its input. -/
def foldFamily (f₀ g : ι → F) (ρ : F) : ι → F := f₀ + ρ • g

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp] theorem foldFamily_apply (f₀ g : ι → F) (ρ : F) (x : ι) :
    foldFamily f₀ g ρ x = f₀ x + ρ * g x := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The fold family IS the affine generator's combination on the pair
`![f₀, g]` — the bridge that lets every landed correlated-agreement theorem
fire on the seam's own object. -/
theorem foldFamily_eq_comb [Fintype F] (f₀ g : ι → F) (ρ : F) :
    foldFamily f₀ g ρ = comb ((affineGenerator F).gen ρ) ![f₀, g] := by
  funext x
  rw [comb_affineGenerator]
  simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **Ladder rung 1 — one fold word pins nothing**: EVERY candidate increment
`g'` is consistent with any single observed fold word (shift the unseen
previous fold by `ρ • (g − g')`). The family, not the member, carries the
increment. -/
theorem single_fold_word_ambiguous (f₀ g g' : ι → F) (ρ : F) :
    foldFamily (f₀ + ρ • (g - g')) g' ρ = foldFamily f₀ g ρ := by
  unfold foldFamily
  rw [smul_sub]
  abel

/-! ## `subUdRecover`: word-resolution list decoding at radius δ -/

/-- **The sub-UD decoder.** Pick any codeword agreeing with `g` on a set of
at least `(1 − δ)·n` coordinates — list decoding at radius δ, presented as an
agreement-set decoder (the shape mutual CA outputs). `dif` idiom: junk `0`
when no such codeword exists (and `0` IS a codeword, so `subUdRecover_mem`
holds unconditionally — the def never lies about its type). Below the
unique-decoding radius the choice is FORCED (`subUdRecover_sound`); beyond
it the choice is genuinely ambiguous (`beyond_ud_list_ambiguous`) — the
`[SUBUD-johnson]` frontier. NO column count appears: this is the decoder the
`t < d` seam runs on. -/
noncomputable def subUdRecover (dom : ι ↪ F) (d : ℕ) (δ : ℝ) (g : ι → F) :
    ι → F :=
  letI : Decidable (∃ u, u ∈ reedSolomonCode dom d ∧ ∃ S : Finset ι,
      (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧ AgreesOn S g u) :=
    Classical.propDecidable _
  if h : ∃ u, u ∈ reedSolomonCode dom d ∧ ∃ S : Finset ι,
      (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧ AgreesOn S g u
  then h.choose else 0

omit [DecidableEq ι] [DecidableEq F] in
/-- The recovered word is ALWAYS a genuine codeword, whatever the input —
even the junk branch returns the zero codeword. -/
theorem subUdRecover_mem (dom : ι ↪ F) (d : ℕ) (δ : ℝ) (g : ι → F) :
    subUdRecover dom d δ g ∈ reedSolomonCode dom d := by
  unfold subUdRecover
  split
  · next h => exact h.choose_spec.1
  · exact Submodule.zero_mem _

/-- **THE PIN — below unique decoding the agreement set determines the
codeword.** If `u` is a codeword agreeing with `g` on ≥ `(1 − δ)·n`
coordinates and `δ < dC/2` (the exact RS unique-decoding radius,
`dC = 1 − (d−1)/n`), then `subUdRecover` returns `u` on the nose: any OTHER
qualifying codeword is also within δ of `g`, and two codewords within
`δ < dC/2` of a common word coincide — the landed
`codeword_eq_of_close_of_close` fed the landed `reedSolomonCode_minDist`
(both CITED, `relDist_le_of_agreesOn` bridging agreement to distance). This
is "recovered up to the mutual-CA list" with the list PROVED a singleton in
the UD regime. -/
theorem subUdRecover_sound [Nonempty ι] (dom : ι ↪ F) {d : ℕ} {δ : ℝ}
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {g u : ι → F} (hu : u ∈ reedSolomonCode dom d) {S : Finset ι}
    (hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ))
    (hAg : AgreesOn S g u) : subUdRecover dom d δ g = u := by
  have hex : ∃ u', u' ∈ reedSolomonCode dom d ∧ ∃ S' : Finset ι,
      (1 - δ) * (Fintype.card ι : ℝ) ≤ (S'.card : ℝ) ∧ AgreesOn S' g u' :=
    ⟨u, hu, S, hS, hAg⟩
  unfold subUdRecover
  rw [dif_pos hex]
  obtain ⟨huC', S', hS', hAg'⟩ := hex.choose_spec
  exact codeword_eq_of_close_of_close (reedSolomonCode_minDist dom d) huC' hu
    hδUD (relDist_le_of_agreesOn hAg' hS') (relDist_le_of_agreesOn hAg hS)

/-- Genuine codewords are recovered EXACTLY — completeness of the sub-UD
decoder, family-free (the honest prover's increments are codewords). -/
theorem subUdRecover_codeword [Nonempty ι] (dom : ι ↪ F) {d : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {g : ι → F} (hg : g ∈ reedSolomonCode dom d) :
    subUdRecover dom d δ g = g := by
  refine subUdRecover_sound dom hδUD hg (S := Finset.univ) ?_ fun x _ => rfl
  rw [Finset.card_univ]
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hδ0 hn]

/-! ## The mutual-CA step: the landed machinery fired on the family -/

omit [DecidableEq ι] in
/-- **Ladder rung 4a — correlated agreement of the seam pair.** If the fold
at a random challenge is δ-close to the code with probability above the
generator's error, then previous fold AND increment agree with codewords on
ONE COMMON set of ≥ `(1 − δ)·n` coordinates — `IsProximityGenerator`
(the standing WHIR Thm 4.8 / BCIKS hypothesis, carried exactly as
`Selvage/ReedSolomon.lean` carries it) fired on the tuple `![f₀, g]`, whose
combinations ARE the fold family (`foldFamily_eq_comb`). The COMMON set is
the correlation doing work: separate agreement sets for `f₀` and `g` would
not survive the increment algebra. -/
theorem foldFamily_correlatedAgreement [Nonempty ι] [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      B err)
    (f₀ g : ι → F) {δ : ℝ} (hδ0 : 0 < δ) (hδB : δ < 1 - B)
    (hobs : err δ < (affineGenerator F).pr
      (fun r => close δ (reedSolomonCode dom d) (comb r ![f₀, g]))) :
    ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
      (∃ u₀ ∈ reedSolomonCode dom d, AgreesOn S f₀ u₀) ∧
      ∃ ug ∈ reedSolomonCode dom d, AgreesOn S g ug := by
  obtain ⟨S, hcard, hall⟩ := hPG ![f₀, g] δ hδ0 hδB hobs
  refine ⟨S, hcard, ?_, ?_⟩
  · simpa using hall 0
  · simpa using hall 1

/-- **Ladder rung 4b — the MUTUAL refinement, cited.** The failure event —
some agreement set of the combined fold is NOT an agreement set of the pair —
has probability ≤ `err δ` on the unique-decoding interval: the landed
`reedSolomonCode_hasMutualCorrelatedAgreement` (WHIR Lemma 4.10 /
Corollary 4.11) applied at the seam pair, VERBATIM. Nothing re-derived. -/
theorem foldFamily_mutualCA [Nonempty ι] [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B →
      err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ)
    (f₀ g : ι → F) {δ : ℝ} (hδ0 : 0 < δ)
    (hδlt : δ < 1 -
      max (1 - (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2) B) :
    (affineGenerator F).pr
        (MutualCAFailure (reedSolomonCode dom d) δ ![f₀, g]) ≤ err δ :=
  reedSolomonCode_hasMutualCorrelatedAgreement (affineGenerator F) dom d hPG
    (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)
    ![f₀, g] δ hδ0 hδlt

/-- **Per-seed recovery — where MUTUAL (not plain) CA is load-bearing.** For
a challenge OUTSIDE the mutual-CA failure event, ANY agreement set the
observed fold exhibits with a codeword — the set the verifier's checks
actually probe — is already a set on which the increment agrees with a
codeword, and below the UD radius `subUdRecover` returns exactly that
correction ON THAT SET. Plain CA only promises SOME common set somewhere;
mutual CA hands the extractor the one the transcript exhibits. -/
theorem subUdRecover_of_seed [Nonempty ι] [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {δ : ℝ}
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {f₀ g : ι → F} {ρ : F}
    (hnofail : ¬ MutualCAFailure (reedSolomonCode dom d) δ ![f₀, g]
      ((affineGenerator F).gen ρ))
    {S : Finset ι} (hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ))
    {w : ι → F} (hw : w ∈ reedSolomonCode dom d)
    (hAg : AgreesOn S (foldFamily f₀ g ρ) w) :
    AgreesOn S g (subUdRecover dom d δ g) := by
  have hg : ∃ u ∈ reedSolomonCode dom d, AgreesOn S g u := by
    by_contra hno
    push Not at hno
    refine hnofail ⟨S, hS, ⟨w, hw, ?_⟩, 1, ?_⟩
    · rwa [← foldFamily_eq_comb]
    · intro u' hu'
      simpa using hno u' hu'
  obtain ⟨ug, hugC, hug⟩ := hg
  rw [subUdRecover_sound dom hδUD hugC hS hug]
  exact hug

/-! ## The composed statement: the family pins where a single fold cannot -/

/-- **`subUdRecover_of_foldFamily` — the sub-UD seam recovery, composed.**
From the observable family event (the recommitted fold at a random challenge
is δ-close to the code more often than the generator's error) and NO column
data at all: the recovered increment is a codeword agreeing with the
COMMITTED increment on a set `S` of ≥ `(1 − δ)·n` coordinates, the previous
fold is SIMULTANEOUSLY corrected on the SAME set, and at EVERY challenge the
recovered family reproduces the committed family throughout `S` — so every
opened column landing in `S` (all but a δ-fraction of any query schedule,
`card_compl_le_of_agreement`) is exactly reproduced. Correlated agreement
does the pinning (`foldFamily_correlatedAgreement`); unique decoding forces
the codeword (`subUdRecover_sound`). Where the erasure seam demanded
`d ≤ t`, NOTHING here counts columns — the premise the deployed protocol
must discharge is the closeness EVENT, priced in the residual. -/
theorem subUdRecover_of_foldFamily [Nonempty ι] [Fintype F]
    {dom : ι ↪ F} {d : ℕ} {B : ℝ} {err : ℝ → ℝ}
    (hPG : IsProximityGenerator (affineGenerator F) (reedSolomonCode dom d)
      B err)
    {f₀ g : ι → F} {δ : ℝ} (hδ0 : 0 < δ) (hδB : δ < 1 - B)
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    (hobs : err δ < (affineGenerator F).pr
      (fun r => close δ (reedSolomonCode dom d) (comb r ![f₀, g]))) :
    subUdRecover dom d δ g ∈ reedSolomonCode dom d ∧
      ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
        AgreesOn S g (subUdRecover dom d δ g) ∧
        ∃ u₀ ∈ reedSolomonCode dom d, AgreesOn S f₀ u₀ ∧
          ∀ ρ : F, AgreesOn S (foldFamily f₀ g ρ)
            (foldFamily u₀ (subUdRecover dom d δ g) ρ) := by
  obtain ⟨S, hcard, h₀, hg⟩ :=
    foldFamily_correlatedAgreement hPG f₀ g hδ0 hδB hobs
  obtain ⟨u₀, hu₀C, hu₀⟩ := h₀
  obtain ⟨ug, hugC, hug⟩ := hg
  have hrec : subUdRecover dom d δ g = ug :=
    subUdRecover_sound dom hδUD hugC hcard hug
  refine ⟨by rw [hrec]; exact hugC, S, hcard, by rw [hrec]; exact hug,
    u₀, hu₀C, hu₀, fun ρ x hx => ?_⟩
  rw [foldFamily_apply, foldFamily_apply, hrec, hu₀ x hx, hug x hx]

/-- At most a δ-fraction of coordinates — hence of ANY query schedule — falls
outside a `(1 − δ)`-agreement set: the mass bound the residual's sampling
bridge (part iv of `[SUBUD-johnson]`) composes with. -/
theorem card_compl_le_of_agreement {S : Finset ι} {δ : ℝ}
    (hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ)) :
    ((Finset.univ \ S).card : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
  have hsub : (Finset.univ \ S).card = Fintype.card ι - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  have hcast : ((Finset.univ \ S).card : ℝ)
      = (Fintype.card ι : ℝ) - (S.card : ℝ) := by
    rw [hsub, Nat.cast_sub hle]
  rw [hcast]
  nlinarith

/-! ## The adversarial increment: corrupted folds, corrected recovery -/

/-- Two `(1 − δ)`-agreement sets intersect in a `(1 − 2δ)`-agreement set —
inclusion–exclusion against the whole domain. -/
theorem card_inter_agreement {S₁ S₂ : Finset ι} {δ : ℝ}
    (h₁ : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S₁.card : ℝ))
    (h₂ : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S₂.card : ℝ)) :
    (1 - 2 * δ) * (Fintype.card ι : ℝ) ≤ ((S₁ ∩ S₂).card : ℝ) := by
  have hkey : ((S₁ ∪ S₂).card : ℝ) + ((S₁ ∩ S₂).card : ℝ)
      = (S₁.card : ℝ) + (S₂.card : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter S₁ S₂
  have hu : ((S₁ ∪ S₂).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_le_univ (S₁ ∪ S₂)
  linarith

omit [Fintype ι] [DecidableEq F] in
/-- Committed folds that agree with the honest successive words `P` and
`P + γ • w` on `S₁`, `S₂` have their challenge-normalized difference agree
with the true increment `w` on `S₁ ∩ S₂` — the seam algebra survives
coordinate corruption wherever BOTH folds are honest. -/
theorem increment_agreesOn {γ : F} (hγ0 : γ ≠ 0) {P w cPrev cNext : ι → F}
    {S₁ S₂ : Finset ι} (hnext : AgreesOn S₁ cNext (P + γ • w))
    (hprev : AgreesOn S₂ cPrev P) :
    AgreesOn (S₁ ∩ S₂) (γ⁻¹ • (cNext - cPrev)) w := by
  intro x hx
  rw [Finset.mem_inter] at hx
  show γ⁻¹ * (cNext x - cPrev x) = w x
  rw [hnext x hx.1, hprev x hx.2]
  show γ⁻¹ * (P x + γ * w x - P x) = w x
  rw [add_sub_cancel_left]
  exact inv_mul_cancel_left₀ hγ0 (w x)

/-- **The adversarial sub-UD recovery**: committed folds merely δ-AGREEING
with the honest successive partial-fold words (the shape mutual CA delivers
from the family event) have their increment recovered EXACTLY at radius
`2δ` — corruption corrected, no columns, no `t ≥ d`. The `2δ < dC/2` window
is the honest price of differencing two corrupted words. -/
theorem subUdRecover_increment [Nonempty ι] (dom : ι ↪ F) {d : ℕ} {δ : ℝ}
    (h2δ : 2 * δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {γ : F} (hγ0 : γ ≠ 0) {P w cPrev cNext : ι → F}
    (hw : w ∈ reedSolomonCode dom d) {S₁ S₂ : Finset ι}
    (hS₁ : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S₁.card : ℝ))
    (hS₂ : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S₂.card : ℝ))
    (hnext : AgreesOn S₁ cNext (P + γ • w)) (hprev : AgreesOn S₂ cPrev P) :
    subUdRecover dom d (2 * δ) (γ⁻¹ • (cNext - cPrev)) = w :=
  subUdRecover_sound dom h2δ hw (card_inter_agreement hS₁ hS₂)
    (increment_agreesOn hγ0 hnext hprev)

/-! ## Ladder rung 3, general form: columns never pin -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- Increments sharing their `t` opened symbols produce IDENTICAL fold-family
columns at EVERY challenge — the correlation is invisible at column
resolution. -/
theorem foldFamily_columns_ambiguous {t : ℕ} {q : Fin t → ι} {g g' : ι → F}
    (hcols : openSymbols q g = openSymbols q g') (f₀ : ι → F) (ρ : F)
    (j : Fin t) : foldFamily f₀ g ρ (q j) = foldFamily f₀ g' ρ (q j) := by
  have h := congrFun hcols j
  simp only [openSymbols_apply] at h
  simp [h]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **No extractor from columns — full quantifier strength.** ANY recovery
function consuming the family's opened columns — the ENTIRE challenge-indexed
table, strictly more than any protocol opens — that recovers one increment
must FAIL on another sharing its `t` symbols. The posed "extend
`recoverFromColumns` to `t < d`" has no realizer at column resolution; the
sub-UD seam is forced to word resolution, where `subUdRecover_of_foldFamily`
lives. -/
theorem no_column_extractor {t : ℕ} {q : Fin t → ι} {g g' : ι → F}
    (hcols : openSymbols q g = openSymbols q g') (hne : g ≠ g') (f₀ : ι → F)
    (rec : (F → Fin t → F) → ι → F)
    (hrec : rec (fun ρ j => foldFamily f₀ g ρ (q j)) = g) :
    rec (fun ρ j => foldFamily f₀ g' ρ (q j)) ≠ g' := by
  have htable : (fun ρ j => foldFamily f₀ g ρ (q j))
      = fun ρ j => foldFamily f₀ g' ρ (q j) :=
    funext fun ρ => funext fun j => foldFamily_columns_ambiguous hcols f₀ ρ j
  rw [← htable, hrec]
  exact hne

end Family

section Seam

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-! ## The seam structure: recommitted partial folds ARE the fold family -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The recommitted seam IS the fold family: round `k`'s recommitted word is
`foldFamily` of the previous partial fold and the round word at the round
challenge — `partialFold_succ` (CITED), repackaged as the family shape the
CA machinery consumes. -/
theorem partialFold_foldFamily (γs : ℕ → F) (f₀ : ι → F)
    (ms : Fin n → ι → F) (k : Fin n) :
    partialFold γs f₀ ms ((k : ℕ) + 1)
      = foldFamily (partialFold γs f₀ ms (k : ℕ)) (ms k) (γs (k : ℕ)) :=
  partialFold_succ γs f₀ ms k

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- The increment is a WORD-resolution function of two successive fold words:
challenge-normalized difference. This is what the recommitted roots bind —
one level deeper than the opened columns, and (rung 3) necessarily so. -/
theorem seam_increment (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F)
    (k : Fin n) (hγ0 : γs (k : ℕ) ≠ 0) :
    (γs (k : ℕ))⁻¹ • (partialFold γs f₀ ms ((k : ℕ) + 1)
        - partialFold γs f₀ ms (k : ℕ))
      = ms k := by
  rw [partialFold_succ, add_sub_cancel_left]
  exact inv_smul_smul₀ hγ0 _

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
/-- **Ladder rung 2 — two exact fold words pin the increment completely**:
the landed two-point extractor (`extractPair_snd`, CITED) inverts the family
at any two distinct challenges. Exact words in, exact increment out; the
mutual-CA machinery is needed precisely when the words are only δ-close. -/
theorem extractPair_foldFamily {ρ ρ' : F} (hne : ρ ≠ ρ') (f₀ g : ι → F) :
    (extractPair (foldFamily f₀ g ρ) (foldFamily f₀ g ρ') ρ ρ').2 = g := by
  rw [extractPair_snd]
  have h : foldFamily f₀ g ρ - foldFamily f₀ g ρ' = (ρ - ρ') • g := by
    unfold foldFamily
    rw [sub_smul]
    abel
  rw [h, inv_smul_smul₀ (sub_ne_zero_of_ne hne)]

/-! ## The sub-UD seam counterfactual: `seamCounterfactual` with no columns -/

/-- **The sub-UD seam counterfactual** — `seamCounterfactual` mirrored field
for field, ONE change visible in the type: it consumes the recommitted fold
WORDS (`folds : ℕ → ι → F`, what the roots bind) where the old seam consumed
opened COLUMNS (`cols : ℕ → Fin t → F`), and routes the increment through
`subUdRecover` instead of `recoverFromColumns`. NO `t`, NO query positions,
NO `d ≤ t` anywhere in the type or its theorems. -/
noncomputable def subUdSeamCounterfactual (dom : ι ↪ F) (d : ℕ) (δ : ℝ)
    (γs γalt : ℕ → F) (h₀ : ι → F) (folds : ℕ → ι → F) (k : Fin n) :
    ι → F :=
  h₀ + (γalt (k : ℕ) - γs (k : ℕ)) •
    subUdRecover dom d δ
      ((γs (k : ℕ))⁻¹ • (folds ((k : ℕ) + 1) - folds (k : ℕ)))

/-- **The sub-UD seam furnishes the counterfactual, exactly** — the mirror of
`seamCounterfactual_sound` with the `d ≤ t` hypothesis GONE: when the fold
words are the genuine recommitted partial folds and the round word is a
codeword, the synthesized transcript equals the true `k`-perturbed one.
`seam_increment` isolates the increment, `subUdRecover_codeword` decodes it,
`flatFold_updSched` (CITED) reweights. -/
theorem subUdSeamCounterfactual_sound [Nonempty ι] (dom : ι ↪ F) {d : ℕ}
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {γs γalt : ℕ → F} {f₀ : ι → F} {ms : Fin n → ι → F} {folds : ℕ → ι → F}
    {k : Fin n} (hγ0 : γs (k : ℕ) ≠ 0)
    (hms : ms k ∈ reedSolomonCode dom d)
    (hfolds : ∀ c : ℕ, c ≤ n → folds c = partialFold γs f₀ ms c) :
    subUdSeamCounterfactual dom d δ γs γalt (flatFold γs f₀ ms) folds k
      = flatFold (updSched γs γalt k) f₀ ms := by
  unfold subUdSeamCounterfactual
  rw [hfolds _ k.isLt, hfolds _ (le_of_lt k.isLt),
    seam_increment γs f₀ ms k hγ0, subUdRecover_codeword dom hδ0 hδUD hms,
    flatFold_updSched]

/-- **The chain extraction through the sub-UD seam** — the mirror of
`extractChain_seamCounterfactual` with NO column hypothesis: the chain
extractor fed the sub-UD-synthesized family returns the full (masked)
witness list exactly, `extractChain_flatFold` (CITED — the
regime-independent shape `[ZK-RBR-extract]` promised carries over verbatim)
closing the composition. The seam that needed `t ≥ d` opened columns now
needs ZERO columns — it needs the fold words the roots bind, which is where
the residual's attribution seam lives. -/
theorem extractChain_subUdSeam [Nonempty ι] (dom : ι ↪ F) {d : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδUD : δ < (1 - ((d : ℝ) - 1) / (Fintype.card ι : ℝ)) / 2)
    {γs γalt : ℕ → F} {f₀ : ι → F} {ms : Fin n → ι → F} {folds : ℕ → ι → F}
    (hne : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hfolds : ∀ c : ℕ, c ≤ n → folds c = partialFold γs f₀ ms c) :
    extractChain γs γalt (flatFold γs f₀ ms)
        (subUdSeamCounterfactual (n := n) dom d δ γs γalt
          (flatFold γs f₀ ms) folds)
      = List.ofFn ms := by
  have h : subUdSeamCounterfactual (n := n) dom d δ γs γalt
        (flatFold γs f₀ ms) folds
      = fun k : Fin n => flatFold (updSched γs γalt k) f₀ ms :=
    funext fun k =>
      subUdSeamCounterfactual_sound dom hδ0 hδUD (hγ0 k) (hms k) hfolds
  rw [h, extractChain_flatFold hne f₀ ms]

end Seam

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Three sites: the landed `RS[F₅, {0,1,2,3}, 2]` (`t = 1 < d = 2`, the
constrained-mask hiding window), the full-rate `RS[F₅, {0,1,2,3}, 4]`
(`hPG` genuinely inhabited via `isProximityGenerator_top`, the family
theorem fired END TO END), and a fresh `RS[F₁₁, {0..7}, 2]` where a
genuinely corrupted committed word is CORRECTED. -/

namespace SubUdSeamExample

open RSExample ErasureExample

/-! ### Satisfiable: recovery at `t`-free `d = 2`, inside the hiding window -/

/-- The sub-UD decoder recovers `xWord` at `δ = 1/4 < dC/2 = 3/8` — no
columns consumed at all; compare `recoverFromColumns`' junk at `t = 1`. -/
theorem subud_recover_xWord :
    subUdRecover dom₅ 2 (1/4 : ℝ) xWord = xWord :=
  subUdRecover_codeword dom₅ (by norm_num)
    (by norm_num [Fintype.card_fin]) xWord_mem

/-- Same for `twoXWord` — the OTHER word of the `t = 1` ambiguity pair. -/
theorem subud_recover_twoXWord :
    subUdRecover dom₅ 2 (1/4 : ℝ) twoXWord = twoXWord :=
  subUdRecover_codeword dom₅ (by norm_num)
    (by norm_num [Fintype.card_fin]) twoXWord_mem

/-- The old route is JUNK exactly where the new one recovers: at `t = 1 < d`
`recoverFromColumns` returns `0` (landed
`recoverFromColumns_junk_outside_regime`, CITED) while `subUdRecover`
returns the word. -/
theorem old_route_junk_new_route_recovers :
    recoverFromColumns dom₅ 2 opened₁ (fun j => xWord (opened₁ j)) = 0 ∧
      xWord ≠ 0 ∧ subUdRecover dom₅ 2 (1/4 : ℝ) xWord = xWord :=
  ⟨recoverFromColumns_junk_outside_regime, xWord_ne_zero,
    subud_recover_xWord⟩

/-- **The `t`-window conflict of lemma A, DISSOLVED at this resolution**: at
`t = 1 < d = 2` — inside the constrained-mask hiding window `t + r ≤ d` that
`not_constrainedMask_hiding_of_recoverable` proved DISJOINT from the column
seam's `d ≤ t` — hiding HOLDS (landed `window_F5`, CITED) and the increment
is recovered anyway. Hiding and recovery share `t = 1` because recovery no
longer consumes `t`. -/
theorem subud_hiding_coexist_F5 :
    MaskedOpeningHiding
        (constrainedMaskSpace dom₅ 2 ZkArgumentExample.pt2)
        ZkArgumentExample.qz (1 : ZMod 5) ∧
      subUdRecover dom₅ 2 (1/4 : ℝ) xWord = xWord :=
  ⟨ZkExtractionExample.window_F5.1, subud_recover_xWord⟩

/-! ### Teeth: the single fold's columns are ambiguous; the family pins -/

/-- The ambiguity pair's opened symbols coincide at `t = 1` — the landed
`recoverFromColumns_teeth` data in `openSymbols` form. -/
theorem cols_eq : openSymbols opened₁ xWord = openSymbols opened₁ twoXWord := by
  funext j
  simp only [openSymbols_apply]
  fin_cases j
  decide

/-- **Single fold ambiguous, family pins — computed.** The two distinct
codeword increments produce IDENTICAL fold columns for EVERY previous fold,
EVERY challenge, at `t = 1 < d = 2` — while `subUdRecover` (consuming the
word the root binds, not the columns) returns each increment exactly. The
correlation is load-bearing at word resolution and invisible at column
resolution. -/
theorem family_pins_where_columns_cannot :
    (∀ (f₀ : Fin 4 → ZMod 5) (ρ : ZMod 5) (j : Fin 1),
        foldFamily f₀ xWord ρ (opened₁ j)
          = foldFamily f₀ twoXWord ρ (opened₁ j)) ∧
      subUdRecover dom₅ 2 (1/4 : ℝ) xWord = xWord ∧
      subUdRecover dom₅ 2 (1/4 : ℝ) twoXWord = twoXWord ∧
      xWord ≠ twoXWord :=
  ⟨fun f₀ ρ j => foldFamily_columns_ambiguous cols_eq f₀ ρ j,
    subud_recover_xWord, subud_recover_twoXWord, xWord_ne_twoXWord⟩

/-- The quantified teeth, fired: EVERY column extractor — fed the whole
challenge-indexed table — that recovers `xWord` fails on `twoXWord`. -/
theorem single_fold_ambiguous_F5 (f₀ : Fin 4 → ZMod 5)
    (rec : (ZMod 5 → Fin 1 → ZMod 5) → Fin 4 → ZMod 5)
    (hrec : rec (fun ρ j => foldFamily f₀ xWord ρ (opened₁ j)) = xWord) :
    rec (fun ρ j => foldFamily f₀ twoXWord ρ (opened₁ j)) ≠ twoXWord :=
  no_column_extractor cols_eq xWord_ne_twoXWord f₀ rec hrec

/-! ### Teeth: the UD radius is load-bearing — the `[SUBUD-johnson]` frontier -/

/-- The near-corner word: `1` at position `1`, `0` elsewhere. -/
def e₁ : Fin 4 → ZMod 5 := fun i => if i = 1 then 1 else 0

/-- **Beyond the UD radius the agreement pin genuinely fails**: at
`δ = 1/2 > dC/2 = 3/8`, TWO distinct codewords each hold a
`(1 − δ)`-agreement set with `e₁` — the choice `subUdRecover` makes there is
unforced, and forcing it is exactly `[SUBUD-johnson]`. Computed premise
inhabitation for the residual, mirroring `recoverFromColumns_teeth`'s role
for the column seam. -/
theorem beyond_ud_list_ambiguous :
    ((0 : Fin 4 → ZMod 5) ∈ reedSolomonCode dom₅ 2 ∧
      xWord ∈ reedSolomonCode dom₅ 2 ∧ (0 : Fin 4 → ZMod 5) ≠ xWord) ∧
    (((1 : ℝ) - 1/2) * (Fintype.card (Fin 4) : ℝ)
        ≤ ((({0, 2, 3} : Finset (Fin 4))).card : ℝ) ∧
      AgreesOn ({0, 2, 3} : Finset (Fin 4)) e₁ 0) ∧
    (((1 : ℝ) - 1/2) * (Fintype.card (Fin 4) : ℝ)
        ≤ ((({0, 1} : Finset (Fin 4))).card : ℝ) ∧
      AgreesOn ({0, 1} : Finset (Fin 4)) e₁ xWord) := by
  refine ⟨⟨Submodule.zero_mem _, xWord_mem, by decide⟩,
    ⟨?_, by unfold AgreesOn; decide⟩, ⟨?_, by unfold AgreesOn; decide⟩⟩
  · rw [show (({0, 2, 3} : Finset (Fin 4))).card = 3 from by decide]
    norm_num [Fintype.card_fin]
  · rw [show (({0, 1} : Finset (Fin 4))).card = 2 from by decide]
    norm_num [Fintype.card_fin]

/-- The sharp boundary, displayed: `δ = 1/2` violates the UD premise
`δ < 3/8` that `subUdRecover_sound` charges. -/
example : ¬ ((1/2 : ℝ) < (1 - ((2 : ℝ) - 1) / (4 : ℝ)) / 2) := by norm_num

/-! ### The family theorem fired END TO END: the full-rate `hPG` site -/

/-- Full rate `d = 4 = n`: the RS code is everything (landed
`reedSolomonCode_card_eq_top`, CITED) — the genuine
`IsProximityGenerator` inhabitation site, exactly as
`Selvage/ReedSolomon.lean`'s keystones use it. -/
theorem rs_top : reedSolomonCode dom₅ 4 = ⊤ := by
  have h := reedSolomonCode_card_eq_top dom₅
  rwa [Fintype.card_fin] at h

/-- **`subUdRecover_of_foldFamily` fired with EVERY hypothesis discharged**:
genuine proximity generator (`isProximityGenerator_top` through `rs_top`),
closeness probability `1 > 0 = err` (`pr_one`), δ-interval inhabited
(`1/10 < dC/2 = 1/8`), and the conclusion delivers the mutual agreement
set with the previous fold corrected on the same set and the family
reproduced at every challenge. Increment `xWord`, previous fold
`twoXWord`. -/
theorem subud_family_fires :
    subUdRecover dom₅ 4 (1/10 : ℝ) xWord ∈ reedSolomonCode dom₅ 4 ∧
      ∃ S : Finset (Fin 4),
        (1 - (1/10 : ℝ)) * (Fintype.card (Fin 4) : ℝ) ≤ (S.card : ℝ) ∧
        AgreesOn S xWord (subUdRecover dom₅ 4 (1/10 : ℝ) xWord) ∧
        ∃ u₀ ∈ reedSolomonCode dom₅ 4, AgreesOn S twoXWord u₀ ∧
          ∀ ρ : ZMod 5, AgreesOn S (foldFamily twoXWord xWord ρ)
            (foldFamily u₀ (subUdRecover dom₅ 4 (1/10 : ℝ) xWord) ρ) := by
  refine subUdRecover_of_foldFamily (B := 0) (err := fun _ => 0) ?_
    (by norm_num) (by norm_num) (by norm_num [Fintype.card_fin]) ?_
  · rw [rs_top]
    exact isProximityGenerator_top _
  · have hall : ∀ r : Fin 2 → ZMod 5,
        close (1/10 : ℝ) (reedSolomonCode dom₅ 4)
          (comb r ![twoXWord, xWord]) := fun r =>
      ⟨comb r ![twoXWord, xWord], by rw [rs_top]; exact Submodule.mem_top,
        by rw [relDist, hammingDist_self]; norm_num⟩
    rw [ProximityGenerator.pr_one _ hall]
    norm_num

/-- The fired site's recovery is EXACT — the pinned codeword is the
committed increment itself. -/
theorem subud_family_recover_exact :
    subUdRecover dom₅ 4 (1/10 : ℝ) xWord = xWord :=
  subUdRecover_codeword dom₅ (by norm_num) (by norm_num [Fintype.card_fin])
    (by rw [rs_top]; exact Submodule.mem_top)

/-! ### The seam extraction fired at depth 2 — no column hypothesis -/

open ZkExtractionExample AccExtractChainExample in
/-- **The sub-UD seam extraction, fired on the landed masked family**: the
whole masked witness list `msEx` extracted from the base transcript plus the
recommitted fold WORDS — `subUdSeamCounterfactual` synthesizing every
perturbed transcript with NO opened column, NO `qPair`, NO `d ≤ t` anywhere
(compare the landed `seam_extraction_F5`, which consumed columns at
`t = d = 2`). Same chain, same schedules, same output. -/
theorem subud_seam_extraction_F5 :
    extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (subUdSeamCounterfactual (n := 2) dom₅ 2 (1/4 : ℝ) γbase γalt₂
          (flatFold γbase xWord msEx) (partialFold γbase xWord msEx))
      = List.ofFn msEx :=
  extractChain_subUdSeam dom₅ (by norm_num) (by norm_num [Fintype.card_fin])
    (by decide) (by decide) msEx_mem (fun _ _ => rfl)

/-! ### The adversarial site: a corrupted commitment, CORRECTED

`RS[F₁₁, {0..7}, 2]`, `n = 8`: large enough that the `2δ`-window admits a
genuine corruption (`n = 4` quantizes it away — at `δ < 3/16`, a
`(1 − δ)`-set is everything). -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The evaluation domain `{0,…,7} ⊂ F₁₁`. -/
def dom₁₁ : Fin 8 ↪ ZMod 11 := ⟨fun i => (i.val : ZMod 11), by decide⟩

/-- The true increment: evaluations of `X`. -/
def xWord₁₁ : Fin 8 → ZMod 11 := fun i => (i.val : ZMod 11)

theorem xWord₁₁_mem : xWord₁₁ ∈ reedSolomonCode dom₁₁ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.X, by rw [Polynomial.degree_X]; decide,
      fun i => by simp [xWord₁₁, dom₁₁]⟩

/-- The corrupted previous-fold commitment: honest word `0` with coordinate
`7` flipped to `1`. -/
def cPrevBad : Fin 8 → ZMod 11 := fun i => if i = 7 then 1 else 0

/-- The coordinates where the corrupted commitment is honest. -/
def okSet : Finset (Fin 8) := Finset.univ.filter (· ≠ 7)

/-- **Corruption corrected**: previous fold committed with one flipped
coordinate (a genuinely non-codeword data surface, next theorem), challenge
`γ = 1`, honest next fold — the root-bound increment `xWord₁₁ − cPrevBad` is
wrong at position `7`, yet `subUdRecover` at radius `2δ = 1/4 < dC/2 = 7/16`
returns the TRUE increment codeword exactly. `recoverFromColumns` has no
counterpart to this at ANY `t` (next theorem but one). -/
theorem corrupted_increment_recovered :
    subUdRecover dom₁₁ 2 (2 * (1/8) : ℝ) (xWord₁₁ - cPrevBad) = xWord₁₁ := by
  have hS₁ : ((1 : ℝ) - 1/8) * (Fintype.card (Fin 8) : ℝ)
      ≤ ((Finset.univ : Finset (Fin 8)).card : ℝ) := by
    norm_num [Finset.card_univ, Fintype.card_fin]
  have hS₂ : ((1 : ℝ) - 1/8) * (Fintype.card (Fin 8) : ℝ)
      ≤ (okSet.card : ℝ) := by
    rw [show okSet.card = 7 from by decide]
    norm_num [Fintype.card_fin]
  have hnext : AgreesOn Finset.univ xWord₁₁
      ((0 : Fin 8 → ZMod 11) + (1 : ZMod 11) • xWord₁₁) := by
    unfold AgreesOn; decide
  have hprev : AgreesOn okSet cPrevBad (0 : Fin 8 → ZMod 11) := by
    unfold AgreesOn; decide
  have h := subUdRecover_increment (δ := (1/8 : ℝ)) dom₁₁
    (by norm_num [Fintype.card_fin]) one_ne_zero xWord₁₁_mem hS₁ hS₂
    hnext hprev
  rwa [inv_one, one_smul] at h

/-- The correction is genuine: input and output differ. -/
theorem corrupted_increment_ne : xWord₁₁ - cPrevBad ≠ xWord₁₁ := by decide

/-- The corrupted increment is genuinely OUTSIDE the code — were it a
codeword, `subUdRecover_codeword` would return it, contradicting the
recovery. The decoder DECODED, it did not copy. -/
theorem corrupted_increment_not_code :
    xWord₁₁ - cPrevBad ∉ reedSolomonCode dom₁₁ 2 := by
  intro hmem
  have h := subUdRecover_codeword (δ := (2 * (1/8) : ℝ)) dom₁₁ (by norm_num)
    (by norm_num [Fintype.card_fin]) hmem
  rw [corrupted_increment_recovered] at h
  exact corrupted_increment_ne h.symm

/-- The `t = d` opening pair `(6, 7)` — position `7` is the corrupted one. -/
def openedPair₁₁ : Fin 2 → Fin 8 := ![6, 7]

theorem openedPair₁₁_inj : Function.Injective (dom₁₁ ∘ openedPair₁₁) := by
  decide

/-- The constant-`6` codeword — what the corrupted columns interpolate to. -/
def sixWord : Fin 8 → ZMod 11 := fun _ => 6

theorem sixWord_mem : sixWord ∈ reedSolomonCode dom₁₁ 2 :=
  mem_reedSolomonCode_iff.mpr
    ⟨Polynomial.C 6,
      by rw [Polynomial.degree_C (by decide : (6 : ZMod 11) ≠ 0)]; decide,
      fun i => by simp [sixWord]⟩

/-- **The resolution contrast, computed**: fed `t = d` columns of the
corrupted increment at positions `(6, 7)` — values `(6, 6)` — the column
decoder confidently returns the WRONG codeword (the constant `6`;
`recoverFromColumns_sound` fired on the codeword those columns DO belong
to), because column resolution cannot express that a coordinate is
corrupted. `subUdRecover` at word resolution corrects it
(`corrupted_increment_recovered`). Not a defect of the landed decoder — its
soundness premise (genuine codeword) is violated here — but the exact
measurement of what the sub-UD seam buys. -/
theorem old_route_decodes_wrong_on_corruption :
    recoverFromColumns dom₁₁ 2 openedPair₁₁
        (fun j => (xWord₁₁ - cPrevBad) (openedPair₁₁ j)) = sixWord ∧
      sixWord ≠ xWord₁₁ :=
  ⟨recoverFromColumns_sound dom₁₁ (by norm_num) openedPair₁₁_inj sixWord_mem
      (fun j => by fin_cases j <;> decide),
    by decide⟩

end SubUdSeamExample

/-! ## Residual obligation — prose, not a stub

**`[SUBUD-johnson]`** — what remains of `[ZK-RBR-extract]` open lemma A
after this file. The lemma as posed is RESOLVED-BY-SPLIT: its column form
("extend `recoverFromColumns` to `t < d`") is REFUTED at full quantifier
strength (`no_column_extractor` — no function of the family's opened
columns, even the entire challenge-indexed table, recovers the increment),
and its mutual-CA form is BUILT and PROVED at the unique-decoding radius:
the family event pins the increment codeword
(`subUdRecover_of_foldFamily`, `subUdRecover_of_seed`), corruption within
the `2δ`-window is corrected (`subUdRecover_increment`), and the whole
chain extraction runs through the column-free seam
(`extractChain_subUdSeam`), restoring coexistence with constrained-mask
hiding at `t + r ≤ d` (`subud_hiding_coexist_F5`) — the incompatibility
that DEFINED lemma A does not exist at word resolution. What remains is
four named parts, none absorbed:

* **(i) The proximity-generator realizer** — the standing `hPG`
  hypothesis: `IsProximityGenerator (affineGenerator F) (RS[dom, d]) B err`
  with proven parameters. In the UD regime (`δ < dC/2`, all this file
  invokes) the literature bound is BCIKS 2020/654 Thm 1.2's unique-decoding
  case (`err = n/|F|` shape) — PROVABLE future work, the near-term target;
  it slots into `hPG` with zero re-derivation and makes
  `subud_family_fires`'s pattern available at macroscopic rate. The
  Johnson-regime realizer (`B = √ρ`) is WHIR Thm 4.8 / BCIKS Thm 1.2 —
  harder, inherited unchanged from `Selvage/ReedSolomon.lean`'s keystone TODO.
* **(ii) Mutual CA beyond the UD radius.** The landed Lemma 4.10 upgrade
  caps the mutual-CA bound at `B⋆ = max (1 − dC/2) B` — its proof is
  intrinsically unique-decoding. For `δ ∈ (dC/2, 1 − √ρ)` mutual CA is
  the territory historically named WHIR Conjecture 4.12. The relevant
  RS/polynomial-generator Johnson instance is now literature-PROVED
  (2025/2051 and 2025/2110, with related proximity consequences in
  2025/2055), but those arguments are not formalized here. This file
  consumes nothing from them: every theorem here prices its radius inside
  `(0, min {dC/2, 1 − B})`. The stronger capacity-level conjecture family
  is false (2025/2046), so Johnson is the positive boundary being cited.
* **(iii) The list pin beyond `dC/2`.** `subUdRecover_sound`'s singleton
  pin (via `codeword_eq_of_close_of_close`) becomes a LIST pin: for
  `δ ≤ 1 − √ρ − η` the qualifying-codeword count is Johnson-bounded
  (≤ `1/(2η√ρ)`), and selecting the intended element is exactly the landed
  prose seam `[OOD-pin-proximity]` (`Selvage/OutOfDomain.lean`) — an
  out-of-domain evaluation pins the list member.
  `beyond_ud_list_ambiguous` is the computed witness that the selection
  problem is real at `δ > dC/2`.
* **(iv) The sampling bridge.** `hobs` — the closeness EVENT's probability
  — must be discharged from the deployed `t`-column spot checks: a fold
  δ-far from every codeword survives one uniform column with probability
  ≤ `1 − δ`, so `t` columns leave the event's complement mass
  ≤ `(1 − δ)^t` per fold; `card_compl_le_of_agreement` is the agreement-set
  side of that computation. `t` enters the sub-UD seam HERE — as soundness
  amplification only — and this is the honest boundary of
  `subUdSeamCounterfactual`'s word-resolution input: the fold words enter
  via what the roots bind (ideal binding, `Selvage/Commitment.lean`), and the
  adversarial gap between "root-bound word" and "δ-close corrected word"
  is priced by (iv) + the lagged-root attribution already named in
  `[ACC-rbr-bcs-resid]`(a).

**What is NOT at risk.** Every citation is a landed unconditional theorem:
`codeword_eq_of_close_of_close`, `relDist_le_of_agreesOn`,
`reedSolomonCode_minDist`, `reedSolomonCode_hasMutualCorrelatedAgreement`
(given `hPG`), `comb_affineGenerator`, `isProximityGenerator_top`,
`reedSolomonCode_card_eq_top`, `partialFold_succ`, `flatFold_updSched`,
`extractChain_flatFold`, `extractPair_snd`,
`recoverFromColumns_junk_outside_regime`, `recoverFromColumns_sound`,
`window_F5`. The negative results here (`single_fold_word_ambiguous`,
`foldFamily_columns_ambiguous`, `no_column_extractor`,
`beyond_ud_list_ambiguous`) are proofs, not conjectures.

**Honest assessment of the seam.** CLOSED at this file's resolution: the
recovery theory at the UD radius — the diagnosis (columns can never carry
it), the mechanism (mutual CA over the challenge family), the decoder with
exactness on codewords and correction within `2δ`, the full chain
extraction, and the hiding coexistence that lemma A's conflict said was
impossible. OPEN LOCALLY: realizing `hPG` (provable, UD case), the sampling
bridge
from `t`-column checks to the closeness event (provable, quantitative),
the root-to-word attribution in the deployed BCS game (inherited,
`[ACC-rbr-bcs-resid]`(a)), and the radius extension past `dC/2` (rides the
locally unformalized, literature-proved RS Johnson MCA result through the
historical `WHIRConjecture412` interface + `[OOD-pin-proximity]`). The first two
are the load-bearing remainder for deploying the constrained-mask seam;
neither touches the shapes landed here.

## Ledger

* `ProximityGenerator.pr_one` — PROVED: the certain event has probability 1.
* `foldFamily` (+ `_apply`, `_eq_comb`) — DEFINED/PROVED: the correlated
  fold family; IS the affine generator's combination on `![f₀, g]`.
* `single_fold_word_ambiguous` / `extractPair_foldFamily` /
  `foldFamily_columns_ambiguous` / `no_column_extractor` — PROVED: the
  recovery ladder's rungs 1–3 — one fold word pins nothing, two exact
  words pin completely (landed `extractPair` cited), `t < d` columns of
  the WHOLE family pin nothing against ANY extractor.
* `subUdRecover` (+ `_mem`, `_sound`, `_codeword`) — DEFINED/PROVED: the
  word-resolution sub-UD decoder; always a codeword; pins UNIQUELY below
  `dC/2` (landed unique decoding cited); exact on codewords.
* `foldFamily_correlatedAgreement` / `foldFamily_mutualCA` /
  `subUdRecover_of_seed` — PROVED: the mutual-CA step on the seam's own
  object — common agreement set for (previous fold, increment); the landed
  WHIR 4.10/4.11 cited verbatim; per non-failing seed the observed
  agreement set is the recovery's.
* `subUdRecover_of_foldFamily` — PROVED: the composed sub-UD recovery —
  family event ⇒ increment pinned on a mutual agreement set carrying the
  previous fold's simultaneous correction and reproducing the committed
  family at every challenge.
* `card_compl_le_of_agreement` / `card_inter_agreement` /
  `increment_agreesOn` / `subUdRecover_increment` — PROVED: the
  off-agreement mass bound; two `(1−δ)`-sets meet in a `(1−2δ)`-set; the
  corrupted-fold increment agrees there; recovery EXACT at radius `2δ`.
* `partialFold_foldFamily` / `seam_increment` / `subUdSeamCounterfactual`
  (+ `_sound`) / `extractChain_subUdSeam` — DEFINED/PROVED: the seam at
  word resolution — `seamCounterfactual` with fold words for columns and
  `subUdRecover` for `recoverFromColumns`; chain extraction end to end
  with NO `d ≤ t` anywhere.
* Keystones — `subud_recover_xWord`, `subud_recover_twoXWord`,
  `old_route_junk_new_route_recovers`, `subud_hiding_coexist_F5`,
  `cols_eq`, `family_pins_where_columns_cannot`,
  `single_fold_ambiguous_F5`, `beyond_ud_list_ambiguous`, `rs_top`,
  `subud_family_fires`, `subud_family_recover_exact`,
  `subud_seam_extraction_F5`, `corrupted_increment_recovered`,
  `corrupted_increment_ne`, `corrupted_increment_not_code`,
  `old_route_decodes_wrong_on_corruption` — fired/computed on
  `RS[F₅,·,2]`, `RS[F₅,·,4]` (genuine `hPG`), and `RS[F₁₁,·,2]`
  (genuine corruption corrected).
* Residual — `[SUBUD-johnson]` (prose above): (i) the `hPG` realizer
  (UD case provable), (ii) mutual CA past `dC/2` (WHIR Conj. 4.12,
  historical LOCAL hypothesis; RS/polynomial-generator Johnson instance
  literature-proved but unformalized here), (iii) the Johnson list pin +
  `[OOD-pin-proximity]`
  selection, (iv) the `t`-column sampling bridge + root attribution
  (`[ACC-rbr-bcs-resid]`(a) inherited).

`#print axioms` on `subUdRecover_of_foldFamily`, `subUdRecover_of_seed`,
`subUdRecover_increment`, `extractChain_subUdSeam`, `foldFamily_mutualCA`,
`SubUdSeamExample.subud_family_fires`,
`SubUdSeamExample.subud_hiding_coexist_F5`,
`SubUdSeamExample.subud_seam_extraction_F5`,
`SubUdSeamExample.corrupted_increment_recovered`,
`SubUdSeamExample.corrupted_increment_not_code`,
`SubUdSeamExample.single_fold_ambiguous_F5`,
`SubUdSeamExample.old_route_decodes_wrong_on_corruption`,
`SubUdSeamExample.beyond_ud_list_ambiguous`,
`SubUdSeamExample.family_pins_where_columns_cannot`:
`propext`, `Classical.choice`, `Quot.sound` (`no_column_extractor` even
choice-free: `propext`, `Quot.sound`) — no `sorryAx` anywhere in the
file. -/

end Minidregg.Selvage
