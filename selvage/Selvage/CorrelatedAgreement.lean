/-
# Selvage.CorrelatedAgreement — OB-6, the v0 floor realizer.

**Mutual correlated agreement at the unique-decoding radius is unconditional for
every linear code** — WHIR (eprint 2024/1586) §4.2: Definition 4.7 (proximity
generator), Definition 4.9 (mutual correlated agreement), Lemma 4.10 (in the
unique-decoding regime every proximity generator has mutual correlated agreement
with the *same* error). This is THE load-bearing property of Selvage's link layer
(docs/SELVAGE-RECOMPOSITION.md §1: plain proximity gaps do not relate input
agreement sets to the output's — WARP fn. 6) and the v0 parameter rung (§5: the
UD regime is unconditional end-to-end).

**Transcription notes (read before auditing):**

* **`max`, not `min`.** WHIR Lemma 4.10 as printed says
  `B⋆(C,ℓ) = min{1 − δ_C/2, B(C,ℓ)}`. That is a typo for **max**: (a) the
  admissible-radius interval is `δ ∈ (0, 1 − B⋆)`, and the proof uses BOTH
  `δ < δ_C/2` (uniqueness of the nearby codeword) and `δ < 1 − B` (each
  invocation of Def 4.7), forcing `1 − B⋆ = min{δ_C/2, 1 − B}`, i.e.
  `B⋆ = max{1 − δ_C/2, B}`; (b) Corollary 4.11 instantiates RS with
  `B = √ρ`, `δ_C = 1 − ρ` and reports `B⋆ = (1+ρ)/2 = max{(1+ρ)/2, √ρ}`
  (AM–GM), whereas the printed min would give `√ρ`. We formalize the max.

* **Error monotonicity + nonnegativity are made explicit.** The paper's proof
  re-invokes Def 4.7 at a *smaller* radius than δ with the same threshold
  ("which we can do since 1 − |T|/n ≤ δ"), silently using that `err` does not
  increase when the radius shrinks; and a mutual-CA error below 0 is
  unsatisfiable (probabilities are ≥ 0). Both facts hold for every
  instantiation in the paper (Theorem 4.8's `err` is nondecreasing in δ and
  nonnegative); here they are honest hypotheses `herr_mono` / `herr_nonneg`.

* **Probability model.** A proximity generator is a finitely-supported
  distribution: a finite seed type with real weights (nonnegative, summing
  to 1), the event probability being the weight of the preimage. This covers
  every generator the papers use (uniform α ← F with powers `(1, α, …)`,
  uniform r ← F for PG(2)). Nothing in Lemma 4.10 is probabilistic beyond
  monotonicity of the measure under event inclusion, so the full statement is
  PROVED here — no deterministic-core/probabilistic-wrapper split was needed.

* **`∆(f, C) ≤ δ` as `∃ u ∈ C, ∆(f,u) ≤ δ`** (`close`): equivalent to the
  paper's min-based reading for every nonempty code (relative distance takes
  finitely many values, so the min over the — possibly infinite — code is
  attained); a submodule always contains 0, hence is nonempty.

* **Nontriviality.** `[Nonempty ι]` excludes the empty evaluation domain
  (relative distance would be 0/0). The theorem is honestly quantified: its
  δ-interval `(0, 1 − B⋆)` is nonempty iff `dC > 0` and `B < 1`; the keystone
  section at the bottom exhibits premise inhabitation (`minDistLB_inhabited`),
  a satisfiability witness where the Def 4.7 hypothesis *fires* non-vacuously
  (`isProximityGenerator_top`), and an end-to-end instantiation with a
  nonempty δ-interval (`hasMutualCorrelatedAgreement_top_affine` + the
  interval-nonemptiness `example`).
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace Minidregg.Selvage

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]
variable {ℓ : ℕ}

/-! ## Relative Hamming distance and δ-balls (WHIR §2 "∆", §3.2) -/

/-- Relative (fractional) Hamming distance between two words of `F^ι`
(WHIR §2: "∆(f, g) is the fractional Hamming distance"). Built on Mathlib's
`hammingDist`; division by `Fintype.card ι` in ℝ. -/
noncomputable def relDist (f g : ι → F) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card ι : ℝ)

omit [DecidableEq ι] [Field F] in
theorem relDist_comm (f g : ι → F) : relDist f g = relDist g f := by
  rw [relDist, relDist, hammingDist_comm]

omit [DecidableEq ι] [Field F] in
/-- Triangle inequality for the relative Hamming distance. -/
theorem relDist_triangle [Nonempty ι] (f g h : ι → F) :
    relDist f h ≤ relDist f g + relDist g h := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (hammingDist f h : ℝ) ≤ (hammingDist f g : ℝ) + (hammingDist g h : ℝ) := by
    exact_mod_cast hammingDist_triangle f g h
  have key : (hammingDist f g : ℝ) / (Fintype.card ι : ℝ)
        + (hammingDist g h : ℝ) / (Fintype.card ι : ℝ)
      = ((hammingDist f g : ℝ) + (hammingDist g h : ℝ)) / (Fintype.card ι : ℝ) := by
    ring
  rw [relDist, relDist, relDist, key, div_le_div_iff_of_pos_right hn]
  exact hd

omit [DecidableEq ι] [Field F] in
/-- Distinct words are at relative distance at least `1/n` — the quantization
floor. Doubles as premise inhabitation for the minimum-distance hypothesis of
the main theorem (see `minDistLB_inhabited`). -/
theorem one_div_card_le_relDist [Nonempty ι] {u v : ι → F} (h : u ≠ v) :
    1 / (Fintype.card ι : ℝ) ≤ relDist u v := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (1 : ℝ) ≤ (hammingDist u v : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hammingDist_ne_zero.mpr h)
  rw [relDist, div_le_div_iff_of_pos_right hn]
  exact hd

/-- `close δ C f`: membership of `f` in the δ-ball around the linear code `C`,
i.e. `∆(f, C) ≤ δ` read existentially (equivalent to the min-based reading for
any nonempty code; a submodule contains 0). -/
def close (δ : ℝ) (C : Submodule F (ι → F)) (f : ι → F) : Prop :=
  ∃ u ∈ C, relDist f u ≤ δ

/-! ## Agreement sets (WHIR §4.2, the sets `S` with `f(S) = u(S)`) -/

/-- `AgreesOn S f u`: `f` and `u` coincide on every coordinate of `S`
(the paper's `f(S) = u(S)`). -/
def AgreesOn (S : Finset ι) (f u : ι → F) : Prop :=
  ∀ x ∈ S, f x = u x

omit [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F] in
theorem AgreesOn.mono {S T : Finset ι} {f u : ι → F} (hST : S ⊆ T)
    (h : AgreesOn T f u) : AgreesOn S f u :=
  fun x hx => h x (hST hx)

omit [Field F] in
/-- Agreement on `S` bounds the Hamming distance by the complement:
`d(f,u) + |S| ≤ n`. (Stated addition-side to avoid ℕ-subtraction.) -/
theorem hammingDist_add_card_le_of_agreesOn {S : Finset ι} {f u : ι → F}
    (h : AgreesOn S f u) :
    hammingDist f u + S.card ≤ Fintype.card ι := by
  classical
  have hdisj : Disjoint (Finset.univ.filter fun x => f x ≠ u x) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    exact (Finset.mem_filter.mp hx).2 (h x hxS)
  have hcard : hammingDist f u = (Finset.univ.filter fun x => f x ≠ u x).card := by
    simp [hammingDist]
  calc hammingDist f u + S.card
      = ((Finset.univ.filter fun x => f x ≠ u x) ∪ S).card := by
        rw [hcard, Finset.card_union_of_disjoint hdisj]
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ι := Finset.card_univ

omit [Field F] in
/-- Agreement on a set of at least `(1−δ)·n` coordinates puts the pair within
relative distance δ — the bridge from agreement sets to δ-balls. -/
theorem relDist_le_of_agreesOn [Nonempty ι] {S : Finset ι} {f u : ι → F} {δ : ℝ}
    (h : AgreesOn S f u) (hS : (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ)) :
    relDist f u ≤ δ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (hammingDist f u : ℝ) + (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hammingDist_add_card_le_of_agreesOn h
  rw [relDist, div_le_iff₀ hn]
  nlinarith

/-! ## Unique decoding -/

omit [DecidableEq ι] in
/-- **Unique decoding.** If `dC` lower-bounds the pairwise relative distance of
distinct codewords (i.e. `dC ≤ δ(C)`), then two codewords within `δ < dC/2` of
a common word coincide — triangle inequality on the code distance. This is the
whole mechanism behind WHIR Lemma 4.10's "|Λ(C, g, δ)| ≤ 1". -/
theorem codeword_eq_of_close_of_close [Nonempty ι] {C : Submodule F (ι → F)}
    {dC δ : ℝ} (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    {u v g : ι → F} (hu : u ∈ C) (hv : v ∈ C) (hδ : δ < dC / 2)
    (hgu : relDist g u ≤ δ) (hgv : relDist g v ≤ δ) : u = v := by
  by_contra hne
  have h1 : dC ≤ relDist u v := hdC u hu v hv hne
  have h2 : relDist u v ≤ relDist u g + relDist g v := relDist_triangle u g v
  have h3 : relDist u g = relDist g u := relDist_comm u g
  linarith

/-! ## Proximity generators (WHIR Definition 4.7) -/

/-- Random linear-combination coefficients applied to a tuple of functions:
`comb r f = ∑ⱼ rⱼ · fⱼ` (the paper's `∑_{i∈[ℓ]} rᵢ · fᵢ`). -/
def comb (r : Fin ℓ → F) (f : Fin ℓ → ι → F) : ι → F :=
  fun x => ∑ j, r j * f j x

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem comb_mem {C : Submodule F (ι → F)} (r : Fin ℓ → F) {u : Fin ℓ → ι → F}
    (hu : ∀ j, u j ∈ C) : comb r u ∈ C := by
  have h : comb r u = ∑ j, r j • u j := by
    funext x
    simp [comb]
  rw [h]
  exact Submodule.sum_mem C fun j _ => Submodule.smul_mem C _ (hu j)

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem comb_agreesOn {S : Finset ι} {r : Fin ℓ → F} {f u : Fin ℓ → ι → F}
    (h : ∀ j, AgreesOn S (f j) (u j)) : AgreesOn S (comb r f) (comb r u) := by
  intro x hx
  exact Finset.sum_congr rfl fun j _ => by rw [h j x hx]

/-- A sampler of ℓ-tuples of combination coefficients: a finitely-supported
distribution presented as a finite seed type with nonnegative real weights
summing to 1 (covers WHIR's `Gen(ℓ; α) = (1, α, …, α^{ℓ−1})` with uniform
`α ← F`, and PG(2) below). The distribution half of WHIR Definition 4.7; the
proximity-gap property is the separate `Prop` `IsProximityGenerator`. -/
structure ProximityGenerator (F : Type*) (ℓ : ℕ) where
  /-- The seed / sample space. -/
  Seed : Type*
  [seedFintype : Fintype Seed]
  /-- The tuple of combination coefficients drawn from a seed. -/
  gen : Seed → Fin ℓ → F
  /-- Probability weight of each seed. -/
  weight : Seed → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum_one : ∑ ω, weight ω = 1

attribute [instance] ProximityGenerator.seedFintype

namespace ProximityGenerator

/-- Probability that the drawn coefficient tuple lands in the event `E`. -/
noncomputable def pr (G : ProximityGenerator F ℓ) (E : (Fin ℓ → F) → Prop) : ℝ :=
  letI : DecidablePred fun ω : G.Seed => E (G.gen ω) := fun _ => Classical.propDecidable _
  ∑ ω ∈ Finset.univ.filter (fun ω => E (G.gen ω)), G.weight ω

omit [Field F] [DecidableEq F] in
theorem pr_nonneg (G : ProximityGenerator F ℓ) (E : (Fin ℓ → F) → Prop) :
    0 ≤ G.pr E :=
  Finset.sum_nonneg fun ω _ => G.weight_nonneg ω

omit [Field F] [DecidableEq F] in
/-- Monotonicity of `pr` under event inclusion — the only probabilistic fact
Lemma 4.10 consumes. -/
theorem pr_mono (G : ProximityGenerator F ℓ) {E₁ E₂ : (Fin ℓ → F) → Prop}
    (h : ∀ r, E₁ r → E₂ r) : G.pr E₁ ≤ G.pr E₂ := by
  classical
  unfold pr
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, h _ hω.2⟩
  · intro ω _ _
    exact G.weight_nonneg ω

omit [Field F] [DecidableEq F] in
theorem pr_eq_zero (G : ProximityGenerator F ℓ) {E : (Fin ℓ → F) → Prop}
    (h : ∀ r, ¬E r) : G.pr E = 0 := by
  classical
  unfold pr
  rw [Finset.filter_false_of_mem fun ω _ => h (G.gen ω), Finset.sum_empty]

end ProximityGenerator

/-- Correlated agreement of the tuple `f` at radius δ: one common set `S` of at
least `(1−δ)·n` coordinates on which every `fᵢ` matches some codeword — the
conclusion of WHIR Definition 4.7. -/
def CorrelatedAgreement (C : Submodule F (ι → F)) (δ : ℝ)
    (f : Fin ℓ → ι → F) : Prop :=
  ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
    ∀ i, ∃ u ∈ C, AgreesOn S (f i) u

/-- **WHIR Definition 4.7 (proximity generator).** `Gen` is a proximity
generator for `C` with proximity bound `B` and error `err` if for every tuple
`f₁, …, f_ℓ` and every `δ ∈ (0, 1−B)`: whenever
`Pr[ ∆(∑ᵢ rᵢ·fᵢ, C) ≤ δ ] > err(δ)`, the tuple has correlated agreement at
radius δ. (`err` is a function of δ here; the paper's `C, ℓ` arguments are
fixed by the ambient statement.) -/
def IsProximityGenerator (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F))
    (B : ℝ) (err : ℝ → ℝ) : Prop :=
  ∀ (f : Fin ℓ → ι → F) (δ : ℝ), 0 < δ → δ < 1 - B →
    err δ < G.pr (fun r => close δ C (comb r f)) →
    CorrelatedAgreement C δ f

/-! ## Mutual correlated agreement (WHIR Definition 4.9) -/

/-- The failure event of mutual correlated agreement for a fixed coefficient
tuple `r` (the event inside the probability of WHIR Definition 4.9): some set
`S` of at least `(1−δ)·n` coordinates on which the combination `∑ⱼ rⱼ·fⱼ`
agrees with a codeword, while some input `fᵢ` agrees with NO codeword on `S` —
the combination's agreement set is not among the tuple's mutual ones. -/
def MutualCAFailure (C : Submodule F (ι → F)) (δ : ℝ) (f : Fin ℓ → ι → F)
    (r : Fin ℓ → F) : Prop :=
  ∃ S : Finset ι, (1 - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) ∧
    (∃ u ∈ C, AgreesOn S (comb r f) u) ∧
    ∃ i, ∀ u' ∈ C, ¬AgreesOn S (f i) u'

/-- **WHIR Definition 4.9 (mutual correlated agreement).** `Gen` has mutual
correlated agreement with proximity bound `B⋆` and error `err⋆` if for every
tuple `f` and `δ ∈ (0, 1−B⋆)` the failure event has probability at most
`err⋆(δ)`. (The printed Def 4.9 writes the range with the underlying `B`;
Lemma 4.10's own `B⋆` restricts it, and we state the property at the bound it
actually certifies.) -/
def HasMutualCorrelatedAgreement (G : ProximityGenerator F ℓ)
    (C : Submodule F (ι → F)) (Bstar : ℝ) (errstar : ℝ → ℝ) : Prop :=
  ∀ (f : Fin ℓ → ι → F) (δ : ℝ), 0 < δ → δ < 1 - Bstar →
    G.pr (MutualCAFailure C δ f) ≤ errstar δ

/-! ## The theorem: WHIR Lemma 4.10 -/

/-- **WHIR Lemma 4.10 — correlated agreement gives mutual correlated agreement
for free in the unique-decoding regime, for EVERY linear code.** If `Gen` is a
proximity generator for `C` with proximity bound `B` and error `err`, and `dC`
lower-bounds the pairwise relative distance of distinct codewords, then `Gen`
has mutual correlated agreement with proximity bound
`B⋆ = max (1 − dC/2) B` — i.e. on the radius interval
`δ ∈ (0, min {dC/2, 1−B})`, the unique-decoding regime — and the SAME error
`err⋆ = err`. (The paper prints `min` for `B⋆`; that is a typo for `max` — see
the module header.)

Hypotheses beyond the paper's statement, both implicit in its proof:
`herr_mono` (the error does not increase when the radius shrinks; Def 4.7 is
re-invoked at a smaller radius with the same threshold) and `herr_nonneg`
(negative error would make the conclusion unsatisfiable against `pr ≥ 0`).
Both hold for every instantiation in the paper (Theorem 4.8).

Proof (= the paper's, with the radius for the final invocation made exact):
take `T` a maximum-cardinality set on which every `fᵢ` agrees with some
codeword `uᵢ`. If the failure probability exceeds `err δ`, then (Def 4.7 at δ)
`|T| ≥ (1−δ)n`. For any failing seed with witness set `S`: the combination
`g_r = ∑ rⱼ·fⱼ` agrees with the codeword `w_r = ∑ rⱼ·uⱼ` on `T`, and with
some codeword `w'` on `S`; both are within δ of `g_r`, and `δ < dC/2` forces
`w' = w_r` (unique decoding). `S ⊄ T` (else the failing `fᵢ` would agree with
`uᵢ` on `S`), so `g_r` agrees with `w_r` on `S ∪ T ⊇ T ∪ {y}`, giving
`∆(g_r, C) ≤ (n − |T| − 1)/n < (n − |T| − ½)/n =: δ'`. Invoking Def 4.7 at δ'
(positive, ≤ δ, so `err δ' ≤ err δ <` the failure probability) yields a common
agreement set `W` with `|W| ≥ (1−δ')n = |T| + ½ > |T|` — contradicting
maximality. If instead `|T| = n`, every `fᵢ` agrees with `uᵢ` everywhere and
the failure event is empty, contradicting `err δ ≥ 0`. -/
theorem hasMutualCorrelatedAgreement_of_isProximityGenerator [Nonempty ι]
    (G : ProximityGenerator F ℓ) (C : Submodule F (ι → F)) {B : ℝ}
    {err : ℝ → ℝ} {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hPG : IsProximityGenerator G C B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement G C (max (1 - dC / 2) B) err := by
  classical
  intro f δ hδ0 hδlt
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn
  -- the two regime facts packed into `1 - max (1 - dC/2) B`
  have hδB : δ < 1 - B := by
    have := le_max_right (1 - dC / 2) B
    linarith
  have hδC : δ < dC / 2 := by
    have := le_max_left (1 - dC / 2) B
    linarith
  by_contra hcon
  push Not at hcon
  -- Step 1: the failure event implies δ-closeness of the combination.
  have hsub1 : ∀ r, MutualCAFailure C δ f r → close δ C (comb r f) := by
    rintro r ⟨S, hScard, ⟨u, huC, huAg⟩, -⟩
    exact ⟨u, huC, relDist_le_of_agreesOn huAg hScard⟩
  -- Step 2: Def 4.7 at δ gives a correlated-agreement set A.
  obtain ⟨A, hAcard, hAgood⟩ :=
    hPG f δ hδ0 hδB (lt_of_lt_of_le hcon (G.pr_mono hsub1))
  -- Step 3: a maximum-cardinality common agreement set T.
  obtain ⟨T, hTmem, hTmaxmem⟩ :=
    Finset.exists_max_image
      (Finset.univ.filter fun S : Finset ι => ∀ i, ∃ u ∈ C, AgreesOn S (f i) u)
      Finset.card
      ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAgood⟩⟩
  have hTgood : ∀ i, ∃ u ∈ C, AgreesOn T (f i) u := (Finset.mem_filter.mp hTmem).2
  have hTmax : ∀ S : Finset ι, (∀ i, ∃ u ∈ C, AgreesOn S (f i) u) →
      S.card ≤ T.card := fun S hS =>
    hTmaxmem S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
  have hTcard : (1 - δ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) :=
    le_trans hAcard (by exact_mod_cast hTmax A hAgood)
  choose u huC huAg using hTgood
  rcases eq_or_lt_of_le (Finset.card_le_univ T) with hTn | hTn
  · -- |T| = n: every fᵢ IS a codeword on all coordinates; no failure possible.
    have hTuniv : T = Finset.univ := Finset.eq_univ_of_card T hTn
    have hempty : ∀ r, ¬MutualCAFailure C δ f r := by
      rintro r ⟨S, -, -, i, hifail⟩
      exact hifail (u i) (huC i) fun x _ =>
        huAg i x (by rw [hTuniv]; exact Finset.mem_univ x)
    rw [G.pr_eq_zero hempty] at hcon
    exact absurd hcon (not_lt.mpr (herr_nonneg hδ0 hδB))
  · -- |T| < n: re-invoke Def 4.7 at the exact radius δ' = (n − |T| − ½)/n.
    set δ' : ℝ := ((Fintype.card ι : ℝ) - (T.card : ℝ) - 2⁻¹) / (Fintype.card ι : ℝ)
      with hδ'def
    have hTn' : (T.card : ℝ) + 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hTn
    have hδ'n : δ' * (Fintype.card ι : ℝ)
        = (Fintype.card ι : ℝ) - (T.card : ℝ) - 2⁻¹ := by
      rw [hδ'def]
      field_simp
    have hδ'0 : 0 < δ' := by
      rw [hδ'def]
      apply div_pos ?_ hn
      linarith
    have hδ'δ : δ' ≤ δ := by
      rw [hδ'def, div_le_iff₀ hn]
      nlinarith
    have hδ'B : δ' < 1 - B := lt_of_le_of_lt hδ'δ hδB
    -- Step 4: every failing seed puts the combination within δ' of C.
    have hsub2 : ∀ r, MutualCAFailure C δ f r → close δ' C (comb r f) := by
      rintro r ⟨S, hScard, ⟨w', hw'C, hw'Ag⟩, i, hifail⟩
      have hwrC : comb r u ∈ C := comb_mem r huC
      have hgrwrT : AgreesOn T (comb r f) (comb r u) := comb_agreesOn huAg
      have h1 : relDist (comb r f) (comb r u) ≤ δ :=
        relDist_le_of_agreesOn hgrwrT hTcard
      have h2 : relDist (comb r f) w' ≤ δ := relDist_le_of_agreesOn hw'Ag hScard
      have hw'wr : w' = comb r u :=
        codeword_eq_of_close_of_close hdC hw'C hwrC hδC h2 h1
      -- S ⊄ T, else the failing fᵢ agrees with uᵢ on S.
      obtain ⟨y, hyS, hyT⟩ : ∃ y ∈ S, y ∉ T := by
        by_contra hify
        push Not at hify
        exact hifail (u i) (huC i) fun x hx => huAg i x (hify x hx)
      have hUnion : AgreesOn (S ∪ T) (comb r f) (comb r u) := by
        intro x hx
        rcases Finset.mem_union.mp hx with hxS | hxT
        · exact (hw'Ag x hxS).trans (congrFun hw'wr x)
        · exact hgrwrT x hxT
      have hcard : T.card + 1 ≤ (S ∪ T).card := by
        have hins : insert y T ⊆ S ∪ T := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hzT
          · exact Finset.mem_union_left _ hyS
          · exact Finset.mem_union_right _ hzT
        calc T.card + 1 = (insert y T).card :=
              (Finset.card_insert_of_notMem hyT).symm
          _ ≤ (S ∪ T).card := Finset.card_le_card hins
      refine ⟨comb r u, hwrC, ?_⟩
      have hd : (hammingDist (comb r f) (comb r u) : ℝ) + ((T.card : ℝ) + 1)
          ≤ (Fintype.card ι : ℝ) := by
        have h5 := hammingDist_add_card_le_of_agreesOn hUnion
        have h6 : hammingDist (comb r f) (comb r u) + (T.card + 1)
            ≤ Fintype.card ι := le_trans (by omega) h5
        exact_mod_cast h6
      rw [relDist, div_le_iff₀ hn, hδ'n]
      linarith
    -- Step 5: Def 4.7 at δ' produces a common agreement set W with |W| > |T|.
    have hchain : err δ' < G.pr (fun r => close δ' C (comb r f)) :=
      lt_of_le_of_lt (herr_mono hδ'0 hδ'δ hδB)
        (lt_of_lt_of_le hcon (G.pr_mono hsub2))
    obtain ⟨W, hWcard, hWgood⟩ := hPG f δ' hδ'0 hδ'B hchain
    have hWT : (W.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hTmax W hWgood
    -- (1−δ')·n = |T| + ½ ≤ |W| ≤ |T|: contradiction.
    nlinarith [hWcard]

/-! ## PG(2): the two-function affine generator (the WARP/WHIR usage)

For batching two oracles the papers draw a single `r ← F` and take the
combination `f + r·g`, i.e. coefficients `(1, r)`. We formalize THAT variant —
it is literally WHIR's `Gen(ℓ; α) = (1, α, …, α^{ℓ−1})` at `ℓ = 2` (Theorem
4.8 / Corollary 4.11 are stated for this geometric generator) and WARP's
fold/batch step. The alternative affine parametrization `(1−r, r)` (the line
`f + r·(g−f)`) generates the same set of combinations up to affine
reparametrization but is NOT the tuple Theorem 4.8 bounds, so we do not use
it. Uniform seed `r ← F` requires `F` finite (as deployed). -/

/-- PG(2): coefficients `(1, r)` for uniform `r ← F` — the combination is
`f₀ + r·f₁`. -/
noncomputable def affineGenerator (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    ProximityGenerator F 2 where
  Seed := F
  gen r := ![1, r]
  weight _ := ((Fintype.card F : ℝ))⁻¹
  weight_nonneg _ := by positivity
  weight_sum_one := by
    have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hF)]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem comb_affineGenerator [Fintype F] (r : F) (f : Fin 2 → ι → F) (x : ι) :
    comb ((affineGenerator F).gen r) f x = f 0 x + r * f 1 x := by
  simp [comb, affineGenerator, Fin.sum_univ_two]

/-- WHIR Lemma 4.10 specialized to PG(2): if the affine generator is a
proximity generator for `C`, it has mutual correlated agreement on the
unique-decoding interval `δ ∈ (0, min {dC/2, 1−B})` with the same error. -/
theorem affineGenerator_hasMutualCorrelatedAgreement [Nonempty ι] [Fintype F]
    (C : Submodule F (ι → F)) {B : ℝ} {err : ℝ → ℝ} {dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hPG : IsProximityGenerator (affineGenerator F) C B err)
    (herr_mono : ∀ {δ₁ δ₂ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₂ → δ₂ < 1 - B → err δ₁ ≤ err δ₂)
    (herr_nonneg : ∀ {δ : ℝ}, 0 < δ → δ < 1 - B → 0 ≤ err δ) :
    HasMutualCorrelatedAgreement (affineGenerator F) C (max (1 - dC / 2) B) err :=
  hasMutualCorrelatedAgreement_of_isProximityGenerator (affineGenerator F) C hdC
    hPG (fun h1 h2 h3 => herr_mono h1 h2 h3) (fun h1 h2 => herr_nonneg h1 h2)

/-! ## Keystone hygiene (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The main theorem is PROVED, so no obligation `Prop` with TODO fields is left
behind; what remains to demonstrate is that its hypotheses are inhabitable and
its quantified interval nonempty — i.e. that it is not a vacuous implication. -/

omit [DecidableEq ι] in
/-- Premise inhabitation for `hdC`: EVERY submodule admits the quantization
floor `dC := 1/n` as a pairwise-distance lower bound. (Real instantiations use
a macroscopic `dC`; this witnesses satisfiability, not useful parameters.) -/
theorem minDistLB_inhabited [Nonempty ι] (C : Submodule F (ι → F)) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 1 / (Fintype.card ι : ℝ) ≤ relDist u v :=
  fun _ _ _ _ h => one_div_card_le_relDist h

omit [DecidableEq ι] in
/-- Satisfiability witness for `IsProximityGenerator` whose conclusion FIRES
(non-vacuous): over the full code `C = ⊤` every function is a codeword, so any
generator is a proximity generator with bound 0 and error 0, and the
correlated-agreement set produced is genuinely `univ`. -/
theorem isProximityGenerator_top (G : ProximityGenerator F ℓ) :
    IsProximityGenerator G (⊤ : Submodule F (ι → F)) 0 (fun _ => 0) := by
  intro f δ hδ0 _ _
  refine ⟨Finset.univ, ?_, fun i => ⟨f i, Submodule.mem_top, fun x _ => rfl⟩⟩
  rw [Finset.card_univ]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]

/-- End-to-end instantiation of the main theorem: PG(2) over the full code with
`dC = 1/n`, `B = 0`, `err = 0`. Every hypothesis is discharged by the witnesses
above; the resulting bound is `B⋆ = 1 − 1/(2n)`, whose interval `(0, 1/(2n))`
is nonempty (see the `example` below). -/
theorem hasMutualCorrelatedAgreement_top_affine [Nonempty ι] [Fintype F] :
    HasMutualCorrelatedAgreement (affineGenerator F)
      (⊤ : Submodule F (ι → F))
      (max (1 - 1 / (Fintype.card ι : ℝ) / 2) 0) (fun _ => 0) :=
  affineGenerator_hasMutualCorrelatedAgreement _
    (minDistLB_inhabited _) (isProximityGenerator_top _)
    (fun _ _ _ => le_refl 0) (fun _ _ => le_refl 0)

/-- Teeth: the δ-interval of `hasMutualCorrelatedAgreement_top_affine` is
nonempty — the statement quantifies over something. -/
example [Nonempty ι] :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 - max (1 - 1 / (Fintype.card ι : ℝ) / 2) 0 := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨1 / (Fintype.card ι : ℝ) / 4, by positivity, ?_⟩
  have h2 : 1 / (Fintype.card ι : ℝ) ≤ 1 := by
    rw [div_le_one hn]; exact hn1
  have hmax : max (1 - 1 / (Fintype.card ι : ℝ) / 2) 0
      = 1 - 1 / (Fintype.card ι : ℝ) / 2 := max_eq_left (by linarith)
  rw [hmax]
  have h3 : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
  linarith

end Minidregg.Selvage
