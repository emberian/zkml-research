/-
# Selvage.ZkExtraction — [ZK-RBR-interleave] missing lemma 2 attacked:
MASKED-CHAIN EXTRACTION. The flank splits in two, with opposite fates — both
PROVED — and the genuinely-open remainder sharpens to `[ZK-RBR-extract]`.

`Selvage/RbrZeroKnowledge.lean` named the extraction flank as the residual's
missing lemma 2: in deployment the chain extractor's `n + 1` transcripts are
erasure-corrected from the SAME `t·n` opened columns the simulator must
reproduce; the mask-augmented chain's extractor must peel `(witness, mask)`
pairs, and its flat family must perturb MASK coordinates — counterfactuals
the honest protocol never runs, which the seam must furnish "WITHOUT handing
the ZK distinguisher a second schedule". `Selvage/ZkTriangular.lean` closed the
hiding flank (missing lemma 1) at the model level; this file attacks the
extraction flank. The finding is a genuine RESOLUTION of the posed question,
not a closure of the whole flank:

**The question splits at the resolution of the extraction target.**

* **At MASKED RESOLUTION — extract the masked words — everything closes.**
  - `extractChain_flatFold`: the chain extractor inverts the honest flat
    chain word EXACTLY, arbitrary depth (`foldWords_ofFn` bridges to the
    landed `foldWords`, so this is the real chain word). The general theorem
    behind the landed F₅ `extractChain_recovers` computation.
  - `mask_sat_of_ker` + `maskedChain_knowledge_sound`: HOMOGENEOUS masks
    (targets `0` — `constrainedMaskSpace`'s shape, the landed mask design)
    are invisible to the claim channel, so the masked words ARE witnesses of
    the UNCHANGED claim chain, and the δ-schedule family alone — no mask
    counterfactual anywhere — extracts them exactly and `Forall₂`-certifies
    the whole chain. Adversarial-transcript form: the claim chain never
    moved, so it is the landed `extractChain_sound` VERBATIM, nothing to
    re-derive. Completeness of the masked protocol on the REAL aggregate:
    `masked_aggregate_satisfies` (via `aggregate_satisfies`, cited).
  - **The seam furnishes the counterfactuals from ONE execution**:
    successive recommitted partial folds differ by one γ-weighted masked
    word (`partialFold_succ`), so `t ≥ d` opened columns erasure-decode the
    increment (`recoverFromColumns_sound`, CITED) and `seamCounterfactual` —
    a pure function of the base transcript, the public schedules, and the
    opened columns; NO witness, NO mask, NO second run in its type —
    synthesizes the exact perturbed transcripts (`seamCounterfactual_sound`),
    through binding (`extractChain_committed_seam`, `[ACC-extract-bind]`
    composed end to end). One straightline FS execution serves the two-point
    extractor at every link.
  - **What extraction reveals is the simulator's own object**: the extracted
    words' openings ARE `jointOpen` — definitionally
    (`extracted_openings_are_jointOpen`, `rfl`) — and sweep the full public
    space over the mask draw (`extraction_surface_witness_free`, citing
    `rbrZeroKnowledge_of_rounds`); the FULL extracted word ranges over the
    claim's own PUBLIC satisfying set, identically for every witness
    (`mask_image_homTwin` / `extracted_word_witness_free`, citing
    `mask_bijOn`). Running the extractor hands the distinguisher nothing the
    simulator does not already produce.

* **At PAIR RESOLUTION — peel `(witness, mask)` — the counterfactual is
  provably NOT furnishable, and provably NOT needed.**
  - `extractMaskedPair` + `extractMaskedPair_sound`: the pair peel is
    complete algebra GIVEN transcripts at a perturbed MASK schedule — the
    `2n + 1`-transcript extractor the residual asked for, exact at arbitrary
    depth. `MaskedChainExtraction` states it with the quantifier positions
    explicit: its type carries BOTH `γalt` and `ηalt`.
  - `masked_pair_ambiguous`: two DISTINCT valid `(witness, mask)` families
    with EQUAL masked-word families — so every transcript at EVERY
    δ-schedule, every opened column, every function of the honest execution
    coincides. The mask counterfactual is not a function of the honest
    protocol's data; no straightline extractor reading one execution peels
    the pair. This impossibility IS hiding working (the pair is what ZK
    protects), and it is harmless: masked resolution already carries
    claim-level knowledge.
  - The games separate by quantifier position and it is VISIBLE in the
    types: `maskedExtraction_coexists_hiding` (both hold on one `(M, q, ηs)`),
    `zero_mask_kills_hiding_not_pair` (η-dial kills hiding, never the peel),
    `mask_diagonal_kills_pair_not_hiding` (one mask schedule collapses the
    peel to `0`, hiding untouched — `RbrZeroKnowledge`'s type cannot mention
    `ηalt`).

* **The parameter window — the sharp quantitative core.** The seam needs
  `d ≤ t`; constrained-mask hiding needs `t + 1 ≤ d`; they NEVER share a `t`
  (`not_constrainedMask_hiding_of_recoverable` — recoverability refutes
  constrained hiding at EVERY challenge, via `open_determines`). The
  whole-code mask coexists with the seam at exactly `t = d`
  (`seam_hiding_coexist_at_d`): the columns fully determine the masked word
  (the extractor's food) while revealing nothing about the witness (the
  simulator's promise) — no contradiction, because what they determine IS
  the masked word. All three regimes computed on one F₅ instance
  (`window_F5`). Consequence — the honest dichotomy: homogeneous masks make
  masked words witnesses but push the seam beyond unique decoding
  (`[ZK-RBR-extract]` open lemma A); whole-code masks keep the seam at
  `t = d` but shift the folded targets, so the mask claims must ride as
  links with their own targets, whose pair-level extraction is exactly the
  provably-unfurnishable counterfactual.

* **The deployment bridge, delivered as a bonus**: `partialFold_eq_triFold`
  identifies the masked chain's recommitted partial fold with
  `Selvage/ZkTriangular.lean`'s `triFold` at the PRODUCT schedule `δ·η` (the
  algebraic half of `[ZK-RBR-triangular]`'s named bridge), and
  `masked_partialFold_hiding` transports `TriangularHiding` verbatim: the
  very columns `seamCounterfactual` decodes are jointly uniform and
  witness-free. One data surface, two games, both satisfied — the
  composition `[ZK-RBR-interleave]` asked whether could exist, exhibited.

**Keystones** (F₅, the SAME instance as `RbrZkExample`/`ZkTriangularExample`):
masked knowledge extraction fired + computed (`masked_knowledge_F5`,
`masked_extraction_computes`); the pair peel fired + computed with the
supplied mask counterfactual (`maskedChainExtraction_F5`,
`pair_extraction_computes` — both rounds' pairs on the nose); the ambiguity
teeth fired + computed (`pair_ambiguous_F5`, `ambiguity_computed`); the seam
fired bare and through the ideal binding commitment (`seam_extraction_F5`,
`seam_extraction_committed_F5`); the window's three regimes (`window_F5`);
game separation both directions (`separation_F5`, `zero_mask_F5`,
`mask_diagonal_F5`); the deployed surface witness-free for ALL witnesses
(`deployed_surface_F5`). No `sorry`, no vacuous `Prop := True`.

**Honest scope.** Masked-resolution closure is relative to the
unique-decoding seam (`d ≤ t`, genuine codewords — the same honest boundary
as `Selvage/Erasure.lean`) and to the flat/product model of the chain word (the
absorption WLOGs of `Selvage/ZkTriangular.lean`, now partially discharged by
the bridge). Pair-resolution extraction is proved exactly as impossible
straightline and exactly as possible with the mask counterfactual — which
game grants that counterfactual is a GAME-PACKAGING question, not an
algebraic one, and is named in `[ZK-RBR-extract]` below with the two open
lemmas that are all that remains of the extraction flank.
-/
import Selvage.RbrZeroKnowledge
import Selvage.ZkTriangular
import Selvage.AccExtractChain
import Selvage.AccExtract
import Selvage.Erasure

namespace Minidregg.Selvage

/- `F : Type` (not `Type*`): the chain-extraction vocabulary this file inverts
(`updSched`, `extractChain` — `Selvage/AccExtractChain.lean`) lives there,
matching that file's sampled-schedule universe discipline. -/
variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {t n : ℕ} {r : ℕ}

/-! ## The masked chain word: the model -/

/-- **The masked witness family**: link `k`'s witness `ws k` masked by the
round's fresh draw `gs k` at the PUBLIC mask challenge `ηs k` — the landed
`mask` operation, per round. These are the words the masked prover folds in
place of the bare witnesses. -/
def maskedWord (ηs : ℕ → F) (ws gs : Fin n → ι → F) : Fin n → ι → F :=
  fun k => mask (ws k) (ηs (k : ℕ)) (gs k)

@[simp] theorem maskedWord_apply (ηs : ℕ → F) (ws gs : Fin n → ι → F)
    (k : Fin n) : maskedWord ηs ws gs k = ws k + ηs (k : ℕ) • gs k := rfl

/-- **The flat chain word**: genesis plus every link's `γs`-weighted
contribution — the closed form of `foldWords` (`foldWords_ofFn` below), on
which the schedule-perturbation algebra is one `Finset` identity per link. -/
def flatFold (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F) : ι → F :=
  f₀ + ∑ k : Fin n, γs (k : ℕ) • ms k

/-- The landed recursion computes the flat form: `foldWords` on an `ofFn`
witness list IS `flatFold`. This is the bridge that makes every theorem below
a theorem about the REAL chain word (`Selvage/LightClient.lean`'s `foldWords`),
not about a private model. -/
theorem foldWords_ofFn (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F) :
    foldWords γs f₀ (List.ofFn ms) = flatFold γs f₀ ms := by
  induction n generalizing γs f₀ with
  | zero => simp [flatFold]
  | succ n ih =>
    rw [List.ofFn_succ, foldWords_cons, ih]
    unfold flatFold
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    abel

/-- Perturbing the schedule at ONE link moves the flat word by exactly that
link's challenge difference times that link's word — the algebra the whole
extraction flank runs on. -/
theorem flatFold_updSched (γs γalt : ℕ → F) (f₀ : ι → F)
    (ms : Fin n → ι → F) (k : Fin n) :
    flatFold (updSched γs γalt k) f₀ ms
      = flatFold γs f₀ ms + (γalt (k : ℕ) - γs (k : ℕ)) • ms k := by
  unfold flatFold
  have h : ∀ j : Fin n, updSched γs γalt k (j : ℕ) • ms j
      = γs (j : ℕ) • ms j
        + (if j = k then (γalt (k : ℕ) - γs (k : ℕ)) • ms k else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [updSched_self, if_pos rfl, sub_smul]
      abel
    · rw [updSched_ne _ _ (fun hc => hj (Fin.ext hc)), if_neg hj, add_zero]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k]
  simp only [Finset.mem_univ, if_pos]
  abel

/-- Two flat words whose witness families differ at ONE link differ by that
link's weighted word difference. -/
theorem flatFold_congr_single (γs : ℕ → F) (f₀ : ι → F)
    {ms ms' : Fin n → ι → F} (k : Fin n)
    (h : ∀ j : Fin n, j ≠ k → ms j = ms' j) :
    flatFold γs f₀ ms
      = flatFold γs f₀ ms' + γs (k : ℕ) • (ms k - ms' k) := by
  unfold flatFold
  have hsum : ∑ j : Fin n, γs (j : ℕ) • ms j
      = (∑ j : Fin n, γs (j : ℕ) • ms' j)
        + γs (k : ℕ) • (ms k - ms' k) := by
    have h1 : ∀ j : Fin n, γs (j : ℕ) • ms j
        = γs (j : ℕ) • ms' j
          + (if j = k then γs (k : ℕ) • (ms k - ms' k) else 0) := by
      intro j
      by_cases hj : j = k
      · subst hj
        rw [if_pos rfl, smul_sub]
        abel
      · rw [h j hj, if_neg hj, add_zero]
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ k]
    simp only [Finset.mem_univ, if_pos]
  rw [hsum]
  abel

/-! ## The chain extractor inverts the flat fold, exactly -/

/-- The single-link kernel: `extractPair`'s second output on a flat base word
and its `k`-perturbed twin is EXACTLY link `k`'s word. The general form of
`AccExtractChainExample.extractChain_recovers`' per-entry computation. -/
theorem extractPair_flatFold_snd {γs γalt : ℕ → F} {k : Fin n}
    (hne : γs (k : ℕ) ≠ γalt (k : ℕ)) (f₀ : ι → F)
    (ms : Fin n → ι → F) :
    (extractPair (flatFold γs f₀ ms)
      (flatFold (updSched γs γalt k) f₀ ms)
      (γs (k : ℕ)) (γalt (k : ℕ))).2 = ms k := by
  rw [extractPair_snd, flatFold_updSched]
  have h1 : flatFold γs f₀ ms
      - (flatFold γs f₀ ms + (γalt (k : ℕ) - γs (k : ℕ)) • ms k)
      = (γs (k : ℕ) - γalt (k : ℕ)) • ms k := by
    rw [sub_smul, sub_smul]
    abel
  rw [h1, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero_of_ne hne), one_smul]

/-- **The chain extractor inverts the honest flat fold, EXACTLY** — arbitrary
depth: on the `n + 1` flat transcripts of any prover that folded the family
`ms`, `extractChain` returns the list `ms` on the nose, not merely a
satisfying list. The general theorem behind the landed F₅ computation
`extractChain_recovers`; consumed below both by the masked-resolution
knowledge theorem and by the seam-furnished one-execution extraction. -/
theorem extractChain_flatFold {γs γalt : ℕ → F}
    (hne : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ)) (f₀ : ι → F)
    (ms : Fin n → ι → F) :
    extractChain γs γalt (flatFold γs f₀ ms)
        (fun k : Fin n => flatFold (updSched γs γalt k) f₀ ms)
      = List.ofFn ms := by
  unfold extractChain
  exact congrArg List.ofFn (funext fun k =>
    extractPair_flatFold_snd (hne k) f₀ ms)

/-! ## Homogeneous masks: the masked word is a genuine witness -/

/-- **The homogeneous-mask absorption**: a witness masked by any code element
in the claim's CHANNEL KERNEL still witnesses the SAME claim, at every mask
challenge — the fold with a homogeneous (target-`0`) mask claim does not move
the claim at all. This is why the masked chain's CLAIM chain is the real
chain unchanged, and why extraction at masked resolution is claim-level
knowledge soundness (below). `mask_mem` supplies membership; the channel
computation is one `map_add`. -/
theorem mask_sat_of_ker {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {w g : ι → F} (η : F) (hw : AccClaim.Satisfies C A w) (hgC : g ∈ C)
    (hker : ∀ i, A.weights i g = 0) :
    AccClaim.Satisfies C A (mask w η g) := by
  refine ⟨mask_mem η hw.1 hgC, fun i => ?_⟩
  show A.weights i (w + η • g) = A.targets i
  rw [map_add, map_smul, hker i, smul_zero, add_zero]
  exact hw.2 i

/-- The masked witness family `Forall₂`-witnesses the UNCHANGED claim chain —
the list-shaped form the light-client theorems consume. -/
theorem maskedWord_forall₂ {C : Submodule F (ι → F)} {ch : Chain Root F ι r}
    {ηs : ℕ → F} {ws gs : Fin ch.length → ι → F}
    (hws : ∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k))
    (hgsC : ∀ k, gs k ∈ C)
    (hker : ∀ k i, (ch.get k).claim.weights i (gs k) = 0) :
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (List.ofFn (maskedWord ηs ws gs)) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  have hget : (List.ofFn (maskedWord ηs ws gs)).get ⟨i, h₂⟩
      = maskedWord ηs ws gs ⟨i, by simpa using h₂⟩ := by
    simp
  rw [hget]
  exact mask_sat_of_ker _ (hws _) (hgsC _) (hker _)

/-- **Completeness of the masked chain, on the REAL aggregate**: the masked
prover's word at EVERY schedule is a genuine witness of the aggregate of the
UNCHANGED chain — `aggregate_satisfies` (cited) on the masked witness list,
presented in flat form through `foldWords_ofFn`. Nothing about the claims
moved: homogeneous masks are invisible to the channel. -/
theorem masked_aggregate_satisfies {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A₀ : AccClaim Root F ι r}
    {ch : Chain Root F ι r} (halign : Aligned A₀ ch) (γs : ℕ → F)
    {ηs : ℕ → F} {f₀ : ι → F} {ws gs : Fin ch.length → ι → F}
    (hf₀ : AccClaim.Satisfies C A₀ f₀)
    (hws : ∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k))
    (hgsC : ∀ k, gs k ∈ C)
    (hker : ∀ k i, (ch.get k).claim.weights i (gs k) = 0) :
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch)
      (flatFold γs f₀ (maskedWord ηs ws gs)) := by
  rw [← foldWords_ofFn]
  exact aggregate_satisfies foldRoot γs (maskedWord_forall₂ hws hgsC hker)
    halign hf₀

/-- **Masked-chain knowledge soundness at MASKED RESOLUTION — the positive
theorem of the flank, arbitrary depth.** From the flat `n + 1`-transcript
family of the masked prover — the SAME δ-schedule counterfactuals the
unmasked extraction uses, NO mask-coordinate counterfactual anywhere — the
chain extractor returns EXACTLY the masked witness list, and that list
genuinely `Forall₂`-witnesses the UNCHANGED claim chain. Knowledge soundness
of the masked protocol costs the extractor nothing and never touches the mask
schedule: what it recovers is the masked word, which for homogeneous masks IS
a witness. (What it provably CANNOT recover — the `(witness, mask)`
decomposition — is `masked_pair_ambiguous` below; that impossibility is
hiding itself, not a defect.) -/
theorem maskedChain_knowledge_sound {C : Submodule F (ι → F)}
    {ch : Chain Root F ι r} {γs γalt ηs : ℕ → F}
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    {f₀ : ι → F} {ws gs : Fin ch.length → ι → F}
    (hws : ∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k))
    (hgsC : ∀ k, gs k ∈ C)
    (hker : ∀ k i, (ch.get k).claim.weights i (gs k) = 0) :
    extractChain γs γalt (flatFold γs f₀ (maskedWord ηs ws gs))
        (fun k : Fin ch.length =>
          flatFold (updSched γs γalt k) f₀ (maskedWord ηs ws gs))
      = List.ofFn (maskedWord ηs ws gs) ∧
    List.Forall₂ (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w)
      ch (extractChain γs γalt (flatFold γs f₀ (maskedWord ηs ws gs))
        (fun k : Fin ch.length =>
          flatFold (updSched γs γalt k) f₀ (maskedWord ηs ws gs))) := by
  have hex := extractChain_flatFold hne f₀ (maskedWord ηs ws gs)
  exact ⟨hex, hex ▸ maskedWord_forall₂ hws hgsC hker⟩

/-! ## What the extraction reveals is the simulator's own surface -/

/-- **The extractor's output IS the simulator's leakage object, syntactically**:
the per-round openings of the extracted masked words are `jointOpen` — the
EXACT map whose image `RbrZeroKnowledge` proves uniform and witness-free.
Definitional equality, recorded so the two files' objects are one object on
the nose, not merely analogous. -/
theorem extracted_openings_are_jointOpen (q : Fin n → Fin t → ι)
    (ηs : ℕ → F) (ws gs : Fin n → ι → F) :
    (fun k => openSymbols (q k) (maskedWord ηs ws gs k))
      = jointOpen q ηs ws gs := rfl

/-- **Confinement of the δ-counterfactuals, opening level**: everything the
δ-schedule extraction can reveal about the openings — the extracted masked
words' opened tuples, over the mask draw — is the FULL public product space,
for EVERY witness family. The extraction game's leakage surface equals the
chain simulator's support (`rbrZeroKnowledge_of_rounds`, CITED): running the
extractor hands the ZK distinguisher nothing the simulator does not already
produce. -/
theorem extraction_surface_witness_free {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {ηs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ)))
    (ws : Fin n → ι → F) :
    (fun gs => jointOpen q ηs ws gs) '' jointMasks M = Set.univ :=
  (rbrZeroKnowledge_of_rounds H).chain_sim_support ws

/-! ## The full extracted word ranges over a PUBLIC set

Openings are one face; the extractor holds the WHOLE masked word. For
homogeneous masks drawn from the claim's full channel kernel, that word
ranges over the claim's OWN satisfying set — a public object — uniformly and
witness-freely, by the landed fold bijection `mask_bijOn` (CITED). -/

/-- The homogeneous twin of a claim: same root, same functionals, all targets
zeroed — the mask claim whose satisfying set is the claim's channel kernel
over the code. -/
def homTwin (A : AccClaim Root F ι r) : AccClaim Root F ι r :=
  ⟨A.rt, fun i => ((A.channel i).1, 0)⟩

@[simp] theorem homTwin_weights (A : AccClaim Root F ι r) (i : Fin r) :
    (homTwin A).weights i = A.weights i := rfl

@[simp] theorem homTwin_targets (A : AccClaim Root F ι r) (i : Fin r) :
    (homTwin A).targets i = 0 := rfl

theorem satisfies_homTwin_iff {C : Submodule F (ι → F)}
    {A : AccClaim Root F ι r} {g : ι → F} :
    AccClaim.Satisfies C (homTwin A) g ↔ g ∈ C ∧ ∀ i, A.weights i g = 0 :=
  Iff.rfl

/-- Folding a claim with its homogeneous twin moves nothing: the folded
channel IS the claim's channel, at every challenge. -/
theorem foldClaims_homTwin_channel (foldRoot : Root → F → Root → Root)
    (A : AccClaim Root F ι r) (η : F) :
    (foldClaims foldRoot A (homTwin A) η).channel = A.channel := by
  funext i
  refine Prod.ext rfl ?_
  show (A.channel i).2 + η * 0 = (A.channel i).2
  ring

/-- **The extracted word's range is the claim's own satisfying set** — a
PUBLIC object, identical for every witness: masking a witness by the full
channel kernel sweeps out exactly `satWords C A`. `mask_bijOn` (the landed
fold bijection, CITED) through the homogeneous twin. -/
theorem mask_image_homTwin (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w : ι → F} {η : F}
    (hη : η ≠ 0) (hw : AccClaim.Satisfies C A w) :
    mask w η '' satWords C (homTwin A) = satWords C A := by
  rw [(mask_bijOn (A := A) (B := homTwin A) foldRoot hη (fun i => rfl)
    hw).image_eq]
  ext h
  constructor
  · exact fun hh => AccClaim.satisfies_of_channel_eq
      (foldClaims_homTwin_channel foldRoot A η) hh
  · exact fun hh => AccClaim.satisfies_of_channel_eq
      (foldClaims_homTwin_channel foldRoot A η).symm hh

/-- **Witness independence of the extractor's whole output**: two provers
holding DIFFERENT witnesses of the same claim produce identical full-word
ranges for the extracted masked word — both are the claim's public satisfying
set. The δ-extraction cannot distinguish witnesses even holding the complete
extracted word, not just its openings. -/
theorem extracted_word_witness_free (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w₁ w₂ : ι → F}
    {η : F} (hη : η ≠ 0) (h₁ : AccClaim.Satisfies C A w₁)
    (h₂ : AccClaim.Satisfies C A w₂) :
    mask w₁ η '' satWords C (homTwin A) = mask w₂ η '' satWords C (homTwin A) := by
  rw [mask_image_homTwin foldRoot hη h₁, mask_image_homTwin foldRoot hη h₂]

/-! ## The mask-augmented extractor: peeling the pair COSTS a mask counterfactual

`[ZK-RBR-interleave]`'s missing lemma 2 asked for the extractor that peels
`(witness, mask)` pairs. Here it is — and its type is the diagnosis: it
consumes `2n + 1` transcripts, the extra `n` at MASK-perturbed schedules
`updSched ηs ηalt k` — counterfactual mask challenges the honest protocol
never runs (the mask challenge is fixed per round). With them, the peel
closes exactly (`extractMaskedPair_sound`); without them it is
information-theoretically impossible (`masked_pair_ambiguous`); and the
without-them extraction that IS possible — masked resolution — is
`maskedChain_knowledge_sound` above. -/

/-- **The mask-augmented pair extractor**: from the base transcript `h₀`, the
`n` link-perturbed transcripts `hlink`, and the `n` MASK-perturbed
transcripts `hmask`, recover round `k`'s `(witness, mask)` pair. The mask is
one field inversion against the mask-coordinate difference (challenge
`γs k · (ηs k − ηalt k)` — the product through which the mask enters the flat
word); the witness is the extracted masked word with the recovered mask
peeled at the public challenge (the `unmask` shape). Straightline: a pure
function of transcript data, no rewinding. -/
def extractMaskedPair (γs γalt ηs ηalt : ℕ → F) (h₀ : ι → F)
    (hlink hmask : Fin n → ι → F) (k : Fin n) : (ι → F) × (ι → F) :=
  ((extractPair h₀ (hlink k) (γs (k : ℕ)) (γalt (k : ℕ))).2
      - ηs (k : ℕ) • ((γs (k : ℕ) * (ηs (k : ℕ) - ηalt (k : ℕ)))⁻¹
        • (h₀ - hmask k)),
    (γs (k : ℕ) * (ηs (k : ℕ) - ηalt (k : ℕ)))⁻¹ • (h₀ - hmask k))

/-- **The pair peel is EXACT — given the mask counterfactuals.** On the
honest masked transcripts (base + link-perturbed + mask-perturbed), the
mask-augmented extractor returns exactly `(ws k, gs k)`, for every round of
an arbitrary-depth chain. Both distinctness dials are load-bearing:
`γs k ≠ γalt k` for the masked word, `ηs k ≠ ηalt k` (and `γs k ≠ 0`) for the
mask; the diagonal collapses below. -/
theorem extractMaskedPair_sound {γs γalt ηs ηalt : ℕ → F} (f₀ : ι → F)
    (ws gs : Fin n → ι → F) {k : Fin n} (hγ : γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : γs (k : ℕ) ≠ 0) (hη : ηs (k : ℕ) ≠ ηalt (k : ℕ)) :
    extractMaskedPair γs γalt ηs ηalt (flatFold γs f₀ (maskedWord ηs ws gs))
      (fun j : Fin n => flatFold (updSched γs γalt j) f₀ (maskedWord ηs ws gs))
      (fun j : Fin n => flatFold γs f₀ (maskedWord (updSched ηs ηalt j) ws gs))
      k
    = (ws k, gs k) := by
  have hprod : γs (k : ℕ) * (ηs (k : ℕ) - ηalt (k : ℕ)) ≠ 0 :=
    mul_ne_zero hγ0 (sub_ne_zero_of_ne hη)
  -- the mask-perturbed transcript differs from the base by the product-weighted mask
  have hdiff : flatFold γs f₀ (maskedWord ηs ws gs)
      = flatFold γs f₀ (maskedWord (updSched ηs ηalt k) ws gs)
        + γs (k : ℕ) • (maskedWord ηs ws gs k
          - maskedWord (updSched ηs ηalt k) ws gs k) := by
    refine flatFold_congr_single γs f₀ k fun j hj => ?_
    show mask (ws j) (ηs (j : ℕ)) (gs j)
      = mask (ws j) (updSched ηs ηalt k (j : ℕ)) (gs j)
    rw [updSched_ne _ _ (fun hc => hj (Fin.ext hc))]
  have hgap : maskedWord ηs ws gs k
      - maskedWord (updSched ηs ηalt k) ws gs k
      = (ηs (k : ℕ) - ηalt (k : ℕ)) • gs k := by
    show (ws k + ηs (k : ℕ) • gs k)
        - (ws k + updSched ηs ηalt k (k : ℕ) • gs k)
      = (ηs (k : ℕ) - ηalt (k : ℕ)) • gs k
    rw [updSched_self, sub_smul]
    abel
  have hmaskrec : (γs (k : ℕ) * (ηs (k : ℕ) - ηalt (k : ℕ)))⁻¹
      • (flatFold γs f₀ (maskedWord ηs ws gs)
        - flatFold γs f₀ (maskedWord (updSched ηs ηalt k) ws gs))
      = gs k := by
    rw [hdiff, hgap]
    have h2 : flatFold γs f₀ (maskedWord (updSched ηs ηalt k) ws gs)
        + γs (k : ℕ) • (ηs (k : ℕ) - ηalt (k : ℕ)) • gs k
        - flatFold γs f₀ (maskedWord (updSched ηs ηalt k) ws gs)
        = (γs (k : ℕ) * (ηs (k : ℕ) - ηalt (k : ℕ))) • gs k := by
      rw [smul_smul]
      abel
    rw [h2, inv_smul_smul₀ hprod]
  unfold extractMaskedPair
  rw [extractPair_flatFold_snd hγ f₀ (maskedWord ηs ws gs), hmaskrec]
  refine Prod.ext ?_ rfl
  show maskedWord ηs ws gs k - ηs (k : ℕ) • gs k = ws k
  rw [maskedWord_apply]
  abel

/-- **The mask-coordinate diagonal collapses**: with the honest mask schedule
on both sides (`ηalt = ηs`) the recovered mask is erased to `0`
unconditionally — `(γ · 0)⁻¹ = 0` — whatever the transcripts. The mask
counterfactual is load-bearing exactly as the link counterfactual was
(`extractPair_self`, `extractChain_self`): ONE mask schedule never peels the
pair. -/
theorem extractMaskedPair_mask_diagonal (γs γalt ηs : ℕ → F) (h₀ : ι → F)
    (hlink hmask : Fin n → ι → F) (k : Fin n) :
    (extractMaskedPair γs γalt ηs ηs h₀ hlink hmask k).2 = 0 := by
  unfold extractMaskedPair
  rw [sub_self, mul_zero, inv_zero, zero_smul]

/-- **`maskedChainExtraction`** — the mask-augmented chain-extraction
statement, quantifier positions explicit: the extractor recovers EVERY
round's `(witness, mask)` pair from the mask-augmented flat family — base,
`n` link-perturbed, `n` MASK-perturbed transcripts. The type carries BOTH
counterfactual schedules `γalt` and `ηalt`; contrast `RbrZeroKnowledge`,
whose type carries neither. Inhabited by `maskedChainExtraction_holds`;
UNREACHABLE from δ-counterfactuals alone by `masked_pair_ambiguous`. -/
def MaskedChainExtraction {F : Type} [Field F] {ι : Type*}
    (γs γalt ηs ηalt : ℕ → F) (n : ℕ) : Prop :=
  ∀ (f₀ : ι → F) (ws gs : Fin n → ι → F) (k : Fin n),
    extractMaskedPair γs γalt ηs ηalt (flatFold γs f₀ (maskedWord ηs ws gs))
      (fun j : Fin n => flatFold (updSched γs γalt j) f₀ (maskedWord ηs ws gs))
      (fun j : Fin n => flatFold γs f₀ (maskedWord (updSched ηs ηalt j) ws gs))
      k
    = (ws k, gs k)

/-- The mask-augmented chain extraction HOLDS whenever both challenge dials
are genuinely two-point at every round — the positive half of the flank's
resolution: given the mask counterfactuals, the peel is complete algebra, no
new obstruction. -/
theorem maskedChainExtraction_holds {γs γalt ηs ηalt : ℕ → F}
    (hγ : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin n, ηs (k : ℕ) ≠ ηalt (k : ℕ)) :
    MaskedChainExtraction (ι := ι) γs γalt ηs ηalt n :=
  fun f₀ ws gs k => extractMaskedPair_sound f₀ ws gs (hγ k) (hγ0 k) (hη k)

/-! ## Teeth: the mask counterfactual is NECESSARY and game-confined -/

/-- **The δ-schedule family can NEVER peel the pair — information-theoretic,
all schedules at once**: two DISTINCT `(witness, mask)` families, both fully
valid (witnesses satisfy their links, masks in the code and channel-killed),
whose masked-word families are EQUAL — so every transcript at EVERY link
schedule δ, every opened column, every function whatsoever of the honest
protocol's data coincides. `single_fold_ambiguous` lifted to the masked chain
at full quantifier strength: the mask-perturbed transcripts `extractMaskedPair`
consumes are not a function of the honest execution, and no extractor
avoiding them recovers the decomposition. This impossibility IS hiding doing
its job — the pair is exactly what zero-knowledge protects; the extraction
game gets the masked words (`maskedChain_knowledge_sound`) and they suffice
for the claims. -/
theorem masked_pair_ambiguous {C : Submodule F (ι → F)}
    {ch : Chain Root F ι r} {ηs : ℕ → F}
    {ws gs : Fin ch.length → ι → F}
    (hws : ∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k))
    (hgsC : ∀ k, gs k ∈ C)
    (hker : ∀ k i, (ch.get k).claim.weights i (gs k) = 0)
    {k₀ : Fin ch.length} (hnz : gs k₀ ≠ 0) :
    ∃ ws' gs' : Fin ch.length → ι → F,
      (ws', gs') ≠ (ws, gs) ∧
      (∀ k, AccClaim.Satisfies C (ch.get k).claim (ws' k)) ∧
      (∀ k, gs' k ∈ C ∧ ∀ i, (ch.get k).claim.weights i (gs' k) = 0) ∧
      maskedWord ηs ws' gs' = maskedWord ηs ws gs ∧
      ∀ (δ : ℕ → F) (f₀ : ι → F),
        flatFold δ f₀ (maskedWord ηs ws' gs')
          = flatFold δ f₀ (maskedWord ηs ws gs) := by
  refine ⟨maskedWord ηs ws gs, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcontra
    have hg : (fun _ => 0 : Fin ch.length → ι → F) = gs :=
      congrArg Prod.snd hcontra
    exact hnz (congrFun hg k₀).symm
  · exact fun k => mask_sat_of_ker _ (hws k) (hgsC k) (hker k)
  · exact fun k => ⟨Submodule.zero_mem C, fun i => map_zero _⟩
  · funext k
    show maskedWord ηs ws gs k + ηs (k : ℕ) • (0 : ι → F)
      = maskedWord ηs ws gs k
    rw [smul_zero, add_zero]
  · intro δ f₀
    congr 1
    funext k
    show maskedWord ηs ws gs k + ηs (k : ℕ) • (0 : ι → F)
      = maskedWord ηs ws gs k
    rw [smul_zero, add_zero]

/-- **The game separation, coexistence form**: on ONE round family `(M, q, ηs)`,
the mask-augmented extraction (BOTH counterfactual schedules in its type) and
round-by-round zero-knowledge (NEITHER in its type) hold simultaneously — the
quantifier-position resolution at the multi-round level. The extraction game
against a cheating prover may perturb mask coordinates; the simulator faces
the honest prover's single schedule; nothing forces the two quantifiers into
one game. -/
theorem maskedExtraction_coexists_hiding {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs γalt ηs ηalt : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ)))
    (hγ : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin n, ηs (k : ℕ) ≠ ηalt (k : ℕ)) :
    MaskedChainExtraction (ι := ι) γs γalt ηs ηalt n
      ∧ RbrZeroKnowledge M q ηs :=
  ⟨maskedChainExtraction_holds hγ hγ0 hη, rbrZeroKnowledge_of_rounds H⟩

/-- **Teeth 1 — a zero mask challenge kills hiding, never the pair peel**: at
`ηs k₀ = 0` multi-round zero-knowledge is refuted outright
(`not_rbrZeroKnowledge_of_zero`, CITED) while the mask-augmented extraction
still recovers every pair (its dials never require `ηs k ≠ 0`). The η-dial is
hiding's, not knowledge's. -/
theorem zero_mask_kills_hiding_not_pair {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs γalt ηs ηalt : ℕ → F} (k₀ : Fin n)
    (h0 : ηs (k₀ : ℕ) = 0) (ht : 0 < t)
    (hγ : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin n, ηs (k : ℕ) ≠ ηalt (k : ℕ)) :
    ¬ RbrZeroKnowledge M q ηs
      ∧ MaskedChainExtraction (ι := ι) γs γalt ηs ηalt n :=
  ⟨not_rbrZeroKnowledge_of_zero k₀ h0 ht,
    maskedChainExtraction_holds hγ hγ0 hη⟩

/-- **Teeth 2 — one mask schedule kills the pair peel, never hiding**: at the
mask diagonal `ηalt = ηs` the recovered mask is `0` for ALL inputs — so no
nonzero mask is ever returned — while `RbrZeroKnowledge` at the same `ηs`
stands untouched; its type cannot even mention `ηalt`. Dual to teeth 1,
and the multi-round lift of `extract_teeth_diagonal`. -/
theorem mask_diagonal_kills_pair_not_hiding {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs γalt ηs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ))) :
    (∀ (h₀ : ι → F) (hlink hmask : Fin n → ι → F) (k : Fin n),
        (extractMaskedPair γs γalt ηs ηs h₀ hlink hmask k).2 = 0)
      ∧ RbrZeroKnowledge M q ηs :=
  ⟨fun h₀ hlink hmask k =>
      extractMaskedPair_mask_diagonal γs γalt ηs h₀ hlink hmask k,
    rbrZeroKnowledge_of_rounds H⟩

/-! ## The erasure seam furnishes the δ-counterfactuals from ONE execution

`[ACC-extract-bind]`'s question for the masked chain: the extractor's `n + 1`
transcripts must come out of ONE straightline FS execution — the opened
columns of the recommitted partial folds — WITHOUT handing the ZK
distinguisher anything new. Closed here at unique decoding: the perturbed
transcripts are a FUNCTION of the base transcript and the opened columns
(`seamCounterfactual` — its type mentions no witness, no mask, no second
execution), because successive partial folds differ by exactly one
γ-weighted masked word, which `t ≥ d` columns erasure-decode
(`recoverFromColumns_sound`, CITED). -/

/-- The `c`-th partial fold of the flat chain word: genesis plus the first
`c` links' weighted words — the word the deployed prover recommits (and the
verifier spot-checks) after `c` rounds. `partialFold n = flatFold`. -/
def partialFold (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F) (c : ℕ) :
    ι → F :=
  f₀ + ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < c),
    γs (j : ℕ) • ms j

@[simp] theorem partialFold_zero (γs : ℕ → F) (f₀ : ι → F)
    (ms : Fin n → ι → F) : partialFold γs f₀ ms 0 = f₀ := by
  unfold partialFold
  have h : Finset.univ.filter (fun j : Fin n => (j : ℕ) < 0)
      = (∅ : Finset (Fin n)) := by
    ext j
    simp
  rw [h, Finset.sum_empty, add_zero]

/-- **The recommitment step**: each partial fold is the previous one plus the
new round's γ-weighted word — the increment the seam will decode. -/
theorem partialFold_succ (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F)
    (k : Fin n) :
    partialFold γs f₀ ms ((k : ℕ) + 1)
      = partialFold γs f₀ ms (k : ℕ) + γs (k : ℕ) • ms k := by
  unfold partialFold
  have h1 : Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1)
      = insert k (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff]
    omega
  have h2 : k ∉ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ)) := by
    simp
  rw [h1, Finset.sum_insert h2]
  abel

/-- The full-depth partial fold is the chain word. -/
theorem partialFold_last (γs : ℕ → F) (f₀ : ι → F) (ms : Fin n → ι → F) :
    partialFold γs f₀ ms n = flatFold γs f₀ ms := by
  unfold partialFold flatFold
  congr 1
  refine Finset.sum_congr ?_ fun j _ => rfl
  ext j
  simp

/-- **The seam-synthesized counterfactual**: round `k`'s perturbed transcript,
computed from the base transcript `h₀`, the public schedules, and the opened
columns `cols` of two SUCCESSIVE recommitted partial folds — erasure-decode
the round increment from the column differences, reweight by the challenge
difference. A pure function of the honest execution's public view: no
witness, no mask, no second protocol run occurs in the type. -/
noncomputable def seamCounterfactual (dom : ι ↪ F) (d : ℕ) {t : ℕ}
    (q : Fin t → ι) (γs γalt : ℕ → F) (h₀ : ι → F)
    (cols : ℕ → Fin t → F) (k : Fin n) : ι → F :=
  h₀ + (γalt (k : ℕ) - γs (k : ℕ)) •
    recoverFromColumns dom d q
      (fun j => (γs (k : ℕ))⁻¹ * (cols ((k : ℕ) + 1) j - cols (k : ℕ) j))

/-- **The seam furnishes the counterfactual family, exactly** — the
unique-decoding closure of the flank's `[ACC-extract-bind]` half: when the
opened columns are genuinely those of the recommitted partial folds and each
round's (masked) word is a codeword, the synthesized transcript EQUALS the
true `k`-perturbed transcript. `recoverFromColumns_sound` (CITED) does the
decoding; `partialFold_succ` isolates the increment; `flatFold_updSched`
reweights it. -/
theorem seamCounterfactual_sound (dom : ι ↪ F) {d t : ℕ} (hdt : d ≤ t)
    {q : Fin t → ι} (hq : Function.Injective (dom ∘ q)) {γs γalt : ℕ → F}
    {f₀ : ι → F} {ms : Fin n → ι → F} {cols : ℕ → Fin t → F} {k : Fin n}
    (hγ0 : γs (k : ℕ) ≠ 0) (hms : ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ n → ∀ j, cols c j = partialFold γs f₀ ms c (q j)) :
    seamCounterfactual dom d q γs γalt (flatFold γs f₀ ms) cols k
      = flatFold (updSched γs γalt k) f₀ ms := by
  have hrec : recoverFromColumns dom d q
      (fun j => (γs (k : ℕ))⁻¹ * (cols ((k : ℕ) + 1) j - cols (k : ℕ) j))
      = ms k := by
    refine recoverFromColumns_sound dom hdt hq hms fun j => ?_
    rw [hcols ((k : ℕ) + 1) k.isLt j, hcols (k : ℕ) (le_of_lt k.isLt) j]
    have hstep := congrFun (partialFold_succ γs f₀ ms k) (q j)
    have h2 : partialFold γs f₀ ms ((k : ℕ) + 1) (q j)
        - partialFold γs f₀ ms (k : ℕ) (q j)
        = γs (k : ℕ) * ms k (q j) := by
      rw [hstep]
      show partialFold γs f₀ ms (k : ℕ) (q j) + γs (k : ℕ) * ms k (q j)
          - partialFold γs f₀ ms (k : ℕ) (q j) = γs (k : ℕ) * ms k (q j)
      ring
    rw [h2, inv_mul_cancel_left₀ hγ0]
  unfold seamCounterfactual
  rw [hrec, flatFold_updSched]

/-- **One execution suffices — the whole extraction from one transcript plus
its opened columns**: `extractChain` fed the seam-synthesized counterfactual
family returns the full (masked) witness list exactly. The two-point
extractor's second transcripts never came from a second run: they are
computed from the SAME `t·n` opened symbols the simulator must reproduce —
and by `extraction_surface_witness_free` those symbols carry no witness
information. The extraction and hiding games genuinely consume one data
surface, each satisfied. -/
theorem extractChain_seamCounterfactual (dom : ι ↪ F) {d t : ℕ}
    (hdt : d ≤ t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {γs γalt : ℕ → F} {f₀ : ι → F} {ms : Fin n → ι → F}
    {cols : ℕ → Fin t → F}
    (hne : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hcols : ∀ c : ℕ, c ≤ n → ∀ j, cols c j = partialFold γs f₀ ms c (q j)) :
    extractChain γs γalt (flatFold γs f₀ ms)
        (seamCounterfactual (n := n) dom d q γs γalt (flatFold γs f₀ ms) cols)
      = List.ofFn ms := by
  have h : seamCounterfactual (n := n) dom d q γs γalt (flatFold γs f₀ ms) cols
      = fun k : Fin n => flatFold (updSched γs γalt k) f₀ ms :=
    funext fun k =>
      seamCounterfactual_sound dom hdt hq (hγ0 k) (hms k) hcols
  rw [h, extractChain_flatFold hne f₀ ms]

omit [Field F] in
/-- **Binding attaches the columns**: verified openings against a root that
commits a word ARE that word's symbols — `BindingCommitment.binding` against
the honest opening, the inner step of `committed_word_recovered` exposed as
the seam's premise-discharger. -/
theorem binding_columns {Root' Op : Type*} (S : BindingCommitment Root' F ι Op)
    {w : ι → F} {rt : Root'} (hrt : rt = S.commit w) {q : Fin t → ι}
    {vals : Fin t → F} {ops : Fin t → Op}
    (hver : ∀ j, S.verifyOpen rt (q j) (vals j) (ops j)) :
    ∀ j, vals j = w (q j) := fun j =>
  S.binding rt (q j) (vals j) (w (q j)) (ops j) (S.openAt w (q j)) (hver j)
    (S.toOpeningScheme.verifyOpen_of_commit_eq hrt (q j))

/-- **The committed seam, end to end** — `[ACC-extract-bind]`(a)+(b)+(c)
composed for the counterfactual family: roots committing the recommitted
partial folds, verified openings at `t ≥ d` columns, and the synthesized
family already equals the true perturbed transcripts — extraction included.
The column values enter through BINDING alone (`binding_columns`); nothing is
assumed about how the prover produced them. -/
theorem extractChain_committed_seam {Root' Op : Type*}
    (S : BindingCommitment Root' F ι Op) (dom : ι ↪ F) {d t : ℕ}
    (hdt : d ≤ t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    {γs γalt : ℕ → F} {f₀ : ι → F} {ms : Fin n → ι → F}
    {rts : ℕ → Root'} {cols : ℕ → Fin t → F} {ops : ℕ → Fin t → Op}
    (hne : ∀ k : Fin n, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin n, γs (k : ℕ) ≠ 0)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (hrts : ∀ c : ℕ, c ≤ n → rts c = S.commit (partialFold γs f₀ ms c))
    (hver : ∀ c : ℕ, c ≤ n → ∀ j,
      S.verifyOpen (rts c) (q j) (cols c j) (ops c j)) :
    extractChain γs γalt (flatFold γs f₀ ms)
        (seamCounterfactual (n := n) dom d q γs γalt (flatFold γs f₀ ms) cols)
      = List.ofFn ms :=
  extractChain_seamCounterfactual dom hdt hq hne hγ0 hms
    fun c hc j => binding_columns S (hrts c hc) (hver c hc) j

/-! ## The parameter window: where the seam and hiding can share one `t`

The seam needs `d ≤ t` (unique-decoding recovery); hiding needs the opening
map surjective FROM the mask space. For the WHOLE-code mask both hold at
exactly `t = d` — the coexistence point. For a CONSTRAINED mask space
(`constrainedMaskSpace`, the homogeneous masks that make the masked words
genuine witnesses) hiding needs `t + 1 ≤ d` — and `d ≤ t` REFUTES it at
every challenge. The same `t` opened columns cannot be unique-decodable and
constrained-mask-hiding: the quantitative core of the residual. -/

/-- **The coexistence point `t = d`, whole-code mask**: at exactly `d` opened
columns, masked-opening hiding (CITED: `rs_maskedOpeningHiding` at `t ≤ d`)
and exact erasure recovery of every committed codeword from those same
columns (CITED: `recoverFromColumns_sound` at `d ≤ t`) hold simultaneously.
The verifier's spot check simultaneously determines the masked word (the
extractor's food) and reveals nothing about the witness (the simulator's
promise) — no contradiction, because what it determines IS the masked word. -/
theorem seam_hiding_coexist_at_d (dom : ι ↪ F) {d : ℕ} {q : Fin d → ι}
    (hq : Function.Injective (dom ∘ q)) {γ : F} (hγ : γ ≠ 0) :
    MaskedOpeningHiding (reedSolomonCode dom d) q γ ∧
      ∀ f ∈ reedSolomonCode dom d,
        recoverFromColumns dom d q (fun j => f (q j)) = f :=
  ⟨rs_maskedOpeningHiding dom le_rfl hq hγ,
    fun f hf => recoverFromColumns_sound (f := f) dom le_rfl hq hf
      fun _ => rfl⟩

/-- **The conflict — recoverability refutes constrained-mask hiding, at EVERY
challenge**: once `d ≤ t` (the seam's regime), the constrained mask space
cannot hide. At `γ = 0` this is the landed γ-teeth; at `γ ≠ 0` the opened
tuple of the constant-`1` codeword is unreachable — a mask reaching it would
BE that codeword (`open_determines`, CITED) yet vanish at the constraint
point. So for `r ≥ 1` homogeneous constraints no `t` serves both games at
unique decoding: `t + 1 ≤ d` (hiding, `constrainedMask_hiding`) and `d ≤ t`
(recovery) are disjoint. The seam for constrained masks must leave unique
decoding — the sharpened residual's quantitative half. -/
theorem not_constrainedMask_hiding_of_recoverable (dom : ι ↪ F) {d : ℕ}
    (hd : 0 < d) (hdt : d ≤ t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) (pt : ι) (γ : F) :
    ¬ MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ := by
  intro H
  rcases eq_or_ne γ 0 with hγ | hγ
  · subst hγ
    exact not_maskedOpeningHiding_zero _ (lt_of_lt_of_le hd hdt) H
  · -- the constant-1 codeword's opened tuple is unreachable from the kernel
    have hone : (fun _ => (1 : F)) ∈ reedSolomonCode dom d :=
      mem_reedSolomonCode_iff.mpr ⟨Polynomial.C 1, by
        rw [Polynomial.degree_C one_ne_zero]
        exact_mod_cast hd, fun i => by simp⟩
    have hv : openSymbols q (fun _ => (1 : F))
        ∈ (fun g => openSymbols q (mask (0 : ι → F) γ g))
          '' (constrainedMaskSpace dom d pt) := by
      rw [H.sim_support_univ 0]
      trivial
    obtain ⟨g, hgM, hgv⟩ := hv
    have hgv' : openSymbols q (γ • g)
        = openSymbols q (fun _ => (1 : F)) := by
      have h1 : openSymbols q (mask (0 : ι → F) γ g)
          = openSymbols q (fun _ => (1 : F)) := hgv
      rwa [mask_apply, zero_add] at h1
    obtain ⟨hgRS, hgpt⟩ := mem_constrainedMaskSpace.mp hgM
    have heq : (γ • g : ι → F) = fun _ => (1 : F) :=
      open_determines dom hdt hq (Submodule.smul_mem _ γ hgRS) hone hgv'
    have hpt := congrFun heq pt
    rw [Pi.smul_apply, hgpt, smul_zero] at hpt
    exact zero_ne_one hpt

/-! ## The deployment bridge: the masked chain's partial fold IS `triFold`

`[ZK-RBR-triangular]` (the sibling flank's residual) asked for the bridge
identifying `Selvage/ZkTriangular.lean`'s abstract `triFold` with the
mask-augmented chain word. Here is its algebraic half: the masked chain's
`(k+1)`-st partial fold equals `triFold` at the PRODUCT schedule
`δ·η` (link challenge times mask challenge — the coefficient through which
round `k`'s mask actually enters the deployed word), with the real links'
weighted words absorbed into the word family — exactly the absorption
ZkTriangular's header declared legal through the ∀-witness quantifier. With
the bridge, `TriangularHiding` applies VERBATIM to the surface the seam
decodes: one data surface, both games. -/

/-- **The bridge equation**: the masked chain's `(k+1)`-st recommitted word
is `triFold` at the product schedule, word family = genesis-plus-weighted
real words. Round `k`'s mask coefficient in the deployed word is
`δ k · ηs k`. -/
theorem partialFold_eq_triFold (δ ηs : ℕ → F) (f₀ : ι → F)
    (ws gs : Fin n → ι → F) (k : Fin n) :
    partialFold δ f₀ (maskedWord ηs ws gs) ((k : ℕ) + 1)
      = triFold (fun m => δ m * ηs m)
          (fun j : Fin n => (if (j : ℕ) = 0 then f₀ else 0) + δ (j : ℕ) • ws j)
          gs k := by
  unfold partialFold triFold triPre
  rw [mask_apply]
  have hfilter : Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1)
      = Finset.univ.filter (fun j : Fin n => j ≤ k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hfilter]
  have hexp : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      δ (j : ℕ) • maskedWord ηs ws gs j
      = (∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
          δ (j : ℕ) • ws j)
        + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
            (δ (j : ℕ) * ηs (j : ℕ)) • gs j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [maskedWord_apply, smul_add, smul_smul]
  rw [hexp]
  have hz : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩ : Fin n)
      ∈ Finset.univ.filter (fun j : Fin n => j ≤ k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    exact Nat.zero_le _
  have hif : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      ((if (j : ℕ) = 0 then f₀ else 0) + δ (j : ℕ) • ws j)
      = f₀ + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
          δ (j : ℕ) • ws j := by
    rw [Finset.sum_add_distrib]
    congr 1
    have hcond : ∀ j : Fin n, (if (j : ℕ) = 0 then f₀ else 0)
        = if j = (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩ : Fin n)
            then f₀ else 0 := by
      intro j
      congr 1
      simp [Fin.ext_iff]
    rw [Finset.sum_congr rfl fun j _ => hcond j,
      Finset.sum_ite_eq' _ _ (fun _ => f₀), if_pos hz]
  have hsplit : Finset.univ.filter (fun j : Fin n => j ≤ k)
      = insert k (Finset.univ.filter (fun j : Fin n => j < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.le_def, Fin.lt_def, Fin.ext_iff]
    omega
  have hk : k ∉ Finset.univ.filter (fun j : Fin n => j < k) := by
    simp
  have hmask : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k),
      (δ (j : ℕ) * ηs (j : ℕ)) • gs j
      = (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k),
          (δ (j : ℕ) * ηs (j : ℕ)) • gs j)
        + (δ (k : ℕ) * ηs (k : ℕ)) • gs k := by
    rw [hsplit, Finset.sum_insert hk]
    abel
  rw [hif, hmask]
  abel

/-- **The deployed surface is the simulator's surface**: the masked chain's
ACTUAL opening schedule — round `k` opens the `(k+1)`-st recommitted partial
fold, the very words whose columns `seamCounterfactual` consumes — reaches
the full public tuple space over the mask draw, for EVERY genesis and every
witness family. Through the bridge this is `TriangularHiding.tri_sim_support`
(`triangularHiding_of_rounds`, CITED) at the product schedule: what the
extraction seam reads is exactly what the triangular simulator produces. -/
theorem masked_partialFold_hiding {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {δ ηs : ℕ → F}
    (H : ∀ k : Fin n,
      MaskedOpeningHiding (M k) (q k) (δ (k : ℕ) * ηs (k : ℕ)))
    (f₀ : ι → F) (ws : Fin n → ι → F) :
    (fun gs : Fin n → ι → F => fun k : Fin n =>
        openSymbols (q k)
          (partialFold δ f₀ (maskedWord ηs ws gs) ((k : ℕ) + 1)))
      '' jointMasks M = Set.univ := by
  have hbridge : (fun gs : Fin n → ι → F => fun k : Fin n =>
      openSymbols (q k)
        (partialFold δ f₀ (maskedWord ηs ws gs) ((k : ℕ) + 1)))
      = triOpen q (fun m => δ m * ηs m)
          (fun j : Fin n =>
            (if (j : ℕ) = 0 then f₀ else 0) + δ (j : ℕ) • ws j) := by
    funext gs k
    rw [triOpen_apply, partialFold_eq_triFold]
  rw [hbridge]
  exact (triangularHiding_of_rounds H).tri_sim_support _

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]`, the SAME instance every ZK file has carried:
the chain is `LCExample.goodChain`, the schedules `γbase = (1,1)` /
`γalt₂ = (2,2)`, both rounds' masks from the landed
`constrainedMaskSpace dom₅ 2 pt2` — witnesses `(0, oneWord)`, masks
`(lineOf 2 1, lineOf 4 2)` (both landed members, both nonzero available). -/

namespace ZkExtractionExample

open RSExample AccExample LCExample ZkHidingExample ZkArgumentExample
  AccExtractChainExample RbrZkExample ZkTriangularExample

/-- The keystone witness family: link 0's witness `0`, link 1's `oneWord` —
`goodChain`'s own honest witnesses. -/
def wsEx : Fin 2 → Fin 4 → ZMod 5 := ![0, oneWord]

/-- The keystone mask family: both draws from the landed constrained mask
space, both NONZERO (`maskWord_mem` / `lineOf42_mem`, cited below). -/
def gsEx : Fin 2 → Fin 4 → ZMod 5 := ![lineOf 2 1, lineOf 4 2]

/-- The keystone mask-alternate schedule `(3, 3)` — distinct from the honest
mask schedule `γbase = (1, 1)` at every round. -/
def ηalt₃ : ℕ → ZMod 5 := padSched ![3, 3]

theorem wsEx_sat : ∀ k, AccClaim.Satisfies (reedSolomonCode dom₅ 2)
    ((goodChain.get k).claim) (wsEx k) := by
  intro k
  fin_cases k
  · exact ⟨Submodule.zero_mem _, fun _ => map_zero q2⟩
  · exact ⟨oneWord_mem, fun _ => rfl⟩

theorem gsEx_mem : ∀ k, gsEx k ∈ reedSolomonCode dom₅ 2 := by
  intro k
  fin_cases k
  · exact lineOf_mem 2 1
  · exact lineOf_mem 4 2

/-- Both mask draws kill the whole channel — the homogeneity that keeps the
masked words genuine witnesses (`mask_sat_of_ker`'s premise). -/
theorem gsEx_ker : ∀ (k : Fin 2) (i : Fin 1),
    ((goodChain.get k).claim.weights i) (gsEx k) = 0 := by decide

/-- Both draws are in the SIMULATOR'S round mask space — the extractor's mask
object and the round simulator's mask object are one object, at both rounds
(`maskWord_mem` and `lineOf42_mem`, both landed, cited verbatim). -/
theorem gsEx_maskSpace : ∀ k : Fin 2,
    gsEx k ∈ constrainedMaskSpace dom₅ 2 pt2 := by
  intro k
  fin_cases k
  · exact maskWord_mem
  · exact lineOf42_mem

/-- The masked witness family, explicit. -/
def msEx : Fin 2 → Fin 4 → ZMod 5 := maskedWord γbase wsEx gsEx

theorem msEx_mem : ∀ k, msEx k ∈ reedSolomonCode dom₅ 2 := by
  intro k
  have h : msEx k = wsEx k + γbase (k : ℕ) • gsEx k := rfl
  rw [h]
  fin_cases k
  · exact Submodule.add_mem _ (Submodule.zero_mem _)
      (Submodule.smul_mem _ _ (lineOf_mem 2 1))
  · exact Submodule.add_mem _ oneWord_mem
      (Submodule.smul_mem _ _ (lineOf_mem 4 2))

/-! ### Satisfiable: masked-resolution extraction fires and computes -/

/-- **Masked knowledge soundness, fired**: on `goodChain`'s masked
transcripts the chain extractor returns EXACTLY the masked witness list, and
that list genuinely witnesses every link — all hypotheses discharged by
landed objects. -/
theorem masked_knowledge_F5 :
    extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (fun k : Fin goodChain.length =>
          flatFold (updSched γbase γalt₂ k) xWord msEx)
      = List.ofFn msEx ∧
    List.Forall₂
      (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain
      (extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (fun k : Fin goodChain.length =>
          flatFold (updSched γbase γalt₂ k) xWord msEx)) :=
  maskedChain_knowledge_sound (by decide) wsEx_sat gsEx_mem gsEx_ker

/-- **The masked extraction, computed**: the extracted list IS the masked
words — link 0's entry is the round-0 MASK itself (its witness was `0`), link
1's is `oneWord` shifted by the round-1 mask. Kernel computation; the
depth-2 companion of the landed `extractor_meets_simulator`. -/
theorem masked_extraction_computes :
    extractChain (ι := Fin 4) γbase γalt₂ (flatFold γbase xWord msEx)
        (fun k : Fin 2 => flatFold (updSched γbase γalt₂ k) xWord msEx)
      = [lineOf 2 1, oneWord + lineOf 4 2] := by decide

/-- **Masked completeness, fired**: the masked transcripts genuinely verify
the UNCHANGED aggregate at every schedule — the transcripts the extractor
just inverted are honest protocol messages, not synthetic data. -/
theorem masked_completeness_F5 (γs : ℕ → ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (aggregate linRoot γs genesis goodChain)
      (flatFold γs xWord msEx) :=
  masked_aggregate_satisfies linRoot goodChain_aligned γs genesis_satisfied
    wsEx_sat gsEx_mem gsEx_ker

/-! ### Satisfiable: the PAIR extraction fires and computes — given `ηalt` -/

/-- **`maskedChainExtraction`, inhabited**: with the mask-alternate schedule
supplied, the pair peel holds at depth 2 on the landed schedules. -/
theorem maskedChainExtraction_F5 :
    MaskedChainExtraction (ι := Fin 4) γbase γalt₂ γbase ηalt₃ 2 :=
  maskedChainExtraction_holds (by decide) (by decide) (by decide)

/-- **The pair peel, computed**: from the `2·2 + 1` transcripts the
mask-augmented extractor recovers BOTH rounds' `(witness, mask)` pairs on the
nose — `(0, lineOf 2 1)` and `(oneWord, lineOf 4 2)`. Kernel computation. -/
theorem pair_extraction_computes :
    ∀ k : Fin 2, extractMaskedPair γbase γalt₂ γbase ηalt₃
      (flatFold γbase xWord (maskedWord γbase wsEx gsEx))
      (fun j : Fin 2 =>
        flatFold (updSched γbase γalt₂ j) xWord (maskedWord γbase wsEx gsEx))
      (fun j : Fin 2 =>
        flatFold γbase xWord (maskedWord (updSched γbase ηalt₃ j) wsEx gsEx))
      k = (wsEx k, gsEx k) := by decide

/-! ### Teeth: the pair is invisible to every δ-schedule -/

/-- The ambiguity twin's mask family for the teeth: round 0's mask nonzero,
round 1's zero. -/
def gsAmb : Fin 2 → Fin 4 → ZMod 5 := ![lineOf 2 1, 0]

theorem gsAmb_mem : ∀ k, gsAmb k ∈ reedSolomonCode dom₅ 2 := by
  intro k
  fin_cases k
  · exact lineOf_mem 2 1
  · exact Submodule.zero_mem _

theorem gsAmb_ker : ∀ (k : Fin 2) (i : Fin 1),
    ((goodChain.get k).claim.weights i) (gsAmb k) = 0 := by decide

/-- **The general teeth, fired**: a second valid `(witness, mask)` family
with the SAME masked words — hence the same transcript at EVERY δ-schedule —
exists for the keystone instance; the honest schedule family can never peel
the pair. Premise inhabitation for `masked_pair_ambiguous`, with the landed
nonzero mask (`maskWord_ne_zero`) as the distinctness witness. -/
theorem pair_ambiguous_F5 :
    ∃ ws' gs' : Fin goodChain.length → Fin 4 → ZMod 5,
      (ws', gs') ≠ (wsEx, gsAmb) ∧
      (∀ k, AccClaim.Satisfies (reedSolomonCode dom₅ 2)
        ((goodChain.get k).claim) (ws' k)) ∧
      (∀ k, gs' k ∈ reedSolomonCode dom₅ 2 ∧
        ∀ i, ((goodChain.get k).claim.weights i) (gs' k) = 0) ∧
      maskedWord γbase ws' gs' = maskedWord γbase wsEx gsAmb ∧
      ∀ (δ : ℕ → ZMod 5) (f₀ : Fin 4 → ZMod 5),
        flatFold δ f₀ (maskedWord γbase ws' gs')
          = flatFold δ f₀ (maskedWord γbase wsEx gsAmb) :=
  masked_pair_ambiguous wsEx_sat gsAmb_mem gsAmb_ker
    (k₀ := ⟨0, by decide⟩) (by decide)

/-- **The ambiguity, computed**: the two DISTINCT pairs
`((0, oneWord), (lineOf 2 1, 0))` and `((lineOf 2 1, oneWord), (0, 0))`
produce IDENTICAL masked-word families — every transcript at every schedule,
every opened column coincides. The mask coordinate's second challenge is the
only tiebreaker, and the honest protocol never runs it. -/
theorem ambiguity_computed :
    maskedWord γbase ![lineOf 2 1, oneWord] ![0, 0]
        = maskedWord γbase wsEx gsAmb
      ∧ (![lineOf 2 1, oneWord], (![0, 0] : Fin 2 → Fin 4 → ZMod 5))
        ≠ (wsEx, gsAmb) := by
  constructor
  · decide
  · decide

/-! ### The seam, fired: one execution's columns furnish the counterfactuals -/

/-- **One-execution extraction, fired at `t = d = 2`**: the whole masked
witness list is extracted from the base transcript plus the opened columns of
the recommitted partial folds — the counterfactual transcripts synthesized by
`seamCounterfactual`, every hypothesis discharged (the columns are genuine by
construction here; the committed version is next). -/
theorem seam_extraction_F5 :
    extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (seamCounterfactual (n := 2) dom₅ 2 qPair γbase γalt₂
          (flatFold γbase xWord msEx)
          (fun c j => partialFold γbase xWord msEx c (qPair j)))
      = List.ofFn msEx :=
  extractChain_seamCounterfactual dom₅ le_rfl qPair_inj (by decide)
    (by decide) msEx_mem (fun _ _ _ => rfl)

/-- **The committed seam, fired**: same conclusion with the columns entering
ONLY through verified openings against the ideal binding commitment
(`CommitExample.S₅`) of each recommitted partial fold — the
`[ACC-extract-bind]` route, end to end on built objects. -/
theorem seam_extraction_committed_F5 :
    extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (seamCounterfactual (n := 2) dom₅ 2 qPair γbase γalt₂
          (flatFold γbase xWord msEx)
          (fun c j => partialFold γbase xWord msEx c (qPair j)))
      = List.ofFn msEx :=
  extractChain_committed_seam CommitExample.S₅ dom₅ le_rfl qPair_inj
    (by decide) (by decide) msEx_mem
    (rts := fun c => CommitExample.S₅.commit (partialFold γbase xWord msEx c))
    (ops := fun _ _ => ()) (fun _ _ => rfl)
    (fun c _ j => CommitExample.S₅.verifyOpen_commit
      (partialFold γbase xWord msEx c) (qPair j))

/-! ### The parameter window, all three regimes on one instance -/

/-- **The window, computed on F₅**: (1) at `t = 1` (`t + 1 = d`) the
constrained mask hides (landed `constrainedMask_hiding`) but one column
cannot determine a codeword (landed `recoverFromColumns_teeth` is exactly
this ambiguity at `qz = opened₁`); (2) at `t = 2 = d` the constrained mask
CANNOT hide, any challenge — recovery and constrained hiding never share a
`t`; (3) at `t = 2 = d` the WHOLE-code mask hides AND every codeword is
recovered from the same two columns — the unique coexistence point. -/
theorem window_F5 :
    MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz (1 : ZMod 5) ∧
    (∀ γ : ZMod 5,
      ¬ MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qPair γ) ∧
    (MaskedOpeningHiding (reedSolomonCode dom₅ 2) qPair (2 : ZMod 5) ∧
      ∀ f ∈ reedSolomonCode dom₅ 2,
        recoverFromColumns dom₅ 2 qPair (fun j => f (qPair j)) = f) :=
  ⟨constrainedMask_hiding dom₅ pt2 (by norm_num) qz_inj qz_ne_pt2 (by decide),
    fun γ => not_constrainedMask_hiding_of_recoverable dom₅ (by norm_num)
      le_rfl qPair_inj pt2 γ,
    seam_hiding_coexist_at_d dom₅ qPair_inj (by decide)⟩

/-- The `t = 1` recovery failure the window cites, landed: one opened column
is consistent with two distinct codewords (`ErasureExample`, verbatim). -/
example : ∃ u v : Fin 4 → ZMod 5, u ∈ reedSolomonCode dom₅ 2 ∧
    v ∈ reedSolomonCode dom₅ 2 ∧ u ≠ v ∧
    (fun j : Fin 1 => u (ErasureExample.opened₁ j))
      = fun j => v (ErasureExample.opened₁ j) :=
  ErasureExample.recoverFromColumns_teeth

/-! ### Game separation, fired -/

/-- **Coexistence on one instance**: multi-round zero-knowledge at the honest
mask schedule (landed `rbrZk_base`) and the mask-augmented pair extraction
(with its counterfactual schedules) hold together — the quantifier-position
separation, non-vacuous at depth 2. -/
theorem separation_F5 :
    RbrZeroKnowledge roundMask roundQuery γbase
      ∧ MaskedChainExtraction (ι := Fin 4) γbase γalt₂ γbase ηalt₃ 2 :=
  ⟨rbrZk_base, maskedChainExtraction_F5⟩

/-- **Teeth, both dials at once**: at the zero-round-0 mask schedule
(`γzeroSched`, landed) hiding is REFUTED while the pair extraction still
holds — the η-dial belongs to hiding alone. -/
theorem zero_mask_F5 :
    ¬ RbrZeroKnowledge roundMask roundQuery γzeroSched
      ∧ MaskedChainExtraction (ι := Fin 4) γbase γalt₂ γzeroSched γalt₂ 2 :=
  zero_mask_kills_hiding_not_pair 0 (by decide) (by norm_num) (by decide)
    (by decide) (by decide)

/-- **The mask diagonal, fired**: with one mask schedule the recovered mask
is `0` — never the landed nonzero draws `gsEx` — while hiding stands. -/
theorem mask_diagonal_F5 :
    (∀ (h₀ : Fin 4 → ZMod 5) (hlink hmask : Fin 2 → Fin 4 → ZMod 5)
        (k : Fin 2),
        (extractMaskedPair γbase γalt₂ γbase γbase h₀ hlink hmask k).2 = 0)
      ∧ RbrZeroKnowledge roundMask roundQuery γbase :=
  mask_diagonal_kills_pair_not_hiding hiding_rounds

/-! ### The deployed surface, fired -/

/-- **The deployed opening surface is witness-free, fired**: for EVERY
genesis and EVERY witness family, the opened tuples of the masked chain's
recommitted partial folds — the exact columns `seam_extraction_F5` consumed —
sweep the full public space over the mask draw. `masked_partialFold_hiding`
through the bridge, per-round hiding at the product challenge `1·1 = 1`
(landed `constrainedMask_hiding`). -/
theorem deployed_surface_F5 (f₀ : Fin 4 → ZMod 5)
    (ws : Fin 2 → Fin 4 → ZMod 5) :
    (fun gs : Fin 2 → Fin 4 → ZMod 5 => fun k : Fin 2 =>
        openSymbols (roundQuery k)
          (partialFold γbase f₀ (maskedWord γbase ws gs) ((k : ℕ) + 1)))
      '' jointMasks roundMask = Set.univ :=
  masked_partialFold_hiding
    (fun k => constrainedMask_hiding dom₅ pt2 (by norm_num) qz_inj qz_ne_pt2
      (by fin_cases k <;> decide)) f₀ ws

end ZkExtractionExample

/-! ## Residual obligation — prose, not a stub

**`[ZK-RBR-extract]`** — the sharpened remainder of `[ZK-RBR-interleave]`'s
missing lemma 2, after this file. The lemma as POSED is resolved: the
mask-coordinate counterfactuals provably cannot be furnished by the honest
execution (`masked_pair_ambiguous` — no function of any δ-schedule family
sees the pair), provably need not be (`maskedChain_knowledge_sound` — masked
words are witnesses, extracted exactly from the δ-family the seam furnishes),
and provably suffice where granted (`extractMaskedPair_sound`); the
quantifier-position confinement is not asserted but exhibited — everything
the extraction game reads is proved simulator-distributed
(`extraction_surface_witness_free`, `mask_image_homTwin`,
`masked_partialFold_hiding`), so the counterfactuals live only in the
extraction game's ∀ and never reach the ZK distinguisher. What remains is
TWO lemmas, named precisely:

* **Open lemma A — the sub-unique-decoding seam.** `seamCounterfactual_sound`
  recovers each round increment from `t ≥ d` opened columns
  (`recoverFromColumns_sound`), and `not_constrainedMask_hiding_of_recoverable`
  proves that regime is INCOMPATIBLE with constrained-mask hiding
  (`t + r ≤ d`) — the homogeneous masks that make masked words witnesses.
  So the deployed constrained-mask protocol needs the increment recovered
  from `t ≤ d − r` columns per round: erasure correction inside the MUTUAL
  AGREEMENT SET across the fold family (WARP App. B's actual route), not
  per-word unique decoding. The open lemma: extend `recoverFromColumns` to
  that regime and re-prove `seamCounterfactual_sound` there. It composes:
  `Selvage/CorrelatedAgreement.lean`'s mutual CA (landed at the UD radius),
  `[ERASURE-list]` + `[OOD-pin-proximity]` (the named list-regime seams,
  unchanged), and this file's `seamCounterfactual` / `extractChain_flatFold`
  shapes, which are regime-independent and carry over verbatim. Every other
  step of the masked-resolution route is closed relative to this lemma.
  (The whole-code alternative — hiding AND the UD seam at exactly `t = d`,
  `seam_hiding_coexist_at_d` — trades the conflict away, but then the mask
  shifts the folded targets: the mask claims must ride as links carrying
  their own prover-supplied targets, and extracting THOSE links' witnesses
  is pair-resolution extraction, which `masked_pair_ambiguous` bars from
  the honest execution. The two horns meet in lemma A; there is no third
  route at this file's resolution.)

* **Open lemma B — the masked-resolution game packaging.** The
  `Reduction`/`RbrKnowledgeSoundness` instance owed since
  `[ACC-sound-rbr-game]`, now with its extraction target FIXED by this
  file: the game's `extract` field must output the MASKED words —
  `extractChain` composed with `seamCounterfactual` — not `(witness, mask)`
  pairs. A straightline FS extractor sees ONE mask challenge per
  commitment (re-querying the oracle at the same commitment returns the
  same challenge; a different commitment is a different mask), so the pair
  target would demand exactly the counterfactual `masked_pair_ambiguous`
  rules out; the masked target is met by this file's theorems with the
  landed `accRbrError` as the round price and `RbrZeroKnowledge` as the
  coexisting ZK half (`maskedExtraction_coexists_hiding` is its
  model-level shape). Root attribution rides the same choice: the masked
  words attach to the RECOMMITTED roots — the only words the ZK schedule
  may commit and open, since opening bare witness or mask words refutes
  hiding (`window_F5`'s middle regime is the `t`-side of that fact). This
  file makes "knowledge of the masked words, attributed to the recommitted
  roots" the theorem-backed resolution, not a concession; packaging it into
  the SR/FS game object is the open composition, inherited from
  `[ACC-sound-rbr-game]` and `Selvage/RbrZeroKnowledge.lean`'s third bullet.

* **What is NOT at risk.** Every citation is an unconditional landed
  theorem: `extractChain_sound`, `extractPair_sound` (through
  `extractPair_flatFold_snd`), `aggregate_satisfies`,
  `recoverFromColumns_sound` / `committed_word_recovered`'s binding step,
  `mask_bijOn`, `rbrZeroKnowledge_of_rounds`, `triangularHiding_of_rounds`,
  `constrainedMask_hiding`, `rs_maskedOpeningHiding`, `open_determines`.
  The negative results (`masked_pair_ambiguous`,
  `not_constrainedMask_hiding_of_recoverable`,
  `extractMaskedPair_mask_diagonal`) are proofs, not conjectures — the
  frontier is exactly lemmas A and B, and nothing here narrows quietly.

## Ledger

* `maskedWord` / `flatFold` / `foldWords_ofFn` / `flatFold_updSched` /
  `flatFold_congr_single` — DEFINED/PROVED: the masked flat chain word,
  bridged to the landed `foldWords`; one-coordinate perturbation algebra.
* `extractPair_flatFold_snd` / `extractChain_flatFold` — PROVED: the chain
  extractor inverts the honest flat fold EXACTLY, arbitrary depth.
* `mask_sat_of_ker` / `maskedWord_forall₂` / `masked_aggregate_satisfies` —
  PROVED: homogeneous masks preserve the claim chain; masked completeness
  on the real aggregate (`aggregate_satisfies` cited).
* `maskedChain_knowledge_sound` — PROVED: masked-resolution knowledge
  soundness from the δ-family alone — exact extraction + `Forall₂`
  certification; adversarial form is the landed `extractChain_sound`
  verbatim (claim chain unchanged).
* `extracted_openings_are_jointOpen` (`rfl`) /
  `extraction_surface_witness_free` / `homTwin` / `mask_image_homTwin` /
  `extracted_word_witness_free` — PROVED: everything extraction reveals is
  the simulator's object (openings = `jointOpen`, full word uniform on the
  claim's public satisfying set via `mask_bijOn`).
* `extractMaskedPair` (+ `_sound`, `_mask_diagonal`) /
  `MaskedChainExtraction` (+ `_holds`) — DEFINED/PROVED: the pair peel,
  exact given the mask counterfactual; collapses at the mask diagonal; the
  statement's type carries both counterfactual schedules.
* `masked_pair_ambiguous` — PROVED: the pair is invisible to EVERY
  δ-schedule — the mask counterfactual is not a function of the honest
  execution; `single_fold_ambiguous` lifted to the masked chain at full
  quantifier strength.
* `maskedExtraction_coexists_hiding` / `zero_mask_kills_hiding_not_pair` /
  `mask_diagonal_kills_pair_not_hiding` — PROVED: game separation by
  quantifier position, teeth both directions.
* `partialFold` (+ `_zero`, `_succ`, `_last`) / `seamCounterfactual`
  (+ `_sound`) / `extractChain_seamCounterfactual` / `binding_columns` /
  `extractChain_committed_seam` — DEFINED/PROVED: the one-execution seam —
  perturbed transcripts synthesized from opened columns of the recommitted
  partial folds, through binding, extraction included (UD regime, honest
  boundary).
* `seam_hiding_coexist_at_d` / `not_constrainedMask_hiding_of_recoverable`
  — PROVED: the parameter window — whole-code coexistence exactly at
  `t = d`; recovery refutes constrained hiding at every challenge.
* `partialFold_eq_triFold` / `masked_partialFold_hiding` — PROVED: the
  deployment bridge to `triFold` at the product schedule
  (`[ZK-RBR-triangular]`'s algebraic half) + the deployed surface is the
  triangular simulator's surface.
* Keystones — `masked_knowledge_F5`, `masked_extraction_computes`,
  `masked_completeness_F5`, `maskedChainExtraction_F5`,
  `pair_extraction_computes`, `pair_ambiguous_F5`, `ambiguity_computed`,
  `seam_extraction_F5`, `seam_extraction_committed_F5`, `window_F5`,
  `separation_F5`, `zero_mask_F5`, `mask_diagonal_F5`,
  `deployed_surface_F5` — all fired/computed on the landed F₅ instance.
* Residual — `[ZK-RBR-extract]` (prose above): open lemma A (the
  sub-unique-decoding seam via mutual CA) + open lemma B (the
  masked-resolution game packaging); the counterfactual question as posed
  is resolved, with the confinement exhibited, not asserted.

`#print axioms` on `extractChain_flatFold`, `maskedChain_knowledge_sound`,
`masked_aggregate_satisfies`, `extractMaskedPair_sound`,
`maskedChainExtraction_holds`, `masked_pair_ambiguous`,
`seamCounterfactual_sound`, `extractChain_committed_seam`,
`partialFold_eq_triFold`, `masked_partialFold_hiding`,
`not_constrainedMask_hiding_of_recoverable`, `mask_image_homTwin`,
`ZkExtractionExample.pair_extraction_computes`,
`ZkExtractionExample.pair_ambiguous_F5`,
`ZkExtractionExample.seam_extraction_committed_F5`,
`ZkExtractionExample.window_F5`, `ZkExtractionExample.deployed_surface_F5`,
`ZkExtractionExample.zero_mask_F5`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
