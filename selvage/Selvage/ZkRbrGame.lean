/-
# Selvage.ZkRbrGame — the full ZK-argument RBR game, ASSEMBLED.

`[ACC-sound-rbr-game]` (`Selvage/AccSoundRbr.lean`) owed the game object whose
`extract` field the naive backward extractor could not fill;
`Selvage/ZkExtraction.lean` FIXED the extract field (the extractor outputs the
MASKED words, attributed to the recommitted roots, exact at arbitrary depth,
with the counterfactual transcripts synthesized from ONE execution's opened
columns) and `Selvage/RbrZeroKnowledge.lean` supplied the simulator vocabulary.
This file is the CAPSTONE assembly: one structure, `ZkRbrGame`, carrying — on
ONE parameter tuple `(C, foldRoot, A₀, ch, M, q, γs, γalt, ηs, ηalt)` — a
straightline non-interactive argument that is simultaneously

* **knowledge-sound** (`knowledge_sound` — the adversarial chain extraction,
  `extractChain_sound`'s conclusion verbatim; `masked_exact` — the extractor
  inverts the honest masked chain word EXACTLY; `pair_extraction` — the
  mask-augmented `2n + 1`-transcript peel, `MaskedChainExtraction`, both
  counterfactual schedules IN ITS TYPE; `straightline_seam` — the
  counterfactual family is a FUNCTION of one execution's committed columns,
  through binding, so the extractor is straightline);
* **zero-knowledge** (`zero_knowledge` — `RbrZeroKnowledge M q ηs`, the
  composed chain simulator; its type mentions NO `γalt`, NO `ηalt`, no
  transcript, no witness — the honest verifier runs one schedule);
* **priced on Selvage's proven per-round scale** (`round_error_prox` — the
  δ-proximity fold bound `err⋆(δ) + 1/|F| = accRbrError`, `accSound_rbr`
  verbatim with the mutual-CA package internal; `round_error_exact` — the
  unconditional exact-word `1/|F|`, `accSound_rbr_exact` verbatim);
* **FS-composed** (`fs_composed` — any WARP-Def-4.2 instance whose per-round
  error is bounded by `accRbrError` compiles non-interactively, straightline,
  at the `(t + k)·accRbrError` grinding factor: `accFsSound` verbatim, riding
  `fsKeystone_proved` which is PROVED unconditionally).

**The quantifier separation `[ZK-RBR-*]` fought for is VISIBLE in the field
types.** `γalt` occurs only in the four knowledge fields; `ηalt` occurs only
in `pair_extraction`; `zero_knowledge`'s type carries neither and cannot —
extraction runs against the cheating prover with the adversarial `2n + 1`
family, simulation faces the honest prover's single schedule, and
`masked_pair_ambiguous` (teeth, fired below) proves the mask counterfactual
is NOT a function of the honest execution: what extraction needs beyond the
honest data is exactly what ZK withholds, and what it can get from the honest
data (`masked words`) is exactly what the simulator already publishes.

`zkRbrGame_holds` inhabits the structure by CITATION ONLY — every field is a
landed theorem (`masked_aggregate_satisfies`, `extractChain_sound`,
`extractChain_flatFold`, `maskedChainExtraction_holds`,
`extractChain_committed_seam`, `rbrZeroKnowledge_of_rounds`, `accSound_rbr`,
`accSound_rbr_exact`, `accFsSound`); nothing is re-derived. The audit
transparency is the same as `RbrZeroKnowledge`'s: the structure's value is
carrying the COMPOSED object (the thing `[ZK-RBR-game]` asked to even state),
one game on one tuple, not a new inequality.

`selvage_zk_argument` is the headline: Selvage has a straightline non-interactive
zero-knowledge argument of knowledge for the accumulated claim — every
aligned chain with genuinely two-point challenge dials and hiding rounds
carries the full game, and the Fiat–Shamir carrier holds unconditionally
(`FsOfRbrSound`, no seam). MODULO, stated plainly:

* **the cryptographic floor** — `[FS-ROM]` (the deployed sponge realizes the
  lazy-sampling handler; `Selvage/FiatShamir.lean`), `[COMMIT-CR]` (the deployed
  Merkle scheme realizes `BindingCommitment`; `Selvage/Commitment.lean`), and
  the standing `hPG` (the macroscopic-δ RS proximity gap, WHIR Thm 4.8 /
  BCIKS, which feeds the mutual-CA package `round_error_prox` consumes;
  `Selvage/ReedSolomon.lean` — consumed as a hypothesis, never claimed);
* **the sub-UD seam** — `[ZK-RBR-extract]` open lemma A (`Selvage/ZkExtraction.lean`):
  the one-execution seam recovers round increments at `t ≥ d` opened columns,
  which coexists with WHOLE-CODE mask hiding at exactly `t = d` but is
  incompatible with CONSTRAINED-mask hiding (`t + r ≤ d`) — the deployed
  constrained-mask protocol needs erasure correction inside the mutual
  agreement set, below unique decoding;
* **`[ZK-RBR-game-resid]`** (this file's honest residual, prose at the
  bottom): the WARP-Def-4.2-NATIVE instance — the literal
  `Reduction`/`KStateFn`/`extract`/`RbrKnowledgeSoundness` quadruple for the
  accumulator chain that would let `fs_composed` fire ON the accumulator
  itself rather than on a supplied Def-4.2 instance. `ZkExtraction` fixed
  what BLOCKED it (the extract target and the counterfactual furnishing);
  what remains is the Def-4.1/4.2 transcript plumbing and the per-round
  `∃ w`-event refinement — named precisely below, not silently absorbed.

**Keystones** (F₅, every landed instance REUSED): the game FIRES whole on
`LCExample.goodChain` (`zkRbrGame_F5` — all nine fields from
`zkRbrGame_holds`, every hypothesis discharged by landed witnesses); each
field fired on the shared data (completeness, adversarial knowledge, exact
masked inversion + its computed value, the pair peel on the nose, the chain
simulator's full support, the committed one-execution seam, the exact-word
round price, FS on a genuine Def-4.2 instance at the `accRbrError` scale);
the separation teeth BOTH directions (the pair invisible to every δ-schedule
on the game's own witness data; the η-dial kills hiding never the peel; the
mask diagonal kills the peel never hiding; the γ-dial kills hiding never
extraction); the one-price-scale coincidence (`zkRbrError = accRbrError`
exact-word) and the attained bound. No `sorry`, no `Prop := True`.
-/
import Selvage.Rbr
import Selvage.FiatShamir
import Selvage.AccSoundRbr
import Selvage.RbrZeroKnowledge
import Selvage.ZkExtraction

namespace Minidregg.Selvage

/- `F : Type` (not `Type*`): matches the chain-extraction and Rbr measure
universes (`Selvage/ZkExtraction.lean`, `Selvage/AccSoundRbr.lean`), so `accFsSound`
can consume `F` as a challenge alphabet directly. The finite-domain instances
(`Fintype ι`, `DecidableEq ι`, `Nonempty ι`, `DecidableEq F`) are consumed by
the PROOFS of the round-error fields (`accSound_rbr`'s mutual-CA counting);
they are the deployed regime (finite field, finite evaluation domain). -/
variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {t : ℕ} {r : ℕ}

/-! ## `ZkRbrGame` — the assembled game object -/

/-- **`ZkRbrGame`** — the full ZK-argument RBR game for the depth-`n`
accumulation chain: genesis `A₀`, chain `ch`, per-round mask spaces `M` and
query selections `q`, link-challenge schedules `γs`/`γalt` (base/alternate),
mask-challenge schedules `ηs`/`ηalt` (honest/alternate). One structure, one
parameter tuple, nine obligations:

* `completeness` — the masked prover's word at the base schedule genuinely
  witnesses the aggregate of the UNCHANGED chain (homogeneous masks are
  invisible to the claim channel).
* `knowledge_sound` — ADVERSARIAL chain extraction: from ANY words verifying
  the aggregate at the base and every `k`-perturbed schedule, `extractChain`
  returns built witnesses of every link. Sees `γalt`; masked transcripts are
  a special case (the claim chain never moved).
* `masked_exact` — on the honest masked transcripts the extractor returns
  EXACTLY the masked word list, arbitrary depth: what extraction yields is
  the simulator's own object, on the nose.
* `pair_extraction` — the mask-augmented `2n + 1`-transcript peel recovers
  every round's `(witness, mask)` pair. The ONLY field whose type carries
  `ηalt` — the counterfactual mask schedule the honest protocol never runs
  (`masked_pair_ambiguous` proves it cannot be synthesized from honest data).
* `straightline_seam` — the δ-counterfactual family is a FUNCTION of one
  execution: base transcript + verified openings of the recommitted partial
  folds against binding roots synthesize the perturbed transcripts, and
  extraction goes through (unique-decoding regime `d ≤ t` — the honest
  boundary; below it is `[ZK-RBR-extract]` lemma A).
* `zero_knowledge` — the composed chain simulator at the honest mask
  schedule: `RbrZeroKnowledge M q ηs`. NO `γalt`, NO `ηalt`, no transcript,
  no witness in the type — the quantifier separation, load-bearing.
* `round_error_prox` — the per-round δ-proximity price on the game's own
  fold channel: `accRbrError F errstar δ = err⋆(δ) + 1/|F|`, the WHIR
  Constr. 7.4 bound at unique decoding, mutual-CA package internal.
* `round_error_exact` — the unconditional exact-word price `1/|F|`
  (`accRbrError` at `errstar ≡ 0`), attained (keystones).
* `fs_composed` — the non-interactive carrier: ANY `Reduction` with a
  Def-4.2 `RbrKnowledgeSoundness` instance whose per-round error is bounded
  by `accRbrError` on a statement set compiles by Fiat–Shamir to a
  STRAIGHTLINE knowledge-sound argument at `(t + k)·accRbrError` — the
  grinding factor, `fsKeystone_proved`'s proved route. (Supplying the
  accumulator's OWN Def-4.2 instance is `[ZK-RBR-game-resid]`, below.)

Audit transparency: `zkRbrGame_holds` shows every field is a landed theorem
given the dial hypotheses — the structure adds no new mathematics; its value
is the ONE OBJECT with the separation visible in its field types. -/
structure ZkRbrGame [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (C : Submodule F (ι → F))
    (foldRoot : Root → F → Root → Root) (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (M : Fin ch.length → Submodule F (ι → F))
    (q : Fin ch.length → Fin t → ι) (γs γalt ηs ηalt : ℕ → F) : Prop where
  /-- Masked completeness on the REAL aggregate: homogeneous masks are
  channel-invisible, so the masked chain word witnesses the unchanged
  aggregate at the base schedule. -/
  completeness : ∀ {f₀ : ι → F} {ws gs : Fin ch.length → ι → F},
    AccClaim.Satisfies C A₀ f₀ →
    (∀ k, AccClaim.Satisfies C (ch.get k).claim (ws k)) →
    (∀ k, gs k ∈ C) →
    (∀ k i, (ch.get k).claim.weights i (gs k) = 0) →
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch)
      (flatFold γs f₀ (maskedWord ηs ws gs))
  /-- Adversarial chain knowledge soundness: verifying words at the flat
  `n + 1`-schedule family yield BUILT witnesses of every link. -/
  knowledge_sound : ∀ {h₀ : ι → F} {hs : Fin ch.length → ι → F},
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀ →
    (∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) →
    List.Forall₂
      (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w) ch
      (extractChain γs γalt h₀ hs)
  /-- Exactness on honest masked transcripts: the extractor's output IS the
  masked word list — the simulator's own leakage object. -/
  masked_exact : ∀ (f₀ : ι → F) (ws gs : Fin ch.length → ι → F),
    extractChain γs γalt (flatFold γs f₀ (maskedWord ηs ws gs))
        (fun k : Fin ch.length =>
          flatFold (updSched γs γalt k) f₀ (maskedWord ηs ws gs))
      = List.ofFn (maskedWord ηs ws gs)
  /-- The mask-augmented pair peel over the adversarial `2n + 1` family —
  the only field whose type carries the counterfactual mask schedule. -/
  pair_extraction : MaskedChainExtraction (ι := ι) γs γalt ηs ηalt ch.length
  /-- Straightline: the counterfactual transcripts are a function of ONE
  execution — binding roots + verified openings of the recommitted partial
  folds synthesize them, and extraction goes through (`d ≤ tS` seam). -/
  straightline_seam : ∀ {Root' Op : Type} (S : BindingCommitment Root' F ι Op)
      (dom : ι ↪ F) {d tS : ℕ}, d ≤ tS → ∀ {qS : Fin tS → ι},
      Function.Injective (dom ∘ qS) →
      ∀ {f₀ : ι → F} {ws gs : Fin ch.length → ι → F} {rts : ℕ → Root'}
        {cols : ℕ → Fin tS → F} {ops : ℕ → Fin tS → Op},
      (∀ k, maskedWord ηs ws gs k ∈ reedSolomonCode dom d) →
      (∀ c : ℕ, c ≤ ch.length →
        rts c = S.commit (partialFold γs f₀ (maskedWord ηs ws gs) c)) →
      (∀ c : ℕ, c ≤ ch.length → ∀ j,
        S.verifyOpen (rts c) (qS j) (cols c j) (ops c j)) →
      extractChain γs γalt (flatFold γs f₀ (maskedWord ηs ws gs))
          (seamCounterfactual (n := ch.length) dom d qS γs γalt
            (flatFold γs f₀ (maskedWord ηs ws gs)) cols)
        = List.ofFn (maskedWord ηs ws gs)
  /-- Zero-knowledge at the honest mask schedule: the composed chain
  simulator. Neither counterfactual schedule occurs in this type. -/
  zero_knowledge : RbrZeroKnowledge M q ηs
  /-- The per-round δ-proximity price on the game's own fold channel:
  `accRbrError = err⋆(δ) + 1/|F|`, mutual-CA package internal (its
  inhabitation at macroscopic δ over RS is the standing `hPG` floor). -/
  round_error_prox : ∀ {A B : AccClaim Root F ι r} {f g : ι → F}
      {δ dC Bstar : ℝ} {errstar : ℝ → ℝ},
    (∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v) →
    HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar →
    0 < δ → δ < 1 - Bstar → δ < dC / 2 →
    (∀ u ∈ C, ∀ v ∈ C, relDist f u ≤ δ → relDist g v ≤ δ →
      ∃ i, ¬(A.weights i u = A.targets i ∧ A.weights i v = B.targets i)) →
    uniformProb F (fun γ => ∃ w, relDist (f + γ • g) w ≤ δ ∧
        AccClaim.Satisfies C (foldClaims foldRoot A B γ) w)
      ≤ accRbrError F errstar δ
  /-- The unconditional exact-word per-round price `1/|F|`. -/
  round_error_exact : ∀ {A B : AccClaim Root F ι r} {f g : ι → F},
    (∃ i, ¬(A.weights i f = A.targets i ∧ A.weights i g = B.targets i)) →
    ∀ δ : ℝ,
      uniformProb F (fun γ =>
          AccClaim.Satisfies C (foldClaims foldRoot A B γ) (f + γ • g))
        ≤ accRbrError F (fun _ => 0) δ
  /-- The non-interactive carrier at the game's error scale: FS of any
  Def-4.2 instance bounded by `accRbrError` is straightline knowledge-sound
  at the `(t + k)·accRbrError` grinding factor. -/
  fs_composed : ∀ (red : Reduction) (rbr : RbrKnowledgeSoundness red)
      (Z : Set (Stmt red)) (errstar : ℝ → ℝ),
    (∀ δ ∈ Set.Ioo (0 : ℝ) red.δstar, 0 ≤ errstar δ) →
    (∀ (i : Fin red.k) (st : Stmt red), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) red.δstar,
        rbr.err i st δ ≤ accRbrError F errstar δ) →
    FsStraightlineKnowledgeSoundness red Z
      (fun _s b δ => ((b : ℝ) + (red.k : ℝ)) * accRbrError F errstar δ)

/-! ## `zkRbrGame_holds` — the game holds, by citation -/

/-- **The game instance holds** — pure composition, nothing re-derived. An
aligned chain whose challenge dials are genuinely two-point at every round
(`γs ≠ γalt` linkwise, `γs ≠ 0`, `ηs ≠ ηalt` linkwise) and whose rounds hide
(`MaskedOpeningHiding` per round at the honest mask challenge) carries the
FULL ZK-argument RBR game. Field-by-field citation ledger:

* `completeness` ← `masked_aggregate_satisfies` (`Selvage/ZkExtraction.lean`);
* `knowledge_sound` ← `extractChain_sound` (`Selvage/AccExtractChain.lean` —
  `[ACC-sound-rbr-game]`'s named chain-level realizer);
* `masked_exact` ← `extractChain_flatFold` (`Selvage/ZkExtraction.lean`);
* `pair_extraction` ← `maskedChainExtraction_holds` /
  `extractMaskedPair_sound` (`Selvage/ZkExtraction.lean` — the fixed extract
  field);
* `straightline_seam` ← `extractChain_committed_seam`
  (`Selvage/ZkExtraction.lean` — `[ACC-extract-bind]` composed end to end);
* `zero_knowledge` ← `rbrZeroKnowledge_of_rounds`
  (`Selvage/RbrZeroKnowledge.lean`);
* `round_error_prox` ← `accSound_rbr` (`Selvage/AccSoundRbr.lean`);
* `round_error_exact` ← `accSound_rbr_exact` (`Selvage/AccSoundRbr.lean`);
* `fs_composed` ← `accFsSound` (`Selvage/AccSoundRbr.lean`, riding
  `fsKeystone_proved`, `Selvage/FiatShamir.lean`, PROVED unconditionally).

The hypotheses are exactly the dials the teeth prove load-bearing: drop
`hγ`/`hγ0` and extraction collapses (diagonal teeth); drop `hη` and the pair
peel collapses (mask-diagonal teeth); drop `hZK` and zero-knowledge is
refutable (γ-teeth). -/
theorem zkRbrGame_holds [Fintype F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A₀ : AccClaim Root F ι r}
    {ch : Chain Root F ι r} {M : Fin ch.length → Submodule F (ι → F)}
    {q : Fin ch.length → Fin t → ι} {γs γalt ηs ηalt : ℕ → F}
    (halign : Aligned A₀ ch)
    (hγ : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hγ0 : ∀ k : Fin ch.length, γs (k : ℕ) ≠ 0)
    (hη : ∀ k : Fin ch.length, ηs (k : ℕ) ≠ ηalt (k : ℕ))
    (hZK : ∀ k : Fin ch.length,
      MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ))) :
    ZkRbrGame C foldRoot A₀ ch M q γs γalt ηs ηalt where
  completeness hf₀ hws hgsC hker :=
    masked_aggregate_satisfies foldRoot halign γs hf₀ hws hgsC hker
  knowledge_sound hbase hpert :=
    extractChain_sound foldRoot halign hγ hbase hpert
  masked_exact f₀ ws gs := extractChain_flatFold hγ f₀ (maskedWord ηs ws gs)
  pair_extraction := maskedChainExtraction_holds hγ hγ0 hη
  straightline_seam := by
    intro Root' Op S dom d tS hdt qS hqS f₀ ws gs rts cols ops hms hrts hver
    exact extractChain_committed_seam S dom hdt hqS hγ hγ0 hms hrts hver
  zero_knowledge := rbrZeroKnowledge_of_rounds hZK
  round_error_prox hdC hMCA hδ0 hδB hδC hfar :=
    accSound_rbr foldRoot hdC hMCA hδ0 hδB hδC hfar
  round_error_exact hviol δ := accSound_rbr_exact foldRoot hviol δ
  fs_composed red rbr Z errstar hnn hb := accFsSound red rbr Z F errstar hnn hb

/-! ## `selvage_zk_argument` — the headline -/

/-- **The ZK completion statement.** Selvage has a straightline non-interactive
zero-knowledge argument of knowledge for the accumulated claim:

* EVERY aligned accumulation chain with genuinely two-point challenge dials
  and per-round mask hiding carries the full `ZkRbrGame` — knowledge-sound
  (the chain extractor, exact on masked transcripts, straightline through the
  committed-column seam, pair-complete over the adversarial family),
  zero-knowledge (the composed chain simulator, counterfactual-free type),
  priced at `accRbrError` per round;
* the Fiat–Shamir carrier holds UNCONDITIONALLY (`FsOfRbrSound` — FS of any
  RBR-sound reduction is straightline knowledge-sound at `(t + k)·ε_rbr`;
  `fsKeystone_proved`, no remaining seam).

MODULO, named — this is the covered scope, in the same sentence as the claim:
the cryptographic floor `[FS-ROM]` (deployed sponge ↦ the lazy handler),
`[COMMIT-CR]` (deployed Merkle ↦ `BindingCommitment`), and the standing `hPG`
(macroscopic-δ RS proximity gap feeding `round_error_prox`'s mutual-CA
package); the sub-unique-decoding seam `[ZK-RBR-extract]` lemma A (the
constrained-mask deployment needs the seam below `t ≥ d`); and
`[ZK-RBR-game-resid]` (the WARP-Def-4.2-native instance for the accumulator —
prose below). Proven parameters only; the numbers quoted are the pessimistic
proved bounds `err⋆(δ) + 1/|F|` per round and `(t + k)·ε` after FS. -/
theorem selvage_zk_argument [Fintype F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι] [Nonempty ι] :
    (∀ (C : Submodule F (ι → F)) (foldRoot : Root → F → Root → Root)
        (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
        (M : Fin ch.length → Submodule F (ι → F))
        (q : Fin ch.length → Fin t → ι) (γs γalt ηs ηalt : ℕ → F),
        Aligned A₀ ch →
        (∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ)) →
        (∀ k : Fin ch.length, γs (k : ℕ) ≠ 0) →
        (∀ k : Fin ch.length, ηs (k : ℕ) ≠ ηalt (k : ℕ)) →
        (∀ k : Fin ch.length, MaskedOpeningHiding (M k) (q k) (ηs (k : ℕ))) →
        ZkRbrGame C foldRoot A₀ ch M q γs γalt ηs ηalt) ∧
      FsOfRbrSound :=
  ⟨fun _C foldRoot _A₀ _ch _M _q _γs _γalt _ηs _ηalt
      halign hγ hγ0 hη hZK =>
        zkRbrGame_holds foldRoot halign hγ hγ0 hη hZK,
    fsKeystone_proved.sound⟩

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]`, every object REUSED: the chain is
`LCExample.goodChain`, schedules `γbase = (1,1)` / `γalt₂ = (2,2)` (links)
and `γbase` / `ηalt₃ = (3,3)` (masks), both rounds' masks from the landed
`constrainedMaskSpace dom₅ 2 pt2` opened at `qz` — the SAME instance
`RbrZkExample` and `ZkExtractionExample` carried, now firing the assembled
game whole. -/

namespace ZkRbrGameExample

open RSExample AccExample LCExample ZkHidingExample ZkArgumentExample
  AccExtractChainExample RbrZkExample ZkExtractionExample AccSoundRbrExample

/-- **THE INSTANCE — satisfiable**: the full ZK-argument RBR game fires on
the landed F₅ chain, all nine fields, every `zkRbrGame_holds` hypothesis
discharged by built witnesses (`goodChain_aligned`; the dials by kernel
computation; `hiding_rounds` — the landed per-round hiding at the honest
schedule). -/
theorem zkRbrGame_F5 :
    ZkRbrGame (reedSolomonCode dom₅ 2) linRoot genesis goodChain
      roundMask roundQuery γbase γalt₂ γbase ηalt₃ :=
  zkRbrGame_holds linRoot goodChain_aligned (by decide) (by decide)
    (by decide) hiding_rounds

/-! ### Every field fired on the one instance -/

/-- **Completeness, fired**: the masked words (nonzero masks at both rounds)
verify the UNCHANGED aggregate. -/
theorem game_completeness_fired :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (aggregate linRoot γbase genesis goodChain)
      (flatFold γbase xWord (maskedWord γbase wsEx gsEx)) :=
  zkRbrGame_F5.completeness genesis_satisfied wsEx_sat gsEx_mem gsEx_ker

/-- **Adversarial knowledge, fired**: from the masked transcript family
(which verifies at every schedule) the chain extractor returns a list that
genuinely witnesses every link. -/
theorem game_knowledge_fired :
    List.Forall₂
      (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain
      (extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (fun k : Fin goodChain.length =>
          flatFold (updSched γbase γalt₂ k) xWord msEx)) :=
  zkRbrGame_F5.knowledge_sound (masked_completeness_F5 γbase)
    (fun k => masked_completeness_F5 (updSched γbase γalt₂ k))

/-- **Exact masked inversion, fired**: the extractor returns EXACTLY the
masked word list. -/
theorem game_masked_exact_fired :
    extractChain γbase γalt₂
        (flatFold γbase xWord (maskedWord γbase wsEx gsEx))
        (fun k : Fin goodChain.length =>
          flatFold (updSched γbase γalt₂ k) xWord
            (maskedWord γbase wsEx gsEx))
      = List.ofFn (maskedWord γbase wsEx gsEx) :=
  zkRbrGame_F5.masked_exact xWord wsEx gsEx

/-- The extracted list, COMPUTED (landed `masked_extraction_computes`,
cited): link 0's entry is the round-0 mask itself, link 1's is `oneWord`
shifted by the round-1 mask — the simulator's objects on the nose. -/
example :
    extractChain (ι := Fin 4) γbase γalt₂ (flatFold γbase xWord msEx)
        (fun k : Fin 2 => flatFold (updSched γbase γalt₂ k) xWord msEx)
      = [lineOf 2 1, oneWord + lineOf 4 2] :=
  masked_extraction_computes

/-- **The pair peel, fired on the nose**: the game's `pair_extraction` field
recovers BOTH rounds' `(witness, mask)` pairs exactly from the `2n + 1`
family — `(0, lineOf 2 1)` and `(oneWord, lineOf 4 2)`. -/
theorem game_pair_fired (k : Fin 2) :
    extractMaskedPair γbase γalt₂ γbase ηalt₃
        (flatFold γbase xWord (maskedWord γbase wsEx gsEx))
        (fun j : Fin 2 => flatFold (updSched γbase γalt₂ j) xWord
          (maskedWord γbase wsEx gsEx))
        (fun j : Fin 2 => flatFold γbase xWord
          (maskedWord (updSched γbase ηalt₃ j) wsEx gsEx))
        k
      = (wsEx k, gsEx k) :=
  zkRbrGame_F5.pair_extraction xWord wsEx gsEx k

/-- **The straightline seam, fired through binding**: the whole masked list
extracted from ONE execution — base transcript + verified openings of the
recommitted partial folds against the ideal binding commitment. -/
theorem game_seam_fired :
    extractChain γbase γalt₂ (flatFold γbase xWord msEx)
        (seamCounterfactual (n := 2) dom₅ 2 qPair γbase γalt₂
          (flatFold γbase xWord msEx)
          (fun c j => partialFold γbase xWord msEx c (qPair j)))
      = List.ofFn msEx :=
  zkRbrGame_F5.straightline_seam CommitExample.S₅ dom₅ le_rfl qPair_inj
    msEx_mem
    (rts := fun c => CommitExample.S₅.commit (partialFold γbase xWord msEx c))
    (ops := fun _ _ => ()) (fun _ _ => rfl)
    (fun c _ j => CommitExample.S₅.verifyOpen_commit
      (partialFold γbase xWord msEx c) (qPair j))

/-- **The chain simulator, fired**: the game's `zero_knowledge` field reaches
the FULL public tuple space over the mask draw, for the honest witness family
— the simulator's support is complete and witness-free. -/
theorem game_zero_knowledge_fired :
    jointOpen roundQuery γbase ![xWord, oneWord] '' jointMasks roundMask
      = Set.univ :=
  zkRbrGame_F5.zero_knowledge.chain_sim_support ![xWord, oneWord]

/-- **The exact-word round price, fired through the game** on the game's OWN
fold channel (`linRoot`): a violating pair satisfies the fold with
probability at most `accRbrError = 1/5`. -/
theorem game_round_error_fired :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims linRoot genesis genesis γ)
          ((0 : Fin 4 → ZMod 5) + γ • 0))
      ≤ accRbrError (ZMod 5) (fun _ => 0) 0 :=
  zkRbrGame_F5.round_error_exact ⟨0, by decide⟩ 0

/-- **The bound is ATTAINED, not slack** (landed
`AccSoundRbrExample.accSound_rbr_exact_attained`, cited): the violating fold
hits `accRbrError` with equality on the landed adversarial instance. -/
theorem game_error_attained :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      = accRbrError (ZMod 5) (fun _ => 0) 0 :=
  accSound_rbr_exact_attained

/-- **Premise inhabitation for the δ-proximity price**: `round_error_prox`'s
hypothesis package (minimum distance, mutual CA, the δ window, falseness) is
jointly satisfiable — the landed `accSound_rbr_fired`, at `C = ⊤` where
mutual CA is exact (`hasMutualCorrelatedAgreement_top_affine`). At the RS
code and macroscopic δ the same package rides the standing `hPG` — the named
floor, consumed never claimed. -/
theorem game_round_error_prox_fired :
    uniformProb (ZMod 5) (fun γ =>
        ∃ w, relDist (xWord + γ • (0 : Fin 4 → ZMod 5)) w ≤ 1 / 16 ∧
        AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          (foldClaims trivialRoot evalA evalB1 γ) w)
      ≤ accRbrError (ZMod 5) (fun _ => 0) (1 / 16) :=
  accSound_rbr_fired

/-- **The one price scale**: the round-level ZK error IS the soundness round
error at exact word — `1/|F|` prices both obligations of the one game, over
the same uniform challenge draw (landed coincidence, cited). -/
theorem game_one_price (δ : ℝ) :
    zkRbrError (ZMod 5) = accRbrError (ZMod 5) (fun _ => 0) δ :=
  zkRbrError_eq_accRbrError_exact (ZMod 5) δ

/-- **FS, fired on a genuine Def-4.2 instance at the game's error scale**:
the game's `fs_composed` field compiles `Selvage/Depth.lean`'s
`trivialReduction`/`trivialRbr` (err ≡ 1 ≤ 4/5 + 1/5 = `accRbrError` at
`errstar ≡ 4/5`) to a straightline FS argument at the `(t + k)·accRbrError`
factor. The instance is Depth's trivial one BECAUSE the accumulator's own
Def-4.2 instance is exactly `[ZK-RBR-game-resid]` — this keystone shows the
carrier field genuinely fires, not that the residual is closed. -/
theorem game_fs_fired :
    FsStraightlineKnowledgeSoundness trivialReduction Set.univ
      (fun _s b δ => ((b : ℝ) + (trivialReduction.k : ℝ))
        * accRbrError (ZMod 5) (fun _ => 4 / 5) δ) :=
  zkRbrGame_F5.fs_composed trivialReduction trivialRbr Set.univ
    (fun _ => 4 / 5) (fun _ _ => by norm_num)
    (fun _i _st _ δ _ => by
      show (1 : ℝ) ≤ accRbrError (ZMod 5) (fun _ => 4 / 5) δ
      unfold accRbrError
      norm_num [ZMod.card])

/-! ### Teeth: knowledge and ZK are genuinely both present and genuinely
separated — the game-separation teeth, on the game's own witness data -/

/-- **Teeth 1 — the pair is invisible to every δ-schedule, on the game's own
keystone data**: a SECOND valid `(witness, mask)` family with masked words
EQUAL to `(wsEx, gsEx)`'s — every transcript at every link schedule, every
opened column, every function of the honest execution coincides. The
`ηalt`-family the game's `pair_extraction` consumes is NOT a function of the
honest data: extraction at pair resolution needs exactly the counterfactual
ZK forbids, and that impossibility IS hiding working. -/
theorem game_teeth_pair_invisible :
    ∃ ws' gs' : Fin goodChain.length → Fin 4 → ZMod 5,
      (ws', gs') ≠ (wsEx, gsEx) ∧
      (∀ k, AccClaim.Satisfies (reedSolomonCode dom₅ 2)
        ((goodChain.get k).claim) (ws' k)) ∧
      (∀ k, gs' k ∈ reedSolomonCode dom₅ 2 ∧
        ∀ i, ((goodChain.get k).claim.weights i) (gs' k) = 0) ∧
      maskedWord γbase ws' gs' = maskedWord γbase wsEx gsEx ∧
      ∀ (δ : ℕ → ZMod 5) (f₀ : Fin 4 → ZMod 5),
        flatFold δ f₀ (maskedWord γbase ws' gs')
          = flatFold δ f₀ (maskedWord γbase wsEx gsEx) :=
  masked_pair_ambiguous wsEx_sat gsEx_mem gsEx_ker
    (k₀ := ⟨0, by decide⟩) (by decide)

/-- **Teeth 2, both dials** (landed, cited): the η-dial kills hiding never
the peel (`zero_mask_F5`); the mask diagonal kills the peel never hiding
(`mask_diagonal_F5`) — `RbrZeroKnowledge`'s type cannot even mention `ηalt`. -/
theorem game_teeth_dials :
    (¬ RbrZeroKnowledge roundMask roundQuery γzeroSched
        ∧ MaskedChainExtraction (ι := Fin 4) γbase γalt₂ γzeroSched γalt₂ 2)
      ∧ ((∀ (h₀ : Fin 4 → ZMod 5) (hlink hmask : Fin 2 → Fin 4 → ZMod 5)
            (k : Fin 2),
            (extractMaskedPair γbase γalt₂ γbase γbase h₀ hlink hmask k).2 = 0)
          ∧ RbrZeroKnowledge roundMask roundQuery γbase) :=
  ⟨zero_mask_F5, mask_diagonal_F5⟩

/-- **Teeth 3 — the γ-dial** (landed, cited): a zero round-challenge refutes
the game's `zero_knowledge` field outright while chain extraction still
recovers the full witness list — hiding's dial is never knowledge's. -/
theorem game_teeth_gamma_dial :
    ¬ RbrZeroKnowledge roundMask roundQuery γzeroSched ∧
    extractChain (ι := Fin 4) γzeroSched (padSched ![1, 2]) (xWord + oneWord)
      ![xWord + oneWord, xWord + (2 : ZMod 5) • oneWord] = [0, oneWord] :=
  ⟨zeroKnowledge_fails_at_zero_round, extraction_survives_zero_round⟩

/-- **Coexistence, from the ONE game object**: the assembled instance itself
delivers zero-knowledge at the honest schedule AND the pair-complete
extraction over the adversarial family — both games, one tuple, separated by
quantifier position alone. -/
theorem game_coexistence :
    RbrZeroKnowledge roundMask roundQuery γbase
      ∧ MaskedChainExtraction (ι := Fin 4) γbase γalt₂ γbase ηalt₃ 2 :=
  ⟨zkRbrGame_F5.zero_knowledge, zkRbrGame_F5.pair_extraction⟩

end ZkRbrGameExample

/-! ## Residual obligation — prose, not a stub

**`[ZK-RBR-game-resid]`** — what `[ACC-sound-rbr-game]` still owes AFTER this
file, stated precisely. This file CLOSES the ZK-argument game packaging at
the chain level: `ZkRbrGame` is one machine-checked object carrying
knowledge-soundness (with the fixed extract target), zero-knowledge, the
proven per-round price, and the FS carrier, with the quantifier separation in
its field types, inhabited by citation and fired on F₅. What it does NOT
close is the WARP-Def-4.2-NATIVE packaging: a concrete
`Reduction`/`KStateFn`/`extract`/`RbrKnowledgeSoundness` quadruple for the
accumulator chain (`k = ch.length`, `Chal = F`, `err = accRbrError`) — the
object that would let `fs_composed`/`accFsSound` fire ON THE ACCUMULATOR
ITSELF (today its `red`/`rbr`/`hbound` premises are supplied by the caller;
the keystone fires them on Depth's trivial instance, honestly labeled).

What `Selvage/ZkExtraction.lean` REMOVED from this debt — the parts
`[ACC-sound-rbr-game]`'s audit flagged as blocking:

* the extract TARGET is fixed: the game's `extract` field outputs the MASKED
  words attributed to the recommitted roots (`extractChain` composed with
  `seamCounterfactual`), NOT `(witness, mask)` pairs — the pair target is
  provably unreachable straightline (`masked_pair_ambiguous`) and provably
  unnecessary (`maskedChain_knowledge_sound`: masked words ARE witnesses);
  exactness at arbitrary depth is a theorem (`extractChain_flatFold`);
* the two-point-vs-single-seed obstruction is resolved: the second
  transcript per round is a FUNCTION of one execution's committed columns
  (`extractChain_committed_seam`) — WARP's backward extractor CAN be seeded
  from a single extended transcript once the transcript carries the
  recommitted roots and openings as prover messages.

What REMAINS, and why it is real work rather than bookkeeping:

* **the Def-4.1 transcript plumbing** — encode the chain game in
  `Reduction`'s shape (statement/word types over `Fin n → A`, `PMsg`
  carrying recommitted roots + opened columns) and exhibit a `KStateFn`
  honoring the three clauses (in particular `prover_monotone` over arbitrary
  prefixes, and the pinned empty/full clauses through `RelaxedMem`'s δ-ball);
* **the per-round `extract_sound` refinement** — WARP Def 4.2's event
  quantifies `∃ w` over EVERY knowledge-state witness of the extended
  transcript; the knowledge state must therefore demand CONSISTENCY WITH THE
  COMMITTED COLUMNS (so binding pins the masked words and the `∃ w` event
  refines into the fold event `accSound_rbr` bounds) — the mutual-CA
  falseness-hypothesis choreography `Selvage/AccSoundRbr.lean`'s audit
  describes, run inside the round extractor δ-obliviously;
* **inherited, unchanged**: `[ZK-RBR-extract]` lemma A (the sub-UD seam for
  constrained masks — the two horns meet there and neither is closed here)
  and the floor `[FS-ROM]` / `[COMMIT-CR]` / `hPG`.

**What is NOT at risk**: every field of the assembled game is an
unconditional landed theorem; the FS carrier (`FsOfRbrSound`) is proved with
no seam; the numbers (`accRbrError`, `(t + k)·ε`) are proved bounds attained
on F₅. The residual is a PACKAGING gap between two proved layers (the chain
game here, the FS carrier there), not a soundness gap in either.

## Ledger

* `ZkRbrGame` — DEFINED: the full ZK-argument RBR game, nine fields on one
  parameter tuple; `γalt` only in the knowledge fields, `ηalt` only in
  `pair_extraction`, `zero_knowledge` counterfactual-free — the quantifier
  separation in the types.
* `zkRbrGame_holds` — PROVED: the game holds by citation (nine landed
  theorems, ledger in the docstring; nothing re-derived).
* `selvage_zk_argument` — PROVED: the headline — every aligned chain with
  two-point dials and hiding rounds carries the game, and the FS carrier
  holds unconditionally; scope MODULO `[FS-ROM]`/`[COMMIT-CR]`/`hPG`,
  `[ZK-RBR-extract]` lemma A, `[ZK-RBR-game-resid]`.
* Keystones — `zkRbrGame_F5` (all fields, one landed instance);
  `game_completeness_fired` / `game_knowledge_fired` /
  `game_masked_exact_fired` (+ computed value) / `game_pair_fired` /
  `game_seam_fired` / `game_zero_knowledge_fired` /
  `game_round_error_fired` / `game_error_attained` /
  `game_round_error_prox_fired` / `game_one_price` / `game_fs_fired`;
  teeth `game_teeth_pair_invisible` / `game_teeth_dials` /
  `game_teeth_gamma_dial`; coexistence from the one object
  `game_coexistence`.
* Residual — `[ZK-RBR-game-resid]` (prose above): the Def-4.2-native
  quadruple, with what ZkExtraction removed and what remains named.

`#print axioms` on `zkRbrGame_holds`, `selvage_zk_argument`,
`ZkRbrGameExample.zkRbrGame_F5`, `ZkRbrGameExample.game_pair_fired`,
`ZkRbrGameExample.game_seam_fired`, `ZkRbrGameExample.game_fs_fired`,
`ZkRbrGameExample.game_teeth_pair_invisible`,
`ZkRbrGameExample.game_teeth_dials`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
