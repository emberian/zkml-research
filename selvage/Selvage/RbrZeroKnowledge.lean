/-
# Selvage.RbrZeroKnowledge — [ZK-RBR-game] attacked: the round-level
zero-knowledge vocabulary, and the multi-round extract/simulate coexistence.

`Selvage/ZkArgument.lean` closed `[OB-4-hiding-rbr]` gap (2) at ONE round and
named `[ZK-RBR-game]` with two missing pieces: (1) **no round-level
zero-knowledge vocabulary exists** — `Selvage/Rbr.lean`'s
`RbrKnowledgeSoundness` (WARP Def 4.2) is the only round-indexed object in
the tree and it is extraction-only (an `extract` field and an `err` bound,
nothing simulator-shaped); (2) the multi-round game must make EVERY round of
a depth-`k` chain simultaneously extractable (chain-level two-point,
`Selvage/AccExtractChain.lean`'s `extractChain`) and simulatable (per-round mask
hiding, `Selvage/ZKHiding.lean`/`Selvage/ConstrainedMask.lean`), interleaved over
depth. This file authors (1), proves the part of (2) that closes, and
sharpens what does not into the named residual `[ZK-RBR-interleave]`.

What lands, in order:

* **`RbrZeroKnowledge`** — the missing vocabulary. A round-indexed family:
  per-round mask spaces `M k`, per-round query selections `q k`, ONE
  challenge schedule `γs : ℕ → F` — deliberately the SAME schedule type the
  chain extractor and the aggregate consume (`Selvage/LightClientSound.lean`'s
  `padSched` world), so one `γs` can serve both games. Three fields:
  `round_hiding` (each round's opened symbols are simulatable without the
  witness — `MaskedOpeningHiding` CITED verbatim, never re-derived), and the
  two CHAIN-simulator fields `chain_sim_support` / `chain_fiber_equinum`
  (the JOINT opened tuples of all `n` rounds, one fresh mask per round, are
  uniform on the full product space `Fin n → Fin t → F`, independently of
  the whole witness FAMILY — the multi-round simulator is the product of
  the per-round ones). The simulator is witness-free by quantifier position:
  every field quantifies over ALL witness families `fs`, and no `fs` occurs
  on any right-hand side.
* **`rbrZeroKnowledge_of_rounds`** — the composition theorem: per-round
  hiding IMPLIES the chain fields. The per-round simulators compose into
  the chain simulator by the product structure: round `k`'s opening reads
  round `k`'s mask draw ONLY (syntactically visible in `jointMaskFiber` —
  each conjunct mentions `gs k` alone), so the joint fiber is a product of
  round fibers and translates coordinatewise. `rbrZeroKnowledge_iff_rounds`
  records honestly that the chain fields add no logical strength — the
  structure's value is carrying the composed object, exactly as
  `ZkArgument`'s value was carrying the conjunction.
* **`zkRbrError`** — the round-level ZK error in `Selvage/Rbr.lean`'s own
  measure idiom, dual to `Selvage/AccSoundRbr.lean`'s `accRbrError`: over ONE
  uniform challenge draw (the SAME `uniformProb F` that measures
  `RbrKnowledgeSoundness.extract_sound`'s per-round event), round hiding
  fails with probability EXACTLY `1/|F|` (`rbrZk_round_error` — the failure
  set is precisely `{γ = 0}`, by the new sharp iff
  `constrainedMask_hiding_iff`). `zkRbrError_eq_accRbrError_exact`: it
  coincides on the nose with the soundness round error at `errstar ≡ 0` —
  the one challenge draw prices BOTH round obligations of the one game.
  There is no `δ` dial on the ZK side: hiding here is perfect
  (distribution-equality), not proximity-relaxed.
* **`RbrZkArgument` + `rbrZk_multiround`** — the multi-round coexistence,
  `ZkArgument` lifted to the chain: completeness (`aggregate_satisfies`),
  knowledge-soundness (`extractChain_sound` — the chain extractor, per
  `[ACC-sound-rbr-game]`'s diagnosis the ONLY correct realizer; `n + 1`
  transcripts), and zero-knowledge (`RbrZeroKnowledge`) in one structure on
  one `(C, foldRoot, A₀, ch, M, q, γs, γalt)`. The quantifier-position
  separation that resolved the single-round tension SURVIVES the lift, and
  is visible in the field types: `γalt` (the extractor's counterfactual
  schedule) and the `n + 1` transcript words occur ONLY in
  `knowledge_sound`; `zero_knowledge`'s type mentions no `γalt`, no
  transcript, no witness — the honest verifier runs one schedule, and that
  is the schedule the simulators hide.
* **Keystones over F₅** (all landed objects REUSED): the 2-round
  `LCExample.goodChain` with BOTH rounds' masks drawn from the landed
  `constrainedMaskSpace dom₅ 2 pt2` fires all three fields on ONE instance
  at the base schedule `(1, 1)` (`rbrZkArgument_F5`, `completeness_fired`,
  `knowledge_sound_fired`, `zero_knowledge_fired`, `chain_simulator_fired`).
  The extractor and the simulator genuinely share structure:
  `goodChain`'s link-0 claim IS a mask claim (its satisfying set IS the
  round mask space, `claim₀_satisfies_iff_mem_maskSpace` — the chain
  transport of `mem_constrainedMaskSpace_iff_satisfies`), and on a masked
  transcript family the chain extractor's link-0 output IS a nonzero
  element of the simulator's mask space (`extractor_meets_simulator`,
  computed). Teeth BOTH directions, lifted from the single round:
  a zero round-challenge kills multi-round ZK but NOT chain extraction
  (`zeroKnowledge_fails_at_zero_round` + `extraction_survives_zero_round`);
  one schedule kills chain extraction (diagonal collapse, landed
  `extract_chain_teeth_diagonal` cited) but NOT zero-knowledge — whose type
  cannot even mention the second schedule
  (`one_schedule_kills_extraction_not_hiding`).

**Honest scope.** The chain simulator proved here is for the FRESH-MASK
PRODUCT model: `n` rounds, round `k` opening `t` symbols of `mask (fs k)
(γs k) (gs k)` — its OWN pre-mask word masked by its OWN fresh draw. That is
the model `Selvage/ZKHiding.lean`'s multi-step residual points at ("fresh
per-step masks", one committed word opened at one step only), and the
product composition is real, closed mathematics. What it is NOT: the
deployed recommitment schedule, where round `k`'s opened word is the `k`-th
PARTIAL FOLD and therefore contains every EARLIER round's mask — the joint
opening map is triangular, not product, and the fibers no longer factor.
That, plus the extractor-side coupling (the second transcript per round is
erasure-corrected from the SAME opened columns the simulator must produce),
is `[ZK-RBR-interleave]` — sharpened at the bottom with the two missing
lemmas named. No `sorry`, no vacuous `Prop := True`.
-/
import Selvage.ZkArgument
import Selvage.Rbr
import Selvage.AccExtractChain
import Selvage.AccSoundRbr
import Selvage.FiatShamir

namespace Minidregg.Selvage

/-! ## The joint (multi-round) opening vocabulary

`n` rounds; round `k` draws its mask from its own space `M k`, opens `t`
symbols at its own selection `q k`, at challenge `γs k`. The schedule is
`ℕ → F` — the chain fold's own schedule type — so ONE `γs` serves the
aggregate, the chain extractor, and the simulators. One `t` for all rounds
mirrors `Selvage/Rbr.lean`'s one-challenge-alphabet specialization (pad to the
max; nothing below reads the pad). -/

variable {F : Type*} [Field F] {ι : Type*} {t n : ℕ}

/-- The joint mask space: one INDEPENDENT draw per round — round `k`'s
coordinate lies in round `k`'s space. The product structure (each conjunct
reads `gs k` alone) is what the composition theorem's proof runs on, and
exactly what the deployed triangular schedule breaks
(`[ZK-RBR-interleave]`). -/
def jointMasks (M : Fin n → Submodule F (ι → F)) : Set (Fin n → ι → F) :=
  {gs | ∀ k, gs k ∈ M k}

@[simp] theorem mem_jointMasks {M : Fin n → Submodule F (ι → F)}
    {gs : Fin n → ι → F} : gs ∈ jointMasks M ↔ ∀ k, gs k ∈ M k := Iff.rfl

/-- The joint opening map: what the verifier sees across all `n` rounds —
round `k`'s `t` opened symbols of round `k`'s masked word. Round `k` reads
`fs k` and `gs k` ONLY (the fresh-mask product model; module header). -/
def jointOpen (q : Fin n → Fin t → ι) (γs : ℕ → F) (fs : Fin n → ι → F)
    (gs : Fin n → ι → F) : Fin n → Fin t → F :=
  fun k => openSymbols (q k) (mask (fs k) (γs (k : ℕ)) (gs k))

@[simp] theorem jointOpen_apply (q : Fin n → Fin t → ι) (γs : ℕ → F)
    (fs gs : Fin n → ι → F) (k : Fin n) :
    jointOpen q γs fs gs k = openSymbols (q k) (mask (fs k) (γs (k : ℕ)) (gs k)) :=
  rfl

/-- The joint explaining-mask fiber: the mask families whose masked words
open to the tuple family `vs` — the product of the per-round `maskFiber`s.
For a uniformly random mask family, `Pr[joint opened = vs]` is this fiber's
share of `jointMasks M`; fiber equinumerosity across all `(fs, vs)` IS joint
uniformity, exactly as one layer down. -/
def jointMaskFiber (M : Fin n → Submodule F (ι → F)) (q : Fin n → Fin t → ι)
    (γs : ℕ → F) (fs : Fin n → ι → F) (vs : Fin n → Fin t → F) :
    Set (Fin n → ι → F) :=
  {gs | ∀ k, gs k ∈ maskFiber (M k) (q k) (γs (k : ℕ)) (fs k) (vs k)}

/-- The joint fiber IS the fiber of the joint opening map over the joint
mask space — the definition above is not a new object, only the product
presentation of the one fiber. -/
theorem mem_jointMaskFiber {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} {fs : Fin n → ι → F}
    {vs : Fin n → Fin t → F} {gs : Fin n → ι → F} :
    gs ∈ jointMaskFiber M q γs fs vs
      ↔ gs ∈ jointMasks M ∧ jointOpen q γs fs gs = vs := by
  constructor
  · intro h
    exact ⟨fun k => (h k).1, funext fun k => (h k).2⟩
  · rintro ⟨hm, ho⟩ k
    exact ⟨hm k, congrFun ho k⟩

/-! ## `RbrZeroKnowledge` — the round-level zero-knowledge vocabulary

The mirror of `RbrKnowledgeSoundness`'s round indexing on the hiding side.
Where Def 4.2 carries a per-round extractor and a per-round error, this
carries the per-round SIMULATOR obligation (round `k`'s opened symbols are
reproducible without the witness — `MaskedOpeningHiding`, the landed object,
cited as the field type) and the CHAIN simulator it composes into. The
simulator itself is the uniform sampler on `Fin n → Fin t → F` — a public
object; that its output distribution equals the real openings' is exactly
what the support/fiber fields say, in the same exact-counting idiom as
`Selvage/ZKHiding.lean` (no probability scaffolding; the `uniformProb`-measured
round error is `zkRbrError` below). -/

/-- **`RbrZeroKnowledge`** — round-by-round zero-knowledge of a depth-`n`
masked opening schedule: per-round mask spaces `M`, query selections `q`,
challenge schedule `γs`.

* `round_hiding` — EVERY round's opened symbols are simulatable without
  that round's witness: `MaskedOpeningHiding` per round, at the round's own
  challenge `γs k`. The per-round vocabulary `[ZK-RBR-game]` said was
  missing, now round-indexed against the chain's own schedule type.
* `chain_sim_support` — the JOINT reachable opened tuples, across all `n`
  rounds at once, are ALL of `Fin n → Fin t → F`, for EVERY witness family:
  the multi-round simulator's support is the full public product space and
  cannot depend on any round's witness.
* `chain_fiber_equinum` — any two joint fibers (any two witness families,
  any two tuple families) are carried onto each other by ONE explicit
  translation lying in the joint mask space: the joint distribution is
  uniform on that support, identically in the witness family. Perfect,
  distribution-equality hiding of the WHOLE schedule's leakage surface.

Witness-freedom is syntactic: `fs` is universally quantified in every field
and absent from every right-hand side. Non-vacuity: inhabited and refuted
keystones below (`rbrZk_base`; `zeroKnowledge_fails_at_zero_round` — one
zero round-challenge refutes the whole object when anything is opened). -/
structure RbrZeroKnowledge (M : Fin n → Submodule F (ι → F))
    (q : Fin n → Fin t → ι) (γs : ℕ → F) : Prop where
  round_hiding : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ))
  chain_sim_support : ∀ fs : Fin n → ι → F,
    jointOpen q γs fs '' jointMasks M = Set.univ
  chain_fiber_equinum : ∀ (fs₁ fs₂ : Fin n → ι → F)
    (vs₁ vs₂ : Fin n → Fin t → F), ∃ cs ∈ jointMasks M,
    Set.BijOn (· + cs) (jointMaskFiber M q γs fs₁ vs₁)
      (jointMaskFiber M q γs fs₂ vs₂)

/-- **The composition theorem — per-round simulators compose into the chain
simulator.** Per-round hiding alone yields `RbrZeroKnowledge`: the joint
support is full because each round's is (choose a mask per round), and the
joint fibers translate onto each other COORDINATEWISE — round `k`'s
translation is round `k`'s landed `fiber_equinum` witness, and the product
map `(· + cs)` restricts to the joint fibers precisely BECAUSE round `k`'s
fiber condition reads `gs k` alone. This is where the fresh-mask product
model earns its keep: were round `k`'s opening to read an earlier round's
mask (the deployed recommitment schedule — triangular, not product),
translating round `j`'s coordinate would move round `k`'s opened tuple and
the coordinatewise map would NOT preserve the fibers. That failure is
`[ZK-RBR-interleave]`'s first missing lemma, not an accident of this proof. -/
theorem rbrZeroKnowledge_of_rounds {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ))) :
    RbrZeroKnowledge M q γs where
  round_hiding := H
  chain_sim_support fs := by
    refine Set.eq_univ_of_forall fun vs => ?_
    have h : ∀ k : Fin n, ∃ g, g ∈ M k ∧
        openSymbols (q k) (mask (fs k) (γs (k : ℕ)) g) = vs k := by
      intro k
      have hv : vs k ∈ (fun g => openSymbols (q k) (mask (fs k) (γs (k : ℕ)) g))
          '' (M k) := by
        rw [(H k).sim_support_univ (fs k)]
        trivial
      obtain ⟨g, hg, hgv⟩ := hv
      exact ⟨g, hg, hgv⟩
    choose gs hgM hgv using h
    exact ⟨gs, hgM, funext hgv⟩
  chain_fiber_equinum fs₁ fs₂ vs₁ vs₂ := by
    have h : ∀ k : Fin n, ∃ c ∈ M k,
        Set.BijOn (· + c)
          (maskFiber (M k) (q k) (γs (k : ℕ)) (fs₁ k) (vs₁ k))
          (maskFiber (M k) (q k) (γs (k : ℕ)) (fs₂ k) (vs₂ k)) :=
      fun k => (H k).fiber_equinum (fs₁ k) (fs₂ k) (vs₁ k) (vs₂ k)
    choose cs hcM hbij using h
    refine ⟨cs, hcM, fun gs hgs k => (hbij k).mapsTo (hgs k),
      (add_left_injective cs).injOn, fun gs' hgs' => ?_⟩
    refine ⟨gs' - cs, fun k => ?_, sub_add_cancel gs' cs⟩
    obtain ⟨x, hx, hxeq⟩ := (hbij k).surjOn (hgs' k)
    have hxeq' : x + cs k = gs' k := hxeq
    have hxe : (gs' - cs) k = x := by
      show gs' k - cs k = x
      rw [← hxeq']
      abel
    rw [hxe]
    exact hx

/-- **Audit transparency**: the chain fields add no logical strength over
per-round hiding — the structure is EQUIVALENT to its round family. The
definition's value is carrying the composed multi-round simulator as one
object (the thing `[ZK-RBR-game]` asked to even STATE), exactly as
`ZkArgument`'s value was the non-vacuous conjunction, not a new inequality. -/
theorem rbrZeroKnowledge_iff_rounds {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} :
    RbrZeroKnowledge M q γs
      ↔ ∀ k : Fin n, MaskedOpeningHiding (M k) (q k) (γs (k : ℕ)) :=
  ⟨fun H => H.round_hiding, rbrZeroKnowledge_of_rounds⟩

/-- **Witness independence of the whole schedule**: two provers holding
DIFFERENT witness families produce identical joint opened-tuple supports —
the distinguisher watching all `n` rounds' spot checks at once learns
nothing about which family is held. `MaskedOpeningHiding.witness_free`
lifted to the multi-round leakage surface. -/
theorem RbrZeroKnowledge.chain_witness_free {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} (H : RbrZeroKnowledge M q γs)
    (fs₁ fs₂ : Fin n → ι → F) :
    jointOpen q γs fs₁ '' jointMasks M = jointOpen q γs fs₂ '' jointMasks M := by
  rw [H.chain_sim_support fs₁, H.chain_sim_support fs₂]

/-- The counting corollary: every joint explaining fiber has the same size —
`Pr[joint opened = vs]` is ONE constant across witness families and tuple
families. The chain simulator's distribution equality in the file's
exact-counting idiom. -/
theorem RbrZeroKnowledge.jointMaskFiber_ncard_eq
    {M : Fin n → Submodule F (ι → F)} {q : Fin n → Fin t → ι} {γs : ℕ → F}
    (H : RbrZeroKnowledge M q γs) (fs₁ fs₂ : Fin n → ι → F)
    (vs₁ vs₂ : Fin n → Fin t → F) :
    (jointMaskFiber M q γs fs₁ vs₁).ncard
      = (jointMaskFiber M q γs fs₂ vs₂).ncard := by
  obtain ⟨cs, -, hbij⟩ := H.chain_fiber_equinum fs₁ fs₂ vs₁ vs₂
  rw [← hbij.image_eq, Set.ncard_image_of_injective _ (add_left_injective cs)]

/-- **Teeth, general form**: ONE round with a zero challenge refutes the
WHOLE multi-round object (as long as that round opens anything, `0 < t`) —
the γ-dial of `Selvage/ZKHiding.lean` propagated to the chain level. A schedule
is only as hiding as its worst round. -/
theorem not_rbrZeroKnowledge_of_zero {M : Fin n → Submodule F (ι → F)}
    {q : Fin n → Fin t → ι} {γs : ℕ → F} (k : Fin n) (h0 : γs (k : ℕ) = 0)
    (ht : 0 < t) : ¬ RbrZeroKnowledge M q γs := fun H =>
  not_maskedOpeningHiding_zero (M k) ht (h0 ▸ H.round_hiding k)

/-! ## `zkRbrError` — the round-level ZK error, in Rbr's measure idiom

`Selvage/AccSoundRbr.lean` packaged the fold's SOUNDNESS round error as
`accRbrError = err⋆(δ) + 1/|F|`, a bound on a `uniformProb F` event over the
round's challenge draw. The ZK dual, over the SAME measure on the SAME
challenge space: round hiding fails on EXACTLY the challenge set `{0}`, so
the ZK round error is `1/|F|` — and it COINCIDES with the soundness round
error's exact-word specialization (`errstar ≡ 0`). One challenge draw, two
round obligations, one price scale. No `δ` enters: hiding is perfect where
it holds, refuted where it does not — there is no proximity-relaxed hiding
regime to price. -/

section MeasuredError

variable {F : Type} [Field F] {ι : Type*} {t d : ℕ}

/-- **`zkRbrError`** — the per-round zero-knowledge error: the probability,
over one uniform round challenge, that the round's mask fails to hide.
`1/|F|`, attained exactly (`rbrZk_round_error`). The measure-idiom dual of
`accRbrError`. -/
noncomputable def zkRbrError (F : Type) [Fintype F] : ℝ :=
  1 / (Fintype.card F : ℝ)

theorem zkRbrError_nonneg (F : Type) [Fintype F] : 0 ≤ zkRbrError F := by
  unfold zkRbrError
  positivity

/-- **The duality with the soundness round error, on the nose**: the ZK
round error IS `accRbrError`'s exact-word specialization — the same `1/|F|`
prices the fold's exact-word soundness failure and the mask's hiding
failure, over the same uniform challenge draw. (The general `accRbrError`
exceeds `zkRbrError` by exactly the mutual-CA term `err⋆(δ)`, which has no
hiding analogue.) -/
theorem zkRbrError_eq_accRbrError_exact (F : Type) [Fintype F] (δ : ℝ) :
    zkRbrError F = accRbrError F (fun _ => 0) δ :=
  (accRbrError_const_zero (F := F) δ).symm

/-- **The sharp round-hiding iff for the constrained mask space** — the F₅
`maskedOpeningHiding_F5_iff` generalized: at the tight budget `t + 1 ≤ d`
with the queries off the constraint point, hiding holds IFF the round
challenge is nonzero. Forward is `constrainedMask_hiding` (CITED); backward
is `not_maskedOpeningHiding_zero`. This is what pins the failure SET (not
just a bound) for the measured error below. -/
theorem constrainedMask_hiding_iff (dom : ι ↪ F) (pt : ι) (ht : t + 1 ≤ d)
    (htpos : 0 < t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    (hpt : ∀ j, q j ≠ pt) (γ : F) :
    MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ ↔ γ ≠ 0 := by
  refine ⟨fun H h0 => ?_, constrainedMask_hiding dom pt ht hq hpt⟩
  subst h0
  exact not_maskedOpeningHiding_zero _ htpos H

/-- **The round-level ZK error, ATTAINED**: over one uniform challenge draw
— `Selvage/Rbr.lean`'s own `uniformProb F`, the measure
`RbrKnowledgeSoundness.extract_sound` prices its round event with — the
constrained mask fails to hide with probability EXACTLY `zkRbrError F =
1/|F|`: the failure event is precisely `{γ = 0}`. The `uniformProb`-measured
round-level ZK bound `[ZK-RBR-game]` named as unbuilt, built. -/
theorem rbrZk_round_error [Fintype F] (dom : ι ↪ F) (pt : ι) (ht : t + 1 ≤ d)
    (htpos : 0 < t) {q : Fin t → ι} (hq : Function.Injective (dom ∘ q))
    (hpt : ∀ j, q j ≠ pt) :
    uniformProb F
      (fun γ => ¬ MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ)
      = zkRbrError F := by
  rw [uniformProb_congr (q := fun γ : F => γ = 0) fun γ =>
    (not_congr (constrainedMask_hiding_iff dom pt ht htpos hq hpt γ)).trans
      not_not]
  unfold uniformProb zkRbrError
  haveI : Unique {c : F // c = 0} := ⟨⟨⟨0, rfl⟩⟩, fun c => Subtype.ext c.2⟩
  rw [Nat.card_unique, Nat.cast_one]

/-- The `≤`-form, shaped like `extract_sound`'s round bound: hiding-failure
probability per round is at most `zkRbrError`. -/
theorem rbrZk_round_error_le [Fintype F] (dom : ι ↪ F) (pt : ι)
    (ht : t + 1 ≤ d) (htpos : 0 < t) {q : Fin t → ι}
    (hq : Function.Injective (dom ∘ q)) (hpt : ∀ j, q j ≠ pt) :
    uniformProb F
      (fun γ => ¬ MaskedOpeningHiding (constrainedMaskSpace dom d pt) q γ)
      ≤ zkRbrError F :=
  le_of_eq (rbrZk_round_error dom pt ht htpos hq hpt)

end MeasuredError

/-! ## `RbrZkArgument` — the multi-round coexistence

`ZkArgument` lifted to the chain: one structure whose fields are the REAL
conclusions of the landed chain theorems, on one shared parameter tuple.
The quantifier-position separation, now at depth: `knowledge_sound` ranges
over the prover's `n + 1` transcript words and the counterfactual schedule
`γalt`; `zero_knowledge`'s type mentions neither — the honest verifier runs
ONE schedule and the simulators hide exactly that one. -/

section ChainArgument

variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {r t : ℕ}

/-- **`RbrZkArgument`** — a zero-knowledge argument for the whole depth-`n`
accumulation chain: genesis `A₀`, chain `ch`, per-round mask spaces `M` and
query selections `q`, base schedule `γs`, alternate challenges `γalt`.

* `completeness` — honest per-link witnesses fold to a witness of the
  aggregate at the base schedule (`aggregate_satisfies`' conclusion).
* `knowledge_sound` — from words verifying the aggregate at the base
  schedule AND at every `k`-perturbed schedule (the flat `n + 1`-transcript
  family — the CHAIN-level two-point extractor, `[ACC-sound-rbr-game]`'s
  named realizer, NOT `n` independent one-round extractors), `extractChain`
  returns BUILT witnesses of every link (`extractChain_sound`'s conclusion
  verbatim). This is the only field that sees `γalt` or a second transcript.
* `zero_knowledge` — the round-by-round simulator family at the base
  schedule: `RbrZeroKnowledge M q γs`. No `γalt`, no transcript word, no
  witness in the type — the quantifier-position separation of
  `Selvage/ZkArgument.lean`, surviving the lift to depth. -/
structure RbrZkArgument (C : Submodule F (ι → F))
    (foldRoot : Root → F → Root → Root) (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) (M : Fin ch.length → Submodule F (ι → F))
    (q : Fin ch.length → Fin t → ι) (γs γalt : ℕ → F) : Prop where
  completeness : ∀ {f₀ : ι → F} {ws : List (ι → F)},
    List.Forall₂
      (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w) ch ws →
    AccClaim.Satisfies C A₀ f₀ →
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) (foldWords γs f₀ ws)
  knowledge_sound : ∀ {h₀ : ι → F} {hs : Fin ch.length → ι → F},
    AccClaim.Satisfies C (aggregate foldRoot γs A₀ ch) h₀ →
    (∀ k : Fin ch.length, AccClaim.Satisfies C
      (aggregate foldRoot (updSched γs γalt k) A₀ ch) (hs k)) →
    List.Forall₂
      (fun (l : Link Root F ι r) w => AccClaim.Satisfies C l.claim w) ch
      (extractChain γs γalt h₀ hs)
  zero_knowledge : RbrZeroKnowledge M q γs

/-- **The multi-round coexistence theorem**: an aligned chain with linkwise
distinct challenge pairs and per-round mask hiding carries an
`RbrZkArgument` — every field by CITATION (`aggregate_satisfies`,
`extractChain_sound`, `rbrZeroKnowledge_of_rounds` over the supplied
hiding facts), nothing re-derived. As at the single round, the coexistence
is definitional once the vocabulary exists: the three obligations are
proved from disjoint premises (fold algebra vs. MDS interpolation) and meet
on the SAME `(ch, γs)` — `hne` feeds only `knowledge_sound`, `hZK` only
`zero_knowledge`, and neither constrains the other. What is NOT definitional
— the deployed interleaving where the extractor's transcripts and the
simulator's openings are the same committed columns — is
`[ZK-RBR-interleave]`, below, not silently absorbed here. -/
theorem rbrZk_multiround {C : Submodule F (ι → F)}
    (foldRoot : Root → F → Root → Root) {A₀ : AccClaim Root F ι r}
    {ch : Chain Root F ι r} {M : Fin ch.length → Submodule F (ι → F)}
    {q : Fin ch.length → Fin t → ι} {γs γalt : ℕ → F}
    (halign : Aligned A₀ ch)
    (hne : ∀ k : Fin ch.length, γs (k : ℕ) ≠ γalt (k : ℕ))
    (hZK : ∀ k : Fin ch.length,
      MaskedOpeningHiding (M k) (q k) (γs (k : ℕ)))
    : RbrZkArgument C foldRoot A₀ ch M q γs γalt where
  completeness hws hA₀ := aggregate_satisfies foldRoot γs hws halign hA₀
  knowledge_sound hbase hpert := extractChain_sound foldRoot halign hne hbase hpert
  zero_knowledge := rbrZeroKnowledge_of_rounds hZK

end ChainArgument

/-- The non-interactive carrier the multi-round game will ride is PROVED
upstream and only CITED here (import made load-bearing): Fiat–Shamir of an
RBR-sound reduction is straightline knowledge-sound at `(t + k) · ε_rbr`
(`Selvage/FiatShamir.lean`, unconditional). `[ZK-RBR-interleave]` composes with
THIS — the FS game whose openings serve both reductions — and never
re-derives it. -/
example : FsOfRbrKeystone := fsKeystone_proved

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

Over `RS[F₅, {0,1,2,3}, 2]`, everything REUSED: the 2-round chain is
`LCExample.goodChain` (genesis `(q2, 2)` witnessed by `xWord`; link 0
`(q2, 0)`; link 1 `(q2, 1)`), the schedules are
`AccExtractChainExample.γbase = (1,1)` / `γalt₂ = (2,2)`, and BOTH rounds
draw masks from the landed `constrainedMaskSpace dom₅ 2 pt2` opened at
`ZkArgumentExample.qz` — the very objects the single-round `ZkArgument`
keystone used, now serving all `n` rounds of the chain at once. -/

namespace RbrZkExample

open RSExample AccExample LCExample ZkHidingExample ZkArgumentExample
  AccExtractChainExample

/-- Both rounds' mask space: the landed constrained mask space (vanish at
`pt2 = 2`) — the SAME submodule the single-round instance drew from. -/
noncomputable def roundMask : Fin 2 → Submodule (ZMod 5) (Fin 4 → ZMod 5) :=
  fun _ => constrainedMaskSpace dom₅ 2 pt2

/-- Both rounds' query selection: one opened symbol at `qz = 0`, the tight
budget `t + 1 = d = 2`. -/
def roundQuery : Fin 2 → Fin 1 → Fin 4 := fun _ => qz

/-- Per-round hiding at the base schedule `(1, 1)`: both round challenges
are nonzero, so `constrainedMask_hiding` (CITED) fires at each round. -/
theorem hiding_rounds (k : Fin 2) :
    MaskedOpeningHiding (roundMask k) (roundQuery k) (γbase (k : ℕ)) :=
  constrainedMask_hiding dom₅ pt2 (by norm_num) qz_inj qz_ne_pt2
    (by fin_cases k <;> decide)

/-- **Premise inhabitation for the vocabulary**: `RbrZeroKnowledge` is
non-vacuously inhabited — the 2-round simulator family exists at the base
schedule, composed by `rbrZeroKnowledge_of_rounds`. -/
theorem rbrZk_base : RbrZeroKnowledge roundMask roundQuery γbase :=
  rbrZeroKnowledge_of_rounds hiding_rounds

/-- **THE INSTANCE**: the multi-round coexistence fires on the landed chain
— `goodChain` at base `(1,1)` / alternate `(2,2)` with both rounds' masks
constrained-and-hiding. Pure composition (`rbrZk_multiround`); every
hypothesis discharged by landed witnesses. -/
theorem rbrZkArgument_F5 :
    RbrZkArgument (reedSolomonCode dom₅ 2) linRoot genesis goodChain
      roundMask roundQuery γbase γalt₂ :=
  rbrZk_multiround linRoot goodChain_aligned (by decide) hiding_rounds

/-! ### All three fields fired on ONE instance -/

/-- **Completeness, fired**: the honest witness list `[0, oneWord]` folds to
a genuine witness of the aggregate at the base schedule. -/
theorem completeness_fired :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (aggregate linRoot γbase genesis goodChain)
      (foldWords γbase xWord [0, oneWord]) :=
  rbrZkArgument_F5.completeness
    (.cons ⟨Submodule.zero_mem _, fun _ => map_zero q2⟩
      (.cons ⟨oneWord_mem, fun _ => rfl⟩ .nil))
    genesis_satisfied

/-- **Knowledge-soundness, fired**: from the three verifying transcripts
(base + one perturbation per link), the chain extractor returns a list that
genuinely witnesses every link — and by the landed
`AccExtractChainExample.extractChain_recovers`, that list is exactly
`[0, oneWord]`. -/
theorem knowledge_sound_fired :
    List.Forall₂
      (fun (l : Link (ZMod 5) (ZMod 5) (Fin 4) 1) w =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2) l.claim w) goodChain
      (extractChain γbase γalt₂ (foldWords γbase xWord [0, oneWord])
        fun k : Fin goodChain.length =>
          foldWords (updSched γbase γalt₂ k) xWord [0, oneWord]) :=
  rbrZkArgument_F5.knowledge_sound (goodChain_aggregate_satisfied γbase)
    fun k => goodChain_aggregate_satisfied (updSched γbase γalt₂ k)

/-- **Zero-knowledge, fired**: the SAME instance's per-round simulator
family — the base schedule both other fields ran at. -/
theorem zero_knowledge_fired : RbrZeroKnowledge roundMask roundQuery γbase :=
  rbrZkArgument_F5.zero_knowledge

/-- **The chain simulator, fired**: for the honest witness family
`(xWord, oneWord)` the joint opened tuples across BOTH rounds reach the full
product space — the multi-round simulator's support is public and complete. -/
theorem chain_simulator_fired :
    jointOpen roundQuery γbase ![xWord, oneWord] '' jointMasks roundMask
      = Set.univ :=
  rbrZk_base.chain_sim_support ![xWord, oneWord]

/-! ### The extractor and the simulator share the round's mask object

`goodChain`'s link-0 claim `(q2, 0)` IS a mask claim: `q2 = evalAtPt pt2`
(landed `q2_eq_evalAtPt2`), so its satisfying set over the code is EXACTLY
the round mask space — the chain transport of the single-round bridge
`mem_constrainedMaskSpace_iff_satisfies`. The chain extractor's link-0
output is therefore an element of the very space the round simulator draws
from; on a masked transcript family this is computed below with a NONZERO
mask. -/

/-- **The bridge, chain-level**: link 0's satisfying set IS the round mask
space, pointwise. The extractor's round object and the simulator's round
object are one set. -/
theorem claim₀_satisfies_iff_mem_maskSpace (w : Fin 4 → ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) claim₀ w
      ↔ w ∈ constrainedMaskSpace dom₅ 2 pt2 := by
  rw [mem_constrainedMaskSpace]
  exact ⟨fun h => ⟨h.1, h.2 0⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

/-- The landed nonzero mask `lineOf 2 1` (∈ the mask space,
`ZkArgumentExample.maskWord_mem`) genuinely witnesses link 0's claim —
through the bridge, by citation. -/
theorem maskWord_sat_claim₀ :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) claim₀ (lineOf 2 1) :=
  (claim₀_satisfies_iff_mem_maskSpace _).mpr maskWord_mem

/-- The masked witness family `[lineOf 2 1, oneWord]` verifies the aggregate
at EVERY schedule — the transcripts of a prover whose link-0 witness IS a
nonzero mask-space element are honest transcripts. -/
theorem masked_chain_verifies (γs : ℕ → ZMod 5) :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2)
      (aggregate linRoot γs genesis goodChain)
      (foldWords γs xWord [lineOf 2 1, oneWord]) :=
  aggregate_satisfies linRoot γs
    (.cons maskWord_sat_claim₀ (.cons ⟨oneWord_mem, fun _ => rfl⟩ .nil))
    goodChain_aligned genesis_satisfied

/-- **The extractor returns the simulator's object, computed**: on the
masked transcript family the chain extractor's link-0 entry is EXACTLY the
nonzero mask `lineOf 2 1` — an element of the round mask space
(`maskWord_mem`, `maskWord_ne_zero` landed). The two games genuinely share
the round's mask object: what one draws to hide, the other recovers to
extract. (Depth-2 instance of the mask-peeling the residual's
masked-chain-extraction lemma must deliver at arbitrary depth.) -/
theorem extractor_meets_simulator :
    extractChain (ι := Fin 4) γbase γalt₂ (xWord + lineOf 2 1 + oneWord)
        ![xWord + (2 : ZMod 5) • lineOf 2 1 + oneWord,
          xWord + lineOf 2 1 + (2 : ZMod 5) • oneWord]
        = [lineOf 2 1, oneWord] ∧
      lineOf 2 1 ∈ constrainedMaskSpace dom₅ 2 pt2 ∧ lineOf 2 1 ≠ 0 :=
  ⟨by decide, maskWord_mem, maskWord_ne_zero⟩

/-! ### Teeth, both directions — the single-round teeth lifted to depth -/

/-- The schedule whose ROUND-0 challenge is zero. -/
def γzeroSched : ℕ → ZMod 5 := padSched ![0, 1]

/-- **Teeth 1a — hiding is the binding constraint at depth**: one zero
round-challenge refutes multi-round zero-knowledge outright (round 0 opens
a symbol, so its mask is published unmasked). -/
theorem zeroKnowledge_fails_at_zero_round :
    ¬ RbrZeroKnowledge roundMask roundQuery γzeroSched :=
  not_rbrZeroKnowledge_of_zero 0 (by decide) (by norm_num)

/-- **Teeth 1b — knowledge is NOT what fails there**: at that same
zero-round schedule (against alternates `(1, 2)` — pairs distinct at every
link) the chain extractor still recovers the full witness list `[0,
oneWord]`, by kernel computation. The γ-dial kills hiding, never
extraction: `zeroKnowledge_fails_at_zero` + `extraction_survives_at_zero`
(`Selvage/ZkArgument.lean`), now at the chain. -/
theorem extraction_survives_zero_round :
    extractChain (ι := Fin 4) γzeroSched (padSched ![1, 2]) (xWord + oneWord)
      ![xWord + oneWord, xWord + (2 : ZMod 5) • oneWord] = [0, oneWord] := by
  decide

/-- **Teeth 2 — one schedule kills extraction, never hiding**: at the
diagonal (`γalt = γbase`) the chain extraction COLLAPSES (landed
`extract_chain_teeth_diagonal`, cited — every entry erased to `0`), while
`RbrZeroKnowledge` at the same base schedule still holds; its TYPE cannot
even mention a second schedule. One transcript is never enough to extract
(`chain_single_schedule_ambiguous`, landed, is the information-theoretic
form) and is exactly what zero-knowledge is a statement about. -/
theorem one_schedule_kills_extraction_not_hiding :
    (extractChain (ι := Fin 4) γbase γbase (xWord + oneWord)
        ![xWord + oneWord, xWord + (2 : ZMod 5) • oneWord] ≠ [0, oneWord]) ∧
      RbrZeroKnowledge roundMask roundQuery γbase :=
  ⟨extract_chain_teeth_diagonal, rbrZk_base⟩

/-! ### The measured round error, attained on F₅ -/

/-- The round-level ZK error fires and is ATTAINED on the landed round
instance: hiding-failure probability over one uniform challenge is exactly
`zkRbrError (ZMod 5)`. -/
theorem rbrZk_round_error_F5 :
    uniformProb (ZMod 5)
      (fun γ => ¬ MaskedOpeningHiding (constrainedMaskSpace dom₅ 2 pt2) qz γ)
      = zkRbrError (ZMod 5) :=
  rbrZk_round_error dom₅ pt2 (by norm_num) (by norm_num) qz_inj qz_ne_pt2

/-- The number: `1/5` — the same `1/|F|` the soundness round error
`accRbrError` charges at `errstar ≡ 0`
(`AccSoundRbrExample.accRbrError_zero_five`). -/
theorem zkRbrError_F5 : zkRbrError (ZMod 5) = 1 / 5 := by
  unfold zkRbrError
  norm_num [ZMod.card]

end RbrZkExample

/-! ## Residual obligation — prose, not a stub

**`[ZK-RBR-interleave]`** — the cross-round interleaving of the chain
extractor's second-transcript source with the per-round simulators' mask
draws: the genuinely-open remainder of `[ZK-RBR-game]` after this file.
What closed here narrows the frontier to two missing lemmas and one
packaging step, named precisely:

* **Missing lemma 1 — triangular joint hiding.** This file's chain
  simulator (`rbrZeroKnowledge_of_rounds`) is proved for the FRESH-MASK
  PRODUCT model: round `k` opens `mask (fs k) (γs k) (gs k)` — its own
  pre-mask word, its own fresh draw, and `jointMaskFiber`'s round-`k`
  conjunct reads `gs k` ALONE. In the deployed recommitment schedule (WARP;
  `Selvage/Accumulator.lean`'s `foldRoot` recommits the folded word each step)
  round `k` opens the `k`-th PARTIAL FOLD, which contains every earlier
  round's mask: the joint opening map is TRIANGULAR (round `k` reads
  `gs 0 … gs k`), the joint fibers do not factor, and the coordinatewise
  translation of `chain_fiber_equinum` no longer preserves them —
  translating round `j`'s mask moves every later round's opened tuple. The
  repair is visibly available but unbuilt: `MaskedOpeningHiding` quantifies
  over EVERY witness word (`sim_support_univ : ∀ f, …`), in particular over
  the mask-dependent partial fold, so a backward induction over rounds
  (condition on `gs 0 … gs (k−1)`, apply round `k`'s hiding at the
  resulting pre-mask word) should recover joint uniformity — PROVIDED the
  schedule invariant of `Selvage/ZKHiding.lean`'s multi-step residual (each
  committed word is opened at ONE step only) is stated and consumed. That
  induction, on the recursive `foldWords`/`aggregate` word, is the first
  missing lemma. It composes: this file's product composition (the base
  shape), `openSymbols_mask` (openings commute with the fold — the hinge,
  landed), and the recommitment schedule (unformalized).

* **Missing lemma 2 — masked-chain extraction.** `extractChain`'s `n + 1`
  transcripts are, in deployment, ONE straightline FS execution: the
  perturbed evaluations are erasure-corrected from the `t` opened columns
  per round (`[ACC-extract-bind]`, `Selvage/AccExtract.lean`;
  `Selvage/Erasure.lean`'s `recoverFromColumns` at unique decoding) — the SAME
  columns `RbrZeroKnowledge` says are uniform witness-free tuples. The two
  reductions consume the same `t·n` symbols with opposite demands, and the
  resolution is again quantifier position, now at the GAME level: the
  extractor runs against a CHEATING prover in the soundness game, the
  simulator against the HONEST prover in the ZK game — no contradiction,
  but an unproved composition. Concretely: extraction must hold for the
  MASKED protocol, i.e. `extractChain` on masked transcripts must recover
  (witness, mask) pairs and peel the mask at the public challenge
  (`unmask`; single round: `extract_recovers_masked`, landed;
  `extractor_meets_simulator` above computes the depth-2 chain instance
  where link 0's claim IS a mask claim and the extractor's output IS a
  nonzero mask-space element). At arbitrary depth this needs the
  mask-AUGMENTED chain — each round's mask claim entering the fold as its
  own link — and there the extractor's flat family must perturb MASK
  coordinates too: a counterfactual schedule the honest protocol never
  runs, whose perturbed evaluations must still come out of the SAME
  opened-column seam WITHOUT handing the ZK distinguisher a second
  schedule. Whether `[ACC-extract-bind]`'s erasure seam furnishes those
  counterfactuals for mask links exactly as for real links — one FS
  execution serving a two-point extractor on `2n` coordinates while `n`
  fresh masks keep the openings simulatable — is the precise open coupling.
  It composes: `extractChain_sound` (landed), `mem_constrainedMaskSpace_iff_satisfies`
  + `claim₀_satisfies_iff_mem_maskSpace` (the shared mask object),
  `unmask`/`extract_recovers_masked` (landed), `[ACC-extract-bind]`
  (unchanged).

* **Packaging — the game object (both halves).** `[ACC-sound-rbr-game]`
  (`Selvage/AccSoundRbr.lean`) still owes the `Reduction`/`KStateFn`/`extract`
  quadruple for the chain on the SOUNDNESS side; the ZK twin — a simulator
  field inside the SAME SR/FS game object, measured by the game's
  `uniformProb` the way `extract_sound` is — inherits that debt. What this
  file contributes toward it: the round-level ZK error now EXISTS in the
  game's measure idiom (`zkRbrError`, attained at `1/|F|`,
  `rbrZk_round_error`) and coincides with the soundness round error's
  exact-word specialization (`zkRbrError_eq_accRbrError_exact`) — the two
  per-round prices of the one game are on one scale, ready for the
  `(t + k)`-style composition `fsKeystone_proved` already carries on the
  soundness side. Neither half's game instance is faked here.

* **What is NOT at risk.** Every citation is an unconditional landed
  theorem: `constrainedMask_hiding` (+ the sharp iff here),
  `extractChain_sound` / `lightClientKnowledgeSound`, `aggregate_satisfies`,
  `accRbrError`'s bounds, `fsKeystone_proved`. The fresh-mask product
  composition proved here is real multi-round mathematics (the joint
  simulator exists and is uniform), not a restatement of the single-round
  fact — but it is the MODEL's theorem, and the distance from model to
  deployment is exactly lemmas 1 and 2, stated above, not hidden.

## Ledger

* `jointMasks` / `jointOpen` / `jointMaskFiber` (+ `mem_jointMaskFiber`) —
  DEFINED: the multi-round leakage surface and its explaining fibers, the
  joint fiber proved to be the fiber of the joint map.
* `RbrZeroKnowledge` — DEFINED: the round-level ZK vocabulary
  (`[ZK-RBR-game]`'s named missing piece (1)) — per-round hiding + the
  composed chain simulator, witness-free by quantifier position.
* `rbrZeroKnowledge_of_rounds` — PROVED: per-round simulators compose into
  the chain simulator (product model); `rbrZeroKnowledge_iff_rounds` —
  PROVED: audit transparency, no hidden strength.
* `RbrZeroKnowledge.chain_witness_free` / `.jointMaskFiber_ncard_eq` —
  PROVED: whole-schedule witness independence + the one-constant joint
  distribution.
* `not_rbrZeroKnowledge_of_zero` — PROVED: one zero round-challenge refutes
  the multi-round object (teeth, general form).
* `zkRbrError` / `constrainedMask_hiding_iff` / `rbrZk_round_error(_le)` /
  `zkRbrError_eq_accRbrError_exact` — PROVED: the `uniformProb`-measured
  round ZK error, attained at `1/|F|`, dual to (and coinciding at
  exact-word with) `accRbrError`.
* `RbrZkArgument` — DEFINED; `rbrZk_multiround` — PROVED: the multi-round
  coexistence by citation; `γalt` and the `n + 1` transcripts quantified
  ONLY in `knowledge_sound`.
* Keystones — `rbrZk_base`, `rbrZkArgument_F5`, `completeness_fired` /
  `knowledge_sound_fired` / `zero_knowledge_fired` /
  `chain_simulator_fired` (all fields on ONE F₅ instance);
  `claim₀_satisfies_iff_mem_maskSpace` + `extractor_meets_simulator` (the
  extractor's object IS the simulator's object, nonzero, computed);
  `zeroKnowledge_fails_at_zero_round` + `extraction_survives_zero_round`
  and `one_schedule_kills_extraction_not_hiding` (teeth both directions at
  depth); `rbrZk_round_error_F5` + `zkRbrError_F5` (the measured error
  attained).
* Residual — `[ZK-RBR-interleave]` (prose above): triangular joint hiding +
  masked-chain extraction + the game packaging, each with its composing
  pieces named.

`#print axioms` on `rbrZeroKnowledge_of_rounds`, `rbrZk_multiround`,
`rbrZk_round_error`, `RbrZkExample.rbrZkArgument_F5`,
`RbrZkExample.extractor_meets_simulator`,
`RbrZkExample.zeroKnowledge_fails_at_zero_round`,
`RbrZkExample.extraction_survives_zero_round`,
`RbrZkExample.rbrZk_round_error_F5`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
