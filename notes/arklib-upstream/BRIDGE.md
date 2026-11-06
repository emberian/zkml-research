# Selvage's state-restoration keystone, derived from ArkLib (initiative 15 (b))

Branch `lane/arklib-sr-bridge` on minidregg (tip f00e39c75, pushed, not merged), package
`bridges/arklib-ud` (opt-in; the minidregg root does not take ArkLib). ArkLib is pinned at
`4d9d67b`. The whole package builds on bb2 under `swarm-build` (4082 jobs), with no `sorry` and
axioms pinned to `propext, Classical.choice, Quot.sound`. Cross-model check 2 (gpt-6-astra) results
are below.

## What is proved

`SelvageArkLib.StateRestoration.straightlineSrKnowledgeSoundness_of_arklib`: for every Selvage
`Reduction` with `[Finite r.PMsg]`, every `RbrKnowledgeSoundness r`, statement set `Z` and
`εrbr` with `0 ≤ εrbr δ` and `rbr.err i st δ ≤ εrbr δ` on `Z`, the conclusion is

    StraightlineSrKnowledgeSoundness r Z (fun _ t δ => (t + k) * εrbr δ)

with extractor `srExtract rbr`. This is `OB2_depth_composition_nonneg`'s and `FsOfRbrSound`'s
conclusion at their hypotheses plus finiteness. `fsStraightlineKnowledgeSoundness_of_arklib` gives
the FS form. `srExtract_bound_of_arklib` is the same bound for the named extractor, adversary by
adversary.

The probability argument is ArkLib's `restored_extraction_bound`. The bridge uses none of Depth's
probability tower (`gameSlotBound_proved`, `freshBad_le`, `hitBad_fibre_le`, `card_resolve_runFrom`,
`OB2_depth_composition_nonneg_proved`). It uses Depth's definitions (`wAt`, `srExtract`, `runFrom`,
`stepOnce`, `resolveIn`), their one-line lemmas, and the counting equalities `uniformProb_equiv`
and `uniformProb_congr`.

| Piece | File | Statement |
|---|---|---|
| L1 certificate | `StateRestoration.lean` | `selvageExtractor_isProverPreserving`, `selvageExtractor_isLocallyBounded`: Selvage's `prover_monotone`/`extract_sound` are ArkLib's prover preservation and all-prefix local bound (`badChallenge` is Selvage's event verbatim) |
| L2 extraction | `StateRestoration.lean` | `extractWitness_selvageExtractor`, `backward_nil_eq_wAt`: ArkLib's named extraction is `wAt … 0` = `srExtract`, independent of `δ` |
| L3 coupling | `StepCoins.lean` (generic, VCVio only) | `evalDist_run_randomOracle_eq_stepCoins`: the lazy random oracle equals the one-coin-per-query oracle averaged over iid coins, jointly with the cache, for every coin count and dependent answer types |
| L4 correspondence | `Restoration.lean` | injective move→key encoding (junk moves at input `.inr`, never in `Z`); `adversarySteps_run` (moves = Selvage's `runFrom`); `complete_run` (completion = Selvage's final-challenge resolution) |
| L5 assembly | `Keystone.lean` | `restoredExecution_run`, `prEvent_answerTape_eq_ofReal`, the keystone |

## Cross-model check 2 (gpt-6-astra, read-only, on f00e39c75's parent d0d711b96)

- **B1 CONFIRMED:** the conclusion is literally Selvage's, with the extractor chosen first. The
  extra hypothesis is `[Finite r.PMsg]` (docstring corrected).
- **B2 vacuity REFUTED:** the identity carrier cast and the proved `arkEvent ↔ selEvent` mean the
  bridge adds no restriction. Junk keys keep `.inr q` and cannot collide with completion keys; they
  consume a coin and count toward `Q = t` but are never charged as bad keys.
- **B3 CONFIRMED:** the coin disciplines match. Completion's cache writes cause no mismatch,
  because final prefixes have distinct lengths.
- **B4 PARTIAL:** no probability-tower proof is used, but the counting equalities are, and the
  tower stays an import dependency through `Selvage.FiatShamir → Selvage.Depth`.
- **B5 PARTIAL:** restricting the message alphabet per adversary is sound. The obstruction was the
  quantifier order `∃ E ∀ … P`. It is fixed by naming the extractor (`srExtract_bound_of_arklib`),
  so the closure is now a transport.

## The infinite-alphabet gap, explicitly

ArkLib requires `Round.finiteMessage`; Selvage allows any nonempty `PMsg`. Closure plan, judged
sound by check 2, and not yet built:

1. For fixed `P, s, t`, let `M_P` be the finite set of messages in every move prefix and every
   output over all coin vectors (finite because `Chal` is), plus one default message.
2. Build the restricted reduction `r'` (message type the subtype on `M_P`, verifier precomposed
   with the inclusion). Relations, witnesses and challenges are unchanged; `Stmt r' ≃ Stmt r`
   canonically.
3. Pull `kstate` and `extract` back along the transcript map, giving `rbr'`.
   `extract_sound` transfers because Selvage's quantifies over all `π`.
4. Build the retyped prover `P'`. Prove `srTrace P' c = (srTrace P c).map lift` and the matching
   `srFinalChal` and `srExtract`; `lift` is injective on moves over `M_P`.
5. Apply `srExtract_bound_of_arklib` to `r', rbr', P'` and transport the event.

Estimated at roughly 300–400 lines. Until it lands, the derived statement covers finite message
alphabets. That includes every deployed instance with field-element, Merkle-root or bounded-word
messages, since these are finite types.

## Which Selvage FS/Depth declarations become derivable (for ember's retirement decision)

Derivable now, on finite `PMsg` (the full statements follow once the closure lands):
- `OB2_depth_composition_nonneg_proved` (`Depth.lean:1956`), its statement only.
- `FsOfRbrKeystone.sound` / `fsKeystone_proved`'s `sound` field (`FiatShamir.lean:639–643`), via
  `fsOfRbrSound_iff_depth`.

Could become unused, but **must stay today**:
- These tower lemmas have consumers outside the keystone, under `Selvage/OracleLog*`:
  - `freshBad_le` (`OracleLogLinked`, `OracleLogExtraction`)
  - `hitBad_fibre_le` (`OracleLogLinked`, `OracleLogProgram`)
  - `card_resolve_runFrom` and `splitAtGame` (`OracleLogLinkedTwoPhaseHorns`, `OracleLogProgram`)
  - `gameSlotBound_proved` (`OracleLogExtraction`, `OracleLogLinked`, `OracleLogProgram`)
- `GameSlotBound` is a stronger per-slot statement than the aggregate bridge establishes (check 2),
  so it is not derivable from the bridge.

Stay regardless:
- Definitions: `Reduction`, `KStateFn`, `RbrKnowledgeSoundness`, `srTrace`, `srFinalChal`, `wAt`,
  `srExtract`, `stepOnce`, `runFrom`, `resolveIn`.
- The `uniformProb` counting toolkit (used across Assurance/Compiler/Selvage, e.g.
  `uniformProb_prod_le` in 25 files).
- `fsStraightline_iff_sr`, the ROM handler and its laws, the teeth and premise witnesses
  (`chalReduction`, `trivialReduction`), and `OB2_depth_composition_false`.

What retirement would cost: minidregg's root would have to take ArkLib (VCVio, CompPoly, PolyFun)
as a dependency; the bridge is opt-in today precisely to avoid that. The cheapest useful step is to
keep both proofs and record in Selvage's keystone docstring that the statement is independently
derived from ArkLib's theorem at `bridges/arklib-ud/SelvageArkLib/Keystone.lean`. Selvage then
retains its own proof and gains an external cross-check, with no dependency change. Retiring Depth's
tower would save at most the ~1,000 lines unused by OracleLog*, and only after the root takes
ArkLib. My recommendation: cross-check, do not retire.
