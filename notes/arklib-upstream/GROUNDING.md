# Initiative 15 grounding: Selvage's RBR→FS/BCS compiler and upstream ArkLib

Lane: initiative 15 (ArkLib upstream contribution). Date 2026-11-06. Pins: ArkLib upstream `main` at
`34613d617` (2026-11-06, "Drop unnecessary hypotheses in the remaining coding-theory theorems (#1465)"),
fork clone `/Users/ember/src/ArkLib-fork` (remote `upstream`, branch `upstream-main`; PR heads fetched
as local refs `pr-1269 pr-1274 pr-1277 pr-1280 pr-1283`, read-only). Selvage at minidregg `c4ecabe0f`.

## Verdict

**The initiative's premise is false at upstream head, and the bar as written should be withdrawn.**
ArkLib already has the round-by-round → state-restoration knowledge-soundness theorem, merged, with
the same `(Q + k)·ε` bound as Selvage's keystone and a sharper per-round form. The state-restoration
→ Fiat–Shamir bridge is open in a stacked series of PRs by ArkLib's lead maintainer (about 6,300
lines, all CI-passing and mergeable). On the shared fragment, upstream's statements are at least as strong as
Selvage's on every axis but one (infinite prover-message alphabets). Selvage has no general BCS
compiler to contribute: its "BCS" is one accumulator-chain instance over a perfectly binding
commitment. A PR-ready "Selvage compiler" branch would duplicate the maintainer's in-flight work,
be weaker than it, and go against CONTRIBUTING's blueprint-first rule for large contributions.

The critique's verdict "ours is ahead: RBR-to-FS/BCS compiler, state restoration, accumulation depth"
(`notes/selvage-foundations-critique-2026-11-05.md:35-40,60,72-75,200`) and Astra's §4 "DIVERGE /
KEEP" (`notes/astra/arklib-rigor-audit.md` §4) need correcting. Astra's absence search used the patterns
`fiatShamir.*sound` and `bcs.*sound`, plus full reads of `OracleReduction/FiatShamir/` and `OracleReduction/BCS/`.
The theorem lives in the native interaction layer, `ArkLib/Interaction/Oracle/Security/StateRestoration*.lean`
(merged 2026-10-08, #1263; so it was present at the audited SHA `4d9d67b` too). The pattern missed
`stateRestoration_knowledge_soundness`. The critique quotes upstream's own status line ("no Fiat–Shamir
or BCS bridge from state restoration", `docs/design/00-current-status.md:435`). That line is true but
narrow: the bridge is missing, while the RBR→SR theorem it bridges from is present.

## What upstream has (read, with exact statements)

Merged on `main`:

| Declaration | File | What it says |
|---|---|---|
| `stateRestoration_knowledge_soundness` | `Interaction/Oracle/Security/StateRestorationGame.lean:102` | For a fixed-round public-coin protocol (`List Round`; each round has a finite `DecidableEq` message, a finite nonempty uniform challenge), a per-input `KnowledgeState` and `RoundExtractor` with `IsProverPreserving` and `IsLocallyBounded … (uniformSchedule error rounds)` on `Z`, endpoint laws `inputLaw`/`outputLaw` identifying states with arbitrary `Rin`/`Rout`, and any adversary `OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)` with `IsTotalQueryBound adversary Q`: `Pr[z ∈ Z ∧ Rout … ∧ ¬ Rin z (extractInputWitness …)] ≤ (Q + rounds.length) * error`, in VCVio's cached `randomOracle`, with completion on the same cache and the actual verifier executed (`verificationGame_eq`). |
| `stateRestoration_oracle_knowledge_soundness` | `StateRestorationOracle.lean` | Same bound when the verifier returns an open oracle claim closed under the path's handler. |
| `stateRestoration_oracle_knowledge_soundness_nonuniform` | `StateRestorationBudget.lean` | Per-round errors: `Q * max_j ε_j + Σ_j ε_j`. |
| `stateRestoration_knowledge_soundness_privateCoins` | `StateRestorationCoins.lean` | Same `(Q + k)·ε` with pre-sampled private coins. |
| measured-extraction wrappers | `StateRestorationResources.lean`, `KnowledgeResources*` | Declared instruction budgets for the named extractor along a path. |

The certificate is CY/WARP-style backward RBR knowledge: `KnowledgeState := ⟨Witness, holds⟩` per prefix
(`Knowledge.lean:37`). `RoundExtractor` holds total backward witness maps (`:52`), and `IsProverPreserving` (`:202`)
says sender moves preserve. `badChallenge` (`:331`) is `∃ w, ¬ state.holds (map w) ∧ after.holds w`.
`IsLocallyBounded` (`:359`) bounds it at **every authored verifier prefix, including zero-probability ones**.
Nonvacuity: `ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean` fires the theorem at
`error = 1/2` with a bad event of probability exactly 1/2 (`badChallenge_iff`, `bounded`, `actual_game_bound`).
`grep sorry ArkLib/Interaction` returns nothing.

Open, stacked, by Quang Dao, all CI-passing and `MERGEABLE` on 2026-11-06:
#1267 → #1268 (randomized interleaved-coin restoration; expected distinct-key counts) → #1269 (native
Sumcheck SR soundness `(Q+k)·d/|F|`) → #1274 (stopped restoration: verifier halts before a failed guard's
query; cost of queries actually made) → #1277 (**native single-salt Fiat–Shamir knowledge soundness**,
`Interaction/Oracle/FiatShamir/SingleSaltSecurity.lean`: `singleSalt_knowledge_soundness` bounds by the
expected fresh-query charge, and `singleSalt_knowledge_soundness_queryBound` by `Q * max ε + Σ ε`, against
an adversary `OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)` with interleaved private
coins) → #1283 (encoded external random-oracle queries with off-image keys at weight zero). #1280 adds honest FS
completeness from native execution. Also open: #469 (duplex-sponge FS, Section 5 statements; Nguyen, Orrù, Zheng),
#1258 (the CY-textbook literature map and contract).

BCS on upstream: `OracleReduction/BCS/Basic.lean` is a stub. Issue #627 (Abraxas1010, legacy layer) has
stage-1 commit-then-reveal completeness in a private staging clone and fences soundness. `docs/design/04-oracle-elimination-compiler.md`
fixes the native architecture: `BCS = HashChainFS(iBCS)` per Chiesa–Yogev, with passes RepresentOracles → LowerAccesses →
TransportBoundary → FiatShamir and a Merkle/ROM backend specified as game-indexed capability records.
The roadmap (`docs/design/05-roadmap.md` "Merkle adapter") says the first Merkle backend adapter
"has not started" and must adapt VCVio's existing shared-ROM extractability theorem, not restate it.

## Selvage, theorem by theorem, against upstream

| Selvage | ArkLib counterpart | Strength on the shared fragment |
|---|---|---|
| `Oracle`, `respond_*`, `srHandlerRun_*`, `srFinalChal_eq_lookup` (`FiatShamir.lean:111-431`): lazy-sampling handler as a list log; the coin-vector SR game is a handler run | VCVio `randomOracle` (cached `QueryImpl`) + `simulateQ … run' ∅` | VCVio's is the general object; Selvage's is a finite special case (deterministic adversary, `t` indexed coins). Nothing to add upstream. |
| `fiatShamir`, `fiatShamir_congr`, `query_injective`, `fsOracle` (`:260-310`) | `#1277` `PublicMessage`, `PublicExecutionCorrespondence`, `singleSaltExecution_eq_stopped` | Upstream runs the actual native verifier strategy and proves an equality of oracle programs; Selvage substitutes a total function. Upstream stronger. |
| `fsStraightline_iff_sr` (`:475`): FS game = SR game | `#1277` `singleSaltExecution_eq_stopped`, `inducedAdversary` | Same idea; upstream's covers early rejection and interleaved coins. |
| `StraightlineSrKnowledgeSoundness` (`Rbr.lean:415`) / `FsOfRbrSound` (`FiatShamir.lean:512`), proved as `OB2_depth_composition_nonneg_proved` (`Depth.lean:1956`), error `(t + k)·ε_rbr` | `stateRestoration_knowledge_soundness` (merged), `singleSalt_knowledge_soundness_queryBound` (#1277) | **Equal bound, upstream more general.** Map: `Reduction`→`List Round` + terminal program; Selvage `RelaxedMem R δ`/`RelaxedMem R' δ` → `Rin`/`Rout` (arbitrary, so the relaxed WARP relations are instances); `empty_iff`→`inputLaw`; `prover_monotone`→`IsProverPreserving`; `full_iff`→`outputLaw`; `extract_sound`→`IsLocallyBounded` with `badChallenge` (literally the same event). Upstream gains: arbitrary dependent witness types per prefix; adaptive `OracleComp` adversaries and (in the stack) interleaved private coins; per-round `Q·max ε + Σε`; expected fresh-key charge; early stopping; oracle outputs; infinite inputs/salts; the extractor sees only the completed path and output witness (Selvage's `SrExtractor` type may also read the query log, a weaker demand in the statement, though the proved `srExtract` ignores it, `Depth.lean:310`). Selvage-only: prover-message alphabets need not be finite (`Round.finiteMessage` is required upstream); the extractor is quantified `∃ E ∀ δ ∀ s` (one extractor for all `δ` and salt sizes) explicitly. Upstream gets this by construction (`extractInputWitness` reads only the witness maps, which in a WARP instance are `δ`-independent), but does not state it. Selvage's `SrMove` also admits junk queries (any prefix length, `Rbr.lean:319`), which upstream's typed `Key` cannot express. A literal transport must simulate them, which is what #1283's off-image encoded keys (weight zero) provide. |
| `OB2_depth_composition_false` (`Depth.lean:544`): the unguarded statement is false at `Z = ∅, ε = -1` | — | It refutes Selvage's own transcription (its "specialization 7"), not a published theorem (the file says the paper never meets the corner). It cannot arise upstream: errors are `ENNReal`. Not a contribution. |
| `gameSlotBound_proved`, `freshBad_le`, the lazy resolver (`Depth.lean:1108-1956`) | `restored_extraction_bound` and VCVio's cached-oracle cost lemmas (VCVio#823) | Same proof idea (fresh-vs-hit attribution of the `k` final prefixes to the `Q + k` budget); upstream's handles repeated and out-of-order queries and expected counts. |
| `accReductionBcs`, `accRbrKnowledgeSoundBcs`, `accFsSound_bcs` (`AccRbrBcs.lean:327-760`) | none general | **Not a compiler.** One RBR instance for the accumulator chain at a root+columns+openings message alphabet, over `BindingCommitment`, whose `binding` field is perfect binding (`Commitment.lean:122`; `no_bindingCommitment_compressing` `:462`: no compressing inhabitant). The CR-priced route (`ColumnEquivocation`, `bcsWord_or_columnEquivocation`) is a per-message split, not a ROM extraction theorem. Upstream's Merkle/ROM requirements (`04` §4: single-trace and stateful multi-extractability over the shared ROM) are of a different, harder kind. |
| `AccRbrBcsShifted` (lagged fold-root schedule) | none | Instance-specific to Selvage's accumulator; no upstream consumer. |
| `CorrelatedAgreement`, the `bridges/arklib-ud` equivalences | ArkLib coding theory | Already bridged in the import direction (`SelvageArkLib/UniqueDecoding.lean`, `Johnson.lean`); irrelevant to the compiler. |

## Cross-model check 1 (gpt-6-astra, read-only, 2026-11-06)

Asked to refute C1 (upstream ⊇ Selvage on the shared fragment), C2 (upstream nonvacuous), C3 (no
general BCS in Selvage) and C4 (FS bridge in flight). Verdicts: **C1 PARTIAL**: the SR mathematics is
duplicated, `badChallenge` has the existential inside the probability exactly as Selvage's does, and no
extractor-uniformity counterexample exists. Literal subsumption needs an adapter for junk queries and
the δ-uniform extractor, and excludes infinite message alphabets. **C2 CONFIRMED**, with a limitation:
the acceptance client fires at `Q = 0` with a pure adversary, so adaptive queries are not exercised
there (a point for the review). **C3 CONFIRMED** (`Commitment.lean:180`, `isEmpty_of_card_lt`), noting
`AuthMapCommitment.lean:97` (`v = w i ∨ OpeningCollision …`) as real reduction material.
**C4 PARTIAL** (codex had no GitHub access); I checked it directly: PR heads fetched, diffs read, all seven
stacked PRs `MERGEABLE` with CI `SUCCESS=5, SKIPPED=1`. Codex independently named the Merkle extraction
adapter as the most valuable non-duplicative contribution, with the shape
`∃ E : Root → CommitLog → Data, ∀ A Q, TwoPhaseQueryBound A Q → Pr[accepted ∧ answer (E root commitLog) q ≠ response] ≤ ε_VCVio(tree, Q)`
(one shared cache across commit, open and verify; VCVio's error preserved unchanged).

## Literature (credit)

The RBR→SR→FS route is Canetti, Chen, Holmgren, Lombardi, Rothblum, Rothblum, Wichs (STOC 2019) for
round-by-round soundness and Fiat–Shamir. State restoration and the BCS transform are Ben-Sasson, Chiesa,
Spooner (TCC 2016-B), and Chiesa–Yogev's textbook *Building Cryptographic Proofs from Hash Functions* has
the modular `BCS = HashChainFS(iBCS)` proof that upstream's design follows. RBR knowledge in the backward-extractor
form Selvage uses is WARP (ePrint 2025/753) Defs 4.1/4.2, B.2, Thm B.4. ArkLib's interaction-layer theory is
Quang Dao's (with Alexander Hicks on measured extraction); VCVio's cached-oracle accounting is VCVio#823.

## What should replace the bar (my recommendation, as a peer)

1. **Withdraw** "PR-ready RBR→FS/BCS compiler branch". There is nothing of Selvage's to upstream there
   that is not already merged or in review in a stronger form.
2. **Do instead, in this order:**
   a. *Statement review of the #1274 → #1277 → #1283 stack* (a draft for ember, posted only if she
      chooses): check the headline statements against CCHLRR19/BCS16/WARP B.4 and attack them for
      vacuity (guards, `outputLaw` gated by `accepts`, `seed` totality, `freshKeysOfLog` counting,
      off-image weight zero). This is the "review of an in-flight upstream PR" shape, and it is where our
      expertise is worth something to them.
   b. *Retire Selvage's FS/Depth tower onto upstream* (minidregg, `bridges/arklib-ud`, opt-in package
      as now). Prove `StraightlineSrKnowledgeSoundness` for finite-alphabet Selvage reductions from
      `stateRestoration_knowledge_soundness`. That is the formal strength review (ArkLib ⇒ Selvage on the
      shared fragment) and the one Lean artifact that changes something for us. Prerequisite: a coupling
      lemma between Selvage's indexed-coin lazy game (`srTrace`/`srFinalChal` under `uniformProb`) and
      VCVio's cached `randomOracle` for a deterministic `t`-query adversary. VCVio may already have the
      general form; check before proving.
   c. *If ember wants an upstream PR from us anyway*, the non-duplicative item upstream itself names as
      unstarted is the **Merkle backend adapter** (`05-roadmap.md`, "Merkle adapter"). After it comes the
      iBCS step (RBR knowledge of the ideal IOP ⇒ SR knowledge of the Merkle-compiled interactive argument,
      with the Merkle extraction error charged), which then composes with #1277 to give BCS. Per
      CONTRIBUTING ("Large Contributions"), this opens as a blueprint/issue comment on #627 first,
      not a drive-by PR. Selvage contributes no proof to it, only the accumulator client as a consumer.
3. Corrections to land in our notes: the critique lines cited above and Astra's audit §4/§5 row
   "FS / BCS compiler absent → Persists" should read "RBR→SR knowledge soundness merged upstream
   (#1263/#1264); SR→FS in review (#1274/#1277/#1283); BCS absent on both sides."

## Register row

| 15 | ArkLib upstream: RBR-to-Fiat-Shamir/BCS compiler contribution | initiative-15 lane | minidregg, fork of ArkLib | L0 (premise refuted) | as written: withdrawn (upstream has RBR→SR merged, SR→FS in review by the maintainer, stronger than ours); proposed: (a) review draft of #1274/#1277/#1283, (b) Selvage FS/Depth retired onto upstream via an L1 bridge in `bridges/arklib-ud`, (c) a Merkle-adapter/iBCS blueprint for #627 only if ember wants an upstream PR | ember: choose among (a)-(c) | 2026-11-06 |
