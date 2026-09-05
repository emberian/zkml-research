# Knowledge-soundness census — minidregg `Selvage/`

**Measured 2026-09-04** against `~/dev/minidregg` at `9db15e7` (138 `Selvage/*.lean`, plus
`Assurance/`, `Compiler/`, `Kernel/` for consumers). Read-only lane; nothing in minidregg
was modified and `lake build` was not run. Turns `forcodex/06-OPEN.md` item 8 — *"Knowledge
soundness, tree-wide — most soundness theorems quantify over a given witness; `Unit`
extractors in places"* — into a ranked work list. Instrument (697 declaration hits), most
of them per-file `F₅` keystones and helpers inheriting their parent's class; the tables
below carry the **structurally distinct** entries only:

```
grep -rn "^\(private \|protected \|@\[[^]]*\] \)*\(noncomputable \)*\(theorem\|def\|structure\|class\|instance\|abbrev\|lemma\)" \
  Selvage/*.lean | grep -i "sound\|knowledge\|extract\|rbr"
```

**Classes.** (K) extractor constructed or ∃-quantified at a nontrivial witness type ·
(S) plain soundness over a given/∀-quantified witness · (U) `Unit` or otherwise
information-free witness/extractor · (H) knowledge soundness stated as a hypothesis or an
uninhabited obligation `Prop`.

## Verdict in one paragraph

The `Unit` extractors are **not** the tree's real gap — all three are deliberate
(`trivialReduction` refutes [OB-2]; `chalReduction` builds FS teeth; `sumcheckReduction`
is a scalar-preservation leg whose docstring says exactly that). The real gap has three
shapes: (1) the tree's **genuine** extractors (`extractPair`, `extractChain`,
`extractMaskedPair`, `seamCounterfactual`) are **never wired into an
`RbrKnowledgeSoundness.extract` field**; (2) the **headline security number**
(`soundnessError deployedBudget ≤ 2⁻⁵⁵`) sums four bounds that are all class (S) or CR —
no extractor enters it anywhere; (3) the **recursion seam**
(`HeteroComposition.KnowledgeSound`) has exactly two inhabitants, both with `Proof = Wit`
and `Rel = Verify`, i.e. identity extractors on non-succinct proofs.

## §1 — The eight `Reduction`s and their witness types

| file:line (`W :=` line) | name | cls | `W :=` verbatim | consumers / headline |
|---|---|---|---|---|
| `Selvage/SumcheckRbr.lean:170` (`:177`) | `sumcheckReduction` | **U** | `W := Unit` | `basefoldSumcheckReduction`; the BaseFold sumcheck leg |
| `Selvage/Depth.lean:478` (`:484`) | `trivialReduction` | **U** | `W := Unit` | `OB2_depth_composition_false`, `fsKeystone_premise`, `ZkRbrGame.game_fs_fired` |
| `Selvage/FiatShamir.lean:539` (`:545`) | `chalReduction` | **U** | `W := Unit` | `fsKeystone_teeth` only |
| `Selvage/AccRbrInstance.lean:380` (`:386`) | `accReduction` | **K** | `W := Fin ch.length → Fin m → F` | `accRbrKnowledgeSound`, `accFsSound_native` |
| `Selvage/AccRbrBcs.lean:322` (`:328`) | `accReductionBcs` | **K** | `W := Fin ch.length → Fin m → F` | `accRbrKnowledgeSoundBcs`, `accFsSound_bcs`, `Assurance/SemanticHistoryBcsGame.lean:586`, Tower256 checkpoint game |
| `Selvage/AccRbrBcsShifted.lean:219` (`:225`) | `accReductionBcsShifted` | **H** | `W := Fin ch.length → Fin m → F` | its `RbrKnowledgeSoundness` is a `Prop` (`:374`), **not inhabited** (`:552`) |
| `Selvage/AccRbrBcsRaw.lean:25` (`:40`) | `accReductionBcsRaw` | — | `W := Fin ch.length -> Fin m -> F` | verifier reflection only; header `:7-9` disclaims all soundness |
| `Selvage/AccRbrFold.lean:467` (`:473`) | `foldReduction` | **H** | `W := W` (free, `AddCommGroup W` + `Module R W`, `:436`) | `foldRbrOfRoundBound`, `fold_fs_sound` — all caller-conditional |

Aliases inheriting the acc witness type: `accReductionBcsShiftedLinked`
(`OracleLogLinked.lean:431`), `linkedReduction`, `preimageLinkedReduction`,
`twoPhaseReduction`, `junkLinkedReduction`, `historyBcsReduction`.

⚠ **Stale docstring.** `HeteroComposition.lean:15-17` asserts *"All seven `Reduction`
instances in the tree are intra-system"* and enumerates seven; `foldReduction` is an
**eighth** (`AccRbrFold.lean` mtime Aug 17, `HeteroComposition.lean` Aug 14). The claim it
supports stays true of the eighth; only the count is wrong.

## §2 — The six `RbrKnowledgeSoundness` constructions

| file:line | name | cls | `extract :=` verbatim | what it computes |
|---|---|---|---|---|
| `Selvage/SumcheckRbr.lean:268` | `sumcheckRbrKnowledgeSound` | **U** | `extract := fun _st _tr _w => ()` (`:278`) | nothing; `err = d/|F|` |
| `Selvage/Depth.lean:524` | `trivialRbr` | **U** | `extract := fun _ _ w => w` (`:526`) | identity on `Unit`; `err ≡ 1` |
| `Selvage/AccRbrInstance.lean:635` | `accRbrKnowledgeSound` | **K** | `extract := fun st tr w => accExtract C st.x ch δs tr w` (`:646`) | reads the last transcript word, installs `decodeLink` at slot `len−1` |
| `Selvage/AccRbrBcs.lean:526` | `accRbrKnowledgeSoundBcs` | **K** | `extract := fun st tr w => accExtractBcs C st.x ch δs dom d q tr w` (`:539`) | erasure-decodes the round word from opened columns, then `accExtract` |
| `Selvage/AccRbrFold.lean:581` | `foldRbrOfRoundBound` | **H** | `extract := extractFn` (`:587`) | pass-through of a caller-supplied function |
| `Selvage/BaseFoldRbr.lean:82` | `basefoldSumcheckRbr` | **U** | (application of `sumcheckRbrKnowledgeSound`) | nothing; `err = 2/|F|` |

`Assurance/SemanticHistoryBcsGame.lean:707` `knowledgeSoundness` and
`…Tower256CheckpointGame.lean:301` `idealHistoryFiatShamir` apply the two (K) rows — the
deployed Tower256 retained-history game is the tree's strongest extractor consumer.

## §3 — Constructed extractors **not** in any `.extract` field

| file:line | name | cls | returns | wired into |
|---|---|---|---|---|
| `Selvage/AccExtract.lean:87` | `extractPair` | **K** | `(ι → F) × (ι → F)` | `accKnowledgeSound` (`:153`); **no** `RbrKnowledgeSoundness` |
| `Selvage/AccExtractChain.lean:272` | `extractChain` | **K** | `List (ι → F)` | `extractChain_sound` (`:306`), `lightClientKnowledgeSound` (`:341`), `RbrZeroKnowledge.lean:453`, `ZkRbrGame.lean:282` — all non-`Reduction` structures |
| `Selvage/ZkExtraction.lean:444` | `extractMaskedPair` | **K** | `(ι → F) × (ι → F)` | `MaskedChainExtraction` (`:522`) |
| `Selvage/ZkExtraction.lean:699` | `seamCounterfactual` | **K** | `ι → F` | `extractChain_committed_seam` (`:781`) — one execution + its opened columns |
| `Selvage/OracleLogLinkedTarget.lean:57` | `linkedShiftedLogExtractor` | **K** | `Fin ch.length → Fin m → F` | `OracleLogReduction`; `linkedAdaptiveIncrementSound_proved` (`…Assembly.lean:461`) at the true `accRbrError` |
| `Selvage/OracleLogLinkedSubUd.lean:212` | `linkedSubUdLogExtractor` | **K** | same | `twoPhaseOracleLogFsSoundness_le` (`…TwoPhaseSoundness.lean:468`) |
| `Selvage/OracleLogSatisfiable.lean:60` | `shiftedOracleLogReduction_one` | **U** | — | real extractor, **trivial price** `εlog ≡ 1` (§8) |

`AccExtractChain.lean:524-530` files the attachment under *"Residual obligations — prose,
not stubs"*; `AccSoundRbr.lean:76-83` gives the reason: *"The natural realizer is
two-point, not one-point … WARP's backward round extractor (Def 4.2) is seeded from a
SINGLE extended transcript per round."*

## §4 — Named obligations (H)

| file:line | name | status |
|---|---|---|
| `Selvage/HeteroComposition.lean:61` | `KnowledgeSound` | hypothesis of `rung_sound` (`:96`) and `ivc_tower_sound` (`:115`); **both have zero consumers tree-wide** |
| `Selvage/AccRbrFold.lean:1073`, `:1078` | `plainCommitSystem_knowledgeSound`, `foldSystem_knowledgeSound` | the **only** two inhabitants of `KnowledgeSound`; both set `Proof := W = Wit` and `Rel = Verify`, proof term `fun _x π h => ⟨π, of_decide_eq_true h⟩`. Docstring `:1043` is honest: *"the proof IS the short opening, so knowledge-soundness is definitional … no extraction is claimed"* |
| `Selvage/AccRbrFold.lean:566` | `FoldRoundBound` | inhabited only at `εfold ≡ 1` (`foldRoundBound_one`, `:594`); identity extractor at `ε ≡ 0` **refuted** (`toy_roundBound_zero_id_false`, `:1277`) |
| `Selvage/AccRbrBcsShifted.lean:374` | `accRbrKnowledgeSoundBcsShifted` | a `Prop`; ledger `:552` — *"STATED …: NOT inhabited"* |
| `Selvage/ZkRbrGame.lean:230` | `ZkRbrGame.fs_composed` | field takes `rbr : RbrKnowledgeSoundness red` as a premise; discharged only at `trivialReduction` (`game_fs_fired`, `:491`) |
| `Assurance/SpartanR1CS.lean:704` | `SpartanOpeningProtocol` | `∀ c, Accepts c → c.Holds S dom`; not discharged — stated over `MleEvalClaim` so *"a discharging lane (BaseFold's braided reduction, or Ligerito) proves exactly this"* |
| `Assurance/SpartanR1CS.lean:731` | `SpartanSparseEvalOracle` | cost obligation, not discharged; refutable (`:737`) |
| `Selvage/HeteroComposition.lean:230`, `:240` | `ComposeErrorBound`, `ComposeFixedPoint` | obligation `Prop`s; **not** implied by `OB2_depth_composition_nonneg` |
| `Selvage/LigeritoInterleaved.lean:406`, `:422` | `MatVecProductSound`, `LigeritoSound` | obligation `Prop`s, deliberately abstract |
| `Assurance/Tower256RawHistoryFsExecution.lean:301` | `NativeMcaPrice.ofSoundness` | takes `sound : FsStraightlineKnowledgeSoundness …` as an argument |
| `Selvage/RingSwitching.lean:386` | `LargeFieldMlePcs.Extractable` | hypothesis — **discharged** for the LCH handle at `AdditiveBasisBinding.lean:245`, refuted for span-only handles at `:340` |

## §5 — (S) soundness over a given witness, and what rests on it

| file:line | name | witness position | headline it supports |
|---|---|---|---|
| `Selvage/LightClientSound.lean:520` | `lightClientSound` | `ws : List (ι → F)`, `f₀` are **parameters** | `Assurance/SelvageV0.lean:186` `.sound`; `loomV0_light_client` (`:201`) — README's light-client suite |
| `Selvage/LightClientGrinding.lean:455` | `lightClientGrinding_sound` | same, per candidate chain | **`Assurance/ErrorBudget.lean` `grindingTerm` — the DOMINANT term of `soundnessError deployedBudget ≤ 2⁻⁵⁵`** |
| `Selvage/LightClientFS.lean:303` | `lightClientFS_sound` | same | fixed-chain FS transport |
| `Selvage/Sumcheck.lean:243` | `sumcheck_soundness` | prover/honest families given | `ErrorBudget.sumcheckTerm` |
| `Selvage/BaseFoldIor.lean:233`, `:78` | `basefoldIor_exact_sound`, `…_wrong_value_sound` | `word`/`table` are **parameters** | `Assurance/ZkmlMatmulBaseFold.lean:50,68,86` — the three zkML matmul claims |
| `Selvage/AccSound.lean:543`, `:667` | `foldClaims_sound_proximity_UD(')` | words given | `accRbrError`, hence every RBR error above |
| `Selvage/Proximity.lean:689` · `DeciderProximity.lean:289` · `Decider.lean:88` | `proximity_sound`, `deciderProx_sound`, `decider_sound` | words given | `SelvageV0Guarantee.decision` |
| `HalfThresholdFriTranscript:466`, `…FriQuery:417`, `…Coherent:217`, `AdditiveFriQuery:691,781` | `committedFri_sound_*`, `friAdaptive_*_sampled_sound` | committed word given | the FRI query layer |
| `Rank1GradientCheck:287` · `MultilinearExtension:652` · `QuadraticSumcheck:246` | `rank1_sound`, `mle_sumcheck_soundness`, `quad_sumcheck_soundness` | tables given | zkML gradient / matmul lanes; `HashRelation:88,160,253` + `HashRelationInverse:98` `GraphSound` are the same shape for the S-boxes |

**The sharpest reading.** `Assurance/ErrorBudget.lean:9-27` names the four priced events
behind `≤ 2⁻⁵⁵`: `lightClientGrinding_sound`, `sumcheck_soundness`, `commitCR_of_RO_pow`,
`hasMutualCorrelatedAgreement_UD`. All four are (S) or CR bounds. **No extractor enters
the deployed security number.** It is honest as *soundness*; it is not a
knowledge-soundness number, and the file never claims it is.

## §6 — Class counts

**(K)** 2 `Reduction`s (+6 aliases), 2 `RbrKnowledgeSoundness` instances (+2 downstream
applications), 6 constructed extractors. **(S)** ~20 distinct headline theorems (≈200 hits
counting keystones). **(U)** 3 `Reduction`s, 3 `RbrKnowledgeSoundness` instances, 1
trivial-price extractor. **(H)** 2 `Reduction`s, 1 `RbrKnowledgeSoundness`, 11 named
obligations.

## §7 — Ranked upgrade list

**1. `sumcheckReduction.W : Unit` → the committed table (BaseFold's PCS leg).** Change
`SumcheckRbr.lean:177` `W := Unit` to a table type and `basefoldSumcheckReduction`
(`BaseFoldRbr.lean:35`) so its source relation reads *"`rt` commits `basefoldWord dom tbl`
**and** `H = mle tbl z`"* rather than today's `R := fun _ H _ _ => H = mle table z` with
`table` a definition parameter; give `extract` the `accExtractBcs` shape (the erasure
decode is landed at `Erasure.recoverFromColumns_sound`). **Unblocks the most:** discharges
`SpartanOpeningProtocol` (`SpartanR1CS.lean:704`), gives `ZkmlMatmulBaseFold`'s three
matmul claims an extractor instead of a given word, retires
`MultilinearCommitment.lean:24`'s stated remainder (*"the remaining object is exactly the
braided BaseFold `Reduction`/`RbrKnowledgeSoundness` instance"*), and is the only upgrade
that gives `basefoldSumcheck_fs_sound` a consumer — today it has none (§9).

**2. Wire `extractChain` into an `RbrKnowledgeSoundness.extract`, or straightline it.**
`[ACC-sound-rbr]`. The blocker is at `AccSoundRbr.lean:76-83` (two-point realizer vs
one-point Def-4.2 seed); the material to fix it exists — `seamCounterfactual`
(`ZkExtraction.lean:699`) synthesizes the perturbed transcripts from **one** execution's
opened columns. Concretely: turn `lightClientKnowledgeSound`'s hypotheses `hbase`/`hpert`
(`AccExtractChain.lean:341` — `n+1` separately-given verifying transcripts) into a
conclusion derived from the same `ws`/`f₀` that `lightClientSound` is anchored at. That
closes the decoupling `Assurance/SelvageV0.lean:119-121` names in its own docstring
(*"Deliberately independent parameters `ws`/`f₀` … versus `γs`/`h₀`/`hs`"*) and makes
`SelvageV0Guarantee`'s `sound` and `knowledge` fields talk about one prover.

**3. Supply a nontrivial `extractFn` for `FoldRoundBound` (`AccRbrFold.lean:566`).** The
whole additive/Nova lane is caller-conditional: `foldRbrOfRoundBound`,
`fold_depth_composition`, `fold_fs_sound`, `fold_fs_price_msis` all take `extractFn` and
`h : FoldRoundBound … extractFn εfold`, and the only values ever passed are the identity
at `ε ≡ 1` — with `ε ≡ 0` machine-refuted (`:1277`). Replace the parameter with a
**constructed** `foldExtract : Stmt → Transcript → W → W` producing the shorter-prefix
relaxed opening, and prove `FoldRoundBound … foldExtract (fun _ => ε_MSIS)`. This is
`[ACC-rbr-fold-resid](a)`; 06-OPEN item 4 already tracks its `ε_MSIS` home.

**4. Inhabit `HeteroComposition.KnowledgeSound` at a system with a succinct proof.** Both
existing inhabitants (`AccRbrFold.lean:1073`, `:1078`) set `Proof := W = Wit` and
`Rel := Verify`, so extraction is the identity and the "proof" is the entire witness.
Build a `ProofSystem` from `accReductionBcs` with `Proof := SrOutput r s`,
`Verify := fiatShamir r s O`, `Wit := r.W`, `Rel := r.R`, and prove `KnowledgeSound` from
`accFsSound_bcs`'s extractor. Until then `rung_sound`/`ivc_tower_sound` are
hypothesis-shaped with **zero consumers**: no recursion or IVC claim in the tree rests on
real extraction.

**5. Inhabit `accRbrKnowledgeSoundBcsShifted` (`AccRbrBcsShifted.lean:374`) — or retire it
in favour of the log route.** It is the constrained-mask fold-root schedule, the
ZK-carrying deployed shape, explicitly not inhabited. Meanwhile
`OracleLogLinkedAssembly.lean:461` `linkedAdaptiveIncrementSound_proved` **does** close a
log-extractor version of the same content at the true `accRbrError`, extractor pinned by
construction (`linkedTarget_pins_extractor`, `OracleLogLinkedTarget.lean:199`; teeth at
`:238`). Either transport that into a Def-4.2 object or amend `:552`'s ledger to say the
log route supersedes it — leaving both standing reads as an open hole half-closed
elsewhere.

## §8 — Honest-by-design, with the quoted justification

**`basefoldSumcheckReduction`'s `W = Unit` — `Selvage/BaseFoldRbr.lean:120-125`:**

> ⚠ Read the content exactly. This reduction's witness type is `Unit`
> (`sumcheckReduction`'s `W`), so `FsStraightlineKnowledgeSoundness` here is straightline
> *soundness* with a trivial extractor, not extraction of the committed table: `R` is
> `claimedValue = mle table z`, a statement predicate. Extracting the committed
> multilinear is the commitment layer's job (`MleEvalClaim`, Merkle binding,
> `[COMMIT-CR]`), not this leg's.

**Agreed as a scope statement, with one caveat.** The deferral is correct — the leg does
preserve a scalar, and the table is pinned by `MleEvalClaim.holds_iff_of_committed`
(`MultilinearCommitment.lean:96`). But the composition it defers to **does not exist as a
theorem** (`MultilinearCommitment.lean:24`: the remaining object is exactly the braided
reduction), and `basefoldSumcheck_fs_sound` has no consumer outside its own file. The
file's stated purpose (`:110-113`, *"Without the theorem below the instance is an
island"*) is half-achieved — the RBR object gained a consumer, the FS theorem did not.

**`trivialReduction`/`trivialRbr` (`Depth.lean:478`, `:524`).** `W := Unit`,
`extract := fun _ _ w => w`, `err ≡ 1`. Correct by construction: its purpose is
`OB2_depth_composition_false` (`:545` — the audited [OB-2] statement is FALSE at `Z = ∅`)
and `fsKeystone_premise` (`FiatShamir.lean:630`); a refutation vehicle should be as small
as possible. Same for **`chalReduction`** (`FiatShamir.lean:539`), which exists solely so
`fiatShamir_teeth` (`:574`) can exhibit a proof string the FS verifier rejects under one
oracle and accepts under another.

**`ZkRbrGame.game_fs_fired` at `trivialReduction` (`ZkRbrGame.lean:485-495`).** The
docstring is honest — *"this keystone shows the carrier field genuinely fires, not that
the residual is closed."* ⚠ But it is now **stale**: `Selvage.lean:56` records that
`AccRbrInstance`'s `native_fs_fired` runs the same `fs_composed` field on the native pair,
*"where `game_fs_fired` could only offer `trivialReduction`"*. Mark it superseded.

**Trivial-price inhabitants, correctly labelled.**
`shiftedOracleLogReduction_one` at `εlog ≡ 1` (`OracleLogSatisfiable.lean:60`) — *"This
establishes satisfiability only; the intended `accRbrError` instance remains refuted"*,
paired with the refutations at `OracleLogProgram.lean:367` and `OracleLogLinked.lean:809`.
`foldRoundBound_one` at `εfold ≡ 1` (`AccRbrFold.lean:594`) — the satisfiability half of an
ATLAS pair whose other half (`:1277`) refutes `ε ≡ 0` with the identity extractor.

## §9 — Absence claims, with the grep

- **No `sorry`, no `axiom` declaration** in `Selvage/` or `Assurance/`:
  `grep -rn "^ *sorry\|:= sorry\| sorry$" --include='*.lean' Selvage/ Assurance/` → empty;
  `grep -rn "^axiom \|^noncomputable axiom" --include='*.lean' Selvage/ Assurance/` → empty.
  And `grep -rn "depends on axioms" --include='*.lean' Selvage/ | grep -v "propext, Classical.choice, Quot.sound"`
  returns only strict *subsets* (e.g. `AccRbrFold:1444` `[propext, Quot.sound]`).
- **`extractPair`/`extractChain`/`extractMaskedPair`/`seamCounterfactual` are in no
  `.extract` field**: `grep -rn "extract := " --include='*.lean' .` → six hits
  (`SumcheckRbr:278`, `Depth:526`, `AccSoundRbr:55` prose, `AccRbrInstance:646`,
  `AccRbrBcs:539`, `AccRbrFold:587`), none naming those four.
- **`basefoldSumcheck_fs_sound` has no consumer outside `Selvage/BaseFoldRbr.lean`**: `grep -rn "basefoldSumcheck_fs_sound" --include='*.lean' Assurance/ Compiler/ Kernel/ Theory/ Pred/ Effects/` exits 1.
- **`rung_sound`/`ivc_tower_sound` have no consumers**: `grep -rn "rung_sound\|ivc_tower_sound" --include='*.lean' .`
  outside `HeteroComposition.lean` returns `Selvage.lean:141` and `AccRbrFold.lean:1045`,
  both docstrings, no proof terms.
- **`W := Unit` occurs exactly three times tree-wide**:
  `grep -rn "W := " --include='*.lean' Selvage/ Assurance/ Compiler/ Kernel/` →
  `SumcheckRbr:177`, `Depth:484`, `FiatShamir:545` (Unit); `AccRbrInstance:386`,
  `AccRbrBcs:328`, `AccRbrBcsShifted:225`, `AccRbrBcsRaw:40` (acc word family);
  `AccRbrFold:473` (`W := W`).
- **`ZKHiding.lean` and `ZkTriangular.lean` carry no soundness / knowledge-soundness /
  extraction / RBR declaration at all** (everything in them is hiding):
  `grep -nE "^(theorem|def|structure|class|noncomputable def) +[A-Za-z_.']*([Ss]ound|[Ee]xtract|[Kk]nowledge|[Rr]br)" ZKHiding.lean ZkTriangular.lean` → no output.
- **`HeteroComposition.KnowledgeSound` has exactly two inhabitants**:
  `grep -rn "KnowledgeSound (" --include='*.lean' . | grep -v "RbrKnowledgeSoundness\|FsStraightline\|StraightlineSr"`
  → `AccRbrFold.lean:1073`, `:1078` only (plus the definition and docstrings).
