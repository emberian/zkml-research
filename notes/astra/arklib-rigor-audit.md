# ArkLib rigor audit — 2026-11-06

[INFERRED] **Take the coding theory through explicit adapters; retain Selvage's protocol/compiler boundary.** ArkLib's proof engineering has materially improved since our earlier evaluation. The main audited protocol statements now have proof bodies rather than admissions, the production source has four explicit admissions, with upstream tooling intended to isolate their dependents, and the known unrestricted-adversary KZG vacuity has been repaired. This supports a selective dependency, not replacing the verifiable-compute stack or declaring deployment soundness repaired by an import.

[READ] Evidence labels: `[READ]` means the cited source statement/body was inspected; `[MEASURED]` means the linked command ran here; `[INFERRED]` means a mathematical or engineering conclusion from that evidence; `[OPEN]` names an unexecuted integration obligation. These correspond to this repository's SOURCE / EXECUTED / DERIVED / OPEN labels. No paid searches were used. No ePrint PDFs were downloaded.

## Snapshot and verification scope

[MEASURED] Ran `git -C /Users/ember/src/ArkLib fetch origin`. It advanced `origin/main` from `9349870ae4c0f2a31ec4874d5c3d8fa733c03c4f` to **`4d9d67be64634f09a85206238df9380aa3733a93`**, commit subject “Drop unnecessary hypotheses in Reed-Solomon list decoding and MCA (#1464)”, timestamp `2026-11-05 20:48:55 -0700`. The original detached checkout was clean and was preserved. Created a separate detached `/Users/ember/src/ArkLib-latest` at that fetched main. This was the latest upstream main observed at fetch time, not a guarantee about future upstream commits.

[MEASURED] Compared against minidregg **`c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`**. All ArkLib paths below are relative to `/Users/ember/src/ArkLib-latest/`; all Selvage paths to `/Users/ember/dev/minidregg/`. Full source pins, command outputs, manifests compared, and disk/build observations are in [arklib/snapshot.json](arklib/snapshot.json).

[MEASURED] Disk available before worktree creation: **133 GiB**. Root's clarified pressure threshold is **Avail <30 GiB**, not percentage used. There was no large local build or multi-GiB download. No companion repository working-tree file was edited.

[OPEN] **This is a source and statement audit, not a fresh successful Lean build.** The latest checkout and original ArkLib checkout both have no `.lake` dependencies or build products. A cold full build is not light enough for this Mac under the task rules. Fresh kernel axiom closure and the integration build **must run on hbox under `swarm-build`**, after the machine rules are read. The committed upstream baseline and acceptance-client source are useful evidence, not a substitute for that run.

## 1. Reproducible rigor census

[MEASURED] Command: `python3 notes/astra/arklib/census.py /Users/ember/src/ArkLib-latest`. [Script](arklib/census.py), [complete output](arklib/census-output.txt), [every file](arklib/census-files.csv), [every directory](arklib/census-directories.csv), [occurrences with source lines](arklib/census-occurrences.json), [summary](arklib/census-summary.json). The scanner masks nested block comments, line comments, strings and quoted identifiers with ArkLib's pinned `scripts/source-trust-audit.py` lexer. Its five mutation tests were run and passed; [output](arklib/scanner-tests.txt). Counts exclude dependencies. The per-directory CSV includes zero-count directories; no directory is silently dropped. The upstream source-trust instrument was also executed over production and acceptance sources (`python3 scripts/source-trust-audit.py --json …`): [inventory](arklib/upstream-source-trust.json), [output](arklib/upstream-source-trust.txt). It checks `admit`/`sorryAx` and `Lean.ofReduceBool`/`Lean.trustCompiler` as well as the requested spellings.

| Source scope | Lean files | Lines | `sorry` | `axiom` | `native_decide` | `opaque` | `implemented_by` | `set_option maxHeartbeats` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Production `ArkLib/` | 1,152 | 332,566 | 4 | 0 | 0 | 0 | 0 | 0 |
| Acceptance `ArkLibTest/` | 253 | 44,468 | 0 | 0 | 0 | 0 | 0 | 0 |
| Tooling / deliberate fixtures `scripts/` | 27 | 3,798 | 0 | 7 | 0 | 2 | 0 | 0 |
| Blueprint Lean | 1 | 16 | 0 | 0 | 0 | 0 | 0 | 0 |

[READ] The tooling axioms/opaques belong to sweep mutation fixtures and tooling, not production theorem declarations. The 23 production occurrences of `unsafe` are **Aesop search-rule classifications**, not Lean `unsafe def` declarations; the occurrence list makes this distinction inspectable. An `opaque` definition with a checked body would not itself be an axiom escape; there are none in current production in any case. Raising heartbeats affects proof search resources, not logical trust; again none were found in current production.

[MEASURED] Requested component-directory counts (all other escape columns are zero in every row):

| Directory | Files | `sorry` | `axiom` / `native_decide` / `opaque` / `implemented_by` / `maxHeartbeats` |
|---|---:|---:|---|
| `Data/CodingTheory` | 386 | 4 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/Sumcheck` | 35 | 0 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/Fri` | 50 | 0 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/BatchedFri` | 4 | 0 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/Binius` | 41 | 0 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/RingSwitching` | 42 | 0 | 0 / 0 / 0 / 0 / 0 |
| `OracleReduction/Composition` | 22 | 0 | 0 / 0 / 0 / 0 / 0 |
| `OracleReduction/Security` | 31 | 0 | 0 / 0 / 0 / 0 / 0 |
| `OracleReduction/FiatShamir` | 2 | 0 | 0 / 0 / 0 / 0 / 0 |
| `OracleReduction/BCS` | 1 | 0 | 0 / 0 / 0 / 0 / 0 |
| `ProofSystem/Stir` | 6 | 0 | 0 / 0 / 0 / 0 / 0 |
| `Commitments` | 71 | 0 | 0 / 0 / 0 / 0 / 0 |

[READ] The four source admissions are:

1. `ArkLib/Data/CodingTheory/ListDecodability/Bounds/Linear.lean:1041`, random-linear-code list-size lower bound (GLMRSW22).
2. `ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon.lean:86`, RS superpolynomial list-size lower bound (BKR06).
3. `ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon.lean:611`, **random-domain RS list-size upper bound** (AGL24).
4. `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean:341`, near-capacity CA lower witness (KKH26 / ABF26-T4.16).

[INFERRED] Therefore yesterday's “lower bounds only” description is false in scope: item 3 is an upper bound. This is not a defect in the audited Johnson theorem, which has a different proof, but it rules out describing the whole coding-theory library as admission-free.

[READ] `scripts/axiom_baseline.json` has **zero ordinary `sorry` debt entries, five `solicited` entries, zero nonstandard entries**. Five declarations can depend on four source admissions because a wrapper is also tainted. The five names are retained in the snapshot JSON. `scripts/AxiomSweep.lean:250–305` traverses declaration types and values, requires solicited entries to retain `sorryAx` and linked issue documentation, and rejects dependence on them from non-solicited declarations. `:68–100` allows standard Lean axioms only and has an **empty** native-trust grandfather list. The upstream gate is substantially stronger than raw grep. [OPEN] Its current successful execution was not reproduced here.

[MEASURED] All **1,152** tracked production modules are present in the umbrella's import clauses, including line-wrapped clauses; [import-coverage.json](arklib/import-coverage.json). This checks source coverage, not elaborated transitive axioms. A broad import can load a module containing an unrelated admission without making a target theorem depend on that admission; only declaration closure distinguishes those cases.

### The historical count was misstated

[MEASURED] Like-for-like command: `python3 notes/astra/arklib/history-census.py`. It reads Git archives in memory with the same lexer, writes no historical checkout, and produces [history-census.json](arklib/history-census.json).

| Pinned production tree | Files | Code `sorry` | `axiom` | `native_decide` | `opaque` | `implemented_by` | `maxHeartbeats` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `9349870` (August baseline) | 347 | 203 | 0 | 0 | 1 | 0 | 7 |
| `22dbd4e` (September baseline) | 430 | 183 | 0 | 0 | 0 | 0 | 0 |
| `4d9d67be` (fetched main) | 1,152 | 4 | 0 | 0 | 0 | 0 | 0 |

[INFERRED] The supported September-to-current source claim is **183 → 4**, not **292 → 4**. Our earlier `notes/formal-delta-2026-09-04.md:65–71` already gave 183. Its 314 and August 416 counts refer to **tainted declarations**, not source `sorry` occurrences. These instruments cannot be mixed. Nor does every removed admission represent a proved theorem: the STIR headline and duplex-sponge development were removed, as earlier notes acknowledged.

## 2. Build and integration feasibility

[MEASURED] Both repositories pin `leanprover/lean4:v4.35.0` and Mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**. All nine shared manifest packages match exactly (full comparison in snapshot). ArkLib additionally pins VCVio `9054989327a7185ff19ef9ff0f119cccea479501`, CompPoly `a1ac8925bde72472724e978d7aa9b94bef3149d9`, PolyFun `4181c82238142d9b73403fbf4c4b13e1a801e400`, QuantumFoundations and other build/doc dependencies. Matching pins remove the earlier Lean/Mathlib-version conflict; they do not establish a compatible semantic adapter or a successful Lake dependency merge.

[READ] `lakefile.toml` enforces `requiresModuleSystem = true` for production and attaches the compiled `ArkLibLintPlugin`; acceptance clients deliberately use classic modules for proof-body visibility and `#print axioms`. `scripts/validate.sh` includes the library, 253 acceptance clients, import coverage, source policy, and runtime checks; its `--axioms` mode runs the sweep regression fixtures and `lake exe axiomsweep --check`. VCVio FFI submodules are additionally needed by executables (`validate.sh:147–154`). These are real build requirements beyond a Mathlib pin.

[OPEN] Build acceptance on hbox should pin this SHA, preserve existing worktrees and caches, run via `swarm-build`, build the narrow selected imports first, then their classic acceptance clients and target axiom closures. A whole-library validation is a separate heavier check. No command is marked successful until its log exists. Do **not** interpret “one bridge file” as a one-file cold build.

## 3. Component decisions and statement audit

The detailed coding-theory and protocol reads below distinguish (a) theorem validity and nonvacuity, (b) comparability, (c) compiler integration. A numeric witness establishes that assumptions can hold; it is not a Lean elaboration certificate unless explicitly labelled as executed.

### Decisions, exact imports, and native consumers

[READ/INFERRED] “Import” below means introduce a pinned dependency and prove the adapter named by its obligations. It does **not** mean replace the local theorem with an identically typed declaration; there are no such drop-in replacements in this table. Keep the old sharper/generic results when they have distinct scope.

| Component | Verdict | Exact ArkLib module and declaration | Selvage theorem whose use changes / comparison |
|---|---|---|---|
| Full-relative-UDR RS CA/MCA | **IMPORT via adapter** | `import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa`; `ProximityGap.rs_epsCa_le_of_le_relUDR` (`EpsCa.lean:81`), `ProximityGap.rs_mcaError_le_of_le_relUDR` (`:179`) | Add a wider-range alternative to `reedSolomonCode_isProximityGenerator_UD_sharp` (`Selvage/ProximityGapUDSharp.lean:113`); direct MCA replaces the affine-line instance's use of `reedSolomonCode_hasMutualCorrelatedAgreement` (`Selvage/ReedSolomon.lean:207`) with an external `hPG`. **Incomparable quantitative packages**: radius improves, `n/q` is worse than local `(floor(δn)+1)/q` on overlap. Do not delete either generic/local theorem. |
| Johnson RS MCA | **IMPORT via adapter** | `import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability`; `ReedSolomon.mcaError_affineLine_johnson_le` (`Probability.lean:41`) | Replace the *conditional invocation* of `mutualCA_johnson` (`Selvage/JohnsonRegime.lean:523`) at explicit imported `err`, thereby bypassing `whirConjecture412_rs_of_haboeck` (`Selvage/JohnsonMcaBridge.lean:331`) and its `hHab`/envelope premise for that instance. Foundationally stronger direct MCA with explicit error; not arbitrary-`err` dominance or automatic JBR73 closure. |
| BCIKS20 RS affine-line CA | **IMPORT via adapter** | `import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main`; `ProximityGap.RS_correlatedAgreement_affineLines` (`Main.lean:40`) | Supplies the actual RS `IsProximityGenerator` instance consumed by `reedSolomonCode_hasMutualCorrelatedAgreement` (`ReedSolomon.lean:207`) / `mutualCA_johnson_of_conj` (`JohnsonRegime.lean:507`), instead of an external premise. **Incomparable** to `CorrelatedAgreement.lean:325`'s arbitrary-code/weighted-generator implication; retain that theorem. |
| BCIKS20 curves / affine spaces | **DEFER direct dependency until a caller; reference/adapter candidate** | `ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves`, `correlatedAgreement_affine_curves` (`:786`); `ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces`, `correlatedAgreement_affine_spaces` (`:1154`) | No bespoke native theorem to replace. Could supply concrete premises to `hasMutualCorrelatedAgreement_of_isProximityGenerator` (`Selvage/CorrelatedAgreement.lean:325`). Curve-degree multiplier and uniform-subspace-vs-coefficient sampling must survive. |
| Sumcheck | **MIRROR / KEEP native** | `ArkLib.ProofSystem.Sumcheck.Spec.General`, `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` (`:513`), `oracleVerifier_knowledgeSoundness` (`:528`) | `Selvage/SumcheckRbr.lean:268` `sumcheckRbrKnowledgeSound`, `:334` `sumcheckRbr_err`; both charge degree/cardinality on shared Boolean specialization. ArkLib has arbitrary finite evaluation domain; native object plugs into our compiler. No direct replacement. |
| FRI soundness | **MIRROR / cross-check** | `ArkLib.ProofSystem.Fri.Spec.Soundness`, `Fri.Spec.soundness_proximity` (`:57`), `soundness` (`:81`), `rbr_soundness` (`:100`); numeric module `ArkLib.ProofSystem.Fri.ErrorBounds` | `Selvage/HalfThresholdFriQuery.lean:417` `friAdaptive_sampled_sound`. **Incomparable**: ArkLib actual oracle execution + powers-MCA; Selvage opened words + ideal binding + fold transition premise. |
| Binary BaseFold | **MIRROR / ADAPT** | `ArkLib.ProofSystem.Binius.BinaryBasefold.General`, `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_and_knowledgeSoundness` (`:324`) | Stronger assembled interactive evaluation opening than local algebraic completeness `Selvage/AdditiveBaseFold.lean:553` `lch_opening_complete`; different security object from `AdditiveFriQuery.lean:781` `additiveFriAdaptive_coherent_sampled_sound_UD`. No drop-in replacement. |
| Ring switching + Binary BaseFold | **ADAPT / MIRROR into native compiler** | `ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch`, `Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness` (`:261`), completeness conjunction (`:277`) | **No existing Selvage ring-switch theorem to replace.** New representation/basis/extractor bridge required; neither `lch_opening_complete` nor an import statement alone provides it. |
| FS / BCS / restoration / depth | **DIVERGE / KEEP native** | No ArkLib soundness transport found; §4 | Native `FsOfRbrSound`, `fsKeystone_proved`, repaired depth theorem; no import replacement. |

### The definitions and hypotheses have content

[READ] The complete statement-level evidence is in [coding-audit.md](arklib/coding-audit.md) and [protocol-audit.md](arklib/protocol-audit.md). They include Lean-shaped signatures, exact source lines, ambient hypotheses, initial/terminal relations, and event interpretation. The following are the consequential findings:

- **RS degree convention agrees; rate conventions need conversion.** Both codes use degree **< dimension**. ArkLib's sharp Johnson theorem uses reduced rate `(k-1)/n`, while local `johnsonRadius` is expressed at `k/n`. ArkLib's MCA is a supremum over every actual input-word family of a projected-code agreement failure (`ProximityGenerator/Basic.lean:119–125,191–194`); local `MutualCAFailure` uses existential extending codewords on the same coordinate set (`Selvage/CorrelatedAgreement.lean:277`). Neither omits the word. The adapter must prove code equality, bad-event equivalence, finite-uniform probability conversion, and supremum elimination at that input tuple.
- **Johnson is actually proved upstream.** `Johnson/Probability.lean:41–65` obtains an exceptional-slope set from the polynomial reconstruction result and translates it to MCA, with no `hHab` or `hPG` assumption. Its exact upper bound is `min 1 (johnsonExceptionCount/q)`. The printed BCHKS25-style estimate is separately derived in `CapacityBounds.lean:235–295`; importing that broad umbrella is unnecessary for the core result and loads an unrelated admitted theorem.
- **Sumcheck names the polynomial and terminal obligation.** The relation (`Sumcheck/Spec/SingleRound.lean:145`) is the partial sum of a bounded-individual-degree polynomial at a sampled prefix, not merely an accepting trace. Guarded sequential composition at `General.lean:519` is real. A terminal evaluation backend remains necessary.
- **FRI's statement is an acceptance bound.** The input relation names the initial word and actual RS code; ordinary adaptive soundness is proved against any prover. Error is `sum foldingError + (1-min θ δ)^l`, with each folding error the actual next code's powers-generator MCA. The numeric theorem requires generalized-Johnson radius/slack conditions: for binary folding its wired exponent is **1/3**, not the affine-line Johnson exponent **1/2**. Do not import the latter number without the generator bridge. This theorem is not Merkle/FS or native-verifier soundness.
- **Binary BaseFold's initial escape is closed.** Although the internal invariant is `badEventExists ∨ good`, `Relations/Initial.lean:55` proves no initial bad event, and `:84` extracts the real initial conjunction. Security is unique-radius first-oracle compatibility; completeness is exact encoding. Its functional uniqueness is codeword uniqueness, not short-digest collision resistance.
- **Ring switching really shares one object.** `FRIBinius/RingSwitch.lean:65,75` proves equality of frontend output and backend input relations, including the packed polynomial and first oracle. Its total error includes the frontend `κ/q + 2ℓ'/q` **in addition to** BaseFold's ledger. The basis has size `2^κ`; over a two-element base this forces extension size `2^(2^κ)`, not arbitrary field parameters.

### Explicit nonvacuity witnesses

[MEASURED/INFERRED] Exact arithmetic for the coding witnesses was executed by [coding-witness.py](arklib/coding-witness.py), with [retained output](arklib/coding-witness.out). Protocol arithmetic appears in [protocol-audit.md](arklib/protocol-audit.md). These are mathematical witnesses with executed arithmetic, **not newly elaborated Lean examples**.

| Component | Inhabited witness and useful bound |
|---|---|
| UD MCA | `F=ZMod 1000003` (trial-division prime checked), 16-point embedded domain, dimension 5, `δ=5/16`; `δ≤11/32` UDR and `δ>11/48` local one-third ceiling; error `16/1000003<1`. |
| Johnson MCA | Same field/domain/dimension, `δ=3/8`, reduced rate `1/4`, slack `1/8`, multiplicity 4. The **printed comparison numerator** is `157527`, giving upper bound `157527/1000003<1`; the raw exception-count theorem is no larger by the comparison lemma. This is genuinely beyond UDR and below the local rounded Johnson radius. |
| BCIKS line / curve / space | Same field/domain, `δ=1/4`, line/space error `16/1000003`; quadratic curve `32/1000003`. Directions `1,X` are independent and all generated words are codewords, so the probability premise fires in a non-singleton affine space. |
| Sumcheck | `ZMod17`, Boolean evaluation domain, one variable, degree cap 2, polynomial `X₀²`, claimed sum 1, singleton state/empty ambient oracle; error `2/17<1`. Claiming sum 0 falsifies the input relation. |
| FRI | `ZMod257`, 16-point multiplicative domain with primitive root 2, one binary fold to constants, eight queries, `θ=δ=1/4`, distance 1, slack `1/8`; generalized estimate ≤`38612963/50528256<1`. Zero polynomial is honest; a half-zero/half-one word has distance 1/2 from the initial affine code. |
| Binary BaseFold | `K=GF2`, `L=GF16=K[X]/(X⁴+X+1)`, basis `(1,α,α²,α³)`, `r=4`, `ℓ=R=ϑ=1`, four repetitions; bound `177/256<1`. Zero source/first oracle/claim honest; claim 1 on that oracle false. |
| Ring switch + BaseFold | Same basis, `κ=2`, `ℓ'=R=ϑ=1`, source-variable count `ℓ=3`, four repetitions; bound `241/256<1`. Dimension, divisibility and rate premises all hold. |

[INFERRED] The coding example also has a positive bad event: `f₀=0`, `f₁=X⁵` fails MCA exactly at slope zero, probability `1/q`. Nonzero slopes cannot agree with a degree-<5 polynomial on the required ten or more coordinates by root counting. This prevents the numerical witnesses from merely inhabiting an everywhere-trivial code.

[REFUTED: proposed Johnson smoke-test bound] The earlier suggestion `ZMod17,n16,d4` cannot obtain `<1` from the printed Johnson bound: the expression is **greater than `16807/51>329`** at every allowed nonnegative radius. It is not an empty hypothesis or a counterexample to MCA; it is a useless upper estimate at that small field. UD still gives `16/17<1`. The larger-field witness repairs the intended Johnson check.


## 4. Fiat–Shamir / BCS: retain our compiler

[READ] `ArkLib/OracleReduction/FiatShamir/Completeness.lean:720–745` proves `fiatShamir_completeness_randomOracle`: an input reduction's completeness error is preserved under a shared lazy challenge oracle with decidable query-key equality. The premise is inhabited by a one-step honest pure reduction (or the empty identity reduction) and a finite challenge alphabet. This is meaningful **completeness**, not a soundness theorem. The next line, `:747`, leaves state-restoration (knowledge) soundness to FS as a TODO.

[READ] `ArkLib/OracleReduction/BCS/Basic.lean:14–35` says the generalized transform is not formalized. Its only defined transformation is `ProtocolSpec.renameMessage` at `:54–57`; the later `OracleReduction` namespace contains variables and no BCS security theorem. A zero-sorry count here is absence of the transform, not proof of it.

[MEASURED] Absence corpus/instrument: all tracked production `ArkLib/**/*.lean` at the audited SHA, lexical search for `fiatShamir.*(sound|Sound)`, `FiatShamir.*(sound|Sound)`, `bcs.*(sound|Sound)`, `BCS.*(sound|Sound)`, plus full reads of the two FS modules and the BCS module. No FS/BCS soundness declaration was found there. This is scoped to ArkLib's production source, not all VCVio, the literature, or private branches.

[READ] Selvage's matching object is `Selvage/FiatShamir.lean:512–521` `FsOfRbrSound`, proved through `fsOfRbrSound_iff_depth` and `fsKeystone_proved` (`:639–642`), with `(t+k)·εrbr` and explicit nonnegativity. `fsKeystone_oracle_inhabited`, `fsKeystone_teeth`, `fsKeystone_premise` (`:617–633`) provide inhabitation/nontriviality witnesses. `Selvage/Depth.lean:1956` proves `OB2_depth_composition_nonneg_proved`; `:544` refutes the unguarded original. [INFERRED] **DIVERGE / KEEP** our FS, state restoration and depth compiler; there is no corresponding ArkLib soundness theorem to import or replacement name to give. ArkLib's completeness theorem and our soundness compiler are different properties, not competing numerical bounds.

## 5. Earlier blockers: which actually disappeared?

[READ] Historical corpus: `notes/formalization-frontier.md`, `notes/formal-delta-2026-09-04.md`, `notes/binaryspartan-position.md` §§11–12, `notes/sis-lattice-verdict.md`, `docs/SELVAGE.md`, `docs/BINARY-POSITION.md`; found with `rg -n -i ArkLib notes docs`, followed by section reads. The known KZG incident is additionally recorded in `/Users/ember/dev/breadstuffs/GOAL-ARKLIB-VACUITY.md`. We did not use the forbidden companion trees.

| Earlier blocker / overclaim | Current source finding | Status |
|---|---|---|
| Composition, sumcheck, FRI and Binius security statements admitted | Proof bodies now present; guarded sequential composition is the actual API; no source admissions in these directories | **Gone at the source-statement level**, fresh closure/build still open |
| Johnson MCA admitted and only partial UD available | Proved direct Johnson MCA and full-relative-UDR MCA present; adapter and quantitative differences remain | **Mathematical gap repaired upstream**, integration gap remains |
| Binary leaves contain 32–33 admissions; FRI-Binius no soundness statement | Zero source admissions, BinaryBaseFold and ring-switch composition security statements present | **Gone for audited cone**, does not certify Binius64 implementation |
| FS / BCS compiler absent | FS completeness exists; FS soundness TODO; BCS stub | **Persists** |
| STIR/WHIR end-to-end soundness | Current STIR components are source-clean; prior main theorem removed; no WHIR protocol theorem audited | **Persists**, do not count deletion as completion |
| Lean/Mathlib version mismatch | Same v4.35.0 and all shared manifest pins | **Gone today**, not a promise across future upgrades |
| VCVio/CompPoly framework dependence | Extra dependencies and OracleReduction/OracleComp versus Selvage finite-uniform semantics | **Persists**, isolate pure-code adapters |
| KZG binding assumes t-SDH for all Lean functions, hence vacuous below 1 | `HardnessAssumptions.lean:107` restricts to `Adv`; `:116` proves unrestricted assumption impossible; `Binding.lean:757` provides assumption-free reduction and `:786` requires reduction membership | **Actual repair landed**, inspect each adversary class before claiming concrete security |
| No proof connection to deployed Rust prover | Library theorems describe interactive oracle relations and abstract reductions | **Persists** |
| Coarse proof-engineering hygiene / source-only census | Module system, classic acceptance clients, guarded source policy, no heartbeat overrides, native-trust zero floor, taint sweep with solicited-isolation gate | **Materially improved**, fresh build not performed here |

[READ] KZG repair is a useful pattern for our binding task. `ArkLib/Commitments/Functional/KZG/Binding.lean:757–778` proves the actual binding experiment is bounded by its explicitly constructed t-SDH reduction's experiment, without an impossible universal hardness hypothesis. The bounded corollary (`:786–799`) carries both a restricted adversary set and membership of that reduction. [INFERRED] An empty adversary set would still make the assumption trivial, but cannot satisfy the separate membership premise for an actual adversary; this is precisely the guard an advantage-carrying interface needs. This repair does not instantiate hash commitment binding.

## 6. Proposed maintainer corrections (not edits to VERDICTS)

[INFERRED] Replace the §9 headline “import it to discharge our Johnson hypothesis and our one-third UD band” with: **“ArkLib now contains proved direct RS MCA bounds at full UDR and up to Johnson. Adopt a pinned coding-theory dependency through an event/rate/probability adapter; retain Selvage's sharper one-third-band bound where it wins. The deployed Johnson budget remains conditional until that adapter and every downstream proximity/FRI premise are discharged.”**

[INFERRED] Replace 292→4 with the measured **183→4 production code-token** comparison at the named September/current SHAs. Keep the older transitive-taint figures separately labelled. Withdraw “lower bounds only”, “a dependency edit, not a port”, and any implication that importing ring-switching statements automatically makes them consumable by Selvage's compiler.

[OPEN] Task-completion meaning: the requested audit and import/mirror/diverge recommendation are delivered. The proposed dependency/semantic bridge and full upstream build remain concrete future engineering work; no PR branch claiming those changes exists in this run.
