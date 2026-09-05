# Nightstream read, 2026-09-04: what its 17 MB of Lean IS, and whether "both legs" changes

2026-09-04. Formal-methods audit lane. `LFDT-Nightstream/Nightstream` ("Lattice zkVM", Lean 17 MB +
Rust 6 MB, ★30, pushed 09-04) implements SuperNeo (eprint 2026/242) with a lot of Lean. Is any of it a
machine-checked *compilation layer* (RBR→FS, BCS at the deployed alphabet, accumulation depth) or a
*concrete* soundness bound? Prior mentions: formal-delta-2026-09-04.md §4/§7 ("axiom-bearing twin",
not cloned), lova-neo-rmfe-read.md §2, neo-verdict.md 09-04 addendum. Clones:
`/Users/ember/src/Nightstream-2026-09` (main) + worktrees `…-fs1`, `…-mc1` (branches, §6).

## 0. Verdict

1. **The claim survives, in their words.** Zero `sorry` on every commit read, but the SuperNeo
   package README: the paper's probabilistic statement — *"PPT adversaries and malicious provers,
   `⟨P*, V⟩` executions, EPT extractors, and the success-probability inequalities of Definitions
   9-10 — is not formalized."* No FS soundness theorem, no BCS/Merkle, no depth theorem, no numeric
   bound (§3–§5). "λ = 125 / floor 96" is a Rust parameter check (`neo-params`), not a theorem.
2. **What the Lean is**: three things on three commits. `main` (07-11): a paper twin (superneo-lean:
   witness-level relation implications over one carried witness), an RV64IM/CHIP-8 kernel model whose
   Rust was deleted, and a direct-CCS IVC-step theorem that *assumes* a sound prior verifier. The
   branch pushed 09-04: all of that deleted, replaced by a Lean-*authored R1CS layout*
   (`nightstream-fprime`, 9,105 theorems) whose headline theorems are row-count equalities plus a
   deterministic "extract-or-name-a-bad-event" composition with no probability attached (§6).
3. **What they have that we do not**: an executable folding pipeline whose recursive-verifier
   circuit is Lean-owned with *kernel-checked row counts*, and a fail-closed `#audit_axioms` gate
   (allowlist `propext, Classical.choice, Quot.sound`) on 4,253 theorems. A real instrument.
4. **Our corrections** (§8): formal-delta "axiom-bearing" → **0 `axiom`** in superneo-lean (185
   `native_decide` instead, Goldilocks primality under the `Field F` instance); neo-verdict "no
   published constraint count … `--ignored` test would print the decider shape" → that test prints
   the *full-history audit* circuit; the recursive step's cost is a Lean theorem on the 09-04 branch:
   **27,537,894 rows** (26-round cut; active 28-round pilot alone 13,600,754). SLVG §I/§IV-b stand.

## 1. Commits [READ, `gh api` + `git log`]

- `pushed_at` 2026-09-04T19:46:01Z is **not main**: main `4696e82` = 2026-07-11 ("Merge #112
  enzo/wasm-vm"); `commits?since=2026-08-15` on main → ∅. Branch tips (`gh api …/commits/<b>`):
  `nico/fprime-stage1-piccs-conformance` `b216df4c` 09-04T14:45-05:00 (= the push),
  `enzo/add-r1cs-builder-crate-neo-application` 09-04, `nico/f-prime-constraints-cuda-formal` 09-02,
  `oai/*` 08-20, `claude/minimizer-campaign` `6e656648` 08-17. 39 branches.
- "Lean 17 MB" = main: `find formal -name '*.lean' | xargs cat | wc -c` → **17,048,531**; Rust
  5,897,321. Org repos (`gh api orgs/LFDT-Nightstream/repos`): Nightstream, Starstream (Rust),
  governance, MVE-Planning — superneo-lean was not relocated; on the 09-04 tip it is gone (§6).

## 2. Inventory of `main` [DERIVED; commands inline]

`find formal -name '*.lean' | wc -l` → **1,015**; `| xargs cat | wc -l` → **267,811**. Six Lake
packages, toolchain v4.28.0 (wasm-zklean v4.25.2). Deps (`lake-manifest.json`): **Mathlib only**
(v4.28.0); nightstream-lean requires superneo/twist-shout as path deps; direct-ccs imports `SuperNeo.*`
(16 files); wasm-zklean requires `GaloisInc/zkLean@014fa397`. **No VCVio, no ArkLib** (Negligible.lean
is a credited VCVio copy, not a dependency).

| package | files | lines | theorem | def | structure | sorry | axiom | native_decide | #guard/example |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| nightstream-lean (RV64IM, CHIP-8, bridge) | 623 | 164,386 | 2,462 | 3,184 | 417 | 0 | 0 | 35 | 0/0 |
| direct-ccs-fprime-lean | 185 | 55,183 | 909 | 349 | 79 | 0 | 0 | 4 | 0/2 |
| superneo-lean (paper twin) | 132 | 36,718 | 1,760 | 828 | 78 | 0 | 0 | 79 | 21/22 |
| twist-shout-lean | 54 | 8,685 | 429 | 339 | 9 | 0 | 0 | 61 (all `tests/`) | 52/110 |
| deprecated/opening-convergence-lean | 17 | 2,559 | 59 | 68 | 13 | 0 | 0 | 6 | 0/0 |
| wasm-zklean (zkLean leaf) | 3 | 280 | 2 | – | – | 0 | **1** | 0 | – |
| **total** | 1,015 | 267,811 | **5,621** | 4,777 | 596 | **0** | **1** | **185** | 73/134 |

Regexes: theorem `^\s*(@\[…\]\s*)?(private |protected |noncomputable )*theorem\b` (`lemma` → 0);
sorry `grep -rw sorry` (0 even before comment-stripping); axiom `^\s*(…)*axiom\b`; `opaque` decls 0
(4 docstring hits); `unsafe`/`implemented_by`/`@[extern]` 0; `#eval` 0; `#print axioms` **0 on main**.

Classification. (a) *Implementation*: `Main.lean`/`CheckCli.lean` (an import-wall grep — all `lake exe
check` verifies), `Golden/GoldilocksGolden.lean`; no `#eval`, no extraction, nothing runs a prover.
Lean is not the zkVM's implementation language; Rust is (§7). (b) *Specification*: 596 structures +
every `*Interface.lean` "machine-checked boundary" beside a prose `specs/*.spec.md`; the RV64IM/CHIP-8
trees model a constraint system whose Rust was removed (wiki/roadmap.md: *"Older documents referencing
a 'published RV32IM proof boundary' describe deleted code"*). (c) *Theorems*: 5,621; name regex
`sound|knowledge|fold|rbr|fiat|shamir|norm_bound|extract|binding|msis` → **879** (top: `Rv64IM/Kernel/
KernelSoundness.lean` 42, `SumCheck/PrefixSoundness.lean` 33, `SumCheck/Game.lean` 33).

## 3. The three measurements, the ArkLib way

- **Literal `sorry`**: 0 / 0 / 0 (main, fs1, mc1; `grep -rw sorry --include='*.lean' formal`).
- **`axiom`**: 1 on main — `wasm-zklean/WasmCircuit/Field.lean:24 axiom goldilocks_prime : Nat.Prime
  goldilocksPrime` (leaf, no dependents); 0 on fs1/mc1. `InvertibilityAxioms.lean` and the 15
  `*Assumption*/*Boundary*` structures (`MSISHardnessBoundary`, `RoundByRoundSoundnessBoundary`,
  `FinalTheoremAssumptions`, …) are **structure-carried hypotheses**, not axioms — formal-delta §4
  misread that filename.
- **Transitive (read, not built)**: the compiler-trust leak is `native_decide`, 185 sites: superneo 79
  (`InvertibilityGoldilocksBase.lean` 32, `GoldilocksPrime.lean` 13, `tests/` 18,
  `InvertibilityAxioms.lean` 7, `ExtensionField` 3, `RingMulComm` 2, `Thm3Core` 2 — Theorem 3 on the
  native basis is `native_decide`), twist-shout 61 (tests), nightstream-lean 35 (`Rv64IM/Execution/
  LoweringRefinementChecks` 8, `Chip8/Kernel/Poseidon2GoldilocksCore` 6, …), deprecated 6, direct-ccs 4.
  **Goldilocks primality is `native_decide`**: `GoldilocksPrime.lean:49 theorem q_prime : Nat.Prime q`
  (seven `native_decide`s), `:62 instance fact_q_prime`. `Field.lean` (`abbrev F := Fin Goldilocks.q`,
  imports GoldilocksPrime) builds `noncomputable instance : Field F` (`:829`) with `fieldInv` through a
  `ZMod q` bridge (`:652–660`, `mul_inv_cancel₀`) — Mathlib's `ZMod` field needs `Fact (Nat.Prime q)`
  [INFERRED by instance resolution; no `#print axioms` on main]. So every theorem dividing in `F` (37 of
  132 files use `⁻¹`/`/`) carries the compiler-trust axiom. Their branch instrument agrees: mc1's
  `tests/Axioms/*.lean` (254 `#guard_msgs`-pinned files) report 430× `[propext]`, 290× `[propext,
  Quot.sound]`, **10× `[Lean.trustCompiler]`**, 4× with `Classical.choice`; `sorryAx` 0.

## 4. The load-bearing statements, verbatim [READ at `4696e82`]

**(1) Final protocol theorem** — `ProofSystem/Protocol.lean:64`:
```lean
theorem finalTheoremShape_of_goldilocksNativePaperCarrierDiffBoundaryPackages
  {ctx : SuperNeo.ProtocolTargetContext} (messageLength : Nat) (hBarNative : ctx.bar = SuperNeo.nativeBarMatrix)
  (hArithmetic : SuperNeo.ArithmeticObligations ctx.bar ctx.m ctx.r … ctx.xEval ctx.expectedEval)
  (hDiff : SuperNeo.samplingDiffSet SuperNeo.paperCarrier ctx.invDelta) (hNe : ctx.invDelta ≠ SuperNeo.zeroRq)
  (hWitness : SuperNeo.SumCheckTransitionWitness ctx)
  (hMsis : SuperNeo.msisHardnessAssumption (SuperNeo.ProofSystem.goldilocksPaperAjtaiParams messageLength)) :
  FinalTheoremShape ctx (…)
```
`FinalTheoremShape … : Prop where completeness ; knowledgeSoundness` (`ProtocolTheorem.lean:693`); the
latter is discharged (`:706`) by `piDECKnowledgeStatement ctx := ∃ deltaInv, mulRq ctx.invDelta
deltaInv = oneRq ∧ ceRelaxedRelation ctx ∧ SumCheckClaimTrue (sumcheckInstanceOfContext ctx)`
(`PiDEC.lean:10`). Read: a context that already carries an accepted sum-check witness satisfies the
relaxed CE relation. No prover, adversary, extractor, or probability. README row S7.6:
*"knowledge-soundness is stated as witness-level composition plus advantage bounds for the carried
failure events rather than as a quantification over PPT adversaries with an extractor."*

**(2) MSIS → binding** — `LatticeReductionsInterface.lean:260 theorem ajtaiBinding_of_msis (hRed :
MSISToAjtaiReductions params) (hMsis : MSISHardnessAssumption params) : AjtaiBindingAssumption params`,
with `MSISHardnessAssumption params := ∃ eps : ErrorFn, IsNegligible eps ∧ MSISAdvantageBound params
eps` (`Lattice.lean:281`), `ErrorFn := Nat → Rat`, negligible = eventually `≤ 1/(n+1)^c` — asymptotic
in a parameter that Goldilocks/κ=18/d=54 never vary with. Exported probability model: `truthProb :
Pr P = if P then 1 else 0` (`LatticeReductions.lean:14`). A shape, not a number.

**(3) Sum-check "advantage bound"** — `SecurityModel/InteractiveReductions.lean:43
sumcheckFailureAdvantageBound_of_assumptions (h : InteractiveReductionAssumptions ctx) (eps)
(hEpsNonneg) : Sumcheck.SoundnessFailureAdvantageBound (…) h.sumcheckTransitionWitness.transcript eps`
— proved by showing the failure event is `False` (the carried witness is honest). The one genuinely
probabilistic statement, `SumCheck/PrefixSoundnessEndpoint.lean:229 SoundnessGame.lundBoundHolds_of_
prefixGapSchwartzZippel … (hAligned : sumcheckLundSoundnessDenominator g.inst = Goldilocks.q) … :
g.lundBoundHolds (fullFieldUniformCoinProbModel g.inst.rounds)` (`advantage × denominator ≤ numerator`,
`Game.lean:488`), is over the *base* field and, per `ProtocolTheoremInterface.lean:156`, *"Retained as
a local replay boundary, not as an active-route final-theorem requirement."* Deployment runs over F_{q²}.

**(4) The "Fiat–Shamir" lemma** — `FiatShamirRerouteInterface.lean:138 rlcParentAuthorityVerifier_
sound_from_parent {fs : ParentAuthorityFS ProtocolTargetContext Digest Challenge} … :
rlcParentAuthorityVerifierAccepts fs … ctx children → rlcParentAuthorityWithDecValidation ctx ∧
continuation (fs.challenge ctx)`. `fs` is a record with a `challenge` function: transcript bookkeeping,
not FS soundness. `grep -rni 'random oracle' formal` → 1 prose line.

**(5) IVC step** — `direct-ccs-fprime-lean/…/DirectParentOnlyProductionSoundness.lean:586
terminal_soundness (ctx : Context …) (verifier : SoundPriorVerifier ctx) … (hAccepted : AcceptedTerminal
…) (hAlt : AlternateLatestStep …) : TerminalSoundness …` = `FPrimeInduction.Reachable (Transition ctx)
ctx.initial (priorSteps+1) nextImage ∧ nextImage = altNext ∧ …`; `Context` carries `msisHardness`. The
prior verifier's soundness is a **hypothesis**; no error accumulates across steps. **(6) RV64IM** —
`Rv64IM/Kernel/KernelSoundness.lean:500 executionCorrect_of_kernelSoundness (kernel :
KernelSoundnessConclusion …)`; package README: *"Lean does not yet prove that the current exported Rust
RV64IM public-proof artifact itself carries enough theorem-bearing data to construct
`ExactKernelBoundaries`."*

## 5. Concrete bound? FS? Depth? Extractor? [READ]

- **Number**: none. `grep -rnE '^\s*theorem.*(2 ?\^|ε|epsilon|negl)'` → `IsNegligible` lemmas and
  norm-parameter facts (`goldilocksTheorem8Bound_gt_five`, `goldilocksPaperBInv = 383`). λ lives in
  Rust: wiki/protocol/parameters.md *"`s_min = ceil((λ + log₂(soundness_factor)) / log₂(q))`; only `s =
  2` is supported"*, *"effective λ … floor of 96 bits and a safety margin of 2"*.
- **Fiat–Shamir**: wiki/security.md *"Random-oracle Fiat-Shamir over Poseidon2: SuperNeo's strong/weak
  interactive reductions (§6) compose, and HyperNova Appendix B's transform applies, when every
  challenge binds all preceding public data."* Applied by citation; not proved.
- **Depth / composition error**: `grep -rnE '^\s*theorem\s+\S*([Dd]epth|AccumulationScheme)'` → 0 on
  all three trees ("accumulator" = the IVC running instance). **BCS / Merkle**: `grep -rnw BCS`, `grep
  -rn Merkle` → 0/0 (Ajtai-only). **Extractor**: on main only algebraic sub-witness constructions
  (`LatticeExtractors.lean`, binding collision ⇒ short MSIS solution, Theorem 2, proved); the 09-04 tip
  has a deterministic fork-extractor (§6). Deferral sentence: README "Faithfulness Boundary" (§0) and
  wiki/security.md *"No independent audit, no formal verification of the Rust implementation."*

## 6. The commit actually pushed 09-04 (`nico/fprime-stage1-piccs-conformance` `b216df4c`)

`git fetch --depth 1 origin <branch>` + worktree; `git diff --name-only main FETCH_HEAD` → 3,350 files,
**1,726 `.lean`**. `formal/` = `ajtai-lean` (14 files, 1,506 lines, v4.30.0) + `nightstream-fprime`
(697 files, 242,919 lines, v4.30.0, Mathlib only). superneo/twist-shout/direct-ccs/nightstream-lean/
wasm-zklean **deleted** (`grep -rl 'piDECKnowledgeStatement\|FinalTheoremShape\|MSISHardnessAssumption\|
lundBoundHolds'` → 0); wiki/formal/index.md there: *"legacy reference material pending deletion … not
authoritative merely because a theorem kernel-checks there."*

Counts (same commands): nightstream-fprime theorem **9,105**, def 6,347, structure 605, sorry 0, axiom
0, `native_decide` **0**, opaque 0; ajtai-lean theorem 50, native_decide 11 (BKZ-estimator interval
arithmetic), `#print axioms` 16. **Instrument** `tests/AxiomAudit.lean` (15 lines): `#audit_axioms`
throws unless closure ⊆ `[propext, Classical.choice, Quot.sound]`; **4,253** audited names in 14
`tests/Axioms*.lean` (lakefile test roots). Green at `b216df4c`? Not checked (no build); the 08-28
external review of the parent branch: *"It does not build, its axiom gate does not finish."*

Theorem kinds: 29 `*_eq_production`, 195 `*[Rr]owCount*`, 130 `*sound*` — gadget soundness, e.g.
`Lifecycle/Stage1/NextPreimage.lean:82 theorem soundness (interface) (env) (offset) (rows : holds env
(Circuit.ops (main interface) offset)) : SpecHolds interface offset env`. The security file,
`Spec/Folding/Nifs/PaperSecurityComposition.lean:533`:
```lean
theorem accepted_implies_securityOutcome … (laws : ExtractionAlgebra …) (strongSet : StrongSetUnits …)
    (accepted : verify key running fresh proof = some result) : SecurityOutcome key running fresh proof laws strongSet
```
`SecurityOutcome` inductive: `knowledge | mixingFailure | sumcheckFailure | parentBindingFailure |
piRlcForkingFailure | piDecChildOpeningFailure`; docstring: *"This module does not own a probabilistic
forking lemma, Fiat--Shamir security, commitment binding, PiDEC child extraction, a concrete field, or
a backend."* ArkLib's bad-event shape with the probabilities left off.

**The numbers that matter to us** (`FPRIME_STAGE1_EXTERNAL_REVIEW_v2.md`, dated 2026-08-28,
"Cumulative footprint ledger"; each row is a Lean equality theorem on that branch):
| Stage-1 recursive-step endpoint (retired 26-round cut) | rows | joint domain |
|---|--:|--:|
| Pilot (in-circuit Poseidon2 digest of the 16-instance running state, ≈10.1 M values) | 13,599,570 | 13,691,432 |
| → PiCCS | 18,835,765 | 18,956,449 |
| → PiRLC | 27,191,367 | 27,310,402 |
| → PiDEC | 27,216,639 | 27,374,284 |
| → running transition (`PilotPiCCSPiRLCPiDECRunningTransition.cumulativeFootprints_eq`) | **27,537,894** | 27,649,646 |
Active 28-round cut (`decisions/fprime-stage1-domain-2p28.md`, 08-28): pilot 13,600,754 rows
(`Layout/PilotProduction.lean:503-625`), PiCCS standalone 5,281,269 (`Layout/PiCCS/v1_1/Composition.
lean:652-685`); cumulative "Open"; must fit `2^28 = 268,435,456`. Digest-only PiCCS schedule accepted
to cut 10,298,432 absorption rows to 224,368 (`OPEN_ISSUES_LEAN_REFACTOR.md` §1). Minimizer README:
*"conservative fixed-width raw wire size of 647,108,852 bytes."* Their transcription of the paper's
intro (`protocol-contract/paper-sources/01-1-introduction.md:35`): Nova *"≈ 10,000 R1CS constraints"*,
Arc *"≈ 1,600,000"*. [DERIVED] this recursive step is **≈ 2.75 × 10⁷ rows ≈ 17× Arc, ≈ 2,750× Nova**,
half of it the running-state hash. Branch artifact, unreviewed (*"No active-profile phase is
Compiler-closed, Conformance-closed, or Production-closed"*).

`claude/minimizer-campaign` (`6e656648`, 08-17): 3,049 files / **11,425,555 lines**, 10,980,101 under
`*/Generated/*` (R1CS artifacts as Lean); `native_decide` 1,321; `#print axioms` 79 + 254 fixtures.

## 7. The Rust [READ]

Main: 9 crates, 477 files, 165,275 lines. Runs: `lifecycle::prove/extend/finish_uncompressed/
verify_uncompressed(_audit)` over Π_CCS→Π_RLC→Π_DEC (Goldilocks, K=F_{q²}, Ajtai κ=18, Poseidon2);
`compress` wired but wiki/roadmap.md (06-10): *"`decider::prove` / `verify` return `Unsupported`."*
README links `docs/audits/` — **`docs/` does not exist on main**. 09-04 tip: 12 crates, 306,665 lines;
adds `nightstream-fprime` (loader for the Lean-emitted package), `wip-spartan` ("Direct sparse-R1CS
Spartan proof with WHIR"), Metal/CUDA crates. **Benchmarks committed**: none on main (`grep -rnEi
'[0-9]+ ?(ms|s)\b|constraints? [:=]?[0-9]{3,}' wiki README.md CHANGELOG.md` → 0); on fs1 only the row
counts above. The `--ignored` test (`crates/neo-fold-clean/tests/perf/fibonacci_bits.rs:594
fibonacci_decider_r1cs_shape_snapshot`): default 4 values (2 transitions, `NEO_FOLD_FIB_DECIDER_VALUES`);
prints application R1CS vars/constraints/nnz, "Full-history audit R1CS" rows/cols/witness len/recursive
F′ steps/links/self-sufficient, timings. Its comment: *"Full-history audit circuit, not the final IVC
terminal decider … should not grow linearly with the number of historical steps."* **Not run**: fresh
clone, release build of neo-fold-clean + spartan2 + plonky3 + bellpepper (329 packages in `Cargo.lock`)
on a loaded machine is not "under a minute, no heavy deps" — and §6 answers the right question.

## 8. Against Selvage, and the sentences that move

| | Nightstream main / 09-04 tip | Selvage |
|---|---|---|
| runs | Rust folding IVC, WASM/iOS demos; decider `Unsupported` | prover 3.1K lines, no accumulator |
| Lean owns | paper identities; tip: the **R1CS layout** of the recursive step, row counts as theorems | protocol soundness + compilation layer |
| sorry / axiom / native_decide | 0 / 1 (leaf) / 185 → 0 / 0 / 0 (+11) | 0 / pinned / 0 |
| axiom gate | none on main; fail-closed `#audit_axioms` ×4,253 on tip | kernel sweep + baseline |
| probabilistic soundness statement | **not formalized** (their words) | RBR, FS-of-RBR, BCS at alphabet, depth |
| composition error / concrete bound | none; λ in Rust params | two-sided `≤2^-55`, `>2^-56` |
| FS / ROM | citation to HyperNova App. B; `ParentAuthorityFS` bookkeeping | `fsKeystone`, inhabited lazy ROM |
| accumulation depth | none (IVC step assumes sound prior verifier) | `Depth.lean` + corner refutation |
| extractor | algebraic MSIS sub-witness; tip: deterministic fork-extractor, no forking lemma | erasure extractors, ZK games |

**SLVG_THOUGHT §I** *"Nobody else has both legs"* — stands (optional clause: "Nightstream's 5.6K→9.1K
sorry-free theorems are Lean-owned *layout*; its README says the probabilistic reduction 'is not
formalized'"). **§IV-b** *"a machine-checked compilation layer | nobody"* — stands. **minidregg
README:89** *"To our knowledge no other mechanized development has these"* — stands.
**formalization-frontier.md:64** *"nobody else has machine-checked recursive/accumulation soundness
end-to-end (…)"* — stands; add "Nightstream's IVC step `terminal_soundness` takes `SoundPriorVerifier`
as a hypothesis". **formal-delta §4/§7** *"axiom-bearing by its own README"* / *"axiom count (not
cloned)"* → "0 `axiom`; 185 `native_decide` incl. Goldilocks primality under `Field F`".
**neo-verdict.md addendum** *"'No published constraint count for its own recursive verifier' survives
— Nightstream has an `--ignored` test that would print the decider R1CS shape"* → **re-word**: that
test prints the full-history audit circuit; the recursive step's cost is a Lean theorem on branch
`nico/fprime-stage1-piccs-conformance`: 27,537,894 rows (26-round cut), 13.6 M of them the
running-state Poseidon2 digest — in no README or paper, so "published" is technically true and now
misleading. **lova-neo-rmfe-read.md §2** *"until someone reads whether it states soundness or only
computes identities"* → resolved: identities + witness-level implications + layout counts.

## 9. Could not verify

No `lake build` on any commit (Mathlib v4.28/v4.30 closures; their AGENTS.md caps Lean at 25 min): no
kernel confirmation of sorry-freedom, no `#print axioms` on main (none exist), no confirmation the
09-04 tip's axiom gate is green (08-28 review: did not finish). The `Field F → ZMod q → Fact (Nat.Prime
q) → native_decide` chain is by instance-resolution reading. Perf test not run. Whether the 09-04
branch merges to main. Row counts quoted from the review document and theorem *names*, not re-derived.

## 10. Absence claims: corpus + instrument

| claim | corpus | instrument | result |
|---|---|---|---|
| no `sorry` | main `4696e82`, fs1 `b216df4c`, mc1 `6e656648` | `grep -rw sorry --include='*.lean' formal` | 0 / 0 / 0 |
| no FS soundness theorem | same three | `grep -rni fiat` 18 / 174 / 503 lines, read; `grep -rni 'random oracle'` 1 / 0 / 7 | bookkeeping lemma + docstrings disclaiming FS |
| no BCS / Merkle | same three | `grep -rnw BCS`; `grep -rn Merkle` | 0 / 0 |
| no depth / accumulation-scheme theorem | same three | `grep -rnE '^\s*theorem\s+\S*([Dd]epth\|AccumulationScheme)'`; `grep -rni 'accumulation scheme'` | 0; 0 |
| no numeric soundness bound | main | `grep -rnE '^\s*theorem.*(2 ?\^\|ε\|negl)'`, read | norm-parameter facts only |
| no committed benchmark | main wiki/README/CHANGELOG | regex in §7 | 0 timing lines |
| superneo-lean not relocated | GitHub org | `gh api orgs/LFDT-Nightstream/repos` | 4 repos, no other Lean |
