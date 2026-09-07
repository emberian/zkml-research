# Finished-proposal integration

[EXECUTED current check, 2026-09-07] **Run014 passes 53 modules / 708 exact theorem
pins and all four umbrellas**, using existing read-only dependency oleans. It
adds the source-noise/window successor (34 pins) and the two mixed-journal
window-frame modules (23 pins) to the prior 651-pin
collection. Patch application, exact content comparison, both import-boundary
checks and all recorded source/companion hashes pass. Elapsed472.952 seconds on
the shared machine. This is not a clean whole-tree build or Rust/runtime refinement.

[EXECUTED] The explicit manifest is `modules_with_source_window.json`; the frozen
proposal is `formal/integration/minidregg-combined-resident-708.patch`, SHA256
`a290120197d9679d9d59060121b7a7b7dc17dc3ccbbef263ac8eac057d77f2c2`.
The current unnumbered proposal has those same bytes. Apply one compatible
combined patch; the historical snapshots below remain separate alternatives.

[EXECUTED] The exact axiom census is 561 standard triples, 48 axiom-free,
41 `propext`, 54 `propext, Quot.sound`, and four `Quot.sound`. Run014's
[summary](results/run_014/SUMMARY.md) and report retain the actual commands,
manifest, harness and source hashes. The completed674 proposal and manifest
remain unchanged. The new source-window theorem derives a Q83/W32/r577 decoding
bound from supported source coefficients; Rust sampler/RNS/NTT/scaler refinement
and admission provenance remain assumptions outside that theorem.

[EXECUTED instrument correction] Run012 stopped before Lean on a lexical false
positive: a witness uses the lawful **imported** admission predicate `admit`,
without declaring a local binder. The census now records such identifiers and
leaves name resolution to Lean, while rejecting obvious placeholder tactics and
requiring every exact kernel axiom guard. `check_census.py` accepts that real
14-pin witness and rejects five missing-guard/placeholder controls. Run013 then
elaborated every guard. The failed run and its checker snapshot remain preserved.

[DERIVED scope] MixedHistory supports real non-window journal entries only with
an explicit check that they preserve the selected window and genesis bytes.
Its admission count is derived from the actual journal projection. The witness
has five commits and three learning admissions, including expiry and retry.
This removes the previous exclusive-window-history restriction at the model
level; the new executable E2E journal still needs its own correspondence checks.

## Historical 528-pin checkpoint

[EXECUTED] The earlier batched integration passed. It compiles **41 proposed
modules, 528 guarded theorem pins, and all four Theory/Compiler/Selvage/Assurance
umbrellas together in one fresh overlay**. This is integration against existing
read-only dependency oleans, not a clean full companion build.

| Run | Selection | Pins | Elapsed seconds | Result |
|---|---|---:|---:|---|
| `results/run_001/report.json` | 12 baseline modules; four umbrellas; two integer executable checks | 217 | 149.300976 | Passed |
| `results/run_002/report.json` | Baseline plus four stable EMA modules; four umbrellas | 265 | 122.319557 | Passed |
| `results/run_003/report.json` | Previous set plus generic contextual gate and actual EMA adaptive adapter; four umbrellas | 307 | 89.049419 | Passed |
| `results/run_010/report.json` | Previous set plus actual mixed Stage0/EMA oracle phases; four umbrellas | 528 | 179.520435 | Passed |
| `results/run_009/report.json` | Previous set plus ciphertext window, integer noise bridge, and BFV target projection; four umbrellas | 499 | 174.616221 | Passed |
| `results/run_006/report.json` | Previous set plus distribution budget, two simplifier modules, and six BFV source-certificate modules; four umbrellas | 371 | 142.107070 | Passed |

[EXECUTED: failures retained] `run_004` and `run_005` stopped during the lexical
census, before compiling Lean: the old scanner truncated the valid identifier
`constant?_eval`, then treated equal short theorem names in `Small` and `Large`
namespaces as ambiguous. The final instrument recognizes Lean `?`/`!` names and
matches fully qualified theorem names using namespace/section scopes. Both
failed reports and their exact harness snapshots are retained. No new proof
failure was hidden by these tooling corrections.

[EXECUTED: failures retained] `run_007` and `run_008` stopped before Lean because the lexical scanner treated the valid admission predicate identifier `admit` as a tactic. The corrected instrument records those identifier occurrences, requires a typed binder or definition, rejects tactic-shaped uses and compilation proof-placeholder diagnostics, and still elaborates every exact axiom guard. The two failed harness snapshots are retained.

[EXECUTED] The module census was obtained by parsing the selected finished patches,
matching their new-file contents to the source files, counting theorem/lemma
declarations, matching every declaration to a guarded exact axiom print, then
elaborating all those actual guards. The extended census is:

| Lane | Modules | Pins |
|---|---:|---:|
| Resident release/restore | 2 | 31 |
| Policy evolution | 1 | 15 |
| Durable integration/collision | 2 | 45 |
| Randomness/adaptive context/multiple receipts | 3 | 46 |
| BFV lift and engine decomposition | 2 | 60 |
| Small and large integer QR emission | 2 | 20 |
| EMA certificate/cell/release/witness | 4 | 48 |
| Generic contextual gate and actual EMA adaptive adapter | 2 | 42 |
| Distributional one-read budget | 1 | 14 |
| Air simplifier and integer specialization | 2 | 27 |
| BFV exact source certificate library | 6 | 23 |
| Ciphertext window core/cell/witness | 3 | 44 |
| Integer window noise and actual BFV bridge | 4 | 62 |
| BFV target projection library | 5 | 22 |
| Mixed oracle phases and actual Stage0/EMA adapter | 2 | 29 |

[EXECUTED] All 528 pins use only the recorded standard kernel axiom vocabulary:
45 use no axioms; 28 use only `propext`; 43 use `propext, Quot.sound`; 4 use only
`Quot.sound`; 408 use
`propext, Classical.choice, Quot.sound`. No forbidden construct was found in the
selected proof sources by the comment/string-masking lexical instrument. The
final run's Lean compilation logs contain no warning or stderr output. Exact per-name
lists and source lines are in each run's `axiom_census.json`.

[EXECUTED] The combined patch passed `git apply --check`, actual `git apply`, and
an exact patched-file content comparison in a separately initialized Git source
copy. That copy included all 524 current companion Lean files plus the unchanged
import-boundary script. The boundary script passed both in the applied source
copy and in the original companion. The existing dirty `Compiler.lean` bytes were
the baseline; no claim is made that this patch targets a clean HEAD checkout.
The final tool preserves each patch's actual umbrella import lines, including
comments, and verifies that every selected module is rooted directly or
transitively. In particular the BFV library roots its verifier/witness modules;
its separate IO runners are not imported into an umbrella.

[EXECUTED] Companion HEAD stayed
`6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`. Before/after `git status --short`
matched. Before/after hashes of all 525 copied companion files matched, as did
the selected proposal sources, lane patches, checker, manifest, and environment
record. No companion files or individual lane patches were edited. The report
records every command and its working directory; cached dependency artifact
paths, sizes, and mtimes are retained separately.

[EXECUTED] The baseline also reran the two integer executable check modules in an
owned scratch hierarchy. The small check accepted all 64 honest signed
coefficients and refused all 685 single-wire mutations. The large check reran
its seven boundary cases and quotient/remainder refusal controls, including the
existing CSE descriptor. Its retained cost output is 52,378 raw gates and 21,279
shared gates. Full generated output and source hashes are kept in
`results/run_001/integer_check_outputs/`. Those unchanged executable checks were
not rerun in the EMA pass.

[EXECUTED] Preserved combined proposed patches:

- Baseline: `../../formal/integration/minidregg-combined-resident-217.patch`, SHA-256
  `cba1e801dcc5fcd8578a934f131de2866b0a9a5c755f2ea3eeaf35d01b65ab6e`.
- Baseline plus EMA: `../../formal/integration/minidregg-combined-resident-265.patch`, SHA-256
  `5da935fd45db2a8c196fd2333df8b0ae757001dd33fdd831d7b50787060113ff`.
- Generic contextual EMA extension: `../../formal/integration/minidregg-combined-resident-307.patch`, SHA-256
  `2823799487d75e844c2501b430022b9b22d0053aa2ee34f44a95a5e249b1efb6`.
- Final finished batch: `../../formal/integration/minidregg-combined-resident-371.patch`, SHA-256
  `81d13254448b17203cc4990c2cdae82ddfd6a8b168e37d44ce15623c392bb80d`.
- `../../formal/integration/minidregg-combined-resident.patch` is the current
  extended proposal; each numbered run also retains its own exact patch copy.

[OPEN] The next target-limb-array extension, separate BFV IO runners, and
independent review witness files remain outside this integration. The 23-pin
source-certificate package and 27-pin simplifier are included. Maintainer application, a clean
dependency rebuild, and runtime integration remain separate work. A green
combined build does not strengthen the source theorems' assumptions: receipt
binding does not become hiding; algebraic engine models do not become runtime
refinement; the EMA privacy/collision residuals retain their named scope.

[EXECUTED] Metered Scry/Kagi queries: zero. No commits or shared-ledger edits were
made by this integration lane.

[EXECUTED] Frozen 499-pin combined patch: `formal/integration/minidregg-combined-resident-499.patch`, SHA256 `8f825765a1dd9dbdbf63e3f0013c8a3428f4a94ab93fd310b20efb83ec5efbcc`. The 217/265/307/371 snapshots remain unchanged. The corresponding explicit manifest is `modules_window_batch.json`; the baseline default remains `modules.json`.

[EXECUTED] Frozen 528-pin combined patch: `formal/integration/minidregg-combined-resident-528.patch`, SHA256 `b6a5d16768fe3b82b4a2cd0a8f30780e650a921061ddda8da1c46bddea5a5153`. Manifest `modules_with_mixed_phases.json` extends the preserved 499 selection by exactly the two frozen mixed-phase modules. Run 010 compiled all 41 modules and all four umbrellas with no warning/stderr, applied and checked the combined patch, and preserved every selected/companion input hash and companion HEAD/status. The separately announced BFV modular-lowering 38-pin patch is not in this selection.

## Final collection check

[EXECUTED final collection, 2026-09-06] Run011 passed: **49 modules /651 exact theorem pins**, all four umbrellas, actual patch application/content comparison and both import-boundary instruments. Elapsed213.909 seconds. No selected input or companion source changed; companion HEAD/status were unchanged. Existing dependency oleans were reused; no clean whole-tree build is claimed. The final snapshot is formal/integration/minidregg-combined-resident-651.patch, SHA256 9398b530f3640d5f279c4f3958ccf57abcbb113f43ca608825ca41d935ed8e42.

[DERIVED scope] This adds saved modular-word38, guarded horizon arithmetic 40 and source-phase 45 to the morning 528-pin pass. It excludes unfinished mixed-journal and source-noise successors. Apply one compatible combined proposal; earlier snapshots are retained as historical evidence.
