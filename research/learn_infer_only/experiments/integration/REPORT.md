# Finished-proposal integration, 2026-09-06

[EXECUTED] Both integration runs passed. The extended run compiles **16 proposed
modules, 265 guarded theorem pins, and all four Theory/Compiler/Selvage/Assurance
umbrellas together in one fresh overlay**. This is integration against existing
read-only dependency oleans, not a clean full companion build.

| Run | Selection | Pins | Elapsed seconds | Result |
|---|---|---:|---:|---|
| `results/run_001/report.json` | 12 baseline modules; four umbrellas; two integer executable checks | 217 | 149.300976 | Passed |
| `results/run_002/report.json` | Baseline plus four stable EMA modules; four umbrellas | 265 | 122.319557 | Passed |

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

[EXECUTED] All 265 pins use only the recorded standard kernel axiom vocabulary:
28 use no axioms; 10 use only `propext`; 7 use `propext, Quot.sound`; 220 use
`propext, Classical.choice, Quot.sound`. No forbidden construct was found in the
selected proof sources by the comment/string-masking lexical instrument. Both
runs' Lean compilation logs contain no warning or stderr output. Exact per-name
lists and source lines are in each run's `axiom_census.json`.

[EXECUTED] The combined patch passed `git apply --check`, actual `git apply`, and
an exact patched-file content comparison in a separately initialized Git source
copy. That copy included all 524 current companion Lean files plus the unchanged
import-boundary script. The boundary script passed both in the applied source
copy and in the original companion. The existing dirty `Compiler.lean` bytes were
the baseline; no claim is made that this patch targets a clean HEAD checkout.

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
- `../../formal/integration/minidregg-combined-resident.patch` is the current
  extended proposal; each numbered run also retains its own exact patch copy.

[OPEN] New Garner-certificate modules, optimizer modules, and independent review
witness files remain outside this integration. Maintainer application, a clean
dependency rebuild, and runtime integration remain separate work. A green
combined build does not strengthen the source theorems' assumptions: receipt
binding does not become hiding; algebraic engine models do not become runtime
refinement; the EMA privacy/collision residuals retain their named scope.

[EXECUTED] Metered Scry/Kagi queries: zero. No commits or shared-ledger edits were
made by this integration lane.
