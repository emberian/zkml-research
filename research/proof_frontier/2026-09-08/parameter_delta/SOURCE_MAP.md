# Exact source map and audit boundary

[SOURCE] Minidregg baseline `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`; files read directly under `/Users/ember/dev/minidregg`. `source-pins.json` contains hashes of the bytes inspected. Definitions/theorem statements and relevant proof consumers were read; this parameter lane did not rebuild those existing modules.

| declaration / source | exact absolute location | what was seen and used |
|---|---|---|
| `SoundnessParams`, `errStarUD` | `/Users/ember/dev/minidregg/Assurance/ErrorBudget.lean:76`, `:105` | Delta is a premise knob; the error is `n/fieldCard`. |
| `grindingTerm`, `sumcheckTerm`, `crTerm`, `soundnessError` | same file `:114`, `:120`, `:125`, `:140` | Exact four-addend algebraic expression; `queries` is adversarial FS work, not sample count. |
| `soundnessError_bound` | same file `:292` | Product-coin-space theorem, separate `hδB` at `:315` and `hδC` at `:316`; uses old MCA at `:367`, `:409`. |
| `deployedBudget`, its two-sided bound, dominance and admissibility | same file `:433`, `:450`, `:457`, `:468`, `:480` | Inherited rate-half BabyBear4 arithmetic point, named 55-bit certificate. Scope remains distinct from VERDICTS' IR-v2 query column. |
| `grindingTermPoW`, `soundnessErrorPoW`, `secureBudget120` | `/Users/ember/dev/minidregg/Assurance/ErrorBudget120.lean:57`, `:62`, `:132` | Only FS grinding discounted by `2^20`; Ext6 target is a resource-budget arithmetic model. Header explicitly retains BUDGET-PoW-compose. |
| `mixedFieldSoundness` and three profiles | `/Users/ember/dev/minidregg/Assurance/MixedFieldBudget.lean:73`, `:104`, `:113`, `:121` | Separate field cards for RBR, gate batch, sumcheck, proximity; base-gate profile is explicitly prospective succinct replacement. |
| `survivalSq`, `queryErr` | `/Users/ember/dev/minidregg/Assurance/TwoRegimeQueryBudget.lean:172`, `:192` | Existing UDR branch already uses `((1+rho)/2)^2`; no new numerical change follows from porting it. |
| `ir2`, `recursionCfg`, `prodV1`, `zkdtvmCore`, `lb2Drop` | same file `:320`, `:325`, `:332`, `:338`, `:828` | Source parameter points; zkdtvm is external calibration, lb2Drop a proposed configuration. |
| `foldDistancePreserving_UD` | `/Users/ember/dev/minidregg/Selvage/ProximityGapUD.lean:534` | Tail radius below `(1-rho)/3`, exception count equal to folded-domain cardinality. |
| `proximity_sound_halfThen_UD` | `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriTower.lean:231` | One half-threshold first fold, radius-preserving tail; whole-word count `m*n0*fieldCard^(m-1)`. |
| `proximity_sound_rateHalf_postJohnson` | same file `:266` | Existing example initial radius `3/10`, tail `3/20`. |
| `committedFri_sound_halfThen_UD` | `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriTranscript.lean:466` | Same count after binding at every opened position; no query count in this theorem. |
| `friEvent_fsOracle_iff` | same file `:502` | Exact challenge-vector syntax transport, explicitly not a new FRI ROM soundness theorem. |
| `friAdaptive_earliestDeviation_cover` | `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriQuery.lean:206` | Every round needs `radius(j+1)+tau <= foldRadius(j)`, final radius nonnegative, and actual fold transitions. |
| `friAdaptive_sampled_sound` | same file `:417` | Independent-per-round ideal-binding theorem: `m*b/fieldCard + (1-tau)^qCount`. |
| `friAdaptive_coherent_sampled_sound` | `/Users/ember/dev/minidregg/Selvage/HalfThresholdFriCoherent.lean:217` | Same bound for uniform initial pair indices with replacement and modulo projections on `PowerTwoFriLevels`; no extra round factor on query term. |
| `reedSolomonCode_minDist` | `/Users/ember/dev/minidregg/Selvage/ReedSolomon.lean:149` | Exact codeword distance `1-(d-1)/n`; ErrorBudget's separate `δ<dC/2` remains required. |

[EXECUTED] Current companion source constants were rechecked at breadstuffs `3e51def6a5a95424e54fbe7432539b06088de5c3`: `/Users/ember/dev/breadstuffs/circuit/src/descriptor_ir2.rs:7269,7272,7273` gives `(6,19,16)`; `circuit/src/plonky3_prover.rs:108,111,112` gives `(3,38,16)`; `recursion-verify/src/config.rs:51,53,58` gives `(3,38,14)`. This is a source-configuration observation, not a fresh deployed-binary audit.

[SOURCE] `docs/VERDICTS.md` remains authoritative and unedited. `notes/proximity-delta-2026-09-04.md:39` identifies the separate query/commit columns; `notes/blowup-drop.md:16` onward identifies the proposed `(2,57,16)` point and its cost scope. Historical notes with broader novelty or deployment claims were not adopted as findings here.

[REPORTED] proof_frontier communicated the in-progress positive-degree full-UD statement: `1<=d`, `2e+d<=n`, more than `n` good scalars imply joint agreement on `n-e` positions; its hPG radius is `(0,(1-d/n)/2)` with error `n/fieldCard`. This audit's arithmetic is conditional on that theorem and its consuming module checks, not on its name or an assumed carrier. The polynomial gluing sublemma is separately checked in `../formal/polynomial_gluing/universe_successor/`.

[EXECUTED] Audit instruments: read-only `rg`/source reads, direct source hashes, and `python3 derive.py`. Web searches: 0. Scry calls: 0. Eprint downloads: 0. Runtime prover benchmarks: 0. `execution.json` retains the calculation command, status and stdout. Rational inequalities and minimum-query tests are exact; printed log2 values are descriptive floating-point conversions.
