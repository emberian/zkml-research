# Wave 11 Lane 1 — credible SVCS lowering and a two-round small-value prover

[EXECUTED] On 2026-11-22 the Lean 4.35.0 kernel accepted the 944-line compiler and all 11 axiom reports. Rust verified the three Lean-emitted bundles and returned the same front-end wires Lean extracted. Across five release benchmarks, the optimized and baseline provers produced identical round evaluations, terminal evaluations, and transcript digests in both repetitions. The timings below cover proof generation from an already constructed row system. [Verification script](../research/wave11_frontier_upgrades_2026_11_22/formal_svcs/build_and_verify.sh)

## What the checker certifies

- [SOURCE] An accepted certificate replays guarded transformations from the reference lowering. `credible_cert_completeness` takes a front witness to a satisfying optimized witness. `credible_cert_knowledge_soundness` takes a satisfying optimized witness back to a front witness. The maps run in opposite orders. `credible_emit_knowledge_soundness` recovers `descriptorHolds`. The additional corollary `credible_emit_accepts` applies `emit_accepts_iff` with an injective, in-range layout and the extracted variable wires pinned to the assignment. [Compiler, lines 483–526](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L483), [Emit theorem, line 378](../../minidregg/Compiler/Emit.lean#L378)
- [SOURCE] `CostModel` is a scoring function on instances. Fusion, duplicate-row removal, and dead-wire elimination each require a strictly lower score. The default charges four per wire, eight per product, one per linear-form term, two per row, three per queried wire, and one per table entry. These are search weights. Semantic validity follows from `step_sound`, `step_complete`, and checker replay. [Cost and search, lines 529–568](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L529), [Step proofs, line 317](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L317)
- [EXECUTED] `teeth_degree_inflating_fusion_rejected` isolates two multiplication rows sharing the proposed pivot. `teeth_missing_pin_rejected` removes the specific public pin. `teeth_missing_pin_would_be_unsound` gives a witness satisfying that edited instance whose readback violates the source. `teeth_unguarded_dce_rejected` tries dropping a live output wire. All four passed as kernel proofs. [Falsifiers, lines 789–809](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L789)
- [SOURCE] At the native boundary, `SvcsBundle::from_json` reads one emitted bundle and `parse_conformance` reads the whole fixture. `bundle.prove(z, mode, session)` and `bundle.verify_and_extract(z, proof, session)` bind the session and the serialized backward map in addition to the row system and witness. The verifier’s caller supplies the trusted bundle and full witness. The fixture includes Lean's readback for comparison. [Bundle API](../../minidregg/prover/src/svcs_smallval_engine.rs#L409), [Lean emitter](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L879)

## Conformance

[EXECUTED] Each row below came from the Lean fixture and the release integration test. The arithmetic example embeds an Emit gate descriptor and adds explicit input pins and byte lookups. The contraction has two consumers of the same matrix-product claim. The DFA checks packed state/byte transitions, the start state, and the accepting state. The native prover and verifier dispatch on row and lookup data for all three. [Emitted JSON](../../minidregg/prover/testdata/svcs_compiler_conformance.json), [Conformance test](../../minidregg/prover/tests/svcs_credible_compiler.rs#L14)

| Bundle | Rows before → after | Wires before → after | Default score before → after | Validated tags |
|---|---:|---:|---:|---:|
| Two-limb u8 add-with-carry | 25 → 10 | 28 → 11 | 1789 → 1661 | 6 |
| Signed i8 × i8, 4 × 4 × 4 contraction | 33 → 17 | 49 → 49 | 9864 → 9176 | 32 |
| Byte DFA with D1b LogUp | 18 → 5 | 26 → 13 | 4328 → 4224 | 12 |

## Arithmetic, lookups, and transcript

[SOURCE] I read the constructions in §§3.3, 5.1, and 6 of Dao, DeStefano, Bagad, Domb, and Thaler, *Speeding Up Sum-Check Proving (Extended Version)*, dated March 24, 2026. The sections cover delayed reduction, a small-value window, and decomposable equality factors. For lookup multiplicities I read §2.3 and the construction in §3 of Haböck. Both texts came from the local ePrint mirror via `pdftotext -layout`. The D1b projective layer layout also has a local implementation reference. [ePrint 2026/587](https://eprint.iacr.org/2026/587), [ePrint 2022/1530](https://eprint.iacr.org/2022/1530), [D1b implementation, §3](../native/qwen35audit/src/gruen_ext4.rs#L397)

[DERIVED] In round zero the optimized prover evaluates signed integer row residues and the quadratic leading coefficient, then sums them using split equality weights. In round one it samples the first coordinate at 0, 1, and 2 while the columns still live in BabyBear. Interpolating those three sums at the first challenge gives the quadratic residual needed for the second round. The prover then folds directly into extension columns. Later rounds peel the current equality factor and use the carried sum and the quadratic leading coefficient, with a direct evaluation for singular challenges. The baseline lifts all columns immediately and evaluates the cubic independently at 0, 1, 2, and 3. [Integer and split-equality kernels](../../minidregg/prover/src/svcs_smallval_engine.rs#L950), [Prover paths](../../minidregg/prover/src/svcs_smallval_engine.rs#L1271)

[DERIVED] A signed BabyBear representative has magnitude below 2³⁰. Each product of two differences has magnitude below 2⁶². Even a 64-bit row-width count keeps the unweighted sum below 2¹²⁶. For a block of k inner equality weights, the runtime checks the observed maximum row magnitude against INT_MAX divided by k(p−1) before multiplying. It selects i64, i128, or reduction to signed field representatives followed by i128. The check uses evaluated columns, so a mislabeled hint cannot select an unsafe width. [Accumulator limits](../../minidregg/prover/src/svcs_smallval_engine.rs#L941)

[SOURCE] D1b combines projective fractions by (a,b),(c,d) ↦ (ad+bc,bd). It binds the multiplicities before sampling a pole outside BabyBear, checks a zero root numerator and nonzero denominator, and reduces each layer through a cubic sumcheck. The final leaf evaluation reads the oracle. Integer query counts below p, exact mass, and a canonical histogram over that same oracle discharge the membership premise used by Lean. Instance and witness digests use SHA3-256. The transcript uses framed, stage-specific labels, cSHAKE256, and rejection sampling of all four challenge limbs. [D1b prover and verifier](../../minidregg/prover/src/svcs_smallval_engine.rs#L1156), [Oracle verifier](../../minidregg/prover/src/svcs_smallval_engine.rs#L1462)

[EXECUTED] Tests rejected a changed gate coefficient with both a replayed proof and freshly generated proofs, a broken round sum, and swapped terminal factors whose product still matched. They also rejected changed lookup mass, redistribution at fixed mass, a forged projective root and internal GKR round, a changed oracle, a cross-session replay, reuse of the first pass as the second, a noncanonical limb, and an altered readback over identical optimized rows. A 47-row case exercised zero padding, wide signed arithmetic, and an invalid lane hint. [Integration falsifiers](../../minidregg/prover/tests/svcs_credible_compiler.rs#L56)

## Soundness accounting

[SOURCE] `svcs_rbr_soundness_composed` gives a one-pass interactive bound of 4m/q for a fixed normalized witness satisfying all lookups, an accepted certificate, truthful terminal evaluation, and prefix-measurable messages of degree at most three. Here m is the number of row variables and q is the challenge-field order. `sopHonest_final` identifies the terminal value with the row polynomial evaluated at the challenge point. [Compiler theorem, line 734](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L734), [Terminal lemma, line 661](../../minidregg/Compiler/SvcsCredibleCompiler.lean#L661), [Zero-test](../../minidregg/Selvage/MultilinearZeroTest.lean#L212), [Adaptive sumcheck](../../minidregg/Selvage/SumcheckReduction.lean#L297)

[DERIVED] For BabyBearExt4, q = 2013265921⁴ and log₂(q) = 123.628. At m = 18, a single 4m/q row test gives 117.458 bits. Batching 2T+1 terminal values at a fresh scalar after they are fixed contributes at most 2T/q for a row width of T products. Exact lookup membership leaves a false front witness with a row violation. Two sequential repetitions with fresh independent interactive challenges therefore have conditional error at most ((4m+2T)/q)². At 2¹⁸ rows and benchmark width T = 1, this gives 234.836 bits in the ideal interactive model. The repetition and batching calculation is a derivation outside the single-pass Lean theorem.

[OPEN] The Rust Fiat–Shamir transcript, the lifting of the emitted BabyBear data to this concrete quartic implementation, and the native verifier have no machine-checked end-to-end cryptographic reduction in this lane. An unconditional >120-bit claim for the noninteractive implementation would require a separate analysis including oracle queries. The present verifier reads the witness directly. A hiding commitment, succinct openings, and a zero-knowledge argument remain outside the measured system.

## Release benchmark

[EXECUTED] The table gives median wall time in milliseconds over three runs per mode on an Apple M2 Max with `rustc 1.98.0-nightly (91fe22da8 2026-06-21)`. Each row system has one product per row, deterministic u8 and signed i16 columns, their field product as an output wire, and no lookup traffic. Timing includes instance and witness hashing, both repetitions, and proof construction. Instance construction, proof comparison, and verification run outside the timer. The test alternates prover order and compares the complete proofs on every trial. Machine load can affect these local ratios. [Benchmark source](../../minidregg/prover/tests/svcs_credible_compiler.rs#L206)

| Rows | Naive Ext4 (ms) | Small-value + split-eq (ms) | Speedup |
|---:|---:|---:|---:|
| 2^14 | 21.860 | 6.578 | 3.323× |
| 2^15 | 43.501 | 13.474 | 3.228× |
| 2^16 | 94.450 | 26.391 | 3.579× |
| 2^17 | 168.227 | 50.924 | 3.304× |
| 2^18 | 365.440 | 109.817 | 3.328× |

[EXECUTED] The end-to-end command ran from the research repository. It used a private Lean overlay, the project import-boundary checker, and `CARGO_TARGET_DIR=/tmp/target-w11-svcs` with release compilation and warnings treated as errors. Selected output from the same run follows.

```sh
bash research/wave11_frontier_upgrades_2026_11_22/formal_svcs/build_and_verify.sh
```

```text
944 lines, 11 pinned axiom reports, target tier check passed
OK: import-boundary: every import of Theory Selvage Effects Pred Kernel Compiler Assurance Host is inside its row; no library cycle outside {Kernel, Compiler, Assurance}
Kernel verified Compiler.SvcsCredibleCompiler; emitted 90229 bytes and 6 passing checks.
test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 78 filtered out; finished in 0.00s
test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 3.32s
```

[EXECUTED] Search accounting for this run was `Kagi: 0`, `Scry: 0`, `eprint downloads: 0`.
