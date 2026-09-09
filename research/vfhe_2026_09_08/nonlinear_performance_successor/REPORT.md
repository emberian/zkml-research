[EXECUTED] **The complete 116-proof saved class kernel accepted.** Four new extension and six new rescale proofs replace the predecessor's corresponding stages; its 88 corrected MAC and 18 tensor proofs are reused. The fresh consumer verified every proof against the same caller-approved model, query, evaluation-key and kernel ciphertext digests. All arithmetic assertions apply to every row. No keys, encoder, encryption or private reader ran.

[EXECUTED] Authoritative result: `runtime/run001/RESULT.json`, SHA256 `01fb98f7415acac0e222d65dac804659b7335b664899ea07d9affd9363fe797c`. The full verification record is `runtime/run001/verification/RESULT.json`, SHA256 `938a001b9b8679a25dd1128f23b154062f6888dd075ffc9ba386109598191e5a`. The single attempt finished at 2026-09-09T02:45:23.632440+00:00, exit0: ten new proofs, ten self-checks, 116 fresh consumer checks, no proof retries or baseline reproof.

| Complete class cost | Corrected predecessor | This mixed bundle |
|---|---:|---:|
| Proof bytes | 133,690,186 | 117,812,579 |
| Recorded/composed proving seconds | 376.534 | 407.962 |
| Maximum recorded stage prover RSS bytes | 9,500,557,312 | 6,604,324,864 |
| Fresh complete consumer seconds | 35.749 | 39.477 |

[DERIVED from retained measurements] Proof data fell **11.88%** and maximum stage prover memory fell **30.48%**. Recorded/composed proving time rose **8.35%**. This is a bandwidth and memory improvement, not a latency improvement. The composed total retains the unchanged MAC/tensor costs and substitutes newly measured extension/rescale costs; it is not a fresh whole-class production timing. The actual ten-stage production plus complete consumption took 349.160 seconds, of which new native proving took 217.038 seconds. These are single observations, not timing distributions.

[EXECUTED] The four extension proofs total 15,485,630 bytes, 87.580 seconds proving, and 6,087,983,104 bytes peak RSS. The six rescale proofs total 24,929,599 bytes, 129.459 seconds proving, and 6,604,324,864 bytes peak RSS. Coverage remains all 16,384 extension positions and all 24,576 rescale positions in deterministic 4096-row chunks.

[DERIVED] The shared profiled signed-matrix compiler now keeps scalar/result/carry values and reconstructs omitted Boolean witnesses from canonical range bounds. The unchanged arithmetic constructors and public aliases force the original exact extension and directed rescale native-output formulas. Nine Compiler modules have 28 exact axiom guards, nonzero source/compact witnesses and range/capacity falsifiers. `ProfiledRowCoverage`, `ProfiledPublicBridge` and `RangeProfiledTransport` keep concrete matrix evaluation out of elaborator normalization; the last reassociates pulled-back assignments before specialization. Final concrete public-output checks passed without changing the emitted artifacts.

| Profile shape | Extension | Rescale |
|---|---:|---:|
| Old declared columns | 22,977 | 24,575 |
| Compact declared columns | 2,239 | 2,599 |
| Actual native main columns | 12,059 | 13,061 |
| Actual Ext4 permutation columns | 922 | 986 |
| Main plus permutation, base-field equivalents | 15,747 | 17,005 |

[EXECUTED] `shape/` records the actual unchanged four-bit range backend and fixed-four lookup grouping. Both changed stages now have degree six and eight ZK quotient chunks. The same native binaries, FRI blowup3, queries38, query PoW16, Ext4, salts/random-codewords4 and witness hiding are pinned. A small declared source is not the committed native width; the table includes decomposition and permutation overhead.

[OPEN / boundary] These source theorems and executed checks do not supply a new numerical PCS/FRI/Fiat–Shamir bound. Native parsing, range/LogUp extraction, NTT transforms, ciphertext decoding and the join controller remain explicit boundaries. Separate native-range work is under `../nonlinear_performance/range_native_bridge/`. This saved-class result does not re-prove historical teaching, produce a new multiclass decision, or remove the full-reader capability.

[EXECUTED / integration] `runtime/caller.py` is a caller-selected subprocess worker over the same exercised producer/verifier engine. Its four operations are `produce-update`, `verify-update`, `produce-infer`, and `verify-infer`; each writes the new output directory's `result.json`. `runtime/caller/PIPELINE.json` has 42 operational pins and no saved-case proofs, requests, baselines or private keys. Its CLI/config were checked without launching another proof. The continuing-system owner will exercise it with the complete fresh workload. No further saved-class cost successor is queued.
