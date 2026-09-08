# Smaller rescale layout reduces real proof cost

[EXECUTED] The new Lean-generated9-to4 RNS rescale relation produced a valid
proof on the first attempt. A fresh process accepted it, and the same proof
was rejected after changing the first public output digit. The proof covers
the same32 actual positions and128 output residues as the frozen baseline.

[EXECUTED] This run used the **exact same native binary**, portable proof
backend, public ciphertext/capture inputs, selected positions, and four Rayon
threads. The existing generic interpreter accepts the new trace width directly;
no Rust build, backend change, handwritten AIR or baseline reproof was needed.
`INPUTS.json` records the selected immutable inputs; `RESULT.json` checks the
saved old/new command paths, backend identity and operation dimensions.

| Metric | Frozen baseline | Smaller layout | Reduction |
|---|---:|---:|---:|
| Trace columns | 63,845 | 24,575 | 61.5% |
| Arithmetic constraints | 76,269 | 32,043 | 58.0% |
| Witness bytes | 8,172,160 | 3,145,600 | 61.5% |
| Proof bytes | 14,454,987 | 5,664,793 | 60.8% |
| Peak proving child RSS, bytes | 412,254,208 | 175,882,240 | 57.3% |
| Proving call | 2.590259s | 0.381009s | 85.3% |
| Fresh verification call | 0.506974s | 0.196285s | 61.3% |
| Whole proving command | 3.868960s | 0.763380s | 80.3% |

[EXECUTED / DERIVED] Byte and column reductions are calculated from the retained
artifacts. Times/RSS are one saved baseline observation and one new observation
on a shared host, at different times with fresh proof randomness. They establish
this observed cost reduction; they do not establish a performance distribution
or guaranteed speedup. Full process measurements are retained under `results/`.

[SOURCE / REPORTED] `../rescale_compiler_successor/` changes allocation to use
proved per-value/per-carry widths while retaining the original value/carry
arithmetic and exact native9-to4 output equation. Its `ProfiledMatrix.sourceSound`,
`NonlinearRnsProfiled.rowSound`, `simplifiedSource_sound` and cross-layout output
agreement are checked. Its emitter checked all32 actual source rows and retained
changed-output/radix512 refusal controls. The88 public columns and exact-public
table11 remain the same. The source theorem package supplies the general proof;
this runtime package supplies the actual cryptographic proof and cost result.

[EXECUTED] Successor proof SHA256:
`2c4806c9526b7aa2a975cfa8bdf2e722d2ca35b9a3aff02d2181970d4d407045`.
Template SHA256:
`37a02768080e1ca8284fab4bc186b2e5981ad0b97a4af7965472953cdfe4df5a`.
The witness is3,145,600 bytes, SHA256
`92ceb5ab11ffa4ff2b3032d1658ad0f13a4e70c28bc6d409bedbbcff86c9e591`.

[OPEN scope] This remains32 of24,576 actual component/coefficient positions.
There is no full ciphertext, convolution or whole-learner proof. Captured-input
provenance, public parsing/NTT/serialization, BFV validity and protocol remain
implementation assumptions. No private key was read and no decryption occurred.
Frozen baseline, query packages and companion trees were not modified.
