# Complete captured nonlinear rescale proved

[EXECUTED] All **24,576 component/coefficient positions** of the actual nonlinear
9-to-4 RNS rescale capture are covered by six accepted proofs, each also accepted
in a fresh native verifier process. This checks all **98,304 output residue
equations**, with no sampling, omitted positions or padding. The single sequence
completed in **146.806 seconds**, from 2026-09-08 22:15:40.544 UTC to
22:18:07.352 UTC. There were no failed steps or retries.

| Chunk | Component | Coefficients | Proof bytes | Prove seconds | Fresh verify seconds |
|---|---:|---|---:|---:|---:|
| 0 | 0 | 0–4095 | 5,771,165 | 17.482 | 0.251 |
| 1 | 0 | 4096–8191 | 5,772,760 | 15.150 | 0.247 |
| 2 | 1 | 0–4095 | 5,772,393 | 15.322 | 0.256 |
| 3 | 1 | 4096–8191 | 5,772,361 | 16.038 | 0.255 |
| 4 | 2 | 0–4095 | 5,771,749 | 16.402 | 0.248 |
| 5 | 2 | 4096–8191 | 5,772,109 | 17.334 | 0.249 |

[EXECUTED] Combined proof size is **34,632,537 bytes**. Summed native witness
emission elapsed time is **38.346 seconds**, proving is **97.729 seconds**, and
fresh verification is **1.507 seconds**. Peak proof-process RSS is
**9,497,837,568 bytes**. These are one sequential execution on the shared
96-GiB arm64 macOS host with four Rayon threads, not repeated timing statistics.
The outer process includes source checks, trace hashing, serialization,
self-verification, fresh verification and compression. `COSTS.csv` retains each
stage's process measurements; `results/whole001.command.json` is the outer cost.

[EXECUTED] The public import reconstructs the complete tensor from the unchanged
real nonlinear operator capture, with global row ID `component*8192+coefficient`.
It checks all 98,304 captured output residues against the canonical raw output
ciphertext through public decoding and inverse NTT. Each native prove/verify
call reconstructs its public tuple from that same capture. The orchestration
requires exactly six consecutive intervals, matching source/output/public-row
hashes, and a successful fresh verification for each. It checks frozen source
and case pins again before declaring completion. No private file or decryption
was needed, and no BFV operation or earlier proof was rerun.

[DERIVED] The unchanged approved smaller relation has 24,575 witness columns,
32,043 arithmetic constraints and an 88-column ExactPublic table. The formal
`NonlinearRnsProfiled.rowSound` / `simplifiedSource_sound` chain forces every
accepted row's four outputs to equal the captured native directed scaler
projection on its nine canonical input residues, including the established
shift-125 word bounds and directed correction. See
`../rescale_compiler_successor/README.md` and the underlying
`../arithmetic_rescale_generic/` native/public alias proofs.

[EXECUTED] The new native witness executor consumes the Lean-generated plan,
copies the approved template unchanged, and emits untrusted witnesses. The
formal lane's original 32-row comparison matched all 3,145,600 predecessor trace
bytes exactly; no baseline reproof was performed. All six larger witnesses
were accepted by the actual generated relation and backend. Native plan/executor
soundness or witness completeness is not inferred from that finite comparison.
`../rescale_native_emitter/README.md` owns its construction and compatibility
record; `PIPELINE.json` pins the exact callable plan, executable and template.

[EXECUTED] The frozen portable public-preprocessing backend is unchanged. Only
public preprocessing uses its pinned portable random stream; witness commitment
randomness and the existing FRI/soundness settings remain as in prior accepted
runs. This package introduces a public reader, exact chunk orchestration and
reusable proof/verify entrypoints, with no Rust-authored arithmetic relation.

[EXECUTED] Public proofs and command records are retained in `results/run001/`.
The six raw witnesses total **2,415,820,800 bytes**. After verification they were
compressed to **105,841,148 bytes** under ignored `work/run001/`, with raw and
compressed hashes retained in each chunk result. The original raw files were
removed only after successful compression. These witnesses are optional local
transport, not required for verification and not added to Git. The full public
case remains in `results/case001/`.

The reusable `run.py CASE NEW_RUN` performs the complete sequence; the available
`verify_all.py CASE PROOF_RUN NEW_VERIFICATION_DIR` verifies the six fixed
intervals without witnesses. This run executed the six native fresh-verifier
calls directly through `run.py`; no redundant aggregate-verifier campaign was
performed.

[OPEN scope] This is the **complete captured rescale**, not the whole ciphertext
multiplication. Captured extended-product provenance, basis extension,
convolution, Rust parsing/serialization, NTT conversion, exact native-language
refinement, BFV security/noise and protocol authorization remain outside this
arithmetic proof. The inherited exact-gamma family is unchanged. No whole
ct×ct or end-to-end model/query proof follows merely from this rescale result.

[EXECUTED] Primary machine-readable result: `RESULT.json`; complete per-chunk
bindings and costs: `results/run001/result.json`; source/build pins:
`PIPELINE.json` and `BUILD.json`; execution rules: `CONTRACT.md`. Reporting here
uses the completed public records only.
