# Complete retained nonlinear Infer

[EXECUTED] One callable consumer accepted the complete saved
`Infer(committed_model, query) → kernel ciphertext`: all 116 fresh proof checks
passed on 2026-09-08. The 88 new proofs cover the packed query multiplication
and all ten rotation/reduction stages; the other 28 are the previously completed
whole-square proofs. The accepted output is the exact saved three-component
degree-8192 ciphertext, SHA256
`1dfa0a85aba49bd4cb5b67610b89eb3211e50bc575ba18449bedf4c34cabf11c`.
There were no runtime failures, retries, square reproofs, or private reads.

The completed record is [RESULT.json](RESULT.json), derived from the actual
[fresh verifier result](results/run001/verification/result.json). The latter's
SHA256 is `735cc5272b650fed8d23a8e3a36aa342a9d5011a5bd7492ba2470686379b35e1`.

From this directory, the reusable proof-only consumer is:

```sh
python3 verify.py REQUEST.json results/case001 results/run001/proofs NEW_VERIFY_DIR
```

`NEW_VERIFY_DIR` must not exist. The consumer reconstructs the public statements
from ciphertext/query/key bytes and the approved Lean linear plan, verifies all
116 proofs in separate native processes, and checks complete row coverage and
every cross-phase binding. It needs no witness or private key. `PIPELINE.json`
selects the approved templates, native binaries, and existing square proofs;
`REQUEST.json` independently selects the approved model, query, and public key
digests. These local approval inputs are part of the verifier's configuration.

[EXECUTED] The actual single production command was
`python3 run.py REQUEST.json results/case001 results/run001`, wrapped by
`run_command.py infer001` for retained process costs. Its result is
`complete_infer_verified: true`. This command generated the 88 new proofs before
invoking the same proof-only consumer; it reused the 28 square proofs.

| Measured quantity | Result |
|---|---:|
| New-proof pipeline plus fresh joined verification | 405.083 s |
| Fresh joined verification, including public reconstruction | 58.093 s |
| New MAC proving, sum of backend timers | 236.780 s |
| New native witness emission, sum of process times | 57.261 s |
| Peak new prover RSS | 1,243,267,072 bytes |
| Peak fresh verifier RSS | 173,916,160 bytes |
| New 88 proofs | 76,358,499 bytes |
| All 116 proofs, including reused square proofs | 145,628,066 bytes |

[EXECUTED] Costs come from `results/infer001.command.json` and the per-process
records aggregated in `results/run001/{proofs,verification}/result.json`.
Execution was sequential across chunks, with `RAYON_NUM_THREADS=4` inside each
host process. Public case import took a separate 12.698 seconds. These are
measured costs for this run with an existing square proof bundle, not a
from-scratch full-Infer benchmark. The new 3,827,957,760 witness bytes were
compressed to 452,065,647 bytes in ignored `work/`; raw traces were removed
after successful proof generation and compression. Each retained chunk result
records both hashes. Proofs and public case files remain available.

[SOURCE] The generated paired-MAC relation is
`out_h = (add_h + Σ_i D_i K_hi) mod q`, with canonical bounded public words.
Its four approved prime profiles come from
[full_bfv_keyswitch_arithmetic](../../full_bfv_keyswitch_arithmetic/README.md).
There are 88 chunks of 4,096 rows: 11 stages × 4 primes × 8,192 NTT positions,
with two output residues per row. Stage zero encodes actual ciphertext/plaintext
multiplication using the same generated relation. Later stages bind the four
RNS lifts, public evaluation-key products, and actual additions. The exact
Galois permutations come from the Lean-generated `linear_plan.json`, also used
by `BfvInferComposition.inferDotSound` in
[the composition source](../../full_bfv_infer_composition/Compiler/BfvInferComposition.lean).
The final dot ciphertext is bound byte-for-byte to the input of the reused
[complete square](../README.md), including its extension, tensor products,
and all 24,576 rescale positions. No handwritten AIR or native arithmetic
replay substitutes for these generated-relation proof checks.

[SOURCE] The native reader is isolated in [src/main.rs](src/main.rs). Its owned
FHE dependency copy adds only a read-only getter for public rotation-key parts;
[public-key-getter.patch](public-key-getter.patch) retains the change and
`GETTER.json` pins both variants. Main companion trees and prior component
runtimes remain unchanged. The existing portable public-preprocessing backend
is reused without changing hiding or soundness settings. `BUILD.json` and
`PIPELINE.json` retain the build/configuration pins.

[SCOPE] The explicit verifier TCB contains public query/SIMD encoding,
ciphertext and evaluation-key decoding, public seed expansion, canonical RNS
lifts and NTT transforms, generated-plan interpretation, affine additions,
IR2 loading/proof backend, and phase/row binding code. These implementation
layers are not claimed to be Lean-refined. The proof binds the supplied model
content digest; the saved revision-9 model's nine teaches and one expiry were
not historically proof-gated and are not proved here. This result covers the
retained one-class kernel Infer arithmetic under that TCB, not text-encoder
correctness, BFV security/noise, key validity/custody, journal authorization, or
a shipped system. Component expansion stopped after this acceptance.
