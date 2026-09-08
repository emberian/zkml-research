# A proof-bearing TFHE bootstrapping entry component

[EXECUTED] This package proves the complete native modulus-switch map for the 806 coefficients of a fresh TFHE Boolean AND's pre-bootstrap LWE ciphertext. A real proof was produced and accepted in a fresh process. Changing one claimed rotation exponent makes the existing cryptographic verifier reject the same proof.

| Saved result | Measurement |
|---|---:|
| Fresh TFHE `AND(true,false)` | 14.271 ms; decoded false |
| Actual LWE words / padded proof rows | 806 / 1024 |
| Trace width / arithmetic constraints per row | 55 / 55 |
| Proof bytes | 233,366 |
| Proving | 829.121 ms |
| Fresh verification | 22.915 ms |
| Changed-exponent rejection | 16.254 ms |

[EXECUTED] Timings are a single local native run, with both fresh verifier processes launched concurrently; they are operational observations, not benchmark estimates. The prover also performed its ordinary same-process verification. The saved reports and exact commands are under `results/`.

## What is proved

[DERIVED, kernel checked] For each public row `(rowID, low16, high16, exponent)`, acceptance of the generated arithmetic implies

```
x = low16 + 65536 * high16
0 <= x < 2^32
0 <= exponent < 1024
exponent = floor((x + 2^21) / 2^22) mod 1024
```

[SOURCE] This is TFHE 1.6.3's existing `modulus_switch::<u32>(x, CiphertextModulusLog(10))` on its default Boolean preset: polynomial degree512, input LWE dimension805, GLWE dimension3, PBS base-log10 and level-count2. It determines the negacyclic rotation exponents modulo `2N`. The exact native implementation adds the rounding offset with wrapping u32 addition and shifts right22. See `SOURCE_SCOPE.md` for exact source locations and the distinction from the paper's parameters.

[DERIVED, kernel checked] `Compiler/TfheModulusSwitch.lean` proves this using the compiler's existing bit-range gadgets and the small integer equation `high16 + 32 = 64*exponent + remainder6 + 65536*wrapBit`. Both sides are proved smaller than BabyBear before lifting the field equality to an integer equality. Low16 cannot alter the rounded quotient. This retains the torus wrap bit; it does not replace u32 arithmetic with an unchecked prime-field congruence.

[EXECUTED] The five guarded theorem axiom reports are exactly `[propext, Classical.choice, Quot.sound]`. A kernel-computed zero witness inhabits the actual relation, and a universal falsifier excludes exponent1 for input0 for every auxiliary assignment. The exporter checked eight rounding/wrap boundary cases and eight changed-exponent negatives, then every native row. Only this new Lean module was compiled, reusing predecessor oleans; no whole-tree build was run.

[EXECUTED] The IR2 constraints are an ordered `Signature.fold` serialization of that same simplified Lean source system. Lean also generates and checks the witness. Rust supplies the caller-visible rows and uses the existing descriptor parser and shared `FixedPublicPreprocessing` backend; it contains no independent arithmetic AIR. The existing exact-public-row table11 binds the row tuples, including IDs. The 218 padding rows repeat actual input/exponent pairs with new IDs.

## Native fixture and scope

[EXECUTED] `native/src/main.rs` generated a fresh default Boolean keypair and two encrypted Boolean operands, invoked the same `ServerKey::and` API used by the completed emitted runtime, and checked its plaintext result while the ephemeral client key was in memory. No key was saved. It then used the exact core calls from `BooleanEngine::and` to capture `left + right - 1/8`, and invoked the existing lazy modulus-switch API on all mask words and the body. These are fresh fixture ciphertexts, not previously stopped or failed artifacts. `fixtures/normal_001/operation.json` pins all public files.

[EXECUTED] The native fixture also constructed the actual constant Boolean lookup accumulator and executed the existing `X^(-bodyExponent)` negacyclic monomial-division routine, saving both GLWE ciphertexts. **That polynomial rotation and the full AND are operational results outside this proof.** The proof establishes the modulus-switch relation between the public tuples supplied to its verifier. The source-level ciphertext decoder/exporter is not a Lean-refined or cryptographically proved parser, nor does the proof itself establish the preceding AND affine combination or ciphertext decryption correctness.

[OPEN] This is an integer entry component of PBS, not a proof of a complete programmable lookup, blind rotation, external product, key switch, useful encrypted learner, or the paper's folding protocol. The next exact runtime boundary is the first `(X^a-1)*ct0` polynomial and its signed decomposition. The existing external product then uses complex FFT arithmetic and torus conversion; replacing it with an ideal ring product would change what is being verified. See `SOURCE_SCOPE.md`.

[SOURCE] The proof backend retains its existing public-only deterministic preprocessing adapter and ordinary randomized hiding commitments. Its full backend ID is recorded in `results/proof001/proof.json`. This package establishes actual acceptance/refusal under that backend; it adds no security-bit, zero-knowledge, QPT, or deployment claim.

## Public replay and reproduction

[EXECUTED] Public proof replay needs no TFHE secret or server key:

```sh
proof/target/release/tfhe-bootstrap-entry-proof verify \
  artifacts/template_ir2.json fixtures/normal_001/public_rows.json \
  results/proof001/proof.bin replay.json
```

[SOURCE] The caller must select the intended template and public rows using the package pins; arbitrary caller-selected rows define an arbitrary statement. The verifier checks exact shape, canonical field elements, strict proof decoding with no trailing bytes, and the actual proof. The negative command `reject-changed` changes row0's public exponent and requires a backend rejection. The saved negative reports `verifier_ran: true` and `InvalidOpeningArgument(InvalidPowWitness)`.

[SOURCE] `build.sh` builds only the two owned Rust crates with their lockfiles. The Lean patch adds `Compiler/TfheModulusSwitch.lean` and `EmitTfheModulusSwitch.lean`; it depends on the already completed `arithmetic_coverage` proposal. `run_record.py --lean` reuses the recorded local Lean overlay. The compressed trace is retained for transport; no further proof run is needed to consume this result.

[EXECUTED provenance limitation] The proof executable finished building at17:10:28UTC, during another lane's accidental formatting of the shared backend source. That source was restored to its original frozen bytes at17:12:25UTC. This lane did not format or modify dependencies. `SOURCE_PINS.json` records the executable, stable source, retained formatting variant and restoration evidence separately; it does not label the restored hash a build-time source freeze. No rebuild or extra proof cycle was performed during closeout.
