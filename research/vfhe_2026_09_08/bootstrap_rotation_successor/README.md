# Proved initial TFHE lookup-accumulator rotation

[EXECUTED] This successor proves the complete saved initial GLWE accumulator rotation from `../bootstrap_successor/` and joins it to that package's genuine modulus-switch proof. The new proof covers all2048 coefficients: three mask polynomials and one body polynomial, each of degree512. The joined native verifier accepts both proofs. Changing one saved output coefficient makes the rotation proof fail while the prior proof still passes.

| Saved single-run result | Value |
|---|---:|
| New rotation proof | 290,448 bytes |
| New proof generation | 386.374 ms |
| Fresh rotation verification | 22.451 ms |
| Prior proof verification in that same consumer | 17.264 ms |
| Changed-output rotation rejection | 12.709 ms |
| Rows / trace width / arithmetic constraints per row | 2048 / 111 / 113 |
| Exact public tables | 2048 input rows +2048 output rows |

[EXECUTED] These are one local native observation, not comparative benchmarks. There was one new proof, its normal self-verification, one fresh joined acceptance and one changed-output refusal. Each joined prove/verify invocation verifies the prior proof first. No new TFHE keys, encryption, rotation, Boolean gate or other encrypted operation was run; all ciphertexts are byte-identical copies of the first package's genuine fixture.

## Exact relation

[SOURCE/DERIVED] TFHE1.6.3's `polynomial_wrapping_monic_monomial_div` divides by `X^b` modulo `X^512+1`. For output index `j`, let

```
source = (j+b) mod512
sign   = floor((j+b)/512) mod2
x      = input[component,source]
output[component,j] = x                    if sign=0
                    = (2^32-x) mod2^32     if sign=1
```

[DERIVED, kernel checked] `Compiler/TfheInitialRotation.lean:41` states the complete row law, including canonical u32 words, index and exponent ranges, forced source index and sign. `rowSound` proves it for every accepting assignment. The generated relation uses existing bit-range gadgets and three small equations:

```
j+b = source +512*sign +1024*fullPair
outLo +2*sign*inLo = inLo +65536*carryLo
outHi +2*sign*inHi +carryLo = inHi +65536*carryHi
```

[DERIVED, kernel checked] Limbs are16 bits and each sign/carry is Boolean. Every equation is lifted from BabyBear only after proving both sides smaller than its modulus. This forces native-u32 wrapping negation, including `-0=0`, and rules out unnoticed field wrap. `library_sign` at line129 proves equivalence to the library's split at `512-(b%512)` and odd-full-cycle sign toggle. `source_injective` and `source_surjective` prove that the source map is a permutation on all512 positions for every exponent.

[EXECUTED] Eleven exact guarded axiom reports pass. Eight use `[propext, Classical.choice, Quot.sound]`; the three index/sign lemmas use `[propext, Quot.sound]`. `zero_witness` and `negated_one_witness` are kernel-computed inhabitants of the actual system; the latter exercises `1 -> 2^32-1` at exponent512. `changed_zero_refused` excludes output1 for input0 for every auxiliary assignment and every admitted index/exponent. Only this new Lean module was compiled using existing predecessor oleans. The final compile log is empty and exits0.

[EXECUTED] The exporter serializes the simplified source terms by `Signature.fold` into IR2 and produces the witness in Lean. Rust contains no separate arithmetic AIR or carry producer. Table11 binds every actual indexed output with the verified exponent. Table12 binds every actual indexed input coefficient; the generated lookup uses the constrained source index. The proof therefore includes input selection, not just arithmetic on an externally selected pair. All2048 saved native rows satisfy the source system; changed-output and out-of-range-limb source controls fail as intended.

## Joined public consumer

[EXECUTED] `src/main.rs:21–45` strictly decodes `pbs_input.ct`, `initial_lut.ct` and `body_rotated_lut.ct` using TFHE's existing types, with size limits, canonical re-encoding, no trailing bytes, native modulus and exact dimensions. It checks every prior row's input limbs against the decoded LWE ciphertext, including the original padding rule. The exact body row is `[805,56149,55195,862]`.

[EXECUTED] The consumer verifies the prior modulus-switch proof against the prior template's fixed expected SHA256 and those ciphertext-bound rows. Only after acceptance does it use body exponent862 to construct every new output-table row. It constructs the input table directly from the complete decoded initial GLWE ciphertext. It then runs the unchanged shared `FixedPublicPreprocessing` backend on the new statement and proof. This is a conjunction of two actual proof verifications with an explicit public-value join; it is not recursive verification inside one proof or a new cryptographic composition theorem.

[EXECUTED] The negative changes bit0 of decoded output coefficient1536, the first body coefficient, before constructing the public statement. The prior proof still accepts; the new verifier returns `InvalidOpeningArgument(InvalidPowWitness)`. The rejection comes from actual proof verification, not a fixture hash comparison or success flag.

```sh
cargo build --release --offline --locked -j2
target/release/tfhe-bootstrap-rotation-proof verify \
  artifacts/template_ir2.json fixtures/normal_001 \
  results/proof001/proof.bin replay.json
```

[SOURCE] The caller must select the intended new template using the package pin; arbitrary supplied templates define arbitrary relations. Its SHA256 is `558397bfd2c7c048b7b5b375d607fadcad4150db54f6492e28281eee1a35ecbc`. The prior template pin is built into the joined consumer. The fixture directory contains all public inputs and the complete prior proof, so replay needs neither keys nor access to the predecessor directory. The local Rust crate uses the existing companion/backend path dependencies; it does not reimplement or copy their verifier configuration.

## Scope and handoff

[EXECUTED] `execution_pins.json` froze the new source, executable, emitted descriptor/witness, public fixtures and relevant dependencies before the new proof. `MANIFEST.json` is the final handoff. The source patch adds just `Compiler/TfheInitialRotation.lean` and `EmitTfheInitialRotation.lean`, on top of the first bootstrap and arithmetic-coverage compiler proposals. The raw trace is also retained compressed for transport. Existing packages, companion sources and microsite files were untouched.

[OPEN] The verified PBS prefix now consists of the prior complete LWE modulus switching followed by this complete initial accumulator rotation. It stops before the first mask-controlled `(X^a-1)*ct0`, signed decomposition and FFT external product. It is not a full blind-rotation/PBS proof, a proof of AND's earlier affine precursor, a proof of lookup-table construction or semantics, a noise/decryption theorem, or a useful encrypted-learner proof. No security-bit or new zero-knowledge claim is added.

[OPEN] Lean establishes source arithmetic, range and permutation soundness and the existing simplification equivalence. It does not formalize TFHE's serialized representation, the Rust reader and join, JSON transport, exact-public-table implementation, or the deployed proof protocol. The saved native ciphertexts, strict public reader, source-derived relation and actual proof results exercise those boundaries without labelling them kernel theorems.
