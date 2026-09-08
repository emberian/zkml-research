# Compiler-native arithmetic for the live BFV query

[EXECUTED] The actual committed `card_arrival` query now has a proof of **both ciphertext/plaintext products and their final subtraction**, over every serialized NTT coefficient of both components and both primes. The sibling `query_runtime` runner proved the emitted relation, verified it in a fresh process, and rejected a changed final output digit. This is the exact query arithmetic component; it does not prove query encoding, decryption, classification correctness, or the service protocol.

[DERIVED] Four new Lean modules check with **22 exact guarded axiom pins**, using only standard Lean axioms. `source_pins.json`, `declarations.json`, and `results/validation.json` give the selected bytes, every theorem's location, and the four successful commands. No companion source was changed. `query-arithmetic.patch` adds the modules and executable emitter for integration on minidregg base `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd`, after the listed arithmetic-coverage and assertion-sharing prerequisites.

## Source and theorem

[SOURCE] `research/learn_infer_only/experiments/end_to_end/crypto/src/main.rs:242–252` performs:

```
pp = Plaintext::try_encode(reverse(max(query, 0)), Encoding::poly(), parameters)
pm = Plaintext::try_encode(reverse(max(-query, 0)), Encoding::poly(), parameters)
answer = canonical((acc * pp) - (acc * pm))
```

[SOURCE] This branch has no rotation, key switching, rescaling, or ciphertext/ciphertext multiplication. The supplied public query has 577 signed coefficients; the native reader later reads decrypted coefficient 576. The ciphertext arithmetic uses N=4096, two components, level zero, plaintext modulus 4294828033, and ciphertext primes 2199023190017 and 4398046486529. These are source facts and public reader checks, not consequences of the new multiplication theorem.

[DERIVED] `Compiler/BfvQueryMul.lean` defines a reusable `ConstraintSystem` through existing compiler arithmetic constructors. `rowSystem_sound` requires only `0 < q < 64^7` and an accepting assignment. The relation itself forces all three words A, B, O into `[0,q)` and concludes `O = (A*B) % q`. The caller supplies no product, carry, bit, quotient, or canonicality premise.

[DERIVED] Seven radix-64 digits represent each word. Fourteen schoolbook columns constrain `A*B = O + q*K`; K has seven range-checked digits. A signed carry is represented by `c+512`, with endpoints fixed to 512 and ten-bit ranges. Each column asserts

```
convolution(A,B)[t] + encodedCarry[t] + 32768
  = padded(O)[t] + convolution(qDigits,K)[t]
    + 64*encodedCarry[t+1] + 512.
```

[DERIVED] `convolution_denote`, `padded_denote`, and `radix_balance` prove the full integer identity, including the top column. `convolution_bound` conservatively bounds each sum by `49*3969`. The two natural sides are at most 228272 and 260528, respectively, strictly below BabyBear's 2013265921; the proof therefore lifts each field equality to an integer equality. Canonical O makes the modular answer unique. These are compiled kernel proofs, not a finite test of the universal statement.

[DERIVED] `Compiler/BfvQueryRow.lean:66`, `wholeRowSound`, composes two multiplication gadgets with the existing `BfvExpiry.rowSystem_sound`. Both products share A; their outputs are the subtraction inputs, and its added fresh word is constrained to zero. For each prime it proves

```
O = ((A*Pplus)%q + q - (A*Pminus)%q) % q.
```

[DERIVED] The final `emittedSystem_sound` applies the existing semantics-preserving `AirAssertionShare.optimize` pass. `EmitBfvQuery.lean` serializes this exact source by `Signature.fold` into the existing ordered DescriptorIR-v2. No Rust-authored replacement AIR is present.

## Witnesses, refusal controls, and execution

[DERIVED] `Compiler/BfvQueryTeeth.lean` constructs a nonzero accepting instance `3*5=15` modulo 17 and applies the universal core to that inhabited premise. A second assignment has output 14 while **all three canonical word gadgets still accept**; `wrong_output_refused` rules it out through multiplication soundness. The separate `digitwise_falsifier` exposes the lost carry in 63*63. These small proofs do not claim kernel reduction of the complete 8192-row runtime witness.

[EXECUTED] `Compiler/BfvQueryWitness.lean` constructs every private product, quotient, carry, slack and range witness from public input values; it copies the caller's output unchanged. The emitter checks four constructed cases (zero, nonzero, maximum residues, and a negative result), a changed output, and a radix-64 overflow. Actual rows are streamed without duplicate interpreter constraint checks; the actual prover checks them. During development a wrongly inferred field-valued canonical carry was caught by the first constructed case and fixed by explicitly typing it `Nat`; the failed logs are retained. Final guarded checks are all green.

[EXECUTED] The emitted real fixture has 8192 rows, 2509 columns, 57 public tuple entries, and an 82,214,912-byte trace. Generic simplification and assertion sharing reduce 4442 source constraints to 2744 arithmetic assertions plus the existing public-row binding. `artifacts/emission.json` records these counts. Public order is `rowID, accumulator(2×7), positivePT(2×7), negativePT(2×7), output(2×7)`; the private intermediates are not external premises.

[EXECUTED, sibling lane] `../query_runtime/results/prove001.stdout`, `verify001.stdout`, and `reject001.stdout` record an 842,564-byte proof, 3.813823250 seconds proving, 0.100227250 seconds self-verification, and 0.111377250 seconds fresh verification. The fresh changed-output run rejected. This is one shared-host observation with four Rayon threads, not a throughput distribution or a new security estimate. The unchanged backend fingerprint is recorded in the native log.

## Reuse and exact scope

[EXECUTED] The selected template SHA256 is `f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d`; the first trace is `8f1d1a0ab009f41756e2164c4a0a833494f1d76ad07992f58b767fb495e78cc5`. The proof is `1fa6b436dd9fab6c84500469e1752f5785226459600708c924dfa5bd2e6ce9f9`. Full source and artifact hashes are in the two pin files. Files are frozen; later service runs must use new output directories.

[EXECUTED] Reusable emitter command, from `/Users/ember/dev/minidregg` (pass caller-owned output directory and public-row JSON as separate arguments):

```sh
lake env bash -c 'LEAN_PATH=/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_arithmetic/build:$LEAN_PATH lean --root=/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_arithmetic --run /Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_arithmetic/EmitBfvQuery.lean "$1" "$2"' query-emit OUT_DIR PUBLIC_ROWS_JSON
```

[OPEN] The native public reader binds canonical ciphertext serialization and computes the exact plaintext NTT encoding. Its parser, `fhe` encoding/NTT implementation, model/request association, proof backend, and protocol logic remain outside this Lean theorem. The native complete payload equality check is concrete correspondence evidence, not a formal NTT or serialization theorem. Decryption, centered coefficient extraction, plaintext/noise bounds, and classification semantics are not proved here. The separate journal successor owns request/committed-state binding and proof-before-private-read behavior.
