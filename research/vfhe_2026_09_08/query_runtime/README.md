# Whole signed-query ciphertext arithmetic

[EXECUTED] This runtime binds a canonical committed learner state,
a canonical public query and the complete two-component ciphertext result to a
Lean-generated joined relation. Each8192-row statement covers the positive
ciphertext–plaintext product, the negative product and their final subtraction.

The57 public columns are rowID then accumulator, positive encoded plaintext,
negative encoded plaintext and final output. Each value has two RNS primes and
seven radix64 digits. The same plaintext NTT coefficients occur in both
ciphertext-component blocks. Intermediate product values are internal witnesses,
computed by the Lean exporter from the public input rows.

The reader uses the fixed resident-crypto parameters and81-byte RSBFV001
ciphertext envelope. It requires canonical full serialization, exact shape,
matching declared key identifiers, a577-entry bounded integer query and its
canonical JSON encoding. The declared key identifier does not prove key
membership. Query reversal/sign split, polynomial encoding and its NTT remain
explicit implementation assumptions; no secret key is read.

`export` reproduces the actual library products and compares the complete final
payload with the submitted output. It retains the actual product coefficients
and checks all32,768 product residues once. Proving and verification reconstruct
only the public encoding/rows; verification does not rerun those products.
Rust writes no AIR or arithmetic witness. The shared portable preprocessing
backend remains unchanged, with the same witness hiding and proof parameters.

```sh
cargo build --release --offline -j2
target/release/vfhe-query-runtime export ACC_CT QUERY_JSON OUTPUT_CT NEW_CASE
RAYON_NUM_THREADS=4 target/release/vfhe-query-runtime prove TEMPLATE CASE TRACE NEW_PROOF
RAYON_NUM_THREADS=4 target/release/vfhe-query-runtime verify TEMPLATE CASE PROOF_BIN
RAYON_NUM_THREADS=4 target/release/vfhe-query-runtime verify-changed-output TEMPLATE CASE PROOF_BIN
```

The application chooses the approved generated template. The runtime replaces
only its57-column ExactPublicRows table11. The final output begins at column43;
the negative check changes its first digit. Strict postcard decoding rejects
trailing bytes. Statement/proof parsing and metadata/receipt authorization remain
implementation responsibilities, distinct from the generated arithmetic theorem.

[EXECUTED] The initial active-class proof, fresh verification and changed-output
rejection passed. `REPORT.md` and `RESULT.json` retain exact scope and costs.
For production orchestration, use the fixed pipeline:

```sh
python3 run.py ACC_CT QUERY_JSON OUTPUT_CT NEW_RUN
```

A successful result is `NEW_RUN/result.json` with `verified: true`.
The case is `NEW_RUN/case`, and the proof is `NEW_RUN/proof/proof.bin`.
The pipeline pins the unchanged native verifier, approved template and Lean
sources. It emits fresh witnesses, checks exact template equality, proves and
verifies in separate native processes. It performs no private receive.
The calling service owns process-group cancellation/quiescence, metadata and
accepted-head checks. Each class requires its own complete query proof; the
initial saved-case result is not a proof of the other class or of ranking.
