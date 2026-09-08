# Public replay interface

[SOURCE] The portable `combined-matvec.patch` targets upstream commit `00379074cad457367a86dde2ecee9d0f318a7e12` of `https://github.com/tremblaythibaultl/matvecmul`. Apply it in a fresh upstream checkout, then build the verifier with the unchanged lockfile:

```sh
cargo build --offline --locked --release --example verify_saved
target/release/examples/verify_saved /absolute/path/statement.bin /absolute/path/fused.proof
```

[SOURCE] Offline building requires the pinned dependencies already cached. This lane's working cache is `../implementation/cargo_home`, created without copying credentials or Cargo configuration. The completed build command set its absolute path through `CARGO_HOME`. The native consumer's ring degree is fixed at 4,096. It accepts a caller-selected statement and proof, imports no secret state, validates the field encodings and sizes, checks every expected-output coefficient, derives all dimensions and transcript preprocessing from the caller's matrix, and calls the unchanged verifier. Saved successful runs are `paired_001/baseline_replay.json` and `paired_001/fused_replay.json`. Source is retained by patch rather than a second tracked implementation tree.

[SOURCE] Wire encoding in `src/protocol/public_wire.rs`: integers/counts are little-endian u64; fields use arkworks compressed canonical serialization with validation. Both envelopes start with bytes `MVFUSE01`, one kind byte (0 statement, 1 proof), then u64 values `[1,D,p,7,100,1,4,4,1]` for version, degree, base prime, extension nonresidue and the named fixed WHIR configuration. No serialized RNG, transcript or trusted variable count is accepted. The full locked source fixes remaining PCS settings and dimension-derived PoW.

[SOURCE] The statement then stores width and height, row-major field matrix coefficients, and two counted ciphertext vectors: input and caller-selected expected output. Each ciphertext has exactly two components, each with D coefficients, in mask/body order. The proof stores its counted output vector, two sumcheck messages (claim, count of rounds, each counted ordered coefficient vector), two counted commitments, then the three required PCS openings in r0/r1/matrix order. Every opening contains tag 1, its extension-field claim and counted opaque proof bytes. Counts are bounded; rounds and degree bounds derive from the caller's matrix; trailing data are rejected. The CLI bounds either input file at 64 MiB. This is a versioned research transport for the fixed source/configuration, not a separately audited network service.

[OPEN] Any web consumer must preserve canonical validation, caller-selected statement/output binding and fresh preprocessing. Calling a wrapper over only the PCS bytes would not verify the full saved matvec proof.
