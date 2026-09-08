# Reusable public input adapter and native replay

[SOURCE] `prepare_inputs.py` converts the pinned, already cached public prototype/query arrays into `learner_inputs.bin`, validates 64 exact score references and eight decisions, and records its public source hashes and selection rule in `input_reference.json`. Running it does not invoke an encoder. `src/learner_adapter.rs`, retained inside `learner-matvec.patch`, supplies the Rust loader, matrix/scale adapter, exact signed decoder and classification tie rule for this eight-class/eight-query 576-feature batch schema.

[SOURCE] Apply `learner-matvec.patch` in a fresh upstream checkout at commit `00379074cad457367a86dde2ecee9d0f318a7e12`. With locked dependencies cached, public verification is:

```sh
cargo build --offline --locked --release --example verify_saved
target/release/examples/verify_saved /absolute/path/normal_001/statement.bin /absolute/path/normal_001/learner.proof
```

[SOURCE] The verifier source and full proof wire format are identical to the scaled predecessor described in `../scaled/REPLAY.md`. Ring degree remains 4096; the caller's matrix now has width 16384 and 64 rows. No recipient key is needed. The statement/proof together verify the public encrypted computation; the consumer does not independently decode the encrypted score or authenticate that the public statement was selected by a particular application.

[SOURCE] Input adapter binary `LRNJ0001` stores nine little-endian u64 configuration values `[4096,16384,64,576,8,8,16381,16369,128]`, eight length-prefixed UTF-8 labels, eight selected row indices, row-major signed i64 prototype/query/score arrays, and eight reference decision indices. The signed array shapes are 8×576,8×576 and 8×8. The loader bounds and validates this data and recomputes scores/decisions. For the retained native public unit test only, place `learner_inputs.bin` in the parent of the patched crate before `cargo test --offline --locked --release --lib learner_public_packing_and_signed_decode`; it is the known-public fixture referenced by that test.

[EXECUTED] The completed one-batch command, source/binary pins and successful consumer output are retained in `command.json`, `source_pins.json` and `normal_001/replay.json`. `run_once.py` intentionally refuses a second launch. No additional proof generation is required to replay the completed artifact.
