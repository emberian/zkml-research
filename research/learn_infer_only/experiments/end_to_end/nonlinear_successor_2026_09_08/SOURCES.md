[SOURCE] No web or Scry queries were used for this successor. The task is an implementation/evaluation over saved local inputs.

- `../useful_learner_2026_09_08/encoder.py`: actual frozen E5 masked-mean/L2 embedding, fixed random projection and quantization. Its `config.json` identifies the local encoder checkpoint and projection seed. Reused read-only.
- `../useful_learner_2026_09_08/{data/selected.json,features.npz,plaintext_result.json}`: the fixed128/320 eight-class fixture and original prototype scores. Data has already been evaluated; this successor does not make a fresh held-out claim.
- `/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ops/mul.rs:159`, `Multiplicator::multiply`: deployed basis extension, component products and downscale. `/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ops/mod.rs:259` is the direct ciphertext multiply implementation. Both trees are read-only.
- `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/src/rns/scaler.rs:71`, `RnsScaler::new`, and `:240`, `scale`: exact directed fixed-point constructor and operation. `src/rq/scaler.rs:26` supplies the polynomial wrapper. This source, not an ideal rounding formula, underlies the trace.
- `public_trace/native_scaler_constants.json`: values extracted from the actual native constructor with the public9→4 bases and t/Q. It uses no keys or ciphertexts. `crypto/src/scaler_constants.rs` is the extractor.

[EXECUTED] `SOURCE_PROVENANCE.json` retains exact source/dependency/data and baseline/current binary hashes. `RESULT.json` binds the completed aggregate result files and public trace. None of these files claims independent source review or a universal correctness/security theorem.
