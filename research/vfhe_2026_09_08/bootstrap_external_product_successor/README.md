# Selected exact TFHE external product

[EXECUTED] This package computes the complete first external product for the saved genuine torus32 accumulator difference, using a new exact CRT-NTT backend and one freshly generated public GGSW block. All 2,048 output coefficients agree with the complete integer reference and the existing TFHE Karatsuba path. Native measurements, source locations, key-identity boundary and the one observed Fourier agreement are in [NATIVE_RESULT.md](NATIVE_RESULT.md).

[DERIVED] The proof boundary is the complete output for the actual sparse signed decomposition: all level-2 digits vanish; the only active level-1 polynomial has coefficients +256 on [0,44), zero on [44,162), and −256 on [162,512). This permits a small anchored recurrence over Z/(2^24), followed by exact multiplication by 256 into native u32. The general CRT-NTT implementation accepts dense digits, but this generated proof does not certify other digit patterns.

[EXECUTED kernel] Lean derives the arithmetic constraints from a shared source and proves that their satisfaction, together with the canonical reader's shared-array/index bindings, gives the full negacyclic convolution. The anchor is computed through all 512 key coefficients by public prefix transitions; it is not supplied as an unchecked claimed sum. The source includes an inhabited premise and counterexample showing why the anchor cannot be omitted. `formal_recurrence/` owns this generated relation and its source evidence. `Compiler/TfheCrtRange.lean` separately proves the generic signed CRT range and reconstruction lemmas.

[DERIVED] The consumer first verifies the saved modulus-switch, initial-rotation and signed-decomposition proofs. It decodes the canonical raw GGSW and output ciphertexts, constructs all 2,048 indexed public rows, enforces the actual digit pattern and zero low eight output bits, pins the exact generated template, and invokes the existing shared `FixedPublicPreprocessing` proof backend. No arithmetic constraints are handwritten in the Rust consumer. Active key residues are bound modulo 2^24; inactive raw rows and the active coefficients' upper eight bits cannot affect this selected product. Whole-file hashes preserve their artifact identity separately.

[OPEN] This is a selected integer-component proof, not a complete blind rotation, PBS proof, original-key continuation, proof of GGSW encryption correctness, or formal equivalence of floating FFT execution. The fresh public GGSW has a new GLWE key identity. No full-PBS successor has launched; that proposed execution is held pending the architectural decision.

Build and public consumer API, from this directory:

```sh
cargo build --release --manifest-path consumer/Cargo.toml
consumer/target/release/tfhe-external-product-proof verify formal_recurrence/artifacts/template_ir2.json fixtures/normal_001 results/proof001/proof.bin results/replay.json
consumer/target/release/tfhe-external-product-proof reject-changed formal_recurrence/artifacts/template_ir2.json fixtures/normal_001 results/proof001/proof.bin results/rejected.json
```

[DERIVED] `verify` uses public files only. `reject-changed` changes output coefficient 1,536 by XOR 256, preserving the low-eight-zero representation and forcing the existing cryptographic verifier to decide the changed statement. These commands do not generate keys or invoke a prover. Exact recorded invocations and proof metrics are retained in `results/`; [PROOF_RESULT.md](PROOF_RESULT.md) records the accepted 306,893-byte proof and fresh changed-output refusal.
