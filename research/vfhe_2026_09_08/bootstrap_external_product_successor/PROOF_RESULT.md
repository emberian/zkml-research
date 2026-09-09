# Completed selected external-product proof

[EXECUTED] One generated proof accepts the complete 2,048-coefficient exact output for the retained genuine TFHE accumulator-difference input and the fresh public raw GGSW block. A fresh public consumer also accepts it; changing output coefficient 1,536 by XOR 256 preserves the u32/low-eight-zero representation and reaches the backend, which rejects the changed statement with `InvalidOpeningArgument(InvalidPowWitness)`.

| Measurement | Retained result |
|---|---:|
| New proof | 306,893 bytes |
| Proving | 295.786750 ms |
| Same-process verification | 27.080875 ms |
| Fresh new-component verification | 21.876834 ms |
| Fresh three-predecessor verifications | 60.513167 ms total |
| Changed-output verification/refusal | 15.052708 ms |
| Full trace | 2,048 × 279; 2,285,568 bytes |
| Generated arithmetic constraints | 295 |
| Exact public row width | 46 |

[EXECUTED] Proof SHA256: `89ee3f4e6d61ec11bb3c9fec0404bb2b32ced48a42efb117622bbb627a8dd8c7`. Template SHA256: `9a3f98d241dad5430e980941ddf4fa0a360ec11c291e51a833f280dee71101b3`. Logs `results/prove-001.*`, `verify-001.*`, and `reject-001.*` retain the exact commands; all exit 0 with empty stderr. The standalone API is in README.md. No second proof or setup was run.

[EXECUTED kernel] All six final recurrence-module checks pass, including 33 exact guarded foundational-axiom lists. The universal shared-array theorem proves the anchored recurrence equals the complete negacyclic convolution in Z/(2^24), and that each raw u32 output is exactly 256 times its canonical 24-bit value. The canonical public reader enforces index/flag transport, prefix adjacency and shared key/output arrays. Nine actual boundary rows and output/scale/anchor falsifiers were interpreted during emission; the actual proof and fresh verifier cover the full generated relation. Lean generates the constraints and trace; the native consumer does not duplicate an AIR.

[EXECUTED] `proof_pins.json` was written successfully before the proof; it records 121 entries. Every actual source, generated artifact, input and binary entry remains unchanged, as do all 37 pre-capture pins. One metadata-only change is explicit: `formal_recurrence/SOURCE_PINS.json` grew from SHA `0fe1809b…` to `5b7bfb47…` through four direct dependency pins and one public-row pin. Exact old bytes were recovered by removing those added entries and matching the pre-proof hash; both versions and the extension appear in `results/pin-closure.json`. Added dependency entries are recorded as post-proof metadata, not retroactively claimed pre-proof pins.

[OPEN] The accepted statement uses the actual sparse first-step digit pattern and a fresh single GGSW block with a new key identity. The general native backend supports dense digits, but this proof covers this selected pattern only. It does not establish the original full bootstrap, later dense products, encryption correctness, formal FFT equivalence, or a new security theorem. The shared proof backend and its parameters are unchanged. The full-PBS successor remains held and unlaunched.
