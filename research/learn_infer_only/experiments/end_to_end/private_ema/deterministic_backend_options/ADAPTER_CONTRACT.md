# Proposed next artifact: native-u32 integer PBS adapter

[HYPOTHESIS] A new isolated source package, not a modification of `emitted_fixed_fft`, should first expose a small bootstrap adapter that delegates to the existing public routines. No new gate schedule, EMA arithmetic, decomposition implementation, convolution implementation, or bootstrap traversal is needed. This note is a design; no Rust code has been compiled here.

[SOURCE] Proposed interface types are already exported by TFHE 1.6.3 core_crypto:

```rust
// Interface sketch only; intentionally no hand-written PBS implementation.
fn bootstrap_u32(
    input: LweCiphertextView<'_, u32>,
    output: LweCiphertextMutView<'_, u32>,
    lut: GlweCiphertextView<'_, u32>,
    standard_bsk: LweBootstrapKeyView<'_, u32>,
    scratch: &mut PodStack,
);
```

[DERIVED] Its executable body can be limited to cloning the LUT into initialized scratch, constructing the existing lazy modulus-switched input, calling `blind_rotate_karatsuba_assign_mem_optimized`, and calling `extract_lwe_sample_from_glwe_ciphertext` at monomial0. All are public; the generic blind-rotation bounds include u32. Use `programmable_bootstrap_karatsuba_lwe_ciphertext_mem_optimized_requirement::<u32>` for scratch layout, while accounting separately for heap allocations inside Karatsuba. Type-checking this composition remains the first implementation check. Do not call the u64-only convenience PBS wrapper with a coefficient cast.

[HYPOTHESIS] Validate before calling: native u32 moduli; N power-of-two; all dimensions match; input LWE dimension equals BSK input; output dimension equals kN; GLWE size=k+1; 0<l*b<32; nonempty levels; modulus-switch log=log2(2N)<32; initialized LUT and complete key data. The exact frozen source parameter geometry n837/k2/N1024/b10/l2 satisfies the numeric constraints. Preserve the parameter and ordinary PBS→KS order. The sign LUT is the existing zero mask and body filled with `PLAINTEXT_TRUE` (`T/src/boolean/engine/bootstrapping.rs:43–65`). Use existing key switching rather than implementing it again.

[OPEN: setup] Input key material must be a standard u32 public BSK or publicly decompressed seeded BSK plus compatible u32 KSK. The current ordinary ServerKey retains Fourier BSK. Do not infer an exact inverse conversion or access current keys. A later authorized new setup can retain standard coefficients before Fourier conversion, or use a new compressed public key; it must record whether it starts a separate key/trajectory. Generating another public BSK for the same client key is a new setup action, not offline reconstruction of the old key.

[HYPOTHESIS: bounded acceptance sequence] First type-check the adapter in an isolated pinned dependency checkout. Next test its lowest reused polynomial or external-product seam on synthetic public coefficient arrays against independent wrapping schoolbook arithmetic, including all-zero, maximum-u32, negative decomposition digits and negacyclic wrap cases. Such arrays require no client key and are not failed-run ciphertexts. Only a separately authorized follow-on should generate new toy keys and test bootstrap semantics or process replay. A full EMA run is not the first cost probe: the source upper bound approaches five billion scalar multiply-accumulates for one PBS at the current geometry.

[OPEN: gate integration] The Boolean engine's AND/XOR branch dispatch is private and takes the ordinary ServerKey. A full successor must introduce a narrow bootstrap-provider hook in an isolated TFHE patch, so the existing affine gate preprocessing and trivial-constant handling can call the new integer provider. Alternatively a separately reviewed wrapper can delegate existing linear primitives, with explicit source correspondence for those few gate rules. Merely implementing another learner circuit is outside this artifact. The frozen emitted JSON remains the sole circuit descriptor for a future generic interpreter.

[HYPOTHESIS: NTT follow-on] Once an exact integer reference exists, replace only its polynomial multiplication seam using `tfhe_ntt::native32::Plan32`, or compare the u64 BNF path under an explicitly proved embedding/error contract. The Plan32 CRT bound in the audit supports one product and a six-product sum at N1024; any other accumulation strategy needs its own bound. The native-binary transform is unsuitable unless an actual multiplied polynomial is binary.

[OPEN] Completion here would mean a checked adapter and local arithmetic correspondence, not Rust language refinement or cryptographic security. Cross-platform output-byte equality still depends on correct integer implementations, compiler lowering, initialized memory, successful allocation/completion, fixed serialized key/input data and canonical output serialization. Equality to the old FFT ciphertext bytes is not an acceptance condition; correct plaintext action and independent deterministic recomputation are distinct obligations.
