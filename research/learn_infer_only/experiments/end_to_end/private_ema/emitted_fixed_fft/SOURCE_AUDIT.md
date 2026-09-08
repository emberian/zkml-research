# Fixed plan source boundary

[SOURCE feature] `feature_source.txt` retains exact numbered excerpts from the
cached TFHE 1.6.3 and tfhe-fft 0.10.1 sources, including the Cargo feature and
the two Fft::new branches. `build_pins.json` records full-file hashes and byte
equality with the corresponding local crate archives. The actual feature name
is `experimental-force_fft_algo_dif4`; the initial `fft64-default` shorthand
was corrected before the new Cargo.toml, build and freeze.

[SOURCE factory] TFHE
`src/core_crypto/fft_impl/fft64/math/fft/mod.rs:169–188` selects either timing
measurement of candidate FFT plans or a supplied Dif4 plan whose base size is
the Fourier size. The feature fixes that selection branch. It does not remove
every platform-dependent SIMD dispatch, floating-point assumption or remaining
implementation dependency.

[EXECUTED build feature evidence] Cargo's retained compiler-artifact event in
`build.events.jsonl`, copied into `build_pins.json`, lists exactly `boolean`
and `experimental-force_fft_algo_dif4` for TFHE. The dependency lock bytes are
identical to the preceding generic runtime. `src/lib.rs` and
`src/ciphertext.rs` are byte-identical to their prior versions. The only main
program changes are in `main_source.diff`: include the diagnostic module,
observe the plan at key load and add its public report field. No alternative
learner semantics was added. Tests/build and all commands are retained.

[SOURCE observed object] `src/plan_observation.rs:16` decomposes the public
ServerKey through `into_raw_parts`, reads its bootstrap polynomial size, and
immediately reconstructs it from the same buffers and order. TFHE
`boolean/engine/bootstrapping.rs:106–161` supplies those public APIs; reconstruction
checks compatibility and returns the same component fields. It does not sample
coins or alter key buffers. This is a source claim, not a theorem for Rust moves.

[SOURCE observed plan] The diagnostic obtains `Fft::new` at that size, formats
its public FftView Debug, and extracts the compact underlying Plan record.
TFHE Fft/FftView derive Debug at fft/mod.rs:81–90; tfhe-fft
`unordered.rs:514–521` emits only base algorithm, base size and FFT size for
the Plan. The diagnostic checks the exact expected Dif4/base-size/Fourier-size
record before host gate execution. It does not export the surrounding public
twiddle arrays or any key coefficients. Debug formatting is a version-pinned
diagnostic, not a stable cross-version schema.

[SOURCE cache and scope] TFHE fft/mod.rs:103–108 defines the process-local map;
Fft::new uses get_or_init at 193–197. Boolean bootstrap calls Fft::new at its
actual public Fourier bootstrap-key size (bootstrapping.rs:460,501,547), so the
diagnostic observes the same per-size cache in that process. The assumptions
include normal single-process execution and no later custom-plan replacement.
`pin_build.py` retains the `rg -n setup_custom_fft_plan src` search of this
successor's Rust source tree: no matches. A separate read-only search of the
cached TFHE 1.6.3 src tree for `setup_custom_fft_plan\(` found only the public
setter definition at fft/mod.rs:110. Neither observation proves Rust/cache or
floating-point semantics.

[SOURCE input selection] `inputs.json` was generated from the prior successful
emitted smoke's four exact operation tuples and the older failure audit's
`failed_pair.public_read_inputs`. It never loads the old failed output paths.
The retained preceding parent states are public ciphertexts; selecting them
holds each control input fixed but does not produce a new learning trajectory.
The old fourteenth-failure tuple is evaluated with the emitted schedule, while
the failed predecessor used hand-authored Boolean operations. This additional
program difference and absent old plan logs prevent causal attribution.

[DERIVED new result boundary] These public-only controls ask whether each
declared build/platform/plan/input tuple produces equal output bytes in two
fresh processes. They do not test plaintext correctness, compare with the old
failed output, retry the old workload, prove deterministic cryptography, or
support an unrestricted replay policy. The earlier mismatch remains retained
evidence. A changed backend needs separately authorized correctness/utility
integration before such claims could follow.

[EXECUTED research accounting] This lane used local repository, cached source
and crate-archive reads. No web, Scry, Kagi, private-key or decryption queries
were used. Cryptographic host invocation counts are recorded in the separate
controls report, not inferred from source.
