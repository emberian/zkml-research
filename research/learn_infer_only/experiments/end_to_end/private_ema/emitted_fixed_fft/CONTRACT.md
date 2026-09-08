# Fixed-FFT public replay controls

[EXECUTED authorization] Root authorized a separate fixed-plan successor with
at most eight host pairs. This contract selects exactly five pairs before
execution. The prior emitted_runtime source/freeze/smoke and older failed long
workload stay unchanged. No retry or full workload is part of this contract.

[SOURCE exact configuration] TFHE 1.6.3 Cargo.toml:95 declares
`experimental-force_fft_algo_dif4`. In its
`src/core_crypto/fft_impl/fft64/math/fft/mod.rs:163–197`, that feature selects
`Method::UserProvided { base_algo: Dif4, base_n: fourier_polynomial_size }`;
without it the factory uses `Method::Measure(Duration::from_millis(10))`.
The preliminary phrase `fft64-default` was not an actual feature name.
This build uses `default-features=false`, features `boolean` plus the exact
experimental feature, and the preceding interpreter's unchanged Cargo.lock.

[DERIVED implementation boundary] Copy the prior generic Boolean interpreter
and envelope adapter unchanged. Add only public plan observation around host
key loading and a report field; no learner/MUX/address/sign circuit is authored.
The two JSON descriptors and schema remain the exact previously emitted files.
The new Cargo feature, source, lock, resolved build features, compiler/platform
and descriptor hashes are frozen separately. The declared platform is the
actual aarch64-apple-darwin host recorded by build_pins.json; this is not a
cross-platform arithmetic or determinism guarantee.

[SOURCE runtime observation] The diagnostic moves a public ServerKey through
its public `into_raw_parts` / `from_raw_parts` API, without modifying buffers,
to obtain the actual bootstrap polynomial size. It calls `Fft::new(size)` and
extracts only the compact `Plan { ... }` record from public FftView Debug.
That record must equal Dif4 with base and Fourier size equal to half the
polynomial size, or execution fails. The process-local plan cache is shared
with the later Boolean bootstrap calls. No custom-plan setter is called by
these sources. This is a source-audited observation path, not formal coverage
of Rust, the cache, floating-point execution or Debug formatting stability.

[DERIVED fixed controls] `prepare.py` materializes five static public input
tuples in `inputs.json`, each pinned before execution. Four are the exact two
Learn and two Infer tuples from the preceding successful emitted smoke's
public records. They use its retained public state bytes, so this is controlled
evaluation of existing cases, not a newly chained learning trajectory. The
fifth is the exact server-key, parent h0-e0013 and ingress h0-e0014.input tuple
from the old long workload's failed fourteenth Learn. That tuple is obtained
from public_failure_audit.json; the old failed output files are never opened,
decoded or compared. All cases use the same emitted Learn/Infer descriptors.
Because the older failed call used a different handwritten schedule and logged
no plan identity, these controls cannot isolate the cause of that old mismatch.

[DERIVED execution] Run each frozen tuple exactly twice in fresh sequential
host processes. Set `RAYON_NUM_THREADS=1`; record runtime environment and public
plan metadata. Hash all read inputs and the binary immediately before and after
each invocation; require stable hashes and equal tuples across the pair.
Require both host exits to succeed, both actual plan observations to match the
declared fixed plan, all output bits Encrypted, and exact complete output-byte
equality. Keep all results, including any mismatch; stop at the first failure
without retry. Source/pin checks and post-run archival integrity checks are
permitted outside host execution and will be recorded separately.

[DERIVED output and privacy boundary] All new ciphertexts and logs go beneath
this directory. This run is public-only: no setup, issuer, reader, private audit,
secret-key read/hash, plaintext correctness comparison, old failed-output
decoding or decryption. Existing public keys/inputs are read-only. The source
interpreter still has the prior all-Encrypted output boundary and PEMA0001
bytes. Equal bytes establish only equality for each tested pair. They do not
establish plaintext correctness under this changed backend configuration.

[OPEN scope] A fixed algorithm choice removes this factory's timing-based plan
selection in the new build; it does not prove universal deterministic floating
point, serialization or crypto correctness, explain the prior failure, or
justify a general backend replay claim. The generic Rust/TFHE TCB, unrestricted
reader in the surrounding experiments, absent program authorization and all
prior privacy/security limitations remain. A long follow-on workload requires
new root coordination after these controls; it is not started automatically.
