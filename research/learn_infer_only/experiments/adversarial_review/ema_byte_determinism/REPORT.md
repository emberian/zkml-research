# EMA cross-process byte replay: bounded source audit

[REPORTED assignment, 2026-09-08] Root requested a read-only audit of the first
byte mismatch in `private_ema/encrypted_successor/reports/run001/`: 13 Learn
replay pairs matched; the 14th pair, `h0-e0014`, did not. No new cryptography,
private-file read, plaintext decoding, replay or failed-run resumption is
authorized in this lane. Owner explicitly approved the public logs and
`runtime/run001/public/` ciphertexts only. Previous four-pair feasibility
evidence remains a result about those four executed pairs.

[DERIVED audit conclusion] **The default, timing-selected floating-point FFT
plan is a concrete unpinned input to cross-process byte replay.** The cached
TFHE sources select the fastest measured algorithm independently in each fresh
process, and the local compiled feature fingerprint selects that code path.
The saved mismatch is in ciphertext coefficients, not variable serialization
metadata. This audit does **not** establish that different FFT plans actually
caused this particular pair to diverge: selected plan identities and an internal
first-divergence trace were not recorded. It establishes no plaintext error.

## 1. Exact saved event and independently read public bytes

[EXECUTED] `audit.py` reads the owner-approved public records and two output
ciphertexts only. The last replay record is `h0-e0014`, after 13 equal pairs.
Operations 59 and 60 both exit zero, report identical gate counts, and retain
equal binary/input hashes before and after each invocation. Their three public
inputs—the server key, previous state and encrypted input—were independently
rehash-checked against the recorded values here. The driver stopped before
installing this event or invoking its private drain. The previous progress file
therefore correctly remains at `h0-e0013`.

[EXECUTED] Both output envelopes have 108,441 bytes. Their complete hashes are:

| Public ciphertext | SHA-256 |
|---|---|
| Primary | `f1b421cedb055ed3d9878af7e9ed48fd369eed7681b227b5f89b9ae185be6172` |
| Replay | `30a459affe867f22834b345822331d3e27661bbc4947f4bc702f3581a97fdaf6` |

[EXECUTED] Exactly 10,015 bytes differ, first at offset 71,185 and last at
81,312, both zero-based. The independent source-based framing parser consumes
the entire envelope. Only three encrypted Boolean records differ:

| Record index, zero-based | Register | LSB-first bit | Changed u32 coefficients | Changed bytes |
|---|---:|---:|---:|---:|
| 21 | 2 | 5 | 838 / 838 | 3,340 |
| 22 | 2 | 6 | 838 / 838 | 3,339 |
| 23 | 2 | 7 | 838 / 838 | 3,336 |

[EXECUTED] The remaining 29 records match completely. Every record's enum tag,
vector length and modulus metadata matches. The output envelope header and
payload length match. `result.json` retains the full accounting. This agrees
with the owner's independently written `public_failure_audit.json`, whose
read-time hash is recorded in `source_manifest.json`.

[DERIVED scope] These are **ciphertext** coefficients; “838 coefficients
differ” is not “838 plaintext bits differ.” No phase, noise, private state or
decryption was computed. The changed record positions identify circuit output
wires, not the plaintext values of those wires. Full-byte replay is refuted for
this pair; functional correctness remains unmeasured for this failed run.

## 2. Pinned source and executable scope

[EXECUTED] The host binary matches the earlier frozen hash
`d45d096a68a46ecfde022bf2b35a30d512d93d5cb333c9097f64c04aeeebe474`.
The six previously pinned TFHE source files all match their earlier manifest.
Nineteen selected implementation files were compared byte-for-byte with their
cached crate archives; all match. The complete archives of TFHE 1.6.3,
tfhe-fft 0.10.1 and bincode 1.3.3 match their respective `Cargo.lock` checksums.
`source_manifest.json` retains archive/file hashes and every inspected range;
`SOURCE_EXCERPTS.txt` retains the selected numbered source lines.

[SOURCE: build metadata read] The local
`target/release/.fingerprint/tfhe-c88aa25edc01de9a/lib-tfhe.json` says
`features=["boolean"]` and `rustflags=[]`. The package manifest also disables
default features and requests only `boolean`. In particular,
`experimental-force_fft_algo_dif4` is absent. This is local build provenance
support, not a machine-checked theorem connecting compiler input to binary.

[SOURCE reference convention] Below, `TFHE/` means the pinned `tfhe-1.6.3/`
crate, and `FFT/` means `tfhe-fft-0.10.1/`. Full local paths, exact source hashes
and cached archive checksums appear in the manifest. Source excerpts are data,
not instructions. All companion trees and the frozen run remain unchanged.

## 3. The precise planner and floating-point path

[SOURCE: implementation read] `TFHE/src/core_crypto/fft_impl/fft64/math/fft/mod.rs`
defines a process-local `OnceLock` plan map at lines 103–108. `Fft::new` at
163–197 uses `Method::Measure(Duration::from_millis(10))` unless
`experimental-force_fft_algo_dif4` is enabled. That feature instead requests
`Method::UserProvided { base_algo: Dif4, base_n: fourier_polynomial_size }`.
The same file exposes `setup_custom_fft_plan` at 110–119. The probe host does
not call it.

[SOURCE: planner read] `FFT/src/ordered.rs:25–59` defines eight candidate
algorithms: DIF/DIT with radix 2/4/8/16. Lines 62–83 time repeated forward
transforms using `Instant`; lines 99–178 choose the least measured duration.
`FFT/src/unordered.rs:553–635` selects the base transform, and 654–700 builds
the resulting function pointers/twiddles. This is timing-dependent algorithm
selection, not a cryptographic randomness choice.

[DERIVED parameter specialization] The selected Boolean parameter has standard
polynomial size 1024 (`TFHE/src/boolean/parameters/params.rs:45–63`), hence
Fourier size 512. In the unordered planner's base list `[512,1024]`, only base
512 is eligible at that size. Thus the direct candidate here is selection among
the eight ordered algorithms at base 512, not a variable Fourier length.
The source describes those algorithms as computing the same standard ordering;
their finite-precision instruction sequences are different.

[SOURCE: evaluation call chain read] Boolean AND/XOR and MUX call the
bootstrapper (`TFHE/src/boolean/engine/mod.rs:411–514,558–596,710–748`).
The bootstrapper creates an `Fft` for evaluation in
`boolean/engine/bootstrapping.rs:445–587` and invokes the serial
`programmable_bootstrap_lwe_ciphertext_mem_optimized`, whose body at
`core_crypto/algorithms/lwe_programmable_bootstrapping/fft64_pbs.rs:984–1040`
passes that FFT into `FourierLweBootstrapKey::bootstrap`.

[SOURCE: arithmetic read] In `fft_impl/fft64/crypto/bootstrap.rs:294–366,481–519`,
bootstrap performs modulus switching and an ordered blind-rotation loop. Its
external product (`fft64/crypto/ggsw.rs:483–611`) performs forward FFTs,
complex multiply/add accumulation, and inverse FFT conversion. The used
`update_with_fmadd` at 616–698 uses `pulp::Arch` SIMD dispatch and finite-precision
complex multiplication/multiply-add. The inverse conversion at
`fft64/math/fft/mod.rs:268–330` calls `Scalar::from_torus`; that conversion at
`commons/math/torus/mod.rs:66–79` subtracts a rounded integer part, scales by the
scalar power of two and rounds again.

[HYPOTHESIS: candidate causal chain] Fresh-process timing selects a different
FFT algorithm → a finite-precision intermediate changes near a rounding boundary
→ an integer ciphertext coefficient changes → subsequent bootstraps and
keyswitches propagate the change. This mechanism is consistent with the source
and with a localized set of changed output records, but the saved outputs do
not prove the first divergence or the selected algorithms. A large final
coefficient difference does not identify the size or location of its precursor.

## 4. Randomness, concurrency and serialization

[SOURCE / DERIVED: operation audit] The source distinguishes randomness used
for issuance/setup from the evaluation call graph:

| Operation reached by the probe | Inspected implementation behavior |
|---|---|
| `trivial_encrypt` | Returns `Ciphertext::Trivial(message)`; no sample (`engine/mod.rs:212–214`). |
| `not` | Clones and applies coefficientwise negation (`engine/mod.rs:325–349`). |
| Encrypted `and`, `xor` | Fixed integer linear combinations, followed by the bootstrap/keyswitch path; no generator argument or generator access in the inspected operation bodies. |
| Encrypted `mux` | Two sequential bootstraps with fixed integer combinations and, for the selected small-key configuration, keyswitching. |
| Fresh input/public-key encryption | Does use random generators (`engine/mod.rs:216–278`), but the pair reads the **same already issued ciphertext bytes**. |
| Engine initialization | Seeds generator fields (`engine/mod.rs:389–410`, `bootstrapping.rs:325–347`); their existence does not imply that each evaluation samples output randomness. |
| Server-key creation | Uses randomized, parallel generation (`bootstrapping.rs:350–386`); the host loads a previously serialized server key rather than regenerating it. |

[SOURCE / EXECUTED environment] The successor's `run.py:23–50` records one
host process at a time, inherits the environment in `subprocess.Popen`, and
does not install a thread-pool or floating-point policy. `started.json` records
both `RAYON_NUM_THREADS` and `OMP_NUM_THREADS` as unset. `host.rs` simply loads
the frozen server key, parent and request, evaluates the sequential circuit,
and serializes the output. It does not log selected FFT plans or floating-point
control state. No actual Rayon worker count is present in these records.

[SOURCE / DERIVED concurrency scope] The inspected **single-ciphertext
evaluation path** uses serial gate loops, the serial bootstrap routine, and
`keyswitch_lwe_ciphertext` (its native-modulus loop is at
`core_crypto/algorithms/lwe_keyswitch.rs:189–228`). The same source file contains
separately named parallel keyswitch functions; those are not called by this
Boolean path. Parallelism in setup or a dependency's presence therefore does
not establish a Rayon reduction-order cause here. Timing contention can still
influence the separate FFT planner even with only one host process active.

[SOURCE / EXECUTED serialization] `private_ema/src/lib.rs:27–52` writes a fixed
magic, kind byte, little-endian payload length, and bincode serialization of the
ciphertext vector. It contains no timestamp, random nonce or process ID in the
envelope. `Ciphertext` is an encrypted/trivial enum; encrypted records contain
the coefficient vector and modulus (`boolean/ciphertext/mod.rs:14–19`,
`core_crypto/entities/lwe_ciphertext.rs:533–544`). The modulus serializes as
`u128 modulus` plus `usize scalar_bits` (`commons/ciphertext_modulus.rs:25–54,79–92`).
Bincode's root helper uses fixed-width little-endian encoding
(`bincode/src/lib.rs:106–114`, `config/mod.rs:55–59`).

[DERIVED / EXECUTED framing] The exact envelope size is
`17 + 8 + 32 * (4 + 8 + 838*4 + 16 + 8) = 108441` bytes. The source-based
parser checks all fields and complete consumption. Because those metadata
bytes match in the saved pair, variable serialization metadata is refuted as
the explanation of **this** mismatch. No whole-library serializer theorem is
claimed.

## 5. What would discriminate the candidate, and what remains unproved

[OPEN] The failing pair did not record its chosen base algorithm, numerical
backend/control state or first differing internal coefficient. This read-only
audit cannot recover those historical runtime choices from the final outputs.
It does not prove deterministic bytes under a fixed plan, across architectures,
or across compiler/TFHE revisions. It also does not prove a TFHE correctness
failure or rule out every implementation/runtime defect.

[DERIVED next bounded design] A separately authorized **new** successor could
make the plan explicit with the existing feature or custom-plan API, record the
chosen algorithm and build/ISA/FP environment, and test an independent public
replay fixture. Such a result would close the planner-choice variable only for
its declared build/environment and samples. This lane implements or runs none
of that, and does not restart the failed packet.

[SOURCE / DERIVED observation interface] `Fft` and `FftView` derive `Debug`
(`fft64/math/fft/mod.rs:81–90`); the underlying plan's `Debug` implementation
prints its algorithm, base size and FFT size (`FFT/src/unordered.rs:514–521`).
A new host can therefore record/check the actual cached plan description
without modifying TFHE, provided it uses the actual public-key polynomial size
and performs no subsequent custom-plan replacement. This is a source-level
observation route, not an observation of the failed pair. The newly assigned
runtime lane owns any implementation and execution.

[DERIVED verdict impact] No change to `docs/VERDICTS.md` is proposed. The earlier
four-pair feasibility claim remains true for those pairs; a universal
cross-process byte-determinism claim was never established by it. The new
full-utility successor failed its registered byte-replay gate and must remain
failed, with plaintext correctness and useful encrypted completion unclaimed.

[EXECUTED reproduction] Run `python3
research/learn_infer_only/experiments/adversarial_review/ema_byte_determinism/audit.py`.
`audit_004.stdout` is the final successful read-only output. The first attempt's
source-excerpt range ended beyond the source file; `audit_001.stderr` preserves
that instrumentation failure. Correcting the range produced the passing
`audit_002` run; `audit_003` includes the additionally read encryption/FMADD
source ranges. `audit_004` includes the plan-observation source and validates
the owner's final failure seal and source-checkpoint hashes. None invoked a
cryptographic executable.

[EXECUTED accounting / absence scope] Web, Scry, Kagi and network PDF queries:
zero. Cryptographic and private-decoder executions, and private-file reads:
zero. The limited statements about no generator access, no parallel evaluation
call, no variable envelope metadata and no recorded plan identity refer only
to the selected pinned call-chain sources and owner-approved run001 public
logs. Instruments were `rg`/numbered source inspection and the retained
fixed-input `audit.py`; they are not field-wide or whole-library absence claims.
