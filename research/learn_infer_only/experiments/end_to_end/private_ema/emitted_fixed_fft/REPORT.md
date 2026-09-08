# Fixed-FFT public replay controls

[EXECUTED result] All five preregistered public replay pairs matched complete
serialized output bytes. All ten fresh host processes observed
`Plan { base_algo: Dif4, base_size: 512, fft_size: 512 }` at bootstrap polynomial
size 1024, and every before/after public input and executable hash matched.
Execution ended at 2026-09-08 04:48:49 UTC, exit 0. This is a fixed-build,
fixed-platform, observed-plan sample. It does not establish universal replay
determinism or identify the cause of the earlier mismatch.

[SOURCE configuration] The new build enables the exact TFHE 1.6.3 Cargo feature
`experimental-force_fft_algo_dif4` together with `boolean`, with default features
disabled. The initial phrase `fft64-default` was inaccurate shorthand and was
corrected before building. Cached source shows the feature selects a supplied
Dif4 plan at the Fourier size; the prior factory branch selects a plan by timing
candidate algorithms. `feature_source.txt` contains numbered excerpts;
`build_pins.json` records source hashes and equality with local crate archives.
This factory-level change is separate from any claim about complete floating-
point or serialized-ciphertext determinism.

[EXECUTED build and pins] Eight tests passed and the release build succeeded.
Cargo's actual compiler-artifact event confirms exactly the two requested TFHE
features. The generic evaluator and byte adapter (`src/lib.rs` and
`src/ciphertext.rs`) are byte-identical to the prior generic runtime; Cargo.lock
is also unchanged. `main_source.diff` records the small host diagnostic change;
`src/plan_observation.rs` contains its public-key-size/plan observation. No
hand-authored learner, MUX, address selector or sign circuit was introduced.
The exact emitted descriptors and schema are unchanged.

| Frozen artifact | SHA256 |
|---|---|
| This pre-execution freeze | `b6805534d4aa32d4ea99f7017d71a3a38738a8c60fc84370c471826cfa94077e` |
| Fixed-feature runtime binary | `6c0954fae626940e720c47bfb535347ecd3c3fc0b19b36d0834b70465b02d197` |
| Control input manifest | `f9ab059597d4b61989385fd1334895b2fce74ca24a65e7d766563079593476f0` |
| Same Learn descriptor | `94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8` |
| Same Infer descriptor | `b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c` |

[EXECUTED platform] Build commands recorded Rust 1.98.0-nightly
(`91fe22da8084a1c9e993d78d4a56f22ab8396236`), LLVM 22.1.7,
target aarch64-apple-darwin, Darwin 25.6.0 and Apple M2 Max.
`build_pins.json` retains actual command output and build environment flags.
The wrapper set `RAYON_NUM_THREADS=1`, ran one host process at a time and
recorded environment, process identifiers, timings and public plan observations.
Other root-coordinated work could overlap; these are contended sample costs.

[SOURCE observation path] The diagnostic moves the same public ServerKey
buffers through the library's public raw-parts API, obtains their polynomial
size, and observes the compact Plan Debug record from `Fft::new(size).as_view()`.
The source uses the same process-local cache as Boolean bootstrap operations.
It does not call the custom-plan setter, modify keys, or log key coefficients.
Every process must match the expected fixed plan before evaluation. The path,
cache assumption, public Debug formatting and remaining TCB are described in
`SOURCE_AUDIT.md`; source inspection and observed plan strings are distinct
evidence from a formal runtime theorem.

[EXECUTED controls] `prepare.py` fixed five static input tuples in `inputs.json`
before `freeze.py` pinned 36 public files. Four tuples are the exact two Learn
and two Infer inputs from the preceding successful emitted smoke. The fifth
uses exactly the older failed fourteenth Learn's public server key, parent
h0-e0013 and h0-e0014.input bytes from its public audit record. These use retained
parent ciphertexts, so they are independent fixed-case controls rather than a
new chained trajectory. Every pair passed:

| Case | Host processes | Complete-byte replay | Observed plans equal |
|---|---:|---|---|
| Prior emitted Learn 001 | 2 | yes | yes |
| Prior emitted Infer 001 | 2 | yes | yes |
| Prior emitted Learn 002 | 2 | yes | yes |
| Prior emitted Infer 002 | 2 | yes | yes |
| Old fourteenth Learn public inputs | 2 | yes | yes |

[EXECUTED public-only boundary] No setup, issuer, reader, private audit,
decryption, private-key read/hash, old failed-output file read or retry occurred.
The old failed outputs were neither decoded nor compared. All new outputs are
separate artifacts under `reports/controls/artifacts/`; host checks require
Encrypted variants. `reports/controls/results.json` keeps full commands,
before/after public hashes, public plan metadata, exit statuses and exact replay
comparisons. Corresponding stdout/stderr and resource reports are retained
alongside the ten public ciphertexts. No long workload was started.

[EXECUTED costs] `costs.csv` keeps every host process. Learn took
16.252–20.055 wall seconds (six processes), and Infer took 0.521–0.624 wall
seconds (four). Learn evaluation alone took 16.059–19.821 seconds, Infer
0.309–0.350 seconds. Maximum recorded RSS was 494,338,048 bytes for Learn and
484,638,720 bytes for Infer. Learn calls 342 XOR/196 AND gates; Infer calls six
XOR/three AND gates; both create two internal public constants. Counts are API
calls, not measured bootstraps. No speedup comparison is justified by these
contended runs.

[OPEN interpretation] The old failed workload used the handwritten circuit,
while this case uses the emitted one, and the old executions logged no selected
FFT plan. The new success therefore cannot establish what caused that failure.
The failure remains preserved. These controls also do not test plaintext
correctness under the changed FFT feature: no new outputs were decrypted.
Rust/serde execution, raw-parts handling, cache behavior, TFHE correctness/noise,
platform arithmetic and full ciphertext-byte determinism remain TCB/open seams.
The exact fixed factory selection is source-backed; general deterministic
evaluation is not proved. A later correctness/utility workload requires root's
separate coordination and a new contract/freeze.
