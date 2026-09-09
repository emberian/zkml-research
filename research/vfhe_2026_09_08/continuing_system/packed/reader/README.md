# Signed class-sum reader

[SOURCE] `native/src/main.rs:69` implements one reader-only command for a bank
of eight class sums. It derives from `../../linear/native/src/main.rs:391`,
`read_dot`; its source and binary identities are in `SOURCE.json`. This is a
separate executable and profile. The existing linear proof producer, verifier,
caller, profile, and executable are not edited by this package.

[EXECUTED] The one-job offline release build succeeded; `native/build.stderr`
retains the compiler output and `SOURCE.json` retains the command. The pinned
wrapper passed its five operational identities. The three pre-decryption
refusals and the original linear profile's 18 unchanged identities are retained
with commands and stdout/stderr in `CHECKS.json`. This package's checks performed
no key generation, private read, or proof run. End-to-end reading belongs to the
coordinated packed learner lifecycle.

## Call contract

[SOURCE] `caller.py` checks `PROFILE.json` before invoking the native executable.
From this directory, use:

```sh
python3 caller.py config
python3 caller.py read ISSUER DOT_CT DOT_SHA256 EVALKEY_SHA256 '[8,3,1,0,0,0,0,0]'
```

[SOURCE] The equivalent native invocation is:

```sh
native/target/release/vfhe-packed-class-reader read \
  ISSUER DOT_CT DOT_SHA256 EVALKEY_SHA256 '[8,3,1,0,0,0,0,0]'
```

[SOURCE] `COUNTS_JSON` is a literal JSON array argument, not a filename. It must
contain exactly eight integers, each in `0..8` (`counts_argument`,
`native/src/main.rs:60`). The two expected digests must be lowercase SHA-256
strings. `ISSUER/evaluation.key` must match the expected evaluation-key bytes,
and `DOT_CT` must match the expected ciphertext bytes. The ciphertext must be
the canonical two-component, level-zero NTT ciphertext in the fixed BFV
parameter profile. Those checks run before opening
`ISSUER/.private/reader.key` (`native/src/main.rs:76`).

[SOURCE] On success the command prints exactly one JSON object to stdout and
exits zero. A failure exits nonzero without a successful JSON output. The
success object has the following fields (`native/src/main.rs:139`):

| Field | Meaning |
|---|---|
| `schema` | `packed-class-sum-reader-v1` |
| `class_sums` | Eight centered signed integer class sums, in lane order |
| `sum_values` | Exact alias of `class_sums` for the packed controller |
| `signed_sum` | Integer sum of all eight class sums |
| `counts` | The exact eight accepted-count arguments |
| `per_class_signed_bounds` | Eight bounds, each `20,000 × counts[lane]` |
| `signed_bound` | Maximum allowed class-sum magnitude, `160,000` |
| `all8192_slots_repeat8` | `true`, only after checking every decoded slot |
| `zero_empty_lanes` | `true`, only after every zero-count lane equals zero |
| `dot_ciphertext_sha256` | The checked expected ciphertext digest |
| `evaluation_key_sha256` | The checked expected evaluation-key digest |
| `full_reader_key` | `true` |
| `scope` | Explicit full-reader and caller-acceptance boundary |

[SOURCE] The decoder checks that all 8,192 SIMD residues are canonical and
repeat their first eight values. It centers residues modulo
`t = 4,294,475,777`, then refuses any lane whose magnitude exceeds its own
count-dependent bound (`native/src/main.rs:105`). In particular, a zero-count
lane must decode to exactly zero. The profile's degree, plaintext modulus,
four ciphertext moduli, and variance come from the existing linear reader's
`params`; the new `params` is at `native/src/main.rs:40`.

[DERIVED] For bounded exemplar vectors and query vector with squared norms
at most 20,000, Cauchy–Schwarz bounds each signed exemplar/query dot product
by 20,000. A lane containing the sum of `c` exemplars therefore has signed dot
magnitude at most `c × 20,000`, by the triangle inequality. At capacity eight,
this is 160,000. A caller obtains a nonempty class's mean signed score as the
exact rational `class_sums[lane] / counts[lane]`; `signed_sum` is not a class
mean or a class label.

## Acceptance boundary

[OPEN] The reader accepts caller-supplied counts; it does not prove their
relationship to a journal, fresh examples, FIFO expiry, bounded initialization,
or an accepted model. The packed controller must provide the counts from its
accepted state and independently verify every requested bank before invoking
any private read. The reader neither verifies proofs nor accepts a producer's
self-verification JSON. Its wrapper pins executable bytes and does not supply
a cryptographic release gate.

[OPEN] `ISSUER/.private/reader.key` remains a full BFV reader key. Matching the
evaluation-key digest binds the caller-selected public file; this command does
not prove a relation between that public key and the private reader key. BFV
decryption correctness, the native parser and NTT maps, proper initialization,
and the caller's ordering remain external assumptions. No new proof of those
boundaries or of the assembled system's security is claimed here.

## Build and retained checks

[EXECUTED] The initial target was an APFS copy-on-write clone of the existing
linear target, and only the separate clone was used for this build. The lockfile
was copied from the linear package and pruned to the reader dependency closure
with the command recorded in `SOURCE.json` and output in `native/lock.stderr`.
From the repository root, the built command was:

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 \
  CARGO_TARGET_DIR="$PWD/research/vfhe_2026_09_08/continuing_system/packed/reader/native/target" \
  /Users/ember/.cargo/bin/cargo build --release --offline --locked \
  --manifest-path research/vfhe_2026_09_08/continuing_system/packed/reader/native/Cargo.toml
python3 research/vfhe_2026_09_08/continuing_system/packed/reader/checks/check_arguments.py
```

[OPEN] The manifest uses a retained absolute vendor path and local Cargo cache.
It is a current-workspace build recipe. A rebuild must match the accepted
profile; changing pins is a separate profile change for the caller to review.
