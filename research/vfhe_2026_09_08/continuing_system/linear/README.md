# Optional complete linear score backend

[DERIVED] This mode returns the eight **signed dot products** from the same packed
encrypted model and bounded public query used by the quadratic learner. It computes
the initial ciphertext/plaintext product and ten rotation/addition stages, proves
all 88 corrected MAC chunks, and independently verifies all 88 before the optional
reader runs. It never computes a ciphertext square, basis extension, tensor
product, or rescale. This is a different scoring rule: a caller can divide
`sum_dot` by its trusted active-example count to obtain the mean dot score.

[EXECUTED] The native executable builds offline, and the profile passes its 18
operational byte pins. `SOURCE.json` records the source and binary identities and
the ten functions that remain byte-identical to the quadratic MAC runtime,
including public-row reconstruction, statement construction, proving and verifying.
No proof production, verification or private read has yet been run in this mode.
The next coordinated run will consume one complete class; the existing quadratic
lifecycle and its profiles are unchanged.

## Caller interface

Run `caller.py` as a separate Python process; it deliberately isolates the frozen
pipeline's module globals and signal handlers from a server. All arguments are
caller-selected paths. Every output directory must be new. No command selects a
saved case, model, query, proof, key or workload from configuration.

```sh
python3 caller.py config
python3 caller.py produce-linear MODEL_CT QUERY_JSON EVALUATION_KEY NEW_PRODUCED
python3 caller.py verify-linear EXPECTED_JSON PRODUCED NEW_VERIFY
python3 caller.py receive-linear ISSUER EXPECTED_JSON PRODUCED NEW_RECEIVE
```

Each command writes `NEW_OUTPUT/result.json`. `produce-linear` accepts the same
canonical two-component level-zero BFV ciphertext and public evaluation key as
the quadratic backend. The query is a JSON array of 576 integers, each in
`[-32,32]`, with squared norm at most 20,000. It computes the dot ciphertext itself;
it does not require the old quadratic crypto capture. It produces 88 fresh proofs,
their public cases and optional compressed witness transport under this directory's
ignored `work/` folder.

`EXPECTED_JSON` must contain these three lowercase SHA-256 values:

```json
{
  "model_ciphertext_sha256": "<caller-approved model bytes>",
  "query_sha256": "<caller-approved query bytes>",
  "evaluation_key_sha256": "<caller-approved evaluation-key bytes>"
}
```

The caller may additionally pin `dot_ciphertext_sha256`. Extra fields are refused.
The fixed linear-plan digest comes from `PIPELINE.json`. `verify-linear` reconstructs
the public rows from the canonical model, query, evaluation key and all eleven
trace ciphertexts; producer-exported public rows and self-verification reports
are not acceptance evidence. Its result includes `complete_linear_verified`,
the five-field binding, the bound dot path, and all 88 native verification records.
It reads no private file and proves nothing new.

`receive-linear` first performs those 88 independent checks, then decrypts the
digest-matched dot once using `ISSUER/.private/reader.key`. It checks that all 8,192
SIMD slots repeat the same eight values, centers them modulo `t = 4294475777`,
and refuses any value outside `[-20000,20000]`. The result contains `dot_values`
and their exact integer `sum_dot`. Empty packed lanes should decode to zero.
The active-example count is supplied by the continuing learner's accepted queue;
this backend does not infer that count from ciphertexts.

## Reuse an explicitly supplied quadratic MAC prefix

```sh
python3 caller.py reuse-linear MODEL_CT QUERY_JSON EVALUATION_KEY QUADRATIC_PRODUCED NEW_BUNDLE
python3 caller.py receive-linear ISSUER EXPECTED_JSON NEW_BUNDLE NEW_RECEIVE
```

[DERIVED] The quadratic producer already emits the identical 88 MAC statements in
`QUADRATIC_PRODUCED/infer_case` and `QUADRATIC_PRODUCED/infer`. This command records
references and hashes to those exact caller-supplied objects; it does not copy,
regenerate or accept them. The subsequent verifier must consume all 88 under the
new linear native consumer. The old case's additional kernel digest is projected
away only when checking case metadata; every new native record must bind exactly
the model, query, evaluation key, linear plan and dot. This reuse preserves the
proved dot computation and makes no claim that a new proof was produced.

The bundle retains absolute references, so keep the source case and proof files.
Deleting or changing them makes subsequent verification fail. A fresh producer
instead places its case and proofs inside its own output directory.

## What the source theorem covers

[SOURCE] `nonlinear_performance/formal/Compiler/RangeKeyswitchInfer.lean:41`,
`Minidregg.Compiler.RangeKeyswitchInfer.dotSound`, proves
`trace 10 = inferDot op key model query` from `Initial` and all ten `Rotation`
relations. It is the existing theorem used before the quadratic square premises.
Its checked source MAC relations and all-row compiler templates are reused here;
there is no second evaluator theorem or handwritten Rust AIR.

[OPEN] Native deserialization, canonical residue lifting, public NTT transforms,
seed expansion, the emitted linear plan, controller ordering, and the native proof
backend/PCS remain the same explicit boundaries. The Lean theorem is conditional
on the accepted arithmetic relations; this package does not prove the complete
native proof parser correct or supply a new end-to-end numerical soundness bound.

[OPEN] BFV decryption correctness and bounded model initialization remain external.
For correctly packed bounded exemplar and query vectors, Cauchy–Schwarz gives
each signed dot magnitude at most 20,000; the reader checks the resulting bound
but does not prove that a malicious model was initialized that way. Its secret
key is a full reader capability. Software ordering of verification before reading
does not turn the receipt JSON or the native `read` command into a cryptographic
release gate. Linear scores also reveal signs that squared scores do not.

## Cost mechanism and build

[DERIVED from executed retained costs] The completed predecessor's MAC prefix
contains 64,418,707 proof bytes, versus 117,812,579 bytes for its whole class.
The corresponding recorded proving times are 164.104 seconds for MAC and 407.962
seconds for the composed class; peak MAC proving memory is 915,111,936 bytes versus
6,604,324,864 bytes for the class. These are the retained phase costs in
`nonlinear_performance_successor/runtime/run001/RESULT.json`, **not a new linear
benchmark**. Dropping the other stages supplies the expected cost mechanism;
actual caller-selected linear performance remains to be measured.

The native build command and terminal logs are in `SOURCE.json` and `native/`.
From the repository root the exact current-workspace build is:

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 \
  CARGO_TARGET_DIR="$PWD/research/vfhe_2026_09_08/continuing_system/linear/native/target" \
  /Users/ember/.cargo/bin/cargo build --release --offline --locked \
  --manifest-path research/vfhe_2026_09_08/continuing_system/linear/native/Cargo.toml
python3 research/vfhe_2026_09_08/continuing_system/linear/caller.py config
```

This uses retained absolute Cargo dependencies, templates, plans, the BigInt
witness executable and the local Cargo cache. It is a working-tree build, not a
portable fresh-clone recipe. A rebuilt executable must match the approved profile;
do not rewrite pins merely to make a different build pass. The main app continues
to use its quadratic backend; integrating this optional scoring rule into its
durable policy is a separate caller decision.
