# Reproduction and proof boundary

[EXECUTED] From `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/integer_certificate_emission/check.py
python3 research/learn_infer_only/experiments/integer_certificate_emission/check.py LargeIntegerCertificateEmission
python3 research/learn_infer_only/experiments/integer_certificate_emission/check.py IntegerCertificateEmissionChecks
python3 research/learn_infer_only/experiments/integer_certificate_emission/check.py LargeIntegerCertificateEmissionChecks
python3 research/learn_infer_only/experiments/integer_certificate_emission/review.py
```

[EXECUTED] The successful final core module logs are
`compile_IntegerCertificateEmission_08.json` and
`compile_LargeIntegerCertificateEmission_05.json`; each contains the exact command,
working directory, LEAN_PATH, source SHA256, exit code and stdout/stderr.
The concrete checker logs are `compile_IntegerCertificateEmissionChecks_02.json`
and `compile_LargeIntegerCertificateEmissionChecks_04.json`.
Earlier failed/interrupted attempts remain alongside them.

[EXECUTED] `review_01.json` pins 20 theorem axiom reports and records the staged
Compiler umbrella check, import-boundary check and `git apply --check`, all exit 0.
It also records the exact companion source hashes inspected and patch hash. The
patch includes two new Compiler files plus their Compiler.lean root imports.
No patch was applied and no companion source was modified.

[DERIVED limit] This is an isolated overlay using already-built dependency oleans,
not a clean full `lake build Minidregg`. The helper refuses to write through a
companion symlink. The large compiled checks are positive evidence distinct from
the small module's kernel-proved negative signed inhabitant. Neither checker is
a cryptographic proof protocol or a private resident implementation.

[EXECUTED] `descriptor.json` and `checker_vectors.json` are emitted directly by the
Lean compiler/evaluator. `large_descriptor.json.gz` and
`large_shared_descriptor.json.gz` retain deterministic gzip copies of the two large
emissions. Decompress them for review; the commands regenerate uncompressed JSON
in the same experiments directory. `checker_results.json`, `large_results.json`
and `large_CSE_costs.json` retain checker verdicts and exact operation counts.
