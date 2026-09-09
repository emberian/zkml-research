The completed class bundle is smaller and uses less peak prover memory, but is slower. [REPORT.md](REPORT.md) records the ten new extension/rescale proofs, 106 reused corrected proofs, complete fresh consumer and exact limits. Source modules and the applicable minidregg patch are in [formal/READY.json](formal/READY.json).

Use the caller-selected worker for continuing-system integration:

```sh
python3 research/vfhe_2026_09_08/nonlinear_performance_successor/runtime/caller.py produce-update PUBLIC_SOURCE NEW_PRODUCED
python3 research/vfhe_2026_09_08/nonlinear_performance_successor/runtime/caller.py verify-update EXPECTED_JSON PRODUCED NEW_VERIFY
python3 research/vfhe_2026_09_08/nonlinear_performance_successor/runtime/caller.py produce-infer MODEL_CT QUERY_CT EVALUATION_KEY PUBLIC_CAPTURE NEW_PRODUCED
python3 research/vfhe_2026_09_08/nonlinear_performance_successor/runtime/caller.py verify-infer EXPECTED_JSON PRODUCED NEW_VERIFY
```

Run each command in its own subprocess. Every output directory must be new, and its `result.json` is authoritative. Production emits progress lines to stdout. Update verification expects the complete caller-approved binding object. Infer verification expects exactly `model_ciphertext_sha256`, `query_sha256`, `evaluation_key_sha256`, and `kernel_ciphertext_sha256`. The public capture uses the existing square builder format, including `basic.dot.ct`, `basic-000.ct` and full square/rescale trace data. The update source uses the existing public accumulator/fresh/expired operand format.

The default profile is `runtime/caller/PIPELINE.json` (SHA256 `daf3baa054b5b979e77ab4d9d9366bc87bf4988e4c8f227579611b8d68947842`). `caller.py config` reads and checks it; a leading `--profile /absolute/directory/PIPELINE.json` selects another approved profile of the same schema. The profile directory receives ignored witness work. The profile fixes the existing N8192 BFV modulus/linear-plan/backend combination, while all input cases are caller-selected. It retains neither a fixture selector nor a private reader credential. This worker requires the pinned workspace binaries and is not a standalone distribution.

`runtime/run.py` is the separately preserved saved-class measurement driver; it is not the continuing-system entry point. No additional measurement or proof run is queued here.
