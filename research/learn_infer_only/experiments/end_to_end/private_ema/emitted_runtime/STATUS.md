# Emitted Boolean schedule runtime

[EXECUTED complete] New generic Rust interpreter built and all eight parser/
execution/byte-boundary tests passed. The exact emitted schedules matched
25,600 Learn and 49,152 Infer public integer-oracle rows. The frozen two-Learn,
two-Infer encrypted smoke finished successfully at 2026-09-08 04:27:52 UTC:
all four complete-byte replay pairs and both private state/sign audits passed.
No additional crypto operation or retry was performed. Preceding private_ema
and encrypted_successor sources, binaries and runtime keys remain read-only.

[SOURCE interface] `formal/private_address_ema/emitted_schedule/SCHEMA.md` is the
formal bridge's frozen descriptor contract. The interpreter accepts only typed
XOR/AND references, validates initialized wires with CSE holes, and adapts the
existing PEMA0001 bit envelopes to the schedule's input/output dimensions.

[DERIVED scope] Rust decoding, loop semantics, TFHE gate correctness/noise and
serialization remain a source-audited trusted computing base. The independent
formal bridge owns emission and its theorem. This is research evidence, not a
shipped system or universal end-to-end proof.

[EXECUTED evidence] `REPORT.md`, `SOURCE_AUDIT.md`, `summary.json`, `costs.csv`,
`reports/plain/`, and `reports/smoke/` retain the result and its limits.
`freeze.json` has SHA256
`b45a38b01838b9b44bf8f8bcdd67c7e908bec0850b0f627d051d3a5e75785b3b`.
Sources, lock, logs, build pins and the exact runtime binary hash are retained.

[EXECUTED discrepancy] Prerequisite public evaluations/replays/hash checks
preceded private audit; the frozen driver also performed a final read-only
integrity recheck afterward, broader than the contract's literal all-checks-first
wording. It is recorded without altering frozen artifacts or rerunning.

[REPORTED separate root context] The older handwritten-runtime long utility
run stopped at a later replay mismatch. This small emitted sample does not
supersede that failure or establish universal replay determinism.

[OPEN handoff] Root owns integration and named-file commits. This lane made
no commits and touched only this directory. See NEXT.md for remaining seams.
