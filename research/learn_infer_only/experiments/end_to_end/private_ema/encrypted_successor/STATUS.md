# Encrypted successor status

[REFUTED: this execution's complete-byte replay] The first run stopped at
`h0-e0014` after thirteen matching Learn replays. The fourteenth pair differs
despite identical read-input hashes and successful process exits. See `REPORT.md`
and `reports/run001/public_failure_audit.json`. No Infer evaluation or reader
decryption occurred. The workload is incomplete and must not be retried.

[EXECUTED] The separate public run started at 2026-09-08 04:12:26 UTC under
root's scheduling authorization. Freeze SHA-256:
`1a47a33cad3e0858a5b2437e3b5edc002cfe3a0fff0a496136b7587604332929`.
It consumes the unchanged 384 Learn/96 Infer fixture with all 480 byte replays,
one host process at a time and public read-input hashes before/after each call.

[EXECUTED] `failure.json` and the public failure audit supersede the last
progress snapshot: fourteen pairs were tested, thirteen were accepted. The
public-close condition was not reached, so verification/drain stages were
never dispatched. All frozen run source pins and partial bytes are preserved.

[DERIVED limits] Both routes are public; each contains four encrypted signed
bytes. The full client key survives. Data and prior utility estimates are
reused synthetic fixtures. The hard/wet subgroup regression is retained in
`CONTRACT.md`; the experiment establishes no utility improvement or fresh
validation estimate.
