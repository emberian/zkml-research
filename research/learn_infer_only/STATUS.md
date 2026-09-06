# Learn/infer-only resident — continuation tranche complete

[EXECUTED, 2026-09-06] The remaining work from the companion was taken through an
executable/formal tranche. All artifacts are local research; no companion source
was edited and no private resident was created or modified.

- [EXECUTED] §6C: ideal-primitive writer recovery ran on 64 synthetic histories /
  288 values, with credential/setup/prefix controls and a same-index substitution
  counterexample. `experiments/results/writer_recovery.json`.
- [EXECUTED] §6D: restored-manifest/current-head model ran with authority rollback,
  quorum compromise, local fork and atomicity falsifiers. Proposed Lean adapter
  composes the real finality checker and durable consumption objects.
- [EXECUTED] §6E, partial: two checked Lean modules extend the existing full-word
  Stage-0 receipt with context and canonical transcript encoding, connect that
  context to finality, and force public addition under the descriptor premise.
  31 exact-output axiom pins; accepted nontrivial witness and refusal teeth.
- [EXECUTED] The unchanged seed audit passes. Final module checks are
  `lean_ResidentReleaseContext_12.json` and `lean_ResidentRestoreFinality_07.json`.
  Staged Assurance umbrella, import-boundary script, `git apply --check`, and
  both CSV schemas pass in `experiments/results/patch_review.json`.

[DERIVED decision] Route 3 remains the strongest integrity/continuity continuation.
The resulting witness is public addition with deterministic randomness. It does
not establish hidden state, private observation ingress, secret fresh development
entropy, authenticated recipient encryption, full DataIntent/preflight integration,
adaptive multi-context security or a post-quantum resident composition. No candidate
audited in this tranche satisfies the combined A/B credential-exposure target.

[DERIVED review entry points] Read [DECISION.md](DECISION.md) for the outcome and
scope corrections, [SECURITY_GAME.md](SECURITY_GAME.md) for the experiments,
[CREDENTIALS.csv](CREDENTIALS.csv) for the union-of-role audit, and
[formal/README.md](formal/README.md) for theorem boundaries/reproduction. The
[minidregg patch](formal/minidregg-resident-release.patch) includes root imports
and is ready for maintainer review; it has not been applied.

[OPEN] Three decisive follow-ons are in [NEXT.md](NEXT.md). No background work or
delegated lane is continuing after this handback. VERDICTS remains unchanged;
proposed wording corrections are in DECISION/CANDIDATES for maintainer folding.
