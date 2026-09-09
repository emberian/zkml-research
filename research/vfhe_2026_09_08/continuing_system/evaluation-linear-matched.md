# Continuing issue router: linear / matched

[DERIVED from executed E5 vectors] The corpus, vectors, teaching order, FIFO capacity and query texts are the frozen baseline workload. Signed dot lanes are computed directly from those coordinates. There is no re-encoding or held-out tuning.

| Checkpoint | Signed linear mean | Frozen initial linear model | Squared comparator | Majority |
|---|---:|---:|---:|---:|
| initial | 20/20 | 20/20 | 20/20 | 10/20 |
| after_teaching | 19/20 | 20/20 | 19/20 | 10/20 |
| after_expiry | 18/20 | 20/20 | 18/20 | 10/20 |

Frozen vectors SHA256 `a373ff5e67ed16bb94010e770a1de320072655aaea7a22f46c1a7141b3df4aed`; baseline reference SHA256 `50d9d39cc68190348d8da0b16432b3a3d8ac057c5ed7b4dcb462d8540521c138`; signed reference SHA256 `87dd7c6c5e60cdd04333b25626bc884395fb286f9fa11e52afd25ffa27a6350a`.

[DERIVED] These are outcomes on a fixed author-written issue set. The comparison does not establish an accuracy improvement or general task performance.

[EXECUTED] 17/17 operations completed. Results and process records: `/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/continuing_system/runtime/matched-lifecycle/resident.workload`.

Recorded worker-attempt wall seconds: `638.0213993747602`.
Actual cumulative unique-request metrics: `{"accepted_fresh_proofs": 3200, "answered_queries": 4, "committed_updates": 12, "discarded_phase_attempts": 0, "private_reads": 8, "proof_bytes": 583046239, "proofs_generated": 3200, "proofs_verified": 3200}`.
Metrics available for every completed crypto operation: `True`.

- `query_initial`: revision 4, prediction `proof_integrity`; 16 signed lane values, sums, counts, repeat8 and exact ranking matched.
- `query_later`: revision 10, prediction `proof_integrity`; 16 signed lane values, sums, counts, repeat8 and exact ranking matched.
- `query_expiry`: revision 12, prediction `proof_integrity`; 16 signed lane values, sums, counts, repeat8 and exact ranking matched.
- `query_restart`: revision 12, prediction `proof_integrity`; 16 signed lane values, sums, counts, repeat8 and exact ranking matched.

Metrics describe each unique stable request once across all invocations. Reused or resumed requests are not counted as fresh work in this invocation.

[DERIVED] This is a full-reader local application. Selecting linear scores or a different proof backend does not remove the reader credential.
