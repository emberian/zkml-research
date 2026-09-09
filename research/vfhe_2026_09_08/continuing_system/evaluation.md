# Continuing issue router: lifecycle evaluation

[EXECUTED: plaintext preparation] The fixed public corpus contains 12 teaching texts and 20 held-out issue texts. All texts were fixed before encoding. The existing local E5 helper encoded them without class labels; no held-out tuning followed.

| Checkpoint | Kernel mean | Current linear mean | Frozen initial model | Majority |
|---|---:|---:|---:|---:|
| initial | 20/20 | 20/20 | 20/20 | 10/20 |
| after_teaching | 19/20 | 19/20 | 20/20 | 10/20 |
| after_expiry | 18/20 | 18/20 | 20/20 | 10/20 |

[DERIVED] Additional teaching and FIFO expiry do not improve accuracy on this fixed set. The nonlinear and linear comparators agree in aggregate. This remains a narrow author-written issue-routing workload, not a benchmark accuracy claim.

[EXECUTED] Encoder statistics: `{"cached_texts": 0, "clipped_coordinates": 0, "encoded_texts": 32, "forward_batches": 2, "forward_seconds": 0.253793501004111, "model_load_seconds": 0.13276116701308638, "numpy": "2.4.2", "torch": "2.10.0", "transformers": "4.57.3"}`.
Preparation elapsed: 3.315168 seconds. The plaintext reference retains per-example predictions and every expected kernel lane.

Prepared artifacts: `/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/continuing_system/prepared`. Corpus SHA256 `cc5bbe33245ac48b7cbc63b5499afba30957a71bb2b86882b427f408ec03eed2`; vectors SHA256 `a373ff5e67ed16bb94010e770a1de320072655aaea7a22f46c1a7141b3df4aed`; reference SHA256 `50d9d39cc68190348d8da0b16432b3a3d8ac057c5ed7b4dcb462d8540521c138`.

[EXECUTED: partial lifecycle] 4/17 operations completed against `/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/continuing_system/runtime/lifecycle/resident`. Full result and attempt logs: `/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/continuing_system/runtime/lifecycle/resident.workload`. Recorded worker-attempt wall time: 94.449410 seconds.


Cumulative metrics for unique stable requests: `{"answered_queries": 0, "committed_updates": 4, "private_reads": 0, "proof_bytes": 23178225, "proofs_generated": 32, "proofs_verified": 32}`.
Metrics available for every completed crypto operation: `True`.
Current invocation reused 0 completed operations and resumed 0 incomplete operation records. These are not claimed as fresh proofs.

[DERIVED] The checked interface retains a full BFV reader. Public texts and features supply the reference; exact agreement establishes execution of this workload, not operator-private state or cryptographically restricted decryption.
