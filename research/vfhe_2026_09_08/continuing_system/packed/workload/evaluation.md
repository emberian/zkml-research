# Packed nine-class lifecycle workload

[EXECUTED: plaintext preparation] Eighteen public authored teaching texts and nine held-out texts were frozen before one E5 encoding pass. Labels were not encoder inputs. There was no held-out tuning.

| Checkpoint | Active classes / banks | Correct / 9 | Correct among active labels | Frozen first bank | Majority |
|---|---:|---:|---:|---:|---:|
| after_restart | 9 / 2 | 9/9 | 9/9 | 8/9 | 1/9 |
| before_expiry | 9 / 2 | 9/9 | 9/9 | 8/9 | 1/9 |
| one_bank | 8 / 1 | 8/9 | 8/8 | 8/9 | 1/9 |
| two_banks_after_expiry | 9 / 2 | 9/9 | 9/9 | 8/9 | 1/9 |

[DERIVED] The initial model has no network-transport teaching. Later teaching changes both class membership and the proof-integrity FIFO. These finite observations establish no general accuracy improvement. Reference class sums include exactly the last eight retained feature dots; the first two proof-integrity texts expire.

Corpus SHA256 `3a1c115a5a34fdd2b3ac3ca33f97d0553672b83675ddd567750d707499d1cac9`; vectors SHA256 `48cfe65173f8d51e864e3b5f0b22e180f81fb20d6954ead9cacdef4bdaf35f8e`; reference SHA256 `f66d5938d057b6a98c57e8104b1625c477076c53e439f30dfb9c5808fe3c5bc5`.

Encoder statistics: `{"cached_texts": 0, "clipped_coordinates": 0, "encoded_texts": 27, "forward_batches": 2, "forward_seconds": 0.5684908340335824, "model_load_seconds": 0.29222825000761077, "numpy": "2.4.2", "torch": "2.10.0", "transformers": "4.57.3"}`.
Preparation wall time: 7.032562 seconds.

[EXECUTED] 22/22 operations complete. Evidence: `/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/continuing_system/runtime/packed-lifecycle/resident.workload`. Worker-attempt wall seconds: 499.706403.

Actual unique-request metrics: `{"accepted_fresh_proofs": 2336, "answered_queries": 3, "classes_answered": 26, "committed_updates": 18, "discarded_phase_attempts": 0, "occupied_banks": 5, "private_reads": 5, "proof_bytes": 424195924, "proofs_generated": 2336, "proofs_verified": 2336}`.

- `query_one_bank`: revision 8, 1 active banks; all 8 signed class-sum lanes, counts, padding, repeat8 and exact ranking matched; prediction `proof_integrity`; worker PID 63032.
- `query_two_banks`: revision 18, 2 active banks; all 16 signed class-sum lanes, counts, padding, repeat8 and exact ranking matched; prediction `proof_integrity`; worker PID 65975.
- `query_restart`: revision 18, 2 active banks; all 16 signed class-sum lanes, counts, padding, repeat8 and exact ranking matched; prediction `proof_integrity`; worker PID 68373.

Actual metrics count each stable request once across invocations. Reused completed requests and resumed phases are not relabeled as new proofs.

[DERIVED] The application retains the full BFV reader. Exact class sums and bank-level proof gating demonstrate this workload, not absence of operator read authority.
