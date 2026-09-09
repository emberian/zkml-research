# Shared seeded semantic learner with a durable model gate

[EXECUTED] The single shared `seeded001` run passed at 2026-09-08 22:37:29 UTC,
in **202.715739 seconds**. Its public phase completed at **163.940719 seconds**,
before any recipient query. A fresh dual-384-bit seeded setup, sixteen honest
recipient-local keys and the fixed semantic registry supported six actual
encrypted teachings, six committed class updates and both real oldest-input
expiries. No second setup or crypto run was performed by the transport builder.

[EXECUTED] Every accepted candidate matched a separate public recomputation of
`acc + fresh - old` over the actual ring. The byte comparison covered the entire
canonical output: **37,901,526 bytes** for each initial class state and
**37,901,597 bytes** for each later state. Candidate and verifier use the same
frozen arithmetic implementation. This is **complete deterministic verification,
not a succinct/compiler proof**.

[EXECUTED] A canonical first-residue change, with the candidate/model hashes
adjusted consistently, reached recomputation and was refused without changing
the head. The journal reopened in a fresh public process at revision four,
then accepted events five and six with exact FIFO expiries. A stale parent
refused; the original event-one request retried to its same receipt without
another transition. Both classes retained exactly two live observations.

[EXECUTED] After all public actor calls and source/setup checks completed,
`PUBLIC_COMPLETE.json` was saved. Sixteen separately sandboxed recipients then
received the exact accepted revision-six model under distinct request/delivery
IDs. All **32 scalar scores and 16 decisions** matched the already-public
semantic fixture. Exact delivery retry returned the same immutable receipt
with **zero new key invocations**; reusing the request with a changed delivery
ID refused. The head remained unchanged. The run retained 53 successful backend
calls, sixteen successful recipient-worker calls and the successful reopen
command. No public actor receipt reports private artifact access; the
orchestrator reads no private key payload.

[EXECUTED] The new public setup is retained directly:

| Artifact | Actual bytes | Content |
| --- | ---: | --- |
| [a.ring](results/seeded001/a.ring) | 798 | Canonical A seed/context descriptor; zero stored coefficient payload |
| [public.ring](results/seeded001/public.ring) | 9,471,117 | Both seed descriptors and sixteen explicit registered product rows |

[SOURCE] The sixteen-query general-B registry was fixed before A's honest
384-bit seed. The canonical registered-product commitment preceded the
independent honest 384-bit missing-row seed. The 561 missing public rows are
**seed-described**, reconstructed as needed; no corresponding private rows or
universal reader are generated. The full finalized descriptor has digest
`d5806f2a657377f3ebf9b4b92b9764363e4cde53b77bb7ff9797768ce27d624d`.
It is explicit in genesis and in every update and delivery request, together
with registry, recipient set, exact input/ciphertext bytes and the complete
accepted model root. Keys generated before finalization bind A, registry and
seed policy; ciphertexts also bind the finalized public file.

[SOURCE] `ring_service.py` commits only after full comparison and a second
current-parent check inside `BEGIN IMMEDIATE`. Durable receipt/head updates use
SQLite WAL/FULL and immutable fsynced content copies. `delivery.py` binds the
registered query, accepted head and files, holds the journal writer lock through
recipient execution, and retains immutable results indexed by both IDs. An
interrupted `running` delivery is refused rather than automatically invoked
again. This is a serialized local implementation, not a concurrent-load or
power-loss recovery experiment.

[SOURCE] The seeded setup claim is conditional in the builder's QROM model;
**SHAKE is the concrete heuristic**, not an unconditional ideal-uniform table
sampler or a measured Ring-LWE hardness guarantee. Exposed fixed keys still
work outside the journal on retained inputs and allowed combinations, giving
colluding recipients their per-input registered-query span. Continuity,
expiry and accepted-state delivery do not establish cryptographic history-bound
release. The known public vectors and expected outputs are reused without an
encoder/model rerun or new accuracy/privacy claim. Full boundaries are in
[SCOPE.md](SCOPE.md).

[SOURCE] The backend's [theorem application](../../../learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_semantic_successor/THEOREM_APPLICATION.md)
supplies the explicit public message-basis reduction, integer range, dual-seed
chronology and conditional QROM assumptions. Its frozen SHA-256 is
`d2761b8d1f075eeb8fc35aabc594a6e1e4918b84fcba6e6932fa0daa8032099f`.
That theorem application and this execution report describe the same single
shared run; neither is an additional setup experiment.

[EXECUTED] Command, issued once from the repository root:

```sh
research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/run_demo.py --run seeded001
```

[EXECUTED] Exact argv/output/exit records are in `results/seeded001/actors/`,
`deliveries/` and `reopen.json`. `accepted_updates.json`,
`changed_candidate_refusal.json`, `stale_and_retry.json`,
`delivery_retry_and_conflict.json`, `PUBLIC_COMPLETE.json` and `RESULT.json`
retain the outcome. The public packet totals **10,096,031 bytes**. Private
key payloads and large ciphertexts remain under ignored `runtime/`.
All twenty genesis source pins and the launch-pinned contract/demo matched
after execution. The frozen predecessor/companion sources were not edited.
The additive source changes are retained in `successor.patch`.

| Artifact | SHA-256 |
| --- | --- |
| `ring_service.py` | `2883ce0409a9b3cd091ced974de778f71f01431728ea7b78d1b4f2fa53b6e2cb` |
| `delivery.py` | `c9035be4831ac629350421fc97ff78f386e74a4ba061dad374da7f7e711ca2ba` |
| `run_demo.py` | `d557c3928b1a6ad445fa3a40704167b2da6fc926a2cdf339bef9ed397f7ba980` |
| `TRANSPORT.json` | `b4d2d3c29198d494569ceeaaf83137e4b2824f036378160807ece3223dec157d` |
| `results/seeded001/RESULT.json` | `b0945855f9f42dfb2a8c1f959fafcc6a4c81204b409f2cc6ed3c0a017ba8b0e8` |
| `results/seeded001/PUBLIC_COMPLETE.json` | `f98b17b208e3ccea5c4475ce169f2114e57c5b83fe064a12a116a1d46cc955d9` |
| `results/seeded001/public.ring` | `d805d4ed5dc77a7521494aa1d98471c043fe03ac93e4c09662ff0b52f95be1e2` |
| `results/seeded001/a.ring` | `e66665b047d7ed67fc9bf0f961a3d0ec7a5895dd63ecb1626cdb3efa48fdf512` |
