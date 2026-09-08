# Durable restricted-ring semantic learner

[EXECUTED] `normal001` passed on 2026-09-08 at 18:20:51 UTC in **179.582 s**,
including **142.436 s before recipient queries**. A fresh ideal-uniform setup
and sixteen recipient-local registered keys served a durable two-class learner.
Six fresh encodings became six accepted revisions; events five and six expired
the actual oldest observations, leaving two live observations per class.
The classes were `card_arrival` and `cash_withdrawal_charge`.

[EXECUTED] Every accepted candidate matched a separate public actor's complete
canonical `acc + fresh - old` output byte-for-byte: 37,901,465 bytes for each
initial class state and 37,901,536 bytes for each subsequent state. This checks
all ring coefficients, scalar masks, context and lineage in the actual ring.
Both actors use the frozen backend arithmetic. This is **complete deterministic
verification, not a succinct/compiler proof** or independent arithmetic implementation.

[EXECUTED] A canonical candidate with its first residue changed, and its declared
file/model hashes adjusted accordingly, reached recomputation and was refused
with `complete_candidate_recomputation_mismatch`. The head remained unchanged.
A distinct stale-parent request refused; an exact historical retry returned the
original receipt without another transition. A fresh sandboxed process reopened
and checked the exact journal/head at revision four before both expiries.

[EXECUTED] After all public actor calls returned, source/setup pins were checked
and `PUBLIC_COMPLETE.json` was saved. Only then did sixteen separate recipient
processes read their own fixed keys and the exact accepted revision-six model.
All **32 scalar scores and 16 decisions** matched the frozen public fixture's
reference. These are known-fixture consistency checks, not a new accuracy study.
All 53 backend calls exited successfully: 21 public calls, 16 registrations and
16 recipient queries. Public actor receipts record no private artifact access;
the orchestrator reads no private payload. Each recipient's sandbox denies other
recipients' private directories and networking.

[SOURCE] `ring_service.py` binds source pins, setup, registry and recipient
registrations into genesis. Requests bind that genesis, current global parent,
selected class accumulator, exact input/fresh/expired/candidate hashes and the
resulting complete model root. Full verification precedes a second parent check
inside `BEGIN IMMEDIATE`; immutable content copies and the receipt/head are
installed with fsync and SQLite WAL/FULL. Publication exposes only accepted class
heads. The executed normal path is serialized; it is not a concurrent-service or
power-loss recovery experiment. Recipient delivery uses one retained transport
record per coordinate; repeated deliveries require an additive successor API.

[SOURCE] The unchanged general-B registry has sixteen fixed query rows and 561
completing public rows. The latter were generated directly uniformly without
their corresponding secrets. No universal reader was constructed. The service
checks accepted-state delivery, but exposed fixed keys remain usable outside it
on retained inputs and allowed combinations. A coalition obtains its per-input
registered-query span. Honest setup/registration/issuer sampling, the encoder,
codec and arithmetic, local journal and shared OS remain trusted boundaries.
This is not cryptographic history-bound release. See [SCOPE.md](SCOPE.md).

[EXECUTED] Command, issued once from the repository root:

```sh
research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/vfhe_2026_09_08/proved_journal/restricted_ring_successor/run_demo.py
```

[EXECUTED] Exact per-actor argv/stdout/stderr/exit records are in
`results/normal001/actors/`; recipient wrappers and the reopen command are retained
beside them. `accepted_updates.json`, `changed_candidate_refusal.json`,
`stale_and_retry.json`, `PUBLIC_COMPLETE.json`, and `RESULT.json` retain the checks.
The six fresh inputs are cached public vectors copied from the completed linear
fixture; no model forward, benchmark, tuning or old-key reuse was performed.
Large public ciphertexts/setup and private keys remain in ignored `runtime/`.
All 23 genesis source pins, plus the launch-pinned contract and demo, matched after
the run. Frozen predecessors and companions were not edited.

| Artifact | SHA-256 |
| --- | --- |
| `ring_service.py` | `0edb517d994efdf0bb96d474025c16e51d87886e50ad2ba9c4e06fb60566d23e` |
| `run_demo.py` | `46359fba29fe4afdc4a2dcd11e847b65214cab380d521b37d1e2167b60d33492` |
| `CONTRACT.md` | `f01b2c8aa7411e0b48675eef7d389951c8b3045d254fc3b3be9677455d45a999` |
| `results/normal001/RESULT.json` | `d6d46e6ea2fe73e260e1b4b117b0043cb2fa312a276dac1186ed94e39630a267` |
| `results/normal001/PUBLIC_COMPLETE.json` | `b2b7e16369f804d223e271cfc88e9fd325c71835d2d268097fbbb9b167fc667d` |
| `results/normal001/accepted_updates.json` | `553788d7d856a8e2349708d47e7cc131e602e0e01a0f77a91993589ac52b14a2` |

