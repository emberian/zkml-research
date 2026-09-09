# Seeded semantic ring journal

[EXECUTED] The sole shared `seeded001` run passed in **202.72 seconds**: six
accepted teachings, two expiries, complete candidate recomputation, reopen and
refusals, followed by sixteen identified recipients reading accepted revision
six. Its public A descriptor is 798 bytes and issuer bundle is 9,471,117 bytes.
[Report](REPORT.md), [result](results/seeded001/RESULT.json).

[SOURCE] This successor joins the selected 384-bit seeded semantic transport,
complete public update recomputation, a durable current-parent model journal and
explicit recipient delivery IDs. It preserves the completed ideal-uniform ring
service and its delivery extension. The exact selected backend and source hashes
are in `TRANSPORT.json`.

[SOURCE interface] From the repository root, the complete six-teach/two-expiry
fixture runs in a new isolated instance with:

```sh
research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/run_demo.py --run NEWID
```

[SOURCE interface] `ring_service.py` exposes `init`, `head`, `audit`, `prepare`,
`submit` and `publish`, each with `--root ABSOLUTE_INSTANCE`. `init` selects the
fixed general-B registry and makes one fresh setup with sixteen recipient-local
keys. `prepare --class LABEL --input VECTOR_JSON --input-id ID --request-id ID`
creates a fresh encryption/candidate and returns its bundle without committing.
Inputs are the registry's 577-component canonical residue vectors. `submit
--bundle PATH` recomputes the entire candidate and commits only its current
parent. An exact accepted request retry returns its old receipt. `audit`
reconstructs the receipt/head chain and checks retained byte hashes without
rerunning ring arithmetic. `publish` exposes the current populated class heads.

[SOURCE interface] Recipient delivery uses explicit IDs:

```sh
RING_PY=research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python
RING_DELIVERY=research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/delivery.py
RING_MODEL=/absolute/seeded-instance

"$RING_PY" -B "$RING_DELIVERY" request --root "$RING_MODEL" --coordinate 0 \
  --request-id query-six --delivery-id delivery-six \
  --models "$RING_MODEL/public/accepted_model_000006.json" > delivery-request.json

"$RING_PY" -B "$RING_DELIVERY" deliver --root "$RING_MODEL" \
  --request delivery-request.json
```

[SOURCE interface] The request binds genesis, complete seeded setup descriptor,
registry/query/registration, current global revision/head and exact accepted
class files. Delivery holds the journal write lock while the registered
recipient runs under its own sandbox. New request/delivery ID pairs can name
later accepted publications; an exact retained retry returns the immutable
receipt without invoking the key. Reusing either ID with changed bindings
refuses. An interrupted `running` attempt is not automatically executed again.
The `worker` entry point is internal and must not be invoked bare: the delivery
launcher supplies its sandbox. `init` writes the local credential-root metadata;
it does not copy private keys into the delivery ledger.

[SOURCE scope] Two independent 384-bit seeds describe A and the missing public
rows, with fixed registry and registered-product commitments in the declared
order. SHAKE is the concrete heuristic instantiation of the builder's
conditional QROM argument. Every candidate is checked by full deterministic
ring recomputation, not a succinct/compiler proof. Each key exposes its fixed
query on retained inputs outside the journal; this is not cryptographic
history-bound release. See [SCOPE.md](SCOPE.md).
