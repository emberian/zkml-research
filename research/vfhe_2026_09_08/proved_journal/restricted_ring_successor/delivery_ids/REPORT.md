# Two accepted revisions, two retained deliveries, one recipient

[EXECUTED] `run_demo.py` completed with PASS in **5.662 seconds** using the
existing ring Python environment. It performed exactly two unchanged backend
recipient-query invocations, both with recipient 0's existing registered key.
No setup, key generation, encryption, teaching or update recomputation ran.
The exact command was:

```sh
/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B run_demo.py > demo.log 2> demo.stderr
```

| accepted revision | delivery ID | card-arrival score | cash-withdrawal score | prediction |
|---:|---|---:|---:|---|
|4|delivery-r4|447965|401795|card_arrival|
|6|delivery-r6|470157|402003|card_arrival|

[EXECUTED] All four scalar scores and both decisions matched the frozen public
fixture. Complete recipient-worker times were 2.231 and 2.143 seconds; the
unchanged transport calls accounted for 1.884 and 1.868 seconds. This is one
bounded demonstration on the shared host, not a latency distribution.

[EXECUTED] Both exact retries returned the identical canonical retained
revision-4 receipt and performed zero new recipient calls. One retry occurred
immediately; the other occurred after the accepted head advanced to revision6.
The result explicitly says `replayed` and retains the original revision4.
Reusing the request ID with a changed delivery ID, or the delivery ID with a
changed request ID, refused with `delivery_id_or_request_conflict`. A fresh
ID pair naming the old head refused with `delivery_not_current_head`.
Both original delivery directories and their final receipts remain present.

[EXECUTED] The one pure metadata interruption control in
`check_incomplete.py` installed a temporary `running` ledger row, then checked
that retry returns `delivery_incomplete_no_automatic_reexecution` without
starting any subprocess. It neither induced nor claimed a crashed crypto run.
`python3 -B check_incomplete.py > incomplete.log 2> incomplete.stderr` passed.

[EXECUTED ordering] Each delivery has `PUBLIC_VALIDATED.json`, written before
its worker starts. The launcher performs no private-artifact reads. Only the
sandboxed recipient worker opens its own key header, followed by the unchanged
transport actor reading the same key payload. Each transport receipt records
one own-key artifact read and zero private writes. The service writer lock
holds the accepted head fixed during this interval, and the head is rechecked
before receipt retention. Public checkpoint work happens between the two
deliveries; the claim is per-delivery ordering, not that all public work
preceded every private read in the complete history.

[EXECUTED preservation] `results/demo001/LAUNCH.json` pins the original service,
driver, retained accepted updates, final head, prior recipient-0 receipt,
genesis, registry and journal file, plus the executed extension sources. All
original pins matched after the demonstration. The checkpoint copied public
CAS and registration files; it did not copy a key or modify the original
`normal001` journal. The imported final head equals the original accepted
revision-6 head exactly.

[SCOPE] Prefix4 and accepted records5/6 were imported from the trusted frozen
local journal. Their hashes and parent/head structure were checked, but their
update arithmetic was not rerun here. This demonstrates repeated delivery
across accepted checkpoint advancement, not fresh learning between reads.
The utility data/results are already public. Local delivery IDs and receipts
do not prevent the exposed key from reading retained ciphertexts outside the
service and do not provide cryptographic history-bound release.

[SOURCE] Evidence: [RESULT.json](results/demo001/RESULT.json),
[retry after advancement](results/demo001/historical_retry4.json),
[refusals](results/demo001/refusals.json),
[interrupted-attempt control](results/INCOMPLETE_CONTROL.json), and the two
delivery directories under `results/demo001/`. Canonical receipt IDs hash the
canonical JSON body; the retained files additionally end with a newline.
