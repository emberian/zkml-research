# Reusable delivery IDs over the frozen restricted-ring service

[DERIVED] `delivery.py` is an additive adapter; the parent `ring_service.py`,
its completed evidence, and `runtime/normal001` remain unchanged. A request
binds both a request ID and a delivery ID to the registered coordinate/query,
genesis, registry, recipient set, accepted revision/head/model root, and exact
model-file path/hash. IDs are ASCII alphanumeric/underscore/hyphen strings of
length 1–80; the local ledger scopes uniqueness to the service instance.

[DERIVED] For a new ID pair, public metadata checks establish that the model
is the currently accepted populated head, including exact class hashes and
counts. The adapter holds the parent journal's `BEGIN IMMEDIATE` writer lock
through the recipient read and final retention. Cooperative `submit` and
checkpoint-import commits cannot advance the head during that interval. The
worker checks the same bindings before touching its own key, and the parent
checks the head again before retaining the result. This local writer-lock
protocol is not a distributed concurrency or administrator-resistance theorem.

[DERIVED] Each delivery has its own immutable request, validation record,
actor command/stdout/stderr/receipt, and final receipt files under
`INSTANCE/deliveries/DELIVERY_ID/`. The SQLite delivery ledger additionally
retains canonical request and receipt bytes/hashes. The same coordinate may
use new ID pairs at later accepted revisions without overwriting prior output.

[DERIVED retry semantics]

- The identical completed request returns the retained canonical receipt,
  even after the accepted head advances, and invokes no recipient actor.
  This is replay of an already delivered result, not a fresh stale-head read.
- Reusing either ID with any changed request binding refuses. A new pair
  referring to a noncurrent head also refuses before private execution.
- The ledger durably marks the attempt `running` before the private actor is
  launched. A process/actor/storage failure may leave that state. Retrying such
  an incomplete attempt refuses and never automatically invokes the key again.
  This provides explicit uncertainty after a crash, not an exactly-once
  physical decryption or complete power-loss-recovery guarantee.
  A crash before the ledger insertion can leave a reserved directory without
  a row; that also refuses automatic reuse (`fresh_delivery_directory`).
- Completed retries trust the locally retained ledger and receipt hash; they
  do not reopen old model files or keys. They still check the frozen service
  source/genesis/registry and registered request identity.

[SOURCE/DERIVED] `delivery_credentials.json` fixes the existing credential-root
path and its genesis. The caller launches the worker with that recipient's
original `recipient_XX.sb` profile. Only that worker reads its own key header;
the unchanged registered-query transport actor reads the same key's payload.
The orchestration code reads no private artifact. The worker deliberately
publishes the known-fixture scores as the predecessor does. These new files
are not confidential-output storage or an authenticated network endpoint.

[PREDECLARED demonstration] Import the already accepted public prefix through
revision 4 into an isolated checkpoint, copying public registry/registration
and required CAS bytes. Invoke existing recipient 0 once with IDs
`request-r4`/`delivery-r4`, then perform one exact retry. Import the previously
accepted public records 5 and 6 into this checkpoint, and invoke recipient 0
once with `request-r6`/`delivery-r6`. Retry the original revision-4 request
after head advancement, and check two ID conflicts and one new stale request.
Compare four known-public scores and two predictions to the saved fixture.
No new setup, key sampling, encryption, teaching, update recomputation, whole
workload replay, private-key copying or private payload inspection is included.

[SCOPE] The import authenticates no untrusted journal: it is a trusted local
checkpoint transfer from the already frozen accepted records, with exact
hash/parent/head checks. The final imported head must match the original
revision-6 head. The demo does not claim that fresh teachings occurred between
these two deliveries, or that their arithmetic was reverified in this lane.
Its ordering claim is per delivery: public validation precedes that delivery's
private read. Public checkpoint work intentionally occurs between the reads.

[SCOPE] The original fixed recipient key remains usable on every retained
issued input and permitted ciphertext combination. Delivery IDs, current-head
checks and local receipts do not make the key cryptographically history-bound
and do not change the fixed registered-query span or its hardness assumptions.
