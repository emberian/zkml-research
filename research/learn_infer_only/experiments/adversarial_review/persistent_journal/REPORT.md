# Independent review of the persistent-journal fixture

[EXECUTED] Completed 2026-09-06. The retained run004 evidence and repaired
run005 evidence pass an independent census. A separate benign process test of
**concurrent retries after installation but before publication** passes on the
frozen run005 protocol. The client-exposed fault-hook finding in run004 is
repaired in run005. No implementation file, shared ledger, companion tree or
main adversarial-review note was edited by this lane; no ML, encryption,
ideal-interface disclosure or metered-search experiment was run.

## Evidence and exact versions

[EXECUTED] `audit_retained.py` checks retained logical snapshots, subprocess
records, crash markers, replies, fixture/export equality and the source hashes.
It does not open the implementation lane's live SQLite files. Results are
`retained_audit.json` / `.log` (run004) and
`retained_audit_run005.json` / `.log` (run005). Exact protocol, runner and fixture
copies are `run004_*` and `run005_*`; `review_manifest.json` pins them and both
source reports. The frozen repaired protocol SHA256 is
`014eaffa1210b70881efe5e49672653bf0373f33df980001b4272baa2ecc5b80`.

[EXECUTED] For **each** retained full run, the census finds 122 unique subprocess
IDs: 38 authority, 20 recipient, 64 client. Exits comprise five SIGKILL/−9,
53 cleanup SIGTERM/−15 and 64 normal client exits; retained stderr files are
empty. There are 20 case directories: four normal crash cases, an early-publish
negative control, a retry/mutation case, twelve races, host-only restoration and
authority rollback. These are case/process counts, not 122 independent claims.

[SOURCE: exporter implementation + retained executed output] The actual
`ExportFixture.lean:27` serializes `Closed.p` and `Closed.racing`, including
intent writes, guards, charges, nullifiers and events. `:42` reads selected and
initial values from those definitions; `:52` emits four executable checks.
`export.py:8` invokes the existing Lean executable/dependency environment;
`export_01.json` records exit0 and JSON exactly equal to the frozen fixture,
with all four checks true. This review did not rerun Lean or establish a Python
implementation refinement. The racing candidate has checked initial preflight;
it is not represented as a second accepted finality certificate.

## Ordering, crashes and concurrency

[SOURCE: frozen run005 implementation] `run005_protocol.py:107` starts
`BEGIN IMMEDIATE` before journal lookup or fresh preflight. The fresh transaction
updates state and all ten resource lanes (`:123`), inserts the transaction,
nonce and packet journal (`:132`), then commits (`:135`). The normal publication
RPC is later (`:143`) and uses that stored row. The journal has separate UNIQUE
constraints on transaction id and nonce (`:22`). Thus the intended normal path
has installed-before-published ordering at the local SQLite transaction boundary.
This is a source-level derivation plus the following process observations.

[EXECUTED] Crash markers contain the actual authority PID, named stage and a
time between its recorded launch and exit; the matching process exits −9.
The retained normal results are:

| Actual crash boundary | Committed journal before restart | Recipient packets before restart | Final publication attempts |
|---|---:|---:|---:|
| Before transaction/reservation | 0 | 0 | 1 |
| After state update, before journal insert/COMMIT | 0 | 0 | 1 |
| After journal/state COMMIT, before publication RPC | 1 | 0 | 1 |
| After recipient commit/reply, before authority publication mark/ack | 1 | 1 | 2 |

[EXECUTED] Every normal retry ends with one journal row, root1/state[1], one
recipient delivery and exactly one unit charged in each of the ten lanes
(initial10 → final9). The precommit crash is genuinely **after** the SQL state
update and **before** journal insertion, not after a simulated assignment. The
last boundary is before both the authority's `published=1` commit and the client
acknowledgment; those are different atomic domains.

[EXECUTED] Each of twelve retained races has two distinct authority PIDs,
distinct sockets and the **same database pathname**, plus two distinct clients
using the same launch barrier. Each accepts one candidate and refuses the other
as `stalePrefix`; one state/journal/debit/delivery remains. Both transaction91
and transaction92 win in recorded cases. [DERIVED] The barrier supplies competing
clients, not exhaustive scheduling or proof that both reach preflight together.
SQLite's shared write transaction provides serialization; this is not replication.

[EXECUTED] The new `focused_pending_retry.py` executes `run005_protocol.py` in
separate role processes and keeps all outputs in `focused_results/run_001/`.
It kills the first authority **after COMMIT and before publication**, verifies
one installed/unpublished row and an empty recipient, then starts two authority
workers sharing that database. Eight client threads issue exact retries. A
supervisor-held recipient SQLite write lock for one second is an explicit
scheduling aid; it changes neither role handler. This one schedule produces
**eight publication attempts, one stored recipient packet, one journal record,
one debit per lane, eight original-packet replay replies**. The final authority
publication bit is1. It is a focused overlap witness, not exhaustive concurrency
coverage. Raw owned SQLite files are gitignored; logical before/after snapshots,
RPC replies, command/PID/exit records, source hashes and logs are retained.

## Identity, deduplication and restore semantics

[SOURCE: frozen implementation] `run005_protocol.py:109` looks up a recorded
transaction before fresh preflight. An identical canonical semantic request
replays its stored packet; a changed body with that transaction id is refused
as `transactionConflict`. [EXECUTED] All eight retained already-published
concurrent retries replay without another publication attempt. All sixteen
same-id mutations are refused: eleven context fields, post bytes, charge,
read guard, nullifier bytes and packet bytes. The focused run additionally
sends a wire encoding with all object key orders reversed; it replays and
leaves both databases unchanged. Exact identity is canonical JSON identity,
not identical wire whitespace/key order; imported packet byte arrays are exact.

[EXECUTED, scoped] The other approved transaction with the same nonce is refused
as `stalePrefix` after the first commit, both in races and the focused test.
The sixteen mutation checks are **same-transaction-id** checks. They do not
independently reach the `alreadyConsumed` branch: this fixture's exact allowlist
and empty prior expose staleness first. [SOURCE] Nonce uniqueness is separately
present in the schema and preflight, but generic nonce/prefix validation is not
independently exercised by these fixed candidates. The prefix check is only a
length check (`run005_protocol.py:61`); the only approved prior is empty. No
claim about arbitrary history contents or mixed-operation framing follows.

[SOURCE + EXECUTED] Recipient `BEGIN IMMEDIATE` records its first nonce→packet
row and every attempt before responding (`run005_protocol.py:84`). Subsequent
identical txid/packet attempts are `duplicateSamePacket`; conflicting envelopes
are `conflictingPacket`. The focused run checks each directly after its eight
retry attempts; the original delivery and authority state remain unchanged.
The authority marks publication in a separate transaction (`:148`). Repeated
physical sends therefore occur even in the correct path. **Exactly-once physical
delivery is neither claimed nor demonstrated.**

[EXECUTED] Host-only restore copies back the host JSON snapshot. The authority
and recipient snapshots remain byte-for-byte equal as parsed objects; authority
revision1 rejects the stale competing candidate and exact retry restores the
host's view. The authority never imports state from that host file.

[EXECUTED + DERIVED scope correction] The authority-rollback control instead
restores its actual database to the initial backup after transaction91 committed.
Transaction92 then commits for the same nonce/parent. The two histories have
different transaction/event IDs and event envelopes, but **identical canonical
payload bytes and identical installed state[1]**. This is duplicate continuation
identity, not a witness of different arithmetic outputs. The persistent recipient
rejects the second envelope and retains its first delivery. Restoring authority
state violates the intended authority-continuity premise; recipient dedup alone
does not reconstruct the lost authority history.

[SOURCE: response semantics] An `accepted`/`replayed` response can carry
`publication=conflictingPacket` (`run005_protocol.py:146`); status alone means
installed/replayed, not successfully delivered. There is no background outbox
worker. After a committed-install crash, publication progress needs a client
retry and an available recipient. These are availability boundaries, not new
failures of the claimed local ordering behavior.

## Finding and repair

[DERIVED, original finding] In run004 the normal client's outer message could
supply `failpoint` and `crash_marker`; the deliberately broken early-publish
sibling read that same message. Therefore the literal normal interface did not
enforce the intended exclusion of trusted negative-control configuration.
The early-publish control produces a recipient packet with no committed journal.
The finding was sent to root and the implementation owner; frozen run004 sources
and evidence are preserved. This is a local fixture/control separation issue,
not a claim about cryptography.

[SOURCE + EXECUTED, repaired] Run005 moves the controls to trusted authority
startup CLI options. The client CLI has no fault options, and the authority
rejects any outer message whose keys are not exactly `{'request'}` **before**
opening a transaction (`run005_protocol.py:101`). The independent audit verifies
server-startup fault arguments and the retained extra-field refusal with empty
authority/recipient state and no marker. The focused process test runs the exact
repaired hash. Source-level access to startup remains trusted; separate local
processes do not enforce that trust against their shared Unix account.

## Claims retained and remaining scope

[DERIVED] The evidence supports this public, one-transition fixture's serialized
installation, persisted packet identity, retry idempotence and recipient logical
deduplication under explicit independent continuity resources. It does not
supply a cryptographic proof checker, hidden state, master-read removal, remote
peer authentication, OS isolation, power-loss durability, distributed consensus,
malicious-storage resistance or an implementation-to-Lean refinement theorem.
The protocol's fresh validity gate is the exact two-body fixture allowlist;
roots are public Bool byte values. These boundaries are explicit in the source
README (`:20`, `:24`, `:30`, `:43`, `:45`, `:59`), not hidden premises introduced
by this review.

[EXECUTED] Review reproduction from the repository root:

```sh
python3 research/learn_infer_only/experiments/adversarial_review/persistent_journal/audit_retained.py --run 004
python3 research/learn_infer_only/experiments/adversarial_review/persistent_journal/audit_retained.py --run 005
python3 research/learn_infer_only/experiments/adversarial_review/persistent_journal/focused_pending_retry.py
```

[EXECUTED] All three commands exited0 in the completed review. The first draft
of the retained audit had a source-path error before reading evidence; its
traceback remains in `retained_audit_initial_path_error.log`. The corrected audit
passes both pinned runs. Scry queries0; web queries0; no benchmark reruns.
