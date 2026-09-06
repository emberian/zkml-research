# Persistent journal and release fixture

[EXECUTED] `results/run_005/report.json` passes all assertions with unchanged source inputs. It retains 122 actual subprocess command records, process ids/exits, server/client output, per-boundary SQLite snapshots, crash markers and the final databases. The run exercises real `SIGKILL` and two independent authority-worker processes contending on the same SQLite journal. It is an execution fixture, not a cryptographic construction or a proof of physical persistence.

| Frozen artifact | SHA256 |
|---|---|
| `protocol.py` | `014eaffa1210b70881efe5e49672653bf0373f33df980001b4272baa2ecc5b80` |
| `run.py` | `9691f642b4920e97264d6933bd13d1895e4774ddfed783b8db8dd0b7a66c7403` |
| `fixture.json` | `584e575c782a5b0c6c350f957912ac40a2791df8e604b68a51e8e7baad422801` |
| `ExportFixture.lean` | `afda90d0c734472c28b6c1f4760ae733cde6f9e9df0a565744ea1051606854ca` |
| `export.py` | `0709d1775b1c54a99acdd5bfadb7e0726bfb2981a6e846dd6ae82049404ce182` |
| `results/run_005/report.json` | `25d65944fcd981a4c669d9f70614f13dfdfee3555c322ae023bdca384f3974a6` |

## The instantiated boundary

[SOURCE, existing proved model] `formal/durable_integration/Assurance/ResidentDurableIntegration.lean:312`, `gatedExecute`, looks up a journaled transaction before fresh authorization. `releasedPacket:326` obtains the packet from the installed journal or recorded retry; it takes no second caller-supplied Plan. `Closed.p:471` is the existing public Bool cell's validated 0→1 write. `Closed.subject:522` inhabits accepted context/receipt, full preflight, actual materialized install, next-root equality and the same receipt's descriptor premise. These frozen proofs are dependencies; no new theorem is asserted by the Python fixture.

[EXECUTED] `ExportFixture.lean` reads those existing definitions and prints their actual context, DataIntent writes/guards, exact ten-lane charge, nullifier envelope and packet bytes. `export_01.json` records the successful command and dependency hashes. Its four executable checks are true: primary preflight, primary exact openings, primary finality gate, and the existing racing candidate's preflight at the initial snapshot. The primary packet binds genesis7, parent0, program0/version1, command1, authorization19, recipient23, deterministic randomness rule/commitment0, next1 and output1. The cell's roots are the example's public byte values, not cryptographic commitments.

[OPEN, explicit fixture premise] Fresh computational validity is an exact allowlist of the exported primary and `Closed.racing` candidate bodies. The Python service does **not** verify a Fiat–Shamir receipt, compile a transition, or prove that two competing candidates were finalized by one Lean vote book. The primary comes from the existing accepted subject; the racing body is the existing materialized/preflight candidate. This fixture tests one continuity authority selecting at most one of those candidates. Replacing the allowlist with the actual authorized proof-bound mechanism remains an implementation-refinement obligation.

[DERIVED from the fixture] There are three roles. The authority owns the SQLite journal, current canonical cell bytes, monotone generic authority revision, exact resource budget and spent-nonce identity. The host holds an independently restorable JSON snapshot and sends candidate requests over a local Unix socket. The recipient owns a separately persistent nonce→exact packet inbox and records every publication attempt. No private credential is generated or retained; all fixture state and packets are public.

[OPEN, independence premise] Separate processes and directories are role modeling, not a security boundary. All processes here run under one local Unix account. A SQLite file that the malicious host can replace is **not** an independent finality resource. The intended premise is that the authority's committed state cannot be rewound by host restoration. The recipient's deduplication state is a second explicit continuity assumption. The authority-rollback negative control deliberately violates the first premise while retaining the second.

[DERIVED from `protocol.py`] A fresh request enters `BEGIN IMMEDIATE` before journal lookup and preflight. It checks the exact approved body, selected genesis/state/authorization/recipient, actual current canonical bytes and prefix, spent nonce, singleton post-root/byte binding, immutable genesis read guard and all ten resource charges. State installation, resource debit, nonce uniqueness and the replay journal enter one SQLite transaction. `COMMIT` precedes publication. Journal transaction id and nonce have independent unique constraints. The selected genesis is immutable fixture configuration whose identity is persisted; this is not a mutable-genesis implementation.

[DERIVED from `protocol.py`] Exact retry compares deterministic canonical JSON of the exported semantic request fields against the recorded body. The packet's imported canonical byte array is retained verbatim. Object key order in incoming JSON is normalized; “exact” does not mean rejecting an equivalent whitespace/key-order wire encoding. The response/publication packet is read solely from the journal row. A changed caller context, post bytes, charge, guard, nullifier or packet cannot relabel a previous success.

[DERIVED, scheduling scope] `meta.head` is a **generic authority revision**, not a window-admission counter or model-learning count. This fixture instantiates one public Bool transition per fresh database, then tests retry/competition/restore. Its exported prior is the empty prefix, so it does not establish general prefix encoding or mixed learn/infer framing. The frozen ciphertext-window theorem's counter=journal length applies only to exclusive window-admission histories; a mixed history needs an admission projection or a scheduling restriction.

## Executed crash and race results

[EXECUTED] Each normal crash case uses an actual client subprocess and kills the authority with `SIGKILL` at the named code boundary; the retained marker identifies stage and pid, and the authority exit is −9. Restart opens the same database and exact retry completes.

| Actual crash point | Durable install before restart | Recipient packet before restart | Retry | Final journal packets / recipient deliveries / attempts |
|---|---:|---:|---|---|
| Before reservation/transaction | 0 | 0 | accepted | 1 / 1 / 1 |
| After state update, before transaction commit | 0 | 0 | accepted | 1 / 1 / 1 |
| After committed install, before publication | 1 | 0 | replayed | 1 / 1 / 1 |
| After recipient publication, before publication mark/client acknowledgment | 1 | 1 | replayed | 1 / 1 / 2 |

[EXECUTED] The uncommitted-install crash rolls back the state, all charges and journal together. The committed-install crash retains all of them. All final databases pass SQLite `integrity_check`; their journal mode is WAL and the connections use `synchronous=FULL`. Those are observed local process-crash results, not a power-loss, malicious-storage, distributed-consensus or filesystem durability theorem.

[EXECUTED] The publication-gap case deliberately crashes after the recipient has committed its packet but before the authority marks publication or acknowledges the client. Retry sends the same stored packet again. The recipient records two identical transport attempts and one logical delivery. Thus this fixture establishes idempotent retained packet identity under its recipient-persistence premise; it does **not** establish one physical network delivery or an atomic transaction across authority and recipient databases.

[EXECUTED] Eight simultaneous exact-retry client processes all receive `replayed` and the original packet. They produce no additional journal entry, charge or publication attempt after the normal publication mark. Sixteen same-id changes are rejected as `transactionConflict`: all eleven context fields plus post bytes, exact charge, read guard, nullifier bytes and packet bytes. The packet bytes are not recomputed on retry. Since this particular accepted program is deterministic, the randomness-field mutation is an identity test, not an encrypted random-output experiment.

[EXECUTED] Twelve same-parent races each launch two separate authority-worker processes sharing one SQLite database and two separate host-client processes released by a barrier. Each race accepts one transaction, refuses the other as stale, and leaves one journal record, one nonce, one resource debit per lane and one recipient packet. Pairs of authority/client pids are retained in the report. The shared database supplies the serialization point; this is not a replicated authority or a network-partition test.

[EXECUTED] Restoring only `untrusted_host/state.json` to its initial revision0 leaves authority revision1, state[1], journal and recipient unchanged. A competing stale request is refused (`stalePrefix`); the exact original transaction replays its original packet and restores the host's view to revision1. The authority and recipient snapshots compare equal before and after that exact retry. No authority state is imported from the host manifest.

## Falsifiers that retain the scope boundary

[REFUTED: publication before committed installation] The deliberate `broken_publish_before_commit` sibling sends the candidate to the recipient while the state transaction is uncommitted, then kills the authority. The recipient holds one packet while the recovered authority has zero journal entries and initial state. A later successful recovery cannot erase that earlier ordering violation. Only explicit trusted authority startup configuration can select this control. Normal request envelopes accept exactly one `request` field; a host-supplied `failpoint`/`crash_marker` envelope is rejected before any transaction or publication, as the new refusal control demonstrates.

[REFUTED: rewindable authority suffices for finality] The authority-rollback control saves the initial authority image with SQLite's backup API, commits transaction91 and publishes its packet, stops the authority, restores that initial image and restarts. Transaction92 then commits against the same nonce and parent. Across the two retained histories there are two distinct committed event envelopes for one nonce (transaction/event ids91 and92). Their canonical payload bytes and installed state[1] are identical; this witnesses duplicate continuation identities, not different arithmetic outputs. The still-current recipient rejects the second packet as `conflictingPacket`, so its one delivery survives. That recipient continuity does not repair the forked authority history; nor does the example prove availability after the conflict. This is an executable failure of the assumed nonrewindable authority, not a break of encryption or the scoped Lean theorem.

[OPEN] Remaining bridge: prove an implementation relation from this or a real authority backend to the kernel's atomic snapshot/journal model; replace the public candidate allowlist with the exact cryptographic authorization path; establish the authority/recipient isolation and persistence assumptions; specify a general mixed-operation journal/admission projection; and model power loss, independent failures, transport authentication, partitions and recovery policy. The experiments do not make a hidden resident or remove a master-read credential from a cryptographic implementation.

## Reproduction

[EXECUTED] From `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/durable_integration/persistent_journal/export.py
python3 research/learn_infer_only/experiments/durable_integration/persistent_journal/run.py
```

[EXECUTED] The exporter reuses the frozen resident dependency oleans, emits no new proof artifact and writes only this owned directory. The runner uses Python's standard library, local Unix sockets and SQLite; no network service, plugin, secret key, production deployment or companion edit is involved. It closes all spawned processes and removes only its own temporary socket directory. Each run gets a new numbered result directory; earlier logs remain. Run001 stopped at a harness error caused by copying a WAL database while its backup connection remained open. The harness now closes both connections and restores through SQLite's backup API. Run002 passed the requested cases; run003 added the early-publication falsifier; run004 additionally raced separate authority worker processes. Review found that its original outer client message could select a negative-control fault mode. Run005 moves all fault configuration to authority startup and verifies normal client fault-field refusal. Exact old protocol/runner sources are preserved in `snapshots/run_004/`; only the frozen, source-matching run005 supports the final interface claim. Scry queries0; web queries0.

[EXECUTED] `archive_runtime.py` hashes and compresses the owned raw SQLite/WAL/SHM files into `sqlite_evidence.tar.gz`; `sqlite_evidence_inventory.json` pins each raw file and the archive. Raw runtime files remain in place but are gitignored. Logical state/snapshot JSON, exact commands, stdout/stderr, source snapshots and failure reports remain ordinary artifacts. No broad deletion or companion write occurred.
