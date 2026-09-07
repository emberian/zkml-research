# Independent normal integration and provenance review

[DERIVED: disposition] **Accept the completed positive path with one nonblocking wording correction.** The frozen designated-span integration's public ledger, source bindings, call identities, acknowledgement boundary and recorded cost totals are consistent. Its public service implements the intended separation between encrypted acceptance and private decoding. This is normal functional/source evidence under the stated trust assumptions; it is not an independently executed cryptographic experiment or proof that the whole research coordinator satisfies the protocol's host-view experiment.

[SOURCE: exact target] Package `integration/EVIDENCE_MANIFEST.json` SHA256 **`36d8fdb7ef23e73e48ba2fb6d6d0f498fe999b933cf0aa76a5e3ea1f2109c6c5`**, `CLOSURE.md` **`3135d59ad0475abede6a646c4b01b1b757bba23c03a96ad2078c97cab0efabb4`**, and exported `report.json` **`dbc7b6b41ff27a380755c210d9a1c190b3792fb1922f0a492add065312113ece`**. The accepted mathematical contract is `../PROTOCOL_PRIVACY.md` at **`aa7b096e5ff44b4c72ef72f005a363897e06a8fb94d0351bfa15856f3564fec0`**. Paths below are relative to `experiments/private_construction/designated_span/integration/`. Review date: 2026-09-07 UTC.

## Independent checks and their boundary

[EXECUTED] `check_public.py` in this review directory rehashed all **72 package files / 3,445,334 bytes**, the **32 exported evidence files**, all **eight genesis-pinned core modules**, all **four crypto runtime files**, the **seven inherited originals and their seven preserved copies**, and the named public native dependency. All matched their frozen hashes. It parsed source with `ast`, without importing operational modules. All 16 public query encodings, row/token/recipient hashes, public-context identity, parameter/program identities and the trusted context-validation record agree. Public row bounds equal `32*127*sum(abs(y))`, and the recorded group order exceeds twice every bound. These are public integer/hash checks, not a subgroup/token-algebra revalidation.

[EXECUTED] The authoritative check command is:

```text
python3 -B check_public.py > check_public_002.log 2>&1
```

[EXECUTED] `check_public.log` preserves the earlier green version; `_002` adds public parameter/program, exact-width and token-identity checks. Results and source hashes are in `public_check.json`. `harness_guard.diff` preserves the original/current driver difference; `diff`'s exit 1 means differences were found, not a failed review check.

| Independent check of retained public evidence | Result |
|---|---:|
| Ordered finalized transitions | 44 |
| Learn / Infer / exact-original expiries | 40 / 4 / 8 |
| Historical exact retries | 2 |
| Matching logged transition-call sequences | 44 each: host, authority, recipient verifier, final replay |
| Canonical public queries | 16 |
| Public CLI records / including recorded setup children | 1,630 / 1,663 |
| Public JSONL records / nested parsed output documents | 1,768 / 1,718 |
| Private files opened or hashed by reviewer | 0 |
| Reviewer crypto runs / new adversarial tests | 0 / 0 |

[DERIVED: evidence distinction] I independently reconstructed the public queue/digest chronology and compared all four roles' logged input/output identities. I did **not** rerun group arithmetic, verify signatures cryptographically, inspect runtime databases/CAS files, open private vectors/keys/answers, or repeat the four private integer comparisons. Those arithmetic executions, persistence checks and private comparison outcomes remain author-executed evidence whose source and public reporting are reviewed here. “Independent recipient verification” means a separate recipient process/state recomputes using the same public transition implementation; it is not an independent mathematical implementation of the primitive.

## Actual normal call path

[SOURCE] `source/journal/roles.py:6` runs setup, validates the public context without a cache token, then generates independent Ed25519 issuer, command and authority keys (`roles.py:24`). Genesis pins the context, validation record, eight adapted core files, four crypto files and native dependency. Public host configuration and public reader configuration do not include a recipient scalar directory. The private drain configuration alone adds that directory and separate private database/cost paths (`roles.py:47`). This is a source-level separation under trusted configuration and shared-account assumptions, not filesystem isolation from the machine operator.

[SOURCE] `source/journal/common.py:74` hashes the pinned runner, crypto sources, native dependency and context before each actual CLI call. After the explicit full validation, operational calls pass the pinned context digest; `source/crypto/crypto.py:173` still parses canonical context bytes and checks public identities/ranges, while skipping the previously validated public algebra. The digest is a trusted validation cache, not a proof that arbitrary supplied context bytes were honestly generated or erased. Ciphertext loading retains its actual subgroup/type/canonicality checks. The four copied crypto files match the previously reviewed backend exactly; no new primitive theorem is inferred from this integration.

[SOURCE] `roles.py:54` issues a freshly encrypted private input and signs the complete action. `model.py:7` checks the signature over the exact canonical action, genesis/program/params/context/key identity, parent, route, record, feature policy and range assertion. Infer additionally binds query hash, fixed row, row hash, token and recipient. The bounded-range claim is an honest issuer assertion, not a zero-knowledge range proof. Source crypto issuance samples `secrets.randbelow(Q)` anew and returns public ciphertext metadata; it does not emit the vector or its hash. Authentication keys are generated independently of crypto setup; their later signed messages may naturally depend on public history.

[SOURCE] `model.py:32` derives expiry from the actual current queue, supplies the exact oldest ciphertext to the backend, and updates the queue with that original reference. It does not accept an independently supplied old object. The authority repeats this computation under its current database head, compares canonical proposal bytes and atomically inserts its signed envelope plus new head before publication (`authority.py:53`). An exact historical request lookup precedes currentness checks, returning its original finalized identity without recomputation or a new revision.

[SOURCE] The actual server started by `source/journal/run.py:26` is `source/verified_reader/service.py`, not the inherited base reader alone. `VerifiedReader.sync` at line 67 checks the current recipient head, exact signed action, uniqueness, every proposed transition and resulting state/output, then commits its own verified journal. `VerifiedReader.receive` at line 137 requires exact membership in that verified journal before delegating to the base acceptance method. The base `reader.py:32` requires the selected authorization ticket and designated output identities, stores only ciphertext/envelope identity in `received`, commits, and returns the ACK. Authority publication calls sync before receive and describes ACK as durable ciphertext acceptance with no decode (`authority.py:32`).

[EXECUTED] The retained first 44 envelopes are byte-identical to the saved replay rows. Their request digests, canonical signed payloads, parent revisions/state digests, next-state digests and recorded verification replies agree. Four Infer operations occur after Learn 10, 20, 30 and 40, selecting rows 0–3. Every Learn uses route 0; route 1 stays exactly at its empty initial state. Final revision is 44, with route-0 queue containing original Learn 9–40 and digest **`1e924a54f4dc23be0bccc3c14f83db9deefce1d6af697726707c36ca8983826e`**. The saved revision-22 checkpoint matches independent public reconstruction. Historical retries of `learn-01` and `infer-10` retain their exact envelopes; both verifier replies say replay, and the Infer acceptance is replayed. The recorded host/authority/verifier/final-replay command sequences each use exactly the reconstructed accumulator, fresh, old or query digest and produce the same output digest.

## Public ACK, private drain and coordinator feedback

[SOURCE] `source/journal/drain.py:13` has no public RPC endpoint. It reads accepted ciphertext rows, verifies signed/request identity, checks exact verified-journal membership and selected ticket, then uses the corresponding row's dedicated scalar. Its answer/dedup table and cost log are separate private persistence. The accepted public database is used only for reads in this path. Later public `register`, `receive`, `status`, `verified_status`, authority head/export and retries do not read private answers, private decode counters or private outcome files. Physical locking, scheduling and shared-machine observation remain excluded; this is a data-dependency statement, not a whole-program timing proof.

[SOURCE / author-executed evidence] The preserved first harness checks that the private answer database does not exist at every Infer ACK and at public completion. It finishes all 44 public events and two historical retries before invoking private drain. It then compares private results, repeats drain, checks four stored decodes and runs a final independent public replay. The saved report records four matching private integers and zero new decodes on the second drain. I reviewed the code establishing these checks and the successful aggregate reporting, without reopening their private evidence.

[DERIVED: necessary scope] **The original coordinator's final public replay is after private drain and comparison.** The source order is `normal_flow.py:65` drain, line 66 comparison, line 67 second drain, then line 69 replay. Report publication and the decision to schedule that replay therefore depend on trusted private-phase progress/success. The accepted `PROTOCOL_PRIVACY.md` excludes such feedback unless it is allowed leakage. This package correctly excludes the research coordinator's scheduling, comparison bit and report from the host view. It does not establish that the complete harness is itself a feedback-safe public protocol. A stricter full-run wrapper should finish public replay/status/event handling before private drain and keep subsequent comparison/reporting private. Merely suppressing scalar stdout would not close this condition.

[DERIVED] The private drain holds all 16 recipient keys, so it is the full fixed-span recipient coalition. Its dedup table does not restrict what those keys can compute outside the program. The accepted game charges every visible issuance, including retained or expired inputs, and requires per-input coalition projection compatibility. The executed fixture is one private random arithmetic history, not a two-world privacy experiment. All 40 raw inputs and known zero initialization remain available to the trusted oracle; that role can reconstruct the full raw aggregate. The experiment therefore supplies neither coalition-wide absence of read-all knowledge nor useful private text/model cognition. No new rank/image/extraction experiment was performed here.

## Guard finalization and wording correction

[EXECUTED / SOURCE] The original harness at SHA256 **`497a3c69212a0cb61637faa2fc13ee7a1d0a603c4dc82d257a1b44703961f478`** is preserved. It reached the final raw-substring omission guard and exited 1 because public `commands.jsonl` contains the parameter name `row_signed_score_bounds`. Independent recursive parsing confirms exactly one such public bounds field, no exact private scalar/decode field, no `reader-decrypt` command and no private-output-omission marker across all six exported JSONL files. All command stderr fields are empty. The parsed check is a concrete field/domain audit, not a general leakage theorem or assurance about arbitrary diagnostic text.

[SOURCE] `finalize_normal_001.py` checks the existing completed ledger/replay and private aggregate/dedup evidence, applies the parsed guard, and writes the corrected report. The retained execution record distinguishes original exit 1, finalizer exit 0 and exporter exit 0. The current future driver changes only the guard import/replacement; the complete modified driver was not rerun. No group/decoder result is regenerated by finalization.

[DERIVED: nonblocking correction agreed by root and author] The frozen README/CLOSURE/finalizer wording “no cryptographic operation was rerun” is literally too broad. **`finalize_normal_001.py:26` calls `verify` for each of the 44 envelopes; `source/journal/common.py:47` performs Ed25519 signature verification, and hashing also occurs.** The precise statement is: **no designated-backend CLI/group-arithmetic operation or private scalar decode was rerun**. This correction does not undermine the completed normal behavior or the unchanged backend command evidence. Frozen bytes were preserved for review; the parent and author acknowledged the wording correction for subsequent citation/folding.

## Costs and retained artifacts

[EXECUTED] Independent summation of the actual public command records reproduces all role counts, total/min/max durations and top-level/setup-child source counters. There are 1630 top-level CLI calls, plus 33 recorded setup child processes. Summed CLI elapsed time is **2203.072922793 seconds**, including the final public replay. This is not an end-to-end wall-time total: role/RPC intervals contain CLI work, and setup child intervals are already inside their parent invocation.

| Role | Calls | Summed public CLI seconds |
|---|---:|---:|
| Trusted setup/query encoding | 19 | 81.056588 |
| Issuer | 40 | 45.600608 |
| Public transport | 84 | 91.473493 |
| One-shot host | 1057 | 1306.110461 |
| Authority | 151 | 230.708667 |
| Recipient verifier | 151 | 249.731925 |
| Final public replay | 128 | 198.391181 |

[EXECUTED] Source counters sum to **1,213,729 native modular powers**, **1,026,248 subgroup checks**, **18 full context validations**, **288 checked token equations** and **1627 pinned-context reuses**. These are independently summed recorded counters, not independent instrumentation of the native library. The 1013 one-shot host inspections account for **1200.593653330 seconds**. Any persistent-host/full-history speed estimate remains a forecast until its separate execution.

[EXECUTED] The last public progress timestamp is **2020.574594500 seconds**, immediately after 40 Learn/4 Infer. The elapsed point after historical retries was not persisted, so the corrected report appropriately leaves its exact phase-time field null. Private decode times and private comparison timings are not included in these totals. Finalizer/packaging signature-verification and hashing costs are also outside the backend CLI sum.

[EXECUTED / SOURCE] The public context is 342331 bytes; parameter/header arithmetic gives state 148147 bytes, designated output 691 bytes and scalar envelope 435 bytes. The exported namespace inventory reports 16 scalar files/6960 bytes, no remaining named delivery/pending/setup entries, separate public/private database paths, and 40 private oracle vectors excluded from export. I checked that the export code records counts/lengths rather than copying or hashing private files; I did not repeat that runtime inventory. Reported CAS storage is 100 objects/11,886,238 bytes each for host and authority, and 88 objects/11,862,466 bytes for the recipient. Expiry retains old ciphertexts. Named-file cleanup and a never-serialized master source path do not prove memory erasure, backup absence or physical deletion.

[DERIVED: final scope] This package is credible normal integration evidence for the frozen conditional classical fixed-span construction, with honest setup/issuer assumptions, trusted coherent configuration, persistent local journals, private scalar drainage and explicitly excluded oracle/coordinator/side-channel observations. It supplies no new hardness bound, post-quantum guarantee, adversarial persistence result, private encoder theorem or recipient self-restraint mechanism. No shared/frozen/companion files were changed, no stopped task was resumed, and metered searches were 0.
