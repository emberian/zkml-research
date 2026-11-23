# Moving a resident between operators

[EXECUTED] A paid move through the `offer`, `accept` and `admit` commands took **114.087 ms median on M2 Max/APFS** and **168.110 ms median on shared hbox/ext4**. Each sample included three live custodian daemons, proof generation, independent verification by B and the public log, durable publication of the package, and a restored A failing to learn at all three custodians. On hbox, a separate run with native differential checking refused all twelve specified cases. [Integration test](../native/resident_custody/tests/full_resident_house_move.rs) · [Audit output](../research/w15_resident_house_move/audit.log)

| Release measurement | Moves | Native differential | Minimum | Median | Maximum |
|---|---:|---|---:|---:|---:|
| M2 Max, APFS, six Rayon workers | 11 | off | 106.617 ms | 114.087 ms | 414.479 ms |
| hbox, ext4, swarm-build, default worker count | 11 | off | 151.648 ms | 168.110 ms | 389.495 ms |
| hbox, ext4, all native checks and refusal assertions | 1 | on | | 183.999 ms | |

[DERIVED] The timer starts before sealing the source receipt. It includes writing the CLI inputs, starting both operators' move commands, reopening the log, file and directory syncs, restoring the old seat and cursor, and starting the fenced operator. The mesh is already running, A's journal is populated, and its snapshot and B's admission policy exist before the timer starts. The measurements use one machine and one disk per run. The 120 ms target holds for the measured Mac median. Both eleven-move samples included slower moves. [Timing code](../native/resident_custody/tests/full_resident_house_move.rs)

[REFUTED: Stage 1 end-to-end timing scope] The 112.792 ms hbox and 185.249 ms Mac medians in the original log timed a callback that retained only the head and latch. The CLI appended the package separately before replacing its latch file. A crash between those writes left an ambiguous journal tail. The current log publishes the package, head and latch together in one fsynced file per epoch. The measured path and the CLI failure/retry test use this same store. [Stage 1 measurements](../research/w15_resident_house_move/bench.log) · [Public log](../native/resident_custody/src/house_move/log.rs)

## What a vote authenticates

[SOURCE] Obend commit `25dd6789`, `lean/Obend/Lower/Pancake/BeltLatch.lean`, defines the guards at lines 50–58, field offsets at 64–74 and the five-word store at 96–100. `pancakeBeltLatch_correct`, `pancakeBeltLatch_refusal_preserves_state`, `pancakeBeltLatch_frame` and `accepted_parent_consumed` concern the Pancake semantics and the pure transition. The Rust API uses distinct state and request buffers. [Rust word codec and tests](../native/resident_custody/src/obend_latch_abi.rs)

| Buffer | Word layout, inclusive offsets |
|---|---|
| State, 14 words | initialized 0, genesis 1–4, epoch 5, head digest 6–9, policy 10–13 |
| Request, 19 words | genesis 0–3, parent epoch 4, next epoch 5, parent digest 6–9, next digest 10–13, policy 14–17, persist acknowledgment 18 |

[DERIVED] Each word is a little-endian u64. Digest limb zero contains bytes 0–7 in their original memory order. The guards require canonical initialization and matching genesis (code 1), matching parent epoch (2), unsigned strictly increasing next epoch (3), matching parent digest (4), matching policy (5) and acknowledgment exactly one (6). Failure returns the first applicable code and preserves the state. Success returns zero and replaces words 5–9 with the next epoch and four digest limbs. The mesh uses consecutive epochs and hashes the entire head, including the world root, into the latch digest. [ABI mapping](../native/resident_custody/src/custody_mesh.rs)

[EXECUTED] Lean 4.35.0 evaluated the pinned pure transition, vectors, word layout and byte encoder directly. All 21 inputs and expected outputs, 11,256 bytes in total, are pinned in the ordinary Rust test. The rebuilt x86-64 CakeML ELF matched those 21 oracle outputs, then matched Rust across all 4,153 comparisons, including 132 single-word mutations and 4,000 deterministic pseudorandom records. Each comparison checks the status, all 14 state words and all 19 request words. Status counts for 0–6 were 911, 1,183, 194, 1,013, 440, 315 and 97. [Lean fixture generator](../research/w15_resident_house_move/lean_vectors.py) · [Audit output](../research/w15_resident_house_move/audit.log)

[DERIVED] Each custodian probes a proposal on a temporary latch. A fresh transition writes and syncs the WAL, renames it and syncs the directory before stepping its installed latch and voting. A failed write maps to Obend 6 and qsag WAL failure. A consumed parent maps to Obend 2, and qsag permits only the exact installed command to replay. The trailing checkpoint is a diagnostic copy. Restart reconstructs and syncs it from the authoritative WAL before listening. Roster contact remains sequential. [Custodian](../native/resident_custody/src/custody_mesh.rs) · [Crash and recovery test](../native/resident_custody/tests/resident_house_move_and_cshake_open.rs)

[DERIVED] Each Ed25519 vote signs a 32-byte mesh digest. Its input is the `durable epoch` domain and the bincode byte vector containing all 152 request bytes with `persistAck = 1`. The public verifier rebuilds this message and checks distinct roster signers under the configured threshold. The run used three of three and exercised all 88 custodian latch steps against the ELF. A signature attests to that custodian's acknowledgment. Actual durability depends on its WAL implementation, filesystem and honesty. [Signature and certificate verification](../native/resident_custody/src/custody_mesh.rs)

## What B and the log check

[SOURCE] At DreggNet `1d4fad6`, `billing/src/handoff.rs` defines the v1 JSON wire types, canonical SHA-256 seat root, Ed25519 signature, mint reconstruction, per-credit checks, transfer epoch floor and checked reserve arithmetic. The signed claims name source, target, asset, customer seat, provisional principal, reversal deficit and issuer cap. The exporter reads payment states in its SQLite transaction and rejects nontransferable states at `billing/src/reserve/store.rs:498`. The two supported credit backings are provisional and settled.

[EXECUTED] B verifies the receipt and its binding to the signed grant before asking the custodians to vote. The public log independently verifies the receipt against its own cap, currency, asset and epoch floor. Both derive the customer seat from the resident genesis and require the signed seat root to equal the authorized claim. The pinned upstream verifier accepted resident-generated receipts and vice versa for two fixtures, including a three-credit seat with a zero remaining balance on one credit. The upstream golden digest was `18a1d5bc50e9b133a5176dd7fb0c8e79bcbccf3600fa1d0a5d4c9308b2895174`. [Interop test](../research/w15_resident_house_move/check_billing.sh) · [Admission checks](../native/resident_custody/src/house_move.rs)

[DERIVED] The non-dispute statement is the issuer's export-time assertion about transferable credits. A v1 receipt has no independent dispute-status attestation or live Stripe lookup. The receiver supplies the trusted epoch floor. The fixture signs synthetic credits and performs offline verification. It does not move balances between live billing ledgers.

[DERIVED] The log checks that the certified successor consumes its installed parent, that the packaged parent matches the commitment, and that issuer, A and B signed the certified Migrate. The provisioned genesis is the trust anchor for an immediate first move. Later parents require a quorum certificate. A move preserves the world root, exposure totals and journal cursor. [Public verifier](../native/resident_custody/src/house_move.rs)

| Journal cell bytes | Field | Public projection |
|---|---|---|
| 0–23 | Genesis/policy identity digest prefix | yes |
| 24–31 | Cursor | yes |
| 32–47 | Experienced, told, inferred and forgotten counts | yes |
| 48–63 | Private journal hash-chain prefix | hidden |

[DERIVED] The journal and eight W0 weights occupy separate blinded leaves of a two-leaf world trie. The 64-party bit-sliced cSHAKE256 proof binds the fixed journal path, sibling, world root and 48-byte projection of the 64-byte cell. The serialized opening carries the W0 sibling, journal cell root, counts, cursor and proof. The verifier reconstructs the identity and fixed projection range. The complete opening has **96 bytes of framing plus at most 90,880 proof bytes, or 90,976 bytes**. In the native run the proof was 89,840 bytes and the complete migration package was 94,632 bytes. [Wire-bound test](../native/resident_custody/src/cshake_selective_open.rs) · [Branch binding](../native/resident_custody/src/trie_opening.rs) · [Measured package](../research/w15_resident_house_move/audit.log)

[DERIVED] A authorizes the public header for its current head in the paid offer. An authenticated snapshot supplies one bounded proof worker while the daemon continues servicing serialized WAL transitions. B verifies the opening while collecting the quorum and checks that all four head fields used in that verification carry across the move. For genesis and for a consumed parent on retry, B can request the successor opening. The log always verifies against its own certified successor. The private episodes, proof witness, W0 weights and blinding keys stay with the custodians. The public package exposes provenance counts and the billing receipt. [Paid move API](../native/resident_custody/src/custody_mesh.rs)

## Adversarial and continuity results

[EXECUTED] The release integration test required each of these refusals. The billing mutations had valid source signatures over their test inputs, and the package-level tests could sign alternative heads with every fixture custodian key. [Full assertions](../native/resident_custody/tests/full_resident_house_move.rs) · [Native output](../research/w15_resident_house_move/audit.log)

| Case | Required outcome |
|---|---|
| 1. Disputed backing | v1 JSON decode refused the explicit backing |
| 2. Excess reserve exposure | `UnbackedReserve` |
| 3. Wrong billing target | `WrongOperator` |
| 4. Sibling parent digest | Obend 4 |
| 5. Policy drift | Obend 5 |
| 6. Missing persistence acknowledgment | Failed custodian WAL, unchanged bytes, code 6 and no quorum. Failed public-log publication, no new epoch, then successful retry |
| 7. Modified projected cursor | Cut-and-choose transcript refusal |
| 8. Replayed earlier header | World-membership refusal |
| 9–11. Restored A attempts Learn, Infer and Migrate | Each refused at 3/3 custodians |
| 12. Receipt from another resident | Both the original seat-root mismatch and the rebound wrong customer seat refused |

[SOURCE] Tulip's bounded handled-message ledger is in allgame `6170b9e`, `claude_resident/handled.py:28`. Its restart loop consults that ledger while filtering a recent message window in `claude_resident/zulip_loop.py:190–244`.

[EXECUTED] The custody test models a message ID as an episode ID. B accepted new IDs 104 and 105 and rejected the repeated IDs, including forgotten 101. Its first 16-byte W0 projection matched A's last, including a zero forgotten coordinate. W0 replay agreed with the orthogonal unlearning operation and the carried disclosure budget still rejected an over-budget Infer. [Continuity assertions](../native/resident_custody/tests/full_resident_house_move.rs)

[DERIVED] This is continuity of certified journal operations against an intact custodian quorum. The fixture records would-be replies in a Rust vector. Actual Tulip delivery, atomic delivery across a messaging crash, physical erasure of the tombstoned episode, and rollback of the custodian quorum are outside this result. Exact-command retries can return an existing certificate. The Rust wire and custody WAL formats have changed from the earlier single-leaf prototype. These runs provision fresh meshes.

## Reproduce

```sh
# From the repository root. The pinned companion trees are read-only inputs.
sh research/w15_resident_house_move/check_billing.sh /Users/ember/dev/DreggNet
python3 research/w15_resident_house_move/lean_vectors.py /Users/ember/dev/obend native/target/lean-records.bin
cmp native/target/lean-records.bin native/resident_custody/tests/fixtures/belt_latch_records.bin
cd native
RUSTFLAGS="-D warnings" cargo test --release -p resident_custody
RAYON_NUM_THREADS=6 RUSTFLAGS="-D warnings" cargo test --release -p resident_custody --test full_resident_house_move house_move_latency -- --ignored --nocapture
# Linux. Point RESIDENT_MESH_DIR at an existing durable directory.
OBEND_BELTLATCH_EXE=/path/beltLatch cargo test --release -p resident_custody --lib obend_latch_abi -- --include-ignored --nocapture
OBEND_BELTLATCH_EXE=/path/beltLatch RESIDENT_MESH_DIR=/disk/mesh cargo test --release -p resident_custody --test full_resident_house_move -- --nocapture --test-threads=1
```

[OPEN] The remaining measurements are separate-host custody, independent storage failure, and latency under controlled CPU load. Proposed verdict wording is a CLI move with a 114.1 ms Mac median, 168.1 ms shared hbox median, twelve specified refusals and independent Lean/Rust/native ABI agreement on all 21 pinned records.
