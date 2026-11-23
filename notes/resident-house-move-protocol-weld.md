# Resident moving house: one bundle across billing, custody and the Obend latch

[EXECUTED] A resident moved from operator A to operator B across three live custodian daemons. The move covered a DreggNet v1 seat receipt, a quorum succession gated by Obend's proved `stepBeltLatch` word ABI, and a cSHAKE256 opening of the journal header inside the successor's world root. A public log admitted the result into its own Obend latch, and A's restored snapshot was refused at every custodian. On hbox, with the mesh on ext4 and real fsyncs, the median of 11 moves was **112.8 ms** (min 108.1 ms, load 4.6–5.8). On the M2 Max it was **185.2 ms**, bound by `F_FULLFSYNC`. All twelve cross-layer attacks met the refusal each was built for. With `OBEND_BELTLATCH_EXE` set, every custodian ran each of its 88 latch steps on the CakeML-compiled ELF as well, with identical results. [Test](../native/resident_custody/tests/full_resident_house_move.rs) · [Raw outputs](../research/w15_resident_house_move/bench.log)

## The Obend latch is the custody gate

[SOURCE] `stepBeltLatch` reads 14 state words and 19 request words. Status codes are 0 for accepted and 1–6 for genesis mismatch, stale parent, non-increasing epoch, parent fork, policy drift and missing acknowledgment. The checks run in that order. Acceptance stores `nextEpoch, nextDigest` over words 5–9 from one snapshot of the request. `obend/lean/Obend/Lower/Pancake/BeltLatch.lean:50,67,71,96,102` at Obend `25dd6789`, unchanged at `3543a3b6`. Its theorems fix the return value and memory (`:176`), state preservation on refusal (`:206`), the frame (`:245`) and parent consumption (`:272`).

| Words | State (`readState`) | Request (`readRequest`) |
|---|---|---|
| 0 | initialized = 1 | genesis limbs 0–3 |
| 1–4 | genesis limbs | — |
| 4 | — | parent epoch |
| 5 | epoch | next epoch |
| 6–9 | digest limbs | parent digest limbs |
| 10–13 | policy limbs | next digest limbs |
| 14–17 | — | policy limbs |
| 18 | — | persistAck |

[DERIVED] A 32-byte digest enters the ABI as four little-endian limbs, limb *i* = bytes 8*i*..8*i*+8. The native driver reads and writes little-endian words, so on x86-64 the four words' memory image is the digest. A custody head enters as genesis = `genesis_id`, epoch, digest = `head_root(head)` and policy = `policy_hash`. `head_root` is the existing parent-commitment hash, so the digest commits to the whole head, including the world root `state_commitment`. A child's request carries `parent_commitment` as its parent digest. [ABI](../native/resident_custody/src/obend_latch_abi.rs) · [Mapping](../native/resident_custody/src/custody_mesh.rs)

[DERIVED] Each custodian holds its 14 words in memory, provisioned from its WAL head at start. A proposal is first probed against them. Because the kernel reads `nextDigest` only to install it, the probe refuses exactly where the child's own request will. After the WAL write, the real step runs with `persistAck` set to that write's outcome. The qsag kernel still decides idempotent replay, and both kernels must agree as follows:

| Custodian situation | qsag `bind` | Obend `stepBeltLatch` |
|---|---|---|
| fresh child of the installed head, WAL durable | `Fresh` | 0 accepted |
| fresh child, WAL write failed | `WalPersistFailed`, poisoned | 6 missing ack, state unchanged |
| exact replay of the installed transition | `Replay` | 2 stale parent; installed head's parent is the grant's |
| competing child of a consumed parent | `EpochAlreadyBound` / `EpochConsumed` | 2 stale parent |
| child of a head at the installed epoch but not equal to it | not reached | 4 parent fork |
| foreign genesis or drifted policy | not reached | 1 or 5 |

Any other pairing is a refusal or an exit. A vote is the custodian's signature over the exact 152-byte Obend request record for its head with `persistAck = 1`. Every verifier rebuilds that record from the head, so a vote over any other acknowledgment does not verify.

[EXECUTED] Obend's checked-in `beltLatch.pnk` and `beltLatch.c` were compiled on hbox with stock CakeML, as the driver's header says. The ELF's SHA-256 was `1aa9a160…2f19`; the Wave 14 audit's was `c6391681…8195` [INFERRED: static libc and build ID differ]. All 4,153 records gave the same status and the same 14 state and 19 request words in Rust and natively. They were the 21 vectors of `PancakeBeltLatchTest.lean:39`, all 132 single-word mutations of an accepted pair, and 4,000 pseudorandom pairs. Every status was reached; the counts for codes 0–6 were 911, 1,183, 194, 1,013, 440, 315 and 97. The ELF's own loop ran at 4.79–5.17 ns per accepted call on CPU 6 at load 9.9. [Parity test](../native/resident_custody/src/obend_latch_abi.rs)

[DERIVED] `persistAck` now means exactly that the WAL record is durable. Recovery reads only `epoch.wal` and rewrites `checkpoint` from it, so the checkpoint is written after the vote has been sent. A failed checkpoint therefore no longer counts as a failed persist. The crash test's `post` boundary moved with the checkpoint, and `wal` still covers "durable but unvoted". [Crash test](../native/resident_custody/tests/resident_house_move_and_cshake_open.rs)

[EXECUTED] Quorum contact stays sequential in roster order. With concurrent contact the crash test failed with a boundary timeout. [DERIVED] Its interrupted Learn bound custodians 1 and 2 while custodian 0 sat at its pre-WAL barrier, so B's Migrate was fenced at both and the mesh wedged. In order, racing proposals meet first at custodian 0.

## The package

| Part | Contents | Bytes in the measured run |
|---|---|---:|
| `seat_receipt` | DreggNet v1 receipt JSON as A sealed it | 3,155–3,168 |
| `parent` | A's head and 3 votes | — |
| `command` | issuer's exact Migrate grant, A's exercise, B's acceptance | — |
| `succession` | B's head and 3 votes over its Obend record | — |
| `header` | W0 leaf, statement, proof | proof 88,480–90,000; bound 90,880 |
| total, bincode | | 93,306–94,816 |

[SOURCE] The DreggNet types are `SeatTransfer { source_operator_id, target_operator_id, transfer_epoch, asset, customer_seat, credits, unsettled_provisional_minor, reversal_deficit_minor, operator_reserve_cap_minor }`. They are sealed over `SHA-256("dreggnet-seat-handoff-v1\0" ‖ JSON)`, and `CreditBacking` has only `Provisional` and `Settled`. DreggNet `1d4fad6` `billing/src/handoff.rs:25,29,162`. The exporter refuses a seat holding any other payment state (`billing/src/reserve/store.rs:498`). The brief's `genesis_id`, `seat_id`, credit totals and `disputed` flag are not fields. Here genesis binds through `customer_seat = resident_seat(genesis_id)` and through the certified `seat_payment_claim = seat_root`. A disputed credit has no encoding.

[EXECUTED] [`seat_receipt.rs`](../native/resident_custody/src/seat_receipt.rs) seals DreggNet's own test fixture to the digest that DreggNet pins, `18a1d5bc…5174` (`billing/tests/handoff.rs:100–107`). The check order and refusal variants are DreggNet's. Billing and custody identities are the same Ed25519 keys. The verifier takes the receipt's issuer and target from the parent and successor heads.

[DERIVED] `state_commitment` is now a two-leaf world trie in the existing `trie_opening` format. The W0 cell is the 8 GDN fast weights, with its own blind. The journal cell has this layout:

| Bytes | Field | Disclosed |
|---|---|---|
| 0–23 | `resident_identity(genesis_id, policy_hash)`, 192 bits | yes |
| 24–31 | journal cursor | yes |
| 32–47 | journaled counts: experienced, told, inferred, forgotten (u32 each) | yes |
| 48–63 | Tulip journal hash chain over (episode id, provenance, step) and forgets | no |

The header opening proves bytes 0–47 of the journal cell inside the world root with the branch-bound 64-party opening. The proof's Fiat–Shamir context includes the path and the W0 leaf. W0 appears only as that leaf, a commitment under a private blind. Custodians answer a `Header` request only for their current certified head and only to its operator. W0 projections now go through the same branch, so their releases are checked against the world root.

[DERIVED] [`Follower`](../native/resident_custody/src/house_move.rs) is a public log's own Obend latch, provisioned at genesis and stepped once per certified succession. A certificate is checked against it before any signature. A package additionally checks, in order:

1. the succession extends the packaged parent, and both quorums verify;
2. the certified change is this Migrate, naming B and the seat claim, and is signed by issuer, A and B;
3. the receipt passes DreggNet's rules with A as issuer and B as target;
4. `seat_root` is the certified claim and the seat is the resident's own;
5. world root, cursor and exposure ledger are unchanged by the move;
6. the header opening verifies.

The log's durable write is the final step's `persistAck`. A failed write leaves the latch unchanged. [`resident_house_move`](../native/resident_custody/src/bin/resident_house_move.rs) is that log as a process: `init`, `follow`, `admit`.

## Measurements

| Machine and storage | Load | Native latch | N | Quorum succession | Header prove + verify | Log admits | A fenced | **Total, median** |
|---|---|---|---:|---:|---:|---:|---:|---:|
| hbox, ext4 | 4.6–5.8 | off | 11 | 46.6 | 47.9 | 16.6 | 1.3 | **112.8 ms** |
| hbox, ext4 | 9.2–9.4 | on | 7 | 49.8 | 86.0 | 23.8 | 4.2 | 165.3 ms |
| M2 Max, APFS | 6.9–11.7 | off | 11 | 91.9 | 63.0 | 27.2 | 2.3 | 185.2 ms |

[EXECUTED] Medians are taken per column, so the totals are separate medians. Sealing and offering took 0.31–0.63 ms at the median and B's receipt check 0.07–0.10 ms. hbox runs used `swarm-build` (`nice 15`, `CPUWeight=50`) on a shared box, where an OpenROAD job was using up to eight cores during some runs. Unit costs on hbox were one durable slot write (file plus directory fsync) at 3.07 ms median and the header proof at 50.1 ms prove and 12.6 ms verify with 22 workers. On the Mac a slot write with two `F_FULLFSYNC`s took 9.42 ms. [Raw outputs](../research/w15_resident_house_move/bench.log)

[DERIVED] Counted work on the honest move's path:

- **Durable slot writes before votes or acknowledgments.** Five: three custodian WALs in sequence, B's cursor and the log's state. Three more checkpoints trail the votes.
- **Ed25519.** The quorum phase has 30 verifications and 4 signatures; the whole timed path has 65 and 10. For scale, the fence phase (16 verifications and three custodian round trips) took 1.3 ms on hbox.
- **Proofs.** One header proof, verified twice: by B on receipt, then by the log.
- **Obend steps.** Twelve: a probe and a durable step at each custodian for the move, a probe at each for A's refused Learn, and three at the log.

The test host puts all three custodians, B and the log on one disk, so the trailing checkpoints still queue behind the next custodian's WAL flush. On the Mac a flush is a whole-drive `F_FULLFSYNC`, and that queueing is the Mac's quorum column.

[REFUTED: hbox `/tmp` timings] The harness first ran its mesh in hbox's `/tmp`, which is tmpfs. The 91.0 ms median there had free fsyncs and is not a durable result. `RESIDENT_MESH_DIR` moves the mesh. The brief's "14.37 ms" opening is the verify time in [the opening note](compact-bitsliced-cshake256-opening.md); its prove time is 67.2 ms with four workers on the M2 Max.

## Twelve attacks

| # | Attack | Construction | Refused by |
|---:|---|---|---|
| 1 | disputed seat receipt | receipt JSON with a `Disputed` backing, validly signed over those bytes; forged move bound to its root | DreggNet decode: `Malformed`, unknown variant |
| 2 | over-cap seat receipt | deficit = cap with 2,500 provisional; sealed by A; forged move bound to it | `UnbackedReserve` |
| 3 | wrong `target_operator` | receipt to a third key, Migrate to B bound to it | `WrongOperator` |
| 4 | parent-digest fork | equivocating quorum certifies a sibling of the logged parent and a move from it | log latch: 4 parent fork |
| 5 | policy-digest drift | successor head with another `policy_hash`, same genesis, forged votes | log latch: 5 policy drift |
| 6 | missing `persistAck` | custodian 0 with an injected WAL failure; log process with a read-only append file | custodian: Obend 6 logged, no vote, quorum refusal; log: exit 2, `MissingAck (code 6)`, latch file unchanged |
| 7 | tampered projection | one cursor byte of the header statement | opening: cut-and-choose transcript |
| 8 | replayed journal cursor | genuine header opening from the cursor-3 world root | opening: world membership |
| 9 | restored A, Learn | A's pre-move seat and cursor files restored | fenced at 3/3 custodians |
| 10 | restored A, Infer | same | fenced at 3/3 |
| 11 | restored A, Migrate | A offers to a third operator, who accepts | fenced at 3/3 |
| 12 | seat receipt transplant | valid A→B receipt for another resident's seat, with the honest move; and with a forged move bound to it | seat binding: root is not the certified claim; seat is not this resident's |

[EXECUTED] The forging helper reproduces the honest move's command and certificate byte for byte, so each forged package differs from the honest one only where its attack says. Attacks 4 and 5 and the forged moves in 1–3 and 12 hold every custodian key, beyond the `f = 1` assumption. An honest quorum never signs those heads; the log refuses them anyway. Replaying the admitted package to the log is refused as 2 stale parent.

## Tulip continuity

[SOURCE] A Tulip resident keeps a durable ledger of handled message ids. On restart it replays every message not in that ledger, `allgame/claude_resident/handled.py:28` and `zulip_loop.py:190,230` at `6170b9e`.

[EXECUTED] Here the ledger is the custodians' episode history, and a Tulip message id is the episode id. B journaled 104 in attack 6's retry, then replayed a backlog of 101–105. Custodians refused A's 101, 102 and 103 (101 forgotten) and B's own 104 as duplicate episodes at 3/3, and certified only 105. Forgotten episodes stay in the history as tombstones, so the forgotten one cannot be relearned. B's first W0 release equalled A's last release byte for byte, with the forgotten coordinate zero. The move carried A's 128 of 128 rank budget, so B's Infer after learning was refused by the cumulative exposure cap at 3/3.

[INFERRED] "No duplicate replies" holds for a resident that replies only after its Learn of the message is certified.

## Open

- [OPEN] One host, one disk. A deployment with a disk per custodian would take the trailing checkpoints off the critical path; this is not measured.
- [OPEN] B verifies the header and so does the log: about 12.6 ms each on hbox. B's check protects only B's liveness.
- [OPEN] Rust ABI parity with the Lean kernel is tested, not proved. The native differential runs one process per step: an ABI check, not a deployment mode.
- [OPEN] The provenance counts are public metadata in every package.
- [OPEN] This is a re-implementation of DreggNet v1. The golden digest catches drift on this side only.
- Proposed for `docs/VERDICTS.md` (not edited): *resident house move — DreggNet v1 receipt, Obend-latched 3-of-3 succession, cSHAKE256 journal header, public-log latch; 112.8 ms durable median on hbox ext4, 185.2 ms on M2 Max APFS; twelve cross-layer attacks refused; 4,153 Rust/CakeML latch comparisons identical.*

## Reproduce

```sh
cd native/resident_custody
RUSTFLAGS="-D warnings" cargo test --release --lib -- obend_latch_abi seat_receipt
RUSTFLAGS="-D warnings" cargo test --release --test full_resident_house_move -- full_resident_house_move --nocapture --test-threads=1
RUSTFLAGS="-D warnings" cargo test --release --test resident_house_move_and_cshake_open -- resident_house_move_and_crash_boundaries quorum_failover_and_grant_binding
# Linux, with a cake --pancake build of Obend's beltLatch.pnk (see bench.log for the build line):
OBEND_BELTLATCH_EXE=/path/beltLatch cargo test --release --lib -- native_beltlatch_parity --ignored --nocapture
OBEND_BELTLATCH_EXE=/path/beltLatch RESIDENT_MESH_DIR=/disk/dir cargo test --release --test full_resident_house_move -- --nocapture --test-threads=1
HOUSE_MOVE_RUNS=11 RESIDENT_MESH_DIR=/disk/dir cargo test --release --test full_resident_house_move -- house_move_latency --ignored --nocapture --test-threads=1
```
