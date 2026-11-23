# Wave 15 lane 6: resident house move

[EXECUTED] One A → B house move across three live custodian daemons. It took a median 112.8 ms on hbox with the mesh on ext4 (11 runs, load 4.6–5.8) and 185.2 ms on the M2 Max on APFS (11 runs, load 6.9–11.7). The hbox median covers the DreggNet v1 seat receipt, the Obend-latched quorum succession, the cSHAKE256 journal-header opening, the public log's durable admission, and A's restored snapshot fenced at 3/3. [Raw outputs](bench.log) · [Note](../../notes/resident-house-move-protocol-weld.md)

[EXECUTED] Every custodian transition probes and then steps Obend's `stepBeltLatch` word ABI, cross-checked against the qsag kernel by an explicit outcome table. Rust matched the CakeML ELF on 4,153 of 4,153 records: the 21 Lean vectors, 132 mutations and 4,000 pseudorandom pairs. With `OBEND_BELTLATCH_EXE` set, all 88 custodian steps of the end-to-end test also ran natively.

[EXECUTED] Twelve cross-layer attacks met their intended refusals: DreggNet `Malformed`, `UnbackedReserve` and `WrongOperator`; Obend `ParentFork` and `PolicyDrift`; `MissingAck` at a custodian and at the log process; opening transcript and world-membership failures; A fenced for Learn, Infer and Migrate; seat binding twice.

[EXECUTED] `seat_receipt.rs` reproduces DreggNet's pinned v1 digest `18a1d5bc…5174`. Votes sign the exact 152-byte Obend request record with `persistAck = 1`. The checkpoint is written after the vote; recovery reads only the WAL.

Files: `native/resident_custody/src/{obend_latch_abi,seat_receipt,house_move}.rs`, `src/bin/resident_house_move.rs`, `src/custody_mesh.rs` (latch gate, world trie, header request, votes), `tests/full_resident_house_move.rs`, `tests/common/mod.rs` (harness shared with the existing test).

hbox scratch, created by this lane: `/home/hbox/lanes/w15-l6-house-move/` (`beltlatch/` ELF build, `native/` source copy, `target/` 277 MB, `mesh/` empty).
