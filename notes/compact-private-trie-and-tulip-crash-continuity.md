# Private trie openings and Tulip delivery across a paid house move

[EXECUTED] On an Apple M2 Max, a 260-bit private code-field opening used **19,222,296 proof bytes** and **60,948,480 bytes peak RSS**. The verifier took 603 ms. The recorded ZKBoo baseline at `691c42f6` used 278,549,100 proof bytes and verified in 1,585 ms. The new prover took longer in this run, 5,936 ms against 3,907 ms. Each proof used a fresh challenge. [Isolated test-binary timings](../research/trie_tulip/audit-prefixes.log) · [Historical baseline](../research/trie_tulip/baseline-old-engine.log)

[EXECUTED] A local Tulip broker delivered exactly one reply to each of messages 101–104 after a real operator SIGKILL, a broker restart from disk, and a paid A-to-B move. All three custodians refused the restarted A. [Crash results](../research/trie_tulip/audit-crashes.log)

## Opening measurements

[EXECUTED] Each row is one fresh release-mode test process with 12 Rayon workers. The fixture constructs the statement and private reveal before timing. The prove interval covers extended-witness generation, the residual check and proof construction. Verify takes the public plan and proof bytes. Peak RSS covers the entire test process, including its worker pool. The 8- and 16-bit cases use explicit test prefixes. The deployed field mapping produces depths 0, 3 and 260. [Fixture and timing boundaries](../native/resident_custody/src/trie_opening/deployed.rs) · [Measurement command](../research/trie_tulip/measure-prefixes.sh)

| Reader prefix | Answer | Proof bytes | Prove ms | Verify ms | Peak RSS bytes |
|---|---|---:|---:|---:|---:|
| 260 bits | One code entry | 19,222,296 | 5,935.506 | 603.245 | 60,948,480 |
| 8 bits | One member | 673,800 | 209.685 | 31.548 | 10,207,232 |
| 8 bits | Empty, private singleton | 750,368 | 262.579 | 30.781 | 10,240,000 |
| 16 bits | One member | 1,261,960 | 382.241 | 46.685 | 11,780,096 |
| 16 bits | Empty, private singleton | 1,339,968 | 420.021 | 47.954 | 11,714,560 |

[DERIVED] With masked extended witness length $W$ and instance frontier size $F$, the proof occupies $96+80F+23(192+W)$ bytes. The frontier test constructs the maximum $F=109$. For the 260-bit plan, 8,424 input bytes and 103,348 committed words give $W=835{,}208$ and a maximum of **19,223,016 bytes**. The observed reduction was 14.49×. The 20 MB ceiling holds at every challenge for this fixture. A 15× reduction from the recorded baseline would require at most 18,569,940 bytes. [Shape and serializer](../native/resident_custody/src/kkw.rs) · [Frontier test](../native/resident_custody/src/cshake_selective_open.rs)

[REFUTED: under 400,000 bytes for the current one-member depth-8 circuit and opening format] The 23 online openings carry 23 copies of a 28,776-byte masked witness. Those copies alone occupy 661,848 bytes. The floor depends on this circuit and serialization. [Depth-8 shape](../research/trie_tulip/audit-prefixes.log)

[EXECUTED] The authenticated single-block cell gate produced four-worker medians of 85,312 bytes, 64.017 ms prove and 14.406 ms verify over nine trials. Earlier Mac and hbox measurements in this directory include an intermediate word-per-party evaluator. The 459 ms Mac and 605 ms hbox full-prefix verify times belong to that evaluator. [Current cell gate](../research/trie_tulip/audit-cell.log) · [Intermediate Mac run](../research/trie_tulip/mac-final-trie.log) · [Intermediate hbox run](../research/trie_tulip/hbox-bench.log)

## Circuit, transcript and soundness

[SOURCE] The deployed prover packs the secret, inner root and padded reveals, then calls `kkw::prove`. The verifier reconstructs the plan from the public statement and calls `kkw::verify`. Cell and framed openings use the same engine. Previously serialized opening proofs require regeneration. The online evaluator transposes 64 party words into 64 bit planes. Bit $p$ in plane $z$ is party $p$’s share of wire bit $z$. Rotation permutes plane indices. Each AND contribution uses the public masked operands and the linear party shares. An inverse transpose supplies 64 individual residual words to the POLYVAL accumulators. [Deployed entry points](../native/resident_custody/src/trie_opening/deployed.rs) · [Online evaluator](../native/resident_custody/src/kkw/gates.rs) · [Cell entry points](../native/resident_custody/src/cshake_selective_open/framed.rs)

[DERIVED] The circuit checks the outer root, each subtree root, walk monotonicity and the outside-terminal condition. Every digest select commits its AND output. Paired Keccak rounds use 25 checkpoint words and two quadratic hints per row. The last pair of a squeeze needs only the first row. The public-root squeeze uses 388 committed words, a private squeeze uses 392, and a full permutation uses 420. [Trie equations](../native/resident_custody/src/trie_opening/deployed/mpc.rs) · [Keccak equations and exhaustive row test](../native/resident_custody/src/kkw/keccak.rs)

[EXECUTED] The row check agrees with all 32 five-bit inputs and four possible hint pairs. The separate hint search enumerated 1,023 nonzero quadratic forms and found no single quadratic hint sufficient for all five inverse coordinates in this representation. The bit-plane fingerprints agree with the scalar reference for every party on the tested cell, framing and trie shapes. Searching the Rust sources under `native/resident_custody` with `rg` found no `prove_mpc`, `verify_mpc`, `REPETITIONS`, legacy `struct View` or `trace_pack`. [Hint search](../research/trie_tulip/one_hint_search.py) · [Test output](../research/trie_tulip/audit-tests.log)

[SOURCE] The first Merkle root binds the masked witnesses and seed commitments before the engine derives two 128-bit POLYVAL keys. Each online party’s broadcast uses a position-bound private pad. The hidden party’s seed, pad and tape key stay behind its puncture. Offline instances reveal their tape seeds. Their masked-witness and broadcast commitments also use a private nonce from a separate random key. The serializer discloses nonces only for the 23 online instances. [Material derivation, transcript and opening parser](../native/resident_custody/src/kkw.rs)

[EXECUTED] The deployed tests accepted the two-member body answer and the empty answer with a private early singleton. They scanned the proof bytes for the secret, inner root, hidden content digest and a 32-byte hidden path substring. They rejected a version relabel and four invalid proofs generated past honest preflight: an omitted member, a selected leaf presented as an outside terminal, an inconsistent committed AND output, and the omitted member under the mixed 14-instance preprocessing strategy. The validly encoded AND case flips the last word of the clear extended witness before commitment. [Trie tests](../native/resident_custody/src/trie_opening/deployed.rs) · [Test output](../research/trie_tulip/audit-tests.log)

[DERIVED] For $M=640$, $N=64$, and $t=23$, the classical one-trial bound is $M L^2/2^{256}+\max_{0\le k\le t}\binom{t}{k}/(\binom{M}{k}N^{t-k})$. Here $L$ counts **residual blocks**, two 64-bit constraint words per block with a padded final word. The deployed 260-bit plan emits 103,361 words, hence $L=51{,}681$. The split calculation conditions on binding commitments and uniform independent challenges. [Ledger](../native/resident_custody/src/kkw.rs) · [Earlier derivation](compact-bitsliced-cshake256-opening.md)

[EXECUTED] Integer cross multiplication over all 24 splits gives $k=14$ and reduced escape probability $23/9748679111155310898117152759361193377792$. For that fraction $a/b$, the test checks $(2^{256}a+bML^2)2^{128}<b2^{256}$ with `BigUint`. It passes for the measured 260-bit plan and at the enforced limit of $2^{20}$ blocks. [Full-prefix run](../research/trie_tulip/audit-prefixes.log) · [Ledger test](../research/trie_tulip/audit-tests.log)

[OPEN] The integer bound does not settle adaptive Fiat–Shamir security or QROM security. Canary absence rules out the sampled literal disclosures. A simulation argument for this transcript’s witness hiding remains open.

## Durable replies and migration

[SOURCE] In allgame commit `bfe1761`, `claude_resident/tools/dispatch.py:275` sends the Zulip message. `claude_resident/resident.py:536–541` records the handled IDs after the response turn. `claude_resident/zulip_loop.py:230` consults the ledger on replay. AgentMail uses an idempotency header at `tools/agentmail_tools.py:72` and derives its send key at line 311. The integration fixture uses its own Unix-socket broker.

[SOURCE] The operator fsyncs the signed command and reply envelope before proposing a Learn. An appended `LearnWithReply` action binds the envelope digest while preserving earlier action discriminants and Learn encoding. The broker verifies the command, quorum certificate, frame identity and posting seat. The broker key is cSHAKE256 with customization `tulip.resident.outbox.v1` over genesis, little-endian episode ID and little-endian reply slot zero. It syncs each post before acknowledging it. Adoption checks the delivered stream prefix against broker receipts and requires pending envelopes to follow it in order. It installs the new seat fence durably before recording the adoption. Retrying the same signed handoff is idempotent. [Bridge and WAL](../native/resident_custody/src/tulip_bridge.rs) · [Custody action](../native/resident_custody/src/custody_mesh.rs)

[EXECUTED] The harness uses real custodian, broker, worker and paid-move processes. At the armed boundary it kills A through its owned `Child`, waits for Unix signal 9, and restarts the broker from its WAL. Before recovery, the test reads the installed epoch from each custodian’s disk. A recovers and signs an offer, B accepts, the public log admits the paid move, and B adopts. The following values were observed after message 103 interrupted A. [Test](../native/resident_custody/tests/tulip_crash_house_move.rs) · [Process and outcome log](../research/trie_tulip/audit-crashes.log)

| Kill point | Epoch on all three disks | Broker replies at restart | B’s result for 103 |
|---|---:|---|---|
| Before quorum, after reading 103 | 2 | 101, 102 | Fresh Learn and post |
| After quorum, before A’s seat cursor | 3 | 101, 102 | Recovered certificate, fresh post |
| After seat cursor, before outbox certificate | 3 | 101, 102 | Saved certificate, fresh post |
| After broker commit, before local acknowledgment | 3 | 101, 102, 103 | Original receipt |

[EXECUTED] In every case B posted 104 once. The public log reached B’s last certificate and its opened header showed four told episodes. A re-signed handoff with an altered 103 body failed the certified Learn digest check, as did the altered post at the broker. A repeated valid 103 returned the original receipt. All three custodians recorded Obend code 2 on the resurrected A’s Learn attempt. The final ordered broker log was exactly 101, 102, 103, 104. The post-run process scan found zero surviving fixture children and the fixture root was empty. The owner waits on each child and the controller joins the issuer thread. [Crash run](../research/trie_tulip/audit-crashes.log) · [Child owner](../native/resident_custody/tests/common/mod.rs)

[OPEN] Recovery assumes an intact quorum, broker disk, and source outbox. If the source withholds a certified pending reply, its successor can stall awaiting the certificate. These experiments leave physical erasure, quorum rollback and exactly-once delivery through a live Zulip service open.

## Reproduction

[EXECUTED] The audit ran on macOS 27.2.1 with rustc 1.98.0-nightly (91fe22da8). The release package suite passed 28 ordinary tests. Clippy passed for all targets of `resident_custody`. Running Clippy from the enclosing virtual workspace also selects unrelated crates. The checked tree reported failures in `pycompat`, `dlvault` and `qwen35audit`. [Suite](../research/trie_tulip/audit-tests.log) · [Package Clippy](../research/trie_tulip/audit-clippy.log) · [Workspace diagnostics excerpt](../research/trie_tulip/workspace-clippy.log)

```sh
# From repository root
sh research/trie_tulip/measure-prefixes.sh
cd native/resident_custody
RUSTFLAGS="-D warnings" cargo test --release -p resident_custody
cargo clippy --all-targets -- -D warnings
RUSTFLAGS="-D warnings" cargo test --release --test tulip_crash_house_move -- --nocapture
```

[DERIVED] Proposed verdict for the maintainer: the deployed private-trie relation shares the 64-party bit-sliced cell engine, with a 19,223,016-byte worst-case proof for the measured 260-bit plan. A local durable broker preserves one certified reply per episode in the four tested operator crash windows across a paid move.
