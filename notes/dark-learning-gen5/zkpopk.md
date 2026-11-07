# dark-learning gen 5, lane zkpopk: the native batched Ligero ZKPoPK and the key ceremony

2026-11-07. Crate `native/dzkpopk/` (API in `src/lib.rs`). Reference: `research/dark_learning_2026_11_06/`
`zkpopk_ligero.py`, `keygen_ceremony.py` (decision doc §20.2, §21.1).

## What is ported

| module | what |
|---|---|
| `field.rs` | F_P, P = 2^255 - 2^39 + 1 (= `zkpopk_ligero.P`), Montgomery 4 x 64, canonical 32-byte BE codec |
| `ntt.rs` | radix-2 NTT, `Code` (k, th, coset D of size nD), negacyclic products in F_P[X]/(X^N+1) |
| `transcript.rs` | `Transcript` (absorb, `ints` by SHAKE-256 rejection sampling, `distinct`), `H`, salted Merkle tree |
| `statement.rs` | `KeyRegistry` (`valid`, `public`), `public_a`, `Statement` (validation, digest), `layout`, `weights`, `quotient_bounds`, `folds_for`, `shape`, `proof_bytes`, `batch_proof_bits` |
| `proof.rs` | `prove` / `prove_with` (rayon over rows, columns and limbs), `verify` / `verify_opts`, `simulate_legacy`; the forgers' `Cheat` (values1, digits1/2, K, raw) |
| `ceremony.rs` | `Ceremony` (commit, reveal, seed, transcript, key_seed, context, register), `Custodian` (commitment, make_key), `run_ceremony` |
| `gen.rs`, `vectors.rs` | `keygen`, `encrypt_sk`, `encrypt_pk` draw for draw with `pycompat::PyRandom`; the harness's test instances |
| `src/bin/dzkpopk.rs` | CLI: `vectors`, `verify`, `ceremony`, `bench`, `counts` |

All three statement kinds ("sk", "pk", "key"), both profiles (`T_LEDGER = 309`, 3 folds; `T_DEMO = 97`, 1 fold).

Two places compute the same field values by a different (faster) route; both are exact identities, and the bit-exact
proofs and cross-verification below exercise them:
- **Folds.** Python builds each (fold, prime) constraint's exact coefficient vectors and then the lambda-combination
  mod P. Native forms the combination directly: comb_s = sum_i adj(a_i) * (sum_f lam rho) + t sum_ij adj(c1_ij) *
  (sum_f lam rho), one transform-domain product per (prime, ciphertext) instead of per (fold, prime, ciphertext).
  The prover's exact quotient numerators use <adj(c) rho, s> = <rho, c s> over Z, with c s computed exactly in F_P
  (|c s| <= N 2^61 |s|max < P/2, lifted centered; refused if the bound fails) and a wrapping 256-bit accumulator
  (exact for in-range witnesses: |total| <= B < P/2 by `quotient_bounds`); forgers' out-of-range values go through
  BigInt.
- **Column linear test.** Python evaluates <alpha_r, Lagrange basis at x> per column (T rows x k). Native encodes each
  alpha row (interp then evaluate on D) once and reads the T opened columns: the same value, interp(alpha_r)(x).

Deterministic hook (TEST ONLY; default behaviour unchanged): `DL_DETERMINISTIC=<seed>` makes `zkpopk_ligero.prove`
draw masks, row randomness and salts from `random.Random("dl-zkpopk|<seed>|prove|<statement digest hex>")` (salts:
`getrandbits(256).to_bytes(32, "little")`), and `keygen_ceremony.Custodian` draw (r, salt, s, e) from
`random.Random("dl-keygen|<seed>|custodian|<i>")`. Native mirrors it with `ProveOpts::det_seed` and
`Custodian::new(i, Some(seed))`; the CLI reads the same env var. Without the variable both files take the `secrets`
path exactly as before (`python_default_is_still_random` checks two unseeded harness proofs differ).

## Bit-exact evidence

[EXECUTED] Mac, N = 16, three 61-bit primes, T = 309 (`cargo test --release -p dzkpopk --test vs_python -- --nocapture`,
3 passed, 23.5 s). Statements built natively from `random.Random(N*1000+M)` exactly as `run_zkpopk_ligero.sk_batch`
(3 sk cts: two forward layouts, one transpose) plus 2 pk cts under a joint key and a key statement:

| kind | bytes (= formula) | sha256 (Python = native, seed `vs-python-1`) | first differing offset |
|---|---:|---|---|
| sk | 477,440 | `4f1fba9f...f967f45b` | none |
| pk | 467,552 | `2fc40715...6f99df4e9` | none |
| key | 386,336 | `17d9b2b6...dabb4c2` | none |

Per kind: native accepts the Python proof; Python accepts a fresh (OS-random) native proof; one flipped byte is
refused by both (Merkle path); a native proof under another seed differs from Python's at offset 0 (the comparison can
fail). Ceremony (`ceremony_bit_exact`): seed, transcript, the 3 commitments, the 3 key-proof digests and the 3 b
vectors identical; another seed changes them.

[EXECUTED] dregg-forge, deployed ring N = 16384, four 61-bit primes, M = 2 (2 sk cts forward + transpose, 1 pk ct,
key), T = 309, seed `gen5-deployed` (`/srv/lanes/dl-gen5-zkpopk/deployed.sh`, log `deployed.log`):

| kind | bytes (= formula) | sha256 (both) | Python prove | native prove / verify | cross-verify | flipped byte |
|---|---:|---|---:|---:|---|---|
| sk | 1,743,040 | `bc672ac5...06514487` | 38.9 s | 0.36 s / 0.12 s | both accept | both refuse (Merkle path, root 1) |
| pk | 1,535,392 | `718d2a8b...028d26a6` | 28.0 s | 0.23 s / 0.11 s | both accept | both refuse |
| key | 1,257,152 | `6b34a5bb...1fe05b55` | 14.9 s | 0.12 s / 0.07 s | both accept | both refuse |

`cmp` of the two files reports identical for all three; the statement digests printed by both sides match too.

## Attack table, natively

[EXECUTED] `cargo test --release -p dzkpopk --test attacks -- --nocapture`: 31 rows, every verdict AND reason string
equal to `zkpopk_ligero_results_N16_L3_M3.json`, plus the recipient gate (3 products after accept, 0 on the forged
batch). Rows: honest sk; stale context x2, other recipient set, replay into the transpose, other custodian's key
(linear test); a = 1 (registry check); b random with forged e_pk (quadratic); mixed limbs (linear); error 9 in a
non-binary digit (quadratic) / claimed 8 (linear); plaintext off the layout (linear); changed w (Merkle path root 1),
q (linear), p (quadratic), column value, salt (Merkle), root 1, root 2 (linear); truncated, trailing byte (length);
noncanonical element (codec); FS falsifier: legacy verifier ACCEPTS the simulated proof of a junk ciphertext, real
verifier refuses (linear); honest pk; pk e0 = 9 claimed 8 (linear); five-prime Q of 305 bits (length); a 17-bit limb
and Q < 17 t (registry invalid).
Differences from the harness rows, by type: primes are `u64`, so the 256-bit "prime" of the Codex-trace rows is
unrepresentable; the native rows use a 62-bit prime just above the profile (a cheat proof of a false statement, and
arbitrary bytes): both refused, "key registry invalid". `verify(None)` has no native analogue.

## Performance (dregg-forge, 16 vCPU, nice 15, load average 5-10 from other tenants during the run)

[EXECUTED] `dzkpopk bench sk N L M S T 2` (`/srv/lanes/dl-gen5-zkpopk/bench.sh`, `bench.log`); every proof's bytes
= formula, every verify Ok; second rep shown.

| batch | T | bytes | prove | verify | Python (one core, §20.0) |
|---|---:|---:|---:|---:|---:|
| **N = 8192, L = 3, d = 4096 forward call, 64 cts x 64 slots** | 309 | 4,826,464 (38.61 Mbit) | **2.59 s** (16 thr), 21.4 s (1 thr) | **0.92 s** (16), 9.4 s (1) | 417 s / 217 s |
| N = 8192, L = 3, transpose call, 32 x 128 | 309 | 3,683,840 | 1.38 s | 0.49 s | |
| **N = 16384, L = 4, forward call, 64 x 64** (ledger ring) | 309 | 6,448,096 (51.58 Mbit) | **4.84 s** | **1.85 s** | |
| N = 16384, L = 4, transpose call, 16 x 256 | 309 | 3,753,056 | 1.51 s | 0.55 s | |
| N = 8192, L = 3, forward, 64 x 64 | 97 | 2,552,320 | 2.43 s | 0.81 s | |
| N = 16384, L = 4, forward, 64 x 64 | 97 | 3,567,328 | 4.87 s | 1.64 s | |
| key proof, N = 8192 / 16384 | 309 | 980,288 / 1,257,152 | 0.13 / 0.19 s | 0.05 / 0.08 s | |

One core, native vs Python: 19.5x prove, 23x verify; 16 threads add 8-10x (shared box).

**Per step at d = 4096** [DERIVED from the rows above; batches from `zkpopk_counts.mpc_batches`: per custodian 4
calls of 64 x 64 (2 forward matvec, 2 outer) and 1 transpose call; 3 custodians = 15 proofs, each verified by 2]:

| ring, T = 309 | per custodian: prove its 5 | per custodian: verify the other two's 10 | step wall time (custodians in parallel, own 16-core box) |
|---|---:|---:|---:|
| N = 8192, L = 3 | 4 x 2.59 + 1.38 = 11.7 s | 2 x (4 x 0.92 + 0.49) = 8.3 s | about 20 s |
| N = 16384, L = 4 | 4 x 4.84 + 1.51 = 20.9 s | 2 x (4 x 1.85 + 0.55) = 15.9 s | about 37 s |

Proving and verifying are not on the critical path together in the schedule only if a recipient can verify while
the next batch is proved; the figures above serialize them. Totals over all three custodians (one machine-equivalent):
3 x (11.7 + 8.3) = 60 s at N = 8192; 3 x (20.9 + 15.9) = 110 s at N = 16384. At T = 97 the forward batch costs the
same prove time (the row count doubles as k halves) and about 10% less verify.

## What I found in the Python

Nothing wrong in the relation, transcript order or codec: native and harness agree byte for byte on every proof
above, and every attack row is refused by the same check. Observations:
- The harness verifier's per-column linear test is O(T x rows x k) field multiplications; that is most of its 217 s
  at d = 4096. Evaluating interp(alpha_r) on D once per row is exact and about T/lg(nD) times cheaper; worth porting
  back if the harness keeps being run at full size.
- `prove(..., rng=)` ignores its `rng` (deliberately, since the review); the parameter could go.
- §20.2's table (186,848 B at N = 16) predates the ledger profile; at T = 309 the N = 16 sk batch is 477,440 B.

## Review

[EXECUTED] `codex exec -m gpt-6-astra --sandbox read-only` (output `scratchpad/dl-gen5/zkpopk/codex-review-1.*`):
withheld ("flagged for possible cybersecurity risk"); its visible trace read the verifier and said the optimized linear
checks "appear algebraically consistent so far", no finding. An independent Claude (Opus) review was run instead,
briefed with the code and the questions only. It ran the attacks and vs_python tests, 3,000 mutated honest proofs
(bit flips, 0xff words: none accepted, none panicked), and canonical JSON against Python on control, DEL, U+2028,
astral and non-ASCII-key strings and a 2^300 integer (identical bytes). It found no accept-what-Python-refuses on
a statement built by `Statement::new`, and checked sound: Montgomery arithmetic and constants, from_be32, the
transcript limits and state chain, `combine` vs linear_system + alpha_beta, the coset linear test, verify's order
and bounds, `valid`, digest/public_a/quotient_bounds, W256 exactness, prover hiding randomness, the ceremony.
Its findings, all fixed (regression `attacks::review_regressions`):
- **Stale digest** (defect, borderline break): `Statement`'s fields were public and its digest cached, so a caller
  who changed `context` after `new` verified an old proof under the new context (Python recomputes the digest).
  Fields are private now, with getters: a statement is immutable once built.
- **Panic on a malformed BigPoly**: `nl = 0` divided by zero (reachable through `Ceremony::register` with a
  custodian's b); a ragged limb vector was silently truncated. Fields private, `BigPoly::from_limbs` refuses both.
- N above 2^31 passed `valid()` and then hit an assert in the NTT; the profile now caps N at 2^31.
- Nits kept: commit length counts bytes (Python: characters; either way the commit cannot be opened);
  `Json::from_serde` refuses integers above u64 (fails closed); `ProveOpts::det_seed` is an ordinary argument,
  documented as test only (a seeded proof is not zero knowledge).

## Fixed during the port

- A deadlock: rayon `par_iter` inside `OnceLock::get_or_init` (residue caches). A worker that steals a task
  re-entering the same initializer blocks forever (seen: test at 0% CPU). Initializers are sequential now.

## Open

- [OPEN] The crate takes ciphertexts as canonical integers (`BigPoly`) or residues (`BigPoly::from_rns`, CRT); if
  darkstep keeps RNS form end to end, a residue-native `Statement` would skip the CRT for the digest only.
- [OPEN] The prover holds every encoded row (about 1.4 GB at N = 16384, 64 cts); streaming rows into the Merkle
  leaves would cut that if three custodians share a box.

## The gate in the native custodians (darkstep `--gate T`)

Built 2026-11-07 (`native/darkstep/src/gate.rs`, `he.rs::swap_cts`, `node.rs`; reference
`research/dark_learning_2026_11_06/native_ref_gated.py`).
- **Keys.** With `--gate T` the three custodians run the ceremony over their mesh (CTRL): commit, reveal, seed,
  `make_key` (b_j and its key proof), and every custodian registers all three keys
  (`Ceremony::register` verifies each key proof). The HE keys are the ceremony's (`OwnKey::from_ceremony` =
  `keygen_ceremony.CeremonyKey`: s_j, pk = (b_j, a_j = public_a(seed/j)), encryption coins from
  random.Random(100 + j)).
- **Gate.** In every HE call each sender proves its batch: one `dzkpopk` "sk" proof per (sender, call), with
  context ["dl-he-batch", "model", 0, 0, kind, call, transpose, sender] and the call's layout slots. The proof is
  sent on HE_CT after the ciphertexts. Each recipient verifies against the sender's REGISTERED key and the context
  and slots it computes itself, before any ptxct. The three then exchange verdicts on CTRL; any refusal aborts the
  step for all three with one reason (the first refusal in (sender, recipient) order).
- **Ungated path unchanged.** Without `--gate`, `vs_reference` d64_n4096 and attacks_refused still pass.
- **Determinism is test-only.** `ProveOpts::det_seed`, `Custodian::new_det` and `run_ceremony_det` exist only
  under the cargo feature `test-det` (darkstep `test-det` enables it). A custodian build cannot seed a proof, and
  `DL_DETERMINISTIC` is refused without the feature.

[EXECUTED] Bit-exact, Mac, N = 4096, L = 3, F = 118, d = 64, T = 309, seed g1
(`cargo test --release -p darkstep --features test-det --test vs_reference_gated -- --nocapture`, 2 passed):
- transcript, all three share digests and sigmas: equal to the reference, and to the ungated reference (the gate
  does not change the step's outputs);
- ceremony seed and all three b_j: equal;
- all 15 batch proofs (5 calls x 3 senders): sha256 equal.
- Negative control `--attack zk_off_layout:0`: sender 0's first matvec batch has 12345 at coefficient 64 with a
  forged proof. All three custodians abort with the reference's reason, "ZKPoPK gate: custodian 1 refused custodian
  0's batch (mv call 1): linear test: the folded limb equations do not hold". There are no matvec returns natively,
  and the reference made 0 products.
- Python reference: 642 s for the step, 532 s of it in the gate.
- [EXECUTED] Ledger profile, N = 16384, L = 4, F = 175, d = 64 (`gated_d64_ledger`): the same equalities hold
  (step digests, ceremony seed and keys, all 15 proof hashes). The Python reference took 2,952 s, 1,873 s of it in
  the gate.

**Low-memory prover.** `ProveOpts::low_memory` re-encodes the round-1 rows on each pass (commit with streamed
column hashes, accumulate, open columns) instead of keeping the m1 x nD table. Same bytes:
`vs_python::n16_bit_exact_and_cross_verified` checks it against Python, and
`low_memory_equals_stored_many_chunks` (N = 4096, 29-51 rows) against the stored prover. Forge, 64 x 64 batch at
N = 16384: prove 8.08 s vs 5.34 s stored; verify the same.
- Why it is needed: `darkstep local` puts three custodians in one 12 GB job, and the ungated d = 4096 step alone
  peaks at 11 GB. With three stored provers at once the gated step was OOM-killed twice.
- Co-located custodians therefore prove low-memory and take turns on one in-process lock for proving and
  verifying. The lock wait is reported apart; in a deployment each custodian is its own process and the lock is
  uncontended.

[EXECUTED] **The gated d = 4096 step** on dregg-forge: N = 16384, L = 4, F = 175, T = 309, three custodians in one
process, 16 vCPU, nice 15, `/srv/lanes/dl-gen5-zkpopk/step4096b.sh`. Same binary, back to back:

| | step (wall) | matvec z1 / z2 / b | outer G2 / G1 | memory peak |
|---|---:|---:|---:|---:|
| ungated | 50.0 s (54.5 s with deal) | 4.0 / 3.6 / 3.2 | 18.9 / 17.9 | 11 GB |
| **gated** | **198.3 s** (203.5 s) | 38.1 / 37.8 / 13.7 | 52.2 / 54.1 | 11.4 GB |

- Both runs ACCEPT, refines_spec true, the same transcript (`081b142f...`).
- Per custodian: prove 31.5-34.6 s for its 5 batches, verify 16.7-17.4 s for the other two's 10, ceremony 0.8 s,
  proof bytes sent 59.1 MB (each proof goes to two recipients).
- The 148 s of overhead is the three custodians' ZK work run one after another through the lock:
  3 x (33 + 17) = 150 s.

**Separate machines.** [DERIVED] With one machine per custodian (stored prover, no lock), a custodian adds about
4 x 5.3 + 1.6 = 22.8 s of proving plus 2 x (4 x 2.0 + 0.55) = 17.1 s of verifying, about 40 s, to the 50 s step
(about 90 s), because the ZK work is on the critical path of each call. This figure is derived from
`dzkpopk bench` rows and has not been measured as a 3-machine run. Two things would hide part of it: verifying one
sender's batch while proving one's own, and starting to verify the first batch as it arrives.

## Run plan: the gated d = 4096 step as deployed (three `darkstep party` processes, forge + bb2) [EXECUTED below]

Handed on: the lane stopped here, near its context limit. Facts were checked on 2026-11-07.
- **Machines.** forge is 178.105.4.114 (16 vCPU, 12 GB job cap). bb2 is 2.31.77.40 (32 cores, 122 GB, 96 GB
  available, 186 GB free on /). Both are on public networks; no firewall test has been run between them yet.

1. **Code.** dev at f8e6cd77 or later. Build `darkstep` WITHOUT `test-det`; this is a production build, so no seeds.
   - forge: `/srv/lanes/dl-gen5-zkpopk/native` is already synced and built (use `--offline` with the vendored
     tree in `/srv/lanes/dl-gen5-zkpopk/vendor`).
   - bb2: rsync the same `native/` (pycompat, dzkpopk, darkstep, a workspace Cargo.toml listing those three,
     Cargo.lock, `.cargo/config.toml` pointing at a copied `vendor/`) to `~/lanes/dl-gen5-zkpopk/`, then
     `nice -n 15 cargo build --release --offline -p darkstep`.
2. **Bytes per link.** `Net.sent_bytes` counts per tag only. Before the run, add a [peer][tag] counter in
   `darkstep/src/net.rs` (the writer thread knows its peer) and print it in result_i.json, so bytes per link can be
   reported. This is a small change, and the bit-exact tests must still pass.
3. **Deal.** On one box: `darkstep deal 16384 4 175 4096 DIR`. Copy `DIR/tape_i.bin` to custodian i's box, and
   `DIR/public.bin` to every box. Measure the tape sizes first; they may be GBs, so copy with rsync.
4. **Reachability.** Pick three ports. Test them both ways with a short `nc -l` / `nc` pair, each started with a
   PID file and stopped by it. If the ports are blocked, use ssh tunnels bound to 127.0.0.1, and say so: the link
   bytes are then measured inside the tunnel.
5. **Run.** Each custodian is its own process in its own scope, detached with a PID file. Bind on the box's own
   address, for this test only.
   - custodian 0 on forge:
     `nohup nice -n 15 systemd-run --scope -p MemoryMax=12G darkstep party 0 16384 4 175 4096 DIR
     178.105.4.114:P0 2.31.77.40:P1 2.31.77.40:P2 --gate 309 & echo $! > party0.pid`
   - custodians 1 and 2 on bb2: the same with `party 1` / `party 2`, each with its own memory cap (a user scope,
     or `prlimit --as`), each with its own PID file.
   - Do not run during forge's 10:00-11:00 UTC pause.
   - In party mode `colocated` is false, so the stored (fast) prover is used. The ZK lock is per process, so it is
     uncontended; `zk_lock_wait_seconds` in result_i.json answers whether the lock was needed (it should be about 0).
6. **Collect.** From each result_i.json: gate prove / verify / wait seconds, step_seconds, the phases, and bytes
   per tag and per link. Copy `shares_*.bin` to one box and run `darkstep reveal 16384 4 175 4096 DIR`, which
   must print refines_spec true.
7. **Teardown.** Stop every party and listener by its PID file. Delete only the files this run created.

Expected: about 90 s per step [DERIVED, see above]. The parties of one call wait on one another (verify before
returning), so the slowest sender sets the pace.

## Executed: the gated d = 4096 step as three custodian processes on forge + bb2 (lane xbox, 2026-11-07)

Code: darkstep at a996539e (dev): `Net::sent_per_peer` ([peer][tag] counter, frame headers included; `total_sent`
unchanged), `bytes_sent_to` in result_i.json, and in party mode `wall_seconds` and `peak_rss_kb` (VmHWM).
`cargo test --release -p darkstep --test vs_reference`: 6 passed; it now also checks that each party's links sum to
its per-tag totals (negative control: a writer that miscounts by one byte per frame fails `d8_n4096`).

Setup [EXECUTED]:
- Production build (no `test-det`), `cargo build --release --offline -p darkstep` on each box from the same sources
  and the zkpopk lane's vendored tree (`/srv/lanes/dl-gen5-xbox/native`, `~/lanes/dl-gen5-xbox/native` on bb2).
- `darkstep deal 16384 4 175 4096` on bb2: 8.8 s, 2.6 GB peak; tape_i.bin is 599 MB each, public.bin 269 MB.
  tape_0 and public relayed to forge through the Mac (`scp -3`, about 9 min, ~1.1 MB/s; sha256 equal both ends);
  tape_1 and tape_2 never left bb2.
- Reachability: `nc -l` on 178.105.4.114:47300 (forge) and 2.31.77.40:47301/47302 (bb2), each PID-filed with a 60 s
  timeout; connections succeeded both ways, so no tunnel was needed. Custodian sockets bound to those addresses.
- Custodian 0 on forge (`nice -n 15 systemd-run --scope -p MemoryMax=12G`, DS_THREADS=16); custodians 1 and 2 on bb2
  (`nice -n 15 systemd-run --user --scope -p MemoryMax=12G`, DS_THREADS=16 each). Each its own PID file
  (`party_<mode>_<i>.pid`); launcher `party.sh` in each lane dir.
- **Contention caveat.** bb2 was shared with other tenants' work (Lean builds, a 400%-CPU session, sort/emit jobs):
  load average 73 at the gated start and 105 at the ungated run, on 32 cores. forge was quiet (load ~1). bb2's
  seats ran at roughly a third of their uncontended speed; read the times below as a lower bound on what the shape
  can do, not a measurement of it. bb2 is EPYC Milan, forge EPYC Genoa.

Results [EXECUTED] (N = 16384, L = 4, F = 175, d = 4096, T = 309; result_i.json per custodian):

| | step | wall (process) | matvec z1 / z2 / b | outer G2 / G1 | peak RSS c0 / c1 / c2 |
|---|---:|---:|---:|---:|---:|
| ungated, cross-box | 153.4 s | 161-167 s | 11.4 / 12.8 / 9.6 | 63.4 / 51.1 | 3.8 / 4.3 / 4.3 GB |
| **gated, cross-box** | **301.7 s** | 311-319 s | 50.6 / 39.9 / 17.1 | 71.2 / 117.7 | 4.7 / 5.2 / 4.9 GB |
| gated, one process on forge (above) | 198.3 s | | 38.1 / 37.8 / 13.7 | 52.2 / 54.1 | 11.4 GB total |

- Gate per custodian (stored prover, `low_memory` false): c0 on forge prove 34.0 s / verify 27.5 s; c1 and c2 on
  bb2 prove 89.3 / 89.0 s, verify 73.6 / 73.1 s. Ceremony 2.3-3.6 s. `zk_lock_wait_seconds` about 2e-6 s on all
  three: the lock is uncontended in its own process, as expected. Proof bytes sent 59.1 MB per custodian.
- All three ACCEPT in both runs. Transcript `081b142f263bb0df...`, the same as the one-process runs. The per-party
  share digests of the gated run equal the ungated run's (c0 `fca75fa7...`, c1 `ced3eb70...`, c2 `d401317e...`):
  the gate does not change the step's outputs across boxes either.
- `darkstep reveal 16384 4 175 4096 run/gated` on bb2 (shares_0.bin relayed from forge): `{"refines_spec":true}` (6.5 s, 3.1 GB). This test-only
  reveal is the one place the three share files met on one box; the gen 6 deployment must not do this.

Bytes per link [EXECUTED] (each custodian's bytes sent to each peer; all six directed links measured equal):

| per directed link | open | he_ct | he_ret | ctrl | total |
|---|---:|---:|---:|---:|---:|
| ungated | 2.9 MB | 285.2 MB | 4,395.8 MB | 1.0 MB | 4,684.9 MB |
| gated | 2.9 MB | 314.8 MB | 4,395.8 MB | 1.8 MB | 4,715.2 MB |

- The proofs ride on HE_CT: +29.6 MB per link = 59.1 MB per custodian over two recipients. The ceremony adds 0.8 MB
  of CTRL per link. The gate costs 0.6% of the wire.
- HE returns are 93% of the wire. One gated step moves 6 x 4.715 GB = 28.3 GB (0.226 Tbit); 4 of the 6 directed
  links (18.9 GB) cross forge <-> bb2, the c1 <-> c2 pair is loopback on bb2.
- [DERIVED] At hbox's measured 39-44 Mbit/s uplink, one seat's 9.43 GB of sends per step take about 30 min; the
  he_ret stream is where to cut (modulus-switch the returns down to the primes decryption needs, seeded `a`).

What the numbers say [DERIVED]:
- The gate adds 148 s cross-box (301.7 vs 153.4), close to the one-process 148 s. It did not drop to the ~40 s the
  separate-machine estimate predicted because bb2's two seats proved and verified at ~2.6x forge's time (89 vs 34 s
  prove) on a box at load 73-105; the slowest sender sets the pace of every call.
- The ungated step was 3x slower cross-box than in one process (153 vs 50 s), mostly in outer G2/G1 (114 vs 37 s),
  the he_ret-heavy calls: bb2 contention plus 18.9 GB over the forge <-> bb2 link. Separating those two needs a run
  on an uncontended bb2 (or a third quiet box) [OPEN].
- Teardown: every party process exited on its own (verified by its PID file); the nc listeners exited after their
  one connection. Run directories kept for the gen 6 deploy lane: forge `/srv/lanes/dl-gen5-xbox/run/`, bb2
  `~/lanes/dl-gen5-xbox/run/`.
