# Gen 5, proof lane: the native collaborative ZK proof and the untrusted-input verifier

Crate: `native/darkproof/` (CLI `darkproof check|rows|gen-check|bench`, test `tests/falsifiers.rs`).
Reference: `research/dark_learning_2026_11_06/{cozk,cosnark,cosnark_zk,cosnark_gates,cosnark_gates_zk,proofwire,owner_sig}.py`.
Vectors: `research/dark_learning_2026_11_06/darkproof_vectors.py`.

## What is built

- `ligero.rs`: cozk (collaborative Ligero over additive shares). `LigParty` is one custodian's state; openings,
  polynomial and scalar Beaver triples go through the transport.
- `pcs.rs`: the ZK share PCS (secret tails, one proximity mask row per life, salted leaves, life counter). The
  codeword is never stored: each leaf is hashed from its column, computed as dot products of the rows with the
  column point's powers (lazy u128 reduction); opened columns are recomputed.
- `spine.rs`, `middle.rs`: prove_zk / verify_zk and prove_middle_zk / verify_middle_zk, prover per party.
- `step.rs`: the verifier's symbolic replay of `mpc_fork.run_step` (RecEngine symbolic), numbering only the
  middle's atoms.
- `wire.rs`: the proofwire bundle codec and `verify_step`; `ledger.rs`: the durable ledger, lines identical to
  Python's `json.dumps`; `owner.rs`: the Lamport/Merkle owner signature.
- `spdz.rs`: a custodian's SPDZ view for the proof's Beaver products (batched, at most 2^19 products per round
  trip) and the MAC check with sigma commit-then-open.
- `net.rs`: the transport, one method `all_gather(Vec<u64>) -> Vec<Vec<u64>>`. `MemNet` (threads and channels)
  and, with `--features tcp`, `TcpNet` over darkstep's sockets (tag `net::PROOF`).
- `live.rs`: a single-process witness generator for the plain-SPDZ step (the program proofwire replays). It is
  not the custodian protocol, which is darkstep.
- `witness.rs`: loads darkproof_vectors.py's JSON witness, and `make_bundle` (three custodian threads).

**Python hook (TEST ONLY).** With `DL_DETERMINISTIC=<seed>` set, these come from
`random.Random("dl-proof|<seed>|...")` streams (`cosnark.det_rng`):
- PCS tails, mask rows and leaf salts (labelled by commitment, party and `H(share)`);
- the cozk party and dealer streams;
- owner commitments;
- `Owner()` seeds.

With the variable unset, the code paths are the old ones.

## Bit-exactness [EXECUTED]

`DL_DETERMINISTIC=7 python3 darkproof_vectors.py VEC d profile pw si`, then `darkproof check VEC <profile>_d<d>`
and `python3 darkproof_vectors.py verify VEC <tag>`:

| profile, d | step 1 (genesis) | step 2 (chained) | owner-signed step 1 | native verifies Python | Python verifies native | one flipped byte |
|---|---|---|---|---|---|---|
| demo, 4 | equal, sha256 784ebdd3… | equal, 250b5493… | — | accept | accept | refused by both |
| demo, 16 | equal, 81dc037c… | equal, bae30506… | equal, 3da15e8f… | accept | accept | refused by both |
| ledger, 4 | equal, 1d1eacf2… (28,306,548 B) | equal, 65cf7c5d… | equal, 9309878b… | accept | accept | refused by both |
| ledger, 16 | [OPEN] Python vectors still running | | | | | |
| demo / ledger, 64 | [OPEN] Python vectors running on bb2 | | | | | |

The comparison can fail. The first run of step 2 differed at byte offset 32 (a carried-commitment key bug), and
that was caught and fixed. `check` reports the sha256 and the first differing offset.

**Witness generator.** `darkproof gen-check` compares `live.rs` with the harness's dumped witness at d = 4. These
are equal: the public transcript, every party's middle atoms (shares and MAC shares), the dealer's MT state after
the step, the alpha shares and every wire. A flipped atom compares unequal (the negative control).

**Transport.** `DP_TCP=1 darkproof check VEC demo_d4` (`--features tcp`, three 127.0.0.1 listeners) gives
byte-identical bundles over darkstep's sockets.

## Refusal rows, native (`darkproof rows VECROWS ledger_d4`) [EXECUTED]

All 31 refusals and 4 acceptances match the harness's verdicts. Where Python logged a reason, the reason string
matches too: `proofwire_d4.log` covers every proofwire row.

- **§18 proofwire rows.**
  - Replay: binding mismatch.
  - Truncated / trailing bytes / non-canonical field element: parse.
  - Flips:
    - model id: binding;
    - root: parent;
    - prox: column challenge;
    - mid-blob: `middle: Merkle opening fails (b, custodian 2)`;
    - last byte: `Ligero: Merkle opening fails (group 25, custodian 2)`.
  - Non-UTF-8 model id: binding.
  - Step 3 patched to step 2: column challenge.
  - Another model id: binding.
  - Equivocation: expected step 3.
  - Restart: same head.
  - Stale parent: parent.
  - Third opening by honest custodians: `LifeExhausted: commitment W1 ...`.
- **§16 spine forgeries.** forge_W1n, forge_z1, forge_sumcheck and lie_in_u are refused by the Ligero linear test.
  The first violated constraints, read off the hidden witness, are §16's: rank-1 W1n; z1 first round; z1 final;
  PCS consistency W1n.
- **§16 middle forgeries.** Forged trunc/lookup openings and mask_out_of_range are refused by the linear batch.
  bad_triple and nonboolean_bit are refused by the zerocheck.
- **§18 signed input.**
  - x′ refused: spine binding constraint.
  - y′ refused: middle binding constraint.
  - Own key: owner signature.
  - Replayed signature: owner signature.
  - Honest steps 1 and 2: accepted.
- **§19 fs_public_falsifier.** The native attack hook steers d1 and W1n by 12,345 and shifts the dead opening after
  gamma, so that the middle's batch holds. The ledger REFUSES it with `spine: column challenge mismatch`: the
  public digest is bound in both proofs.
- **§19 lives_falsifier** (`cargo test --release -p darkproof --test falsifiers`).
  - An honest third opening is refused.
  - A forced third opening at T = 97 recovers the committed data by interpolation.
  - Two lives open fewer than W points.
- **leaf_salt_falsifier and zk_seed_falsifier: not applicable natively [DERIVED].** The native code has no
  unsalted-leaf mode and no public-seed mode: salts and tails come only from a party's secret stream (or the test
  hook). The Python falsifiers exercise legacy switches that the port never had.
- **Rotation.** Native `Ledger::rotate` refuses until the handover verifier is ported (codex finding 1; the
  coordinator is porting `handover.verify`). The old committee's step 3 against the new committee's roots is
  refused (parent).
- **Ledger interop.** The native ledger file (genesis, two steps, rotation) is reopened by Python's `Ledger`, and
  every line is `json.dumps`-identical.

## d = 4096 on dregg-forge [EXECUTED]

Command: `nice -n 15 systemd-run --scope -p MemoryMax=12G darkproof bench 4096 ledger`, with `-C target-cpu=native`,
16 vCPU, all three custodians on the one box over MemNet. Log: `/srv/lanes/dl-gen5-proof/bench4096b.log`.

| | step 1 (genesis) | step 2 (chained, W1/W2 carried) |
|---|---:|---:|
| prove, three custodians, one 16-core box | 247.4 s | 247.4 s |
| of which spine commitments (W1n, W2n + vectors, x3 parties) | 168.9 s | 166.5 s |
| of which middle commitments (P, A, B, C, y, x3) | 50.7 s | 52.1 s |
| middle zerocheck (1.67e7 Beaver products per party, round trips bounded at 2^19 products) | 12.3 s | 13.0 s |
| verify (untrusted bytes) | 12.7 s, accept | 12.5 s, accept |
| bundle bytes | 922,331,700 | 922,331,700 |

- **Sizes equal the formulas exactly.**
  - Spine: 155,072,604 bytes = 16,485,363 field elements + 724,176 hashes + 4,017 indices = **1,191.0 Mbit**.
  - Middle: 90,927,540 bytes = 8,619,603 field elements (indices included) + 687,087 hashes = **701.7 Mbit**.
  - Hidden rows: 712 (spine) and 441 (middle). Atoms 2,895,872 and Hadamard rows 2,260,992 equal
    `cosnark_gates.counts_formula(4096, S1=11, ...)`.
  - The same equality was checked at d = 64 (spine 18,884,172 B, middle 24,517,284 B).
- **The public transcript is 676 MB** of the 922 MB (84.5M opened values, the plain-matvec program). Python's
  2^24 cap would refuse it. The native verifier requires exactly the program's length, before reading.
- The step-1 genesis commitment of W1, W2 runs before the timed prove.
- **Peak RSS is 12.1 GB, at the scope cap.** This is all three parties plus both steps' witnesses in one process;
  one custodian alone holds about a third of it [DERIVED].
- **The cost is the codeword encoding [DERIVED].** It is dot products over 4098 x 4714 rows at 18,856 points per
  matrix, about 0.9 ns per multiply-accumulate per core under contention. A faster encoding is the lever, and it
  is [OPEN]. The evaluation points are 1..npts, fixed by bit-exactness with the harness, so an NTT domain would
  need a protocol change.
- **Beaver batching.** The middle zerocheck's products are one batch per round, chunked at 2^19 products, i.e.
  2^20 openings per exchange: 16 exchanges in round 1 and log2(2^22) = 22 rounds. The run is compute-bound, not
  round-trip-bound. The wire is 2.0e8 elements, as §16 says.

## Design notes and deviations

- **MAC-check coins.** They come from a SHA-256 chain over every opening (fixed only after the last broadcast),
  not from repr() of the frozen transcript. The coins are never part of a proof. Sigma is still committed before
  it is opened.
- **The spine's bg zerocheck.** Python re-centres its claim on 0 each round, a no-op whenever bg = b·g1. Natively
  it is not run, because it would open hidden round sums. Codex checked 320 honest rounds: every adjustment was
  zero.
- **The ideal dealer.** In-process every party replays the dealer stream and keeps its own share. This is faithful
  arithmetic, not the dealer's secrecy boundary (codex). Real tapes come from darkstep/darkprep (below).
- **Step program pinning.** Ledgers above d = 1024 use the §12 shifts (11, 19), (4, 8), (14, 19). The genesis
  record carries `"program"` when it is not the harness's (5, 13), (4, 8), (8, 13); Python ledgers carry none.
- **Model ids.** Ledgers accept 1..64 printable ASCII characters only: the context is hashed as a Python repr,
  which is ported exactly for ASCII.

## Cross-model review

`codex exec -m gpt-6-astra --sandbox read-only` ran (not withheld); its output is at
`scratchpad/dl-gen5/proof/codex-review-darkproof-1.txt`. It found no skipped check and no missing Fiat-Shamir
binding. Its findings and what was done with each:
1. **High.** Rotation accepted roots without a handover proof. Fixed: rotation now refuses until handover.verify is
   ported.
2. **High.** An unreadable owner counter reset to leaf 0. Fixed: only a missing file starts at 0.
3. **Medium.** The public-transcript cap. Fixed: the exact program length is required before reading.
4. **Medium.** The wide program was implied by d alone. Fixed: it is pinned in genesis.
5. **Medium.** A malformed ledger leaf was ignored. Fixed: it must be an integer, increasing and in the tree when
   an owner key is set, and null otherwise.
6. **Low.** The Unicode repr was incomplete. Fixed: model ids are restricted to ASCII.

## [OPEN] / next

- The deployed step uses darkstep's HE matvec and HE outer: their openings replace the d² matvec and outer
  openings. The coordinator and I agreed the HE helpers' openings (he_auth, Freivalds muls, he_outer_commit and
  check) are bound through the public digest only and are not middle constraints. I write the Python reference
  for that (RecEngine symbolic over HEMatvec/HEOuter, plus the proofwire replay) next, then port it.
- Consume `darkstep::step::StepOut.record` (ProofRecord) and tape-sourced proof triples
  (`spine::beaver_count(d) = 13(d-1)` plus `middle::beaver_count(n_had) = 4(plen(n_had)-1)`, asserted against
  what the prover draws). Check darkstep's Trhb tape atoms against RecEngine.
- A faster codeword encoding.
