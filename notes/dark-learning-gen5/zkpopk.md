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
