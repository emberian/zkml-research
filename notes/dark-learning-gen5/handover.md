# Custody handover proof: bytes, a native verifier, the native ledger (gen 5, handover lane)

2026-11-06. Code: `research/dark_learning_2026_11_06/handover.py` (construction, `encode`/`decode`/`verify_bytes`),
`proofwire.py` `Ledger.rotate` (takes bytes), `run_handover.py`, `run_proofwire.py` (rotation row);
native `native/darkproof/src/handover.rs`, `src/ledger.rs` `Ledger::rotate`/`handover_context`,
`tests/handover_vs_python.rs`.

## The construction as built [SOURCE: handover.py]
- **Resharing.** Old custodian i splits its share s_i of each matrix into n_new uniform subshares that sum to s_i
  and sends sub_ij to new custodian j. New custodian j holds s'_j = sum_i sub_ij and authenticates it under its own
  MAC key (`auth_plain`). In the harness this happens in one process; erasure is not modelled in code [OPEN].
- **Statement.** The ledger head's roots are the old committee's commitment of W1, W2: the last step's child, a
  hiding share-tuple ZKPCS. The new committee commits s' afresh. Fiat-Shamir runs over ctx = ("handover", model,
  epoch_old, epoch_new, after_step, old set, new set) and all four root tuples, and gives one point r (2 log2 d
  coordinates) per matrix. A collaborative ZK Ligero among all n_old + n_new custodians then proves three things on
  four hidden row-combination vectors (old W1, new W1, old W2, new W2; ceil(W / 64) Ligero rows each):
  - evaluation consistency against each commitment's opened columns;
  - <u_old - u_new, eq(r_col)> = 0, that is W_old(r) = W_new(r). Schwartz-Zippel gives error 2 log2 d / p per matrix.

  No evaluation value is revealed. Each u row is shared by its own committee only (zero shares from the other
  committee), and every custodian draws Ligero hiding values.
- **Ledger.** `rotate(custodians, new_roots, bytes)` follows this order:
  1. empty or missing bytes are refused;
  2. decode against (d, n_old = |head custodians|, n_new = |custodians|, PARAMS), all supplied by the ledger;
  3. verify against the ledger's own ctx and head roots;
  4. compare the proof's new roots with the claimed ones;
  5. append `{"kind": "rotate", epoch, custodians, roots, "handover_proof": sha256(bytes)}`.

  The native line is byte-identical to Python's json.dumps line: the test compares whole ledger files.

## Lives [DERIVED]
Mask rows are split into LIVES = 2 blocks; each block is one proximity mask.
- **Old child commitment:** life 1 is its step's child opening (block 0). Life 2 is the handover (`base = block`,
  block 1; the verifier's PubShape uses base NMASK // LIVES). After the rotation it is never a parent again, because
  the ledger parent becomes the new roots. A third opening is refused by the custodians' counter (`LifeExhausted`,
  row "a third opening of the old child").
- **New commitment:** life 1 is the handover (block 0). Life 2 is the next step's parent opening (block 1, as every
  chained W).

So LIVES = 2 suffices; the third life anticipated in handover note §2e is not needed.

## The both-periods rule and how the code meets it [SOURCE: veil-pilot/VeilPilot/CustodyHandover.lean]
The Veil model's rule (`windowBoth := true`) is this: inside the handover window a held custodian counts against
BOTH committees' n - 1 budgets (`corruptOld`/`corruptNew` set both flags when `ph = during`), and a sender erases
its subshares with its share (`senderErases`). With either switch off the model finds a leak. The code meets the
rule as follows:
- The window is exactly the span in which the handover proof is computed. A custodian corrupted during it is
  counted in both committees, so a coalition holds at most n_old - 1 old and n_new - 1 new custodians. Each hidden
  u_old row is the sum of the old custodians' shares only, so it keeps one honest old share; the same holds for
  u_new with the new committee. Ligero's hiding values are summed over all n_old + n_new parties, so they are
  uniform to the coalition.
- Opened columns are uniform within each commitment's lives (HIDE = 2 T_COLS covers both lives).
- n-of-n blocks on one crash (the model's liveness note); the code does nothing about it.
- [OPEN] Sender erasure is a custodian-process obligation that no code here enforces; the harness reshares in one
  process.

## Wire format [SOURCE: handover.py docstring]
- **Conventions (proofwire's):** big-endian; a field element is 8 bytes and < p; a hash is 32 bytes; a column index
  is u32 below its domain; no length prefixes; no trailing bytes. Any parse error is a refusal before verification.
- **Header:** `DLHAND01 | d u16 | n_old u8 | n_new u8`. It must equal the ledger's values; a committee-of-four claim
  is refused here.
- **Body, in order:** old_roots, new_roots, eval_roots, mask_roots, (prox_old, cols_old), (prox_new, cols_new),
  ligero (one group of 4 ceil(W/64) rows plus the mask group).

Length, with W = d + HIDE, R = d + NMASK, pl = bitlen(4W - 1) + 1, T = T_COLS = T_OPEN,
lpl = bitlen(4(64 + T_HIDE) - 1) + 1, n = n_old + n_new:

    12 + sum_{side} 2 (32 n_s + 8 n_s W + 4 T + n_s T (8 R + 32 pl)) + 64 n
       + 8 ((64 + T) + (127 + T) + (2 (64 + T) - 1)) + n T (8 * 4 ceil(W/64) + 24 + 64 lpl)

(`handover::byte_len`, asserted equal to the honest Python bytes in the test.)

| d | profile | bytes | PCS part | Ligero part |
|---|---|---|---|---|
| 4 | demo | 990,780 [EXECUTED] | 486,544 | 503,840 |
| 4 | ledger | 3,860,028 [EXECUTED] | 1,785,552 | 2,074,080 |
| 4096 | demo | 40,866,492 [DERIVED, formula] | 39,170,320 | 1,695,776 |
| 4096 | ledger | 129,790,908 [DERIVED, formula] | 123,919,440 | 5,871,072 |

At d = 4096 the opened PCS columns dominate: 2 matrices x 6 parties x 309 columns x (4098 elements + path). A
Brakedown-style column-sum or a shared-column opening would cut this; [OPEN].

## Verdict equality, native vs Python [EXECUTED]
    cd research/dark_learning_2026_11_06
    DL_DETERMINISTIC=7 HANDOVER_DUMP=<dir> python3 run_handover.py 4 <demo|ledger>
    HANDOVER_VECTORS=<demo dir>:<ledger dir> cargo test --release -p darkproof --test handover_vs_python -- --nocapture

For each of the 13 rotation attempts the test replays Python's pre-attempt ledger file through native
`Ledger::rotate`. It requires (verdict, reason) equal to Python's and the ledger file afterwards byte-equal to
Python's. It also runs negative controls on the comparison: the honest bytes under a context with another epoch,
and under head roots with one bit flipped, must be refused.

| row | reason (both) |
|---|---|
| shifted weights | Ligero linear test: the constraints do not hold |
| resharing with a dropped subshare | Ligero linear test: the constraints do not hold |
| honest proof, other new roots | the handover proof is for other new roots |
| honest proof, other custodian set | handover (old committee): column challenge mismatch |
| honest proof, committee of four | parse: width or committee sizes differ from the ledger's |
| no proof | no handover proof |
| tampered (Ligero q[0] + 1, re-encoded) | Ligero linear test: the constraints do not hold |
| one byte flipped (middle) | Ligero: Merkle opening fails (group 0, custodian 0) |
| truncated by one byte | parse: truncated |
| one trailing byte | parse: trailing bytes |
| non-canonical field element | parse: non-canonical field element |
| honest handover | accept (record line byte-identical) |
| replay into epoch 1 -> 2 | handover: old roots are not the ledger head's |

Every reason is prefixed "rotation refused: ". Prover-side rows stay Python-only: the third opening refused by the
life counter, restart after rotation, the old committee's step 2 refused on the parent, and the new committee's
step 2 accepted.

## Timings (Mac, d = 4) [EXECUTED]
| profile | Python prove | Python verify (honest rotate) | native verify (`handover::verify`) | native rotate (with ledger I/O) | hidden rows | constraints |
|---|---|---|---|---|---|---|
| demo | 4.61 s | 0.50 s | 0.041 s | 0.090 s | 16 | 390 |
| ledger | 34.6 s | 1.96 s | 0.208 s | 0.182 s | 40 | 1238 |

The whole `run_handover.py` run took 190 s (demo) and 1410 s (ledger); the two steps dominate. The test reports
every native row as equal in both profiles (`test result: ok`, 26 rotations). [DERIVED] At d = 4096, verifier work
is dominated by Merkle-path checks over the 6 x 2 x 309 opened PCS columns of length R = 4098, plus the constraint
accumulation over W = 4714 cells per opened column. It should be the same order as the spine's PCS part of the
d = 4096 step verify (12.5 s natively, proof lane); not measured.

## A native prover [DERIVED]
Nothing new is needed below the protocol layer. `PcsParty::commit` already commits s' (new committee) and
`row_combo` gives each party's u share. The old commitment's `base` is set to block 1 (`take_life`).
`LigParty::add_row/commit/commit_masks/prove` with n = n_old + n_new parties takes zero rows from the other
committee. The PCS proximity combinations and column openings are spine.rs `pcs_prove` run once per committee
(over the n_old and n_new nets separately), and the constraint system is `HandoverSys` (already here, shared with
the verifier). What remains:
- The transport is n-generic (`Net::n`, `mem_mesh(n)`), so the 6-party Ligero runs on one mesh. The PCS openings
  of each committee are gathered among that committee only: a sub-view of the mesh, or a separate 3-party mesh.
- Resharing as custodian messages with erasure.
- `auth_plain` of s' under the new committee's MAC key.
- A vs-Python test on the proof bytes under DL_DETERMINISTIC. The det_rng labels are cozk's
  `("cozk", (("handover",), ctx), "party", i)` and the ZKPCS `"pcs"` labels.

Estimate: a few hundred lines of party orchestration; no new cryptography.
