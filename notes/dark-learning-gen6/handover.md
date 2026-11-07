# Custody handover, gen 6: native prover, custodian processes, enforced erasure (handover lane)

2026-11-07. Gen 5 (the construction, wire format, verifier, ledger): notes/dark-learning-gen5/handover.md.
Code:
- `native/darkproof/src/handover.rs`: prove, encode, verify, reshare_os.
- `native/darkproof/src/bin/dl-handover.rs`: the bench.
- `native/darkhand/`: erase, scan, ceremony, side, and the bin `dl-hand`.
- Tests: `tests/handover_prover_vs_python.rs`, `tests/handover_vs_python.rs`, `tests/handover_production.rs`.

## 1. Native prover, byte-equal with Python [EXECUTED]
    DL_DETERMINISTIC=7 python3 research/dark_learning_2026_11_06/handover_vectors.py <dir> <4|16> <demo|ledger>
    HANDOVER_PROVER_VECTORS=<dir> cargo test --release -p darkproof --test handover_prover_vs_python -- --nocapture

The prover runs one custodian's part: six parties on one `Net`, with each committee's PCS messages gathered over
the joint net so every party follows one transcript.

For each of the four vectors (d = 4 and 16; demo and ledger profiles) the test checks:
- the native bytes equal Python's;
- all six parties hold the same proof, and the native verifier accepts it;
- a third opening of the old child is refused before anything is sent;
- negative control: another custodian set gives different bytes, refused with "column challenge mismatch";
- native resharing (the Python draw order) equals `handover.reshare`.

## 2. d = 4096 (forge, 16 vCPU, six parties in one process, 12 GB cap, secret coins) [EXECUTED]
    dl-handover bench 4096 <demo|ledger>      (/srv/lanes/dl-gen6-handover/bench4096-split.jsonl)

| profile | proof bytes | resharing | old commitments (3 parties x 2) | NEW commitments (3 x 2) | prove (6 parties) | verify | elements sent per party | peak RSS |
|---|---|---|---|---|---|---|---|---|
| demo | 40,866,492 | 3.2 s | 125 s | 123 s | 1.86 s | 0.17 s | 4.26 M | 3.5 GB |
| ledger | 129,790,908 | 3.2 s | 147 s | 146 s | 5.62 s | 0.49 s | 13.5 M | 4.5 GB |

**After the proof lane's coset-domain PCS** (28769b6a), same bench [EXECUTED] (`bench4096-coset.jsonl`):

| profile | proof bytes | resharing | old commitments | NEW commitments | prove | verify | peak RSS (6 parties in one process) |
|---|---|---|---|---|---|---|---|
| demo | 40,866,492 | 6.0 s | 4.3 s | 4.5 s | 0.72 s | 0.20 s | 10.1 GB |
| ledger | 129,790,908 | 6.0 s | 4.7 s | 5.0 s | 1.33 s | 0.52 s | 11.6 GB |

So a d = 4096 ledger handover now costs about 5 s of new-committee commitment plus a 1.3 s prove on one 16-vCPU
box. The proof is 130 MB. It verifies in 0.5 s.

- **What a handover costs:** the new committee's commitments plus the prove. The old commitments are the step's
  child, already paid for.
- **Commitment time:** in this run the three parties share 16 cores. [DERIVED] With each custodian on its own box,
  each commits its two matrices on all of that box's cores.
- **Sizes:** they equal `handover::byte_len` (gen 5 formula). The opened PCS columns dominate.

## 3. Coin audit: every secret coin of a production handover

| coin | where | production source | seeded stream (tests) | status |
|---|---|---|---|---|
| resharing subshares | darkhand side::old_side (`os_field`); darkproof `handover::reshare_os` | getrandom (OS CSPRNG), rejection on 61 bits | `handover::reshare` (MT19937, Python order), marked TEST ONLY, used only by the vs-Python test | fixed |
| PCS row tails and mask rows (old child, new commitment) | darkproof pcs.rs `PcsParty::commit` | `rng::secret_rng()` = MT19937 seeded from 256 OS bits | `Det(Some)` (runtime-selected, not feature-gated) | [OPEN], proof lane's files: MT is not a CSPRNG; asked for ChaCha20 in non-det mode and `Det(Some)` behind a test feature |
| PCS Merkle leaf salts | pcs.rs, ligero.rs `salt(None)` | getrandom, 32 bytes | `Det` stream | ok |
| Ligero hiding values and mask polynomials | darkproof ligero.rs `LigParty::new` | `secret_rng()` (MT19937, OS-seeded) | `Det` | [OPEN], same as the tails |
| Ligero dealer (polynomial Beaver triples) | ligero.rs | `secret_rng()` | `Det` | unused by the handover (no product gates) |
| new committee's key s, e, ceremony r, salt | dzkpopk `Custodian::new` via darkhand ceremony::run | /dev/urandom, OsHiding | `new_det` behind feature `test-det` | ok |
| new committee's HE encryption coins | darkstep bfv `OwnKey::from_ceremony(seed)` | MT19937 from a 64-bit OS seed | | [OPEN], deploy lane's API (its own finding in darkstep); new_side switches when a CSPRNG constructor lands |
| canary key (memory scan) | darkhand scan | getrandom | | ok |
| step k's state in `dl-hand local` | darkhand bin `deal` | Dealer (MT19937), TEST ONLY: stands in for the run's real state | | by design, test only |

**Control** [EXECUTED] (`cargo test --release -p darkproof --test handover_production -- --nocapture`): two
handovers of the same shares with no deterministic hook give different commitment roots and different proof bytes
(0.6 % / 1.1 % of bytes equal: header, index high bytes), and both verify (demo and ledger, d = 16). Two reshares
of one share differ, and both sum to it.

## 4. Custodian processes and enforced erasure
### How the process flow works
    dl-hand local <work> <d> <demo|ledger> <port_base>    (darkhand/src/bin/dl-hand.rs)

`dl-hand local` runs six custodian processes on 127.0.0.1, each with its PID file in <work>/pids:
- **Old custodians.** Each runs its own epoch-1 key ceremony over the old mesh and keeps its key in a state file.
  It encrypts a ciphertext under its key and keeps it public, standing in for its HE traffic. It commits its W
  shares (the step-k child, one life spent).
- **New custodians.** Their epoch-2 ceremony runs over their own mesh. They receive the subshares on the joint
  six-party mesh and commit them. All six run the joint handover proof. The new committee then re-authenticates
  under its own tape (a different alpha) and MAC-checks 8 + 8 openings against the plaintext W.
- **Ledger.** New custodian 0 submits the proof bytes to the native ledger, and the native verifier accepts the
  rotation.

Step k's end state comes from a TEST-ONLY ideal dealer. The serve loop's CustodianState replaces it in the run.

### The erasure in an old custodian
1. **Zeroizing allocator** (`ZeroOnFree`). Every freed heap block is overwritten with volatile stores, and realloc
   is allocate-copy-wipe. Queue messages, BufWriter buffers and grown Vecs are therefore wiped as they are freed.
2. **Explicit wipes.** These cover:
   - the W shares and MAC shares, and the tape's shares, MAC shares and alpha share;
   - the commitment's rows, tails, salts and Merkle tree;
   - the ceremony secret (s, e) and the HE key s;
   - the return-coin key. The key is dropped in place and its inline bytes zeroed, which also clears the coin PRF
     state.
3. **State files.** tape.bin and key.bin are overwritten with zeros, fsynced and unlinked, and the directory is
   fsynced.
4. **Stack.** The state is built on the heap by a setup closure whose frame is dead before the scan. The erasure
   runs in its own frame, and 4 MiB of stack below the caller is then scrubbed.
5. **Memory scan.** The custodian reads every rw mapping of /proc/self/mem: heap, anonymous mappings and every
   thread's stack. It looks for one-way SipHash canaries (random key) of up to 2^16 sampled words of each secret
   kind:
   - the W1 / W2 shares and MAC shares;
   - the commitment rows and tails;
   - the UNOPENED salts (opened salts are in the proof, so public);
   - the tape shares and MAC shares, and the alpha share;
   - the HE secret key in NTT form, and the return-coin key.

   The ceremony's r and salt are revealed in the ceremony, so they are not canaries.

### Checks [EXECUTED on dregg-forge, Linux]
    dl-hand local /srv/lanes/dl-gen6-handover/er{3,4}/d<d>-<profile> <d> <profile> <port>

All 17 checks hold at d = 64 demo, d = 256 ledger, d = 1024 demo and d = 1024 ledger:
- all six processes exit 0, and all six hold the same proof;
- the ledger accepts the rotation, and its head is the new roots;
- new committee: MAC check passes, the opened entries equal the plaintext W, the new alpha differs from the old,
  and each custodian decrypts its own ciphertext (control);
- old custodians:
  - the scan before erasure finds the material (control);
  - the scan after erasure finds none of it;
  - the scan ran, and the allocator was active;
  - each decrypts its earlier ciphertext before erasure (control) and cannot decrypt it after erasure;
  - no state files are left;
- restarted old custodians: no key or share material on disk, and they decrypt neither their old ciphertext nor any
  new custodian's.

| d | profile | canary hits before erasure (per old custodian) | after | memory scanned | old: prove / erase | new: ceremony / commit / prove / re-auth | proof bytes | peak RSS old / new | wall |
|---|---|---|---|---|---|---|---|---|---|
| 64 | demo | 98,881 | 0 | 120 MB | 0.46 s / 0.007 s | 0.4 / 0.02 / 0.04 / 0.003 s | 1,611,132 | 67 / 55 MB | 1.4 s |
| 256 | ledger | 826,371 | 0 | 211-216 MB | 1.04 s / 0.01 s | 0.8 / 0.10 / 0.14 / 0.02 s | 11,596,860 | 171 / 170-183 MB | 3.2 s |
| 1024 | demo | 1,013,507-1,023,327 | 0 | 223-229 MB | 0.73 s / 0.06 s | 0.4 / 0.34 / 0.10 / 0.14 s | 10,996,668 | 270 / 735 MB | 4.2 s |
| 1024 | ledger | 1,031,631 | 0 | 308 MB | 1.47 s / 0.07 s | 0.8 / 0.48 / 0.27 / 0.15 s | 35,283,132 | 419 / 845 MB | 5.7 s |

**What failed first and why** [EXECUTED]. The first forge run (d = 64) left about 800 hits after erasure:
- 388 + 388 were the opened columns' salts, still in the live proof struct. They are public, so the canary was
  wrong.
- 3 were copies of the alpha share and 1 of the return-coin key, made on the stack when building the canaries and
  by moves of the state struct.

Each fix is named in the commit (ec39b23c). The scan saw every one of these residues, so it is not vacuous.

**What the erasure does not cover** [OPEN]:
- The kernel's socket buffers (TLS protects the bytes in flight).
- Swap: a deployment disables it or uses encrypted swap.
- The page cache of the wiped files: the zero overwrite reaches it.
- Copies inside other libraries' non-allocating state.
- d = 4096 erasure in local mode: six processes on one 12 GB box is too much (new custodians need about 12 GB at
  d = 4096). It belongs in the three-box run.

## 5. The self-handover after an SPDZ abort [EXECUTED on forge]
    dl-hand local-self <work> <d> <profile> <port_base>

An abort retires the MAC key. Recovery keeps the same seats and the HE keys:
- each seat reshares its W shares to itself under a new MAC key;
- the shares are re-authenticated, and the handover proof binds the new commitment to the ledger head;
- the ledger rotates to the same custodian set at epoch + 1;
- the old shares, tape and alpha share are erased while the seat's process runs on.

Each seat is one process, with its old and new roles as two threads on the joint six-party mesh (64 MiB stacks for
the stack scrub). All 13 checks hold at d = 256 ledger, 1024 demo and 1024 ledger. Canary hits before erasure are
760,837 to 988,933 per old role, and after erasure 0. The checks:
- the processes exit 0, and both roles hold the same proof;
- the ledger accepts, its head is the re-committed roots, and its custodian set is unchanged;
- the MAC check under the NEW key passes, the opened entries equal the plaintext W, and the new alpha differs from
  the old;
- the kept HE key still decrypts;
- the scan finds the material before erasure and none of it after, and no old tape file is left.

[OPEN] The run-level test (an abort mid-step in darkstep serve, the self-handover, the run continuing, the weights
equal to the plaintext twin) needs three things from other lanes:
- the deploy lane's `--handover-at` and join mode;
- the train lane's twin;
- fresh preprocessing under the new key from the prep lane.

## 6. Entry points for the serve loop (`darkhand::serve`, usage at the top of serve.rs)
- `old_from_serve(CustodianState, carry, files, retire_he, captured)` returns `OldParts { old, he, net3 }`.
- Then `side::old_side(&common, move || parts.old, || net6)`. In a rotation the process exits after this.
- A new seat calls `side::new_side(&common, j, net3, net6, tape, epoch, 8, keep)`. It returns the new Party, W wires
  (`shares_rows`), the carry (the next parent), the keys, and the proof for `Ledger::rotate`.
- The binary declares `#[global_allocator] static A: darkhand::erase::ZeroOnFree`.
- The resharing tag is `side::RESHARE` (PROOF until the deploy lane's RESHARE = 5).
