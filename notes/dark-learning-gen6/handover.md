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

## 7. Erasure checks against the deployed binary, on the boxes (handover lane gen 2)
Code:
- `darkhand::scan` disk canaries (49ae41c7, 6a7db52e);
- `dl-hand restart-seat` / `verify-rotation` (b9a2eca6);
- `native/darkhand/scripts/check_handover.py` and `research/.../handover_replay.py` (d8c5fd43);
- `serve::rotation_setup` / `self_setup` (8aa3512b, 093ff839).

### What each check reads
    check_handover.py RUN.json OUT [--self] --profile ledger-sq --tools dregg-forge=<dl-hand> bb2=<dl-hand>

The checker reads the deploy lane's run layout over ssh, read-only except for the relaunch. dl-hand is built from
the same commit as dl-custodian, in /srv/lanes/dl-gen6-handover/target-e514 and ~/lanes/dl-gen6-handover/target-e514.

**Per old seat, from handover_P<I>.json, which old_side writes inside dl-custodian:**
- the memory scan before erasure (control) and after;
- the **disk scan** before (control) and after:
  - darkhand scans every file under `scan_paths` at every byte offset: the seat's D and TLS dirs, every tape and
    owner-msg file of the epoch, and their chunk dirs;
  - it looks for the durable kinds: W shares and MAC shares, tape shares and MAC shares, the alpha share, and the HE
    key in NTT form;
  - since 6a7db52e, also the alpha share in MP-SPDZ's Montgomery word and its decimal text (Player-MAC-Keys);
- the pre-handover decryption (control) and the post-erasure one;
- the state files gone, by the report and by a remote stat.

**The restarted seat, on its own box after its process exited:**
- `dl-hand restart-seat`, with the seat's own argv from `<dir>/serve<I>.cmd`. It reports what the binary could load
  (TLS key, checkpoint, carry, tapes and owner messages of steps 0..K). It then tries to decrypt the seat's
  pre-handover ciphertext and each new seat's ciphertext with the only key the disk can give: dl-custodian never
  writes the HE key to disk, so that is the zero key.
- A relaunch of the exact `serve` command line, and of its `--resume` variant, under its own PID file and
  `timeout 300`. Each must exit non-zero at the missing TLS key. Without that key it cannot sign a TLS handshake or
  join a mesh, so it cannot contribute a share.

**Per new seat:**
- the MAC check under its own key, its own decryption (control), and its replica's rotate record;
- `dl-hand verify-rotation`: the replica is replayed up to the rotation into a fresh ledger, and the rotation is
  re-submitted with handover_e1.bin (native verifier). The proof's sha256 must equal the record's, and a copy with
  one byte flipped must be refused.

**Across seats:** one proof digest; the three new replicas equal through the rotation.

**Python:** `handover_replay.py PROFILE LEDGER HANDOVER.bin` (Python Ledger.rotate). It must append the same record
as the native one and refuse the flipped byte.

**Negative controls, executed at d = 16 on the Mac:**
- `DLH_STRAY_COPY=1 dl-hand local` leaves a tape copy, a "3\n<alpha>" key file and a Montgomery-word file that the
  erasure does not know about. The after-erasure disk scan finds each one by name and kind.
- On a dl-hand local proof, verify-rotation and handover_replay.py both refuse the flipped byte ("Ligero linear test").

### run9: three-box rotation at d = 4096 [EXECUTED 2026-11-07, ledger-sq, dl-custodian ca46c2fd]
Layout: old seats forge 0, bb2 1, bb2 2, with --handover-at 0 --wipe-spent; new seats bb2 0, forge 1, bb2 2.
Checker output: scratchpad dl-gen5/handover/run9/check1/{checks,measure}.json.

**Result: 68 of 71 checks hold. The three after-erasure memory scans are red.**

| check | old 0 (forge) | old 1 (bb2) | old 2 (bb2) |
|---|---|---|---|
| memory scan ran (/proc) | ok | ok | ok |
| memory hits before erasure (control) | 1,014,170 | 1,014,171 | 1,014,170 |
| memory hits after erasure | **11** (alpha share, [stack]) | **12** (11 alpha [stack], 1 tape MAC share [anon]) | **11** (alpha, [stack]) |
| disk hits before erasure (control): ckpt + carry | 393,217 | 393,217 | 393,217 |
| disk hits after erasure | 0 | 0 | 0 |
| allocator active; no state file left; no wipe error | ok | ok | ok |
| decrypts its ciphertext before erasure (control) / after | yes / no | yes / no | yes / no |
| restarted: no TLS key, ckpt, carry, tape or owner msg of steps 0..K on disk | ok | ok | ok |
| restarted: decrypts neither its old ct nor any of the 3 new seats' cts (each found) | ok | ok | ok |
| relaunch `serve` / `serve --resume`: exit at "own TLS key" | 101 / 101 (4.1 s) | 101 / 101 (4.9 s) | 101 / 101 (4.9 s) |

| check | new 0 (bb2) | new 1 (forge) | new 2 (bb2) |
|---|---|---|---|
| MAC check under its own key; alpha share nonzero | ok | ok | ok |
| decrypts its own ct under the new key (control) | ok | ok | ok |
| replica: one rotation, to epoch 1 | ok | ok | ok |
| verify-rotation (native): accepted, sha256 = record | 0.72 s | 0.77 s | 0.74 s |
| one-byte flip refused | "Merkle opening fails (W1, custodian 0)" | same | same |

Also: the three replicas are equal through the rotation, and all six seats hold the same proof (129,790,908 bytes).

**Python** [EXECUTED on forge]:

    python3 handover_replay.py ledger-sq run9/new1/D/ledger_P1.jsonl run9/new1/D/handover_e1.bin

Result: ROTATION PASS. Python's Ledger.rotate accepts in 18 s and appends a record equal to the native one. The
flipped byte is refused with "Merkle opening fails (W1, custodian 0)", the same reason the native verifier gives.


**Why the memory scan is red** [DERIVED from the code and the hit maps]:
- `Tape.alpha_i` is inline in `Party`, so it is inline in `CustodianState`.
- dl-custodian moves the state by value: serve_main_with -> serve_state -> finish -> rotate_out -> old_from_serve.
  Each move leaves a copy in a frame that is still live while old_side runs.
- darkhand scrubs only below old_side, because a live caller frame cannot be scrubbed safely. Eleven identical
  copies on every seat fit this.
- The [anon] hit on seat 1 is probably the cached stack of a dead worker thread. The scan now reports each hit's
  map, start, length and offset (6a7db52e), so the next run can locate it exactly.
- The fix:
  - darkhand's half: `serve::rotation_setup` / `self_setup` take the boxed state apart inside old_side's scrubbed
    setup frame;
  - the deploy lane's half (asked): `Box<CustodianState>` from creation.

### Measurements at d = 4096 (run9; ledger-sq, so the pre-cut layout)
Per old seat:

| seat | reshare | prove | erase | handover total | memory scanned (before / after) | disk scan (before / after) | peak RSS (VmHWM / cgroup) |
|---|---|---|---|---|---|---|---|
| old 0 forge | 1.80 s | 8.62 s | 0.80 s | 21.2 s | 4.36 / 3.30 GB | 1.17 / 0.96 s | 7.5 / 7.9 GB |
| old 1 bb2 | 2.22 s | 8.15 s | 0.95 s | 23.7 s | 4.66 / 3.60 GB | 1.90 / 0.95 s | 7.8 / 8.3 GB |
| old 2 bb2 | 2.09 s | 8.22 s | 1.00 s | 23.3 s | 4.57 / 3.79 GB | 1.67 / 0.94 s | 7.8 / 8.3 GB |

Per new seat:

| seat | ceremony | reshare (recv) | commit | prove | re-auth + check | handover total | peak RSS (VmHWM at join / cgroup over the run) |
|---|---|---|---|---|---|---|---|
| new 0 bb2 | 0.77 s | 0.48 s | 2.46 s | 2.85 s | 3.47 s | 17.6 s | 5.3 / 9.9 GB |
| new 1 forge | 0.96 s | 0.53 s | 1.88 s | 3.33 s | 4.55 s | 17.8 s | 5.2 / 9.5 GB |
| new 2 bb2 | 0.77 s | 0.50 s | 2.47 s | 2.80 s | 3.68 s | 17.6 s | 5.4 / 10.1 GB |

Bytes per link, from the Net counters:
- old i -> each new seat: 268,435,490 B RESHARE (2 d^2 field elements), 21,661,471 B PROOF and 1,770 B CTRL (the
  ledger replica); 290.1 MB in all;
- old i -> each other old seat: 21,661,471 B PROOF;
- new j -> each of the other five seats on the six-party mesh: 21,661,471 B PROOF;
- new j -> each new peer, three-party mesh: 1,781,700 B for the ceremony, then 268,435,523 B OPEN for the
  re-authentication (auth_plain_vec opens 2 d^2 masked values).

So a d = 4096 handover moves about 1.6 GB of resharing and about 0.8 GB of re-authentication openings over the
links, plus 22 MB of proof traffic on each of the 30 directed links of the six-party mesh. It finishes in under
25 s on every seat. The old seats' peak RSS is the step-0 process's; the handover itself adds little.

### run11: self-handover after an abort at d = 4096 [EXECUTED, partly superseded]
Seat 1 ran `--attack wrong_return:1`. Step 0 was refused at all three seats ("HE outer: Freivalds check failed").
Each seat reloaded its checkpoint and self-handed over (old role 50.6 / 76.5 / 77.6 s; reshare 2.7-2.8 s; proof
6.6-6.7 s; erase 0.17-0.23 s; new role 22.0 s). The ledger rotated to the same set at epoch 1, and step 0 was
redone and step 1 accepted.

Checker `--self`: 31 of 37 hold. Holding, on all three seats:
- the MAC check under the new key;
- the kept HE key decrypting;
- the same-set rotation at epoch 1;
- verify-rotation, with the flipped byte refused;
- one proof digest.

The red items, and what each means:
- **Commitment canaries:** 2.08 M hits after erasure on seat 0, 2,440 on seats 1 and 2. These are false positives
  on darkhand's side. The carry of a step-0 abort is the PUBLIC genesis commitment (commit_public), which the seat
  keeps. Fixed in e9c14b1f: `side::carry_is_public` recognises it exactly and leaves it out of the canaries.
- **5 alpha-share copies per seat, real:**
  - the partially moved checkpoint `ck.alpha_i` in self_handover's live frame;
  - the main thread's dead stack below self_handover, which still holds the refused step's frames (old_side
    scrubs only its own thread's stack).
  - The deploy lane fixed both in ed88a249 (reload_shares; side::scrub_stack on the main thread before the
    roles spawn).
- **Disk control 0 files:** run11's binary predated the files / scan wiring, so `scan_paths` was empty. Fixed in
  ed88a249.

Rerun: run11b (self-handover), with run12b (rotation) after run12 died before its handover on a TCP self-connect.
Both binaries are at ed88a249.

### run12b: three-box rotation rerun at d = 4096 [EXECUTED, dl-custodian ed88a249, ledger-sq]
The binary has the boxed state, `--erase-extra` for the retired key's MP-SPDZ files and `--scan-extra
wired<I>/mpspdz`. Layout as run9. Checker output: scratchpad dl-gen5/handover/run12b/check1.

**Result: 71 of 74 hold.** The red three are the after-erasure memory scans: **4** alpha-share hits per seat on
[stack]. The relaunch checks were first recorded red because the checker accepted only the TLS-key message. The
binary now stops earlier, at the erased step-0 tape (exit 2, 0.4-2.2 s). With b3655191's criterion (non-zero exit
at a missing erased secret), the recorded tails pass.

What changed against run9:
- **Memory:** the boxed state removed 7 of run9's 11 alpha copies. The 4 left lie 3.1, 6.0, 6.9 and 10.1 KB above
  old_side's scanning frame, on every seat. So they are in the live frames between main and old_side, or in stale
  slots of frames pushed onto stack the step loop dirtied: by-value Tape temporaries in serve_main_with and
  serve_state (read_tape_once -> load_tape).
- **Fix, asked of the deploy lane:**
  - return the boxed state to dl-custodian's main;
  - call `side::scrub_stack_all()` there, before rotate_out;
  - make Tapes boxed.
  - scrub_stack_all (b3655191) passes dl-hand local and local-self at d = 256 on forge.
- **Disk control:** 393,220 hits before erasure in ckpt, carry, `Player-MAC-Keys-p-P<I>` (the decimal alpha form)
  and `Mascot-Secrets-...-P<I>-3` (2 plain copies). 0 after. The two --erase-extra files are gone on every old box.
- **Native verify-rotation:** 0.62-0.68 s, with the flipped byte refused.
- **Python** (`handover_replay.py` on bb2): ROTATION PASS in 24 s, the flipped byte refused.

| seat | reshare | prove | erase | handover total | peak RSS (VmHWM / cgroup) |
|---|---|---|---|---|---|
| old 0 forge | 1.74 s | 7.76 s | 0.87 s | 24.6 s | 7.6 / 7.6 GB |
| old 1 bb2 | 2.70 s | 6.74 s | 0.82 s | 25.4 s | 7.7 / 7.7 GB |
| old 2 bb2 | 2.25 s | 7.14 s | 0.82 s | 25.1 s | 7.8 / 7.8 GB |

| seat | ceremony | reshare | commit | prove | re-auth | total | peak RSS (VmHWM at join / cgroup over the run) |
|---|---|---|---|---|---|---|---|
| new 0 bb2 | 0.69 s | 0.49 s | 2.32 s | 2.50 s | 3.31 s | 16.5 s | 5.6 / 8.9 GB |
| new 1 forge | 0.68 s | 0.50 s | 1.78 s | 3.11 s | 4.23 s | 16.6 s | 5.3 / 8.3 GB |
| new 2 bb2 | 0.71 s | 0.49 s | 2.30 s | 2.53 s | 3.33 s | 16.6 s | 5.5 / 8.6 GB |

Bytes per link are as in run9: d and the profile are the same, and the Net counters agree byte for byte.

### run11b: self-handover rerun at d = 4096 [EXECUTED, dl-custodian 453d8e0f]
The self-handover now runs from main after `scrub_stack_all()` (the deploy lane's Prove::run_deferred). Seat 1
attacks (`wrong_return:1`). Checker `--self`: **33 of 37 hold.** There are no main-thread hits any more.

The red items, both fixed in darkhand 09fd154d:
1. **One alpha copy per seat, in the old role's own thread stack**, 3.9 KB above its scanning frame. The generic
   setup closure was inlined into old_side, so the by-value CustodianState it takes apart lived in old_side's live
   frame. Fix: `#[inline(never)] run_setup`. dl-hand local and local-self at d = 256 then pass on bb2.
2. **Seat 0's 470 K memory hits and 515 K disk hits in MP-SPDZ .pyc files, kind "W1 share": a false positive.** At
   a step-0 abort the carry is the public genesis, so custodian 0's share IS the public W. When the carry is public,
   its committed share is not canaried; the MAC shares stay canaried.

What holds:
- the disk controls (ckpt, tape, owner msg, and the wired-new key files on seats 1 and 2), and 0 hits after erasure
  on seats 1 and 2;
- the erase-extra files gone;
- the MAC check, the kept key, the same-set rotation, verify-rotation and one digest.

### run12c: three-box rotation at d = 4096, ledger-x2 [EXECUTED 2026-11-07 11:05-11:14 UTC, dl-custodian 8319ea81]
Layout as run9 (old: forge 0, bb2 1, bb2 2; new: bb2 0, forge 1, bb2 2). Prep's fresh chunks (w4096h6, ho-sh3,
ho-sh3-steps). The binary has main's scrub_stack_all before the handover and darkhand 09fd154d's non-inlined setup
frame. Checker (tools at 8319ea81):

    check_handover.py runs/run12c.json OUT --profile ledger-x2 --tools dregg-forge=.../target-8319/release/dl-hand bb2=...

**Result: 74 of 74 checks hold.** For the first time the after-erasure memory scan is 0 on every old seat.
Output: scratchpad dl-gen5/handover/run12c/check2 (an earlier check1 ran before seat 1's report existed).

| check | old 0 (forge) | old 1 (bb2) | old 2 (bb2) |
|---|---|---|---|
| memory hits before erasure (control) | 2,994,265 | 2,994,265 | 2,994,265 |
| memory hits after erasure | **0** | **0** | **0** |
| memory scanned before / after | 4.12 / 3.00 GB | 4.27 / 3.15 GB | 4.22 / 3.10 GB |
| disk hits before (control) / after, files scanned | 393,220 / 0, 140 / 135 | 393,220 / 0, 138 / 133 | 393,220 / 0, 138 / 133 |
| decrypts its ciphertext before / after erasure | yes / no | yes / no | yes / no |
| state files left; wipe errors | none; none | none; none | none; none |
| restarted: no TLS key, ckpt, carry, tape or owner msg on disk; loads nothing | ok | ok | ok |
| restarted: decrypts neither its old ct nor any new seat's (each found) | ok | ok | ok |
| relaunch `serve` / `serve --resume`: exit non-zero at an erased secret | 2 / 2 (0.4 s) | 2 / 2 (2.1 s) | 2 / 2 (2.2 s) |
| reshare / prove / erase / handover total | 1.83 / 28.95 / 0.87 / 64.2 s | 2.53 / 28.16 / 1.44 / 94.9 s | 2.78 / 27.92 / 1.26 / 91.9 s |
| peak RSS | 8.2 GB | 8.3 GB | 8.2 GB |

The control's hits are every kind in the canaries: W shares and MAC shares, the commitment rows, tails and unopened
salts, the tape shares and MAC shares, the alpha share, and the HE key in NTT form.

| check | new 0 (bb2) | new 1 (forge) | new 2 (bb2) |
|---|---|---|---|
| MAC check under its own key; alpha nonzero | ok | ok | ok |
| decrypts its own ct under the new key (control) | ok | ok | ok |
| verify-rotation (native): accepted, sha256 = record | 5.98 s | 5.43 s | 6.20 s |
| one-byte flip refused | "Merkle opening fails (W1, custodian 2)" | same | same |
| ceremony / reshare / commit / prove / re-auth / total | 1.41 / 0.63 / 9.10 / 10.94 / 5.76 / 34.6 s | 2.62 / 0.49 / 6.71 / 13.92 / 5.78 / 36.2 s | 1.36 / 0.67 / 8.80 / 11.24 / 5.57 / 34.6 s |

All six seats hold one proof (sha256 86ccfd3c..., 37,603,856 B under ledger-x2), and the three replicas are equal
through the rotation. **Python** (`handover_replay.py ledger-x2` on bb2, under a 32 GB scope): ROTATION PASS. Python's
Ledger.rotate accepts in 852 s (peak RSS about 28 GB) and appends a record equal to the native one; the flipped byte
is refused with the native verifier's reason, "Merkle opening fails (W1, custodian 2)". The binary predates the vault and the TLS canaries, so their checks start with the next build.

### run11c: self-handover after an abort at d = 4096, ledger-x2de + RS, cut E live [EXECUTED 2026-11-07 11:22-11:27 UTC, dl-custodian 11e84d91]
Seat 0 bb2, seat 1 forge (`--attack wrong_return:1`), seat 2 bb2. Prep's tapes: sh-abort (the refused step), ho-x
(the self-handover) and ho-x-steps (the redo and step 1). Each seat runs `--erase-extra` on its wired-new<I>-sh
p-61 files and `--scan-extra` on that dir. There is no vault in this run.
- Step 0 was refused at all three seats (Freivalds).
- Each seat self-handed over at the public-genesis head. The head was final, so no old carries; the handover leaves
  the epoch-1 head pending through its carries.
- The rotate record carries `pending`. This is the first deployed cut E handover.
- Checker: `check_handover.py runs/run11c.json OUT --self --profile ledger-x2de` with tools at d01c914a.

**Result: 37 of 37 checks hold.** The after-erasure memory scan is 0 on every seat.
- A first pass (check1) also applied the TLS-key checks. A self-handover keeps the seat's TLS identity, which is
  not erased, so those checks now apply to rotations only (checker fix).
- Output: scratchpad dl-gen5/handover/run11c/check2.

| check | seat 0 (bb2) | seat 1 (forge) | seat 2 (bb2) |
|---|---|---|---|
| memory hits before erasure (control) | 3,338,307 | 3,338,307 | 3,338,307 |
| memory hits after erasure | **0** | **0** | **0** |
| memory scanned before / after | 7.21 / 8.85 GB | 7.10 / 7.75 GB | 7.06 / 8.73 GB |
| disk hits before (control) / after, files scanned | 3,338,371 / 0, 118 / 113 | 3,338,371 / 0, 117 / 112 | 3,338,371 / 0, 117 / 112 |
| control's hit files | ckpt, owner msg, tape, Player-MAC-Keys, Mascot-Secrets | same | same |
| state files left; erase-extra files gone | none; yes | none; yes | none; yes |
| old role: reshare / prove / erase / total | 3.01 / 16.06 / 1.13 / 102.6 s | 2.11 / 16.92 / 0.87 / 55.6 s | 2.88 / 16.09 / 1.02 / 99.5 s |
| new role: MAC check under the new key; the kept key decrypts | ok; ok | ok; ok | ok; ok |
| new role: reshare / commit / prove / re-auth / total | 3.18 / 9.79 / 5.91 / 10.93 / 41.0 s | 3.54 / 6.55 / 8.80 / 10.32 / 41.0 s | 3.20 / 9.54 / 6.14 / 11.44 / 41.0 s |
| replica rotated to the same set at epoch 1 (with pending) | ok | ok | ok |
| verify-rotation (native, x2de): accepted, sha256 = record; flip refused | 3.28 s; "Merkle opening fails (W2, custodian 1)" | 2.54 s; same | 3.21 s; same |
| peak RSS (old role) | 8.9 GB | 8.0 GB | 8.5 GB |

- All three hold one proof: sha256 5085b746..., 19,427,648 B.
- The x2de handover proof is about half of run12c's x2 one (37.6 MB), because the new W is not opened in it.
- The public genesis carry (`public_carry` W1, W2) is not canaried as a share, as in 09fd154d.

### reh: the first rotation on a vault build (deploy's rehearsal, 11:51-12:01 UTC, r6 at 11e84d91, ledger-x2de + RS) [EXECUTED]
Four steps, with the handover after step 1. Old seats forge 0, bb2 1, bb2 2; new seats forge 0, bb2 1, bb2 2.
Every seat ran `--vault`; the old seats also ran `--keep-erased-copy`. Checker: rotation mode, tools at the
vault-open build.

**Result: 86 of 95 checks pass, and the 9 reds have two causes.**

What holds:
- every vault check: the key was in the keyring, is invalidated and is absent after; the sealed files open under it
  before the erasure;
- every TLS canary check;
- the restarted seat loads and decrypts nothing;
- verify-rotation, and one proof digest.

The erased copies (`dl-hand vault-open NAME FILE...` on each old box, run after the handover):
- 9 sealed files (ckpt 536,870,996 B, carry 288,873,140 B and the TLS key 174 B, per seat);
- none opens, neither by the uid's keyring (the old epoch's key name is absent) nor by the zero key.

**Red 1: relaunch (6 checks), a checker criterion only.** The relaunched serve and serve --resume exit 2 at
"vault <name>: no file key in the keyring". The erased file key is now the first missing secret, before the TLS key
and the checkpoint. The checker now accepts the seat's own vault name in that message.

**Red 2: the after-erasure memory scan (3 checks), 8 hits of "TLS private key (PKCS#8 DER)" per seat. A false
positive of the canary design.**
- The 8 hits were present before and after the erasure, and are 8 consecutive words in [heap].
- The scalar's three forms (big-endian, limbs, Montgomery) have 0 hits both times.
- tests/tls_canary.rs shows that exactly 8 of the DER's 17 aligned words also sit at aligned offsets of the seat's
  own certificate: the public key and the OIDs. The certificate is public and stays live.
- Fix: the DER canary keeps only the words that overlap the private scalar (5), with a test that none of them
  occurs in the certificate.
- This also showed that rustls's key is gone by the time of the before-scan, since the meshes are closed. The TLS
  control is now the key file's plaintext, held through the before-scan and then wiped.
- dl-hand local at d = 256 on bb2 with the fix: the DER private words have 5 hits before and 0 after on every old
  seat, the vault key 12 before and 0 after, and all checks hold.
- A rotation rerun on this darkhand will confirm it on the boxes.

**Also found:** `--keep-erased-copy` copies the `--erase-extra` MP-SPDZ files too (Player-MAC-Keys-p-P<I>,
Mascot-Secrets-...). They are plaintext, not sealed, so the erased dir holds a live copy of the old MAC key share.
The deploy lane shredded them (`shred -u`). Since c2319a8d, `--keep-erased-copy` copies only DLVAULT1 files.
- `shred` overwrites in place, which is not physical erasure on ZFS or an SSD: the blocks may survive. The exposure
  is the old epoch's MAC key share, which is retired at the rotation.
- That is exactly the gap the vault closes for sealed files, and why MP-SPDZ's files need sealing or tmpfs: the open
  prep item.
- The confirming rotation is reh2, on a build at or after c9771f4a and c2319a8d, once prep has made fresh-key
  chunks.

### The disk scan and RAM filesystems (prep's MP-SPDZ dirs on tmpfs) [EXECUTED on bb2]
Prep (gen 3, a8fd625f) moved every MP-SPDZ runtime's Player-Data and Persistence into RAM: symlinks into
`/dev/shm/dl-gen6-prep/<seat>` on forge and bb2, and a tmpfs mounted noswap on hbox.
- **Following symlinks.** The disk scan now follows a symlink only when it leads into a RAM filesystem (statfs: tmpfs
  or ramfs).
- **Counting.** Files there are scanned like the others but counted apart. The report's `disk_scan_*.ram` holds
  files, bytes, hits, hits_by_kind, hit_files, the mounts (point, fstype, options) and the box's SwapTotal. The
  existing `files` / `hits` stay the persistent ones.
- **Checker** (when a report has RAM files):
  - no RAM copy is left after the erasure;
  - every RAM mount cannot page out (the box has no swap, or the mount has `noswap`).
- `tests/ram_scan.rs` (bb2) puts the same 64 canary words in a persistent file and in /dev/shm behind a
  `Player-Data` symlink:
  - each copy is counted once, in its own class (64 / 64), and the mount is reported as tmpfs;
  - after both are removed, 0 / 0.
- **Found on the way:** bb2's /tmp is itself a tmpfs (size 64 GB). The scan classifies it as RAM.
- **Prep's other note:** the rehearsal seat sets shared the old seats' TLS identity. From now on, a check that an
  old seat's identity authenticates nothing after a rotation uses fresh seat sets (prep's seats.sh mints one per
  set).

## 8. The handover proof in F_{p^2} (profiles demo-x2, ledger-x2) [EXECUTED, 1bfb04a3]
The proof lane's x2 cut (proof.md §19) draws every challenge in F_{p^2}. The handover follows it:
- the point per matrix is `X.chal` / `ext::chal`;
- the u rows come in EXT component blocks;
- each identity is EXT F_p constraints, component 0 first;
- the PCS proximity weights are in F_{p^2} (a row is EXT W long, checked by pcs::verify_e);
- the Ligero mask group is 3 EXT.

Native is generic over E (dispatch on pr.ext). Results:

| check | result |
|---|---|
| EXT = 1 unchanged | the d = 4 demo vector is byte-identical to the cut-B one; native == Python on d4 demo, d16 demo, d16 ledger |
| native prover == Python (x2), and byte_len == length | demo-x2 d = 4 512,480 B; d = 16 573,536 B; ledger-x2 d = 4 1,521,968 B |
| run_handover.py 4 demo-x2 | all rows as expected, step 2 by the new committee included |
| handover_vs_python (demo-x2 dump) | native verdict and ledger file equal to Python's on all 14 rotations |
| new refusal row: proximity row u-part + 1 (component 1) | refused, "column challenge mismatch" (the row is absorbed before the columns are drawn) |

**Soundness of one handover** (`handover_soundness.py ledger 4096`; union bound; |F| = p^EXT):

| term | EXT = 1 | EXT = 2 |
|---|---|---|
| Schwartz-Zippel old W(r) = new W(r), per matrix (24 variables) | 2^-56.4 | 2^-117.4 |
| PCS proximity per commitment (4: old and new W1, W2; n = 264,616) | 2^-43.0 | 2^-104.0 |
| PCS columns per commitment ((3/4)^309) | 2^-128.2 | 2^-128.2 |
| Ligero proximity (n = 3,284) / linear / quadratic | 2^-49.3 / 2^-61 / 2^-61 | 2^-110.3 / 2^-122 / 2^-122 |
| Ligero columns | 2^-128.2 | 2^-128.2 |
| **the handover** | **2^-41.0** | **2^-102.0** |

Not in the table: Merkle binding (computational) and Fiat-Shamir grinding.

### Bounds this check does not cover [OPEN]
- **Copy-on-write and SSD storage.** An in-place overwrite is not physical erasure there. hbox's /othersys is ZFS:
  old blocks can survive in free space and snapshots. An SSD's FTL can keep old pages on bb2 and forge too. Against
  a disk image, the runtime dirs need encryption at rest with the key destroyed. That is ember's call.
- **MP-SPDZ runtime dirs.** The old key's Player-MAC-Keys and Mascot-Secrets files in the prep dirs were not in
  run9's scan paths. They are canaried now; the deploy lane adds them to the files list and the scan paths for the
  next rotation.
- **The TLS private key in memory.** It is wiped on disk and the process exits, but it is not canaried in the scan.
- **Kernel socket buffers and swap**, as in section 4.

## 9. Cut E through the handover, in Python (profiles demo-x2de, ledger-x2de; design (b)) [EXECUTED]
Code: `handover.prove_defer` / `verify_defer` / `schema_defer` (magic DLHAND02), `Ledger.rotate` and `_replay`
(proofwire.py), `run_handover.main_defer`, `handover_vectors.py` under DEFER.

**What the handover does under DEFER.** The ledger head is pending: step k committed its child W_(k+1) without
opening it, with carries c_k = W_(k+1)(r_k) to come.
- **The old head's W1, W2** are opened once (one life, base 0). Each is evaluated twice from that one opening:
  - at the handover point r;
  - at the head's r_k, against the old committee's carries c1p, c2p (their second life). This is the head's
    discharge.
- **The new committee's W1, W2 are not opened.** Their roots are absorbed before r is drawn. The new committee then
  commits carries cN1, cN2 = new W(r): each new custodian commits its own share's evaluation, with two lives. These
  are absorbed ("carry") after r and before the Ligero's and the PCS columns' challenges. The proof shows old W(r) = cN.
- **The rotate record's `pending`** is `pending_json(out)`: points {"W1", "W2"} (the handover's r) and carry_roots
  {"c1p": cN1, "c2p": cN2}. The next step, the release or a closing proof discharges it unchanged: new W(r) = cN, at
  new W's one opening.
- **Fiat-Shamir order** (the proof lane's condition 1). The transcript absorbs:
  1. ctx;
  2. the old W roots, the old carry roots (pending head), the new W roots;
  3. then draws r;
  4. then absorbs "carry" (cN roots);
  5. then "lig-evals", then the PCS proximity and columns.
- **Ledger.**
  - `rotate` passes `deferred_of(self.pending)` to `HO.verify_bytes` and records the new pending.
  - `_replay` on a rotate record: `discharge("the handover opened its child")`, then `self.pending = rec["pending"]`
    and `status[step] = "pending"`.
  - A rotation after a close is refused (fail closed in the replay too).
  - The "rotation refused: the head is pending" refusal is gone. In its place, a handover made as for a final head,
    offered to a pending head, is refused (row 2 below).
- **Outside DEFER nothing changes.** The demo-x2 handover vector is byte-identical to the one made before this cut:
  `DL_DETERMINISTIC=7 handover_vectors.py OUT 4 demo-x2` gives sha256 fcc31bb5..., the same as vec-x2/d4-demo-x2.

**Rows** (`python3 run_handover.py 4 demo-x2de`; all as expected, 1,249 s; handover_results_d4_demo-x2de.json):

| row | result | refused by / status |
|---|---|---|
| step 1 by the old committee | ACCEPT | status {1: pending} |
| a handover that does not discharge the pending head (proved as for a final head) | REFUSED | parse: the proof lacks the discharge's parts |
| (ii) step 1 with a forged child (forge_W1n) | ACCEPT | {1: pending} |
| (ii) the handover of that head (faithful resharing of the forged child) | REFUSED | Ligero; first violated "handover discharge: old W1(r_k) = c1p" |
| new committee commits shifted weights and carries their evaluation | REFUSED | Ligero; first violated "handover: old W1(r) = new carry c1" |
| (i) shifted weights, honest carries (cN = old W(r) != new W(r)) | ACCEPT (pending) | {1: pending} |
| (i) the next step over those weights | REFUSED | spine Ligero; first violated "deferred claim of the parent W1: W1(r_prev) = c_prev" |
| honest proof for another new custodian set | REFUSED | column challenge mismatch (ctx) |
| Ligero q[0] + 1; a new carry root replaced; one byte flipped; truncated | REFUSED | Ligero / column challenge / Ligero / parse |
| honest handover (630,808 B at d = 4; 51 s to prove) | ACCEPT | {1: pending}, the rotated head pending |
| a second opening of the old head | REFUSED | life counter (LifeExhausted) |
| (iv) a closing proof right after the rotation | ACCEPT | {1: final (closing proof)} |
| the OLD committee's step 2 after the rotation | REFUSED | parent commitment is not the previous step's child |
| (iii) step 2 by the new committee over the pending rotated head | ACCEPT | {1: final (step 2 opened its child), 2: pending} |

- Status is keyed by step. After a rotation at step k the key k means the rotated head, as the proof lane specified.
  The old head's own "final (the handover opened its child)" is overwritten by the new head's "pending".
- **Vectors for the native port.** `DL_DETERMINISTIC=7 handover_vectors.py OUT 4 demo-x2de` (634,264 B) adds:
  - the head's pending points;
  - the old carries' shares (labels c1, c2, one life spent);
  - the new carry shares;
  - the new pending.

**Native, byte-equal** [EXECUTED on the Mac]:
- `handover::prove_defer` / `verify_defer` / `decode_defer` (a0a07f36). `HANDOVER_DEFER_VECTORS=<vec-e/d4-demo-x2de>
  cargo test --release -p darkproof --features tcp,test-det --test handover_defer_vs_python`:
  - 634,264 B, equal to Python's at all six parties (prove 0.39 s, verify 0.09 s); byte_len equals the length;
  - the new pending, and each new party's carry shares, equal Python's;
  - refused: a flipped byte; the proof offered as for a final head (parse); other pending points (Ligero); a forged
    old carry (the discharge, Ligero); another new set;
  - a second opening of the old head is refused by the life counter.
- `Ledger::rotate` under DEFER (c18e41f8). It verifies against the head's pending and records the new pending.
  `handover_vs_python` on the demo-x2de dump of run_handover.py: on all 10 rotation attempts the native verdict and
  reason equal Python's, and so does every ledger file after them, byte for byte. The demo and demo-x2 dumps still
  pass.
- Non-DEFER is unchanged: handover_prover_vs_python demo-x2 d = 4 (512,480 B == Python) and handover_production pass.
- darkhand (17637da3): `old_side_e` / `new_side_e` take the ledger's `Option<&Pending>`; `serve::with_old_carries`;
  `NewCustodian.defer` is the next step's DeferIn. The deploy lane wired them into dl-custodian.

**Soundness of one handover, at d = 4096** (`handover_soundness.py ledger-x2 4096 ledger-x2d ledger-x2de`; union bound;
|F| = p^2), beside the proof lane's per-step table (proof.md, "Soundness, per step"):

| term | ledger-x2 | ledger-x2d | ledger-x2de |
|---|---|---|---|
| Schwartz-Zippel old W(r) = new W(r), per matrix (24 variables) | 2^-117.4 | 2^-117.4 | 2^-117.4 (old W(r) = cN here, cN = new W(r) at the next opening) |
| PCS proximity, old W1, W2 | 2^-104.0 each | 2^-104.0 each | 2^-104.0 each (one opening, n = 263,380) |
| PCS proximity, new W1, W2 | 2^-104.0 each | 2^-104.0 each | not opened here (the next step's term) |
| PCS columns, old W1, W2 | 2^-128.2 each | 2^-128.2 each | 2^-127.2 each (two evaluations of one opening) |
| PCS columns, new W1, W2 | 2^-128.2 each | 2^-128.2 each | none |
| carries c1p, c2p (old), cN1, cN2 (new): proximity / columns | none | none | 2^-110.7 / 2^-128.2 each |
| Ligero proximity (n = 3,284) / linear / quadratic | 2^-110.3 / 2^-122 / 2^-122 | same | same |
| Ligero columns | 2^-128.2 | 2^-128.2 | 2^-128.2 |
| **the handover** | **2^-102.0** | **2^-102.0** | **2^-103.0** |

- x2d changes only the step's sumchecks (ZKSC "mask"). The handover has none, so its terms equal x2's.
- Under x2de the discharge W(r_k) = c_kp is an exact identity at a point fixed before step k's child could be chosen.
  Its Schwartz-Zippel term is step k's rank-1 term (the proof lane's table), not the handover's.
- Not in the table: Merkle binding (computational) and Fiat-Shamir grinding.

## 10. Cryptographic erasure (darkhand::vault) and the TLS key in the memory scan [EXECUTED on bb2, 45bb7255]
The coordinator's additions: in-place overwrites are not erasure on ZFS or SSDs, so the claim is cryptographic.
- **The file key.** A per-epoch file key K (32 B, OS RNG) seals every secret state file with ChaCha20-Poly1305
  (ring).
  - Format: `DLVAULT1 | nonce | ct | tag`. The AAD is `dl-vault|<name>|<role>`. The role is the file name up to its
    first '_' or '.': ckpt, carry, tls.
  - K lives in process memory and in the uid's persistent kernel keyring (KEYCTL_GET_PERSISTENT), named
    `dl-vault:<model>:<seat>:<epoch>:<TLS cert fingerprint, 16 hex>`.
- **Restart.** A planned restart (`serve --resume`, forge's pause) loads K from the keyring (`Vault::load`). K never
  reaches a disk.
- **Bounds** [DERIVED]:
  - a reboot loses K, so a reboot erases the files: a run cannot resume across a reboot;
  - the persistent keyring expires after kernel.keys.persistent_keyring_expiry seconds of disuse (259,200 s = 3
    days on forge and bb2). **Policy:** every access resets that timer. `Vault::seal_to` refreshes it on every
    checkpoint (each step), and `Vault::load` refreshes it on every resume. So the key is lost only by a pause with no
    step and no resume for more than 3 days. Forge's nightly pause is 1 hour. A seat that does pause longer fails
    closed at its resume:
    - `load` reports "the file key EXPIRED ... unrecoverable, fail closed" (EKEYEXPIRED), or "no file key ...
      expired with its keyring";
    - it never runs on a missing key.
    `tests/vault.rs an_expired_file_key_fails_closed` (bb2) simulates the expiry with KEYCTL_SET_TIMEOUT 1 s: the
    load before it succeeds (control), and the load after it fails with the EXPIRED message. A run that must pause
    longer raises the sysctl first (root);
  - neither forge nor bb2 has swap (SwapTotal 0). Check hbox's swap before routing a seat there;
  - two seats under one uid on one box (the development layouts on bb2) can read each other's K. The deployment is
    one custodian per machine (or per uid).
- **Erasure.** `destroy()` runs KEYCTL_INVALIDATE (the key goes at once, whatever links it) and zeroes the in-memory
  copy.
- **old_side checks.**
  - K joins the memory canaries, plus a 16-byte text canary for the disk scan.
  - Copies of the small sealed state files are taken before the erasure, and must open under K (control).
  - After the erasure: `present(name)` is false, `Vault::load` fails, and no copy opens, by keyring or by the zero
    key.
  - Report fields: vault_before_erasure, vault_destroyed, vault_after_erasure.
- **The TLS private key in the canaries.** The `tls_*.key` state file (PKCS#8 DER, opened under K when sealed) gives:
  - the DER's words;
  - the P-256 scalar as big-endian bytes, as LE limbs, and as ring's Montgomery limbs (d 2^256 mod n).
  `tests/tls_canary.rs` shows that ring's EcdsaKeyPair, the object rustls signs with, holds exactly the Montgomery
  limbs; another key's are not in it.
- **Executed.**
  - `dl-hand local <work> 256 ledger-x2 27400` on bb2: 22 of 22 checks hold.
    - Vault key: 12 memory hits before the erasure, 0 after.
    - Keyring invalidated, name absent after.
    - The sealed TLS copy opens by nothing.
    - The TLS kinds have 0 hits before the erasure in dl-hand local, which holds no live TLS config. The deployed
      seat's live rustls key is the control there.
  - `tests/vault.rs` on bb2: a second process loads K from the keyring and opens the file; after destroy it cannot.
- **Split with the deploy lane (agreed).**
  - Deploy: checkpoint / read_checkpoint, the carry file and the TLS key go through the vault; join and self-handover
    create the next epoch's vault; `serve::with_vault` hands the old one to old_side.
  - Prep, later: tapes and owner messages under the same key, or MP-SPDZ's Player-Data on tmpfs.

## Continuation (handover lane, 2026-11-07; for a successor)
State: every handover piece is on dev (latest darkhand commit 4ce5d616). The three-box run waits on the deploy lane
(a68410e60434efcda) wiring the hooks below into native/darkdeploy/src/bin/dl-custodian.rs. The step-k child
commitment ("carry") lives there in `Prove.carry`, not in darkstep::serve::CustodianState.

### Hooks requested from the deploy lane (sent 2026-11-07)
1. **`--handover-at k`, old seat i, after step k:**
   - `let parts = darkhand::serve::old_from_serve(state, prove.carry.take().unwrap(), files, true, captured_opt);`
   - `files` = ckpt_P<i>.bin, the tape file and tls_<i>.key.
   - Then `darkhand::side::old_side(&common, move || parts.old, || <6-party TLS Net, index i>)`. Write the report
     JSON, then exit.
2. **Join mode, new seat j:**
   - `darkhand::side::new_side(&common, j, <new 3-party TLS Net>, <6-party TLS Net, index 3 + j>, tape, epoch + 1, 8, None)`.
   - Build the next CustodianState from `nc.party`, `serve::shares_rows(&nc.w, d)`, `nc.key` / `nc.keys` (asked for
     `CustodianState::from_parts`), and set `Prove.carry = Some(nc.carry)`.
   - Seat 0 calls `Ledger::rotate(new_set, &nc.new_roots, &nc.proof)`.
3. **`common`:** `darkhand::side::Common { pr, lp (built AFTER field::set_p), d, n_old: 3, n_new: 3, ctx: ledger.handover_context(&new_set), rns, t }`.
4. **Allocator:** `#[global_allocator] static A: darkhand::erase::ZeroOnFree = darkhand::erase::ZeroOnFree;` in dl-custodian.
5. **Self-handover after an SPDZ abort:**
   - `old_from_serve(.., false, None)` keeps `parts.he` and `parts.net3`.
   - Run two threads with 64 MiB stacks: `old_side` at index i, and
     `new_side(.., parts.net3, net6(3 + i), NEW tape, epoch + 1, 8, Some(parts.he.key))`.
   - new_set = old_set.

### Three-box checks still to write (once the command lines exist)
The local versions are `dl-hand local` / `local-self` (darkhand/src/bin/dl-hand.rs). Port each check to read the
seats' report JSONs. Each seat runs on its own box: bb2, forge and hbox, with hbox under swarm-build and on /othersys.

| check | how |
|---|---|
| all six seats exit 0 and hold the same proof | `proof_sha256` in each seat's report |
| the ledger accepts the rotation; its head is the new roots | seat 0's report (`rotation`, `ledger_head_is_new_roots`); also reopen the ledger file with darkproof Ledger::open |
| MAC check under the new key; opened W equals the twin | new seats' `mac_check`, `opened`, against the train lane's plaintext twin at step k |
| memory scan before (control) and after erasure, per old seat | `scan_before_erasure.hits > 0`, `scan_after_erasure.hits == 0`, `available == true` (Linux /proc on every box) |
| old seat decrypts its captured ct before erasure, not after | pass `captured` = one HE_CT it sent in step k (the ct and the sha256 of its plaintext) |
| state files gone | `state_files_left == []`; then `ls` the seat dir on its box |
| restarted old seat holds nothing | port `dl-hand restart` (loads key, tape and checkpoint files from the seat dir; tries to decrypt its old ct and a new seat's ct) and run it on each old box after the handover |
| d = 4096 | the same at full width (about 2 GB per seat) |

### Since the continuation was written (985197b8)
- **New check after re-authentication.** new_side's check opens nothing secret now: one masked random combination
  per matrix, then the MAC check. A failed MAC check is an Err; tested with `DLH_CORRUPT_MAC=1`.
- **`test_reveal`.** The 7th argument of new_side is `test_reveal`, which is TEST ONLY (dl-hand passes 8).
  dl-custodian must pass 0.
- **Deploy lane's wiring (not yet pushed when written).** Its command lines are in its message of 2026-11-07:
  - old seat: `dl-custodian serve ... --prove --handover-at K --mesh6 .. --tls6 DIR6`;
  - new seat: `dl-custodian join J ... --after-step K --mesh6 .. --tls6 DIR6 --handover-tape FILE --prove`;
  - self-handover: `--self-handover-tape FILE --recover-mesh .. --recover-mesh6 .. --tapes2 PAT --owner-msgs2 PAT`.

### Pending: the proof lane's bundle cut (a1cf256613423191a, announced 2026-11-07)
The cut gives profiles ledger and demo SPLIT "balanced", MERKLE "multi" (multiproofs) and K_L 512.
- **Follows automatically:** the handover codecs on both sides (proofwire schemas and walk; wire.rs readers and
  writers).
- **Breaks:** `handover::byte_len` hardcodes the old layout (one path per column). Rederive it from wire::mp_needed,
  or replace it with the encoder's length; it is asserted in handover_vs_python and the dl-handover bench.
- **To re-run once it lands:**
  - regenerate the handover_vectors.py vectors and the HANDOVER_DUMP dirs;
  - run handover_prover_vs_python, handover_vs_python and handover_production;
  - re-run with the old vectors under "<profile>-sq";
  - redo the d = 4096 bench.

### Run-level abort test (self-handover)
- **Steps:** run darkstep or dl-custodian for k steps, inject an SPDZ abort mid-step k+1 (a MAC-check failure; the
  deploy lane's attack hook), then self-handover at k. The run continues from k under the new MAC key and fresh
  preprocessing.
- **Pass:** the revealed weights after the last step equal the train lane's plaintext integer twin bit for bit, and
  the ledger has epoch + 1 with the same custodian set.
- **Needs:** the deploy lane's `--handover-at` and join mode in self mode; the train lane's twin; prep-lane tapes
  under the new alpha (the ideal dealer in dl-hand stands in until then).

### Reproduce what is green
- `HANDOVER_PROVER_VECTORS=<dir> cargo test --release -p darkproof --features test-det --test handover_prover_vs_python`
  The vectors come from `DL_DETERMINISTIC=7 python3 handover_vectors.py <dir> <4|16> <demo|ledger>`.
- `HANDOVER_VECTORS=<dirs> cargo test --release -p darkproof --test handover_vs_python`
  The dirs come from `HANDOVER_DUMP=<dir> run_handover.py 4 <profile>`.
- `cargo test --release -p darkproof --test handover_production`
- On forge, under `nice -n 15 systemd-run --scope -p MemoryMax=12G`: `dl-hand local|local-self <work> <d> <profile> <port>`.
  Use ports below 32768, since forge's ephemeral range collides above it.
- `dl-handover bench 4096 <profile>`

## Continuation, gen 2 (handover lane, updated 2026-11-07 ~09:45 UTC; for a successor)
State: darkhand at 09fd154d. Handover proof in F_{p^EXT} at 1bfb04a3.

**Erasure on the boxes:**
- run9 / run12b (rotation) and run11 / run11b (self-handover) were checked; sections 7 and 8 have the results.
- Every check is green except the after-erasure memory scan. Each red there had an identified cause, now fixed:
  - live caller frames: the deploy lane now boxes the state and runs the handover from main after scrub_stack_all;
  - the inlined setup frame (09fd154d);
  - public-genesis false positives (e9c14b1f, 09fd154d).
- **Next:**
  - run12c (rotation) and a self-handover rerun, built at or after 09fd154d, on prep's fresh chunks;
  - the deploy lane (gen 3, afcd36ed0af383db4) messages at launch and when the seats exit.
- **The checker command**, from the Mac (`--self` for a self-handover):

      python3 native/darkhand/scripts/check_handover.py <scratchpad>/dl-gen5/deploy2/runs/<run>.json OUT --profile ledger-sq \
        --tools dregg-forge=/srv/lanes/dl-gen6-handover/target-e514/release/dl-hand bb2=/home/build/lanes/dl-gen6-handover/target-e514/release/dl-hand

  - The tools are built at ed88a249. Rebuild them if the run's darkproof wire format changes: use `git archive
    <commit> native` into scratch, rsync it to `<lane>/src-<x>`, then `cargo build -p darkhand --bin dl-hand` under
    the box's scope.
- **Python rotation check:** `python3 handover_replay.py <profile> <new seat ledger> <handover_e1.bin>`, run in
  `<lane>/py-ca46` on forge or bb2 (not with -I).
- **Report to the coordinator (aa3209e8d10294bc2)** when run12c and the self rerun are all green.
- **Shell gotcha:** in Monitor and Bash commands, zsh does not word-split `set -- $x`. Wrap such loops in `bash -c`.
  An earlier zsh monitor stayed silent because of this.

**F_{p^2}:** done for the handover (1bfb04a3).

**Cut E discharge through the handover (next quest; profiles demo-x2de / ledger-x2de, DEFER; proof lane
aafff52532f04d20a; its interface is proof.md §21-22, 2adc6652):**
- **Old side:**
  - the head's W1, W2 (w_shape, one life, base 0) are opened once, at the pending points;
  - the carries c1p, c2p (carry_shape(p, True), second life) are opened at the zero point, and their roots are
    checked against `deferred_of(Ledger.pending)["carry_roots"]`;
  - the constraints are those of close_constraints: Y(W at r_k) - C(carry) = 0.
- **Ledger** (proofwire.py, the edit assigned to me): rotate passes `deferred_of(self.pending)` to the handover
  verifier, and `_replay` calls `discharge("handover")` on a rotate record.
- **Open question, asked of the proof lane:** the new commitment's lives. Either (a) the new W keeps two lives and
  the next step accepts that parent shape, or (b) my preference: the handover leaves the new head pending through
  new carries cN = new W(r), committed by the new committee, and the next step discharges them.
- **Decided (proof lane gen 6, aafff52532f04d20a): (b).** Its conditions:
  1. **Fiat-Shamir order.** The new committee's W roots are absorbed BEFORE r is drawn; today's handover already
     absorbs every root before _schedule. The roots of cN1 and cN2 are absorbed after r and before any challenge
     their constraints use (the Ligero's, the PCS columns).
  2. **Record schema.** The rotate record's `pending` is exactly `pending_json(out)`:
     - points keyed "W1" and "W2" (flat F_{p^EXT});
     - `carry_roots` under the keys a step's pending uses (the next step reads them as CARRY_IN c1p, c2p), so the
       new carries map onto those keys.
     - In `_replay`, on a rotate record: `discharge("handover")` of the old head first, then
       `self.pending = rec.get("pending")` and `self.status[self.step] = "pending"`.
     - Drop the "rotation refused: the head is pending" refusal only once HO.verify_bytes takes
       `deferred_of(self.pending)` and checks it.
  3. **Refusal rows wanted:**
     - (i) a new share altered so new W(r) != cN: the rotation is accepted as pending, and the next step is refused
       at the discharge;
     - (ii) the old head's carry not satisfied (forge_W1n on the last step): the handover is refused;
     - (iii) a step after the rotation under the pending head is accepted, and the head is final after it;
     - (iv) a close right after a rotation discharges it.
- **Native E:** the proof lane's helper a93e0325 is porting E. The native handover discharge calls the same
  deferred-eval path once that lands (the proof lane sends the commit).

**Open:**
- the LowGear-Secrets alpha form, which the prep lane reports;
- the TLS key is not canaried in memory;
- the ZFS / SSD bound on disk erasure.

## Continuation, gen 3 (handover lane, 2026-11-07 ~11:45 UTC; for a successor)
**Quest status:**
1. Erasure is green on both reruns: run12c, a rotation under ledger-x2, 74/74; run11c, a self-handover under
   ledger-x2de + RS, 37/37. Both are in §7 and were reported to the coordinator.
   - Python's handover_replay of run12c: ROTATION PASS (852 s, about 28 GB, under a 32 GB scope on bb2).
2. Cut E through the handover is done and reported:
   - Python 63106924;
   - native a0a07f36 (prove_defer / verify_defer, byte-equal);
   - Ledger::rotate c18e41f8 (equal to Python on the demo-x2de dump);
   - darkhand 17637da3 (old_side_e / new_side_e / with_old_carries; wired by deploy in dl-custodian 11e84d91).
3. The soundness table under x2 / x2d / x2de is in §9.
- The coordinator's additions:
  - vault 45bb7255 and checker 1056e227;
  - keyring refresh and expiry fail-closed 888958d3;
  - TLS canaries.
  The deploy lane wired the vault (c24b75fd: vault-init, --vault, --keep-erased-copy). The first vault rotation on
  the boxes is not run yet. When it is, run the checker (rotation mode: the vault checks and `dl-hand vault-present`
  run automatically when the report has them), and check the --keep-erased-copy files open under nothing: write a
  small `dl-hand vault-open NAME FILE ROLE` if needed.

**Tools:**
- dl-hand at d01c914a: /srv/lanes/dl-gen6-handover/target-d01c914a/release/dl-hand (forge) and
  ~/lanes/dl-gen6-handover/target-d01c914a/release/dl-hand (bb2). Rebuild when a run's wire format changes:
  `git archive <c> native` -> `src-<c>`, then `cp -a target-<old> target-<c>`, then `cargo build --release -p
  darkhand --bin dl-hand` under the box's scope.
- Build darkhand / darkproof on a clean `git archive HEAD native` overlay in scratch (`dl-gen5/handover/wt`). Other
  lanes' uncommitted edits in the shared tree often break the build there.
- Vectors: `vec-e/d4-demo-x2de` (handover_defer_vs_python) and `dump-e` (handover_vs_python, cut E rotations).

**Not done / open:**
- Prep's tapes and owner messages under the vault (or MP-SPDZ Player-Data on tmpfs). Raise it with the prep lane
  (now a8fd625fd8dbd4f54; a5caa478 is retired).
- hbox: check its swap before routing a seat there (the vault's memory-only claim needs no swap, or encrypted swap).
- The vault checks ran on deploy's rehearsal "reh" (§7). Its 9 sealed erased copies open under nothing. Its 9 reds
  were fixed in c9771f4a (relaunch criterion; the TLS DER canary's public words). Wanted: one rotation on darkhand
  c9771f4a to confirm 0 after-erasure hits on the boxes. That is reh2, run by the deploy lane, now a21cca37f7d4f4bb7
  (afcd36ed is retired).
  - Tools with vault-open: target-vo on bb2, at c9771f4a's darkhand.
  - Forge's target-vo predates the canary fix. That matters only for dl-hand local; the checker's tools just read
    reports.
