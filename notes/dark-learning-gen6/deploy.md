# dark-learning gen 6, deploy lane (xbox): the three-machine deployment and the run orchestrator

Owns: native/darkstep src/net.rs, src/node.rs, src/bin/*, src/coins.rs, src/bfv.rs and src/he.rs (taken over from the
retired gen-5 zkpopk lane for the coin fix), the multi-step party loop, TLS, deployment scripts under native/deploy/.

## The coin break and its fix

[EXECUTED] Found 2026-11-07, reading the production party path: a `darkstep party` process (no `test-det`) drew
every secret HE coin from PUBLIC seeds:
- the ungated key, `OwnKey::new(rns, 100 + i)`: s, a, e and every later encryption coin from random.Random(100 + i);
- the ceremony key's encryption coins, `OwnKey::from_ceremony(rns, 100 + i, ..)`: random.Random(100 + i). This is
  MT19937, and a is published in every ciphertext, so the stream is recoverable even with a secret seed;
- every HE return, `bfv::make_return`: the mask M, u, e0, e1 and the 2^F flood from random.Random("hm|11|call|
  transpose|me|j|o") (matvec) and random.Random("ho|13|call|me|j|ab|b|kind") (outer).
Attack [DERIVED]: recipient j recomputes sender i's M and decrypts i's return to the plaintext W_i x_j (for matvec)
and the outer products, in every call. That recovers i's share of W1 and W2. Done to both peers, it gives one
corrupted custodian the whole model. In the ungated mode j also recomputes s_i.

Fix (a996539e..; see commit below):
- `darkstep::coins::Coins` = `Py(PyRandom)` (the harness's reference streams) | `Prf` (SHA-256 counter mode under a
  32-byte OS key, one stream per label; uniform samplers by rejection, the same distributions).
- `OwnKey.rng: Coins`, plus `OwnKey.return_key: Option<[u8; 32]>`. HE returns take `key.return_coins(label)`: the PRF
  under return_key with the same label, or the reference stream when it is None.
- New constructors: `OwnKey::new_secure(rns)` and `OwnKey::from_ceremony_secure(rns, s, b, a)`. They draw every coin
  from the OS, and `refresh_return_key()` is called per step. The old `new(seed)` and `from_ceremony(seed, ..)` stay
  as the reference.
- `Prof::secure_coins`: the `party` subcommand always sets it. Only `run_local`, the in-process test harness where
  all three custodians share one process anyway, keeps the reference streams, so vs_reference stays bit-exact.
- `deal` (public-seed ideal dealer) and `reveal` (reassembles the model) now exist only with the cargo feature
  `test-harness`; a deployed party binary has neither.

Tests [EXECUTED, Mac]:
- `cargo test --release -p darkstep --features test-harness --test party_coins`: 2 passed (ungated and gated T = 309,
  N = 4096, d = 64). Each test runs two production runs of the real `darkstep party` binary, three processes each,
  on the same reference tapes and inputs. In both runs all three ACCEPT, agree on one transcript, and refine the
  spec. The share digests differ from the reference's and between the two runs, and so do the transcripts.
- Negative control: with `secure_coins = false` in the binary, the test fails at "broadcast shares carry fresh masks"
  (the transcript equals the Python reference).
- Correction to what I first told the coordinator: the transcript does NOT stay equal to the reference under fresh
  coins. It holds each party's broadcast share, which carries the masks, and the Freivalds/MAC coins are drawn from
  it, so later opened values change too. A public-value check of the run therefore has to be on the step's outputs
  (the plaintext rerun against the released output, and the per-step proofs), not on a transcript digest.
- Unchanged: `--test vs_reference` 6 passed, `--test bfv_vs_python` 1, `--lib` 1 (the PRF samplers' ranges and
  spread, stream separation), `--features test-det --test vs_reference_gated` 3 passed.

## Randomness audit: every source a production party binary reaches

(a) = public by design, (b) = OS / CSPRNG unless test-det.

| source | where | kind |
|---|---|---|
| HE return M, u, e0, e1, flood | bfv::make_return via he.rs matvec/outer | (b) PRF under OwnKey.return_key (fixed here; was public seed) |
| BFV key s, a, e (ungated) | OwnKey::new_secure | (b) PRF under an OS key (fixed; was random.Random(100 + i)) |
| BFV encryption coins (a, e of each sender ct) | OwnKey.rng | (b) PRF (fixed; was random.Random(100 + i)) |
| ceremony r, salt | dzkpopk Custodian::new, hex32_os | (b) /dev/urandom |
| ceremony key s, e | dzkpopk Custodian::make_key, OsHiding | (b) /dev/urandom (seeded only under test-det) |
| ceremony seed, a_j = public_a(seed/j) | dzkpopk Ceremony | (a) public by design (joint commit-reveal) |
| ZKPoPK hiding (masks, salts) | dzkpopk rng::OsHiding | (b) /dev/urandom; DetHiding only under test-det |
| ZKPoPK challenges | dzkpopk transcript | (a) Fiat-Shamir |
| Freivalds rho (matvec check) | he.rs, random.Random(hash of transcript) | (a) Fiat-Shamir, after the openings it checks |
| outer-check coins | he.rs, after the G commitments | (a) Fiat-Shamir |
| MAC-check rho | party.rs mac_check, random.Random(hash of openings + transcript) | (a) Fiat-Shamir, after the openings |
| MAC-check sigma commitment nonce | party.rs, getrandom | (b) OS |
| SPDZ tapes (alpha_i, triples, masks) | tape.rs Dealer, PyRandom(DEALER_SEED = 5) | TEST ONLY: `deal` needs `test-harness`; the deployment's tapes come from darkprep (MASCOT, prep lane) |
| owner input masks r | tape.rs owner PyRandom(OWNER_SEED = 9) | TEST ONLY, as above; deployed: darkprep owner.rs (r = a of a checked input triple) |
| inputs | step::inputs(d) = random.Random(d) | TEST data; the train lane's data-owner feed replaces it |
| TLS keys and certificates | (to come: rcgen + ring SystemRandom) | (b) |

Notes:
- MV_SEED = 11 and OU_SEED = 13 survive only as parts of the PRF labels, so the streams stay separate. They are not
  key material.
- The test dealer is MT19937 under one seed: a custodian holding its own tape could recover the stream and with it
  the other tapes, whatever the seed. That is why it is test-only and not merely re-seeded.
- darkprep: no randomness is drawn natively. Tapes and owner masks are assembled from MP-SPDZ's MASCOT output
  (MP-SPDZ seeds its PRNGs from the OS) [SOURCE: prep lane; to be confirmed by it].
- darkhand (handover lane): `new_side` used `OwnKey::from_ceremony(seed)`, an MT stream; the replacement is
  `OwnKey::from_ceremony_secure` (told to the handover lane).

## The stack (landed on dev, all tested on the Mac)

- **TLS** (612d3382): mutual TLS 1.3 (rustls + ring), pinned self-signed certificates generated per run on each seat
  (`darkstep tls-keygen I DIR`; the key is 0600 and never copied). A peer is identified by its certificate. Party j
  dials every lower seat and accepts every higher one, so the highest seat (hbox, behind NAT) only dials.
  [EXECUTED] `--test tls_mesh`: an unpinned dialer and an unpinned listener are refused; a relay on one link sees no
  plaintext (control: over plain TCP it does).
- **Resumable links** (c958b908): seq/ack per frame, reconnect under the same identities within DS_RECONNECT_SECS,
  resend from the peer's next expected frame. A drop during the MAC check or a Freivalds opening is an abort, and
  ABORT frames stop the peers at once. [EXECUTED] `--test tls_mesh`, `--test serve_steps`: cutting a link mid-step
  resumes it and the steps equal the twin; cutting at the first Freivalds opening makes all three refuse.
  [OPEN] the self-handover after an abort (handover lane).
- **Multi-step custodians** (`darkstep serve`, d769e1c7; library `serve::serve_main` with a per-step hook,
  17d541d5): CustodianState carries the weight shares, checkpoints them after every step (its own file, 0600),
  pauses (custodian 0 decides; all exit 3) and resumes. Inputs come from the owner over TLS, and the custodians
  cross-check sha256 of the broadcasts. Genesis opens W1, W2, x, y; carried steps open only x and y.
- **Owner**: `dl-owner` (darkdeploy) takes its values from darktrain and its masks from darkprep's checked input
  tuples; `darkstep owner-test` serves the test dealer's broadcasts.
- **Per-step proofs** (`dl-custodian serve --prove`, 571825d0, rc 3fea96f4): the proof lane's prove_step runs
  inside each custodian over tag PROOF, and every custodian verifies the bundle against the chain. [EXECUTED]
  `-p darkdeploy --test prove_steps`: three proved steps at the ledger profile, d = 64; one bundle per step, it
  verifies and chains, a flipped byte is refused, and the weights equal the twin.
- **Custody check** (`native/deploy/custody_check.py SEATS.json`): no tape, key, checkpoint, share or owner-message
  file of seat s exists on another box or in another seat's dirs, checked by name and by sha256 content.
- **Wire cuts**:
  - d7484eff: HE returns modulus-switched to 2 primes, with c0 sent only at the decrypted coefficients.
    [EXECUTED] bit-exact with the Python reference at both profiles (transcript, shares, sigmas); he_ret falls to
    52.6% (N = 4096, L = 3) and 28.6% (N = 16384, L = 4). Control: 1 prime breaks decryption.
  - 12e9475f: seeded sender ciphertexts (c0 and a 32-byte seed for a) under the OS coins, half the HE_CT bytes.
  - [OPEN] packing the outer product's blocks 128 x 128 instead of 64 x 64 would fill all N = 16384 coefficients
    of each return (today 4,096 are used), so a quarter as many outer returns. That changes the layout, so it needs a
    new reference.

## Run 1: the first gated d = 4096 step on three machines over TLS (2026-11-07 03:43-04:25 UTC) [EXECUTED]

- **Seats.** Custodian 0 on dregg-forge (`systemd-run --scope -p MemoryMax=12G`, nice 15, 16 threads); 1 on bb2
  (user scope 12G); 2 on hbox (`swarm-build`, SWARM_MEM_MAX=16G, everything on /othersys). The owner (`owner-test`)
  is a separate process on bb2, in its own dir.
- **Setup.** Each seat generated its own TLS key; only the certificates were copied. Each tape was dealt on its own
  box (`deal-steps --only I`, the public-seed test dealer: a stand-in for the prep lane's MASCOT tapes).
  `custody_check.py`: ok (7 secret files, each only on its own seat's box). Ports reachable directly:
  forge 47300, bb2 47301 and 47309; hbox dials out.
- **Build.** The test-harness build, because the run ends in a test-only reveal: no deployed run does this.
- **Profile.** GEN6 program, N = 16384, L = 4, F = 175, d = 4096, gate T = 309, full ciphertexts (the "before").
- **Loads at start.** forge 0.7 (the prep lane's mascot/lowgear jobs present); bb2 31 (Lean, sbcl, sort and
  obend jobs of other tenants); hbox 1.1, its link Wi-Fi (wlo1), 23-48 Mbit/s up and about 57 Mbit/s down measured
  during the run. **The times are upper bounds.**

| | custodian 0 (forge) | 1 (bb2) | 2 (hbox) |
|---|---:|---:|---:|
| verdict | ACCEPT | ACCEPT | ACCEPT |
| step seconds | 2,476 | 2,476 | 2,476 |
| process wall | 2,516 | 2,513 | 2,511 |
| ceremony | 3.0 s | 2.7 s | 1.9 s |
| gate prove / verify | 21.2 / 16.8 s | 25.1 / 23.1 s | 21.3 / 17.7 s |
| CPU (process) | 883 s | 987 s | 844 s |
| peak RSS | 4.68 GB | 4.74 GB | 4.81 GB |

- **Phases (s).** input 1, matvec z1 61, trunc+lookup 6, matvec z2 50, trunc 2, matvec b 49, mul+trunc 1,
  **outer G2 1,155, outer G1 1,151**, MAC check 1. The outers carry the HE returns, and hbox's link sets their pace.
- **Bytes.** All six directed links are equal at 4,717 MB per step: he_ret 4,396, he_ct 315 (proofs included),
  open 4.9, ctrl 1.8. **hbox uploads 9.43 GB per step** (and downloads 9.43 GB).
- **Outputs.** One transcript (cf77c94017d9...). The test-only reveal (all three share files on bb2) prints
  `{"refines_spec":true}`.

## Run 2: the same step with the wire cut (2026-11-07 04:42-05:06 UTC) [EXECUTED]

Run 1's seats, tapes and identities (test reuse of the test dealer's tapes; no deployed run reuses
preprocessing). The binary is at c958b908 (resumable links), with `--ret-primes 2` and seeded ciphertexts.
- **Loads.** forge 0.3, bb2 9.6, hbox 1.2. During part of the run the prep lane's LowGear key setup shared
  hbox's link (about 1.8 GB each way by its count). **The times are upper bounds.**

| | run 1 (full) | **run 2 (cut)** | ratio |
|---|---:|---:|---:|
| step seconds | 2,476 | **1,352** | 0.55 |
| outer G2 / G1 seconds | 1,155 / 1,151 | 608 / 645 | 0.54 |
| matvec z1 / z2 / b seconds | 61 / 50 / 49 | 33 / 39 / 19 | |
| bytes per directed link | 4,717 MB | **2,352 MB** | 0.50 |
| he_ret per link | 4,396 MB | 2,173 MB | 0.494 |
| he_ct per link (proofs included) | 315 MB | 172 MB | 0.55 |
| hbox upload per step | 9.43 GB | **4.70 GB** | 0.50 |
| gate prove / verify (hbox) | 21.3 / 17.7 s | 20.8 / 17.1 s | |
| peak RSS | 4.7-4.8 GB | 4.6-4.7 GB | |

- **Bytes by phase, per directed link** (link counters sampled every 50 ms): matvec z1 44.4 MB, z2 44.4, b 29.2,
  truncations and lookups 4.6, **outer G2 1,114, outer G1 1,114**, MAC check about 0.
- All three ACCEPT with one transcript (998cce564bd0...).
- **Correction to the d = 64 ratio.** At d = 4096 every outer return already uses all N = 16,384 coefficients:
  the block is 256 x 64, since dr = min(d, N/64). So c0 cannot shrink, and the cut is the modulus switch alone,
  4 -> 2 primes, about 0.5. The 0.286 at d = 64 came from c0 sent at only 4,096 coefficients. The [OPEN] packing
  item above does not apply at d = 4096.
- **Further cut [DERIVED, not built].** After the switch, the flood noise is about 2^53 against a budget of
  Q_2/(2t) ~ 2^60. The low bits of each residue are therefore noise. Rounding c0 to its top ~70 bits and c1 to
  its top ~85 bits (c1 is multiplied by s, so its rounding error grows by up to N/2 = 2^13) would save a further
  ~35% of the returns. It needs the exact error bound, a bit-packed wire format and the bit-exact test.

## Asymmetric seats (the coordinator's question 1) [DERIVED]

Each HE cross term a_i ⊗ x_j (outer) or W_i x_j (matvec) can run in either direction. One option: j encrypts
its operand under its own key and i returns Enc_j(a_i ⊗ x_j + M) masked by i's fresh M. The other: i encrypts
and j returns. The returner uploads the d²-sized returns; the encrypter uploads only its d-sized ciphertexts
(with their ZKPoPK) and downloads the returns.
- **What each seat learns.** In either direction the decryptor sees a product one-time-padded by the
  returner's uniform M, and the flood (2^F) hides the returner's plaintext operand from the noise. The returner
  sees only IND-CPA ciphertexts under a registered, ZKPoPK-checked key. The views are symmetric, so reassigning
  directions changes no seat's view. Every cross term must still cross the link between its two seats: hbox's
  share cannot be resharded to forge and bb2, because under a dishonest majority the two would then hold it.
- **What it buys.** The bytes on hbox's link per step are fixed (4 cross terms per outer involve hbox); only
  the up/down split changes. Today hbox uploads 4.70 GB and downloads 4.70 GB. Sending every hbox term the other
  way would give about 0.3 GB up and about 9.1 GB down. Measured, hbox has 23-48 Mbit/s up and about 57 down, and
  Wi-Fi shares airtime between the two directions. The best split puts about 35% of hbox's terms on its uplink:
  about 3.3 GB up against 6.1 GB down, on the order of 15% shorter on a full-duplex link and less on Wi-Fi.
- **Reference.** Reassigning directions changes which party draws which mask and in what order, so the shares
  and the transcript change and the reference needs a new mode (the outputs, i.e. the revealed weights, do not).
- **Verdict.** It is not worth building before the bit-rounding cut (~35%, every link) and the choice of box for
  seat 2. A wired box in place of hbox would remove the bottleneck outright: forge <-> bb2 is 5-7 Gbit/s.

## Run 3: the same step with seat 2 on bb2, no home link (2026-11-07 05:19-05:21 UTC) [EXECUTED]

Custodian 0 on forge; custodians 1 and 2 on bb2, each its own process, scope and PID file. Seat 2 used its own
key and tape, generated and dealt on bb2 in its own dir; hbox's key was not copied. The binary and flags are run 2's
(`--ret-primes 2`, seeded ciphertexts). Loads: forge 0.2 (the prep lane's lowgear-party.x at 2% CPU); bb2 15.6
(other tenants' sbcl, Lean and obend jobs; the proof lane SIGSTOPped its jobs for the window). Upper bounds.

| | run 2 (hbox seat 2) | **run 3 (seat 2 on bb2)** |
|---|---:|---:|
| step seconds | 1,352 | **94.0** |
| outer G2 / G1 | 608 / 645 s | 26.6 / 26.8 s |
| matvec z1 / z2 / b | 33 / 39 / 19 s | 16.2 / 16.2 / 6.2 s |
| bytes per directed link | 2,352 MB | 2,352 MB |
| gate prove / verify (seats 0, 1, 2) | | 21.3/16.9, 29.3/23.4, 29.0/23.6 s |
| ceremony | | 0.7-0.8 s |
| peak RSS | | 4.6-4.7 GB |
| CPU per process | | 678-846 s |

All three ACCEPT with one transcript. The home link costs about 1,258 s of the 1,352 s step (14x).

## Noise-bit rounding of the switched returns [EXECUTED]

- **Reference first.**
  - `research/dark_learning_2026_11_06/wire_round.py` holds the switch to two primes (last prime first, centered
    remainders, as natively) and the rounding of c0 to a multiple of 2^b0 and c1 to 2^b1. `decrypt_wire` is the
    recipient's decryption.
  - Mode `wire=(primes, b0, b1)` of `he_matvec.HEMatvec` and `he_outer.HEOuter`, next to per_return_rng.
    `native_ref.py` turns it on with `DL_WIRE=round` (the derived bits) or `DL_WIRE=round<db0>,<db1>` (the bits
    plus offsets: the controls).
- **The bound** (`wire_round.round_bits` = `bfv::round_bits`, the same integers).
  - Decryption is exact while the noise is under Q2/(2t) - 1.
  - The noise after the switch is E = ceil((2^F + 32 N t) Q2 / Q) + 1 (the flood and the product and
    Enc_pk(0) noise, scaled), plus (1 + N)/2 per dropped prime, plus 2^(b0-1) from c0, plus N 2^(b1-1) from c1
    (the ternary s, worst case).
  - Each rounding gets at most half of what is left.
  - (b0, b1) = **(59, 47) at N = 4096 / L = 3 / F = 118** and **(59, 45) at N = 16384 / L = 4 / F = 175**.
- **Bit-exact.**
  - Python, N = 4096, L = 3, F = 118, d = 8 with DL_WIRE=round: ACCEPT, refines_spec true, and the transcript and
    all parties' share digests equal `native_ref_results/native_ref_N4096_L3_F118_d8.json`.
  - Native, `--test vs_reference rounded_returns_stay_bit_exact`: transcript, shares and sigmas equal the
    reference at both profiles. At d = 64, he_ret is 0.560 (N = 4096) and 0.596 (N = 16384) of the switched size.
- **Controls.**
  - Python: c1 at b1 + 9 = 56 and c0 at b0 + 2 = 61 both REFUSE ("HE matvec: Freivalds check failed").
  - Native, `rounding_past_the_bound_breaks_decryption`: b1 + 9 fails.
  - Native thresholds at the ledger profile (`darkstep local ... --ret-round B0,B1`):
    - c0: 60 accepts, 61 breaks. The bound (59) is one bit from the edge.
    - c1: 52 accepts, 53 breaks. The bound (45) is worst case (|r1 s| <= N 2^(b1-1)), and the typical
      |r1 s| ~ sqrt(2N/3) 2^(b1-1) sits about 7 bits lower.
  - So "one bit past the bound breaks" holds for c0 (at +2), not for c1. c1's bound is a worst-case bound with
    about 7 bits of slack, and it is kept.
- **Hiding.** The switched, rounded return is a deterministic public function of the full return, which the
  decryptor already receives in the reference protocol. By data processing it learns nothing more. The flood is
  added before the switch, so its ratio to the returner-dependent noise is unchanged. **The statistical-hiding
  term in privacy_budget.py does not change (0).**
- **At d = 4096 [DERIVED from the bit widths].** The wire carries c0 in 64 bits and c1 in 78 bits per
  coefficient, against 2 x 64 each switched. That is 0.555 of run 2's returns: he_ret about 1,206 MB per link,
  about 1,430 MB per link in total, and hbox uploading about 2.9 GB per step. With run 2's rate on hbox's link
  the step would take about 820 s. Not yet measured.

## Continuation (deploy lane, xbox, 2026-11-07 ~05:30 UTC, at ~400K tokens)

**State on dev.** See the commits above. In the working tree, not yet committed: `lb: true` in dl-custodian and
per-link proof bytes in serve (`after_step_bytes_to`). Commit both by name once
`-p darkdeploy --features test-harness --test prove_steps` passes with lb on.

**Boxes and dirs (this lane's).**
- forge `/srv/lanes/dl-gen6-deploy/` (builds native/ and native2/; run1..run3; Rust via
  `/srv/lanes/dl-gen5/rust/env.sh`);
- bb2 `~/lanes/dl-gen6-deploy/` (native/ and native2/, run1..run3, owner dirs);
- hbox `/othersys/lanes/dl-gen6-deploy/` (bin/darkstep-test, darkstep2-test, built on bb2 and copied: glibc
  2.34 symbols suffice). Never write to hbox's / (24-25 GB free).
- Every process ran under a PID file in its run dir. All have exited.
- Ports: forge 47300 (seat 0), bb2 47301 (seat 1), owner 2.31.77.40:47309; hbox only dials. Check them with
  `nc` before each run.

**Launch recipe** (run2/run3 dirs show it): per seat, `darkstep tls-keygen I tls` on its own box; copy only the
`cert_*.der`; give each seat its tape (prep chunk or test dealer `--only I`); owner process; then on each box
`DS_THREADS=16 nohup nice -n 15 <scope> darkstep serve I 16384 4 175 4096 D A0 A1 A2 --tls tls --owner O
--steps K --gate 309 --program gen6 --tape ... --ret-primes 2 [--ret-round] & echo $! > serveI.pid`. Scope: forge
`systemd-run --scope -p MemoryMax=12G`, bb2 `systemd-run --user --scope -p MemoryMax=12G`, hbox
`SWARM_MEM_MAX=16G swarm-build`. Record loads first. The `( cd X && nohup ... & echo $! > pid )` form must write
an absolute pid path: a relative one once landed in /build.pid on forge (moved to the lane dir).

**Next, in order.**
1. Commit lb + per-link proof bytes. Rebuild the run binary with `--ret-round` and measure the rounded step through
   hbox (derived about 820 s).
2. First proved three-box step: `dl-custodian serve ... --prove --genesis-cfg train_genesis_gen6.json`, public
   genesis, on the prep lane's real carried chunk (they will send CHUNKDIR paths:
   /srv/lanes/dl-gen6-prep/chunks/c4096-0, /home/build/lanes/dl-gen6-prep/chunks/c4096-0,
   /othersys/lanes/dl-gen6-prep/chunks/c4096-0; tape_I.bin with the proof section if made with --proof, plus
   step-0/owner-msg-P<I>.bin). The owner is `dl-owner --train CFG` (data from research/.../data/mnist), with
   custodians passing `--owner-msgs CHUNKDIR/step-{k}/owner-msg-P<I>.bin`. Measure forge's peak RSS with the proof
   (must stay under 12 GB; do not raise the cap). The tape cursor moves past the proof section in the hook.
3. Ledger node and release: the proof lane's `Ledger` with `Genesis { program: prm (pg set), roots }`,
   `check_public_genesis(cfg_bytes)` before accept. Release via darkproof::run::release_mpc / prove_release (ask
   af16018ee013ba703 for the call shape).
4. Handover: the handover lane (a1742ccf37483c10d) asked for a 6-party Net (connect_tls works for n = 6), the
   RESHARE tag (landed, = 5), `--handover-at k` calling darkhand::old_side(state, net6) and a join mode for the new
   seats, and the ZeroOnFree allocator in the party binary (that one belongs in dl-custodian). The self-handover
   after an abort comes from them.
5. The prep lane uses `darkstep relay` (9869e89f) for MP-SPDZ over the resumable mesh.

**Agents.** Coordinator aa3209e8d10294bc2; prep aa66b1f8ba5714d45; proof af16018ee013ba703 (a02632eb retired);
train ad36593ec00657538; handover a1742ccf37483c10d.

### Continuation addendum (after the section above)

- **Bug fixed in the working tree** (net.rs connect_tls): a dial error containing "Connection refused" (the peer
  not yet listening) was treated as a TLS refusal and failed at once. Now only "TLS handshake" errors are fatal and
  TCP refusals are retried. This was the hang in prove_steps when it ran after another test.
- **Uncommitted, to commit by name once `-p darkdeploy --features test-harness --test prove_steps --
  --test-threads=1` passes:** native/darkstep/src/net.rs (the fix), native/darkstep/src/serve.rs (per-link
  proof bytes, `after_step_bytes_to`, `rebase_sent`), native/darkdeploy/src/bin/dl-custodian.rs (lb: true),
  native/darkdeploy/src/bin/dl-reveal.rs plus darkdeploy/Cargo.toml (test-only twin check: `dl-reveal CFG STEPS
  DIR0 DIR1 DIR2` compares darktrain::weights_digest), native/darkdeploy/tests/prove_steps.rs (lb in its own
  verify; run with --test-threads=1).
- **Real MASCOT chunks from the prep lane** (wired layout: seat 0 forge, seats 1 and 2 bb2):
  - no proof section: forge `/srv/lanes/dl-gen6-prep/chunks/w4096-/srv/lanes/dl-gen6-prep/wired0/mpspdz`; bb2
    `/home/build/lanes/dl-gen6-prep/chunks/w4096-/home/build/lanes/dl-gen6-prep/wired{1,2}/mpspdz` (paths as
    given, launcher placeholder);
  - with RC + LB proof section (3,192,275 triples): forge `/srv/lanes/dl-gen6-prep/chunks/w4096p-P0`; bb2
    `/home/build/lanes/dl-gen6-prep/chunks/w4096p-P1`, `-P2`.
  - Each holds tape_<I>.bin and step-0/{tape_<I>.bin, owner-msg-P<I>.bin}. The MAC key persists per seat
    across chunks unless a run aborts.
  - Next milestone: `dl-custodian serve I 16384 4 175 4096 D A0 A1 A2 --tls tls --owner O --steps 1 --gate 309
    --program gen6 --tape CHUNK/tape_I.bin --owner-msgs CHUNK/step-{k}/owner-msg-P<I>.bin --genesis-cfg
    train_genesis_gen6.json --ret-primes 2 [--prove]`, with `dl-owner --listen O --tls OWNERTLS --t
    2305843009210515457 --d 4096 --train CFG.json` (CFG = the genesis json plus "data": the MNIST dir and
    "seed_order": 2), then `dl-reveal` (test build) against the twin. The prep lane generation 2
    (a5caa478aac6a0658) is making LowGear chunks lg4096{,p}-P<I> and has hbox's link 14:00-15:00 UTC.
- **Handover API landed** (handover lane, 6338de5e, doc at native/darkhand/src/serve.rs top): old seat
  `darkhand::serve::old_from_serve(state, carry, files, true, ct)` then `side::old_side(..)`; new seat
  `side::new_side(..)` returns party, wires, carry, keys and the proof for Ledger::rotate. The self-handover after
  an abort uses the same calls with `false`. The carry (the step's child PcsParty map) is `Prove.carry` in
  dl-custodian, so the handover hook belongs there, next to the proof. RESHARE = 5 has landed (9869e89f); tell
  them so they point darkhand::side::RESHARE at it. They also ask for the ZeroOnFree global allocator in the
  party binary (dl-custodian).
- **Release layout** for the prep lane: none in darkstep yet. It comes from the proof lane's release section
  (58,679,793 triples at M = 64, RC + LB).

## Deploy lane generation 2 (successor of ae142f25, from 2026-11-07 06:17 UTC)

### The launcher: native/deploy/run.py and sync.sh

- `deploy/sync.sh HOST DEST`: rsync of the native workspace (no target dirs, no .git) to a box; prints the commit.
- `deploy/run.py RUN.json setup|check|gate|launch|launch-seats|status|collect|stop`, driven from the Mac over ssh.
  - setup: every seat (and the owner) makes its own TLS identity in its own run dir (`ROOT/NAME/seatI`,
    `ROOT/NAME/owner`); only certificates travel (through the Mac); the genesis cfg and owner cfg are copied.
  - launch: the disk gate (below), loads recorded (`loads_start.json`), then owner and seats started with
    `cd DIR || exit 1; nohup CMD & echo $! > NAME.pid`. Bug fixed on the way: `cd DIR && nohup CMD &` backgrounds
    a subshell, so the PID file held the subshell's PID and ssh stayed open until the job ended.
  - per process a sampler (own PID file) writes `NAME.mon`: epoch, VmRSS kB, its cgroup's memory.current and
    memory.peak, load1, every 5 s.
  - collect: step_*.json, serve_*.json, logs and samplers into OUT/NAME/, plus summary.json (per step and party:
    verdict, step seconds, CPU, peak RSS, transcript prefix, bytes per link, proof seconds/bytes, proof bytes per
    link; per party: sampled peak RSS and cgroup peak).
  - gate (also run by launch): per box, df of the run root against the projected bytes (checkpoint, carry, latest
    bundle per seat; steps x bundle on the archive seat); refuses to launch if a box would end under its line
    (30 GB default; set `disk_line_gb` 25 for hbox's /othersys).
  - stop: by PID files only.
- dl-owner: new `--public-genesis` (step 0 inputs only x, y when the custodians start from the public genesis).

### Item 1: the gated d = 4096 step on the prep lane's real MASCOT chunk (run4, 06:29-06:32 UTC) [EXECUTED]

Seat 0 forge (12G scope, nice 15, 16 threads), seats 1 and 2 separate processes on bb2 (12G user scopes), owner
`dl-owner --train` on bb2 (own dir, own 8G scope). Chunk w4096 (MASCOT, Steady: inputs x, y only), public genesis
(`dl-custodian serve ... --genesis-cfg train_genesis_gen6.json`), program gen6, T = 309, `--ret-primes 2`.
Test-harness build at bb20a601 (for `--test-keep-shares`). Loads: forge 0.3-3.6, bb2 8-58 (other tenants).

| | seat 0 (forge) | 1 (bb2) | 2 (bb2) |
|---|---:|---:|---:|
| verdict | ACCEPT | ACCEPT | ACCEPT |
| step seconds | 139.3 | 139.3 | 139.3 |
| CPU (process) | 666 s | 809 s | 809 s |
| peak RSS (VmHWM) | 3.67 GB | 3.71 GB | 3.70 GB |
| cgroup memory.peak | 3.76 GB | 5.02 GB | 4.14 GB |

One transcript (dd12d71b40e2b067...). 2,351.8 MB per directed link (as run 3). The step is slower than run 3's
94 s because bb2 ran at load 50-58. Test-only `dl-reveal` (forge's share file copied to bb2 through the Mac, then
removed): revealed sha256 21af72e2... equals the twin after 1 step; controls: the twin at 0 and at 2 steps differ.

### Item 2: the same step proved (run5, w4096p, 06:36-06:39 UTC) [EXECUTED]

As run 4 with the chunk w4096p (its RC + LB proof section, 3,192,275 triples) and `--prove`, DP_TRACE=1.

| | seat 0 (forge) | 1 (bb2) | 2 (bb2) |
|---|---:|---:|---:|
| step seconds | 91.3 | 91.3 | 91.3 |
| proof (prove_step) | 12.70 s | 12.66 s | 12.70 s |
| own verify | 3.91 s | 4.01 s | 3.88 s |
| after-step hook | 17.6 s | 17.7 s | 17.6 s |
| proof bytes on tag PROOF per link | 133.8 MB | 133.8 MB | 133.8 MB |
| CPU (process) | 726 s | 926 s | 934 s |
| peak RSS (VmHWM) | **7.64 GB** | 7.89 GB | 7.99 GB |
| cgroup memory.peak | **8.02 GB** | 8.30 GB | 8.40 GB |

- Forge stays under its 12 GB cap (not raised): 8.02 GB at the scope's peak.
- One bundle, 250,915,469 B (sha256 f955a4f2...), at all three. That is ~500 GB of bundles at 2,000 steps; the
  coordinator's interim rule: each replica keeps only the latest bundle, one seat archives all, and run.py gates on
  the projected disk use. The proof lane is asked for a cut.
- The MASCOT side of this one proved step sent 81.4 GB from forge (prep lane's chunk-P0.json): at d = 4096 the
  preprocessing, not the online step, dominates the bytes.

### Run 6: two proved steps back to back (w4096p2, 06:50-06:55 UTC) [EXECUTED]

The prep lane's 2-step proved chunk, wired layout, bb2 at load 25-63 (other tenants). Proofs inline (in the
step hook; not yet pipelined). Binary at bb20a601.

| step | step seconds | prove (P0/P1/P2) | own verify | peak RSS after (P0/P1/P2) |
|---|---:|---:|---:|---:|
| 0 | 126.0 | 18.9 / 19.2 / 19.3 s | 4.4-4.8 s | 5.45 / 5.65 / 5.62 GB |
| 1 | 110.3 | 20.9 / 20.9 / 20.7 s | 4.0-5.2 s | 7.80 / 8.06 / 7.95 GB |

Whole process: wall 298 / 297 / 293 s, CPU 1,458 / 1,840 / 1,847 s, VmHWM 8.32 / 8.36 / 8.29 GB, cgroup
memory.peak 9.43 / 9.40 / 9.33 GB (forge's under its 12 GB cap). One transcript per step.

### dl-custodian as built for the run (generation 2) [EXECUTED on the Mac, see tests]

- **Ledger replica per custodian** (`DIR/ledger_P<I>.jsonl`, darkproof::ledger::Ledger): opened with the Genesis
  record (program with PG = sha256 of the genesis cfg, the committee's names = sha256 of their certificates, the
  public-genesis roots) and `check_public_genesis(cfg)`, at start for a public genesis (so that even a refusal
  before the first proof can rotate) or at the first proof for an owner-input genesis. Each bundle is `accept`ed
  into it, which verifies against the head. The proof's ctx is (model, ledger epoch, ledger step + 1).
- **Bundle storage**: each replica keeps `proof_latest_P<I>.bin`; `--proof-archive ADIR` on one seat keeps all
  (`proof_e<epoch>_s<step>.bin`).
- **Carry checkpoint**: `carry_P<I>.bin` (0600, darkproof::pcs::write_carry, after each accept); `--resume`
  reads it (read_carry) and reopens the replica, so a proved run resumes across forge's nightly pause.
- **Pipelined proofs** (`--pipeline-proofs --proof-mesh A0,A1,A2`): the step hook copies the step record and the
  proof-section triples out (darkproof::run::from_darkstep_n), moves the cursor, and hands the job to a worker
  thread that owns the proof chain (carry, replica) and its own three-party TLS mesh; step k + 1 runs meanwhile.
  At most one proof is in flight; every exit (end, pause, handover, refusal) first drains it. Per proof:
  `DIR/proof_<k>_P<I>.json`; step k + 1's report carries step k's proof report.
- **Rotation** (`serve ... --handover-at K --mesh6 A0..A5 --tls6 DIR6`, and `join J ... --after-step K
  --handover-tape FILE`): after step K and its proof, the serve loop ends (StepHook::stop_after) and hands the
  state to the hook (StepHook::finish). Old seat i: a ciphertext under its key is made (and checked to decrypt) for
  the post-erasure attempt; the 3-mesh is shut; the 6-mesh is joined at index i; its ledger replica (public) is
  sent to the new seats; darkhand::side::old_side reshares, proves and erases (files wiped: ckpt, carry, TLS key,
  tape), scans memory and tries to decrypt; DIR/handover_P<I>.json; exit. New seat j: its 3-mesh with the new
  committee, the 6-mesh at 3 + j, the ledger from all three old seats (must be equal), adopted and checked,
  darkhand::side::new_side (its own ceremony, resharing, joint proof, re-authentication under its MAC key with
  test_reveal = 0, nothing opened), `Ledger::rotate`, then darkstep's He from the ceremony
  (node::he_from_ceremony) and `CustodianState::from_parts`, and the loop from step K + 1 on its own tapes.
- **Self-handover after an abort** (`--self-handover-tape FILE --recover-mesh A0,A1,A2 --recover-mesh6 A0..A5
  --tapes2 PAT [--owner-msgs2 PAT --chunk-first2 K0]`): a refused step ends the loop (the mesh is aborted); each
  seat reloads its checkpoint (the state before the refused step; serve now also checkpoints right after the
  public genesis), opens a fresh 3-mesh, gives its new role an in-process TLS identity (certificate exchanged on
  the pinned fresh mesh), runs old_side (index i) and new_side (index 3 + i, its HE key kept) as two 64 MiB
  threads on the 6-mesh, rotates its replica to the same set at epoch + 1, and redoes the refused step on the new
  key's tapes. One recovery per run.
- **Release** (`--release --release-data MNISTDIR [--release-m 64 --release-tape FILE]`): after the last step,
  darkproof::run::release_custodian (policy run::mnist_policy) and `Ledger::release`; only C is opened.
  DIR/release_P<I>.{bin,json}. Not yet run: the proof lane measures ~29 GB per custodian at M = 64 and is cutting it.
- ZeroOnFree is the global allocator of dl-custodian. `--profile NAME` picks the proof profile (the proof
  section's size must match the tapes'). Patterns take {c} and {j} with `--chunk-steps S [--chunk-first K0]`.
- serve: `StepHook::{stop_after, finish}`, `serve_state` (the loop on a held state, shared by serve, join and the
  self-handover), `identity`, `connect_mesh`, `step_path`; a hook error now aborts the mesh (a peer no longer waits
  forever on the next step's vote).
- dl-owner `--public-genesis`; the owner serves one committee per session (the test drives two sessions).

Tests (Mac, ledger profile N = 16384, L = 4, F = 175, d = 64, T = 309, public genesis):
- `--test handover_steps -- --test-threads=1`: 2 passed (111 s).
  - rotation_to_a_new_committee_after_step_0: three old processes, three `join` processes; all exit 0; old seats'
    ckpt, carry, TLS key and tape are gone and each reported its key decrypting before the handover (control);
    new seats accept step 1 at epoch 1, their replicas hold the rotate record; the revealed weights (test only)
    equal the twin after 2 steps and differ from the twin after 1 (control).
  - self_handover_after_an_abort_redoes_the_step: seat 1 shifts an outer return in step 0 (`--attack
    wrong_return:1`), all three REFUSE ("HE outer: Freivalds check failed"), recover, rotate to the same set at
    epoch 1 under a new MAC key, redo step 0 and run step 1 (both proved at epoch 1); weights = twin after 2 steps.

### Generation 2, second batch (e5143080) [EXECUTED on the Mac]

- `serve --wipe-spent`: after step k's checkpoint is durable, the step's tape and owner-msg files are zeroed, synced
  and unlinked (a hard-linked twin name is cleared too: the inode is overwritten). At a rotation every remaining
  tape/owner-msg file of the epoch joins old_side's wipe list, and the tape files, chunk dirs, D and the TLS dir
  join `old.scan_paths` (the handover lane's disk canary scan, darkhand 49ae41c7).
- The handover proof is kept: DIR/handover_e<E>.bin (+ archive); its sha256 is the ledger's rotate record.
- dl-owner `--next-tls DIR`: one session per committee.
- Release: M defaults to the genesis cfg's `release.M` (52 since the train lane's 0b0631a5). `dl-custodian
  test-deal` makes one seat's test-dealer tape (steps, proof sections, release section) from darktrain's real
  inputs; darkstep's Dealer keeps only that seat's entries (`only`), so a d = 4096 release tape fits one seat.
- Tests: `--test release_steps` 1 passed (d = 64: one proved step then the release; one C at all three, on each
  ledger replica, equal to the plaintext count over the revealed head). Caveat: at d = 64 the cfg has tile 0, so the
  policy images encode to zero and the check is weak; the d = 4096 release run is the real check.
  `--test handover_steps` 2 passed again (adds: handover_e1.bin's sha256 is on the ledger; the spent tape is gone).
- Profiles: dev's default "ledger" profile now (bundle cut db65cc57) needs 3,194,067 proof triples per step; every
  chunk made so far has 3,192,275 = "ledger-sq". The first dry-run launch (run8) died at step 0 on this ("the
  tape's proof section is shorter than the proof needs"); relaunched as run8b with `--profile ledger-sq` on the same
  chunks. Step 0's preprocessing was thereby used twice, on identical inputs (public genesis, the same example): a
  dry-run artefact, not to be repeated in the measured run.

### The 10-step dry run (run8b, 07:25-07:47 UTC) [EXECUTED]

Wired layout (seat 0 forge, seats 1 and 2 bb2, owner bb2), the prep lane's 10-step proved MASCOT set (five 2-step
chunks w4096s10-c{0..4}, `--chunk-steps 2`), public genesis, `dl-owner --train` (MNIST, order 2), program gen6,
T = 309, `--ret-primes 2`, `--prove --pipeline-proofs --proof-mesh ... --profile ledger-sq`, archive on seat 0,
`--pause-utc 10:00-11:00`. Production build (no test harness) at 8299f315. Loads: forge 0.9-12.9, bb2 14.5-68.5
(other tenants). Every number is an upper bound.

| step | step s | proof s (P0/P1/P2, beside the next step) | verify s | waited for previous proof (P0/P1/P2) |
|---|---:|---:|---:|---:|
| 0 | 90.2 | 71.2 / 71.3 / 71.2 | 36.3 / 59.3 / 64.0 | 0 / 0 / 0 |
| 1 | 109.3 | 108.0 / 87.9 / 82.9 | 36.1 / 43.8 / 44.2 | 0 / 19.4 / 23.9 |
| 2 | 111.3 | 82.0 / 74.3 / 74.1 | 35.8 / 47.2 / 46.9 | 6.1 / 13.8 / 14.1 |
| 3 | 106.6 | 98.0 / 87.0 / 87.1 | 36.3 / 50.0 / 51.9 | 1.9 / 13.1 / 13.0 |
| 4 | 119.8 | 93.0 / 79.1 / 77.1 | 36.6 / 44.4 / 43.5 | 2.1 / 16.2 / 18.0 |
| 5 | 103.5 | 81.5 / 73.7 / 74.7 | 35.8 / 43.2 / 41.3 | 8.4 / 16.7 / 15.6 |
| 6 | 101.9 | 81.9 / 74.1 / 76.5 | 35.8 / 52.1 / 51.6 | 5.8 / 13.9 / 11.5 |
| 7 | 105.8 | 112.0 / 95.4 / 96.1 | 35.6 / 45.0 / 46.5 | 2.7 / 19.2 / 18.7 |
| 8 | 124.2 | 85.1 / 75.8 / 74.0 | 36.4 / 41.8 / 41.1 | 5.1 / 14.3 / 16.0 |
| 9 | 99.4 | 51.6 / 45.9 / 46.8 | 34.6 / 34.0 / 34.3 | 9.7 / 15.3 / 14.6 |

- All 30 step verdicts ACCEPT, one transcript per step; every custodian's ledger replica holds genesis + 10 steps;
  10 bundles (250.9 MB each, 2.4 GB) in seat 0's archive.
- Wall for 10 steps: 1,254 / 1,256 / 1,250 s, i.e. 125 s per step with the proofs pipelined, against ~138 s per
  step inline in run 6 (step + hook). The proof beside a step takes 45-112 s instead of 13-21 s alone and the verify
  35-64 s instead of 4-5 s: the step's 16-thread pool and the proof's rayon pool share 16 vCPU on forge and the busy
  bb2. Pipelining saves ~10%; a smaller proof pool (or the proof on idle cores) is the next lever.
- Bytes: 2,350.0 MB per directed link per carried step on the main mesh (2,351.8 at step 0); the proof's bytes
  are on the proof mesh: 33.46M field elements sent per custodian per step (268 MB, ~134 MB per link).
- CPU per process: 8,195 / 10,006 / 9,964 s (~800-1,000 s per step).
- Memory: VmHWM 8.61 / 8.98 / 9.00 GB. **Forge's scope memory.peak reached 12,884,901,888 B, exactly its 12 GiB
  MemoryMax**: the anon peak is 8.6 GB; the rest is page cache (tape reads, 251 MB bundle and checkpoint writes per
  step), which the kernel reclaims at the limit (no OOM kill, the process finished). The cap was not raised. Before
  the long run: drop the page cache of written files (fadvise DONTNEED after each bundle/checkpoint write), or move
  the archive off forge, and watch memory.events.
- Not in this dry run: a handover (run9 next) and the release (proof lane cutting its memory).

### The coordinator's two must-fix items before the long run [EXECUTED on the Mac]

1. **Single-use preprocessing, enforced.** `darkstep::serve::read_tape_once` hashes every tape file it loads
   (sha256 streamed while parsing) and, with a registry set (`--consumed-log FILE`; run.py passes
   `ROOT/consumed.jsonl`, one per box), refuses a digest already in it and appends {sha256, path, key digest, unix,
   pid} under a file lock with fsync before the tape is used. Every load goes through it: the first tape, each step's
   tape in the loop, after --resume, a join's tapes, the self-handover's, the release tape. dl-custodian refuses to
   start without `--consumed-log` outside test builds. `--test single_use`: 1 passed (step 0 runs; a fresh start on
   the same tapes is refused by all three before any step, with "preprocessing already consumed"; seats 1 and 2
   share a box registry; control: `--resume` onto step 1's fresh tapes runs and ACCEPTs).
2. **Profile against the chunk before step 0.** dl-custodian `check_profile`: the first step's tape header must
   hold exactly the step's entries for the program (darkprep::schedule::tags) plus the profile's proof section
   (run::step_section); otherwise exit 2 before any socket. `dl-custodian step-entries N L F d --program gen6
   --profile P` prints it: ledger-sq 12,456,319 entries (3,192,275 triples) = the prep lane's chunks exactly;
   ledger (A + B) 12,461,695 (3,194,067). Checked: a ledger-sq header under `--profile ledger` is refused with the
   message, the same header under `--profile ledger-sq` passes the check. [OPEN] pinning the profile in the ledger's
   genesis record is the proof lane's format (asked).
- Page cache: `serve::drop_cache` (fdatasync + POSIX_FADV_DONTNEED) after every tape read, checkpoint, carry and
  bundle write.

### Item 4 on the three boxes: the rotation (run9, 07:58-08:08 UTC) [EXECUTED]

Old committee on the wired key (seat 0 forge, 1 and 2 bb2; chunk w4096h, 1 proved step), new committee on the
prep lane's wired-new key in other processes on other seats (new 0 bb2, new 1 forge, new 2 bb2; handover tapes
ho-new, then ho-new-steps for steps 1-2). Public genesis, dl-owner --train with `--next-tls` (two sessions),
`--profile ledger-sq --wipe-spent`, inline proofs; binaries at ca46c2fd.

| | old 0 | old 1 | old 2 | new 0 | new 1 | new 2 |
|---|---:|---:|---:|---:|---:|---:|
| step 0 / step 1 / step 2 seconds | 101.9 | 101.9 | 101.9 | 90.2 / 90.0 | 90.2 / 90.0 | 90.2 / 90.0 |
| prove / verify per step | 45.3 / 34.5 | 45.7 / 34.2 | 45.7 / 34.4 | 44.9-46.4 / 34.3-34.9 | 44.6-46.3 / 34.7-35.2 | 44.9-46.3 / 34.2-35.1 |
| old_side seconds (reshare, prove, erase) | 21.2 (1.8, 8.6, 0.8) | 23.7 (2.2, 8.2, 1.0) | 23.3 (2.1, 8.2, 1.0) | | | |
| join seconds (ceremony, reshare, commit, prove, re-auth) | | | | 17.6 (0.77, 0.48, 2.46, 2.85, 3.47) | 17.8 (0.96, 0.53, 1.88, 3.33, 4.55) | 17.6 (0.77, 0.50, 2.47, 2.80, 3.68) |
| VmHWM | 7.65 GB | 7.97 GB | 7.98 GB | 8.92 GB | 8.51 GB | 8.91 GB |

- One transcript per step; the handover proof is 129,790,908 B, the same at all six; the new seats' MAC check under
  their key is ok and each decrypts its own fresh ciphertext; every new replica holds genesis, step 1 (epoch 0),
  the rotate record, steps 2-3 (epoch 1).
- Old seats after the erasure: the captured ciphertext decrypts before and not after; no state file left; the disk
  scan finds 0 canaries (393,217 before, in ckpt and carry; the step's tape was already wiped by --wipe-spent).
- The handover lane's three-box checker: 68 of 71 green (restarted old seats find no key/checkpoint/carry/tape and
  exit at "own TLS key", verify-rotation on all three replicas with a flipped-byte control, equal replicas). Red:
  the after-erasure memory scan finds the alpha share 11-12 times on [stack] in each old seat: copies of the
  by-value CustodianState (its tape holds alpha_i inline) in the live frames serve_main_with -> serve_state ->
  finish -> rotate_out.
- Fix (local, Mac tests green): CustodianState is boxed from `new` / `from_parts` through serve_state, finish,
  rotate_out and self_handover; the old seat calls `old_side(common, darkhand::serve::rotation_setup(st, ..), ..)`
  and the self-handover `darkhand::serve::self_setup`, so the state is taken apart only in darkhand's scrubbed
  setup frame (on the old role's own thread in a self-handover). `--scan-extra PATH` adds e.g. the seat's MP-SPDZ
  dir to the disk scan; --wipe-spent also wipes the consumed handover tape.
- Cost found: proof 45 s / verify 34 s here and in the dry run against 12.7 / 3.9 s in run 5 (same d, profile):
  the ZeroOnFree allocator's byte-wise volatile zeroing. The handover lane has replaced it with memset-speed
  zeroing plus a compiler barrier (darkhand); the next run measures the recovery.

## Continuation (deploy lane generation 2, 2026-11-07 ~08:25 UTC)

**State on dev**: everything up to 68083b34 is pushed (plus `--erase-extra` in the working tree of dl-custodian.rs:
commit it by name with the next change). Boxes: forge `/srv/lanes/dl-gen6-deploy/` and bb2
`~/lanes/dl-gen6-deploy/` hold `ws/` (synced sources, `native/deploy/sync.sh`), targets `ws-target-r2/` (prod,
68083b34) and `ws-target-test2/` (test harness, 68083b34), run dirs run4..run11, `consumed.jsonl` (the box's
single-use registry), `data/mnist`. hbox `/othersys/lanes/dl-gen6-deploy/` has `bin/ws/darkstep` (test build at
bb20a601) and run7 (identities and test-dealer tapes for the rounded hbox step). Run configs and collected results
are in the scratchpad: `.../scratchpad/dl-gen5/deploy2/runs/run*.json` and `runs/run*/summary.json`.

**Launcher**: `python3 native/deploy/run.py RUN.json setup|check|gate|launch|status|collect|stop|resume`. A
config has seats (host, root, bin, scope, addr, tapes|tape, owner_msgs, env, extra, archive), owner, flags,
optional `handover` (at, steps_after, mesh6, new_seats with handover_tape, flags) and `owner_repeat`. Every
process: `<dir>/<name>.{cmd,log,pid,mon}`; stop only via `run.py stop` (PID files).

**Done**: items 1, 2 (run4, run5, run6), the 10-step pipelined dry run (run8b), the three-box rotation (run9, 68/71
in the handover lane's checker; the 3 reds fixed in 5898187e), the must-fix items (single-use registry, profile
check: b838f9dc).

**In flight / next, in order**:
1. run11: the d = 4096 self-handover after an abort (launched 08:19 UTC). Collect (`run.py runs/run11.json
   collect`), tell the handover lane (ac3b201ab6a366ff6), which runs its `--self` checker, and the coordinator.
2. run12: the rotation rerun on prep's w4096h2 / ho-new2 / ho-new2-steps (ready ~08:25), as run9 with bins
   ws-target-r2 and, per old seat, `--erase-extra` for its retired MP-SPDZ key files
   (`<prep>/wired<I>/mpspdz/Player-Data/Mascot-Secrets-p-61-*-P<I>-3` and `.../3-p-61/Player-MAC-Keys-p-P<I>`; list
   them by ssh at config time) and `--scan-extra <prep>/wired<I>/mpspdz`. Expect the [stack] reds gone and the
   prove/verify times back toward 12.7 / 3.9 s (the handover lane's zero_raw fix).
3. run10: the release memory measurement (proof lane a8ee5558dd7fe5a45): `dl-custodian test-deal` on each box
   (seat tapes of 1 step + release at M = 52, `--profile ledger`), seats 1 and 2 on bb2 at MemoryMax=40G, forge at
   12G, DP_TRACE=1; config drafted in runs/run10.json (deal first: `test-deal CFG 1 I DIR --genesis-cfg GEN
   --program gen6 --profile ledger --release [--public on seat 1]`, CFG = runs/deal_cfg_forge_m52.json on forge,
   owner_cfg_bb2_m52.json on bb2, copied into the seat dirs). Send the proof lane VmHWM, memory.peak, the logs.
4. Item 3, the rounded hbox step: run7 config (runs/run7.json) is set up and its tapes dealt; launch when the
   prep lane says hbox's LowGear key-setup traffic has stopped (~15:00 UTC), before its own hbox chunks.
5. Item 6, the measured run: N from the coordinator; prep throughput (~75 h of MASCOT for 2,000 proved steps at
   today's rate) is the binding constraint, so agree the N and the chunk schedule with the coordinator and the prep
   lane first. Use `--pipeline-proofs --proof-mesh`, archive on bb2 (coordinator: move it off forge), `--wipe-spent`,
   `--consumed-log`, `--pause-utc 10:00-11:00` + `run.py resume`, a handover at step k, `--release` at the end.

**Agents**: coordinator aa3209e8d10294bc2; prep a5caa478aac6a0658; proof a8ee5558dd7fe5a45; handover
ac3b201ab6a366ff6; train ad36593ec00657538.

### Run 11 (self-handover, d = 4096) and run 12 (rotation rerun) [EXECUTED]

- **run11** (08:19-08:27 UTC, test build for `--attack wrong_return:1` on seat 1; wired key chunk w4096h3, then the
  prep lane's wired-sh key ho-sh / ho-sh-steps): step 0 REFUSED at all three ("HE outer: Freivalds check failed");
  every seat recovered from its checkpoint; old role 50.6 / 76.5 / 77.6 s (reshare 2.7-2.8, handover proof 6.6-6.7,
  erase 0.17-0.23 s), new role 22.0 s, MAC check under the new key ok, handover proof 129,790,908 B; ledger
  replicas rotated to the same set at epoch 1; step 0 redone (138.8 s), step 1 (86.4 s), both ACCEPT with one
  transcript and proved at epoch 1. Prove 20-28 s and verify 9.5-10 s (the handover lane's memset-speed zeroing;
  45 / 34 s in run 9). The handover lane's checker: 31/37. Reds: (i) the binary on the boxes predated 68083b34, so
  the old role got no files and no scan paths (the refused step's tape is still on disk: this is how it shows);
  (ii) 5 real alpha residues per seat (the partially moved checkpoint struct in self_handover's frame, and the
  refused step's dead frames on the main thread); the rest were false positives on the public-genesis carry (fixed
  on its side, e9c14b1f). Fixed here: `reload_shares` takes only w and step from the checkpoint and zeroes its
  alpha_i in that frame; `side::scrub_stack(4096)` on the main thread before the roles spawn. Rerun pending fresh
  chunks on the wired-new committee.
- **run12** (08:32 UTC, rotation rerun on w4096h2 / ho-new2): died before the handover. New seat 1 (forge) dialled
  old seat 0's six-party port 47330 on the same box before it listened, and the socket connected to itself (TCP
  self-connect: 473xx is inside the ephemeral range 32768-60999): "TLS handshake ... got ClientHello". Stopped by
  PID files. Fixed: `resil::dial` and `serve::dial_owner` reject a socket whose local and peer addresses are equal
  and retry; run configs move to ports below 32768. It consumed w4096h2 and ho-new2 (the registry recorded both);
  the wired key's MP-SPDZ files were not reached.
- `native/deploy/sync.sh` now ships `git archive` of a commit, not the shared working tree (another lane's
  half-written darkproof edit would otherwise reach the boxes); binaries on a box are always one commit.

## Continuation, updated (deploy lane generation 2, 2026-11-07 ~08:50 UTC, near its context limit)

Supersedes the continuation above where they differ. Last commit ed88a249 (pushed); the working tree holds none of
this lane's changes. Boxes: `ws/` synced at ed88a249 on forge and bb2; builds `ws-target-r3` (prod) and
`ws-target-test3` (test harness) running at hand-off (`build-r3.log`, `build-r3.pid` in the lane dir); use these
for every next run (older targets r2/test2 lack the self-connect and self-handover fixes).

Next, in order:
1. **Release memory measurement (run10)** for the proof lane (a8ee5558dd7fe5a45). Test tapes are being dealt at
   hand-off: forge `/srv/lanes/dl-gen6-deploy/run10/seat0/deal/tape_0.bin`, bb2 `~/lanes/dl-gen6-deploy/run10/seat{1,2}/deal/`
   (seat 1 also `public_step0.bin`; logs `run10/deal<I>.log`, PID files `deal<I>.pid`), 1 step + release at M = 52,
   profile "ledger". Then: move `seat1/deal/public_step0.bin` to `run10/owner/`, set the run10.json bins to
   ws-target-test3, keep seats 1 and 2 at MemoryMax=40G and forge at 12G, DP_TRACE=1, `run.py runs/run10.json
   setup` then `launch`; NOTE run.py's setup makes `run10/seat<I>/tls` beside the existing `deal/` dirs. Report each
   seat's release_P<I>.json (C, mpc/prove/verify s, VmHWM), the sampler's cgroup peak and the DP_TRACE lines to the
   proof lane. If forge's seat is killed at 12G, that is the finding: tell the proof lane, do not raise the cap.
2. **Rotation rerun (run12b)** once prep has w4096h5 (old wired key) and ho-new3 (wired-new handover tapes); reuse
   ho-new2-steps for steps 1-2. Copy runs/run12.json, set tapes to w4096h5 / handover_tape to
   ho-new3-P<I>/step-0/tape_<I>.bin, bins ws-target-r3, and MOVE EVERY PORT below 32768 (seat addrs, mesh6) — probe
   them first with `timeout 20 nc -l -p PORT` under a PID file on one box and `/dev/tcp` from the other. Old seats
   keep `--erase-extra` for their wired-key MP-SPDZ files and `--scan-extra wired<I>/mpspdz`. Tell the handover
   lane (ac3b201ab6a366ff6) at launch and when the old seats exit.
3. **Self-handover rerun (run11b)** on the wired-new committee (seat 0 bb2, 1 forge, 2 bb2) with prep's wn-abort
   (aborted step), ho-sh2 (handover tape), ho-sh2-steps (redo + next), test build ws-target-test3; ports below
   32768; check on the box afterwards that the refused step's tape is gone (the files reached old_side) before
   reporting.
4. **Item 3 (rounded hbox step, run7)** when the prep lane reports the LowGear setup's traffic ended (~15:00 UTC):
   run7.json is set up, tapes dealt on each box; hbox needs a fresh `bin/ws/darkstep` from ws-target-test3 (scp -3
   from bb2) since run.py now passes `--consumed-log` (ignored by darkstep serve, harmless) and the self-connect
   fix matters for hbox's dial-only seat too.
5. **Item 6**: the coordinator's N, the run's profile ("ledger-x2" once the proof lane lands it: re-check
   `dl-custodian step-entries ... --profile ledger-x2` against the prep lane's chunk headers), the prep schedule,
   the archive on bb2, then the long run with pipelined proofs, a handover at step k, the release at the end.

## Deploy lane generation 3 (successor of a68410e6, from 2026-11-07 08:46 UTC)

### run12b: the rotation rerun at d = 4096 (08:56-09:05 UTC) [EXECUTED]

Old committee on the wired key (seat 0 forge, seats 1, 2 bb2; chunk w4096h5, 1 proved step), new committee on
wired-new (new 0 bb2, new 1 forge, new 2 bb2; handover tapes ho-new3, steps ho-new2-steps), public genesis,
`--profile ledger-sq --wipe-spent`, inline proofs, archive on bb2 (old seat 1, new seat 0), ports 28100-28135
(below the ephemeral range; ed88a249's self-connect fix). Build ws-target-r3 at ed88a249. Each old seat
`--erase-extra` its wired MP-SPDZ p-61 MAC-key and secrets files, `--scan-extra` its wired<I>/mpspdz.

| | old 0 | old 1 | old 2 | new 0 | new 1 | new 2 |
|---|---:|---:|---:|---:|---:|---:|
| step 0 / 1 / 2 seconds | 83.5 | 83.5 | 83.5 | 120.7 / 88.6 | 120.6 / 88.7 | 120.7 / 88.6 |
| prove / verify (s) | 18.8 / 9.7 | 19.2 / 9.3 | 19.2 / 9.3 | 19.6-20.3 / 9.2-9.5 | 19.8-20.3 / 9.5-9.6 | 19.6-20.3 / 9.3-9.7 |
| old_side s (reshare, prove, erase) | 24.6 (1.7, 7.8, 0.87) | 25.4 (2.7, 6.7, 0.82) | 25.1 (2.3, 7.1, 0.82) | | | |
| sampled VmRSS / cgroup peak | 7.05 / 8.00 GB | 7.77 / 8.10 GB | 7.31 / 8.19 GB | 8.41 / 10.36 GB | 7.70 / 9.63 GB | 8.54 / 9.79 GB |

- One transcript per step; 2,350.0 MB per directed link per step; the handover proof's sha256 75179af3... at all
  six. Prove/verify are back near run 5's (12.7 / 3.9 s alone) at 19-20 / 9-10 s beside the other tenants: the
  memset-speed zeroing recovered most of run 9's 45 / 34 s.
- Old seats after erasure: decrypt before yes, after no; key material left 0; the disk scan after erasure 0 hits
  in 122-124 files (500 MB), the --erase-extra MP-SPDZ files gone.
- The handover lane's checker: 71 of 74. Red: 4 alpha-share copies on [stack] at each old seat, 3-10 KB above
  old_side's scanning frame: live frames between main and old_side (serve_main_with's by-value tape, the
  loop's dead slots reused by later frames).
- Fixed (f2764017): the hook's `finish` defers a rotation or self-handover (`Prove.deferred`); serve_main_with /
  serve_state return, and main's `run_deferred` zeroes the whole main-thread stack below it
  (darkhand `side::scrub_stack_all`) before rotate_out / self_handover, so old_side and its callers start on
  zeroed memory and the live frames above hold boxes only. The rerun is run12c (prep's w4096h6 / ho-sh3 /
  ho-sh3-steps under ledger-x2, after forge's 10:00-11:00 pause).

### run10: the release at M = 52 on the three boxes: forge's seat OOM-killed at 12G (09:06-09:10 UTC) [EXECUTED]

Test-dealer tapes (1 step + release, profile "ledger", 4,115,450,583 B per seat: 229,623,632 release entries,
47,678,368 of them the release's proof section), ws-target-test3, DP_TRACE=1; seat 0 forge (12G), seats 1, 2 bb2
(40G). Seat 0's test-deal itself was OOM-killed at 12G on forge (08:45); dealt on bb2 instead and streamed to
forge (sha256 b7b147b2... checked at both ends; bb2's copy removed).
- Step 0 and its proof ACCEPT at all three (95.0 s). Seat 0's DP_TRACE peak during the step's proof was already
  11.92 GB (11.29 GB RSS at [spine] commitments) against 7.6 GB in run 5: the combined 4.1 GB tape is resident.
- 09:10:25 the kernel killed seat 0 (anon-rss 12,555,112 kB) as the release began; bb2's seats had reached
  VmRSS 11.3 / 12.6 GB, cgroup peak 15.7 / 15.8 GB. Stopped by PID files. The cap was not raised.
- Fixed (453d8e0f): the release reads its own tape (`--release-tape`) after the steps' tape is freed (as in a
  deployment, where the release's preprocessing is its own chunk); `test-deal --split-release`; serve frees the
  last step's tape before loading the next. `--test release_steps` 2 passed (combined; split).
- The proof lane's direction (a8ee5558): stream rather than fit (under ledger-x2 the release's proof section is
  81,031,546 triples): map the tape read-only, hand the proof slices, MADV_DONTNEED consumed ranges. [OPEN] the
  tape's sections are not 8-aligned on disk (24-byte header + n tag bytes before the shares): mapping needs a
  padded tape format (prep's writer) or unaligned reads behind an accessor; darkproof's run::from_darkstep_n /
  release_custodian copy triples out (proof lane offers borrowed slices).
- run10b: the per-seat release peak with all three seats on bb2 at MemoryMax=32G (a memory measurement, not a
  deployment), split tapes, its own test registry (`consumed_log`, public-seed test tapes only).

### run11b: the self-handover after an abort at d = 4096, on the wired-new committee (09:26-09:34 UTC) [EXECUTED]

Seat 0 bb2, seat 1 forge (`--attack wrong_return:1`, test build), seat 2 bb2; prep's wn-abort (the refused step),
ho-sh2 (handover tape), ho-sh2-steps (redo + next); ledger-sq, `--wipe-spent`, archive on bb2, ports
28200-28255; each seat `--erase-extra` its wired-new<I> p-61 MP-SPDZ MAC-key and secrets files (the
self-handover honours it since 64ae2ee9) and `--scan-extra` that dir. Build ws-target-test4 at 453d8e0f (the
handover deferred to main on a zeroed stack, f2764017). bb2 also dealt run10b's tapes meanwhile: upper bounds.

| | seat 0 (bb2) | 1 (forge) | 2 (bb2) |
|---|---:|---:|---:|
| step 0 refused, then old role s (reshare, prove, erase) | 71.9 (2.6, 6.2, 0.97) | 46.2 (2.2, 6.5, 0.84) | 67.1 (2.6, 6.0, 1.05) |
| new role s | 21.8 | 21.8 | 21.8 |
| redo step 0 / step 1 seconds | 149.0 / 101.8 | 149.2 / 101.8 | 148.6 / 101.8 |
| prove / verify (s) | 22.0-24.3 / 10.8-11.6 | 22.0-24.3 / 10.3-10.5 | 21.9-24.0 / 10.6-11.6 |
| sampled VmRSS / cgroup peak | 9.14 / 10.75 GB | 8.90 / 10.17 GB | 8.62 / 10.63 GB |

- One transcript per step at epoch 1; the refused step's tape and owner message and the wired-new MP-SPDZ
  key files are gone from the boxes after the run (checked by ls).
- The handover lane's `--self` checker: 33 of 37. No hits on the main thread's stack any more (the deferral
  works). Reds, both on its side: one alpha copy per seat in old_side's own frame (the generic setup closure
  inlined into it; fixed in darkhand 09fd154d with a non-inlined setup frame), and seat 0's 470,461 memory /
  514,737 disk "W1 share" hits, a false positive (at a step-0 abort custodian 0's share is the public genesis W;
  09fd154d drops share canaries for a public carry). Rebuilt at 8319ea81 for run12c and the next self rerun.

### For the long run (083eb2a6, fbeda41f) [EXECUTED on the Mac; not yet on the boxes]

- `--tape-wait S` (serve): the three vote on CTRL each step whether their chunk is complete (chunk-P<I>.json, which
  darkprep writes last) and wait together; `--test tape_wait` 2 passed.
- The new committee pauses and resumes: join and self-handover write the carry beside the checkpoint; a pause
  before a process's first step releases its unused tape in the registry; `serve --resume` in a new seat's dir
  continues at epoch 1. `--test handover_steps` 3 passed (the new one: the_new_committee_pauses_and_resumes_as_serve).
- run.py `drive`: launch, the new committee after step K - 1, resume after forge's window (either committee),
  stop by PID files on anything else, collect; `record.py hbox|wired` writes the run of record's config.
- [OPEN] hbox as the third box: behind NAT it only dials. The 3-meshes and the proof meshes are fine (it is seat
  2), but in the six-party handover mesh old seat 2 (index 2) must accept new seats 3-5. Needs a dial-only role in
  connect_mesh (not built) or a relay; and hbox has no ssh to bb2 or forge for a tunnel. A wired box needs neither.

### run10b: the release's working set, all three seats on bb2 at 32G (09:37-09:45 UTC) [EXECUTED]

Split test tapes (`test-deal --split-release`: tape_I.bin 211,848,839 B, release_I.bin 3,903,601,768 B, profile
"ledger", M = 52), `--release-tape`, DS_THREADS=10, DP_TRACE=1, ws-target-test4 (453d8e0f), a test-only registry
(`consumed_log`). bb2 at load 25-58 (other tenants). A memory measurement, not a deployment.
- Step 0 + proof ACCEPT (204.4 s); seat 0's step-proof peak 8.10 GB (run10, with the combined tape resident: 11.92).
- The release (seat 0's DP_TRACE): start RSS 10.71 GB (the release tape loaded); MPC 10.3 s, 12.93 GB; proof section
  taken and tape freed, 11.57 GB; replay of the release program 65.5 s, 15.52 GB (peak 16.12); middle witness
  (39,114,557 constraints, 33,353,164 Hadamard rows, 32,275,568 atoms), range rows, lookup circuit: 16.15 GB; then
  "vectors and commitments": VmRSS 16 -> 31 GiB in 5 s, and all three seats were OOM-killed at 32G (09:45:22).
- **The release at M = 52 needs more than 32 GB per custodian.** The resident tape (3.9 GB) is a minor part. The
  cut is the proof lane's (aafff525: R1 + R2 halve the release's Hadamard rows, and a helper cuts the middle's
  vectors phase, target < 10.5 GB under ledger-x2d); rerun on the same tapes when it lands.

### NAT seats: a seat that can only dial (coordinator's request) [EXECUTED on the Mac]

- `darkstep::net::dials(a, b, nat)`: without NAT seats the higher index dials the lower; a NAT seat dials every
  peer and they accept it (pinned TLS unchanged, the acceptor's pinned set is "who dials me"). Two NAT seats
  in one mesh are refused (`check_nat`: "need a relay"), unless they share a box and the lower one's address is
  loopback (hbox's old and new seat in the six-party mesh). `--nat LIST` (the committee's three-party meshes: main,
  proof, recovery) and `--nat6 LIST` (the six-party mesh), the same lists at every process; a NAT seat binds
  nothing unless a NAT peer on its box dials it.
- Tests: darkstep `--test tls_mesh -- a_nat_seat` (seat 0, which normally listens for both, binds nothing and dials;
  its advertised address is a port held by a listener that never accepts; the mesh moves bytes both ways; control:
  without the role the mesh cannot form; two NAT seats on two boxes refused); darkdeploy `--test handover_steps`
  rotation_with_a_nat_seat (--nat 0 --nat6 0,3) and self_handover_with_a_nat_seat (--nat 1 --nat6 1,4), with the
  NAT seats' addresses held by never-accepting listeners: both green, as are the other 3.
- record.py's hbox layout: --nat 2 --nat6 2,5, old hbox seat's six-party address 127.0.0.1.

### State files sealed under the epoch's file key (darkhand::vault, handover lane 45bb7255) [Mac: compiled; Linux tests pending]

- darkstep serve: a `Sealer` hook; `write_secret` / `read_secret` (the checkpoint, `identity`'s TLS key); a sealed
  file opens only with the sealer, a clear one is refused while sealing is on.
- dl-custodian: `vault-init I TLSDIR --epoch E` (setup: the file key in the uid's persistent keyring, the TLS key
  sealed in place, TLSDIR/vault.name); `--vault` (required outside test builds) loads it; the carry is sealed too.
  A rotation hands the key to old_side (`with_vault`), which destroys it; a self-handover destroys the old one
  and makes the epoch + 1 key, reseals the TLS key and the state under it and rewrites vault.name.
  `--keep-erased-copy DIR` keeps the sealed files as they were before the erasure, for the checker.
- run.py: cfg "vault": true runs vault-init at setup (old seats epoch 0, new seats epoch 1) and passes --vault;
  record.py sets it.
- Tests (Linux only, the keyring): `--test handover_steps -- sealed_under_the_vault` (rotation with a pause and
  `serve --resume` loading the new key in a new process; self-handover) on bb2.

### Cut E, RS and the close (5835906b) [EXECUTED on the Mac]

dl-custodian `--rs`; prove_step_l / release_custodian_l with the replica's pending claims; old_side_e /
new_side_e / with_old_carries in both handovers; `close` for a halted run. Tests under DL_PROFILE=ledger-x2de
DL_RS=1: rotation and self-handover pass (darkproof's native rotate under DEFER, c18e41f8); close_steps passes.
Vault tests on bb2 (Linux keyring): rotation_sealed_under_the_vault and self_handover_sealed_under_the_vault
passed (eafb85a9).

## Continuation (deploy lane generation 3, 2026-11-07 ~10:50 UTC)

**State**: everything to 5835906b pushed. Boxes: forge `ws/` at 8319ea81 with `ws-target-r5`/`test5` (used for
run12c, ledger-x2 chunks, no vault/E); bb2 `ws/` at 5835906b, building `ws-target-r6`/`test6` (build-r6.pid);
forge needs `deploy/sync.sh dregg-forge /srv/lanes/dl-gen6-deploy/ws 5835906b` and the same build after 11:00.
hbox `/othersys/lanes/dl-gen6-deploy/bin/ws4/darkstep` (test4) for run7. Configs and summaries:
`.../scratchpad/dl-gen5/deploy2/runs/` (run10b, run11b, run11c, run12b, run12c, run7 updated to ports 287xx).
Mac builds: from a HEAD export (`git archive HEAD native` into the scratchpad's deploy3/wt) plus this lane's files,
never the shared tree (other lanes' half-written darkproof edits).

**Next, in order**:
1. run12c at ~11:02 (`run.py runs/run12c.json setup`, `launch`): rotation on r5 (8319ea81), ledger-x2, chunks
   w4096h6 / ho-sh3 / ho-sh3-steps, archive on bb2, ports 28300-28335. Tell the handover lane (afc2a88b82c0cca1a)
   at launch and when the old seats exit; it reports the count. Report "run12b/12c all green" to the coordinator.
2. run11c (~11:20, prep's sh-abort / ho-x / ho-x-steps under ledger-x2de + RS): runs/run11c.json is drafted on
   test5; switch its bins to ws-target-test6 (forge too), flags `--profile ledger-x2de --rs`, check the erase-extra
   paths (wired-new<I>-sh/mpspdz). Same reporting.
3. The rehearsal: `python3 native/deploy/record.py dev --steps 4 --handover-at 1 --chunks reh --key-dir reh-old
   --no-release > runs/reh.json`, bins ws-target-r6 (the generator writes ws-target-run: set "bin"), `run.py setup`
   (vault-init runs there), then `run.py runs/reh.json drive` in the background with a PID file. Prep writes
   reh-n-c0 last (a --tape-wait test).
4. Item 3 (run7, the rounded hbox step) when prep says the LowGear setup's traffic ended (~15:00); prep then wants
   hbox's link 15:15-16:45.
5. Release memory: rerun run10b's measurement when the proof lane (aafff52532f04d20a, helper aa5e2143) sends a
   build; the tapes must be RS tapes (`test-deal ... --rs --split-release`).
6. The run of record: record.py hbox|wired once the coordinator sends N, K and the layout; the release must fit.

**Agents**: coordinator aa3209e8d10294bc2; prep a5caa478aac6a0658; proof aafff52532f04d20a (E helper
a93e0325f167a4ed2); handover afc2a88b82c0cca1a; train ad36593ec00657538.

### run12c: the rotation on the shallow-handover build, ledger-x2 (11:05-11:22 UTC) [EXECUTED]

As run12b with darkhand 09fd154d (r5 at 8319ea81), profile ledger-x2, chunks w4096h6 (a fresh wired key) /
ho-sh3 / ho-sh3-steps (wired-new-sh), ports 28300-28335. Prep's MASCOT chunks ran on forge and bb2 throughout
(11:00 queue): upper bounds.

| | old 0 (forge) | old 1 | old 2 | new 0 | new 1 (forge) | new 2 |
|---|---:|---:|---:|---:|---:|---:|
| step 0 / 1 / 2 seconds | 221.7 | 221.4 | 221.6 | 189.6 / 107.2 | 189.4 / 107.2 | 189.6 / 107.2 |
| prove / verify (s) | 74.6 / 31.3 | 75.3 / 42.5 | 74.7 / 43.8 | 63.6-82.4 / 36.0-36.4 | 63.5-82.6 / 29.9-31.0 | 63.6-82.3 / 35.7-37.8 |
| old_side s (reshare, prove, erase) | 64.2 (1.8, 28.9, 0.87) | 94.9 (2.5, 28.2, 1.44) | 91.9 (2.8, 27.9, 1.26) | | | |
| cgroup peak | 8.63 GB | 8.73 GB | 8.61 GB | 10.29 GB | 9.67 GB | 10.05 GB |

One transcript per step; bundles 75,989,589 / 76,297,173 / 76,393,653 B (ledger-x2; ledger-sq's were 250.9 MB);
after erasure: no decryption, disk scan 0. The handover lane's count: pending.
- Handover lane's count for run12c: **74/74**, memory scan after erasure 0 at every old seat (handover.md §7).

### run11c: the self-handover under ledger-x2de + RS, cut E live (11:22-11:35 UTC) [EXECUTED]

Seat 0 bb2, 1 forge (attack), 2 bb2; prep's sh-abort (wired-new-sh) / ho-x / ho-x-steps (a fresh key), all
ledger-x2de + RS (8,916,565 entries per step = `step-entries ... --profile ledger-x2de --rs`); ws-target-test6 at
11e84d91 (E through the handover, darkproof's rotate under DEFER c18e41f8). Prep's chunks ran beside it.
- Step 0 REFUSED at all three (Freivalds); old role 102.6 / 55.6 / 99.5 s (its handover proof 16.1-16.9 s, erase
  0.87-1.13 s); new role 41.0 s; redo step 0 207.6 s and step 1 158.9 s, ACCEPT, one transcript each.
- Prove 37.8 / 55.0-55.5 s, verify 17.6-23.1 s; bundles 47,487,701 / 47,467,925 B (ledger-x2de; x2's ~76 MB).
- cgroup peaks 10.94 / 9.49 / 10.71 GB.
- Handover lane's `--self` count: **37/37**, memory scan after erasure 0.

### Item 3: the rounded step through hbox (run7, 11:35-11:48 UTC) [EXECUTED]

Seat 0 forge, seat 1 bb2, seat 2 hbox (swarm-build, 16G, /othersys), test-dealer tapes, darkstep serve (test4),
`--ret-primes 2 --ret-round` (the derived rounding), no proof. Loads: forge 0.2-5.3, bb2 10-64, hbox 0.7-9.4 (prep's
loopback LowGear test on its CPU; its link idle).

| | run 2 (switched) | **run 7 (switched + rounded)** | ratio |
|---|---:|---:|---:|
| step seconds | 1,352 | **791.4** | 0.585 |
| outer G2 / G1 | 608 / 645 s | 361.8 / 352.7 s | 0.57 |
| matvec z1 / z2 / b | 33 / 39 / 19 s | 26.3 / 28.2 / 16.3 s | |
| bytes per directed link | 2,352 MB | **1,385.6 MB** | 0.589 |
| he_ret per link | 2,173 MB | 1,206.8 MB | 0.555 |
| hbox upload per step | 4.70 GB | 2.77 GB | 0.59 |
| peak RSS | 4.6-4.7 GB | 4.61 / 4.69 / 4.77 GB | |

ACCEPT at all three, one transcript. On hbox's link a step is ~13 min before any proof: 2,000 steps ~18 days.
The proof with rounding on: `DL_PROFILE=ledger-x2de DL_RS=1 DL_EXTRA=--ret-round` handover_steps
rotation_to_a_new_committee_after_step_0 passes at d = 64 (both steps proved and accepted, weights = the twin
after 2 steps): the proof binds openings and shares, which rounding does not touch. [OPEN] the same at d = 4096.

### The orchestrator rehearsal (reh, 11:51-12:01 UTC) [EXECUTED]

`record.py dev --steps 4 --handover-at 1 --chunks reh --key-dir reh-old --no-release` (bins r6 at 11e84d91), then
`run.py runs/reh.json setup` (vault-init: six file keys) and `run.py runs/reh.json drive` on the Mac (drive.pid):
launched 11:51:16; the new committee started at 11:53:35 when the old seat 0 had step 0; the old committee rotated
after step 1; the new one ran steps 2-3; "run ended at step 4" 12:01:15; collected. Prep's MASCOT chunks (reh-c0,
reh-ho, reh-n-c0; ledger-x2de + RS, plain), pipelined proofs on a proof mesh per committee, the archive on bb2,
--wipe-spent, --tape-wait 7200 (no wait: reh-n-c0 was complete before step 2), --vault, --keep-erased-copy.

| step | committee | step s | proof s (beside the next step) | verify s |
|---|---|---:|---:|---:|
| 0 | old | 90.6 | 43.4 | 16.8-22.5 |
| 1 | old | 101.4 | 33.6 | 17.7-18.2 |
| 2 | new | 93.1 | 48.0-48.1 | 24.6-25.3 |
| 3 | new | 101.2 | 33.6 | 17.7-18.2 |

All ACCEPT, one transcript per step; cgroup peaks 8.49-8.69 GB (old), 9.27-9.82 GB (new); old seats after the
erasure: file key gone from the keyring, the captured ciphertext does not decrypt.

### run10c: the release fits forge's 12G, one custodian per process (12:04-12:27 UTC) [EXECUTED]

Test-dealer tapes under ledger-x2de + RS (`test-deal ... --rs --release --split-release`, dealt on bb2, seat 0's
streamed to forge and checked by sha256): steps' tape 151,581,629 B, release tape 2,672,096,914 B (157,182,170
entries, 38,666,490 of them the proof section); test7 at fb173e20 (the release's proof section streamed from its
own tape, the proof lane's heap cuts); DP_TRACE=1 DP_CW_HOLD_MB=256 DS_THREADS=12; seat 0 forge MemoryMax=12G,
seats 1-2 bb2 32G; a test-only registry.

| | seat 0 (forge, 12G) | 1 (bb2) | 2 (bb2) |
|---|---:|---:|---:|
| VmHWM | **10.32 GB** | 10.57 GB | 10.44 GB |
| cgroup memory.peak (sampled) | **10.91 GB** | 11.16 GB | 11.02 GB |
| release s (MPC / prove / verify) | 878.8 (93.4 / 353.8 / 215.0) | 914.1 (18.2 / 354.0 / 265.6) | 895.6 (19.9 / 354.0 / 260.4) |

Seat 0's trace: MPC 6.44 GB; replay 66 s, 9.54 GB; middle commitments to 9.78 GB, zerocheck 10.17, build_q (124 s)
10.20 GB. C = 8 of 52 at all three after one step (untrained); one bundle 260,069,187 B (sha256 b8eaf2e6...),
accepted by every replica through release_checked. Step 0 ACCEPT 200.3 s.

## Continuation, updated (deploy lane generation 3, 2026-11-07 ~12:35 UTC, near its context limit)

Supersedes the ~10:50 continuation. Last code commit c2319a8d (pushed). Builds on the boxes: r7 at 665a092b
(forge, bb2: vault, E, RS, sealed tapes DLVAULT1/2, streamed release; lacks only c2319a8d's keep-erased-copy fix),
test7 at fb173e20, test6/r6 at 11e84d91, hbox bin/ws4 (darkstep test4). Mac builds: HEAD export into
.../scratchpad/dl-gen5/deploy3/wt2 plus this lane's files, target-deploy2.

**Done this generation** (all in sections above): run12b/12c (rotation 74/74), run11b/11c (self-handover 37/37
under x2de + RS + E), run10/10b/10c (the release now fits forge: VmHWM 10.32 GB, cgroup 10.91 GB at M = 52), item 3
(run7: 791 s through hbox), the orchestrator rehearsal (reh: drive, vault, rotation, pipelined proofs; vault check
9/9 copies unopenable), NAT seats, the vault, cut E / RS / close, sealed tapes, tape-wait, the new committee's
pause/resume, record.py.

**Next, in order**:
1. run13 (`runs/run13.json`, set up: vault keys made): prep's REAL sealed chunks under ledger-x2de + RS on the wired
   layout, 1 step + release, `--ret-round` on (the d = 4096 proof-with-rounding check). Launch when prep
   (a8fd625fd8dbd4f54) reports run13-rel-P<I>/step-0/tape_I.bin landed (~13:00): `run.py runs/run13.json launch`.
   run13-c0 is ready. Report forge's release VmHWM / cgroup peak and whether step 0 (rounded, proved) ACCEPTs to the
   coordinator. Rebuild at >= c2319a8d first if --keep-erased-copy is used (run13 does not use it).
2. reh2: a second rehearsal on a build >= c9771f4a (darkhand TLS canary fix) and c2319a8d, for the handover lane
   (afc2a88b82c0cca1a) to confirm 0 TLS-canary hits after erasure on the boxes. Ask prep for fresh-key reh2 chunks,
   SEALED (send the vault.name paths after `run.py setup`; vault-init --with-next only if a self-handover).
3. The run of record: `record.py hbox|wired --steps N --handover-at K --chunks NAME --key-dir D` once the coordinator
   sends N, K and the layout (ember is choosing the third box; hbox costs ~13 min/step on its link: run7). The
   release now fits. Re-key at launch if more than 3 days pass after setup (keyring expiry).
4. [OPEN] weights-equal-twin at d = 4096 with rounding (needs a test build + dl-reveal; d = 64 passes).

**Agents**: coordinator aa3209e8d10294bc2; prep a8fd625fd8dbd4f54; proof aafff52532f04d20a (memory helper
aa5e2143a94a1698c, E helper a93e0325f167a4ed2); handover afc2a88b82c0cca1a; train ad36593ec00657538.

## Deploy lane generation 4 (a21cca37, successor of afcd36ed, from 2026-11-07 12:30 UTC)

### run13: prep's real sealed chunks, 1 rounded proved step, then the release at M = 52 (12:35-13:15 UTC) [EXECUTED]

Wired layout (seat 0 forge MemoryMax=12G, seats 1, 2 bb2 12G), prep's run13-c0 (DLVAULT1 step tapes) and
run13-rel (DLVAULT2 release tapes, 2,672,137,730 B, 157,182,170 entries, 38,666,490 of them the proof section),
MASCOT tau = 5 under one MAC key; ledger-x2de + RS, `--ret-primes 2 --ret-round`, inline proof, --vault,
--wipe-spent, archive on bb2. `run.py runs/run13.json launch`, then `run.py runs/run13.json resume`.

Two bugs in sealed-tape paths no test had exercised end to end:
- 12:35, r7: refused before step 0 at all three, "15416554168668176872 entries ... made for another profile":
  dl-custodian's check_profile read a sealed (DLVAULT1) step tape's AEAD bytes as the DLTAPE01 header. Fixed in
  fa9b08c7 (`serve::tape_len` opens the seal). darkdeploy `tests/sealed_tapes.rs` at HEAD had a duplicated fn and
  never compiled, which is how this passed; fixed, plus the_profile_check_reads_a_sealed_tapes_count (bb2: 2 passed).
  Nothing was claimed (consumed.jsonl unchanged).
- 12:52, r9: step 0 ran; the release then stopped at "run13-rel-P<I>/step-0/tape_I.bin: not a tape":
  `serve::claim_tape_file` (fb173e20) took only DLTAPE01. Fixed in 345782da: a sealed tape is claimed once opened,
  hashed as on disk, with the opened tape's alpha_i. run13-c0 was spent by then (single use, wiped), so the release
  ran alone from step 0's checkpoint: `serve --resume --steps 0 --release` (new: no step tape loaded or claimed, the
  checkpoint's alpha_i, which the release tape must carry; check_profile skips; `run.py resume` does it when every
  step ran and the release failed). Test: darkdeploy `--test release_sealed` (Linux): a proved step under --vault,
  release tapes sealed DLVAULT2 under each seat's key, the release alone: one C equal to the plaintext count, each
  registry holding the sealed file; control: the tapes restored byte for byte are refused as consumed (bb2: 1 passed).
- cd4a1b00: --wipe-spent also wipes the release's own tape once claimed (run13 left run13-rel on disk; prep shredded it).

Results (build r9 for step 0, r10 = 345782da for the release):

| | seat 0 (forge, 12G) | 1 (bb2) | 2 (bb2) |
|---|---:|---:|---:|
| step 0 s (rounded, proved) / proof / verify | 102.2 / 29.7 / 15.4 | 102.2 | 102.2 |
| bytes per directed link, step 0 | 1,385.6 MB | | |
| release s (MPC / prove / verify) | 670.1 (14.4 / 251.4 / 201.1) | 651.0 (6.9 / 251.7 / 193.3) | 645.4 (7.2 / 251.7 / 192.9) |
| release VmHWM | **8.94 GB** | 9.32 GB | 9.60 GB |
| release cgroup memory.peak (sampled) | **10.27 GB** | 10.64 GB | 10.95 GB |

- Step 0 ACCEPT at all three, one transcript, proof 43,243,613 B verified: **the proof with rounding on accepts at
  d = 4096** (was [OPEN]).
- The release: C = 8 of 52 at all three, one bundle 260,052,099 B (sha256 09dc6b19...), ledger_accepted at all three.
  Forge's release fits 12G with 1.73 GB to spare (run10c's test-dealer tapes: 10.32 / 10.91 GB).
- **Twin**: `darktrain shadow '<train_genesis_gen6.json>' 1 52` (order 2, as the owner feeds) gives C = 8; controls:
  0 steps C = 0, 2 steps C = 9. The weights-equal-twin check is test-only (not in a production build); C is the
  confirmation here.
- record.py now carries --ret-round.

### The disk plan for the run of record (coordinator-approved) [EXECUTED: run.py plan]

Measured: bundle 47.47 MB per step (x2de + RS), sealed step tape 151.8 MB per seat, process state ~0.95 GB, handover
tape 570 MB and release tape 2.67 GB per new seat, handover bundle 27.6 MB, release bundle 260 MB; prep's lookahead
(`darkprep produce --max-ready 9`, chunk-steps 2: (R + 1) x K = 20 step files per process, confirmed by prep).
`run.py RUN.json plan` (hbox layout, K at the middle; conservative: old seat dirs kept):

| N | forge / (315 GiB free, line 30) | bb2 / (46 GiB then, 103 after the cleanup; line 30) | hbox /othersys (49 GiB, line 30) |
|---|---:|---:|---:|
| 2000 | 99.2 GiB (archive 88.7) | 10.5 | 10.5 |
| 500 | 32.8 (archive 22.4) | 10.4 | 10.4 |

- The archive goes on forge (`record.py --archive-on`, default); it cannot sit on bb2. The Mac (89 GiB) holds it only
  for N = 500.
- fa9b08c7: `run.py plan`; the gate at every launch per (host, filesystem); drive rechecks every disk_poll_s (600) and,
  when a box would end under its line, touches each seat's DIR/PAUSE: serve `--pause-file` (any custodian's file
  pauses the committee at the next boundary; darkstep `--test serve_steps -- pause` 2 passed); drive resumes only once
  every box is above its line. Nothing is deleted.
- bb2 cleanup (coordinator-approved, this session's own run dirs): 92 files, 58.59 GiB (test-dealer tapes,
  checkpoints, carries, reveal shares of finished runs; list in bb2:~/lanes/dl-gen6-deploy/removed-2026-11-07.txt);
  bb2 / 44.2 -> 102.8 GiB free. Kept: every log, json, bundle, and reh's sealed erased copies.
- reh's plaintext MP-SPDZ copies (Player-MAC-Keys-p-P<I>, Mascot-Secrets-p-61-*) were already shredded by gen 3;
  reh/seat*/erased holds only DLVAULT1 files (checked by magic). Nothing left to delete.

### reh2: the rehearsal rotation on the vault, sealed tapes and the TLS-canary fix (13:20-13:31 UTC) [EXECUTED]

`record.py dev --steps 4 --handover-at 1 --chunks reh2 --key-dir reh2-old --no-release --name reh2`, bins r10
(345782da, after c9771f4a and c2319a8d), --ret-round added, each old seat `--keep-erased-copy`; `run.py setup`
(six file keys), then prep's sealed fresh-key chunks (reh2-c0 under the old keys, reh2-ho and reh2-n-c0 under the
new; MP-SPDZ Player-Data on tmpfs), `run.py runs/reh2.json drive` (drive.pid): launched 13:20:32, the new committee
at 13:23:20, "run ended at step 4" 13:31:00; one transcript per step.

The handover lane's checker, run by this lane (coordinator's request; that lane is retired):
`check_handover.py runs/reh2.json deploy4/check-reh2 --profile ledger-x2de --tools dregg-forge=.../ws-target-r10/release/dl-hand bb2=...`
- **98 of 101.** All green at the three new seats and the ledger (replicas equal; one handover proof sha256).
- Old seats: the TLS DER canary's private words 5 before / 0 after at each (reh: 8 false hits; c9771f4a confirmed on the
  boxes), the vault file key 12 / 0, memory ~2.99M hits before / 0 after over 3.1-3.4 GB, decrypt yes / no, key
  material 0, no state files left, keyring key invalidated, relaunch and resume exit at a missing secret, tmpfs 3 / 0,
  RAM cannot page out.
- `dl-hand vault-open <old name> erased/*` on each old box: 9 DLVAULT1 copies (ckpt 536,870,996, carry 288,873,140,
  TLS key 174 B per seat), none opens by the keyring or the zero key; no MP-SPDZ plaintext copied (c2319a8d). The
  --erase-extra p-61 MAC-key and secrets files are gone from /dev/shm (prep's gf2^128 / B-64 secrets remain there).
- **The 3 reds**: "disk scan before erasure finds the material in the state files (control)". Persistent disk held 0
  plaintext hits in ~1.12 GB before the erasure, because everything at rest is now sealed (state, TLS key, prep's
  DLVAULT1 tapes) and the MP-SPDZ key is in tmpfs; the same pass found 3 hits in the RAM class. The control is the
  checker's criterion (darkhand/scripts/check_handover.py:109), written when tapes and state were plain; proposed to
  the coordinator: the control holds on persistent OR RAM hits, plus a positive "no plaintext at rest" check. [OPEN]

### The run of record: staged (13:40 UTC)

- Builds r11 at e722d02c (cd4a1b00's release-tape wipe, --ret-round, the disk plan) on forge
  (/srv/lanes/dl-gen6-deploy/ws-target-r11), bb2 (~/lanes/dl-gen6-deploy/ws-target-r11) and hbox
  (/othersys/lanes/dl-gen6-deploy/ws-target-r11, built under swarm-build 16G), with dl-hand.
- hbox: MNIST copied to /othersys/lanes/dl-gen6-deploy/data/mnist (sha256 equal to bb2's); vault-init works there (file
  key in the persistent keyring, TLS key DLVAULT1). keyctl is not installed, so the test key stays until the keyring's
  expiry; it guards nothing (its dir is deleted). Its 8 GB swap file is full, but swarm-build runs every scope with
  MemorySwapMax=0, so a custodian under it never pages out.
- To launch once the coordinator sends N, K and the layout:
  `record.py hbox|wired --steps N --handover-at K --chunks NAME --key-dir D [--third H,IP,ROOT] > runs/record.json`,
  set "bin" to ws-target-r11 (the generator writes ws-target-run), `run.py runs/record.json plan` (prep's lookahead
  20), `setup`, hand prep the six vault.name paths for sealed chunks, then `run.py runs/record.json drive` in the
  background with drive.pid. Never forge + bb2 + bb2 (development only).
