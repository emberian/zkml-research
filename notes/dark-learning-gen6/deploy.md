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
