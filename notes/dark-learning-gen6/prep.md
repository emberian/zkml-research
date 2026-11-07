# Gen 6 prep: distributed preprocessing, one custodian per box

Lane `prep`, dark-learning gen 6, 2026-11-07. Continues `notes/dark-learning-gen5/preprocessing.md`.
Code: `native/darkprep` (commit 21629f41 and later). Party 0 = dregg-forge, 1 = bb2, 2 = hbox.

## 1. The build (tau = 5)

[EXECUTED] `native/darkprep/build/build-mpspdz.sh ROOT 5` on bb2. Recipe:
- MP-SPDZ v0.4.4 release source, `N_AMPLIFY` set to tau = 5 in `OT/NPartyTripleGenerator.h`;
- dependencies built into ROOT/local with no system packages: m4 1.4.19, GMP 6.3.0, libsodium 1.0.20, zlib 1.3.1,
  zstd 1.5.6 (the distribution's static libcrypto needs it), NTL 11.5.1 (for LowGear/HighGear), boost via libOTe's
  build.py; tarball hashes in ROOT/dl.sha256;
- `make static/{mascot,lowgear,highgear}-party.x`, `ARCH = -march=x86-64-v3 -madx -maes -mpclmul` (the common subset of
  the three boxes), static libraries; glibc >= 2.38 is the only dynamic dependency (hbox has 2.40, forge/bb2 2.41);
- release workarounds (all in the script): `ERROR =` (gmpxx's deprecated literal operator under clang), CPATH /
  LIBRARY_PATH for the bundled base-OT libraries' libsodium, SimplestOT_C configured directly (its make target tries
  a git submodule update), `-lzstd` appended to the static link line.
- sha256 mascot-party.x 67cc2adf..., lowgear-party.x f67541df..., highgear-party.x 772b3da9..., tarball
  mpspdz-tau5.tar.xz 8b363962...

`build/setup-box.sh ROOT I TARBALL` installs it on a box and generates that custodian's TLS key there (mode 600, CN=P<I>);
only the three certificates are copied between boxes and pinned (`c_rehash`). `build/launch3.sh` starts one darkprep
command per box under each box's rules (forge systemd-run MemoryMax=12G, bb2 user scope 24G, hbox swarm-build 16G),
with PID files.

## 2. The network

[EXECUTED] probes (`bw.py`, plain TCP, then MASCOT itself):
- forge <-> bb2 direct: 5.2-6.9 Gbit/s; both accept inbound on 152xx, no tunnel needed.
- hbox is on home Wi-Fi (`wlo1`) behind NAT: 39-44 Mbit/s up, 79 Mbit/s down, RTT 106-320 ms to forge. It is party 2
  because the highest MP-SPDZ (and darkstep) party only dials out.
- During MASCOT, hbox's three links averaged about 19 Mbit/s each way, latency-bound as much as bandwidth-bound.
- Two of four three-box runs aborted on hbox: "write_some: Connection timed out" after 20 min of MASCOT, and a send
  timeout during LowGear key generation. Each abort retired every box's MAC key (by design).

## 3. Event: three boxes, tau = 5, TLS, consumed by darkstep, refines the spec

[EXECUTED] `launch3.sh t64b party-chunk ... --d 64 --mode harness --steps 1 --proof --threads 4` (chunk = the harness
d = 64 step with Trhb atoms and the proof section, 441,939 tape entries per party):

| party (box) | wall | CPU user / sys | peak RSS | MP-SPDZ bytes sent | wire per link, sent (kernel TCP, TLS included) |
|---|---:|---:|---:|---:|---|
| 0 (forge) | 1,078 s | 30.7 / 9.5 s | 774 MB | 2.598 GB | 1.302 GB to bb2, 1.302 GB to hbox |
| 1 (bb2) | 1,075 s | 29.6 / 11.0 s | 774 MB | 2.597 GB | 1.302 GB to forge, 1.301 GB to hbox |
| 2 (hbox) | 1,073 s | 17.6 / 6.6 s | 738 MB | 2.597 GB | 1.302 GB to forge, 1.301 GB to bb2 |

Then the data owner (the Mac, test role) received the three owner messages, checked 8,320 a b = c and computed
`public.bin`; three `darkstep party I 16384 4 175 64` processes on the same three boxes over the tapes: **ACCEPT x 3**
(MAC check passes), step 26-32 s; the test-only `darkstep reveal` (Mac, test-harness build) on the three share files:
**refines_spec: true**. darkstep's online links are plain TCP in this test (deploy lane owns TLS there); the data
is the harness's synthetic d = 64 inputs.

Unit price, measured three-box tau = 5 with TLS: 62.3 Gbit / 172,273 triple-equivalents = **362 kbit per triple**
(all parties). The scholar's formula at tau = 5 and SoftSpoken's 64 bits per OT gives 342,942: measured x 1.055.

## 3b. The wired layout at d = 4096 (no home link): real MASCOT tau = 5, carried step

[EXECUTED] `LAYOUT=wired launch3.sh w4096 party-chunk ... --d 4096 --mode steady --truncs 11,19,7,8,8,19 --steps 1
--threads 8`. Seat 0 is on forge; seats 1 and 2 run on bb2 as separate processes, each with its own runtime dir
(`wired<I>/mpspdz`), TLS key and MAC key. TLS throughout. 2,109,446 tape entries per seat.

| seat | wall | CPU user / sys | peak RSS | MP-SPDZ bytes sent | wire per link, sent |
|---|---:|---:|---:|---:|---|
| 0 (forge) | 74.0 s | 286.5 / 56.9 s | 1.94 GB | 33.76 GB | 33.82 GB to bb2 (both seats) |
| 1 (bb2) | 71.4 s | 257.8 / 56.4 s | 1.98 GB | 33.75 GB | 16.91 GB to forge, 16.89 GB to seat 2 |
| 2 (bb2) | 69.5 s | 256.5 / 55.9 s | 1.97 GB | 33.75 GB | 16.91 GB to forge, 16.89 GB to seat 1 |

The total is 0.810 Tbit, against the 0.817 Tbit predicted from the d = 64 unit price (§5): x 0.99.

With the RC + LB proof section (`--proof --proof-triples 3192275`, `w4096p`, 12,456,319 entries per seat): wall
138-142 s, CPU 621-625 s user plus 152-189 s sys, peak RSS 1.54-1.56 GB, 81.3 GB sent per seat (40.7 GB per link).
The total is 1.953 Tbit against 1.973 Tbit predicted. Both chunks were handed to the deploy lane.

## 4. LowGear (HE-based, Overdrive) against MASCOT

[EXECUTED, loopback on forge, `lgtest/` (a test directory with its own keys, separate from custodian 0's)]:

| run | triples | bytes sent, all parties | marginal bits per triple | time |
|---|---:|---:|---:|---:|
| LowGear S = 40 | 20,000 | 471.95 MB | | 7.3 s + 230 s key setup |
| LowGear S = 40 | 100,000 | 943.83 MB | 47.2 k (20k -> 100k) | 14.5 s |
| LowGear S = 40 | 300,000 | 1,887.81 MB | **37.8 k** (100k -> 300k) | 28.8 s |
| LowGear S = 60, -lg2 64 | 100,000 / 300,000 | 943.84 / 1,887.81 MB | 37.8 k | 14.6 / 29.0 s |

S = 60 costs nothing measurable in bytes.

**LowGear key setup is large.** [EXECUTED, loopback, fresh keys at S = 55 and 56; `lgsetup.sh` per-socket `ss` and
`lgsetup2.sh` lo-interface TX counters agree]: one setup sends **169.6 GB in total (about 56.5 GB per party) in 237 s**.
MP-SPDZ's "Data sent" leaves it out. [SOURCE: Protocols/LowGearKeyGen.h] Malicious LowGear generates the BGV key
components inside a MASCOT computation over the ciphertext-modulus primes (`Mascot-Secrets-p-312`). It runs once per
epoch and is cached in `LowGear-Secrets-*` until an abort retires it. Through hbox that is about 452 Gbit, 6.5-9.6 h. LowGear sends about **9.6x fewer bits per triple** than MASCOT tau = 5
(362 k). Key setup (BGV keys + MAC key) takes about 230 s per epoch and is cached in `LowGear-Secrets-*`.
Three-box LowGear: see §5 (pending).

## 5. Per step at d = 4096, through hbox (DERIVED from the measured unit prices; hbox at its measured 19.3 Mbit/s)

LowGear loopback unit prices (all parties, marginal, S = 60): triple 37.8 k, random bit 38.3 k, power-chain product
37.7 k, joint random 3.78 kbit. MASCOT tau = 5 three-box: 362 k per triple-equivalent, 23.5 k per random (gen 5).

Step at d = 4096, GEN6 program (truncations (11,19), (11,19), (7,8), (8,19)), carried (x, y input): 286,722 Beaver
triples, 1,040,384 power products, 921,600 bits, 8,192 input tuples = 2,256,898 triple-equivalents, plus 16,384
randoms. Proof section per step (proof lane, RC + LB, commit cebe43b4, `run::step_section`): 3,192,275 triples (it
was 16.83M with the gen-5 method and 4,101,581 with RC alone).

| backend | proof section | triple-eq per step | total (Tbit) | **hbox upload per step (Gbit)** | hours per step via hbox |
|---|---|---:|---:|---:|---:|
| MASCOT tau = 5 | no | 2,256,898 | 0.817 | **272.5** | 3.9 |
| MASCOT tau = 5 | RC + LB | 5,449,173 | 1.973 | **657.7** | 9.5 |
| LowGear | no | 2,256,898 | 0.085 | **28.5** | 0.41 |
| LowGear | RC + LB | 5,449,173 | 0.206 | **68.7** | 0.99 |

The release (M = 64) section is 58,679,793 triples on top of the release's own step-like preprocessing. That is
about 21 Tbit on MASCOT or 2.2 Tbit on LowGear, so 0.7 Tbit from hbox, about 10 h on LowGear [DERIVED].

Traffic is symmetric (each party sends a third, half on each link; §3), so hbox's upload is total / 3. The hours assume
hbox's MASCOT-measured 19.3 Mbit/s; LowGear's larger messages may run nearer the 40 Mbit/s raw uplink (§4 three-box
pending). LowGear also costs a one-off key setup per epoch (230 s compute on loopback; over the WAN, over 1.2 GB from
hbox and over 17 minutes on the first attempt).

## 6. Surviving hbox's link

[SOURCE: MP-SPDZ Networking/sockets.cpp, Player.cpp] The stock build aborts on short stalls:
- every client socket gets SO_RCVTIMEO and SO_SNDTIMEO of 10 s;
- TCP keepalive is idle 1 s, interval 3 s, 5 probes, so about 16 s without an ACK kills the connection;
- player sockets get a 300 s receive timeout. LowGear key setup over hbox's link waits longer than that.

[EXECUTED] A 30-minute flow probe from hbox to forge (`trickle.py`: one idle flow with a 1-byte ping every 60 s, one at
1 kB/s, one at 100 kB/s, default kernel TCP settings) kept all three flows. Each closed cleanly after 1,800 s with
every byte delivered. So hbox's link stalls but does not drop flows outright on that timescale. These settings match
the observed aborts: "write_some: Connection timed out", "Sending error (Connection timed out)",
"Fatal error in receiving".

Fix 1, built: `build-mpspdz.sh` now patches these to no send/receive timeout on client sockets, keepalive
30 s / 30 s / 120 probes (an hour), and a player receive timeout of 3600 s. Binary sha256: lowgear-party.x
66c09524..., mascot-party.x 8e24dfa3..., tarball 1b896e6e...

Fix 2, the coordinator's call: run MP-SPDZ over darkstep's resumable relay (deploy lane, 9869e89f). On each box,
MP-SPDZ dials 127.0.0.1:(15210 + j) for peer j, and the relay carries every connection over the seq/ack TLS mesh,
reconnecting under pinned identities. A drop is then a stall of up to DS_RECONNECT_SECS (600 s), not an abort, so it
costs no MAC key. Setup:
- `build/relay3.sh start|stop`; mesh ports 47410 + I; identities from `darkstep tls-keygen I` on each box;
- per-box ip files `ips-relay.txt`: own entry 127.0.0.1:(15200 + I), peers 127.0.0.1:(15210 + j).
- MP-SPDZ's own TLS (-e) stays on inside the relay.

## 7. Randomness: no seeded randomness on a production tape

| component | randomness | source | test-only override |
|---|---|---|---|
| darkprep `party-chunk`, `assemble`, `export-darkstep`, `owner` | none: tapes are linear maps of MASCOT output; the owner check is deterministic | — | the synthetic tests' PyRandom (tests/assemble.rs only) |
| MP-SPDZ `PRNG::ReSeed` (every party-local PRNG: shares, MAC key, OT, BGV keys) | libsodium `randombytes_buf` (getrandom) | OS | `-o zero_seed` calls `insecure()`, which exits unless built with `-DINSECURE`; our build does not define it |
| MASCOT's check coins (MAC check, sacrifice, combine) | `Create_Random_Seed`: commit-and-open among all parties, each contribution from `ReSeed` | OS, jointly | none |
| `Processor::shared_prng` | party 0's `ReSeed`, sent to the others | OS (one party) | used only by public-random program instructions; darkprep.mpc has none |
| TLS keys (`setup-box.sh`) | `openssl req -newkey` on each box | OS | — |
| loopback tests (`lgtest/`, `run`) | as above, but all three keys in one directory | OS | test-only by construction (never a custodian directory) |

## 8. The continuous producer

[EXECUTED] `LAYOUT=wired launch3.sh prodtest produce --queue {ROOT}/queue-P{I} --max-ready 1 --start 0 --count 2 ...
--d 64 --steps 2`. Each seat produced `chunk-000000` and then waited, because one ready chunk had filled its queue.
After the test consumer moved chunk-000000 out of every queue, each seat produced `chunk-000001` (2 steps, back to
back) and exited. Each seat appends one JSON line per chunk to `producer-P<I>.jsonl`. The three producers stay in
lockstep through MP-SPDZ's own connection setup. A file `QDIR/STOP` ends a producer after its current chunk.

Deploy-lane contract per chunk and seat:
- read `chunk-<c>/tape_<I>.bin`, and send `chunk-<c>/step-<j>/owner-msg-P<I>.bin` to the data owner;
- then delete the chunk directory or move it out of the queue;
- the next chunk starts only when fewer than `--max-ready` remain.

## Continuation (handover, 2026-11-07)

**Running: LowGear three-box key setup** (party 0 forge, 1 bb2, 2 hbox; S = 60, -lg2 64; the patched, WAN-tolerant
binaries; direct TLS, not the relay). It was started by `launch3.sh lg64d party-chunk --backend lowgear --extra
-S,60,-lg2,64 ... --d 64 --mode steady --truncs 11,19,7,8,8,19 --steps 1 --threads 4 --out {ROOT}/chunks/lg64d`.
- PID files: the darkprep wrapper is `<ROOT>/runs/lg64d.pid`, and the MP-SPDZ party is
  `<ROOT>/chunks/lg64d.tmp-P<I>/mascot-P<I>.pid`. The name says mascot but it is the lowgear-party.x PID.
- Party logs: `<ROOT>/chunks/lg64d.tmp-P<I>/P<I>.log`; darkprep's JSON is in `<ROOT>/runs/lg64d.log`.
- ROOT is /srv/lanes/dl-gen6-prep on forge, /home/build/lanes/dl-gen6-prep on bb2, /othersys/lanes/dl-gen6-prep on hbox.
- Progress: hbox's sent bytes (`ss -tinpH | grep -A1 "pid=<P>,"`, sum of bytes_acked) were 7.0 GB at 63 min, of about
  56.5 GB expected (loopback measurement). At about 15 Mbit/s that means finishing around 8.5 h after the start.
- It has finished when the P<I>.log lines move past "Generate secret key by binomial" (to "Key generation took",
  "MAC key generation took", then "Time ="), when `<ROOT>/chunks/lg64d` exists (the tmp dir is renamed on success),
  and when `<ROOT>/mpspdz/Player-Data/LowGear-Secrets-60-*-P<I>-3` exists on each box.
- If it aborts, darkprep retires the keys and the setup starts over. Next time run it over the relay
  (`build/relay3.sh start`, `--ipfile {ROOT}/ips-relay.txt`), which survives Wi-Fi drops as stalls.

**Next, once the keys exist** (they are cached, so no setup is repeated):

    LAYOUT= build/launch3.sh lg4096 party-chunk --backend lowgear --extra -S,60,-lg2,64 --mpspdz {ROOT}/mpspdz \
      --mpc-src {ROOT}/native/darkprep/mpc/darkprep.mpc --ipfile {ROOT}/ips.txt --p 2305843009210515457 --d 4096 \
      --mode steady --truncs 11,19,7,8,8,19 --steps 1 --threads 8 --out {ROOT}/chunks/lg4096-P{I}

That gives about 29 Gbit from hbox, about 25 min (estimate). Measure it as in §3, then add `--proof --proof-triples
3192275`. Before you do, ask the deploy lane for a window on hbox's link. Then hand the chunk dirs to the deploy lane.

**Per-chunk commands for the deploy lane.** Run on box I, by that custodian only:
- `darkprep party-chunk --party I --mpspdz ROOT/mpspdz --mpc-src ROOT/native/darkprep/mpc/darkprep.mpc --ipfile
  ROOT/ips.txt --p 2305843009210515457 --d 4096 --truncs 11,19,7,8,8,19 --steps K [--proof --proof-triples N]
  [--backend lowgear --extra -S,60,-lg2,64] --threads T --out CHUNKDIR`.
- N comes from the proof lane (`darkproof counts`, run::step_section). It is 3,192,275 at GEN6 with RC + LB.
- Outputs: `CHUNKDIR/tape_I.bin` (darkstep DLTAPE01, all K steps, one alpha_i) and
  `CHUNKDIR/step-<j>/owner-msg-P<I>.bin` (send to the owner). The owner runs `darkprep owner --msgs m0,m1,m2 --p P
  --out owner.bin`.
- Continuous: `darkprep produce --queue QDIR --max-ready N --start C --count M <same options>` (§8).
- Launchers from the Mac: `build/launch3.sh` (LAYOUT=wired puts seats 1 and 2 on bb2) and `build/relay3.sh`.

**Open:**
- the LowGear d = 4096 chunk through hbox, with and without the proof section (after the key setup above);
- release-phase preprocessing (M = 64; per example 4,096 truncations (11, 19) plus lookups, 10 truncations (11, 19),
  9 comparisons as truncations (10, 10) and 8 products; proof section 58,679,793 triples). Wire it once darkstep has
  the release shape: one more Event list in schedule.rs, checked against darkstep's release dealer the same way the
  step is;
- the wired-layout test directories `wired<I>/` and `lgtest/` are test-only. Never route a deployed custodian
  through them.

## 9. Generation 2 (2026-11-07 morning): forge's nightly pause, chunks for the dry run and the handover

**The LowGear key setup across fn2's nightly.** The setup runs about 9 h, from 05:00 UTC, so it crosses forge's
10:00-11:00 pause. The coordinator's call was to pause it. `runs/nightly-pause.sh` on forge (PID file
`nightly-pause.pid`) sends SIGSTOP to forge's lowgear-party.x by its PID file at 10:00:00 and SIGCONT at 10:58:30.
Why a stop is safe [SOURCE]:
- the parties run with `-e`, and every player read goes through boost::asio::ssl::stream;
- asio's `sync_recv` (boost/asio/detail/impl/socket_ops.ipp:817-858) treats a SO_RCVTIMEO expiry (EAGAIN) as
  would_block and waits in `poll_read(-1)`, so the patched 3600 s player timeout never fires under TLS;
- send timeouts are patched to 0, and a stopped process's kernel keeps ACKing and answering keepalives.
[EXECUTED] Per-socket counters, sampled 66 s apart at 06:07 UTC: all six directed links carry about 0.9 MB/s, all
paced by hbox, so a stop on forge stalls the whole computation rather than one link. The parties' idle loopback
sockets had passed 3600 s by then without an abort.

**The release schedule** [EXECUTED, commits bb20a601 (swept into the proof lane's commit from the shared index) and
e0aa498a]:
- `StepParams.phase = Phase::Release(Release { m, ncls, kc })`, following darkproof::run::deal_release's order:
  - Trunc(11, 19) x d M;
  - Lookup x d M;
  - Mul x ncls M d;
  - Trunc(11, 19) x ncls M;
  - Trunc(kc, kc) x M (ncls - 1);
  - Mul x M (ncls - 2);
  - then the proof section.
- Trhb atoms are on, as the proof lane confirmed.
- The tags equal darkproof's dealer with proof_rng on, at (d, M) = (4, 2) and (8, 3) with GEN6 RC + LB.
- CLI: `party-chunk --release 64,10,10 --proof-triples N`. N always comes from darkproof::run::release_section
  (58,679,793 at the current profile; the proof lane's Ligero-width change will move it).
- `darkprep plan` at d = 4096, M = 64: 66,567,793 triples, 262,144 power chains, truncation classes (11, 19) x 262,784
  and (10, 10) x 576. That is 282.6M tape entries per seat: 4.5 GB of Transactions plus 4.8 GB of tape.

**Release-sized memory** [EXECUTED, e931d52a]:
- Transactions is a read-only mmap, decoded on access, and the schedule is run-length (`runs`, `n_entries`).
- Assembly streams through `tape::DarkstepWriter`, which writes DLTAPE01 by column at fixed offsets. A one-step
  chunk's combined tape is a hard link.
- Unit test: the stream is byte-identical to darkstep's `write_to`.
- On real MASCOT (`shtest64`, d = 64, 2 steps, three seats): the streamed tapes reconstruct with 0 MAC failures
  over 95,996 entries and 0 bad triples among 10,964. Negative control: one share + 1 gives one MAC failure.
- A 33.5M-entry handover tape assembled in 214 MB peak RSS.

**Handover tapes** [EXECUTED]:
- `Phase::Handover(n)` is n auth_plain entries (darkhand::side::new_side needs 2 d^2 + 2; the deploy lane asked for
  2 d^2 + 16 = 33,554,448).
- `--new-mac-key` retires the seat's key share first. Under LowGear it would also retire LowGear-Secrets, so a new
  key there means a new key setup.
- Test seats come from `build/seats.sh new|sh`, launched with `launch3.sh LAYOUT=wired-new|wired-sh` and `BIN=`
  (a second target dir, so a running job's binary is never replaced).

**Chunks made (wired layout, MASCOT tau = 5, TLS, d = 4096 GEN6 Steady, RC + LB proof section 3,192,275)**:

| chunk | seats | per seat: wall | CPU user | peak RSS | sent |
|---|---|---:|---:|---:|---:|
| w4096p2 (2 steps) | wired | 268-272 s | 1,203-1,275 s | 1.83 GB | 162.7 GB |
| w4096s10-c0..c4 (5 x 2 steps, consecutive, one key) | wired | 262-296 s each | 1,174-1,335 s | 1.84 GB | 162.7 GB |
| ho-new (handover, 33,554,448 Ar, new key) | wired-new: 0 bb2, 1 forge, 2 bb2 | 163-165 s | 396-449 s | 0.21 GB | 32.8 GB |
| ho-new-steps (2 steps, the same new key) | wired-new | 248-250 s | 1,215-1,264 s | 1.84 GB | 162.7 GB |

Each new seat's alpha_i in the DLTAPE01 header is the same in ho-new and ho-new-steps, and differs from the wired key.
Auth_plain on MASCOT costs about 32.8 GB x 8 x 3 / 33.5M = 23.5 kbit per value (gen 5 measured 23.5 k).

**Release, priced [DERIVED]**:
- Counts: 66,567,793 triples, 66,584,576 power products and 15,533,056 random bits, so 148.7M triple-equivalents.
  Without the proof section it is 90.0M; the 262,144 degree-255 lookups dominate that part.
- hbox upload is total / 3:
  - MASCOT tau = 5: 53.8 Tbit, 17.9 Tbit from hbox, 258 h at 19.3 Mbit/s;
  - LowGear: 5.6 Tbit, 1.87 Tbit from hbox, 27 h at 19.3 Mbit/s or 13 h at 40 Mbit/s.
- The earlier §5 estimate (0.7 Tbit, 10 h) counted the proof section only.
- On the wired layout (MASCOT, forge + bb2), the w4096p unit cost scales to about 1 h of wall time.

Later chunks, made for the deploy lane's handover runs. All are `--step-tapes-only` (only `step-<j>/` files) with the
ledger-sq proof section of 3,192,275:

| chunk | key | contents | wall per seat |
|---|---|---|---:|
| w4096h, w4096h2, w4096h3, w4096h5 | wired (old committee) | 1 proved step | 131-135 s |
| ho-sh, then ho-sh-steps | wired<I>-sh, new key (`--new-mac-key`) | 33,554,448 Ar, then 2 proved steps | 125-130 s; 279-283 s |
| ho-new2, ho-new3, ho-new2-steps | wired-new | 33,554,448 Ar each; 2 proved steps | about 160 s; about 320 s |
| wn-abort | wired-new | 1 proved step (the aborted step) | about 130 s |
| ho-sh2, then ho-sh2-steps | wired-new<I>-sh, new key (`seats.sh newsh`, ports 15900 + I) | 33,554,448 Ar, then 2 proved steps | about 130 s; about 250 s |

Custody changes made at the deploy and handover lanes' request:
- [EXECUTED, 1dfda757] Retiring a key share now wipes it (overwrite, sync, unlink), and so do older `*.retired-*` copies.
- [EXECUTED, 831ae62c] MP-SPDZ's Transactions file and its memory dump `Player-Data/Memory-p-P<I>` are wiped after
  assembly.
- [EXECUTED] The spent chunks were removed with `shred -n 0 -z -u`.

Byte forms of alpha_i, for the handover lane's disk scan [EXECUTED, wired1-sh on bb2]:
- `3-p-61/Player-MAC-Keys-p-P<I>` holds decimal text;
- `Mascot-Secrets-p-61-*` holds a plain u64 LE at offsets 8 and 9292;
- the Transactions header holds the Montgomery form alpha * 2^64 mod p, LE.

Known limit: on ZFS (hbox /othersys) and behind an SSD's FTL, an in-place overwrite is not physical erasure.
