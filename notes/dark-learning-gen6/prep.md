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

## 10. The 10:58 abort, the EINTR fix, sealed tapes, RS

**Abort [EXECUTED].** The first three-box LowGear key setup (lg64d) died at 10:58:32 UTC, when forge's party received
SIGCONT at the end of the nightly SIGSTOP. All three logs share that stamp. forge's says "read_some: Interrupted system
call [system:4]".
- Cause: on Linux, a blocking socket call on a socket with SO_RCVTIMEO fails with EINTR after a stop/continue instead
  of restarting (signal(7)). asio's sync_recv treats EINTR as fatal. The patched 3600 s player timeout was the trigger.
- §9's verdict that the pause was safe was wrong: it checked the timeout path, not the stop-signal path.
- About 6 h of hbox upload was lost. The rule is now in ~/swarm/MACHINES.md under forge's nightly rule (2ec9278).

**Fix [EXECUTED, d1299708].** `build-mpspdz.sh`:
- sets the player sockets' receive timeout to 0 (none); keepalive still detects a dead peer;
- retries TLS reads on EINTR. TLS writes are not retried, since asio's engine may already have consumed the bytes.
- Tarball 0d338c68, lowgear-party.x ae12b01d, mascot-party.x 4d50d76f. Installed in all three custodian runtimes
  (`ROOT/mpspdz`).

**Test [EXECUTED, hbox loopback, `eintr.sh`, S = 60, -e]**: stop P2 so that P0 blocks in a receive, then stop and
continue P0.

| binary | P0 stopped | result |
|---|---:|---|
| old 1b896e6e | 30 s | aborts (exit 1 1 1), P0 "Interrupted system call [system:4]" |
| new 0d338c68 | 400 s | exit 0 0 0; darkprep verify Report { entries 1646, macs 4938, triples 162, truncs 16, chains 4, inputs 8 } |
| new, unpaused | — | exit 0 0 0, the same Report |

Stopping a party while it computes does not reproduce the abort (an old-binary run did not fail). The stopped party must
be blocked in a receive.

**Sealed tapes [EXECUTED; ad51f6da, 6103301a]**:
- Every step tape and owner message is sealed whole as DLVAULT1 under the seat's epoch file key (darkhand::vault), with
  roles `tape|<chunk>|<j>` and `owner-msg|<chunk>|<j>`.
- The release tape is DLVAULT2 (crate `native/dlvault`): 1 MiB ChaCha20-Poly1305 blocks, AAD = key name, role, file id,
  block index, count, length, block size. darkproof's `run::load_release_tape_sealed` streams it, and the proof
  section's readers open their own blocks.
- party-chunk takes `--vault-file TLSDIR/vault.name` (or `--vault NAME`) and only loads the key; dl-custodian
  `vault-init` makes it. A production build refuses a chunk without a vault; only feature `test-plain-tapes` writes
  plain files.
- Tests (darkprep --test assemble 22/22; dlvault 3/3; the vault tests also on bb2 against the kernel keyring):
  - a sealed file opens only as itself;
  - after `vault.destroy()` nothing opens;
  - plain files are refused;
  - the sealed release's MPC part and proof-section triples equal the plain tape's;
  - swapped, dropped and spliced blocks are refused.

**Other landed changes**:
- RS layout (be2b01e7): `StepParams.rs`, K + 1 - s Trhb bits, CLI `--rs`.
- The release's L cut: `Release.lookup_triples`, 27 Beaver triples per lookup, CLI `--lookup-triples 27`.
- Both checked against darkstep's and darkproof's dealers.
- The chunk guard (02e5a5dc): a chunk without the seat's MAC key share is refused unless `--new-mac-key`.
- Test seat layouts (`seats.sh` new|sh|newsh|newsh2|rehold|rehnew, `launch3.sh` LAYOUT of the same names).

**Prices at ledger-x2de + RS [DERIVED; unit prices from §3-§5]**:
- Step: 2,256,898 MPC + 2,225,349 proof = 4.48M triple-equivalents.
  - Wired: about 115 s and 67 GB per seat.
  - Through hbox: MASCOT 541 Gbit, 7.8 h; LowGear 56.5 Gbit, 0.81 h, at 19.3 Mbit/s.
- Release, M = 52: plan 50,826,274 triples plus truncation bits, so 63.4M triple-equivalents.
  - Wired: about 27 min.
  - Through hbox: MASCOT 7.66 Tbit, 110 h; LowGear 0.80 Tbit, 11.5 h.
- These replace the ledger-x2 figures (7.69M per step; 154.2M for the release).

## Continuation (generation 2's hand-off, 2026-11-07 12:00 UTC)

**Running: the three-box LowGear key setup `lg64e`** (party 0 forge, 1 bb2, 2 hbox; S = 60, -lg2 64; the EINTR-fixed
binary; direct TLS over `ips.txt`; no pause scheduled). Started 11:50 UTC.
- Launched by `BIN=target-g2/release/darkprep build/launch3.sh lg64e party-chunk --backend lowgear --extra
  -S,60,-lg2,64 --new-mac-key --mpspdz {ROOT}/mpspdz ... --d 64 --mode steady --truncs 11,19,7,8,8,19 --steps 1
  --threads 4 --step-tapes-only --out {ROOT}/chunks/lg64e`. It is a plain-tape build, so the d = 64 chunk it makes is
  test-only: wipe it after.
- PID files:
  - the darkprep wrapper: `ROOT/runs/lg64e-P<I>.pid`;
  - the MP-SPDZ party: `ROOT/chunks/lg64e.tmp-P<I>/mascot-P<I>.pid` (it is lowgear-party.x).
- Logs: `ROOT/chunks/lg64e.tmp-P<I>/P<I>.log` and `ROOT/runs/lg64e-P<I>.log`. ROOT is forge `/srv/lanes/dl-gen6-prep`,
  bb2 `/home/build/lanes/dl-gen6-prep`, hbox `/othersys/lanes/dl-gen6-prep`.
- Progress: hbox had sent 1.09 GB at 9 min. Expect about 56.5 GB, ending about 21:30 UTC, well before the 10:00
  nightly.
- Done when `ROOT/chunks/lg64e` exists on all three boxes and `ROOT/mpspdz/Player-Data/LowGear-Secrets-60-*-P<I>-3`
  exists on each.
- Watcher on the Mac: `scratchpad/dl-gen5/prep2/wait-setup-e.sh` (log `wait-e.log`). Its task dies with the session,
  so re-arm it.
- If it aborts, report the cause to the coordinator before retrying.

**When it finishes**:
1. Tell the deploy lane (afcd36ed0af383db4, or its successor) at once. It may take about 15 min of hbox's link first.
2. Run the LowGear d = 4096 GEN6 carried chunk through hbox, then the same with the proof section. Use `--rs
   --proof-triples 2225349` (ledger-x2de + RS; confirm the count with the deploy lane first).
   - Use `BIN=target-g3/release/darkprep` and `--backend lowgear --extra -S,60,-lg2,64 --mpspdz {ROOT}/mpspdz --ipfile
     {ROOT}/ips.txt --step-tapes-only`. Do not pass `--new-mac-key`: the key now exists.
   - Sealed: `--vault-file <the consuming seat's TLSDIR>/vault.name`, from the deploy lane. Without it, it needs a
     test-plain-tapes build and `--plain-tapes`, and the deploy lane must agree to consume a plain test chunk.
   - Measure wall time, kernel per-link bytes (the chunk JSON's `links`), CPU and peak RSS per party. Compare with
     the loopback unit prices: 37.8 kbit per triple-equivalent, 28.5 / 68.7 Gbit at the old proof counts, now about
     19 / 56.5 Gbit of hbox upload.
   - Hand the chunk to the deploy lane for a gated darkstep step that refines the spec.
3. LowGear-Secrets byte layout for the handover lane's disk scan: compare `LowGear-Secrets-*-P<I>-3` against the
   chunk's alpha_i (method in §9). Tell the handover lane (afc2a88b82c0cca1a).
4. Send the coordinator LowGear's privacy-budget terms with the objects per step:
   - sacrifice 1/p per triple;
   - BGV drowning at S = 60 per ciphertext;
   - ZK soundness at S = 60 per proof.
   The slot count and proof batching are in P0.log ("Finding parameters ... slots" is printed by
   `FHE/NTL-Subs.cpp` at the end of the run), and ciphertexts per step = triple-equivalents / (slots / 2) per pair.

**target-g3** (the sealing darkprep, 6103301a) is built or building in `ROOT/target-g3` on forge, bb2 and hbox:
`scratchpad/dl-gen5/prep2/../tasks/b3628pmmd`; check `ROOT/runs/build-g3.log`. `target-g2` is the pre-vault build
that lg64e runs on. Do not rebuild g2 while lg64e runs.

**Sealed chunks wait on the deploy lane.**
- For each run, run.py's setup writes `ROOT_deploy/<run>/seat<I>/tls/vault.name` (and `new<J>/...`, plus
  `vault.name.next` for a self-handover).
- ROOT_deploy is `/srv/lanes/dl-gen6-deploy` (forge) and `/home/build/lanes/dl-gen6-deploy` (bb2).
- The deploy lane sends the list after each setup. Make each chunk on the consuming seat's box under the same uid.
- dl-custodian must call `load_release_tape_sealed` for the release (dl-custodian.rs:785; the deploy lane's).

**Open**:
- The LowGear d = 4096 chunk through hbox, measured and consumed.
- The release peak with a real sealed d = 4096, M = 52 tape (DP_HEAP=1). The proof lane asks for this: the release
  fits forge's 12G only with a01a1fb9's page-cache drops, which dlvault's reader keeps because drop_cache works on the
  path.
- Price the ledger-x2de + RS chunks with LowGear's measured three-box rate (above: derived from loopback).
- The test chunks on forge and bb2 (`ROOT/chunks/{w4096h*,ho-*,wn-abort,sh-abort,ho-x*,reh-*}`) are the deploy
  lane's until it says they are spent; then wipe them (`shred -n 0 -z -u`).
- `ROOT/lgtest/` on forge is a loopback test dir with all three parties' keys. The handover lane does not scan it.

## 11. Generation 3 (2026-11-07 afternoon): MP-SPDZ secrets in RAM, sealed run13 chunks, budget objects

**MP-SPDZ secrets on tmpfs [EXECUTED, `build/ramdir.sh`]** (the handover lane's request, via the coordinator):
- Each runtime's `Player-Data` and `Persistence` are symlinks into RAM. That covers the MAC key shares, Mascot-/LowGear-/HighGear-Secrets, `Memory-*` and the Transactions file.
  - Forge and bb2: `/dev/shm/dl-gen6-prep/<seat>/`. Neither box has swap.
  - hbox: `ROOT/ram/mpspdz`. hbox has an 8 GB swap file, full, so this is a dedicated `noswap` tmpfs (`sudo mount -t tmpfs -o size=8G,mode=700,uid=1000,gid=1000,noswap,nosuid,nodev`; kernel 6.11).
- The script refuses a target that is not tmpfs, and a tmpfs with swap behind it. The disk copies are `shred -n 0 -z -u`.
- A disk skeleton `Player-Data.skel` keeps only the certificates, their c_rehash links, the TLS key and PairwiseParams.
- Test (dummy runtime on bb2), all passed: refusal on ext4; move; no secret left on disk; idempotent rerun; reboot simulation (RAM dir removed) rebuilds without a key.
- Applied to every prep runtime on the three boxes. That includes lg64e's runtime, live: it had no Player-Data file open, and it writes LowGear-Secrets only at the end. Also shredded: hbox's spent `eintr*/` loopback test keys.
- A scan of the three lane roots (find, which does not follow symlinks) finds no MP-SPDZ secret on disk.
- Earlier copies were overwritten in place on ext4 (forge, bb2) and on ZFS (hbox: rpool/lanes is aes-256-gcm encrypted, with no snapshots). On ZFS that is not physical erasure.
- Resume costs:
  - a process restart, the nightly pause or `serve --resume`: nothing, since the tmpfs outlives processes;
  - a reboot: a re-key. The chunk guard refuses until `--new-mac-key`, and unconsumed tapes are void. That is free under MASCOT and a key setup under LowGear (about 4 min wired, about 9 h via hbox). The seat's epoch vault key in the persistent keyring is also lost on a reboot.
- The TLS private key stays on disk: it is an identity, not erased at handover.

**Sealed chunks for run13 (wired: seat 0 forge, seats 1 and 2 bb2; MASCOT tau = 5, TLS) [EXECUTED]**
- `run13-c0` is one carried step: `--rs --proof --proof-triples 2225349 --new-mac-key --vault-file ../dl-gen6-deploy/run13/seat<I>/tls/vault.name`.
  - 8,916,565 entries per seat, as the deploy lane counted.
  - DLVAULT1 tape (151.6 MB) and owner message.
  - The MAC key share was born in RAM.

| seat | wall | CPU user / sys | peak RSS | MP-SPDZ sent | wire sent per link |
|---|---:|---:|---:|---:|---|
| 0 (forge) | 204.4 s | 555.2 / 136.3 s | 1.54 GB | 66.95 GB | 67.06 GB to bb2 |
| 1 (bb2) | 202.2 s | 541.9 / 126.1 s | 1.57 GB | 66.92 GB | 33.53 GB forge, 33.50 GB seat 2 |
| 2 (bb2) | 200.0 s | 539.5 / 124.4 s | 1.55 GB | 66.92 GB | 33.53 GB forge, 33.49 GB seat 1 |

- The §10 estimate was about 115 s per step. It was 200 s: the bytes are as predicted (67 GB per seat), and the wall time is 1.75x.
- `run13-rel` is the release under the same key: `--release 52,10,10 --lookup-triples 27 --rs --proof-triples 38666490`. Its DLVAULT2 tape is at `run13-rel-P<I>/step-0/tape_<I>.bin`, with role `tape|run13-rel-P<I>|0`.

**Budget objects under ledger-x2de + RS [EXECUTED `darkprep plan`; DERIVED terms]**

| | triples | bits | power products | inputs | randoms | triple-eq | truncations |
|---|---:|---:|---:|---:|---:|---:|---:|
| step | 2,512,071 | 921,600 | 1,040,384 | 8,192 | 16,384 | 4,482,247 (2^22.10) | 16,384 |
| release M = 52 | 50,826,274 | 12,620,608 | 0 | 0 | 0 | 63,446,882 (2^25.92) | 213,980 |

- RS shortens the Trhb tape entries only; MASCOT still generates K + 40 bits per truncation.
- MASCOT tau = 5, per step: combine 2^-69.4, sacrifice 2^-38.9, auth 2^-37.0, owner check 2^-48.0. Release: 2^-65.6, 2^-35.1, 2^-33.2.
- LowGear, S = 60 [EXECUTED `-o verbose_he_setup`, bb2 loopback, stopped by PID file before key generation]:
  - "Need ciphertext modulus of length 312 and 8192 slots".
  - TopGear: V = ceil(62 / log2(16385)) = 5, so U = 10 ciphertexts per proof, which is 81,920 triples per batch.
  - [SOURCE] Per batch, each ordered pair sends 4U drowned ciphertexts: the a·b cross term (SimpleEncCommit.cpp:398) plus the MACs on a, b and c (PairwiseGenerator::run). Each party proves once per batch.
  - [SOURCE] `Ciphertext::rerandomize` adds uniform noise of about p0/2 per coefficient. Since p0 >= B_clean (1 + 3·2^S) p, the bound is 2^-48.6 per ciphertext.
  - Per step: 54.7 batches, 13,132 drowned ciphertexts (2^-34.9), 164 proofs (2^-52.6), sacrifice 2^-38.9.
  - Release: 775 batches, 2^-31.1 drowning, 2^-48.8 proofs, 2^-35.1 sacrifice.
  - At S = 80, drowning is 2^-54.9 per step.
  - Every term is below the statistical-truncation term (2^-26 per step).
- [SOURCE NoiseBounds.cpp:77-89, OPEN for ember or the coordinator] MP-SPDZ sizes the ring as phi(m) >= 15.1 log q, from its own estimator run. That gives N = 8,192 for q = 2^312, while the HE standard's 128-bit bound for N = 8,192 is 218 bits. N = 16,384 needs a patched min_phi_m and a new key setup. lg64e is at N = 8,192.

**Follow-ups (the coordinator's decisions, 2026-11-07 afternoon)**
- **TLS identities rotate with the committee.** The MP-SPDZ TLS private key stays on disk on this condition: a new committee always gets new keys, made on their boxes, and pins only its own three certificates. Then an old seat's key authenticates to nobody after a rotation.
  - [EXECUTED, fingerprints] `seats.sh new` already did this: wired-new pins 28:E7.., 99:82.., FB:52.., disjoint from wired's A6:A8.., 2B:55.., 14:21...
  - The copy modes (`sh`, `newsh`, `newsh2`, `rehold`, `rehnew`) reused the source seat's TLS identity, so reh-old and reh-new pinned the same three certificates.
  - Fixed: every seats.sh mode now runs `openssl req -newkey rsa:3072` on the box for each new seat, and applies ramdir.sh to the new runtime.
  - A deployed rotation must take its new committee's MP-SPDZ runtimes from `seats.sh new` (or one of the modes above, as fixed), never a copy that carries the old key.
- **lg64e is under strength.** It is N = 8,192 with q = 2^312 (MP-SPDZ's own ring choice), so it is used only to measure LowGear's cost through hbox. A LowGear key the run uses must be at N = 16,384 (min_phi_m patched in build-mpspdz.sh), or at whatever the lattice estimator says reaches 128 bits. No N = 16,384 key setup through hbox until ember has chosen the third box.
- **hbox mount.** Recorded in ~/swarm/MACHINES.md under hbox (local commit 350825f). Undo with `sudo umount /othersys/lanes/dl-gen6-prep/ram` when the lane no longer needs it, after its processes there have exited.

**LowGear RLWE, estimated [EXECUTED on forge: `est/lowgear_rlwe.py`, gen 4's lattice-estimator under Sage, `nice` + `systemd-run MemoryMax=12G`]**
- Instance: MP-SPDZ v0.4.4 LowGear keys at -S 60. The secret and error are both centered binomial with eta = 1 (`FHE_Params` Chi(0.7), so NewHopeB = round(2 · 0.49) = 1), with m = N samples. 0-level q is 2^312.
- The estimator's full run excluded arora-gb and bkw, as gen 4 did.

| N | log2 q | rough (core-SVP) | usvp | bdd | dual | dual_hybrid | minimum |
|---|---:|---:|---:|---:|---:|---:|---:|
| 8,192 (as built, lg64e) | 312 | 53.7 | 87.0 | 86.8 | 88.1 | 87.8 | **86.8** |
| 16,384 | 314 | 149.2 | 179.2 | 179.0 | 180.5 | 179.4 | **179.0** |

- MP-SPDZ's built-in sizing gives about 87 bits for this field, far below 128. Its comment cites "alpha = 0.7 sqrt(2 pi) / q", which matches these distributions, but `min_phi_m = 15.1 log q` does not reproduce its own table.
- N = 16,384 clears 128 bits with margin, at both the rough and the full count. The 314 bits are an estimate; MP-SPDZ fixes the exact length when it builds the parameters.
- The run's LowGear must be at N = 16,384: patch `min_phi_m` in build-mpspdz.sh. lg64e (N = 8,192) is for cost measurement only.

**run13-rel, the sealed release chunk [EXECUTED, wired layout, MASCOT tau = 5, TLS, same key as run13-c0]**: 157,182,170 entries per
seat; DLVAULT2 tape 2,672,137,730 bytes; (sealed, empty) owner message 52 bytes.

| seat | wall | CPU user / sys | peak RSS | MP-SPDZ sent | assembly |
|---|---:|---:|---:|---:|---:|
| 0 (forge) | 1,467.2 s | 6,707 / 1,791 s | 1.37 GB | 946.8 GB | 7.4 s |
| 1 (bb2) | 1,465.1 s | 7,229 / 2,069 s | 1.42 GB | 946.3 GB | 8.4 s |
| 2 (bb2) | 1,462.3 s | 7,199 / 2,100 s | 1.40 GB | 946.3 GB | 8.1 s |

- Price check: 63.45M triple-equivalents in 24.4 min, against 4.48M in 3.4 min for the step. That is 23.1 versus 22.4 triple-eq per ms.
- Bytes: 946 GB per seat, about 119 kbit per triple-eq per seat, so 357 k for all parties. That matches the 362 k unit price of §3.
- The §10 estimate of about 27 min was right.
- The Transactions file was in RAM, and assembly wiped it.

**reh2's sealed chunks [EXECUTED; fresh seat sets `seats.sh fresh reh2-old 16300` / `reh2-new 16400`, MASCOT tau = 5, TLS]**
- Both seat sets got fresh TLS keys, made on their boxes. The pinned fingerprints are disjoint:
  - old: 67:F7.., 29:B7.., 03:40..;
  - new: 4F:EC.., 0D:08.., E3:DB...
- MAC key shares: reh2-old, reh2-new and wired are pairwise different (sha256 of the alpha_i word at offset 8 of Mascot-Secrets).
- Everything is held in RAM.

| chunk | key / vault | entries per seat | wall per seat | peak RSS | sent per seat |
|---|---|---:|---:|---:|---:|
| reh2-c0 (steps 0-1) | reh2-old, new key; seat<I> | 2 x 8,916,565 | 209-213 s | 1.83 GB | 133.8 GB |
| reh2-ho (handover) | reh2-new, new key; new<I> | 33,554,448 Ar | 123-127 s | 0.22 GB | 32.8 GB |
| reh2-n-c0 (steps 2-3) | reh2-new; new<I> | 2 x 8,916,565 | 201-205 s | 1.83 GB | 133.8 GB |

- Two steps per chunk took about the same wall time as one: 209 s against 200 s for run13-c0, with twice the bytes. So run13-c0 moved bytes at half the rate.
- [OPEN] The cause is not established. It may be a concurrent load on forge or bb2 at 12:06, or fixed setup cost.
- The 2-step chunks (and the release, 22-23 triple-eq per ms) give about 105 s per step on the wired layout.

**The release on a sealed tape fits forge [the deploy lane's measurement, run13, with fixes fa9b08c7 and 345782da on its side]**
- Forge, seat 0 (one custodian per process, MemoryMax=12G, `load_release_tape_sealed`): cgroup memory.peak **10.27 GB**, VmHWM 8.94 GB.
- bb2's seats: memory.peak 10.64 and 10.95 GB, VmHWM 9.32 and 9.60 GB.
- Release: 670 s (MPC 14.4 s, prove 251 s, verify 201 s). C = 8 of 52 at all three, as in the plaintext twin.
- The run13 chunks are spent and were shredded (`shred -n 0 -z -u`).

**A seat's erasure covers every field [EXECUTED, ff6f8c0d]** (the coordinator's finding: reh2's old seats kept their gf2^128 and B-64 MASCOT keys in /dev/shm after the handover)
- MP-SPDZ keeps one MASCOT MAC key per field it initializes, in Player-Data: `Mascot-Secrets-{p-61, 2-128, B-64}`, LowGear's key-generation field `p-3xx`, and a `Player-MAC-Keys-*` file in each `3-<field>/`. It also keeps memory dumps `Memory-{p,B}-P<i>` and Transactions files.
- All of these belong to the seat's epoch.
- `retire_mac_keys` (used by `--new-mac-key` and on abort) now wipes every file that `is_party_secret` names, in every field and in Persistence. Before, it wiped only the 61-bit files.
  - Test `retiring_a_seat_erases_every_secret_of_that_party_and_only_those`: 14 secret files of party 0 are erased, while another party's files and the public ones (pem, key, PairwiseParams) are kept. The old rule fails this test on the 2-128 file.
- `ramdir.sh RT RAM erase` does the same for a whole seat runtime from the shell, then lists anything left.
- reh2-old{0,1,2} were erased this way: 7 files each (Memory-B, the B-64 and 2-128 keys and their Player-MAC-Keys, the gf2n and clear Transactions). The deploy lane has the full --erase-extra set.

**LowGear at N = 16,384 (the coordinator's call: stop lg64e and replace it) [EXECUTED]**
- lg64e was stopped at 13:37 UTC by its PID files (SIGTERM to each lowgear-party.x).
  - The wrappers exited with "abort, status 15"; no LowGear-Secrets had been written yet.
  - The partial key-setup secrets (Mascot-Secrets-p-319 and the other fields) were erased with `ramdir.sh erase`.
  - The cached N = 8,192 `PairwiseParams-*`, whose filename does not encode N, was deleted from RAM and from the skeletons.
- Build: `build-mpspdz.sh` now patches `FHE/NoiseBounds.cpp` `min_phi_m` from `15.1 * log_q` to `40 * log_q`.
  - Built on bb2: lowgear-party.x 38adf2bf, highgear-party.x 4434b1ab, tarball de1b6dba. mascot-party.x is unchanged (4d50d76f, the EINTR-fixed d1299708).
  - Installed in the three custodian runtimes as lowgear and highgear only.
- [EXECUTED, bb2 loopback, `-o verbose_he_setup`, stopped by PID file] "Need ciphertext modulus of length 314 and 16384 slots", the instance estimated at 2^179.0. The field prime is 1 mod 32,768.
- `lg64f` is the three-box key setup at N = 16,384: the same command as lg64e (`BIN=target-g2`, `--new-mac-key`, d = 64 test chunk), started 13:5x UTC.
  - PairwiseParams is 5.77 MB (it was 2.88 MB at N = 8,192).
  - The secrets land in RAM. On hbox that is the 8G noswap tmpfs: LowGear-Secrets at N = 16,384 is megabytes, and Transactions for a 2-step d = 4096 chunk is about 0.3 GB.
- run13's key on wired{0,1,2} was retired after run13 (9 files each, `ramdir.sh erase`). The deploy lane's dl-custodian `--erase-runtime RT` (902b44c4) uses the same `is_party_secret` set at a rotation.

**run13's key retired [EXECUTED, 2026-11-07 ~13:47-14:00 UTC]**
- MP-SPDZ files (`ramdir.sh erase`): 9 per seat on wired0 (forge) and wired1, wired2 (bb2), all in RAM:
  - Mascot-Secrets-{p-61, 2-128, B-64}-*-P<I>-3;
  - {3-p-61, 3-2-128, 3-TT-8}/Player-MAC-Keys-*-P<I>;
  - Memory-{p,B}-P<I>;
  - Transactions-{clear,gf2n}-P<I>.data.
  The individual names were counted, not captured.
- Epoch file keys: dl-vault:dl-gen6:0:0:da4e4c79b16ee4de (forge), 1:0:6eedd3acf11a0a38 and 2:0:f71f51f3e3a91a3e (bb2).
  - Each was invalidated with `scratchpad/.../keyinv.py`: link the persistent keyring, KEYCTL_SEARCH by name (which must return the serial /proc/keys shows), then KEYCTL_INVALIDATE.
  - /proc/keys no longer lists them.
- Name check (check_handover.py's `is_party_secret`, the same `find -L ... -maxdepth 2`): wired0, wired1 and wired2 each show 0 secret files.
  - Negative control: a planted `Mascot-Secrets-2-128-ctl-P0-3` was detected, then removed.
- The chunk tapes were shredded earlier. reh2's keys (both committees) and chunks are retired and shredded the same way.
