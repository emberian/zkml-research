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
