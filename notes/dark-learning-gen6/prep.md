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

## 4. LowGear (HE-based, Overdrive) against MASCOT

[EXECUTED, loopback on forge, `lgtest/` (a test directory with its own keys, separate from custodian 0's)]:

| run | triples | bytes sent, all parties | marginal bits per triple | time |
|---|---:|---:|---:|---:|
| LowGear S = 40 | 20,000 | 471.95 MB | | 7.3 s + 230 s key setup |
| LowGear S = 40 | 100,000 | 943.83 MB | 47.2 k (20k -> 100k) | 14.5 s |
| LowGear S = 40 | 300,000 | 1,887.81 MB | **37.8 k** (100k -> 300k) | 28.8 s |
| LowGear S = 60, -lg2 64 | 100,000 / 300,000 | 943.84 / 1,887.81 MB | 37.8 k | 14.6 / 29.0 s |

S = 60 costs nothing measurable in bytes. LowGear sends about **9.6x fewer bits per triple** than MASCOT tau = 5
(362 k). Key setup (BGV keys + MAC key) takes about 230 s per epoch and is cached in `LowGear-Secrets-*`.
Three-box LowGear: see §5 (pending).

## 5. Per step at d = 4096, through hbox (DERIVED from the measured unit prices; hbox at its measured 19.3 Mbit/s)

LowGear loopback unit prices (all parties, marginal, S = 60): triple 37.8 k, random bit 38.3 k, power-chain product
37.7 k, joint random 3.78 kbit. MASCOT tau = 5 three-box: 362 k per triple-equivalent, 23.5 k per random (gen 5).

Step at d = 4096, GEN6 program (truncations (11,19), (11,19), (7,8), (8,19)), carried (x, y input): 286,722 Beaver
triples, 1,040,384 power products, 921,600 bits, 8,192 input tuples = 2,256,898 triple-equivalents, plus 16,384
randoms. Proof section (proof lane, commit 1a38eb82, `darkproof counts`): 4,101,581 triples.

| backend | proof section | triple-eq per step | total (Tbit) | **hbox upload per step (Gbit)** | hours per step via hbox |
|---|---|---:|---:|---:|---:|
| MASCOT tau = 5 | no | 2,256,898 | 0.817 | **272.5** | 3.9 |
| MASCOT tau = 5 | yes | 6,358,479 | 2.302 | **767.4** | 11.0 |
| LowGear | no | 2,256,898 | 0.086 | **28.6** | 0.41 |
| LowGear | yes | 6,358,479 | 0.242 | **80.6** | 1.16 |

Traffic is symmetric (each party sends a third, half on each link; §3), so hbox's upload is total / 3. The hours assume
hbox's MASCOT-measured 19.3 Mbit/s; LowGear's larger messages may run nearer the 40 Mbit/s raw uplink (§4 three-box
pending). LowGear also costs a one-off key setup per epoch (230 s compute on loopback; over the WAN, over 1.2 GB from
hbox and over 17 minutes on the first attempt).

## 6. Randomness: no seeded randomness on a production tape

| component | randomness | source | test-only override |
|---|---|---|---|
| darkprep `party-chunk`, `assemble`, `export-darkstep`, `owner` | none: tapes are linear maps of MASCOT output; the owner check is deterministic | — | the synthetic tests' PyRandom (tests/assemble.rs only) |
| MP-SPDZ `PRNG::ReSeed` (every party-local PRNG: shares, MAC key, OT, BGV keys) | libsodium `randombytes_buf` (getrandom) | OS | `-o zero_seed` calls `insecure()`, which exits unless built with `-DINSECURE`; our build does not define it |
| MASCOT's check coins (MAC check, sacrifice, combine) | `Create_Random_Seed`: commit-and-open among all parties, each contribution from `ReSeed` | OS, jointly | none |
| `Processor::shared_prng` | party 0's `ReSeed`, sent to the others | OS (one party) | used only by public-random program instructions; darkprep.mpc has none |
| TLS keys (`setup-box.sh`) | `openssl req -newkey` on each box | OS | — |
| loopback tests (`lgtest/`, `run`) | as above, but all three keys in one directory | OS | test-only by construction (never a custodian directory) |
