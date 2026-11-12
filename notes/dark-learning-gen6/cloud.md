# dark-learning gen 6, cloud seat lane: the third custodian on a rented datacenter box

ember's decision (2026-11-07): no more custody traffic through hbox's home Wi-Fi; the third custodian goes on a
rented box ("deal with the cloud resources you have"). This lane takes the deployment lane's role for the run of
record. vast.ai first ($19.28 left of ember's $25 cap), GCP only as the fallback (egress ~$0.12/GB: 0.6 TB out alone
would be ~$72, over its $20 cap).

## The harness: `vast_box.py hold` and `cpu-offers` [EXECUTED]

notes/accelerator-readiness/harness/vast_box.py keeps its rules (key read in-process only, one box at a time, the
$25 ledger cap, destroy and verify absence, every rental in VAST-LEDGER.md). New:
- `cpu-offers`: on-demand offers ranked by hours x rate + TB out x the host's upload price + TB in x its download
  price (hosts bill each direction per GB; prices span $0 to $52/TB, which decides more than the hourly rate here).
- `hold`: rent, wait for ssh with our key (destroy if the host refuses it for --ssh-timeout), write OUT/ssh.json and
  OUT/ssh_config (Host alias, the per-instance known_hosts, StrictHostKeyChecking yes), then watch. Destroyed and
  verified absent at the first of: wall clock, spend cap (credit drop through the API, or rate x elapsed), OUT/RELEASE,
  SIGTERM, the instance leaving "running". `--runtype ssh_direct` and image `docker.io/vastai/kvm:...` for a VM.
- run.py: cfg "ssh_config" (passed as `ssh -F` / `scp -F` to every call): a held box's Host block followed by
  `Match all` + `Include ~/.ssh/config`. ember's ~/.ssh/config is a Mackup/iCloud symlink, so it is not edited.

## Box 1: a container in Switzerland, refused for the seat (17:33-17:46 UTC) [EXECUTED]

Offer 57922449 (Ryzen 7 5700X 16 threads, 47 GB, $0.267/h, $0/TB, static IP; the first choice, Czechia 13080902
at $0/TB, was rented away before our PUT). ssh key accepted in 167 s. Probe (`bash -s < probe.sh`):
- **The kernel keyring is blocked**: `add_key`, `keyctl(GET_KEYRING_ID)`, `keyctl(GET_PERSISTENT)` all EPERM
  (Docker's seccomp, Seccomp: 2). dl-hand's vault keeps the epoch's file key in the uid's persistent keyring and the
  erasure check invalidates it there, so no vast container can be a seat like hbox's. Docker's default profile is
  the norm on vast hosts: the seat needs a VM instance.
- The host has an 8 GB /swap.img (the container's memory.swap.max is 0).
- Baseline link from Switzerland (tcpprobe.py, 512 MB per direction): RTT 31 ms to both; one stream up 506 / 511,
  down 325 / 546 Mbit/s (forge / bb2); four streams up 680 / 663, down 355 / 606.
Destroyed and verified absent. Cost about $0.06 (the ledger's $0.46 credit drop includes another lane's H100,
accel-h100-tower-e2e-01, rented at 17:34 while this box was held: a rule conflict the coordinator raised upward).

## Box 2: a KVM VM in Quebec, the seat (from 17:48 UTC) [EXECUTED]

European VM hosts that meet the specs cost $0.24-0.9/h plus $2.6-3.9/TB each way: $9-20 for the run, too close to
the cap (and the cheap ones are 8-core / 300-400 Mbit). Coordinator-approved: a Quebec VM at $0/TB.

| | |
|---|---|
| provider, offer, instance | vast.ai, offer 58947060, instance 59604881 (verified host, reliability 0.994), on-demand |
| location | Quebec, CA; public IP 67.70.78.162, ssh direct port 26865 (the proxy port timed out) |
| price | $0.067/h; bandwidth $0/TB up and down; disk 150 GB |
| guest | KVM, Ubuntu 22.04.5, kernel 6.8.0-59; 19 vCPU Xeon E5-2673 v4 2.3 GHz (AVX2, BMI2, ADX, AES, PCLMUL; no AVX-512); 49 GB RAM (the offer said 63) |
| caps | hold: cap $8, watchdog 40 h (destroyed by 2026-11-09 09:48 UTC at the latest) |

ssh key accepted in 230 s.

### The link from Quebec to forge and bb2 [EXECUTED]

`native/deploy/cloud/tcpprobe.py`: servers on forge and bb2 (port 28690, own PID files, self-ending after 900 s), the
VM dials (it is NAT'd: only its ssh port is mapped), uploads then downloads 1 GiB per stream count; throughput timed
at the receiver of the data. Stock kernel settings on all three (cubic; tcp_wmem max 4 MiB, tcp_rmem max 6 MiB).

| peer | RTT min / median | up x1 | down x1 | up x4 | down x4 |
|---|---:|---:|---:|---:|---:|
| forge (stock) | 103.3 / 103.6 ms | 166 Mbit/s | 231 | 593 | 885 |
| bb2 (stock) | 102.4 / 102.8 ms | 158 | 238 | 362 | 901 |
| forge, first probe (512 MiB) | 104.4 / 104.9 | 159 | 234 | 573 | 835 |
| forge, VM 64 MiB buffers + BBR | 103.3 / 103.8 | 158 | 241 | 163 | 892 |
| forge, VM 64 MiB buffers, cubic | 101.9 / 102.3 | 69 | 250 | 196 | 863 |
| forge, VM rmem 32 MiB only | 105.8 / 106.0 | 163 | 239 | 566 | 868 |

- One TCP stream is bounded by the 104 ms RTT: download by the SENDER's send buffer (forge/bb2 4 MiB = ~320
  Mbit/s at 104 ms; not this lane's boxes to tune), upload at ~160 Mbit/s. Raising the VM's send buffer made upload
  worse (losses on the host's shaped uplink), so the VM runs stock settings (the sysctl file is parked at
  /root/90-dl-cloud.conf.off). Parallel streams reach ~0.6 Gbit/s up and ~0.9 Gbit/s down.
- For planning: a single darkstep TLS link per directed pair carries ~160 Mbit/s from the VM and ~235 Mbit/s to it;
  the seat's two links together ~320 / ~470 Mbit/s, unless a protocol opens several connections per pair.

### Building the seat [EXECUTED]

- `native/deploy/cloud/seat-setup.sh base` (swap off and masked; keyutils, rust 1.99.1 as on forge): BASE-OK, no
  swap, `keyctl add` + `invalidate` on @u works, `keyctl get_persistent @u` works, /dev/shm tmpfs 24.6 G.
- Rust r13 and t13 at 090a11a0 built on the VM (Ubuntu 22.04). Source tree check: sha256 over the 147 source
  files of forge's /srv/lanes/dl-gen6-deploy/ws equals the VM's (b61b692c...), so forge's r13 was built from
  exactly 090a11a0. The binaries' sha256 differ (glibc 2.35 vs 2.41 toolchains): forge r13 dl-custodian 522297c8,
  darkstep dda0c07c, dl-owner 0b25d55a, dl-hand 47fbcff9; VM 44e015d7, bc664727, d7f6fe6d, 8e6fc5eb.
- MNIST staged at /srv/lanes/dl-gen6-deploy/data/mnist; sha256 of all four files equal to bb2's.
- Linux-only erasure tests on the VM (0 GPU, KVM kernel 6.8): darkhand `--test vault` 3 passed (the keyring survives
  the process, destroy erases it; its child run after destroy fails to find the key, the built-in control);
  `--test ram_scan` 1 passed.
- MP-SPDZ from prep's build-mpspdz.sh (ff6f8c0d, the script that built the seats' lowgear 38adf2bf): the seven source
  tarballs are byte-identical to bb2's dl.sha256, but the release tarball leaves the SimpleOT / SimplestOT_C / libOTe2
  submodules empty (bb2's are git checkouts: SimpleOT 44aac605, SimplestOT_C 7ef76669, libOTe2 fe6b2ff8, libOTe
  558f74d5), Ubuntu 22.04's clang 14 needs libstdc++-12-dev, and the static link then fails (libsodium's blake2b vs
  cryptoTools'). Toolchain drift from bb2's Debian 13 / clang 19. Instead the VM is upgraded to Ubuntu 24.04
  (glibc 2.39), where prep's own static binaries (mpspdz-tau5.tar.xz = de1b6dba: lowgear 38adf2bf, mascot 4d50d76f)
  and forge's r13 binaries run unchanged: the same sha256 on all three seats. The vast image's held NVIDIA 575
  packages were purged first (the seat does not use the GPU); one reboot (back in < 1 min, still no swap).
