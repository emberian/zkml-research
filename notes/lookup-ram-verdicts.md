# Lookup & RAM frontier: the three-member law and the per-consumer verdicts

2026-08-13. Final campaign lane, delivered in halves (peer relay + addendum);
sources verified at repo HEAD for Jolt/SP1/OpenVM/Ceno. One sub-lane
FABRICATED a quote from 2025/105 — caught by grepping the extracted text,
discarded; the surviving claims rest on real passages.

## The organizing law (the sweep's centerpiece)

**One-hot addressing (Twist/Shout) requires a commitment scheme in which
sparse/boolean data is structurally cheap. Three members exist: MSM zeros
(curves), binary-tower bits (Binius/Blaze), and — the live third — lattice/SIS
sparsity.** BabyBear + Poseidon2 + FRI has NONE of the three, **on the
authors' own authority**: 2025/105's committing-to-0s-is-not-free passage
(only rescue named: GF(2^128) packing), and 2025/611 verbatim pointing
projects on other fields at Lasso+Spice. Verified absence four ways; the
only "one-hot addressing" phrase hits archive-wide are 2025/105 itself and
2026/1390. The large-K small-prime-FRI instantiation is the open problem
(2025/105 fn.3 concedes tiny memories work anywhere).

**The third member is being built now**: Jolt's Akita — an Ajtai/SIS PCS
co-designed for one-hot witnesses (repo-measured: 81.3s → 8.19s across July,
targeting ≤0.5× Dory). And **ArkLib's real proof effort is on Hachi, the
Jolt-adjacent lattice PCS** — where the formalization community points.

## Production corroboration (repo truth at HEAD, 2026-08-12)

SP1 (KoalaBear — CONFIRMED moved off BabyBear), OpenVM (BabyBear), Ceno
(Goldilocks-family): **all three small-field hash-PCS zkVMs ship LogUp-GKR
lookups + classic timestamp offline memory checking. None ships one-hot.**
The one Twist/Shout system (Jolt) runs Dory over BN254 — a pairing curve.
Jolt's migration is real (Spice/Lasso DELETED, zero grep hits) with the
honest delta ~3× commitment / ~2× field ops for registers per the paper
itself — the "10×+" headlines are against the expensive log-proof Quarks
config (~13× dearer, ~500 field-ops-equivalent per op in random commitments).

SP1 details worth holding: two-tier memory — intra-shard LogUp-GKR
timestamp-diff checking (hash-based, PQ-fine) + cross-shard EC multiset hash
over KoalaBear^7 (**Shor-breakable — disqualifies the design as-is for PQ**;
Ceno's analogue is BabyBear^7, keep them straight); measured **~14×
first-touch amplification** (502 trace cells vs 39–44 for the load itself);
and **SP1 prices FRI in the PROVEN regime** (`unique_decoding_queries`).

## The read-only/write-once levers (the decode-loop gift)

The biggest measured lever anywhere in the sweep: **SP1's preprocessed
program ROM costs complexity 0, and its recursion machine uses WRITE-ONCE
SSA memory — 2 preprocessed + 4 main columns per access vs ~502 cells for a
general RAM touch.** The mechanism behind the read-only discount: no
timestamp range checks (drops Spice 11T→3T committed, 80T→12T ops).

Mapped onto our decode loop [mine]: **weights are read-only (preprocessed
tables), the KV-cache is append-dominant (write-once-shaped)** — the
expensive general-RAM case barely appears. Plus: the BKV24 optimal-tree
shape is right exactly for FAT cells, and KV-cache entries are fat; and
2024/2084's stack/queue technique (2–5 mult gates/op, no commitment
dependency, challenge drawn in Ext4 or soundness is ~2^-11) drops straight
into BabyBear wherever access is genuinely LIFO/FIFO.

## Status changes and cautions

- **T2 (Twist/Shout over hash commitments via logup*) is claimed, not
  built**: Powdr's note (Oct 2025, never on eprint — mirror-invisible)
  writes exactly this composition; field-generic, paper-only, zero code.
  Raises the spike's value, removes "unclaimed." Read it before spiking.
- **Nebula's memory technique ports to hash stacks** (its incremental
  commitment is abstractly a hash chain) but its 480× is against
  curve-multiset-Spice INSIDE IVC — **in a monolithic STARK with
  post-commitment challenges the trick buys nothing.** Re-derive before
  pricing. The folding substrate does not port.
- **Lower bounds: gap closed, and not harvestable.** BKV24's own
  construction matches the Ω(log n/log log n) bound with public state — but
  the bound counts BANDWIDTH, not hash permutations; the "optimal" shape
  hashes ~2× MORE. Do not upgrade a binary Merkle tree expecting a SNARK
  win. Offline checking is outside the model entirely (both papers say so);
  Spice escapes 2025/358 twice over.
- **All field-op constants are moving**: 2026/587 (CCS'26) claims >10×
  sumcheck-prover inside Jolt — Haböck's 43, Celer's 10, everything in the
  comparison tables is denominated in a unit this paper moves. Do not lock
  LogUp-vs-Celer until it is read. (A cost verdict outlives its premise.)
- **Jolt soundness incident** (May 2026): the verifier never checked the
  uni-skip output claim — forged proofs verified. Another
  gate-that-cannot-go-red specimen for the instruments file.
- New lookup arguments beating LogUp-GKR/Shout, May–Aug 2026: **none**
  (verified). Twist/Shout is at CRYPTO next week (camera-ready ~3× prover
  vs old Jolt, claim-level). **Flock** (Bünz et al., hash-based batched
  boolean/hash SNARK, 42k SHA-256/s on one M4 core, >9× Binius64, measured)
  noted for hash-heavy batch workloads.

## Per-consumer verdicts

⚠ Anti-myopia (ember): consumers (a)-(d) below are the zkML/vFHE set, but
**Selvage/minidregg has its OWN internal lookup and memory consumers** —
`LogupStar`, `BinaryLookup`, `LogupIndexLink`, the `Tower256Logup*`
controller/admission family, the AIR-side LogUp bridges
(`AuthenticatedColumnLogupBridge`, `SparseAuthenticatedStateLogupBridge`),
`AirRange`, and the umem memory boundary. Every frontier verdict here
(LogUp-GKR standing, the moving 2026/587 constants, the read-only/write-once
levers, the three-member one-hot law) applies to those consumers too, and
any migration decision must enumerate them — consumer (g), the home tree.

(a) 2^16 exact tables → **LogUp-GKR stays**, Celer spike still gated on
2026/587's re-pricing. (b) vFHE gadget decomposition → LogUp-GKR/719-style.
(c) hash lookups → moot (no 31-bit Monolith). (d) KV-cache RAM → **offline
timestamp checking + the read-only/write-once levers**, with Deep
Thought/Nebula techniques re-derived in the monolithic setting, and
stacks/queues where access is LIFO/FIFO. One-argument-vs-three: **three
specialized arguments is the honest answer** — the production field already
made the same choice.
