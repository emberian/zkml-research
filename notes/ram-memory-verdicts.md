# RAM/memory-checking verdicts (first half of the lookup/RAM lane)

2026-08-13, via peer relay. Repo-verified at Jolt and SP1 HEAD; mirror
full-texts cited by line. An addendum on RISC Zero/OpenVM/Ceno/Nexus is
referenced as already-landed but has not reached this session — reconcile
when it does. Second half (lookup arguments proper) pending.

## The dominant finding: Twist/Shout is CLOSED to our stack — by its authors

Not inference. The Twist/Shout paper itself: hashing-based commitments make
committing zeros non-free, the K·T one-hot cost is intolerable, and **the
only named rescue is packing into GF(2^128) — binary fields only**
(Binius/FRI-Binius/Blaze). And 2025/611 (Nair–Thaler–Zhu), verbatim: Twist+
Shout wants curve, lattice, or binary-field-hash commitments; **"the
Lasso+Spice version of Jolt may still prove useful for projects that seek to
work with other commitment schemes over other fields."** BabyBear/KoalaBear
+ FRI + Poseidon2 is none of the three. **The authors are pointing stacks
like ours at Spice-class offline checking.** Corroborated by behavior:
Jolt's own answer to one-hot commitment was to build a LATTICE PCS (Akita),
not FRI.

⚑ Consequence for the towers: **binary-tower packing is what unlocks
Twist/Shout** — one more argument for the prime↔tower seam as the committed
second field (the field memo's own recommendation).

## Jolt at HEAD, repo-verified

Migration landed totally: RAM/registers = Twist, lookups/bytecode = Shout;
**Lasso and Spice DELETED** (grep: zero hits; the 0.1.0 design is an
appendix). Default PCS is **Dory over BN254 — pairing-bound**, production
path confirmed in source. Honest delta from the paper itself: Twist beats
Spice ~3×/~2× for the 32 registers, "more modest" for larger memories — the
circulating "10×+" is against the log-proof Quarks configuration that pays
~500 extra field ops per op. Vendor numbers (unverified): >1M RISC-V
cycles/s on 32 cores, ~50 KB proofs, 6× overall, <2 GB RAM streaming.

## SP1 Hypercube, two corrections and two levers

- ⚠ **SP1 is on KoalaBear, not BabyBear** — including the septic-extension
  multiset-hash curve (Ceno's analogous accumulator is the BabyBear^7 one;
  keep them straight). Another data point for the field memo's verdict.
- **The cross-shard tier is Shor-breakable**: an EC multiset hash whose
  binding is EC DLOG. Intra-shard LogUp-GKR is PQ-fine; the cross-shard
  curve disqualifies the design as-is for PQ targets. **Our Selvage
  accumulation is hash-based — do not copy SP1's cross-shard design.**
- Measured amplification: a first-touched address costs ~502 trace cells
  (~194 gas) vs 39–44 for the load itself — **~14×, scaling with distinct
  addresses per shard, not memory ops.**
- **The levers to steal**: trusted ROM as a PREPROCESSED table (17 cols,
  zero memory traffic), and the recursion machine's **write-once SSA
  memory** — {addr, mult} both preprocessed, no timestamps, no sorting, no
  range checks: 2+4 cols per access vs ~502. Our recursion circuits should
  use exactly this.

## Read-only vs read-write: the mechanism, priced

Spice per-op: read commits 5 small values, write 6 (~40 field ops with fast
grand products); **read-only drops to Lasso 3T / LogUpGKR 2T / Shout T
because timestamps need no range checks — "simply incremented by 1"** (the
range checks are 2 of the 5 committed values and 4 of the 6 factors). For
us: weights and tables are read-only → the cheap path; only true
read-write state (KV-cache) pays the Spice premium.

## The drop-in gem: stacks/queues (2024/2084)

Pure Horner/universal hashing in-circuit — **no commitment-scheme
dependency, no field assumption**: queue reads 3 mults + 1 advice, writes
2 mults; stack similar. Three orders cheaper than Spice **iff the access
pattern is genuinely LIFO/FIFO**. Soundness (T−1+