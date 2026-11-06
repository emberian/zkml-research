# Recommendation: change the leaf, keep the spine

2026-11-06, redesign lane. Evidence: MODEL.md (composed model and the measured kernel), DESIGNS.md (ranking),
CODEX.md (blind proposal; it reached the same core change independently). Tags as there.

## 1. The call

**Change** the certificate leaf from "one symbol per Tower256 element" to **packed binary**: commit the trace at
its own width (bits and bytes packed 256 per Tower256 word), encode with additive RS over GF(2^16) = T_4
twiddles, hash wide cSHAKE leaves, reach Tower256 challenges by ring switching, and make the byte lane's
systematic subtree the record's content tree. **Keep** the spine: Tower256 as the challenge field, cSHAKE256
everywhere (roots and internal trees), UD-100 proximity, the additive-FRI/BaseFold controllers with collision
extraction, Lean-owned acceptance. **Aggregate by batching**, never by per-leaf recursion. Run the leaf prover
**CPU-first**.

Expected end-to-end gain [MODEL; the PIOP, the packed encode, today's leaf rates and the 64-core per-core rate
are MEASURED, MODEL.md sections 3 and 8]:

| | today (a) | packed (c) | gain |
|---|---:|---:|---:|
| per 4 KiB record, batched, one Kaggle core | 69.8 ms | 4.5 ms | 15x (PIOP measured; 10-18x over the encode range) |
| per record, 64-core Genoa-class box | 894 us | 58 us | 15x |
| per record, H100 [MODEL] | 1.27 ms | 69 us | 18x |
| per record with per-leaf recursion instead of batching, one core | 2.29 s | 222 ms | batching removes ~98% of either |
| audit at 1%, per record, one core | 0.70 ms | 46 us | 15x |
| light-client verify | 28.6 ms | 2.8 ms | 10x |
| proof bytes at UD-100 | 1.46 MB | ~0.45 MB [A] | 3x |

The order of the levers, largest first: batch instead of recursing per leaf (~40x of a leaf), pack (15-18x),
then everything hardware-shaped (tensor GF(2) 2.5-3.5x on GPUs if a fused kernel wins; BLAKE3 internal trees
1.0-1.6x batched; GF(2^128) challenges 1.4x). This is the same ordering PROOF-SYSTEM-SPACE found for zkML
(statement shape and amortization before tensor cores), now in seconds for our own leaf.

## 2. Preconditions (ember's decisions)

1. **The content-tree format.** The packed proof's message subtree must be the store's content tree,
   framing and leaf width included (Codex's point: matching the algorithm name is not enough). That means record
   content trees with wide leaves (e.g. 128-256 contiguous bytes per leaf, cSHAKE, the u32 length codec of
   LEAF-PROVER-DECISION section 7). It is a store-format flag day. It also makes the store's own commit cheaper
   (~47 Keccak-f per 4 KiB against 255 for one-byte leaves). Without it, the leaf must open the store's tree
   in-circuit: 255 Keccak-f x 38,400 constraints ~ 9.8M constraints per 4 KiB record, more than the DFA.
2. **The security budget.** Whether "100 bits" is per-term (today's 148 queries) or a composed budget (Codex:
   ~192 elementary bits, ~300 queries). It changes verifier hashing and proof bytes ~2x in every design and does
   not change the ranking. It does decide that challenges stay in Tower256 rather than T_7.
3. **No hash-ruling change now.** Revisit BLAKE3 for parity/fold oracles only if the packed prover measures a
   hash share above ~50% after batching.

## 3. Migration, in order (each step usable on its own)

| step | what | where | cost |
|---|---|---|---|
| 1 | **Done (native openings).** `tower256_openings.c` behind the GPU host, minidregg `lane/redesign-native-openings` 95463f3ae | minidregg prover/cuda | **measured on a T4, receipts identical:** ell 20 openings 212 -> 31.5 ms, wall 335 -> 144 ms (2.3x); ell 14 119 -> 41 ms. Left: one gather kernel per round instead of k - 1 (the 31.5 ms), and the Rust host for production |
| 2 | Lean: subfield-twiddle domain (basis in T_4, twiddle closure, computable) | minidregg Theory/Compiler | one bounded statement; `Coordinate` arithmetic and the T_4 embedding exist |
| 3 | Lean: systematic-subtree binding, `named_or_collision` for the message subtree of a codeword tree | Compiler/Tower256ContentCert successor | one bounded statement, same shape as the landed one |
| 4 | Lean: ring switching instantiated at Tower256 with T_4 packing, feeding the succinct controller | Selvage/RingSwitching.lean exists (Diamond-Posen compiler) | instantiation, not new theory |
| 5 | Native packed commit: blocked LCH encode + the tuned Keccak, CPU first (kernels/encode.c is the bit-exact reference shape) | minidregg prover | encode is 4.7-9.9 ns per codeword byte unblocked on a Xeon core; blocking is the known 2-3x |
| 6 | The leaf PIOP: binary zerocheck + Shout read-check over the packed DFA trace. **Minimal layer built and measured** (`kernels/piop.c`): 8.00 multiplies, 161-186 ns per row on one Kaggle core, 128-141 on Genoa, 94% thread scaling on 16 cores; the full DFA layer composes to ~16/row, as the model assumed | Selvage/MultilinearZeroTest, BinaryLookup exist; owed by any design | the full layer (4 address chunks, ~6 constraint columns) is the next run, not a new unknown |
| 7 | Batch-first aggregation: 1,024 records (or one 64 KiB stream window) per proof; recursion only to compress a final proof | composition layer | removes per-leaf recursion |
| later | Ligerito instead of BaseFold (after its soundness bridge), bit-sliced fused GPU encode (predicted 0.03 ns/B), GPU PIOP via fixed-r tensor folds, BLAKE3 internal trees, T_7 challenges | | each gated on an end-to-end measurement |

**What dies:** the one-symbol-per-element trace layout and the per-byte-leaf `contentRoot` of
`Tower256ContentCert` (its statement shape survives; the root's leaf width changes). Nothing in the Tower256
arithmetic, cSHAKE, controllers, ArkLib UD bridge or Selvage cone is discarded.

**Automata leaf interface:** `ContentCert` keeps its fields; `contentRoot` becomes the wide-leaf cSHAKE root
(precondition 1); `deltaRoot` becomes a packed committed table read by binary Shout (`Selvage/BinaryLookup.lean`
fixes the one-hot semantics). Weld8's binary hot spot (8 rows x 11 columns per byte on BabyBear, COUNTS.md) becomes
8 packed bits per byte: it is the case this design is shaped for.

## 4. What would make this wrong

- The full DFA layer costs more than ~64 Tower256 multiplies per row (the measured minimal layer is 8; then (c)
  would lead (a) by only ~5x on GPUs; it would still lead).
- A measured binary recursion step much cheaper than 38,400 constraints per Keccak-f (then per-leaf recursion
  matters less and the hash question returns).
- The store cannot adopt wide content leaves (then content binding costs ~9.8M constraints per 4 KiB in-circuit
  and the packed design's advantage on single records shrinks; batches over many records still amortize).

## 5. What was measured here

`kernels/encode.c` and `kernels/encode_gpu.cu`: the packed commit's encode, bit-exact against a Lagrange
reference (an independent port of minidregg's Fan-Paar multiply) and identical across Mac NEON, Xeon SSSE3, T4
per-layer and T4 fused kernels. Kaggle runs `redesign-encode-t4-01` and `-02` (KAGGLE-LEDGER.md rows; results in
`runs/`). Since then (`redesign-piop-t4-03`, `redesign-openings-t4-02/-03`, dregg-forge):
- the PIOP's minimal layer (`kernels/piop.c`, checked by `piop_ref.py`: transcript identical to an independent
  Python prover, the verifier accepts, one violated row makes it reject): 8.00 multiplies and 161-186 ns per row
  on the Kaggle core, 128-141 on Genoa, 1.18e8 rows/s on 16 Genoa cores; the model's guess was within 5%;
- the T4 fused encode with basis-built tables: 0.055-0.079 ns per codeword byte (1.2-1.4x); the earlier
  "bank conflict" diagnosis was wrong (MODEL.md section 3);
- native openings (step 1) on the T4: wall 2.3x at ell 20.
Nothing was rented. Not measured: the full DFA layer, any H100/B200/TPU number for this design (the model scales
T4 and CPU measurements), a GPU PIOP, and BLAKE3. bb2 was not used (load 35 on 32 vCPUs from obend).
