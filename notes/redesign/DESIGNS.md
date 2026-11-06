# Designs, ranked by composed time, recursion cost, soundness and what our Lean can carry

2026-11-06, redesign lane. Numbers: `composed.py` (MODEL.md section 4); per-record, batch throughput unless noted.
Tags as in MODEL.md. "Lean carry" names files in minidregg `Selvage/`, `Theory/`, `Compiler/` that exist today
[READ] and the statements that would be new.

## 1. The candidates

| id | design | field / code / hash |
|---|---|---|
| **a** | today: Tower256 additive FRI, one symbol per 32-byte element, one element per Merkle leaf | Tower256; additive RS rate 1/4 (Gao-Mateer); cSHAKE trees |
| **b** | (a) + tensor-core GF(2) fixed-r encode/folds + BLAKE3 internal trees | as (a); dense 0/1 GEMM + parity read (ROTATION 2(b)) |
| **c** | **packed binary**: commit the trace at its own width (bits/bytes packed 256 per Tower256 word), additive RS with T_4 = GF(2^16) twiddles, wide cSHAKE leaves; the byte lane's systematic (message) subtree is the content tree; ring switching to Tower256 challenges; zerocheck + binary Shout lookup | Tower256 challenges; GF(2^16)-twiddle additive RS (FRI-Binius/BaseFold shape, later Ligerito); cSHAKE everywhere |
| c128 | (c) with challenges sampled from T_7 = GF(2^128) inside Tower256 | 4x cheaper CPU multiplies; less soundness margin |
| cB | (c128) + BLAKE3 for parity and fold oracles (content subtree stays cSHAKE) | needs a ruling change |
| **d** | Brakedown/expander over BabyBear on tensor cores | BabyBear felts; linear-time code; Keccak content binding in-circuit |
| **e** | BabyBear/KoalaBear sumcheck-heavy (Spartan/HyperPlonk), boundary-only commitment | as (d) for certificates (same binding cost) |
| f | Codex's target: (c) with a recursive interleaved RS (Ligerito) PCS instead of BaseFold/FRI | smaller proofs and verifier; soundness bridge open |

(d) and (e) are priced together in the model: for **certificate** leaves both pay the same fatal term, the
record's cSHAKE root evaluated in a prime field (31 Keccak-f per 4 KiB x 63,192 BabyBear cells = 1.96M cells per
record, LEAF-PROVER-DECISION section 1). For dense arithmetic (inference recompute, dark-learning spine), (e) is
the right shape and is ranked separately in section 4.

## 2. Ranking for the certificate pipeline

Per record, aggregate-batch (1,024 records per proof), from `composed.py` with the measured PIOP (MODEL.md
section 8; cpu64 = 64 Genoa-class cores, per-core rate measured on dregg-forge):

| rank | design | cpu1 | cpu64 | T4 | H100 | B200 | B300 | TPU v5e [A] | $ / M records (best target) |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---|
| 1 | **c** packed binary | 4.52 ms | 57.9 us | 286 us | 69 us | 64 us | 59 us | 150 us | 0.01 (TPU [A]), 0.02 (cpu64) |
| (1) | c128 (knob) | 3.27 ms | 41.9 us | 110 us | 26 us | 24 us | 22 us | 63 us | 0.01 |
| (1) | cB (knob) | 2.08 ms | 26.7 us | 103 us | 24 us | 23 us | 21 us | 54 us | 0.01 |
| 2 | b Tower256 + tensor + BLAKE3 | - | - | 2.16 ms | 420 us | 347 us | 329 us | - | 0.21 (T4) |
| 3 | a today | 69.8 ms | 894 us | 5.33 ms | 1.27 ms | 1.18 ms | 1.10 ms | 2.76 ms | 0.28 (TPU [A]), 0.37 (cpu64) |
| 4 | d/e BabyBear | 1.32 s | 17.0 ms | 16.6 ms | 3.31 ms | 2.55 ms | 2.36 ms | 9.93 ms | 0.99 (TPU) |

Other columns of the same model (MODEL.md section 4), for (a) -> (c):
- **per-leaf recursion** (aggregate-recursive): 2.29 s -> 222 ms on one core; 10.5 ms -> 1.0 ms on an H100. It is
  37-50x a leaf in both designs: batching is worth more than any design change.
- **audit at 1%**: 0.7 ms -> 46 us per record on one core; 12.7 -> 0.7 us on an H100.
- **light-client verify** (one core): 28.6 ms -> 2.8 ms; verifier Keccak-f 53,263 -> ~5,200; proof 1.46 MB -> ~0.45 MB [A].
- **stream** (64 KiB windows, accumulated): 104 ms -> 8.4 ms per record on one core.

Sensitivity: (c) beats (a) by 5.4-48x on every target when the packed encode moves 4x or the PIOP constant moves 4x
either way (MODEL.md section 5). (b) beats (a) only on GPUs, by 2.5-3.5x, and only if the fused tensor kernel is
built; the unfused one measured 5-8x slower than the table on the T4 (MMA.md section 9).

## 3. Soundness and Lean carry

| | soundness at 100+ provable bits | what our Lean already carries [READ] | what is new |
|---|---|---|---|
| **a** | UD-100 at 148 q (rate 1/4); field term negligible at 2^256 | additive-FRI raw/succinct controllers with collision extraction; Tower256 coordinate arithmetic; cSHAKE equal to spec; RS MCA on the whole UD radius (bridges/arklib-ud); final-polynomial check | zerocheck/AIR layer for Tower256 traces; char-2 lookup; native prover + receipt codec (LEAF-PROVER-DECISION section 4) |
| **b** | as (a) | `gf2_dot_*`, `lazy_bilinear` (lane/mma-exact) | Tower256 instance of `lazy_bilinear`; a per-SKU measured `m` as the hardware premise; BLAKE3 spec + proved implementation; a ruling change |
| **c** | UD-100 at 148 q on the packed word (same proximity regime); ring switching adds a `k/|F|`-type term at 2^256 (negligible); packing changes **what** is committed, not the code | everything in (a), plus `Selvage/RingSwitching.lean` (Diamond-Posen compiler), `AdditiveBaseFold.lean` (LCH `novelPack` encoder, char-2 fold), `CosetNovelTransform.lean`, `MultilinearZeroTest.lean`, `BinaryLookup.lean` (Shout/Lasso read semantics, one-hot = chi vector), `SmallField.lean` (extension-degree security dial), `LigeritoInterleaved.lean` (interleaved metric) | (1) the subfield-twiddle domain: basis in T_4, twiddle closure (a computable lemma); (2) the systematic-subtree binding: `named_or_collision` for a subtree of the codeword tree; (3) ring switching instantiated at Tower256 / T_4 packing; and, owed by (a) too, zerocheck + lookup soundness at the leaf |
| c128 | sumcheck/zero-test terms become `N/2^128`; Codex: `16 * 2^19 / 2^128 = 2^-105` leaves little budget for FS and composition losses | `SmallField.securityBits` | a composed budget (CODEX.md section 6) |
| cB | as c128 | none for BLAKE3 | BLAKE3 in Lean; mixed-hash tree binding; ruling |
| **d/e** | BabyBear^4/^8 challenges fine; Brakedown distance needs more queries; Blaze-style RAA codes carry a 2^-27..2^-41 bad-code term (Codex, CODEX.md) | Selvage's prime-field FRI/AIR/LogUp* cone (BabyBear); `BabyBearExt4.lean` | a Keccak AIR's semantics, or a different store root (ruled out) |
| f | Ligerito's soundness bridge has named assumptions (Codex READ `LigeritoInterleaved.lean`) | the interleaved metric is proved | the rest of Ligerito's soundness |

**What decides the ranking more than any kernel:** (c)'s incremental Lean over (a) is three bounded statements,
because the Selvage tree already holds ring switching, the additive BaseFold encoder, the multilinear zero test
and binary lookup semantics. The zerocheck and lookup owed by both designs are the same work in either.

## 4. Outside the certificate pipeline (hypotheses 3 and 4)

- **Prime-field sumcheck is memory-bound everywhere (H3): confirmed from sources.** T4 measured 1.2-1.6x copy for
  INT8 limb inner products and 0.82-0.83 of copy for FP16 byte limbs (MMA.md section 9); OPTIMAL Rule 1. The levers
  are bytes and passes: fused rounds (one read per round for all d+1 evaluations and the fold), the fold folded into
  the next round's load, L2-resident tail rounds. A faster multiplier buys nothing. For (e) as the dense-arithmetic
  branch: keep BabyBear (KoalaBear is a null knob, PROOF-SYSTEM-SPACE section 5), BabyBear^8 challenges, INT8 limbs
  everywhere except B300 (FP16 byte limbs, ROTATION 2(a)).
- **Dark learning's 61-bit RNS (H4): half right.** On B300, FP16 byte digits beat INT8 by 8.7x (ROTATION 2(e)); on
  TPU the int8 MXU four-step NTT is the only route (no 64-bit in Pallas). But the larger lever on every GPU is
  splitting each 61-bit prime into ~30-bit primes on SIMT: 0.45-0.5x per 61 bits (OPTIMAL 2.4, SASS counts), and
  31-bit primes cut tensor limb products 4x per prime. And the step's real costs are elsewhere: the ZKPoPK prover is
  Python (417-606 s per batch, DARK-LEARNING-SCHEME-DECISION section 20) and the protocol moves 0.5-1.9 Gbit of proofs
  per step. Native code first, kernel format second. Codex flags a separate soundness item there: a degree-2
  sumcheck over 24 variables with one 61-bit challenge field is `48/2^61 = 2^-55.4` [Codex DERIVED, unchecked here];
  extension challenges or repetition are needed wherever that term applies.

## 5. Hypotheses, verdicts

| # | hypothesis | verdict |
|---|---|---|
| 1 | Encoding, not hashing, dominates; a dense-matmul code may beat additive NTT | **Half.** Encoding does dominate today's GPU prover (80%, measured) and still leads the packed one on the T4 (fused 0.074-0.14 ns/B against ~0.02-0.03 ns/B of leaf hashing, measured). But the remedy is not a dense-matmul code: a GF(2) radix-16 block costs 1,024 bit-MACs per symbol-layer against ~2.5 SIMT ops, which loses on T4 (b1) and B200 (FP4) [MODEL]; the unfused tensor Tower256 multiply measured 5-8x slower than tables. The remedy is fewer, smaller symbols (packing; GF(2^16) twiddles) and fewer passes (fusion). |
| 2 | Only store roots must be cSHAKE; internal commitments may use another hash | **True in principle, small in effect after batching.** BLAKE3 internal trees buy 1.0-1.6x per batched record and 2.7x on per-leaf recursion paths. Lattice/hash-free commitments lose (an Ajtai commitment of bits is ~1,024 MACs per bit: ~120 GB/s on an H100 at ~1,024 MACs per bit [A: kappa x d], against Keccak's ~400 GB/s, plus opening proofs and no Lean). Binary-friendly algebraic hashes add a cryptanalysis project. Not worth a ruling change before the packed prover exists. |
| 3 | Prime-field sumcheck is memory-bound; passes beat multipliers | **Confirmed** (section 4). |
| 4 | Dark-learning RNS maps better to FP16 bytes on B300 and int8 on TPU | **Half** (section 4): true per target, but 30-bit primes on SIMT and a native ZKPoPK are the bigger levers. |
