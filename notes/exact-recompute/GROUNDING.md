# Initiative 8, redirected: the audit theorem over our own bit-exact recompute of gpt-oss-20b

2026-11-06. Ember's redirect: FlashProve is one comparison point, not the substrate. The bar now is
the audit theorem (`minidregg/Selvage/AuditSampling.lean`, instantiated in
`Selvage/AuditFlashProve.lean`) over a recompute of a real model that agrees bit for bit across
backends and silicon, so a sampled request is checked with zero tolerance. This file is written
before building.

## What exists

- **The weights, committed.** `registry/manifests/openai__gpt-oss-20b.6cee5e81ee83.full.json`: the
  full-mode commitment to `openai/gpt-oss-20b` at revision `6cee5e81ee83917806bbde320786a8fb61efebee`
  (commitment `3218eb92…db61f`), with per-shard `file_hash` and per-tensor SHA-256. Three shards,
  13.76 GB. The Mac download (`~/models/gpt-oss-20b/6cee5e81/`) is checked against those hashes,
  not trusted from Hugging Face.
- **The arithmetic facts.** `docs/mx-formats.md` and VERDICTS §5: gpt-oss's MoE experts (98.1% of
  weights, 78.9% of per-token linear FLOPs) are MXFP4 (E2M1 values, block 32, E8M0 power-of-two
  scales). E2M1 values are multiples of ½, so with an MXFP4 activation a block-32 dot product is
  an exact ≤ 13-bit integer computation (20,000 random blocks, two orders, zero deviations).
  Per-row exponent spread of the real weights: p50 2, p99 3, max 8 (`phase0/e8m0_spread.py`). The
  census's load-bearing caveat: the shipped format pins the WEIGHTS, not the COMPUTATION. vLLM has
  twelve MoE backends (W4A16, W4A8, W4A4); OCP MX v1.0 §6.1 makes the dot product's internal
  precision and order implementation-defined; the FP32 cross-block sum is order-dependent.
- **The integer-model template.** FlashProve's `docs/model.md` (Apache-2.0) defines an integer
  Llama 4 Maverick: integer weights, fixed-point activations with fitted power-of-two shifts,
  `rq` rounding, an integer RMS norm (`isqrt`), integer RoPE, softmax and SiLU by public tables
  built from float64 with stated rounding, and digests of the tables. FlashProve also reports a vLLM
  plug-in that computes their integer model exactly (48 of 48 short replies). This is the prior art
  for "an integer program is the model". We follow its recipes where gpt-oss has the same op, cite
  them, and add what gpt-oss needs (attention sinks, alternating 128-token sliding window, YaRN
  RoPE, top-4 routing with a softmax over the chosen four, the clamped SwiGLU with α = 1.702 and
  `up + 1`, biases).
- **The auditor.** `breadstuffs/audit-flashprove`: MMR of request records, requester
  countersignature, drand seen + 2 beacon, staging, fail-closed decision compiled from Lean,
  receipts, offline recheck. Its checker is `cp_verify`; the generalization replaces the checker
  with an exact recompute and keeps everything else.
- **The steering prior art.** Zamir (arXiv 2602.15756), Theorem 1: an equivalent network with a
  δ-consistent transcript for every target; any per-element tolerance window is steerable
  (`notes/archive/PLAN.md`). Tolerance-based inference checks (TOPLOC-style locality hashes,
  DiFR-style thresholds) grant such a window. No result here is claimed as new without that list.
- **Kaggle.** `swarm/kaggle.md`: account `emberian64`, `uvx --from kaggle --with six kaggle`, one ID
  per experiment, watchdogs, `/kaggle/working` small, one TPU session at a time, a run ledger.

## Where the bar needs restating

**"Reproduce a pinned backend bit-exactly" is only reachable for a backend whose math is pinned.**
A float backend (the official PyTorch reference, vLLM's kernels) does its block sums and
transcendental functions in an order and precision that its library chooses, so reproducing it
means reproducing that library's blocking on each machine. It is fragile, and no audit can rest on
it. The bar I set: **the pinned backend is an integer gpt-oss-20b (`gptoss-int v0`), specified in a
document as FlashProve's is.** Its MXFP4 expert weights are the checkpoint's own integers, and
every activation is a fixed-point integer. Every sum is an exact integer sum, so any order gives the
same result. Every nonlinearity is a public table built once in float64 and pinned by digest.
Bit-exactness is then a property of the spec, and what we measure is three independent
implementations agreeing on real weights and real requests: a NumPy int64 reference on the Mac, a
JAX program that does the block-32 dots on TPU v5e's INT8 MXU with int32 accumulation, and the same
JAX program on a T4. The float backends are measured for **fidelity only**: how often the integer
model's greedy token equals the float reference's. That number is reported and never hidden. The
integer model is a derivative of the served float computation, as FlashProve's is.

## Open questions that are measured first, not assumed

1. **Attention and router weights are BF16, not MXFP4.** Exactly, they are dyadic rationals with
   per-element exponents. Census: per-row exponent spread of every BF16 matrix. If it fits an int32
   significand window, they enter exactly. Otherwise they are re-quantized FlashProve-style, and
   that is stated.
2. **Activation width.** FlashProve clamps to 12 bits. gpt-oss's fidelity at 12, 14 and 16 bits is
   measured against the float reference before a width is fixed.
3. **TPU INT8 MXU exactness.** int8 × int8 → int32 must be exact on v5e under XLA, with no bf16
   path taken silently: asserted per run with `preferred_element_type=int32` and a known-answer
   block.

## Lean policy for this work (ember, 2026-11-06)

General theorems (the audit composition, fail-closedness, the integer primitives' laws) stay
kernel-proved. Facts about concrete data (weights, recompute outputs, digests, receipts, cp_verify
transcripts) are checked by compiled evaluation (`#guard`, an exe, or `native_decide` where a
theorem needs one, with its axioms pinned), never by kernel `decide`/`rfl` through encoders or
hashes. A verified-kernel rerun is a later phase.

## Plan and gates

- G0: weights downloaded and hash-checked against the registry.
- G1: `gptoss-int v0` spec for one layer. NumPy reference and JAX (CPU) agree bit for bit on layer
  0 for a real prompt. **First bit-exact match; report here.**
- G2: the same JAX program on Kaggle T4, then TPU v5e (serialized, watchdog, ledger), bit-identical
  to the Mac's digest of every intermediate.
- G3: the whole 24-layer model, plus greedy-token fidelity against the float reference on a
  request set.
- G4: the auditor generalized: the checker is "recompute the sampled request and compare the
  committed output tokens exactly". Fail-closed as before. The Lean `Round` is unchanged, and
  δchk = 0 for a deterministic exact recompute, up to the transport hypothesis that the
  implementation computes the spec.
- G5: the attack. On real weights, positions where the top-2 logits of the float reference sit
  within a tolerance checker's threshold. A steered output (the second token, or activations
  perturbed within the per-element window) is accepted by a TOPLOC/DiFR-style threshold and refused
  by the exact recompute. Counts.
- Readiness rule (ember): all tuning on the Mac (NumPy, JAX CPU) and Kaggle T4/TPU. An H100 on
  vast or latitude.sh is requested only with a script that does its whole measurement in one
  bounded hour.

## Register row

| 8 | Audit theorem over a bit-exact recompute of gpt-oss-20b (FlashProve kept as a comparison point) | init-8 lane | zkml-research, minidregg, breadstuffs | L1 (FlashProve instance L2-L3) | integer gpt-oss-20b spec reproduced bit-exactly by NumPy, JAX-TPU (INT8 MXU), JAX-T4; auditor recomputes sampled requests fail-closed; steered output accepted by a tolerance checker and refused by exact recompute, on real weights | G1 first bit-exact layer | 2026-11-06 |
