# The zkML landscape — and why the open position is vacant rather than crowded

2026-08-11. Lane report. Artifacts in `~/paperbin/`, code in `~/src/`
(`ceno`, `expander`, `deep-prove`).

## 1. The finding that reframes everything: "open" zkML mostly isn't

License blobs checked at HEAD, 2026-08-12:

- **DeepProve** (Lagrange) — `license: NOASSERTION`, a custom binding "Lagrange
  License." 3.4k stars. **The strongest LLM proving result in existence, and you
  may not use it.**
- **JSTprove** (Inference Labs) — verbatim: *"**NO USE RIGHTS ARE GRANTED BY
  THIS LICENSE.** Any operational use including but not limited to: Execution of
  the software … requires express written permission."* Readable, not runnable.
- **ezkl** — **no LICENSE file, no COPYING, no `license` field in Cargo.toml,
  only a `cla.md`.** Universally described as open source — including by
  Attestable, who benchmark against it.

Genuinely OSI-licensed and relevant:

- **Ceno (Scroll) — Apache-2.0, pushed 2026-08-12.** Goldilocks + BaseFold +
  sumcheck/GKR. **This is the engine DeepProve is built on.** The fastest
  published open LLM prover sits on an Apache-2.0 foundation while being itself
  unusable. Building on Ceno legally reproduces DeepProve's substrate.
- **Expander (Polyhedra) — AGPL-3.0, active.** GKR over M31, Orion (PQ) or KZG,
  zkPyTorch compiler, zkCUDA GPU frontend. Copyleft but usable.
- **Jolt / Jolt Atlas (a16z) — Apache-2.0/MIT, daily commits.** Most genuinely
  open culture; nanoGPT scale. Their paper's §6.2 "GPT-2 (125M)" is *literally
  empty* — heading, one sentence, no numbers.
- **ZKTorch (Kang, UIUC) — Apache-2.0.** Universal ONNX compiler, honest
  academic group; 0.09 tokens/min on GPT-J, quiet since 2025-11.

**So the "open verifiable ML" position is vacant, not contested.** That is a
much better strategic situation than I assumed this morning.

## 2. The real open state of the art is far smaller than the discourse implies

| system | model | hardware | tok/s | PQ? | usable? |
|---|---|---|---|---|---|
| Attestable (self-reported) | Gemma 4 31B | 1× H100 | 53 | yes | no code |
| **DeepProve** (best open result) | Gemma 3 **270M** | 24-core CPU | **1.45** | yes | ✗ license |
| DeepProve | GPT-2 **124M** | 16-core CPU | 2.92 | yes | ✗ |
| zkLLM (CCS'24) | LLaMA-2-13B | A100 | ~2.55 equiv* | **no** | archived, attention only |
| zkGPT (USENIX'25) | GPT-2 124M | Xeon | 0.046 | **no** | unreleased |
| zkPyTorch/Expander | Llama-3 8B | 1 CPU core | 0.0067 | configurable | ✓ AGPL |
| ZKTorch | GPT-J 6B | 32-core, **4 TB RAM** | 0.0015 | no | ✓ Apache |

\* zkLLM's "13B in under 15 min" is **one forward pass over 2048 tokens**, not
2048 decode steps.

**The strongest open end-to-end LLM proving result is on a quarter-billion
parameter model**, and DeepProve's own paper says >3B "would likely require over
a terabyte of RAM."

Attestable's "×50,000 faster than ezkl" uses a **2024-01-28 blog benchmark on
linear regression and random forests**. ezkl has never published an LLM number.
That comparison is a straw man; the honest comparison is against DeepProve and
zkLLM, where they are ahead by ~10–140× hardware-normalized — large, but an
**engineering** gap, not an algorithmic one.

## 3. The roofline argument — why their number is plausible, and available to anyone

*This derivation is the lane's, not from any source, and I have not
independently checked the arithmetic.*

An H100 SXM at 3.35 TB/s over ~31 GB of int8 weights caps **batch-1 decode at
~108 tok/s** before KV traffic. Attestable's 53 tok/s is ~50% of the pure
inference roofline — proving costs about one inference-time.

Why that is reachable: batch-1 decode is **memory**-bound. 62 GFLOP/token
against ~2000 TOPS of int8 capacity is **under 1% ALU utilization**. Sumcheck
proving of a matvec costs O(#weights) small-field operations — the same order as
the memory traffic already being paid. **A small-field sumcheck prover hides
inside the memory-bound bubble.**

That is the whole trick, and nothing about it is proprietary.

## 4. The cost breakdown that makes our bf16 finding strategically central

DeepProve measured, on the open side: **>50% of prover time in activations /
Softmax / requantization, with requantization alone at 27%.**

Corroborating shape from Attestable's own numbers *(lane's inference)*: their
batch scaling is backwards — 4× batch buys only 1.45× aggregate throughput
(a 2.75× per-sequence regression) where ordinary inference gains ~4×. That says
the prover dominates and its cost is roughly linear in tokens, i.e. witness
commitment and non-linear ops rather than matmuls. Contexts differ (16K vs 4K),
so this is suggestive rather than conclusive.

**This is the connection worth making.** *My inference, not sourced:*

- **Requantization exists only because of quantization.** A bf16 path has no
  quantize/dequantize step, so that 27% is not reduced — it is *absent*.
- **Activations and Softmax are exactly what a 2^16 bf16 table makes one exact
  lookup**, with no approximation error and no Taylor expansion.

So the dominant measured cost in open zkML is precisely the cost our format
choice removes. If that holds, it is a stronger argument than any throughput
claim: not "we optimized the expensive part" but "we chose a representation in
which the expensive part does not occur." **Unverified — this needs to be
measured, and it is the first thing worth measuring.**

## 5. Post-quantum is table stakes, not a differentiator

DeepProve already ships and measures a **BaseFold-over-Goldilocks** config which
their paper calls "plausible post-quantum secure" — and it is the *lower memory*
one (96 GB vs 147 GB). Expander offers Orion. Jolt is hash-based.

Not PQ: zkLLM (BLS12-381), zkGPT (BN254), ZKTorch (KZG+Mira), ezkl (halo2-KZG),
NanoZK (Halo2 IPA).

We should stop treating "post-quantum" as our edge. It is a hygiene property
several projects already have.

## 6. GKR/sumcheck has won

Every serious 2024–2026 LLM system is sumcheck/GKR: zkLLM, zkGPT, zkPyTorch,
DeepProve, Jolt Atlas. Structural reason: no FFT, and you commit only layer
inputs/outputs rather than the whole trace. zkGPT measures the consequence —
**185× over halo2-based ZKML**, which needed >1 hour per GPT-2 token.

General zkVMs are the wrong tool: RISC Zero is 65.9× slower than ezkl on toy
models, and no LLM-scale zkVM inference proof has been published.

**This bears on our own architecture.** We have a Plonky3 AIR-shaped prover. The
field has converged on GKR/sumcheck for this workload for a structural reason.
That should be weighed honestly rather than assumed away.

## 7. An unclosed attack that is a genuine open-project differentiator

**Hollow-LLM, arXiv 2607.28884 (Jul 2026)** — `~/paperbin/hollow-llm-attack.pdf`.

A ZK proof of inference certifies an NP relation over *committed private
weights*. It does **not** bind computational **effort**. A provider can embed
"ghost weights" whose algebraic structure collapses, keep the declared
architecture and parameter count, emit entirely valid proofs, and serve at
small-model cost.

Attestable's framing — *"a digital signature created by the computation
itself"* — does not address this, and neither does anyone else's deployment.
**Closing it needs a public weight-commitment registry or a proof-of-effort
binding, and an open project can do that where a closed one structurally
cannot** (the whole point is that the commitment must be publicly checkable
against published weights).

That may be the most defensible thing on this list.

## 8. Adjacent non-ZK competition — the "good enough" answer to watch

- **H100/Blackwell confidential computing** — ~0% overhead, hardware trust root.
  This is what most buyers will actually use.
- **TensorCommitments** (arXiv 2602.12630) — 0.97% prover overhead on
  LLaMA-2-13B, but **96.02% attack *detection accuracy***. Statistical, not
  sound. Must not be benchmarked against ZK on equal footing, and will be.
- Verde/Gensyn refereed delegation; EigenAI; SVIP; VeriLLM; opML.

## 9. Skepticism to keep about the Attestable numbers

Not because they are dishonest — they say "alpha" themselves — but because
every number is a self-report with no paper, no code, and no third-party
reproduction. Also: the benchmark table and eval charts are **images**, so the
figures are not in the page text; "100 bits of security" names no proof system,
field, hash, or soundness analysis (for FRI-family systems conjectured vs
provable routinely differs by 40–80 bits); and what is proven is the *quantized
derivative* — unless the commitment to W is publicly pinned to a published
quantization of published weights, the statement does not say "Gemma 4 31B ran."
