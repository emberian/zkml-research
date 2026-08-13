# "Append-dominant, write-once-shaped" — sound as a spec, unsound as serving

2026-08-13. Peer lane, ground-truthed against a local vLLM checkout at a
pinned SHA with file:line cites. This corrects a claim I used in `SYSTEM.md`
as a *load-bearing* argument (that our statement is cheap because inference
memory is the cheap case).

## The verdict, which is precise and mostly recoverable

**Sound as a specification of the computation. Unsound as a description of
serving.** Three things our notes fused must be split:

- **(a) Is the IDEAL decode loop an append-only fold?** YES for
  full-attention layers: `KV_t = KV_{t−1} ++ (k_t,v_t)`. Genuine monotone
  accumulator, legitimate IVC step function. Nothing below touches this.
- **(b) Is the DEPLOYED ENGINE's KV state append-only?** **NO, on six
  independent counts.**
- **(c) Does (a) still buy anything?** **YES — but only if you commit to the
  LOGICAL ACCEPTED TOKEN SEQUENCE, never to cache writes.**

## The six counts (all read at source in vLLM @ 8cd174fa)

1. **Speculative-decode rollback is an in-place overwrite of committed KV,
   on the common path.** On rejection `num_computed_tokens` moves *backwards*
   and the next step's slot mapping resolves to **the same physical slots the
   rejected drafts wrote** — no free, no CoW, no truncation event to hook.
   Worse than a deletion for accumulator modeling: a deletion you can at
   least witness. At throughput-optimal K=6, **~62% of drafted tokens are
   rejected** (single study — direction certain, number workload-specific).
2. **~75% of the 2026 frontier is not append-only at all.** Qwen3-Next/3.5,
   Nemotron-H (92% Mamba-2), Granite 4, Jamba, Zamba2 use ~3:1 linear/SSM to
   attention. vLLM's own accounting proves the mechanism: `MambaSpec` returns
   **one page for the entire sequence, independent of length** — a fixed-size
   register overwritten every step, the exact inverse of an append-only log.
3. **CacheBlend deliberately rewrites stored KV at interior positions** to
   repair cross-attention for stitched RAG chunks — and it **ships in
   LMCache, a first-class vLLM connector**. Only "same-quality," not
   same-value. The one exception that is *not* semantically transparent.
4. **Sliding-window layers delete mid-request, architecturally, by default**
   — and ⚑ **gpt-oss, our own Tier-1 target, is 128-token banded**; Gemma 4
   likewise. vLLM's own comment says full attention is the *special case*.
5. **Preemption wipes an in-flight request's entire KV** and is **not
   configurable off** — it is how the engine survives memory pressure.
6. **KV bytes are lossily quantized at write time** (FP8/INT8/NVFP4 modes on
   every AttentionSpec). The committed leaf is not the value the model
   computed.

Also: physical slots recycle across unrelated requests, and KV crosses
RDMA/TCP to SSD tiers with LRU/ARC eviction. **"Write-once" is a property of
the logical (request, position) slot only; the physical KV tensor is a
mutable arena.**

**Narrowing in our favour:** token-level attention-score eviction (H2O,
SnapKV, PyramidKV) is **research, not in vLLM upstream** — within a live
request there is no attention-based eviction.

## The fix, and it is clean

**Fold over the ACCEPTED TOKEN SEQUENCE and the per-layer state transition —
never over cache writes.** Every non-monotone op except CacheBlend and lossy
quantization is *supposed* to be semantically transparent: speculative
decoding is **provably lossless** (accepted output distribution identical to
plain sampling), preemption+recompute is exact, prefix-cache hits are exact.
So a proof over the accepted-token fold still proves the right thing — you
simply cannot claim it is a proof about the engine's memory.

Restate the ledger item as: **"append-only over accepted tokens for
full-attention layers; fixed-size recurrent fold for linear/SSM layers;
bounded-window fold for sliding-window layers."**

Costs, per exception: spec-decode **free if you fold over accepted tokens,
fatal if you fold over cache writes** (the whole ballgame); preemption,
chunked prefill, MLA free; prefix sharing free **but the prover must
recompute or re-attest the shared prefix — it cannot import a peer's KV on
trust**; sliding-window is arguably a *gift* (a bounded-window fold) but a
different fold, and you must prove eviction matched the window;
**FP8/NVFP4 KV is a real spec fork** — commit pre- or post-quantization;
**CacheBlend genuinely breaks it — exclude it.**

## ⚑ The escalation

**"Full attention only" is realistic today and not realistic long-term.**
DeepSeek-V3, Kimi K2, Llama-class qualify now — but the 2026 trajectory
(Qwen3.5, Nemotron 3, Granite 4, Gemma 4) is toward 3:1 hybrid, and a design
whose core memory argument works only on full attention **gets narrower every
quarter.** Good news: a fixed-size overwritten SSM state is the *easiest*
IVC step function — it just isn't an accumulator (no Merkle structure, no
sublinear opening). **If the accumulator is load-bearing, price the hybrid
case now.**

## And a narrowing of our own novelty claim

**ePrint 2024/480 ("Folding-based zkLLM") contains ZERO occurrences of
"cache" and ZERO of "attention"** — it models the LLM as a **RAM machine**
with per-opcode constraint circuits. So "KV-cache-as-accumulator is unbuilt"
survives, but **"folding × the decode loop is virgin ground" does not**: the
field's one prior answer went to general random-access memory instead. That
is evidence the accumulator framing is **a choice we would be making, not the
obvious one** — and the note should cite 2024/480 saying so.

One check worth redoing: a blog claims SGLang ships H2O/SnapKV eviction
upstream; the lane believes it false (contradicted by their issue tracker)
but ran out of budget before confirming at the repo.
