# ML-systems sweep: four more refutations, one new design constraint, one gift

2026-08-13. The lane that exists because our corpus is crypto-shaped. It
refuted four more of our claims and found something that changes the MoE spec.

## ⚑ THE DESIGN CONSTRAINT (new, hard, and our spec does not carry it)

**Publishing routing decisions leaks the prompt.** *Expert Selections In MoE
Models Reveal (Almost) As Much As Text* (Nuriyev & Kulp, MBZUAI/RAND+OSU,
ICLR 2026 workshop, 2602.04105): a sequence decoder recovers **91.2% of
tokens top-1, 94.8% top-10 from expert selections alone**; added noise
*"reduces but does not eliminate"* it.

**Therefore router binding must be ZERO-KNOWLEDGE over `topk_ids`, not a
public commitment opening.** Our MoE spec's statement variants all assume the
selection can be committed and opened. That is a privacy break for any
deployment where the input is sensitive. Rewrite the spec's statement layer
before anything is built on it.

## ⚑ THE GIFT (also from the same sweep)

**DeepSeek-V4 uses HASH ROUTING in its first several blocks** — expert
selection is *"determined according to a predefined hash function with regard
to the input token ID."* For those layers selection is a **public
deterministic function of the token id**: no float, no ties, **binding is
free, and there is nothing to leak.** A structural gift that the frontier
handed us while we were writing the hard version.
(Also from V4: routing affinity moved Sigmoid → **Sqrt(Softplus)**, so our
V3 instance does not carry; and there is a **second top-k inside attention**
— router binding is not the only selection that needs binding. Sparsity
improved to 32.7× on V4-Pro.)

## Four more refutations

1. **"The first MX-format-for-proving measurement in any literature" — the
   STATISTIC is published, and the paper is in ~/paperbin.** arXiv 2608.03867
   (Brown/Michigan/**Google**) Fig. 3 is a CDF of per-block exponent range at
   block size 32 across four models — *"over 90% of output channels span a
   range of 3 or less and none exceeds 11."* Ours: p50=2/p90=2/p99=3/max=8.
   Same statistic, different purpose (they reclaim spare exponent bits as
   metadata). **And they have the activation-side number we listed as
   unmeasured**: an online per-token bias keeps *">99.99% of blocks within
   range,"* worst clamped tail 0.0086%. Narrow to "first *for proving*" and
   cite them. (Their Algorithm 1 also specifies *"arg max returns the lowest
   index on ties"* — a hardware paper with the tie discipline vLLM lacks.)
2. **"A public weight-and-architecture registry is an open position" —
   REFUTED at four layers.** Apple PCC (shipped append-only Merkle log that
   *does* bind model cryptexes into attestation), Berkeley 2504.04715 App. B,
   **Attestable Audits (2506.23706) — already in our own paperbin**, OpenSSF
   Model Signing v1.0 + Rekor, Project Oak. **What survives**: none binds
   *architecture*, none binds *which model is active at serving time*, none
   is third-party-operated with a public opening. ⚑ **And PCC has a
   Hollow-LLM-shaped hole at exactly our layer**: the *set* of loadable
   models is attested; `ModelSwitchingProperty` is *"not part of the node's
   attested state."* Plus their verifier ships a **fail-open** flag.
3. **Proof-aware QAT — refuted independently a second time** (PoT-QAT
   2601.02298; IBM HE-friendly training 2111.03362; **DeepSeek-V4 does FP4
   QAT at 1.6T scale**).
4. **"Nobody sequentially audits an LLM service" — refuted.** MPI-SWS
   2510.05181 builds an **e-value/martingale auditor** with guaranteed
   detection and bounded false-flag rate, detecting an unfaithful provider in
   **<70 outputs**, claiming the first use of e-values here. Our
   q-composition and machine-checking survive; the framing does not.

## Two corrections to our own numbers

- **Our tie-probability model is wrong by 12–30×.** `P ≈ n/2^b` is a
  fixed-point-over-full-range model; for floating-point scores the criterion
  is `ulp(score)/gap`. Measured (i.i.d. model): gpt-oss n=128 raw logits
  **3.9%** tie rate, not "dominant." **BUT** DeepSeek-V3's actual
  `sigmoid` scoring **saturates in bf16** (ulp at 1.0 is 2^-8), giving
  **24.7% at σ=1 and 98.4% at σ=4**. So the conclusion survives with a
  mechanism change: **ties are a live attack because sigmoid saturates, not
  because of step-vs-gap.** Replace "ties dominate" with the number and the
  reason.
- **MXFP4 is losing the accuracy argument to NVFP4** (five studies + NVIDIA
  pretraining in it). ⚑ **NVFP4 preserves within-block exactness but its
  scale is E4M3 with a per-tensor FP32 second level — so "rescaling is a
  shift" and our cheap width-8 alignment window DO NOT TRANSFER.** Our
  arithmetization is MXFP4-specific; say so.

## Effort-binding: say what we actually do

**Proof-of-Learning is broken and has been for five years** (Papernot et al.,
EuroS&P 2023: *"one cannot develop a provably robust PoL verification
mechanism without further understanding of optimization in deep learning"*).
**If our answer to Hollow-LLM is a registry, we bind IDENTITY and sidestep
EFFORT — say that plainly rather than claiming the effort gap is closed.**

## The TEE argument just got much stronger for us

**GPU-TEE attestation is forgeable for $50–$1000, published, unpatched.**
TEE.fail (S&P 2026) extracts the CPU provisioning key with a DDR5 interposer
and — because NVIDIA CC *"relies entirely on the CVM for trust"* — **runs GPU
workloads outside TEE protection while passing NVIDIA CC attestation**.
Battering RAM ($50 DDR4) *"breaks SEV's attestation on fully patched
systems."* WireTap forges SGX quotes that verify under Intel's official QVL.
Physical attacks are explicitly out of scope for AMD and Intel; NVIDIA's
policy binds driver+VBIOS RIMs only — no claim names an application, kernel,
container, model, or weights; H100 HBM is not encrypted. And honest perf is
**TTFT +22–28%, throughput −18–21%** full-stack, not the vendor's 5–7%.

## Determinism: it shipped, and the price is the batching you give up

`VLLM_BATCH_INVARIANT` is real (1,021-line kernel module, **and a negative
control test that fails if everything matches**). Cost measurements only look
contradictory: **24–56% throughput** on a continuous-batching engine (LLM-42,
MSR+UW) vs **95–98% of cuBLAS** on an already-atomics-free single-stream
quantized server. **The price of determinism is the price of the dynamic
batching you give up.** Unaddressed by the flag: prefix caching (default-on),
EPLB, **and ties**. ⚠ **EPLB makes the executing expert a function of batch
position** (`replica_idx = (token_idx * 2654435769) % replica_count`) with no
batch-invariance check anywhere in its path.

**And Microsoft already answered the cross-platform question in the
negative**: RepDL (2510.09180, *in our paperbin*) achieves bitwise
reproducibility — **float32 only**, stating low precision is *"non-standard
and hardware-specific… We hope [it] will be standardized in the future."*
Our backend-pinning caveat is independently confirmed by the people who built
the reproducibility library.

## The claims still to re-check with an ML-side instrument

Highest risk first: **"verified table contents unclaimed"** (the
correctly-rounded-math-library community publishes proved-correct table
generation — Lim & Nagarakatte PLDI'21); "streaming prover exists in zero
systems" (the offloading literature is enormous — the *prover* claim is
probably fine, the phrasing invites refutation); "co-scheduled fusion"
(MLSys/ASPLOS publish kernel co-scheduling constantly — query in their
words); "LoRA inference-side proving" (unswept).

## The cheapest decisive experiment named by the lane

**Dump real router logits.** Every tie number above is modeled under i.i.d.
Gaussian logits and the sigmoid case is highly scale-sensitive. The router is
a tiny linear layer and gpt-oss/DeepSeek weights are public — this converts
the whole table from a model into a measurement. **Do it before quoting any
of these figures.**
