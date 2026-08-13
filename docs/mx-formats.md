# We picked the wrong format, not the wrong idea

> **Status since written: the central hypothesis was tested and holds.**
> **MXFP4 within-block exactness holds**, and it is what the live
> arithmetization is built on. ⚠ **NVFP4 preserves the exactness but destroys
> the power-of-two-scale shift argument** — so the "16-element NV variants"
> mentioned below are *not* interchangeable with MX for our purposes; our
> arithmetization is **MXFP4-specific**. `docs/VERDICTS.md` §5.

2026-08-11, written immediately after `PHASE0-RESULT.md`. **This is a hypothesis
with the same status my bf16 claim had this morning, and it must get the same
treatment before anyone believes it.**

## What Phase 0 actually refuted

Not "format choice doesn't matter." The harness says it in one line:

> **bf16 is NOT a block format — it carries a PER-ELEMENT exponent.**

The two columns it measured were:

| design | median speedup |
|---|---|
| **static shift** (shared exponent per block) | **2.29×**, range 1.51–3.30× |
| dynamic normalization (per-element exponent) | 1.42×, range 0.85–1.99× |

I wrote "block-float bf16" throughout the plan and never noticed those are
contradictory. Block float means a **shared** exponent across a block; bf16
carries **one exponent per element**. So every element needs its own
renormalization shift, the shift is data-dependent, and data-dependence is the
whole cost. Phase 0 correctly priced the design I actually specified, which was
not the design I thought I was specifying.

**The static column is not hypothetical. It is what you get if the format really
does share an exponent.**

## MX formats are exactly that, and they are a standard

OCP Microscaling (MX): a **block of 32 elements** with a **shared 8-bit
power-of-two scale (E8M0)** plus narrow per-element values. MXFP8, MXFP6, MXFP4,
**MXINT8**. NVIDIA Blackwell implements MXFP8/MXFP4 natively; there are 16-element
NV variants too.

That is a shared-block exponent by construction — the static-shift case, as a
published format the hardware already speaks.

## Why MXINT8 in particular looks right for *us*

Three things line up, and the third is the one I care about:

1. **The shift is static per block.** Phase 0's static column applies by
   construction rather than by assumption.
2. **The scale is a power of two.** Phase 0's ablation put that at +0.69× on its
   own — no `Quant(2^f·ε)` multiplier, rescaling is a shift. Note OpenLLM moved
   deliberately the *other* way, to a rational scale `s = a/b`, buying accuracy at
   roughly that cost.
3. **It stays bit-exact, so §5 survives intact.** MXINT8 elements are exact
   integers; the scale is a power of two; products of integers don't round; the
   accumulation is integer and therefore associative, so Freivalds/sumcheck still
   applies. **There is no per-element error window for Zamir's construction to
   steer.** This is the property that makes the whole soundness argument work,
   and unlike bf16-with-approximations it is not in tension with it.

## And it may fix the accuracy failure that motivated all of this

DeepProve measured Gemma 3 at **cosine similarity 0.2035** under 8-bit — the
number that made int8 look unusable for modern models. That was **per-tensor**
scaling. Outlier activations blow out a single tensor-wide scale; that is exactly
the failure mode MX exists to solve, with a scale per 32 elements.

An earlier lane noted (sourced, arXiv 2510.25602) that **MXINT8 beats MXFP8 on
accuracy *and* area/energy**.

So the shape of the bet changes: not "avoid quantization because it destroys
Gemma 3," but "**use the block-scaled quantization the hardware standardized,
which was designed to fix precisely that failure**" — and get static shifts and
power-of-two scales as a side effect.

## ⚠ The concession that reframes this note (ember, 2026-08-12)

**MXINT8 on an unmodified model is quantization.** It does not preserve the
served computation; you prove a *derivative* of the model. That silently
surrenders the property that made bf16 attractive in the first place — models
already ship in bf16, so proving the bf16 path is proving the unmodified model
with zero semantic gap. The 2.29× static column is real, but as stated above it
buys speed by reopening the "what did you actually attest?" question — the same
criticism we levelled at int8 pipelines.

The reconciliation worth testing (hypothesis, unverified): **target the model's
NATIVE serving format, whatever it is.** For older models that is bf16 (the
1.4× path — fine, soundness-first). For a growing frontier class the native
format is already a block format — gpt-oss reportedly ships MXFP4 weights;
DeepSeek-V3 trained in FP8; Blackwell serves MX natively. For those models the
block structure and static shifts come free AND zero-loss, because the block
computation IS the model. "Prove the shipped format exactly" is the principle;
MXINT8-as-conversion was a wrong turn off it. Needs a lane to verify which
models genuinely ship block-native and what their serving semantics pin down.

## Status — read this before repeating my mistake

**Unmeasured.** Everything above is inference from Phase 0's static column plus
the MX spec. The specific things that must be measured, not assumed:

- ~~Does the static-shift model actually apply end-to-end, or does block-boundary
  handling reintroduce dynamic shifts?~~ **MEASURED 2026-08-13, on real gpt-oss-20b
  weights** (10 scales tensors, 5 layers × both MoE projections, 124.4M scale
  bytes, 1.38M reduction rows, range-fetch integrity verified): per-row exponent
  spread is **p50=2, p90=2, p99=3, max=8**. **100% of rows fit a width-8
  alignment window; 99.92% fit width-4; 94.63% have spread ≤2.** Zero
  denormal/special bytes. So the cheap alignment path is not the common case —
  it is effectively the *only* case for gpt-oss's MXFP4 weights (all 78.9% of
  per-token linear FLOPs), and the wide accumulator is a one-in-a-million
  fallback. Script: `phase0/e8m0_spread.py`; results:
  `phase0/results_e8m0_spread.txt`. Caveats: weights only (activation-side
  spread is a runtime question and backend-dependent); 20b measured, 120b
  inferred-same (same scheme, same 90-block rows). **This is, per the verified
  zeros, the first MX-format-for-proving measurement in any literature.**
- Does MXINT8 recover Gemma 3's cosine similarity? DeepProve's Table 4 is
  per-tensor; nobody has published the MX row.
- What does a 32-element block do to accumulator width, given the
  26-bit tensor-core window and BabyBear's 31 bits?
- Are there constraint counts for MX anywhere? Almost certainly not — the
  earlier verified absence of "block floating point" × ZK covers "microscaling"
  and "shared exponent" too.

**Phase 0 cost a day and saved a quarter. Phase 0′ should cost the same day.**

## RESOLVED by the native-format census (2026-08-12, byte-verified)

The census (HF safetensors headers + config.json + decoded tensor bytes)
settles this note's hypothesis, with one correction:

**MXINT8 was the wrong name; MXFP4 is the right one — for this note's own
reasons.** MXINT8 has ZERO model releases. MXFP4 is what actually ships, and it
has the same properties this note wanted: E2M1 values are multiples of ½, so a
k=32 block dot product is an exact ≤13-bit integer computation — verified over
20,000 random blocks under two summation orders against exact rationals, zero
deviations. Exact elements, power-of-two E8M0 scales, static shifts, no
per-element window for Zamir. And because the checkpoint IS the evaluated
model, zero semantic gap.

**Tier 1 — block-native, power-of-two scales, no BF16 original exists:**
- **⚠ **DeepSeek-V4 DOES NOT EXIST** (HTTP 404 with credentials, verified by the registry lane). DeepSeek-V4-Flash/Pro** — the strongest case in existence: every weight
  power-of-two block-scaled (experts FP4-E2M1 block-32 E8M0; the rest FP8
  E4M3 at 128×128 E8M0). There is no unscaled path to defer to.
- **gpt-oss-120b/20b** — MXFP4 block-32 E8M0 on the MoE experts = 98.1% of
  weights, 78.9% of per-token linear FLOPs; attention stays BF16. The card:
  "All evals were performed with the same MXFP4 quantization" — the MXFP4
  checkpoint is the ground truth; no BF16 original.
- **Kimi-K3 (2.8T)** — same shape, largest open model ever.
- DeepSeek-V3.1/V3.2 — 128×128 tiles with byte-verified power-of-two scales
  (2688/2688; V3/R1's older scales are NOT powers of two, 0/896).

Tier 3 (nothing to exploit, BF16/per-tensor): Gemma 4 — the model Attestable
proves via int8 — plus Qwen, GLM-5.2, Llama 4, Mistral's FP8-per-tensor line.

**The load-bearing caveat: "prove the shipped format" pins the WEIGHTS, not
the COMPUTATION.** Three reasons, none fixable by format choice: (i) one
gpt-oss checkpoint runs W4A16/W4A8/W4A4 across vLLM's TWELVE MoE backends —
the canonical fallback is W4A16 with BF16 activations; (ii) OCP MX v1.0 §6.1,
verbatim: "The internal precision of the dot product and order of operations
is implementation-defined"; (iii) cross-block FP32 accumulation over 90–128
blocks with differing exponents is order-dependent even when each block is
exact. **So the provable statement is "gpt-oss under backend X on SM100", not
"gpt-oss" — pinning a backend is part of the statement.** The within-block
exactness result confines the nondeterminism to the cross-block sum, which is
exactly where an order-independent exact accumulator (our §(b) from the first
bf16 note) earns its keep.

Spec artifacts in ~/paperbin: `ocp-microscaling-mx-v1.0-spec.pdf` (primary),
`numeric-format-catalog-bitexact-conformance-2606.09686.pdf` (conformance
vectors for FP8/BF16/MXFP4 — a ready-made differential oracle), and
`ozaki-scheme-fp4-tensorcore-base13-limbs-2608.06812.pdf` (exact FP64 GEMM on
FP4 tensor cores via limb decomposition — the bit-exact-float-as-integer-limbs
technique, developed HPC-side, unaware of ZK; most transplantable single idea
the census found).
