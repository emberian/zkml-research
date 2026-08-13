# We picked the wrong format, not the wrong idea

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

- Does the static-shift model actually apply to MXINT8 end-to-end, or does the
  block-boundary handling (crossing blocks in a dot product, converting between
  block scales between layers) reintroduce dynamic shifts? **This is the exact
  place my bf16 reasoning failed, and it is the first thing to check.**
- Does MXINT8 recover Gemma 3's cosine similarity? DeepProve's Table 4 is
  per-tensor; nobody has published the MX row.
- What does a 32-element block do to accumulator width, given the
  26-bit tensor-core window and BabyBear's 31 bits?
- Are there constraint counts for MX anywhere? Almost certainly not — the
  earlier verified absence of "block floating point" × ZK covers "microscaling"
  and "shared exponent" too.

**Phase 0 cost a day and saved a quarter. Phase 0′ should cost the same day.**
