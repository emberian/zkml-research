# bf16 is the ZK-friendly float — two verified facts and what they buy

Status: design note, 2026-08-11. The two numeric facts below were computed
here; nothing else in this note is sourced yet. Research lanes are still out and
their findings will be merged and marked.

## Where this starts

Attestable published the first production-scale numbers for proving LLM
inference (Gemma 4 31B, one H100, 53 tok/s at batch-1 16K, 4.35–7.92 MiB
proofs, 157–648 ms verification, hash-based and post-quantum). That is real
work and it made the design space concrete — before it, "zkML for frontier
models" was a slogan with a 1M-parameter CPU benchmark behind it.

They also stated their own limitations plainly: 16K context, and **all matmuls
quantized to int8** with non-linear ops kept in float. They say they expect to
lift both.

This note asks a narrower question: **is the int8 step necessary at all?** Not
as a criticism of a sensible engineering choice, but because if a different
float format removes the need for it, that is worth knowing publicly. The
answer appears to be that bf16 — the format ML hardware already speaks — is
unusually well-suited to arithmetization, for two reasons that are easy to
check and easy to miss.

## Fact 1 — every unary function on bf16 is an exact 2^16 table

bf16 is 1 sign + 8 exponent + 7 mantissa = **16 bits**, so there are exactly
`65_536` bf16 values. The complete graph of any unary function

```
{ (x, f(x)) : x ∈ bf16 }
```

therefore has 65_536 rows. For `exp`, `GELU`, `SiLU`, `tanh`, `rsqrt`, `1/x`,
`log` — all of them — the *entire function* fits in a lookup table smaller than
range-check tables already used routinely.

This is not an approximation. There is no spline, no piecewise polynomial, no
Chebyshev fit, and **no approximation-error term to carry through the
analysis**. A LogUp lookup against that table proves `y = f(x)` exactly, at
whatever rounding semantics the table is built with.

The table can be typed `bf16 -> fp32`: still 65_536 rows, ~256 KiB, and the
transcendental is delivered at full fp32 precision. Softmax's `exp` need not
lose anything.

One table is shared by every lookup in a proof, so its cost amortises to nothing
against the millions of activations in a transformer layer.

## Fact 2 — bf16 × bf16 → fp32 is EXACT

A bf16 significand is 8 bits (7 stored + 1 implicit). The product of two 8-bit
significands is at most `255 × 255 = 65_025 < 2^16`, and fp32 carries a 24-bit
significand. **16 ≤ 24, so the product never rounds.**

Verified numerically over 200_000 random bf16 pairs against exact rational
arithmetic: `200000/200000` exact, zero roundings.

This is precisely why the hardware primitive is "bf16 multiply, fp32
accumulate". It means that in a bf16 matmul **the multiplications contribute no
rounding at all**. Every product is an exact integer in the significand domain.

## What follows: the only rounding in a matmul is the accumulation

A dot product becomes exact integer products followed by a sum. That relocates
the whole numerical difficulty into one place — how the sum accumulates — and
that place is integer arithmetic with exponent alignment, which is what a
BabyBear STARK is good at.

Two options, and the interesting one is not the obvious one.

**(a) Bit-match the hardware.** Prove each fp32 accumulation step with its
rounding. Faithful to what the GPU did; expensive; and it inherits the GPU's
non-deterministic reduction order, which is a genuine obstacle to reproducible
verification.

**(b) Accumulate exactly, round once.** Sum the exact products in a wide
fixed-point accumulator with a per-block exponent, then round once at the end.
This is block floating point, which ML hardware already uses.

Option (b) is better on three axes at once: the arithmetization is pure integer
arithmetic; the result is *deterministic* regardless of reduction order; and the
answer is **more accurate than the hardware's**. We would be proving a
computation strictly better than the one being attested — which is a strange and
rather nice position for a verifier to be in.

The cost of (b) is accumulator width. bf16 carries an 8-bit exponent, so full
dynamic range would need roughly a 280-bit accumulator. In practice a layer's
activations occupy a narrow exponent band — exactly why block floating point
works in hardware — so per-block alignment should keep it modest. **This is the
open quantitative question and where the cleverness has to go.** Measure it on
real activation distributions before believing any number, including this one.

## The shape of the difference

| | int8-quantized matmul | bf16 with exact products |
|---|---|---|
| matmul inputs | quantized | native bf16 |
| rounding in matmul | quantization + accumulation | accumulation only (or once, under (b)) |
| non-linear ops | float, various methods | exact 2^16 table, no approximation error |
| determinism | inherits reduction order | (b) is order-independent |
| fidelity vs unquantized baseline | measurable regression | no quantization step to lose |

The claim is not that this is faster — nothing here is a throughput claim. It is
that the fidelity cost of quantization may not be necessary, and the format that
removes it is the one the hardware already uses.

## What is NOT established here

- The accumulator-width question. Unmeasured, and it is the crux.
- bf16 **addition** (as distinct from accumulation) needs variable alignment
  shifts. It decomposes into small tables but has not been costed.
- Whether end-to-end prover cost is competitive with anything.
- Whether a tabulated `f` matches a given reference implementation. The table is
  a public constant so soundness is unaffected, but its *contents* should be
  generated from a reference and ideally have their properties proved.
- Attention, masking, and KV-cache handling are untouched by this note.
- fp8 formats (e4m3, e5m2) have 256 values and would make even *binary* op
  tables trivial (2^16 pairs). Not analysed; possibly relevant for the parts of
  a network that tolerate it.
