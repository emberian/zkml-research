# Ozaki FP4-limbs transplant: refuted as import, clarified as gap

2026-08-12. Lane verdict + its own self-correction after the prior-art sweep.

## The refutation

"Most transplantable single idea found" does not survive reading. The Ozaki
paper's engineering core — keep intermediate sums in the FP32 accumulator's
integer range instead of writing back to FP4 — **is deferred carry / lazy
reduction, which ZK has had for years under six names in six codebases**
(Aztec `bigfield` budgets 2^10 products per normalization; noir-bignum ~64;
gnark `deferredChecker`; arkworks `mul_without_reduce`; …). Its distinctive
parts (base-13, p×q splits, RNS) are hardware artifacts that do not transfer.

**SP1 already runs the integer substrate in production on BabyBear**: 256-bit
values as 32×8-bit limbs, witnessed vanishing polynomial, degree-2 AIR, ~126
range checks per modmul, explicit headroom budget 2^21 vs 2^31 — structurally
the same accounting as Ozaki's Lemma 2, deployed.

## What is genuinely missing (the sharpened gap)

ZK supplies the whole *integer* half: limbs, exact limbwise products, deferred
carry with headroom budgets, one-shot normalization, range checks at ~1
constraint per 8 bits amortized. It supplies **none of the numerical half**:
choosing a FLOAT split so limb products are exact by construction, the
dynamic-range/shift machinery, and error-free recombination semantics. That
composition is the unclaimed object — narrower than "transplant Ozaki," and
better defined.

## Numbers (gnark/BN254 R1CS; NOT transferable to BabyBear precision)

- Full Kulisch accumulator: ~3,100 constraints (0.76/scalar MAC) — **3.5×**
  cheaper than ZKLP's 127 fp32 adds (was optimistically 4.5×).
- Alignment-window path: ~1,050 — **10.3×** (was 17×).
- **Range checks are 79–99% of cost** in existing bignum circuits (xJsnark
  RSA: 79%; circom BigMult-256: 7 mult constraints vs ~981 normalization).
  Design target: minimize range-checked witness bits, not constraint count.

## Flags raised

- **Spain (eprint 2026/1356) must be read before building anything here** — it
  claims 32×–10^4× over Otti/ZKLP with division and sqrt at ONE constraint
  each. If that holds for addition, the ZKLP baseline both our numbers are
  measured against is superseded. (We hold both the eprint and OSDI versions;
  the earlier read covered its GPT-2 loss to zkGPT, not its techniques.)
- **Binius does not obviously serve a Kulisch accumulator**: its integer
  multiplication is schoolbook on 8-bit words with literal ripple-carry bits —
  no deferred-carry limb semantics. Mapping A's *commitment* use is
  unaffected; the *accumulation* hope is weakened.
- Limber corroborated at source: `q = Ω(λ²m²)`, Goldilocks not BabyBear,
  integers only — consistent with the earlier lane.
- RNS-in-SNARK is live (Casting Out Primes 2022/1470; Ambrona 2025/695,
  EasyCrypt-formalized) — "CRT is anti-transplantable" was overscoped; it
  applies to our workload, not universally.

## The named next step, cheapest-first

**Measure the E8M0 exponent spread in real gpt-oss scales.** The `_scales`
tensors are uint8 E8M0, small, and fetchable by HTTP range request. The
within-tensor spread and adjacent-block deltas decide whether the
~1,050-constraint alignment-window path covers most of the 78.9% MXFP4 FLOPs —
i.e. whether the cheap path is the common path. Highest information per hour
of anything on this thread. (Lane launched.)
