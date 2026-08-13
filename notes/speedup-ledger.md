# The speedup ledger — everything found, in one place

2026-08-12. Consolidates the week's positive findings scattered across PLAN.md,
PHASE0-RESULT, missed-threads, ml-to-crypto-mappings, and mirror-mine. Three
bins: measured speedups sitting in the literature, combinations nobody has
done, and things that exist on paper only.

## Bin 1 — measured speedups, mostly sitting unused

| lever | gain | source | status |
|---|---|---|---|
| Packed sumcheck over BabyBear | **2.78×** | 2025/719 | measured *on our field*; unadopted |
| Substrate: FRI-M61 vs KZG-BN254 | **3.8–5.7× prover, ~1000× verify** | OpenLLM's own tables | third-party confirmation of small-field+hash |
| BaseFold vs HyperKZG | faster **and half the RAM** (174 vs 146 TPM, 42 vs 78 GiB) | DeepProve's own A/B | they switched away anyway; the fast config is absent from their public code |
| Thaler Thm 3 matmul sumcheck | **0.18–0.33% overhead** vs 6.2× generic GKR | Thaler '13 Table 5 | engine exists in `p3-sumcheck`; never wired for ML |
| zkCNN linear-time FFT sumcheck | **33.2×** over GKR-on-FFT | zkCNN §4.3 | conv-specific |
| Monomial-basis sumcheck | ~10% end-to-end | 2026/762 | free constant |
| Jolt in small space | **<2× time at tiny memory, no recursion** | 2025/611 | the scale enabler |
| VEIL ZK wrapper | **3% prover overhead** for the ZK property | 2026/683 | ZK is nearly free now |
| Binius ring-switching | **zero embedding overhead** for tiny values | 2024/504 | the small-value lever, formal substrate already in our tree |
| Sampling audit | **24× prover → ~1.24× system** at p=1% | our derivation + Rinberg | the deployability multiplier; not a prover speedup, better |
| Small-value sumcheck handling | **2–3× (Spartan-in-Jolt), 20×+ at memory limits** | 2026/587 | measured; the Thaler-program substrate for mapping A |
| Sparrow space-efficient data-parallel | **3.2–28.7× less prover space than Gemini; 1.4× native space** | 2024/1631 | mappings D+F in one paper |
| VerfCNN | **10× over plaintext CPU inference** (VGG-16, 12.6 s) | 2025/2020 | best overhead ratio seen anywhere; conv-specific |
| exp table rank-1 hi/lo | 2^16 table → two 2^8 tables | 2026/1390 Prop 3 | exact version unclaimed (OpenLLM has the rounded version) |
| MXINT8 static-shift path | **2.29× median** (Phase 0's static column, 1.51–3.30×) | our Phase 0 harness | the format that actually shares exponents; Phase 0′ unrun |

## Bin 2 — combinations nobody has done (each half exists; the product doesn't)

1. **Binius small-value commitment × the Ω(m) nonlinearity floor.** The floor
   (2026/1390) says you can't reduce the *count* of committed activations; ring
   switching says you can shrink each one's *cost* to its bit-width. Nonlinear
   commitment is the measured 66–75% of prover time, so this attacks the
   dominant term at its constant. Binius×ML: **zero papers in 7,090.**
2. **Data-parallel sumcheck × transformer layer uniformity.** The primitive is
   Thaler '13 / 2024/143; folding L identical layers (and the batch dim) into
   the hypercube as log(L) extra variables is in nobody's system — all run
   per-layer.
3. **Streaming provers × LLM weights.** Hobbit (optimal prover time,
   USENIX'25), Scribe (disk streaming), 2025/1473 (tradeoff proven optimal) —
   all exist; "prove a 70B model on a 64 GB box" exists in **zero systems**.
   DeepProve projects >1 TB for 3B; that's the wall this removes.
4. **Neo/SuperNeo folding × the decode loop.** PQ small-field folding
   (2026/242) exists; KV-cache-as-accumulator-state over autoregressive decode
   is unbuilt. Kills the per-token fixed costs that make batch-scaling regress.
5. **MoE router binding × proof-cost-∝-active-params.** Zero papers in 7,090.
   For DeepSeek-V3-class models (37B active of 671B) this is an **~18×
   architectural discount** no prover optimization can match — *if* the top-k
   routing is bound by a permutation argument, which is also what stops
   route-to-cheap-expert cheating.
6. **Sampling audit × any prover at all.** The only lever that changes
   *deployment* economics rather than prover economics. Composes with
   everything above multiplicatively.
7. **The memory-bubble fusion** — prover rides decode's weight traffic in the
   idle integer pipeline. Three adjacent works (zkComposer, FluxZK,
   2606.05433's concurrent streams) fuse *within* proving; none fuses proving
   *with inference*. Read those three before claiming.
8. **Proof-aware QAT** — train the model into field-native ops (I-BERT's
   integer approximations port directly). In nobody's paper.

## Bin 3 — exists on paper only, no implementation anywhere

- **LogUp-GKR wall-clock**: no published number in any venue. SP1's CUDA bench
  harness exists unrun-in-public.
- **Plonky3 GKR**: none; `p3-sumcheck` isn't even wired to `p3-lookup`.
- **LoRA inference-side proving**: the NDSS/arXiv cluster covers fine-tuning
  only; prove-base-once + thin-adapter serving is open.
- **The open Attestable-equivalent**: DeepProve unforkable (evaluation-only
  license contradicting its own Cargo.toml), ezkl has no license file,
  JSTprove grants no use rights. **The open position is entirely vacant.**
- **Machine-checked commit-then-audit**: 2026/541 is pen-and-paper; the
  `q = p(1−ε_snd) − ε_bind − ε_beacon` composition and the Lean version remain
  unclaimed. Our `lightClientSound` is structurally the theorem.
- **Lean-verified lookup tables/constraint semantics**: ACL2 precedent for
  Jolt's tables (2024/1841); nobody does it for zkML, and it's our house
  discipline anyway.

## If you want one sentence

The compounding stack nobody has assembled: **Ceno/Expander-style small-field
GKR substrate + packed sumcheck (2.78×) + layer-fold (unclaimed) + Binius
small-value commitments against the nonlinearity floor (unclaimed) + streaming
weights (unclaimed) + MoE active-param discount (unclaimed, ~18× on frontier
MoEs) + sampling audit (~20× deployment amortization) — all post-quantum, all
open-source, with the audit theorem and the tables machine-checked in Lean.**

Every factor exists or is verified absent from the literature. None of the
unclaimed ones is priced yet — that is what the next phase's harnesses are for.
