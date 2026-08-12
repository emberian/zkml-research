# The position: bit-exact against a different spec

2026-08-11. This supersedes the framing in `notes/float-in-zk-three-regimes.md`.
Two of my earlier claims were wrong and one line of enthusiasm was dangerous.
The design that survives is sharper than the one I started with.

## Correction 1 — the 8854-gate figure is a strawman, and I repeated it

I cited Garg et al.'s "8854 gates for IEEE fp32 multiply, ~9000-fold overhead"
as the baseline. The lane traced it: **nobody ever implemented it.** It
propagates Garg → ZKLP → ZIP by citation. Worse, ZKLP reports Garg's own costs
as 108/25 while Garg's Table 1 says 89/35, and ZKLP concedes *"we are unable to
present a fair comparison."*

Discount that number. The load-bearing measurements are ZKLP's **64
constraints/op** and Spain's benchmarks below.

Related folklore also corrected: a 24×24→48-bit mantissa product is **one native
field multiplication** in BN254 with 200 bits spare. Float is not expensive
because of the multiply. It is expensive because of **normalization**
(data-dependent shift) and **rounding** (sticky bit = OR across all discarded
low bits). Lookups help float by serving its *range checks*, not by tabulating
its arithmetic — and at BabyBear the cheap-multiply case evaporates entirely.

## Correction 2 — approximate proving loses to quantized, measured

**Spain** (DeStefano, Golub, Huang, Zhang, Frank, Walfish — NYU Courant, OSDI
2026), `~/paperbin/spain-numerical-osdi2026.pdf`, is the strongest float system
in the literature and takes exactly the approximate-satisfiability line I was
enthusiastic about. It is 8–2700× faster than float baselines.

Its own Figure 4 caption: *"The first exception is zkGPT, which outperforms
Spain on all metrics."* Same workload, GPT-2 seq=32:

| | zkGPT (quantized) | Spain (float) |
|---|---|---|
| prover | 64 s | **750 s** (11.7×) |
| verifier | 5.8 s | 78 s (13.4×) |
| proof | 88 KB | **1.6 MB** (18.6×) |

Their §8, unprompted: *"Spain's prover isn't the fastest in the literature; that
honor belongs to zkGPT."*

**The best approximate-float system loses to quantized by ~12×, reported by the
people with every incentive to show otherwise.** That is the cleanest empirical
answer available to "should we just do float?" and it is no.

## Correction 3 — the obvious way to relax the relation is provably exploitable

**Or Zamir, "A Note on Non-Composability of Layerwise Approximate Verification
for Neural Inference"** (arXiv 2602.15756, Feb 2026),
`~/paperbin/zamir-noncomposability-layerwise-approx-2602.15756.pdf`. Four pages,
written as a direct response to the approximate-sumcheck line.

**Theorem 1.** For *any* network F there exists F′ that is **exactly
functionally equivalent** — F′(x) = F(x) for all x — such that for every input
and **every target z in the output range, there is a δ-consistent transcript
whose output equals z.**

The threat-model sentence is the one that matters for a product: *"in realistic
zk-ML threat models one should not assume the network is 'natural'. Typically,
the network is constructed by an adversary and then committed to."* Audits are
black-box benchmarks; F′ passes every one, because it computes the same
function.

This does **not** touch Spain or Bitan et al., whose soundness is
protocol-internal rather than black-box layerwise composition. It kills the
*generic* "prove each layer to tolerance δ" design — which is precisely what I
proposed for accumulation this morning, and precisely what anyone reaches for
first.

*My reading of their bound, not a claim the paper makes:* the required weight
bound is `max(g, 2R/(δ·g^{k-2}))`; for g > 1 the second term collapses with
depth — at g=2, k=32, δ=1e-3, R=10 it is ~2e-5, so the attack needs **no weight
inflation at all**. "Bound the committed weights" is not a mitigation at
transformer depth. Confirm against the proof before relying on it.

## The finding that resolves it: the hardware is already doing block floating point

**arXiv 2606.00279** (`~/paperbin/h100-tensorcore-numerics-2606.00279.pdf`), §4.1,
verified at source:

> "block FMA computes raw products without FP32 normalization. Instead,
> **products are aligned to a maximum exponent within a fixed-point window**
> (e.g., 26 bits for the A100: 2 integer, 23 fraction, 1 extra alignment bit),
> bits shifted out of the window are truncated, **the components are summed as
> integers**, and the final result is truncated to FP32."

NVIDIA tensor cores already perform **shared-exponent integer accumulation**.
Block FMA sums 8 products; one `mma.sync.aligned.m16n8k16` chains two.

Three consequences:

1. My "accumulate exactly, round once" is not a deviation from the hardware —
   it is **closer to what the silicon does** than IEEE per-element rounding is.
   My earlier caveat that we could not claim bit-identity with an H100 was
   pessimistic in the wrong direction.
2. **The 26-bit window fits inside a single BabyBear element.** Within a block
   there is no multi-limb cost at all. The ~280-bit accumulator I worried about
   was an artifact of assuming full bf16 dynamic range in one block; at
   *hardware* block sizes it does not arise.
3. It explains why one prior analysis priced multi-limb arithmetic at ~121×
   overhead — its "block" was the entire matrix.

## The position

**Do not chase IEEE-754 bit-exactness.** Nobody wins there, and the headline
cost figures are unbenchmarked.

**Do not chase error-tolerance either.** Spain says it loses to quantized by
12×; Zamir says the generic layerwise form is exploitable by exactly the party
you are proving against.

**Be bit-exact against a different, published, deterministic spec: block
floating point with an exact accumulator.** This:

- keeps sumcheck/GKR, which the whole field has converged on;
- **matches what tensor cores physically do**, so it is not a fidelity
  compromise — arguably the reverse;
- gives bf16-class dynamic range, and bf16 unary ops stay exact 2^16 tables;
- fits a block accumulator in one BabyBear element;
- has **no quantization step**, so DeepProve's measured 27% requantization cost
  is absent rather than reduced;
- is **order-independent**, so it does not inherit GPU reduction nondeterminism;
- and gives the prover **zero freedom** — which is what makes it Zamir-immune.
  Zamir's construction needs slack to hide in. An exact spec has none.

That last point is the one I would not have found without the counterexample.
The reason to be bit-exact is not fidelity, it is **soundness**: every bit of
tolerance you grant the prover is a bit the adversary can steer.

**And it is unclaimed.** The lane verified absence three ways — OpenAlex
full-text co-occurrence of "block floating point" against {zkSNARK, proof
system, verifiable computation, lookup argument, sumcheck, Groth16, R1CS} and of
"shared exponent"/"microscaling"/"group-wise quantization" against
zero-knowledge returns **zero**; a GitHub API sweep; and a grep of 83 full-text
ZK papers, one incidental hit in a non-ZK numerical paper. Absent from both
dedicated surveys. The idea exists in crypto — CKKS is routinely described as
block floating point — but for FHE noise management, never for constraint count.

## Next step, and it is cheap

`~/src/zk-Location/float/` is parameterized by (E, M). Measuring bf16 and a
block-exponent variant is **hours, not a research programme.** That is the
de-risking step before anything else.

## Traps recorded

- ResearchGate attributes *"a per-layer block scaling exponentiation scheme is
  utilized"* to **zkVC** (2504.12217, DAC'25). **That text is not in zkVC.** Do
  not cite it.
- ZKLP's headline 15.9×/12.2× is against **ZKLP's own unoptimized fixed-point
  baseline**, not another system's float. It is not "float beats fixed-point."
- Lasso/Jolt contain **zero** float content; Jolt targets RV64IM, integer
  multiply only.

## Still unknown

- Measured float costs in production zkVMs (RISC Zero `f32` cycles, SP1 float
  precompiles). Neither lane produced a hard number and I will not quote one.
- ePrint 2025/2152 (Bitan et al.) beyond the abstract. Its protocol-internal
  soundness is *not* hit by Zamir, so the approximate-sumcheck line stays open
  as a component even though the generic layerwise design is dead.
