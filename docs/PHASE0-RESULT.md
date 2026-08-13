# Phase 0: the thesis does not hold. 1.4×, not 4×.

2026-08-11. Measurement harness at `~/dev/zkml-research/phase0/`. This is the
measurement that killed the bf16 4× thesis and with it the plan built on it —
`PLAN.md` is now `notes/archive/PLAN.md`; the live successors are
`docs/AGENDA.md` and `docs/FRONTIER-QUEUE.md`.

## The number

| design | baseline | 54-point sweep | median | points below 2× |
|---|---|---|---|---|
| static shift *(what I assumed)* | 2.63× | 1.51–3.30× | 2.29× | 17/54 |
| **dynamic normalization *(the real design)*** | **1.54×** | **0.85–1.99×** | **1.42×** | **54/54** |

At one parameter point bf16 is **slower**. And the pricing is already optimistic:
the harness charges ~2× for making a shift data-dependent, where Hao et al.
(USENIX'24, Table 1) measure **3.4× runtime and 3.2× communication** for exactly
that change (Msnzb 30.224 µs / 0.508 KB vs constant-shift PosTrunc 8.951 µs /
0.159 KB).

## Why I was wrong, precisely

**Two errors, and the second is the bigger one.**

**1. "Requantization is absent, not optimized" — false.** It is the *same
operation*, moved into its expensive setting. DeepProve's rescale is a per-tensor
**constant** shift fixed at preprocessing. A bf16 renormalization is
**data-dependent**, and data-dependent shifts are what cost. Confirmation from
their own design: where DeepProve's rescale *does* go data-dependent — RMSNorm —
it reinvents block float on the spot (`s₁/(d_j·s₂) = 2^{−l_j}·ε_j`, shared max
shift `r := max_j l_j + f`). We were not removing their step; we were
generalising it in the direction that costs more.

**2. The 75% double-counts.** Of the 75 points, **49.8 are already lookup
tables** — DeepProve §B.2 implements GELU and softmax as tables and *fuses*
requantization into them. You cannot save 75% by converting to tables what is
already tables. **The two halves of the claimed saving are not additive**, and I
added them.

## Where the real advantage comes from — not where I said

| ablation | speedup |
|---|---|
| baseline | 2.63× |
| saturation removed (int-q gets a free clamp) | 1.85× |
| power-of-two scale removed (f=0) | 1.94× |
| **both removed** | **1.05×** |

So the genuine wins are two narrow facts, neither of which I identified:
**saturation** (bf16 has ±inf; an integer-quantized path must *prove* a clamp)
and **power-of-two scale** (no `Quant(2^f·ε)` multiplier). Real, but jointly
worth ~1.4× — which does not justify reordering a programme around format
choice.

## The three facts, tested exhaustively

**Domain escape — holds exactly, and this one is a genuine result.** All 65,536
addresses × 6 functions: **zero addresses with no entry.** `inf` and `nan` are
bf16 values, so the table is *total*; exp's underflow is correct rounding, not a
clip. Against zkAgent's measured abort rates of 0.21% / 0.94% / **4.16%** per
token — near-certain failure over a 512-token transcript — a by-construction
impossibility is worth stating on its own.

**"bf16×bf16→fp32 never rounds" — false as I stated it.** Exhaustive over all
2^32 pairs: 76.17% exact, **23.23% of finite-operand pairs round** (12.52%
overflow, 8.24% underflow, 2.30% subnormal). But **zero normal-range failures** —
every single failure is *exponent*-range, not significand. Correctly qualified
as `−126 ≤ e_x + e_y ≤ 126`, it is 100% exact over 3,179,217,920 pairs. The
significand argument is exhaustively intact; my *statement* was missing a
qualifier, and my 200k random sample never reached the exponent extremes. That
is what sampling buys you and exhaustion doesn't.

**Rank-1 exp — refuted for any exact design.** The control reproduces 2026/1390
(real-valued table, rank 1, σ₂/σ₁ = 1.2e-15). But the **rounded** table — the one
a prover actually commits — has exact rank **253 of 256** over BabyBear, with a
hard counterexample: minor(0,1; 0,18) = −54 ≠ 0. ρ=1 is a property of *exact
arithmetic*, and buying its 256× requires accepting ε-approximation — **the one
thing §5's Zamir argument cannot spend.** §4b and §5 were in direct conflict and
I did not notice. Moot regardless: the table term is **0.054%** of a GPT-2 proof.

## The finding that may outrank all of the above

From the literature sweep (arXiv 2606.05433 §B.2, *not* verified at source):
**float addition is not associative, so Freivalds/sumcheck does not apply to
bf16/fp32 accumulation.** Exact FP GEMM is O(mnd) — one Llama-405B Q-projection
at ~5×10¹³ constraints.

Block-float **integer** accumulation stays associative and keeps the sumcheck, so
§1's 5.3%-matmul premise survives — **but only on the branch that never clears
2×.** The same paper builds the exact 2^16-bf16-table architecture, reports the
MAC chain at **>99% of constraints**, and notably does *not* use bf16 tables for
softmax/RMSNorm because their inputs are fp32.

## What this does to the plan

**Cut:** §1's 75% framing (double-counted), §2's "requantization is absent"
(false), §4b entirely (refuted, conflicts with §5, and worth 0.054% anyway), and
the "~20% from ZKLP" line — which appears to be **unsourced**; the nearest real
figure is ZKLP's fp32-vs-fp64 at 23.5%, and their native-constraint row is
bit-identical across widths, so precision touches only the range-check tail.

**Keep, and it is now the centre rather than the supporting argument:** §5. The
soundness case for bit-exactness — every bit of tolerance is a bit the adversary
steers, with Zamir's Theorem 1 and the Goldwasser/Ishai/Kalai/Thaler
no-multivariate-Remez obstruction behind it — **never depended on the cost
claim.** It stands undamaged, and it is the strongest thing in the document.

**Keep:** domain-escape totality; the corrected product-exactness fact; the
landscape and licensing findings; the audit-sampling and system-primitives work.

**Re-price:** Phase 1 against 1.4×, not 4×.

## The honest strategic read

The bet was that a format choice would buy a large constant. It buys ~1.4×. So
the project should not be *"faster verifiable inference via bf16."*

What survives is better founded and less crowded: **an open, bit-exact,
slack-free verifiable inference stack whose soundness argument is complete** —
in a field where three of the four best-known "open" projects are not
open-source, where every deployed system hands the prover a per-element error
window that Zamir's construction provably exploits, and where nobody has closed
Hollow-LLM's effort gap.

That is a soundness-and-openness project, not a throughput project. It was
always the stronger half; Phase 0's job was to find out whether the throughput
half was real, and it isn't.
