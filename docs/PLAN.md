# Plan: open verifiable inference on block-float bf16

2026-08-11. Written after six research lanes. Every number below is marked
**[measured]** (from a paper's own tables), **[verified]** (computed here), or
**[mine]** (inference). The plan changed twice during the research and this is
the version that survived contact.

---

## 1. The finding that reorders everything

**Matmul is 5.3% of prover time. Nonlinear work is 75%.**

DeepProve Table 7, GPT-2 seq 512, BaseFold, 24-core EPYC — **[measured]**:

| component | % of total prover time |
|---|---|
| **Requantization** | **25.3%** (Gemma 3: **34.4%**) |
| Softmax | 23.7% |
| Activation (GELU) | 18.0% |
| RMSNorm | 8.1% |
| Logits | 8.0% |
| **EinSum — every matmul in the model** | **5.3%** |
| **nonlinear subtotal** | **75.1%** (Gemma 3: 66.9%) |

**Independently corroborated a second time, by a group that did not notice.**
OpenLLM (eprint 2026/1578, Zhejiang/CAS/Antgroup) never cites DeepProve and
never reports requantization's share — but their own Table VII gives one
`Requan` at 1024×1024 as **2.935 s** against GELU 10.045 s (**29.2%**), Softmax
11.556 s (**25.4%**), Norm 9.306 s (**31.5%**), and their protocol figures call
it **3–9 times per operator**. Different codebase, different field (M61),
different PCS, same 25–34%. **[measured]** That is the strongest form of
evidence for §1 — a number reproduced by people who were not looking for it.

Also confirmed on a different backend: **zkGPT** (USENIX Sec'25, GKR +
Lasso), GPT-2, 16-core — all matmuls **1.5 s of 21.8 s = 6.9%**; lookups alone
**55.5%**. **[measured]**

And it is not an artifact of current engineering — **eprint 2026/1390,
Corollary 3** proves an **Ω(m) commitment floor**: proving `m` activation
evaluations requires Ω(m) commitment work. *"Function structure amortizes the
shared table, never the m per-operation commitments."* **[measured]**

Why: matmul-by-sumcheck is `O(mn + np)` for an `mnp`-op product — *sublinear in
the work proved*, with zero per-proof commitment. Every nonlinearity costs
`Ω(#elements)` of committed witness. **FLOP dominance and proof-cost dominance
run in opposite directions.**

## 2. Which means the format choice is the whole game

Our two verified facts **[verified]**:

- bf16 has exactly 2^16 values ⇒ every unary function is an **exact 65,536-row
  table**. No approximation, no error term.
- bf16 × bf16 → fp32 **never rounds** (8-bit significands, 16-bit product,
  24-bit fp32 significand; 200k random pairs against exact rationals, zero
  roundings).

Set against the cost table **[mine, and the core bet]**:

- **Requantization — 25–34%, the single largest line item — does not exist in a
  bf16 path.** There is no quantize/dequantize step to prove. Not optimized:
  *absent*.
- **Softmax + GELU + RMSNorm = 49.8%** are exactly what a 2^16 table makes one
  exact lookup.

So **~75–84% of measured prover cost is what the format choice removes or
collapses**, and matmul — the thing everyone's intuition says to optimize —
is 5%.

## 3. And the competitor's quantization is measurably broken on modern models

DeepProve Table 4, cosine similarity vs full precision **[measured]**:

| model | 8-bit | 10-bit | 12-bit |
|---|---|---|---|
| GPT-2 | 0.9967 | 0.9993 | 0.9966 |
| **Gemma 3** | **0.2035** | 0.6998 | 0.9587 |

Gemma 3 perplexity: baseline 515 → **>1150 at 8-bit**. Outlier activations plus
extra RMSNorms defeat smoothing. **12-bit is the floor for modern
architectures.**

This is the strongest single fact in the whole research programme. Attestable
proves Gemma **4** 31B with *all matmuls int8*. Their own eval concedes IFEval
regression. DeepProve's independent measurement says int8 destroys Gemma **3**
at 0.2035 cosine similarity. **The quantization is not a minor fidelity tax; on
this model family it is catastrophic** — and our path has no quantization step
at all.

## 4. The field question, and why bf16 wins it too

At 12-bit the accumulator is `lhs + weight + ceil_log2(d)` = **34–36 bits**,
which **overflows BabyBear's 31-bit base field** **[measured]**. That is why
Ceno and DeepProve-v1 chose Goldilocks, and why zkPyTorch co-designed
quantization for **M61** rather than move to a curve field.

Now the convergence. NVIDIA tensor cores already do **shared-exponent integer
accumulation** — arXiv 2606.00279 §4.1 **[measured]**:

> "products are aligned to a maximum exponent within a fixed-point window (e.g.,
> **26 bits for the A100**: 2 integer, 23 fraction, 1 extra alignment bit), bits
> shifted out of the window are truncated, **the components are summed as
> integers**, and the final result is truncated to FP32."

**A 26-bit window fits inside a single BabyBear element. A 34–36-bit quantized
accumulator does not.** **[mine]** So block-float bf16 fits the field the
quantized path is forced out of — and it does so by matching what the silicon
physically does, not by deviating from it.

## 4b. The exp table is rank-1, and that is a theorem

eprint 2026/1390 Proposition 3: per-proof table cost is `Θ̃(ρ·2^{r/2})` where ρ is
the table's **bipartition rank**. Generic tables are full-rank (Prop. 4) and do
not decompose. But **exp does, exactly** — verbatim: *"an addition theorem gives
an outer product, ρ = 1 (checked: the r=16 exp table has σ₂/σ₁ = 1.6×10⁻¹⁵;
**this is the deployed hi/lo split**)."* **[measured]**

Because `exp(a+b) = exp(a)·exp(b)`, the 2^16 table factors into **two 2^8
tables**. So the headline is better than "one 65,536-row table": for exp it is
two 256-row tables and a multiply, and the paper certifies that as the rank-1
optimum. **[measured]**

⚠ **Prior art, and our claim must be narrowed accordingly.** OpenLLM Fig. 7
already uses multiplicative digit factorization for exp — decompose into 12-bit
digits, per-digit table, recombine by ProdCheck. **The factorization is not
ours.** What is ours is **exactness**: their table entries carry a `⌊·⌉`, so
error is introduced per digit and compounds through the product, whereas a bf16
hi/lo split is the complete graph of the function with no rounding anywhere.
Claim exactness, never factorization.

⚠ Correction to an earlier relay: the holonomic/ODE construction is **not** a
general win at our operating point — measured 0.56× for erf but **1.28× worse**
for native `1/√x`; the 126× only appears past r > 28, which we never reach.
Worth a spike for GELU/erf only; keep mantissa-indexed lookup for rsqrt.

## 5. Why bit-exact, not error-tolerant

I spent the morning enthusiastic about approximate proving. Two findings killed
it:

- **Spain** (OSDI 2026), the best float system in the literature, taking exactly
  the approximate-satisfiability line — **loses to quantized zkGPT by 11.7× on
  prover and 18.6× on proof size**, same workload, reported in their own
  Figure 4. Their §8: *"Spain's prover isn't the fastest in the literature; that
  honor belongs to zkGPT."* **[measured]**
- **Zamir, arXiv 2602.15756** (Feb 2026), Theorem 1: for any network F there is
  an **exactly functionally equivalent** F′ such that for every input and
  **every target z in the output range there is a δ-consistent transcript
  outputting z.** In zkML the network is *adversary-constructed then committed*,
  and F′ passes every black-box audit because it computes the same function.
  **[measured]**

**And the windows in deployed systems are wide enough to matter.** Every
fidelity-carrying system hands the prover an acceptance window on *every*
element: ZIP **δ = 9×10⁻³ relative**, zkLLM **ε ≈ 10⁻² row-sum band**, Spain a
per-op ε. Zamir's construction at R≈20, δ≈10⁻³, g=2, k=20 needs a trigger weight
of **M ≈ 0.15** — an utterly ordinary weight — with amplification g^{k−2} = 2¹⁸.
**Tolerances at fp16 rounding scale suffice for arbitrary output steering.**
**[measured]**

Our design has **zero per-element window**: `q = (T_hi[a]·T_lo[b] + 2^29) >> 30`
is an exact integer relation plus two table-membership assertions, and the only
slack is one scalar acting as a uniform rescale. That is the single property
Theorem 1 cannot touch.

**And the repair route provably does not exist.** This is the strongest sentence
available to us and it is not ours. Bitan, DeStefano, Goldwasser, Ishai, Kalai
and Thaler, §5 p.23 of the March 2026 revision, on extending approximate
sum-check to GKR/Spartan — verbatim:

> "Proving soundness in both cases seems to require an approximate multivariate
> Schwartz-Zippel style lemma… **Unfortunately, no useful approximate
> multivariate Schwartz-Zippel lemma exists**: unlike the univariate case where
> Remez inequalities tightly control sublevel sets, a multivariate polynomial can
> be small on a large-measure set while large elsewhere [SVZ25, §1.2]."

Slote–Volberg–Zhang (*Discrete Analysis* 2025:4) §1.2 confirms it is not a gap
in the state of the art: *"there is no hope for such an inequality phrased in
terms of µ(E) for any positive-measure E"*, with `f_n(x) = 1 − Σx_j²` on the
unit ball as the counterexample. **[measured]**

So no layerwise-approximate zkML scheme can be repaired by better analysis. The
obstruction is analytic and it is the twin of Zamir's construction.

So: **every bit of tolerance granted the prover is a bit the adversary can
steer.** Being bit-exact against a *published deterministic block-float spec* is
not a fidelity preference — it is what makes the construction Zamir-immune,
because his attack needs slack to hide in and an exact spec has none.

**And nobody has connected block floating point to ZK.** Verified three ways:
OpenAlex full-text co-occurrence of "block floating point" / "shared exponent" /
"microscaling" against {zkSNARK, sumcheck, lookup argument, verifiable
computation, R1CS…} returns **zero**; a GitHub API sweep; a grep of 83 full-text
ZK papers, one incidental non-ZK hit. Absent from both dedicated surveys. The
idea exists in crypto — CKKS is block floating point — but for FHE noise
management, never for constraint count. **[measured]**

## 6. Substrate

**Plonky3 has no GKR** — `grep -ri gkr` at HEAD returns zero matches. `p3-sumcheck`
(20,262 lines, SVO + HVZK) exists and is excellent but **is not wired to
`p3-lookup`**; its only consumers are `whir/`, `multi-stark/`, `examples/`.
Adopting LogUp-GKR is a build, not an integration. **[measured]**

Small-field + hash-based GKR is production-proven regardless: **Expander**
(Polyhedra) is a multi-field GKR engine over babybear/goldilocks/m31 with
**Orion** (hash-based, linear-time) and CUDA MSM; Inference Labs migrated *onto*
it from ezkl. **SP1 Hypercube** runs LogUp-GKR on KoalaBear with CUDA. **[measured]**

**And small-field + hash-based GKR is what Polyhedra ships, not a road not
taken.** Expander is a multi-field GKR engine with `arith/babybear`,
`arith/mersenne31`, `arith/goldilocks` as first-class crates and **Orion**
(hash-based, linear-time) as a shipped PCS alongside KZG/Hyrax; **Inference Labs
migrated onto it from ezkl**. zkPyTorch compiles PyTorch → Expander and
co-designed its quantization for **M61** rather than move to a curve field —
independent evidence that the accumulator-width problem is real and that the
standard answer is *a wider small field*, not a curve. Its reported VGG-16
2.2 s/image and Llama-3 150 s/token name **no hardware and no baseline**, and
Polyhedra's own blog says 6.3 s for the same VGG-16 figure — treat both as soft.
**[measured, with the provenance caveat]**

**And a third group measured the substrate question our way.** OpenLLM
benchmarked all three PCS on identical hardware: **FRI-M61 is 3.8–5.7× faster on
prover than KZG-BN254 and ~1000× faster on verify** (GELU 1024²: 10.045 s /
4.170 ms vs 57.496 s / 22.501 ms; Softmax verify 5.112 ms vs 13,948 ms for IPA).
**[measured]**

So DeepProve's exit to BN254 is one team's trade for proof size, not the
field's verdict. And DeepProve's own A/B argues *for* the hash-based path they
left: BaseFold
**174.32 TPM / 41.85 GiB** vs HyperKZG **146.03 TPM / 78.49 GiB**, and HyperKZG
**OOM'd** on Gemma 3 at 128 GB. They switched for ~2× smaller proofs, not
throughput. Their public code is HyperKZG-only, so **the headline numbers are
not reproducible from the published code.** **[measured]**

## 7. Licensing — the position is vacant

Checked at HEAD, 2026-08-12 **[measured]**:

- **DeepProve** — revocable "Lagrange License", use *"solely for testing and
  evaluating"*, §4 forbids derivative works, §3 grants no patent rights,
  terminable "with or without cause" — while `Cargo.toml:16` declares
  `license = "MIT OR Apache-2.0"`. Direct contradiction. **Not forkable.**
- **JSTprove** — *"NO USE RIGHTS ARE GRANTED BY THIS LICENSE."*
- **ezkl** — **no LICENSE file at all**, only a `cla.md`. Universally called
  open source, including by Attestable.

Genuinely open and usable: **Ceno** (Apache-2.0, DeepProve's own substrate),
**Expander** (AGPL-3.0), **Jolt** (Apache/MIT), **ZKTorch** (Apache-2.0),
**Plonky3** (MIT/Apache).

## 8. The plan

**Phase 0 — de-risk the bet, hours not weeks.**
`~/src/zk-Location/float/` is parameterized by (E, M). Measure bf16 and a
block-exponent variant. Then measure the claim in §2 directly: build the three
tables (exp, GELU/SiLU, rsqrt) as 2^16 LogUp tables over BabyBear and count
constraints against DeepProve's fused-requantization protocol. **If ~75% of
prover cost does not fall, the thesis is wrong and we should know in a day.**

**Phase 1 — the block-float spec.** Publish a deterministic block-float
inference spec: block size, exponent selection, alignment window, truncation
rule, single final rounding. Bit-exact, order-independent, tensor-core-shaped.
This is the object everything else is proved against, and publishing it *is* the
contribution — Zamir-immunity comes from it having no slack.

**Phase 2 — catgrad backend as a stager.** `impl Backend for ProvingBackend`
over catgrad's 39-method trait, modelled on `shape_only.rs`. Resolves shapes and
branches, records a trace, **authors zero constraints** (house law). Smallest
demo is a ~10-line diff at `examples/hidden.rs:73-95`. Ask the catgrad
maintainers first: the repo is dormant ~9 weeks and the team appears to have
moved to `catena-lang`.

**Phase 3 — Lean-authored constraint semantics** for the ~20-op subset, emitting
DescriptorIR2, consumed by the existing `circuit/src/descriptor_ir2.rs` batch
STARK. The bf16 tables are public constants; their *contents* should be
generated from a reference and their properties proved.

**Phase 4 — matmul by sumcheck.** Thaler Theorem 3 on `p3-sumcheck`
(`SumcheckProver::new(ProductPolynomial, sum)` is literally the shape), measured
at 0.18–0.33% overhead vs 6.2× for generic GKR-over-a-multiplication-circuit.
Do it — but knowing it is worth ~5%.

**Phase 0 must also measure two things nobody reports.**

- **Domain-escape rate.** zkAgent measures per-token overflow — activation
  leaves the calibrated table domain and the proof *aborts* — at 0.21% (GPT-2),
  0.94% (LLaMA-2-13B), **4.16% (C4)**. Over a 512-token transcript that is an
  abort probability of **0.66 to ~1**. **[measured]** Mitigation: out-of-domain
  must be a **proved affine tail** (GELU/SiLU are asymptotically affine), never
  a clip. exp's domain [−88,0] is safe — that is an underflow boundary, not a
  clip. Instrument overflow rate as a first-class metric; only zkAgent reports it.
- **Whether bf16 actually buys what I think.** There is **no measured per-op
  constraint count for bf16/fp16 anywhere**, and extrapolation from ZKLP
  suggests bf16 buys only **~20%** over fp32 for *IEEE arithmetic*. Our claim is
  a different one — exact tables and non-rounding products, not cheaper float
  ops — but the absence of any measurement is exactly why Phase 0 exists.

**A collaboration opening worth taking.** OpenLLM's requantization numbers are
the strongest independent evidence for our central premise and they did not draw
the conclusion. Leading with that observation is a genuine gift and costs us
nothing. The group holds deep knowledge of both systems we benchmark against —
Xuanming Liu (`hinsliu@zju.edu.cn`) is a co-author of *both* OpenLLM and zkGPT.
Their artifact is already gone (anonymous repo, HTTP 410, no licence, no
mirror), so an open comparison would be informative to them too.

**Deliberately not doing:** IEEE-754 bit-exactness (nobody wins, and the
headline 8854-gate figure is an unbenchmarked strawman propagated by citation);
error-tolerant proving (§5); racing anyone on throughput before §8 Phase 0
lands.

**And approximate sum-check is not our accumulation fallback.** I proposed it as
one this morning. Three independent kills, any one sufficient **[measured]**:

1. **Wrong field.** The κ contraction function — the entire technical content —
   comes from *archimedean* Remez inequalities, needing an archimedean absolute
   value, FTA + continuity for the "at most d arcs" sublevel-set step, and
   arc-length measure. The paper's only finite-field instantiation (§3.2, p.17)
   is the degenerate `δ=0` case, which *is* classical sum-check. Not
   BabyBear/M31/Goldilocks.
2. **No PCS exists.** §7, p.25, verbatim: *"realizing full SNARKs will require
   identifying polynomial commitment schemes that maintain soundness under
   approximation."* It is a PIOP, not a proof system — and hash-based PCS
   soundness is code-based, which this paper explicitly discards (§6, p.25).
3. **It loses to exact accumulation on its own terms.** Our full-dynamic-range
   exact accumulator is ~280 bits, integer, order-independent, composable. For
   N=2^20, d=2 approximate sum-check needs ~254 bits of *floating-point* working
   precision for **40 bits of interactive** soundness — and **~4,040 bits
   non-interactively at λ=100**. Roughly **14× more precision than exact
   accumulation to prove the same inner product**, with a weaker guarantee and
   no commitment layer.

⚠ **Trap:** §6's precision-comparison table is derived under *interactive*
soundness while the approaches it compares against are non-interactive-ready.
Quoting those figures for a SNARK quotes the wrong number.

## 9. Numbers to beat

DeepProve **174 TPM** GPT-2 / **86 TPM** Gemma 3 (BaseFold, 16-core Ryzen) —
these are the *BaseFold* figures, i.e. the config absent from their public code.
Distributed 1855 TPM is **simulated**, not a cluster. Measured prover overhead
vs PyTorch-CPU: **~24×**. **[measured]**

Attestable 53 tok/s on 31B / 1×H100 is a self-report with no paper, no code, no
artifact; benchmark tables are images; "100 bits" names no field, hash, or
soundness analysis.

## 10. Two cautions I am carrying forward

**GPU will not save us.** Irreducible measures GPU sumcheck at only **2.6–4.0×**
over CPU — it is memory-bound. ZK field ops use only the **integer pipeline**,
whose per-SM throughput is **flat across GPU generations**. Provers do not ride
the AI-hardware curve. Our GPU backend still helps Merkle/hashing in a FRI
stack. **[measured]**

**The Hollow-LLM attack is unclosed by everyone.** arXiv 2607.28884: a ZK proof
of inference binds the *relation* over committed weights, not the computational
*effort*. Ghost weights with collapsing algebraic structure emit valid proofs at
small-model cost. Closing it needs a publicly checkable weight-commitment
registry — **which an open project can do and a closed one structurally
cannot.** **[measured]**
