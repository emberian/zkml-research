# The mapping tricks: ML structure → crypto structure

2026-08-11, Fable. Ember: "there are surely other efficiency tricks mapping ML
to crypto." Yes. The day's research treated ML as a generic circuit with one
knob (number format). But ML computation has *structure* — low rank, sparsity,
uniformity, small values, verify-easier-than-compute — and each piece of
structure has a cryptographic counterpart. Brainstormed against what the log
already established; each entry states the mapping, the evidence, and status.

## A. Small values → small commitments (Binius direction) — OUR biggest miss

**ML fact:** quantized weights and activations are 4–8 bits. **Crypto fact:**
in binary-tower schemes (Binius; Basefold-family small-value optimizations),
commitment cost scales with the *bit-width of the committed values*, not the
field width. An int8 activation committed as 8 bit-columns costs a fraction of
the same value embedded in a 31-bit field element.

This composes with the one *theorem* the research produced about cost: the
Ω(m) commitment floor for nonlinearities (2026/1390). **You cannot beat the
floor in element count — but you can shrink its per-element constant from a
field element to 8 bits.** The floor is why nonlinearities are 75% of prover
time; this is the only lever that attacks the floor itself.

And the punchline: **our own tree is already a binary-tower shop.**
`Theory.BinaryTower` (the GF(2) tower substrate, "[OB-8-tower] … (Binius
path)"), `BinaryTowerFanPaar` (formalized Fan–Paar multiplication),
`AdditiveNTT`/`AdditiveFriTower` (additive FRI over binary towers),
`Tower256ConcreteBackend` + `binary_tower_256.rs` native kernels. We spent the
day comparing 31-bit prime fields while sitting on a formalized
small-value-native commitment substrate. Expander ships `gf2`/`gf2_128` crates
too. **Status — CORRECTED by the full-corpus mine (2026-08-12): not an
unexplored lever.** Small-value preservation is a named technique in Thaler's
own survey ("Sum-check Is All You Need", 2025/2041), Dao–Thaler do
constraint-packing over binary towers (2024/1038, ~128× on the eq
pre-computation), and 2026/587 measures **2–3× on Spartan-in-Jolt, 20×+ at
memory limits, from small-value handling alone**. What remains unclaimed is
the **ML application** — pointing this surveyed program at the Ω(m)
nonlinearity floor. Narrower gap, better substrate.

## B. Low-rank deltas → tiny proofs (LoRA)

**ML fact:** most deployed fine-tunes are LoRA: W' = W + A·Bᵀ with rank r ≪ d.
**Crypto mapping:** the base model is committed *once, globally* (this is the
Hollow-LLM registry, now doing double duty); a fine-tune commits only its
adapter — kilobytes, not gigabytes. And proving (W + ABᵀ)x = Wx + A(Bᵀx) is
the base-model sumcheck plus two *thin* matmuls, nearly free.

Bonus: "fine-tune provenance" — prove an adapter was derived from a registered
base — is a product in itself, and catgrad's source-to-source autodiff means
the backward pass is also an open hypergraph if anyone ever wants training
steps. **Status: LoRA appears nowhere in the log. Cheap to add; large
practical surface, since fine-tunes are the common deployment case.**

## C. Conditional sparsity → proof cost ∝ active params (MoE)

**ML fact:** MoE models (DeepSeek, Mixtral, gpt-oss — all in catgrad's model
list) activate k of E experts per token; active params are a small fraction of
total. **Crypto mapping:** prove only the fired experts' matmuls, plus a
*router-binding* argument that the top-k selection was honest — and top-k is a
permutation argument plus monotonicity check, which SNARKs do cheaply.

Router binding also closes an effort-gap cousin of Hollow-LLM: an unproven
router lets the prover route everything to a cheap expert. ~~**Status: absent
from the log and from every zkML paper we read; all of them prove dense
models.**~~

⚑ **RETRACTED 2026-08-13 — the absence is FALSE.** `notes/moe-router-binding.md`
§7. **ZK-DeepSeek (arXiv 2511.19902)** proves DeepSeek-V3's grouped two-round top-k
and proves only the selected experts; **arXiv 2606.05433 §A.5 OP-10** names routing
commitment and top-K verification as protocol sub-problems. **Both were already in
`~/paperbin/`, pulled and correctly named on 2026-08-12 — the same day the absence
was declared.** The sweep read first-2-page caches and both papers bury MoE in a
§4.3 and an appendix. What remains open is narrower and sharper: the tie-break
(ZK-DeepSeek's non-decreasing sort is **unsound** on ties; 2606.05433 calls bf16 ties
"rare" and the criterion `2^mantissa < n_experts` says they **dominate**), **expert-
identity binding** (neither addresses it; the naive fix costs Θ(E·d·f) and erases the
discount), and the discount's **decay with context length** (18.3× at C=1 → 2.7× at
128k, unpublished). Also cite **CryptoMoE** (NeurIPS'25) — the counter-current that
hides routing.

## D. Layer uniformity → one sumcheck over the layer dimension

**ML fact:** a transformer is the *same* layer circuit repeated L times (and
the same model run across B batch entries). **Crypto mapping:** data-parallel
sumcheck (Thaler '13 already handles identical sub-circuits): make the layer
index log(L) extra Boolean variables of the multilinear extension and prove
*all layers' matmuls in a single sumcheck*, instead of L sequential ones.
Same for the batch dimension. This attacks exactly the per-proof fixed costs
that made "below B≈14 a plain AIR wins."

**Status: zkCNN/zkLLM/DeepProve all run per-layer. The uniformity of
transformers is maximal and unexploited.**

## E. Verify-don't-compute (nondeterministic advice) as the organizing principle

**ML fact:** many ML ops are hard to compute but trivial to *check*: division
(witness the inverse, check x·x⁻¹=1), rsqrt (check y²≤x<(y+1)²), argmax/top-k
(witness the permutation, check sortedness + membership), sampling under a
committed seed (check the CDF inversion). **Crypto mapping:** the witness IS
the answer; the circuit only checks. Permutation/multiset arguments — the
cheapest primitives we have — carry sorting and selection.

Individually these are folklore; the log used the pattern implicitly (LayerNorm
via two lookups) but never named it as the design rule: **for every op, ask
"what is the cheapest CHECK?" — never "how do I compute this in-circuit?"**
Naming it matters because it is the rule that generated zkLLM's zkAttn and the
hint-based rsqrt, and it generates the MoE router argument above.

## F. The memory wall → streaming sumcheck (prove models bigger than RAM)

**ML fact:** frontier models exceed prover RAM — DeepProve projects >1 TB for
a 3B model and OOM'd at 128 GB on Gemma 3; ZKTorch needed 4 TB for GPT-J.
**Crypto mapping:** sumcheck is *streaming-friendly* — each round is one pass
over the data, and blocked/elastic variants (Gemini lineage) trade passes for
memory. Weights stream from disk; the prover never holds the model.

**"Prove a 70B model on a 64 GB box" is a capability that exists in zero
published systems**, and the barrier is engineering, not theory. For an open
project this is a headline nobody contests. **Status — UPGRADED by the mine:
integration, not campaign.** Sparrow (2024/1631, the Hobbit authors) is a
space-efficient sumcheck for *data-parallel* circuits — mappings D and F in
one paper — measuring **3.2–28.7× less prover space than Gemini** and, on a
400 MB dataset, **prover space 1.4× the native computation**. Theory floor:
2021/358 (Block et al.) and 2025/1473 (optimality).

## G. Proof-aware quantization — the dual of everything we tried

**ML fact:** integer-only inference exists (I-BERT: integer polynomial
approximations of GELU/softmax/LN co-designed for int-only hardware), and QAT
routinely retrains models into constrained formats at ~no quality loss.
**Crypto mapping:** stop adapting the proof to the model's format; adapt the
model to the proof's native arithmetic. Quantization-aware training whose
target is *field-native ops* — everything exact by construction, no
requantization relation at all, §5's zero-slack property free.

zkPyTorch's M61 co-design is a half-step; I-BERT's approximations port to
fields directly. Requires touching training, so it is for open-weight models —
which is our audience anyway. **Status: one sentence of it in the log
(zkPyTorch); the full idea — "train the model to be the circuit" — is in
nobody's paper.**

## H. Small structural freebies

- **RoPE is nearly free**: block-diagonal 2×2 rotations with *static*
  per-position constants — four multiplies against committed constants per
  pair. No table, no approximation. Nobody prices it because it's negligible —
  worth one line in a spec so nobody "optimizes" it.
- **Global table registry**: nonlinearity tables are model-independent public
  constants. Commit the canonical exp/GELU/rsqrt tables *once for the
  ecosystem*; every verifier hardcodes the roots. Composes with Lean-verified
  table contents (the moat item).
- **Embedding = row-select** is already a lookup; vocab-sized tables are the
  same LogUp machinery.

## Ranking against what we hold

By (leverage × our-asset alignment):

1. **A. Binius/small-value commitment** — attacks the proven cost floor, and
   the substrate is *already formalized in our tree*.
2. **F. Streaming prover** — uncontested capability, pure engineering.
3. **D. Layer-uniform sumcheck** — big constant, clean theory, unexploited.
4. **B. LoRA deltas + registry** — practical surface + the registry we already
   wanted for Hollow-LLM.
5. **C. MoE router binding** — frontier-architecture relevance + soundness gap
   nobody has closed.
6. **G. Proof-aware QAT** — deepest long-term, needs training runs.
7. **E** as the stated design rule; **H** as spec lines.

## Prior-art sweep (Kagi, 2026-08-12) — status per mapping

Papers pulled to `~/paperbin/`; mirror now covers 2024–2025 fully and 2026
through ~May.

| mapping | status | what the sweep found |
|---|---|---|
| **A. Binius × ML** | **unclaimed** | Only Binius-internal work (a 2026 MDPI Hybrid-Commit paper on PCS engineering). Nothing connects small-value commitment to ML inference. |
| **B. LoRA × ZK** | **claimed for FINE-TUNING; narrow to inference** | `verilora-ndss26.pdf` (NDSS 2026 — "first framework to integrate LoRA fine-tuning with ZKPs"), `zk-lora-verification.pdf` (2501.13965), `smdp-model-updates.pdf` (2604.04738 — succinct model-difference proofs). All prove the *training/update* side. Prove-base-once-plus-thin-adapter at **inference**, and the registry link, appear open — but every claim must now cite these. |
| **C. MoE router binding** | ~~unclaimed~~ **⚑ REFUTED 2026-08-13** | ~~No verifiable-MoE hit at all; every published system proves dense models.~~ **FALSE.** ZK-DeepSeek (2511.19902) + 2606.05433 OP-10, **both already in `~/paperbin/` when this row was written**. The first-2-page cache cannot see a §4.3. See `notes/moe-router-binding.md` §7 for the corrected gap. |
| **D. layer-fold sumcheck** | primitive known, application unclaimed | Data-parallel GKR sumcheck is in the literature (`collab-zksnark-dataparallel.pdf`, eprint 2024/143; Thaler '13). Nobody folds transformer layers into one hypercube. |
| **F. streaming LLM prover** | **substrate exists — read Hobbit first** | `hobbit-space-efficient.pdf` (USENIX Sec'25): space-efficient zkSNARK with **optimal prover time** — exactly the primitive; plus `gemini-elastic.pdf` and `sumcheck-speedup-2026-587.pdf`. The LLM-scale application (weights streamed from disk, 70B on 64 GB) remains unclaimed. Hobbit may change F from "engineering campaign" to "integration." |
| **G. proof-aware QAT** | unclaimed as stated | ZEN's quantization-oriented optimizations (survey 2502.18535) are post-hoc handling, not training-into-the-circuit. LLM-QAT/ZeroQAT are pure ML. "Train the model to be the circuit" is in nobody's paper. |
| **bubble (fusion)** | **close-adjacent — check three sources** | `zkcomposer.pdf` (2607.08095, decomposing proof construction to scale zkML), FluxZK (ACM, GPU kernel fusion *within* proving: memory-access fusion, compute-transfer pipelining), and 2606.05433 mentions a concurrent-GPU-stream design. None clearly fuses proving with the *inference* kernel to ride its weight traffic — but the distance is one idea, not ten. Read before claiming. |

Net effect on the ranking: **A and C are the clean unclaimed ones.** F gets
*easier* (Hobbit is the substrate) but less novel as a paper claim. B narrows
to inference + registry. The bubble needs a careful read of three adjacent
works before anyone says "nobody has costed that kernel" again — the sweep
already found the sentence weakening.

None of these is a format. That is the point.
