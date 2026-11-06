# Codex (gpt-6-astra) blind proposal, and how it compares with this lane's design

2026-11-06. Run before this lane formed a view: `codex exec -m gpt-6-astra --sandbox read-only` from
/Users/ember/dev/zkml-research, prompt in section 3 (it named the sources and the question; it carried no
design preference). 254,692 tokens. Its final answer is reproduced in section 4 verbatim, citations included;
its file links point at its own reading.

## 1. Where we agree (reached independently)

| point | Codex | this lane |
|---|---|---|
| Core change | "separate the field used to store and encode witnesses from the field used to obtain soundness": packed binary symbols, wide challenges | same: commit at the data's width, Tower256 challenges via ring switching (design c) |
| Starting point | packed additive FRI/BaseFold on the existing Tower256 spine (its rank 2) | same (c is that) |
| Twiddles | small subfield, GF(2^32): 8x fewer bit-MACs per fixed multiply | GF(2^16) = T_4: 16x; built and measured (kernels/) |
| Aggregation | batch first, aggregate at window/epoch boundaries, no per-leaf recursion | same; the model prices per-leaf recursion at 37-50x a leaf |
| Tensor GF(2) | unfused T4 path loses (MMA.md section 9); require end-to-end wins | same; dense-matmul codes lose to SIMT on subfield twiddles [MODEL] |
| Dense arithmetic | BabyBear boundary-only sumcheck, BabyBear^8 challenges | same (DESIGNS section 4) |
| Dark learning | keep the protocol; native ZKPoPK first | same |
| Brakedown / Blaze | not the default; Blaze's bad-code term 2^-27..2^-41 is unacceptable unaccounted | same ranking (d below c) for a different reason: cSHAKE binding in a prime field |

## 2. Where we differ, and what each side changed

1. **Internal hash.** Codex recommends BLAKE3-256 for internal trees under a scoped ruling change. This lane's
   model gives BLAKE3 1.0-1.6x on a batched packed record and 2.7x only on per-leaf recursion, which batching
   removes. **This lane: defer** the ruling change until the packed prover measures its hash share. (Codex's own
   Amdahl arithmetic, 1.10-1.40x for a 3x hash, agrees with the small batched effect; the difference is that it
   weights recursion more.)
2. **Target PCS.** Codex's rank 1 is a recursive interleaved RS (Ligerito); this lane keeps BaseFold/FRI-Binius
   on the existing additive controllers as the target until Ligerito's named soundness assumptions are discharged
   (Codex says the same as a condition). No real difference in the first two migration steps.
3. **Hardware placement.** Codex dispatches binary encoding to GPUs/TPUs per target. This lane's measurement and
   model say the packed leaf prover is **CPU-first**: after packing, the hot operation is the extension-field
   multiply in the PIOP, which a CPU does in 22.9 ns (PCLMUL) and a GPU in 12,000+ int32-op equivalents. A 64-core
   box models at half an H100's time per record and a quarter of its cost. Codex did not price CPUs.
4. **Composed security budget (Codex's, adopted).** Codex argues that "100 bits" must be a composed budget (FS
   loss, query budget, obligations per horizon) and suggests ~192 elementary bits, 300 rate-1/4 queries. This lane
   adopted it as the reason c128 (GF(2^128) challenges) is a knob, not the default. The query count is ember's
   call; 300 queries doubles verifier hashing and proof bytes in every design and does not change the ranking.
5. **Host openings (Codex's, adopted).** The measured T4 wall at ell 20 is 223 of 362 ms Python openings; Codex
   computed that a 4-5x arithmetic speedup moves the wall only 1.24-1.26x. Adopted in RECOMMENDATION step order.
6. **Store-root binding (Codex's, adopted as a precondition).** "Matching the algorithm name is insufficient": the
   content tree that a packed proof's message subtree equals must BE the store's tree, framing and leaf width
   included. This lane's design makes that a store-format decision (RECOMMENDATION section 2).
7. **Dark learning (Codex's, flagged, not checked here):** the ZKPoPK is over a 255-bit field, not the 61-bit
   prime, and a 24-variable degree-2 sumcheck over one 61-bit field is 2^-55.4.

## 3. The prompt

You are a proof-system architect. Read these sources in this repo (and /Users/ember/dev/minidregg where named) and propose, from your own judgment, the best TOTAL-SYSTEM proof-system design for this project given the hardware we now understand. Do not just defend the current design.

Sources:
- notes/tensor-core-holography/ROTATION.md, F3-MODEL.md; notes/construction-search/mma_counts.py
- notes/accelerator-readiness/ (MMA.md, TOWER256.md esp section 8, runs/, RUNBOOK.md, VAST-LEDGER.md)
- notes/tpu-perf/ (STYLE.md, GROUNDING.md)
- notes/hw-optimality/ (whatever exists)
- docs/LEAF-PROVER-DECISION.md, docs/PROOF-SYSTEM-SPACE.md (and its space.py), docs/CERTIFICATES.md, docs/FLASHPROVE-AUDIT.md, docs/DARK-LEARNING-SCHEME-DECISION.md sections 13-20
- /Users/ember/dev/minidregg/docs/TOWER256-FRI-PROVER-WORK.md, /Users/ember/dev/minidregg/board/RULINGS.md, /Users/ember/dev/minidregg/Selvage/
- research/dark_learning_2026_11_06/, research/exact_recompute_2026_11_06/

Hardware facts (verify in sources): Blackwell has no 1-bit MMA; B300 INT8 is ~1/30 of FP8; T4 Tower256 table multiply measured 12,000-17,400 int32-op equivalents, bit-sliced 52,700; GPU Tower256 prover is arithmetic-bound (hash share 0.13-0.18); a tensor-core GF(2) path would cut arithmetic 4-5x, after which hashing is 30-43%. TPU: MXU INT8, VPU-bound NTT/sumcheck.

Workloads consuming proofs: automata/certificate leaves (binary-symbol hot spots), recursion/aggregation, commit-then-audit with exact recompute, streaming windows, call trees, dark learning (61-bit prime Ligero ZKPoPK).

Question: what leaf proof system, internal commitment hash, field(s), code, and recursion strategy give the highest end-to-end composed performance across T4, H100/B200, B300, and TPU v5e, at >=100 provable bits of soundness, while respecting that store roots must be cSHAKE256 and that a Lean verification stack exists (Selvage, ArkLib bridge)? Consider at least: Tower256 additive FRI; tensor-core GF(2) encoding; Ligero/Ligerito/tensor codes over binary fields; Brakedown/expander codes over small primes on tensor cores; BabyBear/KoalaBear sumcheck-heavy with boundary-only commitment; anything better. Give: your recommended design, a ranked list with rough numbers (show your arithmetic and tag which numbers come from the sources vs your estimates), the migration path, and the biggest risks. Be concrete and quantitative.

## 4. Codex's final answer (verbatim)

**I recommend a heterogeneous proof system, with packed binary proofs as the certificate and aggregation backbone.** Keep prime-field sumcheck for dense arithmetic, preserve the specialized dark-learning protocol, and use exact recomputation directly where the security contract is commit-then-audit.

The central architectural change is to **separate the field used to store and encode witnesses from the field used to obtain soundness**. Tower256 is a useful challenge field and existing verification substrate. It is an expensive default representation for every symbol and every encoding butterfly.

My target design is:

| Component | Recommendation |
|---|---|
| Certificate leaves | Binary constraints and lookups, packed into small binary-field symbols |
| Encoding | Deterministic Reed–Solomon over additive domains; initially packed additive FRI/BaseFold, ultimately recursive interleaved RS/Ligerito if its complete soundness bridge is discharged |
| Fields | GF(2)/GF(2⁸) for source symbols; GF(2³²) for packed encoding and eligible twiddles; GF(2²⁵⁶) for challenges |
| Dense arithmetic | Boundary-committed sumcheck over BabyBear, with BabyBear⁸ challenges |
| Dark learning | Retain its 61-bit arithmetic and separate 255-bit Ligero ZKPoPK; strengthen challenge/composition parameters |
| Internal commitment hash | BLAKE3-256, subject to a narrow change to the current hash ruling; retain cSHAKE256 during migration |
| Store roots | Exactly the existing cSHAKE256 construction, including framing, lengths, and tree structure |
| Recursion | Batch relations first; use binary aggregation at window/epoch boundaries; avoid recursively verifying every small leaf |
| Audit path | Commit to inputs, outputs, model and execution semantics; recompute selected executions exactly |

[HYPOTHESIS] This portfolio should outperform a universal Tower256-FRI design because it reduces work before accelerating it: fewer wide-field operations, fewer commitments, fewer recursive hash checks, and fewer computations unnecessarily converted into proofs. The available measurements do **not** establish a numerical end-to-end winner for this complete design yet.

Below, `[SOURCE]` denotes inspected source material, `[REPORTED]` denotes measurements recorded there, `[DERIVED]` denotes arithmetic from those inputs, and `[HYPOTHESIS]` denotes my proposed design or forecast.

**1. The hardware evidence changes the design—but does not yet establish the advertised tensor speedup.**

[SOURCE] The newer measurements supersede important conclusions in `F3-MODEL.md`. Its 718-operation bit-sliced multiplication assumption is refuted by the recorded T4 results. Consequently, its “hash-heavy Tower256” conclusion and rejection of byte-operand tensor approaches are no longer sound premises. The replacement measurements are approximately **12,000–17,400 int32-operation equivalents for table multiplication**, versus **52,700 for resident bit-slicing**. [TOWER256.md](/Users/ember/dev/zkml-research/notes/accelerator-readiness/TOWER256.md), [F3-MODEL.md](/Users/ember/dev/zkml-research/notes/tensor-core-holography/F3-MODEL.md)

[REPORTED] The T4 `ell=20` run gives the most useful present baseline:

| Component | Time |
|---|---:|
| Encoding | 86.80 ms |
| Merkle work | 14.07 ms |
| Folding | 6.91 ms |
| Device total | **107.78 ms** |
| Python opening construction | 223.38 ms |
| Complete measured wall time | **362.4 ms** |
| Four-thread CPU comparison | 1,782 ms |

The device prover is arithmetic-bound; hashing is approximately 13%. But the complete implementation also has a larger host-side opening bottleneck. A GPU arithmetic improvement alone does not fix that. [Recorded run](/Users/ember/dev/zkml-research/notes/accelerator-readiness/runs/accel-tower-dryrun-04/results.json)

[REPORTED] More importantly, the actual T4 tensor experiment currently **loses**:

- INT8 unpack/GEMM/repack: **22.6 ns per element**, including 6.6 ns GEMM.
- FP16 equivalent: **27–37 ns per element**.
- Table multiplication baseline: approximately **2.9–4.3 ns per element**.

The projected tensor advantage requires fused packing, multiplication, parity extraction, and storage. Materializing expanded bits in HBM defeats it. [MMA.md §9](/Users/ember/dev/zkml-research/notes/accelerator-readiness/MMA.md:187)

[SOURCE] Blackwell has no native `.b1` MMA. B300’s approximately 1:30 INT8:FP8 throughput ratio is documented, but the inspected project corpus does not contain a completed B300 prover benchmark establishing the corresponding application performance. The hardware-optimality corrections also matter: Blackwell bitwise throughput was overestimated in parts of the model, and float-to-int conversion is particularly expensive. [ROTATION.md](/Users/ember/dev/zkml-research/notes/tensor-core-holography/ROTATION.md), [NVIDIA arithmetic-throughput table](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html#arithmetic-instructions), [B300 throughput audit](https://arxiv.org/html/2608.11693v1)

[DERIVED] Applied to the measured T4 device baseline, a hypothetical arithmetic speedup gives:

\[
T_{\rm device}(s)=14.07+\frac{86.80+6.91}{s}\ {\rm ms}.
\]

| Arithmetic speedup | Device time | Device speedup | New hash share |
|---|---:|---:|---:|
| 4× | 37.50 ms | 2.87× | 37.5% |
| 5× | 32.81 ms | 3.29× | 42.9% |

That supports the approximately 40% hash-share forecast for this run. The broader statement “13–18% initially, 4–5× arithmetic improvement, then 30–43% hashing” is not a universally consistent range: combining its endpoints gives approximately **37–52%**.

[DERIVED] Keeping the measured host overhead unchanged, those device improvements reduce 362.4 ms only to approximately **292 or 287 ms**: **1.24–1.26× complete speedup**. Native batched openings are therefore a first-class optimization, alongside arithmetic.

For TPU, the evidence is weaker: the inspected work establishes compiler/layout behavior and models a VPU bottleneck; it does not establish measured v5e prover throughput. MXU INT8 throughput is not a substitute for benchmarking reductions, folding, hashing, and layout conversion. [TPU grounding](/Users/ember/dev/zkml-research/notes/tpu-perf/GROUNDING.md)

**2. My ranked design choices favor smaller representations and fewer commitments.**

This ranks architectural investments for the **whole workload portfolio**, rather than pretending one proof system wins every relation.

| Rank | Design | Quantitative case | Principal limitation |
|---|---|---|---|
| **1** | Packed binary constraints + recursive interleaved RS PCS | Potentially 8× cheaper small-subfield multiplication on wide values; much smaller initial codewords; binary hash verification | Complete instantiated soundness, ZK, and extraction remain unfinished |
| **2** | Packed additive FRI/BaseFold using the existing Tower256 verification spine | Closest migration path; retains deterministic RS structure and much existing Lean work | Repeated folding commitments and wide late-stage arithmetic |
| **3** | BabyBear sumcheck with boundary-only commitment | Strong fit for dense arithmetic; recorded H100 degree-2 sumcheck is 4.04 ms at \(2^{25}\) elements | Full protocol is much more expensive than its sumcheck kernel |
| **4** | Brakedown/expander-code prime-field system | Linear encoding and demonstrated GPU implementations | Distance/security parameters and irregular sparse operations; tensor TOPS alone do not price it |
| **5** | Uniform Tower256 additive FRI, with tensor acceleration | Existing measured baseline and formal investment; modeled device gains around 2–3× | Pays for wide-field encoding everywhere; current tensor prototype loses |
| **6** | Plain Ligero/tensor code as the universal leaf and recursion system | Useful specialized ZKPoPK and distributed-proving structure | Opening size and recursive verification make it a poor universal compression layer |

[HYPOTHESIS] **Rank 2 is the implementation starting point; rank 1 is the target architecture.** I would not discard the existing additive-FRI system while its proposed successor still has named security assumptions instead of discharged theorems.

The most important arithmetic is representation arithmetic.

[DERIVED] Consider one MiB of byte-valued data, before relation-specific expansion:

- One Tower256 element per byte, rate 1/4:
  \[
  2^{20}\cdot4\cdot32=128\ {\rm MiB}.
  \]
- Four bytes packed into each GF(2³²) symbol, rate 1/4:
  \[
  2^{18}\cdot4\cdot4=4\ {\rm MiB}.
  \]

That is **32× less initial codeword storage** in this illustrative comparison—not a 32× prover-speed claim. Random linear combinations eventually require extension-field values, and packing needs a proved relation to the original bits.

[DERIVED] A fixed multiplication in GF(2²⁵⁶), represented as a binary matrix, costs \(256^2=65,536\) bit-MACs. Multiplication by an element of a GF(2³²) subfield can operate on eight 32-bit coordinates:

\[
8\cdot32^2=8,192\ \text{bit-MACs},
\]

an **8× reduction**. A genuinely 32-bit encoded value needs only 1,024 bit-MACs.

[HYPOTHESIS] Therefore the first tensor-oriented algebraic change should be to place the encoding domain and eligible twiddles inside a small subfield, while retaining wide challenges. This requires proving the actual basis, offset, and twiddle closure properties. It is not permission to move soundness challenges into GF(2³²). This design lever already appears in [F3-MODEL.md](/Users/ember/dev/zkml-research/notes/tensor-core-holography/F3-MODEL.md).

For certificate relations, I would use:

- Direct Boolean constraints for small binary automata.
- Commit-once lookup arguments for substantial transition tables.
- Binary-friendly constraints for the required cSHAKE computations.
- A sumcheck/zerocheck layer connecting these constraints to the packed RS commitment.

[SOURCE] The current bare low-degree test does not supply that complete certificate argument. Likewise, `LigeritoInterleaved.lean` proves useful column-metric correspondence, but contains named assumptions for important remaining soundness components. Neither should be advertised as a complete certificate ZK argument merely because its encoding or verifier compiles. [Leaf decision](/Users/ember/dev/zkml-research/docs/LEAF-PROVER-DECISION.md), [LigeritoInterleaved.lean](/Users/ember/dev/minidregg/Selvage/LigeritoInterleaved.lean)

For prime-field arithmetic, the biggest lever is **boundary-only commitment**, not changing BabyBear to KoalaBear.

[SOURCE] TensorZKP reports **215.28 ms end-to-end** on H100 at \(2^{25}\) gates, versus **4.04 ms** for the degree-2 sumcheck and **11.58 ms** for encoding; its permutation check accounts for roughly **134 ms**. Accelerating the 4 ms kernel cannot deliver a comparable improvement to the whole 215 ms protocol. :codex-file-citation{path="/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/1250.pdf" purpose="source"}

[HYPOTHESIS] Keep BabyBear for this branch because it fits existing work and offers adequate domain capacity. KoalaBear can be a backend option when measured reduction costs justify it; the evidence does not justify a system-wide field migration.

For “anything better,” Blaze-style repeat-accumulate codes deserve investigation, but not the default slot.

[SOURCE] The inspected Blaze parameters include a bad-code probability around \(2^{-27.4}\), or approximately \(2^{-41.5}\) with much more expensive generation. Those are not acceptable as unaccounted terms in a 100-bit total-system claim. This is a rejection of those parameterizations for this requirement, not of the code family. :codex-file-citation{path="/Users/ember/dev/gh/forks/IACR-eprint-mirror/2024/1609.pdf" purpose="source"}

**3. Use different hardware backends without changing the statement being proved.**

[HYPOTHESIS] I would implement the following dispatch:

| Hardware | Binary encoding | Prime arithmetic | Main concern |
|---|---|---|---|
| T4 | Table fallback; fused small-field tensor kernels only when they win end-to-end | INT8 limb kernels; batch aggressively | Launch overhead, packing, host openings |
| H100 | Benchmark native binary operations and INT8 small-field transforms | INT8 tensor kernels | HBM traffic and irregular protocol stages |
| B200 | Exact FP tensor encoding where established; table fallback | Benchmark INT8 against FP16/FP8 | Actual bandwidth and accumulator behavior |
| B300 | Exact FP tensor path, not an INT8-first design | FP16 byte limbs are the leading candidate | Conversion throughput and unverified exactness assumptions |
| TPU v5e | MXU INT8 for regular encoding; fused VPU work | MXU products with fused VPU reductions | VPU/layout costs; no measured full-prover result yet |

[SOURCE] The arithmetic models put a \(2^{25}\)-element BabyBear⁸ degree-2 sumcheck at approximately **44 ms T4, 4 ms H100, and 2 ms B200/B300**. The roughly **17.5 ms TPU estimate omits important VPU limitations**. These are kernel estimates, not certificate or recursive proof times. [Hardware-optimality analysis](/Users/ember/dev/zkml-research/notes/hw-optimality/OPTIMAL.md)

[DERIVED] Re-evaluating the Tower256 proxy with the documented Blackwell SIMT correction gives this sensitivity table:

| Hardware | Table-arithmetic proxy | Tensor-arithmetic proxy | Ratio |
|---|---:|---:|---:|
| T4 | 41.9 ms | 17.4 ms | 2.4× |
| H100 | 10.2 ms | 3.47 ms | 2.9× |
| B200 | 9.48 ms | 2.81 ms | 3.4× |
| B300 | 8.77 ms | 2.60 ms | 3.4× |

These are **one-column model outputs**, using transferred operation costs—not measurements or complete proof forecasts. The T4 model’s 41.9 ms versus the measured 107.8 ms device result demonstrates why I would not budget a product from this table. [Model](/Users/ember/dev/zkml-research/notes/construction-search/mma_counts.py)

**4. Change the internal hash, but keep the store-root contract exact.**

[HYPOTHESIS] I recommend **BLAKE3-256 for internal Merkle commitments**, retaining cSHAKE256 for store roots and initially for the Fiat–Shamir transcript.

This requires a narrow revision to the present ruling restricting BLAKE3 use. It is a proposed design change, not something the current ruling already permits.

The reason is both native hashing and recursive verification cost.

[SOURCE] The inspected BinarySpartan paper gives approximate binary constraint counts per compression/permutation:

| Primitive | Binary constraints |
|---|---:|
| BLAKE3 | 14,000 |
| SHA-256 | 30,376 |
| Keccak-f | 38,400 |

Thus the nominal Keccak/BLAKE3 ratio is **2.74×**, before accounting for different framing and block counts. I found throughput figures in repository summaries that differ from the local paper version, so I would use these structural counts—not mix the conflicting throughput figures into a GPU forecast. :codex-file-citation{path="/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/1656.pdf" purpose="source"}

[DERIVED] Even a **3× faster native hash** improves a prover by only

\[
S=\frac{1}{1-h+h/3}.
\]

That is **1.10–1.14×** when hashing is 13–18%, and **1.25–1.40×** when hashing is 30–43%. The larger benefit is often in recursion.

[SOURCE] The updated pair-opening/cached-prefix calculation gives approximately **35,757 Keccak permutations** for an `ell=20`, 148-query child verifier. [Recursion count analysis](/Users/ember/dev/zkml-research/notes/holography-accumulation-verdict.md)

[DERIVED] At the preceding binary constraint counts:

\[
35,757\cdot38,400 \approx 1.37\ \text{billion constraints}.
\]

Using 14,000 as a first-order replacement cost gives approximately **501 million constraints**, before correcting the hash-call count for BLAKE3 framing.

That is still expensive. A hash change helps; eliminating unnecessary recursive verifications helps more.

[HYPOTHESIS] I would not introduce Vision/Twill or another binary algebraic hash as the default merely to obtain cheaper recursion. That would add a cryptanalytic and formalization project to an already unfinished stack. Poseidon2 is attractive inside prime arithmetic, but a universal prime-field wrapper would make binary certificate and cSHAKE verification expensive.

Finally, an internally committed proof must establish the **actual store root**. Matching the algorithm name is insufficient: a cube-tree commitment and the store’s framed object/tree construction need not have the same root. Bind lengths, object types, policy/table versions, model identifiers, and execution semantics explicitly. [Certificates](/Users/ember/dev/zkml-research/docs/CERTIFICATES.md)

**5. Batch first; recurse only where compression is worth its cost.**

[HYPOTHESIS] My recursion strategy is:

1. Prove a batch of related events or a streaming window as one relation.
2. Carry authenticated boundary state between windows.
3. Aggregate at epoch or substantial call-tree boundaries.
4. Produce a terminal succinct proof when a consumer actually needs it.

Start by benchmarking batches of **64–256 events**. Those are engineering starting points, not cryptographic constants.

For automata, the boundary includes the automaton state. For nested execution, it includes the appropriate call/return state and pending obligations. For streaming, it includes position, length, predecessor commitment, and semantic version. An accumulator must not erase unproved obligations merely because it has a compact root.

[SOURCE] The holography audit does **not** establish cheap accumulation of the current Merkle PCS. Its useful constructions require an accumulatable PCS or fall back to child verification. Likewise, an algebraic accumulator theorem is not a cost theorem or a complete knowledge-soundness theorem. [Holography verdict](/Users/ember/dev/zkml-research/notes/holography-accumulation-verdict.md)

[HYPOTHESIS] Keep transparent binary recursion as the initial terminal strategy. Consider a separate pairing-based terminal wrapper only if a concrete consumer needs very small proofs and verification, and its setup/security/formalization tradeoff is justified. It should not become a prerequisite for the streaming pipeline.

**6. “At least 100 bits” must be a composed security budget.**

[SOURCE] The present artifacts do not establish a complete 100-bit theorem for the proposed heterogeneous system. In particular:

- 148 FRI queries price a sampling term.
- 309 Ligero columns price another sampling term.
- Neither automatically prices Fiat–Shamir loss, field challenges, code failure, extraction, hashing, and repeated composition.
- The FlashProve audit records a reduction below 59 bits at its stated oracle budget. [FlashProve audit](/Users/ember/dev/zkml-research/docs/FLASHPROVE-AUDIT.md)

[DERIVED] For the RS unique-decoding query factor \((1+\rho)/2\), rate 1/4 gives \(0.625^q\). For a \(0.75^t\) sampling term:

| Target for this term alone | RS: \(0.625^q\) | \(0.75^t\) |
|---|---:|---:|
| 100 bits | 148 | 241 |
| 128 bits | 189 | 309 |
| 192 bits | 284 | 463 |

This explains why current query counts cannot simply be labeled “100-bit composed security.”

[HYPOTHESIS] I would adopt an explicit initial budget such as:

- At most \(2^{20}\) relevant proof obligations per security horizon.
- A stated classical random-oracle query budget, illustratively \(2^{64}\).
- Explicit bounds for every reduction and composition term.
- Approximately **192 bits or more in elementary algebraic/sampling bounds** before those losses.

[DERIVED] Illustratively,

\[
2^{20}\cdot2^{64}\cdot2^8\cdot2^{-192}=2^{-100}.
\]

This is a budget example, not a replacement for the actual theorem. Convenient starting parameters would be approximately **300 rate-1/4 RS queries** and **480 columns for a \(0.75^t\) term**, providing approximately 203 and 199 bits respectively before other losses.

Use **GF(2²⁵⁶)** and **BabyBear⁸** challenges to leave room for degree and composition losses. A 128-bit field is not automatically sufficient: even the simple expression

\[
16\cdot2^{19}/2^{128}=2^{-105}
\]

leaves almost no room for the rest of the system.

[SOURCE] The ArkLib unique-decoding bridge is valuable precisely because it connects a concrete RS theorem to the proximity/correlated-agreement assumptions. It does not discharge the entire protocol by itself. The requested Tower256 work document was absent from the named checkout; I located it in the `md-arklib` worktree. [Tower256 work](/Users/ember/dev/md-arklib/docs/TOWER256-FRI-PROVER-WORK.md), [UniqueDecoding.lean](/Users/ember/dev/md-arklib/bridges/arklib-ud/SelvageArkLib/UniqueDecoding.lean)

[HYPOTHESIS] Extend that stack statement-first: packed representation → encoding → proximity theorem → relation check → transcript → shared-adversary composition → concrete budget. The strict heterogeneous-composition definitions are the relevant target; a theorem that merely sums nonnegative error labels is insufficient. [HeteroCompositionErrorBound.lean](/Users/ember/dev/minidregg/Selvage/HeteroCompositionErrorBound.lean)

These recommendations assume **classical** 100-bit security under the stated cryptographic assumptions. If the requirement includes 100-bit generic quantum collision resistance, 256-bit digests and the current classical analysis require reconsideration.

**7. Preserve the specialized dark-learning and exact-recompute paths.**

There is an important correction to the question’s description.

[SOURCE] The dark-learning spine and middle use a 61-bit prime, but the inspected **Ligero ZKPoPK uses a 255-bit proof field**. Its integer quotient/no-wrap argument depends on that distinction. Replacing its proof field with BabyBear or a single 61-bit prime would invalidate the argument unless carry/CRT constraints replaced it. [zkpopk_ligero.py](/Users/ember/dev/zkml-research/research/dark_learning_2026_11_06/zkpopk_ligero.py)

[REPORTED] The recorded full forward-batch ZKPoPK has approximately:

- **4.83 MB proof size**;
- **416.6 seconds Python proving**;
- **216.7 seconds Python verification**.

Meanwhile, the latest dark-learning ledger has approximately **1.893 Gbit** of spine-plus-middle proof traffic, and total protocol communication on the order of **a terabit**. Optimizing this ZKPoPK alone will not transform total communication, although native implementation could substantially improve latency. [Dark-learning decision §§13–20](/Users/ember/dev/zkml-research/docs/DARK-LEARNING-SCHEME-DECISION.md), [Experiment directory](/Users/ember/dev/zkml-research/research/dark_learning_2026_11_06/)

[HYPOTHESIS] My priorities here are:

1. Native implementation of the existing 255-bit ZKPoPK.
2. Stronger challenge/composition accounting for the 61-bit spine and middle.
3. Preserve the low-rank verifier structure that avoids quadratic MPC multiplication costs.
4. Only then investigate packed binary digits or CRT proof fields with an explicit integer-linking theorem.

[DERIVED] A degree-2 sumcheck over 24 variables using one 61-bit challenge field has the familiar bound

\[
48/2^{61}\approx2^{-55.4}.
\]

Increasing Ligero columns does not repair that separate term. Extension-field challenges—such as a suitable degree-four extension—or properly analyzed independent repetition are needed where that bound applies.

For exact recomputation:

[SOURCE] The experiments support deterministic integer execution relative to pinned semantics. They do not prove that arbitrary floating-point backends execute the same function. The T4 experiment is a correctness harness, and TPU execution remains unverified in the inspected evidence. [Exact-recompute research](/Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/)

[HYPOTHESIS] Commit to the model, inputs, outputs, randomness where applicable, and exact arithmetic/table semantics. Recompute selected executions directly. Avoid committing every activation unless a specific dispute or partial-check protocol needs those commitments.

An audited receipt and a fully proved receipt must remain distinct types.

[DERIVED] With a 1% audit rate, an individual dishonest execution can escape auditing with probability approximately **99%**. Exact recomputation makes the selected audit decisive; it does not turn sampling into 100-bit per-execution correctness. A public consumer needs either its own replay, an explicitly trusted audit service, or a proof of the recomputation.

**8. Migration order and the risks that could change my recommendation.**

[HYPOTHESIS] I would execute the migration in this order:

1. **Close the statement and security gaps.** Bind exact store semantics, lengths, policy/model versions, window boundaries, and challenge budgets. Establish what each receipt actually guarantees.
2. **Make the existing baseline representative.** Native batched openings, full certificate relations, and complete wall-time accounting. Retain current table multiplication as the reference.
3. **Introduce packed symbols and small-subfield twiddles.** Prove their relationship to the existing Tower256 statement before replacing the PCS.
4. **Build fused hardware backends.** Require bit-exact output and complete encoding/proving improvement; GEMM-only wins do not qualify.
5. **Prototype recursive interleaved RS against optimized additive FRI.** Compare identical relations, soundness budgets, proof sizes, verifier costs, and peak memory. Promote it only after the missing security bridge is discharged.
6. **Change the internal hash under a scoped ruling revision.** Measure native and recursive benefits with actual framing.
7. **Integrate window batching and terminal aggregation.** Add the dense-arithmetic branch and native dark-learning prover through explicit composition interfaces.

The largest risks are concrete:

- **Packing and register pressure:** already demonstrated capable of erasing tensor gains.
- **Incomplete security connections:** the best-looking encoding is not necessarily a proved argument of knowledge.
- **Recursive hashing:** even cheaper hashes leave hundreds of millions of constraints in naïve child verification.
- **Hidden-policy lookups:** per-transition Merkle authentication can dominate an otherwise tiny automaton.
- **Cross-field semantics:** careless packing or CRT substitution can prove a different statement.
- **TPU uncertainty:** compiler success and peak MXU arithmetic do not establish prover performance.
- **ZK state management:** masks, retry accounting, and transcript binding remain essential in the distributed learning protocol.

**My architectural choice is packed binary RS proofs with wide challenges, batched binary aggregation, and specialized arithmetic branches.** Tower256 additive FRI should remain the migration backbone and reference implementation. The highest-value change is to stop making it perform wide arithmetic—and recursive commitment verification—where the workload does not require either.
