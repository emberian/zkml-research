# `zkTransformer` Primary-Source Cross-Check & `catgrad` / `gptoss-int` Compiler-Seam Evaluation

**Date:** 2026-11-20  
**Lane:** `catgrad-lit-seam`  
**Scope:** (1) Primary-source verification of `zkTransformer` (`arXiv:2603.19609v1`, UIUC Kang Lab) completeness claims, prior art on `EinSumcheck` and `StructuredExp`, `Hollow-LLM` weight-registry exposure, and `Softmax`/`Sigmoid`/`RMSNorm` tolerance soundness across `~/paperbin/`, the local IACR ePrint mirror (`/Users/ember/dev/gh/forks/IACR-eprint-mirror/`), and upstream source repositories; (2) Concrete compiler-seam evaluation mapping `catgrad` (GPT-2) and `gptoss-int v0` (`gpt-oss-20b` MoE+GQA) onto `EinSumcheck`, including a native MXFP4 3-operand `EinSumcheck` (`ikb,jkb,jk -> ij`) construction.  
**Reproducible Verification Script:** [verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py) (`[EXECUTED]`).

---

## 0. Executive Summary of Findings

1. **`zkGPT` & `zkLLM` Completeness Bugs Verified at Source (`[READ]`, `[EXECUTED]`):**
   - **`zkGPT` Eq. (8)** (`~/paperbin/zkgpt-usenix25.txt:678-691`, §6.2; `zkgpt-eprint2025.txt:707-740`): Substitutes batch randomness $r' \in \mathbb{F}^{\log M}$ directly into both $\tilde{A}(r' \| r'_x \| c)$ and $\tilde{B}(r' \| c \| r'_y)$ without summing over $b \in \{0,1\}^{\log M}$ against $\widetilde{\text{eq}}(r', b)$. Because the RHS has degree 2 in $r'$ while the LHS $\tilde{V}_1$ is multilinear (degree 1), honest provers fail verification with probability $1 - O(\log M / |\mathbb{F}|)$.
   - **`zkLLM` `proof.cu`** (`jvhs0706/zkllm-ccs2024@993311e`, `proof.cu:67-107`): `hadamard_product_sumcheck` (`Fr_hp_sc`), actively invoked by `rmsnorm.cu:47` on `Y = g_inv_rms_ * X`, evaluates quadratic slice coefficients `out0(u_)`, `out1(u_)`, `out2(u_)` without multiplying by $\widetilde{\text{eq}}(u_0, T)$, so $g_1(0) + g_1(1) \neq \tilde{Y}(u)$ in every run; `rmsnorm.cu:47` only exits cleanly because it discards the returned proof vector without checking it. Meanwhile, `multi_hadamard_sumchecks` (`proof.cu:191-241`, called in `zksoftmax.cu:186`) correctly multiplies by `Polynomial::eq(u.back())`, and `ffn.cu:73` (`down_in = swiglu_out * up_out_`) omits a Hadamard proof call altogether.

2. **Prior Art on Decomposed & Range-Reduced `exp` (`[READ]`):**
   - **`Rank1ProdExp` (base-$b$ / $2^d$ additive split $\exp(a+b) = \exp(a)\exp(b)$ with unrescaled product) is established prior art across four zkML works:** `zkLLM` (CCS '24, §2 Eq. 3 & §5.1 Eqs. 19–26), `Hao et al.` (USENIX Security '24 / `ePrint 2025/507`, §5.1 Fig. 12 `Π_Exp`), `zkAgent` (`ePrint 2026/199`, §3.3), and **deployed `Jolt Atlas` + `Jo` (`ePrint 2026/1390`, §8.5 `EXP-5` & §9 Propositions 2–3)**, where Jo explicitly proves the rank-1 outer-product bipartition ($\rho = 1$, $\sigma_2/\sigma_1 = 1.6 \times 10^{-15}$ at $r=16$) AND proves via the **Separation Principle** (Proposition 5) that splitting an $r$-bit lookup into $c$ sub-lookups shrinks only the per-proof table term $a(r)$ while multiplying the dominant per-lookup address commitment term $b \cdot m$ by $c\times$.
   - **`StructuredExp` ($\ln 2$ Cody–Waite range reduction + Shout structured $2^{-k}$ MLE + Horner Taylor):** Base-2 range reduction $\exp(x) = 2^{\lfloor x/\ln 2 \rfloor} \cdot 2^{\{x/\ln 2\}}$ with polynomial/algebraic evaluation on $[0,1]$ in ZK is prior art in **Kurik & Laud (`ePrint 2024/859`, WPES '24, §4.2–4.3)** (using integer bit-decomposition for $2^{\lfloor x \rfloor}$). Pairing integer range reduction $q = -k\lfloor 2^s \ln 2 \rceil + r$ specifically with Shout's multiplicatively structured power-of-2 table MLE $\tilde{T}_{\text{pow}}(y) = \prod_i ((2^{2^{i-1}}-1)y_i + 1)$ (`zkTransformer` §4.4) was **not** found in prior zkML papers across our searched corpora.

3. **Prior Art on `EinSumcheck` (`[READ]`):**
   - Prior zkML protocols (`Power circuits` `2023/1611`, `zkPyTorch` `2025/535`, `ZKTorch` `2507.07031`, `TensorSwitch` `2025/2065`, `DeepProve` `2026/1112`, `Jolt Atlas` `2602.17452`) handled individual special cases (2D matmul [Thaler13], Hadamard product with $\widetilde{\text{eq}}$, manual head-batched MHA with power-of-2 padding in `DeepProve` §4.3.5, sparse one-hot embedding matmul $Y = H_x \cdot T$ in `DeepProve` §4.3.1 / `zkGPT`). None of those papers formulated a general arbitrary-string Einsum compiler partitioning $(\mathcal{I}_{\text{free}} = F_1 \sqcup F_{\ge 2}, \mathcal{I}_{\text{sum}})$ with $\widetilde{\text{eq}}$ restricted strictly to $F_{\ge 2}$ and an unequal-variable-count partial-sumcheck schedule (`zkTransformer` §4.2–4.3).

4. **`Hollow-LLM` Exposure & Critical `Softmax`/`Sigmoid` Soundness Bugs in `zkTransformer` (`[READ]`, `[SOURCE]`):**
   - **`Hollow-LLM` unclosed:** Private weight commitments $\{W^{(\ell)}\}$ without a public weight registry leave `zkTransformer` fully exposed to `Hollow-LLM` (`arXiv:2607.28884`) Attacks A (zero-work residual layers) and B ($m\times$ width replication with LayerNorm/RMSNorm invariance + $1/m$ collapse).
   - **Zamir vulnerability in paper + missing/broken constraints in `main`:** Paper §2.2 Eq. (1) (*"sum to approximately 1"*) and `RMSReciprocal` (`|z - 32768| <= 512`, $\pm 1.56\%$) create per-row $\delta$-tolerance slack directly vulnerable to **Zamir's Theorem 1** (`arXiv:2602.15756`; `VERDICTS.md` §1). Worse, in `uiuc-kang-lab/zkTransformer` `main`:
     1. `gpt2_attention` (`src/dag/gpt2.rs:133-139`) and `llama_attention` (`src/dag/llama.rs:439-443`) **omit the Softmax row-sum check completely** (`// Soundness check (sum ≈ SF) belongs in a later pass.`, with no pass implementing it).
     2. `SoftmaxConst` (`src/basicblock/llama.rs:239`) allocates a **4D witness tensor `[B, H, S, S]` instead of `[B, H, S, 1]`**, giving the prover an unconstrained independent scalar per `(b, h, s, t)` entry — so even adding a row-sum check later would allow forging **any** probability distribution independent of $QK^\top$.
     3. `SigmoidConst` (`src/dag/builder.rs:300-305`, `src/basicblock/llama.rs:318-389`) is **completely unconstrained** (`verify -> true`), leaving every GELU (`gpt2_mlp`) and SiLU (`llama_mlp`) unsound.
     By contrast, `gptoss-int v0` (`layer.py:169-184, 217-225`) enforces **exact Euclidean integer division** ($q \cdot d + r = n, 0 \le r < d$), achieving zero tolerance slack ($\delta = 0$).

5. **Compiler Seam & Native MXFP4 3-Operand `EinSumcheck` (`ikb,jkb,jk -> ij`) (`[DERIVED]`, `[EXECUTED]`, `[OURS]`):**
   - `minidregg`'s `Theory/ZkmlTensorOps.lean` (`TOp.arithmetic`, `arith_transport`) and `Theory/ZkmlMatmulSum.lean` (`foldl_add_eq_listSum`, `SatExample.sat_bridge_fails`) formally pin why shape/ring islands fuse cleanly into `EinSumcheck` while `rq`/`rq0`/`rq2`, `clamp`, `norm_int`, `exp_table`/`glu_table`, and MoE `route` (`topk`) form mandatory commitment boundaries.
   - **Native MXFP4 without weight dequantization:** Expressing exact MXFP4 integer block-scaled matmul before row-shift `rq2` as the 3-operand contraction $D[i,j] = \sum_{k \in [K_{\text{blk}}]} \sum_{b \in [32]} X[i,k,b] \cdot Q[j,k,b] \cdot S[j,k]$ (`ikb,jkb,jk -> ij`) requires $\widetilde{\text{eq}}(r_j, j)$ on $j \in F_{\ge 2}$ only. Under elimination order $j \to k \to b$, round degrees are **$(3, \dots, 3)$ on $j$-rounds, $(3, \dots, 3)$ on $k$-rounds, and $(2, \dots, 2)$ on the 5 intra-block $b$-rounds — never degree 4**, avoiding a 2-stage split's redundant double sumcheck over $k$. Across `gpt-oss-20b`'s 19.11B MoE weights, native MXFP4 cuts committed weight bits by **`5.49–6.82×`** (`4.25–5.28` vs `29.0` bits/weight; `10.15 GB` vs `69.28 GB`) and committed field elements by **`1.94×`** (`1.03125` vs `2.0` felts/weight against `model.py`'s `(Wh, Wl)` 2-limb representation).

---

## 1. Primary-Source Verification of `zkTransformer`'s Completeness & Einsum Claims

### 1.1 `zkGPT` Batched MatMul Completeness Bug (`[READ]`, `[EXECUTED]`)

In `zkTransformer` §1 (footnote 1) and §3 (`zkTransformer.txt:80-86, 209-216`), the authors report that `zkGPT` [58] suffers a completeness failure in batched matrix multiplication because multiplying two multilinear extensions at a shared random batch challenge produces a degree-2 polynomial rather than a multilinear one.

**Verification at source (`[READ]`):** In `~/paperbin/zkgpt-usenix25.txt:678-691` (§6.2 *Combining Multiple Matrix Multiplications*, Eq. 8; identically in `~/paperbin/zkgpt-eprint2025.txt:707-740`), `zkGPT` stacks $M$ matmuls $C_\ell = A_\ell \times B_\ell$ ($\ell \in [1, M]$) into 3D tensors $A \in \mathbb{F}^{M \times n \times m}$, $B \in \mathbb{F}^{M \times m \times k}$, and output $V_1 \in \mathbb{F}^{M \times n \times k}$. Given two verifier evaluation points $r_1 = (r' \| r'_x \| r'_y)$ and $r_2 = (r'' \| r''_x \| r''_y)$ with $r', r'' \in \mathbb{F}^{\log M}$, `zkGPT` Eq. (8) asserts:

$$\alpha \tilde{V}_1(r_1) + \beta \tilde{V}_1(r_2) \stackrel{\text{Eq. (8)}}{=} \sum_{c \in \{0,1\}^{\log m}} \left( \alpha \tilde{A}(r' \| r'_x \| c)\tilde{B}(r' \| c \| r'_y) + \beta \tilde{A}(r'' \| r''_x \| c)\tilde{B}(r'' \| c \| r''_y) \right).$$

**Exact algebraic defect (`[DERIVED]`, `[EXECUTED]`):** On the Boolean hypercube $b \in \{0,1\}^{\log M}$, $V_1(b, x, y) = \sum_{c \in \{0,1\}^{\log m}} A(b, x, c) B(b, c, y)$ holds pointwise. However, the unique multilinear extension $\tilde{V}_1(r', r'_x, r'_y)$ has individual degree **1** in each coordinate of $r'$, whereas $\sum_c \tilde{A}(r', r'_x, c)\tilde{B}(r', c, r'_y)$ has individual degree **2** in each coordinate of $r'$! The two polynomials agree on $r' \in \{0,1\}^{\log M}$ but disagree at random $r' \in \mathbb{F}^{\log M}$ whenever $\sum_c (A(1, x, c) - A(0, x, c))(B(1, c, y) - B(0, c, y)) \not\equiv 0$. Because batch index $b$ appears in **both** $A$ and $B$ ($b \in F_{\ge 2}$ in `EinSumcheck` notation for `bxc,bcy -> bxy`), completeness requires summing over $b \in \{0,1\}^{\log M}$ against $\widetilde{\text{eq}}(r', b)$:

$$\tilde{V}_1(r', r'_x, r'_y) = \sum_{b \in \{0,1\}^{\log M}} \sum_{c \in \{0,1\}^{\log m}} \widetilde{\text{eq}}(r', b)\, \tilde{A}(b, r'_x, c)\, \tilde{B}(b, c, r'_y).$$

Reproduced deterministically over BabyBear ($p = 2013265921$) on a $2 \times 2 \times 2$ instance in [verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py#L46-L91) (`LHS = 1424152492 != RHS_zkGPT = 1629010779`, while `RHS_EinSumcheck = 1424152492`, `[EXECUTED]`).

*(Note on `zkGPT` code artifact availability: `zkgpt-usenix25.txt:901-907` cites `github.com/security-Anonymous/zkGPT` and `zenodo.org/records/14722553`; we verified the bug directly from Eq. (8) of the USENIX Security '25 camera-ready PDF/text in `~/paperbin/` without needing external network fetches.)*

---

### 1.2 `zkLLM` Element-Wise Multiplication Completeness Bug (`[READ]`, `[SOURCE]`, `[EXECUTED]`)

In `zkTransformer` §1 (footnote 2, citing `https://github.com/jvhs0706/zkllm-ccs2024/blob/993311e/proof.cu`) and §3 (`zkTransformer.txt:85-86, 209-216`), the authors state that `zkLLM`'s released code exhibits the same repeated-index completeness failure on element-wise (Hadamard) multiplication (`i,i -> i`).

**Verification at source (`[SOURCE]`):** Inspecting `jvhs0706/zkllm-ccs2024` at commit `993311e` across `proof.cu`, `fr-tensor.cu`, `polynomial.cu`, `rmsnorm.cu`, `zksoftmax.cu`, and `ffn.cu` reveals a subtle two-part state in the upstream codebase:

1. **The live broken function `hadamard_product_sumcheck` (`Fr_hp_sc`, `proof.cu:67-107`):**
   - In `fr-tensor.cu:589-609`, `Fr_me` folds tensor indices **LSB-first** (`gid0 = 2 * gid`, `gid1 = 2 * gid + 1`, consuming `u[0]` first).
   - `Fr_hp_sc` (`proof.cu:67-94`) adapts `inner_product_sumcheck` (`Fr_ip_sc`, `proof.cu:29-53`) by computing quadratic LSB-slice coefficients `out0[gid] = a0 * b0`, `out1[gid] = a0*(b1-b0) + b0*(a1-a0)`, `out2[gid] = (a1-a0)*(b1-b0)` (`Fr_ip_sc_step`, `proof.cu:12-27`), and pushing their multilinear evaluations at `u_ = (u_1, ..., u_{d-1})` (`proof.cu:82-86`):
     ```cpp
     vector<Fr_t> u_(u_begin + 1, u_end);
     proof.push_back(out0(u_));
     proof.push_back(out1(u_));
     proof.push_back(out2(u_));
     ```
   - **Exact bug:** `Fr_hp_sc` completely omits the $\widetilde{\text{eq}}(u_0, T) = (1 - u_0) + (2u_0 - 1)T$ factor! Consequently, its round-1 polynomial $g_1(T) = \text{out0}(u_{>0}) + \text{out1}(u_{>0})T + \text{out2}(u_{>0})T^2$ satisfies
     $$g_1(0) + g_1(1) = \widetilde{(a \odot b)}(0, u_{>0}) + \widetilde{(a \odot b)}(1, u_{>0}) \neq (1 - u_0)\widetilde{(a \odot b)}(0, u_{>0}) + u_0\widetilde{(a \odot b)}(1, u_{>0}) = \tilde{Y}(u),$$
     failing the standard sumcheck round-1 check (and every subsequent round check $g_k(0) + g_k(1) = g_{k-1}(v_{k-1})$)!
   - **Why `rmsnorm.cu` didn't crash in `zkLLM`'s demo (`rmsnorm.cu:47`):** Line 47 of `rmsnorm.cu` calls `hadamard_product_sumcheck(g_inv_rms_, X, random_vec(ceilLog2(Y.size)), random_vec(ceilLog2(Y.size)));` — **discarding the returned `vector<Fr_t>` proof without running any verifier check against `Y`**! Reproduced in [verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py#L105-L143) (`g1(0)+g1(1) = 1958784222 != Y(u) = 1508054396`, `[EXECUTED]`).
2. **Partial upstream fix & missing SwiGLU proof (`proof.cu:159, 191-241`; `ffn.cu:73`):**
   - At `proof.cu:159`, the `zkLLM` authors wrote `// TODO: DEPRECATE ABOVE` and added `multi_hadamard_sumchecks` (`proof.cu:191-241`, used by `zksoftmax.cu:186` for product of segment lookups), which splits MSB-first (`gid + N_out`) and **does** multiply by `Polynomial::eq(u.back())` (`proof.cu:226`) and assert `claim == p(0) + p(1)` (`proof.cu:228`). However, they left the broken `hadamard_product_sumcheck` active in `rmsnorm.cu:47`, and in `ffn.cu:73` (`auto down_in = swiglu_out * up_out_;`) they omitted any Hadamard sumcheck call between `hidden_rescale.prove(down_in, down_in_)` (`line 86`) and `swiglu.prove` / `up_rescale.prove` (`lines 87, 92`) (`[SOURCE]`).

---

### 1.3 Prior Art on Compiling Einsum / Tensor Contractions (`[READ]`)

**Question:** Did `Power circuits` (`ePrint 2023/1611`), `zkPyTorch` (`ePrint 2025/535`), or other prior zkML systems compile general Einsum contractions with $\widetilde{\text{eq}}$ restricted to shared free indices ($F_{\ge 2}$) before `EinSumcheck` (`zkTransformer` §4.2–4.3)?

| Work | Source Inspected | How Linear / Tensor Contractions Are Proved | General Einsum $(F_1, F_{\ge 2}, S)$ Compiler? |
|---|---|---|---|
| **Power Circuits** (Soukhanov, `ePrint 2023/1611`) | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2023/1611.pdf` (`289` lines, read in full) `[READ]` | Replaces bilinear GKR gates with affine layers $\mathbf{y} = M_i \mathbf{x}$ plus element-wise squaring $x \mapsto x^2$ (encoding $ab = \frac{1}{2}((a+b)^2 - a^2 - b^2)$). Still uses wiring MLE $\tilde{M}_i(y, x)$ sumchecks (`§3.2`, `§4`). | **No.** Zero mention of Einsum, tensor contractions, or free-index partitioning. |
| **zkPyTorch** (Creation / Polyhedra, `ePrint 2025/535`) | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/535.pdf` (`560` lines, read in full) `[READ]` | System/compiler whitepaper lowering PyTorch $\to$ ONNX $\to$ Expander GKR/layered circuits + parallel attention subgraph (`§3.1–3.3`). | **No.** Contains no sumcheck equations or Einsum index reduction rules. |
| **ZKTorch** (Chen, Tang, Kang, `arXiv:2507.07031`) | `~/paperbin/zktorch-2507.07031.txt` (`1,111` lines, `§3–§6` read) `[READ]` | Compiles ONNX to `BasicBlock`s (`CQLin` for fixed-weight MatMul, `Permute`/`CopyConstraint` for `Transpose`/`Reshape` when final axis changes, Mira accumulation; `lines 727-745`). | **No.** Explicitly pays `Permute` / `CopyConstraint` for shape ops modifying the final axis — the exact bottleneck `zkTransformer` (from the same Kang Lab group) replaces with `EinSumcheck`. |
| **TensorSwitch** (`ePrint 2025/2065`) | `~/paperbin/tensorswitch-2025-2065.pdf` (`3,339` lines extracted, searched & checked) `[READ]` | PCS switching compiler reducing multilinear/tensor evaluation claims across code-based / curve-based PCSs; not an ML operator or Einsum compiler. | **No.** Zero Einsum or ML contraction rules. |
| **Jolt Atlas** (ICME Lab, `arXiv:2602.17452`) | `~/paperbin/jolt-atlas-2602.17452.txt` (`1,001` lines, read in full) `[READ]` | Lists ONNX `Einsum` (`mk,kn->mn`, `bmk,bkn->bmn`, etc.) in supported ops (`§5.2`, `lines 776-778`), and states standard Hadamard virtualization $\tilde{V}(r) = \sum_t \widetilde{\text{eq}}(r, t)L(t)R(t)$ (`§2.2`, `lines 280-286`). | **No general compiler published.** Paper writes only 2-operand Hadamard virtualization; no $(F_1, F_{\ge 2}, S)$ index partition or unequal-variable-count partial-sumcheck algorithm is given. |
| **DeepProve** (Lagrange, `ePrint 2026/1112`) | `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/1112.pdf` (`2,896` lines, `§3–§4`, `App. B.1–B.8` read) `[READ]` | Uses `"Einsum"` in Table 3 (`line 956`) as a benchmark bucket for 2D `MatMul` (`Protocol 3`, `D = a A·B + b C`) and `BatchedMatMul` (`Protocol 4`, HyperPlonk batching of $h$ separate 2D matmuls). Proves token `Embed(T, x) = H_x · T` via sparse one-hot matmul (`§4.3.1`, `Protocol 6`, `lines 489-496, 1659-1699`). | **No.** In MHA (`§4.3.5`, `lines 594-631`), DeepProve commits $h$ separate head matrices $[[f_{T_{s,i}}]]$ and manually recombines head claims with $\beta(i, r_h)$, requiring matrix padding whenever $d/h$ is not a power of two. |

**Verdict on `EinSumcheck` novelty (`[DERIVED]`):** Special cases — 2D MatMul ($F_1=\{i,j\}, F_{\ge 2}=\emptyset, S=\{k\}$, [Thaler13]), Hadamard product ($F_1=\emptyset, F_{\ge 2}=\{i\}, S=\emptyset$), sparse one-hot embedding gather `sv,vd -> sd` (`zkGPT` §6.1; `DeepProve` §4.3.1 Protocol 6), and our own internal note `notes/contraction-sumcheck.md` — were known, **but `zkTransformer` §4.2–4.3 is the first paper in our audited corpora to package arbitrary multi-tensor Einsum strings into a single clean rule** ($\widetilde{\text{eq}}$ on $F_{\ge 2}$ only, direct challenge substitution on $F_1$, sum over $F_{\ge 2} \cup S$, plus the Algorithm 1 unequal-variable-count phase schedule) that simultaneously eliminates `Reshape`, `Transpose`, `Broadcast`/GQA head repeat, batched `MatMul`, `Mul`, and `ReduceSum` without intermediate commitments.

---

## 2. Prior Art on Decomposed & Range-Reduced `exp` in zkML

### 2.1 Base-$b$ / $2^d$ Product Chunking (`Rank1ProdExp`) Is Prior Art Across Four Primary Sources (`[READ]`)

Our candidate `Rank1ProdExp` decomposes a non-negative integer negated logit $u = 2^d u_{\text{hi}} + u_{\text{lo}}$ using the addition theorem $\exp(-(2^d u_{\text{hi}} + u_{\text{lo}})/\Delta) = \exp(-2^d u_{\text{hi}}/\Delta)\cdot \exp(-u_{\text{lo}}/\Delta)$, looking up two tiny subtables and multiplying their outputs once before rescaling. **Primary-source audit shows this exact mechanism is already published and deployed in four zkML works:**

1. **`zkLLM` (Sun, Li, Zhang, CCS 2024 — `~/paperbin/zkllm-ccs2024.txt:92-106, 496-605, 898-903`) `[READ]`:**
   - **§2 Eq. (3) (`lines 98-106`):** Explicitly states base-$B$ digit decomposition of fixed-point exponential inputs using $\exp(\sum_{k=0}^{K-1} B^{(k)} x^{(k)}) = \prod_{k=0}^{K-1} \exp(B^{(k)} x^{(k)})$ to replace exponential table growth with $K$ small `tlookup` tables.
   - **§5.1 Eqs. (19)–(26) & Lemma 5.1 (`lines 496-605`) + §8 (`lines 898-903`):** Decomposes negated shifted Softmax inputs $z_i = \sum_{k=0}^{K-1} B^k z_i^{(k)}$ into $K=5$ 16-bit segments ($B = 2^{16}$), approximates the $L=3$ least-significant segments by $1$ and most-significant overflow segments by $\mathbf{1}[z_i^{(k)}=0]$, looks up the **2 active middle 16-bit segments** via `tlookup`, and enforces the **unrescaled product** $y_i = \prod_k y_i^{(k)}$ via `multi_hadamard_sumchecks` (`zksoftmax.cu:186`)!

2. **`Hao et al.` (USENIX Security 2024 & `ePrint 2025/507` — `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/507.pdf`, `scratch/eprint_2025_507.txt:566-626`) `[READ]`:**
   - **§5.1 Fig. 12 `Protocol Π_Exp` (`lines 566-626`, citing MPC protocol SiRNN [Rathee et al., S&P '21]):** Negates $x \le 0$ to unsigned $\hat{x} = -x$, decomposes $\hat{x} = \hat{x}_{k-1} \| \dots \| \hat{x}_0$ into $k$ digits of width $d_j \le 12$ bits (`LUT threshold` $L=8$ or $12$), looks up $y_i = \lfloor (1/e)^{2^{\sum_{j<i} d_j}\hat{x}_i - s} \cdot 2^s \rfloor$ in $k$ small tables of size $2^{d_i}$, and multiplies them. Crucially, `lines 621-625` explicitly note that **intermediate `PosTrunc` rescalings can be deferred across products whenever $\prod y_i < p$**!
   - *(Note: Hao et al. do **not** use $\ln 2$ range reduction; for division in Softmax they compute explicit reciprocal $w = \lfloor 2^{2s}/\sum z_j \rfloor$ via `Π_Recip` constrained by $0 \le 2^{2s} - w \cdot d < d$ — i.e., **exact Euclidean division**, `§5.2 Fig. 13`, `lines 628-695`!)*

3. **`zkAgent` (`ePrint 2026/199` — `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/199.pdf`, `scratch/eprint_2026_199.txt:538-550`) `[READ]`:**
   - **§3.3 (`lines 538-550`):** Decomposes $\delta_i = s_{\max} - s_i = \sum_{k=0}^{K-1} b^k x_i^{(k)}$ with digits $x_i^{(k)} \in [0, b-1]$, range-checks digits, looks up $y_i^{(k)} \approx \exp(-b^k x_i^{(k)})$ via Shout, and enforces $e_i = \prod_{k=0}^{K-1} y_i^{(k)}$. *(Bibliographic note: `zkAgent` attributes this trick to `zkGPT [58]`, whereas `zkGPT` §4.3 `zkgpt-usenix25.txt:496-520` actually uses a single unstructured lookup table for nonlinearities; the base-$b$ `exp` split comes from `zkLLM` [70] and `Hao et al.`.)*

4. **`Jolt Atlas` (`arXiv:2602.17452`) + `Jo` (`ePrint 2026/1390`, *The Separation Principle* — `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/1390.pdf`, `scratch/eprint_2026_1390.txt:621-635, 944-1048`) `[READ]`:**
   - While the `Jolt Atlas` paper (`~/paperbin/jolt-atlas-2602.17452.txt:615-645`) emphasizes prefix-suffix range tables and "Neural Teleportation" ($\sigma(x/\tau)$ domain compression), **Jo (`2026/1390` §8.5 `EXP-5`, `lines 621-624`) audited the Jolt Atlas codebase directly and reports:**
     > *"Softmax/exp (EXP-5). The nonlinearity the floor theory is built around (softmax's exp) is implemented by Jolt not as one dense table but as a hi/lo 2-way split with an explicit degree-3 multiplication."*
   - Even more directly, **Jo (`2026/1390` §9 Propositions 2, 3, and 5, `lines 949-1048`) formalizes the exact rank-1 outer-product theory of `Rank1ProdExp`:**
     - **Proposition 2 & 3 (`lines 952-953, 984-1003`):** Rearranging an $r$-bit fixed-point table into the $2^a \times 2^{r-a}$ bipartition matrix $M_f[u, v] = T_f(u \| v)$, an addition-theorem activation ($e^{a+b} = e^a e^b$) has **exact matrix rank $\rho = 1$** (verified numerically by Jo at $r=16$: $\sigma_2/\sigma_1 = 1.6 \times 10^{-15}$), giving per-proof table-MLE cost $a(r) = \tilde{\Theta}(2^{r/2})$.
     - **Proposition 5 (*Separation Principle*, `lines 1027-1042`):** In a Shout-style lookup argument, node cost decomposes as $K(f, r) = a(r) + b \cdot m$, where $a(r)$ is **per-proof** (one table-MLE evaluation amortized across all $m$ lookups!) and $b \cdot m \propto d \cdot m$ is **per-lookup** (committing the one-hot read-address polynomials). Activation structure only touches $a(r)$ and has **zero leverage** on $b$; splitting 1 lookup into 2 hi/lo sub-lookups **doubles** the number of committed address nonzeros unless $d$ is adjusted!
     - **Direct implication for `gptoss-int v0` (`[DERIVED]`):** In `gptoss-int v0` (`tables.py:42-51`), `exp_table` has only $2^{12} + 1 = 4,097$ entries ($r = 12$). Under Shout (`d=1` or `d=2`), the per-proof dense table evaluation $a(12) = 4,097$ field ops is **completely negligible** compared to $m = H \cdot S^2$ per-element lookups ($64 \times 1024^2 \approx 6.7 \times 10^7$ per layer at $S=1024$)! Splitting a 12-bit lookup into two 6-bit subtables + a degree-2 product + an extra RHA shift (`Rank1ProdExp`) saves $4097 - 128 = 3969$ per-proof ops while adding an $O(m)$ multiplication sumcheck and an $O(m)$ truncation range check! By contrast, `Rank1ProdExp` **only** pays off when $r \ge 20$ (where $2^r$ hits the dense-table wall) or in LogUp/multiset substrates where the prover pays $O(|T|)$ multiplicity commitments per table.

---

### 2.2 Prior Art on $\ln 2$ Range Reduction (`StructuredExp`) (`[READ]`)

`zkTransformer` §4.4 (`zkTransformer.txt:466-548`) computes $\exp(q / 2^s)$ for $q \le 0$ by decomposing
$$q = -k \cdot \lfloor 2^s \ln 2 \rceil + r, \qquad k \ge 0,\quad r \in [0, \lfloor 2^s \ln 2 \rceil),$$
so $\exp(q / 2^s) = 2^{-k} \cdot \exp(r / 2^s)$, proving $2^{-k}$ via Shout against the multiplicatively structured MLE $\tilde{T}_{\text{pow}}(y) = \prod_{i=1}^{\log_2 K} ((2^{2^{i-1}} - 1)y_i + 1)$ (`line 496`) and evaluating $\exp(r / 2^s)$ via a degree-5 Horner Taylor polynomial on $[0, \ln 2)$.

**Primary-source cross-check across ZK & zkML archives (`[READ]`):**
- **Kurik & Laud (`ePrint 2024/859`, *Elementary Function Approximations in Zero-Knowledge Proofs*, WPES '24 — `~/paperbin/elementary-function-approximations-in-zk-kurik-laud-2024-859.pdf`, `§4.2–4.3`, `lines 329-369`) `[READ]`:** Explicitly implements $\exp(x) := \text{exp2}((\log_2 e) \cdot x)$ in ZK fixed-point circuits via the base-2 range reduction $\text{exp2}(z) = 2^{\lfloor z \rfloor} \cdot 2^{\{z\}}$, computing $2^{\lfloor z \rfloor}$ via integer bit-decomposition arithmetic and $2^{\{z\}}$ on $[0, 1]$ via Sollya minimax polynomial (`§4.3.1`) or algebraic root-finding (`§4.3.2`).
- **`ZKLP` (aca, `ePrint 2024/1842` — `~/paperbin/zklp-float-snark-2024-1842.pdf`, `§5–6`, `lines 680-692, 864-872`) `[READ]`:** Notes the standard 3-step math-library recipe (range reduction + Taylor/Remez polynomial + output compensation) as its fixed-point baseline in circuit benchmarking.
- **`catgrad` / MPC prior art (`notes/zkml-integration-architecture.md:146-148`) `[READ]`:** `catgrad/approx.rs` already uses Cody–Waite range reduction $x = k \ln 2 + r$ with degree-4 polynomial + $2^k$ scaling (inherited from standard libm / CrypTen / MP-SPDZ).
- **zkML lookup papers (`zkLLM`, `zkGPT`, `Hao et al. 2025/507`, `zkAgent 2026/199`, `Jolt Atlas 2602.17452`, `DeepProve 2026/1112`, `NanoZK`, `Jo 2026/1390`) `[READ]`:** **None** of these zkML papers use $\ln 2$ range reduction for `exp`.
- **What is specifically new in `StructuredExp` (`[DERIVED]`):** Replacing Kurik–Laud's circuit bit-decomposition of $2^{-k}$ with a **Shout lookup into the structured power-of-2 MLE $\tilde{T}_{\text{pow}}(y)$** (`zkTransformer` line 496; building on Lasso/Shout decomposable/structured tables [STW23, AST24]) so $2^{-k}$ costs $O(\log K)$ verifier field ops with zero table materialization, paired with fixed-point Horner evaluation on $r \in [0, \lfloor 2^s \ln 2 \rceil)$.
- **Caveat in `zkTransformer`'s `StructuredExp` (`[SOURCE]`):** Because $\lfloor 2^s \ln 2 \rceil \approx 0.69315 \cdot 2^s$ is not a power of two, `zkTransformer`'s power-of-2 range table $[0, 2^{\lceil \log_2(2^s \ln 2) \rceil})$ leaves $\approx 30.7\%$ slack ($[0.693 \cdot 2^s, 1.0 \cdot 2^s)$) if only $r \in [0, 2^b)$ is checked without a second shifted range check $r + (2^b - \lfloor 2^s \ln 2 \rceil) \in [0, 2^b)$! Checking `src/basicblock/exp.rs` in upstream `main`: let us note that `upstream-audit-pr` covers `exp.rs` line-by-line, while from the compiler-seam side, `StructuredExp`'s 5 sequential Horner multiplications + 5 intermediate `Scale` truncations per element make it strictly heavier per element than a single 12-bit Shout lookup on `gptoss-int v0`'s 4,097-entry `exp_table`.

---

## 3. Security Gap Audit: `Hollow-LLM` Registry Exposure & `Softmax`/`Sigmoid`/`RMSNorm` Zamir Audit

### 3.1 `Hollow-LLM` & Missing Public Weight Registry (`[READ]`)

We cross-checked `zkTransformer` (§5.1 `zkTransformer.txt:560-573` & Fig. 2 `line 1257`) against `Hollow-LLM` (`~/paperbin/hollow-llm-attack.pdf`, `arXiv:2607.28884`, `hollow-llm-attack.txt:1-792`).

- **What `zkTransformer` proves (`[READ]`):** In `zkTransformer` Fig. 2 (`line 1257`), the prover commits private weight tensors $\{W^{(\ell)}\}$ via HyperKZG (`Commit(pp, \tilde{W}^{(\ell)})`) and proves $y = \mathcal{M}(x; \{W^{(\ell)}\})$ for a fixed public architecture graph $\mathcal{M}$ (e.g., LLaMA-2-70B layer/head/hidden dimensions). There is **no** public weight registry, training proof, or canonical benchmark/canary attestation binding $C_W$ to genuine 70B parameters.
- **Why `Hollow-LLM` applies verbatim (`[READ]`, `[DERIVED]`):** `Hollow-LLM` (`hollow-llm-attack.txt:69-105, 482-791`) defines the **Effort-Gap Threat Model**: a dishonest service commits *once* to a structured "hollow" parameter vector $\hat{\theta}$ fitting the exact tensor shapes of a frontier architecture (e.g., 70B) while embedding a small secret model $\theta_S$ (e.g., 1.5B–7B):
  - **Attack A (Zero-Work Residual Layers, `§5.2`, `lines 482-578`):** Sets $W_O^{(\ell)} = 0$ and $W_{\text{down}}^{(\ell)} = 0$ in $L_{\text{target}} - L_{\text{small}}$ layers so $h^{(\ell)} = h^{(\ell-1)}$ identically; online inference skips those layers completely while proof generation proves the valid (trivial) forward pass under $\hat{\theta}$.
  - **Attack B ($m\times$ Width Replication, `§5.3`, `lines 580-791`):** Replicates hidden state $x \in \mathbb{R}^{d_S}$ $m$ times to $\tilde{x} \in \mathbb{R}^{m d_S}$ (preserving LayerNorm/RMSNorm mean and variance identically, Lemma at `lines 601-630`), embeds block-diagonal $Q/K/V$ and MLP matrices with $1/m$-scaled dense collapse (`lines 632-746`), and handles both learned APE and RoPE (`§5.4`, `lines 748-791`).
  - Furthermore, because HyperKZG commitments over sparse/replicated MLEs reuse identical sub-commitments internally for the prover while remaining hiding to the verifier, even commitment generation cost collapses for the attacker. **Closing `Hollow-LLM` requires binding $C_W$ to a public weight hash/registry (for open-weight models like `gpt-oss-20b`) or behavioral/training provenance (`VERDICTS.md` §10).**

---

### 3.2 `Softmax`, `Sigmoid`, and `RMSNorm`: Paper Zamir Vulnerability vs Upstream `main` Missing Constraints (`[SOURCE]`, `[DERIVED]`)

#### A. Paper-Level Specification: Vulnerable to Zamir's Theorem 1 (`[READ]`, `[DERIVED]`)

In `zkTransformer` §2.2 Eq. (1) (`zkTransformer.txt:182-200`), the paper adopts `zkLLM`'s shift-invariance advice: the prover supplies $r' = \max_i t_i + r$ (claiming $r \approx \ln \sum_i e^{t_i - \max_j t_j}$), computes $y_i = \exp(t_i - r')$, and *"verifies that the resulting values sum to approximately 1"*:
$$\left| \sum_{j=1}^{S} y_j - 2^s \right| \le \Delta_{\text{tol}}.$$
Similarly, in upstream `src/dag/llama.rs:144-159, 336-374`, `reciprocal` (used in `llama_rms_norm`) introduces a non-deterministic witness `inv_rms` and enforces only an approximate fixed-point product check:
$$|x_{\text{rms}} \cdot \text{inv\_rms} / 2^{15} - 32768| \le 512 \qquad (\text{a } \pm 1.5625\% \text{ per-token scaling window!}).$$

**Exposure to Zamir (`arXiv:2602.15756`; `docs/the-position.md:49-76`; `VERDICTS.md` §1) `[DERIVED]`:**  
Zamir's Theorem 1 proves that in any verification protocol whose layerwise constraints permit an $\ell_\infty$ or multiplicative slack $\delta > 0$ per layer — without pinning canonical rounding to a unique deterministic value — a malicious prover can steer intermediate activations within the legal $\pm \delta$ ball at every layer to embed $O(\log |\mathcal{V}|)$ steganographic bits or flip argmax token decisions on near-tied logits while producing a **100% valid cryptographic proof** against the honest model commitment $C_W$. Both `zkTransformer` Eq. (1)'s approximate Softmax sum and `llama.rs`'s $\pm 512 / 32768$ (`1.56%`) `RMSNorm` window are textbook instances of Zamir's non-unique witness slack (`DeepProve` `2026/1112` Protocol 10 & Protocol 12 and `zkAgent` `2026/199` Eq. 15 share the same approximate-normalization slack `[READ]`).

#### B. Upstream `uiuc-kang-lab/zkTransformer` `main` Code: Three Outright Soundness Breaks (`[SOURCE]`)

Inspecting `src/dag/gpt2.rs`, `src/dag/llama.rs`, `src/dag/builder.rs`, and `src/basicblock/llama.rs` from `uiuc-kang-lab/zkTransformer` (`main`) shows that the released implementation is **not merely Zamir-vulnerable — Softmax and Sigmoid are completely unconstrained in `main`**:

1. **Unimplemented Softmax Row-Sum Check (`src/dag/gpt2.rs:133-139`, `src/dag/llama.rs:439-443`) `[SOURCE]`:**
   In `gpt2_attention` (`src/dag/gpt2.rs:133-139`):
   ```rust
   // Softmax shift: add auxiliary shift c so exp inputs are <= 0 and outputs sum to ~SF.
   // Soundness check (sum ≈ SF) belongs in a later pass.
   let softmax_c = g.softmax_const(scores)[0];
   scores = g.add(scores, softmax_c)[0];
   scores = g.exp(scores)[0];
   ```
   And identically in `llama_attention` (`src/dag/llama.rs:439-443`):
   ```rust
   let softmax_c = g.softmax_const(scores)[0];
   scores = g.add(scores, softmax_c)[0];
   scores = g.exp(scores)[0];
   ```
   Searching the entire `src/` tree (`builder.rs`, `dag/mod.rs`, `basicblock/*.rs`) confirms **no pass ever emits the `sum ≈ SF` check**! And `SoftmaxConst::prove` / `verify` (`src/basicblock/llama.rs:289-315`) are no-ops returning `(vec![], vec![])` and `true`! Thus a malicious prover can set `softmax_c = -100000` everywhere so `scores = exp(...) = 0`, zeroing out attention completely while passing verification with probability 1!

2. **4D Witness Shape Bug in `SoftmaxConst` (`src/basicblock/llama.rs:239`) `[SOURCE]`:**
   Even if a downstream pass *did* check $\sum_t P_{b,h,s,t} \approx \text{SF}$, look at `SoftmaxConst::run` (`src/basicblock/llama.rs:238-239, 281`):
   ```rust
   let x = inputs[0];
   let y_shape = x.shape.clone(); // [B, H, S, S] -- NOT [B, H, S, 1]!
   ...
   vec![ArrayD::from_shape_vec(IxDyn(&y_shape), out).unwrap()]
   ```
   Because `softmax_c` has shape `[B, H, S, S]` instead of `[B, H, S, 1]` (not broadcast along the key axis!), the prover commits an **independent unconstrained scalar $c_{b,h,s,t}$ for every individual $(s, t)$ matrix entry**! Even with an exact row-sum constraint $\sum_t P_{b,h,s,t} = \text{SF}$, a cheating prover can choose $c_{b,h,s,t} = \text{desired\_log\_prob}_{b,h,s,t} - \text{score}_{b,h,s,t}$ to force **any arbitrary attention matrix $P$**, completely disconnecting attention outputs from $Q K^\top$! Fixing this requires committing a 3D tensor `c` of shape `[B, H, S]` and fusing `scores[b,h,s,t] + c[b,h,s]` via broadcast/linear combination!

3. **Unconstrained `SigmoidConst` in GELU and SiLU (`src/dag/builder.rs:300-305`, `src/basicblock/llama.rs:318-389`) `[SOURCE]`:**
   In `src/dag/builder.rs:300-305`:
   ```rust
   pub fn sigmoid(&mut self, a: NodeId) -> Vec<NodeId> {
       let c = self.sigmoid_const(a)[0];
       let shifted = self.add(a, c)[0];
       self.exp(shifted)
   }
   ```
   Here `SigmoidConst` (`src/basicblock/llama.rs:318-389`) computes $c = \lfloor -\ln(1 + e^a) \cdot \text{SF} - a \rceil$ as witness advice so $\exp((a+c)/\text{SF}) = \sigma(a)$, **with `prove -> empty` and `verify -> true` and ZERO algebraic relation checking $(1 + e^a) \cdot y \approx 1$**! Every `gpt2_mlp` (`gelu` calls `g.sigmoid`, `src/dag/gpt2.rs:157-166`) and `llama_mlp` (`silu` calls `g.sigmoid`, `src/dag/llama.rs:377-382`) allows the prover to output arbitrary values in $(0, 1]$ per coordinate!

#### C. Contrast with `gptoss-int v0`: Zero-Slack Exact Euclidean Integer Division (`[READ]`)

In our `gptoss-int v0` specification (`research/exact_recompute_2026_11_06/layer.py:169-184, 217-225` and `model.py:47-54`), **every** normalization and Softmax denominator is uniquely pinned by exact integer inequalities ($\delta = 0$, Zamir-immune):
- **`norm_int` (`layer.py:169-184`, `model.py:47-54`):** Exact integer sum of squares $s = \sum_{j=0}^{D-1} x_j^2$; `isqrt` uniquely pinned by $r^2 \le n < (r+1)^2$ (`n = (s * 2**(2*FRAC_S) + D - 1) // D`); output uniquely pinned by exact Euclidean floor division $y_j = \lfloor (x_j \cdot g_j \cdot 2^{f_a - F_G + \text{FRAC\_S}}) / \text{rms} \rfloor$, verified in-circuit by
  $$y_j \cdot \text{rms} + \text{rem}_j = \text{num}_j, \qquad 0 \le \text{rem}_j < \text{rms}.$$
- **Softmax + Attention Sink (`layer.py:217-225`, `tables.py:42-51`):** Exact row max $m_i = \max(\max_j s_{i,j}, \text{sink}_h)$ (certified via non-negative differences + zero-product or witness index); `d = clamp(m_i - s, 0, 4096)`; exact table lookup $w_{i,j} = T_{\exp}[d_{i,j}] \in [0, 65536]$; exact integer sum $\text{den}_i = \sum_j w_{i,j} + w_{\text{sink}, i}$; and **exact Euclidean integer division** on the attention numerator:
  $$\text{ao}_{i,h,d} = \left\lfloor \frac{\sum_j w_{i,j} V_{j,g,d}}{\text{den}_i} \right\rfloor \iff \text{ao}_{i,h,d} \cdot \text{den}_i + \text{rem}_{i,h,d} = \sum_j w_{i,j} V_{j,g,d}, \quad 0 \le \text{rem}_{i,h,d} < \text{den}_i.$$
  Notice a striking structural bonus (`[OURS]`): in `gptoss-int v0`, we **do not divide each $w_{i,j}$ by $\text{den}_i$** (which would require $H \cdot S^2$ divisions and introduce $S$ rounding errors per row); `layer.py:224-225` contracts the unnormalized integer weights $w_{i,j} \in [0, 65536]$ directly with $V_{j,g,d}$ (`num = einsum("ihj,jgd->ihd", w, V)` — a single `EinSumcheck`!) and performs exact Euclidean integer division only **once per output coordinate** ($H \cdot S \cdot d_h \ll H \cdot S^2$ for $S > d_h = 64$)!

---

## 4. Concrete Compiler-Seam Evaluation: `catgrad` & `gptoss-int v0` $\to$ `EinSumcheck`

### 4.1 Why Shape/Ring Islands Fuse While Rescale/Rounding/Routing Boundaries Cannot (`minidregg` Formal Anchor) (`[READ]`, `[DERIVED]`)

In `/Users/ember/dev/minidregg/Theory/ZkmlTensorOps.lean` and `/Users/ember/dev/minidregg/Theory/ZkmlMatmulSum.lean`, our Lean 4 formalization already draws the exact boundary that governs `EinSumcheck` fusion:

1. **The Ring-Homomorphic Fragment (`ZkmlTensorOps.lean:576-675`):**
   - `TOp.arithmetic` (`line 576`) carves out the exact subset of `TOp` constructors whose denotation commutes with every ring homomorphism $\psi : \alpha \to^{+*} \beta$ between two `IsRingReading` interpretations (`line 597`): `add`, `sub`, `mul`, `neg`, `fma`, `select` (on $\{0,1\}$-valued predicates via $s \cdot a + (1-s) \cdot b$, `lines 475-479`), `matmul` (`lines 650-659`), `sum` (`lines 640-649`), identity `cast`, `reshape`, `broadcast`, and `transpose`.
   - Theorem `arith_transport` (`ZkmlTensorOps.lean:670-675`, `#print axioms` = `[propext, Quot.sound]`, `lines 991-993`) proves that on any trace where all ops satisfy `TOp.arithmetic`, evaluating the trace over $\mathbb{Z}$ and projecting into $\mathbb{F}_p$ (`ZMod p`) equals evaluating the trace directly over $\mathbb{F}_p$.
   - **Extension to `gather` (`TOp.gather`, `line 277`) `[DERIVED]`:** While `TOp.gather` is excluded from `TOp.arithmetic` because its index wire has non-ring sort `Dtype.idx` (`line 660`), once an index tensor $I \in [N]^M$ is materialized as its boolean one-hot indicator $H_I \in \{0,1\}^{M \times N}$ ($H_I[m, n] = \mathbf{1}[n = I[m]]$), `gather(tbl, I)` becomes the pure bilinear contraction $\sum_{n \in [N]} H_I[m, n] \cdot \text{tbl}[n, \dots]$ (`mn,nd -> md`), re-entering the ring fragment! This covers both token embedding (`sv,vd -> sd`, public $H_{\text{tok}}$ evaluated in $O(S \log V)$ verifier time without commitment, matching `DeepProve` Protocol 6) and MoE top-$k$ expert gather/scatter (committed sparse $H_{\text{route}} \in \{0,1\}^{T \times K \times E}$).

2. **Why You Cannot Fuse Across `rq`, `clamp`, `norm_int`, Lookup Tables, or `route` (`ZkmlMatmulSum.lean:71-95, 238-322`):**
   - Contracting two adjacent linear stages (e.g., $(X W_1) W_2$ or $\sum_j w_{i,j} (X_j W_V)$) into a single sumcheck requires **distributivity and associativity** over the ring (`foldl_add_eq_listSum`, `ZkmlMatmulSum.lean:71-95`, which requires `[AddMonoid α]`).
   - Every fixed-point rescale `rq(a, k) = (a + 2^{k-1}) >> k` (`model.py:21-24`), saturating clamp `clamp(a, lo, hi)` (`model.py:43-44`), Euclidean floor division (`norm_int`, `ao // den`), non-linear LUT (`exp_table`, `glu_table`), and `topk` router (`route`, `layer.py:90-92`) violates both ring homomorphism ($\lfloor (a+b)/2^k \rfloor \neq \lfloor a/2^k \rfloor + \lfloor b/2^k \rfloor$) and associativity.
   - Theorem `SatExample.sat_bridge_fails` (`ZkmlMatmulSum.lean:303-322`, `#print axioms` at `lines 368-371`) constructs a concrete $1 \times 3 \times 1$ trace ($[6, 6, -5] \cdot [1, 1, 1]^\top$ on `[-8, 7]` saturating `Int4`) where sequential saturating fold produces `2` while exact ring `Finset.sum` over $\mathbb{Z}$ produces `7` (`2 ≠ 7`), refuting any sumcheck reduction that attempts to push an inner sum past a rounding or saturation boundary (`[READ]`).
   - **Compiler Law (`[OURS]`):** Every `rq` / `rq0` / `rq2`, `clamp`, integer division, LUT, and `route` node in `gptoss-int v0` is a **mandatory witness commitment & range/lookup boundary**. Everything *between* two such boundaries is a pure multilinear ring expression that fuses into a **single** `EinSumcheck` (or linear MLE combination) with **zero** intermediate shape/transpose/broadcast commitments!

---

### 4.2 Architectural Fit with `/Users/ember/src/catgrad-spike` (`[READ]`, `[OURS]`)

Inspecting `/Users/ember/src/catgrad-spike/catgrad/src/interpreter/backend/proving.rs` (`lines 1-304`) and `notes/catgrad-seam.md` (`lines 1-141`):
- `ProvingBackend` implements `catgrad`'s `Backend` trait (~300 LOC) using a shape-only `ProvingTensor { id, shape, dtype }` handle (`lines 60-65`) and records flat `Operation` variants (`Constant`, `Add`, `Sub`, `Mul`, `Div`, `Pow`, `Neg`, `MatMul`, `Reshape`, `Transpose`, `Broadcast`, `Slice`, `Concat`, `ReduceSum`, `ReduceMax`, `Argmax`, `TopK`, `Index`, `Compare`, `Where`, `Clamp`, `Cast`, `Arange`; `lines 68-167`) into `Rc<RefCell<Vec<TraceEntry>>>`.
- **Zero-Constraint-in-Rust Invariant Preserved (`notes/catgrad-seam.md:107-128`):** `catgrad` in Rust should **not** grow ad-hoc string-rewriting passes that decide soundness-critical sumcheck equations. Instead:
  1. `ProvingBackend` continues emitting the flat SSA `TraceEntry` DAG (extended only with explicit fixed-point boundary ops `RequantShift`, `IntDivRem`, `TableLookup` for integer quantized models).
  2. **Lean (`minidregg`) owns the contraction-fusion lowering** from `Trace` (`ZkmlTensorOps.lean`) to a verified `EinSumcheckSpec` descriptor `(inputs, F_1, F_{\ge 2}, S, elim_order)`:
     - `Reshape` (when dimensions factor into powers of two, e.g., $D = H \cdot d_h = 64 \times 64$ or $K = K_{\text{blk}} \cdot 32$), `Transpose` (index permutation), `Broadcast` (dropping axes from an input's index tuple), and `Slice`/`Concat` along static 2-way splits (RoPE halves `[..., 0..32]` & `[..., 32..64]`, SwiGLU gate/up `[..., 0..IM]` & `[..., IM..2*IM]`) become **pure index-tuple renamings** with **zero** trace commitments and **zero** sumcheck rounds!
     - Adjacent `MatMul`, `Mul`, and `ReduceSum` nodes that do not cross a non-arithmetic boundary merge into one `EinSumcheckSpec`.

*(Padding note for `gpt-oss-20b` `[DERIVED]`: in `gpt-oss-20b`, $H=64, G=8, d_h=64, E=32, K_{\text{top}}=4$, and block size $B=32$ are **all exact powers of 2**! Only hidden size $D = \text{IM} = 2880 = 90 \times 32$ has a non-power-of-2 block count $K_{\text{blk}} = 90$, which pads cleanly to $2^7 = 128$ blocks with zeros — adding zero error to sums and requiring only standard zero-padded MLE commitment.)*

---

### 4.3 Complete Decoder-Block Seam Maps

#### Table 1: GPT-2 Decoder Block (`catgrad-llm-models/src/models/gpt2.rs` + `stdlib/nn/mod.rs`) (`[READ]`, `[OURS]`)

Source inspected: `/Users/ember/src/catgrad-spike/catgrad-llm-models/src/models/gpt2.rs:1-215` and `catgrad/src/stdlib/nn/mod.rs:155-274`. Dimensions: sequence $S$, hidden $D = 768 = 12 \times 64$ ($H=12 \to 16$ padded, $d_h=64$), MLP inner $4D = 3072$.

| Sub-block | `catgrad` Trace Ops (`gpt2.rs` / `nn/mod.rs`) | Eliminated Zero-Cost View Ops | Proof / `EinSumcheck` Lowering | Mandatory Commitment Boundary |
|---|---|---|---|---|
| **Embeddings** (`gpt2.rs:163-186`) | `Index(wte, tok)` + `Broadcast(Slice(wpe, 0..S))` + `Add` | `Slice` (`0..S` prefix MLE evaluation at leading 0s), `Broadcast` | `EinSumcheck` `sv,vd -> sd` on public one-hot $H_{\text{tok}}$ ($O(S \log V)$ verifier eval) + virtual linear `Add` with `wpe` | Commit `x_0[S, D]` (after input `rq` if quantized) |
| **Pre-Attn `layernorm`** (`gpt2.rs:28-51`) | `ReduceSum` (mean $\mu$), `Broadcast`, `Sub`, `Mul` ($x'^2$), `ReduceSum` ($\sigma^2$), `Sqrt`, `Div`, `Mul` ($\gamma$), `Add` ($\beta$) | `Broadcast` ($\mu, \sigma, \gamma, \beta$) | Mean sumcheck (`sd -> s`); variance sumcheck (`sd,sd -> s`); exact `isqrt` + Euclidean floor div `(x - mu) * gamma // std + beta` | Commit `ln1_out[S, D]` + `mu[S]`, `std[S]`, `rem[S, D]` |
| **`c_attn` QKV Proj** (`gpt2.rs:95-109`) | `Transpose(W)`, `Broadcast(W)`, `MatMul(x, W)` $\to [S, 3D]$, `Broadcast(b)`, `Add`, `Reshape` $\to [S, 3, H, d_h]$, `Slice` ($Q, K, V$), `Transpose` $\to [H, S, d_h]$ | `Transpose`, `Broadcast`, `Reshape`, 3-way `Slice`, head `Transpose` — **all 6 view ops vanish!** | **1 `EinSumcheck`** `sd,3hde -> 3hse` (or 3 batched `sd,hde -> hse`) + virtual bias `Add` | Commit `Q[H,S,d_h]`, `K[H,S,d_h]`, `V[H,S,d_h]` after `rq` |
| **QK Scores** (`gpt2.rs:110-126`) | `Transpose(K, 2, 3)`, `MatMul(Q, K^T)` $\to [H, S, S]$, `Div(sqrt(d_h))`, causal `Where(mask, -inf, scores)` | `Transpose(K)` | **1 `EinSumcheck`** `hsd,htd -> hst` ($F_1 = \{s, t\}$, $F_{\ge 2} = \{h\}$, $S = \{d\}$: $\widetilde{\text{eq}}$ on $h$ only!) | Commit `scores_rq[H, S, S]` after `rq` |
| **Causal `softmax`** (`nn/mod.rs:175-186`) | `ReduceMax`, `Broadcast`, `Sub`, `Exp`, `ReduceSum`, `Broadcast`, `Div` | `Broadcast` ($m, \text{den}$) | Exact masked row-max $m_{h,s}$; non-negative `d = clamp(m - s)` LUT `w = T_exp[d]`; row-sum `hst -> hs` | Commit `w[H, S, S]` (unnormalized integer weights) + `m[H, S]` |
| **Attn Value + `c_proj` + Residual** (`gpt2.rs:128-133, 146`) | `MatMul(w, V)`, `Div(den)`, `Transpose`, `Reshape` $\to [S, D]$, `MatMul(W_proj)` + `b` + `x_in` | `Transpose(1,2)`, `Reshape([S, H*d_h])`, `Broadcast(b)` | **(1)** `EinSumcheck` `hst,htd -> hsd` ($F_{\ge 2}=\{h\}$) $\to$ exact Euclidean div `// den[h,s]`; **(2)** `EinSumcheck` `hsd,hdo -> so` (`c_proj`) + bias + residual `x_in` | Commit `ao[H,S,d_h]` (+ `rem`) at division boundary; commit `x_mid[S,D]` after `c_proj` `rq` |
| **Pre-MLP `layernorm` + `c_fc`** (`gpt2.rs:60-63, 147`) | `layernorm(x_mid)` $\to$ `linear(D, 4D)` | `Transpose`, `Broadcast` | `layernorm` (as above) $\to$ **1 `EinSumcheck`** `sd,df -> sf` + bias | Commit `ln2_out[S, D]`; commit `fc_out[S, 4D]` after `rq` |
| **`gelu` + `c_proj` + Residual** (`gpt2.rs:64-66, 148`) | `gelu(fc_out)` $\to$ `linear(4D, D)` + `x_mid` | `Transpose`, `Broadcast` | Single 12–16b GELU table lookup (replacing 8 float ops in `nn/mod.rs:159-173`) $\to$ **1 `EinSumcheck`** `sf,fd -> sd` + bias + `x_mid` | Commit `gelu_out[S, 4D]`; commit block output `x_out[S, D]` after `rq` |

**GPT-2 Seam Summary (`[DERIVED]`):** Across a full GPT-2 block, every single `Reshape`, `Transpose`, `Broadcast`, and QKV `Slice` (~22 shape/view nodes per block in `ProvingBackend`) disappears into `EinSumcheck` index tuples at **zero commitment cost**, leaving exactly **5 `EinSumcheck` contractions** (QKV, $QK^\top$, $wV$, `c_proj`, `c_fc`, MLP `c_proj` — 6 matmul contractions) separated by exact rescale/norm/LUT boundaries.

---

#### Table 2: `gpt-oss-20b` MoE + GQA Decoder Block (`gptoss-int v0`, `layer.py:192-272` & `gpt_oss.rs:1-386`) (`[READ]`, `[OURS]`)

Sources inspected: `/Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py:192-272`, `model.py:21-150`, `tables.py:21-58`, and `/Users/ember/src/catgrad-spike/catgrad-llm-models/src/models/gpt_oss.rs:1-386`.  
Model constants (`layer.py:27-35`): $L=24$, $D=2880$ ($K_{\text{blk}}=90 \to 128$), $H=64 = G \times R = 8 \times 8$ (8 KV heads, GQA group size $R=8$), $d_h=64$, $\text{IM}=2880$, $E=32$ experts, $K_{\text{top}}=4$, YaRN RoPE (`tables.py:21-39`), learned attention sinks (`sinks_q[64]`), clamped SwiGLU (`tables.py:54-58`).

| Stage in `layer_int` (`layer.py` lines) | Exact Integer Semantics (`gptoss-int v0`) | `catgrad` View/Shape Ops Eliminated | `EinSumcheck` Lowering (Index String & Shared Free Set $F_{\ge 2}$) | Mandatory Commitment & Non-Arithmetic Check Boundary |
|---|---|---|---|---|
| **1. Pre-Attn `norm_int`** (`L196`, `L169-184`) | $s_t = \sum_d x_{t,d}^2$; $\text{rms}_t = \text{isqrt}(\lceil s_t 2^{2F_S}/D \rceil)$; $h_{t,d} = \lfloor (x_{t,d} g_d 2^{\text{sh}}) / \text{rms}_t \rfloor$ | `Broadcast` ($\text{rms}_t, g_d$) | Sum-of-squares `EinSumcheck`: `td,td -> t` ($F_1=\emptyset, F_{\ge 2}=\{t\}, S=\{d\}$) | Commit `h[T, D]`, `rms[T]`, `rem[T, D]`; prove $r^2 \le n < (r+1)^2$ and $h \cdot \text{rms} + \text{rem} = \text{num}$ |
| **2. Q / K / V Projections** (`L199-203`) | `lin(h, q_w/k_w/v_w)` $\to$ exact integer dot + `rq2` per row + bias (`model.py:135-149`) | `Reshape` `[T, 4096] -> [T, 8, 8, 64]` ($H = (g, r)$) and `[T, 512] -> [T, 8, 64]` | **3 Native MXFP4 `EinSumcheck`s** (§5): `tkb,grdkb,grdk -> tgrd` ($Q$) and `tkb,gdkb,gdk -> tgd` ($K, V$); $F_{\ge 2} = \{(g,r,d)\}$ or $\{(g,d)\}$ | Commit pre-shift dot or post-`rq2` `q0[T,8,8,64]`, `k0[T,8,64]`, `v[T,8,64]` + `rq2` remainder range check |
| **3. YaRN `rope_int`** (`L204-205`, `L186-190`) | $y_1 = \text{rq}(x_1 C - x_2 S, F_{\text{ROPE}})$, $y_2 = \text{rq}(x_2 C + x_1 S, F_{\text{ROPE}})$ (`F_ROPE = 15`) | `Slice` (`0..32`, `32..64`), `Broadcast` ($C, S$ across $(g, r)$), `Concat` | Public MLEs $\tilde{C}(t, d'), \tilde{S}(t, d')$ ($32 T$ constants, verifier-evaluatable or preprocessed): linear + Hadamard `tgrd',td' -> tgrd'` ($F_{\ge 2}=\{t,d'\}$) before `rq`! *(Cannot fuse into $QK^\top$ without changing `rq` rounding!)* | Commit rotated `q[T,8,8,64]` and `k[T,8,64]` after `rq(..., 15)` |
| **4. GQA Scores** (`L213`) | `sc = einsum("tihd,nihd->tihn", q_gqa, k_gqa)` with $H = (g, r)$ (`8` KV groups $\times$ `8` Q-per-group, KV len $N$) | `Reshape`, `Broadcast` / `Repeat` (`8 -> 64` KV head expansion in `gpt_oss.rs:208-219`) — **8× KV bloat eliminated!** | **1 `EinSumcheck`**: `tgrd,ngd -> tgrn`! Here $F_1 = \{t, r, n\}$, **$F_{\ge 2} = \{g\}$ (only 3 bits for $G=8$!)**, $S = \{d\}$ (6 bits). Zero KV replication! | Commit `sc` only if `f_sc > 0`, or fold `rq(sc, f_sc)` directly into `m_tgr - sc` difference check! |
| **5. Causal/Sliding Mask + Sink Softmax** (`L214-223`) | Masked row-max $m_{t,g,r} = \max(\max_{n \in \mathcal{M}(t)} s_{t,g,r,n}, \text{sink}_{g,r})$; `d = clamp(m - s, 0, 4096)`; `w = EXP_TAB[d]`; `den = sum_n w + w_sink` | `Broadcast` ($m, \text{mask}, \text{den}$) | Row-sum `tgrn -> tgr` (`ReduceSum` = MLE eval of `w` with $n$-vars summed); `EXP_TAB` via 4,097-entry Shout lookup | Commit `m[T,8,8]`, clamped `d` + saturation witness, `w[T,8,8,N]` |
| **6. GQA Value Weighted Sum + Exact Div** (`L224-225`) | `num = einsum("tgrn,ngd->tgrd", w, v)`; `ao = num // den` | `Broadcast`/`Repeat` of $V$ (`8 -> 64`), `Reshape` `[T,8,8,64] -> [T,4096]` | **1 `EinSumcheck`**: `tgrn,ngd -> tgrd`! Again $F_1 = \{t, r, d\}$, **$F_{\ge 2} = \{g\}$ (only 3 bits!)**, $S = \{n\}$. | Commit `ao[T, 4096]` + `rem[T, 4096]`; prove `ao * den + rem = num` and $0 \le \text{rem} < \text{den}$ |
| **7. `o_proj` + Residual 1** (`L228-230`) | `o = lin(ao, o_w) + o_b`; `x1 = rq(x_res_scaled + o, sh)` | `Transpose`, `Broadcast` | **1 Native MXFP4 `EinSumcheck`** (`tkb,dkb,dk -> td`, $F_{\ge 2}=\{d\}$) + `rq2` + residual `Add` | Commit `x1[T, D]` |
| **8. Pre-MLP `norm_int` + Router `lin`** (`L232-238`) | `h2 = norm_int(x1)`; `rl = lin(h2, router_w)` (`[T, 32]`) | `Transpose`, `Broadcast` | `norm_int` (`td,td -> t`) + **1 `EinSumcheck`** `td,ed -> te` (BF16/int `router_w` `[32, 2880]` fits in 92K weights — no MXFP4 needed) | Commit `h2[T, D]` (+ `rms2, rem2`); commit router logits `rl[T, 32]` |
| **9. MoE Top-4 Routing + 4-Way Softmax** (`L239-248`, `L90-92`) | `idx, vals = route(rl)` (top-4 over 32 experts, tie-break smaller index, `notes/moe-router-binding.md`); 4-way exact `EXP_TAB` + `rw = (w * 65536) // sum(w)` | `TopK`, `Gather` | Sparse selection indicator $H_{\text{route}} \in \{0,1\}^{T \times 4 \times 32}$ (`sum_e = 1`, unselected $rl_e < \tau$ or $(rl_e = \tau \wedge e > e_{\text{tie}})$ per `moe-router-binding.md`) | Commit `H_route[T,4,32]`, `rw[T,4]`, 4-way `rem[T,4]` ($4T$ tiny lookups!) |
| **10. MoE Active Expert `mlp1` (`gate_up`)** (`L255-256`) | For each $(t, r_{\text{slot}} \in [4])$ with chosen expert $e = \text{idx}[t, r_{\text{slot}}]$: `gu = lin(h2[t], mlp1_w[e]) + mlp1_b[e]` (`[T, 4, 5760]`) | Dynamic per-expert loop / `Index(mlp1_w, idx)` / `Concat` (`gpt_oss.rs:285-320`) | **Active-4 Sparse-Gather MXFP4 `EinSumcheck`:** Commit full expert bank `Q_1[32, 5760, 90, 32]`, `S_1[32, 5760, 90]`, and contract with $H_{\text{route}}[t, r_{\text{slot}}, e]$ and $h_2[t, k, b]$: `tre,tkb,ejkb,ejk -> trj`! *(See §4.4 below!)* | Commit `gu[T, 4, 5760]` after per-expert `rq2` + bias |
| **11. Clamped `GLU_TAB` + Gate-Up Product** (`L257-264`, `tables.py:54-58`) | Split `gu` into `gate, up` (`[T, 4, 2880]`); `gate_c = clamp(gate, -7*2^f, +7*2^f)`; `up_c = clamp(up, -8*2^f, +6*2^f)`; `g = GLU_TAB[idx]`; `act = rq(g * (up_c + 2^f), 15)` | 2-way interleaved `Slice` (`0::2`, `1::2` = fixing LSB of $j$ to `0` vs `1`!) | `GLU_TAB` Shout lookup ($14,337$ entries, `tables.py:54-58`); Hadamard product `trm,trm -> trm` ($F_{\ge 2}=\{t,r,m\}$) before `rq(..., 15)` | Commit `act[T, 4, 2880]` (+ `clamp` & `rq` witnesses) |
| **12. MoE `mlp2` (`down`) + Router-Weighted Sum + Residual 2** (`L265-272`) | `dn = lin(act, mlp2_w[e]) + mlp2_b[e]` (`[T, 4, 2880]`); `mo = sum_{r_slot=0}^3 rq(dn * rw, 16)` (or fused weighted sum before final `rq` if spec allows; exact `layer.py:266` has `rq(..., 16)` per slot then sum) | Per-expert scatter-add loop | **(a)** Active-4 MXFP4 `EinSumcheck` `tre,trkb,edkb,edk -> trd` + `rq2`; **(b)** Slot-weight `EinSumcheck` `trd,tr -> trd` + `rq(..., 16)` + virtual sum over $r \in [4]$ + residual `x1` | Commit `dn[T, 4, 2880]`, slot-scaled `ws[T, 4, 2880]`, and final block output `x_out[T, 2880]` |

---

### 4.4 Two High-Leverage Structural Insights from the `gpt-oss-20b` Seam Map (`[DERIVED]`, `[OURS]`)

1. **GQA ($64$ Q heads, $8$ KV heads) Has Only a 3-Bit Shared Free Index ($F_{\ge 2} = \{g\}$):**
   In `catgrad`'s `gpt_oss.rs:208-219`, GQA expands `k` and `v` from `[B, 8, S, 64]` to `[B, 64, S, 64]` via `reshape` + `broadcast` + `reshape`, inflating KV tensors $8\times$ if materialized. Under `EinSumcheck`, factoring head index $h \in [64]$ into $(g, r) \in [8] \times [8]$ turns $QK^\top$ into `tgrd,ngd -> tgrn` and $WV$ into `tgrn,ngd -> tgrd`:
   - Intra-group query head index $r \in [8]$ appears **only** in $Q$ (for $QK^\top$) or **only** in $W$ (for $WV$), so **$r \in F_1$ is bound directly to verifier randomness $r_{\text{intra}}$ with zero sumcheck rounds and zero $\widetilde{\text{eq}}$ overhead**!
   - Only the 3-bit KV-group index $g \in [8]$ lies in $F_{\ge 2}$, adding just **3 rounds** of degree-3 sumcheck while keeping $K$ and $V$ committed at their native $1/8$ size (`[T, 8, 64]`).

2. **MoE Top-4 Expert Execution (`NE=32, TOPK=4`) as a 4-Operand Sparse `EinSumcheck` (`tre,tkb,ejkb,ejk -> trj`):**
   In `gpt-oss-20b`, all 32 experts' weights `mlp1_w[32, 5760, 90, 32]` are committed **once offline** (`AGENDA.md` Pillar II), while online execution runs only $K_{\text{top}} = 4$ experts per token ($4/32 = 12.5\%$ active compute). Naively proving all 32 experts and masking at the end wastes $8\times$ prover matmul work; naively copying the 4 selected expert matrices per token into a witness tensor `[T, 4, 5760, 2880]` would force committing $4 \times 5760 \times 2880 \approx 66.4\text{M}$ weights *per token*!
   Instead, `EinSumcheck` proves the active-4 contraction directly against the static 32-expert commitment via:
   $$D_1[t, r, j] = \sum_{e \in [32]} \sum_{k \in [K_{\text{blk}}]} \sum_{b \in [32]} H_{\text{route}}[t, r, e] \cdot h_2[t, k, b] \cdot Q_1[e, j, k, b] \cdot S_1[e, j, k],$$
   where $F_1 = \emptyset$, $F_{\ge 2} = \{t, r, j\}$, and $S = \{e, k, b\}$! Because $H_{\text{route}}[t, r, \cdot]$ has **only 1 nonzero per $(t, r)$**, in the prover's bookkeeping tables:
   - Binding $(t, r)$ or summing $e \in [32]$ touches only the $4T$ active $(t, r, e^*(t,r))$ triples during the token-side pass and folds the static weight bank $Q_1, S_1$ into a single $[5760, 90, 32]$ slice once the 5 $e$-variables are bound — **zero per-token weight re-commitment**, and only **5 extra sumcheck rounds** ($\log_2 32 = 5$) to bridge online routing to the static 32-expert commitment!

---

## 5. Native MXFP4 Block-Scaled Matmul via 3-Operand `EinSumcheck` (`ikb,jkb,jk -> ij`)

### 5.1 Exact MXFP4 Arithmetic in `gptoss-int v0` (`[READ]`, `[DERIVED]`)

From `docs/mx-formats.md`, `docs/AGENDA.md` (§Pillar I), `research/exact_recompute_2026_11_06/model.py:66-150`, and `jaxint.py:1-125`:
- Each MXFP4 weight matrix $W \in \mathbb{R}^{N \times K}$ ($K = 32 K_{\text{blk}}$) stores:
  1. A 4-bit signed E2M1 code per element, whose exact doubled integer value is
     $$Q[j, k, b] \in \{0, \pm 1, \pm 2, \pm 3, \pm 4, \pm 6, \pm 8, \pm 12\} \subset [-12, 12] \qquad (j \in [N],\; k \in [K_{\text{blk}}],\; b \in [32]),$$
  2. One shared 8-bit E8M0 exponent $E[j, k] \in \mathbb{Z}$ per 32-element block (`jaxint.py:86-102`).
- Let $e_{\min}[j] = \min_{k \in [K_{\text{blk}}]} (E[j, k] - 1)$ be the public per-row base exponent (`rowexp[j]` in `model.py:68-71`) and define the non-negative integer block scale
  $$S[j, k] := 2^{(E[j, k] - 1) - e_{\min}[j]} = 2^{\text{sh}[j, k]} \in \mathbb{Z}_{\ge 1}.$$
  Then the exact integer weight before row exponent $2^{e_{\min}[j]}$ is $W_{\text{int}}[j, 32k+b] = Q[j, k, b] \cdot S[j, k]$ (`jaxint.py:95-102`).
  *(Measured across `gpt-oss-20b` checkpoints in `jaxint.py` / `EXACT-RECOMPUTE.md`: within-row exponent spread $\text{sh}[j, k] = (E[j,k]-1) - e_{\min}[j]$ has **p50 = 2, p99 = 3, max $\le$ 8** on well-behaved rows, so $S[j, k] \in \{1, 2, 4, \dots, 256\}$ on virtually all rows!)*
- Given quantized activation $X \in \mathbb{Z}^{B_{\text{tok}} \times K_{\text{blk}} \times 32}$ ($|X[i,k,b]| \le 32,640$, `jaxint.py:19`), `model.py:135-149` computes the exact integer dot product
  $$D[i, j] = \sum_{k=0}^{K_{\text{blk}}-1} \sum_{b=0}^{31} X[i, k, b] \cdot Q[j, k, b] \cdot S[j, k], \qquad (i \in [B_{\text{tok}}],\; j \in [N]),$$
  followed by per-row round-half-away right shift $Y[i, j] = \text{rq}(D[i, j], s_j) + \text{bias}[j]$ with public row shift $s_j = x_f - e_{\min}[j] - f_o$ (`model.py:138-149`).

---

### 5.2 The 3-Operand `EinSumcheck` Identity & Its $(3, 3, 2)$ Round-Degree Schedule (`[DERIVED]`, `[EXECUTED]`, `[OURS]`)

Instead of offline-dequantizing $W_{\text{int}} = Q \cdot S$ into 29-bit integers (or two 20-bit limbs `(Wh, Wl)` as in `model.py:66-76`), commit **`Q` directly at native 4–5 bits** and **`S` once per 32 weights**, and prove `ikb,jkb,jk -> ij` as a single 3-operand `EinSumcheck`!

- **Index Classification:**
  - Free indices $\mathcal{I}_{\text{free}} = \{i, j\}$:
    - $i \in [B_{\text{tok}}]$ appears **only** in $X$ $\implies i \in F_1$ (**no $\widetilde{\text{eq}}$ needed!** Bound directly to verifier challenge $r_i \in \mathbb{F}^{\log_2 B_{\text{tok}}}$).
    - $j \in [N]$ appears in **both** $Q$ and $S$ $\implies j \in F_{\ge 2}$ (**requires $\widetilde{\text{eq}}(r_j, j)$** and sumcheck over $j \in \{0,1\}^{\log_2 N}$).
  - Contracted indices $\mathcal{I}_{\text{sum}} = \{k, b\}$ ($k \in \{0,1\}^{\lceil \log_2 K_{\text{blk}} \rceil}$, $b \in \{0,1\}^5$).

- **Exact Multilinear Sumcheck Identity:**
  For random verifier evaluation point $(r_i, r_j) \in \mathbb{F}^{\log_2 B_{\text{tok}}} \times \mathbb{F}^{\log_2 N}$,
  $$\tilde{D}(r_i, r_j) = \sum_{j \in \{0,1\}^{\log_2 N}} \sum_{k \in \{0,1\}^{\lceil \log_2 K_{\text{blk}} \rceil}} \sum_{b \in \{0,1\}^5} \widetilde{\text{eq}}(r_j, j) \cdot \tilde{X}(r_i, k, b) \cdot \tilde{Q}(j, k, b) \cdot \tilde{S}(j, k).$$

- **Sharp Round-Degree Theorem (`[DERIVED]`, `[EXECUTED]`):**
  A naive generic $m$-input `EinSumcheck` implementation (such as `zkTransformer`'s `LinearSumcheckProver`, which sets polynomial degree to `inputs.len() + 1 = 4` whenever $F_{\ge 2} \neq \emptyset$) charges **degree 4** in every round. **However, no variable in $\{j, k, b\}$ appears in all four factors!** Inspecting factor incidence per variable group under elimination order **$j \to k \to b$**:

  | Phase | Variables Bound | Number of Rounds (`gpt-oss-20b` `mlp1` / `mlp2`) | Active Factors Containing Round Variable | **Exact Univariate Degree** | Prover Sends / Round |
  |---|---|---|---|---|---|
  | **Phase 1 ($j$-rounds)** | $j \in \{0,1\}^{\log_2 N}$ | $\log_2 N$ (`13` / `12` rounds) | $\widetilde{\text{eq}}(r_j, j)$, $\tilde{Q}(j, k, b)$, $\tilde{S}(j, k)$ ($\tilde{X}(r_i, k, b)$ is independent of $j$!) | **Degree 3** ($\Delta^4 g \equiv 0$) | 4 felts (or 3 with $g(0)+g(1)=\text{claim}$) |
  | **Phase 2 ($k$-rounds)** | $k \in \{0,1\}^{\lceil \log_2 K_{\text{blk}} \rceil}$ | $\lceil \log_2 90 \rceil = 7$ rounds | $\tilde{X}(r_i, k, b)$, $\tilde{Q}(r'_j, k, b)$, $\tilde{S}(r'_j, k)$ ($\widetilde{\text{eq}}(r_j, r'_j)$ is now a constant scalar!) | **Degree 3** ($\Delta^4 g \equiv 0$) | 4 felts (or 3) |
  | **Phase 3 ($b$-rounds)** | $b \in \{0,1\}^5$ | $5$ rounds | $\tilde{X}(r_i, r'_k, b)$, $\tilde{Q}(r'_j, r'_k, b)$ (**both** $\widetilde{\text{eq}}(r_j, r'_j)$ and $\tilde{S}(r'_j, r'_k)$ are now scalars!) | **Degree 2** ($\Delta^3 g \equiv 0$) | 3 felts (or 2) |

  **Verified by execution (`[EXECUTED]`):** [verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py#L155-L315) runs the complete 3-phase sumcheck over both BabyBear (`p = 2013265921`) and Goldilocks (`p = 2^64 - 2^32 + 1`), asserting finite differences at 5 evaluation points per round: `degrees j=[3, 3], k=[3, 3], b=[2, 2, 2, 2, 2]` with exact final oracle agreement!

- **Why 1-Stage 3-Operand `ikb,jkb,jk -> ij` Strictly Beats a 2-Stage Split (`[DERIVED]`):**
  Suppose one tried to split into Stage 1 (`B[i, j, k] = sum_b X[i,k,b] * Q[j,k,b]`, `ikb,jkb -> ijk`) and Stage 2 (`D[i, j] = sum_k B[i,j,k] * S[j,k]`, `ijk,jk -> ij`):
  1. If `B[i,j,k]` is materialized and committed, you commit $B_{\text{tok}} \cdot N \cdot K_{\text{blk}}$ intermediate scalars ($90\times$ larger than output $D[i,j]$!).
  2. Even if `B[i,j,k]` is virtualized (pipelining Stage 2's evaluation claim $\tilde{B}(r_i, r'_j, r'_k)$ into Stage 1 without committing $B$), look at index $k$ in Stage 1 (`ikb,jkb -> ijk`): **$k$ is a shared free index ($k \in F_{\ge 2}$) of Stage 1**, so Stage 1 must STILL sumcheck over $k \in \{0,1\}^{\lceil \log_2 K_{\text{blk}} \rceil}$ (with $\widetilde{\text{eq}}(r'_k, k)$ at degree 3) **after** Stage 2 already sumchecked over $k$ (at degree 2)! Thus a 2-stage virtualized split runs $2 \lceil \log_2 K_{\text{blk}} \rceil = 14$ rounds on $k$ instead of $7$, doing strictly more prover work and rounds than the single 3-operand `EinSumcheck`!
  - **Prover inner-loop optimization in Phase 1 (`[DERIVED]`):** Notice that in Phase 1 ($j$-rounds), $\tilde{X}(r_i, k, b)$ does not depend on $j$ — wait: even better, if we instead eliminate **$b \to k \to j$**, wait: let's check both orders!
    - Under $b \to k \to j$: in the first 5 $b$-rounds, $Q(j, k, b)$ has size $N \cdot K_{\text{blk}} \cdot 32$ (folded down $32\times$ in 5 degree-2 rounds!); then 7 $k$-rounds fold $N \cdot K_{\text{blk}}$; then $\log_2 N$ $j$-rounds run on tiny vectors of size $N$! Wait: under $b \to k \to j$, in the $b$-rounds only $X$ and $Q$ depend on $b$, so **$b$-rounds are STILL degree 2**, $k$-rounds depend on $(X, Q, S)$ (**still degree 3**), and $j$-rounds depend on $(\text{eq}, Q, S)$ (**still degree 3**)! Both orders $j \to k \to b$ and $b \to k \to j$ have the **exact same $(2^5, 3^7, 3^{\log_2 N})$ degree multiset**, and $b \to k \to j$ halves the $N \cdot K_{\text{blk}} \cdot 32$ weight table at **quadratic** cost (3 evals instead of 4) in the biggest 5 rounds! That is a clean prover-time win worth benchmarking in `breadstuffs`.

---

### 5.3 Field-Overflow Analysis & BabyBear `int8` Activation-Limb Split (`[DERIVED]`, `[EXECUTED]`)

To ensure $D[i, j] \bmod p$ uniquely recovers $D[i, j] \in \mathbb{Z}$ without modular wraparound, we require $2 |D[i, j]| < p$. With $K = 2880$, $|X[i,k,b]| \le 32,768$ (`int16`), $|Q[j,k,b]| \le 12$, and block scale $S[j,k] = 2^{\text{sh}}$ ([verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py#L318-L335)):

| Max Row Spread $\text{sh}$ | Worst-Case $|D[i,j]|_{\max}$ (Unsplit `int16` $X$) | Fits $\ge 61$-bit Fields ($p_{61}$, Goldilocks, BN254)? | Fits BabyBear ($p \approx 2.013 \times 10^9$) Unsplit? | Worst-Case $|D_{\text{limb}}|_{\max}$ with `int8` $X = X_{\text{lo}} + 2^8 X_{\text{hi}}$ (`jaxint.py:18`) | Fits BabyBear with 2-Limb $X$ Split? |
|---|---|---|---|---|---|
| `sh = 2` (p50) | $4.53 \times 10^9$ (`32.1 bits`) | **Yes** | No ($2|D|/p = 4.50$) | $1.77 \times 10^7$ (`24.1 bits`) | **Yes** ($2|D_{\text{limb}}|/p = 0.018$) |
| `sh = 3` (p99) | $9.06 \times 10^9$ (`33.1 bits`) | **Yes** | No ($2|D|/p = 9.00$) | $3.54 \times 10^7$ (`25.1 bits`) | **Yes** ($2|D_{\text{limb}}|/p = 0.035$) |
| `sh = 6` | $7.25 \times 10^{10}$ (`36.1 bits`) | **Yes** | No | $2.83 \times 10^8$ (`28.1 bits`) | **Yes** ($2|D_{\text{limb}}|/p = 0.281$) |
| `sh = 7` | $1.45 \times 10^{11}$ (`37.1 bits`) | **Yes** | No | $5.66 \times 10^8$ (`29.1 bits`) | **Yes** ($2|D_{\text{limb}}|/p = 0.562$) |
| `sh = 8` | $2.90 \times 10^{11}$ (`38.1 bits`) | **Yes** (up to $\text{sh} \le 24$!) | No | $1.13 \times 10^9$ (`30.1 bits`) | Borderline ($1.125$); split $S = S_{\text{lo}} + 2^6 S_{\text{hi}}$ (`1/32` weight overhead) $\implies$ **Yes**! |

- **Over Goldilocks / Mersenne-61 / BN254:** One unsplit 3-operand `EinSumcheck` handles every row up to $\text{sh} \le 24$ with huge margin (`38.1 bits` $\ll 61\text{–}254\text{ bits}$).
- **Over BabyBear ($p = 2013265921 \approx 2^{30.91}$):** Mirroring `jaxint.py:18-23` (`x = 256 * hi + lo` into two signed `int8` runtime activation limbs, which touches **only** the tiny $O(T \cdot D)$ activation tensor and **never** touches the 19.1B weight commitments!), both limb contractions $D_{\text{lo}}, D_{\text{hi}}$ batch into the **same** `EinSumcheck` (`\alpha D_{\text{lo}} + \beta D_{\text{hi}}`, opening $\tilde{Q}$ and $\tilde{S}$ at a **single** random point!) while staying strictly inside $(-p/2, p/2)$ for all rows with $\text{sh} \le 7$ (99.9%+ of rows), and a 2-limb split on $S[j,k]$ (at `1/32` felt/weight cost!) handles outlier rows up to $\text{sh} \le 13$.

---

### 5.4 Exact Commitment Savings on `gpt-oss-20b` (`[EXECUTED]`)

Across all 24 MoE layers of `gpt-oss-20b` (`mlp1_w`: $32 \times 5760 \times 2880$; `mlp2_w`: $32 \times 2880 \times 2880$), total MoE weight count is **$19,110,297,600$ weights** in **$597,196,800$ blocks** of 32 ([verify_seam_and_mxfp4.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/verify_seam_and_mxfp4.py#L337-L357)):

| Weight Commitment Representation | Bits / Weight | Total Committed Payload (`24L` MoE) | Committed Felts (`24L` MoE) | Reduction vs Dequantized Baseline |
|---|---|---|---|---|
| **Dequantized 29-bit Integer** (`AGENDA.md` §Pillar I) | `29.000` b/w | `69.275 GB` | `19.11B` ($\ge 64$b) or `38.22B` (BabyBear 2-limb) | `1.00×` |
| **`gptoss-int v0` `model.py` `(Wh, Wl)` 2-Limb** (`model.py:66-76`) | `40.000` b/w (`2 × 20b`) | `95.551 GB` | `38,220,595,200` (`2.000` felts/w) | `0.73×` bits / `1.00×` felts |
| **Native MXFP4 (`Q` in `[-12,12]` 5-bit + `S` 9-bit)** | **`5.281` b/w** | **`12.616 GB`** | **`19,707,494,400`** (`1.03125` felts/w) | **`5.49×` bit reduction / `1.94×` felt reduction** |
| **Native MXFP4 (4-bit E2M1 code + 8-bit `sh`, LUT-mapped)** | **`4.250` b/w** | **`10.152 GB`** | **`19,707,494,400`** (`1.03125` felts/w) | **`6.82×` bit reduction / `1.94×` felt reduction** |

*(Note: In a lattice/code PCS such as BaseFold/WHIR over BabyBear or binary tower fields where commitment work scales with bit-width / small-value MSM or binary-field packing, the `5.49–6.82×` bit-width reduction translates directly into offline preprocessing memory, commitment key size, and prover MSM/hash throughput, while completely eliminating offline weight dequantization.)*

---

## 6. Corpus & Instrument Disclosure Ledger + Proposed `VERDICTS.md` Folds

### 6.1 Explicit Corpus & Instrument Disclosures (`AGENTS.md` / `VERDICTS.md` §5d Compliance)

1. **IACR ePrint Local Mirror (`/Users/ember/dev/gh/forks/IACR-eprint-mirror/`, complete through `2026/1861`):**
   - **Instrument:** Direct `pdftotext -layout` extraction into `/Users/ember/.gemini/antigravity-cli/brain/04e22f63-de65-467a-a797-48c8dfd7eeb0/scratch/` + full/section `read_file` inspection (zero network requests to `eprint.iacr.org`).
   - **Primary PDFs extracted & read at source:** `2023/1611.pdf` (`Power circuits`, 289 lines, read in full), `2025/507.pdf` (`Hao et al.`, 1,200+ lines read covering §§1–7), `2025/535.pdf` (`zkPyTorch`, 560 lines, read in full), `2026/199.pdf` (`zkAgent`, 1,009 lines read covering §§1–4), `2026/1112.pdf` (`DeepProve`, 2,896 lines extracted, §§3–4 & App. B.1–B.8 read), `2026/1390.pdf` (`Jo, Separation Principle`, lines 1–1600 read covering §§1–10).
2. **`~/paperbin/` Archive (`2,013` PDFs total; `VERDICTS.md` §5d grep-invisibility accounted for):**
   - **Instruments:**
     1. Enumerated all `2,013` `*.pdf` filenames in `~/paperbin/` via Python directory scan (`os.listdir`), identifying `150` ZK/ML/sumcheck/lookup/float PDFs lacking pre-existing `.txt` companions.
     2. Extracted target PDFs lacking `.txt` via `pdftotext -layout` into `$SCR/`: `elementary-function-approximations-in-zk-kurik-laud-2024-859.pdf` (`ePrint 2024/859`), `zklp-float-snark-2024-1842.pdf` (`ePrint 2024/1842`), `tensorswitch-2025-2065.pdf` (`ePrint 2025/2065`), `deepprove-2026-1112.pdf`, `zktorch-2507.07031.pdf`.
     3. Read pre-extracted `.txt` files in `~/paperbin/` at source: `zkgpt-usenix25.txt`, `zkgpt-eprint2025.txt`, `zkllm-ccs2024.txt`, `jolt-atlas-2602.17452.txt`, `hollow-llm-attack.txt`, `nanozk` (`arXiv`), plus regex sweep (`grep -rliE`) across all `.txt` files in `~/paperbin/` for `ln 2`, `Cody-Waite`, `range reduction`, and `einsum`.
3. **Upstream Source Repositories & Companion Trees:**
   - `uiuc-kang-lab/zkTransformer` (`main` via `raw.githubusercontent.com`): `src/dag/{gpt2,llama,builder,mod}.rs`, `src/basicblock/{mod,einsum,exp,llama,scale,range,clamp,add,shape}.rs`.
   - `jvhs0706/zkllm-ccs2024` (`993311e` via `raw.githubusercontent.com` & GitHub tree API): `proof.cu`, `polynomial.cu`, `fr-tensor.cu`, `rmsnorm.cu`, `zksoftmax.cu`, `ffn.cu`.
   - Companion trees (read-only): `/Users/ember/dev/minidregg/Theory/{ZkmlTensorOps,ZkmlMatmulSum}.lean`, `/Users/ember/src/catgrad-spike/{catgrad,catgrad-llm-models}`, `/Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/{layer,model,tables,jaxint}.py`.

---

### 6.2 Proposed Updates to `docs/VERDICTS.md` (For Maintainer Fold — Not Edited Here)

1. **`VERDICTS.md` §1 (Zamir Soundness & Canonical Rounding) & §10 (`Hollow-LLM`):**
   - Record `zkTransformer` (`arXiv:2603.19609v1`) as a concrete case study on both fronts: (a) private weight commitment without a weight registry leaves `Hollow-LLM` Attacks A & B open; (b) paper §2.2 Eq. (1) approximate Softmax normalization and `RMSReciprocal` ($\pm 1.56\%$) admit Zamir slack, while upstream `main` (`src/dag/{gpt2,llama,builder}.rs`, `src/basicblock/llama.rs`) omits the Softmax sum check altogether, commits a 4D `[B,H,S,S]` unconstrained `SoftmaxConst` tensor, and leaves `SigmoidConst` unconstrained — reinforcing `gptoss-int v0`'s exact Euclidean division (`ao * den + rem = num`, $0 \le \text{rem} < \text{den}$).
2. **`VERDICTS.md` §3 / `AGENDA.md` §Pillar I (MXFP4 Native Proving & `catgrad` Seam):**
   - Fold the **Native MXFP4 3-Operand `EinSumcheck` (`ikb,jkb,jk -> ij`)** construction: proves exact MXFP4 block-scaled matmul without offline weight dequantization at round degrees $(3^{\log_2 N}, 3^{\lceil \log_2 K_{\text{blk}} \rceil}, 2^5)$ (`5.49–6.82×` bit-commitment reduction, `1.94×` felt reduction vs `(Wh, Wl)` limbs), compatible with BabyBear via `jaxint.py`'s 2-limb `int8` activation split.
   - Fold **GQA `tgrd,ngd -> tgrn`** ($F_{\ge 2} = \{g\}$, 3 bits) and **Active-4 MoE `tre,tkb,ejkb,ejk -> trj`** into the Lean-authored `TOp` $\to$ `EinSumcheckSpec` lowering design (`notes/catgrad-seam.md`).
3. **`VERDICTS.md` §5 (Prior-Art Ledger on Lookup / Nonlinearity Arithmetic):**
   - Record that base-$b$ / hi-lo product `exp` (`Rank1ProdExp`) is established prior art across `zkLLM` (§5.1), `Hao et al.` (`2025/507` §5.1), `zkAgent` (`2026/199` §3.3), and `Jolt Atlas` / `Jo` (`2026/1390` §8.5 `EXP-5`, §9 Propositions 2–3 & 5), and note Jo's Separation Principle consequence: on `gptoss-int v0`'s small 4,097-entry `exp_table` ($r=12$), a single direct Shout lookup avoids doubling per-lookup address commitments.
