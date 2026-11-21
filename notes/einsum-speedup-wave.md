# Next-Generation `EinSumcheck` Speedups on `gptoss-int v0` (`gpt-oss-20b`)

**Date:** 2026-11-21 · **Lane:** `einsum-turbo` (Wave 1)  
**Verification & Pricing Script (`[EXECUTED]`):** [einsum_turbo_pricing.py](file:///Users/ember/dev/zkml-research/research/speedup_wave_2026_11_21/experiments/einsum_turbo_pricing.py) (`python3 research/speedup_wave_2026_11_21/experiments/einsum_turbo_pricing.py`, exit `0`, BabyBear $p = 2013265921$, `Ext4` $= \mathbb{F}_p[X]/(X^4 - 11)$).  
**Companion Baseline:** [zktransformer-verdicts.md](file:///Users/ember/dev/zkml-research/notes/zktransformer-verdicts.md), [layer.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py), [model.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/model.py).

---

## 0. Executive Verdicts (Current Truth)

1. **Gruen `eq`-Factored `EinSumcheck` (`ePrint 2024/108` §3.2 + `ePrint 2025/1117` §5.1) — ADOPT (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`):**
   - Factoring $s_u(X) = \ell_u(X) \cdot q_u(X)$ on shared-free rounds $u \in F_{\ge 2}$ ($\deg q_u = m_u$) and solving $q_u(1) = \ell_u(1)^{-1}(\sigma_{\text{prev}} - \ell_u(0) q_u(0))$ cuts evaluation points per $F_{\ge 2}$ round from $m_u + 2$ (`{0,1,2,3}`) to **$m_u$ (`{0, \infty}` = 2 points for $m_u = 2$ — a `2×` point cut)**, with **zero** soundness degradation (and tightened per-round error $m_u/|\mathbb{F}| = 2/|\mathbb{F}|$ in direct-$q_u$ Mode 2, `2024/108` App. A.3).
   - On un-repeated GQA (`tgrd,ngd -> tgrn` + `tgrn,ngd -> tgrd`), Gruen cuts sumcheck `Ext4` muls **`4.73–4.75×`** vs `zkTransformer`'s `LinearSumcheckProver` (**`37.9–38.0×`** vs repeated-KV `LinearSumcheckProver`) and **`1.25–1.26×`** below our already-factored `{0,1,\infty}` prover ([einsum_gqa_counts.py](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/experiments/einsum_gqa_counts.py)), while shrinking transcript `Ext4` elements `1.11–1.14×` with **zero** prover inversions.
   - On native MXFP4 (`ikb,jkb,jk -> ij`), because $X[i,k,b]$ is independent of $j$, $j \in F_{\ge 2}$ has $m_j = 2$ (only $\tilde{Q}, \tilde{S}$). Thus **both** $b \in S$ (5 rounds) **and** $j \in F_{\ge 2}$ ($\log_2 N \in \{12, 13\}$ rounds) become **quadratic degree-2 rounds** (`18/25` rounds on `gate_up`, `17/24` on `down`/`q_proj`), leaving only the 7 $k$-rounds degree-3.

2. **MXFP4 Elimination Order, `SVO` (`ePrint 2025/1117`), & Tensor-Factored E2M1 Horner — ADOPT `b -> j -> k` (`l_0 = 5`) (`[DERIVED]`, `[EXECUTED]`, `[REFUTED: generic SVO l_0 >= 3 on BabyBear]`):**
   - Across all 6 block schedules under `Algorithm 1`, `k`-first loses by `0.75×` (degree-3 rounds on full $J K B$), while naive `b`-first still promotes `Q` to a `(J, K, 16)` `Ext4` buffer (`268.6 MB` on `gate_up`).
   - **`[REFUTED: generic Toom-Cook SVO l_0 >= 3 on BabyBear+Ext4]`:** Reproducing `2024/1046`'s warning at $\kappa_{ll/sl} = 9/4 = 2.25$, generic `SVO` (`2025/1117` Thm 6.1) peaks at $\ell_0 = 2$ (`1.32×` total BB gain) and **regresses** at $\ell_0 = 3$ (`1.18×`) due to $(3/2)^{\ell_0}$ `base × Ext4` growth.
   - **Tensor-Factored Delayed Block-Bind ($\ell_0 = 5$) + E2M1 4-Bit-Plane Horner (`[DERIVED]`, `[EXECUTED]`):** Because $X_{r_i}[k,b]$ is independent of $j$ and $S[j,k]$ is independent of $b$, $Q[j,k,b]$ has degree **$d_Q = 1$** in $b$. Collapsing $M[k,b] = \sum_j (\mathrm{eq}(r_j,j) S[j,k]) Q[j,k,b]$ runs all 5 $b$-rounds on `4,096` `Ext4` elements before binding $Q^{(5)}[j,k] = \sum_{b=0}^{31} \mathrm{eq}(r_b,b) Q[j,k,b]$ in one pass, cutting peak `Ext4` memory **`16.4×` (`276.9 MB -> 16.8 MB` padded, `8.36 MB` active)** and `Ext4 × Ext4` muls **`10.9×` (`15.4×` active)**. Further, every E2M1 integer $\{0,\pm 1,\pm 2,\pm 3,\pm 4,\pm 6,\pm 8,\pm 12\}$ has binary Hamming weight $\le 2$, so 7-bucket 4-bit-plane Horner (`(((2 C_8 + C_4)\cdot 2 + C_2)\cdot 2 + C_1)`) evaluates both $M[k,b]$ and $Q^{(5)}[j,k]$ with **zero field multiplications** on `Q`, yielding **`12.65×` padded / `18.36×` active** total BabyBear mul speedup on `gate_up` with bit-identical round messages.

3. **Block-Banded Sliding-Window `EinSumcheck` (`W = 128` on 12/24 Layers) + Zero-Commitment `step_β` Bridge — ADOPT (`[DERIVED]`, `[EXECUTED]`):**
   - `gptoss-int v0` ([layer.py:21, 84-88, 211-227](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L21)) runs dense `[H, T, T]` `einsum` and `EXP_TAB` lookups even on the **12 even layers** (`l % 2 == 0`) whose causal window is $W = 128$.
   - Writing $i = 128 b + u$ ($b \in [T/128], u \in [128]$) and contracting against the 256-token virtual window $K_{\text{win}}[b, w, g, d]$ ($w = 128 s + v \in [256]$) reproduces `layer_int` **bit-for-bit** (`max |diff| == 0` verified at $T = 512$) and reduces $\tilde{K}_{\text{win}}, \tilde{V}_{\text{win}}$ to **already-committed** $\tilde{K}, \tilde{V}$ via a closed-form $O(\beta)$ multilinear carry-chain selector $\mathrm{step}_\beta(r_b, b')$ (**zero** extra KV commitments, $\le 508$ `Ext4` muls at $T = 16{,}384$).
   - **Per sliding layer (`12` even layers):** cuts `EXP_TAB` lookups, committed `E` cells, and total attention+PCS BabyBear muls by **`4.5×` ($T=512$), `16.6×` ($T=2048$), `32.8×` ($T=4096$), and `130.5×` ($T=16{,}384$)** (honestly noting that the tiny sumcheck-only `Ext4` term rises `2.5×` from `526k -> 1.32M` because $b \in F_{\ge 2}$, trading `+7.1M` SC muls to save `5.24T` `EXP_TAB`/PE/PCS muls).
   - **24-layer Amdahl ceiling:** With $2\times$ causal triangle pruning on the 12 odd full-attention layers, full-model 24-layer attention+PCS cost drops **`2.89×` ($T=512$) $\to$ `3.84×` ($T=4096$) $\to$ `4.01×` ($T=16{,}384$)**, asymptotically pinned at `4×` because the 12 odd causal triangles retain `25%` of dense 24-layer cells.

4. **Active-4 Bucketed MoE `EinSumcheck` + 24-Layer Uniform Folding — ADOPT (`[DERIVED]`, `[EXECUTED]`):**
   - Proving active buckets $T_e > 0$ against per-expert registry commitments ([moe-router-binding.md](file:///Users/ember/dev/zkml-research/notes/moe-router-binding.md) §5.3 D4–D5; router share **`0.13%`** of MoE cells) exhibits a **three-regime curve** unseen in plaintext MAC models: **`8.00×`** at $T=1$ (`4/32` experts fire), a **coupon-collector dip to `2.41×` ($T=8$) / `3.11×` ($T=32$)** as active experts saturate $32(1 - (28/32)^T) \to 32$ (forcing all 32 expert weight matrices to be scanned once), and **asymptotic recovery to `7.50×` (dyadic bucket padding, `1.49×` pad overhead) / `8.26×` (Jagged PCS, `1.00×` pad)** at $T = 16{,}384$ once $4T$ activation/lookup commitments dominate.
   - Folding `24` uniform layers (`+ 32` experts) with **zero-padded dummy-layer skipping** (`l \in [24..31)` skipped, `0.0%` prover mul overhead vs `+33.3%` naive dyadic pad) collapses full-model contraction proofs from **`1,704` sumchecks (`40,824` rounds, `3,408` PCS openings, `1,355.6 KB` transcript) $\to$ `11` sumchecks (`269` rounds, `24` openings, `8.92 KB` — `152×` transcript & round reduction)**, unaffected by per-layer fixed-point scales ([params-v1.json](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/params-v1.json)) because `EinSumcheck` proves exact pre-`rq2` integer dots.

---

## 1. Gruen `eq`-Factored `EinSumcheck` (`ePrint 2024/108` §3.2)

### 1.1 Algebraic Formulation, Two Wire Modes, and Soundness (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`)

In `EinSumcheck` ([ZkmlEinSumcheck.lean](file:///Users/ember/dev/zkml-research/research/zktransformer_2026_11_20/formal/Assurance/ZkmlEinSumcheck.lean)), after binding degree-1 free indices $F_1$ via `partial_eval_f1_base`, the prover proves
$$H = \sum_{x \in \{0,1\}^\ell} \widetilde{\mathrm{eq}}(r_{F_{\ge 2}}, x) \sum_{y \in \{0,1\}^{\mu_S}} \prod_{t=1}^{m} \tilde{P}_t(x, y).$$
In round $u \in \{0, \dots, \ell - 1\}$ eliminating $x_u \in F_{\ge 2}$ (shared across $m_u \ge 2$ operands), $\widetilde{\mathrm{eq}}$ splits as ([`2024/108` §3.2, pp. 8–9](file:///Users/ember/dev/gh/forks/IACR-eprint-mirror/2024/108.pdf); [`2025/1117` §5.1 Eq. 16, p. 17](file:///Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/1117.pdf)):
$$s_u(X) = \underbrace{\widetilde{\mathrm{eq}}(r_{<u}, r^{\text{chal}}_{<u}) \cdot \big((1 - r_u)(1 - X) + r_u X\big)}_{\ell_u(X),\; \deg = 1} \cdot \underbrace{\sum_{x_{>u}} \widetilde{\mathrm{eq}}(r_{>u}, x_{>u}) \sum_y \prod_{t=1}^m \tilde{P}_t(r^{\text{chal}}_{<u}, X, x_{>u}, y)}_{q_u(X),\; \deg = m_u}.$$

- **2× Evaluation Cut (`[DERIVED]`):** From $\ell_u(0) q_u(0) + \ell_u(1) q_u(1) = \sigma_{\text{prev}}$, whenever $\ell_u(1) \neq 0$ the prover solves $q_u(1) = \ell_u(1)^{-1}(\sigma_{\text{prev}} - \ell_u(0) q_u(0))$ in $O(1)$ scalar ops and evaluates $q_u(X)$ only on $\widehat{U}_{m_u} = \{0, \infty, 2, \dots, m_u - 1\}$ ($m_u$ points vs $m_u + 2$). For $m_u = 2$ (both GQA $g \in F_{\ge 2}$ and MXFP4 $j \in F_{\ge 2}$), $\widehat{U}_2 = \{0, \infty\}$ (`A0*B0` and `dA*dB` — **2 inner products** vs 4 on `{0,1,2,3}`). Suffix tables $\widetilde{\mathrm{eq}}(r_{>u}, \cdot)$ are built once MSB-to-LSB (`build_eq_suffix_tables`) in $\max(0, 2^{\ell-1} - 2)$ `Ext4` muls with **zero** per-round `eq` folds.
- **Two Verified Wire Modes (`[EXECUTED]` in `einsum_turbo_pricing.py`):**
  1. **Mode 1 (Wire-Transparent, Setty–Thaler `2025/105` / `2025/1117` Proc. 8):** Prover reconstructs $s_u(X) = \ell_u(X) q_u(X)$ in $O(1)$ ops and sends cubic messages to an **unmodified** `AirSumcheckCubic` verifier (`0` Lean verifier changes; deterministic fallback to direct `q_u(1)` when $\ell_u(1) = 0$ gives completeness $1$ on all of $\mathbb{F}_{p^4}$, verified by forcing $r_g[1] = 0$).
  2. **Mode 2 (Direct-$q_u$, Gruen `2024/108` §3.3 & App. A.3):** Prover sends $(q_u(0), q_u(\infty))$ directly (**zero** prover inversions; `2` `Ext4` elements/round; per-round soundness **$m_u / |\mathbb{F}| = 2/|\mathbb{F}|$** vs $3/|\mathbb{F}|$). At $u = \ell$, $\sigma'_\ell = q_{\ell-1}(\text{ch}_{\ell-1})$ has already stripped $\widetilde{\mathrm{eq}}(r_{F_{\ge 2}}, \text{ch}_{F_{\ge 2}})$ and chains directly into Phase 2 (`S`-rounds); we include an explicit boundary-splice falsifier modeled on the Jolt Uni-Skip bug (`[SOURCE: ~/paperbin/audit-blog-zksecurity-jolt-uniskip.txt, PR #1474]`).

### 1.2 Exact GQA Sumcheck Counts (`tgrd,ngd -> tgrn` + `tgrn,ngd -> tgrd`, 1 Layer, `[EXECUTED]`)

| Context $T$ | `zkT` Naive Rep SC `Ext4` | `zkT` Naive GQA SC `Ext4` | Prev Canonical (`{0,1,inf}`) SC `Ext4` | **Gruen Mode 2 (`{0,inf}`)** SC `Ext4` | SC Gain vs `zkT` GQA / Prev | Transcript `Ext4` (`Prev -> Gruen`) |
|---:|---:|---:|---:|---:|---:|---:|
| 128 | 233,558 | 29,158 | 7,791 | **6,164** | **4.73×** / **1.26×** | `48 -> 42` (**1.14×**) |
| 512 | 700,502 | 87,526 | 23,157 | **18,452** | **4.74×** / **1.25×** | `52 -> 46` (**1.13×**) |
| 2,048 | 2,568,278 | 320,998 | 84,603 | **67,604** | **4.75×** / **1.25×** | `56 -> 50` (**1.12×**) |
| 4,096 | 5,058,646 | 632,294 | 166,526 | **133,140** | **4.75×** / **1.25×** | `58 -> 52` (**1.12×**) |
| 16,384 | 20,000,854 | 2,500,070 | 658,052 | **526,356** | **4.75×** / **1.25×** | `62 -> 56` (**1.11×**) |

---

## 2. Native MXFP4 (`ikb,jkb,jk -> ij`) Elimination Schedules, `SVO`, & E2M1 Horner

### 2.1 Why Generic `SVO` Stalls at $\ell_0 = 2$ on BabyBear while Tensor-Factored E2M1 Horner Reaches $\ell_0 = 5$ (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`)

After $F_1$ partial evaluation on $i$ (`X_ri[k,b]`, `4,096` `Ext4` elems — note BabyBear's 2-limb `int8` activation split $\alpha D_{\text{lo}} + \beta D_{\text{hi}}$ merges into `X_ri` *before* sumcheck at **zero** extra MXFP4 sumcheck cost), the `(b, k, j)` sumcheck contracts `X_ri[k,b]` (`Ext4`), `Q[j,k,b]` (`int4` E2M1), `S[j,k]` (`base`), and `eq(r_j, j)` (`Ext4`):

1. **All 6 Variable-Block Schedules (`Algorithm 1` + Gruen):** Eliminating `k` first (`k->j->b`, `k->b->j`) runs degree-3 rounds (`{0,2,\infty}`) over the unreduced $J K B$ grid (`0.75×` slower than `j`-first). Under standard `Algorithm 1`, even `b`-first promotes `Q` after round $b_0$ into a `(J, K, 16)` `Ext4` array (`268.6 MB` on `gate_up`, `134.3 MB` on `down`/`q_proj`).
2. **Generic Toom-Cook `SVO` (`[SOURCE: ePrint 2025/1117 §6.1 Thm 6.1]`; `[SOURCE: ePrint 2024/1046 pp. 31–32]`):** Generic `SVO` treats all operands as full-domain arrays, paying $\approx (3/2)^{\ell_0} J K B$ `base × Ext4` muls to delay `Ext4` promotion by $\ell_0$ rounds. On BabyBear+`Ext4`, $\kappa_{ll/sl} = 9/4 = 2.25$ (vs $\sim 7.5\text{–}12$ on BN254), so total BabyBear mul-equivalents peak at **$\ell_0 = 2$ (`1.32×`)** and **regress at $\ell_0 = 3$ (`1.18×`)** (`[REFUTED: generic Toom-Cook SVO l_0 >= 3 on BabyBear+Ext4]`).
3. **Tensor-Factored Block-Bind ($\ell_0 = 5$) + E2M1 4-Bit-Plane Horner (`[DERIVED]`, `[EXECUTED]`):** In `ikb,jkb,jk -> ij`, neither $\widetilde{\mathrm{eq}}(r_j, j)$ nor $S[j,k]$ depends on $b$, and $X_{r_i}[k,b]$ is independent of $j$. By multilinearity of $\tilde{Q}$ in $b$:
   - Pre-project $E_{jk}[j,k] = \widetilde{\mathrm{eq}}(r_j,j) S[j,k]$ (`J K` `base×Ext4` muls, `32×` smaller than `Q`) and $M[k,b] = \sum_j E_{jk}[j,k] Q[j,k,b]$ (`4,096` `Ext4` elems).
   - Run all **5 `b`-rounds** on `(X_ri, M)` (`4,096` elems $\implies$ `15,872` `Ext4` muls), then bind $Q^{(5)}[j,k] = \sum_{b=0}^{31} \widetilde{\mathrm{eq}}(r_b, b) Q[j,k,b]$ directly into a `(J, K)` `Ext4` buffer (**`16.84 MB` padded / `8.36 MB` active on `gate_up`**), followed by Gruen `j -> k` (where round $j_0$ still keeps `S[j,k]` in the base field, beating `b -> k -> j`).
   - **Zero-Mul E2M1 Addition Chain:** Every nonzero E2M1 integer $\{1,2,3,4,6,8,12\}$ has binary weight $\le 2$ ($12=8+4, 6=4+2, 3=2+1$). Accumulating 7 signed `Ext4` buckets and evaluating `(((2 C_8 + C_4)\cdot 2 + C_2)\cdot 2 + C_1)` (`C_8=B_8+B_{12}`, `C_4=B_4+B_6+B_{12}`, `C_2=B_2+B_3+B_6`, `C_1=B_1+B_3`) replaces all $2 J K B$ `int4 × Ext4` muls on `Q` with pure `Ext4` additions/doublings (**`0` multiplications on `Q`**).

### 2.2 Exact MXFP4 Pricing on `gpt-oss-20b` Shapes (`[EXECUTED]`, `0` OpCounter Discrepancy)

| Shape & Schedule / Variant | `base × Ext4` Muls | `Ext4 × Ext4` Muls | BB Mul-Equiv (`Kar=9`) | Peak `Ext4` Buf | `Ext4` Gain | **Total BB Gain** |
|---|---:|---:|---:|---:|---:|---:|
| **`gate_up` ($5760 \times 2880 \to 8192 \times 128 \times 32$):** | | | | | | |
| 1. `j -> k -> b` (`Alg1` + Gruen) | 51,904,512 | 51,933,276 | 675,017,532 | 276.89 MB | 1.00× | **1.00×** |
| 2. `j -> b -> k` (`Alg1` + Gruen) | 51,904,512 | 51,930,609 | 674,993,529 | 276.89 MB | 1.00× | **1.00×** |
| 3. `k -> j -> b` (`Alg1` + Gruen) | 69,206,016 | 69,140,475 | 899,088,339 | 276.99 MB | 0.75× | **0.75×** |
| 4. `k -> b -> j` (`Alg1` + Gruen) | 69,206,016 | 69,304,305 | 900,562,809 | 276.99 MB | 0.75× | **0.75×** |
| 5. `b -> j -> k` (`Alg1` + Gruen) | 62,390,272 | 52,019,439 | 717,736,039 | 268.60 MB | 1.00× | **0.94×** |
| 6. `b -> k -> j` (`Alg1` + Gruen) | 62,914,560 | 53,747,697 | 735,387,513 | 268.60 MB | 0.97× | **0.92×** |
| 7a. `b -> j -> k` + Generic `SVO` ($\ell_0 = 1$) | 85,458,944 | 26,853,615 | 583,518,311 | 134.41 MB | 1.93× | **1.16×** |
| 7b. `b -> j -> k` + Generic `SVO` ($\ell_0 = 2$) | 95,944,704 | 14,270,703 | 512,215,143 | 67.31 MB | 3.64× | **1.32×** |
| 7c. `b -> j -> k` + Generic `SVO` ($\ell_0 = 3$, regresses) | 125,304,832 | 7,979,247 | 573,032,551 | 33.75 MB | 6.51× | **1.18×** |
| 8a. `b -> j -> k` Tensor-Factored ($\ell_0 = 5$, mul) | 69,730,304 | 4,763,533 | 321,793,013 | 16.84 MB | 10.90× | **2.10×** |
| **8b. `b -> j -> k` Tensor-Factored + E2M1 Horner** | **2,621,440** | **4,763,533** | **53,357,557** | **16.84 MB** | **10.90×** | **12.65×** |
| **8c. `b -> j -> k` TF + Horner + ActiveSupport** | **1,624,320** | **3,362,929** | **36,763,641** | **8.36 MB** | **15.44×** | **18.36×** |
| **`down` ($2880 \times 2880 \to 4096 \times 128 \times 32$):** | | | | | | |
| 1. `j -> k -> b` (`Alg1` + Gruen) | 25,952,256 | 25,970,780 | 337,546,044 | 138.48 MB | 1.00× | **1.00×** |
| 7b. `b -> j -> k` + Generic `SVO` ($\ell_0 = 2$) | 47,972,352 | 7,137,519 | 256,127,079 | 33.69 MB | 3.64× | **1.32×** |
| **8b. `b -> j -> k` Tensor-Factored + E2M1 Horner** | **1,310,720** | **2,389,901** | **26,751,989** | **8.45 MB** | **10.87×** | **12.62×** |
| **8c. `b -> j -> k` TF + Horner + ActiveSupport** | **812,160** | **1,689,713** | **18,456,057** | **4.21 MB** | **15.37×** | **18.29×** |
| **`q_proj` ($4096 \times 2880 \to 4096 \times 128 \times 32$):** | | | | | | |
| 1. `j -> k -> b` (`Alg1` + Gruen) | 25,952,256 | 25,970,780 | 337,546,044 | 138.48 MB | 1.00× | **1.00×** |
| **8b. `b -> j -> k` Tensor-Factored + E2M1 Horner** | **1,310,720** | **2,389,901** | **26,751,989** | **8.45 MB** | **10.87×** | **12.62×** |
| **8c. `b -> j -> k` TF + Horner + ActiveSupport** | **921,600** | **1,689,713** | **18,893,817** | **5.96 MB** | **15.37×** | **17.87×** |

*(Note: In raw `gptoss-int v0` shards ([layer.py:23-25](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L23-L25), [census_bf16.json](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/census_bf16.json)), `q/k/v/o_proj` are stored in BF16 while MoE `gate_up` and `down` are MXFP4; `q_proj` above prices MXFP4-quantized attention projections.)*

---

## 3. Block-Banded Sliding-Window `EinSumcheck` (`W = 128` on 12/24 Layers)

### 3.1 Zero-Commitment Virtual Window & Carry-Chain `step_β` Reduction (`[DERIVED]`, `[EXECUTED]`)

In `gptoss-int v0` ([layer.py:21, 84-88](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L84-L88)), the 12 even layers enforce `0 <= i - j < 128`. Writing $i = 128 b + u$ ($b \in [B_{\text{blk}}], B_{\text{blk}} = T/128 = 2^\beta, u \in [128]$), every valid key for block $b$ lies in the 256-token window $K_{\text{win}}[b, w, g, d]$ with $w = 128 s + v$ ($s \in \{0,1\}, v \in [128]$: $s=0$ is block $b-1$, zero-padded at $b=0$; $s=1$ is block $b$), under local mask $(s = 1 \wedge v \le u) \vee (s = 0 \wedge b \ge 1 \wedge v > u)$:
- **Windowed GQA Contractions:** `bugrd,bwgd -> bgruw` ($Q K_{\text{win}}^\top$) and `bgruw,bwgd -> bugrd` ($E_{\text{win}} V_{\text{win}}$) keep $(u, r) \in F_1$ (`10` bits, **0** rounds) and $w \in F_1(K_{\text{win}})$ / $d \in F_1(V_{\text{win}})$, placing $(b, g)$ ($\beta + 3$ bits) in $F_{\ge 2}$.
- **Zero Extra KV Commitments via $\mathrm{step}_\beta$:** To open $\tilde{K}_{\text{win}}(r_b, r_s, r_v, r_g, r_d)$ against already-committed $\tilde{K}(b', v, g, d)$, define the unique multilinear extension of $\mathbf{1}[x = y + 1 \wedge y < 2^\beta - 1]$ on $\{0,1\}^\beta \times \{0,1\}^\beta$ (LSB-first carry run):
  $$\mathrm{step}_\beta(x, y) = \sum_{c=0}^{\beta-1} \left(\prod_{\tau=0}^{c-1} (1 - x_\tau) y_\tau\right) x_c (1 - y_c) \left(\prod_{\tau=c+1}^{\beta-1} \mathrm{eq}_1(x_\tau, y_\tau)\right).$$
  Then $\tilde{K}_{\text{win}}(r_b, r_s, r_v, r_g, r_d) = \sum_{b' \in \{0,1\}^\beta} \big((1 - r_s)\mathrm{step}_\beta(r_b, b') + r_s \widetilde{\mathrm{eq}}(r_b, b')\big)\tilde{K}(b', r_v, r_g, r_d)$, proved by a $\beta$-round quadratic sumcheck ($\beta \le 7 \implies \le 508$ `Ext4` muls) and $O(\beta)$ verifier work. Because $\{v \le u\}$ and $\{v > u\}$ partition $[128]$, `EXP_TAB` runs on only $128 T - 8{,}128$ active cells/head (`8,192 T` packed `E` cells/layer vs `64 T^2`).

### 3.2 Exact Attention + `EXP_TAB` (`D1b` LogUp-GKR) + WHIR PCS Pricing (`[EXECUTED]`)

| $T$ | 1L Sliding `EXP_TAB` (`Dense -> Win128`) | 1L Sliding PE `×` / SC `Ext4` (`GQA -> Win128`) | **1L Sliding Tot `×`** | 24L `EXP_TAB` (`Dense -> Hybrid`) | 24L Total Attn+PCS BB Muls (`Rep -> GQA -> Hybrid`) | **24L Speedup vs Rep / GQA** |
|---:|---:|---:|---:|---:|---:|---:|
| 512 | `16.81M -> 3.71M` (**4.5×**) | **2.8×** PE / `18,452 -> 41,124` SC | **4.5×** | `0.40B -> 0.15B` (**2.77×**) | `119.14B -> 113.64B -> 41.27B` | **2.89×** / **2.75×** |
| 2,048 | `268.57M -> 16.39M` (**16.4×**) | **9.7×** PE / `67,604 -> 164,580` SC | **16.6×** | `6.45B -> 1.81B` (**3.56×**) | `1893.52B -> 1869.76B -> 518.70B` | **3.65×** / **3.60×** |
| 4,096 | `1074.00M -> 33.30M` (**32.3×**) | **18.8×** PE / `133,140 -> 329,188` SC | **32.8×** | `25.78B -> 6.85B` (**3.76×**) | `7648.10B -> 7598.83B -> 1990.11B` | **3.84×** / **3.82×** |
| 16,384 | `17180.92M -> 134.75M` (**127.5×**) | **73.7×** PE / `526,356 -> 1,316,836` SC | **130.5×** | `412.34B -> 104.72B` (**3.94×**) | `125802.40B -> 125591.24B -> 31396.08B` | **4.01×** / **4.00×** |

---

## 4. Active-4 Sparse MoE `EinSumcheck` + 24-Layer Uniform Folding

### 4.1 Coupon-Collector Weight Saturation vs Large-$T$ Activation Recovery (`[DERIVED]`, `[EXECUTED]`)

Grouping the $4T$ routed `(token, slot)` pairs by expert $e \in [32]$ ([layer.py:246-269](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L246-L269)) against `24 × 32 = 768` per-expert registry roots (`24.5 KB` model-wide; [moe-router-binding.md](file:///Users/ember/dev/zkml-research/notes/moe-router-binding.md) §2.3 variant (b) + §5.3 D4–D5) reveals a key difference between sumcheck proving and plaintext MACs: in `EinSumcheck`, an active expert's weight matrix $(Q_e, S_e)$ is scanned **once** regardless of bucket size $T_e \ge 1$. Under uniform routing, expected active experts per layer are $32(1 - (28/32)^T)$:

| $T$ | Active Experts `/ 32` | Active `4T` vs Dyadic-Pad Rows (`Pad ×`) | Pure Weight-SC Gain | `EinSumcheck` Only Gain (Jagged) | Total 24L MoE BB Muls (`Dense -> Dyadic -> Jagged`) | **Total MoE Gain (Dyadic / Jagged)** | Router Cell Share |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | `4.00` | `4 -> 4.0` (`1.00×`) | `8.00×` | `8.00×` | `46.62B -> 5.83B -> 5.83B` | **8.00×** / **8.00×** | `0.13%` |
| 8 | `21.00` | `32 -> 33.8` (`1.06×`) | `1.52×` | `1.53×` | `77.36B -> 32.09B -> 32.05B` | **2.41×** / **2.41×** | `0.13%` |
| 32 | `31.55` | `128 -> 161.5` (`1.26×`) | `1.01×` | `1.03×` | `186.01B -> 59.87B -> 59.08B` | **3.11×** / **3.15×** | `0.13%` |
| 128 | `32.00` | `512 -> 728.1` (`1.42×`) | `1.00×` | `1.05×` | `632.32B -> 118.82B -> 113.32B` | **5.32×** / **5.58×** | `0.13%` |
| 512 | `32.00` | `2,048 -> 3004.0` (`1.47×`) | `1.00×` | `1.18×` | `2464.24B -> 359.76B -> 333.79B` | **6.85×** / **7.38×** | `0.13%` |
| 2,048 | `32.00` | `8,192 -> 12172.0` (`1.49×`) | `1.00×` | `1.68×` | `9978.80B -> 1354.01B -> 1239.02B` | **7.37×** / **8.05×** | `0.13%` |
| 4,096 | `32.00` | `16,384 -> 24384.0` (`1.49×`) | `1.00×` | `2.23×` | `20164.31B -> 2704.83B -> 2466.78B` | **7.45×** / **8.17×** | `0.13%` |
| 16,384 | `32.00` | `65,536 -> 97744.0` (`1.49×`) | `1.00×` | `4.23×` | `82523.14B -> 11003.27B -> 9989.22B` | **7.50×** / **8.26×** | `0.13%` |

*(Note: Jagged-PCS total gain reaches `8.26× > 8.00×` at $T = 16{,}384$ because $8\times$ smaller committed traces save `3` log-height levels in WHIR's $O(N \log N)$ LDE encoding.)*

### 4.2 24-Layer (+ 32-Expert) Uniform Folding (`[DERIVED]`, `[EXECUTED]`)

Stacking $l \in [24]$ (`5` bits in $F_{\ge 2}$; `4` bits for 12 even / 12 odd attention layers; `10` bits for `768` `(l, e)` MoE buckets) into one Gruen `EinSumcheck` per operator family — while skipping the `8` zero-padded dummy layers $l \in [24..32)$ during `F_1` partial evaluation and round $l_0$ — preserves exact active-layer prover muls (`0.0%` overhead vs `+33.3%` naive pad) while collapsing verification, recursion, and PCS openings (`[SOURCE: Sparrow, ePrint 2024/1631]` for data-parallel sumcheck):

| Operator Family (`24` Layers) | Sumchecks (`Unf -> Fold`) | Total Rounds (`Unf -> Fold`) | Round Cut | PCS Openings (`Unf -> Fold`) | Transcript (`Unf -> Fold`) |
|---|---:|---:|---:|---:|---:|
| `q_proj` (`4096 × 2880`) | `24 -> 1` | `576 -> 29` | **19.9×** | `48 -> 2` | `19.1 KB -> 0.95 KB` |
| `k_proj + v_proj` (`2 × 512 × 2880`) | `48 -> 2` | `1,008 -> 52` | **19.4×** | `96 -> 4` | `33.8 KB -> 1.72 KB` |
| `o_proj` (`2880 × 4096`) | `24 -> 1` | `576 -> 29` | **19.9×** | `48 -> 2` | `19.1 KB -> 0.95 KB` |
| Sliding-128 GQA `QK+EV` (`12` even L) | `24 -> 2` | `336 -> 36` | **9.3×** | `48 -> 4` | `11.6 KB -> 1.22 KB` |
| Full Causal GQA `QK+EV` (`12` odd L) | `24 -> 2` | `288 -> 32` | **9.0×** | `48 -> 4` | `10.1 KB -> 1.09 KB` |
| MoE Router (`32 × 2880`) | `24 -> 1` | `408 -> 22` | **18.5×** | `48 -> 2` | `13.9 KB -> 0.73 KB` |
| MoE Active-4 `gate_up` (`768` buckets) | `768 -> 1` | `19,200 -> 35` | **548.6×** | `1,536 -> 3` | `636.0 KB -> 1.14 KB` |
| MoE Active-4 `down` (`768` buckets) | `768 -> 1` | `18,432 -> 34` | **542.1×** | `1,536 -> 3` | `612.0 KB -> 1.11 KB` |
| **TOTAL (Full 24-Layer Model)** | **`1,704 -> 11` (155×)** | **`40,824 -> 269` (151.8×)** | **151.8×** | **`3,408 -> 24` (142×)** | **`1,355.6 KB -> 8.92 KB` (152×)** |

---

## 5. Corpus & Query Ledger + Proposed `docs/VERDICTS.md` Folds

- **Corpus & Search Ledger:**
  - **IACR ePrint local mirror (`/Users/ember/dev/gh/forks/IACR-eprint-mirror/`, `0` `eprint.iacr.org` network fetches):** Extracted via `pdftotext` and read at source: `2024/108` (Gruen, all 1,115 lines), `2024/1046` (Bagad–Domb–Thaler, BabyBear `Ext4` experiments pp. 31–32), `2024/1631` (Sparrow data-parallel sumcheck), `2025/1117` (Bagad–Dao–Domb–Thaler `SVO` + `EqPoly`, all 3,411 lines).
  - **`~/paperbin/` (`2,013` PDFs):** Inspected `audit-blog-zksecurity-jolt-uniskip.txt` (Kim, PR #1474), `2025-mohamed-univariate-sumcheck-gruen-skip-2505.00554.txt`, `chimera-gpu-sumcheck-backend-2026-1388.txt`, `zkdeepseek-2511.19902.txt`; regex sweep over `~/paperbin/*.txt` (`grep -liE`) found zero zkML/sumcheck works formulating block-windowed GQA `step_β` `EinSumcheck` or E2M1 bit-plane Horner MXFP4 sumcheck.
  - **Metered Search Tools:** `Scry`: **3** SQL calls (`2` rejected column/index syntax checks + `1` executed `openalex.works` token scan across `482,018,170` records through `2026-11-21`, `record_id = 328034f6-05fc-4d12-b9b1-5ae50a1e2d49`, returning `0` rows for `['zkml','sumcheck','zkllm','zktransformer'] × ['sliding','mxfp4','einsum','experts','grouped']`); `Kagi`: **0** queries.
- **What Was NOT Verified Here:** Wall-clock SIMD/GPU throughput in `breadstuffs` (counts only per `SLVG_THOUGHT.md` §II.2) and the Lean `step_β` / Gruen Mode-2 formalization in `minidregg` (Mode 1 already verifies against unmodified `AirSumcheckCubic.lean`).
- **Proposed Maintainer Folds for `docs/VERDICTS.md` (Not Edited Here):**
  1. **`VERDICTS.md` §9 (`zkTransformer` / `EinSumcheck` entry):** Upgrade `EinSumcheck` with **Gruen `eq`-factoring** (`2024/108` §3.2; `4.75×` GQA SC speedup vs `zkTransformer`, `18/25` quadratic rounds on MXFP4 `gate_up`) and **`b -> j -> k` Tensor-Factored ($\ell_0 = 5$) + E2M1 Horner MXFP4 proving** (`16.4×` smaller `Ext4` buffer `276.9 -> 16.8 MB`, `12.65×` padded / `18.36×` active BB mul speedup; record generic Toom-Cook `SVO` regression at $\ell_0 \ge 3$ on BabyBear).
  2. **`VERDICTS.md` §9 (`gptoss-int v0` / Attention):** Add **Block-Windowed Sliding-128 GQA `EinSumcheck`** (`W = 128` on the 12 even layers + zero-commitment `step_β` carry-chain reduction + $2\times$ causal pruning on the 12 odd layers): **`130.5×`** single-sliding-layer speedup and **`4.01×`** 24-layer attention+PCS speedup at $T = 16{,}384$.
  3. **`VERDICTS.md` §4 & `moe-router-binding.md` §3.4:** Record the **sumcheck MoE coupon-collector curve** (`8.00×` at $T=1 \to 2.41×$ dip at $T=8 \to 7.50×/8.26×$ recovery at $T=16{,}384$) and **24-layer uniform `EinSumcheck` folding** (`1,704 -> 11` sumchecks, `152×` transcript/round cut at `0.0%` prover mul overhead with zero-layer skipping).
