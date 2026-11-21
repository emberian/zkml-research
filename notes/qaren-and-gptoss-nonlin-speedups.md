# Qāren (`ePrint 2026/347`) Closed & `gptoss-int v0` Non-Arithmetic Wall Cut `2.07×–3.15×`

2026-11-21. Primary source `ePrint 2026/347` (*"Relaxed Modular PCS from Arbitrary PCS and Applications to SNARKs for Integers"*, Shirzad, Sridhar, Papadopoulos, Papamanthou) read in full (`§§1–5`, `Appendices A–C`) and priced deterministically against byte-sliced helper-free LogUp-GKR (**D1b**); full 24-layer non-arithmetic cell/lookup census and four exact-equivalence rewrites verified bit-for-bit against shipped `openai/gpt-oss-20b` (`6cee5e81`) in [gptoss_nonlin_and_qaren_pricing.py](file:///Users/ember/dev/zkml-research/research/speedup_wave_2026_11_21/experiments/gptoss_nonlin_and_qaren_pricing.py).

---

## Executive Verdicts (Current Truth)

1. **`AGENDA.md:111` (`Qāren`, `ePrint 2026/347`) — CLOSED, REJECT as Mod-PCS and as integer arithmetic backend (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`):**
   - **Bit-per-cell commitment inflation (`24×–332.8×` on primitives; `2,240×–165,777×` on Mod-PCS):** Qāren's batched Integer Commitment Scheme (`ICS`, `Construction 1`, `eprint_2026_347.txt:1118-1146`) expands each $B$-bit integer into $B$ binary $\mathbb{F}_p$ evaluations (`t B` committed $\mathbb{F}_p$ cells for $t$ integers), doubles slot width $B = 2^{\lceil \log_2(2 B_{\text{in}})\rceil}$ in `PIOR 5`/`PIOR 6` to prevent cyclic wrap (`lines 1516-1531, 1624-1636`), and in its relaxed Mod-PCS (`Constructions 2–5`, `lines 1834-2038`) packs an $N = 2^\mu$-element $B$-bit integer MLE into a single integer $e_{p,\alpha} = \sum_{i=0}^{N-1} p_i \alpha^i$ with $\alpha_{\text{source}} > 2^{7 B \mu}$ (`line 1838`), paying **`2,240 N` $\mathbb{F}_p$ cells** at commitment time ($N = 2^{20}, B = 16$), **`4,497 N` cells** after `2×` commitment switching ($\alpha_{\text{target}} = q \alpha_{\text{source}}$), and **`112,017 N` (non-adaptive) / `165,777 N` (adaptive) $\mathbb{F}_p$ cells** across `2×`/`3×` `ROKCoreEval` (`MaSDAK + Range`) — while still only achieving *rational* extractability requiring a separate PIOP lookup for integrality (`lines 144-146`).
   - **Four constructive completeness & soundness bugs in `2026/347` as printed (`[SOURCE]`, `[DERIVED]`, `[EXECUTED]`):**
     - **BUG-Q1 (`[REFUTED: ePrint 2026/347 Lemma 4.6 & PIOR 1 completeness]`):** `Lemma 4.6` (`line 1250`) claims $\tilde{m}(\mathrm{Rot}_\sigma(x))$ is multilinear. False: `Def. 4.5`'s carry chain $c[j]$ multiplies $x_0$ across coordinates $1 \dots \mu-1$, giving $\tilde{m}(\mathrm{Rot}_1(x))$ individual degree $\mu$ in $x_0$. At $\mu = 2, m = [1,0,0,0], r = (2,0) \in \mathbb{F}_p^2$, true $\widetilde{m'}(2,0) = 0 \neq \tilde{m}(\mathrm{Rot}_1(2,0)) = p - 2$; consequently **honest $1 + 1 = 2$ is rejected by `PIOR 1` (`RAdd-Oracle`, `lines 1279-1284`)** (`LHS = 0 != RHS = 4`).
     - **BUG-Q2 (`[REFUTED: ePrint 2026/347 PIOR 1 & PIOR 2 soundness as written]`):** `PIOR 1` Step 5 (`lines 1290-1306`) checks booleanity on $(a, b, c) \in R_{\text{Bin}}^3$, omitting carry $\tilde{k} \in R_{\text{Bin}}$ and slot-boundary reset $k_i[0] = 0$. Setting $k[0] \equiv (\mathrm{Int}(a)+\mathrm{Int}(b)-\mathrm{Int}(c))(2^{tB}-1)^{-1} \pmod p$ forges false range claims (`7 <= 3`) on $\{0,1\}^\mu$ with probability `1`; even with binary $k \in \{0,1\}^{tB}$, omitting $k_i[0] = 0$ bleeds carries across batch slots (`8 + 8 = 0` in slot 0, `0 + 0 = 1` in slot 1).
     - **BUG-Q3 (`[REFUTED: ePrint 2026/347 PIOR 5 & PIOR 6 completeness for integers with bit carries]`):** `PIOR 5` (`lines 521, 1538-1564`) and `PIOR 6` (`lines 609, 1638-1684`) check $\mathrm{NTT}(a) \circ \mathrm{NTT}(b) = \mathrm{NTT}(c)$ on binary vectors $a,b,c \in \{0,1\}^B$, omitting `[LNS20]`'s carry term $(X - 2) k_{\text{carry}}(X)$. Honest $3 \times 3 = 9$ (`(1+X)^2 = 1+2X+X^2 != 1+X^3`) and honest division $5 = 3\cdot 1 + 2$ fail verification.
     - **BUG-Q4 (`[SOURCE: eprint_2026_347.txt:1383, 1465-1471]`, `[EXECUTED]`):** `PIOR 3` writes $Z_H(\omega) = 0$ instead of $Z_H(r) = r^B - 1$; `PIOR 4` sums over batch variables $y \in \{0,1\}^\tau$ without $\widetilde{\mathrm{eq}}(\rho_y, y)$, letting opposite NTT errors cancel ($q_0(X) + q_1(X) = 0$).
   - **Standalone primitives (`Rot_σ` and Barycentric `Lagrange-Check`, `[DERIVED]`, `[EXECUTED]`):**
     - `Rot_σ` direct point substitution $\tilde{m}(\mathrm{Rot}_\sigma(r))$ is unusable (`BUG-Q1`). Carry-free XOR/RoPE half-swaps (`x_5 -> 1 - x_5` in [layer.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L186-L190)) are already degree-1 virtual involutions; genuine cyclic shifts mod $2^\mu$ require a **width-2 carry-automaton sumcheck kernel** $\widetilde{\mathrm{shift}}_\sigma(r, x)$ ($2\times 2$ matrix product per bit, $O(\mu)$ verifier, verified in script).
     - Repaired Barycentric `Lagrange-Check` (`PIOR 3–4`, $1$ size-$N$ `Lag` commitment independent of batch $t$) does **not** help `gptoss-int v0` (YaRN RoPE in [tables.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/tables.py#L21-L40) is a $2\times 2$ real rotation table, not an FFT/NTT), **but is worth holding for `vFHE`** (`VERDICTS.md` §3b, §9) whenever SIMD-slot (NTT) commitments must bridge to coefficient-domain rescale (`Hole B`), replacing $\log_2 N = 13$ butterfly GKR layers with one $N$-cell `Lag` MLE.

2. **`gptoss-int v0` 24-Layer Non-Arithmetic Wall — Cut `2.07×–2.24×` (`2.57×–3.15×` vs bit-blasted `norm_int`) with Zero Output Change (`[DERIVED]`, `[EXECUTED]`):**
   - Across all 24 layers at $T = 4096$, combining four exact-equivalence algebraic rewrites cuts non-arithmetic committed $\mathbb{F}_p$ cells from **`204.38B → 98.75B` (`-105.63B` cells, `2.07×`; `254.14B → 98.75B` = `2.57×` vs bit-blasted `norm_int`)**, cuts table/range lookups from **`214.75B → 95.34B` (`-119.41B` lookups, `2.25×`)**, cuts $T = 1$ decode non-arithmetic cells from **`29.87M → 13.34M/tok` (`2.24×`; `3.15×` vs bit-blast)**, and cuts `D1b + WHIR(ρ=1/4)` prover base-mul equivalents by **`2.21×–2.29×`**.
   - Verified bit-identical (`0` integer deviations, **9/9 SHA-256 intermediate digests equal** to [g1-numpy.json](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/g1-numpy.json) on real Layer-0 `gpt-oss-20b` weights and **9/9 SHA-256 digests equal** to unmodified `layer_int` on Layer-9 massive residuals with $s \in \{7, 12\}$).

---

## 1. Exact Pricing of Qāren (`ePrint 2026/347`) vs. Byte-Sliced `D1b` LogUp-GKR

### 1.1 Primitive Arguments at Batch Size $t = 2^{20}$ (`[SOURCE: eprint_2026_347.txt:1118-1785]`, `[DERIVED]`, `[EXECUTED]`)

Let $B_{\text{in}}$ be the integer bit-width and $t = 2^\tau = 2^{20}$ be the batch count.
- **Range (`PIOR 2 → PIOR 1`):** Slot width $B = 2^{\lceil \log_2 B_{\text{in}}\rceil}$. Commits input $\tilde{a}$ ($tB$), slack $\tilde{b}$ ($tB$), and carry $\tilde{k}$ ($tB$) = **`3 t B` $\mathbb{F}_p$ cells**; $\beta + \tau$ sumcheck rounds.
- **Multiplication (`PIOR 5`) & Division/`rq` (`PIOR 6`):** No-overflow mask $\tilde{m}(x,y) = 1 - x_{\beta-1}$ (`lines 1513, 1621`) forces slot width **$B = 2^{\lceil \log_2(2 B_{\text{in}})\rceil} \ge 2 B_{\text{in}}$**.
  - *Paper as printed (completeness-broken without carry):* commits 3 bit-vectors ($3 t B$) + 3 NTT MLEs ($3 t B$) + 3 `Lag` MLEs ($3 t B$ as written in `Def. 4.10` `line 1363`, or $B$ if deduplicated across the 3 NTT checks at shared $r$) = **`6 t B + B` (steelman) to `9 t B` $\mathbb{F}_p$ cells**; $\beta + \tau$ sumcheck rounds.
  - *Carry-repaired (`[LNS20]` $(2 - \omega^i)\mathrm{NTT}(k_{\text{carry}})_i$):* $k_{\text{carry}}[j] \in [0, B_{\text{in}}]$ adds $\lceil \log_2(B_{\text{in}}+1)\rceil$ bit-planes plus $\mathrm{NTT}(k_{\text{carry}})$ = **`(7 + \lceil \log_2(B_{\text{in}}+1)\rceil) t B + B` $\mathbb{F}_p$ cells**.
- **Byte-sliced `D1b` Helper-Free LogUp-GKR (`Assurance/AirSumcheckCubic.lean`):** Commits `m + 256` base cells per byte-lookup table (`0` extension-field inverse helper columns). For `rq(y, k)` with $k = B_{\text{in}} - 16$ and $q \in [-32640, 32639]$, commits 2 `int8`-limb cells for $q$ plus $\lceil k/8\rceil - 1$ split cells for $r$ (`r_0` virtual from $y + 2^{k-1} - 2^k q$).

| $B_{\text{in}}$ | Qāren `PIOR 2` Range Cells | `D1b` Range Cells | **Range Ratio** | Qāren `PIOR 5` Mul (`B_slot`, sc rds) Repaired Cells | `D1b` Mul Cells | **Mul Ratio** | Qāren `PIOR 6` `rq` (Broken / Repaired) Cells | `D1b` `rq` Cells | **`rq` Ratio (Brk / Rep)** |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **16** | `50.33M` (`48 t`) | `2.10M` (`2 t`) | **`24.0×`** | `268.44M` (`B=32`, `25` rds, `256 t`) | `4.19M` (`4 t`) | **`64.0×`** | `201.33M` / `402.65M` (`192 t` / `384 t`) | `2.10M` (`2 t`) | **`96.0×` / `192.0×`** |
| **32** | `100.66M` (`96 t`) | `4.19M` (`4 t`) | **`24.0×`** | `580.91M` (`B=64`, `26` rds, `554 t`) | `8.39M` (`8 t`) | **`69.3×`** | `402.65M` / `872.42M` (`384 t` / `832 t`) | `3.15M` (`3 t`) | **`128.0×` / `277.3×`** |
| **48** | `201.33M` (`192 t`) | `6.29M` (`6 t`) | **`32.0×`** | `1,744.83M` (`B=128`, `27` rds, `1664 t`) | `16.78M` (`16 t`) | **`104.0×`** | `805.31M` / `1,744.83M` (`768 t` / `1664 t`) | `5.24M` (`5 t`) | **`153.6×` / `332.8×`** |
| **64** | `201.33M` (`192 t`) | `8.39M` (`8 t`) | **`24.0×`** | `1,879.05M` (`B=128`, `27` rds, `1792 t`) | `23.07M` (`22 t`) | **`81.5×`** | `805.31M` / `1,879.05M` (`768 t` / `1792 t`) | `7.34M` (`7 t`) | **`109.7×` / `256.0×`** |

- **On `gptoss-int v0` `norm_int` (`48` norms, $T = 4096 \implies 566.23\text{M}$ elements, `[DERIVED]`, `[EXECUTED]`):** Three shifts per element (`xs`, `t`, output `rq` at up to 64 bits $\implies B = 128$) cost **`1.305T` (broken) / `3.044T` (repaired) $\mathbb{F}_p$ cells** under Qāren vs **`15.43B` cells** under our `D1b` Speedup (a)+(b) — an **`84.5×–197.2×` blowup**.
- **On Relaxed Mod-PCS (`Constructions 2–5`, $N = 2^{20}, \mu = 20, B = 16$, `[SOURCE: lines 1838, 1929-2038]`, `[DERIVED]`):** $\log_2 \alpha_{\text{source}} \ge 7 B \mu = 2,240$, so `ICS.Commit(e_{p,α_source})` alone commits **`2.349B` $\mathbb{F}_p$ cells** (`2,240×` native PCS; `4,096×` after power-of-two rounding to $2^{32}$). Commitment switching (`\alpha_{\text{target}} = q \alpha_{\text{source}}`, $q > 2^{16}$) commits a second **`2.367B`-cell** polynomial (`4,497×` commit-only), and the `2×` non-adaptive / `3×` adaptive `ROKCoreEval` calls (`t = 4` integers $[l, m, r, h]$ of bit-width $\approx N \log_2 \alpha$) inflate total committed cells to **`112,017×` / `165,777×`** native PCS.

---

## 2. Four Exact-Equivalence Speedups on `gptoss-int v0` ([layer.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py))

All four reductions preserve **100% bit-identical `gptoss-int v0` integer semantics** (`[DERIVED]`, `[EXECUTED]`).

### Speedup (a): Dynamic-Row-Shift `norm_int` ([layer.py:169-184](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L169-L184)) via 15-Entry Row-Level `TwoPow`

In `norm_int`, each row $i \in [0, T)$ computes `mx = max_c |x[i, c]| < 2^39` and dynamic shift $s_i = \sum_{k=0}^{13} \mathbf{1}[\mathrm{mx}_i \ge 2^{25+k}] \in \{0, \dots, 14\}$, shared across all $D = 2880$ columns. Instead of bit-decomposing `x` (`39` bits) and `x * Rc` (`64` bits) (`+88` cells/element) or performing `2880 T` per-element `TwoPow` lookups + `14` 39-bit threshold comparisons/row:
1. **One 15-entry `TwoPow` lookup per row (`T` lookups, not `2880 T`):** Public table $\mathcal{T}_{\text{norm}}[s]$ returns $(s,\; P_s = 2^s,\; H_s = \lfloor 2^{s-1}\rfloor,\; P_{\text{inv}} = 2^{14-s},\; E_s = \mathrm{rq0}(E, 2s),\; B_{\text{lo}} = \mathbf{1}_{s\ge 1} 2^{24+s},\; S_{\text{mx}} = 2^{13}\mathbf{1}_{s=0} + P_{\text{inv}}\mathbf{1}_{s\ge 1})$, eliminating the runtime `rq0(E, 2s)` circuit completely (`[DERIVED]`).
2. **One static 38-bit range check proves $s_i$ from $\mathrm{mx}_i$ (`14×` fewer `s`-checks):** Checking $(\mathrm{mx}_i - B_{\text{lo}}) \cdot S_{\text{mx}} \in [0, 2^{38})$ enforces $0 \le \mathrm{mx}_i < 2^{25}$ when $s_i = 0$ and $2^{24+s_i} \le \mathrm{mx}_i < 2^{25+s_i}$ when $s_i \in \{1..14\}$ (`[DERIVED]`, `[EXECUTED]`).
3. **Static power-of-two remainder bounds via $P_s \cdot P_{\text{inv}} = 2^{14}$:**
   - For `xs = rq0(x, s)`: define $\hat{r}_{\text{xs}} := (x + H_s) P_{\text{inv}} - 2^{14} \mathrm{xs}$. Since $2^{14} = P_s P_{\text{inv}}$ and $P_{\text{inv}} > 0$, checking $\hat{r}_{\text{xs}} \in [0, 2^{14})$ (`2` byte lookups) over $\mathbb{Z}$ enforces $0 \le x + H_s - P_s \mathrm{xs} < P_s$ — proving both `xs == x` when $s = 0$ ($P_0 = 1, H_0 = 0 \implies \hat{r}_{\text{xs}} = 0$) and `xs == rq(x, s)` when $s \ge 1$ (`[DERIVED]`, `[EXECUTED]`).
   - For `t = rq(x * Rc, 24 + s)`: reusing the **same** row scalar $P_{\text{inv}}$ (`0` extra lookups), checking $\hat{r}_t := (x \cdot \mathrm{Rc}) P_{\text{inv}} + 2^{37} - 2^{38} t \in [0, 2^{38})$ (`5` byte lookups) proves $t = \mathrm{rq}(x \cdot \mathrm{Rc}, 24 + s)$ (`|t| <= 2^24` unconditionally since $\sigma \ge \max(|\mathrm{xs}|, 11121)$).

### Speedup (b): Fused `ClampRq`, `[0, 255) × [0, 256)` Cartesian `int8` Limbs & 4-into-1 `gate_up → key` Collapse

1. **Exact Cartesian `[-32640, 32639]` decomposition (`[DERIVED]`, `[EXECUTED]`):** Because $32639 - (-32640) + 1 = 65,280 = 255 \times 256$, $y \in [-32640, 32639]$ holds **iff** $y + 32640 = 256 u_{\text{hi}} + u_{\text{lo}}$ with $u_{\text{hi}} \in [0, 255)$ and $u_{\text{lo}} \in [0, 256)$ (**2 cells, 2 lookups, zero slack**), and $(a_{\text{hi}}, a_{\text{lo}}) = (u_{\text{hi}} - 127, u_{\text{lo}} - 128)$ are identically [jaxint.py](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/jaxint.py#L18-L22)'s balanced `int8` matmul limbs ($256 a_{\text{hi}} + a_{\text{lo}} = y$, saving a second decomposition before matmul). Similarly, `up ∈ [-28672, 28672]` (`57,345 = 224 × 256 + 1`) uses `[0, 224) × [0, 256)` when $b_{\text{top}} = 0$ and $y = 28672$ when $b_{\text{top}} = 1$.
2. **Virtual-Quotient Signed-Slack `ClampRq(z, k, lo, hi)` (`[DERIVED]`, `[EXECUTED]`):** Absorbing scaled bias $b_{\text{sc}} \cdot 2^k$ into pre-shift $z$ ($\lfloor \mathrm{dot}/2^k\rfloor + b_{\text{sc}} = \lfloor (\mathrm{dot} + b_{\text{sc}} 2^k)/2^k\rfloor$ for $k \ge 1$), define virtual un-clamped quotient $q_{\text{virt}} := y + (1 - 2 b_{\text{dir}}) u_{\text{slack}}$ ($b_{\text{dir}} \in \{0,1\}, u_{\text{slack}} \in [0, 2^{8 L_q})$) and enforce:
   $$z + 2^{k-1} = 2^k q_{\text{virt}} + r \;\;(0 \le r < 2^k), \qquad (1 - b_{\text{dir}})\,u_{\text{slack}}\,(y - \mathrm{hi}) = 0, \qquad b_{\text{dir}}\,u_{\text{slack}}\,(y - \mathrm{lo}) = 0.$$
   `q_raw`, `s_+`, and `s_-` are completely eliminated (`3` multi-byte range checks collapsed into **`1`** `u_slack` check bounded by exact $L_1$ weight-row census on `gpt-oss-20b`: `L_q = 2` bytes on `rope_int`, `3` bytes on `norm_int` and `q_proj`, `4` bytes on `k_proj, v_proj, up, key`).
3. **Exact 4-into-1 `gu_even → gate → key` double-rounding collapse ([layer.py:254-259](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L254-L259), `[DERIVED]`, `[EXECUTED]`):**
   - Across all `4,423,680` `gate_up_proj` rows of `gpt-oss-20b`, shift $s \in [1, 11]$ (`96.66%` have $s \le 8$, `1` byte) (`[EXECUTED]`).
   - By the exact integer floor identity $\lfloor (\lfloor A/m\rfloor + c)/n\rfloor = \lfloor (A + cm)/(mn)\rfloor$ ($\forall A, c \in \mathbb{Z}, m,n \ge 1$) and monotony $\mathrm{rq}(28672, 4) = 1792 = \mathrm{GHI}\ll \mathrm{GK}$, all four steps (`rq2` $\to$ `+bias` $\to$ `gate = min(..., 28672)` $\to$ `key = clamp(rq(gate, 4), -4096, 1792)`) equal **one single `ClampRq`**:
     $$\mathrm{key} = \mathrm{clamp}\!\left(\left\lfloor \frac{\mathrm{dot}_{\text{even}} + b_{\text{even}} 2^s + 17 \cdot 2^{s-1}}{2^{s+4}} \right\rfloor,\; -4096,\; 1792\right),$$
     with `key ∈ [-4096, 1792]` proved at **0 extra range lookups** by `(key + 4096, glu) ∈ G_TAB` (`30.03 → 7.97` cells, `31.03 → 6.97` lookups/channel: **`3.77×` cell / `4.46×` lookup reduction** across `1.132B` channels at $T = 4096$).
   - **Bonus (`down_proj` exact-shift census, `[EXECUTED]`):** Across all `2,211,840` `down_proj` rows, **`2,037,223` (`92.105%`) have $s \le 0$** (`s ∈ [-9, 0]`), where `rq2` in [model.py:38-40](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/model.py#L38-L40) is an **exact left shift** requiring `0` rounding and `0` remainder lookups!

### Speedup (c): Row-Broadcast Attention Division (`EinSumcheck` `c ∈ F_1` + Sliding-128 3-Byte Remainder)

In [layer.py:225-226](file:///Users/ember/dev/zkml-research/research/exact_recompute_2026_11_06/layer.py#L225-L226), `o = (2 * acc + Zt) // (2 * Zt)` divides `[T, 64, 64]` by row-sum `Zt` of shape `[T, 64, 1]`:
1. **`EinSumcheck` broadcast (`ih,ihc -> ihc`, `[DERIVED]`, `[EXECUTED]`):** Head-channel $c \in [64]$ appears only in `o` ($F_1 = \{c\}, F_{\ge 2} = \{i, h\}, S = \emptyset$). Binding $c$ directly to verifier randomness $r_c \in \mathbb{F}_{\text{ext}}^6$ avoids `64×` `Zt` expansion (`-395.84M` cells at $T = 4096$) and runs `0` sumcheck rounds on $c$ (`64×` smaller sumcheck domain `64 T` vs `4096 T`).
2. **Sliding-128 3-byte remainder (`[DERIVED]`, `[EXECUTED]`):** On all 12 even layers (`l % 2 == 0`), each row sums $\le 128$ window scores + `1` sink with `EX[u] <= 32768`, so $65,536 \le 2 Z_t \le 258 \times 32,768 = 8,454,144 < 2^{24}$ for **every** $T$ (and on odd layers for $i < 255$). Both $\mathrm{rem}$ and $2 Z_t - 1 - \mathrm{rem}$ drop from `4` bytes to **`3` bytes (`25%` lookup cut)**.
3. **Unified `EXP_TAB_AUG` (`3,096` entries, `[DERIVED]`, `[EXECUTED]`):** Appending `(2840 + b, 0)_{b=0}^{255}` to `EXP_TAB` (`EX[0..2839] >= 1`) fuses `mx >= z`, shift `u = (mx - z) >> sh_u`, and clip `u >= 2840 => e = 0` into `(u - b_clip*(256 w_1 + ...), e) ∈ EXP_TAB_AUG` + `b_clip * e = 0` (`12 → 5.25` lookups/score).

### Speedup (d): Exhaustive Audit of All 11 `clamp` / `minimum` Sites in `layer_int` (`[DERIVED]`, `[EXECUTED]`)

| Site in `layer.py` | Operation | 24L Elems / Tok | Mathematical Status over Valid Domain | Action |
|---|---|---:|---|---|
| `183` (`196, 229`) | `norm_int` out `[-32640, 32639]` | `138,240` | **LIVE** (1-sparse $x \implies \pm 2,115,714$; `0` hits on G3) | Fused `ClampRq` (`L_q=3`) |
| `198` | `q_proj` `[-32640, 32639]` | `98,304` | **LIVE** on `98,006` rows ($\pm 15.08\text{M}$); **DEAD** on `298` rows | Fused `ClampRq` + skip `298` rows |
| `199` | `k_proj` `[-32640, 32639]` | `12,288` | **LIVE** on `12,247` rows ($\pm 30.82\text{M}$); **DEAD** on `41` rows | Fused `ClampRq` + skip `41` rows |
| `200` | `v_proj` `[-32640, 32639]` | `12,288` | **LIVE** on all `12,288` rows ($\pm 68.30\text{M}$) | Fused `ClampRq` (`L_q=4`) |
| `202, 203` | `rope_int(q, k)` `[-32640, 32639]` | `110,592` | **LIVE** (YaRN `att=1.3466` $\implies \max(|C|+|S|)=31,201 \implies \pm 62,158$) | Fused `ClampRq` (`L_q=2`) |
| **`227`** | **`attn o` `[-32640, 32639]`** | **`98,304`** | **100% DEAD** ($v \in [-32640,32639], e, e_s \ge 0, Z_t \ge 32768 \implies o \in [-32640,32639]$) | **DELETE (`-3.22B` cells/lkps @ 4k)** |
| **`256`** | **`gate = minimum(gu_even, 28672)`** | **`276,480`** | **100% SUBSUMED** by line `258` upper clamp `1792` ($\forall g \in \mathbb{Z}$) | **DELETE (`-10.19B` cells @ 4k)** |
| `257` | `MoE up` `[-28672, 28672]` | `276,480` | **LIVE** ($\pm 370.4\text{M}$) | Fused `ClampRq` (`L_k=1.03, L_q=4`) |
| **`258`** | **`key` `clamp(rq(gate,4), -4096, 1792)`** | **`276,480`** | **UPPER-DEAD** (`rq(<=28672, 4) <= 1792`); output range absorbed by `G_TAB` | **4-into-1 `ClampRq` + `0` key lkps** |
| **`260`** | **`SwiGLU h_` `[-32640, 32639]`** | **`276,480`** | **100% DEAD** (`up ∈ [-28672,28672], G ∈ [-670,28672] => h_ ∈ [-21504,28672]`, `|prod| < p_BB/2`) | **DELETE (`-9.06B` cells/lkps @ 4k)** |

- **Standalone savings from dead / subsumed clamps alone at $T = 4096$ (`24` layers, `[DERIVED]`, `[EXECUTED]`):** Deleting pure dead two-sided clamps (`lines 227 + 260`: `1.535B` elements) saves **`12,280.92M` (`12.28B`) committed cells + `12,280.92M` range lookups**; including subsumed `line 256` + `line 258-hi` + `339` unconditionally in-range `q/k` rows saves **`28,141.02M` (`28.14B`) committed cells + `25,874.70M` range lookups**.

---

## 3. Exact 24-Layer Non-Arithmetic Cost Census (`gptoss-int v0`, `[EXECUTED]`)

### 3.1 Per-Token & Full-Pass Scaling Across $T \in \{1, 128, 1024, 4096\}$

*(Public table footprint across the entire model is only **`9,927` entries** = `[0,256) + [0,255) + [0,224) + [0,128) + [0,64) + TwoPow(15) + EXP_TAB_AUG(3096) + G_TAB(5889)` $< 2^{13.3}$, so multiplicity commitments are negligible.)*

| Seq Len $T$ | Naive Cells / Tok | **Opt Cells / Tok** | **Cell Speedup (vs Bit-Blast `norm`)** | Naive Lookups / Tok | **Opt Lookups / Tok** | **Lookup Speedup** | **`D1b + WHIR(1/4)` Prover Mul Speedup** |
|---:|---:|---:|---:|---:|---:|---:|---:|
| **`1`** | `29,874,603` | **`13,342,728`** | **`2.24×` (`3.15×`)** | `32,406,723` | **`14,178,230`** | **`2.29×`** | **`2.29×`** |
| **`128`** | `31,045,035` | **`13,952,328`** | **`2.23×` (`3.10×`)** | `33,577,155` | **`14,690,294`** | **`2.29×`** | **`2.29×`** |
| **`1,024`** | `35,685,867` | **`16,493,484`** | **`2.16×` (`2.90×`)** | `38,217,987` | **`16,844,714`** | **`2.27×`** | **`2.27×`** |
| **`4,096`** | `49,896,507` | **`24,109,065`** | **`2.07×` (`2.57×`)** | `52,428,627` | **`23,276,075`** | **`2.25×`** | **`2.21×`** |

### 3.2 Full 24-Layer Per-Subproblem Breakdown at $T = 4096$ (`[EXECUTED]`)

| Subproblem (`24` layers, $T = 4096$) | Naive Cells | **Opt Cells** | **Ratio** | Naive Lookups | **Opt Lookups** | **Ratio** |
|---|---:|---:|---:|---:|---:|---:|
| 1. `norm_int` ($\times 48$, dynamic `s ∈ 0..14`) | `19,411.11M` *(+`49.76B` bit-blast)* | **`15,434.91M`** | **`1.26×` (`4.48×`)** | `21,675.84M` | **`16,567.17M`** | **`1.31×`** |
| 2. `attn q/k/v` (`rq2 + clamp`) | `8,187.17M` | **`4,456.91M`** | **`1.84×`** | `8,690.49M` | **`4,458.30M`** | **`1.95×`** |
| 3. `YaRN rope_int` (`rq + clamp` on `q, k`) | `4,982.83M` | **`2,717.91M`** | **`1.83×`** | `5,435.82M` | **`2,717.91M`** | **`2.00×`** |
| 4. `attn causal max + EXP_TAB_AUG` | `82,173.30M` | **`43,812.56M`** | **`1.88×`** | `82,160.71M` | **`36,953.25M`** | **`2.22×`** |
| 5. `attn // (2*Zt) + dead clamp (227)` | `6,838.81M` | **`2,793.50M`** | **`2.45×`** | `8,053.06M` | **`3,598.81M`** | **`2.24×`** |
| 6. `attn o_proj` (unclamped `rq2`) | `2,264.92M` | **`1,875.47M`** | **`1.21×`** | `2,548.04M` | **`2,158.58M`** | **`1.18×`** |
| 7. `router rq2 + top-4 + softmax-4` | `37.58M` | **`34.44M`** | **`1.09×`** | `41.02M` | **`37.88M`** | **`1.08×`** |
| 8. `MoE gu_even → gate → key → G_TAB` | `34,011.64M` | **`9,020.85M`** | **`3.77×`** | `35,144.10M` | **`7,888.39M`** | **`4.46×`** |
| 9. `MoE gu_odd → up` (`rq2 + clamp`) | `18,157.17M` | **`7,965.01M`** | **`2.28×`** | `19,289.63M` | **`7,965.01M`** | **`2.42×`** |
| 10. `MoE SwiGLU h_ + dead clamp (260)` | `12,457.08M` | **`3,397.39M`** | **`3.67×`** | `13,589.54M` | **`4,529.85M`** | **`3.00×`** |
| 11. `MoE down_proj (92.1% s<=0) + ws rq` | `15,854.47M` | **`7,241.79M`** | **`2.19×`** | `18,119.39M` | **`8,463.66M`** | **`2.14×`** |
| **TOTAL (`24` layers, $T = 4096$)** | **`204,376.09M`** *(+`49.76B`)* | **`98,750.73M`** | **`2.07×` (`2.57×`)** | **`214,747.65M`** | **`95,338.80M`** | **`2.25×`** |

---

## 4. Corpus, Instrument & Query Ledger

- **External search queries:** `Scry`: `0`; `Kagi`: `0`; `eprint.iacr.org` network fetches: `0`.
- **Primary sources & artifacts read/executed locally:**
  - `IACR ePrint 2026/347` (`Qāren`): full extracted text (`3,303` lines) from local mirror `/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026/347.pdf`.
  - `openai/gpt-oss-20b` (`rev 6cee5e81ee83`): local safetensors shards `/Users/ember/models/gpt-oss-20b/6cee5e81` (`model-00000/1/2-of-00002.safetensors`, `np.memmap` exact $L_1$ & `rowexp` census across all `6,828,288` BF16+MXFP4 rows).
  - Repo modules: `research/exact_recompute_2026_11_06/{layer,model,tables,weights,params-v0,params-v1,g1-numpy}.*`, `research/zktransformer_2026_11_20/experiments/exp_pricing.py`, `notes/{spain-celer-verdicts,lookup-ram-verdicts,zktransformer-verdicts}.md`.
  - Verification command (`exit 0`): `python3 research/speedup_wave_2026_11_21/experiments/gptoss_nonlin_and_qaren_pricing.py`.

---

## 5. Proposed Maintainer Folds (Not Edited Here)

1. **`docs/AGENDA.md:111-113`:** Replace *"New read-and-price item: eprint 2026/347, exact-integer Mod-PCS from any PCS, hash-based"* with:
   > **CLOSED (`notes/qaren-and-gptoss-nonlin-speedups.md`)**: `Qāren` (`ePrint 2026/347`) rejected as Mod-PCS and integer backend — its 1-bit-per-felt `ICS` + `2×` commitment-switching (`α_target = q α_source`, `log₂ α_source ≥ 7 B μ`) inflates $N=2^{20}, B=16$ commitments `2,240×` (`112,017×–165,777×` with `ROKCoreEval`), inflates `rq`/mul/range `24×–333×` vs byte-sliced `D1b` LogUp-GKR, and has four constructive completeness/soundness bugs as printed (`Lemma 4.6` non-multilinearity breaking `PIOR 1` on $1+1=2$; missing `k` booleanity + boundary reset in `PIOR 1/2`; missing `[LNS20]` carry polynomial in `PIOR 5/6` failing on $3\times 3=9$; unweighted batch sum in `PIOR 4`). Hold only repaired Barycentric `Lagrange-Check` (`PIOR 3–4`) for `vFHE` NTT-to-coefficient bridges.
2. **`docs/VERDICTS.md` §5 & §9 (`gptoss-int v0` proving):** Record the exact 24-layer non-arithmetic census (`29.87M → 13.34M` cells/tok at $T=1$, `49.90M → 24.11M` cells/tok at $T=4096$, **`2.07×–3.15×`** cell cut and **`2.25×–2.29×`** lookup cut, 9/9 SHA-256 layer digests bit-identical on real `gpt-oss-20b` weights): (a) 15-entry row-level `TwoPow` `norm_int`, (b) virtual-quotient `ClampRq` + `[0,255)×[0,256)` Cartesian `int8` limbs + exact 4-into-1 `gu_even → key` collapse + `92.1%` exact shift-up `down_proj`, (c) `EinSumcheck` (`c ∈ F_1`) attention division + 3-byte sliding-128 remainder + `EXP_TAB_AUG`, and (d) deletion of provably-dead clamps `layer.py:227, 256, 258-hi, 260` (`-28.14B` cells / `-25.87B` lookups alone at $T=4096$).
