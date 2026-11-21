# Multi-Round $2^k$-ary WHIR / BaseFold PCS + `GMask` Sumcheck Blinding Across `darkvfhe` and `qwen35audit`

**Date:** 2026-11-21 · **Lane:** `whir-gmask-pcs-compress`  
**Owned Artifacts:** [`native/darkvfhe/src/whir_pcs.rs`](../native/darkvfhe/src/whir_pcs.rs) · [`native/darkvfhe/tests/whir_gmask_compress.rs`](../native/darkvfhe/tests/whir_gmask_compress.rs) · [`native/qwen35audit/src/whir_ext4.rs`](../native/qwen35audit/src/whir_ext4.rs) · [`native/qwen35audit/tests/whir_ext4_compress.rs`](../native/qwen35audit/tests/whir_ext4_compress.rs)  
**Companion Citations:** [`native/darkproof/src/gmask.rs:1-90`](../native/darkproof/src/gmask.rs) · [`notes/darkvfhe-succinct-pcs-and-custodian-gdn.md`](darkvfhe-succinct-pcs-and-custodian-gdn.md) · [`notes/two-regime-calculator.md`](two-regime-calculator.md) · `/Users/ember/dev/minidregg/Assurance/TwoRegimeQueryBudget.lean`

**Claim tags (`AGENTS.md`):** `[EXECUTED]` compiled & run in `--release` on this machine · `[DERIVED]` exact algebra / probability · `[SOURCE]` inspected at named `path:line` · `[REFUTED: scope]` bounded falsification · `[OPEN]` unverified boundary.

---

## 0. Executive Summary

Prior 1-step Ligero / Reed–Solomon commitments in [`native/darkvfhe/src/succinct_pcs.rs`](../native/darkvfhe/src/succinct_pcs.rs) (`2,616 KiB` at $d=64$, `22,747 KiB` at $d=4096$) and [`native/qwen35audit/src/pcs_ext4.rs`](../native/qwen35audit/src/pcs_ext4.rs) (`4,644 KiB` `Qwen3.5` leaf receipt, `4,709–5,295 KiB` `Qwen3.8-Flash-Next` leaf receipt) stopped after row combination, serializing raw length-$W$ extension vectors `u_eval` / `u_prox` (`O(\sqrt{N})` wire elements), and sent unblinded sumcheck round polynomials (`darkvfhe-succinct-pcs-and-custodian-gdn.md` §1.1 `[OPEN]`) `[SOURCE: succinct_pcs.rs:923-1398, pcs_ext4.rs:1-520]`.

This lane builds **multi-round $2^k$-ary `WHIR` / BaseFold coset-NTT folding** paired with **`GMask` separable univariate sumcheck round blinding** across both crates:

1. **`darkvfhe::whir_pcs` (`WhirPcs61` + `GMask61` over $\mathbb{F}_{p_0^3}$, $p_0 = 2^{61}-376831$, $|\mathbb{F}_{p_0^3}| = 2^{183.00}$):**
   - Shrinks deployed $N = 8192$ `ExactGarner15` `HoistedB61 + D1b` proofs from **`2,616.07 -> 508.21 KiB` (`5.15x`, `SinglePCS = 384.8 KiB` / `6.8x`, verify `20.08 ms`)** at $d=64$, **`3,637.30 -> 559.57 KiB` (`6.50x`, `SinglePCS = 430.4 KiB` / `8.5x`, verify `21.80 ms`)** at $d=256$, **`8,368.32 -> 747.27 KiB` (`11.20x`, verify `30.13 ms`)** at $d=1024$, and **`22,747.35 -> 2,452.93 KiB` (`9.27x` full persistent-`A` bundle; `~1,743 KiB` / `12.6x` WHIR PCS payload; `~445 KiB` / `~51x` online witness WHIR PCS; verify `64.64 ms`)** at $d=4096$ `[EXECUTED]`.
   - Achieves **`130.08` bits `[BCIKS20]` Unique-Decoding (UDR)** and **`140.51–144.51` bits `[DKT26]` Thm 5.12 JBR** provable soundness (`blow = 4`, `t_queries = 192`), clearing `>= 128` bits without CBR conjectures `[DERIVED, EXECUTED]`.
2. **`qwen35audit::whir_ext4` (`WhirExt4Pcs` + `GMaskExt4` over `BabyBear Ext4` $X^4 - 11$, `cSHAKE256` Merkle/FS):**
   - Compresses the `Qwen3.5-0.8B` `U1` VRF-audited `GDN + MXFP4 SwiGLU + ZK Absent("sk-...")` receipt from **`4,643.78 -> 584.47 KiB` (`7.95x` smaller)** with **`19.86 ms` standalone zero-witness verify** (`3.77x` faster than `74.79 ms`) `[EXECUTED]`.
   - Compresses the `Qwen3.8-Flash-Next` $H_v = 48$ (`1,048,576`-cell WY + `512E` `MXFP4` MoE + full algebraic `QSA` `C3+C5` Top-$K_B$) receipt from **`4,709.38 KiB` WY+MoE (`5,295.21 KiB` w/ QSA) -> `548.56 KiB` ALL-IN-ONE (`8.58x` vs WY+MoE, `9.65x` vs WY+MoE+QSA)** with **`10.58 ms` standalone zero-witness verify** (`5.14x` faster than `54.34 ms`) `[EXECUTED]`.
   - Achieves **`101.6` bits `[BCIKS20]` Thm 1.4/1.5 UDR** soundness (`100.63` bits with $\eta = 2^{-5}$ slack; `blow = 8`, `t_queries = 140`, `u_ood = 2`) `[DERIVED, EXECUTED]`.

---

## 1. Algebraic Construction, Soundness Pricing, and Exact HVZK Scope

### 1.1 Separable `GMask` Sumcheck Blinding + Rank-Preserved WHIR Opening (`[DERIVED]`, `[SOURCE: darkproof/src/gmask.rs:16-90]`)

- **Separable Degree-$d$ Masking (`GMask61` in `whir_pcs.rs:120-588`, `GMaskExt4` in `whir_ext4.rs:135-425`):** For an $\ell$-round degree-$d$ sumcheck over $\mathbb{F}_{q}$ ($q = p_0^3$ or $p_{\text{BB}}^4$), the prover samples independent random univariate polynomials $g_j(X) = \sum_{k=0}^d c_{j,k} X^k \in \mathbb{F}_q[X]$ ($j \in [0,\ell)$) packed into dedicated rows of the committed matrix PCS. Defining $g(x_0,\dots,x_{\ell-1}) = \sum_{j=0}^{\ell-1} g_j(x_j)$, its hypercube sum is $G = 2^{\ell-1}\sum_{j=0}^{\ell-1}(g_j(0) + g_j(1))$, and its partial hypercube sum in round $i$ after challenges $r_{<i}$ is:
  $$g_{\text{round},i}(t) = 2^{\ell-1-i}\Big(\sum_{j<i} g_j(r_j) + g_i(t)\Big) + 2^{\ell-2-i}\sum_{j>i}\big(g_j(0)+g_j(1)\big) \quad [DERIVED].$$
  Sending $(G, \{\tilde{s}_i(t) = s_i(t) + \rho g_{\text{round},i}(t)\}_{i=0}^{\ell-1})$ for Fiat–Shamir $\rho \in \mathbb{F}_q^\times$ satisfies $\tilde{s}_0(0)+\tilde{s}_0(1) = S + \rho G$ and $\tilde{s}_\ell \equiv f(r) + \rho g(r)$.
- **Full-Rank Bijection Proof (`[DERIVED]`, `[EXECUTED]`):** Setting $u_j(t) = g_j(t) - g_j(0)$ for $t \in \{1,\dots,d\}$ and $z_0 = G$, the linear map $(z_0, \{u_j(t)\}_{j,t}) \mapsto (G, \{g_{\text{round},i}(t) - g_{\text{round},i}(0)\}_{i,t})$ is block-lower-triangular with invertible diagonal entries $2^{\ell-1}$ and $2^{\ell-1-i} \in \mathbb{F}_q^\times$, hence a **bijection of rank $1 + d\ell$** over $\mathbb{F}_q^{1+d\ell}$ (`test_gmask61_algebraic_rank_and_statistical_hvzk_indistinguishability`, `test_gmask_ext4_algebraic_hvzk_and_witness_indistinguishability`).
- **Dual-Mask Rank Preservation Across Coefficient Sumcheck:** To prevent evaluating $P_{\text{gmask}}(\zeta)$ in the WHIR coefficient sumcheck from adding a $(1 + d\ell + 1)$-th linear constraint on $(1 + d\ell)$ coefficients, both `WhirPcs61` (`whir_pcs.rs:1683-1710`) and `WhirExt4Pcs` (`whir_ext4.rs:640-725`) commit an auxiliary mask polynomial $Z_{\text{gm}}(X)$, publish blinded linear projections $\langle v_G, Z_{\text{gm}}\rangle$ and $\langle v_{\text{at}}, Z_{\text{gm}}\rangle$, fold $\hat{P}_{\text{gm}}(X) = P_{\text{gmask}}(X) + \beta_{\text{gm}} Z_{\text{gm}}(X)$, and blind Stage-0 columns via `hide = C >= t_queries * 2^{k_0}` tail coefficients plus `4` data-blinding rows and `Ext` proximity-mask rows `[DERIVED]`.
- **Exact HVZK Scope (`#117.A.4` Cross-Audit Specification, `[DERIVED]`):**
  - **Exact `TVD = 0` Witness-Independent Components:** All `GMask61` / `GMaskExt4` blinded `EinSumcheck` and PCS row-sumcheck round polynomials, salted Stage-0 opened columns ($t_{\text{queries}} \cdot 2^{k_0} \le \text{hide}$), and folded WHIR coset codewords (`u_prox` masks $F^{(0)}(X)$ uniformly over $\mathbb{F}_q^{w_0}$) have zero statistical dependence on the witness `[DERIVED, EXECUTED]`.
  - **Succinct Application Subproof Boundary (`[OPEN]` for full-bundle ZK):** The outer wrappers `HoistedWhirBundle`, `Qwen35U1WhirBundle`, and `Qwen38FnWhirReceipt` intentionally serialize random-point polynomial evaluations (`p0_poly_evals`, `p17_poly_subsums`, `rhs_eval_at_z`, `b_at_dfa_leaf`, etc.) and unmasked `D1b` LogUp-GKR / `MXFP4` Horner sumcheck subproofs (`prove_logup_gkr_with_mults`, `verify_d1b_range_ext4`, `verify_mxfp4_delayed_bjk_horner_ext4`). Converting those outer subproofs to masked sumchecks + Pedersen/masked evaluation commitments is `[OPEN]`.

### 1.2 Multi-Round $2^k$-ary WHIR Folding & Provable Soundness Regimes (`[DERIVED]`)

Instead of transmitting degree-$< w_0$ extension vectors in the clear, both engines fold $F^{(0)}(X) \in \mathbb{F}_q[X]_{< w_0}$ across $R_{\text{fold}} \in \{2,3,4\}$ rounds with step sizes $k_r \in \{1,2,3,4\}$ down to $w_{\text{final}} \le 128..256$, interleaving `u_ood` out-of-domain (OOD) shift claims with degree-2 lockstep sumchecks (`whir_pcs.rs:1760-2210`, `whir_ext4.rs:730-1055`):

| Engine | Field & Size $|\mathbb{F}_q|$ | Rate $\rho$ (`blow`) | Queries $t_q$ | OOD $u_{\text{ood}}$ | `[BCIKS20]` UDR Bits | `[DKT26]` Thm 5.12 JBR Bits |
|---|---|---:|---:|---:|---:|---:|
| `WhirPcs61` (`darkvfhe`) | $\mathbb{F}_{p_0^3}$, $2^{183.00}$ | $1/4$ (`4`) | `192` | `1` | **`130.08` b** | **`140.51–144.51` b** |
| `WhirExt4Pcs` (`qwen35audit`) | `BabyBear Ext4`, $2^{123.63}$ | $1/8$ (`8`) | `140` | `2` | **`101.60` b** (`100.63` b @ $\eta=2^{-5}$) | **`> 108` b** (for $N_0 \le 2^{18}$) |

- **`WhirPcs61` (`[DERIVED]`):** At $\rho = 1/4$, unique-decoding distance is $\theta_{\text{UD}} = (1-\rho)/2 = 3/8$, giving query error $(1 - \theta_{\text{UD}})^{192} = (5/8)^{192} = 2^{-130.08}$ (`Minidregg` `TwoRegimeQueryBudget.lean` UDR regime), while `[DKT26]` (`ePrint 2026/2056` Thm 5.12) Johnson-bound list decoding ($\theta_J = 1 - \sqrt{\rho} - \eta = 1/2 - \eta$, list size $L \le 1/(2\eta)$) with $|\mathbb{F}_{p_0^3}| = 2^{183}$ yields `140.51–144.51` bits across $N_0 \le 2^{23}$.
- **`WhirExt4Pcs` (`[DERIVED]`, `[REFUTED: 120-bit Johnson over 123.6-bit Ext4]`):** Over `BabyBear Ext4` ($|\mathbb{F}| = 2^{123.63}$), Johnson-regime list-decoding incurs $(L \cdot N_0)^2 / |\mathbb{F}|$ correlated-agreement denominator loss (`whir-neon-pricer` audit), refuting `>= 115`-bit JBR claims at $N_0 = 2^{18}$ `[REFUTED: BabyBear Ext4 JBR >= 115b at N0=2^18]`. Operating strictly inside `[BCIKS20]` Unique Decoding ($L = 1$, $\theta_{\text{UD}} = (1 - 1/8)/2 = 7/16$ at `blow = 8`, `t_queries = 140`, `u_ood = 2`) yields $(9/16)^{140} = 2^{-116.18}$ query soundness and $N_0 / |\mathbb{F}| \le 2^{18 - 123.63} = 2^{-105.63}$ per-round algebraic soundness (`101.60` bits union bound across all rounds; `100.63` bits with $\eta = 2^{-5}$ slack) `[DERIVED]`.

### 1.3 Cross-Audit Algebraic Hardening (`#117` & `#131`, `[DERIVED]`, `[EXECUTED]`)

- **Full Algebraic `QSA` `C3 + C5` Top-$K_B$ (`whir_ext4.rs:4130-4675`):** Proves `sel_qb` booleanity + `eta_inact * (1 - act_qb) * sel_qb == 0` phantom-cell guard (`#117.A.1`), exact $1/2$-hypercube Top-$K_B = 4$ cardinality per `(h, q)` row, signed branch relation `(2*sel - act)*(key - tau) == slack + act - sel` with 16-bit `D1b` non-negativity on `slack`, and `expected_qsa_keys_whir_root` pin.
- **Collision-Free `Absent("sk-...")` DFA + Prefix Range + EOF Zerocheck (`whir_ext4.rs:3210-3765`):** Encodes transitions as `q + 8 * b + 4096 * q_next` (`b in 0..=256`, zero carry collision vs `2048` stride; `#117.A.3`), enforces `m_tab = 8` unbiased `[0, 256)` byte range on `0..word_len`, `eof_sc` zerocheck `bytes_pad[t] == 256` on `word_len..pad_len`, `final_dfa_state < 4`, power-of-two `pad_len >= 2048`, and cleartext MLE bind at `z_dfa_leaf`.
- **Untrusted Header & Persistent-`A` Root Guards (`whir_pcs.rs:5488-5512, 5821-5825`):** Bounds `192 <= t_queries <= min(512, 2^mc, n_leaves_0)` and `mr + mc <= 31` (`#117.A.2`, `#131`), unconditionally enforces `expected_persistent_a_root == Some(aroot)` whenever `bundle.persistent_a` is set, and runs a 3-round zero-swap streaming sumcheck prefix (`run_slot_row_sumcheck_61`, `whir_pcs.rs:1496-1755`) cutting temporary table RAM by `8x` (`19.3 GiB -> 3.2 GiB` at $d=4096$).

---

## 2. Executed Release Benchmarks & Adversarial Rejection Ledger

### 2.1 `darkvfhe` ($N = 8192$, `ExactGarner15`, `HoistedB61 + D1b` LogUp-GKR)

Command (`[EXECUTED]`, `0` warnings in `darkvfhe`, `3/3` tests pass, exit `0`):
```bash
CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-whir cargo test \
  --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml --release \
  -p darkvfhe --test whir_gmask_compress -- --nocapture --test-threads=1
```

| Dim $d$ | Blocks $(R, K)$ | 1-Step `succinct_pcs` | `WhirPcs61 + GMask61` (Persistent `Enc(W)`) | Online `SinglePCS` | Compression Ratio | Prove Old / WHIR (ms) | Standalone Verify (ms) | Soundness (`BCIKS / DKT`) |
|---:|---|---:|---:|---:|---:|---:|---:|---|
| `64` | `1 x 1` | `2,616.07 KiB` | **`508.21 KiB`** | **`384.8 KiB`** | **`5.15x`** (`6.80x` SinglePCS) | `861.64 / 1,156.87` | **`20.08 ms`** (`3.1x` faster) | `130.08 / 144.51 b` |
| `256` | `2 x 4` | `3,637.30 KiB` | **`559.57 KiB`** | **`430.4 KiB`** | **`6.50x`** (`8.45x` SinglePCS) | `1,221.45 / 2,326.26` | **`21.80 ms`** (`3.5x` faster) | `130.08 / 142.51 b` |
| `1024` | `8 x 16` | `8,368.32 KiB` | **`747.27 KiB`** (`SharedTwo`) | `~515 KiB` (est.) | **`11.20x`** (`~13.8x` PCS-only) | `5,249.45 / 40,730.88` | **`30.13 ms`** (`3.1x` faster) | `130.08 / 140.51 b` |
| `4096` | `32 x 64` | `22,747.35 KiB` | **`2,452.93 KiB`** (`SeparateTwo`) | `~445 KiB` (wit PCS) | **`9.27x`** (`12.6x` PCS / `~51x` wit PCS) | `32,842.80 / 147,044.17` | **`64.64 ms`** (`3.9x` faster) | `130.08 / 141.51 b` |

*Byte breakdown at $d = 4096$ (`[DERIVED, EXECUTED]`):* Of `2,452.93 KiB`, `~710 KiB` consists of explicit non-PCS `HoistedB61` cross-prime integer subsums (`4,096` persistent-$A$ + `288` online polynomials $\times$ `(1 p_0 eval + 21 x 58-bit subsums)`) + `LogUpGkrProof`, while `SeparateTwo` WHIR PCS accounts for `~1,743 KiB` (`~445 KiB` online `witness_pcs` + `~1,298 KiB` 521-row `a_pcs`).

### 2.2 `qwen35audit` (`Qwen3.5-0.8B` `U1` VRF Audit & `Qwen3.8-Flash-Next` $H_v = 48$ Receipt)

Command (`[EXECUTED]`, `0` warnings in `qwen35audit`, `2/2` tests pass, exit `0`):
```bash
CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-whir cargo test \
  --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml --release \
  -p qwen35audit --test whir_ext4_compress -- --nocapture --test-threads=1
```

| Audited Receipt Workload | 1-Step `pcs_ext4` | `WhirExt4Pcs + GMaskExt4` | Compression | Prove Old / WHIR | Standalone Verify | `[BCIKS20]` UDR |
|---|---:|---:|---:|---:|---:|---:|
| **`Qwen3.5-0.8B` `U1` (`GDN + MXFP4 SwiGLU + ZK Absent("sk-...")`)** | `4,643.78 KiB` (`74.79 ms` vfy) | **`584.47 KiB`** | **`7.95x`** | `743.84 / 1,534.71 ms` | **`19.86 ms`** (`< 25 ms`) | **`101.6 b`** |
| **`Qwen3.8-Flash-Next` $H_v = 48$ (`1M` WY + `512E` MoE + `QSA` Top-$K_B$)** | `4,709.38 KiB` (`5,295.21 KiB` w/ QSA, `54.34 ms` vfy) | **`548.56 KiB`** (ALL-IN-ONE) | **`8.58x`** (`9.65x` w/ QSA) | `— / 3,435.48 ms` | **`10.58 ms`** (`< 25 ms`) | **`101.6 b`** |

### 2.3 Adversarial Falsifier Suites (`[EXECUTED]`)

- **`darkvfhe` (`whir_gmask_compress.rs`, `8/8` attack families deterministically rejected):** (1) tampered `GMask61` round polynomial, (2) tampered WHIR intermediate OOD shift claim, (3) `GMask61` hypercube-sum forgery (`M' != S + \rho G`), (4) Stage-0 salted column bit-flip, (5) folded WHIR Merkle sibling bit-flip, (6) `HoistedB61` `p17` cross-prime subsum forgery, (7) malformed `wit_mr = 0` / oversized `t_queries = 9999` untrusted headers (`Err`, zero panic), and (8) missing or mismatched `expected_persistent_a_root` even when `Some(opened_a)` is supplied (`#117.A.2`, `#131`).
- **`qwen35audit` (`whir_ext4_compress.rs`, `9/9` attack families deterministically rejected):** (1) tampered `GMaskExt4` WY `EinSumcheck` round, (2) tampered WHIR cascade OOD evaluation, (3) `GMaskExt4` terminal weld forgery, (4) Stage-0 / cascade `cSHAKE256` Merkle sibling flip, (5) `Absent("sk-...")` secret injection (`"sk-live-9981"` in `Qwen3.5` output rejected), (6) `Qwen3.8` `512E` MoE `MXFP4` scale / routing forgery, (7) `QSA` `C3+C5` Top-$K_B$ slack / inactive-cell `sel_qb` forgery (`#117.A.1`), (8) `expected_qsa_keys_whir_root` substitution, and (9) `2048`-stride byte overflow / `eof` tail injection (`#117.A.3`).

---

## 3. Proposed Maintainer Folds for `docs/VERDICTS.md` & `notes/README.md`

- **FHE / vFHE (`darkvfhe`):** Fold `whir_pcs.rs` alongside `succinct_pcs.rs`: multi-round $2^k$-ary WHIR + `GMask61` compresses $N = 8192$ `HoistedB61 + D1b` proofs `5.15x–11.20x` (`384.8–747.3 KiB` at $d \le 1024$; `2,452.9 KiB` = `9.27x` full persistent-`A` bundle / `12.6x` PCS-only at $d = 4096$) with `20.1–64.6 ms` standalone verification at `130.08b BCIKS / 140.51–144.51b DKT` soundness, closing the univariate sumcheck blinding `[OPEN]` item on PCS / `EinSumcheck` rounds (`TVD = 0`).
- **zkML (`qwen35audit`):** Fold `whir_ext4.rs`: `WhirExt4Pcs + GMaskExt4` (`blow = 8, t_queries = 140, u_ood = 2`, `101.6b [BCIKS20]` UDR) compresses `Qwen3.5-0.8B` `U1 + Absent` (`4,644 -> 584.5 KiB`, `7.95x`, `19.86 ms` verify) and `Qwen3.8-Flash-Next` $H_v = 48$ WY + `512E` MoE + algebraic `QSA` Top-$K_B$ (`5,295 -> 548.6 KiB`, `9.65x`, `10.58 ms` verify).
