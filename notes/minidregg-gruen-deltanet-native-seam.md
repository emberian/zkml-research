# Native `minidregg` Seam: `Gruen` `{0, ∞}` Mode-2 `EinSumcheck`, 0-Mul E2M1 MXFP4 Horner, & Division-Free `Gated DeltaNet` Chunkwise WY

**Date:** 2026-11-21 · **Lane:** `mini-prover-gruen` (`system_wave_2026_11_21`) · **Base `minidregg` Commit:** `99dfbf0ec`

---

## 0. Executive Verdicts

1. **Lean-to-Rust `Gruen` `{0, ∞}` Mode-2 `EinSumcheck` Seam Closed (`[DERIVED]`, `[EXECUTED]`, `[SOURCE]`):**
   [GruenEinSumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/GruenEinSumcheckConformance.lean) instantiates [ZkmlGruenSumcheck.lean](file:///Users/ember/dev/minidregg/Assurance/ZkmlGruenSumcheck.lean) (`ePrint 2024/108` §3.2–3.3 & App. A.3) and [ZkmlEinSumcheck.lean](file:///Users/ember/dev/minidregg/Assurance/ZkmlEinSumcheck.lean) over BabyBear ($p = 2013265921$) at a 5-round instance ($\mu_L = 1, \mu_R = 1, \mu_S = 3, \kappa = 2$) with **interior zero-`eq` round $z_1 = 0$** (`2024/108` fn. 23 deterministic $q(1)$ fallback) alongside $z_0, z_2 \neq 0$, proves $O(2^m)$ table-folding equivalence (`mle_foldLsb`, `foldLsb5_eq_mle`) and universal $\{0, 1, \infty\}$ reconstruction (`roundQuotient_eq_quadFromZeroOneInf`), kernel-decides (`by decide`) every round value and stripped claim, and authors [gruen_einsumcheck_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/gruen_einsumcheck_conformance.json) (`3,422 B`). Native Rust [gruen_einsum.rs](file:///Users/ember/dev/minidregg/prover/src/gruen_einsum.rs) (`0` prover inversions) reproduces the Lean vector wire-for-wire, passes all 3 mechanized soundness teeth, and achieves **`11.70×–11.80×` single-round (`48.43×–50.58×` BabyBear-specialized)** and **`5.47×–5.76×` full-protocol (`15.48×–17.70×` BabyBear-specialized)** `--release` speedups over [sumcheck.rs](file:///Users/ember/dev/minidregg/prover/src/sumcheck.rs#L441-L495) at $m \in \{14, 18, 20\}$.
2. **Type-Enforced Zero-Mul 7-Bucket E2M1 Horner & Delayed Block-Bind (`b -> j -> k`) (`[DERIVED]`, `[EXECUTED]`):**
   In [GruenEinSumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/GruenEinSumcheckConformance.lean#L125-L185), `e2m1Horner` is typed over `[AddCommGroup R]` (no `Mul R` instance in scope — Lean's typechecker enforces **zero multiplications**), proved equal to $\sum_i \mathrm{e2m1Decode}(q_i) \cdot v_i$ over any `[CommRing R]` (`e2m1Horner_eq_dot`), and pinned on a 32-nibble BabyBear vector. In [gruen_einsum.rs](file:///Users/ember/dev/minidregg/prover/src/gruen_einsum.rs#L473-L639), `prove_mxfp4_delayed_bjk_horner` ($\ell_0 = 5$ on $B = 32$) matches naive `bmul`-materialized `b -> j -> k` bit-for-bit (including interior $r_j[1] = 0$ fallback) with `16×` smaller peak $Q$ buffer and **`5.60×` `--release` wall-clock speedup** (`27.691 ms -> 4.941 ms` on $J=512, K=128, B=32 = 2.10\text{M}$ E2M1 weights).
3. **Division-Free `Gated DeltaNet` Chunkwise WY `(I + L)[U | W] = RHS` Seam & Full-Layer Timing (`[DERIVED]`, `[EXECUTED]`, `[SOURCE]`):**
   [DeltaNetWyConformance.lean](file:///Users/ember/dev/minidregg/Compiler/DeltaNetWyConformance.lean) instantiates [ZkmlDeltaNet.lean](file:///Users/ember/dev/minidregg/Theory/ZkmlDeltaNet.lean) (`arXiv:2608.30320` Eqs. 1–5) over BabyBear at $C = 4, d_k = d_v = 2$ with non-zero $S_{\text{init}}$, tight nilpotency ($L^2 \neq 0 \wedge L^4 = 0$), and explicit **zero-decay step $\alpha_1 = 0$**, kernel-deciding exact equivalence between sequential `gdnStep`/`gdnReadout`, `neumannInv L * RHS`, and `(1 + L) * UW = RHS` into [deltanet_wy_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/deltanet_wy_conformance.json) (`1,016 B`). Native Rust [deltanet_wy.rs](file:///Users/ember/dev/minidregg/prover/src/deltanet_wy.rs) proves `L · UW = RHS - UW` across all $H_v = 48$ value heads (`d = 128, C = 64`) of a **full `Qwen3.8-Flash-Next` GDN layer** in **`1.514 ms` (`12` quadratic Gruen rounds, `0` GKR layers, `0` inversions)** and **`116.342 ms` division-free WY witness generation** (`117.856 ms` total = **`1.842 ms/tok`** single-threaded `--release`).

---

## 1. Authority Boundary & Reproducible Verification Commands (`[EXECUTED]`)

Following `minidregg`'s Law of the Native Seam ([SumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/SumcheckConformance.lean#L1-L35)), Lean is the **sole author** of both `prover/testdata/*.json` files via `#eval`; Rust implements both literal mirrors and fast folded kernels and proves vector agreement in `prover/tests/*.rs`.

- **Lean 4.35.0 Overlay Build & Import-Boundary Check (`[EXECUTED]`):**
  - Script: [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_mini_prover/build_and_verify.sh)
  - Command: `bash /Users/ember/dev/zkml-research/research/system_wave_2026_11_21/formal_mini_prover/build_and_verify.sh`
  - Output (`exit 0`, `0` warnings, `0 sorry`, `0 axiom`, `0 native_decide`, `0 #guard`):
    ```text
    OK: ATLAS syntax check (0 sorry, 0 axiom, 0 native_decide, 0 #guard; #print axioms pinned)
    OK: scripts/check-import-boundary.sh passed
      [CONFORMANCE 22.15s] Compiler.GruenEinSumcheckConformance -> rc=0
      [CONFORMANCE  6.27s] Compiler.DeltaNetWyConformance -> rc=0
    OK: Verified Lean-emitted JSON gruen_einsumcheck_conformance.json (3422 bytes)
    OK: Verified Lean-emitted JSON deltanet_wy_conformance.json (1016 bytes)
    OK: Kernel-verified all conformance modules in 28.43s
    ```
- **Rust `--release` Conformance, Teeth, & Benchmark Suites (`[EXECUTED]`):**
  - Command: `CARGO_TARGET_DIR=/Users/ember/dev/minidregg/prover/target-gruen cargo test --manifest-path /Users/ember/dev/minidregg/prover/Cargo.toml --release --test gruen_einsumcheck_conformance --test deltanet_wy_conformance -- --nocapture --test-threads=1`
  - Output: **`11 passed; 0 failed`** (`6/6` in [gruen_einsumcheck_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/gruen_einsumcheck_conformance.rs), `5/5` in [deltanet_wy_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/deltanet_wy_conformance.rs), `0` compiler warnings; existing `sumcheck_conformance`, `sumcheck_cubic_conformance`, and `zkml_matmul_conformance` also verified green).

---

## 2. Lean 4 Conformance Modules & Kernel-Pinned Theorems (`[DERIVED]`, `[EXECUTED]`)

Every theorem below carries a `#guard_msgs (whitespace := lax) in #print axioms` pin depending exclusively on `[propext, Classical.choice, Quot.sound]`:

| Module | Theorem / Witness | Mathematical Content & Seam Role |
| :--- | :--- | :--- |
| [GruenEinSumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/GruenEinSumcheckConformance.lean#L51-L122) | `mle_foldLsb`, `foldLsb5_eq_mle`, `roundQuotient_eq_quadFromZeroOneInf`, `roundQuotient_gruen_sum` | Proves $O(2^m)$ `foldLsb` equals `Selvage.mle` along `lsbCons`, `roundQuotient` equals `quadFromZeroOneInf(q(0), q(1), q(∞))` over any `CommRing`, and $\ell_z(0)q(0) + \ell_z(1)q(1)$ equals the `eq`-weighted hypercube sum. |
| [GruenEinSumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/GruenEinSumcheckConformance.lean#L125-L185) | `e2m1Horner` (`[AddCommGroup R]`), `e2m1Horner_eq_dot`, `grE2m1Horner_values` | Type-enforces `0` multiplications on E2M1 nibbles (`±{0,1,2,3,4,6,8,12}`), proves equality to $\sum_i \mathrm{e2m1Decode}(q_i) v_i$ over any `CommRing`, and kernel-decides all 7 buckets + 4 bit-planes + dot (`793181528`) on $B=32$. |
| [GruenEinSumcheckConformance.lean](file:///Users/ember/dev/minidregg/Compiler/GruenEinSumcheckConformance.lean#L244-L337) | `grClaim_eq_mle3`, `grZS_interior_zero`, `grClaim_value`, `grRound0_values`..`grRound4_values`, `grTerminal_values`, `grTerminal_matches_mle`, `grPhaseSplice_no_double_strip` | Kernel-decides 5-round BabyBear Mode-2 transcript (`σ₀ = 1687038750`, interior $z_1 = 0$ `ZeroEqFallback` `q₁(1) = 922178728`, `S`-entry `σ₃ = 1645677380`, terminal `475473014 · 1881988079 = 1935010981`) + Jolt `#1474` double-strip refutation. |
| [DeltaNetWyConformance.lean](file:///Users/ember/dev/minidregg/Compiler/DeltaNetWyConformance.lean#L72-L261) | `wyCouplingL_strictLower`, `wyAlpha_has_zero_step`, `wyL_nilpotency_tight`, `wyU_bilinear_and_recurrence`, `wySequential_agrees_with_chunkwise` | Proves `IsStrictLowerTri` of prefix-product `wyCouplingL` over any `CommRing`, pins $\alpha_1 = 0$ and $L^2 \neq 0 \wedge L^4 = 0$, instantiates `wyChunk_bilinear_iff_recurrence` on `(wyU, wyVbeta)` and `(wyUW, wyRHS)`, and decides agreement with 4-step `gdnStep`/`gdnReadout`. |
| [DeltaNetWyConformance.lean](file:///Users/ember/dev/minidregg/Compiler/DeltaNetWyConformance.lean#L264-L324) | `wyL_value`, `wyNeumannInvL_value`, `wyUW_value`, `wyYOut_value`, `wySFinal_value`, `wyNonStrictLower_babybear_falsifier` | Kernel-decides all BabyBear matrices + diagonal $L_{0,0} = -1$ (`2013265920`) non-strict-lower collision witness ($U_1 \neq U_2$ with $(1+L_{\text{bad}})U_1 = (1+L_{\text{bad}})U_2$). |

---

## 3. Mechanized Soundness & Completeness Teeth Verified in Rust (`[EXECUTED]`)

1. **Gruen Tooth 1 — Interior $r_u = 0$ Unconstrained $q(1)$ (`tooth_1_r_zero_unconstrained_q1_without_fallback`, `[SOURCE: ePrint 2024/108 fn. 23]`):** At round 1 ($z_1 = 0$), $\ell_0(1) = 0$ annihilates $q_1(1)$ in $\ell_0(0)q_1(0) + \ell_0(1)q_1(1) = \sigma_1$. Sending `TwoPoint` without $q_1(1)$ is rejected; algebraically, $q_{1,\text{true}}(1) = 922178728$ and forged $q_{1,\text{fake}}(1) = 922178729$ both satisfy the round-1 sum check yet diverge at every $c \neq 0$, and `verify_gruen_einsum_mode2` rejects the forged fallback at round 2.
2. **Gruen Tooth 2 — Mode-2 $d=2$ Roots vs Unstripped $d+1=3$ Forgery (`tooth_2_mode2_d_roots_vs_unstripped_d_plus_1_forgery`, `[SOURCE: ePrint 2024/108 App. A.3]`):** Verified on both the exact $\mathbb{F}_7$ witness ($r=2, q_{\text{prov}}=(X-2)(X-3), \sigma_{\text{false}}=5$, accepting $\{2,3\}$ under Mode 2 vs $\{2,3,5\}$ unstripped) and over BabyBear ($r = z_0 = 111111111$, extra root $c_\ell = (1-r)(1-2r)^{-1} \bmod P$ caught by Mode 2 and passed by unstripped Mode 1).
3. **Gruen Tooth 3 — Jolt PR `#1474` `F_{>=2} -> S` Double-Strip (`tooth_3_jolt_1474_double_strip_at_f2_to_s_boundary_rejected`, `[SOURCE: ~/paperbin/audit-blog-zksecurity-jolt-uniskip.txt]`):** At round $2 \to 3$, Mode-2 `s_phase_entry_claim = 1645677380` already stripped $\ell_{z_2}(c_2) \notin \{0,1\}$; dividing by $\ell_{z_2}(c_2)$ or $\mathrm{eqMle}(z_S, c_S) = 108855645$ again corrupts $\sigma_3$ and fails verification.
4. **DeltaNet WY Falsifiers `A1a` & `A1b` ([deltanet_wy_conformance.rs](file:///Users/ember/dev/minidregg/prover/tests/deltanet_wy_conformance.rs#L276-L379)):**
   - **`A1a`:** Single-cell `+1` mutation in `UW` fails both against the honest transcript and when re-proved by a dishonest prover (`L · UW_bad != RHS - UW_bad`).
   - **`A1b`:** Perturbing $L_{0,0} = P - 1$ (`-1 mod P`) produces distinct $UW_1 \neq UW_2$ that **both pass** `verify_wy_bilinear_unchecked_l` (`(I + L_bad) UW_1 == (I + L_bad) UW_2 == 0`), while deployed `verify_wy_chunk_gruen` rejects both via `is_strict_lower_tri_flat`.

---

## 4. Native Rust `--release` Benchmarks (Apple Silicon Single-Thread, BabyBear, `[EXECUTED]`)

### 4.1 `Gruen` `{0, ∞}` Mode-2 vs `sumcheck::cubic_round_evals` & `prove_cubic_sumcheck`

`gruen_p` uses the **exact same runtime-modulus `p: u64` arithmetic** as `sumcheck.rs` (isolating the algorithmic $4 \to 2$ point cut + 2-table vs 5-table folding + MSB-to-LSB suffix `eq` tables); `gruen_bb` adds compile-time BabyBear `P` constant folding (`0` prover inversions in both):

| Cube Dim $m$ ($\mu_S, \kappa$) | `sumcheck::cubic_round_evals` | `gruen_f2_round_evals_p` (**Speedup**) | `gruen_f2_round_evals_bb` (**Speedup**) | Full `prove_cubic_sumcheck` | Full `prove_gruen_mode2` (`p` / `bb`) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| **$m = 14$** ($7, 7$) | `1.719 ms` | `0.146 ms` (**`11.80×`**) | `0.036 ms` (**`48.43×`**) | `4.327 ms` | `0.791 ms` (**`5.47×`**) / `0.279 ms` (**`15.48×`**) |
| **$m = 18$** ($9, 9$) | `27.532 ms` | `2.337 ms` (**`11.78×`**) | `0.544 ms` (**`50.58×`**) | `69.861 ms` | `12.689 ms` (**`5.51×`**) / `4.308 ms` (**`16.22×`**) |
| **$m = 20$** ($10, 10$) | `117.081 ms` | `10.007 ms` (**`11.70×`**) | `2.382 ms` (**`49.16×`**) | `307.362 ms` | `53.399 ms` (**`5.76×`**) / `17.369 ms` (**`17.70×`**) |

### 4.2 MXFP4 Delayed Block-Bind (`b -> j -> k`, $\ell_0 = 5$) + 0-Mul Horner & `Qwen3.8-Flash-Next` Full GDN Layer

| Kernel / Workload (`--release`, single-thread) | Baseline / Breakdown | Native Kernel Latency | Key Metric |
| :--- | :--- | :--- | :--- |
| **MXFP4 `b -> j -> k`** ($J=512, K=128, B=32 = 2.10\text{M}$ E2M1 weights) | Naive `bmul` `27.691 ms` (`16.8 MB` `Q` buf) | **`4.941 ms`** (`1.05 MB` `Q5` buf) | **`5.60×` wall-clock**, `16×` RAM cut, `0` `Q`-muls |
| **`Qwen3.8-Flash-Next` 1L GDN** ($H_k=16, H_v=48, d=128, C=64$, incl. $\alpha=0$) | `wy_witness_solve = 116.342 ms`; `verify = 2.123 ms` | **`gruen_mode2_prove(12r) = 1.514 ms`** | **`117.856 ms` / 64-tok chunk (`1.842 ms/tok`)**, `0` invs |

---

## 5. Unverified Scope & Proposed `docs/VERDICTS.md` Folds (Not Edited Here)

- **Unverified Scope (`[OPEN]`):** Native Rust benchmarks above are over base-field BabyBear (`Fp = u64`) single-threaded (`minidregg-prover` has zero `rayon` dependency); `Ext6` (`field6.rs`) challenge-lifted sumcheck and WHIR/BaseFold PCS opening commitments remain separate `minidregg` rungs (`[PROVER-fs]`, `[MATMUL-pcs]`). Zero metered search queries (`Scry: 0`, `Kagi: 0`, `eprint.iacr.org: 0`).
- **Proposed Maintainer Folds for `docs/VERDICTS.md`:**
  1. **§9 (`EinSumcheck` / `minidregg` native seam):** Record `Compiler/{GruenEinSumcheck,DeltaNetWy}Conformance.lean` + `prover/src/{gruen_einsum,deltanet_wy}.rs` closing the Lean-to-Rust conformance seam (`11.7×–11.8×` round / `5.5×–5.8×` full-prove speedup vs `sumcheck.rs` at identical `p: u64` arithmetic; `48.4×–50.6×` / `15.5×–17.7×` BabyBear-specialized; `5.60×` MXFP4 delayed-bind 0-mul E2M1 Horner).
  2. **§3 / §9 (`Qwen3.8-Flash-Next` GDN):** Close the native prover wall-clock item from [qwen38-next-zkml-vfheml-architecture.md](file:///Users/ember/dev/zkml-research/notes/qwen38-next-zkml-vfheml-architecture.md#L131): 1-layer `Qwen3.8-Flash-Next` GDN ($H_v=48, d=128, C=64$) proves `(I+L)[U|W]=RHS` in **`1.514 ms`** (`116.342 ms` division-free WY witness solve = **`1.842 ms/tok`** single-core).
