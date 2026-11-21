# STATUS — `vfhe_sota_2026_11_21`

**Date:** 2026-11-21
**State:** COMPLETED & VERIFIED (`exit 0` across both Python pricing/verifier suites and Lean 4 `build_and_verify.sh`).

## 1. Completed Deliverables

| Lane | Worker(s) | Executable / Formal Artifacts | Evidence Note | Status |
|---|---|---|---|---|
| **1. Fast `vFHE` (`HoistedB61`) & 2025–2026 Mirror Audit** | `vfhe-fast-cert` (`Carbon`) + `vfhe-neon-mirror` (`Neon` helper) | `experiments/vfhe_hoisted_b61_and_pir.py` (`1,514` lines, `exit 0` in `~51s`: `N=8192` verifier, `13/13` adversarial attacks, `τ=4` trajectory equivalence) | `notes/vfhe-hoisted-certificate-breakthrough.md` | **DONE (`exit 0`)** |
| **2. Frontier `Qwen3.8-Flash-Next` (`arXiv:2608.30320`) `zkML` & `vFHEML`** | `qwen38-zkvfhe` (`Carbon`) | `experiments/qwen38_next_zk_vfhe_pricing.py` (`1,379` lines, `exit 0` in `~1.0s`: BabyBear `GDN` WY, `bfv_ref` depth-1 `GDN`, `QSA` `B1a`/`B1b` traps, `GR` outlier simulation, `PLE` + E2E tables) | `notes/qwen38-next-zkml-vfheml-architecture.md` | **DONE (`exit 0`)** |
| **3. Kernel-Checked `minidregg` Lean 4 Formalizations** | `lean-vfhe-sota` (`Carbon`) | `formal/Theory/BfvHoistedRescale.lean` (`651` lines), `formal/Theory/ZkmlDeltaNet.lean` (`406` lines), `formal/Assurance/ZkmlGruenSumcheck.lean` (`394` lines), `formal/build_and_verify.sh` (`exit 0` in `~18s`), `formal/minidregg-vfhe-deltanet-gruen.patch` (`git apply --check` `exit 0`) | `notes/lean-vfhe-deltanet-gruen.md` | **DONE (`exit 0`)** |

## 2. Headline Verified Outcomes (`[EXECUTED]`, `[DERIVED]`, `[SOURCE]`)

1. **`HoistedB61` Flips `FHE vs MPC` at `d = 4096` (`DARK-LEARNING-SCHEME-DECISION.md` §§1, 7, 8):**
   - Slashes `6,144` eager per-block `B61` `ct×ct` certificates to **`128` hoisted group certificates** (`25.3×` under strict `digits61`, `34.2×` under packed `w=20`), fitting in existing `k = 5` extension primes (`2^446 < 2^488`) with **`7.65×` smaller rounding noise** (`589 -> 77`).
   - Exact dense SGD (`Hoist-FHE(b, τ=64)` + low-rank SPDZ bilinear correction + §20.2 Ligero ZKPoPK) refines `step_spec.step` bit-for-bit and drops steady-state commitments from `2,368.9 Gbit` (`2,958.4 Gbit` fixing `step_counts.py:195`'s omitted `relin` digits) to **`11.08 Gbit` (`0.35× MPC` packed)** and **`21.50 Gbit = 0.68× MPC` (`25.08 Gbit = 0.80× MPC` under zero-slack `Exact-Garner-15`)** under strict `digits61` (`MPC = 31.50 Gbit`), at **`9.5×` smaller online wire** (`32.24M` vs `305.9M`).
   - `Inference-Only vFHEML` (`d = 4096`): **`3.73 Gbit` packed / `10.78 Gbit` `digits61` (`0.84×` 2L-MPC `12.89 Gbit`)** at **`17.7×` smaller online wire** (`11.50M` vs `203.4M`).
   - Dark `vPIR` (`V = 151,936, d = 4096`): **`15,260.7 -> 25.37 Gbit` `digits61` (`601.4×` reduction)** at `N = 8192` (`151,936 -> 1` rescale cert at `N = 4096`).
2. **`Qwen3.8-Flash-Next` (`125.74B-A6.04B + 51.20B N-Gram`) Is Crypographically Superior to Dense & `gpt-oss` Architectures:**
   - `75%` `Gated DeltaNet` (`36L`): division-free `C=64` chunkwise WY `(I+L)[U|W]=RHS` verifies via **1 flat degree-2 Gruen `EinSumcheck`** (`0` GKR layers, `0` inversions, `0` `T^2` `EXP_TAB`s) and runs **`O(1)`-state (`0.211 GiB` through `1M`) depth-1 `vFHEML`**.
   - `25%` `Qwen Sparse Attention` (`12L`): `0` indexer `EXP_TAB`s, caps softmax at `K = 2048` (`850×–3,401×` fewer `EXP`s vs `Dense-125B` at `256K–1M`), with two constructive BabyBear Top-`K_B` traps (`B1a` wraparound bottom-`k` forgery without `RangeCheck(τ < 2^30)`, `B1b` `ReLU == 0` completeness crash without index tie-breaking).
   - `51.20B` Layer-2 Hash N-Gram PLE: refutes naive `D1b` (`Jo 2026/1390`); proved in `88.75K` ZK P2-Merkle cells/tok (`576,891× < D1b` at `T=1`; `0` SC muls public prompt) and `27.9 KB`/tok `2P-DPF` (`~1,250×` smaller upload than `YPIR+SP+ZKPoPK`).
   - Beats `gpt-oss-20b` per token for all `T >= 64K` (`2.57×–3.43×` fewer prover BB muls at `256K`, `8.0×–10.8×` at `1M`) despite `6×` more total parameters.
3. **3 Kernel-Checked `minidregg` Lean 4 Modules (`1,451` lines, `0 sorry`, `0 axiom`, `33` `#print axioms` pins):**
   - `Theory/BfvHoistedRescale.lean`, `Theory/ZkmlDeltaNet.lean`, and `Assurance/ZkmlGruenSumcheck.lean` verify cleanly against `minidregg` @ `d58330d9a` and ship as a clean `git apply` patch (`formal/minidregg-vfhe-deltanet-gruen.patch`).

## 3. Consolidated Corpus & Metered Search Ledger

- **`eprint.iacr.org` PDF fetches:** **`0`** (strictly local `/Users/ember/dev/gh/forks/IACR-eprint-mirror/` through `2026/1861`: `2024/108`, `2024/270`, `2025/2285`, `2026/27`, `2026/857`, `2026/1127`, `2026/1390`, `2026/1816`, `2026/1839`, `2026/1857` + `~/paperbin/pirouette-36byte-query-single-server-pir-2025-680.txt`).
- **Scry (`swarm/tools/scry.py`):** **`8` SQL queries total** (`3` coordinator `crawl.pages` + `2` `qwen38-zkvfhe` `openalex.works` + `3` `vfhe-neon-mirror` `openalex.works`).
- **Kagi (`swarm/tools/kagi.py`):** **`5` web queries total** (`1` coordinator + `2` `qwen38-zkvfhe` + `2` `vfhe-neon-mirror`).
- **Protected trees untouched:** `docs/VERDICTS.md`, `docs/DARK-LEARNING-SCHEME-DECISION.md`, `/Users/ember/dev/minidregg`, and `/Users/ember/dev/breadstuffs` verified clean (`git status --short` empty).
