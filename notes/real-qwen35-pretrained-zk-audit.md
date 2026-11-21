# Real Pretrained `Qwen3.5-0.8B` & `Qwen3.8-Flash-Next` ZK-Audit (`U1` + `Ext4` PCS)

**Date:** 2026-11-21 · **Lane:** `real-qwen35-zk-audit` (`real_systems_wave_2026_11_21`)
**Metered search counts:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org: 0` (`Qwen3.5-0.8B` offline from local HF cache; `Qwen3.8-Flash-Next` via bounded HTTP `Range` tensor byte-slices).
**Artifacts:** [`native/qwen35audit/`](../native/qwen35audit/), [`real_qwen35_gdn_eval.py`](../research/real_systems_wave_2026_11_21/experiments/real_qwen35_gdn_eval.py)

---

## 0. Headline Verdicts

1. **Real 24-layer pretrained `Qwen/Qwen3.5-0.8B-Base` (`18 × Gated DeltaNet + 6 × GQA`, `V = 248,320`) runs end-to-end on our division-free integer `C = 64` chunkwise WY + `FP8`/`MXFP4` execution path with `0` WY errors across `23,592,960` solved cells `[EXECUTED]`.** Across `5 × T = 64 = 320` real English/math/Python/Rust/secret-config token positions (`315` targets), `FP8-E4M3 + IntWY(C=64)` achieves **`KL = 0.00555 nats` vs `BF16` (`PPL = 3.959` vs `3.984`, `98.12%` Top-1, `100.00%` Top-1-in-Top-5)**; `Mixed MXFP4 (72 MLP) + FP8 (114 Attn/GDN) + IntWY` achieves **`KL = 0.06385 nats` (`PPL = 4.194`, `91.25%` Top-1, `99.37%` Top-1-in-Top-5)**; `Pure MXFP4 (All 186 mats) + IntWY` achieves **`KL = 0.15092 nats` (`PPL = 4.663`, `89.69%` Top-1, `98.75%` Top-1-in-Top-5)** `[EXECUTED]`.
2. **Pretrained `Gated DeltaNet` exhibits a `10^-3` low-`beta` underflow trap under naive shared `v`-scaling (`[REFUTED: shared RHS scale on pretrained GDN]`), cured at `0` prover gate cost (`38×` KL reduction) `[DERIVED, EXECUTED]`.** Real `Qwen3.5` Layer-0 GDN heads (`h ∈ {0, 4}`) emit `beta ≈ 10^-3` (`y_rms ≈ 9e-5`) immediately prior to scale-invariant `Qwen3NextRMSNormGated`. Shared fixed-point scaling on `v` crushes `U_rhs = beta * v` (`L0 SNR = 12.76 dB`, `FP8 KL = 0.209 nats`). Per-head power-of-two scaling `u_scale[h]` on `U_rhs[h]` preserves exact $\mathbb{Z}$-linearity of $(I + \tilde{L}/M_{\text{wy}})[U \mid W] = \text{RHS}$ (`0` extra sumcheck/lookup gates) and cuts `FP8+IntWY` KL **`38×` (`0.209 -> 0.00555 nats`, `+14.4 dB` L0 SNR -> `27.17 dB`)** `[EXECUTED]`.
3. **Multithreaded (`rayon`) Rust `native/qwen35audit` proves and standalone-verifies real full-width pretrained `Qwen3.5` (`H_v=16, d=1024, f=3584`) and `Qwen3.8-Flash-Next` (`H_v=48, d=2560, 512E MoE, QSA`) layers over `123.7`-bit `BabyBear Ext4` ($X^4 - 11$) + succinct ZK Coset-RS/Ligero PCS (`103.49` bits `[AHIV17]` $d/3$ UD / `105.63` bits `[BCIKS20]` UD) `[EXECUTED]`.**
   - Zero-copy `libc::mmap` parses `488` `safetensors` tensors in **`0.78–0.90 ms`** and commits all `24` layers (`186` `MXFP4` E2M1 matrices, `497.61M` params) to a `cSHAKE256` Merkle registry in **`1.57 s`** (`weight_root = 59726b21a3129f1f..`) `[EXECUTED]`.
   - `U1` online `25`-boundary commitment (`T = 64, d = 1024`) runs in **`29.37–42.78 µs/tok`** (`1.88–2.74 ms` streaming `cSHAKE256`) or **`2,850.12 µs/tok`** (`182.41 ms` full 25-layer ZK `SuccinctExt4Pcs`) `[EXECUTED]`.
   - Full VRF-audited `Qwen3.5` `GDN + SwiGLU` layer proof (`L10`, including WY Gruen + `StrictLowerTri` zerocheck + `D1b` `[0, 4096)` range + `MXFP4` delayed-bind 7-bucket 0-mul Horner + boundary weld + zero-cleartext ZK `Absent("sk-...")` DFA receipt) proves in **`550.09 ms` (`8.60 ms/tok`)**, verifies standalone in **`55.29 ms`** (`4,642.56 KiB` proof, `0` prover inversions, `0` cleartext output bytes revealed), and rejects **`5/5` planted soundness attacks** `[EXECUTED]`.
4. **Real `Qwen/Qwen3.8-Flash-Next-FP8` (`qwen4_exp`, `L0..L3` = `3 GDN + 1 QSA + 8 GR + 4×512E MoE + Layer-2 51.2B PLE`) + shipped `NVFP4-CSF` & `MLX-4bit` weights executed & proved via HTTP `Range` `[SOURCE, EXECUTED]`.**
   - Real `GR` (`hc_count = 4, hc_lowrank = 320`) keeps stream norms `max |h| <= 0.5746` (`L2` norms `[0.28..2.24]`, `inj_w <= 1.426`); real `51.20B` Layer-2 SplitMix64 16-prime PLE matches our formula bit-for-bit (`336` unique rows = `51 KiB` fetched); real `L3` `QSA` clips `23.03%` of per-head `ReLU` dots (`0/496` all-4-head zero block ties); `MXFP4` MoE + `FP8/BF16` GDN/QSA holds **`cos = 0.99873, SNR = 25.53 dB`** after `L3` `[EXECUTED]`.
   - Native `Ext4` prover verifies real `L0` `H_v = 48` (`1.05M`-cell) GDN WY + Top-1 routed `512E` `MXFP4` Expert `#7` in **`1,613.40 ms` prove / `44.02 ms` verify** (`4,707.54 KiB`), and real `L3` `QSA` `C3+C5` Top-$K_B$ in **`157.06 ms` prove / `10.85 ms` verify** (`585.17 KiB`, `Trap B1a` wraparound rejected) `[EXECUTED]`.

---

## 1. `Qwen/Qwen3.5-0.8B-Base` Pretrained Census & Architecture Verification

Inspected read-only from `/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/` `[SOURCE]`:

- **Tensor census (`488` tensors, `873,438,784` params = `1.66 GiB`) `[EXECUTED]`:** `320` Text LM tensors (`752,393,024` params: `embed_tokens` `[248320, 1024]` tied, `18 × GDN` at `l % 4 != 3` with `H_k=H_v=16, d_k=d_v=128, w_conv=4`, `6 × GQA` at `{3,7,11,15,19,23}` with `H_q=8` gated `[4096, 1024]`, `H_kv=2, d_h=256`, `25%` partial RoPE `64/256`, $\theta=10^7$, `24 × SwiGLU` `f=3584`; `186` 2D linear/MLP matrices = `497,614,848` weights) + `153` Vision (`100.59M`) + `15` MTP (`20.45M`).
- **Dual RMSNorm split `[SOURCE: modeling_qwen3_5.py, EXECUTED]`:** `input_layernorm`, `post_attention_layernorm`, `q_norm`, `k_norm`, and `language_model.norm` use zero-centered $\text{rmsnorm}(x) \cdot (1 + w)$, whereas `linear_attn.norm.weight` (`mean = 0.9518`) uses `Qwen3NextRMSNormGated` $w \cdot \text{rmsnorm}(y) \cdot \text{silu}(z)$ (no `1 +`).
- **Exact WY & cache checks (`T = 64`) `[EXECUTED]`:** L0 FP32 recurrent vs `C = 64` chunkwise WY: `max |dY| = 5.215e-8`, `max |dS| = 1.669e-6`; 24L cached decode vs prefill: `max |dLogit| = 3.815e-5`.

---

## 2. Honest 24-Layer `Qwen3.5-0.8B` Quantization Fidelity & Generation (`real_qwen35_gdn_eval.py`)

Command `[EXECUTED]`:
```bash
/Users/ember/.cache/uv/environments-v2/22c912b003d45dd8/62b316b52f48579c/bin/python \
  research/real_systems_wave_2026_11_21/experiments/real_qwen35_gdn_eval.py --export /tmp/qwen35_real_layer_turn.bin
```

| Execution Mode (`24` Pretrained Layers, `5 × T=64 = 320` pos) | NLL (nats) | PPL | Mean KL vs BF16 | Med KL vs BF16 | Top-1 Agree | Top-1 in Top-5 | Top-5 Overlap | L0 Cos / SNR | L23 Cos / SNR |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `BF16` (Native Pretrained) | `1.3824` | `3.984` | `0.00000` | `0.00000` | `100.00%` | `100.00%` | `100.00%` | `1.00000 / ∞` | `1.00000 / ∞` |
| `FP32` (Exact Float Reference) | `1.3828` | `3.986` | `0.00015` | `0.00007` | `99.38%` | `100.00%` | `98.69%` | `0.99999 / 49.00 dB` | `0.99996 / 41.36 dB` |
| **`FP8-E4M3` (All 186) + INT16 + IntWY(`C=64`)** | **`1.3760`** | **`3.959`** | **`0.00555`** | **`0.00204`** | **`98.12%`** | **`100.00%`** | **`94.75%`** | **`0.99906 / 27.17 dB`** | **`0.99751 / 23.10 dB`** |
| **`Mixed MXFP4` (72 MLP) + `FP8` (114 Attn/GDN) + IntWY** | **`1.4336`** | **`4.194`** | **`0.06385`** | **`0.02688`** | **`91.25%`** | **`99.37%`** | **`82.38%`** | **`0.99473 / 19.70 dB`** | **`0.97105 / 12.72 dB`** |
| **`Pure MXFP4-E2M1` (All 186 Mats) + INT16 + IntWY** | **`1.5397`** | **`4.663`** | **`0.15092`** | **`0.04856`** | **`89.69%`** | **`98.75%`** | **`77.25%`** | **`0.97684 / 13.47 dB`** | **`0.94353 / 9.54 dB`** |

- **Division-free integer WY (`M_wy = 4096`) `[EXECUTED]`:** `0` identity errors across all `23,592,960` solved entries/mode (`max |LHS| = 17,570,741`, `57.3× < p_BB / 2`; `0` INT16 clips).
- **Coherent 32-token completions `[EXECUTED]`:** All 4 modes solve `17 * 23 = 391` step-by-step, emit runnable Python `binary_search` and Rust `gcd` loops, and echo `'sk-proj-9f8a7b6c5d4e3f2a1b0c9d8e\n Mirroring config'` on `P5_Secret` for redaction + ZK `Absent` testing.

---

## 3. Real `Qwen/Qwen3.8-Flash-Next-FP8` + Shipped `NVFP4` / `MLX-4bit` Audit (`--qwen38fn-only`)

Pulled exact safetensors byte-ranges (`--qwen38fn-only --export-qwen38fn /tmp/qwen38fn_real_4layer_slice.bin`, `12.786 MiB` witness bundle) from `Qwen/Qwen3.8-Flash-Next-FP8`, `nvidia/Qwen3.8-Flash-Next-FP4-Local`, and `mlx-community/Qwen3.8-Flash-Next-4bit` `[SOURCE, EXECUTED]`:

- **Shipped 4-bit / 8-bit format comparison on real Layer-0 weights `[SOURCE, EXECUTED]`:**
  - `L0.mlp.experts.0.{gate,up,down}_proj` (`640×2560` vs `FP8` block-128): NVIDIA **`NVFP4-CSF`** (block-16 E2M1 + slab-delta E4M3 scales + `226–1,045` `24b-idx|8b-E4M3` exceptions + F32 `s2`) = **`cos 0.99518–0.99527 / 20.07–20.12 dB`**; **`MLX-4bit`** (affine `U4` group-32 `scales + biases`) = **`cos 0.99599–0.99626 / 21.03–21.26 dB`**; **our `MXFP4-E2M1` block-32 power-of-2 0-mul Horner** = **`cos 0.99276–0.99314 / 18.42–18.62 dB`** (`-1.5 dB` vs `NVFP4-CSF` in exchange for `0` prover multiplications and power-of-2 integer scales).
  - `L0.linear_attn.{in_proj_qkv,out_proj}` (`10240×2560`, `2560×6144` vs `BF16`): NVIDIA **retains `MXFP8` (`31.50 dB`)** instead of `NVFP4`! Across `L0..L3`, quantizing `512E` MoE experts to `MXFP4` while keeping GDN/QSA in `FP8/BF16` (`stream_mxfp4_moe`) holds **`cos = 0.99873, SNR = 25.53 dB`** (`98.4% -> 90.6%` Top-1 router match, `99.4% -> 95.9%` Top-10 overlap), vs `0.99312 / 18.31 dB` (`76.6%` Top-1) when quantizing GDN/QSA to `MXFP4` `[EXECUTED]`.
- **Real `GR`, `51.2B` `PLE`, `H_v = 48` `GDN`, & `QSA` measurements (`T = 64` with `<|endoftext|>` at pos `31`) `[EXECUTED]`:**
  - **8 `GR` blocks (`hc_count=4, hc_lowrank=320`):** `max |h_stream|` stays in `[0.0532, 0.5746]` (`L3` branch L2s `[0.276, 0.916, 2.232, 0.693]`, `inj_w ∈ [4e-9, 1.426]`), confirming `O(1)` FP8/INT16-safe residuals without Sinkhorn.
  - **Layer-2 (`l=1`) `51.20B` PLE:** Checkpoint `layer_multipliers = [23703573157769, 20109073645365, 8052911324071]` and 16 primes `20000003..20000171` (`weight_scale = 1.993e-4`) match our SplitMix64 generator bit-for-bit; `<|endoftext|>` (`248044`) at `t = 31` resets positions `[31, 32, 33]`; `1,024` lookups touch `336` unique rows (`51 KiB`).
  - **L0..L2 `H_v = 48` `GDN` (`786,432` active WY cells/layer):** `0` integer WY errors (`M_wy = 4096`), **`SNR = 56.09–60.22 dB`** vs FP32 `solve_triangular` (`max |dY| = 2.2e-8..1.8e-7` vs recurrent).
  - **L3 `QSA` `4Q/1KV` `ReLU` indexer (`496` causal `(q, b)` pairs):** Per-head `raw_dot <= 0` (`ReLU = 0`) fires **`23.03%`** (`21.88%` at `t=63`), while all-4-head sum `score == 0` fires **`0 / 496` (`0.0%`, `score ∈ [6.038, 14.100]`)**.

---

## 4. Native Multithreaded (`rayon`) Rust Prover & Succinct `Ext4` Verifier (`native/qwen35audit/`)

Commands `[EXECUTED]`:
```bash
CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-qwen35audit \
  cargo test --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml --release -p qwen35audit
CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-qwen35audit \
  cargo run --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml --release -p qwen35audit --bin qwen35_audit_demo
```

- **Cryptographic soundness (`src/{ext4,pcs_ext4,gruen_ext4,u1_audit}.rs`) `[DERIVED, EXECUTED]`:**
  - `BabyBear Ext4` ($p = 2013265921$, $X^4 - 11$, `123.69`-bit challenges, `0` prover inversions incl. `ZeroEqFallback`); NIST `cSHAKE256` Merkle & Fiat–Shamir.
  - `SuccinctExt4Pcs` (`blowup = 8, t_cols = 208, zk = true`, Shamir degree hiding + row masks): **`103.49` bits `[AHIV17]` $d/3$ UD | `105.63` bits `[BCIKS20]` $(1-\rho)/2$ UD** (unconditional, `0` conjectures).
  - Subdomain-lifted `D1b` projective fraction-tree LogUp-GKR (`ProveKit v2` §3.2 prefix projection: `64×` smaller table tree on `[0, 4096)` WY range; `2,560`-row DFA table for zero-cleartext ZK `Absent("sk-...")` per `CERTIFICATES.md` `P4`/`P6`/`L3`).

| Subsystem / Proof Target (`native/qwen35audit --release`, Apple Silicon) | Scale / Witness | Prove / Commit | Standalone Verify | Proof / Root Size |
|---|---|---:|---:|---:|
| Zero-copy `libc::mmap` + 24L `MXFP4` `cSHAKE256` registry | `488` tensors, `186` mats (`497.61M` w) | `0.90 ms` + `1,569.4 ms` | — | `32 B` (`59726b21..`) |
| **`U1` Online 25-Boundary Stream / Full ZK `SuccinctExt4Pcs`** | `25 × 64 × 1024` (`T = 64`) | **`29.4–42.8 µs/tok`** / `182.4 ms` | `1.88 ms` / bundled | `800 B` (`25 × 32 B`) |
| **VRF-Audited `Qwen3.5` `GDN+SwiGLU` Layer (`L10`, E2E ZK)** | `262K` WY + `D1b` + `3584×1024` `MXFP4` + ZK DFA | **`550.09 ms` (`8.60 ms/tok`)** | **`55.29 ms`** | **`4,642.56 KiB`** |
| PyTorch `Qwen3.5` L0 `MXFP4` `in_proj_z` / `out_proj` / `gate_proj` | `2048×1024` / `1024×2048` / `3584×1024` | `161.6` / `132.1` / `244.6 ms` | `12.1` / `12.5` / `17.4 ms` | succinct `Ext4` PCS |
| Standalone Zero-Cleartext ZK `Absent("sk-...")` Receipt (`P5`) | `L = 128` padded (`2,560` DFA rows) | **`43.55 ms`** | **`7.50 ms`** | `444 KiB` (ZK PCS) |
| **Real `Qwen3.8-Flash-Next` L0 `H_v=48` WY + Top-1 `512E` Expert `#7`** | `1,048,576` WY + `D1b` + `640×2560` `MXFP4` | **`1,613.40 ms`** | **`44.02 ms`** | **`4,707.54 KiB`** |
| **Real `Qwen3.8-Flash-Next` L3 `QSA` `C3+C5` Threshold Top-$K_B$** | `64 × 16` blocks + `D1b` (`Trap B1a` tested) | **`157.06 ms`** | **`10.85 ms`** | **`585.17 KiB`** |

- **Planted soundness teeth (`6/6` deterministically rejected in `tests/real_qwen35_e2e.rs` & `qwen35_audit_demo`) `[EXECUTED]`:** (1) `MXFP4` weight nibble swap; (2) `GDN` WY `UW` cell mutation; (3) `U1` boundary activation tamper; (4) `SuccinctExt4Pcs` coset column forgery; (5) unredacted `sk-proj-...` leak (`q_L = 4` sink); (6) `QSA` `Trap B1a` $\tau \ge 2^{30}$ bottom-$k$ wraparound (`tau_hi = 32768` rejected).

---

## 5. Proposed `docs/VERDICTS.md` Folds, Open Boundaries, & Absence Ledger

1. **Verdict-changing findings (for coordinator fold; `docs/VERDICTS.md` untouched):**
   - **`VERDICTS.md` §9 (`Exact Recompute / Audit` & `EinSumcheck`):** Close the pretrained model-reality gap — integer `C = 64` WY + `FP8`/`MXFP4` runs with `0` WY errors on real `Qwen3.5-0.8B` (`24L`, `FP8 KL = 0.00555 nats`, `Mixed-MXFP4 KL = 0.06385 nats`) and real `Qwen3.8-Flash-Next` (`L0..L3`), with per-head `u_scale[h]` mandatory against pretrained `beta ≈ 10^-3` underflow (`38×` KL gain at `0` prover gates) and `FP8/MXFP8` Attn/GDN + `MXFP4` MLP/MoE validated against NVIDIA's shipped `NVFP4 + MXFP8` split.
   - **`VERDICTS.md` §9 (`U1 Commit-Then-Audit & Content Certificates`):** Record native `BabyBear Ext4` (`103.5`-bit provable UD) `U1` online overhead (`29.4–42.8 µs/tok` hash stream / `2.85 ms/tok` ZK PCS) and standalone VRF-audited layer + zero-cleartext ZK `Absent("sk-...")` verification (`55.3 ms` `Qwen3.5`, `44.0 ms` `Qwen3.8` `H_v=48` GDN+MoE).
2. **What we could NOT verify (`[OPEN]`):**
   - Full 48-layer `248,320`-vocab perplexity on `Qwen/Qwen3.8-Flash-Next-FP8` (`180 GB` across `94` shards + `51.2B` PLE; `383 GiB` free disk precluded full download) `[OPEN: full 48L Qwen3.8 PPL]`.
   - Outer recursive STARK/`WHIR` compression of the `4.53–4.60 MiB` unrecursed `t_cols = 208` Ligero leaf receipts `[OPEN: outer WHIR/FRI wrap]`.
3. **Absence claims (corpus + instrument):**
   - Zero `nvfp4`/`mxfp4` decoders in upstream `transformers` `models/qwen4_exp/`: searched `/Users/ember/.cache/uv/archive-v0/tcu2kQKeHZ7tkbkh/transformers/models/qwen4_exp/` via `ls` and `read_file` (`modeling_qwen4_exp.py`, `configuration_qwen4_exp.py`); `NVFP4-CSF` (`nvfp4_csf_fixed` + `24b-idx|8b-E4M3` `nvfp4_csf_exceptions` + `weight_scale_2`) was decoded directly from `nvidia/Qwen3.8-Flash-Next-FP4-Local` `safetensors` byte slices.
