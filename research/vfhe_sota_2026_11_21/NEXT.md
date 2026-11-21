# NEXT — `vfhe_sota_2026_11_21`

## 1. Ready-to-Land Maintainer Actions

1. **Apply the Kernel-Verified Lean 4 Patch to `/Users/ember/dev/minidregg` (When Approved):**
   ```bash
   git -C /Users/ember/dev/minidregg apply --check /Users/ember/dev/zkml-research/research/vfhe_sota_2026_11_21/formal/minidregg-vfhe-deltanet-gruen.patch
   git -C /Users/ember/dev/minidregg apply /Users/ember/dev/zkml-research/research/vfhe_sota_2026_11_21/formal/minidregg-vfhe-deltanet-gruen.patch
   ```
   Adds `Theory/BfvHoistedRescale.lean`, `Theory/ZkmlDeltaNet.lean`, `Assurance/ZkmlGruenSumcheck.lean`, and wires their root imports in `Theory.lean` and `Assurance.lean`.
2. **Proposed Maintainer Folds for `docs/DARK-LEARNING-SCHEME-DECISION.md` (§§1, 7, 8, 22):**
   - Fold `HoistedB61` (`6,144 -> 128` hoisted matvec certificates + fused `d`-free polynomial rescale + `Direct-20` / `Exact-Garner-15` canonical lifts + `step_counts.py:195` `relin` digit fix).
   - Record that **`Hoist-FHE(b, τ=64)` + §20.2 Ligero ZKPoPK flips strictly below `MPC` at `d = 4096`** in both committed bits (`21.50 Gbit = 0.68× MPC` w/ `Direct-20`, `25.08 Gbit = 0.80× MPC` w/ zero-slack `Exact-Garner-15`, `11.08 Gbit = 0.35× MPC` packed) and online wire (`32.24M` vs `305.9M` = `9.5×` smaller), and **`Inference-Only vFHEML` (`10.78 Gbit` `digits61`, `11.50M` wire)** beats 2L-MPC (`12.89 Gbit`, `203.4M` wire) even without Ligero ZKPoPK.
3. **Proposed Maintainer Folds for `docs/VERDICTS.md`:**
   - **§3 (`Encrypted attention`):** Keep dense softmax attention `[REFUTED]` at depth `<= 3`, and carve out **`Qwen3.8-Flash-Next` `Gated DeltaNet` (`75%` of layers: `O(1)` `0.211 GiB` encrypted state through `1M` ctx, depth-1 parallel-read crossing)** + **`QSA` (`25%` of layers: `K = 2048` crossing softmax, `850×–3,401×` fewer `EXP`s)**.
   - **§7.5 (`Hole B`) & §9:** Mark `Hole B`'s polynomial specification closed in Lean (`Theory/BfvHoistedRescale.lean`: `HoistedRescaleCert`, `hoistedRescaleCert_iff`, `hoistedRescaleCert_unique`, `holeB_modQ_alias_falsifier`), alongside `Theory/ZkmlDeltaNet.lean` (`wyChunk_bilinear_iff_recurrence` over any `CommRing`) and `Assurance/ZkmlGruenSumcheck.lean` (Mode-2 `<= 2/|F|` soundness + `r=0` & Jolt `#1474` teeth).
   - **§2 / §5 (`Lookup & Sparse Top-K`):** Record the two BabyBear `QSA` Top-`K_B` invariants (`C5: RangeCheck(τ < 2^30)` and `C3` tie-breaking on `ReLU == 0`) and the `51.2B` PLE separation (`Poseidon2 Merkle` / `2P-DPF` over `D1b`).

## 2. Open Follow-Up Experiments (`[OPEN]`)

1. **Post-Mirror-Sync Full-PDF Audit of `PRISM` (`ePrint 2026/1956`, CCS 2026) & `2026/2878`:**
   - Once `/Users/ember/dev/gh/forks/IACR-eprint-mirror/` syncs past `2026/1861`, read `2026/1956.pdf` locally to test whether its multi-field PCS (`MF-PCS`) + NTT PIOP further compresses the `128` remaining `HoistedB61` group certificates.
2. **Rust `breadstuffs` Implementation & Wall-Clock Benchmark:**
   - Benchmark `HoistedB61` (`32 × 64` scalar matvec at witness-bound FS points + `ProveKit v2` `2^20` subdomain projection + `c=3`/`c=4` `p61` `D1b` LogUp-GKR) and `Qwen3.8-Flash-Next` `C=64` chunkwise WY Gruen `EinSumcheck` in `breadstuffs`.
3. **Integer-Quantized `Qwen3.8-Flash-Next-FP8` Layer-Equivalence & Perplexity Gate:**
   - Build a single-layer (`1 GDN + 1 QSA + GR + 512E Top-10+1 MoE + Layer-2 PLE`) bit-exact integer reference harness against shipped `Qwen/Qwen3.8-Flash-Next-FP8` shard tensors.
