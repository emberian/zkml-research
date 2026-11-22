# Wearable SHE Organ #2 ("JITT"): Multi-Chunk `Qwen3.5` Gated-DeltaNet Recurrent State Carry (`S_c -> S_{c+1}`) over `WhirExt4Pcs + GMaskExt4` with `TVD = 0` Blinded State-Handoff

**Date:** 2026-11-22 · **Lane:** `she-gdn-chunk-carry-zk` (Wave 9 *Rainbows End* Wearable SHE Organ #2) · **Metered search ledger:** `Scry: 0, Kagi: 0, eprint.iacr.org: 0` `[EXECUTED]`

## 1. Scope & Deconfliction

- `[SOURCE]` Closes [wave8-unified-qwen-turn-and-payable-receipt.md](file:///Users/ember/dev/zkml-research/notes/wave8-unified-qwen-turn-and-payable-receipt.md) `§4 [OPEN]` item 3 (*"cross-chunk recurrent GDN state carry `S_{chunk,c} -> S_{chunk,c+1}` beyond `S_{init} = 0`"*). Read-only siblings inspected: [ZkmlDeltaNet.lean](file:///Users/ember/dev/minidregg/Theory/ZkmlDeltaNet.lean), [StreamCodec.lean](file:///Users/ember/dev/minidregg/Theory/StreamCodec.lean), [BabyBearExt4.lean](file:///Users/ember/dev/minidregg/Selvage/BabyBearExt4.lean), [Tower256CshakeMerkleBinding.lean](file:///Users/ember/dev/minidregg/Compiler/Tower256CshakeMerkleBinding.lean), and `qwen35audit::`{[qwen35_layer.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/qwen35_layer.rs), [whir_ext4.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/whir_ext4.rs), [continual_memory.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/continual_memory.rs), [unified_turn_weld.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/unified_turn_weld.rs)}.
- `[DERIVED]` For non-zero incoming fast-weight state $S_c \in R^{d_k \times d_v}$, intra-chunk token $i$ sees decayed incoming contribution $\gamma^{(i)} S_c$, shifting the division-free WY right-hand side to $(1 + L_c) U_{\text{wy},c} = V_{\beta,c} - K_{\text{dec},c} S_c$ (`(K_{dec,c})_{i,x} = \beta_i \gamma^{(i)} k_{i,x}`), outgoing carry to $S_{c+1} = \gamma_c S_c + K_{\text{tail},c}^\top U_{\text{wy},c}$, and readout to $Y_c = Q_{\text{dec},c} S_c + A_c U_{\text{wy},c}$.
- `[DERIVED]` Wrap-free `BabyBear` (`P = 2,013,265,921`) integer scales `M_WY = 512` (`HALF_WY = 256`, `R ∈ [0, 512)`), `S_SCALE = 512`, operator bound `[-512, 512)`, and state/WY bound `[-8192, 8192)` bound worst-case `K_{dec,c} · S_c` (`128 · 512 · 8192 + 512 · 8192 + 512 = 541,065,728 < P/2 = 1,006,632,960`) and `L_c · U_{wy,c}` / `K_{tail,c}^T · U_{wy,c}` (`276,824,576 < P/2`), packing all 11 `D1b` range witnesses into one `2^{22}` `[0, 16384)` LogUp table.
- `[DERIVED]` Strictly disjoint owned paths (`0` edits to `lib.rs`, `Assurance.lean`, `docs/VERDICTS.md`, or `notes/README.md`):
  1. [StreamingGdnCarryIvc.lean](file:///Users/ember/dev/minidregg/Assurance/StreamingGdnCarryIvc.lean) (`813 < 900` lines, Lean `v4.35.0`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `23` `#guard_msgs` axiom pins, `0` warnings).
  2. [streaming_gdn_carry.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/streaming_gdn_carry.rs) & [streaming_wearable_jitt.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/streaming_wearable_jitt.rs) (`#![deny(warnings)]`).
  3. [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/formal_gdn_carry/build_and_verify.sh) (isolated Lean `v4.35.0` overlay + `--release` Rust suite; auto-cleans `build/` and `target-w9-gdn-carry`).

## 2. Verified Lean `v4.35.0` Theorems (`[EXECUTED]`, `[DERIVED]`)

| Property | Theorem in `Assurance/StreamingGdnCarryIvc.lean` | Statement & Axiom Pin |
|---|---|---|
| Stateful WY $\leftrightarrow$ sequential `gdnStep` | `gdnPrefix_eq_stateful_wy` (`L179`), `wyStatefulChunk_eq_sequential_gdn` (`L270`), `wyStatefulReadout_eq_sequential_readout` (`L282`) | Over any `CommRing R`, `(1 + wyL) * U_wy = wyVBeta - wyKDec * S_c` forces exact step-by-step `gdnStep` state carry and `gdnReadout` from arbitrary `S_c` (`[propext, Classical.choice, Quot.sound]`). |
| Multi-chunk `C · L` exactness | `chunkedGdnChain_eq_sequential_gdn` (`L337`), `solveStatefulWy_spec` (`L164`) | Across `C` chunks (`C · L` tokens) from any `S 0`, per-chunk `ValidStatefulWyChunk` forces `S (Fin.last C) = gdnSeqList (flattenChunks chunks) (S 0)` (`[propext, Classical.choice, Quot.sound]`). |
| `O(1)` verifier RAM & `cSHAKE256` chain | `CarryVerifierState.byteFootprint_const` (`L381`), `verifyStreamingCarryChain_invariants` (`L442`), `streamingCarryChain_eq_or_collision` (`L499`) | Constant `144`-byte Lean verifier state (`0` axioms); equal terminal `chainDigest` pins `init` and every chunk's `(chunkIdx, layerIdx, rt_{S,c}, rt_{S,c+1}, tokCommit)` or extracts `FramedXofCollision`. |
| `C · ε_chunk` union bound | `union_bound_fin_prob` (`L526`), `streamingCarryChain_soundness_union_bound` (`L550`) | Any false terminal claim `S_C ≠ gdnSeqList (flattenChunks chunks) S_0` is accepted across all `C` chunks with probability `≤ (C : ℚ) * ε_chunk`. |
| Exact `TVD = 0` dual-mask handoff | `dualMaskHandoff_bijective` (`L603`), `dualMaskHandoff_binding_of_isUnit` (`L606`), `handoffTVD_eq_zero` (`L634`), `babyBearExt4_handoffTVD_eq_zero` (`L641`) | `(Δ_M, α * S_c(r) + M_1)` induces an explicit `F × F` bijection (`handoffTranscriptProb = 1 / |F|^2`, `TVD = 0`) over `BabyBearExt4` while binding `s₁ = s₂` for unit `α` (`[propext]`). |
| Witnesses & 4 `#tooth` falsifiers | `multiChunk_stateful_wy_witness_int` (`L672`), `multiChunk_witness_zmod16` (`L687`), `tooth_silent_s_init_zero_reset` (`L704`), `tooth_chunk_reorder_splice` (`L722`), `tooth_dropped_kc_sc_wy_coupling` (`L736`), `tooth_reused_single_mask_breaks_tvd_zero` (`L756`) | Non-zero `S₀, S₁, S₂` over `ℤ` and non-field `ZMod 16` (`4 * 4 = 0`); `[REFUTED: broken variants]` catches `S_init = 0` mid-session reset, chunk-reorder splice, dropped `- K_c · S_c` over `ℤ`/`BabyBear`, and single-mask reuse (`TVD > 0` over `ZMod 7`). |

## 3. Real `Qwen3.5-0.8B` `4 x 64` (`256`-Token) Wearable JITT Benchmarks (`[EXECUTED]`)

Command: `/Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/formal_gdn_carry/build_and_verify.sh` (`exit 0`, `0` warnings; Lean `v4.35.0` verified in **`5.93s`**):

| Chunk Transition (`Layer 8` GDN, `16x128x128`) | Wire Receipt | 24L Forward + WHIR Prove | Standalone Verify (`< 25 ms` budget) | Live `O(1)` Verifier RAM |
|---|---:|---:|---:|---:|
| Chunk 0 (`rt_{S,0} -> rt_{S,1}`) | `386.40 KiB` (`395,673 B`) | `6,546.80 ms` | **`8.44 ms`** | `136 B` |
| Chunk 1 (`rt_{S,1} -> rt_{S,2}`) | `384.57 KiB` (`393,795 B`) | `6,269.84 ms` | **`8.45 ms`** | `136 B` |
| Chunk 2 (`rt_{S,2} -> rt_{S,3}`) | `384.79 KiB` (`394,029 B`) | `6,301.86 ms` | **`8.28 ms`** | `136 B` |
| Chunk 3 (`rt_{S,3} -> rt_{S,4}`) | `384.76 KiB` (`393,991 B`) | `6,493.15 ms` | **`8.23 ms`** | `136 B` |

- `[EXECUTED]` **Zero drift & `O(1)` wearable memory:** Across 256 real BPE tokens vs. monolithic `1 x 256` execution (`9,154.6 ms`), streaming `4 x 64` achieved **`0 / 8,388,608` IEEE-754 `f32` bit drift** on final hidden states, **`0 / 4,718,592` cell drift** across all 18 GDN layers (`64,603..204,551 / 262,144` non-zero quantized integers/layer; `96,947` at audited Layer 8), identical top-1 next token (`220`), constant **`19.27 MiB` (`20,201,504 B`)** retained 24-layer state RAM, and **`630.00 MiB`** evicted from chunks `0..2`.
- `[EXECUTED]` **10 adversarial attack categories (`12` assertions) refused:** (1) `S_init = 0` silent mid-session reset at chunk 2, (2) `[r0, r2]` chunk-reorder splice, (3) stale `rt_{S,1}` rollback replay, (4) cross-session replay, (5) cross-layer splice (`L4 -> L8`), (6) dropped `K_c · S_c` WY coupling on non-zero `S_c`, (7) forged `s_out_root` substitution, (8a/8b) `+1` tamper on `TVD = 0` `mu_wy` and `delta_masks[0]`, (9) non-zero `L` diagonal (`IsStrictLowerTri` violation), and (10a/b/c) `gamma_int > M_WY`, GQA layer masquerade (`layer_idx = 3`), and trailing wire byte.

## 4. Model Boundary & `[OPEN]` Seams

- `[OPEN]` Each `SaltedGdnStateCommitment` allocates 5 disjoint one-time `Ext4` mask slots (`2` write, `3` read); proving a single checkpoint root more than once as incoming state requires a fresh re-masked commitment `rt'_{S,c}` (`rerandomize` step) to preserve `TVD = 0` without mask reuse.
- `[OPEN]` Folding all 18 GDN layers' `StreamingGdnCarryReceipt` instances per chunk into a single `Dregg-180` `OP_HEM` leaf (`Organ #1`) is unmeasured on hardware cycle-accurate RTL.
