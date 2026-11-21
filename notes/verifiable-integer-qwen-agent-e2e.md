# Verifiable Exact-Integer `Qwen` Agent Serving and Lean-Verified `VAGENT01` Byte-Stream Turn Weld

**Date:** 2026-11-21
**Status:** Kernel-verified in Lean 4.35.0 (`0 sorry`, `0` custom axioms, `0 native_decide`, `0 #guard`, `23` `#guard_msgs`-pinned `#print axioms` checks, `-DwarningAsError=true` in isolated overlay `./build/`) and executed in 100%-native `--release` Rust (`zero` Python in the online path, `zero` floating-point ops in online prefill/decode, bit-identical `1T == 12T` SHA-256 & `cSHAKE256` intermediate digests across 24 layers + 248,320-vocab `lm_head`).

## 1. Executive Summary & Closed Gaps

Prior waves left two architectural trust-boundary gaps between local LLM serving and formal policy enforcement:

1. **System Integration Gap #1 — Float Serving vs Integer Proving (`[REFUTED: float Q4_K / BF16 llama.cpp serving as witness-compatible with deterministic integer zkML layer proofs]`):** Floating-point SIMD reductions reorder non-associative `f32`/`bf16` additions across thread counts, causing hidden-state drift between the served model and the integer witness proved in `qwen35audit`.
2. **Trust-Boundary Gap #5 — Unwelded Receipts Across `U1` + Sanitizer + Parser (`[REFUTED: standalone model-audit, redaction, and CFG proofs without a single byte-decoded turn weld]`):** Separate proofs of `U1` layer execution, `RewriteCert` secret scrubbing, and LL(1) `miniJsonCfg` parsing do not prevent cross-stage `TK` boundary/prompt splicing, third-party bundle re-pointing, or non-canonical wire-prefix smuggling unless welded from raw octets.

We close both gaps end-to-end across `minidregg/Assurance/` and `native/qwen35audit/` (incorporating all `Claude Fable` + `Codex gpt-6.2-astra` cross-audit hardenings):

| Artifact | Tier / Role | Core Verified / Executed Deliverable |
|---|---|---|
| [agent_runner.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/agent_runner.rs#L1-L6013) | Native Rust engine & `VAGENT01` / `QW35U1P2` | Pure-Rust `QwenBpeTokenizer`, 100%-integer 24-layer `ExactIntQwen35Engine` (`320` committed execution tensors, `Mixed-MXFP4/FP8-E4M3` + `INT16/Q16` + `C=64` `IntWY` w/ dynamic `u_shift[h]` + integer LUTs + exact `i32` boundary deltas), pure-Rust RFC 1951 `.npz` `Qwen3.8-27B` `MXFP4` prover (`8 -> 0` `-0.0` canonicalization), `VASTMT01`/`VAGENT01` codecs, statement-bound `QW35U1P2` (`UW`/`RHS` `D1b` + stride-`4096` `Absent` + `248`-bit `w_clean` MLE tie), `verify_vagent01_bytes_pinned`, & `0`-`sk-` `PublicRedactedVAgent01Bundle` (`[EXECUTED]`) |
| [verifiable_qwen_agent.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/bin/verifiable_qwen_agent.rs#L1-L208) | Live agent CLI | Zero-Python E2E turn runner: `Qwen3.8-27B` `.npz` slice proof + live 24L `Qwen3.5-0.8B` `CotToolCall` generation + `1T == 12T` determinism check + pinned `VAgent01Bundle` & `PublicRedactedVAgent01Bundle` emission (`[EXECUTED]`) |
| [verifiable_agent_e2e.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/verifiable_agent_e2e.rs#L1-L404) | Rust E2E & falsifier suite | `Qwen3.8-27B` `51,851`-nibble `-0.0` canonicalization, `[0, 255]` / `>= 2^64` overflow / `BatchCons` & `Digits` wire-bomb / duplicate-key JSON splice refusal, `1T == 12T` digest equality, Lean golden vector parity, `8` planted forgery/re-pointing/pin attacks, & `PublicRedactedVAgent01Bundle` `0` `>= 6B` secret-slice leak audit (`[EXECUTED]`) |
| [VerifiableAgentTurnWeld.lean](file:///Users/ember/dev/minidregg/Assurance/VerifiableAgentTurnWeld.lean#L1-L1838) | `Assurance/` (`Lean 4.35.0`) | `miniValueStream`, `turnStmtStream` (`VASTMT01`), `turnReceiptStream` (`VAGENT01`), round-trip/injectivity/trailing-byte refusal, input-pinned `u1TurnHead_eq_or_collision` (`U1TurnHeadCollision`), `verifyAgentTurnBytes_sound_or_collision` (`AgentTurnWeldCollision`), `QueryEnv`-parametric `verifyAgentTurnBytes_certSound` + `verifiableAgentTurn_produced_weld` + non-vacuous `< 1` `loggedSampleTurnEnv_bindSound` & `verifiableAgentTurn_produced_weld_nonvacuous`, universal falsifiers, & `#eval` live Rust `VAGENT01` check (`[DERIVED]`, `[EXECUTED]`) |
| [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_weld/build_and_verify.sh#L1-L212) | Isolated-overlay verifier | `check-import-boundary.sh` + isolated `./build/` Lean 4.35.0 kernel check (`-DwarningAsError=true`, `0` `lake build` into `minidregg/.lake`) + `--release` Rust E2E tests + live CLI -> Lean `#eval` round-trip (`[EXECUTED]`) |

---

## 2. 100%-Integer 24-Layer `Qwen3.5-0.8B` Serving & `Qwen3.8-27B` `MXFP4` Canonicalization

### 2.1 Zero-Float Online Serving Architecture (`ExactIntQwen35Engine`)

In [agent_runner.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/agent_runner.rs#L100-L2530), `ExactIntQwen35Engine` memory-maps `/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/model.safetensors-00001-of-00001.safetensors` ([SOURCE: Qwen/Qwen3.5-0.8B-Base HF snapshot]) directly in Rust with zero PyTorch or Python dependencies:

- **Full `320`-Tensor Execution Commitment (`497.61M` quantized 2D params + all 1D norms/SSM params + embeddings, `weight_root = 4aa1ef57d119e840...`, `[EXECUTED]`):**
  - `18` `GatedDeltaNet` (`GDN`, `l % 4 != 3`, `H = 16, d_h = 128`) + `6` `GQA` (`l % 4 == 3`, `H_q = 8, H_{kv} = 2, d_h = 256, rot = 64`) attention projections (`114` 2D tensors in block-32 `FP8-E4M3`, excluding `0x80` `-0.0`) + `72` `SwiGLU` MLP matrices (`gate_proj`, `up_proj`, `down_proj` in block-32 `MXFP4-E2M1` with `canonicalize_e2m1_nibble` mapping `8 -> 0`).
  - All `132` per-layer 1D execution tensors (`input_layernorm`, `post_attention_layernorm`, `conv1d`, `A_log`, `dt_bias`, `linear_attn.norm`, `q_norm`, `k_norm`) are appended to each layer's Merkle leaf (`layer_digests[0..24]`), and global `embed_tokens.weight` (256-chunk parallel Merkle root) + `final_norm.weight` are committed in `layer_digests[24]` (`320` total tensors in `weight_root`).
  - Tied `[248320, 1024]` `BF16` embeddings / `lm_head` use a 65,536-entry `BF16 -> Q16` `i16` LUT (`0` float ops in `argmax_lm_head_int`).
- **Deterministic Integer Nonlinearities & `C = 64` `IntWY` (`[DERIVED]`, `[EXECUTED]`):**
  - `RMSNorm` (`1 + w` on standard norms; plain `w` on `Qwen3NextRMSNormGated` `linear_attn.norm.weight` per [real_qwen35_gdn_eval.py](file:///Users/ember/dev/zkml-research/research/real_systems_wave_2026_11_21/experiments/real_qwen35_gdn_eval.py#L140-L215)) uses exact `i128` sum-of-squares + 2048-entry `rsqrt` LUT + 1 integer Newton–Raphson step; `EXP`/`SIGMOID`/`SILU`/`SOFTPLUS`/`RoPE` use fixed-point `Q16`/`Q15` LUTs.
  - Chunkwise `C = 64` `IntWY` (`prefill_chunk64_int`) solves $(I + L) U = V_{\text{scaled}}$ in `i64`/`i128` with per-head dynamic `u_shift[h] ∈ [4, 26]`, widens boundary residual deltas to exact `i32` (`(mb as i32) - (h_b_i16[i] as i32)`, zero `i16` saturation), and updates `ExactIntDecodeCache` (`conv_q16`, `ssm_q16`, `k_cache_q12`, `v_cache_q12`) during autoregressive decoding.
  - Disjoint-row sequential `i64`/`i128` accumulators yield **bit-identical SHA-256 and `cSHAKE256` digests across `1` vs `12` `rayon` threads** (`[EXECUTED]`).

### 2.2 Native `Qwen3.8-27B` Real `MXFP4` `.npz` Slice & `-0.0` Nibble Canonicalization

In [agent_runner.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/agent_runner.rs#L2535-L3240), `audit_qwen38_27b_mxfp4_npz_slice` parses `/Users/ember/.cache/zkml-models/qwen38_27b_e2m1_slice/qwen38_27b_l0_gate_proj_256x5120.npz` (`[256, 5120]` = `1,310,720` weights) via a checked pure-Rust RFC 1951 `DEFLATE` + ZIP/`.npy` reader:
- **Measured `-0.0` Rate (`[EXECUTED]`):** **`51,851` nibbles (`3.956%`) are non-canonical `0b1000` (`-0.0`)**. Canonicalizing `8 -> 0` leaves `0` `0b1000` nibbles, preserves exact integer contractions (`max |diff| = 0`, `max |Y_raw| = 562,704 < P/2`), separates raw vs canonical `cSHAKE256` digests, and proves/verifies a `124`-bit `BabyBear Ext4` `Mxfp4DelayedBjkExt4Proof` + `SuccinctExt4Pcs` opening in **`115.84–145.31 ms` prove / `13.34–13.55 ms` verify** (`1,528.73 KiB` = `1,565,421 B`).

---

## 3. Lean 4.35.0 Turn Weld & Dual-Family Cross-Audit Hardening

### 3.1 Canonical `VASTMT01` & `VAGENT01` `StreamCodec` Wire Format

In [VerifiableAgentTurnWeld.lean](file:///Users/ember/dev/minidregg/Assurance/VerifiableAgentTurnWeld.lean#L68-L477), we construct prefix-free `StreamCodec` instances ([SOURCE: Theory/StreamCodec.lean:194-320]) `miniValueStream`, `turnStmtStream` (`VASTMT01`), and `turnReceiptStream` (`VAGENT01`), proving `decodeTurnStmt_encodeTurnStmt`, `encodeTurnStmt_injective`, `trailing_stmt_bytes_refused`, `decodeTurnReceipt_encodeTurnReceipt`, `encodeTurnReceipt_injective`, and `trailing_wire_bytes_refused` (`[DERIVED]`).

### 3.2 Input-Pinned Collisions, `QueryEnv` `P8` Weld, & `QW35U1P2` Cryptographic Hardenings

Adversarial cross-audits (`Claude Fable` + `Codex gpt-6.2-astra`, board `#112` & `#117`) drove six verified hardenings (`[DERIVED]`, `[EXECUTED]`):
1. **Input-Pinned Collision Frames & Byte-Stream Capstone (`[DERIVED]`):** Deterministic `u1ChainCollisionFrames` and `u1TurnHeadCollisionFrames` eliminate existential `∃ cust left right, FramedXofCollision` pigeonhole vacuity. Theorem `verifyAgentTurnBytes_sound_or_collision` ([lines 868–959](file:///Users/ember/dev/minidregg/Assurance/VerifiableAgentTurnWeld.lean#L868-L959)) proves `verifyAgentTurnBytes stmtBytes receiptBytes = true` welds `(namedPrompt, namedBoundaries[0..L], namedProofDigest, namedRaw, namedClean)`, canonical 5-rule `redactBytes` + universal `AbsentPlain`/`Regex.paddedComplement`, and unique LL(1) `AttrReplay miniJsonCfg` AST extraction (`ast' = stmt.claimedAst ∧ rs' = rs`) — or exhibits input-pinned `AgentTurnWeldCollision`.
2. **Non-Vacuous `QueryEnv`-Parametric `P8` `Produced` Weld (`[DERIVED]`):** `verifyAgentTurnBytes_certSound` and `verifiableAgentTurn_produced_weld` ([lines 1068–1156](file:///Users/ember/dev/minidregg/Assurance/VerifiableAgentTurnWeld.lean#L1068-L1156)) generalize from `unrestrictedEnv` (where `lengthRootScheme` hits 33-byte pigeonhole `bindAdv ≥ 1`) to **arbitrary `E : QueryEnv UInt8`** and bind `(stmt.weightRoot, (stmt.promptLength, ofDigest256 stmt.promptRoot))` directly to `stmt`. Theorems `loggedSampleTurnEnv_bindSound` and `verifiableAgentTurn_produced_weld_nonvacuous` ([lines 1335–1452](file:///Users/ember/dev/minidregg/Assurance/VerifiableAgentTurnWeld.lean#L1335-L1452)) constructively inhabit all three premises `(ProducedSound, CertSound, BindSound)` simultaneously on `91` B / `95` B logs at **`ε_u1 = 0, ε_cert = 0, bindAdv = 0 < 1`**.
3. **Anti-Re-Pointing Statement-Bound `QW35U1P2` + `248`-Bit `w_clean` MLE Tie (`[EXECUTED]`):** `prove_hardened_vagent_u1_bundle` / `verify_hardened_vagent_u1_bundle` absorb `(weight_root, prompt_len, prompt_root, raw_len, raw_root, clean_len, clean_root, boundary_roots[0..25])` into both layer and absence transcripts before squeezing challenges, and enforce `mle_eval_bb_at_ext4(bytes_pad(w_clean), z) == b_eval` at both `z_dfa_leaf` and `z_b8_leaf` (`248` bits over `Ext4`), defeating third-party VRF-grinding re-pointing forgeries (Planted Attacks 7a & 7b) and pinning `(expected_weight_root, expected_qs_binding)` via `verify_vagent01_bytes_pinned`.
4. **Collision-Free Stride-`4096` `Absent` DFA + Position-Dependent Byte/EOF Range (`[EXECUTED]`):** `HardenedPaddedAbsenceZkReceipt` uses injective `tuple = q + 8*b + 4096*q_next` (`8 * 512 == 4096`, eliminating `(0, 256, 0) == (0, 0, 1) == 2048` stride-`2048` overlap), checks `shift_gruen_proof.rounds.len() == m`, and proves `b_pad[t] - 256 * 1[t >= word_len] ∈ [0, 256)` (`m_tab = 8`), forcing `b_pad[t] < 256` on `0..word_len` and `b_pad[t] == 256` on `word_len..pad_len` even when `opt_cleartext_bytes == None`.
5. **Signed-Quotient `UW`/`RHS` `D1b` Bounds Against `mod P` Wraparound (`[EXECUTED]`):** Commits `UW + 65536 ∈ [0, 2^{17})` and `RHS + 16384 ∈ [0, 2^{15})` prior to `z_hik` and opens both at `z_hik` against `layer_proof.{uw,rhs}_eval_at_z`, bounding `|4096*(RHS - UW) + 2048 - rem| <= 335,548,416 < P/2` (blocking `UW = 491,520` `mod P` wraparound).
6. **Secret Hygiene & Privacy Scope (`[EXECUTED]`):** Local quarantine `VAgent01Bundle` (`0xA1`) carries `w_raw` for TCB `redactBytes` verification; external `PublicRedactedVAgent01Bundle` (`0xA2`, `to_public_redacted_bytes` / `verify_public_redacted_vagent01_bytes`) strips `prompt_bytes` and `w_raw` (`0` `"sk-"` substrings on wire). `SuccinctExt4Pcs` provides single-opening salted RS column-tail + row-mask commitment hiding on unopened coordinates while random-point `Ext4` evaluations and `D1b` subproofs are disclosed in clear (not full-transcript HVZK); `QW35U1P2` layer audit covers the 64-token prefill `GDN+SwiGLU` chunk while decode steps emit deterministic `U1` boundary digests (`decode_stream_cshake256`).

---

## 4. End-to-End `[EXECUTED]` Benchmarks, Thread Determinism, & Wire Sizes

Command (`exit 0`): `/Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_weld/build_and_verify.sh`

| Stage / Metric | Measured Result (`--release` M2 Max / Lean 4.35.0) | Provenance |
|---|---|---|
| **24L `Qwen3.5-0.8B` Load (`mmap` + quantize & hash `320` tensors)** | **`1,077.37 ms`** (`497.61M` quantized params, `weight_root = 4aa1ef57d119e840...`) | `[EXECUTED]` |
| **Exact-Integer Prefill (`64` tok, `C = 64` `IntWY`, 12T)** | **`1,451.74 ms`** (**`44.09 tok/s`** unloaded; `31.81 tok/s` under heavy load) | `[EXECUTED]` |
| **Exact-Integer Greedy Decode (`28` tok `CotToolCall`, 12T)** | **`1,741.67 ms`** (**`16.08 tok/s`** unloaded; `13.96 tok/s` under heavy load) | `[EXECUTED]` |
| **Online `U1` Fast 25-Boundary `cSHAKE256` Stream** | **`24.06–29.17 µs/tok`** | `[EXECUTED]` |
| **`1T == 12T` Prefill 25-Boundary + Logit SHA-256 / `cSHAKE256`** | `ff64c7d992f753e3...` / `7cdc456f636ea787...` (bit-identical across runs & threads) | `[EXECUTED]` |
| **`1T == 12T` 28-Step Decode Stream SHA-256 / `cSHAKE256`** | `1f70b3e06c9deb13...` / `4def7048364043a9...` (bit-identical across runs & threads) | `[EXECUTED]` |
| **Wire Sizes (`VASTMT01` / `VAGENT01` / `QW35U1P2` Local & Public)** | **`236 B`** stmt / **`1,415 B`** receipt / **`5,831,863–5,833,527 B`** (`5,695–5,697 KiB`) local / **`5,831,543–5,833,207 B`** public (`0` `>= 6B` secret slices) | `[EXECUTED]` |
| **Hardened `QW35U1P2` Prove / Pinned Standalone Verify** | **`2,671.10 ms`** prove / **`146.62 ms`** verify (`L9`, `L21` VRF-selected, `UW`/`RHS` `D1b` + stride-`4096` `Absent`) | `[EXECUTED]` |
| **`Qwen3.8-27B` `[256x5120]` `.npz` `MXFP4` Slice (`51,851` `-0.0` -> `0`)** | **`109.86 ms`** prove / **`13.01 ms`** verify / **`1,528.73 KiB`** (`1,565,421 B`) `Ext4` proof | `[EXECUTED]` |
| **Isolated-Overlay Lean 4.35.0 Check (`VerifiableAgentTurnWeld.lean`)** | **`18.02–18.88 s`**, `0` warnings/errors (`-DwarningAsError=true`), `23` `#print axioms` pins, accepts fresh CLI `VAGENT01` bytes | `[EXECUTED]` |

---

## 5. Metered Search Ledger & Proposed Maintainer Folds

- **Metered Search Queries:** `0` `scry.py` queries, `0` `kagi.py` queries, `0` `eprint.iacr.org` downloads.
- **Proposed Maintainer Folds (unmodified per ownership rules):**
  1. `minidregg/Assurance.lean`: add `import Assurance.VerifiableAgentTurnWeld`.
  2. `docs/VERDICTS.md`: record closure of Float-vs-Integer Serving Gap (`44.09 tok/s` prefill / `16.08 tok/s` decode exact-integer 24L `Qwen3.5-0.8B`, `1T == 12T` bit-identical) and Lean-verified `VAGENT01` (`236 B` + `1,415 B`) + hardened `QW35U1P2` (`PublicRedactedVAgent01Bundle`, `0` `>= 6B` secret slices) turn weld.
