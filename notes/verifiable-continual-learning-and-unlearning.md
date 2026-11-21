# Verifiable Continual Cognitive Fast-Weight Learning & Rank-`r` Subspace Machine Unlearning

**Date:** 2026-11-21 · **Lane:** `verifiable-fastweight` (`afp_and_unified_wave_2026_11_21`; audited by `fastweight-neon-audit` `#93`, `Codex gpt-6.2-astra` `#115`, and `Claude Fable 5.2` `#132`)  
**Metered search counts:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org: 0` (`Qwen/Qwen3.5-0.8B-Base` read offline via `mmap` from local HF cache).  
**Verification Script (`[EXECUTED]`):** [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_continual/build_and_verify.sh) (`exit 0`, Lean `v4.35.0` `-DwarningAsError=true` + `scripts/check-import-boundary.sh` + `--release` Rust `continual_memory_unlearn` & `qwen_continual_memory_demo`).  
**Authored Artifacts (`[EXECUTED]`):** [VerifiableContinualLearning.lean](file:///Users/ember/dev/minidregg/Theory/VerifiableContinualLearning.lean) (`950` lines, `27` `#print axioms` pins), [continual_memory.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/continual_memory.rs) (`5,785` lines), [continual_memory_unlearn.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/continual_memory_unlearn.rs) (`394` lines), [qwen_continual_memory_demo.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/bin/qwen_continual_memory_demo.rs) (`270` lines).

---

## 0. Headline Verdicts (`[DERIVED]`, `[EXECUTED]`, `[REFUTED: raw non-orthogonal key erasure]`)

1. **Counterfactual gold-standard machine unlearning holds as an exact `CommRing` identity over Gated DeltaNet (`GDN`) fast weights (`0` retraining from genesis) `[DERIVED, EXECUTED]`.**
   - In Lean 4.35.0 ([VerifiableContinualLearning.lean](file:///Users/ember/dev/minidregg/Theory/VerifiableContinualLearning.lean)), sequential zero-value erasure `gdnErase k S := gdnStep 1 1 k 0 S = (1 - k ⊗ k) S` over any pairwise-orthonormal family `u : Fin r → (Fin dk → R)` (`Uᵀ U = 1`) collapses with zero cross-terms to `gdnEraseSeq (List.ofFn u) S = (1 - U Uᵀ) S` (`gdnEraseSeq_eq_one_sub_basisMatrix_mul`), annihilating every $x = \sum_a c_a u_a \in \text{span}(u)$ (`(S')ᵀ x = 0`, `gdnEraseSeq_annihilates_span`), preserving every orthogonal query $q \perp \text{span}(u)$ (`(S')ᵀ q = Sᵀ q`, `gdnEraseSeq_preserves_orth`), and satisfying `P² = P` (`gdnEraseSeq_idempotent`).
   - `retroactive_unlearn_state_eq_counterfactual` and `retroactive_unlearn_after_episode` prove that for any multi-episode session interleaving forgettable steps along $k_m \in \text{span}(u)$ (at $\alpha = 1$, arbitrary $\beta_m, v_m$) with orthogonal retained steps $q_j \perp \text{span}(u)$ (arbitrary $\alpha_j, \beta_j, v_j$), applying `gdnEraseSeq (List.ofFn u)` **once** post-session yields exact counterfactual state `gdnRun retained (gdnEraseSeq u S₀)` (`= gdnRun retained 0` at $S_0 = 0$) and identical surviving readouts for **arbitrary** $S_0$.
2. **Unorthogonalized erase keys and un-isolated cross-episode keys fail order-independence and counterfactual equivalence (`[REFUTED: raw non-orthogonal key erasure as counterfactual unlearning]`) `[DERIVED, EXECUTED]`.**
   - Proved sharp in Lean via `gdnErase_noncomm_of_nonorth` (`ℤ`), unit-norm Pythagorean `gdnErase_noncomm_unit_babybear` (`ZMod 2013265921`), `corrupted_orthogonality_leaves_residual_falsifier` (duplicate columns in $U$ negate rather than erase $S^\top U$), `retroactive_unlearn_nonorth_interference_falsifier`, and `retroactive_unlearn_decay_falsifier`.
   - Confirmed empirically on **real pretrained `Qwen/Qwen3.5-0.8B-Base` weights** (`[EXECUTED]`): with Walsh–Hadamard domain subspace routing (`32` modes/domain), post-unlearning Episode B recall drops `100.0% → 0.0%` (`7.427e-5 < 10^-4` relative residual on `H_v = 16`, `4.590e-5` on `H_v = 48`) while Episodes A & C preserve **`100.0%` recall (`85.91 dB` / `85.26 dB` SNR on `H_v = 16`; `90.23 dB` / `90.95 dB` on `H_v = 48`)** vs `Train(A + C)`. Dropping domain orthogonality (`MemoryDomain::UnisolatedRaw`) still annihilates Episode B (`7.307e-5`), **but collapses Episode C counterfactual SNR from `85.26 dB` to `3.55 dB`** (`-81.7 dB`) via delta-rule residual contamination $e_C = v_C - S_B^\top q_C$.
3. **Cross-audit-hardened `BabyBear Ext4` ZK Continual-WY & Rank-`r` Unlearning Prover/Verifier (`0` `mod P` wraparound across all 9 contractions) rejects `9/9` adversarial vectors `[EXECUTED]`.**

---

## 1. Kernel-Verified Lean 4.35.0 Theorems (`[DERIVED]`, `[EXECUTED]`)

Verified in `2.44 s` via [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_continual/build_and_verify.sh) (`0` warnings under `-DwarningAsError=true`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`; `27` `#guard_msgs`-pinned `#print axioms` in `{propext, Classical.choice, Quot.sound}`; `Theory/` import boundary `Mathlib.*` + `Theory.ZkmlDeltaNet` only):

| Part | Theorems in [VerifiableContinualLearning.lean](file:///Users/ember/dev/minidregg/Theory/VerifiableContinualLearning.lean) | Algebraic Guarantee Established over Any `[CommRing R]` |
|---|---|---|
| **A. Rank-`r` Unlearning** | `gdnErase_eq_proj_mul` (`L114`), `gdnErase_comm_of_orth` (`L145`), `gdnEraseSeq_perm_of_pairwise_orth` (`L212`), `gdnEraseSeq_ofFn_eq_subspaceProjCompl` (`L241`), `basisMatrix_transpose_mul_eq_one_iff` (`L259`), `gdnEraseSeq_eq_one_sub_basisMatrix_mul` (`L279`), `gdnEraseSeq_annihilates_span` (`L359`), `unlearned_transpose_mul_basisMatrix_eq_zero` (`L371`), `gdnEraseSeq_preserves_orth` (`L393`), `gdnEraseSeq_idempotent` (`L790`) | Commutativity & arbitrary `List.Perm` order-independence under orthogonality; collapse to $(1 - U U^\top) S$; exact annihilation $(S')^\top (\sum_a c_a u_a) = 0$ & $S'^\top U = 0$; exact preservation $(S')^\top q = S^\top q$ on $\text{span}(u)^\perp$; idempotence $P^2 = P$. |
| **B. Continual WY Monoid** | `gdnMultiStep_state_associative` (`L450`), `GdnChunkSummary.comp_assoc` (`L489`), `summarizeEpisode_append` (`L503`), `summarizeEpisode_eval_eq_gdnRun` (`L536`), `gdnMultiStep_witness_int` (`L561`), `gdnMultiStep_witness_babybear` (`L579`) | Fold associativity `gdnRun (ep₁ ++ ep₂) S₀ = gdnRun ep₂ (gdnRun ep₁ S₀)`; affine monoid homomorphism decomposing stateful chunks into `trans * S₀ + gdnRun ep 0`; kernel-decided `ℤ` & `ZMod 2013265921` witnesses. |
| **C. Retroactive Counterfactual** | `gdnEraseSeq_absorbs_span_step` (`L629`), `gdnEraseSeq_comm_orth_step` (`L646`), `retroactive_unlearn_state_eq_counterfactual` (`L732`), `retroactive_unlearn_after_episode` (`L756`), `retroactive_unlearn_three_episode_witness` (`L822`) | Post-hoc `gdnEraseSeq u` absorbs arbitrary $\alpha = 1$ `span(u)` writes and commutes past arbitrary $(\alpha_j, \beta_j)$ orthogonal writes, matching counterfactual `Train(D \ D_forget)` entry-for-entry (`by decide` 3-episode witness). |
| **Sharpness Teeth** | `gdnErase_noncomm_of_nonorth` (`L157`), `gdnErase_noncomm_unit_babybear` (`L848`), `corrupted_orthogonality_leaves_residual_falsifier` (`L407`), `retroactive_unlearn_nonorth_interference_falsifier` (`L864`), `retroactive_unlearn_decay_falsifier` (`L881`) | Refutes non-orthogonal order-independence (incl. unit-norm BabyBear keys), non-orthonormal $U$ projection, overlapping cross-episode keys, and $\alpha \ne 1$ on forgotten steps. |

---

## 2. Native Rust Architecture & Real `Qwen3.5` / `Qwen3.8` Measurements (`[SOURCE]`, `[EXECUTED]`)

### 2.1 Zero-Wraparound Fixed-Point & ZK Protocol Design ([continual_memory.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/continual_memory.rs))

Every inner product in both proofs is range-bounded in-circuit via `D1b` LogUp-GKR so its worst-case integer magnitude is strictly $< (P_{\text{BB}} - 1)/2 = 1{,}006{,}632{,}960$, eliminating `mod P` wraparound (`#93`, `#115`, `#132` `[DERIVED, EXECUTED]`):

1. **Scales & Centered 2-Limb Basis (`M_GS = 32,768 = 256 × 128`, `S_SCALE = 76,000`, `CMEM_WY_SCALE = 128`):**
   - `U_int = U_lo + 256 · U_hi` with `U_lo ∈ [-128, 127]`, `U_hi ∈ [-128, 127]` (`[0, 256)` `D1b` tables, `|U_int| <= 32,896`) and two-sided `S ± 60,000 ∈ [0, 131,072)` (`|S| <= 60,000` -> $128 \times 60{,}000 \times 128 = 9.83 \times 10^8 < P_{\text{BB}}/2$).
2. **`ZkContinualUpdateProof` (`CMWYUP03`, `S_prev -> S_post` + `cSHAKE256` MMR with `leaf_index == episode_idx`):**
   - **`W0` (`K ∈ span(U)` registration weld, `#115.1`):** Proves `u_inactive_zero` (`U_{h >= h_v ∨ a >= r} == 0`) and `U_int * C_ep == M_GS * (K_int - E_span) + R_span - M_GS/2` (`|C_ep| <= 128`, `|E_span| < 4`, $8 \times 32{,}896 \times 128 = 3.37 \times 10^7 < P_{\text{BB}}/2$), binding `forget_request_root = H(h_v, h_pad, rank_r, u_pcs_root, nonce)` to `k_pcs_root` at episode registration.
   - **`W1` (`L <-> K K^T` Gram weld, `#115.2`):** Proves `K_int * K_int^T == 128 * (L + D_U) + R_kk - 64` (`128^3 = 2.10e6 < P_BB/2`) with `(1 - SLT) ⊙ L == 0` and `SLT ⊙ D_U == 0`.
   - **`W2..W4` (Division-free `C = 64` WY):** Proves `L * UW`, `RHS[col >= 128] == K_int`, `W * S_prev`, and `K_int^T * Delta_eff` with `|K|, |W|, |L| <= 128` and `|UW|, |Delta_eff|, |dS| <= 65,536` ($\le 9.83 \times 10^8 < P_{\text{BB}}/2$).
3. **`ZkUnlearningCertificate` (`CMUNLN03`, `S_before -> S_unlearned` against blind `forget_request_root`):**
   - Proves `(h_v, rank_r)` + optional `EpisodeMmrEntry` inclusion, `U0` (`u_inactive_zero`), and 2-step `÷ 256 / ÷ 128` contractions for `U1` (`|U^T U - 32768^2 I_{<r}| < 256 · 512`), `U2` (`U_int * P_proj -> S_before - S_unlearned`), and `U3` (`|div_euclid(S_unlearned^T U_int + 16384, 32768)| < TAU_ZERO = 4`; including `r_u3_hi ∈ [0, 256)` slack, `|S_unlearned^T u_hat| < 5` state units $= 6.58 \times 10^{-5}$ normalized `[DERIVED]`).

### 2.2 Measured Recall, Unlearning Fidelity, & `--release` ZK Benchmarks (`[EXECUTED]`)

Command: `bash research/afp_and_unified_wave_2026_11_21/formal_continual/build_and_verify.sh` (`exit 0`; `488`-tensor `Qwen/Qwen3.5-0.8B-Base` safetensors `mmap` + `248,320` BPE + `24L` MXFP4 preload in `1,360.04 ms`; 3-episode `192`-token `24L` extraction in `6,171.82 ms`):

| Memory Stage (`H_v = 16`, `248,320` Vocab) | Ep A (`Systems/Lean`, `6` facts) | Ep B (`Confidential`, `6` facts) | Ep C (`ZK Crypto`, `6` facts) | Counterfactual SNR vs `Train(A+C)` |
|---|---|---|---|---|
| **`S_0` (Frozen Pretrained Baseline)** | `0/6` (`0.0%`, `+0.00` logit) | `0/6` (`0.0%`, `\|\|y\|\| = 0`) | `1/6` (`16.7%`, `+0.00` logit) | — |
| **`S_3` (Continual WY `A -> B -> C`, `0` backprop)** | **`6/6` (`100.0%`, `+83.80`, `cos=0.9140`)** | **`6/6` (`100.0%`, `+76.78`, `\|\|y\|\|=0.810`)** | **`6/6` (`100.0%`, `+85.90`, `cos=0.9202`)** | — |
| **`S_unlearned` (Rank-`6` Erase of Ep B)** | **`6/6` (`100.0%`, `+83.80`, `cos=0.9140`)** | **`0/6` (`0.0%`, `-0.00` logit, `rel=7.43e-5`)** | **`6/6` (`100.0%`, `+85.90`, `cos=0.9202`)** | **`85.91 dB` (A) / `85.26 dB` (C)** |
| **`S_unlearned` (`H_v = 48` `Qwen3.8` Width, `1.05M` cells)** | **`6/6` (`100.0%`)** | **`0/6` (`0.0%`, `rel=4.59e-5 < 10^-4`)** | **`6/6` (`100.0%`)** | **`90.23 dB` (A) / `90.95 dB` (C)** |

| Succinct ZK Proof (`SuccinctExt4Pcs`, `zk=true, blowup=8, t_cols=208`, `103.49b` AHIV17 / `106.63b` BCIKS20 UD) | State Cells | Prove (`ms`) | Standalone Verify (`ms`) | Proof Size (`KiB`) |
|---|---:|---:|---:|---:|
| **`ZkContinualUpdateProof` (`Qwen3.5`, `H_v = 16`, `S_2 -> S_3`)** | `262,144` | `3,630.20` | `96.18` | `7,366.39` |
| **`ZkUnlearningCertificate` (`Qwen3.5`, `H_v = 16`, `r = 6`, MMR-tied)** | `262,144` | `2,517.54` | `65.26` | `4,746.59` |
| **`ZkContinualUpdateProof` (`Qwen3.8`, `H_v = 48 -> 64`, `S_2 -> S_3`)** | `1,048,576` | `14,912.26` | `163.93` | `14,633.92` |
| **`ZkUnlearningCertificate` (`Qwen3.8`, `H_v = 48 -> 64`, `r = 6`)** | `1,048,576` | `10,667.02` | `103.91` | `9,057.30` |

- **Adversarial soundness suite (`9/9` rejected in [continual_memory_unlearn.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/continual_memory_unlearn.rs)) `[EXECUTED]`:** (1a/1b) Verifier & prover no-op $S' = S$; (2a/2b) partial rank-1 erase (leaves `>= 4/6` confidential facts recoverable, rejected by `forget_request_root`) & `h_v = 1` downgrade; (3a/3b/3c) duplicate non-orthogonal $U$ column, non-zero inactive $U_{a \ge r}$, & Gram eval tamper; (4a/4b/4c) forged `S_unlearned_root`, PCS Merkle multiproof bit-flip, & forged WY `S_post_root`; (5a/5b-i/5b-ii) residual $\ge 2\tau_{\text{zero}}$ & exact $M_{\text{GS}}^{-1} \equiv -61{,}440 \pmod P$ wraparound (both one-sided PCS weld and two-sided `D1b` `[0, 131072)`); (6) decoy orthogonal $U \ne \text{span}(K)$ at registration (`#115.1`); (7) zeroed $L = 0 \ne \text{round}(K K^\top / 128)$ (`#115.2`); (8) swapped `episode_idx != mmr_proof.leaf_index` (`#115.4`).

---

## 3. Honest Privacy Scope, `[OPEN]` Seams, & Proposed `VERDICTS.md` Folds

- **Exact zero-knowledge & commitment-hiding scope (`#115.4` `[DERIVED]`):** `ProverVaultKey` salts `S` and `U` `SuccinctExt4Pcs` codewords (`0` dictionary attacks on `S_0 = 0` or `forget_request_root`, `0` cleartext matrix/key rows revealed). Because `state_pcs_seed` / `basis_pcs_seed` reuse the same committed RS codeword when chaining `S_t` (`post -> prev -> before`) or `U` (`registration -> unlearn`) across two publicly verified transcripts (`2 × 208 = 416` column queries, shared `f_prox` row) and `Gruen` / `D1b` emit random-point `Ext4` evaluations in clear, privacy is **salted commitment hiding + random-point evaluation disclosure**, not multi-transcript full-simulation HVZK. Upgrading to full multi-transcript HVZK (`[OPEN: re-randomized state bridge + GMaskExt4 sumcheck blinding]`) requires per-proof re-salted commitments welded via `GMaskExt4`-blinded equality sumchecks (`WhirExt4Pcs` reduces wire size `~10×`).
- **Absence ledger:** `0` `sorry` / `axiom` / `native_decide` in `VerifiableContinualLearning.lean` (checked via `build_and_verify.sh`).
- **Proposed Maintainer Folds (Not Edited Here):**
  1. **`minidregg/Theory.lean`:** Add `import Theory.VerifiableContinualLearning`.
  2. **`docs/VERDICTS.md` §9 (`zkML` / `Qwen3.8` Gated DeltaNet):** Record exact `CommRing` counterfactual rank-$r$ subspace unlearning (`(1 - U U^\top) S`) + `7.43e-5` (`H_v=16`) / `4.59e-5` (`H_v=48`) unlearned residual and `85–91 dB` counterfactual SNR on pretrained `Qwen3.5-0.8B` (`65–104 ms` standalone `Ext4` ZK verification).
