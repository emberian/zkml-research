# Emulation-Free Dual-Characteristic `248,320`-Vocab BPE Token-to-Byte Bridge

**Date:** 2026-11-21 · **Lane:** `dual-char-bpe-bridge` (`afp_and_unified_wave_2026_11_21`, audited by `bpe-neon-audit` + cross-audited & hardened by `afp-codex-claude-xaudit`)  
**Metered search counts:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org: 0` (`Qwen/Qwen3.5-0.8B-Base` `tokenizer.json` read offline from local HF cache).  
**Verification Script (`[EXECUTED]`):** [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/afp_and_unified_wave_2026_11_21/formal_bpe_bridge/build_and_verify.sh) (`exit 0`, Lean `v4.35.0` `14.57s` + `scripts/check-import-boundary.sh` + `--release` Rust `dual_char_bpe_bridge`).  
**Authored Artifacts (`[EXECUTED]`):** [DualCharTokenBridge.lean](file:///Users/ember/dev/minidregg/Theory/DualCharTokenBridge.lean) (`27` `#print axioms` pins), [bpe_bridge.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/src/bpe_bridge.rs), [dual_char_bpe_bridge.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/dual_char_bpe_bridge.rs).

---

## 0. Headline Verdicts (`[DERIVED]`, `[EXECUTED]`, `[REFUTED: token-ID filtering]`)

1. **Token-ID-level safety filtering is algebraically and empirically unsound (`[REFUTED: token-ID filtering as sufficient for byte-prefix absence]`) `[DERIVED, EXECUTED]`.**
   - In Lean 4.35.0 ([DualCharTokenBridge.lean](file:///Users/ember/dev/minidregg/Theory/DualCharTokenBridge.lean)), `tokenLevelGuard_bypassed_by_bpe_split` and `tokenFree_not_implies_byteAbsent` prove that BPE detokenization `detok V ts := ts.flatMap V` is a non-injective free-monoid homomorphism (`detok_append`, `detok_flatten`, `detok_not_injective`): distinct token sequences `["s", "k-proj"] ≠ ["sk", "-proj"]` avoid a banned `"sk-"` token ID **and** satisfy `AbsentW (V t) "sk-"` on every individual token, yet both detokenize to `"sk-proj"` (`OccursInW · "sk-"`).
   - Across the **real `248,320`-entry `Qwen/Qwen3.5-0.8B-Base` `tokenizer.json`** (`248,066` defined tokens; `[EXECUTED]`), **`0 / 248,066` single tokens contain `b"sk-"`, `b"Bearer "`, `b"ghp_"`, or `b"-----BEGIN "`** because Qwen's pre-tokenizer regex splits letter runs from punctuation/whitespace prior to BPE merging! Moreover, `"sk-proj-"` admits **`30` exact BPE factorizations** (`222,406` 2-token `*sk | -*` cross-boundary pairs), `"Bearer "` admits **`26` factorizations** (`105,380` `Bearer | ' '*` pairs), and `"-----BEGIN RSA PRIVATE KEY-----"` admits **`17,633,280` factorizations** `[EXECUTED]`. Every policy check (`Absent`, `RedactRule`, `LL(1)` AST) **must** operate on the welded raw byte stream `detok V ts` (composition corollary `detok_redactBytes_scrubs_any_split`).
2. **Variable-length BPE detokenization reduces to a `1`-multiply-per-token degree-2 rolling recurrence over ANY `CommRing R` (`0` character inner loops, `0` Keccak bit-blasting, `0` cross-field emulation) `[DERIVED, EXECUTED]`.**
   - Precomputing per-token ROM tuples `(len_t := |V(t)|, pow_t := B^{len_t}, val_t := evalBytesWith emb B (V t))` lets the online prover fold `(acc', totalLen') = (acc · pow_t + val_t, totalLen + len_t)` (`stepTokenRoll`) across variable-length tokens (`1..128` bytes in Qwen) in **one degree-2 step per token**. `rollTokensWith_eq_evalBytesWith_detok` and `rollTokens_eq_evalBytes_detok` kernel-prove exact equality with `(evalBytes B (detok V ts), |detok V ts|)` over **every** `CommRing R` (`ℤ`, `BabyBear Ext4`, `ZMod p_61`, and `Tower256 = GF(2^256)`), closing the `tokens → bytes` relation flagged in [PROOF-SYSTEM-SPACE.md:196](file:///Users/ember/dev/zkml-research/docs/PROOF-SYSTEM-SPACE.md#L196).
3. **Full `248,320`-vocab native Rust prover & standalone verifier (`bpe_bridge.rs`) welds `BabyBear Ext4` (`123.63`-bit) and `Tower256` (`GF(2^256)`, `370.88`-bit XOF squeeze `< 2^{-57.4}` from uniform) with `103.49`-bit per-opening (`>= 99.68`-bit 14-opening union-bounded) unconditional `[AHIV17]` $d/3$ UD soundness (`t_cols = 208, blowup = 8` in both PCSs) `[EXECUTED]`.**

---

## 1. Kernel-Verified Lean 4.35.0 Theorems (`[DERIVED]`, `[EXECUTED]`)

Verified in `14.57s` (`0` warnings, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`; `27` `#guard_msgs`-pinned `#print axioms` in `{propext, Classical.choice, Quot.sound}`):

| § | Theorem(s) in [DualCharTokenBridge.lean](file:///Users/ember/dev/minidregg/Theory/DualCharTokenBridge.lean) | Mathematical Obligation Established |
|---|---|---|
| **§1** | `detok_append`, `detok_flatten`, `tokenLevelGuard_bypassed_by_bpe_split`, `detok_not_injective`, `tokenFree_not_implies_byteAbsent`, `detok_redactBytes_scrubs_any_split` | Free-monoid `detok` homomorphism; constructive `by decide` split-token `"sk-proj"` bypass refuting token-ID + per-token `AbsentW` filters; composition corollary for `VerifiedAstTransducer.redactBytes` across equal-`detok` splits. |
| **§2** | `evalBytesWith_append`, `evalBytesWith_cons`, `evalBytesBase_eq_sum_pow`, `rollTokensWith_eq_evalBytesWith_detok`, `rollTokens_eq_evalBytes_detok`, `rollTokens_eq_of_detok_eq`, `rollTokens_map_ringHom` | Exact big-endian Horner power sum $\sum_{i=0}^{L-1} b_i B^{L-1-i}$, degree-2 per-token ROM concatenation identity over any `[CommRing R]`, split-token rolling invariance, and `R →+* S` ring-homomorphism naturality. |
| **§3** | `bytePolyWith_injective_of_length_eq`, `evalBytesWith_eq_imp_bytes_eq_or_root`, `card_colliding_bases_le`, `schwartz_zippel_collision_ratio_le`, `natCast_uint8_injective_of_ringChar`, `fanPaarByteToTower256_injective`, `tower256_card_colliding_bases_le` | Over any `[Field F]` with `Function.Injective emb`, equal-length `bs₁ ≠ bs₂` colliding at `B` force `B` to be a root of $\Delta \ne 0$ with $\deg \Delta \le L - 1$ ($\le (L - 1)/|S|$ error), instantiated both via `Nat.cast` (`char = 0 ∨ 256 ≤ char`) and concretely on `binaryTower 8 = GF(2^256)` via the 3-level Fan–Paar basis embedding `fanPaarByteToTower256`. |
| **§3 Teeth** | `leadingZero_length_omission_falsifier`, `char2_natCast_alias_falsifier`, `colliding_root_branch_inhabited`, `zmod257_colliding_root_inhabited` | (1) `[0, 65]` vs `[65]` share `evalBytesBase B` for **every** `(R, B)` (`totalLen` is load-bearing); (2) `Nat.cast` in `ZMod 2` aliases `[65]` vs `[67]` at **every** `B` (`GF(2^8)` injection is load-bearing); (3) `[1, 5]` vs `[2, 3]` achieves tight `#bad = 1 = L - 1` both on `ZMod 7` and in-class on `ZMod 257` (`256 ≤ ringChar (ZMod 257)`). |
| **§4** | `evalBytesInt_bounds`, `evalBytesInt_injective_of_length_eq`, `tokenByteWeldRow_holdsInt_iff_detok_eq`, `tokenByteWeldRow_holdsMod_iff_zmod_eq`, `dualChar_integer_fingerprint_bound`, `dualChar_integer_fingerprint_inhabited` | Unconditional injectivity of `(L, evalBytesBase 256)` over `ℤ`; exact equivalence of `Row.HoldsMod p` with `ZMod p` token rolling; reduction to `Theory.IntegerFingerprint.pow_card_undetected_le` with non-empty `undetected` witness (`17 ∣ 195840`). |

---

## 2. Real `Qwen3.5-0.8B-Base` `248,320`-Vocab BPE Census (`[SOURCE]`, `[EXECUTED]`)

Inspected from `/Users/ember/.cache/huggingface/hub/models--Qwen--Qwen3.5-0.8B-Base/snapshots/dc7cdfe2ee4154fa7e30f5b51ca41bfa40174e68/tokenizer.json` (`config.json` `text_config.vocab_size = 248,320`; `[SOURCE, EXECUTED]`):

- **Exact ID partition (`248,320` slots, padded to `2^{18} = 262,144`):** `0..248,043` = `248,044` ByteLevel BPE tokens (`0` non-ByteLevel Unicode scalars, `0` duplicate raw byte slices); `248,044..248,065` = `22` `added_tokens` (`14` `special = true`, `8` `special = false` incl. `<tool_call>`, `</tool_call>`); `248,066..248,319` = `254` unallocated model-padding IDs (rejected via `is_pad` in `D1bExt4TableProof`); `248,320` = dedicated `PAD_TOK_ID` (`is_pad = 1, len = 0, pow = 1, val = 0`, constrained to indices `>= num_tokens`). Note: `QwenBpeRom` maps all `248,066` defined tokens to their literal `content` bytes (`skip_special_tokens = false`); consumers that strip `special = true` tokens (`e.g. <|vision_pad|>`) during rendering must disallow or strip them identically before policy evaluation (`[DERIVED]`).
- **Token byte-length & partial-UTF-8 distribution (`n = 248,066`):** `min = 1 B` (`256` single-byte tokens = exact `0x00..0xFF` bijection, e.g. `id = 188` `'Ā'` $\mapsto$ `0x00`), `median = 6 B`, `mean = 7.43 B`, `p99 = 21 B`, `max = 128 B` (`id = 55036`). **`944` tokens (`816` multi-byte) are NOT valid standalone UTF-8**, confirming why the ROM and rolling hash must operate on raw `UInt8` bytes `[DERIVED, EXECUTED]`.

| Forbidden Byte Prefix | Single Qwen Tokens Containing Prefix | Exact Vocab Factorizations of Prefix | Cross-Boundary / Extended Split Surface |
|---|---:|---:|---|
| `b"sk-"` (`3 B`) | **`0 / 248,066`** | `2` (`["sk","-"]`, `["s","k","-"]`) | `222,406` 2-tok `*sk \| -*` pairs; `30` splits of `b"sk-proj-"` |
| `b"Bearer "` (`7 B`) | **`0 / 248,066`** | `26` (`2..7` tokens, e.g. `["Bear","er"," "]`) | `105,380` 2-tok `Bearer \| ' '*` pairs; `130` splits of `b"Bearer eyJ"` |
| `b"ghp_"` (`4 B`) | **`0 / 248,066`** | `3` (`3..4` tokens, e.g. `["gh","p","_"]`) | `3` splits of `b"ghp_1234"` (requires $\ge 3$ tokens) |
| `b"-----BEGIN "` (`11 B`) | **`0 / 248,066`** | `280` (`3..11` tokens) | **`17,633,280`** exact Qwen BPE splits of `b"-----BEGIN RSA PRIVATE KEY-----"` |

---

## 3. Native Dual-Characteristic Architecture & `--release` Benchmarks (`[EXECUTED]`)

1. **Phase-1 Pre-Challenge Commitments:** Commits `tok_col`, `len_col`, `cum_len_col`, `cum_len_next_col`, `bytes_bb_col` (`content_root_bb`) via `SuccinctExt4Pcs` (`t_cols = 208, blowup = 8`), plus `tower256_salted_root` (`248`-bit per-byte salts) and `tower256_bytes_pcs_root` (`Tower256Pcs`, `m >= 2`, `t_cols = 208, blowup = 8`, `beta_zk`-bound mask rows), **before** squeezing `(\beta_{ext4}, \beta_{256}, p_{61,0}, p_{61,1})` (`squeeze_t256` mixes 3 `Ext4` squeezes = `370.88` bits via `cSHAKE256` into full `2^{256}` `Tower256`).
2. **`BabyBear Ext4` + `Tower256` Verification:** Subdomain-lifted `D1bExt4TableProof` (`m_wit <= m_tab = 18`, `K_pad <= 8192 < p_BB`), packed-limb `Ext4` rolling AIR (`acc_next - val == acc * pow`), `[0, 512)` byte range + `EOF == 256`, `Tower256` Frobenius `GF(2^8)` canonicality ($\widetilde{B}(z^{2^{248}})^{256} = \widetilde{B}(z)$), and char-2 `{q(0), q(1), q(\infty)}` Horner + pointwise tail-zero sumchecks.

| Workload (`Qwen3.5` `248,320`-Vocab ROM, `t_cols = 208` Both Worlds, Parallel Load) | Scale | Prove / Setup (`ms`) | Standalone Verify (`ms`) | Wire Size (`KiB`) |
|---|---|---:|---:|---:|
| `QwenBpeRom::load_default` (`tokenizer.json` + `262,144`-leaf `cSHAKE256` Merkle) | `248,066 / 248,320` toks | `509.7–2,136.8` | — (`32 B` root `29a803d6..`) | `0.03` |
| **`DualCharTokenBridge` (`K = 64` Qwen tokens)** | `319 B` UTF-8 (`m_tok=7, m_byte=9`) | `5,433.5–6,953.4` | `255.8–897.3` | `1,703.2` |
| **`DualCharTokenBridge` (`K = 256` Qwen tokens)** | `1,284 B` UTF-8 (`m_tok=9, m_byte=11`) | `10,272.2–12,520.3` | `797.9–1,463.8` | `2,434.8` |
| **`DualCharTokenBridge` (`K = 512` Qwen tokens)** | `2,586 B` UTF-8 (`m_tok=10, m_byte=12`) | `20,800.0–23,762.9` | `269.5–1,014.7` | `3,746.2` |

- **Smuggling & Soundness Suite (`100%` rejected in [dual_char_bpe_bridge.rs](file:///Users/ember/dev/zkml-research/native/qwen35audit/tests/dual_char_bpe_bridge.rs)) `[EXECUTED]`:** `4` tokenizations (`1` canonical containing banned IDs + `3` split-token bypasses, `72..77` tokens -> identical `185 B` stream) all weld to identical bytes, trigger `Absent("sk-...")` rejection when unredacted, and pass after deterministic scrubbing; rejects 1-token swaps, forged ROM tuples, leading-`\0` (`id = 188`) length aliases, forged `Ext4`/`Tower256` accumulators, unallocated ID `248,100`, active-stream `PAD_TOK_ID`, tampered `num_tokens` PAD boundary, `s_mask` shifts, and salted-root tampering.

---

## 4. Exact Security & Privacy Calibration + `[OPEN]` Seams

- **Pre-Challenge Binding in `Some(raw_bytes)` vs `None` (`[DERIVED]`):**
  1. **Salted Policy-Enclave Weld (`prove_dual_char_bpe_bridge_salted` + `verify_dual_char_bpe_bridge_with_salts`):** Verifies `(raw_bytes, salts)` against the pre-challenge `stmt.tower256_salted_root` commitment **before** `(beta_ext4, beta_256)` are squeezed, unconditionally binding `tok_pcs_root`, `bytes_bb_pcs_root`, `tower256_salted_root`, and `tower256_bytes_pcs_root` to the exact same `(byte_len, raw_bytes)` (`>= 99.68`-bit union-bounded UD across all 14 PCS openings). Calling `verify_dual_char_bpe_bridge` with `opt_salts = None` is sound only when `expected_bs` is fixed externally prior to challenge derivation.
  2. **Zero-Cleartext External Audit (`opt_expected_bytes = None`):** Proves `detok(tok_pcs_root) == bytes_bb_pcs_root` and independently proves `tower256_bytes_pcs_root` is a valid `L`-byte `GF(2^8)` stream with accumulator `final_acc_t256`. Linking `tok_pcs_root` directly to `final_acc_t256` without `raw_bytes` (`[OPEN: zero-cleartext cross-characteristic token-ROM fold]`), proving `fp_p61_{0,1}` algebraically in `None` mode, and aligning `commit_salted_bytes_t256` (`byte_pad_len >= 512`) with Lean `saltedContentCommit` / `u1_audit` (`>= 2048` single-batch PCS commitment) remain explicit integration seams.
- **Transcript Privacy Scope (`[DERIVED]`, `[OPEN]`):** Single-batch PCS commitments hide unopened columns (`t_cols = 208` Shamir tail + `beta_zk` mask rows), whereas sumcheck round polynomials (`q0, q1` in `Tower256` direct-IP determine up to 64 bytes) and clear accumulators (`final_acc_*`, `fp_p61_*`) are **not** HVZK-masked; compose with `GMask` (`SumcheckHvzkMask.lean`) / trace masking when byte-stream zero-knowledge is required (`[OPEN]`).
- **Proposed Maintainer Folds (Not Edited Here):** Add `import Theory.DualCharTokenBridge` to `minidregg/Theory.lean`, and record the `1`-multiply-per-token `DualCharTokenBridge` + `248,320`-vocab split-token smuggling refutation in `docs/PROOF-SYSTEM-SPACE.md` §U3 and `docs/VERDICTS.md` §9.
