# Wave 8: Cross-Tree Gate `G9`, `SpecPrefill` Carry Weld, and `PayableComputeReceipt`

**Date:** 2026-11-22 · **Lane:** `w8-unified-turn-weld` (`G9` + `wave7` §4 `L2/L7` + Flagship Vertical #2)
**Owned Artifacts:** [`native/qwen35audit/src/unified_turn_weld.rs`](../native/qwen35audit/src/unified_turn_weld.rs) · [`native/qwen35audit/tests/unified_turn_weld_e2e.rs`](../native/qwen35audit/tests/unified_turn_weld_e2e.rs)
**Companion Citations:** `/Users/ember/dev/minidregg/Kernel/ProviderExecutionLease.lean:413-415` · `/Users/ember/dev/breadstuffs/dice/src/source.rs:727-840` · [`notes/wave7-claude-codex-adversarial-audit.md`](wave7-claude-codex-adversarial-audit.md) §4 `L2, L7` · [`notes/whir-gmask-succinct-proof-compression.md`](whir-gmask-succinct-proof-compression.md) · [`notes/speculative-prefill-and-looped-moe-proving.md`](speculative-prefill-and-looped-moe-proving.md) · [`notes/dual-characteristic-bpe-token-byte-bridge.md`](dual-characteristic-bpe-token-byte-bridge.md)
**Claim tags (`AGENTS.md`):** `[EXECUTED]` compiled & run in `--release` (`RUSTFLAGS="-D warnings"`) · `[DERIVED]` exact algebra / probability · `[SOURCE]` inspected at `path:line` · `[REFUTED: scope]` bounded falsification · `[OPEN]` unverified boundary.
**Metered Queries:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org: 0`.

---

## 1. Executive Summary

This lane closes Cross-Tree Gate `G9` and `wave7` §4 `L2/L7`, and ships Flagship Vertical #2 (`PayableComputeReceipt`) over real 24-layer `Qwen/Qwen3.5-0.8B-Base` weights (`safetensors`), the `248,320`-token `QwenBpeRom`, and League of Entropy `drand` `quicknet` (`BLS12-381` RFC 9380) `[EXECUTED, DERIVED]`:

1. **Unified Salted Byte PCS & `TVD = 0` Cross-Commitment Equality Weld (`G9`):** Unifies `bpe_bridge` (`pad >= 512`) and `whir_ext4` `U1 + Absent("sk-...")` (`pad >= 2048`) under `SaltedByteWhirCommitment` (`CANONICAL_BYTE_MIN_PAD = 2048`, `content_root = cSHAKE256("QW35-CONTENT-SCHEME-ROOT-V1", word_len_le8 || whir_root)`). `MaskedByteEqualityProof` proves prefix equality across heterogeneous padding (`512` vs `2048`) in **`88.32 KiB` (`90,436 B`)** with **zero unmasked evaluations (`TVD = 0`)**, plus `LegacyBpeToCanonicalWhirWeld` bridging `DualCharBridgeProof` (`SuccinctExt4Pcs` + `Tower256`) to canonical `WhirExt4Pcs` `[DERIVED, EXECUTED]`.
2. **Autoregressive `SpecPrefill` Token-Carry & `R = 3` Looped Residual-Carry (`wave7` §4 `L2`):** `SpecPrefillCarryWitness` proves `tok_in[0..P] == prompt` and `tok_in[t + 1] == y_hat_tok[t]` (`0` extra wire bytes via shifted `DenseSmall` multilinear claim), `IsGreedyDom` smallest-index tie-break via first-difference `strict_lt[t, v] = 1[v < v*]` + `u16` `D1b` gap range, and `R = 3` $\rho$-folded `MXFP4` residual transitions $2048(X_{r+1} - X_r) + \text{rem}_r - Y_r = 1024$ ($\text{rem}_r \in [0, 2048)$) in **`8.30 ms` verify** `[DERIVED, EXECUTED]`.
3. **Post-Countersignature `drand` `quicknet` Audit & `PayableComputeReceipt` (`G9` + Vertical #2):** Implements pure-Rust zero-dependency `BLS12-381` optimal Ate pairing + RFC 9380 `SSWU` + 11-isogeny (`bls-unchained-g1-rfc9380`, **`2.15 ms`** on live `drand` round `1_000_000`) `[SOURCE: breadstuffs/dice/src/source.rs:760-840]`, `WOTS+` (`cSHAKE256`, `w = 16`) Phase-1 commit (`trace_merkle_root, byte_root, bpe_weld_root, carry_weld_root`) & Phase-2 escrow countersignature (`round_commit < target_beacon_round <= expiry_round`), and a 6-matrix single-cascade `WhirExt4Pcs + GMaskExt4` receipt of **`614.53 KiB` (`629,283 B < 650 KiB`)** verifying standalone in **`21.53 ms` (`< 25 ms`)** with conserved settlement `paid + refunded == prepaid_budget` `[SOURCE: minidregg/Kernel/ProviderExecutionLease.lean:413-415, EXECUTED]`.

---

## 2. Algebraic Constructions & Soundness Pricing (`[DERIVED]`)

- **`TVD = 0` Cross-Padding Byte Equality Bijection (`unified_turn_weld.rs:2485-2795`):** Commit $(B_i, R_i, G_{\text{eof},i})$ for $i \in \{1, 2\}$ ($m_i = \log_2 \text{pad}_i$, $m_{\min} = \min(m_1, m_2)$) where $R_i \in \text{Ext4}$ is stored as 4 BabyBear cells. At challenge $z \in \text{Ext4}^{m_{\min}}$ and $\alpha \in \text{Ext4}^\times$, prover sends $(\Delta_R, \mu_1) = (R_1 - R_2, \alpha \widetilde{B}_1(z, 0^{m_1-m_{\min}}) + R_1)$ and opens $\alpha \widetilde{B}_1(z, 0) + R_1 = \mu_1$ and $\alpha \widetilde{B}_2(z, 0) + R_2 = \mu_1 - \Delta_R$ inside one shared `WhirExt4Pcs` batch alongside `GMaskExt4` tail-EOF `hvzk_terminal_weld` claims ($t \in [\text{word\_len}, \text{pad}_i) \implies B_i[t] = 256$). Over $\text{Ext4}^2$, $(R_1, R_2) \mapsto (R_1 - R_2, \alpha v + R_1)$ has determinant $-1 \neq 0$, so $(\Delta_R, \mu_1)$ is uniform and independent of $(B_1, B_2)$ (`TVD = 0`); if $B_1[0..\text{word\_len}) \neq B_2[0..\text{word\_len})$, Schwartz–Zippel + $\alpha$-linearity bounds soundness error by $\frac{m_{\min}}{|\text{Ext4}|} + \frac{1}{|\text{Ext4}| - 1} < 2^{-119.8}$ `[DERIVED]`.
- **Wrap-Free Integer WY Contraction (`wave7` §4 `L2/L7`, `unified_turn_weld.rs:6075-6115`):** Consolidated `virt_wy8192` ($2^{21}$ witness over $[0, 8192)$ `D1b`) proves $UW + 4096, RHS + 4096, L + 4096 \in [0, 8192)$ ($UW, RHS, L \in [-4096, 4095]$), $\text{rem}_{\text{wy}}, \text{rem}_{\text{wy}} + 4096 \in [0, 8192)$ ($\implies \text{rem}_{\text{wy}} \in [0, 4096)$), $b, b + 7936 \in [0, 8192)$ ($\implies b \in [0, 256)$), and $q, q + 8184 \in [0, 8192)$ ($\implies q \in [0, 8)$). Since $\big|\sum_{j<i} L_{ij} UW_{jk} - (4096(RHS_{ik} - UW_{ik}) + 2048 - \text{rem}_{ik})\big| \le 63 \cdot 4096^2 + 8191 \cdot 4096 + 4096 = 1,090,519,040 < P = 2,013,265,921$, modular equality over $\mathbb{F}_P$ implies exact integer Euclidean division over $\mathbb{Z}$ `[DERIVED]`.
- **Exact-Dyadic `CompactWhirMxfp4` & L1-Cached ROM Fold (`unified_turn_weld.rs:4652-4720, 5085-5255`):** Decomposing `Qwen3.5-0.8B` `gate_proj` ($3584 = 2048 + 1024 + 512$) into subtables $[21, 20, 19, 16, 15, 14]$ fits $3,784,704 \le 4,194,304$ cells (`rd = 128` vs `256`, saving `67.8 KiB`) and hosts the $j < 1024$ looped residual `MXFP4` opening with `0` extra matrices (`-82.5 KiB`). Rewriting `verify_d1b_qwen_rom_fast` via $8192$-slot `u64` MADD buckets ($8192 \cdot 248320 \cdot (P - 1) = 4.09 \times 10^{18} < 2^{64}$) eliminates all per-token `Ext4` multiplications and `% P` reductions `[DERIVED, EXECUTED]`.
- **Provable PCS Soundness:** All 6 matrices operate inside `[BCIKS20]` Thm 1.4/1.5 Unique Decoding (`blow = 8`, $\theta_{\text{UD}} = 7/16$, $t_{\text{queries}} = 140$, $u_{\text{ood}} = 2$, $N_0 \le 2^{18}$), achieving `101.6` bits UD (`100.63` bits at $\eta = 2^{-5}$) `[DERIVED, SOURCE: notes/whir-gmask-succinct-proof-compression.md:47-50]`.

---

## 3. Executed `--release` Benchmarks & Adversarial Falsifier Ledger (`[EXECUTED]`)

Command (`0` warnings under `RUSTFLAGS="-D warnings"`, `3/3` tests `ok`, exit `0`):
```bash
CARGO_TARGET_DIR=/Users/ember/dev/zkml-research/native/target-w8-turn RUSTFLAGS="-D warnings" \
  cargo test --manifest-path /Users/ember/dev/zkml-research/native/Cargo.toml \
  --release -p qwen35audit --test unified_turn_weld_e2e -- --nocapture
```

| Component / Receipt (`unified_turn_weld_e2e.rs`) | Wire Size | Prover Time | Verifier Time | Outcome |
|---|---:|---:|---:|---|
| Live `drand` `quicknet` round `1_000_000` (`BLS12-381` RFC 9380) | `144 B` | — | **`2.15 ms`** | `ok` `[EXECUTED]` |
| `MaskedByteEqualityProof` (`pad = 512` <-> `pad = 2048`, `TVD = 0`) | **`88.32 KiB`** (`90,436 B`) | `4.39 ms` | `38.33 ms`* | `ok` `[EXECUTED]` |
| `SpecPrefillCarryWeldProof` (`P = 1, T = 128, R = 3` loop) | standalone WHIR | `3,541.50 ms` | **`8.30 ms`** | `ok` `[EXECUTED]` |
| **`PayableComputeReceipt` (`2x64t` 24L `Qwen3.5-0.8B` + `248,320` ROM + `drand` `#1,000,000` -> `layer=10, chunk=1`)** | **`614.53 KiB`** (`629,283 B < 650 KiB`) | `2,889.4 ms` P1 + `2,538.9 ms` P4 | **`21.53 ms`** (`< 25 ms` median) | **`paid = 130,000`, `refunded = 131,000`** `[EXECUTED]` |

*\*Ran concurrently with 24-layer `rayon` safetensors quantization under default multi-threaded `cargo test`.*

### Bounded Refutations (`[REFUTED: scope]`, all verified in `unified_turn_weld_e2e.rs`)
- `[REFUTED: pre-countersignature or off-schedule drand grinding]` Stale `beacon.round <= round_commit`, off-schedule `round_commit + 2 != target_beacon_round`, mutated `BLS12-381` `G1` signature/randomness, wrong `G2` committee PK, tampered `EscrowCountersignature`, post-countersignature `byte_root` grinding, and wrong `(audited_layer, audited_chunk)` substitution all fail `verify_payable_compute_receipt_and_settle` `[EXECUTED]`.
- `[REFUTED: cross-padding byte mismatch & split-token sk-proj smuggling]` 1-byte/79-byte payload substitution across `pad = 512` vs `2048`, tampered `mu_1`, split-token `"s" + "k" + "-proj-998877"` welded to clean canonical commitment, unredacted `"sk-live-..."` output (sink state `4`), and tampered `final_acc_ext4` all fail `[EXECUTED]`.
- `[REFUTED: autoregressive token splice, looped residual splice, & tie-break forgery]` Spliced `tok_in[42] != y_hat_tok[41]`, spliced `X_2 != stepPost(X_1, Y_1)`, non-greedy tie-break at `v < v*`, tampered `b_out_eval`, premature timeout refund (`round <= expiry_round`), and `claimed_units > max_units` all fail `[EXECUTED]`.

---

## 4. Open Scope Boundaries (`[OPEN]`) & Proposed Maintainer Fold

- **Scope Boundaries (`[OPEN]`):** (1) Audit unpredictability assumes `drand` `quicknet` threshold `BLS12-381` unforgeability prior to `target_beacon_round`. (2) `MaskedByteEqualityProof` achieves full transcript `TVD = 0`; the composite `PayableComputeReceipt` masks all sumchecks and Stage-0 WHIR columns via `GMaskExt4` + WHIR salts while serializing random-point `Ext4` evaluations and `D1b`/`MXFP4` subproofs per `#117.A.4`. (3) Multi-chunk `U1` auditing welds per-chunk 24-layer boundary chains (`50` WHIR roots in `trace_merkle_root`); cross-chunk recurrent GDN state carry $S_{\text{chunk}, c} \to S_{\text{chunk}, c+1}$ beyond $S_{\text{init}} = 0$ remains `[OPEN]`.
- **Proposed `docs/VERDICTS.md` / `notes/README.md` Fold (not edited here per `AGENTS.md`):** Record `G9` + `wave7` `L2/L7` closed and Flagship Vertical #2 `PayableComputeReceipt` shipped in `native/qwen35audit/src/unified_turn_weld.rs` (`614.53 KiB`, `21.53 ms` verify, live `drand` `quicknet` `#1,000,000` + `Qwen3.5-0.8B` + `248,320` BPE ROM).
