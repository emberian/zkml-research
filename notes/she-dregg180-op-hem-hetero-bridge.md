# Wearable SHE Organ #1 — Streamed `< 16 KiB` `Dregg-180` `OP_FOLD` / `OP_HEM` `GoldilocksExt4` Verifier VM & Heterogeneous Leaf Bridge

**Date:** 2026-11-22 · **Metered queries:** Scry `0` · Kagi `0` · `eprint.iacr.org` `0`

## 1. Scope & Problem Closed

Wearable SHE child proofs span incompatible algebraic characteristics (`BabyBear Ext4` `X^4 - 11` for audited `Qwen` `WhirExt4Pcs`, characteristic-2 `Tower256` `GF(2^{256})` for zero-leakage `Absent("sk-...")` DFA zerocheck, and `cSHAKE256` `WOTS+` `Simplex` `n - f` quorum `FinCert`), whereas the zero-SRAM-macro `Dregg-180` (`QSAG-NI-180`, `gf180mcuD` `SLOT_0P5X0P5`) silicon verifier executes streamed `OP_FOLD` (`0x30`) / `OP_HEM` (`0x31`) bytecode over `Goldilocks` (`p = 2^{64} - 2^{32} + 1`) and `GoldilocksExt4` (`v^4 = 7`, limb basis `[1, v^2, v, v^3]`) `[SOURCE: /Users/ember/dev/qsag/hardware/gf180mcu/README.md:390-399, /Users/ember/dev/qsag/hardware/gf180mcu/model/qsag_prims.py:55-96]`. This lane closes that proof-field chasm formally in Lean `v4.35.0` and natively in Rust.

## 2. Lean `v4.35.0` Mechanization (`Selvage/GoldilocksDregg180Bridge.lean`)

Verified via `bash research/wave9_wearable_she_2026_11_21/formal_dregg180/build_and_verify.sh --lean-only` (`946` lines `< 950`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0` warnings under `-DwarningAsError=true`, `17` `#guard_msgs`-pinned `#print axioms`, `scripts/check-import-boundary.sh` PASS, `35.41s`) `[EXECUTED]`:

- **Field & Hardware Register Isomorphism:** `goldilocksModulus_prime` proves `Nat.Prime (2^64 - 2^32 + 1)` via `lucas_primality` at primitive root `7` over `p - 1 = 2^{32} \cdot 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537` using 64-step `powFuel` + kernel `decide`; `goldilocksExt4Poly_irreducible` and `goldilocksExt4_finrank` establish `Irreducible (X^4 - 7)` and `finrank = 4`; `GlExt4.toExt4_mul` and `GlExt4.toExt4_injective` prove ring isomorphism with `Dregg-180`'s `[1, v^2, v, v^3]` hardware limb layout (`dregg180_ext4_kat_vector`: `[1,2,3,4] * [5,6,7,8] = [453,261,302,60]`) `[DERIVED]` `[EXECUTED]`.
- **Streamed `< 16 KiB` VM Invariants:** `Dregg180VmState` models `OP_ABSORB_ROOT`, `OP_SUMCHECK_ROUND`, `OP_WHIR_FOLD`, `OP_CANOPY_PATH`, and `OP_ASSERT_FINAL` with `dregg180StaticRamBytes_le_16KiB` (`0` axioms), monotone sponge sequence `dregg180RunFrom_spongeSeq_monotone`, sticky fault latch `dregg180Step_stickyFail_sticky`, and acceptance soundness `dregg180Verify_requires_all_leaves_absorbed` `[DERIVED]`.
- **Multi-Leaf `ComposeErrorBoundStrict` Capstone:** `heteroMultiLeaf_composeErrorBoundStrict` and `wearableShe_dregg180_end_to_end_soundness` instantiate `Selvage.composeErrorBoundStrict_closes` `[SOURCE: /Users/ember/dev/minidregg/Selvage/HeteroCompositionErrorBound.lean:105-135]` over `BabyBear Ext4` + `Tower256` `Absent` + `Simplex` `FinCert`, proving $\mu(\mathsf{KsFailure}_{\text{comp}}) \le \varepsilon_{\text{hem}} + (\varepsilon_{\text{qwen}} + \varepsilon_{\text{absent}} + \varepsilon_{\text{fincert}})$, witnessed by `wearableShe_honest_bundle_accepted` `[DERIVED]` `[EXECUTED]`.
- **`#tooth` Falsifiers:** `widened_child_leaf_refuses_hem_embedding_tooth` (`IsEmpty (VerifierEmbedding ...)` when $n \le 3f$), `unabsorbed_child_root_rejected_tooth` (`< 3` `OP_ABSORB_ROOT`s rejected for all streams), `unabsorbed_root_breaks_binding_tooth`, `transcript_replay_splice_rejected_tooth`, `forged_merkle_index_rejected_tooth`, and `sk_dash_payload_refuted_tooth` `[REFUTED: widened child relation, unabsorbed child root, post-final/pdig replay, H_BIND_IDX bypass, "sk-" payload]`.

## 3. Zero-Heap `< 16 KiB` Rust Silicon Verifier & Heterogeneous Bridge

Verified via `bash research/wave9_wearable_she_2026_11_21/formal_dregg180/build_and_verify.sh` (`#![deny(warnings)]`, `RUSTFLAGS="-D warnings"`, `--release`, `2/2` test suites PASS) in `native/qwen35audit/src/dregg180_hem_bridge.rs` and `native/qwen35audit/tests/dregg180_op_hem_vm.rs` `[EXECUTED]`:

| Metric | Measured Value | Provenance |
| :--- | :--- | :--- |
| `sizeof(Dregg180StreamVm)` static RAM | **`1,056 B` (`1.03 KiB <= 16.00 KiB`, `6.4%`)** | `[EXECUTED]` `dregg180_op_hem_vm.rs` |
| Heap allocations during VM verification | **`0` allocs** (full-slice, `48 B` SPI burst, `1 B` stream) | `[EXECUTED]` `CountingAllocator` |
| Heterogeneous 3-leaf `--release` prove | **`17.06 ms`** (`BabyBear Ext4` + `Tower256` + `Simplex` `WOTS+`) | `[EXECUTED]` `--release` |
| `GoldilocksExt4` `Hem` stream compile | **`9.35 ms`** (`6` SC rounds, `10`-bit PoW, `6` dual Canopy queries) | `[EXECUTED]` `--release` |
| `Dregg180StreamVm` `--release` verify | **`0.620 ms`** (identical verdict on `full`, `48 B`, and `1 B` feeds) | `[EXECUTED]` `--release` |
| `OP_HEM` (`0x31`) wire stream size | **`13,024 B` (`12.72 KiB`)**, `293` records (`420` imm + `914` proof words) | `[EXECUTED]` `--release` |
| `Dregg-180` silicon cycles (`SLOT_0P5X0P5`) | **`7,214,502` cycles** (`288.58 ms` @ `25 MHz`; `557.97 ms` @ `12.93 MHz` TT) | `[DERIVED]` + `[EXECUTED]` |
| Silicon primitive breakdown | `204` `Poseidon2-12`, `49` `Keccak`, `42` `Ext4` mul, `73` `Ext4` add/sub, `714` `GF128` | `[EXECUTED]` `--release` |

### Adversarial Falsifiers Rejected (`11/11` in `tests/dregg180_op_hem_vm.rs`)

1. `[REFUTED: 0-assertion LOAD R_CH stream]` (`Dregg-180` D6 #2 regression).
2. `[REFUTED: LOAD R_CH in pin_mode=true]` (`flags = 0x08`).
3. `[REFUTED: non-canonical Goldilocks proof word == p]` (`non_canonical_word = true`).
4. `[REFUTED: swapped DeferredLeafClaim immediate]` (`program_digest_mismatch = true` under `GF(2^128)` `K_MAC`).
5. `[REFUTED: 1-bit flip in streamed proof body]`.
6. `[REFUTED: H_BIND_IDX Merkle query index substitution]`.
7. `[REFUTED: tampered cSHAKE256("QSAG.PCS.CANOPY/v2") Canopy sibling]`.
8. `[REFUTED: "sk-live-..." secret leak in assistant bytes & forged sink state >= 4]`.
9. `[REFUTED: sub-quorum (2 < n - f = 3) & duplicate validator index in Simplex FinCert]`.
10. `[REFUTED: cross-leaf content_root splice between Qwen turn and Absent certificate]`.
11. `[REFUTED: truncated wire stream & trailing-word overrun]`.

## 4. Open Boundary & Maintainer Fold Proposal

- `[OPEN]` `compile_deferred_leaves_to_dregg180_hem_stream` commits verified child `DeferredLeafClaim` digests into the `GoldilocksExt4` `Hem` polynomial after host/edge leaf verification (`bridge_wearable_she_bundle_to_dregg180_stream` / `bridge_payable_compute_receipt_to_dregg180_stream`); full in-circuit non-native `BabyBear`/`Tower256`/`WOTS+` verification inside `GoldilocksExt4` R1CS/AIR is not mechanized and relies on `K_MAC` / `H_ZK_PIN` immediate program-digest pinning (`expected_pdig`) of the absorbed `DeferredLeafClaim`s.
- **Proposed maintainer fold (not edited in this run):** add `import Selvage.GoldilocksDregg180Bridge` to `/Users/ember/dev/minidregg/Selvage.lean` and record Organ #1 (`1,056 B` zero-heap `Dregg180StreamVm`, `13,024 B` `OP_HEM` stream, `0.620 ms` host / `7.21M` silicon cycles) in `docs/VERDICTS.md`.
