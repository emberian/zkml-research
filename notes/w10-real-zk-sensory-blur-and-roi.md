# Wave 10 Tier 1A: Real Succinct `BabyBearExt4` Sensor Blur & Ambient ZK + PQ Enclave Signing

- **Status:** `[EXECUTED]` Lean `v4.35.0` + Rust `--release` verified after `gpt-6.2-astra` audit (`2026-11-22`).
- **Artifacts:** `minidregg/Assurance/SensoryRoiZeroKnowledge.lean` (`940` lines), `minidregg/prover/src/sensory_roi_cert.rs`, `minidregg/prover/tests/sensory_roi_wearable.rs`, `minidregg/prover/testdata/sensory_roi_conformance.json`, `research/wave10_reality_hardening_2026_11_22/formal_sensory/build_and_verify.sh`.

## 1. Refuted v1 Theater (`[REFUTED: v1 BlurTileEntry cleartext tile_sum]`)
- `[SOURCE]` v1 `sensory_roi_cert.rs` (`L806-814`) shipped cleartext `BlurTileEntry::tile_sum: u32` next to decorative `masked_terms: Vec<u64>`, hashed `sumCommit` in plaintext at capture time, and authenticated headers with a symmetric `hw_key: &[u8]` MAC (letting any verifier forge headers).
- `[DERIVED]` Lean `#tooth` `tooth_cleartext_tile_sum_leaks_spatial_luminance` proves two frames with identical ambient total (`25600`: `[25600, 0]` vs `[12800, 12800]`) have advantage-`1` distinguishable v1 transcripts under ANY `masked_terms`, whereas v2's `BabyBearExt4` `GMaskExt4` sumcheck view achieves exact `TVD = 0` (`GapAtMost tapes 0 den`).
- **Deleted:** `sumCommit`/`sumSalt`, symmetric `hw_key`, cleartext `BlurTileEntry::tile_sum`, and fake `masked_terms`.

## 2. v2 Real Cryptographic Protocol (`[SOURCE]` / `[DERIVED]`)
- **Raw-Only Asymmetric Enclave Sealing:** Enclave commits ONLY to salted per-tile `tile_merkle_root` (for `O(|U| log N)` zero-bystander ROI opens) + salted HVZK coset-RS matrix PCS `rt_raw` (`rate = 1/4`, `C >= 1024`, degree-`[C..2C)` random row tails) and signs `SensorFrameHeader` with asymmetric PQ `WotsCshake256` (`crate::pq_biscuit`, single-key or stateful XMSS tree). Verifiers hold ONLY `EnclavePublicKey`.
- **`BlurDownscaleZkProof`:** Untrusted-worker ZK proof over `rt_raw` via `BabyBearExt4` (`u^4 = 11`, `|F^4| ≈ 2^{123.63}`) mixed-degree `[5, 3, ...]` HVZK masked sumcheck (`t_0(1-t_0)` terminal blinding + `log2(tile_len)` Boolean bit columns `b_k (1 - b_k) = 0`) + `Z_s`/`B_prox` + independent-challenge `[BCIKS20]` Thm 1.7 affine proximity RLC + lockstep BaseFold/FRI proving `sum_u Raw[t, u] = tile_len * B[t] + rem[t]` with `B[t] ∈ [0, 256)` and `rem[t] < tile_len` (no BabyBear wrap: `<= 16,777,215 < P = 2,013,265,921`).
- **`AmbientEnvelopeZkProof`:** Degree-2 HVZK sumcheck + BaseFold/FRI over `rt_raw` proving `sum_{t ∈ S, u} Raw[t, u] = claimed_total <= threshold` with ZERO per-tile sums on the wire.
- **Query Budget (`[DERIVED]`):** At `rate = 1/4`, `q = 148`, `16`-bit PoW: bare single-trial UDR `(5/8)^{148} ≈ 2^{-100.35} < 2^{-100}` (WITHOUT relying on PoW), and `(21/32)^{148} / 2^{16} ≈ 2^{-105.94} < 2^{-100}` under `η = 1/32` slack + 16-bit grinding work.

## 3. Lean `v4.35.0` Formalization (`[EXECUTED]`)
- `Assurance/SensoryRoiZeroKnowledge.lean`: `940` lines (`< 950`), `0 sorry`, `0` custom `axiom`, `0 native_decide`, `16` `#guard_msgs`-pinned `#print axioms` (standard Lean/Mathlib axioms only), `scripts/check-import-boundary.sh` PASS, kernel-verified with `0` warnings in `11.54s`, emits `prover/testdata/sensory_roi_conformance.json` (`14,412` B).
- **Verified theorems:** `verifyFrameHeader_bodyBounded`, `verifyFrameHeader_wots_complete`, `headerSigningPayload_inj`, `header_unforgeable_without_sk` (`treeDepth = 0`), `header_unforgeable_xmss_or_collision` (`treeDepth > 0`), `tooth_cross_timestamp_replay_refused`, `merklePath_sound_or_collision`, `unopened_bystander_tiles_hidden` (+ fresh-salt poles), `roi_reveal_sound_or_collision`, `booleanBitsNat_lt`, `blur_div_unique_of_boolean_rem`, `tooth_unconstrained_rem_forges_blur_mean`, `ext4_hvzk_sumcheck_gap_zero`, `ud100_query_arithmetic_rate4_q148_pow16`, `tooth_q48_rate4_not_ud100`, `tooth_cleartext_tile_sum_leaks_spatial_luminance`.

## 4. Rust `--release` Execution & `1280x720` Benchmarks (`[EXECUTED]`)
- Command: `research/wave10_reality_hardening_2026_11_22/formal_sensory/build_and_verify.sh --rebuild-lean` (`#![deny(warnings)]`, `sha3`-only): `2/2` lib unit tests + `14/14` wearable integration/conformance/adversarial tests passed in `1.34s`.

| `1280x720` (`3,600` `16x16` tiles, `N_raw = 2^20`, `rate = 1/4`, `q = 148`, `16b` PoW) | Prove / Seal | Verify | Wire Size |
|---|---:|---:|---:|
| Enclave Seal (`tile_merkle_root` + `rt_raw` + XMSS-WOTS) | `62.51 ms` | — | — |
| Authorized ROI Reveal (`64` frustum tiles) | — | `0.836 ms` | `O(\|U\| log N)` |
| `BlurDownscaleZkProof` (`3,536` non-ROI tiles, Boolean `8`-bit `rem`) | `184.89 ms` | `6.89 ms` | `564.0 KiB` |
| `AmbientEnvelopeZkProof` (`3,536` non-ROI tiles, `0` per-tile sums) | `100.86 ms` | `6.63 ms` | `544.5 KiB` |

- `adv10` wire audit: Frame A (`[25600, 0]`, `168,721 B`) vs Frame B (`[12800, 12800]`, `168,337 B`) contain zero bystander strings/salts and zero cleartext per-tile sums.

## 5. `gpt-6.2-astra` Adversarial Audit & Fixes (`[EXECUTED]`)
Read-only `codex exec` review (`147,835` tokens) verified all blur/ambient/BaseFold/FRI/prefix-MLE/multiproof/transcript equations and surfaced 8 prioritized findings — **all 8 fixed and regression-tested**:
1. **High — Repeated `rt_raw` openings exhaust `[C..2C)` Vandermonde blinding:** Added shared `Arc<AtomicUsize>` column-opening budget on `RawPcsCommitment` enforcing `used + 2q <= shape.c` across blur/ambient proofs and `.clone()` handles (`RawCommitmentOpeningBudgetExhausted`, `adv12`).
2. **High — `q = 140` bare `(5/8)^140 = 2^{-94.93}` (< 100b without PoW) & `[BCIKS20]` Thm 1.4:** Raised `UD100_QUERIES = 148` so bare `(5/8)^{148} < 2^{-100.35}` clears `UD-100` without PoW; renamed Lean theorem `ud100_query_arithmetic_rate4_q148_pow16`; cited `[BCIKS20]` Thm 1.7 (affine spaces).
3. **High — Full-wire HVZK scope & shared `CUST_RNG_PROVER`:** Split `CUST_RNG_PROVER_AMBIENT` / `CUST_RNG_PROVER_BLUR` via length-prefixed `CShakeRng::from_parts` binding `(seed, header_payload, subset, public_outputs)`; scoped Lean `TVD = 0` explicitly to the ideal sumcheck view.
4. **High — `fetch_add` OTS counter wrap, test seed reuse, depth-0-only Lean reduction:** Switched `sign_header` to bounded `compare_exchange` (`adv12`); gave live Rust frames in `lean_435_byte_exact_conformance` fresh XMSS keys; added Lean `header_unforgeable_xmss_or_collision` (`treeDepth > 0`).
5. **Med — `tile_len = 1` (`n_bits = 0`) wire rejection & mismatched large-frame caps:** Allowed `n_bits <= 16` (`adv11` roundtrips `1x1` and `2x2` `tile_len = 1`); unified `MAX_FRAME_TILES = 65_536` / `MAX_RAW_PCS_ROWS = 2048` across sealing, proving, and wire decoders.
6. **Med — Direct Rust struct verification bypassed `< P_U32` checks (`bb_sub` panic risk):** Added `validate_canonical()` on `ZkBaseFoldPcsOpening`, `AmbientEnvelopeZkProof`, and `BlurDownscaleZkProof`, enforced at entry of both verifiers (`adv12`).
7. **Med — Lean vs Rust header/ROI predicate mismatches:** Aligned Lean `verifyFrameHeader` (`isPow2Le16`, `merkleDepth < 31`, `BodyBounded`, `verifyFrameHeader_bodyBounded`) and `verifyRoiOpening` (`o.pixels.length = h.tileLen`).
8. **Low — `sum_bytes` `u32` overflow, unchecked streaming geometry, late Stage-0 check:** Widened `sum_bytes -> u64`; used checked `checked_mul`/`u32::try_from` and early `RawPcsShape::for_frame`; moved Stage-0 opening length check before `g_raw` allocation in `verify_zk_basefold_opening`.

## 6. Explicit `[OPEN]` Seams
- `[OPEN]` Full composed verifier soundness bound (sumcheck + batching + `[BCIKS20]` Thm 1.7 correlated agreement + lockstep FRI + Fiat-Shamir ROM) in Lean beyond `ud100_query_arithmetic_rate4_q148_pow16`.
- `[OPEN]` Full-wire joint HVZK transcript distribution + seeded `cSHAKE256` CSPRNG reduction (note `AmbientEnvelopeZkProof` reveals `claimed_total` by spec, so singleton subsets reveal that tile's sum).
- `[OPEN]` Formalizing the coset-RS `rt_raw` encoder in Lean so one byte table binds both `tileMerkleRoot` and `rt_raw`.
- `[OPEN]` Enclave durable monotonic NVM persistence of the XMSS OTS index before signature release (RFC 8391 §4.1.9).
