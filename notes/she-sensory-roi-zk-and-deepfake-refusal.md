# Wearable SHE Organ #4 ("Epiphany Lens"): Zero-Pixel-Leakage CSI-2 Tile-Merkle ROI Redaction, Algebraic `BabyBear` Blur/Envelope Certificates & Deepfake-Splice Refusal

**Date:** 2026-11-21 · **Lane:** `she-sensory-roi-zk` (Wave 9 *Rainbows End* Wearable SHE Organ #4) · **Metered search ledger:** `Scry: 0, Kagi: 0, eprint.iacr.org: 0` `[EXECUTED]`

## 1. Scope & Deconfliction

- `[SOURCE]` Inspected read-only siblings [ContentCertificate.lean](file:///Users/ember/dev/minidregg/Selvage/ContentCertificate.lean) (`ContentScheme` / `BindBreak` computational binding), [StoreHiding.lean](file:///Users/ember/dev/minidregg/Compiler/StoreHiding.lean) (`narrowed_view_independent_of_uncovered_given_salts` & `SaltedLeafHiding` poles), [Sp800185Cshake256Core.lean](file:///Users/ember/dev/minidregg/Theory/Sp800185Cshake256Core.lean), and [BabyBear.lean](file:///Users/ember/dev/minidregg/Compiler/BabyBear.lean) (`p = 2^31 - 2^27 + 1 = 2,013,265,921`).
- `[DERIVED]` Unlike plain post-redaction hashing (`OBEND.SHE.SENSOR_SEAL/v1`), Organ #4 binds every raw `16x16` CSI-2 camera luminance tile and I2S audio window at hardware capture time via a **two-subleaf domain-separated SP 800-185 `cSHAKE256` Merkle tree**:
  - `rawCommit_i = cSHAKE256(".../RAW_TILE/V1", ctx(24B) || idx(4B) || rawSalt_i(32B) || len(4B) || pixels_i)`
  - `sumCommit_i = cSHAKE256(".../SUM_LEAF/V1", ctx(24B) || idx(4B) || sumSalt_i(32B) || sum_i(4B) || len(4B))`
  - `tileLeaf_i  = cSHAKE256(".../TILE_LEAF/V1", ctx(24B) || idx(4B) || rawCommit_i || sumCommit_i)`
  - Hardware frame attestation `headerTag = cSHAKE256(".../HW_FRAME_SEAL/V1", hwKey || ctx || gridW || gridH || depth || modality || merkleRoot)` where `ctx = (sensorId, frameSeq, timestampNs)` is bound into both the header and every tile leaf.
- `[DERIVED]` Strictly disjoint owned paths touched (`0` edits to `lib.rs` or `Assurance.lean`):
  1. [SensoryRoiZeroKnowledge.lean](file:///Users/ember/dev/minidregg/Assurance/SensoryRoiZeroKnowledge.lean) (`879` lines `< 900`, Lean `v4.35.0`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `13` `#guard_msgs`-pinned `#print axioms`, `0` warnings).
  2. [sensory_roi_cert.rs](file:///Users/ember/dev/minidregg/prover/src/sensory_roi_cert.rs) (`#![deny(warnings)]`), [sensory_roi_wearable.rs](file:///Users/ember/dev/minidregg/prover/tests/sensory_roi_wearable.rs), and Lean-emitted [sensory_roi_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/sensory_roi_conformance.json) (`5,354` bytes).
  3. [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/formal_sensory_roi/build_and_verify.sh) (isolated Lean `v4.35.0` overlay + `--release` Rust suite; zero `lake build` in `minidregg`).

## 2. Verified Lean `v4.35.0` Theorems (`[EXECUTED]`, `[DERIVED]`)

| Property | Lean Theorem (`Assurance/SensoryRoiZeroKnowledge.lean`) | Statement & Axiom Pin |
|---|---|---|
| Merkle binding | `merklePath_sound_or_collision` (`verifyMerklePath_complete`) | Verified `evalMerklePathAux` opening pins exact `leaves[idx]` or constructively extracts `Cshake256Collision` (`[propext, Classical.choice, Quot.sound]`). |
| Zero-bystander view independence | `unopened_bystander_tiles_hidden`, `bystander_salt_disclosed_iff_in_frustum` | Two frames matching on frustum `U` and sealed bystander leaves `j ∉ U` yield identical `(merkleRoot, RoiTileItem list)`; pixels & salts appear iff `inFrustum idx = true` (`[propext, Quot.sound]`). |
| Fresh-salt bystander hiding | `unopened_bystander_tiles_hidden_fresh_salts` + poles `constTileScheme_hiding` / `identityTileScheme_not_hiding` | Under named `TileLeafHiding deployedTileScheme Indist` (zero custom axioms!), mutating any bystander pixel under fresh 256-bit salts yields an indistinguishable leaf (`[propext, Quot.sound]`). |
| ROI reveal soundness | `roi_reveal_sound_or_collision` | Accepted `RoiRevealCert` binds every opened tile `i ∈ U` to exact hardware-captured `(pixels, rawSalt, sumSalt)` or extracts `Cshake256Collision` (`[propext, Classical.choice, Quot.sound]`). |
| Exact `BabyBear` no-wrap | `bounded_sum_no_wrap_babybear`, `bounded_nat_no_wrap_babybear` | For `totalSamples * 255 < babyBearP`, integer sums cast to `BabyBear` with zero modular wrap-around (`[propext, Classical.choice, Quot.sound]`). |
| `TVD = 0` sub-tile/formant hiding | `zeroSumMask_preserves_sum`, `zeroSumMask_hides_individual_samples` | Explicit involution `shiftMask p p' m = m + p - p'` over zero-sum `BabyBear` masks maps any two equal-sum pixel/audio blocks to identical masked views (`[propext, Classical.choice, Quot.sound]`). |
| Zero-raw-pixel blur & ambient-dB soundness | `blur_cert_sound_or_collision` | Accepted `BlurEnvelopeCert` leaves `rawCommit_i` sealed while proving exact `16x16 -> 1x1` tile means and exact bounded integer `E_win = (sumBB maskedTerms).val`, or extracts `Cshake256Collision`. |
| Anti-deepfake `#tooth` suite | `tooth_synthetic_pixel_splice_refused`, `tooth_cross_timestamp_replay_refused`, `tooth_tile_coordinate_graft_refused`, `tooth_forged_blur_mean_refused`, `tooth_unmasked_salt_reuse_refused`, `tooth_blur_bad_mean_rejected` | Universally refuses 1-pixel splices, cross-timestamp/seq header replays, cross-tile coordinate grafts, forged blur means/envelopes (up to `Cshake256Collision`), and kernel-decides (`0` axioms) frame-wide salt reuse refusal. |

## 3. Native Rust Engine, Conformance & `720p` `60 fps` Benchmarks (`[EXECUTED]`)

Executed `/Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/formal_sensory_roi/build_and_verify.sh --rebuild-lean` (`exit 0`, `0` warnings):

1. **Lean `v4.35.0` overlay + import boundary:** `Assurance.SensoryRoiZeroKnowledge` verified in **`2.83s`**, `scripts/check-import-boundary.sh` passed, emitted `sensory_roi_conformance.json` (`5,354` B) with all 7 Lean self-checks `true`.
2. **Byte-exact Lean $\leftrightarrow$ Rust conformance (`lean_435_byte_exact_conformance`):** Matched `empty_leaf`, all 4 CSI-2 `16x16` tile leaves, `merkle_root`, `header_tag`, Merkle paths, `sealed_raw_commit`, I2S audio `merkle_root`/`header_tag`, and `BabyBear` zero-sum masked envelope terms bit-for-bit.
3. **`1280x720` (`80x45 = 3,600` `16x16` tiles, depth `12`) streaming `--release` benchmark (`bench_720p_streaming_sealer_and_verifier_within_60fps_budget`):**
   - **Streaming tile-Merkle seal:** **`1.863 ms/frame`** (budget `< 4.0 ms`; `11.2%` of `16.67 ms` `60 fps` frame budget) using pre-absorbed `CShake256Core` handles, stack `[u8; 256]` tile extraction, and `std::thread::scope`.
   - **Combined ROI + blur verify (`64` ROI tiles + `64` algebraic blur tiles):** **`0.886 ms`** (budget `< 2.0 ms`).
4. **8 adversarial deepfake / bystander-recovery tests (`11/11` tests passed in `0.04s`):**
   - `adv1`: 1-pixel LSB splice in ROI tile → `MerklePathMismatch`.
   - `adv2`: cross-timestamp header tamper & cross-frame replay → `HeaderAttestationMismatch` / `MerklePathMismatch`.
   - `adv3`: authentic tile grafted from tile `0` to tile `2` → `MerklePathMismatch`.
   - `adv4`: intra-tile (`rawSalt == sumSalt`) and cross-tile salt reuse → `SaltReuseDetected`.
   - `adv5`: forged `16x16 -> 1x1` blur mean & `+1` tile sum → `InvalidBlurMean` / `MerklePathMismatch`.
   - `adv6`: tampered `BabyBear` masked envelope & duplicate-tile energy inflation → `BabyBearSumcheckMismatch` / `DuplicateTileIndex`.
   - `adv7`: zero-bystander-leakage wire audit confirms zero bystander face/screen bytes or salts appear in `RoiRevealCert` / `BlurEnvelopeCert` wire streams, and bystander mutations leave opened ROI view items byte-identical.
   - `adv8`: `BabyBear` zero-sum mask bijection renders distinct equal-energy I2S speech vs. flat-ambient windows bit-identical (`TVD = 0`) and rejects out-of-range `tile_sum > tile_len * 255`.

## 4. Explicit Security Boundary & `[OPEN]` Hardware Seam

- `[OPEN]` `TileLeafHiding deployedTileScheme Indist` is stated as an explicit named assumption (mirroring `Compiler.StoreHiding.SaltedLeafHiding`, `0` custom axioms); computational indistinguishability rests on `cSHAKE256` PRF/RO security over fresh 256-bit hardware TRNG salts.
- `[OPEN]` In production Epiphany Lens silicon, the symmetric `hwKey` header MAC (`CUST_FRAME_SEAL`) swaps cleanly for a hardware-enclave asymmetric signature (e.g., Ed25519 / ML-DSA over the same 77-byte `headerBodyBytes`) backed by the CSI-2/I2S DMA-isolated sensor SoC root of trust.
