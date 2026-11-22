# Wave 10 Tier 2C: RFC 9106 `Argon2id` + Multi-Snapshot Write-All Oblivious Duress Vault (Organ #5)

**Status (2026-11-22):** `[DERIVED]` Lean `v4.35.0` kernel proofs + `[EXECUTED]` pure-Rust (`#![deny(warnings)]`, zero `unsafe`, `sha3`-only) RFC 9106 `Argon2id` & `MultiSnapshotDuressVault` + `gpt-6.2-astra` audit fixes. Research artifact; not a shipped system.
**Artifacts:**
- `/Users/ember/dev/minidregg/Theory/WetwareSafetyAndDuress.lean` (`938 < 950` lines; `0 sorry`/custom `axiom`/`native_decide`; `43` `#guard_msgs`-pinned `#print axioms`, all within `[propext, Classical.choice, Quot.sound]`; Part A preserved intact)
- `/Users/ember/dev/minidregg/prover/src/wetware_duress_guard.rs` (`#![deny(warnings)]`, pure-Rust RFC 7693 `BLAKE2b` + RFC 9106 `Argon2id` + `MultiSnapshotDuressVault`)
- `/Users/ember/dev/minidregg/prover/tests/wetware_and_duress.rs` (`26` `--release` tests) & `/Users/ember/dev/minidregg/prover/testdata/wetware_duress_conformance.json`
- Harness: `/Users/ember/dev/zkml-research/research/wave10_reality_hardening_2026_11_22/formal_duress/build_and_verify.sh` (`exit 0`, prints `ALL OK`, deletes `build/` and `target-duress/` on exit) `[EXECUTED]`.

## 1. Real Pure-Rust RFC 9106 `Argon2id` (`v = 0x13`) Passphrase KDF
- Replaces v1's single non-memory-hard `cSHAKE256` passphrase KDF (`derive_root`, kept only as a legacy v1 baseline) with `derive_vault_root_argon2id` (`ad = "SHE-WETWARE-DURESS/ARGON2ID-ROOT/v2"`, `tag_len = 32`), defaulting to RFC 9106 §4's memory-constrained profile (`ARGON2ID_WEARABLE_DEFAULT`: `m = 65,536 KiB` = 64 MiB, `t = 3` passes, `p = 4` lanes).
- Implements unkeyed RFC 7693 `BLAKE2b` (`1..=64` B), RFC 9106 §3.3 variable-length `H'`, 1,024-byte `G`/`P`/`fBlaMka`, exact RFC 9106 §3.4.1 hybrid indexing (pass `0`, slices `0..1` `Argon2i` data-independent; pass `0`, slices `2..3` and passes `>= 1` `Argon2d` data-dependent), pass `>= 1` XOR-overwrite, and checked allocation (`try_reserve_exact`).
- `[EXECUTED]` Verified bit-for-bit against:
  - `[SOURCE: RFC 9106 §5.3]` official `Argon2id` 32-byte tag: `0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659`;
  - `[SOURCE: RFC 7693 App. A + Python hashlib.blake2b]` 7 `BLAKE2b` KATs (`""`, `"abc"` at `64/32/1` B, exact `128/129/256`-B boundaries);
  - `[EXECUTED]` 4 OpenSSL 4.1.0 `openssl kdf ARGON2ID` cross-check vectors covering `segment_length = 512 > 128` address-block rollover (`T = 65, 96, 100` multi-block `H'`) and non-aligned `m = 39, p = 4` (`m' = 32 != m`).

## 2. Multi-Snapshot Write-All Oblivious Duress Vault (`MultiSnapshotDuressVault`)
- **Geometry:** Fixed `40 + 64·N`-byte image: `(epoch: u64, volume_salt: [u8; 32])` + `N` × 64-byte `(body ‖ tag_e) XOR pad_e` blocks, where `pad_e` and `tag_e` bind `(root, volume_salt, epoch, slot_index)` under domain-separated `cSHAKE256`.
- **Disjoint slot maps:** `derive_decoy_slots` and `derive_sovereign_slots_disjoint` use unbiased keyed Fisher–Yates rejection sampling (`zone = (2^64 - rem) % rem`) over `[0..N)` and `[0..N) \ I_decoy`, guaranteeing `I_decoy ∩ I_sov = ∅`. `create_dual` and `commit_dual` reject `IdenticalRoots`, `EmptyCompartment`, `SlotCollision`, `NoOwnedSlots`, `NoOwnedSovereignSlots`, `TooManySlots`, and `EpochOverflow`.
- **Write-all invariant:** Every commit (`commit_decoy_only`, `init_sovereign_compartment`, `commit_dual`) increments `epoch = epoch + 1` and rewrites **all `N` blocks** — decoy slots under `(root_decoy, epoch + 1)`, sovereign slots (when mounted) under `(root_sov, epoch + 1)`, and all remaining slots with fresh CSPRNG chaff.
- **Honest coercion vs. availability boundary:** In `commit_decoy_only`, `root_sov` is absent, so rewriting every `i ∉ I_decoy` with fresh chaff **intentionally panic-shreds** unmounted sovereign slots in the new image (preserving multi-snapshot deniability; historical snapshots remain opaque). Updating decoy notes while preserving hidden sovereign slots requires `commit_dual` (both roots present) or external backup + `init_sovereign_compartment`.

## 3. Lean `v4.35.0` Theorems & `#tooth` Refutations (`Theory/WetwareSafetyAndDuress.lean`)
- `[DERIVED]` `multi_snapshot_trace_indistinguishable` & `multi_snapshot_joint_distribution_equal`: across any `K`-epoch trace (`Fin K → Fin N → S`), whenever `∀ e, Disjoint D (Sov e)`, an explicit bijection (`multiSovShift`) proves exact acceptance-count equality (`TVD = 0`, ideal-XOF model) between dual-sovereign write-all traces (`realTrace`) and decoy-only write-all traces (`chaffTrace`), even for dynamically varying `Sov : Fin K → Finset (Fin N)`.
- `[DERIVED]` `multi_snapshot_duress_unlock_correct` (load-bearing on `Disjoint D (Sov e)`), `multi_snapshot_sovereign_unlock_correct` (wired directly to `SlotScheme.seal`/`open_`), and `multi_snapshot_premises_inhabited` (non-vacuous `K = 2, N = 4` witness).
- `[REFUTED: v1 in-place single-slot update under 2-snapshot forensics]` (`[DERIVED]` `tooth_single_slot_update_leaks_across_two_snapshots`): when untouched chaff stays static across 2 snapshots, `nonDecoyChanged` fires on `0` decoy-only traces for every chaff vector `U`, vs. `12/16` (`3/4`) of in-place sovereign updates even with independent pads (Rust `tooth_v1_single_slot_update_leaks_across_two_snapshots` pinpoints exact slot `3`).
- `[DERIVED]` `#tooth` `tooth_reused_epoch_pad_leaks_across_two_snapshots`: reusing pads across 2 epochs in `realTrace` yields `16/16` (`100%`) slot equality vs. `64/256` (`25%`) for fresh `chaffTrace` (advantage `3/4`).
- `[DERIVED]` `#tooth` `tooth_slot_collision_breaks_deniability`: dropping `Disjoint D (Sov e)` drops decoy slot-0 preservation from `16/16` to `4/16` (advantage `3/4`) and forces `SlotScheme.open_` to return `none`.

## 4. `gpt-6.2-astra` Audit & Executed Numbers (`--release`, single thread)
- **Audit fixes folded (`0` CRITICAL):** (H1) `commit_dual` now requires `sov_count > 0` (`NoOwnedSovereignSlots`) and separates `init_sovereign_compartment` so a mistyped sovereign passphrase can never silently wipe sovereign data; (H2) added `from_bytes_min_epoch` (`EpochRollback`) and documented trusted monotonic counter requirement against flash rollback/branching; (M3/M5) checked `N <= u32::MAX`, `checked_image_len`, and `try_reserve_exact` in Argon2id; (L6/L7/L8) pinned 4 OpenSSL 4.1.0 Argon2id edge vectors, rejected empty compartments at creation, and documented PHC `salt >= 8` policy; tightened Lean `#tooth` statements to use `realTrace`/`chaffTrace`/`open_` directly.

| Benchmark / Check (`build_and_verify.sh`, `--release`) | Result (`[EXECUTED]`) |
|---|---|
| Lean `v4.35.0` kernel check (`938` lines, `43` axiom pins) | `2.59 s`, `rc = 0`, `0` warnings; `check-import-boundary.sh` OK |
| `Argon2id` (`m = 65,536 KiB`, `t = 3`, `p = 4`) | **`100.04 ms`** (pure Rust, zero `unsafe`) |
| `MultiSnapshotDuressVault` `N = 64` `commit_dual` (write-all) | **`0.338 ms/commit`** |
| Multi-snapshot epoch-diff `χ²` (200 epochs, 255 dof, crit ≈ 370) | `275.9` sovereign / `251.9` chaff |
| Part A scrubber 720p / 1080p 4:4:4 (preserved) | `2.158 ms` (`463.3 fps`) / `4.864 ms` (`205.6 fps`) |

## 5. Open / Modeling Boundaries
- `[HYPOTHESIS]` Computational PRF reduction from `cSHAKE256` under Argon2id-derived roots to the Lean ideal-XOF model is not mechanised.
- `[OPEN]` Rollback/forking of a raw flash image cannot be stopped by flash contents alone; callers must supply `min_epoch` from a trusted hardware monotonic counter (`from_bytes_min_epoch`) and pass an OS CSPRNG for chaff.
- `[OPEN]` Pure-Rust Argon2id buffer wiping is best-effort (`fill(0)` + `black_box`, no `unsafe`/`zeroize` crate), and machine-code constant-time timing was not audited.
