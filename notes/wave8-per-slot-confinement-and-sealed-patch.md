# Wave-8 Gate `G7`: Per-Slot Hybrid `X25519 + ML-KEM-768` Key Confinement & Statement-Pinned Keyless Sealed-`Hyperdocument` Binding

**Date:** 2026-11-21 · **Lane:** `w8-hyperdoc-mlkem-gate` · **Gates Closed:** `G7` (`CAP-21`, `L8`, `F4` in [MASTER_REVIVAL_ALIGNMENT.md](../research/breadstuffs_revival_2026_11_21/MASTER_REVIVAL_ALIGNMENT.md#L114))
**Status:** Verified end-to-end (`exit 0`, `0` warnings on Lean `v4.35.0` kernel `25.67s` + `check-import-boundary.sh` + `--release` Rust with `RUSTFLAGS="-D warnings"`).
**Metered search ledger:** `kagi.py`: `0`; `scry.py`: `0`; `eprint.iacr.org`: `0` (`[EXECUTED]`).

## 1. Defects Closed (`[SOURCE]`, `[DERIVED]`)

1. **`CAP-21` Root `ViewKey` Leakage (`breadstuffs/cell-crypto/src/read_cap.rs:334-345`):** Legacy `ReadCap::attenuate` copied the raw root `ViewKey` into every attenuated read capability, allowing a delegate granted only slot `2` to derive `slot_secret(7)` directly (`[SOURCE]`).
2. **`L8` Witness-Chosen `cell_blinding_key` & `F4` Keyless Public `ciphertext -> saltedPatchRoot` Gap (`Assurance/SealedHyperdocGrammarGate.lean`, `prover/src/grammar_capability.rs:2231-2244, 2606`):** Wave-7A `#118` kept `cell_blinding_key` witness-supplied (`L8`), while the keyless public observer verified only ciphertext length (`F4`), without binding public `ciphertext` bytes to `(saltedPatchRoot, key_commit_i, nonce, slot_aad)` (`[SOURCE]`, `[DERIVED]`).

## 2. Lean `v4.35.0` Formalization (`0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`)

[PerSlotKeyConfinement.lean](file:///Users/ember/dev/minidregg/Assurance/PerSlotKeyConfinement.lean) (`948` lines `< 950`, `17` `#guard_msgs`-pinned `#print axioms`, `Assurance/` import tier) proves (`[DERIVED, EXECUTED]`):

- **Per-Slot Hybrid Confinement (`CAP-21` Fix):**
  - `slotKeyCommit (i, s) = cSHAKE256("SLOT_KEY_COMMIT", u64LE i || digestLE s)` with constructive binding `slotKeyCommit_eq_or_collision` (`FramedXofCollision cshakeC "SLOT_KEY_COMMIT"`).
  - `AttenuatedSlotCap` carries **no `rootViewKey`** and distributes only hybrid `X25519 + ML-KEM-768` wrapped per-slot keys (`wrapSlotKey` / `unwrapSlotKey`, honest roundtrip `unwrapSlotKey_wrapSlotKey`).
  - `attenuate_refuses_amplification` and `attenuate_omits_ungranted_slots`: attenuation narrows `grantedSlots` monotonically and omits every `j ∉ subSlots` (`lookupWrapped j = none`).
  - `ungranted_slot_non_derivable` and `no_adversary_distinguishes_ungranted_slot`: mutating the per-slot KDF oracle at any `j ∉ grantedSlots` leaves the entire `AttenuatedSlotCap` envelope literally identical, so no adversary (even unbounded) distinguishes `slot_secret(j)`.
  - `hybrid_wrap_dual_protection`: XOR masking under the hybrid combiner KEK is a `Coordinate 8` bijection, hiding `slot_secret(i)` if either X25519 or ML-KEM-768 remains unbroken.
  - `#tooth` regressions `tooth_legacy_readcap_leaks_ungranted_slot` and `tooth_confinement_gate_rejects_legacy_root_copy` exhibit legacy `CAP-21` leakage of ungranted slot `7` and prove `verifyReadCapConfinement` refuses root-bearing envelopes.
- **Statement-Pinned `key_commit_i` & Keyless `Tower256` Blinded-XOR Weld (`L8` + `F4`):**
  - `packSaltedLeaf_xor_eq_ciphertextLeaf`: in characteristic-2 `Tower256` (`Coordinate 8`), `packSaltedLeaf pt s ⊕ packSaltedLeaf ks s = packSaltedLeaf (pt ⊕ ks) 0`, cancelling the 248-bit salt identically.
  - `salted_xor_mask_eval_eq_ciphertext_eval`, `blinded_xor_weld_holds`, and `blinded_xor_weld_zero_leakage`: for any Fiat–Shamir challenge $\gamma \in \mathrm{GF}(2^{256})$ and one-time pad `bPad`, `(evalS ⊕ bPad) ⊕ (evalM ⊕ bPad) = evalC`, with `bPad ↦ evalS ⊕ bPad` an exact zero-leakage bijection.
  - `verifyKeylessCiphertextWeld_sound_or_collision`, `keyless_weld_rejects_forged_ciphertext_or_collision`, and `keyless_weld_rejects_swapped_root_or_collision`: the keyless verifier (`0` secrets, `0` plaintext) enforces `ciphertextMerkleRoot`, `computeWeldDigest` over `(saltedPatchRoot, maskMerkleRoot, ctMerkleRoot, keyCommit, nonce, aadDigest, patchLen, aeadTag, blindPadCommit)`, and `blindEvalS ⊕ blindEvalM = evalC`, rejecting forged ciphertexts or swapped roots up to explicit `FramedXofCollision cshakeC`.
  - Capstone `verifyConfinedSealedHyperdocPatch_sound_or_collision` welds `SealedHyperdocGrammarGate.verifySealedHyperdocPatch_sound_or_collision` with pinned `slotKeyCommit` (`witSlotSecret = registeredSecret`), exact stream-AEAD sealing, and `verifyKeylessCiphertextWeld`, inhabited by `demo_confined_gate_verified`, `demo_tooth_corrupted_blind_xor_rejected`, and `demo_tooth_attenuated_cap_omits_slot7`, emitting [per_slot_seal_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/per_slot_seal_conformance.json) (`3,551 B`).

## 3. Native Pure-Rust Engine, Conformance, & Benchmarks (`[EXECUTED]`)

Implemented in [per_slot_seal.rs](file:///Users/ember/dev/minidregg/prover/src/per_slot_seal.rs) and tested in [per_slot_seal_gate.rs](file:///Users/ember/dev/minidregg/prover/tests/per_slot_seal_gate.rs) with zero new Cargo dependencies (`sha3 = "0.10"` + `std` only):
- **Real RFC 7748 `X25519`:** constant-time Montgomery ladder with low-order all-zero rejection, verified against RFC 7748 §6.1 official Alice/Bob test vectors.
- **Real FIPS 203 `ML-KEM-768`:** exact `k=3, n=256, q=3329, du=10, dv=4` (`ek=1,184 B`, `dk=2,400 B`, `ct=1,088 B`, `ss=32 B`) with NTT, `SamplePolyCBD_2`, canonical 12-bit coefficient checks, and constant-time FO implicit rejection (`J(z || c)`).
- **Lean $\leftrightarrow$ Rust Parity & Adversarial Matrix:** `28/28` Lean-emitted conformance vectors match bit-for-bit; `0` plaintext slices `>= 6 B` appear in `KeylessPublicPatchStmt`; all 8 keyless forgery variants (1-bit ciphertext flip, swapped `salted_patch_root`, swapped `key_commit`, swapped `nonce`, mutated `slot_aad`, mutated `aead_tag`, corrupted `blind_eval_s`, and re-hashed forged ciphertext) return `Err(PerSlotError::CiphertextRootMismatch(_))`, and rogue witness keys return `Err(PerSlotError::KeyCommitMismatch)`.

| Verification / Benchmark Gate (`--release`, Apple Silicon, `RUSTFLAGS="-D warnings"`) | Measured (`[EXECUTED]`) |
| --- | --- |
| Lean `4.35.0` `Assurance.PerSlotKeyConfinement` (`-DwarningAsError=true`, `17` axiom pins) | `exit 0`, `0` warnings (`25.67 s` cold) |
| Pure-Rust Hybrid `X25519 + ML-KEM-768` keygen / mint (`2` slots) / unwrap (`1` slot) | **`0.478 ms`** / **`1.659 ms`** / **`0.456 ms`** |
| `4 KiB` (`4,096 B`) statement-pinned seal (`seal_pinned_slot_patch`, 8-thread salts/Merkle/Horner) | **`29.648 ms`** |
| `4 KiB` **keyless** consensus verify (`verify_keyless_ciphertext_weld`, `0` secrets, `0` plaintext) | **`13.709 ms`** |
| Full 3-hop `verify_confined_sealed_hyperdoc_patch` (grammar chain + pinned key + keyless weld) | **`1.339 ms`** |

## 4. Exact Security Calibration & Remaining Seam (`[DERIVED]`, `[OPEN]`)

- **Closed here (`G7` core):** `CAP-21` root-key exposure is eliminated by type and oracle non-interference; `L8` witness-chosen `cell_blinding_key` is eliminated by statement-pinned `slotKeyCommit`; `F4` keyless public verification rejects ciphertext/root/key-commit/nonce/AAD/AEAD-tag tampering without secrets, and authorized slot readers verify `saltedContentCommit(pt, salts) == saltedPatchRoot` unconditionally (`[DERIVED, EXECUTED]`).
- **Residual `[OPEN]` composition seam (`F6` / `G8`):** Against a *malicious prover holding `slot_secret(i)`* who fabricates a valid-looking `(blindEvalS, blindEvalM)` disconnected from `saltedPatchRoot` and `maskMerkleRoot`, proving Merkle-column evaluation consistency (and in-circuit `cSHAKE256` keystream derivation) without a keyed custodian composes with `Tower256AlgebraicCert` once BaseFold `#130` (`G8`) closes (`[OPEN]`).

## 5. Reproduction Command & Proposed Maintainer Folds

```bash
bash /Users/ember/dev/zkml-research/research/wave8_forward_extrapolation_2026_11_21/formal_perslot/build_and_verify.sh
```

- **Proposed maintainer folds (unmodified here):** add `import Assurance.PerSlotKeyConfinement` to `minidregg/Assurance.lean`, index this note in `notes/README.md`, and mark Gate `G7` (`CAP-21` + `L8` + `F4`, leaving only `F6` gated on `G8/#130`) closed in `docs/VERDICTS.md`.
