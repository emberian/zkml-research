# Wave 8 — Post-Quantum Issuer-Root-Isolated `ZkBiscuit` Selective-Disclosure Credentials (`D8`; Closing `CAP-01`, `CAP-10`, `CAP-12`)

**Date:** 2026-11-21 · **Lane:** `w8-zkbiscuit-pq-creds` (`wave8_forward_extrapolation_2026_11_21`)
**Metered Search Ledger:** `Scry: 0` · `Kagi: 0` · `eprint.iacr.org fetches: 0` `[EXECUTED]`.
**Read-Only Donors Inspected (`0` Edits):** [breadstuffs/credentials/src/issuance.rs](file:///Users/ember/dev/breadstuffs/credentials/src/issuance.rs#L85-L95), [revocation.rs](file:///Users/ember/dev/breadstuffs/credentials/src/revocation.rs#L135-L242), [webauth-core/src/lib.rs](file:///Users/ember/dev/breadstuffs/webauth-core/src/lib.rs#L176-L255), [dregg-pq/src/lib.rs](file:///Users/ember/dev/breadstuffs/dregg-pq/src/lib.rs#L1-L62), [obend/lean/Obend/Polis/ZkBiscuit.lean](file:///Users/ember/dev/obend/lean/Obend/Polis/ZkBiscuit.lean#L1-L987) `[SOURCE]`.

---

## 1. Closed Defects & Architecture (`D8`, `[SOURCE]`, `[DERIVED]`)

Replacing burned `breadstuffs/credentials` and legacy `webauth-core` / `dregg-agent` `dga1_` flows ([MASTER_REVIVAL_ALIGNMENT.md](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/MASTER_REVIVAL_ALIGNMENT.md#L53) §1 `A3`, §5.2 `D8`), we formalize and implement a **100% post-quantum** (`cSHAKE256` SP 800-185 + pluggable `PqSigScheme` / `PqSigBackend`, instantiated by 256-bit pure-hash `wotsCshake256` and compatible with `dregg-pq` Hybrid Ed25519+ML-DSA-65; **zero** elliptic-curve pairings or Pedersen commitments) selective-disclosure `ZkBiscuit` credential layer:

| Defect | Legacy Donor Failure (`[SOURCE]`) | Formal & Native Closure (`[DERIVED]` / `[EXECUTED]`) |
|---|---|---|
| **`CAP-01`** | `credentials/src/issuance.rs:94` serializes `pub root_key: [u8; 32]` inside `Credential`, letting any holder forge fresh root macaroons. | `IssuerSecret` never enters `HolderToken` or `serialize_bytes()`. `holder_attenuate_needs_no_issuer_secret` proves holder-only attenuation; `block0_unforgeable_reduction` gives an EUF-CMA reduction to the PQ signature scheme (`PqSelectiveBiscuit.lean:656, 703`); `#tooth` `cap01_tooth_forged_block0_rejected` (`:769`). |
| **`CAP-10` (+ `CAP-13`)** | `credentials/src/revocation.rs:135-144, 238` re-sorts a copy when hashing the root, then runs `binary_search` on the **unsorted** witness vector; `webauth-core:176-180` checks tail only (bypassed by appending a no-op block). | `RevocationSet.ofList` (`dedupSort`) enforces `Pairwise (· < ·)` by construction: `contains_ofList_iff` (`100%` complete regardless of insertion order, `:317`), `ofList_order_independent` (`:319`), `fromVerifiedWitness` rejects unsorted witnesses before search (`:327`), `revoke_ancestor_kills_cone` checks every prefix `0..=k` (`:739`); `#tooth` `cap10_tooth_unsorted_bsearch_miss_killed` (`:777`). |
| **`CAP-12`** | `webauth-core/src/lib.rs:205, 250` scans holder-appended blocks via `first_attr("acct")`, enabling `acct=admin` subject spoofing. | `extractSubject` (`:560`) and `extractIssuerAuthority` (`:568`) read **exclusively** block `0` (`extractSubject_invariant_under_hops`, `:570`); `attenuation_monotone_from_block0` (`:714`) proves monotone narrowing of `rights` and `expiresAt` across every prefix; `#tooth` `cap12_tooth_holder_appended_acct_admin_killed` (`:781`). |
| **Selective Hiding (`D8`)** | Unrevealed attributes must stay hidden against offline dictionary attacks without elliptic-curve Pedersen/BBS+. | `cSHAKE256` Merkle tree (`0x00`/`0x01`/`0x02` domain tags) with `256`-bit per-leaf `salt_i`: `verifyMerkleOpening_complete` (`:389`), `merkleFold_binds` (`:408`), `attrLeafCommit_binds` (`:339`), `unrevealed_attr_view_independent` (`:455`), and exact finite counting bound `unrevealed_salt_offline_guess_bound` (`saltHitCount ≤ q` over `2^256`, `:483`). |

---

## 2. Verified Artifacts & Line Counts (`[EXECUTED]`)

| File | Footprint | Verification Status (`build_and_verify.sh`, `exit 0`, `0` warnings) |
|---|---|---|
| [PqSelectiveBiscuit.lean](file:///Users/ember/dev/minidregg/Theory/PqSelectiveBiscuit.lean) | `868` lines (`< 900`) | Lean `v4.35.0` isolated overlay (`-DwarningAsError=true`), `1.59 s`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `14` `#guard_msgs`-pinned `#print axioms` (all within `{propext, Classical.choice, Quot.sound}`), `Theory/` import-boundary clean (`Theory.HashBytes`, `Theory.Sp800185Cshake256Core` only; `scripts/check-import-boundary.sh` passed). |
| [pq_biscuit_conformance.json](file:///Users/ember/dev/minidregg/prover/testdata/pq_biscuit_conformance.json) | `14,972` bytes | Emitted directly by Lean `#eval emitPqBiscuitConformance` using native `cSHAKE256` (`libmini_kernels_lean.so`): 4 salted attributes, 2-hop attenuated `wotsCshake256` chain (with `"acct=admin"` decoy hop 1), `S = {1, 3}` selective disclosure, order-independent revocation root, and ancestor-cone kill. |
| [pq_biscuit.rs](file:///Users/ember/dev/minidregg/prover/src/pq_biscuit.rs) | `755` lines | Byte-exact native Rust mirror (`sha3` `cSHAKE256` only, `RUSTFLAGS="-D warnings"`, `2/2` unit tests passed). |
| [pq_biscuit_selective.rs](file:///Users/ember/dev/minidregg/prover/tests/pq_biscuit_selective.rs) | `515` lines | `6/6` `--release` tests passed (`0.30 s`): byte-exact Lean JSON parity, `CAP-01`, `CAP-10`, `CAP-12`, unrevealed-attribute hiding, and `--release` microbenchmarks. |
| [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/wave8_forward_extrapolation_2026_11_21/formal_biscuit/build_and_verify.sh) | `285` lines | Isolated Lean 4.35.0 overlay (zero `lake build` in `minidregg`) + `--release` Cargo test runner. |

---

## 3. Native `--release` Microbenchmarks (`WotsCshake256` + `cSHAKE256` Merkle, `[EXECUTED]`)

Measured via `cargo test --release --test pq_biscuit_selective -- --nocapture --test-threads=1` (`100` iterations, `16` salted attributes / height `4`, `4`-of-`16` disclosed, `1,024`-entry revocation set, `2`-hop attenuated chain):

| Operation | Latency (`--release`) | Size / Notes |
|---|---:|---|
| `issue_root_token` (includes `wotsPk` + block-0 sign) | `1,164.7 µs` | `67`-chain `w=16` `cSHAKE256` WOTS+ (`2,144` B sig) |
| `attenuate_token` (`1` hop, holder key only) | `387.3 µs` | `0` access to `IssuerSecret` (`CAP-01`) |
| `verify_presentation` (`2`-hop + `4/16` Merkle + `1024`-rev cone) | `1,108.3 µs` | Checks prefixes `0, 1, 2` against sorted `RevocationSet` |
| `RevocationSet::from_raw` (`1,024` unsorted 256-bit IDs) | `15.2 µs` | Canonical `sort` + `dedup` (`CAP-10`) |
| Canonical `HolderToken::serialize_bytes()` (`2`-hop WOTS+) | — | `6,705` B (`0` bytes of `IssuerSecret`) |

---

## 4. Open Follow-Ons (`[OPEN]`)

1. **Multi-Show Unlinkability (`D8` Phase 2):** Single-issuer salted Merkle selective disclosure is closed above; unlinkable multi-show ring presentations can wrap `verifyPresentation` inside `Tower256AlgebraicCert` once gate `G8` (`#130` BaseFold fold-root binding) closes.
2. **Hybrid ML-DSA-65 Backend Adapter:** Wiring `dregg-pq::MlDsaKey` + Ed25519 into `PqSigBackend` inside `obend-net` / `obend-surfaces` requires zero changes to `PqSelectiveBiscuit.lean` (`PqSigScheme` is already backend-polymorphic).
