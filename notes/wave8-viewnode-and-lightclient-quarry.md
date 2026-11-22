# Wave-8 Quarry: Toolkit-Free `ViewNode` IR (`Frustum` Non-Interference) & `S11`-Hardened Light-Client Gates

**Date:** 2026-11-21 · **Lane:** `w8-viewnode-lightclient` (`Phase 1` `obend-surfaces` & `obend-lightclients`) · **Metered search ledger:** `Scry: 0, Kagi: 0, eprint.iacr.org: 0` `[EXECUTED]`

## 1. Scope & Donor Provenance

- `[SOURCE]` **Surface IR donor:** `breadstuffs/deos-view/src/tree.rs:25-249` (25-variant `ViewNode`), `deos-view/src/fmt.rs:24-120` (`BindFmt`), `obend/lean/Obend/Vault/FrustumMembrane.lean:661-710` (`Disposition`: `sever / attenuate / interpose / tether`), and `obend/lean/Obend/Vault/Affordance.lean:235-268` (`synthesizeRepairBadge`).
- `[SOURCE]` **Light-client donors & audit findings (`S8`, `S11`):** `breadstuffs/eth-lightclient/src/{lib.rs,ssz.rs,finality.rs,store.rs}` (mainnet period-1800 Electra `397/512`, depth-7 finality branch, depth-4 execution branch; omitted `signature_slot`, wall-clock staleness, and slot-derived period) and `breadstuffs/cosmos-lightclient/src/{lib.rs,bank.rs,verified_gate.rs}` (`cosmoshub-4` adjacent & `~95`-block skip, two-level ICS-23 `bank` balances `0x02` decoder). See [DISTRIBUTED_UI_AND_OBEND_SYNTHESIS.md](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/DISTRIBUTED_UI_AND_OBEND_SYNTHESIS.md) and [CONSENSUS_BLOCKLACE_AND_SETTLEMENT_AUDIT.md](file:///Users/ember/dev/zkml-research/research/breadstuffs_revival_2026_11_21/CONSENSUS_BLOCKLACE_AND_SETTLEMENT_AUDIT.md#L159-L162).
- `[DERIVED]` All quarried shells are zero-GPUI, zero-legacy-`cell`, zero-external-dependency pure `std` Rust (`#![forbid(unsafe_code)]`), paired with a machine-checked Lean `v4.35.0` specification and shared golden vectors.

## 2. Verified Lean `v4.35.0` Assurance Module

`[SOURCE]` [LightClientAndViewLens.lean](file:///Users/ember/dev/minidregg/Assurance/LightClientAndViewLens.lean) (`936` lines `< 950`, `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0` warnings under `lean -DwarningAsError=true`, `10` `#guard_msgs`-pinned `#print axioms` checks):

| Part | Key Theorems & `#tooth` Falsifiers | What Is Proved |
|---|---|---|
| **A · 25-Variant `ViewNode` + `Frustum`** | `fog_of_war_viewNode_noninterference`, `severed_secret_mutation_invisible`, `sever_host_erases_subtree`, `tooth_visible_slot_mutation_changes_projection` | Two worlds agreeing on `frustum.visibleSlots` yield identical projections across all 25 variants (`sectionBox` mirrors Rust `Section`) under `sever`/`attenuate`/`interpose`/`tether`; mutating any hidden or `sever`ed cell slot is invisible; `#tooth` proves visible-slot mutation changes output (non-vacuity). |
| **A · Tree Diff / Patch & Repair** | `applyPatch_diff`, `diff_self_keep`, `applyPatch_keep`, `tooth_applyPatch_mismatched_container_refused`, `synthesizeRepairBadge_ok_iff` | Total structural roundtrip `∀ v v', applyPatch v (diff v v') = some v'`, fail-closed refusal on container mismatch, and exact repair-badge characterization. |
| **B · Electra `S11` Gate** | `ethS11_accepts_implies_pins`, `ethS11_rejects_{cross_chain_replay,future_slot_spoof,expired_staleness,future_time_spoof,sub_supermajority,fork_digest_mismatch,finalized_rollback,period_drift}` | Acceptance entails `expectedChainId`, domain-separated `forkDigest`, `attestedSlot ≤ signatureSlot`, `periodOfSlot signatureSlot = currentPeriod` (`slot / 8192`), `hostNow ≤ attestedTime + maxStaleness`, `attestedTime ≤ hostNow + maxClockDrift`, non-decreasing `finalizedSlot`, `≥ 342/512` supermajority, Altair/Electra finality depth `6 ∨ 7`, exec depth `4`. Golden witnesses: `397/512` & `342/512` accept; `341/512`, Sepolia replay, future slot, and stale header rejected. |
| **B · CometBFT `S11` Gate** | `cometS11_accepts_implies_pins`, `cometS11_rejects_{cross_chain_replay,expired_trust_period,stale_header,future_time_spoof,insufficient_voting_power,zero_overlap_skip}` | Acceptance entails strict `> 2/3` voting power (`2·total < 3·signed`), chain/fork/freshness/trusting-period pins, and disjoint adjacent (`h = trusted + 1` + `epochBindOk`) vs skipping (`h > trusted + 1` + `> 1/3` trust overlap). Golden witnesses: `cosmoshub-4` adjacent & `95`-block skip accept; `theta-testnet-001`, expired trust period, `200/300`, and zero-overlap skip rejected. |

## 3. Standalone Rust `quarried_shells` & Landed `obend` Worktree Crates

- `[SOURCE]` **Research quarry crate:** [quarried_shells](file:///Users/ember/dev/zkml-research/research/wave8_forward_extrapolation_2026_11_21/quarried_shells/Cargo.toml) (`src/viewnode_ir.rs`, `src/lightclient_gate.rs`, `tests/conformance_and_attacks.rs`, `build_and_verify.sh`):
  - Complete 25-variant `ViewNode`, canonical `DVN1` binary codec (`MAX_VIEW_DEPTH = 16`, `MAX_VIEW_NODES = 4096`, trailing-byte refusal), deterministic `diff`/`apply_patch`, `Frustum` fog-of-war scrubber, and `synthesize_repair_badge`.
  - Pure-Rust FIPS 180-4 SHA-256 (checked against NIST `"abc"` KAT), SSZ `is_valid_merkle_branch`, `S11`-hardened Electra & CometBFT gates with sealed `VerifiedEthHeader` / `VerifiedCometHeader`, two-level ICS-23 `bank` balance envelope verifier (`0x02` prefix, `0x00` supply refusal, leading-zero & `u128` overflow refusal), and sealed `ProvenForeignHolding` deriving `chain_id` solely from the verified header (`S8` closed).
- `[EXECUTED]` **Landed `obend` Phase-1 crates (worktree branch `revival-shells-surfaces-lightclient`, commit `dae8cd03b8`):**
  - Added `crates/obend-surfaces` and `crates/obend-lightclients` and wired both into workspace `Cargo.toml` (`7` files, `+2,860` lines).
  - Verified remotely on `hbox` (`SWARM_MEM_MAX=12G timeout --kill-after=10s 600s env RUSTFLAGS="-D warnings" cargo test --release -p obend-surfaces -p obend-lightclients`): `exit 0`, `0` warnings (`4/4` `obend-surfaces` tests + `2/2` `obend-lightclients` tests passed in `2.62s`).
  - Verified `/Users/ember/dev/obebuilder/target/release/obb lint --repo "$WT" --json`: `0` findings on `obend-surfaces` and `obend-lightclients`.

## 4. Verification Summary

- `[EXECUTED]` `build_and_verify.sh`:
  - `LightClientAndViewLens.lean`: `936` lines (`< 950`), isolated Lean `v4.35.0` `-DwarningAsError=true` `exit 0` (`0` warnings, `10/10` `#guard_msgs` axiom pins verified).
  - `quarried_shells`: `RUSTFLAGS="-D warnings" cargo test --release` `exit 0`, `9/9` conformance & adversarial attack tests passed (`0` warnings); `quarried_shells/target` cleaned afterward.
- `[OPEN]` Connecting `obend-lightclients` to live BLS12-381 (`blst`) & Ed25519 signature carriers and binding `obend-surfaces` to `obend-ffi` / `http-serve` belongs to Phase 2 integration.
