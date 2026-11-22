# Wave 8A & 8B Status — Coherent Extrapolated Systems & `~/dev/obend` Revival Cutover

**Date:** 2026-11-22
**State:** `COMPLETE` (`16 / 16` lanes verified; `13 / 13` `obend` commits pushed live to `origin/dev`; all `minidregg` and `zkml-research` artifacts verified with `0` warnings).

## 1. Pushed `~/dev/obend` Commits (`origin/dev` `dae8cd03..d6a39879`)

1. `dae8cd03` — `obend-surfaces` (25-variant `ViewNode` + `Frustum`) & `obend-lightclients` (`S11` Electra/CometBFT + ICS-23) (`D7`, `S11`) (`[EXECUTED]`).
2. `b5482693` — `Obend/Crypto/Tower256.lean` + `Obend/Vault/ContentCert.lean` canonical 32B LE Fan–Paar wire codec (`G4`) (`[EXECUTED]`).
3. `ae2299c6` — `Obend/Ledger/Floors.lean` explicit `FloorPolicy` polarity (`G2`) (`[EXECUTED]`).
4. `17f4be53` — `Obend/Consensus/Simplex.lean` `n - f` quorum over `3f + 1 <= n` (`G5`) (`[EXECUTED]`).
5. `ba650b53` — `obend-prove-worker` bounded `ProveService<I,O>` + deterministic `c=1/4` grinder (`[EXECUTED]`).
6. `3f07402f` — `obend-oracles-e2ee` (`CAP-24..26` TEE/GPU gate, `V3/V4` TLSNotary/E2EE channel binding, exact integer `FHSDD001`/`FHQPB001` KKT) (`[EXECUTED]`).
7. `6e60a47e` — `obend-sel4-verifier` 4-PD Microkit chokepoint, disjoint CSpaces, TRNG gate, `FinCert` + `effectsRoot` (`G11` Part 2) (`[EXECUTED]`).
8. `86718dde` — `Obend/Core/{Ty,Check,Elab}` custody-bearing `mustBeLinear` enforcement (`G1`) (`[EXECUTED]`).
9. `97ae4a2b` — `Obend/Polis/CapTP.lean` 256-bit `Digest256` keys/nullifiers & nonzero handoff epoch (`G3`) (`[EXECUTED]`).
10. `89eeec8d` — `Obend/Vault/Replay.lean` open `RegisteredHandlerSpec` turn waist (`D2`) & `Obend/Consensus/Finality.lean` `IConfluent` tier relaxation (`D5`) (`[EXECUTED]`).
11. `d7a046f5` — `obend-sandbox` Seatbelt/seccomp/env confinement, `.spk` `verify_strict`, `LineChannel`, Wasm fuel, slot-AAD secrets (`G11` Part 1 / `CAP-17..23`) (`[EXECUTED]`).
12. `149f4105` — `Obend/Lower/Pancake/*` HOL4 `PanSem`, path-sensitive `CondSClk`, non-vacuous `RefinesClkPan`, `LcnfCode -> PStmt` (`G6`) (`[EXECUTED]`).
13. `d6a39879` — `Obend/Apps/SovereignDrex.lean` finality-bound `2x128b` L1 settlement, `S2` instruction domain separation, `S3` staggered windows, `S4` `0x00/0x01` Merkle framing (`G12`) (`[EXECUTED]`).

## 2. `~/dev/minidregg` (`main`) & `~/dev/zkml-research` (`dev`) Artifacts

- `Theory/Char2Degree4SumcheckHvzk.lean` (`6d976df85`), `Assurance/LightClientAndViewLens.lean` (`250094265`), `Theory/PqSelectiveBiscuit.lean` + `prover/src/pq_biscuit.rs` (`1ad98013b`), `Assurance/PerSlotKeyConfinement.lean` + `prover/src/per_slot_seal.rs` (`f6cc772a0`), `Theory/Tower256EndianBridge.lean` (`3757739ae`), `Theory/ExactKktClearingCert.lean` (`7c8d76281`), `Compiler/Tower256AlgebraicCert{,Conformance}.lean` (`965148f0b`).
- `native/darkvfhe/src/{dark_clearing.rs,threshold_custody.rs}` & `native/qwen35audit/src/unified_turn_weld.rs` (`1edd5f33`).
