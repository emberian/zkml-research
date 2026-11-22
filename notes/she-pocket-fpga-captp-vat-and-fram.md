# Wave-9 Organ #6 (Gap #1): Pocket-FPGA `dregg_captp_vat` Companion, Any-Bit Power-Cut 2-Slot SPI-FRAM Counter, & LUT4/PIP Bitstream Readback Verifier

**Date:** 2026-11-21 · **Lane:** `she-pocket-fpga-vat` · **Scope:** *Rainbows End* Wearable SHE Gap #1 Immediate Hardware Companion
**Status:** Verified end-to-end (`exit 0`, `0` warnings on Lean `v4.35.0` kernel + `check-import-boundary.sh` + `--release` Rust with `RUSTFLAGS="-D warnings"` and `#![forbid(unsafe_code)]`) (`[EXECUTED]`).
**Metered search ledger:** `kagi.py`: `0`; `scry.py`: `0`; `eprint.iacr.org`: `0` (`[EXECUTED]`).

## 1. Donor Silicon & Fabric Architecture (`[SOURCE]`, `[DERIVED]`)

- **`Dregg-180` (`QSAG-NI-180`) RTL Provenance:** While `Dregg-180` awaits Run-3 wafer fabrication ([README.md](file:///Users/ember/dev/qsag/hardware/gf180mcu/README.md#L462-L469)), a wearable ARM64 SoC needs an immediate off-SoC COTS Pocket-FPGA + 8-pin SPI-FRAM companion enforcing the same physical invariants (`[SOURCE, DERIVED]`):
  1. Hardware CapTP capability membrane (`pw_w1`, `pw_w2`, `p_spend`, `child_word_ok` monotone attenuation, `invoke_legal`) from [dregg_captp_vat.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/dregg_captp_vat.sv#L58-L123) (`[SOURCE]`).
  2. Write-ahead 2-slot SPI-FRAM monotone `Cut-the-Hash` leaf counter (`WREN 0x06`, `WRITE 0x02`, `READ 0x03`, read-after-write `rcmp`) from [qsag_anchor_spi.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/qsag_anchor_spi.sv#L1-L115) and `S_CA0..S_CA3` in [qsag_wire_engine.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/qsag_wire_engine.sv#L1728-L1738) (`[SOURCE]`).
  3. Dedicated physical presence + Vernier ToF proximity wires ([dregg_distance_tdc.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/dregg_distance_tdc.sv#L1-L90)) and 1-clock emergency secret zeroization ([dregg_shield_canaries.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/dregg_shield_canaries.sv#L1-L149), [qsag_sponge.sv](file:///Users/ember/dev/qsag/hardware/gf180mcu/rtl/qsag_sponge.sv#L9-L20)) (`[SOURCE]`).
- **FABulous-Style LUT4/PIP Readback Model:** Adapts the `LUT4c_frame_config_dffesr` (`INIT[15:0]`, `FF`, `SR`) and `cus_mux41` switch-matrix PIP semantics of [Tile.lean](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabulous/Tile.lean#L36-L144) and [Readback.lean](file:///Users/ember/dev/obend/lean/Obend/Hardware/Fabulous/Readback.lean#L64-L154) to inspect JTAG/SPI bitstreams read back from the Pocket-FPGA (`[SOURCE, DERIVED]`).

## 2. Lean `v4.35.0` Formalization (`0 sorry`, `0` custom `axiom`, `0 native_decide`)

[PocketFpgaCaptpVat.lean](file:///Users/ember/dev/minidregg/Compiler/PocketFpgaCaptpVat.lean) (`873` lines `< 950`, `12` `#guard_msgs`-pinned `#print axioms`, `Compiler/` tier) proves (`[DERIVED, EXECUTED]`):

1. **Hardware Physical-Presence, ToF Wire Gate, & 1-Cycle Zeroization (`§1`):**
   - `compromised_host_cannot_sign_without_touch_and_tof`: for **any** initial state `st₀` and **any** arbitrary trace of malicious SPI commands/words injected by a root-compromised ARM64 OS, whenever `physTouchAck = false ∨ tofWithinRadius = false ∨ tamperCanaryTripped = true`, `vatSignEnable` is identically `false` on every cycle.
   - `tamper_canary_zeroizes_keys_in_one_cycle_and_locks_forever`: tripping `tamperCanaryTripped` drops `vatSignEnable` in `0` cycles, clears all 256 bits of `secretKeyRegs` to `zeroSecretKey` in `1` clock cycle, and locks signing off permanently across all future traces.
   - `captp_attenuation_monotone_non_amplifying`: `attenuateChildLegal` forbids rights amplification, stripping of `G_STATEFUL`/`G_PHYS_TOUCH`/`G_TOF_DIST` guards, `[epochFloor, epochCeil]` widening, `maxTofCycles` expansion, or `spendLimit` inflation.
   - `#tooth` `tooth_software_csr_touch_override_allows_forged_sign` (`[REFUTED: host-writable CSR presence flags]`): proves software-writable CSR presence bits allow signing with `physTouchAck = false ∧ tofWithinRadius = false`.
2. **Any-Bit Power-Cut Atomic 2-Slot SPI-FRAM Monotone Counter (`§2`):**
   - `512`-bit (`64`-byte) slot layout `policyDigest[0..255] || leafIdx[256..319] || spendUsed[320..383] || epochSeq[384..447] || crcTag[448..511]` (`CRC-64-ECMA`, IV `"DRG1FRAM"`). Placing `leafIdx` (`w4`) strictly before `epochSeq` (`w6`) and `crcTag` (`w7`) makes bit-prefix tearing (`bits512Bit_tearBits512`) **unconditionally** monotone (`0` CRC-collision assumptions!): for `cutBit ≤ 384`, `standby.epochSeq` is untouched (`< active.epochSeq`); for `cutBit > 384`, `standby.leafIdx` is already `100%` written (`= nextRec.leafIdx ≥ active.leafIdx`).
   - `fram_power_cut_any_bit_monotone_safe` & `no_leaf_reuse_across_arbitrary_power_cuts`: cutting power at **any** bit `0..512` never bricks recovery (`isSome`) and guarantees strictly increasing (`List.Pairwise (· < ·)`), duplicate-free released `Cut-the-Hash` leaves across arbitrary schedules of completed signings and mid-bit power cuts.
   - `#tooth` `tooth_single_slot_overwrite_bricks_on_mid_write_power_cut` (`[REFUTED: 1-slot in-place FRAM write]`, bricks at bit `288`) & `tooth_commit_before_payload_permits_leaf_rollback` (`[REFUTED: commit/epoch-before-leaf layout]`, rolls `leafIdx` backward from `10` to `3` at bit `64`).
3. **Inspectable Pocket-FPGA Bitstream Readback & Anti-Trojan Non-Interference (`§3`):**
   - `verifyVatFabricReadback_sound`: on the `4 × 2` (`8`-tile, `512`-bit bitstream) `LUT4c_dffesr` + `cus_mux41` PIP fabric, acceptance proves (a) multi-cycle trace equivalence (`runFabricTrace = runVatCoreRtlTrace`), (b) physical touch + ToF pad gating, and (c) **zero covert Trojan key paths** — both graph-level PIP quarantine (`checkNoUnauthorizedSecretPips`) and semantic `spi_miso` non-interference (`evalFabricSpiMiso ... k₁ = evalFabricSpiMiso ... k₂`) whenever `tamperCanary` or `¬vatSignEnable` holds.
   - `#tooth` `tooth_trojan_pip_exfiltrates_key_and_is_rejected` (2-MUX PIP reroute through spare tile `X3Y0` leaks `secretKeyReg` during `READ_DIAG`) & `tooth_trojan_lut_init_leaks_key_and_is_rejected` (all PIPs clean, mutated `LUT4` `INIT` leaks `secretKeyReg` when `¬signEnable`, proving PIP-only checks without `INIT` verification are insufficient).

## 3. Standalone Pure-Rust Cosimulator & Fault Fuzzer (`[EXECUTED]`)

Implemented in [pocket_fpga_vat](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/src/lib.rs) ([vat_rtl_sim.rs](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/src/vat_rtl_sim.rs), [fram_powercut.rs](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/src/fram_powercut.rs), [bitstream_readback.rs](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/src/bitstream_readback.rs)) and verified in [conformance_and_faults.rs](file:///Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/tests/conformance_and_faults.rs) (`0` external crates, `#![forbid(unsafe_code)]`):

| Verification Gate (`--release`, `RUSTFLAGS="-D warnings"`) | Result (`[EXECUTED]`) |
| --- | --- |
| Live Lean `v4.35.0` ↔ Rust golden JSON parity (`CRC-64`, `8` bitstream words, `4` Trojan words) | `14 / 14` exact `u64` matches |
| Root-compromised host SPI fuzzer (`10,000` random cycles without `touch ∧ ToF`) | `0 / 10,000` sign enables; `0` MISO leaks |
| Exhaustive FRAM tear sweep (`0..=512` frame bits × `2` dirs + `0..=544` SPI `SCK` edges + `5,000`-op chain) | `0` bricked boots; `0` leaf reuses |
| Fabric cosim (`8,192` `(state, pin)` points + `256`-cycle trace + `512 / 512` 1-bit flips + `2` Trojans) | `100%` RTL match; `514 / 514` bad bitstreams refused |

## 4. Remaining Hardware Seam & Reproduction (`[OPEN]`, `[EXECUTED]`)

- **Physical Board Seam (`[OPEN]`):** Readback proves gate/PIP configuration equivalence and `spi_miso` logical non-interference; physical DPA/EM leakage across COTS FPGA routing capacitance and board-level desoldering of the 8-pin SPI-FRAM (`MB85RS64V`) remain physical-layer obligations until `Dregg-180` silicon lands (`[OPEN]`).
- **Reproduce:** `bash /Users/ember/dev/zkml-research/research/wave9_wearable_she_2026_11_21/pocket_fpga_vat/build_and_verify.sh` (`[EXECUTED]`).
- **Proposed maintainer folds (unmodified here):** add `import Compiler.PocketFpgaCaptpVat` to `minidregg/Compiler.lean`, index this note in `notes/README.md`, and record Gap #1 Pocket-FPGA companion verification in `docs/VERDICTS.md`.
