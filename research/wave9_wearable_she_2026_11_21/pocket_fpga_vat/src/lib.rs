#![forbid(unsafe_code)]
#![deny(warnings)]

//! Wearable SHE Organ #6 (Gap #1 Pocket-FPGA Companion):
//! Cycle-exact `Dregg-180` `dregg_captp_vat` RTL cosimulator, bit-tear-safe 2-slot SPI-FRAM
//! monotone `Cut-the-Hash` leaf counter, and FABulous-style `4x2` LUT4/FF + switch-matrix PIP
//! bitstream readback & Trojan-path verifier mirroring `Compiler/PocketFpgaCaptpVat.lean`.

pub mod bitstream_readback;
pub mod fram_powercut;
pub mod vat_rtl_sim;

pub use bitstream_readback::{
    check_no_unauthorized_secret_pips, check_semantic_miso_non_interference,
    eval_fabric_sign_enable, eval_fabric_spi_miso, eval_vat_core_sign_enable,
    eval_vat_core_spi_miso, pack_tile_cfg_word, run_fabric_trace, run_vat_core_rtl_trace,
    step_fabric_state, step_vat_core_rtl, trojan_lut_bitstream, trojan_pip_bitstream,
    vat_golden_bitstream, vat_golden_cert, vat_ordered_grid, verify_vat_fabric_readback,
    BelCellSpec, PipSource, SmMux4, VatBitstream, VatFabricGrid, VatFabricInputs, VatFabricState,
    VatReadbackCert,
};
pub use fram_powercut::{
    bits512_bit, boot_resync_standby, broken_commit_first_encode, broken_commit_first_recover,
    compute_fram_crc_tag, decode_fram_slot, encode_fram_slot, fram_slot_valid, genesis_dual_fram,
    mk_valid_fram_record, recover_dual_fram, run_fram_events, select_standby_slot, step_fram_event,
    tear_bits512, tear_word64, write_standby_with_power_cut, Bits512, DualSlotFram,
    FramPowerEvent, FramSlotRecord, PolicyDigest256, SpiFramDevice,
};
pub use vat_rtl_sim::{
    attenuate_child_legal, broken_csr_sign_enable, eval_vat_rtl_output, init_vat_rtl_state,
    run_vat_rtl_trace, step_vat_rtl, vat_policy_invoke_legal, vat_sign_enable, CapPolicyRegs,
    SecretKeyRegs, VatCycleInput, VatCycleOutput, VatFsmState, VatRtlState, GUARD_PIN_VK,
    GUARD_PHYS_TOUCH, GUARD_STATEFUL_FRAM, GUARD_TOF_DIST, RIGHT_ATTENUATE_BIT, SPI_OP_ATTENUATE,
    SPI_OP_FRAM_COMMIT, SPI_OP_KEY_LOAD, SPI_OP_NOP, SPI_OP_PREP_SIGN, SPI_OP_READ_DIAG,
    SPI_OP_TRIGGER_SIGN,
};

/// Golden 256-bit policy digest matching `goldenPolicyDigest` in `PocketFpgaCaptpVat.lean`.
pub const GOLDEN_POLICY_DIGEST: PolicyDigest256 = PolicyDigest256 {
    d0: 0x0102_0304_0506_0708,
    d1: 0x1112_1314_1516_1718,
    d2: 0x2122_2324_2526_2728,
    d3: 0x3132_3334_3536_3738,
};
