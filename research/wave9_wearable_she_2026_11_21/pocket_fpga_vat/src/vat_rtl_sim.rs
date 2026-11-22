//! Synchronous cycle-level `PocketCaptpVatRtl` mirroring `Compiler/PocketFpgaCaptpVat.lean` (§1)
//! and `qsag/hardware/gf180mcu/rtl/dregg_captp_vat.sv`.

use crate::fram_powercut::PolicyDigest256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct SecretKeyRegs {
    pub k0: u64,
    pub k1: u64,
    pub k2: u64,
    pub k3: u64,
}

impl SecretKeyRegs {
    pub const ZERO: Self = Self {
        k0: 0,
        k1: 0,
        k2: 0,
        k3: 0,
    };
}

pub const GUARD_STATEFUL_FRAM: u16 = 0x0001;
pub const GUARD_PHYS_TOUCH: u16 = 0x0002;
pub const GUARD_TOF_DIST: u16 = 0x0004;
pub const GUARD_PIN_VK: u16 = 0x0008;
pub const RIGHT_ATTENUATE_BIT: u16 = 0x0008;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct CapPolicyRegs {
    pub rights_mask: u16,
    pub guards_mask: u16,
    pub max_tof_cycles: u32,
    pub epoch_floor: u32,
    pub epoch_ceil: u32,
    pub spend_limit: u32,
    pub spend_used: u32,
    pub policy_digest: PolicyDigest256,
}

/// Hardware CapTP attenuation check (`dregg_captp_vat.sv:88-94`).
pub fn attenuate_child_legal(parent: &CapPolicyRegs, child: &CapPolicyRegs) -> bool {
    ((parent.rights_mask & RIGHT_ATTENUATE_BIT) == RIGHT_ATTENUATE_BIT)
        && ((child.rights_mask & !parent.rights_mask) == 0)
        && ((child.guards_mask & parent.guards_mask) == parent.guards_mask)
        && (child.max_tof_cycles <= parent.max_tof_cycles)
        && (parent.epoch_floor <= child.epoch_floor)
        && (child.epoch_ceil <= parent.epoch_ceil)
        && (child.epoch_floor <= child.epoch_ceil)
        && (child.spend_limit <= parent.spend_limit)
        && (child.spend_limit != 0)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VatFsmState {
    Idle,
    Prepared,
    FramCommitted,
    SignArmed,
    DeadZeroized,
}

pub const SPI_OP_NOP: u8 = 0x00;
pub const SPI_OP_READ_DIAG: u8 = 0x05;
pub const SPI_OP_KEY_LOAD: u8 = 0x40;
pub const SPI_OP_PREP_SIGN: u8 = 0x41;
pub const SPI_OP_FRAM_COMMIT: u8 = 0x43;
pub const SPI_OP_TRIGGER_SIGN: u8 = 0x44;
pub const SPI_OP_ATTENUATE: u8 = 0x52;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VatCycleInput {
    pub spi_cmd_byte: u8,
    pub spi_arg_word: u64,
    pub spi_candidate_policy: CapPolicyRegs,
    pub spi_candidate_key: SecretKeyRegs,
    pub req_epoch: u32,
    pub req_spend: u32,
    pub req_right_bit: u16,
    pub measured_tof_cycles: u32,
    pub fram_readback_ok: bool,
    pub public_diag_bit: bool,
    pub msg_challenge_bit: bool,
    pub phys_touch_ack: bool,
    pub tof_within_radius: bool,
    pub tamper_canary_tripped: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VatRtlState {
    pub fsm: VatFsmState,
    pub secret_key_regs: SecretKeyRegs,
    pub key_valid: bool,
    pub tamper_latched: bool,
    pub policy: CapPolicyRegs,
    pub pending_leaf: u64,
    pub hwm_leaf: u64,
}

pub fn init_vat_rtl_state(genesis_policy: CapPolicyRegs) -> VatRtlState {
    VatRtlState {
        fsm: VatFsmState::Idle,
        secret_key_regs: SecretKeyRegs::ZERO,
        key_valid: false,
        tamper_latched: false,
        policy: genesis_policy,
        pending_leaf: 0,
        hwm_leaf: 0,
    }
}

pub fn vat_policy_invoke_legal(st: &VatRtlState, inp: &VatCycleInput) -> bool {
    let spend_sum = (st.policy.spend_used as u64) + (inp.req_spend as u64);
    st.key_valid
        && ((st.policy.rights_mask & inp.req_right_bit) == inp.req_right_bit)
        && (st.policy.epoch_floor <= inp.req_epoch)
        && (inp.req_epoch <= st.policy.epoch_ceil)
        && (spend_sum <= (st.policy.spend_limit as u64))
        && (inp.measured_tof_cycles <= st.policy.max_tof_cycles)
}

pub fn vat_sign_enable(st: &VatRtlState, inp: &VatCycleInput) -> bool {
    !st.tamper_latched
        && !inp.tamper_canary_tripped
        && st.key_valid
        && (st.fsm == VatFsmState::SignArmed)
        && vat_policy_invoke_legal(st, inp)
        && inp.phys_touch_ack
        && inp.tof_within_radius
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VatCycleOutput {
    pub vat_sign_enable: bool,
    pub spi_miso: bool,
    pub tamper_fault: bool,
}

pub fn eval_vat_rtl_output(st: &VatRtlState, inp: &VatCycleInput) -> VatCycleOutput {
    let sign_en = vat_sign_enable(st, inp);
    let key_bit0 = (st.secret_key_regs.k0 & 1) == 1;
    let sig_bit = sign_en && (key_bit0 != inp.msg_challenge_bit);
    VatCycleOutput {
        vat_sign_enable: sign_en,
        spi_miso: if sign_en { sig_bit } else { inp.public_diag_bit },
        tamper_fault: st.tamper_latched || inp.tamper_canary_tripped,
    }
}

pub fn step_vat_rtl(st: &VatRtlState, inp: &VatCycleInput) -> VatRtlState {
    if st.tamper_latched || inp.tamper_canary_tripped {
        let mut next = *st;
        next.fsm = VatFsmState::DeadZeroized;
        next.secret_key_regs = SecretKeyRegs::ZERO;
        next.key_valid = false;
        next.tamper_latched = true;
        next
    } else if inp.spi_cmd_byte == SPI_OP_KEY_LOAD {
        let mut next = *st;
        next.fsm = VatFsmState::Idle;
        if !st.key_valid {
            next.secret_key_regs = inp.spi_candidate_key;
            next.key_valid = true;
            next.policy = inp.spi_candidate_policy;
            next.policy.spend_used = 0;
        }
        next
    } else if inp.spi_cmd_byte == SPI_OP_ATTENUATE {
        let mut next = *st;
        next.fsm = VatFsmState::Idle;
        if st.key_valid && attenuate_child_legal(&st.policy, &inp.spi_candidate_policy) {
            next.policy = inp.spi_candidate_policy;
            next.policy.spend_used = st.policy.spend_used;
        }
        next
    } else if inp.spi_cmd_byte == SPI_OP_PREP_SIGN {
        let mut next = *st;
        if st.key_valid && (st.hwm_leaf <= inp.spi_arg_word) && (inp.spi_arg_word != u64::MAX) {
            next.fsm = VatFsmState::Prepared;
            next.pending_leaf = inp.spi_arg_word;
        } else {
            next.fsm = VatFsmState::Idle;
        }
        next
    } else if inp.spi_cmd_byte == SPI_OP_FRAM_COMMIT {
        let mut next = *st;
        if st.fsm == VatFsmState::Prepared && inp.fram_readback_ok && vat_policy_invoke_legal(st, inp)
        {
            next.fsm = VatFsmState::FramCommitted;
            next.hwm_leaf = st.pending_leaf.wrapping_add(1);
        } else {
            next.fsm = VatFsmState::Idle;
        }
        next
    } else if inp.spi_cmd_byte == SPI_OP_TRIGGER_SIGN {
        let mut next = *st;
        if st.fsm == VatFsmState::FramCommitted
            && vat_policy_invoke_legal(st, inp)
            && inp.phys_touch_ack
            && inp.tof_within_radius
        {
            next.fsm = VatFsmState::SignArmed;
        } else {
            next.fsm = VatFsmState::Idle;
        }
        next
    } else if st.fsm == VatFsmState::SignArmed {
        let mut next = *st;
        next.fsm = VatFsmState::Idle;
        if vat_sign_enable(st, inp) {
            next.policy.spend_used = st.policy.spend_used.wrapping_add(inp.req_spend);
        }
        next
    } else {
        let mut next = *st;
        next.fsm = VatFsmState::Idle;
        next
    }
}

pub fn run_vat_rtl_trace(
    mut st: VatRtlState,
    trace: &[VatCycleInput],
) -> (Vec<VatCycleOutput>, VatRtlState) {
    let mut outs = Vec::with_capacity(trace.len());
    for inp in trace {
        outs.push(eval_vat_rtl_output(&st, inp));
        st = step_vat_rtl(&st, inp);
    }
    (outs, st)
}

/// `#tooth` software-CSR override model matching `brokenCsrSignEnable` in Lean.
pub fn broken_csr_sign_enable(
    csr_presence_override: bool,
    st: &VatRtlState,
    inp: &VatCycleInput,
) -> bool {
    !st.tamper_latched
        && !inp.tamper_canary_tripped
        && st.key_valid
        && (st.fsm == VatFsmState::SignArmed)
        && (inp.phys_touch_ack || csr_presence_override)
        && (inp.tof_within_radius || csr_presence_override)
}
