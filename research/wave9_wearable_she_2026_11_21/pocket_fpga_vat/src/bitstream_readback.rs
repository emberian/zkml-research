//! Inspectable Pocket-FPGA `4x2` (`8`-tile) LUT4/FF (`LUT4c_frame_config_dffesr`) + Switch-Matrix
//! PIP bitstream readback verifier & Trojan-PIP / Trojan-LUT detector mirroring
//! `Compiler/PocketFpgaCaptpVat.lean` (§3) and `Obend.Hardware.Fabulous.{Tile,Net,Readback}`.

use crate::fram_powercut::Bits512;

pub type VatBitstream = Bits512;

pub fn mux2b(s: bool, x0: bool, x1: bool) -> bool {
    if s { x1 } else { x0 }
}

pub fn eval_lut4(init: u16, i0: bool, i1: bool, i2: bool, i3: bool) -> bool {
    let idx = (i0 as usize) + 2 * (i1 as usize) + 4 * (i2 as usize) + 8 * (i3 as usize);
    ((init >> idx) & 1) == 1
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PipSource {
    Const(bool),
    PadIn(usize),
    BelOut(usize, usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SmMux4 {
    pub in0: PipSource,
    pub in1: PipSource,
    pub in2: PipSource,
    pub in3: PipSource,
    pub cfg_tile: usize,
    pub cfg_bit_lo: usize,
}

impl SmMux4 {
    pub const fn const_mux(tile: usize, bit_lo: usize, b: bool) -> Self {
        Self {
            in0: PipSource::Const(b),
            in1: PipSource::Const(false),
            in2: PipSource::Const(false),
            in3: PipSource::Const(false),
            cfg_tile: tile,
            cfg_bit_lo: bit_lo,
        }
    }
}

pub fn bs_bit(bs: &VatBitstream, tile_idx: usize, bit_offset: usize) -> bool {
    if bit_offset >= 64 {
        false
    } else {
        ((bs.word(tile_idx) >> bit_offset) & 1) == 1
    }
}

pub fn sm_mux4_sel(m: &SmMux4, bs: &VatBitstream) -> usize {
    let b0 = bs_bit(bs, m.cfg_tile, m.cfg_bit_lo) as usize;
    let b1 = bs_bit(bs, m.cfg_tile, m.cfg_bit_lo + 1) as usize;
    b0 + 2 * b1
}

pub fn sm_mux4_selected_src(m: &SmMux4, bs: &VatBitstream) -> PipSource {
    match sm_mux4_sel(m, bs) {
        0 => m.in0,
        1 => m.in1,
        2 => m.in2,
        _ => m.in3,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BelCellSpec {
    pub tile_idx: usize,
    pub bel_idx: usize,
    pub bel_cfg_base: usize,
    pub mux_i0: SmMux4,
    pub mux_i1: SmMux4,
    pub mux_i2: SmMux4,
    pub mux_i3: SmMux4,
    pub mux_en: SmMux4,
    pub mux_sr: SmMux4,
}

pub fn bel_init_bits(c: &BelCellSpec, bs: &VatBitstream) -> u16 {
    ((bs.word(c.tile_idx) >> c.bel_cfg_base) & 0xFFFF) as u16
}

pub fn bel_is_flop(c: &BelCellSpec, bs: &VatBitstream) -> bool {
    bs_bit(bs, c.tile_idx, c.bel_cfg_base + 16)
}

pub fn bel_sr_val(c: &BelCellSpec, bs: &VatBitstream) -> bool {
    bs_bit(bs, c.tile_idx, c.bel_cfg_base + 17)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VatFabricGrid {
    pub bels: Vec<BelCellSpec>,
    pub sign_enable_mux: SmMux4,
    pub spi_miso_mux: SmMux4,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct VatFabricInputs {
    pub tamper_canary_tripped: bool,
    pub phys_touch_ack: bool,
    pub tof_within_radius: bool,
    pub spi_key_load_cmd: bool,
    pub spi_key_bit_in: bool,
    pub spi_sign_req_cmd: bool,
    pub policy_and_fram_ok: bool,
    pub msg_challenge_bit: bool,
    pub public_diag_bit: bool,
}

impl VatFabricInputs {
    pub fn from_mask(mask: u16) -> Self {
        Self {
            tamper_canary_tripped: ((mask >> 0) & 1) == 1,
            phys_touch_ack: ((mask >> 1) & 1) == 1,
            tof_within_radius: ((mask >> 2) & 1) == 1,
            spi_key_load_cmd: ((mask >> 3) & 1) == 1,
            spi_key_bit_in: ((mask >> 4) & 1) == 1,
            spi_sign_req_cmd: ((mask >> 5) & 1) == 1,
            policy_and_fram_ok: ((mask >> 6) & 1) == 1,
            msg_challenge_bit: ((mask >> 7) & 1) == 1,
            public_diag_bit: ((mask >> 8) & 1) == 1,
        }
    }

    pub fn pin_at(&self, pin: usize) -> bool {
        match pin {
            0 => self.tamper_canary_tripped,
            1 => self.phys_touch_ack,
            2 => self.tof_within_radius,
            3 => self.spi_key_load_cmd,
            4 => self.spi_key_bit_in,
            5 => self.spi_sign_req_cmd,
            6 => self.policy_and_fram_ok,
            7 => self.msg_challenge_bit,
            8 => self.public_diag_bit,
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct VatFabricState {
    pub tamper_latched: bool,
    pub key_valid: bool,
    pub secret_key_reg: bool,
    pub sign_armed: bool,
}

impl VatFabricState {
    pub fn from_mask(mask: u8) -> Self {
        Self {
            tamper_latched: ((mask >> 0) & 1) == 1,
            key_valid: ((mask >> 1) & 1) == 1,
            secret_key_reg: ((mask >> 2) & 1) == 1,
            sign_armed: ((mask >> 3) & 1) == 1,
        }
    }

    pub fn flop_at(&self, tile_idx: usize, bel_idx: usize) -> bool {
        match (tile_idx, bel_idx) {
            (0, 0) => self.tamper_latched,
            (0, 1) => self.key_valid,
            (1, 0) => self.secret_key_reg,
            (1, 1) => self.sign_armed,
            _ => false,
        }
    }
}

pub fn step_vat_core_rtl(st: &VatFabricState, inp: &VatFabricInputs) -> VatFabricState {
    let tamper_any = st.tamper_latched || inp.tamper_canary_tripped;
    let presence_ok = inp.phys_touch_ack && inp.tof_within_radius && !tamper_any;
    VatFabricState {
        tamper_latched: tamper_any,
        key_valid: if tamper_any {
            false
        } else {
            st.key_valid || inp.spi_key_load_cmd
        },
        secret_key_reg: if tamper_any {
            false
        } else if !st.key_valid && inp.spi_key_load_cmd {
            inp.spi_key_bit_in
        } else {
            st.secret_key_reg
        },
        sign_armed: !tamper_any
            && st.key_valid
            && inp.spi_sign_req_cmd
            && inp.policy_and_fram_ok
            && presence_ok,
    }
}

pub fn eval_vat_core_sign_enable(st: &VatFabricState, inp: &VatFabricInputs) -> bool {
    let tamper_any = st.tamper_latched || inp.tamper_canary_tripped;
    let presence_ok = inp.phys_touch_ack && inp.tof_within_radius && !tamper_any;
    st.sign_armed && st.key_valid && presence_ok
}

pub fn eval_vat_core_spi_miso(st: &VatFabricState, inp: &VatFabricInputs) -> bool {
    let sign_en = eval_vat_core_sign_enable(st, inp);
    let sig_bit = sign_en && (st.secret_key_reg != inp.msg_challenge_bit);
    if sign_en { sig_bit } else { inp.public_diag_bit }
}

pub fn run_vat_core_rtl_trace(
    mut st: VatFabricState,
    trace: &[VatFabricInputs],
) -> (Vec<(bool, bool)>, VatFabricState) {
    let mut outs = Vec::with_capacity(trace.len());
    for inp in trace {
        outs.push((
            eval_vat_core_sign_enable(&st, inp),
            eval_vat_core_spi_miso(&st, inp),
        ));
        st = step_vat_core_rtl(&st, inp);
    }
    (outs, st)
}

fn eval_pip_source(inp: &VatFabricInputs, bel_vals: &[((usize, usize), bool)], src: PipSource) -> bool {
    match src {
        PipSource::Const(b) => b,
        PipSource::PadIn(p) => inp.pin_at(p),
        PipSource::BelOut(t, b) => bel_vals
            .iter()
            .find(|((ti, bi), _)| *ti == t && *bi == b)
            .map(|(_, v)| *v)
            .unwrap_or(false),
    }
}

fn eval_sm_mux4(
    m: &SmMux4,
    bs: &VatBitstream,
    inp: &VatFabricInputs,
    bel_vals: &[((usize, usize), bool)],
) -> bool {
    eval_pip_source(inp, bel_vals, sm_mux4_selected_src(m, bs))
}

pub fn eval_fabric_bels(
    bs: &VatBitstream,
    st: &VatFabricState,
    inp: &VatFabricInputs,
    bels: &[BelCellSpec],
) -> (Vec<((usize, usize), bool)>, Vec<((usize, usize), bool)>) {
    // Synchronous registered flip-flop Q outputs are valid at the start of the cycle;
    // combinational BELs append their wire outputs in topological order.
    let mut outs = Vec::with_capacity(4 + bels.len());
    outs.push(((0, 0), st.tamper_latched));
    outs.push(((0, 1), st.key_valid));
    outs.push(((1, 0), st.secret_key_reg));
    outs.push(((1, 1), st.sign_armed));
    let mut next_flops = Vec::with_capacity(bels.len());
    for c in bels {
        let v0 = eval_sm_mux4(&c.mux_i0, bs, inp, &outs);
        let v1 = eval_sm_mux4(&c.mux_i1, bs, inp, &outs);
        let v2 = eval_sm_mux4(&c.mux_i2, bs, inp, &outs);
        let v3 = eval_sm_mux4(&c.mux_i3, bs, inp, &outs);
        let en = eval_sm_mux4(&c.mux_en, bs, inp, &outs);
        let sr = eval_sm_mux4(&c.mux_sr, bs, inp, &outs);
        let lut_out = eval_lut4(bel_init_bits(c, bs), v0, v1, v2, v3);
        let q_cur = st.flop_at(c.tile_idx, c.bel_idx);
        let wire_o = if bel_is_flop(c, bs) { q_cur } else { lut_out };
        let q_next = mux2b(en, q_cur, mux2b(sr, lut_out, bel_sr_val(c, bs)));
        if !bel_is_flop(c, bs) {
            outs.push(((c.tile_idx, c.bel_idx), wire_o));
        }
        next_flops.push(((c.tile_idx, c.bel_idx), q_next));
    }
    (outs, next_flops)
}

pub fn eval_fabric_sign_enable(
    grid: &VatFabricGrid,
    bs: &VatBitstream,
    st: &VatFabricState,
    inp: &VatFabricInputs,
) -> bool {
    let (outs, _) = eval_fabric_bels(bs, st, inp, &grid.bels);
    eval_sm_mux4(&grid.sign_enable_mux, bs, inp, &outs)
}

pub fn eval_fabric_spi_miso(
    grid: &VatFabricGrid,
    bs: &VatBitstream,
    st: &VatFabricState,
    inp: &VatFabricInputs,
) -> bool {
    let (outs, _) = eval_fabric_bels(bs, st, inp, &grid.bels);
    eval_sm_mux4(&grid.spi_miso_mux, bs, inp, &outs)
}

fn lookup_next_flop(flops: &[((usize, usize), bool)], t: usize, b: usize) -> bool {
    flops
        .iter()
        .find(|((ti, bi), _)| *ti == t && *bi == b)
        .map(|(_, v)| *v)
        .unwrap_or(false)
}

pub fn step_fabric_state(
    grid: &VatFabricGrid,
    bs: &VatBitstream,
    st: &VatFabricState,
    inp: &VatFabricInputs,
) -> VatFabricState {
    let (_, next_flops) = eval_fabric_bels(bs, st, inp, &grid.bels);
    VatFabricState {
        tamper_latched: lookup_next_flop(&next_flops, 0, 0),
        key_valid: lookup_next_flop(&next_flops, 0, 1),
        secret_key_reg: lookup_next_flop(&next_flops, 1, 0),
        sign_armed: lookup_next_flop(&next_flops, 1, 1),
    }
}

pub fn run_fabric_trace(
    grid: &VatFabricGrid,
    bs: &VatBitstream,
    mut st: VatFabricState,
    trace: &[VatFabricInputs],
) -> (Vec<(bool, bool)>, VatFabricState) {
    let mut outs = Vec::with_capacity(trace.len());
    for inp in trace {
        outs.push((
            eval_fabric_sign_enable(grid, bs, &st, inp),
            eval_fabric_spi_miso(grid, bs, &st, inp),
        ));
        st = step_fabric_state(grid, bs, &st, inp);
    }
    (outs, st)
}

fn mux2(a: PipSource, b: PipSource, tile: usize, bit_lo: usize) -> SmMux4 {
    SmMux4 {
        in0: a,
        in1: b,
        in2: PipSource::Const(false),
        in3: PipSource::Const(false),
        cfg_tile: tile,
        cfg_bit_lo: bit_lo,
    }
}

pub fn vat_ordered_grid() -> VatFabricGrid {
    use PipSource::{BelOut, Const, PadIn};
    let c00 = BelCellSpec {
        tile_idx: 0,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: mux2(Const(false), BelOut(0, 0), 0, 36),
        mux_i1: mux2(Const(false), PadIn(0), 0, 38),
        mux_i2: SmMux4::const_mux(0, 40, false),
        mux_i3: SmMux4::const_mux(0, 42, false),
        mux_en: SmMux4::const_mux(0, 44, true),
        mux_sr: SmMux4::const_mux(0, 46, false),
    };
    let c20 = BelCellSpec {
        tile_idx: 2,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: mux2(Const(false), BelOut(0, 0), 2, 36),
        mux_i1: mux2(Const(false), PadIn(0), 2, 38),
        mux_i2: SmMux4::const_mux(2, 40, false),
        mux_i3: SmMux4::const_mux(2, 42, false),
        mux_en: SmMux4::const_mux(2, 44, false),
        mux_sr: SmMux4::const_mux(2, 46, false),
    };
    let c21 = BelCellSpec {
        tile_idx: 2,
        bel_idx: 1,
        bel_cfg_base: 18,
        mux_i0: mux2(Const(false), PadIn(1), 2, 48),
        mux_i1: mux2(Const(false), PadIn(2), 2, 50),
        mux_i2: mux2(Const(false), BelOut(2, 0), 2, 52),
        mux_i3: SmMux4::const_mux(2, 54, false),
        mux_en: SmMux4::const_mux(2, 56, false),
        mux_sr: SmMux4::const_mux(2, 58, false),
    };
    let c01 = BelCellSpec {
        tile_idx: 0,
        bel_idx: 1,
        bel_cfg_base: 18,
        mux_i0: mux2(Const(false), BelOut(0, 1), 0, 48),
        mux_i1: mux2(Const(false), PadIn(3), 0, 50),
        mux_i2: SmMux4::const_mux(0, 52, false),
        mux_i3: SmMux4::const_mux(0, 54, false),
        mux_en: SmMux4::const_mux(0, 56, true),
        mux_sr: mux2(Const(false), BelOut(2, 0), 0, 58),
    };
    let c10 = BelCellSpec {
        tile_idx: 1,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: mux2(Const(false), BelOut(1, 0), 1, 36),
        mux_i1: mux2(Const(false), BelOut(0, 1), 1, 38),
        mux_i2: mux2(Const(false), PadIn(3), 1, 40),
        mux_i3: mux2(Const(false), PadIn(4), 1, 42),
        mux_en: SmMux4::const_mux(1, 44, true),
        mux_sr: mux2(Const(false), BelOut(2, 0), 1, 46),
    };
    let c11 = BelCellSpec {
        tile_idx: 1,
        bel_idx: 1,
        bel_cfg_base: 18,
        mux_i0: mux2(Const(false), BelOut(0, 1), 1, 48),
        mux_i1: mux2(Const(false), PadIn(5), 1, 50),
        mux_i2: mux2(Const(false), PadIn(6), 1, 52),
        mux_i3: mux2(Const(false), BelOut(2, 1), 1, 54),
        mux_en: SmMux4::const_mux(1, 56, true),
        mux_sr: mux2(Const(false), BelOut(2, 0), 1, 58),
    };
    let c30 = BelCellSpec {
        tile_idx: 3,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: SmMux4 {
            in0: Const(false),
            in1: PadIn(8),
            in2: BelOut(1, 0),
            in3: Const(false),
            cfg_tile: 3,
            cfg_bit_lo: 36,
        },
        mux_i1: SmMux4::const_mux(3, 38, false),
        mux_i2: SmMux4::const_mux(3, 40, false),
        mux_i3: SmMux4::const_mux(3, 42, false),
        mux_en: SmMux4::const_mux(3, 44, false),
        mux_sr: SmMux4::const_mux(3, 46, false),
    };
    let c60 = BelCellSpec {
        tile_idx: 6,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: mux2(Const(false), BelOut(1, 1), 6, 36),
        mux_i1: mux2(Const(false), BelOut(0, 1), 6, 38),
        mux_i2: mux2(Const(false), BelOut(2, 1), 6, 40),
        mux_i3: SmMux4::const_mux(6, 42, false),
        mux_en: SmMux4::const_mux(6, 44, false),
        mux_sr: SmMux4::const_mux(6, 46, false),
    };
    let c61 = BelCellSpec {
        tile_idx: 6,
        bel_idx: 1,
        bel_cfg_base: 18,
        mux_i0: mux2(Const(false), BelOut(6, 0), 6, 48),
        mux_i1: mux2(Const(false), BelOut(1, 0), 6, 50),
        mux_i2: mux2(Const(false), PadIn(7), 6, 52),
        mux_i3: SmMux4::const_mux(6, 54, false),
        mux_en: SmMux4::const_mux(6, 56, false),
        mux_sr: SmMux4::const_mux(6, 58, false),
    };
    let c70 = BelCellSpec {
        tile_idx: 7,
        bel_idx: 0,
        bel_cfg_base: 0,
        mux_i0: mux2(Const(false), BelOut(6, 0), 7, 36),
        mux_i1: mux2(Const(false), BelOut(6, 1), 7, 38),
        mux_i2: SmMux4 {
            in0: Const(false),
            in1: PadIn(8),
            in2: BelOut(3, 0),
            in3: Const(false),
            cfg_tile: 7,
            cfg_bit_lo: 40,
        },
        mux_i3: SmMux4::const_mux(7, 42, false),
        mux_en: SmMux4::const_mux(7, 44, false),
        mux_sr: SmMux4::const_mux(7, 46, false),
    };
    VatFabricGrid {
        bels: vec![c00, c20, c21, c01, c10, c11, c30, c60, c61, c70],
        sign_enable_mux: mux2(Const(false), BelOut(6, 0), 7, 48),
        spi_miso_mux: SmMux4 {
            in0: Const(false),
            in1: BelOut(7, 0),
            in2: BelOut(3, 0),
            in3: Const(false),
            cfg_tile: 7,
            cfg_bit_lo: 50,
        },
    }
}

pub const fn pack_tile_cfg_word(
    la_init: u16,
    la_flop: bool,
    la_sr: bool,
    lb_init: u16,
    lb_flop: bool,
    lb_sr: bool,
    sm_mask: u32,
) -> u64 {
    (la_init as u64)
        | ((la_flop as u64) << 16)
        | ((la_sr as u64) << 17)
        | ((lb_init as u64) << 18)
        | ((lb_flop as u64) << 34)
        | ((lb_sr as u64) << 35)
        | (((sm_mask & 0x0FFF_FFFF) as u64) << 36)
}

pub const fn vat_golden_bitstream() -> VatBitstream {
    Bits512 {
        w: [
            pack_tile_cfg_word(0xEEEE, true, false, 0xEEEE, true, false, 0x0405005),
            pack_tile_cfg_word(0xBA8A, true, false, 0x8000, true, false, 0x0455455),
            pack_tile_cfg_word(0xEEEE, false, false, 0x0808, false, false, 0x0015005),
            0,
            0,
            0,
            pack_tile_cfg_word(0x8080, false, false, 0x2828, false, false, 0x0015015),
            pack_tile_cfg_word(0xD8D8, false, false, 0x0000, false, false, 0x0005015),
        ],
    }
}

pub const fn trojan_pip_bitstream() -> VatBitstream {
    let mut bs = vat_golden_bitstream();
    bs.w[3] = pack_tile_cfg_word(0xAAAA, false, false, 0x0000, false, false, 0x0000002);
    bs.w[7] = pack_tile_cfg_word(0xD8D8, false, false, 0x0000, false, false, 0x0009015);
    bs
}

pub const fn trojan_lut_bitstream() -> VatBitstream {
    let mut bs = vat_golden_bitstream();
    bs.w[6] = pack_tile_cfg_word(0x8080, false, false, 0xCCCC, false, false, 0x0015015);
    bs.w[7] = pack_tile_cfg_word(0xCCCC, false, false, 0x0000, false, false, 0x0005015);
    bs
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VatReadbackCert {
    pub expected_bitstream: VatBitstream,
    pub secret_bel: (usize, usize),
}

pub const fn vat_golden_cert() -> VatReadbackCert {
    VatReadbackCert {
        expected_bitstream: vat_golden_bitstream(),
        secret_bel: (1, 0),
    }
}

pub fn mux_reads_secret(secret_bel: (usize, usize), m: &SmMux4, bs: &VatBitstream) -> bool {
    sm_mux4_selected_src(m, bs) == PipSource::BelOut(secret_bel.0, secret_bel.1)
}

pub fn check_no_unauthorized_secret_pips(
    grid: &VatFabricGrid,
    secret_bel: (usize, usize),
    bs: &VatBitstream,
) -> bool {
    let bel_ok = grid.bels.iter().all(|c| {
        let allow_i0 = c.tile_idx == 1 && c.bel_idx == 0;
        let allow_i1 = c.tile_idx == 6 && c.bel_idx == 1;
        (!mux_reads_secret(secret_bel, &c.mux_i0, bs) || allow_i0)
            && (!mux_reads_secret(secret_bel, &c.mux_i1, bs) || allow_i1)
            && !mux_reads_secret(secret_bel, &c.mux_i2, bs)
            && !mux_reads_secret(secret_bel, &c.mux_i3, bs)
            && !mux_reads_secret(secret_bel, &c.mux_en, bs)
            && !mux_reads_secret(secret_bel, &c.mux_sr, bs)
    });
    bel_ok
        && !mux_reads_secret(secret_bel, &grid.sign_enable_mux, bs)
        && !mux_reads_secret(secret_bel, &grid.spi_miso_mux, bs)
}

/// Exhaustive semantic `spi_miso` non-interference check across all `8` non-secret state combinations
/// and `512` input pin combinations whenever `tamper_canary`, `tamper_latched`, or `!sign_enable` holds.
pub fn check_semantic_miso_non_interference(grid: &VatFabricGrid, bs: &VatBitstream) -> bool {
    for st_mask in 0u8..16 {
        let st_base = VatFabricState::from_mask(st_mask);
        let mut st_k0 = st_base;
        st_k0.secret_key_reg = false;
        let mut st_k1 = st_base;
        st_k1.secret_key_reg = true;
        for inp_mask in 0u16..512 {
            let inp = VatFabricInputs::from_mask(inp_mask);
            let sign_en = eval_fabric_sign_enable(grid, bs, &st_base, &inp);
            if inp.tamper_canary_tripped || st_base.tamper_latched || !sign_en {
                let miso0 = eval_fabric_spi_miso(grid, bs, &st_k0, &inp);
                let miso1 = eval_fabric_spi_miso(grid, bs, &st_k1, &inp);
                if miso0 != miso1 {
                    return false;
                }
            }
        }
    }
    true
}

pub fn verify_vat_fabric_readback(
    grid: &VatFabricGrid,
    cert: &VatReadbackCert,
    bs: &VatBitstream,
) -> bool {
    (*grid == vat_ordered_grid())
        && (*cert == vat_golden_cert())
        && (*bs == cert.expected_bitstream)
        && check_no_unauthorized_secret_pips(grid, cert.secret_bel, bs)
}
