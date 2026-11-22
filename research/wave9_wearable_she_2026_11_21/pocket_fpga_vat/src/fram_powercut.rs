//! Any-bit power-cut atomic 2-slot SPI-FRAM monotone counter (`512` payload bits + SPI Mode-0
//! `WREN`/`WRITE`/`READ` wire framing) mirroring `Compiler/PocketFpgaCaptpVat.lean` (§2) and
//! `qsag/hardware/gf180mcu/rtl/qsag_anchor_spi.sv`.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct PolicyDigest256 {
    pub d0: u64,
    pub d1: u64,
    pub d2: u64,
    pub d3: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Bits512 {
    pub w: [u64; 8],
}

impl Bits512 {
    pub const ZERO: Self = Self { w: [0; 8] };

    pub fn word(&self, idx: usize) -> u64 {
        if idx < 8 {
            self.w[idx]
        } else {
            self.w[7]
        }
    }
}

pub fn bits512_bit(b: &Bits512, idx: usize) -> bool {
    let w = b.word(idx / 64);
    ((w >> (idx % 64)) & 1) == 1
}

pub fn tear_word64(old_w: u64, new_w: u64, local_cut: usize) -> u64 {
    if local_cut == 0 {
        old_w
    } else if local_cut >= 64 {
        new_w
    } else {
        let mask = (1u64 << local_cut) - 1;
        (new_w & mask) | (old_w & !mask)
    }
}

/// Bit-exact SPI-FRAM power-cut tear across all `512` frame bits (`0..=512`).
pub fn tear_bits512(old_raw: &Bits512, new_raw: &Bits512, cut_bit: usize) -> Bits512 {
    let mut out = [0u64; 8];
    for (i, slot) in out.iter_mut().enumerate() {
        let local_cut = cut_bit.saturating_sub(i * 64);
        *slot = tear_word64(old_raw.w[i], new_raw.w[i], local_cut);
    }
    Bits512 { w: out }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct FramSlotRecord {
    pub policy_digest: PolicyDigest256,
    pub leaf_idx: u64,
    pub spend_used: u64,
    pub epoch_seq: u64,
    pub crc_tag: u64,
}

pub fn crc64_step_bit(crc: u64, bit: bool) -> u64 {
    let feedback = ((crc & 1) == 1) != bit;
    let shifted = crc >> 1;
    if feedback {
        shifted ^ 0xC96C_5795_D787_0F42
    } else {
        shifted
    }
}

pub fn crc64_absorb_word(mut crc: u64, w: u64) -> u64 {
    for i in 0..64 {
        crc = crc64_step_bit(crc, ((w >> i) & 1) == 1);
    }
    crc
}

pub fn compute_fram_crc_tag(
    pd: &PolicyDigest256,
    leaf_idx: u64,
    spend_used: u64,
    epoch_seq: u64,
) -> u64 {
    let mut crc: u64 = 0x4452_4731_4652_414D; // "DRG1FRAM"
    for w in [
        pd.d0, pd.d1, pd.d2, pd.d3, leaf_idx, spend_used, epoch_seq,
    ] {
        crc = crc64_absorb_word(crc, w);
    }
    crc ^ 0xFFFF_FFFF_FFFF_FFFF
}

pub fn mk_valid_fram_record(
    pd: PolicyDigest256,
    leaf_idx: u64,
    spend_used: u64,
    epoch_seq: u64,
) -> FramSlotRecord {
    let crc_tag = compute_fram_crc_tag(&pd, leaf_idx, spend_used, epoch_seq);
    FramSlotRecord {
        policy_digest: pd,
        leaf_idx,
        spend_used,
        epoch_seq,
        crc_tag,
    }
}

pub fn encode_fram_slot(r: &FramSlotRecord) -> Bits512 {
    Bits512 {
        w: [
            r.policy_digest.d0,
            r.policy_digest.d1,
            r.policy_digest.d2,
            r.policy_digest.d3,
            r.leaf_idx,
            r.spend_used,
            r.epoch_seq,
            r.crc_tag,
        ],
    }
}

pub fn decode_fram_slot(raw: &Bits512) -> FramSlotRecord {
    FramSlotRecord {
        policy_digest: PolicyDigest256 {
            d0: raw.w[0],
            d1: raw.w[1],
            d2: raw.w[2],
            d3: raw.w[3],
        },
        leaf_idx: raw.w[4],
        spend_used: raw.w[5],
        epoch_seq: raw.w[6],
        crc_tag: raw.w[7],
    }
}

pub fn fram_slot_valid(raw: &Bits512) -> bool {
    let r = decode_fram_slot(raw);
    r.epoch_seq != 0
        && r.epoch_seq != u64::MAX
        && r.crc_tag == compute_fram_crc_tag(&r.policy_digest, r.leaf_idx, r.spend_used, r.epoch_seq)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct DualSlotFram {
    pub slot0: Bits512,
    pub slot1: Bits512,
}

pub fn genesis_dual_fram(pd: PolicyDigest256) -> DualSlotFram {
    DualSlotFram {
        slot0: encode_fram_slot(&mk_valid_fram_record(pd, 0, 0, 1)),
        slot1: Bits512::ZERO,
    }
}

pub fn recover_dual_fram(dual: &DualSlotFram) -> Option<FramSlotRecord> {
    let v0 = fram_slot_valid(&dual.slot0);
    let v1 = fram_slot_valid(&dual.slot1);
    let r0 = decode_fram_slot(&dual.slot0);
    let r1 = decode_fram_slot(&dual.slot1);
    if v0 && v1 {
        if r0.epoch_seq < r1.epoch_seq {
            Some(r1)
        } else {
            Some(r0)
        }
    } else if v0 {
        Some(r0)
    } else if v1 {
        Some(r1)
    } else {
        None
    }
}

pub fn select_standby_slot(dual: &DualSlotFram) -> bool {
    let v0 = fram_slot_valid(&dual.slot0);
    let v1 = fram_slot_valid(&dual.slot1);
    let r0 = decode_fram_slot(&dual.slot0);
    let r1 = decode_fram_slot(&dual.slot1);
    if v0 && v1 {
        !(r0.epoch_seq < r1.epoch_seq)
    } else {
        v0
    }
}

pub fn write_standby_with_power_cut(
    dual: &DualSlotFram,
    new_raw: &Bits512,
    cut_bit: usize,
) -> DualSlotFram {
    if select_standby_slot(dual) {
        DualSlotFram {
            slot0: dual.slot0,
            slot1: tear_bits512(&dual.slot1, new_raw, cut_bit),
        }
    } else {
        DualSlotFram {
            slot0: tear_bits512(&dual.slot0, new_raw, cut_bit),
            slot1: dual.slot1,
        }
    }
}

pub fn boot_resync_standby(dual: &DualSlotFram) -> DualSlotFram {
    if select_standby_slot(dual) {
        DualSlotFram {
            slot0: dual.slot0,
            slot1: Bits512::ZERO,
        }
    } else {
        DualSlotFram {
            slot0: Bits512::ZERO,
            slot1: dual.slot1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FramPowerEvent {
    SignLeafComplete {
        req_leaf: u64,
        new_spend: u64,
        new_policy: PolicyDigest256,
    },
    InterruptedWrite {
        req_leaf: u64,
        new_spend: u64,
        new_policy: PolicyDigest256,
        cut_bit: usize,
    },
}

pub fn step_fram_event(dual: &DualSlotFram, ev: FramPowerEvent) -> (DualSlotFram, Option<u64>) {
    let Some(cur) = recover_dual_fram(dual) else {
        return (*dual, None);
    };
    match ev {
        FramPowerEvent::SignLeafComplete {
            req_leaf,
            new_spend,
            new_policy,
        } => {
            if cur.leaf_idx <= req_leaf
                && req_leaf < u64::MAX
                && cur.epoch_seq < u64::MAX - 1
            {
                let next_rec =
                    mk_valid_fram_record(new_policy, req_leaf + 1, new_spend, cur.epoch_seq + 1);
                let written = write_standby_with_power_cut(dual, &encode_fram_slot(&next_rec), 512);
                (boot_resync_standby(&written), Some(req_leaf))
            } else {
                (*dual, None)
            }
        }
        FramPowerEvent::InterruptedWrite {
            req_leaf,
            new_spend,
            new_policy,
            cut_bit,
        } => {
            if cur.leaf_idx <= req_leaf
                && req_leaf < u64::MAX
                && cur.epoch_seq < u64::MAX - 1
            {
                let next_rec =
                    mk_valid_fram_record(new_policy, req_leaf + 1, new_spend, cur.epoch_seq + 1);
                let torn = write_standby_with_power_cut(dual, &encode_fram_slot(&next_rec), cut_bit);
                (boot_resync_standby(&torn), None)
            } else {
                (*dual, None)
            }
        }
    }
}

pub fn run_fram_events(
    mut dual: DualSlotFram,
    events: &[FramPowerEvent],
) -> (Vec<u64>, DualSlotFram) {
    let mut released = Vec::new();
    for &ev in events {
        let (next_dual, rel) = step_fram_event(&dual, ev);
        dual = next_dual;
        if let Some(leaf) = rel {
            released.push(leaf);
        }
    }
    (released, dual)
}

/// Bit-serial SPI Mode-0 FRAM peripheral (`0x06 WREN` = 8 bits, `0x02 WRITE` + `addr[15:0]` = 24 bits,
/// followed by `512` payload bits = `544` total SPI clock edges), modeling physical `SCK`-edge power cuts.
#[derive(Clone, Debug)]
pub struct SpiFramDevice {
    pub dual: DualSlotFram,
}

impl SpiFramDevice {
    pub fn new(genesis_pd: PolicyDigest256) -> Self {
        Self {
            dual: genesis_dual_fram(genesis_pd),
        }
    }

    /// Simulates a full SPI `WREN (0x06, 8 sck) + WRITE (0x02, 8 sck) + ADDR16 (16 sck) + 512-bit frame`
    /// (`544` SPI clocks total) interrupted at `sck_cut_edge` (`0..=544`).
    pub fn spi_write_standby_with_wire_cut(&mut self, next_rec: &FramSlotRecord, sck_cut_edge: usize) {
        // First 32 SPI clocks carry WREN (8) + WRITE opcode (8) + 16-bit slot address (0x0000 or 0x0040).
        // Zero FRAM memory cells are modified before SCK edge 32!
        let payload_cut = sck_cut_edge.saturating_sub(32).min(512);
        let encoded = encode_fram_slot(next_rec);
        self.dual = write_standby_with_power_cut(&self.dual, &encoded, payload_cut);
    }
}

pub fn broken_commit_first_encode(epoch: u64, leaf: u64) -> Bits512 {
    let mut w = [0u64; 8];
    w[0] = epoch;
    w[1] = leaf;
    Bits512 { w }
}

pub fn broken_commit_first_recover(slot0: &Bits512, slot1: &Bits512) -> u64 {
    if slot0.w[0] < slot1.w[0] {
        slot1.w[1]
    } else {
        slot0.w[1]
    }
}
