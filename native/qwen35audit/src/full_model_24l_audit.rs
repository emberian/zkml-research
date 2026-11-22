#![deny(warnings)]
//! Full 24-Layer End-to-End Cryptographic Audit (`Full24LayerQwen35Receipt`) of Real Pretrained
//! `Qwen/Qwen3.5-0.8B-Base` (`18` Gated-DeltaNet + `6` Full-Attention GQA + `24` SwiGLU MLPs +
//! `48` Layer RMSNorms + `embed_tokens` + `final_norm` + `248,320`-Vocab Tied `lm_head` Argmax)
//! in Layer-Batched `WhirExt4Pcs + GMaskExt4` (`0` unproved layers, `0` cross-layer residual splice
//! gap, `0` `< P/2` BabyBear modular wraparound; per-PCS `[BCIKS20]` UD query budgets `2^{-125.8}`
//! online / `2^{-108.6}` public weights, `D1b` LogUp pole union bound `<= 2^{-97.2}`, composed
//! Fiat-Shamir/WHIR reduction tracked explicitly as `[OPEN]`).

use crate::agent_runner::QwenBpeTokenizer;
use crate::bpe_bridge::{QwenBpeRom, QWEN_DEFINED_TOKENS, QWEN_VOCAB_SIZE};
use crate::ext4::{
    badd, bb_from_i64, binv, bmul, bpow, bsub, build_eq_suffix_tables_ext4,
    build_eq_table_lsb_ext4, cshake256_32, eq_lin_ext4, eq_mle_ext4,
    eval_cubic_zero_one_two_inf_ext4, fold_ext4, merkle_node_cshake, mle_eval_bb_at_ext4,
    os_random_seed_32, ByteCursor, CShakeRng, CShakeTranscript, Ext4, INV2_BB, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, verify_d1b_range_ext4, CubicExt4RoundMsg, D1bLayerProof,
    D1bRangeExt4Proof,
};
use crate::pcs_ext4::MerkleMultiProof;
use crate::safetensors_mmap::{MmapSafetensors, QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE};
use crate::whir_ext4::{
    canonical_coset_shift_bb, canonical_ext4_k_schedule, eval_poly_ext4, open_whir_batch_ext4,
    pack_bb_31b, pack_ext4_slice, unpack_bb_31b, unpack_ext4_slice, verify_gmask_einsum_ext4,
    verify_whir_batch_ext4, BlindedEinSumExt4Proof, CosetLevelExt4, GMaskExt4, GMaskSpecExt4,
    JointLinearClaimExt4, LinearTermExt4, SubtableMeta, WhirBatchOpeningProofExt4,
    WhirCascadeLevelProofExt4, WhirCommittedMatrixExt4, WhirExt4MatrixShape, WHIR_EXT4_BLOWUP,
};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;
use std::sync::OnceLock;

// ================================================================================================
// §1. Architectural Constants, Fixed-Point Scales, & `< P/2` Wrap-Freedom Invariants
// ================================================================================================

pub const FULL_24L_MAGIC: &[u8; 8] = b"QW35F24L";
pub const FULL_24L_SEQ_LEN: usize = 16;
pub const LOG_SEQ: usize = 4;
pub const NUM_LAYERS: usize = 24;
pub const LAYERS_PAD: usize = 32;
pub const LOG_LAYERS_PAD: usize = 5;
pub const NUM_GDN_LAYERS: usize = 18;
pub const GDN_PAD: usize = 32;
pub const LOG_GDN_PAD: usize = 5;
pub const NUM_GQA_LAYERS: usize = 6;
pub const GQA_PAD: usize = 8;
pub const LOG_GQA_PAD: usize = 3;

pub const D_MODEL: usize = 1024;
pub const LOG_D_MODEL: usize = 10;
pub const D_FF: usize = 3584;
pub const D_FF_PAD: usize = 4096;
pub const LOG_D_FF_PAD: usize = 12;
pub const VOCAB_SIZE: usize = QWEN_VOCAB_SIZE; // 248,320
pub const VOCAB_PAD: usize = 1 << 18; // 262,144
pub const LOG_VOCAB_PAD: usize = 18;

pub const GDN_H: usize = 16;
pub const LOG_GDN_H: usize = 4;
pub const GDN_D: usize = 128;
pub const LOG_GDN_D: usize = 7;
pub const GDN_QKV_DIM: usize = 6144;
pub const GDN_QKV_PAD: usize = 8192;
pub const LOG_GDN_QKV_PAD: usize = 13;

pub const GQA_HQ: usize = 8;
pub const LOG_GQA_HQ: usize = 3;
pub const GQA_HKV: usize = 2;
pub const LOG_GQA_HKV: usize = 1;
pub const GQA_DH: usize = 256;
pub const LOG_GQA_DH: usize = 8;
pub const GQA_ROT_DIM: usize = 64;

pub const GDN_LAYER_INDICES: [usize; NUM_GDN_LAYERS] = [
    0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22,
];
pub const GQA_LAYER_INDICES: [usize; NUM_GQA_LAYERS] = [3, 7, 11, 15, 19, 23];

/// Fixed-point scales (`P = 2,013,265,921`, `P/2 = 1,006,632,960`):
/// - `S_RES = 2048` (`Q11` residual stream `h_in`, `h_mid`, `h_out`, `attn_out`, `mlp_out` in `[-30000, 30000)`),
/// - `S_ACT = 256` (`Q8` normalized activations), `S_SW = 128` (`Q7` SwiGLU intermediate), all matmul inputs
///   `D1b`-bounded in `[-22000, 22000)`,
/// - `S_W = 512` (`Q9` quantized 2D weights & 1D gains; measured `max_row_l1 = 41,087 <= MAX_ALLOWED_ROW_L1 = 44,000`,
///   guaranteeing `22,000 * 44,000 = 968,000,000 < P/2` even against unbounded adversarial witnesses!).
pub const S_RES: i64 = 2048;
pub const S_ACT: i64 = 256;
pub const S_SW: i64 = 128;
pub const S_W: i64 = 512;
pub const MAX_ALLOWED_ROW_L1: u32 = 44_000;
pub const MAX_ALLOWED_CONV_L1: u32 = 8_192;
pub const MAX_ALLOWED_GAIN_ABS: u32 = 8_192;
pub const MAX_ALLOWED_GDN_QK_GAIN: u32 = 128;
pub const MAX_ALLOWED_SCALAR_ABS: u32 = 8_192;

/// Online ZK WHIR query count (`mc = 15, w0 = 65,536, blow = 8, n0 = 524,288` -> `4 * (9/16)^154 = 2^{-125.83}` UD query term).
pub const ONLINE_WHIR_T_QUERIES: usize = 154;
/// Public weight WHIR query count (`mc = 21, w0 = 2,097,152, blow = 4, n0 = 8,388,608` -> `(5/8)^160 = 2^{-108.55}` UD query term).
pub const PUBLIC_WEIGHT_T_QUERIES: usize = 160;

const PUB_W_S0_LEAF_DOM: &[u8] = b"QW35-PUBW24L-S0-LEAF-V1";
const PUB_W_FOLD_LEAF_DOM: &[u8] = b"QW35-PUBW24L-FOLD-LEAF-V1";
const PUB_W_NODE_DOM: &[u8] = b"QW35-PUBW24L-NODE-V1";
const SAFETENSORS_PARAM_LEAF_DOM: &[u8] = b"QW35-24L-PARAM-RAW-V1";
const SAFETENSORS_PARAM_NODE_DOM: &[u8] = b"QW35-24L-PARAM-NODE-V1";

// Weight subtable indices in `WeightModelRoot24L` (strictly descending `m_vars` -> zero alignment padding):
pub const WST_EMBED: usize = 0; // m = 28: [d: 1024, v: 262144]
pub const WST_GDN_QKV: usize = 1; // m = 28: [d: 1024, c: 8192, g: 32]
pub const WST_MLP_GATE: usize = 2; // m = 27: [d: 1024, j: 4096, l: 32]
pub const WST_MLP_UP: usize = 3; // m = 27: [d: 1024, j: 4096, l: 32]
pub const WST_MLP_DOWN: usize = 4; // m = 27: [j: 4096, d: 1024, l: 32]
pub const WST_GDN_Z: usize = 5; // m = 26: [d: 1024, k: 2048, g: 32]
pub const WST_GDN_OUT: usize = 6; // m = 26: [k: 2048, d: 1024, g: 32]
pub const WST_GQA_Q: usize = 7; // m = 24: [d: 1024, dh: 256, hq: 8, q: 8]
pub const WST_GQA_GATE: usize = 8; // m = 24: [d: 1024, dh: 256, hq: 8, q: 8]
pub const WST_GQA_O: usize = 9; // m = 24: [k: 2048, d: 1024, q: 8]
pub const WST_GQA_K: usize = 10; // m = 22: [d: 1024, dh: 256, hkv: 2, q: 8]
pub const WST_GQA_V: usize = 11; // m = 22: [d: 1024, dh: 256, hkv: 2, q: 8]
pub const WST_GDN_CONV: usize = 12; // m = 20: [kw: 4, c: 8192, g: 32]
pub const WST_GDN_B: usize = 13; // m = 19: [d: 1024, h: 16, g: 32]
pub const WST_GDN_A: usize = 14; // m = 19: [d: 1024, h: 16, g: 32]
pub const WST_NORM1024: usize = 15; // m = 16: [d: 1024, slot: 64]
pub const WST_NORM_GQA256: usize = 16; // m = 15: [d: 256, hslot: 16, q: 8]
pub const WST_NORM_GDN128: usize = 17; // m = 13: [d: 128, gk: 64]
pub const WST_GDN_DT: usize = 18; // m = 9:  [h: 16, g: 32] (Q8 = 256)
pub const WST_GDN_ALOG: usize = 19; // m = 9:  [h: 16, g: 32] (Q9 = 512)

pub const WEIGHT_SUBTABLE_MVARS: [usize; 20] = [
    28, 28, 27, 27, 27, 26, 26, 24, 24, 24, 22, 22, 20, 19, 19, 16, 15, 13, 9, 9,
];

#[inline(always)]
pub fn div_round_i64(num: i64, den: i64) -> i64 {
    debug_assert!(den > 0);
    (num + (den / 2)).div_euclid(den)
}

#[inline(always)]
pub fn div_round_with_rem(num: i64, den: i64) -> (i64, u32) {
    debug_assert!(den > 0);
    let shifted = num + (den / 2);
    let q = shifted.div_euclid(den);
    let rem = shifted.rem_euclid(den) as u32;
    debug_assert!(num == den * q + (rem as i64) - (den / 2));
    (q, rem)
}

#[inline(always)]
fn bb_to_signed_i64(v: u32) -> i64 {
    let half = P_U32 / 2;
    if v <= half {
        v as i64
    } else {
        (v as i64) - (P as i64)
    }
}

// ================================================================================================
// §2. Deterministic Public Non-Linear LUTs (`SiLU`, `Sigmoid`, `Softplus`, `ExpNeg`, `Rsqrt`, `RoPE`)
// ================================================================================================

pub struct Full24LPublicLuts {
    pub silu_i64: Vec<i64>, // [-16384..16384) -> Q8
    pub silu_x_bb: Vec<u32>,
    pub silu_y_bb: Vec<u32>,
    pub sig_i64: Vec<i64>, // [-16384..16384) -> Q10 [0..=1024]
    pub sig_x_bb: Vec<u32>,
    pub sig_y_bb: Vec<u32>,
    pub sp_i64: Vec<i64>, // [-16384..16384) -> Q8 [0..16384)
    pub sp_x_bb: Vec<u32>,
    pub sp_y_bb: Vec<u32>,
    pub expneg_i64: Vec<i64>, // [0..32768) -> Q12 [0..=4096]
    pub expneg_u_bb: Vec<u32>,
    pub expneg_y_bb: Vec<u32>,
    pub rsqrt_lut: Vec<u32>, // [0..16384) -> min(262143, round(262144 / sqrt(max(1, u))))
    /// `131,072 = 2^17` valid `(pow4, pow2, half_pow2, u_ms, rm)` tuples + slot `(e, u) -> slot_idx`.
    pub rsqrt_norm_cols: [Vec<u32>; 5],
    pub rsqrt_slot_map: HashMap<(u8, u16), usize>,
    pub rope_diag_bb: Vec<u32>,  // [d: 256, t: 16] = 4096
    pub rope_cross_bb: Vec<u32>, // [d: 256, t: 16] = 4096
    pub rope_cos_q10: [[i64; 32]; FULL_24L_SEQ_LEN],
    pub rope_sin_q10: [[i64; 32]; FULL_24L_SEQ_LEN],
}

pub fn public_luts_24l() -> &'static Full24LPublicLuts {
    static LUTS: OnceLock<Full24LPublicLuts> = OnceLock::new();
    LUTS.get_or_init(|| {
        let n_signed = 32_768usize;
        let mut silu_i64 = Vec::with_capacity(n_signed);
        let mut silu_x_bb = Vec::with_capacity(n_signed);
        let mut silu_y_bb = Vec::with_capacity(n_signed);
        let mut sig_i64 = Vec::with_capacity(n_signed);
        let mut sig_x_bb = Vec::with_capacity(n_signed);
        let mut sig_y_bb = Vec::with_capacity(n_signed);
        let mut sp_i64 = Vec::with_capacity(n_signed);
        let mut sp_x_bb = Vec::with_capacity(n_signed);
        let mut sp_y_bb = Vec::with_capacity(n_signed);

        for i in 0..n_signed {
            let x_q8 = (i as i64) - 16_384;
            let xf = (x_q8 as f64) / 256.0;
            let x_clamped = xf.clamp(-40.0, 40.0);
            let sig_f = 1.0 / (1.0 + (-x_clamped).exp());
            let silu_v = (256.0 * (xf * sig_f)).round() as i64;
            let sig_v = (1024.0 * sig_f).round() as i64;
            let sp_v = if xf > 30.0 {
                x_q8
            } else {
                (256.0 * (1.0 + x_clamped.exp()).ln()).round() as i64
            };
            let xb = bb_from_i64(x_q8);
            silu_i64.push(silu_v);
            silu_x_bb.push(xb);
            silu_y_bb.push(bb_from_i64(silu_v));
            sig_i64.push(sig_v);
            sig_x_bb.push(xb);
            sig_y_bb.push(sig_v as u32);
            sp_i64.push(sp_v);
            sp_x_bb.push(xb);
            sp_y_bb.push(sp_v as u32);
        }

        let mut expneg_i64 = Vec::with_capacity(n_signed);
        let mut expneg_u_bb = Vec::with_capacity(n_signed);
        let mut expneg_y_bb = Vec::with_capacity(n_signed);
        for u in 0..n_signed {
            let uf = (u as f64) / 256.0;
            let ev = (4096.0 * (-uf).exp()).round() as i64;
            expneg_i64.push(ev);
            expneg_u_bb.push(u as u32);
            expneg_y_bb.push(ev as u32);
        }

        let mut rsqrt_lut = vec![0u32; 16_384];
        for (u, dst) in rsqrt_lut.iter_mut().enumerate().skip(1) {
            let v = (262_144.0 / (u as f64).sqrt()).round() as u32;
            *dst = v.min(262_143);
        }

        let cap_rsqrt = 1usize << 17; // 131,072
        let mut rsqrt_norm_cols: [Vec<u32>; 5] =
            std::array::from_fn(|_| Vec::with_capacity(cap_rsqrt));
        let mut rsqrt_slot_map = HashMap::with_capacity(103_000);
        // Slot 0: inactive `(pow4 = 0, pow2 = 1, half_pow2 = 0, u_ms = 0, rm = 0)`
        rsqrt_norm_cols[0].push(0);
        rsqrt_norm_cols[1].push(1);
        rsqrt_norm_cols[2].push(0);
        rsqrt_norm_cols[3].push(0);
        rsqrt_norm_cols[4].push(0);
        rsqrt_slot_map.insert((255u8, 0u16), 0usize);

        for e in 0..=7u8 {
            let pow4 = 1u32 << (2 * e);
            let pow2 = 1u32 << e;
            let half_pow2 = if e == 0 { 0 } else { 1u32 << (e - 1) };
            let min_u = if e == 0 { 1usize } else { 4096usize };
            for u in min_u..16_384usize {
                let slot = rsqrt_norm_cols[0].len();
                rsqrt_norm_cols[0].push(pow4);
                rsqrt_norm_cols[1].push(pow2);
                rsqrt_norm_cols[2].push(half_pow2);
                rsqrt_norm_cols[3].push(u as u32);
                rsqrt_norm_cols[4].push(rsqrt_lut[u]);
                rsqrt_slot_map.insert((e, u as u16), slot);
            }
        }
        while rsqrt_norm_cols[0].len() < cap_rsqrt {
            rsqrt_norm_cols[0].push(0);
            rsqrt_norm_cols[1].push(1);
            rsqrt_norm_cols[2].push(0);
            rsqrt_norm_cols[3].push(0);
            rsqrt_norm_cols[4].push(0);
        }

        let mut rope_cos_q10 = [[0i64; 32]; FULL_24L_SEQ_LEN];
        let mut rope_sin_q10 = [[0i64; 32]; FULL_24L_SEQ_LEN];
        let mut rope_diag_bb = vec![0u32; GQA_DH * FULL_24L_SEQ_LEN];
        let mut rope_cross_bb = vec![0u32; GQA_DH * FULL_24L_SEQ_LEN];
        for t in 0..FULL_24L_SEQ_LEN {
            for pair in 0..32 {
                let freq = 1.0 / 10_000_000.0_f64.powf((2 * pair) as f64 / 64.0);
                let cs = (1024.0 * ((t as f64) * freq).cos()).round() as i64;
                let sn = (1024.0 * ((t as f64) * freq).sin()).round() as i64;
                rope_cos_q10[t][pair] = cs;
                rope_sin_q10[t][pair] = sn;
                rope_diag_bb[pair + (t << LOG_GQA_DH)] = bb_from_i64(cs);
                rope_diag_bb[(32 + pair) + (t << LOG_GQA_DH)] = bb_from_i64(cs);
                rope_cross_bb[pair + (t << LOG_GQA_DH)] = bb_from_i64(-sn);
                rope_cross_bb[(32 + pair) + (t << LOG_GQA_DH)] = bb_from_i64(sn);
            }
            for d in GQA_ROT_DIM..GQA_DH {
                rope_diag_bb[d + (t << LOG_GQA_DH)] = 1024;
                rope_cross_bb[d + (t << LOG_GQA_DH)] = 0;
            }
        }

        Full24LPublicLuts {
            silu_i64,
            silu_x_bb,
            silu_y_bb,
            sig_i64,
            sig_x_bb,
            sig_y_bb,
            sp_i64,
            sp_x_bb,
            sp_y_bb,
            expneg_i64,
            expneg_u_bb,
            expneg_y_bb,
            rsqrt_lut,
            rsqrt_norm_cols,
            rsqrt_slot_map,
            rope_diag_bb,
            rope_cross_bb,
            rope_cos_q10,
            rope_sin_q10,
        }
    })
}

/// Exact `O(m)`-operation multilinear extension of `[x < bound]` on `{0, 1}^m` (`LSB-first` bits).
pub fn eval_lt_const_mle(z: &[Ext4], bound: usize) -> Ext4 {
    let m = z.len();
    if bound == 0 {
        return Ext4::ZERO;
    }
    if bound >= (1usize << m) {
        return Ext4::ONE;
    }
    let mut suffix_eq = vec![Ext4::ONE; m + 1];
    for bit in (0..m).rev() {
        let b_val = if ((bound >> bit) & 1) == 1 {
            z[bit]
        } else {
            Ext4::ONE.sub(z[bit])
        };
        suffix_eq[bit] = suffix_eq[bit + 1].mul(b_val);
    }
    let mut acc = Ext4::ZERO;
    for bit in 0..m {
        if ((bound >> bit) & 1) == 1 {
            acc = acc.add(Ext4::ONE.sub(z[bit]).mul(suffix_eq[bit + 1]));
        }
    }
    acc
}

/// Evaluate `[i > j]` (`strict_gt = true`) or `[i >= j]` (`strict_gt = false`) on `4`-bit indices `(z_i, z_j)`.
fn eval_cmp_ij_mle(z_i: &[Ext4], z_j: &[Ext4], strict_gt: bool) -> Ext4 {
    let eq_i = build_eq_table_lsb_ext4(z_i);
    let eq_j = build_eq_table_lsb_ext4(z_j);
    let mut acc = Ext4::ZERO;
    for i in 0..eq_i.len() {
        let hi = if strict_gt { i } else { i + 1 };
        let mut s = Ext4::ZERO;
        for &ej in &eq_j[..hi] {
            s = s.add(ej);
        }
        acc = acc.add(eq_i[i].mul(s));
    }
    acc
}

// ================================================================================================
// §3. Cache-Friendly Stage-Packed NTT & Public 24-Layer Checkpoint WHIR (`WeightModelRoot24L`)
// ================================================================================================

struct PackedNttPlanBb {
    n: usize,
    lg: u32,
    stage_tw: Vec<u32>,
}

impl PackedNttPlanBb {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 2);
        let lg = n.trailing_zeros();
        let mut stage_tw = Vec::with_capacity(n - 1);
        let mut len = 2usize;
        while len <= n {
            let omega = crate::ext4::root_of_unity_bb(len);
            let mut cur = 1u32;
            for _ in 0..(len / 2) {
                stage_tw.push(cur);
                cur = bmul(cur, omega);
            }
            len <<= 1;
        }
        Self { n, lg, stage_tw }
    }

    fn forward_in_place(&self, a: &mut [u32]) {
        assert_eq!(a.len(), self.n);
        let shift = usize::BITS - self.lg;
        for i in 0..self.n {
            let r = i.reverse_bits() >> shift;
            if i < r {
                a.swap(i, r);
            }
        }
        let mut tw_off = 0usize;
        let mut len = 2usize;
        while len <= self.n {
            let half = len / 2;
            let tw = &self.stage_tw[tw_off..tw_off + half];
            for chunk in a.chunks_exact_mut(len) {
                let (lo, hi) = chunk.split_at_mut(half);
                for j in 0..half {
                    let u = lo[j];
                    let v = bmul(hi[j], tw[j]);
                    lo[j] = badd(u, v);
                    hi[j] = bsub(u, v);
                }
            }
            tw_off += half;
            len <<= 1;
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicWeightWhirShape24L {
    pub mr: usize,
    pub mc: usize,
    pub rd: usize,
    pub usable_rows: usize,
    pub w0: usize,
    pub blow: usize,
    pub n0: usize,
    pub subtables: Vec<SubtableMeta>,
}

impl PublicWeightWhirShape24L {
    pub fn canonical_24l() -> Self {
        let mut offset = 0usize;
        let mut subtables = Vec::with_capacity(WEIGHT_SUBTABLE_MVARS.len());
        for (id, &m_vars) in WEIGHT_SUBTABLE_MVARS.iter().enumerate() {
            assert_eq!(offset & ((1usize << m_vars) - 1), 0);
            subtables.push(SubtableMeta {
                id,
                m_vars,
                base_cell: offset,
            });
            offset += 1usize << m_vars;
        }
        let mc = 21usize;
        let w0 = 1usize << mc; // 2,097,152
        let usable_rows = offset.div_ceil(w0); // 542
        let rd = usable_rows.next_power_of_two(); // 1,024
        let mr = rd.trailing_zeros() as usize; // 10
        let blow = 4usize;
        let n0 = blow * w0; // 8,388,608 = 2^23
        Self {
            mr,
            mc,
            rd,
            usable_rows,
            w0,
            blow,
            n0,
            subtables,
        }
    }

    fn tag_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(12 + self.subtables.len() * 5);
        b.push(self.mr as u8);
        b.push(self.mc as u8);
        b.push(self.blow as u8);
        b.extend_from_slice(&(self.usable_rows as u16).to_le_bytes());
        b.extend_from_slice(&(self.subtables.len() as u16).to_le_bytes());
        for st in &self.subtables {
            b.push(st.m_vars as u8);
            b.extend_from_slice(&(st.base_cell as u32).to_le_bytes());
        }
        b
    }
}

/// Public, precomputable 24-layer checkpoint commitment (`WeightModelRoot24L`) binding all `320`
/// `model.language_model.*` parameter tensors + `QwenBpeRom` root + standalone `< P/2` wrap-freedom guards.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WeightModelRoot24L {
    pub weight_whir_root: [u8; 32],
    pub safetensors_param_root: [u8; 32],
    pub bpe_rom_root: [u8; 32],
    pub max_row_l1: u32,
    pub max_conv_l1: u32,
    pub max_gain_abs: u32,
    pub max_gdn_qk_gain: u32,
    pub max_scalar_abs: u32,
}

impl WeightModelRoot24L {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.weight_whir_root);
        out.extend_from_slice(&self.safetensors_param_root);
        out.extend_from_slice(&self.bpe_rom_root);
        out.extend_from_slice(&self.max_row_l1.to_le_bytes());
        out.extend_from_slice(&self.max_conv_l1.to_le_bytes());
        out.extend_from_slice(&self.max_gain_abs.to_le_bytes());
        out.extend_from_slice(&self.max_gdn_qk_gain.to_le_bytes());
        out.extend_from_slice(&self.max_scalar_abs.to_le_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        Ok(Self {
            weight_whir_root: cur.read_arr32()?,
            safetensors_param_root: cur.read_arr32()?,
            bpe_rom_root: cur.read_arr32()?,
            max_row_l1: cur.read_u32()?,
            max_conv_l1: cur.read_u32()?,
            max_gain_abs: cur.read_u32()?,
            max_gdn_qk_gain: cur.read_u32()?,
            max_scalar_abs: cur.read_u32()?,
        })
    }

    pub fn absorb_into(&self, tr: &mut CShakeTranscript) {
        tr.absorb_root(b"w24l_whir_root", &self.weight_whir_root);
        tr.absorb_root(b"w24l_param_root", &self.safetensors_param_root);
        tr.absorb_root(b"w24l_bpe_root", &self.bpe_rom_root);
        tr.absorb_u32(b"w24l_max_l1", self.max_row_l1);
        tr.absorb_u32(b"w24l_conv_l1", self.max_conv_l1);
        tr.absorb_u32(b"w24l_gain_abs", self.max_gain_abs);
        tr.absorb_u32(b"w24l_qk_gain", self.max_gdn_qk_gain);
        tr.absorb_u32(b"w24l_scalar_abs", self.max_scalar_abs);
    }
}

pub struct PrecomputedModelWeights24L {
    pub model_root: WeightModelRoot24L,
    pub shape: PublicWeightWhirShape24L,
    /// `usable_rows` (`542`) rows of length `w0 = 2^{21}` stored as signed `i16` (`None` if row is all zero!).
    pub rows_i16: Vec<Option<Vec<i16>>>,
    /// `usable_rows` (`542`) coset-NTT codewords of length `n0 = 2^{23}` (`None` if row is all zero!).
    pub row_evals: Vec<Option<Vec<u32>>>,
    pub tree0: Vec<Vec<[u8; 32]>>,
}

#[inline]
fn hash_pub_w_col_cshake(col_idx: usize, col: &[u32]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(4 + col.len() * 4);
    buf.extend_from_slice(&(col_idx as u32).to_le_bytes());
    for &v in col {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    cshake256_32(PUB_W_S0_LEAF_DOM, &buf)
}

#[inline]
fn hash_pub_w_fiber_cshake(round: usize, f_idx: usize, vals: &[Ext4]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(5 + vals.len() * 16);
    buf.push(round as u8);
    buf.extend_from_slice(&(f_idx as u32).to_le_bytes());
    for v in vals {
        buf.extend_from_slice(&v.to_bytes());
    }
    cshake256_32(PUB_W_FOLD_LEAF_DOM, &buf)
}

fn build_merkle_tree_dom(dom: &[u8], leaves: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    assert!(!leaves.is_empty() && leaves.len().is_power_of_two());
    let mut tree = vec![leaves];
    let mut level = 0u8;
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = if prev.len() >= 512 {
            prev.par_chunks_exact(2)
                .enumerate()
                .map(|(idx, pair)| merkle_node_cshake(dom, level, idx as u32, &pair[0], &pair[1]))
                .collect()
        } else {
            prev.chunks_exact(2)
                .enumerate()
                .map(|(idx, pair)| merkle_node_cshake(dom, level, idx as u32, &pair[0], &pair[1]))
                .collect()
        };
        tree.push(next);
        level += 1;
    }
    tree
}

fn verify_merkle_multiproof_dom(
    dom: &[u8],
    mp: &MerkleMultiProof,
    expected_root: &[u8; 32],
    n_leaves: usize,
    sorted_indices: &[usize],
    leaf_hashes: &[[u8; 32]],
) -> bool {
    if !n_leaves.is_power_of_two()
        || sorted_indices.is_empty()
        || sorted_indices.len() != leaf_hashes.len()
    {
        return false;
    }
    for w in sorted_indices.windows(2) {
        if w[0] >= w[1] {
            return false;
        }
    }
    if *sorted_indices.last().unwrap() >= n_leaves {
        return false;
    }
    let num_levels = n_leaves.trailing_zeros() as usize;
    let mut cur_nodes: Vec<(usize, [u8; 32])> = sorted_indices
        .iter()
        .copied()
        .zip(leaf_hashes.iter().copied())
        .collect();
    let mut aux_pos = 0usize;
    for level in 0..num_levels {
        let mut next_nodes = Vec::with_capacity((cur_nodes.len() + 1) / 2);
        let mut k = 0usize;
        while k < cur_nodes.len() {
            let (idx, hash) = cur_nodes[k];
            let sib = idx ^ 1;
            let (left, right) = if k + 1 < cur_nodes.len() && cur_nodes[k + 1].0 == sib {
                let sh = cur_nodes[k + 1].1;
                k += 2;
                if (idx & 1) == 0 {
                    (hash, sh)
                } else {
                    (sh, hash)
                }
            } else {
                if aux_pos >= mp.aux_hashes.len() {
                    return false;
                }
                let sh = mp.aux_hashes[aux_pos];
                aux_pos += 1;
                k += 1;
                if (idx & 1) == 0 {
                    (hash, sh)
                } else {
                    (sh, hash)
                }
            };
            let parent = merkle_node_cshake(dom, level as u8, (idx >> 1) as u32, &left, &right);
            next_nodes.push((idx >> 1, parent));
        }
        cur_nodes = next_nodes;
    }
    aux_pos == mp.aux_hashes.len() && cur_nodes.len() == 1 && &cur_nodes[0].1 == expected_root
}

impl PrecomputedModelWeights24L {
    pub fn build_default() -> Result<Self, String> {
        Self::build_from_safetensors(QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE)
    }

    pub fn build_from_safetensors(
        safetensors_path: impl AsRef<Path>,
        tokenizer_path: impl AsRef<Path>,
    ) -> Result<Self, String> {
        let mmap = MmapSafetensors::open(safetensors_path)?;
        let bpe_rom = QwenBpeRom::load_from_path(tokenizer_path.as_ref())?;

        // 1. Merkle-commit all 320 raw `model.language_model.*` safetensors parameter shards (`safetensors_param_root`):
        let names: Vec<String> = mmap
            .tensors
            .keys()
            .filter(|k| k.starts_with("model.language_model."))
            .cloned()
            .collect();
        if names.len() != 320 {
            return Err(format!(
                "expected 320 model.language_model.* tensors, got {}",
                names.len()
            ));
        }
        let mut raw_leaves: Vec<[u8; 32]> = names
            .par_iter()
            .map(|name| {
                let (info, raw) = mmap.tensor_bytes(name).expect("valid tensor slice");
                let mut hdr = Vec::with_capacity(64 + name.len());
                hdr.extend_from_slice(&(name.len() as u32).to_le_bytes());
                hdr.extend_from_slice(name.as_bytes());
                hdr.extend_from_slice(&(info.dtype.len() as u32).to_le_bytes());
                hdr.extend_from_slice(info.dtype.as_bytes());
                hdr.extend_from_slice(&(info.shape.len() as u32).to_le_bytes());
                for &d in &info.shape {
                    hdr.extend_from_slice(&(d as u64).to_le_bytes());
                }
                let raw_digest = cshake256_32(SAFETENSORS_PARAM_LEAF_DOM, raw);
                hdr.extend_from_slice(&raw_digest);
                cshake256_32(SAFETENSORS_PARAM_LEAF_DOM, &hdr)
            })
            .collect();
        let pad_leaves = raw_leaves.len().next_power_of_two();
        raw_leaves.resize(pad_leaves, [0u8; 32]);
        let param_tree = build_merkle_tree_dom(SAFETENSORS_PARAM_NODE_DOM, raw_leaves);
        let safetensors_param_root = param_tree.last().unwrap()[0];

        // 2. Populate quantized `S_W = 512` (`i16`) subtables directly into sparse `rows_i16`:
        let shape = PublicWeightWhirShape24L::canonical_24l();
        let w0 = shape.w0;
        let mc = shape.mc;
        let mut rows_i16: Vec<Option<Vec<i16>>> = (0..shape.usable_rows).map(|_| None).collect();
        let mut max_row_l1 = 0u32;
        let mut max_conv_l1 = 0u32;
        let mut max_gain_abs = 0u32;
        let mut max_scalar_abs = 0u32;

        let quantize_checked_i16 = |f: f32, scale: f32, ctx: &str| -> Result<i16, String> {
            if !f.is_finite() {
                return Err(format!("non-finite weight {f} in {ctx}"));
            }
            let q = (f * scale).round();
            if !((-32_767.0..=32_767.0).contains(&q)) {
                return Err(format!("quantized weight {q} out of [-32767, 32767] in {ctx}"));
            }
            Ok(q as i16)
        };

        let set_cell =
            |rows: &mut [Option<Vec<i16>>], st_id: usize, u: usize, val: i16| {
                assert_ne!(val, i16::MIN, "i16::MIN disallowed in weight cell");
                if val == 0 {
                    return;
                }
                let cell = shape.subtables[st_id].base_cell + u;
                let r = cell >> mc;
                let col = cell & (w0 - 1);
                let row = rows[r].get_or_insert_with(|| vec![0i16; w0]);
                row[col] = val;
            };

        // Helper to quantize a 2D `[out_dim, in_dim]` tensor (`in_dim` contiguous at low bits!):
        let load_2d_into = |rows: &mut [Option<Vec<i16>>],
                            max_l1_ref: &mut u32,
                            st_id: usize,
                            name: &str,
                            out_limit: usize,
                            in_dim: usize,
                            layer_offset_cells: usize|
         -> Result<(), String> {
            let (sh, vals) = mmap.read_f32(name)?;
            if sh.len() != 2 || sh[0] != out_limit || sh[1] != in_dim {
                return Err(format!("unexpected shape {sh:?} on {name}"));
            }
            // Parallelize checked quantization + u64 row-L1 scan:
            let row_res: Result<(Vec<i16>, u64), String> = vals
                .par_chunks_exact(in_dim)
                .map(|row| -> Result<(Vec<i16>, u64), String> {
                    let mut out_r = Vec::with_capacity(in_dim);
                    let mut l1 = 0u64;
                    for &f in row {
                        let q = quantize_checked_i16(f, S_W as f32, name)?;
                        l1 += (q as i32).unsigned_abs() as u64;
                        out_r.push(q);
                    }
                    Ok((out_r, l1))
                })
                .try_reduce(
                    || (Vec::new(), 0u64),
                    |(mut v1, m1), (v2, m2)| {
                        v1.extend_from_slice(&v2);
                        Ok((v1, m1.max(m2)))
                    },
                );
            let (q_vals, mat_l1_u64) = row_res?;
            let mat_l1 = u32::try_from(mat_l1_u64).map_err(|_| format!("row L1 overflow on {name}"))?;
            if mat_l1 > *max_l1_ref {
                *max_l1_ref = mat_l1;
            }
            let base = shape.subtables[st_id].base_cell + layer_offset_cells;
            for j in 0..out_limit {
                let src = &q_vals[j * in_dim..(j + 1) * in_dim];
                let cell0 = base + j * in_dim;
                let r = cell0 >> mc;
                let col0 = cell0 & (w0 - 1);
                debug_assert!(col0 + in_dim <= w0);
                if src.iter().any(|&x| x != 0) {
                    let dst_row = rows[r].get_or_insert_with(|| vec![0i16; w0]);
                    dst_row[col0..col0 + in_dim].copy_from_slice(src);
                }
            }
            Ok(())
        };

        // 0: `embed_tokens.weight [248320, 1024]` -> `WST_EMBED [d: 1024, v: 262144]`
        load_2d_into(
            &mut rows_i16,
            &mut max_row_l1,
            WST_EMBED,
            "model.language_model.embed_tokens.weight",
            VOCAB_SIZE,
            D_MODEL,
            0,
        )?;

        // Final norm `1 + norm.weight [1024]` -> `WST_NORM1024` slot `24`:
        {
            let (_, fn_w) = mmap.read_f32("model.language_model.norm.weight")?;
            for (d, &w) in fn_w.iter().enumerate() {
                let q = quantize_checked_i16(1.0 + w, S_W as f32, "norm.weight")?;
                max_gain_abs = max_gain_abs.max((q as i32).unsigned_abs());
                set_cell(&mut rows_i16, WST_NORM1024, d + (24 << LOG_D_MODEL), q);
            }
        }

        // L2 unit-norm gain `round(2 * S_W / sqrt(128)) = 91` for GDN Q & K (`gk = 3*g + 0`, `3*g + 1`):
        let gdn_qk_l2_gain = ((2.0 * (S_W as f64)) / (GDN_D as f64).sqrt()).round() as i16; // 91
        let max_gdn_qk_gain = (gdn_qk_l2_gain as i32).unsigned_abs();
        max_gain_abs = max_gain_abs.max(max_gdn_qk_gain);

        let mut gdn_ord = 0usize;
        let mut gqa_ord = 0usize;
        for l in 0..NUM_LAYERS {
            let pfx = format!("model.language_model.layers.{l}");
            let (_, ln1_w) = mmap.read_f32(&format!("{pfx}.input_layernorm.weight"))?;
            let (_, ln2_w) = mmap.read_f32(&format!("{pfx}.post_attention_layernorm.weight"))?;
            for d in 0..D_MODEL {
                let q1 = quantize_checked_i16(1.0 + ln1_w[d], S_W as f32, "input_layernorm")?;
                let q2 = quantize_checked_i16(1.0 + ln2_w[d], S_W as f32, "post_attention_layernorm")?;
                max_gain_abs = max_gain_abs
                    .max((q1 as i32).unsigned_abs())
                    .max((q2 as i32).unsigned_abs());
                set_cell(&mut rows_i16, WST_NORM1024, d + (l << LOG_D_MODEL), q1);
                set_cell(&mut rows_i16, WST_NORM1024, d + ((32 + l) << LOG_D_MODEL), q2);
            }

            // MLP `[gate_proj, up_proj, down_proj]`:
            load_2d_into(
                &mut rows_i16,
                &mut max_row_l1,
                WST_MLP_GATE,
                &format!("{pfx}.mlp.gate_proj.weight"),
                D_FF,
                D_MODEL,
                l << (LOG_D_MODEL + LOG_D_FF_PAD),
            )?;
            load_2d_into(
                &mut rows_i16,
                &mut max_row_l1,
                WST_MLP_UP,
                &format!("{pfx}.mlp.up_proj.weight"),
                D_FF,
                D_MODEL,
                l << (LOG_D_MODEL + LOG_D_FF_PAD),
            )?;
            // `down_proj` is `[1024, 3584]`, padded along contracted `j` from `3584 -> 4096`:
            {
                let (sh, dw) = mmap.read_f32(&format!("{pfx}.mlp.down_proj.weight"))?;
                if sh != vec![D_MODEL, D_FF] {
                    return Err(format!("bad down_proj shape {sh:?} at layer {l}"));
                }
                let base = shape.subtables[WST_MLP_DOWN].base_cell
                    + (l << (LOG_D_FF_PAD + LOG_D_MODEL));
                for d_out in 0..D_MODEL {
                    let row = &dw[d_out * D_FF..(d_out + 1) * D_FF];
                    let mut l1 = 0u64;
                    let cell0 = base + (d_out << LOG_D_FF_PAD);
                    let r = cell0 >> mc;
                    let col0 = cell0 & (w0 - 1);
                    let dst = rows_i16[r].get_or_insert_with(|| vec![0i16; w0]);
                    for (j, &f) in row.iter().enumerate() {
                        let q = quantize_checked_i16(f, S_W as f32, "down_proj")?;
                        l1 += (q as i32).unsigned_abs() as u64;
                        dst[col0 + j] = q;
                    }
                    let l1_u32 = u32::try_from(l1).map_err(|_| "down_proj L1 overflow".to_string())?;
                    if l1_u32 > max_row_l1 {
                        max_row_l1 = l1_u32;
                    }
                }
            }

            if l % 4 != 3 {
                let g = gdn_ord;
                gdn_ord += 1;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GDN_QKV,
                    &format!("{pfx}.linear_attn.in_proj_qkv.weight"),
                    GDN_QKV_DIM,
                    D_MODEL,
                    g << (LOG_D_MODEL + LOG_GDN_QKV_PAD),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GDN_Z,
                    &format!("{pfx}.linear_attn.in_proj_z.weight"),
                    2048,
                    D_MODEL,
                    g << (LOG_D_MODEL + 11),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GDN_OUT,
                    &format!("{pfx}.linear_attn.out_proj.weight"),
                    D_MODEL,
                    2048,
                    g << (11 + LOG_D_MODEL),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GDN_B,
                    &format!("{pfx}.linear_attn.in_proj_b.weight"),
                    GDN_H,
                    D_MODEL,
                    g << (LOG_D_MODEL + LOG_GDN_H),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GDN_A,
                    &format!("{pfx}.linear_attn.in_proj_a.weight"),
                    GDN_H,
                    D_MODEL,
                    g << (LOG_D_MODEL + LOG_GDN_H),
                )?;

                // `conv1d.weight [6144, 1, 4]` -> `[kw: 4, c: 8192, g: 32]`
                let (csh, cwf) = mmap.read_f32(&format!("{pfx}.linear_attn.conv1d.weight"))?;
                if csh != vec![GDN_QKV_DIM, 1, 4] {
                    return Err(format!("bad conv1d shape {csh:?}"));
                }
                for c in 0..GDN_QKV_DIM {
                    let mut cl1 = 0u64;
                    for kw in 0..4 {
                        let q = quantize_checked_i16(cwf[c * 4 + kw], S_W as f32, "conv1d")?;
                        cl1 += (q as i32).unsigned_abs() as u64;
                        set_cell(
                            &mut rows_i16,
                            WST_GDN_CONV,
                            kw + (c << 2) + (g << (2 + LOG_GDN_QKV_PAD)),
                            q,
                        );
                    }
                    let cl1_u32 = u32::try_from(cl1).map_err(|_| "conv1d L1 overflow".to_string())?;
                    if cl1_u32 > max_conv_l1 {
                        max_conv_l1 = cl1_u32;
                    }
                }

                // `dt_bias [16]` (`Q8 = 256`) & `exp(A_log) [16]` (`Q9 = 512`):
                let (_, dt_f) = mmap.read_f32(&format!("{pfx}.linear_attn.dt_bias"))?;
                let (_, alog_f) = mmap.read_f32(&format!("{pfx}.linear_attn.A_log"))?;
                for h in 0..GDN_H {
                    let dt_q8 = quantize_checked_i16(dt_f[h], S_ACT as f32, "dt_bias")?;
                    let ea_q9 = quantize_checked_i16(alog_f[h].exp(), S_W as f32, "A_log")?;
                    max_scalar_abs = max_scalar_abs
                        .max((dt_q8 as i32).unsigned_abs())
                        .max((ea_q9 as i32).unsigned_abs());
                    set_cell(&mut rows_i16, WST_GDN_DT, h + (g << LOG_GDN_H), dt_q8);
                    set_cell(&mut rows_i16, WST_GDN_ALOG, h + (g << LOG_GDN_H), ea_q9);
                }

                // `WST_NORM_GDN128 [d: 128, gk: 64]` (`3*g+0 = q`, `3*g+1 = k`, `3*g+2 = y_norm`):
                let (_, yn_w) = mmap.read_f32(&format!("{pfx}.linear_attn.norm.weight"))?;
                for d in 0..GDN_D {
                    set_cell(
                        &mut rows_i16,
                        WST_NORM_GDN128,
                        d + ((3 * g) << LOG_GDN_D),
                        gdn_qk_l2_gain,
                    );
                    set_cell(
                        &mut rows_i16,
                        WST_NORM_GDN128,
                        d + ((3 * g + 1) << LOG_GDN_D),
                        gdn_qk_l2_gain,
                    );
                    // Plain RMSNorm (`NO 1 + w` on `linear_attn.norm.weight`!):
                    let qy = quantize_checked_i16(yn_w[d], S_W as f32, "linear_attn.norm")?;
                    max_gain_abs = max_gain_abs.max((qy as i32).unsigned_abs());
                    set_cell(
                        &mut rows_i16,
                        WST_NORM_GDN128,
                        d + ((3 * g + 2) << LOG_GDN_D),
                        qy,
                    );
                }
            } else {
                let q = gqa_ord;
                gqa_ord += 1;
                // `q_proj [4096, 1024]` interleaved `[8, 512, 1024]`: first `256` -> `WST_GQA_Q`, second `256` -> `WST_GQA_GATE`
                let (qsh, qwf) = mmap.read_f32(&format!("{pfx}.self_attn.q_proj.weight"))?;
                if qsh != vec![4096, D_MODEL] {
                    return Err(format!("bad q_proj shape {qsh:?}"));
                }
                for hq in 0..GQA_HQ {
                    for dh in 0..GQA_DH {
                        let row_q = &qwf[(hq * 512 + dh) * D_MODEL..(hq * 512 + dh + 1) * D_MODEL];
                        let row_g =
                            &qwf[(hq * 512 + 256 + dh) * D_MODEL..(hq * 512 + 256 + dh + 1) * D_MODEL];
                        let idx_sub =
                            (dh << LOG_D_MODEL) + (hq << (LOG_D_MODEL + LOG_GQA_DH)) + (q << 21);
                        let cell_q = shape.subtables[WST_GQA_Q].base_cell + idx_sub;
                        let cell_g = shape.subtables[WST_GQA_GATE].base_cell + idx_sub;
                        let mut l1_q = 0u64;
                        let mut l1_g = 0u64;
                        {
                            let dst_q =
                                rows_i16[cell_q >> mc].get_or_insert_with(|| vec![0i16; w0]);
                            let col_q = cell_q & (w0 - 1);
                            for (d, &f) in row_q.iter().enumerate() {
                                let v = quantize_checked_i16(f, S_W as f32, "q_proj")?;
                                l1_q += (v as i32).unsigned_abs() as u64;
                                dst_q[col_q + d] = v;
                            }
                        }
                        {
                            let dst_g =
                                rows_i16[cell_g >> mc].get_or_insert_with(|| vec![0i16; w0]);
                            let col_g = cell_g & (w0 - 1);
                            for (d, &f) in row_g.iter().enumerate() {
                                let v = quantize_checked_i16(f, S_W as f32, "q_proj_gate")?;
                                l1_g += (v as i32).unsigned_abs() as u64;
                                dst_g[col_g + d] = v;
                            }
                        }
                        let l1_qg = u32::try_from(l1_q.max(l1_g)).map_err(|_| "q_proj L1 overflow".to_string())?;
                        max_row_l1 = max_row_l1.max(l1_qg);
                    }
                }

                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GQA_K,
                    &format!("{pfx}.self_attn.k_proj.weight"),
                    512,
                    D_MODEL,
                    q << (LOG_D_MODEL + 9),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GQA_V,
                    &format!("{pfx}.self_attn.v_proj.weight"),
                    512,
                    D_MODEL,
                    q << (LOG_D_MODEL + 9),
                )?;
                load_2d_into(
                    &mut rows_i16,
                    &mut max_row_l1,
                    WST_GQA_O,
                    &format!("{pfx}.self_attn.o_proj.weight"),
                    D_MODEL,
                    2048,
                    q << (11 + LOG_D_MODEL),
                )?;

                // `q_norm [256]` (`hslot 0..8`) & `k_norm [256]` (`hslot 8..10`), both `1 + w`:
                let (_, qn_w) = mmap.read_f32(&format!("{pfx}.self_attn.q_norm.weight"))?;
                let (_, kn_w) = mmap.read_f32(&format!("{pfx}.self_attn.k_norm.weight"))?;
                for d in 0..GQA_DH {
                    let qq = quantize_checked_i16(1.0 + qn_w[d], S_W as f32, "q_norm")?;
                    let qk = quantize_checked_i16(1.0 + kn_w[d], S_W as f32, "k_norm")?;
                    max_gain_abs = max_gain_abs
                        .max((qq as i32).unsigned_abs())
                        .max((qk as i32).unsigned_abs());
                    for hslot in 0..8 {
                        set_cell(
                            &mut rows_i16,
                            WST_NORM_GQA256,
                            d + (hslot << LOG_GQA_DH) + (q << (LOG_GQA_DH + 4)),
                            qq,
                        );
                    }
                    for hslot in 8..10 {
                        set_cell(
                            &mut rows_i16,
                            WST_NORM_GQA256,
                            d + (hslot << LOG_GQA_DH) + (q << (LOG_GQA_DH + 4)),
                            qk,
                        );
                    }
                }
            }
        }
        assert_eq!(gdn_ord, NUM_GDN_LAYERS);
        assert_eq!(gqa_ord, NUM_GQA_LAYERS);

        if max_row_l1 > MAX_ALLOWED_ROW_L1
            || max_conv_l1 > MAX_ALLOWED_CONV_L1
            || max_gain_abs > MAX_ALLOWED_GAIN_ABS
            || max_gdn_qk_gain > MAX_ALLOWED_GDN_QK_GAIN
            || max_scalar_abs > MAX_ALLOWED_SCALAR_ABS
        {
            return Err(format!(
                "weight L1 bounds exceeded: row={max_row_l1}, conv={max_conv_l1}, gain={max_gain_abs}, qk={max_gdn_qk_gain}, scalar={max_scalar_abs}"
            ));
        }

        // 3. Parallel coset-NTT encoding (`N_0 = 2^{23}`) on non-zero rows ONLY:
        let log_n0 = shape.n0.trailing_zeros() as usize;
        let shift = canonical_coset_shift_bb(log_n0);
        let ntt_plan = PackedNttPlanBb::new(shape.n0);
        let mut shift_pows = Vec::with_capacity(w0);
        let mut cur = 1u32;
        for _ in 0..w0 {
            shift_pows.push(cur);
            cur = bmul(cur, shift);
        }

        let row_evals: Vec<Option<Vec<u32>>> = rows_i16
            .par_iter()
            .map(|opt_row| {
                let row = opt_row.as_ref()?;
                let mut buf = vec![0u32; shape.n0];
                for (k, &v) in row.iter().enumerate() {
                    let vi = v as i32;
                    if vi != 0 {
                        let vb = if vi > 0 {
                            vi as u32
                        } else {
                            P_U32 - ((-vi) as u32)
                        };
                        buf[k] = bmul(vb, shift_pows[k]);
                    }
                }
                ntt_plan.forward_in_place(&mut buf);
                Some(buf)
            })
            .collect();

        // 4. Hash `N_0 = 2^{23}` Stage-0 columns in L1-friendly `64`-column tiles (`0` full transpose!):
        let tile = 64usize;
        let usable = shape.usable_rows;
        let leaves: Vec<[u8; 32]> = (0..(shape.n0 / tile))
            .into_par_iter()
            .flat_map_iter(|blk| {
                let j0 = blk * tile;
                let mut tile_cols = vec![0u32; tile * usable];
                for (r, opt_ev) in row_evals.iter().enumerate() {
                    if let Some(ev) = opt_ev {
                        let slice = &ev[j0..j0 + tile];
                        for dj in 0..tile {
                            tile_cols[dj * usable + r] = slice[dj];
                        }
                    }
                }
                (0..tile).map(move |dj| {
                    let col = &tile_cols[dj * usable..(dj + 1) * usable];
                    hash_pub_w_col_cshake(j0 + dj, col)
                })
            })
            .collect();
        let tree0 = build_merkle_tree_dom(PUB_W_NODE_DOM, leaves);
        let weight_whir_root = tree0.last().unwrap()[0];

        Ok(Self {
            model_root: WeightModelRoot24L {
                weight_whir_root,
                safetensors_param_root,
                bpe_rom_root: bpe_rom.rom_merkle_root,
                max_row_l1,
                max_conv_l1,
                max_gain_abs,
                max_gdn_qk_gain,
                max_scalar_abs,
            },
            shape,
            rows_i16,
            row_evals,
            tree0,
        })
    }

    #[inline]
    pub fn read_i64(&self, st_id: usize, u: usize) -> i64 {
        let cell = self.shape.subtables[st_id].base_cell + u;
        let r = cell >> self.shape.mc;
        let col = cell & (self.shape.w0 - 1);
        self.rows_i16[r].as_ref().map_or(0, |row| row[col] as i64)
    }

    #[inline]
    pub fn row_slice_i16<'a>(
        &'a self,
        st_id: usize,
        offset_in_st: usize,
        len: usize,
        zero_scratch: &'a [i16],
    ) -> &'a [i16] {
        let cell = self.shape.subtables[st_id].base_cell + offset_in_st;
        let r = cell >> self.shape.mc;
        let col = cell & (self.shape.w0 - 1);
        debug_assert!(col + len <= self.shape.w0);
        match &self.rows_i16[r] {
            Some(row) => &row[col..col + len],
            None => &zero_scratch[..len],
        }
    }

    /// Evaluate `\widetilde{W}_{st_id}(d, z_{mid}, hi)` into `out[hi + (d << log_hi)]` (`hi` at low bits for `einsum`!).
    pub fn fold_mid_weight_for_einsum(
        &self,
        st_id: usize,
        log_d: usize,
        log_mid: usize,
        log_hi: usize,
        z_mid: &[Ext4],
    ) -> Vec<Ext4> {
        let d_len = 1usize << log_d;
        let mid_len = 1usize << log_mid;
        let hi_len = 1usize << log_hi;
        assert_eq!(log_d + log_mid + log_hi, self.shape.subtables[st_id].m_vars);
        let eq_mid = build_eq_table_lsb_ext4(z_mid);
        let base_st = self.shape.subtables[st_id].base_cell;
        let mc = self.shape.mc;
        let w0 = self.shape.w0;

        let pairs: Vec<Vec<Ext4>> = (0..hi_len)
            .into_par_iter()
            .map(|hi| {
                let mut acc_d = vec![[0i128; 4]; d_len];
                let hi_base = base_st + (hi << (log_d + log_mid));
                for m in 0..mid_len {
                    let ew = eq_mid[m].0;
                    let cell0 = hi_base + (m << log_d);
                    let r = cell0 >> mc;
                    if let Some(row) = &self.rows_i16[r] {
                        let col0 = cell0 & (w0 - 1);
                        let sl = &row[col0..col0 + d_len];
                        for d in 0..d_len {
                            let v = sl[d] as i128;
                            if v != 0 {
                                acc_d[d][0] += v * (ew[0] as i128);
                                acc_d[d][1] += v * (ew[1] as i128);
                                acc_d[d][2] += v * (ew[2] as i128);
                                acc_d[d][3] += v * (ew[3] as i128);
                            }
                        }
                    }
                }
                acc_d
                    .into_iter()
                    .map(|a| {
                        Ext4([
                            a[0].rem_euclid(P as i128) as u32,
                            a[1].rem_euclid(P as i128) as u32,
                            a[2].rem_euclid(P as i128) as u32,
                            a[3].rem_euclid(P as i128) as u32,
                        ])
                    })
                    .collect()
            })
            .collect();

        let mut out = vec![Ext4::ZERO; hi_len * d_len];
        for (hi, vec_d) in pairs.into_iter().enumerate() {
            for (d, val) in vec_d.into_iter().enumerate() {
                out[hi + (d << log_hi)] = val;
            }
        }
        out
    }

    pub fn eval_subtable_point(&self, st_id: usize, pt: &[Ext4]) -> Ext4 {
        let st = self.shape.subtables[st_id];
        assert_eq!(pt.len(), st.m_vars);
        let mc = self.shape.mc;
        let w0 = self.shape.w0;
        if st.m_vars <= mc {
            let eq = build_eq_table_lsb_ext4(pt);
            let r = st.base_cell >> mc;
            let col0 = st.base_cell & (w0 - 1);
            let Some(row) = &self.rows_i16[r] else {
                return Ext4::ZERO;
            };
            let sl = &row[col0..col0 + eq.len()];
            let mut acc = [0i128; 4];
            for (&v, &e) in sl.iter().zip(eq.iter()) {
                let vi = v as i128;
                if vi != 0 {
                    acc[0] += vi * (e.0[0] as i128);
                    acc[1] += vi * (e.0[1] as i128);
                    acc[2] += vi * (e.0[2] as i128);
                    acc[3] += vi * (e.0[3] as i128);
                }
            }
            Ext4([
                acc[0].rem_euclid(P as i128) as u32,
                acc[1].rem_euclid(P as i128) as u32,
                acc[2].rem_euclid(P as i128) as u32,
                acc[3].rem_euclid(P as i128) as u32,
            ])
        } else {
            let eq_col = build_eq_table_lsb_ext4(&pt[..mc]);
            let eq_row = build_eq_table_lsb_ext4(&pt[mc..]);
            let r_start = st.base_cell >> mc;
            (0..eq_row.len())
                .into_par_iter()
                .map(|dr| {
                    let rw = eq_row[dr];
                    let Some(row) = &self.rows_i16[r_start + dr] else {
                        return Ext4::ZERO;
                    };
                    let mut acc = [0i128; 4];
                    for (&v, &ec) in row.iter().zip(eq_col.iter()) {
                        let vi = v as i128;
                        if vi != 0 {
                            acc[0] += vi * (ec.0[0] as i128);
                            acc[1] += vi * (ec.0[1] as i128);
                            acc[2] += vi * (ec.0[2] as i128);
                            acc[3] += vi * (ec.0[3] as i128);
                        }
                    }
                    let dot = Ext4([
                        acc[0].rem_euclid(P as i128) as u32,
                        acc[1].rem_euclid(P as i128) as u32,
                        acc[2].rem_euclid(P as i128) as u32,
                        acc[3].rem_euclid(P as i128) as u32,
                    ]);
                    rw.mul(dot)
                })
                .reduce(|| Ext4::ZERO, |a, b| a.add(b))
        }
    }
}

#[derive(Clone, Debug)]
pub struct PublicWeightClaim24L {
    pub terms: Vec<(usize, Vec<Ext4>, Ext4)>, // `(subtable, point, weight)`
    pub rhs: Ext4,
}

impl PublicWeightClaim24L {
    pub fn point_eval(subtable: usize, point: Vec<Ext4>, rhs: Ext4) -> Self {
        Self {
            terms: vec![(subtable, point, Ext4::ONE)],
            rhs,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicWeightOpeningProof24L {
    pub row_sc_rounds: Vec<[Ext4; 3]>,
    pub col_sc_rounds: Vec<[Ext4; 3]>,
    pub u_eval_at_zeta: Ext4,
    pub u_prox_at_zeta: Ext4,
    pub s0_col_vals: Vec<u32>,
    pub s0_multiproof: MerkleMultiProof,
    pub cascade_levels: Vec<WhirCascadeLevelProofExt4>,
    pub final_ood_evals: [Ext4; 2],
    pub final_poly: Vec<Ext4>,
}

impl PublicWeightOpeningProof24L {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.row_sc_rounds.len() as u8);
        out.push(self.col_sc_rounds.len() as u8);
        let mut hdr = Vec::with_capacity(
            2 + (self.row_sc_rounds.len() + self.col_sc_rounds.len()) * 3,
        );
        hdr.push(self.u_eval_at_zeta);
        hdr.push(self.u_prox_at_zeta);
        for r in &self.row_sc_rounds {
            hdr.extend_from_slice(r);
        }
        for r in &self.col_sc_rounds {
            hdr.extend_from_slice(r);
        }
        pack_ext4_slice(&hdr, out);
        pack_bb_31b(&self.s0_col_vals, out);
        self.s0_multiproof.write_to(out);
        out.push(self.cascade_levels.len() as u8);
        for cl in &self.cascade_levels {
            out.extend_from_slice(&cl.root);
            out.push(cl.lockstep_sc.len() as u8);
            let mut lhdr = Vec::with_capacity(2 + cl.lockstep_sc.len() * 3);
            lhdr.extend_from_slice(&cl.ood_evals);
            for r in &cl.lockstep_sc {
                lhdr.extend_from_slice(r);
            }
            pack_ext4_slice(&lhdr, out);
            pack_ext4_slice(&cl.opened_fibers, out);
            cl.multiproof.write_to(out);
        }
        pack_ext4_slice(&self.final_ood_evals, out);
        pack_ext4_slice(&self.final_poly, out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let n_rsc = cur.read_u8()? as usize;
        let n_csc = cur.read_u8()? as usize;
        if n_rsc != 10 || n_csc != 21 {
            return Err("invalid PublicWeightOpeningProof24L round counts".into());
        }
        let need = 2 + (n_rsc + n_csc) * 3;
        let hdr = unpack_ext4_slice(cur, need)?;
        if hdr.len() != need {
            return Err("PublicWeightOpeningProof24L header mismatch".into());
        }
        let u_eval_at_zeta = hdr[0];
        let u_prox_at_zeta = hdr[1];
        let mut row_sc_rounds = Vec::with_capacity(n_rsc);
        for i in 0..n_rsc {
            let st = 2 + 3 * i;
            row_sc_rounds.push([hdr[st], hdr[st + 1], hdr[st + 2]]);
        }
        let mut col_sc_rounds = Vec::with_capacity(n_csc);
        for i in 0..n_csc {
            let st = 2 + 3 * (n_rsc + i);
            col_sc_rounds.push([hdr[st], hdr[st + 1], hdr[st + 2]]);
        }
        let s0_col_vals = unpack_bb_31b(cur, 1 << 20)?;
        let s0_multiproof = MerkleMultiProof::read_from(cur)?;
        let n_cl = cur.read_u8()? as usize;
        if n_cl == 0 || n_cl > 8 {
            return Err("invalid PublicWeightOpeningProof24L cascade count".into());
        }
        let mut cascade_levels = Vec::with_capacity(n_cl);
        for _ in 0..n_cl {
            let root = cur.read_arr32()?;
            let n_lsc = cur.read_u8()? as usize;
            if n_lsc == 0 || n_lsc > 4 {
                return Err("invalid lockstep_sc len".into());
            }
            let lhdr = unpack_ext4_slice(cur, 2 + n_lsc * 3)?;
            if lhdr.len() != 2 + n_lsc * 3 {
                return Err("lhdr mismatch".into());
            }
            let ood_evals = [lhdr[0], lhdr[1]];
            let lockstep_sc = (0..n_lsc)
                .map(|i| [lhdr[2 + 3 * i], lhdr[2 + 3 * i + 1], lhdr[2 + 3 * i + 2]])
                .collect();
            let opened_fibers = unpack_ext4_slice(cur, 1 << 15)?;
            let multiproof = MerkleMultiProof::read_from(cur)?;
            cascade_levels.push(WhirCascadeLevelProofExt4 {
                root,
                ood_evals,
                lockstep_sc,
                opened_fibers,
                multiproof,
            });
        }
        let fo = unpack_ext4_slice(cur, 2)?;
        if fo.len() != 2 {
            return Err("final_ood_evals len mismatch".into());
        }
        let final_poly = unpack_ext4_slice(cur, 256)?;
        Ok(Self {
            row_sc_rounds,
            col_sc_rounds,
            u_eval_at_zeta,
            u_prox_at_zeta,
            s0_col_vals,
            s0_multiproof,
            cascade_levels,
            final_ood_evals: [fo[0], fo[1]],
            final_poly,
        })
    }
}

#[inline]
fn squeeze_non_base_ext4_local(tr: &mut CShakeTranscript, label: &[u8]) -> Ext4 {
    loop {
        let c = tr.squeeze_ext4(label, true);
        if c.0[1] != 0 || c.0[2] != 0 || c.0[3] != 0 {
            return c;
        }
    }
}

fn combine_sparse_i16_rows_ext4(
    rows_i16: &[Option<Vec<i16>>],
    w0: usize,
    row_weights: &[Ext4],
) -> Vec<Ext4> {
    let mut out = vec![Ext4::ZERO; w0];
    let active: Vec<(usize, Ext4)> = row_weights
        .iter()
        .copied()
        .enumerate()
        .filter(|&(r, w)| r < rows_i16.len() && rows_i16[r].is_some() && !w.is_zero())
        .collect();
    out.par_chunks_mut(512).enumerate().for_each(|(blk, dst)| {
        let c0 = blk * 512;
        let mut acc = vec![[0i128; 4]; dst.len()];
        for (step, &(r, rw)) in active.iter().enumerate() {
            let row = rows_i16[r].as_ref().unwrap();
            let sl = &row[c0..c0 + dst.len()];
            let w = rw.0;
            for (dc, &v) in sl.iter().enumerate() {
                let vi = v as i128;
                if vi != 0 {
                    acc[dc][0] += vi * (w[0] as i128);
                    acc[dc][1] += vi * (w[1] as i128);
                    acc[dc][2] += vi * (w[2] as i128);
                    acc[dc][3] += vi * (w[3] as i128);
                }
            }
            if (step & 15) == 15 {
                for a in &mut acc {
                    for l in a.iter_mut() {
                        *l = l.rem_euclid(P as i128);
                    }
                }
            }
        }
        for (dc, slot) in dst.iter_mut().enumerate() {
            *slot = Ext4([
                acc[dc][0].rem_euclid(P as i128) as u32,
                acc[dc][1].rem_euclid(P as i128) as u32,
                acc[dc][2].rem_euclid(P as i128) as u32,
                acc[dc][3].rem_euclid(P as i128) as u32,
            ]);
        }
    });
    out
}

fn encode_ext4_on_coset_fast(lvl: &CosetLevelExt4, poly: &[Ext4]) -> Vec<Ext4> {
    let w = poly.len();
    let plan = PackedNttPlanBb::new(lvl.n_pts);
    let mut sp = Vec::with_capacity(w);
    let mut cur = 1u32;
    for _ in 0..w {
        sp.push(cur);
        cur = bmul(cur, lvl.shift);
    }
    let limbs: Vec<Vec<u32>> = (0..4usize)
        .into_par_iter()
        .map(|l| {
            let mut buf = vec![0u32; lvl.n_pts];
            for k in 0..w {
                buf[k] = bmul(poly[k].0[l], sp[k]);
            }
            plan.forward_in_place(&mut buf);
            buf
        })
        .collect();
    (0..lvl.n_pts)
        .into_par_iter()
        .map(|j| Ext4([limbs[0][j], limbs[1][j], limbs[2][j], limbs[3][j]]))
        .collect()
}

fn build_monomial_tensor_local(z: Ext4, log_w: usize) -> Vec<Ext4> {
    let mut v = Vec::with_capacity(1usize << log_w);
    v.push(Ext4::ONE);
    let mut z_pow = z;
    for _ in 0..log_w {
        let cur_len = v.len();
        for i in 0..cur_len {
            let prod = v[i].mul(z_pow);
            v.push(prod);
        }
        z_pow = z_pow.sq();
    }
    v
}

/// Memory-lean (`0` `16 GiB` `Ext4` allocation!) WHIR batch opener for `PrecomputedModelWeights24L`:
/// folds `mr = 10` row variables FIRST via rank-1 separable claim structure, then `mc = 21` col variables!
pub fn open_public_weight_whir_24l(
    weights: &PrecomputedModelWeights24L,
    claims: &[PublicWeightClaim24L],
    tr: &mut CShakeTranscript,
) -> PublicWeightOpeningProof24L {
    let sh = &weights.shape;
    tr.absorb_root(b"pubw_root", &weights.model_root.weight_whir_root);
    tr.absorb_bytes(b"pubw_shape", &sh.tag_bytes());
    tr.absorb_u32(b"pubw_ncl", claims.len() as u32);
    for cl in claims {
        tr.absorb_u32(b"pubw_nterms", cl.terms.len() as u32);
        for (st_id, pt, w) in &cl.terms {
            tr.absorb_u32(b"pubw_stid", *st_id as u32);
            tr.absorb_ext4_slice(b"pubw_pt", pt);
            tr.absorb_ext4(b"pubw_wt", *w);
        }
        tr.absorb_ext4(b"pubw_rhs", cl.rhs);
    }
    let beta = tr.squeeze_ext4(b"pubw_beta", true);

    // Flatten `(scale, st_id, point)` terms:
    let mut flat_terms: Vec<(Ext4, usize, Vec<Ext4>)> = Vec::new();
    let mut b_pw = Ext4::ONE;
    for cl in claims {
        for (st_id, pt, w) in &cl.terms {
            flat_terms.push((b_pw.mul(*w), *st_id, pt.clone()));
        }
        b_pw = b_pw.mul(beta);
    }

    // For each term `t`, decompose into `(a_row[0..rd], m_row[0..rd])` where `m_row[r] = <v_unit_t, W(·, r)>`
    // is evaluated across ALL `r in 0..sh.usable_rows` so `\widetilde{m_row}(r_row) == <v_unit_t, W(·, r_row)>`!
    let term_pairs: Vec<(Vec<Ext4>, Vec<Ext4>)> = flat_terms
        .par_iter()
        .map(|&(scale, st_id, ref pt)| {
            let st = sh.subtables[st_id];
            assert_eq!(pt.len(), st.m_vars);
            let mut a_row = vec![Ext4::ZERO; sh.rd];
            let mut m_row = vec![Ext4::ZERO; sh.rd];
            if st.m_vars <= sh.mc {
                let r_owner = st.base_cell >> sh.mc;
                let col0 = st.base_cell & (sh.w0 - 1);
                a_row[r_owner] = scale;
                let eq_lo = build_eq_table_lsb_ext4(pt);
                for r_idx in 0..sh.usable_rows {
                    if let Some(row) = &weights.rows_i16[r_idx] {
                        let sl = &row[col0..col0 + eq_lo.len()];
                        let mut acc = [0i128; 4];
                        for (&v, &e) in sl.iter().zip(eq_lo.iter()) {
                            let vi = v as i128;
                            if vi != 0 {
                                acc[0] += vi * (e.0[0] as i128);
                                acc[1] += vi * (e.0[1] as i128);
                                acc[2] += vi * (e.0[2] as i128);
                                acc[3] += vi * (e.0[3] as i128);
                            }
                        }
                        m_row[r_idx] = Ext4([
                            acc[0].rem_euclid(P as i128) as u32,
                            acc[1].rem_euclid(P as i128) as u32,
                            acc[2].rem_euclid(P as i128) as u32,
                            acc[3].rem_euclid(P as i128) as u32,
                        ]);
                    }
                }
            } else {
                let eq_lo10 = build_eq_table_lsb_ext4(&pt[..10]);
                let eq_hi11 = build_eq_table_lsb_ext4(&pt[10..sh.mc]);
                let eq_r = build_eq_table_lsb_ext4(&pt[sh.mc..]);
                let r_start = st.base_cell >> sh.mc;
                for (dr, &er) in eq_r.iter().enumerate() {
                    a_row[r_start + dr] = scale.mul(er);
                }
                let active_hi: Vec<(usize, Ext4)> = eq_hi11
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|&(_, eh)| !eh.is_zero())
                    .collect();
                for r_idx in 0..sh.usable_rows {
                    if let Some(row) = &weights.rows_i16[r_idx] {
                        let mut row_dot = Ext4::ZERO;
                        for &(hi, eh) in &active_hi {
                            let sl = &row[(hi << 10)..((hi + 1) << 10)];
                            let mut b_acc = [0i64; 4];
                            for (lo, &v) in sl.iter().enumerate() {
                                if v != 0 {
                                    let vi = v as i64;
                                    let ew = eq_lo10[lo].0;
                                    b_acc[0] += vi * (ew[0] as i64);
                                    b_acc[1] += vi * (ew[1] as i64);
                                    b_acc[2] += vi * (ew[2] as i64);
                                    b_acc[3] += vi * (ew[3] as i64);
                                }
                            }
                            let blk_ext = Ext4([
                                b_acc[0].rem_euclid(P as i64) as u32,
                                b_acc[1].rem_euclid(P as i64) as u32,
                                b_acc[2].rem_euclid(P as i64) as u32,
                                b_acc[3].rem_euclid(P as i64) as u32,
                            ]);
                            row_dot = row_dot.add(eh.mul(blk_ext));
                        }
                        m_row[r_idx] = row_dot;
                    }
                }
            }
            (a_row, m_row)
        })
        .collect();

    // 1. `mr = 10`-round Row Sumcheck over `r in {0, 1}^{10}`:
    let mut cur_pairs = term_pairs;
    let mut row_sc_rounds = Vec::with_capacity(sh.mr);
    let mut r_row = Vec::with_capacity(sh.mr);
    let mut cur_r_len = sh.rd;
    for _ in 0..sh.mr {
        let half = cur_r_len / 2;
        let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for (a_v, m_v) in &cur_pairs {
            for u in 0..half {
                let (a0, a1) = (a_v[2 * u], a_v[2 * u + 1]);
                let (m0, m1) = (m_v[2 * u], m_v[2 * u + 1]);
                if a0.is_zero() && a1.is_zero() {
                    continue;
                }
                let da = a1.sub(a0);
                let dm = m1.sub(m0);
                c0 = c0.add(a0.mul(m0));
                c1 = c1.add(a0.mul(dm).add(da.mul(m0)));
                c2 = c2.add(da.mul(dm));
            }
        }
        let poly = [c0, c1, c2];
        tr.absorb_ext4_slice(b"pubw_rsc", &poly);
        let ch = tr.squeeze_ext4(b"pubw_rz", true);
        row_sc_rounds.push(poly);
        r_row.push(ch);
        for (a_v, m_v) in &mut cur_pairs {
            *a_v = fold_ext4(a_v, ch);
            *m_v = fold_ext4(m_v, ch);
        }
        cur_r_len = half;
    }

    // 2. Build `u_eval[0..w0]` (`W(·, r_row)`) & combined column weight `v_col[0..w0]`:
    let eq_r_row = build_eq_table_lsb_ext4(&r_row);
    let u_eval = combine_sparse_i16_rows_ext4(&weights.rows_i16, sh.w0, &eq_r_row);

    let mut v_col = vec![Ext4::ZERO; sh.w0];
    for (&(scale, st_id, ref pt), (a_folded, _)) in flat_terms.iter().zip(cur_pairs.iter()) {
        let _ = scale;
        let row_scalar = a_folded[0]; // equals `scale * row_prefix_mle(r_row)`!
        let st = sh.subtables[st_id];
        if st.m_vars <= sh.mc {
            let col0 = st.base_cell & (sh.w0 - 1);
            let eq_lo = build_eq_table_lsb_ext4(pt);
            for (dc, &e) in eq_lo.iter().enumerate() {
                v_col[col0 + dc] = v_col[col0 + dc].add(row_scalar.mul(e));
            }
        } else {
            let eq_lo10 = build_eq_table_lsb_ext4(&pt[..10]);
            let eq_hi11 = build_eq_table_lsb_ext4(&pt[10..sh.mc]);
            for (hi, &eh) in eq_hi11.iter().enumerate() {
                if eh.is_zero() {
                    continue;
                }
                let sc_hi = row_scalar.mul(eh);
                let dst = &mut v_col[(hi << 10)..((hi + 1) << 10)];
                for (lo, &el) in eq_lo10.iter().enumerate() {
                    dst[lo] = dst[lo].add(sc_hi.mul(el));
                }
            }
        }
    }

    // `mc = 21`-round Column Sumcheck `<v_col, u_eval>`:
    let mut v_cur = v_col;
    let mut u_cur = u_eval.clone();
    let mut col_sc_rounds = Vec::with_capacity(sh.mc);
    let mut zeta = Vec::with_capacity(sh.mc);
    for _ in 0..sh.mc {
        let half = v_cur.len() / 2;
        let eval_u = |u: usize| -> [Ext4; 3] {
            let (v0, v1) = (v_cur[2 * u], v_cur[2 * u + 1]);
            let (p0, p1) = (u_cur[2 * u], u_cur[2 * u + 1]);
            let dv = v1.sub(v0);
            let dp = p1.sub(p0);
            [v0.mul(p0), v0.mul(dp).add(dv.mul(p0)), dv.mul(dp)]
        };
        let poly = if half >= 2048 {
            (0..half).into_par_iter().map(eval_u).reduce(
                || [Ext4::ZERO; 3],
                |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
            )
        } else {
            let mut acc = [Ext4::ZERO; 3];
            for u in 0..half {
                let x = eval_u(u);
                for k in 0..3 {
                    acc[k] = acc[k].add(x[k]);
                }
            }
            acc
        };
        tr.absorb_ext4_slice(b"pubw_csc", &poly);
        let zi = tr.squeeze_ext4(b"pubw_cz", true);
        col_sc_rounds.push(poly);
        zeta.push(zi);
        if half >= 4096 {
            v_cur = (0..half)
                .into_par_iter()
                .map(|u| v_cur[2 * u].add(zi.mul(v_cur[2 * u + 1].sub(v_cur[2 * u]))))
                .collect();
            u_cur = (0..half)
                .into_par_iter()
                .map(|u| u_cur[2 * u].add(zi.mul(u_cur[2 * u + 1].sub(u_cur[2 * u]))))
                .collect();
        } else {
            v_cur = fold_ext4(&v_cur, zi);
            u_cur = fold_ext4(&u_cur, zi);
        }
    }
    let u_eval_at_zeta = u_cur[0];
    tr.absorb_ext4(b"pubw_uez", u_eval_at_zeta);

    // 3. Proximity RLC `u_prox` + WHIR cascade (`k_sched = [3, 3, 3, 3, 2]`):
    let gamma = tr.squeeze_ext4(b"pubw_gamma", true);
    let mut g_pows = Vec::with_capacity(sh.usable_rows);
    let mut gp = Ext4::ONE;
    for _ in 0..sh.usable_rows {
        g_pows.push(gp);
        gp = gp.mul(gamma);
    }
    let u_prox = combine_sparse_i16_rows_ext4(&weights.rows_i16, sh.w0, &g_pows);
    let eq_zeta = build_eq_table_lsb_ext4(&zeta);
    let u_prox_at_zeta = u_prox
        .par_iter()
        .zip(eq_zeta.par_iter())
        .map(|(&u, &e)| u.mul(e))
        .reduce(|| Ext4::ZERO, |a, b| a.add(b));
    tr.absorb_ext4(b"pubw_uprz", u_prox_at_zeta);
    let th_ev = tr.squeeze_ext4(b"pubw_thev", true);

    let mut cur_poly: Vec<Ext4> = u_prox
        .par_iter()
        .zip(u_eval.par_iter())
        .map(|(&p, &e)| p.add(th_ev.mul(e)))
        .collect();
    let mut w_acc = eq_zeta;
    let k_sched = canonical_ext4_k_schedule(sh.mc);
    let mut cur_level = CosetLevelExt4::new(sh.n0.trailing_zeros() as usize);

    struct PendingPub {
        level: CosetLevelExt4,
        kr: usize,
        cw: Vec<Ext4>,
        tree: Vec<Vec<[u8; 32]>>,
        root: [u8; 32],
        ood_evals: [Ext4; 2],
        lockstep_sc: Vec<[Ext4; 3]>,
    }
    let mut pending = Vec::with_capacity(k_sched.len());

    for (r, &kr) in k_sched.iter().enumerate() {
        let cw = encode_ext4_on_coset_fast(&cur_level, &cur_poly);
        let n_fibers = cur_level.n_pts >> kr;
        let leaves: Vec<[u8; 32]> = (0..n_fibers)
            .into_par_iter()
            .map(|f_idx| {
                let js = cur_level.fiber_point_indices(kr, f_idx);
                let fv: Vec<Ext4> = js.into_iter().map(|j| cw[j]).collect();
                hash_pub_w_fiber_cshake(r, f_idx, &fv)
            })
            .collect();
        let tree = build_merkle_tree_dom(PUB_W_NODE_DOM, leaves);
        let root = tree.last().unwrap()[0];
        tr.absorb_root(b"pubw_froot", &root);

        let z0 = squeeze_non_base_ext4_local(tr, b"pubw_z0");
        let z1 = squeeze_non_base_ext4_local(tr, b"pubw_z1");
        let o0 = eval_poly_ext4(&cur_poly, z0);
        let o1 = eval_poly_ext4(&cur_poly, z1);
        tr.absorb_ext4(b"pubw_o0", o0);
        tr.absorb_ext4(b"pubw_o1", o1);
        let t0 = tr.squeeze_ext4(b"pubw_t0", true);
        let t1 = tr.squeeze_ext4(b"pubw_t1", true);

        let lg_w = cur_poly.len().trailing_zeros() as usize;
        let m0 = build_monomial_tensor_local(z0, lg_w);
        let m1 = build_monomial_tensor_local(z1, lg_w);
        w_acc
            .par_iter_mut()
            .enumerate()
            .for_each(|(u, w)| *w = w.add(t0.mul(m0[u])).add(t1.mul(m1[u])));

        let mut sc = Vec::with_capacity(kr);
        for _ in 0..kr {
            let half = cur_poly.len() / 2;
            let eval_l = |u: usize| -> [Ext4; 3] {
                let (w0, w1) = (w_acc[2 * u], w_acc[2 * u + 1]);
                let (f0, f1) = (cur_poly[2 * u], cur_poly[2 * u + 1]);
                let dw = w1.sub(w0);
                let df = f1.sub(f0);
                [w0.mul(f0), w0.mul(df).add(dw.mul(f0)), dw.mul(df)]
            };
            let poly = if half >= 2048 {
                (0..half).into_par_iter().map(eval_l).reduce(
                    || [Ext4::ZERO; 3],
                    |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
                )
            } else {
                let mut acc = [Ext4::ZERO; 3];
                for u in 0..half {
                    let x = eval_l(u);
                    for k in 0..3 {
                        acc[k] = acc[k].add(x[k]);
                    }
                }
                acc
            };
            tr.absorb_ext4_slice(b"pubw_lsc", &poly);
            let alpha = tr.squeeze_ext4(b"pubw_alpha", true);
            sc.push(poly);
            w_acc = fold_ext4(&w_acc, alpha);
            cur_poly = fold_ext4(&cur_poly, alpha);
        }
        pending.push(PendingPub {
            level: cur_level,
            kr,
            cw,
            tree,
            root,
            ood_evals: [o0, o1],
            lockstep_sc: sc,
        });
        cur_level = cur_level.fold(kr);
    }

    tr.absorb_ext4_slice(b"pubw_fpoly", &cur_poly);
    let zf0 = squeeze_non_base_ext4_local(tr, b"pubw_fz0");
    let zf1 = squeeze_non_base_ext4_local(tr, b"pubw_fz1");
    let fo0 = eval_poly_ext4(&cur_poly, zf0);
    let fo1 = eval_poly_ext4(&cur_poly, zf1);
    tr.absorb_ext4(b"pubw_fo0", fo0);
    tr.absorb_ext4(b"pubw_fo1", fo1);

    let q_indices = tr.squeeze_distinct_indices(b"pubw_queries", sh.n0, PUBLIC_WEIGHT_T_QUERIES);
    let mut s0_col_vals = Vec::with_capacity(q_indices.len() * sh.usable_rows);
    for &c_idx in &q_indices {
        for r in 0..sh.usable_rows {
            let v = weights.row_evals[r].as_ref().map_or(0u32, |ev| ev[c_idx]);
            s0_col_vals.push(v);
        }
    }
    let s0_multiproof = MerkleMultiProof::build(&weights.tree0, &q_indices);

    let mut cur_pts = q_indices;
    let mut cascade_levels = Vec::with_capacity(pending.len());
    for pt in pending {
        let n_fibers = pt.level.n_pts >> pt.kr;
        let mask_f = n_fibers - 1;
        let mut uniq_f = BTreeSet::new();
        for &p_idx in &cur_pts {
            uniq_f.insert(p_idx & mask_f);
        }
        let uniq_fibers: Vec<usize> = uniq_f.into_iter().collect();
        let mut opened_fibers = Vec::with_capacity(uniq_fibers.len() * (1usize << pt.kr));
        for &f_idx in &uniq_fibers {
            for j in pt.level.fiber_point_indices(pt.kr, f_idx) {
                opened_fibers.push(pt.cw[j]);
            }
        }
        let multiproof = MerkleMultiProof::build(&pt.tree, &uniq_fibers);
        cascade_levels.push(WhirCascadeLevelProofExt4 {
            root: pt.root,
            ood_evals: pt.ood_evals,
            lockstep_sc: pt.lockstep_sc,
            opened_fibers,
            multiproof,
        });
        cur_pts = uniq_fibers;
    }

    PublicWeightOpeningProof24L {
        row_sc_rounds,
        col_sc_rounds,
        u_eval_at_zeta,
        u_prox_at_zeta,
        s0_col_vals,
        s0_multiproof,
        cascade_levels,
        final_ood_evals: [fo0, fo1],
        final_poly: cur_poly,
    }
}

pub fn verify_public_weight_whir_24l(
    root: &[u8; 32],
    sh: &PublicWeightWhirShape24L,
    claims: &[PublicWeightClaim24L],
    prf: &PublicWeightOpeningProof24L,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    if prf.row_sc_rounds.len() != sh.mr || prf.col_sc_rounds.len() != sh.mc {
        return Err("PublicWeightOpeningProof24L round count mismatch".into());
    }
    tr.absorb_root(b"pubw_root", root);
    tr.absorb_bytes(b"pubw_shape", &sh.tag_bytes());
    tr.absorb_u32(b"pubw_ncl", claims.len() as u32);
    for cl in claims {
        tr.absorb_u32(b"pubw_nterms", cl.terms.len() as u32);
        for (st_id, pt, w) in &cl.terms {
            tr.absorb_u32(b"pubw_stid", *st_id as u32);
            tr.absorb_ext4_slice(b"pubw_pt", pt);
            tr.absorb_ext4(b"pubw_wt", *w);
        }
        tr.absorb_ext4(b"pubw_rhs", cl.rhs);
    }
    let beta = tr.squeeze_ext4(b"pubw_beta", true);
    let mut running = Ext4::ZERO;
    let mut beta_pows = Vec::with_capacity(claims.len());
    let mut b_pw = Ext4::ONE;
    for cl in claims {
        running = running.add(b_pw.mul(cl.rhs));
        beta_pows.push(b_pw);
        b_pw = b_pw.mul(beta);
    }

    let mut r_row = Vec::with_capacity(sh.mr);
    for (i, poly) in prf.row_sc_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != running {
            return Err(format!("PublicWeight row sumcheck round {i} failed"));
        }
        tr.absorb_ext4_slice(b"pubw_rsc", poly);
        let ch = tr.squeeze_ext4(b"pubw_rz", true);
        r_row.push(ch);
        running = eval_poly_ext4(poly, ch);
    }

    let mut zeta = Vec::with_capacity(sh.mc);
    for (i, poly) in prf.col_sc_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != running {
            return Err(format!("PublicWeight col sumcheck round {i} failed"));
        }
        tr.absorb_ext4_slice(b"pubw_csc", poly);
        let ch = tr.squeeze_ext4(b"pubw_cz", true);
        zeta.push(ch);
        running = eval_poly_ext4(poly, ch);
    }

    // Evaluate `V_col(zeta)` in `O(|terms| * (mc + mr))` muls:
    let mut z_full = Vec::with_capacity(sh.mc + sh.mr);
    z_full.extend_from_slice(&zeta);
    z_full.extend_from_slice(&r_row);
    let m_bits = sh.mc + sh.mr;
    let mut v_at_zeta = Ext4::ZERO;
    for (q_idx, cl) in claims.iter().enumerate() {
        let bp = beta_pows[q_idx];
        for (st_id, pt, w) in &cl.terms {
            if *st_id >= sh.subtables.len() {
                return Err("PublicWeight subtable OOB".into());
            }
            let st = sh.subtables[*st_id];
            if pt.len() != st.m_vars {
                return Err("PublicWeight point len mismatch".into());
            }
            let prefix = st.base_cell >> st.m_vars;
            let mut ev = bp.mul(*w);
            for (b, &pb) in pt.iter().enumerate() {
                ev = ev.mul(eq_lin_ext4(pb, z_full[b]));
            }
            for b in st.m_vars..m_bits {
                let bit = (prefix >> (b - st.m_vars)) & 1;
                let zb = z_full[b];
                ev = ev.mul(if bit == 1 { zb } else { Ext4::ONE.sub(zb) });
            }
            v_at_zeta = v_at_zeta.add(ev);
        }
    }
    if running != v_at_zeta.mul(prf.u_eval_at_zeta) {
        return Err("PublicWeight col sumcheck terminal check failed".into());
    }

    tr.absorb_ext4(b"pubw_uez", prf.u_eval_at_zeta);
    let gamma = tr.squeeze_ext4(b"pubw_gamma", true);
    tr.absorb_ext4(b"pubw_uprz", prf.u_prox_at_zeta);
    let th_ev = tr.squeeze_ext4(b"pubw_thev", true);

    let k_sched = canonical_ext4_k_schedule(sh.mc);
    if prf.cascade_levels.len() != k_sched.len() {
        return Err("PublicWeight cascade level count mismatch".into());
    }
    let tot_k: usize = k_sched.iter().sum();
    let w_final = sh.w0 >> tot_k;
    if prf.final_poly.len() != w_final {
        return Err("PublicWeight final_poly len mismatch".into());
    }

    let mut lsc_running = prf.u_prox_at_zeta.add(th_ev.mul(prf.u_eval_at_zeta));
    let mut ood_records = Vec::with_capacity(k_sched.len());
    let mut round_alphas = Vec::with_capacity(k_sched.len());
    let mut all_alphas = Vec::with_capacity(tot_k);

    for (r, &kr) in k_sched.iter().enumerate() {
        let cl = &prf.cascade_levels[r];
        if cl.lockstep_sc.len() != kr {
            return Err("PublicWeight lockstep_sc len mismatch".into());
        }
        tr.absorb_root(b"pubw_froot", &cl.root);
        let z0 = squeeze_non_base_ext4_local(tr, b"pubw_z0");
        let z1 = squeeze_non_base_ext4_local(tr, b"pubw_z1");
        tr.absorb_ext4(b"pubw_o0", cl.ood_evals[0]);
        tr.absorb_ext4(b"pubw_o1", cl.ood_evals[1]);
        let t0 = tr.squeeze_ext4(b"pubw_t0", true);
        let t1 = tr.squeeze_ext4(b"pubw_t1", true);
        ood_records.push((all_alphas.len(), z0, t0, z1, t1));
        lsc_running = lsc_running
            .add(t0.mul(cl.ood_evals[0]))
            .add(t1.mul(cl.ood_evals[1]));

        let mut ar = Vec::with_capacity(kr);
        for poly in &cl.lockstep_sc {
            let p0 = poly[0];
            let p1 = poly[0].add(poly[1]).add(poly[2]);
            if p0.add(p1) != lsc_running {
                return Err("PublicWeight lockstep sumcheck round failed".into());
            }
            tr.absorb_ext4_slice(b"pubw_lsc", poly);
            let alpha = tr.squeeze_ext4(b"pubw_alpha", true);
            ar.push(alpha);
            all_alphas.push(alpha);
            lsc_running = eval_poly_ext4(poly, alpha);
        }
        round_alphas.push(ar);
    }

    tr.absorb_ext4_slice(b"pubw_fpoly", &prf.final_poly);
    let zf0 = squeeze_non_base_ext4_local(tr, b"pubw_fz0");
    let zf1 = squeeze_non_base_ext4_local(tr, b"pubw_fz1");
    tr.absorb_ext4(b"pubw_fo0", prf.final_ood_evals[0]);
    tr.absorb_ext4(b"pubw_fo1", prf.final_ood_evals[1]);
    if prf.final_ood_evals[0] != eval_poly_ext4(&prf.final_poly, zf0)
        || prf.final_ood_evals[1] != eval_poly_ext4(&prf.final_poly, zf1)
    {
        return Err("PublicWeight final OOD mismatch".into());
    }

    let mut fin_weights = vec![Ext4::ZERO; w_final];
    let eq_pref = eq_mle_ext4(&zeta[..tot_k], &all_alphas);
    let eq_rem = build_eq_table_lsb_ext4(&zeta[tot_k..]);
    for q in 0..w_final {
        fin_weights[q] = fin_weights[q].add(eq_pref.mul(eq_rem[q]));
    }
    for &(a_off, z0, t0, z1, t1) in &ood_records {
        for (z_ood, tau) in [(z0, t0), (z1, t1)] {
            let mut z_pow = z_ood;
            let mut pref = tau;
            for &ab in &all_alphas[a_off..] {
                pref = pref.mul(Ext4::ONE.sub(ab).add(ab.mul(z_pow)));
                z_pow = z_pow.sq();
            }
            let mut cur = pref;
            for fw in &mut fin_weights {
                *fw = fw.add(cur);
                cur = cur.mul(z_pow);
            }
        }
    }
    let want_lsc = fin_weights
        .iter()
        .zip(prf.final_poly.iter())
        .fold(Ext4::ZERO, |acc, (&w, &f)| acc.add(w.mul(f)));
    if lsc_running != want_lsc {
        return Err("PublicWeight terminal lockstep check failed".into());
    }

    let q_indices = tr.squeeze_distinct_indices(b"pubw_queries", sh.n0, PUBLIC_WEIGHT_T_QUERIES);
    if prf.s0_col_vals.len() != q_indices.len() * sh.usable_rows {
        return Err("PublicWeight s0_col_vals count mismatch".into());
    }
    if prf.s0_col_vals.iter().any(|&v| v >= P_U32) {
        return Err("non-canonical BabyBear element in PublicWeight s0_col_vals".into());
    }
    let leaf_hashes: Vec<[u8; 32]> = (0..q_indices.len())
        .into_par_iter()
        .map(|ui| {
            let col = &prf.s0_col_vals[ui * sh.usable_rows..(ui + 1) * sh.usable_rows];
            hash_pub_w_col_cshake(q_indices[ui], col)
        })
        .collect();
    if !verify_merkle_multiproof_dom(
        PUB_W_NODE_DOM,
        &prf.s0_multiproof,
        root,
        sh.n0,
        &q_indices,
        &leaf_hashes,
    ) {
        return Err("PublicWeight Stage-0 Merkle multiproof failed".into());
    }

    let eq_row = build_eq_table_lsb_ext4(&r_row);
    let mut w_row = Vec::with_capacity(sh.usable_rows);
    let mut gp = Ext4::ONE;
    for r in 0..sh.usable_rows {
        w_row.push(gp.add(th_ev.mul(eq_row[r])));
        gp = gp.mul(gamma);
    }

    let mut prev_vals: Vec<Ext4> = (0..q_indices.len())
        .into_par_iter()
        .map(|ui| {
            let col = &prf.s0_col_vals[ui * sh.usable_rows..(ui + 1) * sh.usable_rows];
            let mut acc = [0u128; 4];
            for (i, (&w, &v)) in w_row.iter().zip(col.iter()).enumerate() {
                let vv = v as u128;
                acc[0] += vv * (w.0[0] as u128);
                acc[1] += vv * (w.0[1] as u128);
                acc[2] += vv * (w.0[2] as u128);
                acc[3] += vv * (w.0[3] as u128);
                if (i & 31) == 31 {
                    for l in &mut acc {
                        *l %= P as u128;
                    }
                }
            }
            Ext4([
                (acc[0] % (P as u128)) as u32,
                (acc[1] % (P as u128)) as u32,
                (acc[2] % (P as u128)) as u32,
                (acc[3] % (P as u128)) as u32,
            ])
        })
        .collect();

    let mut cur_level = CosetLevelExt4::new(sh.n0.trailing_zeros() as usize);
    let mut cur_pts = q_indices;
    for (r, &kr) in k_sched.iter().enumerate() {
        let cl = &prf.cascade_levels[r];
        let b_len = 1usize << kr;
        let n_fibers = cur_level.n_pts >> kr;
        let mask_f = n_fibers - 1;
        let shift_sub = cur_level.log_n - kr;
        let mut uniq_f = BTreeSet::new();
        let mut locs = Vec::with_capacity(cur_pts.len());
        for &p_idx in &cur_pts {
            uniq_f.insert(p_idx & mask_f);
            locs.push((p_idx & mask_f, p_idx >> shift_sub));
        }
        let uniq_fibers: Vec<usize> = uniq_f.into_iter().collect();
        if cl.opened_fibers.len() != uniq_fibers.len() * b_len {
            return Err("PublicWeight opened_fibers len mismatch".into());
        }
        let f_hashes: Vec<[u8; 32]> = (0..uniq_fibers.len())
            .into_par_iter()
            .map(|ui| {
                let fv = &cl.opened_fibers[ui * b_len..(ui + 1) * b_len];
                hash_pub_w_fiber_cshake(r, uniq_fibers[ui], fv)
            })
            .collect();
        if !verify_merkle_multiproof_dom(
            PUB_W_NODE_DOM,
            &cl.multiproof,
            &cl.root,
            n_fibers,
            &uniq_fibers,
            &f_hashes,
        ) {
            return Err("PublicWeight cascade Merkle multiproof failed".into());
        }
        let pos_map: BTreeMap<usize, usize> = uniq_fibers
            .iter()
            .copied()
            .enumerate()
            .map(|(i, f)| (f, i))
            .collect();
        for (i, &(f_idx, sub_pos)) in locs.iter().enumerate() {
            let ui = pos_map[&f_idx];
            if cl.opened_fibers[ui * b_len + sub_pos] != prev_vals[i] {
                return Err("PublicWeight cascade fiber consistency failed".into());
            }
        }
        let b_inv = binv(b_len as u32).unwrap();
        let (_, zeta_r) = cur_level.fiber_base_and_zeta(kr, 0);
        let zeta_inv = bpow(zeta_r, (b_len - 1) as u64);
        let mut z_inv_pows = Vec::with_capacity((b_len / 2).max(1));
        let mut cz = 1u32;
        for _ in 0..(b_len / 2).max(1) {
            z_inv_pows.push(cz);
            cz = bmul(cz, zeta_inv);
        }
        let eq_alpha = build_eq_table_lsb_ext4(&round_alphas[r]);
        prev_vals = (0..uniq_fibers.len())
            .into_par_iter()
            .map(|ui| {
                let x0 = cur_level.fiber_base_and_zeta(kr, uniq_fibers[ui]).0;
                let x0_inv = binv(x0).unwrap();
                let fv = &cl.opened_fibers[ui * b_len..(ui + 1) * b_len];
                let mut buf = fv.to_vec();
                for i in 0..b_len {
                    let rev = i.reverse_bits() >> (usize::BITS - (kr as u32));
                    if i < rev {
                        buf.swap(i, rev);
                    }
                }
                let mut len = 2usize;
                while len <= b_len {
                    let half = len / 2;
                    let step = b_len / len;
                    for st in (0..b_len).step_by(len) {
                        for j in 0..half {
                            let u = buf[st + j];
                            let v = buf[st + j + half].scale_bb(z_inv_pows[j * step]);
                            buf[st + j] = u.add(v);
                            buf[st + j + half] = u.sub(v);
                        }
                    }
                    len <<= 1;
                }
                let mut acc = Ext4::ZERO;
                let mut sc = b_inv;
                for b in 0..b_len {
                    acc = acc.add(eq_alpha[b].mul(buf[b].scale_bb(sc)));
                    sc = bmul(sc, x0_inv);
                }
                acc
            })
            .collect();
        cur_pts = uniq_fibers;
        cur_level = cur_level.fold(kr);
    }

    for (i, &p_idx) in cur_pts.iter().enumerate() {
        let y = cur_level.point(p_idx);
        let mut acc = Ext4::ZERO;
        for &c in prf.final_poly.iter().rev() {
            acc = acc.scale_bb(y).add(c);
        }
        if prev_vals[i] != acc {
            return Err("PublicWeight final_poly point evaluation mismatch".into());
        }
    }
    Ok(())
}

// ================================================================================================
// §4. Rayon-Parallel `D1b` Range & Tuple-LUT Provers + Parallel `GMaskExt4` `EinSumcheck`
// ================================================================================================

fn run_d1b_fraction_tree_par(
    p0: Vec<Ext4>,
    q0: Vec<Ext4>,
    m_wit: usize,
    absorb_root_lbl: &[u8],
    eta_lbl: &[u8],
    c_lbls: [&[u8]; 4],
    ch_lbl: &[u8],
    pq_lbls: [&[u8]; 4],
    rbit_lbl: &[u8],
    tr: &mut CShakeTranscript,
) -> (Ext4, Vec<D1bLayerProof>, Vec<Ext4>) {
    let mut p_layers = Vec::with_capacity(m_wit + 2);
    let mut q_layers = Vec::with_capacity(m_wit + 2);
    p_layers.push(p0);
    q_layers.push(q0);

    for _ in 0..=m_wit {
        let prev_p = p_layers.last().unwrap();
        let prev_q = q_layers.last().unwrap();
        let next_len = prev_p.len() / 2;
        let (np, nq): (Vec<Ext4>, Vec<Ext4>) = if next_len >= 1024 {
            (0..next_len)
                .into_par_iter()
                .map(|i| {
                    let (pl, pr) = (prev_p[2 * i], prev_p[2 * i + 1]);
                    let (ql, qr) = (prev_q[2 * i], prev_q[2 * i + 1]);
                    (pl.mul(qr).add(pr.mul(ql)), ql.mul(qr))
                })
                .unzip()
        } else {
            (0..next_len)
                .map(|i| {
                    let (pl, pr) = (prev_p[2 * i], prev_p[2 * i + 1]);
                    let (ql, qr) = (prev_q[2 * i], prev_q[2 * i + 1]);
                    (pl.mul(qr).add(pr.mul(ql)), ql.mul(qr))
                })
                .unzip()
        };
        p_layers.push(np);
        q_layers.push(nq);
    }

    let root_q = q_layers.last().unwrap()[0];
    tr.absorb_ext4(absorb_root_lbl, root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut layer_proofs = Vec::with_capacity(m_wit + 1);
    let two = Ext4::from_bb(2);

    for step in 0..=m_wit {
        let child_lvl = m_wit - step;
        let child_p = &p_layers[child_lvl];
        let child_q = &q_layers[child_lvl];
        let eta = tr.squeeze_ext4(eta_lbl, true);
        let half = 1usize << step;

        let (mut pl_cur, mut pr_cur): (Vec<Ext4>, Vec<Ext4>) = if half >= 2048 {
            (0..half)
                .into_par_iter()
                .map(|i| (child_p[2 * i], child_p[2 * i + 1]))
                .unzip()
        } else {
            (0..half)
                .map(|i| (child_p[2 * i], child_p[2 * i + 1]))
                .unzip()
        };
        let (mut ql_cur, mut qr_cur): (Vec<Ext4>, Vec<Ext4>) = if half >= 2048 {
            (0..half)
                .into_par_iter()
                .map(|i| (child_q[2 * i], child_q[2 * i + 1]))
                .unzip()
        } else {
            (0..half)
                .map(|i| (child_q[2 * i], child_q[2 * i + 1]))
                .unzip()
        };
        let mut eq_cur = build_eq_table_lsb_ext4(&cur_pt);

        let mut rounds = Vec::with_capacity(step);
        let mut sum_chals = Vec::with_capacity(step);
        for _ in 0..step {
            let h2 = eq_cur.len() / 2;
            let eval_idx = |idx: usize| -> [Ext4; 4] {
                let (e0, e1) = (eq_cur[2 * idx], eq_cur[2 * idx + 1]);
                let de = e1.sub(e0);
                let e2 = e0.add(two.mul(de));
                let (pl0, pl1) = (pl_cur[2 * idx], pl_cur[2 * idx + 1]);
                let dpl = pl1.sub(pl0);
                let pl2 = pl0.add(two.mul(dpl));
                let (pr0, pr1) = (pr_cur[2 * idx], pr_cur[2 * idx + 1]);
                let dpr = pr1.sub(pr0);
                let pr2 = pr0.add(two.mul(dpr));
                let (ql0, ql1) = (ql_cur[2 * idx], ql_cur[2 * idx + 1]);
                let dql = ql1.sub(ql0);
                let ql2 = ql0.add(two.mul(dql));
                let (qr0, qr1) = (qr_cur[2 * idx], qr_cur[2 * idx + 1]);
                let dqr = qr1.sub(qr0);
                let qr2 = qr0.add(two.mul(dqr));

                [
                    e0.mul(pl0.mul(qr0).add(pr0.mul(ql0)).add(eta.mul(ql0.mul(qr0)))),
                    e1.mul(pl1.mul(qr1).add(pr1.mul(ql1)).add(eta.mul(ql1.mul(qr1)))),
                    e2.mul(pl2.mul(qr2).add(pr2.mul(ql2)).add(eta.mul(ql2.mul(qr2)))),
                    de.mul(dpl.mul(dqr).add(dpr.mul(dql)).add(eta.mul(dql.mul(dqr)))),
                ]
            };
            let [p0_acc, p1_acc, p2_acc, pinf_acc] = if h2 >= 2048 {
                (0..h2).into_par_iter().map(eval_idx).reduce(
                    || [Ext4::ZERO; 4],
                    |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2]), a[3].add(b[3])],
                )
            } else {
                let mut acc = [Ext4::ZERO; 4];
                for idx in 0..h2 {
                    let x = eval_idx(idx);
                    for k in 0..4 {
                        acc[k] = acc[k].add(x[k]);
                    }
                }
                acc
            };
            let msg = CubicExt4RoundMsg {
                p0: p0_acc,
                p1: p1_acc,
                p2: p2_acc,
                p_inf: pinf_acc,
            };
            tr.absorb_ext4(c_lbls[0], msg.p0);
            tr.absorb_ext4(c_lbls[1], msg.p1);
            tr.absorb_ext4(c_lbls[2], msg.p2);
            tr.absorb_ext4(c_lbls[3], msg.p_inf);
            rounds.push(msg);
            let ch = tr.squeeze_ext4(ch_lbl, true);
            sum_chals.push(ch);

            if h2 >= 4096 {
                let fold_par = |v: &[Ext4]| -> Vec<Ext4> {
                    (0..h2)
                        .into_par_iter()
                        .map(|i| v[2 * i].add(ch.mul(v[2 * i + 1].sub(v[2 * i]))))
                        .collect()
                };
                eq_cur = fold_par(&eq_cur);
                pl_cur = fold_par(&pl_cur);
                pr_cur = fold_par(&pr_cur);
                ql_cur = fold_par(&ql_cur);
                qr_cur = fold_par(&qr_cur);
            } else {
                eq_cur = fold_ext4(&eq_cur, ch);
                pl_cur = fold_ext4(&pl_cur, ch);
                pr_cur = fold_ext4(&pr_cur, ch);
                ql_cur = fold_ext4(&ql_cur, ch);
                qr_cur = fold_ext4(&qr_cur, ch);
            }
        }

        let (p_lo, p_hi, q_lo, q_hi) = (pl_cur[0], pr_cur[0], ql_cur[0], qr_cur[0]);
        tr.absorb_ext4(pq_lbls[0], p_lo);
        tr.absorb_ext4(pq_lbls[1], p_hi);
        tr.absorb_ext4(pq_lbls[2], q_lo);
        tr.absorb_ext4(pq_lbls[3], q_hi);
        let r_bit = tr.squeeze_ext4(rbit_lbl, true);
        let mut next_pt = Vec::with_capacity(step + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
        layer_proofs.push(D1bLayerProof {
            rounds,
            p_lo,
            p_hi,
            q_lo,
            q_hi,
        });
    }
    (root_q, layer_proofs, cur_pt)
}

/// Parallel `prove_d1b_range_ext4` producing a standard `D1bRangeExt4Proof` verified by `gruen_ext4::verify_d1b_range_ext4`!
pub fn prove_d1b_range_par_ext4(
    rem_table: &[u32],
    mult_table: &[u32],
    m_wit: usize,
    m_tab: usize,
    tr: &mut CShakeTranscript,
) -> (D1bRangeExt4Proof, Vec<Ext4>) {
    let n_wit = 1usize << m_wit;
    let n_tab = 1usize << m_tab;
    assert_eq!(rem_table.len(), n_wit);
    assert_eq!(mult_table.len(), n_tab);
    let alpha = tr.squeeze_ext4(b"d1b_alpha", true);

    let mut p0 = vec![Ext4::ZERO; n_wit * 2];
    let mut q0 = vec![Ext4::ZERO; n_wit * 2];
    p0[..n_wit]
        .par_iter_mut()
        .zip(q0[..n_wit].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            *pd = Ext4::ONE;
            *qd = alpha.sub(Ext4::from_bb(rem_table[x] % P_U32));
        });
    let mask_tab = n_tab - 1;
    p0[n_wit..]
        .par_iter_mut()
        .zip(q0[n_wit..].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            if x < n_tab {
                let m_bb = mult_table[x] % P_U32;
                *pd = Ext4::from_bb(if m_bb == 0 { 0 } else { P_U32 - m_bb });
            } else {
                *pd = Ext4::ZERO;
            }
            *qd = alpha.sub(Ext4::from_bb((x & mask_tab) as u32));
        });

    let (root_q, layers, cur_pt) = run_d1b_fraction_tree_par(
        p0,
        q0,
        m_wit,
        b"d1b_root_q",
        b"d1b_eta",
        [b"d1b_c0", b"d1b_c1", b"d1b_c2", b"d1b_cinf"],
        b"d1b_ch",
        [b"d1b_plo", b"d1b_phi", b"d1b_qlo", b"d1b_qhi"],
        b"d1b_rbit",
        tr,
    );
    let z_leaf = cur_pt[..m_wit].to_vec();
    let rem_leaf_eval = mle_eval_bb_at_ext4(rem_table, &z_leaf);
    let mult_leaf_eval = mle_eval_bb_at_ext4(mult_table, &z_leaf[..m_tab]);
    tr.absorb_ext4(b"d1b_rem_eval", rem_leaf_eval);
    tr.absorb_ext4(b"d1b_mult_eval", mult_leaf_eval);
    (
        D1bRangeExt4Proof {
            m_wit,
            m_tab,
            root_q,
            layers,
            rem_leaf_eval,
            mult_leaf_eval,
        },
        z_leaf,
    )
}

/// Multi-column `Ext4`-RLC `D1b` public-table lookup proof (`Q = alpha - sum_j beta^j * col_j`).
pub fn prove_d1b_tuple_public_table_par_ext4(
    wit_cols: &[&[u32]],
    pub_cols: &[&[u32]],
    mult_table: &[u32],
    tr: &mut CShakeTranscript,
) -> (D1bRangeExt4Proof, Ext4, Vec<Ext4>) {
    assert!(!wit_cols.is_empty() && wit_cols.len() == pub_cols.len());
    let n_wit = wit_cols[0].len();
    let n_tab = pub_cols[0].len();
    assert!(n_wit.is_power_of_two() && n_tab.is_power_of_two() && mult_table.len() == n_tab);
    let m_wit = n_wit.trailing_zeros() as usize;
    let m_tab = n_tab.trailing_zeros() as usize;
    assert!(m_tab <= m_wit);

    let tup_beta = tr.squeeze_ext4(b"d1b_tup_beta", true);
    let alpha = tr.squeeze_ext4(b"d1b_tup_alpha", true);
    let mut b_pows = Vec::with_capacity(wit_cols.len());
    let mut bp = Ext4::ONE;
    for _ in 0..wit_cols.len() {
        b_pows.push(bp);
        bp = bp.mul(tup_beta);
    }

    let mut p0 = vec![Ext4::ZERO; n_wit * 2];
    let mut q0 = vec![Ext4::ZERO; n_wit * 2];
    p0[..n_wit]
        .par_iter_mut()
        .zip(q0[..n_wit].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            *pd = Ext4::ONE;
            let mut acc = Ext4::from_bb(wit_cols[0][x]);
            for j in 1..wit_cols.len() {
                acc = acc.add(b_pows[j].scale_bb(wit_cols[j][x]));
            }
            *qd = alpha.sub(acc);
        });
    let mask_tab = n_tab - 1;
    p0[n_wit..]
        .par_iter_mut()
        .zip(q0[n_wit..].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            if x < n_tab {
                let m_bb = mult_table[x] % P_U32;
                *pd = Ext4::from_bb(if m_bb == 0 { 0 } else { P_U32 - m_bb });
            } else {
                *pd = Ext4::ZERO;
            }
            let xm = x & mask_tab;
            let mut acc = Ext4::from_bb(pub_cols[0][xm]);
            for j in 1..pub_cols.len() {
                acc = acc.add(b_pows[j].scale_bb(pub_cols[j][xm]));
            }
            *qd = alpha.sub(acc);
        });

    let (root_q, layers, cur_pt) = run_d1b_fraction_tree_par(
        p0,
        q0,
        m_wit,
        b"d1b_tup_rq",
        b"d1b_tup_eta",
        [b"d1b_tc0", b"d1b_tc1", b"d1b_tc2", b"d1b_tcinf"],
        b"d1b_tch",
        [b"d1b_tplo", b"d1b_tphi", b"d1b_tqlo", b"d1b_tqhi"],
        b"d1b_trbit",
        tr,
    );
    let z_leaf = cur_pt[..m_wit].to_vec();
    let mut wit_ev = Ext4::ZERO;
    for (j, col) in wit_cols.iter().enumerate() {
        wit_ev = wit_ev.add(b_pows[j].mul(mle_eval_bb_at_ext4(col, &z_leaf)));
    }
    let mult_ev = mle_eval_bb_at_ext4(mult_table, &z_leaf[..m_tab]);
    tr.absorb_ext4(b"d1b_tup_wev", wit_ev);
    tr.absorb_ext4(b"d1b_tup_mev", mult_ev);

    (
        D1bRangeExt4Proof {
            m_wit,
            m_tab,
            root_q,
            layers,
            rem_leaf_eval: wit_ev,
            mult_leaf_eval: mult_ev,
        },
        tup_beta,
        z_leaf,
    )
}

pub fn verify_d1b_tuple_public_table_ext4(
    pub_cols: &[&[u32]],
    proof: &D1bRangeExt4Proof,
    tr: &mut CShakeTranscript,
) -> Result<(Ext4, Vec<Ext4>), String> {
    if proof.m_tab > proof.m_wit || proof.m_wit > 24 {
        return Err("D1b tuple invalid m_tab / m_wit bounds".into());
    }
    let tab_len = 1usize
        .checked_shl(proof.m_tab as u32)
        .ok_or_else(|| "D1b tuple m_tab shift overflow".to_string())?;
    if pub_cols.is_empty()
        || pub_cols
            .iter()
            .any(|col| col.len() != tab_len || col.iter().any(|&v| v >= P_U32))
    {
        return Err("tuple public table size or canonicality mismatch".into());
    }
    if proof.root_q.is_zero() || proof.layers.len() != proof.m_wit + 1 {
        return Err("D1b tuple root_q == 0 or layer count mismatch".into());
    }
    let tup_beta = tr.squeeze_ext4(b"d1b_tup_beta", true);
    let alpha = tr.squeeze_ext4(b"d1b_tup_alpha", true);
    tr.absorb_ext4(b"d1b_tup_rq", proof.root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p = Ext4::ZERO;
    let mut cur_q = proof.root_q;

    for (step, lyr) in proof.layers.iter().enumerate() {
        if lyr.rounds.len() != step {
            return Err("D1b tuple round count mismatch".into());
        }
        let eta = tr.squeeze_ext4(b"d1b_tup_eta", true);
        let mut sigma = cur_p.add(eta.mul(cur_q));
        let mut sum_chals = Vec::with_capacity(step);
        for msg in &lyr.rounds {
            if msg.p0.add(msg.p1) != sigma {
                return Err("D1b tuple sumcheck failed".into());
            }
            tr.absorb_ext4(b"d1b_tc0", msg.p0);
            tr.absorb_ext4(b"d1b_tc1", msg.p1);
            tr.absorb_ext4(b"d1b_tc2", msg.p2);
            tr.absorb_ext4(b"d1b_tcinf", msg.p_inf);
            let ch = tr.squeeze_ext4(b"d1b_tch", true);
            sum_chals.push(ch);
            sigma = eval_cubic_zero_one_two_inf_ext4(msg.p0, msg.p1, msg.p2, msg.p_inf, ch);
        }
        tr.absorb_ext4(b"d1b_tplo", lyr.p_lo);
        tr.absorb_ext4(b"d1b_tphi", lyr.p_hi);
        tr.absorb_ext4(b"d1b_tqlo", lyr.q_lo);
        tr.absorb_ext4(b"d1b_tqhi", lyr.q_hi);
        let eq_ev = eq_mle_ext4(&cur_pt, &sum_chals);
        let num_v = lyr.p_lo.mul(lyr.q_hi).add(lyr.p_hi.mul(lyr.q_lo));
        let den_v = lyr.q_lo.mul(lyr.q_hi);
        if sigma != eq_ev.mul(num_v.add(eta.mul(den_v))) {
            return Err("D1b tuple terminal layer check failed".into());
        }
        let r_bit = tr.squeeze_ext4(b"d1b_trbit", true);
        cur_p = lyr.p_lo.add(r_bit.mul(lyr.p_hi.sub(lyr.p_lo)));
        cur_q = lyr.q_lo.add(r_bit.mul(lyr.q_hi.sub(lyr.q_lo)));
        let mut next_pt = Vec::with_capacity(step + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
    }

    tr.absorb_ext4(b"d1b_tup_wev", proof.rem_leaf_eval);
    tr.absorb_ext4(b"d1b_tup_mev", proof.mult_leaf_eval);

    let z_leaf = &cur_pt[..proof.m_wit];
    let z_side = cur_pt[proof.m_wit];
    let mut sub_zero = Ext4::ONE;
    for &zb in &z_leaf[proof.m_tab..] {
        sub_zero = sub_zero.mul(Ext4::ONE.sub(zb));
    }
    let p_tab = sub_zero.mul(proof.mult_leaf_eval).neg();
    let eq_tab = build_eq_table_lsb_ext4(&z_leaf[..proof.m_tab]);
    let mut bp = Ext4::ONE;
    let mut pub_ev = Ext4::ZERO;
    for col in pub_cols {
        let mut ce = Ext4::ZERO;
        for (&v, &e) in col.iter().zip(eq_tab.iter()) {
            ce = ce.add(e.scale_bb(v));
        }
        pub_ev = pub_ev.add(bp.mul(ce));
        bp = bp.mul(tup_beta);
    }
    let q_tab = alpha.sub(pub_ev);
    let q_wit = alpha.sub(proof.rem_leaf_eval);

    let exp_p = eq_lin_ext4(z_side, Ext4::ZERO).add(eq_lin_ext4(z_side, Ext4::ONE).mul(p_tab));
    let exp_q = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(q_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(q_tab));
    if cur_p != exp_p || cur_q != exp_q {
        return Err("D1b tuple leaf consistency check failed".into());
    }
    Ok((tup_beta, z_leaf.to_vec()))
}

#[inline]
fn cubic_monomial_from_012inf(p0: Ext4, p1: Ext4, p2: Ext4, p_inf: Ext4) -> [Ext4; 4] {
    let six_c3 = p_inf.scale_bb(6);
    let two_p1 = p1.add(p1);
    let c2 = p2.sub(two_p1).add(p0).sub(six_c3).scale_bb(INV2_BB);
    let c1 = p1.sub(p0).sub(c2).sub(p_inf);
    [p0, c1, c2, p_inf]
}

/// Rayon-parallel `prove_gmask_einsum_ext4` producing a standard `BlindedEinSumExt4Proof` verified by
/// `whir_ext4::verify_gmask_einsum_ext4`!
#[allow(clippy::too_many_arguments)]
pub fn prove_gmask_einsum_par_ext4(
    left_tab: &[Ext4],
    right_tab: &[Ext4],
    mu_s: usize,
    kappa: usize,
    z_s: &[Ext4],
    gmask: &GMaskExt4,
    spec_name: &str,
    tr: &mut CShakeTranscript,
) -> (BlindedEinSumExt4Proof, Ext4, Vec<Ext4>, Ext4, Ext4, Ext4) {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);

    let gmask_sum = gmask.hypercube_sum(spec_name);
    tr.absorb_ext4(b"gm_es_gsum", gmask_sum);
    tr.absorb_ext4_slice(b"gm_es_zs", z_s);
    let rho = tr.squeeze_ext4(b"gm_es_rho", true);

    let suf_tables = build_eq_suffix_tables_ext4(z_s);
    let mut l_cur = left_tab.to_vec();
    let mut r_cur = right_tab.to_vec();
    let mut rounds = Vec::with_capacity(m);
    let mut challenges = Vec::with_capacity(m);
    let mut prefix_eq = Ext4::ONE;

    for u in 0..mu_s {
        let suf = &suf_tables[mu_s - 1 - u];
        let rem_h_pairs = suf.len();
        let nk = 1usize << kappa;
        let stride_p = rem_h_pairs * 2;
        let eval_q = |q: usize| -> [Ext4; 4] {
            let mut acc = [Ext4::ZERO; 4];
            let q_base = q * stride_p;
            for (h_rem, &w) in suf.iter().enumerate() {
                let idx0 = q_base + 2 * h_rem;
                let (a0, a1) = (l_cur[idx0], l_cur[idx0 + 1]);
                let (b0, b1) = (r_cur[idx0], r_cur[idx0 + 1]);
                let da = a1.sub(a0);
                let db = b1.sub(b0);
                let a2 = a1.add(da);
                let b2 = b1.add(db);
                acc[0] = acc[0].add(w.mul(a0.mul(b0)));
                acc[1] = acc[1].add(w.mul(a1.mul(b1)));
                acc[2] = acc[2].add(w.mul(a2.mul(b2)));
                acc[3] = acc[3].add(w.mul(da.mul(db)));
            }
            acc
        };
        let [q0, q1, q2, q_inf] = if nk * rem_h_pairs >= 2048 && nk >= 4 {
            (0..nk).into_par_iter().map(eval_q).reduce(
                || [Ext4::ZERO; 4],
                |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2]), a[3].add(b[3])],
            )
        } else {
            let mut acc = [Ext4::ZERO; 4];
            for q in 0..nk {
                let x = eval_q(q);
                for k in 0..4 {
                    acc[k] = acc[k].add(x[k]);
                }
            }
            acc
        };

        let zu = z_s[u];
        let eq0 = prefix_eq.mul(Ext4::ONE.sub(zu));
        let eq1 = prefix_eq.mul(zu);
        let eq2 = prefix_eq.mul(zu.scale_bb(3).sub(Ext4::ONE));
        let eq_slope = prefix_eq.mul(zu.add(zu).sub(Ext4::ONE));
        let unmasked = cubic_monomial_from_012inf(
            eq0.mul(q0),
            eq1.mul(q1),
            eq2.mul(q2),
            eq_slope.mul(q_inf),
        );
        let bv = gmask.blind_round_poly(spec_name, u, &challenges, rho, &unmasked);
        let blinded = [bv[0], bv[1], bv[2], bv[3]];
        tr.absorb_ext4_slice(b"gm_es_rd", &blinded);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        rounds.push(blinded);
        challenges.push(ch);
        if l_cur.len() >= 8192 {
            let half = l_cur.len() / 2;
            l_cur = (0..half)
                .into_par_iter()
                .map(|i| l_cur[2 * i].add(ch.mul(l_cur[2 * i + 1].sub(l_cur[2 * i]))))
                .collect();
            r_cur = (0..half)
                .into_par_iter()
                .map(|i| r_cur[2 * i].add(ch.mul(r_cur[2 * i + 1].sub(r_cur[2 * i]))))
                .collect();
        } else {
            l_cur = fold_ext4(&l_cur, ch);
            r_cur = fold_ext4(&r_cur, ch);
        }
        prefix_eq = prefix_eq.mul(eq_lin_ext4(zu, ch));
    }

    for v in 0..kappa {
        let half = l_cur.len() / 2;
        let eval_k = |idx: usize| -> [Ext4; 3] {
            let (a0, a1) = (l_cur[2 * idx], l_cur[2 * idx + 1]);
            let (b0, b1) = (r_cur[2 * idx], r_cur[2 * idx + 1]);
            let da = a1.sub(a0);
            let db = b1.sub(b0);
            [a0.mul(b0), a0.mul(db).add(da.mul(b0)), da.mul(db)]
        };
        let [c0, c1, c2] = if half >= 2048 {
            (0..half).into_par_iter().map(eval_k).reduce(
                || [Ext4::ZERO; 3],
                |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
            )
        } else {
            let mut acc = [Ext4::ZERO; 3];
            for idx in 0..half {
                let x = eval_k(idx);
                for k in 0..3 {
                    acc[k] = acc[k].add(x[k]);
                }
            }
            acc
        };
        let unmasked = [
            prefix_eq.mul(c0),
            prefix_eq.mul(c1),
            prefix_eq.mul(c2),
            Ext4::ZERO,
        ];
        let bv = gmask.blind_round_poly(spec_name, mu_s + v, &challenges, rho, &unmasked);
        let blinded = [bv[0], bv[1], bv[2], bv[3]];
        tr.absorb_ext4_slice(b"gm_es_rd", &blinded);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        rounds.push(blinded);
        challenges.push(ch);
        if half >= 4096 {
            l_cur = (0..half)
                .into_par_iter()
                .map(|i| l_cur[2 * i].add(ch.mul(l_cur[2 * i + 1].sub(l_cur[2 * i]))))
                .collect();
            r_cur = (0..half)
                .into_par_iter()
                .map(|i| r_cur[2 * i].add(ch.mul(r_cur[2 * i + 1].sub(r_cur[2 * i]))))
                .collect();
        } else {
            l_cur = fold_ext4(&l_cur, ch);
            r_cur = fold_ext4(&r_cur, ch);
        }
    }

    let term = eval_poly_ext4(rounds.last().unwrap(), *challenges.last().unwrap());
    (
        BlindedEinSumExt4Proof { gmask_sum, rounds },
        rho,
        challenges,
        l_cur[0],
        r_cur[0],
        term,
    )
}

/// Build custom `mc = 15` (`c = 32,768, w0 = 65,536, blow = 8, n0 = 524,288, zk = true`) online WHIR shape.
fn online_zk_shape_mc15(m_vars_list: &[usize]) -> WhirExt4MatrixShape {
    let mut indexed: Vec<(usize, usize)> = m_vars_list.iter().copied().enumerate().collect();
    indexed.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let mut offset = 0usize;
    let mut by_orig = vec![
        SubtableMeta {
            id: 0,
            m_vars: 0,
            base_cell: 0,
        };
        m_vars_list.len()
    ];
    for (orig_id, m_v) in indexed {
        assert_eq!(offset & ((1usize << m_v) - 1), 0);
        by_orig[orig_id] = SubtableMeta {
            id: orig_id,
            m_vars: m_v,
            base_cell: offset,
        };
        offset += 1usize << m_v;
    }
    let mc = 15usize;
    let c = 1usize << mc; // 32,768
    let w0 = 2 * c; // 65,536
    let blow = WHIR_EXT4_BLOWUP; // 8
    let n0 = blow * w0; // 524,288 = 2^19
    let needed_rows = offset.max(64).div_ceil(c);
    let rd = (needed_rows + 4).max(8).next_power_of_two();
    let mr = rd.trailing_zeros() as usize;
    WhirExt4MatrixShape {
        mr,
        mc,
        rd,
        usable_rows: rd - 4,
        c,
        w0,
        blow,
        n0,
        zk: true,
        r_total: rd + 12,
        subtables: by_orig,
    }
}

// ================================================================================================
// §5. Exact `f32` Reference Forward Pass (24 Layers) & Tamper Specification
// ================================================================================================

#[derive(Clone, Debug)]
pub struct F32Reference24LResult {
    pub top1_token_id: u32,
    pub top1_logit: f32,
    pub logits: Vec<f32>,
}

pub fn execute_f32_reference_24l(
    safetensors_path: impl AsRef<Path>,
    prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
) -> Result<F32Reference24LResult, String> {
    let mmap = MmapSafetensors::open(safetensors_path)?;
    let (_, emb_w) = mmap.read_f32("model.language_model.embed_tokens.weight")?;
    let mut h = vec![0.0f32; FULL_24L_SEQ_LEN * D_MODEL];
    for (t, &tid) in prompt_tokens.iter().enumerate() {
        let tid_u = tid as usize;
        if tid_u >= VOCAB_SIZE {
            return Err("token ID out of vocab".into());
        }
        h[t * D_MODEL..(t + 1) * D_MODEL]
            .copy_from_slice(&emb_w[tid_u * D_MODEL..(tid_u + 1) * D_MODEL]);
    }

    let rmsnorm_f32 = |x: &[f32], dim: usize, gain: &[f32], plus_one: bool| -> Vec<f32> {
        let rows = x.len() / dim;
        let mut out = vec![0.0f32; x.len()];
        for r in 0..rows {
            let xr = &x[r * dim..(r + 1) * dim];
            let ms: f32 = xr.iter().map(|&v| v * v).sum::<f32>() / (dim as f32);
            let inv = 1.0 / (ms + 1e-6).sqrt();
            for d in 0..dim {
                let g = if plus_one { 1.0 + gain[d] } else { gain[d] };
                out[r * dim + d] = xr[d] * inv * g;
            }
        }
        out
    };

    let matmul_f32 = |x: &[f32], seq: usize, in_d: usize, w: &[f32], out_d: usize| -> Vec<f32> {
        let mut y = vec![0.0f32; seq * out_d];
        y.par_chunks_mut(out_d).enumerate().for_each(|(t, yr)| {
            let xr = &x[t * in_d..(t + 1) * in_d];
            for j in 0..out_d {
                let wr = &w[j * in_d..(j + 1) * in_d];
                yr[j] = xr.iter().zip(wr.iter()).map(|(&a, &b)| a * b).sum();
            }
        });
        y
    };

    for l in 0..NUM_LAYERS {
        let pfx = format!("model.language_model.layers.{l}");
        let (_, ln1_w) = mmap.read_f32(&format!("{pfx}.input_layernorm.weight"))?;
        let (_, ln2_w) = mmap.read_f32(&format!("{pfx}.post_attention_layernorm.weight"))?;
        let x1 = rmsnorm_f32(&h, D_MODEL, &ln1_w, true);

        let attn_out = if l % 4 != 3 {
            let (_, w_qkv) = mmap.read_f32(&format!("{pfx}.linear_attn.in_proj_qkv.weight"))?;
            let (_, w_z) = mmap.read_f32(&format!("{pfx}.linear_attn.in_proj_z.weight"))?;
            let (_, w_b) = mmap.read_f32(&format!("{pfx}.linear_attn.in_proj_b.weight"))?;
            let (_, w_a) = mmap.read_f32(&format!("{pfx}.linear_attn.in_proj_a.weight"))?;
            let (_, w_o) = mmap.read_f32(&format!("{pfx}.linear_attn.out_proj.weight"))?;
            let (_, cw) = mmap.read_f32(&format!("{pfx}.linear_attn.conv1d.weight"))?;
            let (_, dt) = mmap.read_f32(&format!("{pfx}.linear_attn.dt_bias"))?;
            let (_, alog) = mmap.read_f32(&format!("{pfx}.linear_attn.A_log"))?;
            let (_, yn_w) = mmap.read_f32(&format!("{pfx}.linear_attn.norm.weight"))?;

            let qkv = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_qkv, GDN_QKV_DIM);
            let z = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_z, 2048);
            let b = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_b, GDN_H);
            let a = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_a, GDN_H);

            let mut conv = vec![0.0f32; FULL_24L_SEQ_LEN * GDN_QKV_DIM];
            for t in 0..FULL_24L_SEQ_LEN {
                for c in 0..GDN_QKV_DIM {
                    let mut acc = 0.0f32;
                    for kw in 0..4 {
                        if t + kw >= 3 {
                            acc += qkv[(t + kw - 3) * GDN_QKV_DIM + c] * cw[c * 4 + kw];
                        }
                    }
                    conv[t * GDN_QKV_DIM + c] = acc / (1.0 + (-acc).exp());
                }
            }
            let mut state = vec![0.0f32; GDN_H * GDN_D * GDN_D];
            let mut yf = vec![0.0f32; FULL_24L_SEQ_LEN * 2048];
            let inv_sqrt_d = 1.0 / (GDN_D as f32).sqrt();
            for t in 0..FULL_24L_SEQ_LEN {
                let row = &conv[t * GDN_QKV_DIM..(t + 1) * GDN_QKV_DIM];
                for hi in 0..GDN_H {
                    let qs = &row[hi * GDN_D..(hi + 1) * GDN_D];
                    let ks = &row[2048 + hi * GDN_D..2048 + (hi + 1) * GDN_D];
                    let vs = &row[4096 + hi * GDN_D..4096 + (hi + 1) * GDN_D];
                    let qn_inv =
                        inv_sqrt_d / (qs.iter().map(|&v| v * v).sum::<f32>() + 1e-6).sqrt();
                    let kn_inv = 1.0 / (ks.iter().map(|&v| v * v).sum::<f32>() + 1e-6).sqrt();
                    let beta = 1.0 / (1.0 + (-b[t * GDN_H + hi]).exp());
                    let sp = (1.0 + (a[t * GDN_H + hi] + dt[hi]).exp()).ln();
                    let alpha = (-alog[hi].exp() * sp).exp();
                    let st = &mut state[hi * GDN_D * GDN_D..(hi + 1) * GDN_D * GDN_D];
                    for v in st.iter_mut() {
                        *v *= alpha;
                    }
                    let mut sk = [0.0f32; GDN_D];
                    for dv in 0..GDN_D {
                        let mut s = 0.0f32;
                        for dk in 0..GDN_D {
                            s += st[dv * GDN_D + dk] * (ks[dk] * kn_inv);
                        }
                        sk[dv] = beta * (vs[dv] - s);
                    }
                    for dv in 0..GDN_D {
                        let mut yv = 0.0f32;
                        for dk in 0..GDN_D {
                            st[dv * GDN_D + dk] += sk[dv] * (ks[dk] * kn_inv);
                            yv += st[dv * GDN_D + dk] * (qs[dk] * qn_inv);
                        }
                        yf[t * 2048 + hi * GDN_D + dv] = yv;
                    }
                }
            }
            let y_norm = rmsnorm_f32(&yf, GDN_D, &yn_w, false);
            let gated: Vec<f32> = y_norm
                .iter()
                .zip(z.iter())
                .map(|(&yn, &zv)| yn * (zv / (1.0 + (-zv).exp())))
                .collect();
            matmul_f32(&gated, FULL_24L_SEQ_LEN, 2048, &w_o, D_MODEL)
        } else {
            let (_, w_q) = mmap.read_f32(&format!("{pfx}.self_attn.q_proj.weight"))?;
            let (_, w_k) = mmap.read_f32(&format!("{pfx}.self_attn.k_proj.weight"))?;
            let (_, w_v) = mmap.read_f32(&format!("{pfx}.self_attn.v_proj.weight"))?;
            let (_, w_o) = mmap.read_f32(&format!("{pfx}.self_attn.o_proj.weight"))?;
            let (_, qn_w) = mmap.read_f32(&format!("{pfx}.self_attn.q_norm.weight"))?;
            let (_, kn_w) = mmap.read_f32(&format!("{pfx}.self_attn.k_norm.weight"))?;

            let qg = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_q, 4096);
            let kr = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_k, 512);
            let vr = matmul_f32(&x1, FULL_24L_SEQ_LEN, D_MODEL, &w_v, 512);
            let mut q_only = vec![0.0f32; FULL_24L_SEQ_LEN * GQA_HQ * GQA_DH];
            let mut gate = vec![0.0f32; FULL_24L_SEQ_LEN * 2048];
            for t in 0..FULL_24L_SEQ_LEN {
                for hq in 0..GQA_HQ {
                    q_only[(t * GQA_HQ + hq) * GQA_DH..(t * GQA_HQ + hq + 1) * GQA_DH]
                        .copy_from_slice(
                            &qg[t * 4096 + hq * 512..t * 4096 + hq * 512 + GQA_DH],
                        );
                    gate[(t * GQA_HQ + hq) * GQA_DH..(t * GQA_HQ + hq + 1) * GQA_DH]
                        .copy_from_slice(
                            &qg[t * 4096 + hq * 512 + GQA_DH..t * 4096 + (hq + 1) * 512],
                        );
                }
            }
            let mut qh = rmsnorm_f32(&q_only, GQA_DH, &qn_w, true);
            let mut kh = rmsnorm_f32(&kr, GQA_DH, &kn_w, true);
            for t in 0..FULL_24L_SEQ_LEN {
                for pair in 0..32 {
                    let freq = 1.0 / 10_000_000.0_f32.powf((2 * pair) as f32 / 64.0);
                    let (cs, sn) = ((t as f32 * freq).cos(), (t as f32 * freq).sin());
                    for hq in 0..GQA_HQ {
                        let b = (t * GQA_HQ + hq) * GQA_DH;
                        let (xa, xb) = (qh[b + pair], qh[b + 32 + pair]);
                        qh[b + pair] = xa * cs - xb * sn;
                        qh[b + 32 + pair] = xb * cs + xa * sn;
                    }
                    for hk in 0..GQA_HKV {
                        let b = (t * GQA_HKV + hk) * GQA_DH;
                        let (ka, kb) = (kh[b + pair], kh[b + 32 + pair]);
                        kh[b + pair] = ka * cs - kb * sn;
                        kh[b + 32 + pair] = kb * cs + ka * sn;
                    }
                }
            }
            let mut aoh = vec![0.0f32; FULL_24L_SEQ_LEN * 2048];
            for hq in 0..GQA_HQ {
                let hk = hq / 4;
                for ti in 0..FULL_24L_SEQ_LEN {
                    let qt = &qh[(ti * GQA_HQ + hq) * GQA_DH..(ti * GQA_HQ + hq + 1) * GQA_DH];
                    let mut sc = vec![0.0f32; ti + 1];
                    let mut mx = f32::NEG_INFINITY;
                    for (tj, sc_slot) in sc.iter_mut().enumerate() {
                        let kt = &kh[(tj * GQA_HKV + hk) * GQA_DH..(tj * GQA_HKV + hk + 1) * GQA_DH];
                        let d: f32 = kt.iter().zip(qt.iter()).map(|(&a, &b)| a * b).sum::<f32>() / 16.0;
                        *sc_slot = d;
                        if d > mx {
                            mx = d;
                        }
                    }
                    let mut zsum = 0.0f32;
                    for s in &mut sc {
                        *s = (*s - mx).exp();
                        zsum += *s;
                    }
                    let dst = &mut aoh[(ti * GQA_HQ + hq) * GQA_DH..(ti * GQA_HQ + hq + 1) * GQA_DH];
                    for (tj, &prob) in sc.iter().enumerate() {
                        let p = prob / zsum;
                        let vt = &vr[(tj * GQA_HKV + hk) * GQA_DH..(tj * GQA_HKV + hk + 1) * GQA_DH];
                        for d in 0..GQA_DH {
                            dst[d] += p * vt[d];
                        }
                    }
                }
            }
            let ao_g: Vec<f32> = aoh
                .iter()
                .zip(gate.iter())
                .map(|(&a, &g)| a / (1.0 + (-g).exp()))
                .collect();
            matmul_f32(&ao_g, FULL_24L_SEQ_LEN, 2048, &w_o, D_MODEL)
        };

        for (hv, &av) in h.iter_mut().zip(attn_out.iter()) {
            *hv += av;
        }
        let x2 = rmsnorm_f32(&h, D_MODEL, &ln2_w, true);
        let (_, w_gate) = mmap.read_f32(&format!("{pfx}.mlp.gate_proj.weight"))?;
        let (_, w_up) = mmap.read_f32(&format!("{pfx}.mlp.up_proj.weight"))?;
        let (_, w_down) = mmap.read_f32(&format!("{pfx}.mlp.down_proj.weight"))?;
        let gf = matmul_f32(&x2, FULL_24L_SEQ_LEN, D_MODEL, &w_gate, D_FF);
        let uf = matmul_f32(&x2, FULL_24L_SEQ_LEN, D_MODEL, &w_up, D_FF);
        let sw: Vec<f32> = gf
            .iter()
            .zip(uf.iter())
            .map(|(&g, &u)| (g / (1.0 + (-g).exp())) * u)
            .collect();
        let mlp_out = matmul_f32(&sw, FULL_24L_SEQ_LEN, D_FF, &w_down, D_MODEL);
        for (hv, &mv) in h.iter_mut().zip(mlp_out.iter()) {
            *hv += mv;
        }
    }

    let (_, fn_w) = mmap.read_f32("model.language_model.norm.weight")?;
    let hf = rmsnorm_f32(&h, D_MODEL, &fn_w, true);
    let last_h = &hf[(FULL_24L_SEQ_LEN - 1) * D_MODEL..FULL_24L_SEQ_LEN * D_MODEL];
    let logits: Vec<f32> = emb_w
        .par_chunks_exact(D_MODEL)
        .map(|wr| last_h.iter().zip(wr.iter()).map(|(&a, &b)| a * b).sum())
        .collect();
    let mut best_id = 0u32;
    let mut best_val = f32::NEG_INFINITY;
    for (idx, &v) in logits.iter().enumerate() {
        if v > best_val {
            best_val = v;
            best_id = idx as u32;
        }
    }
    Ok(F32Reference24LResult {
        top1_token_id: best_id,
        top1_logit: best_val,
        logits,
    })
}

/// Mandatory 8-way adversarial tamper kinds proving ZERO layers/links are skipped!
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Full24LayerTamperKind {
    /// (1) `+1` flip in `embed_tokens` `h_in[0]` (`ST_H_CARRY[b=0]`).
    EmbedTokensHIn0,
    /// (2) `+1` flip in Layer `0` GDN WY `U_wy`.
    Layer0GdnWyUwy,
    /// (3) `+1` flip in Layer `3` GQA `Q K^T` / `RoPE` / softmax (`qh_r` -> `sc_q8` -> `p_sm`).
    Layer3GqaQkRopeSoftmax,
    /// (4) `+1` flip in Layer `11` (`q_idx = 2`) GQA `O_proj` output.
    Layer11GqaOProj,
    /// (5) `+1` flip in Layer `14` SwiGLU `down_proj` output (`!= swiglu · W_down[14]`, keeping all local `RMSNorm`/`SiLU`/`WY` valid!).
    Layer14SwiGluSiluDownProj,
    /// (5b) `+1` flip in Layer `14` SwiGLU multiplication quotient (`sw != gs * up / 512`).
    Layer14SwiGluMul,
    /// (5c) `+1` flip in Layer `14` `SiLU` LUT output (`gs + 1`, keeping downstream `sw = (gs+1)*up/512`, `down_proj`, and Layers `15..23` locally consistent!).
    Layer14SwiGluSiluLut,
    /// (6) Cross-layer splice `h_out[7] != h_in[8]` (Layers `0..=7` AND Layers `8..=23` internally valid!).
    CrossLayerSpliceL7ToL8,
    /// (7) `+1` flip in Layer `22` pre-attention RMSNorm scale (`rho`).
    Layer22RmsNormScale,
    /// (8) `+1` flip in final `lm_head` argmax token claim (`emitted_next_token_id`).
    FinalLmHeadArgmaxToken,
}

// ================================================================================================
// §6. Online Witness Generation, Virtual Range/LUT Consolidation, & Super-Matrix Layout
// ================================================================================================

// Matrix 0 (`GDN` 18-layer super-matrix, `38` subtables):
const M0_QKV: usize = 0; // 22: [c: 8192, t: 16, g: 32]
const M0_REM_QKV: usize = 1; // 22
const M0_CONV_PRE: usize = 2; // 22: [c: 8192, t: 16, g: 32]
const M0_REM_CONV: usize = 3; // 22
const M0_CONV_SILU: usize = 4; // 22: [d: 128, h: 16, sec: 4, t: 16, g: 32]
const M0_Z_PROJ: usize = 5; // 20: [k: 2048, t: 16, g: 32]
const M0_REM_Z: usize = 6; // 20
const M0_Z_SILU: usize = 7; // 20
const M0_GATED: usize = 8; // 20
const M0_REM_GATED: usize = 9; // 20
const M0_V_BETA: usize = 10; // 20: [d: 128, h: 16, t: 16, g: 32]
const M0_REM_VBETA: usize = 11; // 20
const M0_U_WY: usize = 12; // 20: [d: 128, h: 16, t: 16, g: 32]
const M0_REM_UWY: usize = 13; // 20
const M0_Y_WY: usize = 14; // 20: [d: 128, h: 16, t: 16, g: 32]
const M0_REM_YWY: usize = 15; // 20
const M0_ATTN_OUT: usize = 16; // 19: [d: 1024, t: 16, g: 32]
const M0_REM_OUT: usize = 17; // 19
const M0_GAMMA: usize = 18; // 17: [h: 16, i: 16, j: 16, g: 32]
const M0_REM_GAMMA: usize = 19; // 17
const M0_DKK: usize = 20; // 17: [h: 16, i: 16, j: 16, g: 32]
const M0_REM_DKK: usize = 21; // 17
const M0_BG: usize = 22; // 17
const M0_REM_BG: usize = 23; // 17
const M0_L_WY: usize = 24; // 17
const M0_REM_LWY: usize = 25; // 17
const M0_DQK: usize = 26; // 17
const M0_REM_DQK: usize = 27; // 17
const M0_A_WY: usize = 28; // 17
const M0_REM_AWY: usize = 29; // 17
const M0_B_PROJ: usize = 30; // 13: [h: 16, t: 16, g: 32]
const M0_REM_B: usize = 31; // 13
const M0_A_PROJ: usize = 32; // 13
const M0_REM_A: usize = 33; // 13
const M0_BETA_Q10: usize = 34; // 13
const M0_SP_IN: usize = 35; // 13
const M0_SP_Q8: usize = 36; // 13
const M0_G_EXP: usize = 37; // 13
const M0_REM_GEXP: usize = 38; // 13
const M0_ALPHA_Q12: usize = 39; // 13
const M0_COUNT: usize = 40;

// Matrix 1 (`GQA` 6-layer super-matrix, `30` subtables):
const M1_Q_RAW: usize = 0; // 18: [dh: 256, hq: 8, t: 16, q: 8]
const M1_REM_Q: usize = 1; // 18
const M1_GATE: usize = 2; // 18
const M1_REM_GATE: usize = 3; // 18
const M1_QH_R: usize = 4; // 18
const M1_REM_ROPE_Q: usize = 5; // 18
const M1_AO_H: usize = 6; // 18
const M1_REM_AOH: usize = 7; // 18
const M1_SIG_GATE: usize = 8; // 18
const M1_AO_G: usize = 9; // 18
const M1_REM_AOG: usize = 10; // 18
const M1_ATTN_OUT: usize = 11; // 17: [d: 1024, t: 16, q: 8]
const M1_REM_OUT: usize = 12; // 17
const M1_K_RAW: usize = 13; // 16: [dh: 256, hkv: 2, t: 16, q: 8]
const M1_REM_K: usize = 14; // 16
const M1_V_PROJ: usize = 15; // 16
const M1_REM_V: usize = 16; // 16
const M1_KH_R: usize = 17; // 16
const M1_REM_ROPE_K: usize = 18; // 16
const M1_SC_Q8: usize = 19; // 14: [tj: 16, ti: 16, hq: 8, q: 8]
const M1_REM_SC: usize = 20; // 14
const M1_SEL_MAX: usize = 21; // 14
const M1_U_SM: usize = 22; // 14
const M1_E_SM_RAW: usize = 23; // 14
const M1_E_SM: usize = 24; // 14
const M1_P_SM: usize = 25; // 14
const M1_REM_PSM: usize = 26; // 14
const M1_DIFF_PSM: usize = 27; // 14
const M1_M_MAX: usize = 28; // 10: [ti: 16, hq: 8, q: 8]
const M1_Z_SM: usize = 29; // 10: [1..=65536] on active rows
const M1_Z_SM_M1: usize = 30; // 10: `Z_SM - 1` in `[0, 65536)` on active rows (`q < 6`), `0` on `q >= 6`
const M1_COUNT: usize = 31;

// Matrix 2 (`24L Residual Continuity + 24L SwiGLU MLP + Final Logits + D1b Mults + GMaskExt4`):
const M2_MLP_GATE: usize = 0; // 21: [j: 4096, t: 16, l: 32]
const M2_REM_GATE: usize = 1; // 21
const M2_MLP_UP: usize = 2; // 21
const M2_REM_UP: usize = 3; // 21
const M2_GATE_SILU: usize = 4; // 21
const M2_SWIGLU: usize = 5; // 21
const M2_REM_SWIGLU: usize = 6; // 21
const M2_H_CARRY: usize = 7; // 19: [d: 1024, t: 16, b: 32] (`b=0`: embed, `b=l+1`: `h_out[l]`)
const M2_H_IN: usize = 8; // 19: [d: 1024, t: 16, b: 32] (`b=l`: `h_in[l]`, `b=24`: `final_in`)
const M2_H_MID: usize = 9; // 19: [d: 1024, t: 16, l: 32]
const M2_MLP_OUT: usize = 10; // 19: [d: 1024, t: 16, l: 32]
const M2_REM_MLPOUT: usize = 11; // 19
const M2_LOGITS: usize = 12; // 18: [v: 262144]
const M2_REM_LOGITS: usize = 13; // 18
const M2_DIFF_ARGMAX: usize = 14; // 18
const M2_MULT_RSQRT: usize = 15; // 17 (131,072)
const M2_MULT_RANGE0: usize = 16; // 16 (65,536)
const M2_MULT_RANGE1: usize = 17; // 16 (65,536)
const M2_MULT_RANGE2: usize = 18; // 16 (65,536)
const M2_MULT_SILU: usize = 19; // 15 (32,768)
const M2_MULT_SIG: usize = 20; // 15 (32,768)
const M2_MULT_SP: usize = 21; // 15 (32,768)
const M2_MULT_EXPNEG: usize = 22; // 15 (32,768)
const M2_GM_LIMB0: usize = 23; // 12 (4,096)
const M2_GM_LIMB1: usize = 24; // 12
const M2_GM_LIMB2: usize = 25; // 12
const M2_GM_LIMB3: usize = 26; // 12
const M2_COUNT: usize = 27;

// Matrix 3 (`All RMSNorms: 3 groups × 22 subtables = 66 subtables`):
// Per group `g_rms in {0: Norm1024, 1: NormGdn128, 2: NormGqa256}`, base = `g_rms * 22`:
const RGRP_SQLO: usize = 0; // m_full
const RGRP_SQHI: usize = 1; // m_full
const RGRP_RSQ: usize = 2; // m_full
const RGRP_UQ9: usize = 3; // m_full
const RGRP_RU: usize = 4; // m_full
const RGRP_YOUT: usize = 5; // m_full
const RGRP_RY: usize = 6; // m_full
const RGRP_B128_LO: usize = 7; // m_full - 4
const RGRP_B128_HI: usize = 8; // m_full - 4
const RGRP_RB128: usize = 9; // m_full - 4
const RGRP_MS_LO: usize = 10; // m_row
const RGRP_MS_HI: usize = 11; // m_row
const RGRP_RMS: usize = 12; // m_row
const RGRP_POW4: usize = 13; // m_row
const RGRP_POW2: usize = 14; // m_row
const RGRP_HPOW2: usize = 15; // m_row
const RGRP_UMS: usize = 16; // m_row
const RGRP_RMLUT: usize = 17; // m_row
const RGRP_RNORM: usize = 18; // m_row
const RGRP_DIFF_NORM: usize = 19; // m_row
const RGRP_RHO_LO: usize = 20; // m_row
const RGRP_RHO_HI: usize = 21; // m_row
const RGRP_RRHO: usize = 22; // m_row
const RGRP_DIFF_RHO: usize = 23; // m_row
const RGRP_STRIDE: usize = 24;
const M3_COUNT: usize = 3 * RGRP_STRIDE; // 72

#[derive(Clone, Copy, Debug)]
struct RmsGroupCfg {
    grp: usize,
    log_d: usize,
    m_row: usize,
    gain_div: i64,
    wst_gain: usize,
}

const RMS_CFGS: [RmsGroupCfg; 3] = [
    // Group 0: `Norm1024`: `[d: 1024, t: 16, slot: 64]` (`m_row = 10`, `m_full = 20`)
    RmsGroupCfg {
        grp: 0,
        log_d: 10,
        m_row: 10,
        gain_div: 1024,
        wst_gain: WST_NORM1024,
    },
    // Group 1: `NormGdn128`: `[d: 128, h: 16, t: 16, gk: 64]` (`m_row = 14`, `m_full = 21`)
    RmsGroupCfg {
        grp: 1,
        log_d: 7,
        m_row: 14,
        gain_div: 1024,
        wst_gain: WST_NORM_GDN128,
    },
    // Group 2: `NormGqa256`: `[d: 256, hslot: 16, t: 16, q: 8]` (`m_row = 11`, `m_full = 19`)
    RmsGroupCfg {
        grp: 2,
        log_d: 8,
        m_row: 11,
        gain_div: 2048,
        wst_gain: WST_NORM_GQA256,
    },
];

fn fill_rmsnorm_row(
    m3: &mut [Vec<u32>],
    cfg: RmsGroupCfg,
    row_idx: usize,
    x_row: &[i64],
    w_slot: usize,
    weights: &PrecomputedModelWeights24L,
    luts: &Full24LPublicLuts,
    tamper_rho_plus1: bool,
) -> Vec<i64> {
    let dim = 1usize << cfg.log_d;
    assert_eq!(x_row.len(), dim);
    let base = cfg.grp * RGRP_STRIDE;
    let n_blk = dim / 16;
    let div_ms = (dim / 32) as i64;

    let mut sum_b128 = 0i64;
    for blk in 0..n_blk {
        let mut sum_sq16 = 0i64;
        for j in 0..16 {
            let d = blk * 16 + j;
            let xv = x_row[d];
            let x2 = xv * xv;
            let sq16 = x2 / 16;
            let r_sq = (x2 % 16) as u32;
            let full_idx = d + (row_idx << cfg.log_d);
            m3[base + RGRP_SQLO][full_idx] = (sq16 & 8191) as u32;
            m3[base + RGRP_SQHI][full_idx] = (sq16 >> 13) as u32;
            m3[base + RGRP_RSQ][full_idx] = r_sq;
            sum_sq16 += sq16;
        }
        let b128 = sum_sq16 / 32;
        let r_b128 = (sum_sq16 % 32) as u32;
        let blk_idx = blk + (row_idx << (cfg.log_d - 4));
        m3[base + RGRP_B128_LO][blk_idx] = (b128 & 8191) as u32;
        m3[base + RGRP_B128_HI][blk_idx] = (b128 >> 13) as u32;
        m3[base + RGRP_RB128][blk_idx] = r_b128;
        sum_b128 += b128;
    }

    let num_ms = sum_b128 + div_ms;
    let m_ms = num_ms / div_ms;
    let r_ms = (num_ms % div_ms) as u32;
    m3[base + RGRP_MS_LO][row_idx] = (m_ms & 8191) as u32;
    m3[base + RGRP_MS_HI][row_idx] = (m_ms >> 13) as u32;
    m3[base + RGRP_RMS][row_idx] = r_ms;

    let mut e = 0u8;
    while e < 7 && (m_ms >> (2 * e)) >= 16_384 {
        e += 1;
    }
    let pow4 = 1i64 << (2 * e);
    let pow2 = 1i64 << e;
    let hpow2 = if e == 0 { 0i64 } else { 1i64 << (e - 1) };
    let u_ms = m_ms >> (2 * e);
    let r_norm = m_ms - pow4 * u_ms;
    let rm = luts.rsqrt_lut[u_ms as usize] as i64;
    let mut rho = (rm + hpow2) / pow2;
    let r_rho = (rm + hpow2 - pow2 * rho) as u32;
    if tamper_rho_plus1 {
        rho += 1;
    }

    m3[base + RGRP_POW4][row_idx] = pow4 as u32;
    m3[base + RGRP_POW2][row_idx] = pow2 as u32;
    m3[base + RGRP_HPOW2][row_idx] = hpow2 as u32;
    m3[base + RGRP_UMS][row_idx] = u_ms as u32;
    m3[base + RGRP_RMLUT][row_idx] = rm as u32;
    m3[base + RGRP_RNORM][row_idx] = r_norm as u32;
    m3[base + RGRP_DIFF_NORM][row_idx] = (pow4 - 1 - r_norm) as u32;
    m3[base + RGRP_RHO_LO][row_idx] = (rho & 4095) as u32;
    m3[base + RGRP_RHO_HI][row_idx] = (rho >> 12) as u32;
    m3[base + RGRP_RRHO][row_idx] = r_rho;
    m3[base + RGRP_DIFF_RHO][row_idx] = (pow2 as u32) - 1 - r_rho;

    let mut y_out = vec![0i64; dim];
    for d in 0..dim {
        let full_idx = d + (row_idx << cfg.log_d);
        let (u_q9, r_u) = div_round_with_rem(x_row[d] * rho, 2048);
        let wg = weights.read_i64(cfg.wst_gain, d + (w_slot << cfg.log_d));
        let (yv, r_y) = div_round_with_rem(u_q9 * wg, cfg.gain_div);
        m3[base + RGRP_UQ9][full_idx] = bb_from_i64(u_q9);
        m3[base + RGRP_RU][full_idx] = r_u;
        m3[base + RGRP_YOUT][full_idx] = bb_from_i64(yv);
        m3[base + RGRP_RY][full_idx] = r_y;
        y_out[d] = yv;
    }
    y_out
}

fn matmul_witness_rows(
    x_seq: &[i64], // [seq * in_dim]
    seq: usize,
    in_dim: usize,
    weights: &PrecomputedModelWeights24L,
    wst_id: usize,
    layer_offset_cells: usize,
    out_limit: usize,
    in_stride_in_wst: usize,
    out_div: i64,
) -> (Vec<i64>, Vec<u32>) {
    let zero_buf = vec![0i16; in_dim];
    let pairs: Vec<(Vec<i64>, Vec<u32>)> = (0..seq)
        .into_par_iter()
        .map(|t| {
            let xr = &x_seq[t * in_dim..(t + 1) * in_dim];
            let mut y_t = Vec::with_capacity(out_limit);
            let mut rem_t = Vec::with_capacity(out_limit);
            for j in 0..out_limit {
                let wr = weights.row_slice_i16(
                    wst_id,
                    layer_offset_cells + j * in_stride_in_wst,
                    in_dim,
                    &zero_buf,
                );
                let mut acc = 0i64;
                for d in 0..in_dim {
                    acc += xr[d] * (wr[d] as i64);
                }
                let (yv, rv) = div_round_with_rem(acc, out_div);
                y_t.push(yv);
                rem_t.push(rv);
            }
            (y_t, rem_t)
        })
        .collect();

    let mut y_all = Vec::with_capacity(seq * out_limit);
    let mut r_all = Vec::with_capacity(seq * out_limit);
    for (yt, rt) in pairs {
        y_all.extend_from_slice(&yt);
        r_all.extend_from_slice(&rt);
    }
    (y_all, r_all)
}

struct Full24LGeneratedWitness {
    m0: Vec<Vec<u32>>,
    m1: Vec<Vec<u32>>,
    m2: Vec<Vec<u32>>,
    m3: Vec<Vec<u32>>,
    emitted_token_id: u32,
    claimed_max_logit: i32,
    logits_i32: Vec<i32>,
}

fn generate_24l_witness(
    weights: &PrecomputedModelWeights24L,
    prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
    tamper: Option<Full24LayerTamperKind>,
) -> Full24LGeneratedWitness {
    let luts = public_luts_24l();

    let m0_vars = [
        22, 22, 22, 22, 22, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 19, 17, 17, 17, 17,
        17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
    ];
    let m1_vars = [
        18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 17, 16, 16, 16, 16, 16, 16, 14, 14, 14,
        14, 14, 14, 14, 14, 14, 10, 10, 10,
    ];
    let m2_vars = [
        21, 21, 21, 21, 21, 21, 21, 19, 19, 19, 19, 19, 18, 18, 18, 17, 16, 16, 16, 15, 15, 15,
        15, 12, 12, 12, 12,
    ];
    let mut m3_vars = Vec::with_capacity(M3_COUNT);
    for cfg in RMS_CFGS {
        let mf = cfg.log_d + cfg.m_row;
        let mb = mf - 4;
        let mr = cfg.m_row;
        m3_vars.extend_from_slice(&[
            mf, mf, mf, mf, mf, mf, mf, mb, mb, mb, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr,
            mr, mr,
        ]);
    }

    let mut m0: Vec<Vec<u32>> = m0_vars.iter().map(|&v| vec![0u32; 1usize << v]).collect();
    let mut m1: Vec<Vec<u32>> = m1_vars.iter().map(|&v| vec![0u32; 1usize << v]).collect();
    let mut m2: Vec<Vec<u32>> = m2_vars.iter().map(|&v| vec![0u32; 1usize << v]).collect();
    let mut m3: Vec<Vec<u32>> = m3_vars.iter().map(|&v| vec![0u32; 1usize << v]).collect();

    // Initialize inactive rows of `Norm1024`, `NormGdn128`, `NormGqa256` with `(pow2 = 1)` so `(0, 1, 0, 0, 0)` holds everywhere!
    for cfg in RMS_CFGS {
        let base = cfg.grp * RGRP_STRIDE;
        m3[base + RGRP_POW2].fill(1);
    }
    // Initialize `Sigmoid(0) = 512`, `Softplus(0) = sp_y_bb[16384]`, `ExpNeg(0) = 4096` on padded slots:
    m0[M0_BETA_Q10].fill(512);
    m1[M1_SIG_GATE].fill(512);
    m0[M0_SP_Q8].fill(luts.sp_y_bb[16_384]);
    m0[M0_ALPHA_Q12].fill(4096);
    m1[M1_E_SM_RAW].fill(4096);

    // 1. `embed_tokens` lookup -> `h_cur [16 * 1024]`:
    let scale_emb = S_RES / S_W; // 4
    let mut h_cur = vec![0i64; FULL_24L_SEQ_LEN * D_MODEL];
    for (t, &tid) in prompt_tokens.iter().enumerate() {
        let base_v = (tid as usize) << LOG_D_MODEL;
        for d in 0..D_MODEL {
            let mut val = weights.read_i64(WST_EMBED, base_v + d) * scale_emb;
            if tamper == Some(Full24LayerTamperKind::EmbedTokensHIn0) && t == 0 && d == 0 {
                val += 1;
            }
            h_cur[t * D_MODEL + d] = val;
            m2[M2_H_CARRY][d + (t << LOG_D_MODEL)] = bb_from_i64(val);
        }
    }

    let mut gdn_ord = 0usize;
    let mut gqa_ord = 0usize;
    for l in 0..NUM_LAYERS {
        // Cross-layer handoff into `M2_H_IN[b = l]`:
        if tamper == Some(Full24LayerTamperKind::CrossLayerSpliceL7ToL8) && l == 8 {
            h_cur[0] += 1;
        }
        for t in 0..FULL_24L_SEQ_LEN {
            for d in 0..D_MODEL {
                m2[M2_H_IN][d + (t << LOG_D_MODEL) + (l << (LOG_D_MODEL + LOG_SEQ))] =
                    bb_from_i64(h_cur[t * D_MODEL + d]);
            }
        }

        // Pre-attention `RMSNorm` (`slot = l` in `Norm1024`):
        let mut x_ln1 = vec![0i64; FULL_24L_SEQ_LEN * D_MODEL];
        for t in 0..FULL_24L_SEQ_LEN {
            let row_idx = t + (l << LOG_SEQ);
            let tamper_rho =
                tamper == Some(Full24LayerTamperKind::Layer22RmsNormScale) && l == 22 && t == 0;
            let yr = fill_rmsnorm_row(
                &mut m3,
                RMS_CFGS[0],
                row_idx,
                &h_cur[t * D_MODEL..(t + 1) * D_MODEL],
                l,
                weights,
                luts,
                tamper_rho,
            );
            x_ln1[t * D_MODEL..(t + 1) * D_MODEL].copy_from_slice(&yr);
        }

        let mut attn_out_layer = vec![0i64; FULL_24L_SEQ_LEN * D_MODEL];
        if l % 4 != 3 {
            let g = gdn_ord;
            gdn_ord += 1;
            let (qkv, rem_qkv) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GDN_QKV,
                g << (LOG_D_MODEL + LOG_GDN_QKV_PAD),
                GDN_QKV_DIM,
                D_MODEL,
                S_W,
            );
            let (z_proj, rem_z) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GDN_Z,
                g << (LOG_D_MODEL + 11),
                2048,
                D_MODEL,
                S_W,
            );
            let (b_proj, rem_b) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GDN_B,
                g << (LOG_D_MODEL + LOG_GDN_H),
                GDN_H,
                D_MODEL,
                S_W,
            );
            let (a_proj, rem_a) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GDN_A,
                g << (LOG_D_MODEL + LOG_GDN_H),
                GDN_H,
                D_MODEL,
                S_W,
            );

            let mut conv_silu = vec![0i64; FULL_24L_SEQ_LEN * GDN_QKV_DIM];
            for t in 0..FULL_24L_SEQ_LEN {
                for c in 0..GDN_QKV_DIM {
                    let idx22 = c + (t << LOG_GDN_QKV_PAD) + (g << (LOG_GDN_QKV_PAD + LOG_SEQ));
                    m0[M0_QKV][idx22] = bb_from_i64(qkv[t * GDN_QKV_DIM + c]);
                    m0[M0_REM_QKV][idx22] = rem_qkv[t * GDN_QKV_DIM + c];

                    let mut acc = 0i64;
                    for kw in 0..4 {
                        if t + kw >= 3 {
                            let cw = weights.read_i64(
                                WST_GDN_CONV,
                                kw + (c << 2) + (g << (2 + LOG_GDN_QKV_PAD)),
                            );
                            acc += qkv[(t + kw - 3) * GDN_QKV_DIM + c] * cw;
                        }
                    }
                    let (c_pre, r_conv) = div_round_with_rem(acc, S_W);
                    let cs = luts.silu_i64[(c_pre + 16_384) as usize];
                    m0[M0_CONV_PRE][idx22] = bb_from_i64(c_pre);
                    m0[M0_REM_CONV][idx22] = r_conv;
                    m0[M0_CONV_SILU][idx22] = bb_from_i64(cs);
                    conv_silu[t * GDN_QKV_DIM + c] = cs;
                }
            }

            // `q_n` (`gk = 3g`) & `k_n` (`gk = 3g + 1`):
            let mut q_n = vec![0i64; FULL_24L_SEQ_LEN * GDN_H * GDN_D];
            let mut k_n = vec![0i64; FULL_24L_SEQ_LEN * GDN_H * GDN_D];
            for t in 0..FULL_24L_SEQ_LEN {
                for h in 0..GDN_H {
                    let q_in: Vec<i64> = (0..GDN_D)
                        .map(|d| 2 * conv_silu[t * GDN_QKV_DIM + h * GDN_D + d])
                        .collect();
                    let k_in: Vec<i64> = (0..GDN_D)
                        .map(|d| 2 * conv_silu[t * GDN_QKV_DIM + 2048 + h * GDN_D + d])
                        .collect();
                    let row_q = h + (t << LOG_GDN_H) + ((3 * g) << (LOG_GDN_H + LOG_SEQ));
                    let row_k = h + (t << LOG_GDN_H) + ((3 * g + 1) << (LOG_GDN_H + LOG_SEQ));
                    let q_out = fill_rmsnorm_row(
                        &mut m3,
                        RMS_CFGS[1],
                        row_q,
                        &q_in,
                        3 * g,
                        weights,
                        luts,
                        false,
                    );
                    let k_out = fill_rmsnorm_row(
                        &mut m3,
                        RMS_CFGS[1],
                        row_k,
                        &k_in,
                        3 * g + 1,
                        weights,
                        luts,
                        false,
                    );
                    q_n[(t * GDN_H + h) * GDN_D..(t * GDN_H + h + 1) * GDN_D]
                        .copy_from_slice(&q_out);
                    k_n[(t * GDN_H + h) * GDN_D..(t * GDN_H + h + 1) * GDN_D]
                        .copy_from_slice(&k_out);
                }
            }

            let mut beta_q10 = [[0i64; GDN_H]; FULL_24L_SEQ_LEN];
            let mut alpha_q12 = [[0i64; GDN_H]; FULL_24L_SEQ_LEN];
            for t in 0..FULL_24L_SEQ_LEN {
                for h in 0..GDN_H {
                    let idx13 = h + (t << LOG_GDN_H) + (g << (LOG_GDN_H + LOG_SEQ));
                    let bv = b_proj[t * GDN_H + h];
                    let av = a_proj[t * GDN_H + h];
                    let bt = luts.sig_i64[(bv + 16_384) as usize];
                    let dt = weights.read_i64(WST_GDN_DT, h + (g << LOG_GDN_H));
                    let sp_in = av + dt;
                    let sp = luts.sp_i64[(sp_in + 16_384) as usize];
                    let ea = weights.read_i64(WST_GDN_ALOG, h + (g << LOG_GDN_H));
                    let (ge, r_ge) = div_round_with_rem(sp * ea, S_W);
                    let al = luts.expneg_i64[ge as usize];

                    m0[M0_B_PROJ][idx13] = bb_from_i64(bv);
                    m0[M0_REM_B][idx13] = rem_b[t * GDN_H + h];
                    m0[M0_A_PROJ][idx13] = bb_from_i64(av);
                    m0[M0_REM_A][idx13] = rem_a[t * GDN_H + h];
                    m0[M0_BETA_Q10][idx13] = bt as u32;
                    m0[M0_SP_IN][idx13] = bb_from_i64(sp_in);
                    m0[M0_SP_Q8][idx13] = sp as u32;
                    m0[M0_G_EXP][idx13] = ge as u32;
                    m0[M0_REM_GEXP][idx13] = r_ge;
                    m0[M0_ALPHA_Q12][idx13] = al as u32;
                    beta_q10[t][h] = bt;
                    alpha_q12[t][h] = al;
                }
            }

            let mut gamma = [[[0i64; FULL_24L_SEQ_LEN]; FULL_24L_SEQ_LEN]; GDN_H];
            let mut l_wy = [[[0i64; FULL_24L_SEQ_LEN]; FULL_24L_SEQ_LEN]; GDN_H];
            let mut a_wy = [[[0i64; FULL_24L_SEQ_LEN]; FULL_24L_SEQ_LEN]; GDN_H];
            for h in 0..GDN_H {
                for j in 0..FULL_24L_SEQ_LEN {
                    gamma[h][j][j] = 512;
                    let diag_idx = h + (j << 4) + (j << 8) + (g << 12);
                    m0[M0_GAMMA][diag_idx] = 512;
                    for i in (j + 1)..FULL_24L_SEQ_LEN {
                        let (gm, r_gm) = div_round_with_rem(gamma[h][i - 1][j] * alpha_q12[i][h], 4096);
                        gamma[h][i][j] = gm;
                        let idx17 = h + (i << 4) + (j << 8) + (g << 12);
                        m0[M0_GAMMA][idx17] = gm as u32;
                        m0[M0_REM_GAMMA][idx17] = r_gm;
                    }
                }
                for i in 0..FULL_24L_SEQ_LEN {
                    for j in 0..FULL_24L_SEQ_LEN {
                        let idx17 = h + (i << 4) + (j << 8) + (g << 12);
                        let ki = &k_n[(i * GDN_H + h) * GDN_D..(i * GDN_H + h + 1) * GDN_D];
                        let kj = &k_n[(j * GDN_H + h) * GDN_D..(j * GDN_H + h + 1) * GDN_D];
                        let qi = &q_n[(i * GDN_H + h) * GDN_D..(i * GDN_H + h + 1) * GDN_D];
                        let dot_kk: i64 = ki.iter().zip(kj.iter()).map(|(&a, &b)| a * b).sum();
                        let (dkk, r_dkk) = div_round_with_rem(dot_kk, 512);
                        let (bg, r_bg) = div_round_with_rem(beta_q10[i][h] * gamma[h][i][j], 1024);
                        let dot_qk: i64 = qi.iter().zip(kj.iter()).map(|(&a, &b)| a * b).sum();
                        let (dqk, r_dqk) = div_round_with_rem(dot_qk, 724);

                        m0[M0_DKK][idx17] = bb_from_i64(dkk);
                        m0[M0_REM_DKK][idx17] = r_dkk;
                        m0[M0_BG][idx17] = bg as u32;
                        m0[M0_REM_BG][idx17] = r_bg;
                        m0[M0_DQK][idx17] = bb_from_i64(dqk);
                        m0[M0_REM_DQK][idx17] = r_dqk;

                        if i > j {
                            let (lv, r_lv) = div_round_with_rem(dkk * bg, 512);
                            l_wy[h][i][j] = lv;
                            m0[M0_L_WY][idx17] = bb_from_i64(lv);
                            m0[M0_REM_LWY][idx17] = r_lv;
                        }
                        if i >= j {
                            let (av, r_av) = div_round_with_rem(dqk * gamma[h][i][j], 512);
                            a_wy[h][i][j] = av;
                            m0[M0_A_WY][idx17] = bb_from_i64(av);
                            m0[M0_REM_AWY][idx17] = r_av;
                        }
                    }
                }
            }

            let mut u_wy = vec![0i64; FULL_24L_SEQ_LEN * GDN_H * GDN_D];
            let mut y_wy = vec![0i64; FULL_24L_SEQ_LEN * GDN_H * GDN_D];
            for h in 0..GDN_H {
                for i in 0..FULL_24L_SEQ_LEN {
                    for d in 0..GDN_D {
                        let idx20 = d + (h << 7) + (i << 11) + (g << 15);
                        let vr = conv_silu[i * GDN_QKV_DIM + 4096 + h * GDN_D + d];
                        let (vb, r_vb) = div_round_with_rem(beta_q10[i][h] * vr, 256);
                        let mut sum_lu = 0i64;
                        for j in 0..i {
                            sum_lu += l_wy[h][i][j] * u_wy[(j * GDN_H + h) * GDN_D + d];
                        }
                        let (mut uv, r_uv) = div_round_with_rem(512 * vb - sum_lu, 512);
                        if tamper == Some(Full24LayerTamperKind::Layer0GdnWyUwy)
                            && l == 0
                            && h == 0
                            && i == 1
                            && d == 0
                        {
                            uv += 1;
                        }
                        u_wy[(i * GDN_H + h) * GDN_D + d] = uv;
                        m0[M0_V_BETA][idx20] = bb_from_i64(vb);
                        m0[M0_REM_VBETA][idx20] = r_vb;
                        m0[M0_U_WY][idx20] = bb_from_i64(uv);
                        m0[M0_REM_UWY][idx20] = r_uv;
                    }
                }
                for i in 0..FULL_24L_SEQ_LEN {
                    for d in 0..GDN_D {
                        let idx20 = d + (h << 7) + (i << 11) + (g << 15);
                        let mut sum_au = 0i64;
                        for j in 0..=i {
                            sum_au += a_wy[h][i][j] * u_wy[(j * GDN_H + h) * GDN_D + d];
                        }
                        let (yv, r_yv) = div_round_with_rem(sum_au, 1024);
                        y_wy[(i * GDN_H + h) * GDN_D + d] = yv;
                        m0[M0_Y_WY][idx20] = bb_from_i64(yv);
                        m0[M0_REM_YWY][idx20] = r_yv;
                    }
                }
            }

            let mut gated = vec![0i64; FULL_24L_SEQ_LEN * 2048];
            for t in 0..FULL_24L_SEQ_LEN {
                for h in 0..GDN_H {
                    let row_y = h + (t << LOG_GDN_H) + ((3 * g + 2) << (LOG_GDN_H + LOG_SEQ));
                    let yn = fill_rmsnorm_row(
                        &mut m3,
                        RMS_CFGS[1],
                        row_y,
                        &y_wy[(t * GDN_H + h) * GDN_D..(t * GDN_H + h + 1) * GDN_D],
                        3 * g + 2,
                        weights,
                        luts,
                        false,
                    );
                    for d in 0..GDN_D {
                        let k = h * GDN_D + d;
                        let idx20 = k + (t << 11) + (g << 15);
                        let zv = z_proj[t * 2048 + k];
                        let zs = luts.silu_i64[(zv + 16_384) as usize];
                        let (gv, r_gv) = div_round_with_rem(yn[d] * zs, S_ACT);
                        m0[M0_Z_PROJ][idx20] = bb_from_i64(zv);
                        m0[M0_REM_Z][idx20] = rem_z[t * 2048 + k];
                        m0[M0_Z_SILU][idx20] = bb_from_i64(zs);
                        m0[M0_GATED][idx20] = bb_from_i64(gv);
                        m0[M0_REM_GATED][idx20] = r_gv;
                        gated[t * 2048 + k] = gv;
                    }
                }
            }

            let (ao, rem_ao) = matmul_witness_rows(
                &gated,
                FULL_24L_SEQ_LEN,
                2048,
                weights,
                WST_GDN_OUT,
                g << (11 + LOG_D_MODEL),
                D_MODEL,
                2048,
                (S_ACT * S_W) / S_RES, // 32
            );
            for t in 0..FULL_24L_SEQ_LEN {
                for d in 0..D_MODEL {
                    let idx19 = d + (t << LOG_D_MODEL) + (g << (LOG_D_MODEL + LOG_SEQ));
                    m0[M0_ATTN_OUT][idx19] = bb_from_i64(ao[t * D_MODEL + d]);
                    m0[M0_REM_OUT][idx19] = rem_ao[t * D_MODEL + d];
                }
            }
            attn_out_layer.copy_from_slice(&ao);
        } else {
            let q = gqa_ord;
            gqa_ord += 1;
            let (q_raw, rem_q) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GQA_Q,
                q << 21,
                2048,
                D_MODEL,
                S_W,
            );
            let (gate, rem_gate) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GQA_GATE,
                q << 21,
                2048,
                D_MODEL,
                S_W,
            );
            let (k_raw, rem_k) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GQA_K,
                q << (LOG_D_MODEL + 9),
                512,
                D_MODEL,
                S_W,
            );
            let (v_proj, rem_v) = matmul_witness_rows(
                &x_ln1,
                FULL_24L_SEQ_LEN,
                D_MODEL,
                weights,
                WST_GQA_V,
                q << (LOG_D_MODEL + 9),
                512,
                D_MODEL,
                S_W,
            );

            let mut qh_r = vec![0i64; FULL_24L_SEQ_LEN * GQA_HQ * GQA_DH];
            let mut kh_r = vec![0i64; FULL_24L_SEQ_LEN * GQA_HKV * GQA_DH];
            for t in 0..FULL_24L_SEQ_LEN {
                for hq in 0..GQA_HQ {
                    for dh in 0..GQA_DH {
                        let idx18 = dh + (hq << 8) + (t << 11) + (q << 15);
                        m1[M1_Q_RAW][idx18] = bb_from_i64(q_raw[(t * GQA_HQ + hq) * GQA_DH + dh]);
                        m1[M1_REM_Q][idx18] = rem_q[(t * GQA_HQ + hq) * GQA_DH + dh];
                        m1[M1_GATE][idx18] = bb_from_i64(gate[(t * GQA_HQ + hq) * GQA_DH + dh]);
                        m1[M1_REM_GATE][idx18] = rem_gate[(t * GQA_HQ + hq) * GQA_DH + dh];
                    }
                    let q_in: Vec<i64> = (0..GQA_DH)
                        .map(|dh| 2 * q_raw[(t * GQA_HQ + hq) * GQA_DH + dh])
                        .collect();
                    let row_idx = hq + (t << 4) + (q << 8);
                    let w_slot = hq + (q << 4);
                    let qhi = fill_rmsnorm_row(
                        &mut m3,
                        RMS_CFGS[2],
                        row_idx,
                        &q_in,
                        w_slot,
                        weights,
                        luts,
                        false,
                    );
                    for pair in 0..32 {
                        let (cs, sn) = (luts.rope_cos_q10[t][pair], luts.rope_sin_q10[t][pair]);
                        let (xa, xb) = (qhi[pair], qhi[32 + pair]);
                        let (mut ra, r_ra) = div_round_with_rem(xa * cs - xb * sn, 4096);
                        let (rb, r_rb) = div_round_with_rem(xb * cs + xa * sn, 4096);
                        if tamper == Some(Full24LayerTamperKind::Layer3GqaQkRopeSoftmax)
                            && l == 3
                            && t == 0
                            && hq == 0
                            && pair == 0
                        {
                            ra += 1;
                        }
                        qh_r[(t * GQA_HQ + hq) * GQA_DH + pair] = ra;
                        qh_r[(t * GQA_HQ + hq) * GQA_DH + 32 + pair] = rb;
                        let idx_a = pair + (hq << 8) + (t << 11) + (q << 15);
                        let idx_b = (32 + pair) + (hq << 8) + (t << 11) + (q << 15);
                        m1[M1_QH_R][idx_a] = bb_from_i64(ra);
                        m1[M1_REM_ROPE_Q][idx_a] = r_ra;
                        m1[M1_QH_R][idx_b] = bb_from_i64(rb);
                        m1[M1_REM_ROPE_Q][idx_b] = r_rb;
                    }
                    for dh in GQA_ROT_DIM..GQA_DH {
                        let (rv, r_rv) = div_round_with_rem(1024 * qhi[dh], 4096);
                        qh_r[(t * GQA_HQ + hq) * GQA_DH + dh] = rv;
                        let idx18 = dh + (hq << 8) + (t << 11) + (q << 15);
                        m1[M1_QH_R][idx18] = bb_from_i64(rv);
                        m1[M1_REM_ROPE_Q][idx18] = r_rv;
                    }
                }

                for hk in 0..GQA_HKV {
                    for dh in 0..GQA_DH {
                        let idx16 = dh + (hk << 8) + (t << 9) + (q << 13);
                        m1[M1_K_RAW][idx16] = bb_from_i64(k_raw[(t * GQA_HKV + hk) * GQA_DH + dh]);
                        m1[M1_REM_K][idx16] = rem_k[(t * GQA_HKV + hk) * GQA_DH + dh];
                        m1[M1_V_PROJ][idx16] =
                            bb_from_i64(v_proj[(t * GQA_HKV + hk) * GQA_DH + dh]);
                        m1[M1_REM_V][idx16] = rem_v[(t * GQA_HKV + hk) * GQA_DH + dh];
                    }
                    let k_in: Vec<i64> = (0..GQA_DH)
                        .map(|dh| 2 * k_raw[(t * GQA_HKV + hk) * GQA_DH + dh])
                        .collect();
                    let row_idx = (8 + hk) + (t << 4) + (q << 8);
                    let w_slot = (8 + hk) + (q << 4);
                    let khi = fill_rmsnorm_row(
                        &mut m3,
                        RMS_CFGS[2],
                        row_idx,
                        &k_in,
                        w_slot,
                        weights,
                        luts,
                        false,
                    );
                    for pair in 0..32 {
                        let (cs, sn) = (luts.rope_cos_q10[t][pair], luts.rope_sin_q10[t][pair]);
                        let (ka, kb) = (khi[pair], khi[32 + pair]);
                        let (ra, r_ra) = div_round_with_rem(ka * cs - kb * sn, 4096);
                        let (rb, r_rb) = div_round_with_rem(kb * cs + ka * sn, 4096);
                        kh_r[(t * GQA_HKV + hk) * GQA_DH + pair] = ra;
                        kh_r[(t * GQA_HKV + hk) * GQA_DH + 32 + pair] = rb;
                        let idx_a = pair + (hk << 8) + (t << 9) + (q << 13);
                        let idx_b = (32 + pair) + (hk << 8) + (t << 9) + (q << 13);
                        m1[M1_KH_R][idx_a] = bb_from_i64(ra);
                        m1[M1_REM_ROPE_K][idx_a] = r_ra;
                        m1[M1_KH_R][idx_b] = bb_from_i64(rb);
                        m1[M1_REM_ROPE_K][idx_b] = r_rb;
                    }
                    for dh in GQA_ROT_DIM..GQA_DH {
                        let (rv, r_rv) = div_round_with_rem(1024 * khi[dh], 4096);
                        kh_r[(t * GQA_HKV + hk) * GQA_DH + dh] = rv;
                        let idx16 = dh + (hk << 8) + (t << 9) + (q << 13);
                        m1[M1_KH_R][idx16] = bb_from_i64(rv);
                        m1[M1_REM_ROPE_K][idx16] = r_rv;
                    }
                }
            }

            let mut ao_g = vec![0i64; FULL_24L_SEQ_LEN * 2048];
            for hq in 0..GQA_HQ {
                let hk = hq / 4;
                for ti in 0..FULL_24L_SEQ_LEN {
                    let mut sc_row = [0i64; FULL_24L_SEQ_LEN];
                    let mut max_sc = i64::MIN;
                    let mut best_tj = 0usize;
                    for tj in 0..=ti {
                        let idx14 = tj + (ti << 4) + (hq << 8) + (q << 11);
                        let kt = &kh_r[(tj * GQA_HKV + hk) * GQA_DH..(tj * GQA_HKV + hk + 1) * GQA_DH];
                        let qt = &qh_r[(ti * GQA_HQ + hq) * GQA_DH..(ti * GQA_HQ + hq + 1) * GQA_DH];
                        let dot: i64 = kt.iter().zip(qt.iter()).map(|(&a, &b)| a * b).sum();
                        let (sc, r_sc) = div_round_with_rem(dot, 64);
                        sc_row[tj] = sc;
                        m1[M1_SC_Q8][idx14] = bb_from_i64(sc);
                        m1[M1_REM_SC][idx14] = r_sc;
                        if sc > max_sc {
                            max_sc = sc;
                            best_tj = tj;
                        }
                    }
                    let idx10 = ti + (hq << 4) + (q << 7);
                    m1[M1_M_MAX][idx10] = bb_from_i64(max_sc);
                    m1[M1_SEL_MAX][best_tj + (ti << 4) + (hq << 8) + (q << 11)] = 1;

                    let mut e_row = [0i64; FULL_24L_SEQ_LEN];
                    let mut z_sum = 0i64;
                    for tj in 0..=ti {
                        let idx14 = tj + (ti << 4) + (hq << 8) + (q << 11);
                        let u_sm = max_sc - sc_row[tj];
                        let ev = luts.expneg_i64[u_sm as usize];
                        e_row[tj] = ev;
                        z_sum += ev;
                        m1[M1_U_SM][idx14] = u_sm as u32;
                        m1[M1_E_SM_RAW][idx14] = ev as u32;
                        m1[M1_E_SM][idx14] = ev as u32;
                    }
                    m1[M1_Z_SM][idx10] = z_sum as u32;
                    m1[M1_Z_SM_M1][idx10] = (z_sum - 1) as u32;

                    let mut p_row = [0i64; FULL_24L_SEQ_LEN];
                    for tj in 0..=ti {
                        let idx14 = tj + (ti << 4) + (hq << 8) + (q << 11);
                        let num = 2048 * e_row[tj];
                        let pv = num / z_sum;
                        let r_pv = (num % z_sum) as u32;
                        p_row[tj] = pv;
                        m1[M1_P_SM][idx14] = pv as u32;
                        m1[M1_REM_PSM][idx14] = r_pv;
                        m1[M1_DIFF_PSM][idx14] = (z_sum as u32) - 1 - r_pv;
                    }

                    for dh in 0..GQA_DH {
                        let idx18 = dh + (hq << 8) + (ti << 11) + (q << 15);
                        let mut acc_v = 0i64;
                        for tj in 0..=ti {
                            acc_v += p_row[tj] * v_proj[(tj * GQA_HKV + hk) * GQA_DH + dh];
                        }
                        let (aoh, r_aoh) = div_round_with_rem(acc_v, 2048);
                        let gv = gate[(ti * GQA_HQ + hq) * GQA_DH + dh];
                        let sg = luts.sig_i64[(gv + 16_384) as usize];
                        let (aog, r_aog) = div_round_with_rem(aoh * sg, 1024);
                        m1[M1_AO_H][idx18] = bb_from_i64(aoh);
                        m1[M1_REM_AOH][idx18] = r_aoh;
                        m1[M1_SIG_GATE][idx18] = sg as u32;
                        m1[M1_AO_G][idx18] = bb_from_i64(aog);
                        m1[M1_REM_AOG][idx18] = r_aog;
                        ao_g[ti * 2048 + hq * GQA_DH + dh] = aog;
                    }
                }
            }

            let (mut ao, rem_ao) = matmul_witness_rows(
                &ao_g,
                FULL_24L_SEQ_LEN,
                2048,
                weights,
                WST_GQA_O,
                q << (11 + LOG_D_MODEL),
                D_MODEL,
                2048,
                (S_ACT * S_W) / S_RES, // 32
            );
            if tamper == Some(Full24LayerTamperKind::Layer11GqaOProj) && l == 11 {
                ao[0] += 1;
            }
            for t in 0..FULL_24L_SEQ_LEN {
                for d in 0..D_MODEL {
                    let idx17 = d + (t << LOG_D_MODEL) + (q << (LOG_D_MODEL + LOG_SEQ));
                    m1[M1_ATTN_OUT][idx17] = bb_from_i64(ao[t * D_MODEL + d]);
                    m1[M1_REM_OUT][idx17] = rem_ao[t * D_MODEL + d];
                }
            }
            attn_out_layer.copy_from_slice(&ao);
        }

        // Residual 1: `h_mid[l] = h_in[l] + attn_out[l]`
        for t in 0..FULL_24L_SEQ_LEN {
            for d in 0..D_MODEL {
                let hm = h_cur[t * D_MODEL + d] + attn_out_layer[t * D_MODEL + d];
                h_cur[t * D_MODEL + d] = hm;
                m2[M2_H_MID][d + (t << LOG_D_MODEL) + (l << (LOG_D_MODEL + LOG_SEQ))] =
                    bb_from_i64(hm);
            }
        }

        // Post-attention `RMSNorm` (`slot = 32 + l` in `Norm1024`):
        let mut x_ln2 = vec![0i64; FULL_24L_SEQ_LEN * D_MODEL];
        for t in 0..FULL_24L_SEQ_LEN {
            let row_idx = t + ((32 + l) << LOG_SEQ);
            let yr = fill_rmsnorm_row(
                &mut m3,
                RMS_CFGS[0],
                row_idx,
                &h_cur[t * D_MODEL..(t + 1) * D_MODEL],
                32 + l,
                weights,
                luts,
                false,
            );
            x_ln2[t * D_MODEL..(t + 1) * D_MODEL].copy_from_slice(&yr);
        }

        // SwiGLU MLP:
        let (mlp_gate, rem_mg) = matmul_witness_rows(
            &x_ln2,
            FULL_24L_SEQ_LEN,
            D_MODEL,
            weights,
            WST_MLP_GATE,
            l << (LOG_D_MODEL + LOG_D_FF_PAD),
            D_FF,
            D_MODEL,
            S_W,
        );
        let (mlp_up, rem_mu) = matmul_witness_rows(
            &x_ln2,
            FULL_24L_SEQ_LEN,
            D_MODEL,
            weights,
            WST_MLP_UP,
            l << (LOG_D_MODEL + LOG_D_FF_PAD),
            D_FF,
            D_MODEL,
            S_W,
        );
        let mut swiglu_pad = vec![0i64; FULL_24L_SEQ_LEN * D_FF_PAD];
        for t in 0..FULL_24L_SEQ_LEN {
            for j in 0..D_FF {
                let idx21 = j + (t << LOG_D_FF_PAD) + (l << (LOG_D_FF_PAD + LOG_SEQ));
                let gv = mlp_gate[t * D_FF + j];
                let uv = mlp_up[t * D_FF + j];
                let mut gs = luts.silu_i64[(gv + 16_384) as usize];
                if tamper == Some(Full24LayerTamperKind::Layer14SwiGluSiluLut)
                    && l == 14
                    && t == 0
                    && j == 0
                {
                    gs += 1;
                }
                let (mut sw, r_sw) = div_round_with_rem(gs * uv, (S_ACT * S_ACT) / S_SW); // 512
                if tamper == Some(Full24LayerTamperKind::Layer14SwiGluMul)
                    && l == 14
                    && t == 0
                    && j == 0
                {
                    sw += 1;
                }
                m2[M2_MLP_GATE][idx21] = bb_from_i64(gv);
                m2[M2_REM_GATE][idx21] = rem_mg[t * D_FF + j];
                m2[M2_MLP_UP][idx21] = bb_from_i64(uv);
                m2[M2_REM_UP][idx21] = rem_mu[t * D_FF + j];
                m2[M2_GATE_SILU][idx21] = bb_from_i64(gs);
                m2[M2_SWIGLU][idx21] = bb_from_i64(sw);
                m2[M2_REM_SWIGLU][idx21] = r_sw;
                swiglu_pad[t * D_FF_PAD + j] = sw;
            }
        }
        let (mut mlp_out, rem_mo) = matmul_witness_rows(
            &swiglu_pad,
            FULL_24L_SEQ_LEN,
            D_FF_PAD,
            weights,
            WST_MLP_DOWN,
            l << (LOG_D_FF_PAD + LOG_D_MODEL),
            D_MODEL,
            D_FF_PAD,
            (S_SW * S_W) / S_RES, // 16
        );
        if tamper == Some(Full24LayerTamperKind::Layer14SwiGluSiluDownProj) && l == 14 {
            // Forge `down_proj` output (`!= swiglu · W_down[14]`) while keeping all `RMSNorm`/`SiLU`/`WY` locally valid!
            mlp_out[0] += 1;
        }

        // Residual 2: `h_out[l] = h_mid[l] + mlp_out[l]` -> written to `M2_H_CARRY[b = l + 1]`!
        for t in 0..FULL_24L_SEQ_LEN {
            for d in 0..D_MODEL {
                let idx19 = d + (t << LOG_D_MODEL) + (l << (LOG_D_MODEL + LOG_SEQ));
                m2[M2_MLP_OUT][idx19] = bb_from_i64(mlp_out[t * D_MODEL + d]);
                m2[M2_REM_MLPOUT][idx19] = rem_mo[t * D_MODEL + d];
                let hout = h_cur[t * D_MODEL + d] + mlp_out[t * D_MODEL + d];
                h_cur[t * D_MODEL + d] = hout;
                m2[M2_H_CARRY][d + (t << LOG_D_MODEL) + ((l + 1) << (LOG_D_MODEL + LOG_SEQ))] =
                    bb_from_i64(hout);
            }
        }
    }

    // Final handoff `M2_H_IN[b = 24]` + `final_norm` (`slot = 24` in `Norm1024`):
    let mut x_final_last = vec![0i64; D_MODEL];
    for t in 0..FULL_24L_SEQ_LEN {
        for d in 0..D_MODEL {
            m2[M2_H_IN][d + (t << LOG_D_MODEL) + (24 << (LOG_D_MODEL + LOG_SEQ))] =
                bb_from_i64(h_cur[t * D_MODEL + d]);
        }
        let row_idx = t + (24 << LOG_SEQ);
        let yr = fill_rmsnorm_row(
            &mut m3,
            RMS_CFGS[0],
            row_idx,
            &h_cur[t * D_MODEL..(t + 1) * D_MODEL],
            24,
            weights,
            luts,
            false,
        );
        if t == FULL_24L_SEQ_LEN - 1 {
            x_final_last = yr;
        }
    }

    // Tied `lm_head` (`248,320` vocab) on `x_final_last` (`out_div = (S_ACT * S_W) / 256 = 512` -> Q8 logits):
    let (logits_vec, rem_logits) = matmul_witness_rows(
        &x_final_last,
        1,
        D_MODEL,
        weights,
        WST_EMBED,
        0,
        VOCAB_SIZE,
        D_MODEL,
        (S_ACT * S_W) / 256, // 512
    );
    let mut best_tok = 0usize;
    let mut best_logit = i64::MIN;
    let mut logits_i32 = Vec::with_capacity(VOCAB_SIZE);
    for v in 0..VOCAB_SIZE {
        let lv = logits_vec[v];
        logits_i32.push(lv as i32);
        m2[M2_LOGITS][v] = bb_from_i64(lv);
        m2[M2_REM_LOGITS][v] = rem_logits[v];
        if lv > best_logit {
            best_logit = lv;
            best_tok = v;
        }
    }

    let (emitted_token_id, claimed_max_logit) =
        if tamper == Some(Full24LayerTamperKind::FinalLmHeadArgmaxToken) {
            let forged = (best_tok + 1) % VOCAB_SIZE;
            (forged as u32, logits_vec[forged] as i32)
        } else {
            (best_tok as u32, best_logit as i32)
        };

    for v in 0..VOCAB_SIZE {
        let strict = if v < (emitted_token_id as usize) {
            1i64
        } else {
            0i64
        };
        let diff = (claimed_max_logit as i64) - logits_vec[v] - strict;
        // Clamp negative diff to `0` on `FinalLmHeadArgmaxToken` so `D1b` succeeds and verifier catches the argmax lie!
        m2[M2_DIFF_ARGMAX][v] = diff.max(0) as u32;
    }

    Full24LGeneratedWitness {
        m0,
        m1,
        m2,
        m3,
        emitted_token_id,
        claimed_max_logit,
        logits_i32,
    }
}

// ================================================================================================
// §7. Virtual Range `[a, b)` & Virtual Non-Linear LUT Packers (Zero Extra Witness Commitment!)
// ================================================================================================

#[derive(Clone, Copy, Debug)]
struct VirtualRangeSlice {
    mat_id: usize,
    subtable: usize,
    m_vars: usize,
    base_cell: usize,
    add_const_bb: u32,
}

#[derive(Clone, Debug)]
struct RangeBucketPlan {
    m_tab: usize,
    m_wit: usize,
    slices: Vec<VirtualRangeSlice>,
}

fn canonical_range_bucket_plans() -> Vec<RangeBucketPlan> {
    // Group every range check `(mat_id, st, mv, lo, hi)` into power-of-two `m_tab` ceiling:
    // If `hi - lo == 1 << m_tab`, ONLY ONE slice is needed (`0` upper-shift slice)!
    // If `hi - lo < 1 << m_tab`, emit two slices (`-lo` and `-lo + (1<<m_tab) - (hi - lo)`) in that `m_tab`!
    let mut raw_specs: Vec<(usize, usize, usize, i64, i64)> = Vec::with_capacity(180);
    raw_specs.extend_from_slice(&[
        (0, M0_QKV, 22, -30_000, 30_000),
        (0, M0_REM_QKV, 22, 0, 512),
        (0, M0_REM_CONV, 22, 0, 512),
        (0, M0_CONV_SILU, 22, -15_800, 15_800),
        (0, M0_REM_Z, 20, 0, 512),
        (0, M0_GATED, 20, -22_000, 22_000),
        (0, M0_REM_GATED, 20, 0, 256),
        (0, M0_V_BETA, 20, -30_000, 30_000),
        (0, M0_REM_VBETA, 20, 0, 256),
        (0, M0_U_WY, 20, -28_500, 28_500),
        (0, M0_REM_UWY, 20, 0, 512),
        (0, M0_Y_WY, 20, -30_000, 30_000),
        (0, M0_REM_YWY, 20, 0, 1024),
        (0, M0_ATTN_OUT, 19, -30_000, 30_000),
        (0, M0_REM_OUT, 19, 0, 64),
        (0, M0_GAMMA, 17, 0, 1024),
        (0, M0_REM_GAMMA, 17, 0, 4096),
        (0, M0_DKK, 17, -4096, 4096),
        (0, M0_REM_DKK, 17, 0, 512),
        (0, M0_BG, 17, 0, 2048),
        (0, M0_REM_BG, 17, 0, 1024),
        (0, M0_L_WY, 17, -2048, 2048),
        (0, M0_REM_LWY, 17, 0, 512),
        (0, M0_DQK, 17, -4096, 4096),
        (0, M0_REM_DQK, 17, 0, 724),
        (0, M0_A_WY, 17, -2048, 2048),
        (0, M0_REM_AWY, 17, 0, 512),
        (0, M0_REM_B, 13, 0, 512),
        (0, M0_A_PROJ, 13, -30_000, 30_000),
        (0, M0_REM_A, 13, 0, 512),
        (0, M0_REM_GEXP, 13, 0, 512),
        (1, M1_Q_RAW, 18, -15_800, 15_800),
        (1, M1_REM_Q, 18, 0, 512),
        (1, M1_REM_GATE, 18, 0, 512),
        (1, M1_QH_R, 18, -1920, 1920),
        (1, M1_REM_ROPE_Q, 18, 0, 4096),
        (1, M1_AO_H, 18, -30_000, 30_000),
        (1, M1_REM_AOH, 18, 0, 2048),
        (1, M1_AO_G, 18, -22_000, 22_000),
        (1, M1_REM_AOG, 18, 0, 1024),
        (1, M1_ATTN_OUT, 17, -30_000, 30_000),
        (1, M1_REM_OUT, 17, 0, 64),
        (1, M1_K_RAW, 16, -15_800, 15_800),
        (1, M1_REM_K, 16, 0, 512),
        (1, M1_V_PROJ, 16, -28_000, 28_000),
        (1, M1_REM_V, 16, 0, 512),
        (1, M1_KH_R, 16, -1920, 1920),
        (1, M1_REM_ROPE_K, 16, 0, 4096),
        (1, M1_SC_Q8, 14, -16_384, 16_384),
        (1, M1_REM_SC, 14, 0, 64),
        (1, M1_P_SM, 14, 0, 2049),
        (1, M1_REM_PSM, 14, 0, 65_536),
        (1, M1_DIFF_PSM, 14, 0, 65_536),
        (1, M1_M_MAX, 10, -16_384, 16_384),
        (1, M1_Z_SM_M1, 10, 0, 65_536),
        (2, M2_REM_GATE, 21, 0, 512),
        (2, M2_MLP_UP, 21, -30_000, 30_000),
        (2, M2_REM_UP, 21, 0, 512),
        (2, M2_SWIGLU, 21, -22_000, 22_000),
        (2, M2_REM_SWIGLU, 21, 0, 512),
        (2, M2_H_CARRY, 19, -30_000, 30_000),
        (2, M2_H_IN, 19, -30_000, 30_000),
        (2, M2_H_MID, 19, -30_000, 30_000),
        (2, M2_MLP_OUT, 19, -30_000, 30_000),
        (2, M2_REM_MLPOUT, 19, 0, 32),
        (2, M2_LOGITS, 18, -30_000, 30_000),
        (2, M2_REM_LOGITS, 18, 0, 512),
        (2, M2_DIFF_ARGMAX, 18, 0, 65_536),
    ]);

    for cfg in RMS_CFGS {
        let b = cfg.grp * RGRP_STRIDE;
        let mf = cfg.log_d + cfg.m_row;
        let mb = mf - 4;
        let mr = cfg.m_row;
        let div_ms = (1usize << cfg.log_d) / 32;
        let y_bound = if cfg.grp == 0 { 22_000 } else { 30_000 };
        let ms_hi_bound = if cfg.grp == 0 { 3_800 } else { 7_650 };
        raw_specs.extend_from_slice(&[
            (3, b + RGRP_SQLO, mf, 0, 8192),
            (3, b + RGRP_SQHI, mf, 0, 7650),
            (3, b + RGRP_RSQ, mf, 0, 16),
            (3, b + RGRP_UQ9, mf, -16_384, 16_384),
            (3, b + RGRP_RU, mf, 0, 2048),
            (3, b + RGRP_YOUT, mf, -y_bound, y_bound),
            (3, b + RGRP_RY, mf, 0, cfg.gain_div),
            (3, b + RGRP_B128_LO, mb, 0, 8192),
            (3, b + RGRP_B128_HI, mb, 0, 1910),
            (3, b + RGRP_RB128, mb, 0, 32),
            (3, b + RGRP_MS_LO, mr, 0, 8192),
            (3, b + RGRP_MS_HI, mr, 0, ms_hi_bound),
            (3, b + RGRP_RMS, mr, 0, div_ms as i64),
            (3, b + RGRP_RNORM, mr, 0, 16_384),
            (3, b + RGRP_DIFF_NORM, mr, 0, 16_384),
            (3, b + RGRP_RHO_LO, mr, 0, 4096),
            (3, b + RGRP_RHO_HI, mr, 0, 64),
            (3, b + RGRP_RRHO, mr, 0, 128),
            (3, b + RGRP_DIFF_RHO, mr, 0, 128),
        ]);
    }

    // Group into 3 clean `m_tab` tiers: `9` (`512`), `13` (`8192`), `16` (`65536`), splitting any bucket `> 2^{24}`!
    let mut by_tab: BTreeMap<usize, Vec<(usize, usize, usize, u32)>> = BTreeMap::new();
    for (mat_id, st, mv, lo, hi) in raw_specs {
        let width = hi - lo;
        let m_tab = if width <= 512 {
            9usize
        } else if width <= 8192 {
            13usize
        } else {
            16usize
        };
        let tab_cap = 1i64 << m_tab;
        let entry = by_tab.entry(m_tab).or_default();
        entry.push((mat_id, st, mv, bb_from_i64(-lo)));
        if width < tab_cap {
            entry.push((mat_id, st, mv, bb_from_i64(-lo + (tab_cap - width))));
        }
    }

    let max_bucket_cells = 1usize << 24; // `D1bRangeExt4Proof::read_from` caps `m_wit <= 24`!
    let mut plans = Vec::new();
    for (m_tab, mut items) in by_tab {
        items.sort_by(|a, b| b.2.cmp(&a.2));
        let mut cur_slices = Vec::new();
        let mut cur_off = 0usize;
        for (mat_id, st, mv, add_c) in items {
            let sz = 1usize << mv;
            if cur_off + sz > max_bucket_cells && !cur_slices.is_empty() {
                let m_wit = cur_off.max(1usize << m_tab).next_power_of_two().trailing_zeros() as usize;
                plans.push(RangeBucketPlan {
                    m_tab,
                    m_wit,
                    slices: cur_slices,
                });
                cur_slices = Vec::new();
                cur_off = 0;
            }
            debug_assert_eq!(cur_off & (sz - 1), 0);
            cur_slices.push(VirtualRangeSlice {
                mat_id,
                subtable: st,
                m_vars: mv,
                base_cell: cur_off,
                add_const_bb: add_c,
            });
            cur_off += sz;
        }
        if !cur_slices.is_empty() {
            let m_wit = cur_off.max(1usize << m_tab).next_power_of_two().trailing_zeros() as usize;
            plans.push(RangeBucketPlan {
                m_tab,
                m_wit,
                slices: cur_slices,
            });
        }
    }
    plans
}

// ================================================================================================
// §8. Complete `Full24LayerQwen35Receipt`, Prover (`prove_full_24l_qwen35_turn`), & Standalone Verifier
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecSecEinSumOpening {
    pub prf: BlindedEinSumExt4Proof,
    pub left_at_r: Ext4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecPubWeightEinSumOpening {
    pub prf: BlindedEinSumExt4Proof,
    pub weight_at_r: Ext4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Full24LayerQwen35Receipt {
    pub model_root: WeightModelRoot24L,
    pub prompt_tokens: [u32; FULL_24L_SEQ_LEN],
    pub emitted_next_token_id: u32,
    pub claimed_max_logit: i32,
    pub online_roots: [[u8; 32]; 4],
    pub range_d1b_proofs: Vec<D1bRangeExt4Proof>,
    pub lut_d1b_proofs: [D1bRangeExt4Proof; 5], // `[silu, sig, sp, expneg, rsqrt_norm]`
    pub weight_matmul_proofs: Vec<SecPubWeightEinSumOpening>, // `12` weight contractions + `conv1d` + `sp*alog` + `3 uq9*wgain` = `17`
    pub pub_ind_proofs: Vec<BlindedEinSumExt4Proof>,          // public-indicator zerochecks / RoPE
    pub sec_sec_proofs: Vec<SecSecEinSumOpening>,             // bilinear witness × witness contractions
    pub linear_point_evals: Vec<Ext4>,                        // claimed point evaluations for linear equations
    pub weight_whir_proof: PublicWeightOpeningProof24L,
    pub online_whir_proof: WhirBatchOpeningProofExt4,
}

impl Full24LayerQwen35Receipt {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2_600_000);
        out.extend_from_slice(FULL_24L_MAGIC);
        self.model_root.write_to(&mut out);
        for &t in &self.prompt_tokens {
            out.extend_from_slice(&t.to_le_bytes());
        }
        out.extend_from_slice(&self.emitted_next_token_id.to_le_bytes());
        out.extend_from_slice(&self.claimed_max_logit.to_le_bytes());
        for r in &self.online_roots {
            out.extend_from_slice(r);
        }
        out.push(self.range_d1b_proofs.len() as u8);
        for p in &self.range_d1b_proofs {
            p.write_to(&mut out);
        }
        for p in &self.lut_d1b_proofs {
            p.write_to(&mut out);
        }
        out.push(self.weight_matmul_proofs.len() as u8);
        for wp in &self.weight_matmul_proofs {
            wp.prf.write_to(&mut out);
            out.extend_from_slice(&wp.weight_at_r.to_bytes());
        }
        out.push(self.pub_ind_proofs.len() as u8);
        for ip in &self.pub_ind_proofs {
            ip.write_to(&mut out);
        }
        out.push(self.sec_sec_proofs.len() as u8);
        for sp in &self.sec_sec_proofs {
            sp.prf.write_to(&mut out);
            out.extend_from_slice(&sp.left_at_r.to_bytes());
        }
        pack_ext4_slice(&self.linear_point_evals, &mut out);
        self.weight_whir_proof.write_to(&mut out);
        self.online_whir_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let magic = cur.read_exact(8)?;
        if magic != FULL_24L_MAGIC {
            return Err("invalid Full24LayerQwen35Receipt magic".into());
        }
        let model_root = WeightModelRoot24L::read_from(&mut cur)?;
        let mut prompt_tokens = [0u32; FULL_24L_SEQ_LEN];
        for slot in &mut prompt_tokens {
            *slot = cur.read_u32()?;
        }
        let emitted_next_token_id = cur.read_u32()?;
        let claimed_max_logit = i32::from_le_bytes(cur.read_exact(4)?.try_into().unwrap());
        let mut online_roots = [[0u8; 32]; 4];
        for r in &mut online_roots {
            *r = cur.read_arr32()?;
        }
        let n_rng = cur.read_u8()? as usize;
        if n_rng == 0 || n_rng > 16 {
            return Err("invalid range_d1b_proofs count".into());
        }
        let mut range_d1b_proofs = Vec::with_capacity(n_rng);
        for _ in 0..n_rng {
            range_d1b_proofs.push(D1bRangeExt4Proof::read_from(&mut cur)?);
        }
        let lut_d1b_proofs = [
            D1bRangeExt4Proof::read_from(&mut cur)?,
            D1bRangeExt4Proof::read_from(&mut cur)?,
            D1bRangeExt4Proof::read_from(&mut cur)?,
            D1bRangeExt4Proof::read_from(&mut cur)?,
            D1bRangeExt4Proof::read_from(&mut cur)?,
        ];
        let n_wm = cur.read_u8()? as usize;
        if n_wm > 32 {
            return Err("invalid weight_matmul_proofs count".into());
        }
        let mut weight_matmul_proofs = Vec::with_capacity(n_wm);
        for _ in 0..n_wm {
            let prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
            let weight_at_r = cur.read_ext4()?;
            weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r });
        }
        let n_pi = cur.read_u8()? as usize;
        if n_pi > 32 {
            return Err("invalid pub_ind_proofs count".into());
        }
        let mut pub_ind_proofs = Vec::with_capacity(n_pi);
        for _ in 0..n_pi {
            pub_ind_proofs.push(BlindedEinSumExt4Proof::read_from(&mut cur)?);
        }
        let n_ss = cur.read_u8()? as usize;
        if n_ss > 64 {
            return Err("invalid sec_sec_proofs count".into());
        }
        let mut sec_sec_proofs = Vec::with_capacity(n_ss);
        for _ in 0..n_ss {
            let prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
            let left_at_r = cur.read_ext4()?;
            sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r });
        }
        let linear_point_evals = unpack_ext4_slice(&mut cur, 512)?;
        let weight_whir_proof = PublicWeightOpeningProof24L::read_from(&mut cur)?;
        let online_whir_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(format!("trailing {} bytes in Full24LayerQwen35Receipt", cur.remaining()));
        }
        let parsed = Self {
            model_root,
            prompt_tokens,
            emitted_next_token_id,
            claimed_max_logit,
            online_roots,
            range_d1b_proofs,
            lut_d1b_proofs,
            weight_matmul_proofs,
            pub_ind_proofs,
            sec_sec_proofs,
            linear_point_evals,
            weight_whir_proof,
            online_whir_proof,
        };
        if parsed.to_bytes().as_slice() != bytes {
            return Err("non-canonical Full24LayerQwen35Receipt byte representation".into());
        }
        Ok(parsed)
    }
}

/// Canonical list of all `GMaskSpecExt4` names & round counts (shared deterministically by prover & verifier!).
fn all_gmask_specs_24l() -> Vec<GMaskSpecExt4> {
    vec![
        // 17 `SecPubWeightEinSumOpening`:
        GMaskSpecExt4::new("wm_gdn_qkv", 5 + 10, 3),
        GMaskSpecExt4::new("wm_gdn_z", 5 + 10, 3),
        GMaskSpecExt4::new("wm_gdn_b", 5 + 10, 3),
        GMaskSpecExt4::new("wm_gdn_a", 5 + 10, 3),
        GMaskSpecExt4::new("wm_gdn_out", 5 + 11, 3),
        GMaskSpecExt4::new("wm_gdn_conv", 18 + 2, 3),
        GMaskSpecExt4::new("wm_gdn_sp_alog", 9, 3),
        GMaskSpecExt4::new("wm_gqa_q", 3 + 10, 3),
        GMaskSpecExt4::new("wm_gqa_gate", 3 + 10, 3),
        GMaskSpecExt4::new("wm_gqa_k", 3 + 10, 3),
        GMaskSpecExt4::new("wm_gqa_v", 3 + 10, 3),
        GMaskSpecExt4::new("wm_gqa_o", 3 + 11, 3),
        GMaskSpecExt4::new("wm_mlp_gate", 5 + 10, 3),
        GMaskSpecExt4::new("wm_mlp_up", 5 + 10, 3),
        GMaskSpecExt4::new("wm_mlp_down", 5 + 12, 3),
        GMaskSpecExt4::new("wm_lm_head", 1 + 9, 3), // `10` rounds (`mu_s = 1, kappa = 9` since `num_rounds >= 1`!)
        GMaskSpecExt4::new("wm_rms0_gain", 20, 3),
        GMaskSpecExt4::new("wm_rms1_gain", 21, 3),
        GMaskSpecExt4::new("wm_rms2_gain", 19, 3),
        // `pub_ind_proofs`:
        GMaskSpecExt4::new("pi_gdn_gamma_zc", 17, 3),
        GMaskSpecExt4::new("pi_gdn_lwy_slt", 17, 3),
        GMaskSpecExt4::new("pi_gdn_awy_ut", 17, 3),
        GMaskSpecExt4::new("pi_gqa_rope_q_diag", 18, 3),
        GMaskSpecExt4::new("pi_gqa_rope_q_cross", 18, 3),
        GMaskSpecExt4::new("pi_gqa_rope_k_diag", 16, 3),
        GMaskSpecExt4::new("pi_gqa_rope_k_cross", 16, 3),
        GMaskSpecExt4::new("pi_gqa_sc_caus", 14, 3),
        GMaskSpecExt4::new("pi_gqa_sel_caus", 14, 3),
        GMaskSpecExt4::new("pi_gqa_usm_caus", 14, 3),
        GMaskSpecExt4::new("pi_gqa_esm_caus", 14, 3),
        GMaskSpecExt4::new("pi_gqa_psm_caus", 14, 3),
        GMaskSpecExt4::new("pi_gqa_dpsm_caus", 14, 3),
        GMaskSpecExt4::new("pi_rms0_dnorm", 10, 3),
        GMaskSpecExt4::new("pi_rms1_dnorm", 14, 3),
        GMaskSpecExt4::new("pi_rms2_dnorm", 11, 3),
        // `sec_sec_proofs`:
        GMaskSpecExt4::new("ss_gdn_gamma_rec", 17, 3),
        GMaskSpecExt4::new("ss_gdn_dkk", 9 + 7, 3),
        GMaskSpecExt4::new("ss_gdn_bg", 17, 3),
        GMaskSpecExt4::new("ss_gdn_lwy", 17, 3),
        GMaskSpecExt4::new("ss_gdn_dqk", 9 + 7, 3),
        GMaskSpecExt4::new("ss_gdn_awy", 17, 3),
        GMaskSpecExt4::new("ss_gdn_vbeta", 20, 3),
        GMaskSpecExt4::new("ss_gdn_uwy_solve", 9 + 4, 3),
        GMaskSpecExt4::new("ss_gdn_ywy_read", 9 + 4, 3),
        GMaskSpecExt4::new("ss_gdn_gated", 20, 3),
        GMaskSpecExt4::new("ss_gqa_qk", 10 + 8, 3),
        GMaskSpecExt4::new("ss_gqa_sel_bool", 14, 3),
        GMaskSpecExt4::new("ss_gqa_sel_max", 14, 3),
        GMaskSpecExt4::new("ss_gqa_psm_div", 14, 3),
        GMaskSpecExt4::new("ss_gqa_pv", 6 + 4, 3),
        GMaskSpecExt4::new("ss_gqa_aog", 18, 3),
        GMaskSpecExt4::new("ss_mlp_swiglu", 21, 3),
        GMaskSpecExt4::new("ss_rms0_sq", 20, 3),
        GMaskSpecExt4::new("ss_rms0_p4u", 10, 3),
        GMaskSpecExt4::new("ss_rms0_p2r", 10, 3),
        GMaskSpecExt4::new("ss_rms0_xrho", 20, 3),
        GMaskSpecExt4::new("ss_rms1_sq", 21, 3),
        GMaskSpecExt4::new("ss_rms1_p4u", 14, 3),
        GMaskSpecExt4::new("ss_rms1_p2r", 14, 3),
        GMaskSpecExt4::new("ss_rms1_xrho", 21, 3),
        GMaskSpecExt4::new("ss_rms2_sq", 19, 3),
        GMaskSpecExt4::new("ss_rms2_p4u", 11, 3),
        GMaskSpecExt4::new("ss_rms2_p2r", 11, 3),
        GMaskSpecExt4::new("ss_rms2_xrho", 19, 3),
    ]
}

fn concat_pts(parts: &[&[Ext4]]) -> Vec<Ext4> {
    let len: usize = parts.iter().map(|p| p.len()).sum();
    let mut out = Vec::with_capacity(len);
    for p in parts {
        out.extend_from_slice(p);
    }
    out
}

fn bits_to_ext4(val: usize, num_bits: usize) -> Vec<Ext4> {
    (0..num_bits)
        .map(|b| {
            if ((val >> b) & 1) == 1 {
                Ext4::ONE
            } else {
                Ext4::ZERO
            }
        })
        .collect()
}

/// Evaluate `\widetilde{T}(low, z_{mid}, hi)` (`T` has `low` at `[0..log_lo)`, `mid` at `[log_lo..log_lo+log_mid)`,
/// `hi` at `[log_lo+log_mid..)`) into `out[hi + (low << log_hi)]` (`hi` at low bits for `prove_gmask_einsum_par_ext4`!).
fn fold_mid_u32_for_einsum(
    tab: &[u32],
    log_lo: usize,
    log_mid: usize,
    log_hi: usize,
    z_mid: &[Ext4],
) -> Vec<Ext4> {
    let lo_len = 1usize << log_lo;
    let mid_len = 1usize << log_mid;
    let hi_len = 1usize << log_hi;
    assert_eq!(tab.len(), lo_len * mid_len * hi_len);
    let eq_mid = build_eq_table_lsb_ext4(z_mid);
    let rows: Vec<Vec<Ext4>> = (0..hi_len)
        .into_par_iter()
        .map(|hi| {
            let mut acc_lo = vec![[0u128; 4]; lo_len];
            let hi_base = hi << (log_lo + log_mid);
            for m in 0..mid_len {
                let ew = eq_mid[m].0;
                let sl = &tab[hi_base + (m << log_lo)..hi_base + ((m + 1) << log_lo)];
                for lo in 0..lo_len {
                    let v = sl[lo] as u128;
                    if v != 0 {
                        acc_lo[lo][0] += v * (ew[0] as u128);
                        acc_lo[lo][1] += v * (ew[1] as u128);
                        acc_lo[lo][2] += v * (ew[2] as u128);
                        acc_lo[lo][3] += v * (ew[3] as u128);
                    }
                }
            }
            acc_lo
                .into_iter()
                .map(|a| {
                    Ext4([
                        (a[0] % (P as u128)) as u32,
                        (a[1] % (P as u128)) as u32,
                        (a[2] % (P as u128)) as u32,
                        (a[3] % (P as u128)) as u32,
                    ])
                })
                .collect()
        })
        .collect();
    let mut out = vec![Ext4::ZERO; hi_len * lo_len];
    for (hi, vec_lo) in rows.into_iter().enumerate() {
        for (lo, val) in vec_lo.into_iter().enumerate() {
            out[hi + (lo << log_hi)] = val;
        }
    }
    out
}

fn online_shapes_24l(num_range_buckets: usize) -> [WhirExt4MatrixShape; 4] {
    let m0_vars = [
        22, 22, 22, 22, 22, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 19, 19, 17, 17, 17, 17,
        17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
    ];
    let m1_vars = [
        18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 17, 17, 16, 16, 16, 16, 16, 16, 14, 14, 14,
        14, 14, 14, 14, 14, 14, 10, 10, 10,
    ];
    let plans = canonical_range_bucket_plans();
    assert_eq!(plans.len(), num_range_buckets);
    let mut m2_vars = vec![
        21, 21, 21, 21, 21, 21, 21, 19, 19, 19, 19, 19, 18, 18, 18, 17, 15, 15, 15, 15, 12, 12,
        12, 12,
    ];
    for pl in &plans {
        m2_vars.push(pl.m_tab);
    }
    let mut m3_vars = Vec::with_capacity(M3_COUNT);
    for cfg in RMS_CFGS {
        let mf = cfg.log_d + cfg.m_row;
        let mb = mf - 4;
        let mr = cfg.m_row;
        m3_vars.extend_from_slice(&[
            mf, mf, mf, mf, mf, mf, mf, mb, mb, mb, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr, mr,
            mr, mr,
        ]);
    }
    [
        online_zk_shape_mc15(&m0_vars),
        online_zk_shape_mc15(&m1_vars),
        online_zk_shape_mc15(&m2_vars),
        online_zk_shape_mc15(&m3_vars),
    ]
}

// Re-indexed Matrix-2 tail subtables cleanly supporting dynamic `canonical_range_bucket_plans()`:
const M2D_MULT_RSQRT: usize = 15; // 17
const M2D_MULT_SILU: usize = 16; // 15
const M2D_MULT_SIG: usize = 17; // 15
const M2D_MULT_SP: usize = 18; // 15
const M2D_MULT_EXPNEG: usize = 19; // 15
const M2D_GM_LIMB0: usize = 20; // 12
const M2D_GM_LIMB1: usize = 21; // 12
const M2D_GM_LIMB2: usize = 22; // 12
const M2D_GM_LIMB3: usize = 23; // 12
const M2D_RANGE_MULT_BASE: usize = 24;

/// Tokenize a prompt with `QwenBpeTokenizer`, verify `QwenBpeRom` membership, and prove all 24 layers!
pub fn prove_full_24l_qwen35_turn_from_prompt(
    weights: &PrecomputedModelWeights24L,
    tokenizer: &QwenBpeTokenizer,
    prompt_text: &str,
) -> Result<Full24LayerQwen35Receipt, String> {
    let ids = tokenizer.encode(prompt_text);
    if ids.len() != FULL_24L_SEQ_LEN {
        return Err(format!(
            "expected {FULL_24L_SEQ_LEN} BPE tokens, prompt encoded to {} tokens",
            ids.len()
        ));
    }
    let mut arr = [0u32; FULL_24L_SEQ_LEN];
    arr.copy_from_slice(&ids);
    prove_full_24l_qwen35_turn(weights, &arr)
}

pub fn prove_full_24l_qwen35_turn(
    weights: &PrecomputedModelWeights24L,
    prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
) -> Result<Full24LayerQwen35Receipt, String> {
    prove_full_24l_qwen35_turn_inner(weights, prompt_tokens, None)
}

/// Adversarial receipt builder (`tamper = Some(...)`) that executes with the requested `+1` fault /
/// cross-layer splice and generates a freshly committed `Full24LayerQwen35Receipt` to test soundness!
pub fn prove_tampered_full_24l_qwen35_turn(
    weights: &PrecomputedModelWeights24L,
    prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
    tamper: Full24LayerTamperKind,
) -> Result<Full24LayerQwen35Receipt, String> {
    prove_full_24l_qwen35_turn_inner(weights, prompt_tokens, Some(tamper))
}

fn prove_full_24l_qwen35_turn_inner(
    weights: &PrecomputedModelWeights24L,
    prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
    tamper: Option<Full24LayerTamperKind>,
) -> Result<Full24LayerQwen35Receipt, String> {
    let _ = (
        M0_COUNT,
        M1_COUNT,
        M2_COUNT,
        M2_MULT_RSQRT,
        M2_MULT_RANGE0,
        M2_MULT_RANGE1,
        M2_MULT_RANGE2,
        M2_MULT_SILU,
        M2_MULT_SIG,
        M2_MULT_SP,
        M2_MULT_EXPNEG,
        M2_GM_LIMB0,
        M2_GM_LIMB1,
        M2_GM_LIMB2,
        M2_GM_LIMB3,
    );
    for &tid in prompt_tokens {
        if (tid as usize) >= QWEN_DEFINED_TOKENS {
            return Err(format!("token id {tid} >= {QWEN_DEFINED_TOKENS}"));
        }
    }

    let luts = public_luts_24l();
    let wit = generate_24l_witness(weights, prompt_tokens, tamper);
    let m0 = wit.m0;
    let m1 = wit.m1;
    let m3 = wit.m3;

    // Assemble `m2` (`0..15` from `wit.m2`, `15..24` = LUT mults + GMask limbs, `24..` = range mults):
    let range_plans = canonical_range_bucket_plans();
    let shapes = online_shapes_24l(range_plans.len());

    let gm_specs = all_gmask_specs_24l();
    let mut gm_rng = CShakeRng::from_seed(b"QW35-24L-GMASK-RNG-V1", &os_random_seed_32());
    let gmask = GMaskExt4::sample(gm_specs.clone(), &mut gm_rng);
    let gm_limbs = gmask.to_four_bb_tables();
    assert_eq!(gm_limbs[0].len(), 4096, "expected GMaskExt4 limb len 4096");

    let mut m2 = Vec::with_capacity(M2D_RANGE_MULT_BASE + range_plans.len());
    for i in 0..15 {
        m2.push(wit.m2[i].clone());
    }
    // Placeholders `15..24`:
    m2.push(vec![0u32; 1 << 17]); // 15: Rsqrt
    m2.push(vec![0u32; 1 << 15]); // 16: SiLU
    m2.push(vec![0u32; 1 << 15]); // 17: Sigmoid
    m2.push(vec![0u32; 1 << 15]); // 18: Softplus
    m2.push(vec![0u32; 1 << 15]); // 19: ExpNeg
    m2.push(gm_limbs[0].clone()); // 20
    m2.push(gm_limbs[1].clone()); // 21
    m2.push(gm_limbs[2].clone()); // 22
    m2.push(gm_limbs[3].clone()); // 23

    // Build virtual range buffers & their `D1b` multiplicities in parallel:
    let mats_ref = [&m0, &m1, &m2, &m3];
    let range_bufs_and_mults: Vec<(Vec<u32>, Vec<u32>)> = range_plans
        .par_iter()
        .map(|pl| {
            let mut buf = vec![0u32; 1usize << pl.m_wit];
            for sl in &pl.slices {
                let src = &mats_ref[sl.mat_id][sl.subtable];
                let dst = &mut buf[sl.base_cell..sl.base_cell + src.len()];
                for (d, &v) in dst.iter_mut().zip(src.iter()) {
                    *d = badd(v, sl.add_const_bb);
                }
            }
            let mult = compute_d1b_multiplicities(&buf, pl.m_tab)
                .expect("honest/clamped virtual range slice in [0, 2^m_tab)");
            (buf, mult)
        })
        .collect();
    for (_, mult) in &range_bufs_and_mults {
        m2.push(mult.clone());
    }

    // Build virtual LUT witness buffers & their multiplicities:
    // 0: `SiLU` (`m_wit = 23 = 8,388,608`): `M0_CONV_PRE` (`2^{22}`) + `M2_MLP_GATE` (`2^{21}`) + `M0_Z_PROJ` (`2^{20}`)
    let mut silu_wx = vec![0u32; 1 << 23];
    let mut silu_wy = vec![0u32; 1 << 23];
    silu_wx[0..(1 << 22)].copy_from_slice(&m0[M0_CONV_PRE]);
    silu_wy[0..(1 << 22)].copy_from_slice(&m0[M0_CONV_SILU]);
    silu_wx[(1 << 22)..(1 << 22) + (1 << 21)].copy_from_slice(&m2[M2_MLP_GATE]);
    silu_wy[(1 << 22)..(1 << 22) + (1 << 21)].copy_from_slice(&m2[M2_GATE_SILU]);
    silu_wx[(1 << 22) + (1 << 21)..(1 << 22) + (1 << 21) + (1 << 20)]
        .copy_from_slice(&m0[M0_Z_PROJ]);
    silu_wy[(1 << 22) + (1 << 21)..(1 << 22) + (1 << 21) + (1 << 20)]
        .copy_from_slice(&m0[M0_Z_SILU]);
    let mut mult_silu = vec![0u32; 1 << 15];
    for &xb in &silu_wx {
        let idx = (bb_to_signed_i64(xb) + 16_384) as usize;
        mult_silu[idx] += 1;
    }
    m2[M2D_MULT_SILU] = mult_silu;

    // 1: `Sigmoid` (`m_wit = 19 = 524,288`): `M1_GATE` (`2^{18}`) + `M0_B_PROJ` (`2^{13}`) + pad `(0, 512)`
    let mut sig_wx = vec![0u32; 1 << 19];
    let mut sig_wy = vec![512u32; 1 << 19];
    sig_wx[0..(1 << 18)].copy_from_slice(&m1[M1_GATE]);
    sig_wy[0..(1 << 18)].copy_from_slice(&m1[M1_SIG_GATE]);
    sig_wx[(1 << 18)..(1 << 18) + (1 << 13)].copy_from_slice(&m0[M0_B_PROJ]);
    sig_wy[(1 << 18)..(1 << 18) + (1 << 13)].copy_from_slice(&m0[M0_BETA_Q10]);
    let mut mult_sig = vec![0u32; 1 << 15];
    for &xb in &sig_wx {
        let idx = (bb_to_signed_i64(xb) + 16_384) as usize;
        mult_sig[idx] += 1;
    }
    m2[M2D_MULT_SIG] = mult_sig;

    // 2: `Softplus` (`m_wit = 15 = 32,768`): `M0_SP_IN` (`2^{13}`) + pad `(0, sp(0))`
    let mut sp_wx = vec![0u32; 1 << 15];
    let mut sp_wy = vec![luts.sp_y_bb[16_384]; 1 << 15];
    sp_wx[0..(1 << 13)].copy_from_slice(&m0[M0_SP_IN]);
    sp_wy[0..(1 << 13)].copy_from_slice(&m0[M0_SP_Q8]);
    let mut mult_sp = vec![0u32; 1 << 15];
    for &xb in &sp_wx {
        let idx = (bb_to_signed_i64(xb) + 16_384) as usize;
        mult_sp[idx] += 1;
    }
    m2[M2D_MULT_SP] = mult_sp;

    // 3: `ExpNeg` (`m_wit = 15 = 32,768`): `M1_U_SM` (`2^{14}`) + `M0_G_EXP` (`2^{13}`) + pad `(0, 4096)`
    let mut en_wu = vec![0u32; 1 << 15];
    let mut en_wy = vec![4096u32; 1 << 15];
    en_wu[0..(1 << 14)].copy_from_slice(&m1[M1_U_SM]);
    en_wy[0..(1 << 14)].copy_from_slice(&m1[M1_E_SM_RAW]);
    en_wu[(1 << 14)..(1 << 14) + (1 << 13)].copy_from_slice(&m0[M0_G_EXP]);
    en_wy[(1 << 14)..(1 << 14) + (1 << 13)].copy_from_slice(&m0[M0_ALPHA_Q12]);
    let mut mult_en = vec![0u32; 1 << 15];
    for &ub in &en_wu {
        mult_en[ub as usize] += 1;
    }
    m2[M2D_MULT_EXPNEG] = mult_en;

    // 4: `RsqrtNorm` (`m_wit = 17 = 131,072`): `NormGdn128` (`2^{14}`) + `NormGqa256` (`2^{11}`) + `Norm1024` (`2^{10}`)
    let mut rsq_wcols: [Vec<u32>; 5] = std::array::from_fn(|c| {
        vec![if c == 1 { 1u32 } else { 0u32 }; 1 << 17]
    });
    let rsq_srcs = [
        (1usize, 0usize, 1usize << 14),
        (2usize, 1usize << 14, 1usize << 11),
        (0usize, (1usize << 14) + (1usize << 11), 1usize << 10),
    ];
    let col_offs = [RGRP_POW4, RGRP_POW2, RGRP_HPOW2, RGRP_UMS, RGRP_RMLUT];
    for &(grp, dst_off, len) in &rsq_srcs {
        for (c, &co) in col_offs.iter().enumerate() {
            rsq_wcols[c][dst_off..dst_off + len]
                .copy_from_slice(&m3[grp * RGRP_STRIDE + co][..len]);
        }
    }
    let mut mult_rsq = vec![0u32; 1 << 17];
    for i in 0..(1 << 17) {
        let p4 = rsq_wcols[0][i];
        let slot = if p4 == 0 {
            0usize
        } else {
            let e = (p4.trailing_zeros() / 2) as u8;
            let u = rsq_wcols[3][i] as u16;
            luts.rsqrt_slot_map[&(e, u)]
        };
        mult_rsq[slot] += 1;
    }
    m2[M2D_MULT_RSQRT] = mult_rsq;

    // Commit all 4 online ZK super-matrices (`WhirExt4Pcs`, `zk = true`)!
    let m0_slices: Vec<&[u32]> = m0.iter().map(|v| v.as_slice()).collect();
    let m1_slices: Vec<&[u32]> = m1.iter().map(|v| v.as_slice()).collect();
    let m2_slices: Vec<&[u32]> = m2.iter().map(|v| v.as_slice()).collect();
    let m3_slices: Vec<&[u32]> = m3.iter().map(|v| v.as_slice()).collect();

    let mat0 = WhirCommittedMatrixExt4::commit_with_shape(shapes[0].clone(), &m0_slices, None);
    let mat1 = WhirCommittedMatrixExt4::commit_with_shape(shapes[1].clone(), &m1_slices, None);
    let mat2 = WhirCommittedMatrixExt4::commit_with_shape(shapes[2].clone(), &m2_slices, None);
    let mat3 = WhirCommittedMatrixExt4::commit_with_shape(shapes[3].clone(), &m3_slices, None);
    let online_roots = [mat0.root, mat1.root, mat2.root, mat3.root];

    // Initialize transcript & absorb ALL public roots and turn parameters BEFORE any challenge!
    let mut tr = CShakeTranscript::new(b"QW35-FULL24L-AUDIT-V1");
    weights.model_root.absorb_into(&mut tr);
    for (i, &t) in prompt_tokens.iter().enumerate() {
        tr.absorb_u32(b"tok_in", (i as u32) ^ (t << 5));
        tr.absorb_u32(b"tok_id", t);
    }
    tr.absorb_u32(b"tok_out", wit.emitted_token_id);
    tr.absorb_u32(b"max_logit", wit.claimed_max_logit as u32);
    for (m_idx, r) in online_roots.iter().enumerate() {
        tr.absorb_u32(b"onl_idx", m_idx as u32);
        tr.absorb_root(b"onl_root", r);
    }

    let mut online_claims: [Vec<JointLinearClaimExt4>; 4] =
        [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    let mut weight_claims: Vec<PublicWeightClaim24L> = Vec::new();
    let gm_limb_ids = [M2D_GM_LIMB0, M2D_GM_LIMB1, M2D_GM_LIMB2, M2D_GM_LIMB3];

    // Step A: Prove all consolidated virtual `D1b` range buckets & discharge leaf evaluations!
    let mut range_d1b_proofs = Vec::with_capacity(range_plans.len());
    for (b_idx, (pl, (buf, mult))) in range_plans
        .iter()
        .zip(range_bufs_and_mults.iter())
        .enumerate()
    {
        let (prf, z_leaf) = prove_d1b_range_par_ext4(buf, mult, pl.m_wit, pl.m_tab, &mut tr);
        online_claims[2].push(JointLinearClaimExt4::point_eval(
            M2D_RANGE_MULT_BASE + b_idx,
            z_leaf[..pl.m_tab].to_vec(),
            prf.mult_leaf_eval,
        ));
        // Discharge `prf.rem_leaf_eval` across the 4 matrices by evaluating each matrix's slices + constant sum:
        // Wait: a `JointLinearClaimExt4` applies to ONE matrix! Since a bucket can span `mat 0..3`, send `3`
        // sub-sums (or compute per-matrix sub-sum in `linear_point_evals`!). Sending per-matrix sub-sums (`<= 4` `Ext4`s)
        // lets each matrix check its own `JointLinearClaimExt4` while the verifier checks `sum_m sub_m + const_sum == prf.rem_leaf_eval`!
        range_d1b_proofs.push((prf, z_leaf));
    }

    // Step B: Prove all 5 consolidated virtual `D1b` non-linear public LUTs!
    let (prf_silu, beta_silu, z_silu) = prove_d1b_tuple_public_table_par_ext4(
        &[&silu_wx, &silu_wy],
        &[&luts.silu_x_bb, &luts.silu_y_bb],
        &m2[M2D_MULT_SILU],
        &mut tr,
    );
    let (prf_sig, beta_sig, z_sig) = prove_d1b_tuple_public_table_par_ext4(
        &[&sig_wx, &sig_wy],
        &[&luts.sig_x_bb, &luts.sig_y_bb],
        &m2[M2D_MULT_SIG],
        &mut tr,
    );
    let (prf_sp, beta_sp, z_sp) = prove_d1b_tuple_public_table_par_ext4(
        &[&sp_wx, &sp_wy],
        &[&luts.sp_x_bb, &luts.sp_y_bb],
        &m2[M2D_MULT_SP],
        &mut tr,
    );
    let (prf_en, beta_en, z_en) = prove_d1b_tuple_public_table_par_ext4(
        &[&en_wu, &en_wy],
        &[&luts.expneg_u_bb, &luts.expneg_y_bb],
        &m2[M2D_MULT_EXPNEG],
        &mut tr,
    );
    let (prf_rsq, beta_rsq, z_rsq) = prove_d1b_tuple_public_table_par_ext4(
        &[
            &rsq_wcols[0],
            &rsq_wcols[1],
            &rsq_wcols[2],
            &rsq_wcols[3],
            &rsq_wcols[4],
        ],
        &[
            &luts.rsqrt_norm_cols[0],
            &luts.rsqrt_norm_cols[1],
            &luts.rsqrt_norm_cols[2],
            &luts.rsqrt_norm_cols[3],
            &luts.rsqrt_norm_cols[4],
        ],
        &m2[M2D_MULT_RSQRT],
        &mut tr,
    );

    let mut linear_point_evals: Vec<Ext4> = Vec::with_capacity(256);
    let mats_all = [&m0, &m1, &m2, &m3];
    let push_eval = |mat_id: usize,
                         st: usize,
                         pt: Vec<Ext4>,
                         tr_ref: &mut CShakeTranscript,
                         lin_evs: &mut Vec<Ext4>,
                         onl_cl: &mut [Vec<JointLinearClaimExt4>; 4]|
     -> Ext4 {
        let v = mle_eval_bb_at_ext4(&mats_all[mat_id][st], &pt);
        tr_ref.absorb_ext4(b"lin_ev", v);
        lin_evs.push(v);
        onl_cl[mat_id].push(JointLinearClaimExt4::point_eval(st, pt, v));
        v
    };

    // Discharge virtual range `rem_leaf_eval`s via per-matrix `JointLinearClaimExt4`:
    let mut final_range_proofs = Vec::with_capacity(range_d1b_proofs.len());
    for (pl, (prf, z_leaf)) in range_plans.iter().zip(range_d1b_proofs.into_iter()) {
        let mut by_mat: [Vec<LinearTermExt4>; 4] = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
        let mut mat_vals = [Ext4::ZERO; 4];
        for sl in &pl.slices {
            let prefix = sl.base_cell >> sl.m_vars;
            let mut pref_ev = Ext4::ONE;
            for b in sl.m_vars..pl.m_wit {
                let bit = (prefix >> (b - sl.m_vars)) & 1;
                let zb = z_leaf[b];
                pref_ev = pref_ev.mul(if bit == 1 { zb } else { Ext4::ONE.sub(zb) });
            }
            let sub_pt = z_leaf[..sl.m_vars].to_vec();
            let s_val = mle_eval_bb_at_ext4(&mats_all[sl.mat_id][sl.subtable], &sub_pt);
            mat_vals[sl.mat_id] = mat_vals[sl.mat_id].add(pref_ev.mul(s_val));
            by_mat[sl.mat_id].push(LinearTermExt4::PointEval {
                subtable: sl.subtable,
                point: sub_pt,
                weight: pref_ev,
            });
        }
        for m_id in 0..4 {
            if !by_mat[m_id].is_empty() {
                let mv = mat_vals[m_id];
                tr.absorb_ext4(b"rng_mev", mv);
                linear_point_evals.push(mv);
                online_claims[m_id].push(JointLinearClaimExt4 {
                    terms: std::mem::take(&mut by_mat[m_id]),
                    rhs: mv,
                });
            }
        }
        final_range_proofs.push(prf);
    }

    // Discharge virtual LUT leaf evaluations:
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SILU,
        z_silu[..15].to_vec(),
        prf_silu.mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SIG,
        z_sig[..15].to_vec(),
        prf_sig.mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SP,
        z_sp[..15].to_vec(),
        prf_sp.mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_EXPNEG,
        z_en[..15].to_vec(),
        prf_en.mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_RSQRT,
        z_rsq[..17].to_vec(),
        prf_rsq.mult_leaf_eval,
    ));

    // SiLU virtual leaf (`m_wit = 23`):
    {
        let _ = beta_silu;
        let _ = push_eval(0, M0_CONV_PRE, z_silu[..22].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_CONV_SILU, z_silu[..22].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(2, M2_MLP_GATE, z_silu[..21].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(2, M2_GATE_SILU, z_silu[..21].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_Z_PROJ, z_silu[..20].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_Z_SILU, z_silu[..20].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
    }
    // Sigmoid virtual leaf (`m_wit = 19`):
    {
        let _ = beta_sig;
        let _ = push_eval(1, M1_GATE, z_sig[..18].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_SIG_GATE, z_sig[..18].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_B_PROJ, z_sig[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_BETA_Q10, z_sig[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
    }
    // Softplus virtual leaf (`m_wit = 15`):
    {
        let _ = beta_sp;
        let _ = push_eval(0, M0_SP_IN, z_sp[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_SP_Q8, z_sp[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
    }
    // ExpNeg virtual leaf (`m_wit = 15`):
    {
        let _ = beta_en;
        let _ = push_eval(1, M1_U_SM, z_en[..14].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_E_SM_RAW, z_en[..14].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_G_EXP, z_en[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_ALPHA_Q12, z_en[..13].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
    }
    // RsqrtNorm virtual leaf (`m_wit = 17`, all in `mat 3`):
    {
        let mut terms = Vec::with_capacity(15);
        let mut bp = Ext4::ONE;
        for &co in &col_offs {
            for &(grp, dst_off, len) in &rsq_srcs {
                let mv = len.trailing_zeros() as usize;
                let prefix = dst_off >> mv;
                let mut pref = bp;
                for b in mv..17 {
                    let bit = (prefix >> (b - mv)) & 1;
                    pref = pref.mul(if bit == 1 {
                        z_rsq[b]
                    } else {
                        Ext4::ONE.sub(z_rsq[b])
                    });
                }
                terms.push(LinearTermExt4::PointEval {
                    subtable: grp * RGRP_STRIDE + co,
                    point: z_rsq[..mv].to_vec(),
                    weight: pref,
                });
            }
            bp = bp.mul(beta_rsq);
        }
        // Account for padded tail `[18432 + 1024 = 19456 .. 131072)` having `pow2 == 1` (`beta_rsq^1`):
        let used = (1usize << 14) + (1usize << 11) + (1usize << 10);
        let pad_ind = Ext4::ONE.sub(eval_lt_const_mle(&z_rsq, used));
        let rhs_rsq = prf_rsq.rem_leaf_eval.sub(beta_rsq.mul(pad_ind));
        online_claims[3].push(JointLinearClaimExt4 {
            terms,
            rhs: rhs_rsq,
        });
    }

    let mut weight_matmul_proofs: Vec<SecPubWeightEinSumOpening> = Vec::with_capacity(19);
    let mut pub_ind_proofs: Vec<BlindedEinSumExt4Proof> = Vec::with_capacity(16);
    let mut sec_sec_proofs: Vec<SecSecEinSumOpening> = Vec::with_capacity(28);

    // Helper for standard batched 2D weight matmul (`X[d, t, l] * W[d, j, l] = out_div * Y[j, t, l] + REM[j, t, l] - (out_div/2) * act`):
    struct MatmulJob<'a> {
        spec: &'a str,
        x_mat: usize,
        x_st: usize,
        x_layer_map: Option<&'a [usize]>, // if `Some(indices)`, `X` is in `Norm1024 YOUT` at `slot = indices[l]`!
        wst: usize,
        y_mat: usize,
        y_st: usize,
        rem_st: usize,
        log_d: usize,
        log_j: usize,
        log_l: usize,
        out_div: u32,
        j_bound: usize,
        l_bound: usize,
    }
    let gdn_ln1_slots: Vec<usize> = GDN_LAYER_INDICES.to_vec();
    let gqa_ln1_slots: Vec<usize> = GQA_LAYER_INDICES.to_vec();
    let mlp_ln2_slots: Vec<usize> = (0..NUM_LAYERS).map(|l| 32 + l).collect();

    let mm_jobs = [
        MatmulJob { spec: "wm_gdn_qkv", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gdn_ln1_slots), wst: WST_GDN_QKV, y_mat: 0, y_st: M0_QKV, rem_st: M0_REM_QKV, log_d: 10, log_j: 13, log_l: 5, out_div: 512, j_bound: GDN_QKV_DIM, l_bound: NUM_GDN_LAYERS },
        MatmulJob { spec: "wm_gdn_z", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gdn_ln1_slots), wst: WST_GDN_Z, y_mat: 0, y_st: M0_Z_PROJ, rem_st: M0_REM_Z, log_d: 10, log_j: 11, log_l: 5, out_div: 512, j_bound: 2048, l_bound: NUM_GDN_LAYERS },
        MatmulJob { spec: "wm_gdn_b", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gdn_ln1_slots), wst: WST_GDN_B, y_mat: 0, y_st: M0_B_PROJ, rem_st: M0_REM_B, log_d: 10, log_j: 4, log_l: 5, out_div: 512, j_bound: 16, l_bound: NUM_GDN_LAYERS },
        MatmulJob { spec: "wm_gdn_a", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gdn_ln1_slots), wst: WST_GDN_A, y_mat: 0, y_st: M0_A_PROJ, rem_st: M0_REM_A, log_d: 10, log_j: 4, log_l: 5, out_div: 512, j_bound: 16, l_bound: NUM_GDN_LAYERS },
        MatmulJob { spec: "wm_gdn_out", x_mat: 0, x_st: M0_GATED, x_layer_map: None, wst: WST_GDN_OUT, y_mat: 0, y_st: M0_ATTN_OUT, rem_st: M0_REM_OUT, log_d: 11, log_j: 10, log_l: 5, out_div: 64, j_bound: 1024, l_bound: NUM_GDN_LAYERS },
        MatmulJob { spec: "wm_gqa_q", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gqa_ln1_slots), wst: WST_GQA_Q, y_mat: 1, y_st: M1_Q_RAW, rem_st: M1_REM_Q, log_d: 10, log_j: 11, log_l: 3, out_div: 512, j_bound: 2048, l_bound: NUM_GQA_LAYERS },
        MatmulJob { spec: "wm_gqa_gate", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gqa_ln1_slots), wst: WST_GQA_GATE, y_mat: 1, y_st: M1_GATE, rem_st: M1_REM_GATE, log_d: 10, log_j: 11, log_l: 3, out_div: 512, j_bound: 2048, l_bound: NUM_GQA_LAYERS },
        MatmulJob { spec: "wm_gqa_k", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gqa_ln1_slots), wst: WST_GQA_K, y_mat: 1, y_st: M1_K_RAW, rem_st: M1_REM_K, log_d: 10, log_j: 9, log_l: 3, out_div: 512, j_bound: 512, l_bound: NUM_GQA_LAYERS },
        MatmulJob { spec: "wm_gqa_v", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&gqa_ln1_slots), wst: WST_GQA_V, y_mat: 1, y_st: M1_V_PROJ, rem_st: M1_REM_V, log_d: 10, log_j: 9, log_l: 3, out_div: 512, j_bound: 512, l_bound: NUM_GQA_LAYERS },
        MatmulJob { spec: "wm_gqa_o", x_mat: 1, x_st: M1_AO_G, x_layer_map: None, wst: WST_GQA_O, y_mat: 1, y_st: M1_ATTN_OUT, rem_st: M1_REM_OUT, log_d: 11, log_j: 10, log_l: 3, out_div: 64, j_bound: 1024, l_bound: NUM_GQA_LAYERS },
        MatmulJob { spec: "wm_mlp_gate", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&mlp_ln2_slots), wst: WST_MLP_GATE, y_mat: 2, y_st: M2_MLP_GATE, rem_st: M2_REM_GATE, log_d: 10, log_j: 12, log_l: 5, out_div: 512, j_bound: D_FF, l_bound: NUM_LAYERS },
        MatmulJob { spec: "wm_mlp_up", x_mat: 3, x_st: RGRP_YOUT, x_layer_map: Some(&mlp_ln2_slots), wst: WST_MLP_UP, y_mat: 2, y_st: M2_MLP_UP, rem_st: M2_REM_UP, log_d: 10, log_j: 12, log_l: 5, out_div: 512, j_bound: D_FF, l_bound: NUM_LAYERS },
        MatmulJob { spec: "wm_mlp_down", x_mat: 2, x_st: M2_SWIGLU, x_layer_map: None, wst: WST_MLP_DOWN, y_mat: 2, y_st: M2_MLP_OUT, rem_st: M2_REM_MLPOUT, log_d: 12, log_j: 10, log_l: 5, out_div: 32, j_bound: 1024, l_bound: NUM_LAYERS },
    ];

    for job in &mm_jobs {
        let z_j = tr.squeeze_ext4_vec(b"mm_zj", job.log_j, true);
        let z_t = tr.squeeze_ext4_vec(b"mm_zt", LOG_SEQ, true);
        let z_l = tr.squeeze_ext4_vec(b"mm_zl", job.log_l, true);
        let y_pt = concat_pts(&[&z_j, &z_t, &z_l]);
        let _ = push_eval(job.y_mat, job.y_st, y_pt.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(job.y_mat, job.rem_st, y_pt, &mut tr, &mut linear_point_evals, &mut online_claims);

        let w_folded = weights.fold_mid_weight_for_einsum(job.wst, job.log_d, job.log_j, job.log_l, &z_j);
        let x_folded = if let Some(slot_map) = job.x_layer_map {
            let d_len = 1usize << job.log_d;
            let l_len = 1usize << job.log_l;
            let eq_t = build_eq_table_lsb_ext4(&z_t);
            let mut xf = vec![Ext4::ZERO; l_len * d_len];
            for (li, &slot) in slot_map.iter().enumerate() {
                for t in 0..FULL_24L_SEQ_LEN {
                    let ew = eq_t[t];
                    let base = (t + (slot << LOG_SEQ)) << job.log_d;
                    let sl = &m3[RGRP_YOUT][base..base + d_len];
                    for d in 0..d_len {
                        xf[li + (d << job.log_l)] = xf[li + (d << job.log_l)].add(ew.scale_bb(sl[d]));
                    }
                }
            }
            xf
        } else {
            fold_mid_u32_for_einsum(&mats_all[job.x_mat][job.x_st], job.log_d, LOG_SEQ, job.log_l, &z_t)
        };

        let (prf, rho, ch, _x_at_r, w_at_r, term) = prove_gmask_einsum_par_ext4(
            &x_folded,
            &w_folded,
            job.log_l,
            job.log_d,
            &z_l,
            &gmask,
            job.spec,
            &mut tr,
        );
        tr.absorb_ext4(b"mm_wr", w_at_r);
        let r_l = &ch[..job.log_l];
        let r_d = &ch[job.log_l..];
        weight_claims.push(PublicWeightClaim24L::point_eval(
            job.wst,
            concat_pts(&[r_d, &z_j, r_l]),
            w_at_r,
        ));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, job.spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));

        let eq_zl = eq_mle_ext4(&z_l, r_l);
        let scale_x = eq_zl.mul(w_at_r);
        if let Some(slot_map) = job.x_layer_map {
            let eq_rl = build_eq_table_lsb_ext4(r_l);
            let mut x_val = Ext4::ZERO;
            let mut x_terms = Vec::with_capacity(slot_map.len());
            for (li, &slot) in slot_map.iter().enumerate() {
                let s_bits = bits_to_ext4(slot, 6);
                let pt = concat_pts(&[r_d, &z_t, &s_bits]);
                let v = mle_eval_bb_at_ext4(&m3[RGRP_YOUT], &pt);
                x_val = x_val.add(eq_rl[li].mul(v));
                x_terms.push(LinearTermExt4::PointEval {
                    subtable: RGRP_YOUT,
                    point: pt,
                    weight: eq_rl[li],
                });
            }
            tr.absorb_ext4(b"mm_xmap", x_val);
            linear_point_evals.push(x_val);
            online_claims[3].push(JointLinearClaimExt4 { terms: x_terms, rhs: x_val });
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale_x.mul(x_val)),
            ));
        } else if job.x_mat == 2 {
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                vec![LinearTermExt4::PointEval {
                    subtable: job.x_st,
                    point: concat_pts(&[r_d, &z_t, r_l]),
                    weight: scale_x,
                }],
                gm_limb_ids,
                &w_at,
                rho,
                term,
            ));
        } else {
            let x_pt = concat_pts(&[r_d, &z_t, r_l]);
            let xv = push_eval(job.x_mat, job.x_st, x_pt, &mut tr, &mut linear_point_evals, &mut online_claims);
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale_x.mul(xv)),
            ));
        }
        let _ = (job.out_div, job.j_bound, job.l_bound);
        weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r: w_at_r });
    }

    // `wm_gdn_conv` (`mu_s = 18` `(c: 13, g: 5)`, `kappa = 2` `kw`):
    {
        let z_c = tr.squeeze_ext4_vec(b"conv_zc", 13, true);
        let z_t = tr.squeeze_ext4_vec(b"conv_zt", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"conv_zg", 5, true);
        let pt_ctg = concat_pts(&[&z_c, &z_t, &z_g]);
        let _ = push_eval(0, M0_CONV_PRE, pt_ctg.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_CONV, pt_ctg, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_t = build_eq_table_lsb_ext4(&z_t);
        let cg_len = 1usize << 18;
        let mut left_conv = vec![Ext4::ZERO; cg_len * 4];
        let mut right_conv = vec![Ext4::ZERO; cg_len * 4];
        for g in 0..GDN_PAD {
            for c in 0..GDN_QKV_PAD {
                let cg = c + (g << 13);
                for kw in 0..4 {
                    let wv = if g < NUM_GDN_LAYERS && c < GDN_QKV_DIM {
                        weights.read_i64(WST_GDN_CONV, kw + (c << 2) + (g << 15))
                    } else {
                        0
                    };
                    right_conv[cg + (kw << 18)] = Ext4::from_bb(bb_from_i64(wv));
                    let mut acc = Ext4::ZERO;
                    for t in 0..FULL_24L_SEQ_LEN {
                        if t + kw >= 3 {
                            let s = t + kw - 3;
                            let qv = m0[M0_QKV][c + (s << 13) + (g << 17)];
                            acc = acc.add(eq_t[t].scale_bb(qv));
                        }
                    }
                    left_conv[cg + (kw << 18)] = acc;
                }
            }
        }
        let z_cg = concat_pts(&[&z_c, &z_g]);
        let (prf, rho, ch, l_at_r, w_at_r, term) = prove_gmask_einsum_par_ext4(
            &left_conv, &right_conv, 18, 2, &z_cg, &gmask, "wm_gdn_conv", &mut tr,
        );
        tr.absorb_ext4(b"conv_wr", w_at_r);
        let (r_c, r_g, r_kw) = (&ch[..13], &ch[13..18], &ch[18..20]);
        weight_claims.push(PublicWeightClaim24L::point_eval(
            WST_GDN_CONV,
            concat_pts(&[r_kw, r_c, r_g]),
            w_at_r,
        ));
        tr.absorb_ext4(b"conv_lr", l_at_r);
        linear_point_evals.push(l_at_r);
        let eq_kw = build_eq_table_lsb_ext4(r_kw);
        let mut s_terms = Vec::with_capacity(16);
        for s in 0..16 {
            let mut wt = Ext4::ZERO;
            for kw in 0..4 {
                if s + 3 >= kw && s + 3 - kw < 16 {
                    wt = wt.add(eq_kw[kw].mul(eq_t[s + 3 - kw]));
                }
            }
            let s_bits = bits_to_ext4(s, 4);
            s_terms.push(LinearTermExt4::PointEval {
                subtable: M0_QKV,
                point: concat_pts(&[r_c, &s_bits, r_g]),
                weight: wt,
            });
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: s_terms, rhs: l_at_r });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_gdn_conv", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_cg, &ch[..18]).mul(l_at_r).mul(w_at_r)),
        ));
        weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r: w_at_r });
    }

    // `wm_gdn_sp_alog` (`SP_Q8[h, t, g] * EXP_ALOG[h, g] = 512 * G_EXP + REM_GEXP - 256 * act_gdn(g)`):
    {
        let z_h = tr.squeeze_ext4_vec(b"spa_zh", 4, true);
        let z_t = tr.squeeze_ext4_vec(b"spa_zt", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"spa_zg", 5, true);
        let pt13 = concat_pts(&[&z_h, &z_t, &z_g]);
        let _ = push_eval(0, M0_G_EXP, pt13.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_GEXP, pt13, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_t = build_eq_table_lsb_ext4(&z_t);
        let mut left_hg = vec![Ext4::ZERO; 512];
        let mut right_hg = vec![Ext4::ZERO; 512];
        for g in 0..GDN_PAD {
            for h in 0..GDN_H {
                let hg = h + (g << 4);
                let ea = weights.read_i64(WST_GDN_ALOG, hg);
                right_hg[hg] = Ext4::from_bb(bb_from_i64(ea));
                let mut s = Ext4::ZERO;
                for t in 0..16 {
                    s = s.add(eq_t[t].scale_bb(m0[M0_SP_Q8][h + (t << 4) + (g << 8)]));
                }
                left_hg[hg] = s;
            }
        }
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (prf, rho, ch, _sp_r, w_at_r, term) = prove_gmask_einsum_par_ext4(
            &left_hg, &right_hg, 9, 0, &z_hg, &gmask, "wm_gdn_sp_alog", &mut tr,
        );
        tr.absorb_ext4(b"spa_wr", w_at_r);
        weight_claims.push(PublicWeightClaim24L::point_eval(WST_GDN_ALOG, ch.clone(), w_at_r));
        let sp_ev = push_eval(0, M0_SP_Q8, concat_pts(&[&ch[..4], &z_t, &ch[4..9]]), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_gdn_sp_alog", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_hg, &ch).mul(sp_ev).mul(w_at_r)),
        ));
        weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r: w_at_r });
    }

    // `wm_lm_head` (`X_FINAL[d, t=15, slot=24] * W_EMBED[d, v] = 512 * LOGITS[v] + REM_LOGITS[v] - 256 * act_vocab(v)`):
    // (`mu_s = 1` on `d[0]`, `kappa = 9` on `d[1..10]`, `z_s = [half]`? No, `mu_s = 1` with `eq([half], b0) = 1/2`,
    // so `2 * sum_{b0, d_hi} eq([half], b0) X[b0, d_hi] W[b0, d_hi] == sum_{d=0}^{1023} X[d] W[d]`!!).
    {
        let z_v = tr.squeeze_ext4_vec(b"lmh_zv", 18, true);
        let _ = push_eval(2, M2_LOGITS, z_v.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(2, M2_REM_LOGITS, z_v.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(2, M2_DIFF_ARGMAX, z_v.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        // Also open `LOGITS` at the exact Boolean hypercube point `bits(emitted_token_id)`!
        let vstar_bits = bits_to_ext4(wit.emitted_token_id as usize, 18);
        online_claims[2].push(JointLinearClaimExt4::point_eval(
            M2_LOGITS,
            vstar_bits,
            Ext4::from_bb(bb_from_i64(wit.claimed_max_logit as i64)),
        ));

        let w_emb_folded = weights.fold_mid_weight_for_einsum(WST_EMBED, 10, 18, 0, &z_v);
        let row_last = 15 + (24 << 4);
        let x_fin: Vec<Ext4> = (0..D_MODEL)
            .map(|d| Ext4::from_bb(m3[RGRP_YOUT][d + (row_last << 10)]))
            .collect();
        let z_half = [Ext4::from_bb(INV2_BB)];
        let (prf, rho, ch, _x_r, w_at_r, term) = prove_gmask_einsum_par_ext4(
            &x_fin, &w_emb_folded, 1, 9, &z_half, &gmask, "wm_lm_head", &mut tr,
        );
        tr.absorb_ext4(b"lmh_wr", w_at_r);
        weight_claims.push(PublicWeightClaim24L::point_eval(
            WST_EMBED,
            concat_pts(&[&ch, &z_v]),
            w_at_r,
        ));
        let t15_s24 = concat_pts(&[&ch, &bits_to_ext4(15, 4), &bits_to_ext4(24, 6)]);
        let x_ev = push_eval(3, RGRP_YOUT, t15_s24, &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_lm_head", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_half, &ch[..1]).mul(x_ev).mul(w_at_r)),
        ));
        weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r: w_at_r });
    }

    // `wm_rms{0,1,2}_gain` (`UQ9 * W_GAIN = gain_div * YOUT + RY - (gain_div/2) * act`):
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let spec = ["wm_rms0_gain", "wm_rms1_gain", "wm_rms2_gain"][g_idx];
        let mf = cfg.log_d + cfg.m_row;
        let z_full = tr.squeeze_ext4_vec(b"rmsg_zf", mf, true);
        let b = cfg.grp * RGRP_STRIDE;
        let _ = push_eval(3, b + RGRP_YOUT, z_full.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_RY, z_full.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);

        let full_len = 1usize << mf;
        let uq9_ext: Vec<Ext4> = m3[b + RGRP_UQ9].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let wgain_ext: Vec<Ext4> = (0..full_len)
            .into_par_iter()
            .map(|idx| {
                let d = idx & ((1usize << cfg.log_d) - 1);
                let row = idx >> cfg.log_d;
                let w_slot = match g_idx {
                    0 => row >> 4,                  // `t: 4, slot: 6` -> `slot`
                    1 => row >> 8,                  // `h: 4, t: 4, gk: 6` -> `gk`
                    _ => (row & 15) + ((row >> 8) << 4), // `hslot: 4, t: 4, q: 3` -> `hslot + (q << 4)`
                };
                Ext4::from_bb(bb_from_i64(weights.read_i64(cfg.wst_gain, d + (w_slot << cfg.log_d))))
            })
            .collect();
        let (prf, rho, ch, _u_r, w_at_r, term) = prove_gmask_einsum_par_ext4(
            &uq9_ext, &wgain_ext, mf, 0, &z_full, &gmask, spec, &mut tr,
        );
        tr.absorb_ext4(b"rmsg_wr", w_at_r);
        let w_pt = match g_idx {
            0 => concat_pts(&[&ch[..10], &ch[14..20]]),
            1 => concat_pts(&[&ch[..7], &ch[15..21]]),
            _ => concat_pts(&[&ch[..8], &ch[8..12], &ch[16..19]]),
        };
        weight_claims.push(PublicWeightClaim24L::point_eval(cfg.wst_gain, w_pt, w_at_r));
        let u_ev = push_eval(3, b + RGRP_UQ9, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_full, &ch).mul(u_ev).mul(w_at_r)),
        ));
        weight_matmul_proofs.push(SecPubWeightEinSumOpening { prf, weight_at_r: w_at_r });
    }

    // Step C: `pub_ind_proofs` (public indicator zerochecks, RoPE, & `DIFF_NORM`):
    // Helper closure for `Wit * PubInd == claim`:
    let prove_wit_pub = |spec: &str,
                             wit_mat: usize,
                             wit_st: usize,
                             wit_override: Option<Vec<Ext4>>,
                             wit_pt_map: Option<fn(&[Ext4]) -> Vec<Ext4>>,
                             pub_vec: Vec<Ext4>,
                             z_s: Vec<Ext4>,
                             tr_ref: &mut CShakeTranscript,
                             lin_evs: &mut Vec<Ext4>,
                             onl_cl: &mut [Vec<JointLinearClaimExt4>; 4],
                             pi_out: &mut Vec<BlindedEinSumExt4Proof>| {
        let m = z_s.len();
        let w_ext: Vec<Ext4> = wit_override.unwrap_or_else(|| {
            mats_all[wit_mat][wit_st]
                .par_iter()
                .map(|&v| Ext4::from_bb(v))
                .collect()
        });
        let (prf, rho, ch, w_at_r, p_at_r, term) =
            prove_gmask_einsum_par_ext4(&w_ext, &pub_vec, m, 0, &z_s, &gmask, spec, tr_ref);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        onl_cl[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        let scale = eq_mle_ext4(&z_s, &ch).mul(p_at_r);
        let mapped_pt = wit_pt_map.map_or_else(|| ch.clone(), |f| f(&ch));
        if wit_mat == 2 && wit_st < 999 {
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                vec![LinearTermExt4::PointEval {
                    subtable: wit_st,
                    point: mapped_pt,
                    weight: scale,
                }],
                gm_limb_ids,
                &w_at,
                rho,
                term,
            ));
        } else if wit_st < 999 {
            let wev = push_eval(wit_mat, wit_st, mapped_pt, tr_ref, lin_evs, onl_cl);
            let _ = w_at_r;
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale.mul(wev)),
            ));
        } else {
            // Custom linear expression discharged by caller using `w_at_r`!
            tr_ref.absorb_ext4(b"pi_wr", w_at_r);
            lin_evs.push(w_at_r);
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale.mul(w_at_r)),
            ));
        }
        pi_out.push(prf);
        ch
    };

    // Build 17-bit GDN triangular masks `[h: 16, i: 16, j: 16, g: 32]`:
    let mut bad_gamma = vec![Ext4::ZERO; 1 << 17];
    let mut bad_lwy = vec![Ext4::ZERO; 1 << 17];
    let mut bad_awy = vec![Ext4::ZERO; 1 << 17];
    for g in 0..32 {
        for j in 0..16 {
            for i in 0..16 {
                let ge = g < 18 && i >= j;
                let gt = g < 18 && i > j;
                for h in 0..16 {
                    let idx = h + (i << 4) + (j << 8) + (g << 12);
                    if !ge {
                        bad_gamma[idx] = Ext4::ONE;
                        bad_awy[idx] = Ext4::ONE;
                    }
                    if !gt {
                        bad_lwy[idx] = Ext4::ONE;
                    }
                }
            }
        }
    }
    let z_g1 = tr.squeeze_ext4_vec(b"pi_zg1", 17, true);
    prove_wit_pub("pi_gdn_gamma_zc", 0, M0_GAMMA, None, None, bad_gamma, z_g1, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
    let z_g2 = tr.squeeze_ext4_vec(b"pi_zg2", 17, true);
    prove_wit_pub("pi_gdn_lwy_slt", 0, M0_L_WY, None, None, bad_lwy, z_g2, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
    let z_g3 = tr.squeeze_ext4_vec(b"pi_zg3", 17, true);
    prove_wit_pub("pi_gdn_awy_ut", 0, M0_A_WY, None, None, bad_awy, z_g3, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);

    // GQA Q-RoPE (`[dh: 256, hq: 8, t: 16, q: 8]` = `18` vars) & K-RoPE (`[dh: 256, hkv: 2, t: 16, q: 8]` = `16` vars):
    {
        let z_rq = tr.squeeze_ext4_vec(b"rope_zq", 18, true);
        let _ = push_eval(1, M1_QH_R, z_rq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_ROPE_Q, z_rq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let b2 = 2 * RGRP_STRIDE;
        let qnorm_18: Vec<Ext4> = (0..(1 << 18))
            .map(|idx| {
                let dh = idx & 255;
                let hq = (idx >> 8) & 7;
                let t = (idx >> 11) & 15;
                let q = idx >> 15;
                Ext4::from_bb(m3[b2 + RGRP_YOUT][dh + (hq << 8) + (t << 12) + (q << 16)])
            })
            .collect();
        let qswap_18: Vec<Ext4> = (0..(1 << 18))
            .map(|idx| qnorm_18[idx ^ 32])
            .collect();
        let rdiag_18: Vec<Ext4> = (0..(1 << 18))
            .map(|idx| {
                let dh = idx & 255;
                let t = (idx >> 11) & 15;
                let q = idx >> 15;
                if q < 6 {
                    Ext4::from_bb(luts.rope_diag_bb[dh + (t << 8)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let rcross_18: Vec<Ext4> = (0..(1 << 18))
            .map(|idx| {
                let dh = idx & 255;
                let t = (idx >> 11) & 15;
                let q = idx >> 15;
                if q < 6 {
                    Ext4::from_bb(luts.rope_cross_bb[dh + (t << 8)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        // Record the unmasked partial claims of `diag` and `cross` so `diag + cross == 2048 * QH_R + REM_ROPE_Q - 1024 * act_gqa`!
        let eq_zrq = build_eq_table_lsb_ext4(&z_rq);
        let cl_qd: Ext4 = (0..(1 << 18))
            .into_par_iter()
            .map(|i| eq_zrq[i].mul(qnorm_18[i]).mul(rdiag_18[i]))
            .reduce(|| Ext4::ZERO, |a, b| a.add(b));
        tr.absorb_ext4(b"rope_q_cd", cl_qd);
        linear_point_evals.push(cl_qd);
        fn map_q18_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[&ch[..8], &ch[8..11], &[Ext4::ZERO], &ch[11..15], &ch[15..18]])
        }
        fn map_q18_swap_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..5],
                &[Ext4::ONE.sub(ch[5])],
                &ch[6..8],
                &ch[8..11],
                &[Ext4::ZERO],
                &ch[11..15],
                &ch[15..18],
            ])
        }
        prove_wit_pub("pi_gqa_rope_q_diag", 3, b2 + RGRP_YOUT, Some(qnorm_18), Some(map_q18_to_rms), rdiag_18, z_rq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        prove_wit_pub("pi_gqa_rope_q_cross", 3, b2 + RGRP_YOUT, Some(qswap_18), Some(map_q18_swap_to_rms), rcross_18, z_rq, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);

        // K-RoPE (`16` vars `[dh: 256, hkv: 2, t: 16, q: 8]` -> `hslot = 8 + hkv = [hkv, 0, 0, 1]`!):
        let z_rk = tr.squeeze_ext4_vec(b"rope_zk", 16, true);
        let _ = push_eval(1, M1_KH_R, z_rk.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_ROPE_K, z_rk.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let knorm_16: Vec<Ext4> = (0..(1 << 16))
            .map(|idx| {
                let dh = idx & 255;
                let hk = (idx >> 8) & 1;
                let t = (idx >> 9) & 15;
                let q = idx >> 13;
                Ext4::from_bb(m3[b2 + RGRP_YOUT][dh + ((8 + hk) << 8) + (t << 12) + (q << 16)])
            })
            .collect();
        let kswap_16: Vec<Ext4> = (0..(1 << 16)).map(|idx| knorm_16[idx ^ 32]).collect();
        let rdiag_16: Vec<Ext4> = (0..(1 << 16))
            .map(|idx| {
                let dh = idx & 255;
                let t = (idx >> 9) & 15;
                let q = idx >> 13;
                if q < 6 {
                    Ext4::from_bb(luts.rope_diag_bb[dh + (t << 8)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let rcross_16: Vec<Ext4> = (0..(1 << 16))
            .map(|idx| {
                let dh = idx & 255;
                let t = (idx >> 9) & 15;
                let q = idx >> 13;
                if q < 6 {
                    Ext4::from_bb(luts.rope_cross_bb[dh + (t << 8)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let eq_zrk = build_eq_table_lsb_ext4(&z_rk);
        let cl_kd: Ext4 = (0..(1 << 16))
            .into_par_iter()
            .map(|i| eq_zrk[i].mul(knorm_16[i]).mul(rdiag_16[i]))
            .reduce(|| Ext4::ZERO, |a, b| a.add(b));
        tr.absorb_ext4(b"rope_k_cd", cl_kd);
        linear_point_evals.push(cl_kd);
        fn map_k16_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..8],
                &[ch[8], Ext4::ZERO, Ext4::ZERO, Ext4::ONE],
                &ch[9..13],
                &ch[13..16],
            ])
        }
        fn map_k16_swap_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..5],
                &[Ext4::ONE.sub(ch[5])],
                &ch[6..8],
                &[ch[8], Ext4::ZERO, Ext4::ZERO, Ext4::ONE],
                &ch[9..13],
                &ch[13..16],
            ])
        }
        prove_wit_pub("pi_gqa_rope_k_diag", 3, b2 + RGRP_YOUT, Some(knorm_16), Some(map_k16_to_rms), rdiag_16, z_rk.clone(), &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        prove_wit_pub("pi_gqa_rope_k_cross", 3, b2 + RGRP_YOUT, Some(kswap_16), Some(map_k16_swap_to_rms), rcross_16, z_rk, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
    }

    // GQA 14-bit causal indicator checks `[tj: 16, ti: 16, hq: 8, q: 8]`:
    {
        let mut caus_ind = vec![Ext4::ZERO; 1 << 14];
        let mut non_caus = vec![Ext4::ZERO; 1 << 14];
        for q in 0..8 {
            for hq in 0..8 {
                for ti in 0..16 {
                    for tj in 0..16 {
                        let idx = tj + (ti << 4) + (hq << 8) + (q << 11);
                        if q < 6 && tj <= ti {
                            caus_ind[idx] = Ext4::ONE;
                        } else {
                            non_caus[idx] = Ext4::ONE;
                        }
                    }
                }
            }
        }
        let zc1 = tr.squeeze_ext4_vec(b"gqa_zc1", 14, true);
        prove_wit_pub("pi_gqa_sc_caus", 1, M1_SC_Q8, None, None, non_caus.clone(), zc1, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        let zc2 = tr.squeeze_ext4_vec(b"gqa_zc2", 14, true);
        prove_wit_pub("pi_gqa_sel_caus", 1, M1_SEL_MAX, None, None, non_caus.clone(), zc2, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);

        // `I_caus * (M_MAX - SC_Q8) == U_SM`:
        let zc3 = tr.squeeze_ext4_vec(b"gqa_zc3", 14, true);
        let _ = push_eval(1, M1_U_SM, zc3.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let diff_msc: Vec<Ext4> = (0..(1 << 14))
            .map(|idx| {
                let m_v = m1[M1_M_MAX][idx >> 4];
                Ext4::from_bb(bsub(m_v, m1[M1_SC_Q8][idx]))
            })
            .collect();
        let ch3 = prove_wit_pub("pi_gqa_usm_caus", 1, 999, Some(diff_msc), None, caus_ind.clone(), zc3, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        let wr3 = *linear_point_evals.last().unwrap();
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_M_MAX, point: ch3[4..].to_vec(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M1_SC_Q8, point: ch3, weight: Ext4::ONE.neg() },
            ],
            rhs: wr3,
        });

        // `I_caus * E_SM_RAW == E_SM`:
        let zc4 = tr.squeeze_ext4_vec(b"gqa_zc4", 14, true);
        let _ = push_eval(1, M1_E_SM, zc4.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        prove_wit_pub("pi_gqa_esm_caus", 1, M1_E_SM_RAW, None, None, caus_ind.clone(), zc4, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);

        // `(1 - I_caus) * P_SM == 0`:
        let zc5 = tr.squeeze_ext4_vec(b"gqa_zc5", 14, true);
        prove_wit_pub("pi_gqa_psm_caus", 1, M1_P_SM, None, None, non_caus, zc5, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);

        // `I_caus * (Z_SM - 1 - REM_PSM) == DIFF_PSM`:
        let zc6 = tr.squeeze_ext4_vec(b"gqa_zc6", 14, true);
        let _ = push_eval(1, M1_DIFF_PSM, zc6.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let diff_zrem: Vec<Ext4> = (0..(1 << 14))
            .map(|idx| {
                let zv = m1[M1_Z_SM][idx >> 4];
                Ext4::from_bb(bsub(bsub(zv, 1), m1[M1_REM_PSM][idx]))
            })
            .collect();
        let ch6 = prove_wit_pub("pi_gqa_dpsm_caus", 1, 999, Some(diff_zrem), None, caus_ind, zc6, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        let wr6 = *linear_point_evals.last().unwrap();
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_Z_SM, point: ch6[4..].to_vec(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M1_REM_PSM, point: ch6, weight: Ext4::ONE.neg() },
            ],
            rhs: wr6.add(Ext4::ONE),
        });
    }

    // `pi_rms{0,1,2}_dnorm`: `act_row(row) * (POW4 - 1 - RNORM) == DIFF_NORM`:
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let spec = ["pi_rms0_dnorm", "pi_rms1_dnorm", "pi_rms2_dnorm"][g_idx];
        let b = cfg.grp * RGRP_STRIDE;
        let mr = cfg.m_row;
        let zr = tr.squeeze_ext4_vec(b"rmsdn_zr", mr, true);
        let _ = push_eval(3, b + RGRP_DIFF_NORM, zr.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let act_vec: Vec<Ext4> = (0..(1usize << mr))
            .map(|row| {
                let active = match g_idx {
                    0 => {
                        let sl = row >> 4;
                        sl < 25 || (32..56).contains(&sl)
                    }
                    1 => (row >> 8) < 54,
                    _ => (row & 15) < 10 && (row >> 8) < 6,
                };
                if active { Ext4::ONE } else { Ext4::ZERO }
            })
            .collect();
        let diff_p4: Vec<Ext4> = (0..(1usize << mr))
            .map(|row| {
                let p4 = m3[b + RGRP_POW4][row];
                let rn = m3[b + RGRP_RNORM][row];
                Ext4::from_bb(bsub(bsub(p4, 1), rn))
            })
            .collect();
        let chr = prove_wit_pub(spec, 3, 999, Some(diff_p4), None, act_vec, zr, &mut tr, &mut linear_point_evals, &mut online_claims, &mut pub_ind_proofs);
        let wr = *linear_point_evals.last().unwrap();
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_POW4, point: chr.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: b + RGRP_RNORM, point: chr, weight: Ext4::ONE.neg() },
            ],
            rhs: wr.add(Ext4::ONE),
        });
    }

    // Step D: `sec_sec_proofs` (all witness × witness bilinear contractions across GDN, GQA, MLP, & RMSNorm):
    // 1. `ss_gdn_gamma_rec`: `GAMMA_PREV[h, i, j, g] * ALPHA_Q12[h, i, g] == 4096 * (GAMMA - 512 * I_diag) + REM_GAMMA - 2048 * I_gt`
    {
        let z17 = tr.squeeze_ext4_vec(b"gmrec_z", 17, true);
        let _ = push_eval(0, M0_GAMMA, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_GAMMA, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let mut g_prev = vec![Ext4::ZERO; 1 << 17];
        let mut a_lift = vec![Ext4::ZERO; 1 << 17];
        for g in 0..GDN_PAD {
            for j in 0..16 {
                for i in 0..16 {
                    for h in 0..16 {
                        let idx = h + (i << 4) + (j << 8) + (g << 12);
                        a_lift[idx] = Ext4::from_bb(m0[M0_ALPHA_Q12][h + (i << 4) + (g << 8)]);
                        if i > j {
                            g_prev[idx] = Ext4::from_bb(m0[M0_GAMMA][h + ((i - 1) << 4) + (j << 8) + (g << 12)]);
                        }
                    }
                }
            }
        }
        let (prf, rho, ch, gp_at_r, al_at_r, term) = prove_gmask_einsum_par_ext4(
            &g_prev, &a_lift, 17, 0, &z17, &gmask, "ss_gdn_gamma_rec", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", gp_at_r);
        let _ = al_at_r;
        // Discharge `gp_at_r = GAMMA_PREV(ch)` (`M0_GAMMA` is already 0 on `g >= 18` via `pi_gdn_gamma_zc`!):
        let eq_i = build_eq_table_lsb_ext4(&ch[4..8]);
        let eq_j = build_eq_table_lsb_ext4(&ch[8..12]);
        let mut terms_gp = Vec::with_capacity(120);
        for j in 0..16 {
            for ip in j..15 {
                let wt = eq_i[ip + 1].mul(eq_j[j]);
                terms_gp.push(LinearTermExt4::PointEval {
                    subtable: M0_GAMMA,
                    point: concat_pts(&[&ch[..4], &bits_to_ext4(ip, 4), &bits_to_ext4(j, 4), &ch[12..17]]),
                    weight: wt,
                });
            }
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: terms_gp, rhs: gp_at_r });
        let al_ev = push_eval(0, M0_ALPHA_Q12, concat_pts(&[&ch[..8], &ch[12..17]]), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_gamma_rec", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z17, &ch).mul(gp_at_r).mul(al_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: gp_at_r });
    }

    // 2. `ss_gdn_dkk` (`k_n[i] @ k_n[j] = 512 * DKK + REM_DKK - 256 * act_gdn(g)`, `mu_s = 9` `(h:4, g:5)`, `kappa = 7` `d`):
    {
        let z_h = tr.squeeze_ext4_vec(b"dkk_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"dkk_zi", 4, true);
        let z_j = tr.squeeze_ext4_vec(b"dkk_zj", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"dkk_zg", 5, true);
        let pt17 = concat_pts(&[&z_h, &z_i, &z_j, &z_g]);
        let _ = push_eval(0, M0_DKK, pt17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_DKK, pt17, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_i = build_eq_table_lsb_ext4(&z_i);
        let eq_j = build_eq_table_lsb_ext4(&z_j);
        let mut kn_i = vec![Ext4::ZERO; 512 * 128];
        let mut kn_j = vec![Ext4::ZERO; 512 * 128];
        let b1 = RGRP_STRIDE;
        for g in 0..NUM_GDN_LAYERS {
            let gk = 3 * g + 1;
            for h in 0..16 {
                let hg = h + (g << 4);
                for t in 0..16 {
                    let base = (h + (t << 4) + (gk << 8)) << 7;
                    let sl = &m3[b1 + RGRP_YOUT][base..base + 128];
                    for d in 0..128 {
                        kn_i[hg + (d << 9)] = kn_i[hg + (d << 9)].add(eq_i[t].scale_bb(sl[d]));
                        kn_j[hg + (d << 9)] = kn_j[hg + (d << 9)].add(eq_j[t].scale_bb(sl[d]));
                    }
                }
            }
        }
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &kn_i, &kn_j, 9, 7, &z_hg, &gmask, "ss_gdn_dkk", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let (r_h, r_g, r_d) = (&ch[..4], &ch[4..9], &ch[9..16]);
        let eq_rg = build_eq_table_lsb_ext4(r_g);
        let mut t_i = Vec::with_capacity(18);
        let mut t_j = Vec::with_capacity(18);
        let mut r_val = Ext4::ZERO;
        for g in 0..NUM_GDN_LAYERS {
            let gk_bits = bits_to_ext4(3 * g + 1, 6);
            let pti = concat_pts(&[r_d, r_h, &z_i, &gk_bits]);
            let ptj = concat_pts(&[r_d, r_h, &z_j, &gk_bits]);
            r_val = r_val.add(eq_rg[g].mul(mle_eval_bb_at_ext4(&m3[b1 + RGRP_YOUT], &ptj)));
            t_i.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: pti, weight: eq_rg[g] });
            t_j.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: ptj, weight: eq_rg[g] });
        }
        tr.absorb_ext4(b"dkk_rr", r_val);
        linear_point_evals.push(r_val);
        online_claims[3].push(JointLinearClaimExt4 { terms: t_i, rhs: l_r });
        online_claims[3].push(JointLinearClaimExt4 { terms: t_j, rhs: r_val });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_dkk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(l_r).mul(r_val)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 3. `ss_gdn_bg` (`BETA_Q10[h, i, g] * GAMMA[h, i, j, g] = 1024 * BG + REM_BG - 512 * act_gdn(g)`):
    {
        let z17 = tr.squeeze_ext4_vec(b"bg_z", 17, true);
        let _ = push_eval(0, M0_BG, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_BG, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let b_lift: Vec<Ext4> = (0..(1 << 17))
            .map(|idx| {
                let h = idx & 15;
                let i = (idx >> 4) & 15;
                let g = idx >> 12;
                Ext4::from_bb(m0[M0_BETA_Q10][h + (i << 4) + (g << 8)])
            })
            .collect();
        let gm_ext: Vec<Ext4> = m0[M0_GAMMA].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &b_lift, &gm_ext, 17, 0, &z17, &gmask, "ss_gdn_bg", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let b_ev = push_eval(0, M0_BETA_Q10, concat_pts(&[&ch[..8], &ch[12..17]]), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = b_ev;
        let gm_ev = push_eval(0, M0_GAMMA, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_bg", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(l_r).mul(gm_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 4. `ss_gdn_lwy` (`(I_gt * DKK) * BG = 512 * L_WY + REM_LWY - 256 * I_gt`):
    {
        let z17 = tr.squeeze_ext4_vec(b"lwy_z", 17, true);
        let _ = push_eval(0, M0_L_WY, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_LWY, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let dkk_gt: Vec<Ext4> = (0..(1 << 17))
            .map(|idx| {
                let i = (idx >> 4) & 15;
                let j = (idx >> 8) & 15;
                if i > j {
                    Ext4::from_bb(m0[M0_DKK][idx])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let bg_ext: Vec<Ext4> = m0[M0_BG].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &dkk_gt, &bg_ext, 17, 0, &z17, &gmask, "ss_gdn_lwy", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let eq_i = build_eq_table_lsb_ext4(&ch[4..8]);
        let eq_j = build_eq_table_lsb_ext4(&ch[8..12]);
        let mut dkk_terms = Vec::with_capacity(120);
        for j in 0..16 {
            for i in (j + 1)..16 {
                dkk_terms.push(LinearTermExt4::PointEval {
                    subtable: M0_DKK,
                    point: concat_pts(&[&ch[..4], &bits_to_ext4(i, 4), &bits_to_ext4(j, 4), &ch[12..17]]),
                    weight: eq_i[i].mul(eq_j[j]),
                });
            }
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: dkk_terms, rhs: l_r });
        let bg_ev = push_eval(0, M0_BG, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_lwy", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(l_r).mul(bg_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 5. `ss_gdn_dqk` (`q_n[i] @ k_n[j] = 724 * DQK + REM_DQK - 362 * act_gdn(g)`):
    {
        let z_h = tr.squeeze_ext4_vec(b"dqk_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"dqk_zi", 4, true);
        let z_j = tr.squeeze_ext4_vec(b"dqk_zj", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"dqk_zg", 5, true);
        let pt17 = concat_pts(&[&z_h, &z_i, &z_j, &z_g]);
        let _ = push_eval(0, M0_DQK, pt17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_DQK, pt17, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_i = build_eq_table_lsb_ext4(&z_i);
        let eq_j = build_eq_table_lsb_ext4(&z_j);
        let mut qn_i = vec![Ext4::ZERO; 512 * 128];
        let mut kn_j = vec![Ext4::ZERO; 512 * 128];
        let b1 = RGRP_STRIDE;
        for g in 0..NUM_GDN_LAYERS {
            for h in 0..16 {
                let hg = h + (g << 4);
                for t in 0..16 {
                    let bq = (h + (t << 4) + ((3 * g) << 8)) << 7;
                    let bk = (h + (t << 4) + ((3 * g + 1) << 8)) << 7;
                    for d in 0..128 {
                        qn_i[hg + (d << 9)] = qn_i[hg + (d << 9)].add(eq_i[t].scale_bb(m3[b1 + RGRP_YOUT][bq + d]));
                        kn_j[hg + (d << 9)] = kn_j[hg + (d << 9)].add(eq_j[t].scale_bb(m3[b1 + RGRP_YOUT][bk + d]));
                    }
                }
            }
        }
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &qn_i, &kn_j, 9, 7, &z_hg, &gmask, "ss_gdn_dqk", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let (r_h, r_g, r_d) = (&ch[..4], &ch[4..9], &ch[9..16]);
        let eq_rg = build_eq_table_lsb_ext4(r_g);
        let mut t_i = Vec::with_capacity(18);
        let mut t_j = Vec::with_capacity(18);
        let mut r_val = Ext4::ZERO;
        for g in 0..NUM_GDN_LAYERS {
            let pti = concat_pts(&[r_d, r_h, &z_i, &bits_to_ext4(3 * g, 6)]);
            let ptj = concat_pts(&[r_d, r_h, &z_j, &bits_to_ext4(3 * g + 1, 6)]);
            r_val = r_val.add(eq_rg[g].mul(mle_eval_bb_at_ext4(&m3[b1 + RGRP_YOUT], &ptj)));
            t_i.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: pti, weight: eq_rg[g] });
            t_j.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: ptj, weight: eq_rg[g] });
        }
        tr.absorb_ext4(b"dqk_rr", r_val);
        linear_point_evals.push(r_val);
        online_claims[3].push(JointLinearClaimExt4 { terms: t_i, rhs: l_r });
        online_claims[3].push(JointLinearClaimExt4 { terms: t_j, rhs: r_val });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_dqk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(l_r).mul(r_val)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 6. `ss_gdn_awy` (`DQK * GAMMA = 512 * A_WY + REM_AWY - 256 * I_ge`; `GAMMA == 0` outside `I_ge` via `pi_gdn_gamma_zc`!):
    {
        let z17 = tr.squeeze_ext4_vec(b"awy_z", 17, true);
        let _ = push_eval(0, M0_A_WY, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_AWY, z17.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let dqk_ext: Vec<Ext4> = m0[M0_DQK].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let gm_ext: Vec<Ext4> = m0[M0_GAMMA].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &dqk_ext, &gm_ext, 17, 0, &z17, &gmask, "ss_gdn_awy", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let _ = push_eval(0, M0_DQK, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let gm_ev = push_eval(0, M0_GAMMA, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_awy", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(l_r).mul(gm_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 7. `ss_gdn_vbeta` (`BETA_Q10[h, t, g] * V_R[d, h, t, g] = 512 * V_BETA + REM_VBETA - 256 * act_gdn(g)`):
    {
        let z20 = tr.squeeze_ext4_vec(b"vb_z", 20, true);
        let _ = push_eval(0, M0_V_BETA, z20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_VBETA, z20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let b_lift: Vec<Ext4> = (0..(1 << 20))
            .map(|idx| {
                let h = (idx >> 7) & 15;
                let t = (idx >> 11) & 15;
                let g = idx >> 15;
                if g < 18 {
                    Ext4::from_bb(m0[M0_BETA_Q10][h + (t << 4) + (g << 8)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let vr_ext: Vec<Ext4> = (0..(1 << 20))
            .map(|idx| {
                let dh = idx & 2047;
                let tg = idx >> 11;
                Ext4::from_bb(m0[M0_CONV_SILU][dh + 4096 + (tg << 13)])
            })
            .collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &b_lift, &vr_ext, 20, 0, &z20, &gmask, "ss_gdn_vbeta", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let eq_rg = build_eq_table_lsb_ext4(&ch[15..20]);
        let b_terms: Vec<LinearTermExt4> = (0..NUM_GDN_LAYERS)
            .map(|g| LinearTermExt4::PointEval {
                subtable: M0_BETA_Q10,
                point: concat_pts(&[&ch[7..15], &bits_to_ext4(g, 5)]),
                weight: eq_rg[g],
            })
            .collect();
        online_claims[0].push(JointLinearClaimExt4 { terms: b_terms, rhs: l_r });
        let vr_pt = concat_pts(&[&ch[..11], &[Ext4::ZERO, Ext4::ONE], &ch[11..20]]);
        let vr_ev = push_eval(0, M0_CONV_SILU, vr_pt, &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_vbeta", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z20, &ch).mul(l_r).mul(vr_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 8 & 9: `ss_gdn_uwy_solve` (`L_WY @ U_WY = 512*(V_BETA - U_WY) + 256*act_gdn - REM_UWY`) & `ss_gdn_ywy_read` (`A_WY @ U_WY = 512*Y_WY + REM_YWY - 256*act_gdn`):
    for (spec, mat_st, out_st, rem_st, is_solve) in [
        ("ss_gdn_uwy_solve", M0_L_WY, M0_U_WY, M0_REM_UWY, true),
        ("ss_gdn_ywy_read", M0_A_WY, M0_Y_WY, M0_REM_YWY, false),
    ] {
        let z_d = tr.squeeze_ext4_vec(b"wy_zd", 7, true);
        let z_h = tr.squeeze_ext4_vec(b"wy_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"wy_zi", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"wy_zg", 5, true);
        let pt20 = concat_pts(&[&z_d, &z_h, &z_i, &z_g]);
        if is_solve {
            let _ = push_eval(0, M0_V_BETA, pt20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        }
        let _ = push_eval(0, out_st, pt20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, rem_st, pt20, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_i = build_eq_table_lsb_ext4(&z_i);
        let eq_d = build_eq_table_lsb_ext4(&z_d);
        let mut left_hgj = vec![Ext4::ZERO; 512 * 16];
        let mut right_hgj = vec![Ext4::ZERO; 512 * 16];
        for g in 0..32 {
            for h in 0..16 {
                let hg = h + (g << 4);
                for j in 0..16 {
                    let mut sl = Ext4::ZERO;
                    for i in 0..16 {
                        sl = sl.add(eq_i[i].scale_bb(m0[mat_st][h + (i << 4) + (j << 8) + (g << 12)]));
                    }
                    left_hgj[hg + (j << 9)] = sl;
                    let mut sr = Ext4::ZERO;
                    let u_base = (h << 7) + (j << 11) + (g << 15);
                    for d in 0..128 {
                        sr = sr.add(eq_d[d].scale_bb(m0[M0_U_WY][u_base + d]));
                    }
                    right_hgj[hg + (j << 9)] = sr;
                }
            }
        }
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &left_hgj, &right_hgj, 9, 4, &z_hg, &gmask, spec, &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let (r_h, r_g, r_j) = (&ch[..4], &ch[4..9], &ch[9..13]);
        online_claims[0].push(JointLinearClaimExt4::point_eval(
            mat_st,
            concat_pts(&[r_h, &z_i, r_j, r_g]),
            l_r,
        ));
        let u_ev = push_eval(0, M0_U_WY, concat_pts(&[&z_d, r_h, r_j, r_g]), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(l_r).mul(u_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 10. `ss_gdn_gated` (`Y_NORM * Z_SILU = 256 * GATED + REM_GATED - 128 * act_gdn(g)`):
    {
        let z20 = tr.squeeze_ext4_vec(b"gg_z", 20, true);
        let _ = push_eval(0, M0_GATED, z20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_REM_GATED, z20.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let b1 = RGRP_STRIDE;
        let yn_20: Vec<Ext4> = (0..(1 << 20))
            .map(|idx| {
                let g = idx >> 15;
                if g < 18 {
                    let dht = idx & 0x7FFF;
                    Ext4::from_bb(m3[b1 + RGRP_YOUT][dht + ((3 * g + 2) << 15)])
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        let zs_20: Vec<Ext4> = m0[M0_Z_SILU].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &yn_20, &zs_20, 20, 0, &z20, &gmask, "ss_gdn_gated", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let eq_rg = build_eq_table_lsb_ext4(&ch[15..20]);
        let mut yn_terms = Vec::with_capacity(18);
        for g in 0..NUM_GDN_LAYERS {
            yn_terms.push(LinearTermExt4::PointEval {
                subtable: b1 + RGRP_YOUT,
                point: concat_pts(&[&ch[..15], &bits_to_ext4(3 * g + 2, 6)]),
                weight: eq_rg[g],
            });
        }
        online_claims[3].push(JointLinearClaimExt4 { terms: yn_terms, rhs: l_r });
        let zs_ev = push_eval(0, M0_Z_SILU, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_gated", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z20, &ch).mul(l_r).mul(zs_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 11. `ss_gqa_qk`: `(I_caus(tj, ti, q) * KH_R[dh, hq>>2, tj, q]) @ QH_R[dh, hq, ti, q] = 256 * SC_Q8 + REM_SC - 128 * I_caus`
    {
        let z_tj = tr.squeeze_ext4_vec(b"qk_ztj", 4, true);
        let z_ti = tr.squeeze_ext4_vec(b"qk_zti", 4, true);
        let z_hq = tr.squeeze_ext4_vec(b"qk_zhq", 3, true);
        let z_q = tr.squeeze_ext4_vec(b"qk_zq", 3, true);
        let pt14 = concat_pts(&[&z_tj, &z_ti, &z_hq, &z_q]);
        let _ = push_eval(1, M1_SC_Q8, pt14.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_SC, pt14, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_tj = build_eq_table_lsb_ext4(&z_tj);
        let mut k_caus = vec![Ext4::ZERO; 1024 * 256];
        let mut q_unf = vec![Ext4::ZERO; 1024 * 256];
        for q in 0..GQA_PAD {
            for hq in 0..GQA_HQ {
                let hk = hq >> 2;
                for ti in 0..16 {
                    let row10 = ti + (hq << 4) + (q << 7);
                    let q_base = (hq << 8) + (ti << 11) + (q << 15);
                    for dh in 0..256 {
                        q_unf[row10 + (dh << 10)] = Ext4::from_bb(m1[M1_QH_R][q_base + dh]);
                    }
                    if q < NUM_GQA_LAYERS {
                        for tj in 0..=ti {
                            let ew = eq_tj[tj];
                            let k_base = (hk << 8) + (tj << 9) + (q << 13);
                            for dh in 0..256 {
                                k_caus[row10 + (dh << 10)] =
                                    k_caus[row10 + (dh << 10)].add(ew.scale_bb(m1[M1_KH_R][k_base + dh]));
                            }
                        }
                    }
                }
            }
        }
        let z10 = concat_pts(&[&z_ti, &z_hq, &z_q]);
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &k_caus, &q_unf, 10, 8, &z10, &gmask, "ss_gqa_qk", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let (r_ti, r_hq, r_q, r_dh) = (&ch[..4], &ch[4..7], &ch[7..10], &ch[10..18]);
        let eq_rti = build_eq_table_lsb_ext4(r_ti);
        let eq_rq = build_eq_table_lsb_ext4(r_q);
        let mut k_terms = Vec::with_capacity(96);
        for q in 0..NUM_GQA_LAYERS {
            let q_bits = bits_to_ext4(q, 3);
            for tj in 0..16 {
                let mut sum_ti = Ext4::ZERO;
                for &eti in &eq_rti[tj..16] {
                    sum_ti = sum_ti.add(eti);
                }
                let wt = eq_rq[q].mul(eq_tj[tj]).mul(sum_ti);
                k_terms.push(LinearTermExt4::PointEval {
                    subtable: M1_KH_R,
                    point: concat_pts(&[r_dh, &[r_hq[2]], &bits_to_ext4(tj, 4), &q_bits]),
                    weight: wt,
                });
            }
        }
        online_claims[1].push(JointLinearClaimExt4 { terms: k_terms, rhs: l_r });
        let q_ev = push_eval(
            1,
            M1_QH_R,
            concat_pts(&[r_dh, r_hq, r_ti, r_q]),
            &mut tr,
            &mut linear_point_evals,
            &mut online_claims,
        );
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_qk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z10, &ch[..10]).mul(l_r).mul(q_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 12. `ss_gqa_sel_bool`: `SEL_MAX * (1 - SEL_MAX) == 0`
    {
        let z14 = tr.squeeze_ext4_vec(b"selb_z", 14, true);
        let sel_ext: Vec<Ext4> = m1[M1_SEL_MAX].iter().map(|&v| Ext4::from_bb(v)).collect();
        let comp_ext: Vec<Ext4> = sel_ext.iter().map(|&v| Ext4::ONE.sub(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &sel_ext, &comp_ext, 14, 0, &z14, &gmask, "ss_gqa_sel_bool", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_SEL_MAX, ch.clone(), l_r));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_sel_bool", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z14, &ch).mul(l_r).mul(Ext4::ONE.sub(l_r))),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 13. `ss_gqa_sel_max`: `SEL_MAX * (M_MAX[ti, hq, q] - SC_Q8[tj, ti, hq, q]) == 0`
    {
        let z14 = tr.squeeze_ext4_vec(b"selm_z", 14, true);
        let sel_ext: Vec<Ext4> = m1[M1_SEL_MAX].iter().map(|&v| Ext4::from_bb(v)).collect();
        let diff_ext: Vec<Ext4> = (0..(1 << 14))
            .map(|idx| Ext4::from_bb(bsub(m1[M1_M_MAX][idx >> 4], m1[M1_SC_Q8][idx])))
            .collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &sel_ext, &diff_ext, 14, 0, &z14, &gmask, "ss_gqa_sel_max", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_SEL_MAX, ch.clone(), l_r));
        let m_ev = push_eval(1, M1_M_MAX, ch[4..].to_vec(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let sc_ev = push_eval(1, M1_SC_Q8, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_sel_max", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z14, &ch).mul(l_r).mul(m_ev.sub(sc_ev))),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 14. `ss_gqa_psm_div`: `Z_SM[ti, hq, q] * P_SM[tj, ti, hq, q] == 4096 * E_SM - REM_PSM`
    {
        let z14 = tr.squeeze_ext4_vec(b"psmd_z", 14, true);
        let _ = push_eval(1, M1_E_SM, z14.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_PSM, z14.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let z_lift: Vec<Ext4> = (0..(1 << 14))
            .map(|idx| Ext4::from_bb(m1[M1_Z_SM][idx >> 4]))
            .collect();
        let p_ext: Vec<Ext4> = m1[M1_P_SM].iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &z_lift, &p_ext, 14, 0, &z14, &gmask, "ss_gqa_psm_div", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_Z_SM, ch[4..].to_vec(), l_r));
        let p_ev = push_eval(1, M1_P_SM, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_psm_div", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z14, &ch).mul(l_r).mul(p_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 15. `ss_gqa_pv`: `P_SM[tj, ti, hq, q] @ V_PROJ[dh, hq>>2, tj, q] == 4096 * AO_H + REM_AOH - 2048 * act_gqa`
    {
        let z_dh = tr.squeeze_ext4_vec(b"pv_zdh", 8, true);
        let z_hq = tr.squeeze_ext4_vec(b"pv_zhq", 3, true);
        let z_ti = tr.squeeze_ext4_vec(b"pv_zti", 4, true);
        let z_q = tr.squeeze_ext4_vec(b"pv_zq", 3, true);
        let pt18 = concat_pts(&[&z_dh, &z_hq, &z_ti, &z_q]);
        let _ = push_eval(1, M1_AO_H, pt18.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_AOH, pt18, &mut tr, &mut linear_point_evals, &mut online_claims);

        let eq_ti = build_eq_table_lsb_ext4(&z_ti);
        let eq_dh = build_eq_table_lsb_ext4(&z_dh);
        let mut p_fold = vec![Ext4::ZERO; 64 * 16];
        let mut v_fold = vec![Ext4::ZERO; 64 * 16];
        for q in 0..8 {
            for hq in 0..8 {
                let hk = hq >> 2;
                let hqq = hq + (q << 3);
                for tj in 0..16 {
                    let mut sp = Ext4::ZERO;
                    for ti in 0..16 {
                        sp = sp.add(eq_ti[ti].scale_bb(m1[M1_P_SM][tj + (ti << 4) + (hq << 8) + (q << 11)]));
                    }
                    p_fold[hqq + (tj << 6)] = sp;
                    let mut sv = Ext4::ZERO;
                    let v_base = (hk << 8) + (tj << 9) + (q << 13);
                    for dh in 0..256 {
                        sv = sv.add(eq_dh[dh].scale_bb(m1[M1_V_PROJ][v_base + dh]));
                    }
                    v_fold[hqq + (tj << 6)] = sv;
                }
            }
        }
        let z6 = concat_pts(&[&z_hq, &z_q]);
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &p_fold, &v_fold, 6, 4, &z6, &gmask, "ss_gqa_pv", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        let (r_hq, r_q, r_tj) = (&ch[..3], &ch[3..6], &ch[6..10]);
        online_claims[1].push(JointLinearClaimExt4::point_eval(
            M1_P_SM,
            concat_pts(&[r_tj, &z_ti, r_hq, r_q]),
            l_r,
        ));
        let v_ev = push_eval(
            1,
            M1_V_PROJ,
            concat_pts(&[&z_dh, &[r_hq[2]], r_tj, r_q]),
            &mut tr,
            &mut linear_point_evals,
            &mut online_claims,
        );
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_pv", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z6, &ch[..6]).mul(l_r).mul(v_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 16. `ss_gqa_aog`: `AO_H * SIG_GATE == 1024 * AO_G + REM_AOG - 512 * act_gqa`
    {
        let z18 = tr.squeeze_ext4_vec(b"aog_z", 18, true);
        let _ = push_eval(1, M1_AO_G, z18.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(1, M1_REM_AOG, z18.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let aoh_ext: Vec<Ext4> = m1[M1_AO_H].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let sg_ext: Vec<Ext4> = m1[M1_SIG_GATE].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &aoh_ext, &sg_ext, 18, 0, &z18, &gmask, "ss_gqa_aog", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_AO_H, ch.clone(), l_r));
        let sg_ev = push_eval(1, M1_SIG_GATE, ch.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_aog", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z18, &ch).mul(l_r).mul(sg_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 17. `ss_mlp_swiglu`: `GATE_SILU * MLP_UP == 512 * SWIGLU + REM_SWIGLU - 256 * act_mlp`
    {
        let z21 = tr.squeeze_ext4_vec(b"swg_z", 21, true);
        let _ = push_eval(2, M2_SWIGLU, z21.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(2, M2_REM_SWIGLU, z21.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let gs_ext: Vec<Ext4> = m2[M2_GATE_SILU].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let up_ext: Vec<Ext4> = m2[M2_MLP_UP].par_iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf, rho, ch, l_r, _r_r, term) = prove_gmask_einsum_par_ext4(
            &gs_ext, &up_ext, 21, 0, &z21, &gmask, "ss_mlp_swiglu", &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_r);
        online_claims[2].push(JointLinearClaimExt4::point_eval(M2_GATE_SILU, ch.clone(), l_r));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_mlp_swiglu", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: M2_MLP_UP,
                point: ch.clone(),
                weight: eq_mle_ext4(&z21, &ch).mul(l_r),
            }],
            gm_limb_ids,
            &w_at,
            rho,
            term,
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf, left_at_r: l_r });
    }

    // 18..29: `RMSNorm` `4` bilinear checks × `3` groups (`sq`, `p4u`, `p2r`, `xrho`):
    let build_rms_xin_vec = |g_idx: usize| -> Vec<Ext4> {
        match g_idx {
            0 => {
                let mut v = vec![Ext4::ZERO; 1 << 20];
                for slot in 0..32 {
                    for td in 0..(1 << 14) {
                        v[td + (slot << 14)] = Ext4::from_bb(m2[M2_H_IN][td + (slot << 14)]);
                    }
                }
                for l in 0..32 {
                    for td in 0..(1 << 14) {
                        v[td + ((32 + l) << 14)] = Ext4::from_bb(m2[M2_H_MID][td + (l << 14)]);
                    }
                }
                v
            }
            1 => {
                let mut v = vec![Ext4::ZERO; 1 << 21];
                for g in 0..18 {
                    for t in 0..16 {
                        for dh in 0..2048 {
                            let c0 = m0[M0_CONV_SILU][dh + (t << 13) + (g << 17)];
                            let c1 = m0[M0_CONV_SILU][dh + 2048 + (t << 13) + (g << 17)];
                            let yw = m0[M0_Y_WY][dh + (t << 11) + (g << 15)];
                            v[dh + (t << 11) + ((3 * g) << 15)] = Ext4::from_bb(bmul(2, c0));
                            v[dh + (t << 11) + ((3 * g + 1) << 15)] = Ext4::from_bb(bmul(2, c1));
                            v[dh + (t << 11) + ((3 * g + 2) << 15)] = Ext4::from_bb(yw);
                        }
                    }
                }
                v
            }
            _ => {
                let mut v = vec![Ext4::ZERO; 1 << 19];
                for q in 0..8 {
                    for t in 0..16 {
                        for hq in 0..8 {
                            for d in 0..256 {
                                let qr = m1[M1_Q_RAW][d + (hq << 8) + (t << 11) + (q << 15)];
                                v[d + (hq << 8) + (t << 12) + (q << 16)] = Ext4::from_bb(bmul(2, qr));
                            }
                        }
                        for hk in 0..2 {
                            for d in 0..256 {
                                let kr = m1[M1_K_RAW][d + (hk << 8) + (t << 9) + (q << 13)];
                                v[d + ((8 + hk) << 8) + (t << 12) + (q << 16)] = Ext4::from_bb(bmul(2, kr));
                            }
                        }
                    }
                }
                v
            }
        }
    };

    let discharge_rms_xin = |g_idx: usize, pt: &[Ext4], expected_val: Ext4, onl_cl: &mut [Vec<JointLinearClaimExt4>; 4]| {
        match g_idx {
            0 => {
                let s5 = pt[19];
                let pt19 = pt[..19].to_vec();
                onl_cl[2].push(JointLinearClaimExt4 {
                    terms: vec![
                        LinearTermExt4::PointEval { subtable: M2_H_IN, point: pt19.clone(), weight: Ext4::ONE.sub(s5) },
                        LinearTermExt4::PointEval { subtable: M2_H_MID, point: pt19, weight: s5 },
                    ],
                    rhs: expected_val,
                });
            }
            1 => {
                let eq_gk = build_eq_table_lsb_ext4(&pt[15..21]);
                let mut terms = Vec::with_capacity(54);
                let two = Ext4::from_bb(2);
                for g in 0..18 {
                    let g_bits = bits_to_ext4(g, 5);
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_CONV_SILU,
                        point: concat_pts(&[&pt[..11], &[Ext4::ZERO, Ext4::ZERO], &pt[11..15], &g_bits]),
                        weight: two.mul(eq_gk[3 * g]),
                    });
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_CONV_SILU,
                        point: concat_pts(&[&pt[..11], &[Ext4::ONE, Ext4::ZERO], &pt[11..15], &g_bits]),
                        weight: two.mul(eq_gk[3 * g + 1]),
                    });
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_Y_WY,
                        point: concat_pts(&[&pt[..15], &g_bits]),
                        weight: eq_gk[3 * g + 2],
                    });
                }
                onl_cl[0].push(JointLinearClaimExt4 { terms, rhs: expected_val });
            }
            _ => {
                let two = Ext4::from_bb(2);
                let (h1, h2, h3) = (pt[9], pt[10], pt[11]);
                let w_q = two.mul(Ext4::ONE.sub(h3));
                let w_k = two.mul(h3).mul(Ext4::ONE.sub(h2)).mul(Ext4::ONE.sub(h1));
                onl_cl[1].push(JointLinearClaimExt4 {
                    terms: vec![
                        LinearTermExt4::PointEval {
                            subtable: M1_Q_RAW,
                            point: concat_pts(&[&pt[..11], &pt[12..19]]),
                            weight: w_q,
                        },
                        LinearTermExt4::PointEval {
                            subtable: M1_K_RAW,
                            point: concat_pts(&[&pt[..9], &pt[12..19]]),
                            weight: w_k,
                        },
                    ],
                    rhs: expected_val,
                });
            }
        }
    };

    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let b = cfg.grp * RGRP_STRIDE;
        let mf = cfg.log_d + cfg.m_row;
        let mr = cfg.m_row;
        let specs = [
            ["ss_rms0_sq", "ss_rms0_p4u", "ss_rms0_p2r", "ss_rms0_xrho"],
            ["ss_rms1_sq", "ss_rms1_p4u", "ss_rms1_p2r", "ss_rms1_xrho"],
            ["ss_rms2_sq", "ss_rms2_p4u", "ss_rms2_p2r", "ss_rms2_xrho"],
        ][g_idx];
        let xin_vec = build_rms_xin_vec(g_idx);

        // (a) `sq`: `X_IN * X_IN == 16 * (SQLO + 8192 * SQHI) + RSQ`
        let z_sq = tr.squeeze_ext4_vec(b"rmssq_z", mf, true);
        let _ = push_eval(3, b + RGRP_SQLO, z_sq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_SQHI, z_sq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_RSQ, z_sq.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (prf_sq, rho_sq, ch_sq, l_sq, _, term_sq) = prove_gmask_einsum_par_ext4(
            &xin_vec, &xin_vec, mf, 0, &z_sq, &gmask, specs[0], &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_sq);
        discharge_rms_xin(g_idx, &ch_sq, l_sq, &mut online_claims);
        let (ws0, wa0) = GMaskExt4::build_spec_weights(&gm_specs, specs[0], &ch_sq);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws0, prf_sq.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &wa0, rho_sq, term_sq.sub(eq_mle_ext4(&z_sq, &ch_sq).mul(l_sq).mul(l_sq)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf: prf_sq, left_at_r: l_sq });

        // (b) `p4u`: `POW4 * UMS == MS_LO + 8192 * MS_HI - RNORM`
        let z_p4 = tr.squeeze_ext4_vec(b"rmsp4_z", mr, true);
        let _ = push_eval(3, b + RGRP_MS_LO, z_p4.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_MS_HI, z_p4.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_RNORM, z_p4.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let p4_ext: Vec<Ext4> = m3[b + RGRP_POW4].iter().map(|&v| Ext4::from_bb(v)).collect();
        let um_ext: Vec<Ext4> = m3[b + RGRP_UMS].iter().map(|&v| Ext4::from_bb(v)).collect();
        let (prf_p4, rho_p4, ch_p4, l_p4, _, term_p4) = prove_gmask_einsum_par_ext4(
            &p4_ext, &um_ext, mr, 0, &z_p4, &gmask, specs[1], &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_p4);
        online_claims[3].push(JointLinearClaimExt4::point_eval(b + RGRP_POW4, ch_p4.clone(), l_p4));
        let um_ev = push_eval(3, b + RGRP_UMS, ch_p4.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let (ws1, wa1) = GMaskExt4::build_spec_weights(&gm_specs, specs[1], &ch_p4);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws1, prf_p4.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &wa1, rho_p4, term_p4.sub(eq_mle_ext4(&z_p4, &ch_p4).mul(l_p4).mul(um_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf: prf_p4, left_at_r: l_p4 });

        // (c) `p2r`: `POW2 * (RHO_LO + 4096 * RHO_HI) == RMLUT + HPOW2 - RRHO`
        let z_p2 = tr.squeeze_ext4_vec(b"rmsp2_z", mr, true);
        let _ = push_eval(3, b + RGRP_RMLUT, z_p2.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_HPOW2, z_p2.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_RRHO, z_p2.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let p2_ext: Vec<Ext4> = m3[b + RGRP_POW2].iter().map(|&v| Ext4::from_bb(v)).collect();
        let rho_row_ext: Vec<Ext4> = (0..(1usize << mr))
            .map(|r| Ext4::from_bb(m3[b + RGRP_RHO_LO][r] + 4096 * m3[b + RGRP_RHO_HI][r]))
            .collect();
        let (prf_p2, rho_p2, ch_p2, l_p2, _, term_p2) = prove_gmask_einsum_par_ext4(
            &p2_ext, &rho_row_ext, mr, 0, &z_p2, &gmask, specs[2], &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_p2);
        online_claims[3].push(JointLinearClaimExt4::point_eval(b + RGRP_POW2, ch_p2.clone(), l_p2));
        let rlo_ev = push_eval(3, b + RGRP_RHO_LO, ch_p2.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let rhi_ev = push_eval(3, b + RGRP_RHO_HI, ch_p2.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let rho_ev = rlo_ev.add(rhi_ev.scale_bb(4096));
        let (ws2, wa2) = GMaskExt4::build_spec_weights(&gm_specs, specs[2], &ch_p2);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws2, prf_p2.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &wa2, rho_p2, term_p2.sub(eq_mle_ext4(&z_p2, &ch_p2).mul(l_p2).mul(rho_ev)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf: prf_p2, left_at_r: l_p2 });

        // (d) `xrho`: `X_IN * RHO == 2048 * UQ9 + RU - 1024 * act_row`
        let z_xr = tr.squeeze_ext4_vec(b"rmsxr_z", mf, true);
        let _ = push_eval(3, b + RGRP_UQ9, z_xr.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(3, b + RGRP_RU, z_xr.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let rho_full_ext: Vec<Ext4> = (0..(1usize << mf))
            .into_par_iter()
            .map(|idx| rho_row_ext[idx >> cfg.log_d])
            .collect();
        let (prf_xr, rho_xr, ch_xr, l_xr, _, term_xr) = prove_gmask_einsum_par_ext4(
            &xin_vec, &rho_full_ext, mf, 0, &z_xr, &gmask, specs[3], &mut tr,
        );
        tr.absorb_ext4(b"ss_lr", l_xr);
        discharge_rms_xin(g_idx, &ch_xr, l_xr, &mut online_claims);
        let r_row_pt = ch_xr[cfg.log_d..].to_vec();
        let rlo2 = push_eval(3, b + RGRP_RHO_LO, r_row_pt.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let rhi2 = push_eval(3, b + RGRP_RHO_HI, r_row_pt, &mut tr, &mut linear_point_evals, &mut online_claims);
        let rho_ev2 = rlo2.add(rhi2.scale_bb(4096));
        let (ws3, wa3) = GMaskExt4::build_spec_weights(&gm_specs, specs[3], &ch_xr);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws3, prf_xr.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &wa3, rho_xr, term_xr.sub(eq_mle_ext4(&z_xr, &ch_xr).mul(l_xr).mul(rho_ev2)),
        ));
        sec_sec_proofs.push(SecSecEinSumOpening { prf: prf_xr, left_at_r: l_xr });
    }

    // Step E: Direct Zero-Round Linear Welds (`embed_tokens`, padding guards, `ST_H_IN == ST_H_CARRY` cross-layer weld,
    // `h_mid`, `h_out`, RMSNorm block/mean-sq/`DIFF_RHO`, GDN `SP_IN`/`GAMMA` diag, GQA softmax row sums):
    // E1. `embed_tokens` <-> `M2_H_CARRY[b=0]`:
    {
        let z_dt = tr.squeeze_ext4_vec(b"emb_zdt", 14, true);
        let h0_ev = push_eval(
            2,
            M2_H_CARRY,
            concat_pts(&[&z_dt, &bits_to_ext4(0, 5)]),
            &mut tr,
            &mut linear_point_evals,
            &mut online_claims,
        );
        let eq_t = build_eq_table_lsb_ext4(&z_dt[10..14]);
        let scale_emb_bb = Ext4::from_bb((S_RES / S_W) as u32);
        let mut emb_terms = Vec::with_capacity(16);
        for (t, &tid) in prompt_tokens.iter().enumerate() {
            emb_terms.push((
                WST_EMBED,
                concat_pts(&[&z_dt[..10], &bits_to_ext4(tid as usize, 18)]),
                scale_emb_bb.mul(eq_t[t]),
            ));
        }
        weight_claims.push(PublicWeightClaim24L {
            terms: emb_terms,
            rhs: h0_ev,
        });
    }

    // E2. Padding-zero guards on `M2_H_IN[25..32]`, `M2_H_CARRY[25..32]`, `M2_H_MID[24..32]`:
    {
        let z_pad = tr.squeeze_ext4_vec(b"pad_zdt", 14, true);
        let g_pad = tr.squeeze_ext4(b"pad_gam", true);
        let mut terms_pad = Vec::with_capacity(22);
        let mut gp = Ext4::ONE;
        for b_idx in 25..32 {
            let pt = concat_pts(&[&z_pad, &bits_to_ext4(b_idx, 5)]);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_IN, point: pt.clone(), weight: gp });
            gp = gp.mul(g_pad);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_CARRY, point: pt, weight: gp });
            gp = gp.mul(g_pad);
        }
        for l_idx in 24..32 {
            let pt = concat_pts(&[&z_pad, &bits_to_ext4(l_idx, 5)]);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_MID, point: pt, weight: gp });
            gp = gp.mul(g_pad);
        }
        online_claims[2].push(JointLinearClaimExt4 { terms: terms_pad, rhs: Ext4::ZERO });
    }

    // E3. Zero-Gap Cross-Layer Residual Continuity Weld (`M2_H_IN(z_weld) - M2_H_CARRY(z_weld) == 0`):
    {
        let z_weld = tr.squeeze_ext4_vec(b"xlayer_zweld", 19, true);
        online_claims[2].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M2_H_IN, point: z_weld.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M2_H_CARRY, point: z_weld, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ZERO,
        });
    }

    // E4. Residual Add 1 (`H_MID == H_IN_24 + GDN_ATTN_OUT + GQA_ATTN_OUT` across all 24 layers):
    {
        let z_r1 = tr.squeeze_ext4_vec(b"res1_z", 19, true);
        let _ = push_eval(2, M2_H_MID, z_r1.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let eq_zl = build_eq_table_lsb_ext4(&z_r1[14..19]);

        let mut hin_val = Ext4::ZERO;
        let mut hin_terms = Vec::with_capacity(24);
        for l in 0..24 {
            let pt = concat_pts(&[&z_r1[..14], &bits_to_ext4(l, 5)]);
            hin_val = hin_val.add(eq_zl[l].mul(mle_eval_bb_at_ext4(&m2[M2_H_IN], &pt)));
            hin_terms.push(LinearTermExt4::PointEval { subtable: M2_H_IN, point: pt, weight: eq_zl[l] });
        }
        tr.absorb_ext4(b"res1_hin", hin_val);
        linear_point_evals.push(hin_val);
        online_claims[2].push(JointLinearClaimExt4 { terms: hin_terms, rhs: hin_val });

        let mut gdn_val = Ext4::ZERO;
        let mut gdn_terms = Vec::with_capacity(18);
        for (g, &l) in GDN_LAYER_INDICES.iter().enumerate() {
            let pt = concat_pts(&[&z_r1[..14], &bits_to_ext4(g, 5)]);
            gdn_val = gdn_val.add(eq_zl[l].mul(mle_eval_bb_at_ext4(&m0[M0_ATTN_OUT], &pt)));
            gdn_terms.push(LinearTermExt4::PointEval { subtable: M0_ATTN_OUT, point: pt, weight: eq_zl[l] });
        }
        tr.absorb_ext4(b"res1_gdn", gdn_val);
        linear_point_evals.push(gdn_val);
        online_claims[0].push(JointLinearClaimExt4 { terms: gdn_terms, rhs: gdn_val });

        let mut gqa_val = Ext4::ZERO;
        let mut gqa_terms = Vec::with_capacity(6);
        for (q, &l) in GQA_LAYER_INDICES.iter().enumerate() {
            let pt = concat_pts(&[&z_r1[..14], &bits_to_ext4(q, 3)]);
            gqa_val = gqa_val.add(eq_zl[l].mul(mle_eval_bb_at_ext4(&m1[M1_ATTN_OUT], &pt)));
            gqa_terms.push(LinearTermExt4::PointEval { subtable: M1_ATTN_OUT, point: pt, weight: eq_zl[l] });
        }
        tr.absorb_ext4(b"res1_gqa", gqa_val);
        linear_point_evals.push(gqa_val);
        online_claims[1].push(JointLinearClaimExt4 { terms: gqa_terms, rhs: gqa_val });
    }

    // E5. Residual Add 2 (`ST_H_CARRY[l + 1] == H_MID[l] + MLP_OUT[l]` across all 24 layers):
    {
        let z_r2 = tr.squeeze_ext4_vec(b"res2_z", 19, true);
        let eq_zl = build_eq_table_lsb_ext4(&z_r2[14..19]);
        let mut terms_r2 = Vec::with_capacity(26);
        for l in 0..24 {
            terms_r2.push(LinearTermExt4::PointEval {
                subtable: M2_H_CARRY,
                point: concat_pts(&[&z_r2[..14], &bits_to_ext4(l + 1, 5)]),
                weight: eq_zl[l],
            });
        }
        terms_r2.push(LinearTermExt4::PointEval { subtable: M2_H_MID, point: z_r2.clone(), weight: Ext4::ONE.neg() });
        terms_r2.push(LinearTermExt4::PointEval { subtable: M2_MLP_OUT, point: z_r2, weight: Ext4::ONE.neg() });
        online_claims[2].push(JointLinearClaimExt4 { terms: terms_r2, rhs: Ext4::ZERO });
    }

    // E6. RMSNorm Block-16 Sum, Row Mean-Square, & `DIFF_RHO` for all 3 groups:
    let half_ext = Ext4::from_bb(INV2_BB);
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let b = cfg.grp * RGRP_STRIDE;
        let mb = cfg.log_d - 4 + cfg.m_row;
        let mr = cfg.m_row;
        let n_blk = 1u32 << (cfg.log_d - 4);
        let div_ms = (1u32 << cfg.log_d) / 32;

        let z_kr = tr.squeeze_ext4_vec(b"rmsb_z", mb, true);
        let z_sq_half = concat_pts(&[&[half_ext; 4], &z_kr]);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_SQLO, point: z_sq_half.clone(), weight: Ext4::from_bb(16) },
                LinearTermExt4::PointEval { subtable: b + RGRP_SQHI, point: z_sq_half, weight: Ext4::from_bb(16 * 8192) },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_LO, point: z_kr.clone(), weight: Ext4::from_bb(32).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_HI, point: z_kr.clone(), weight: Ext4::from_bb(32 * 8192).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_RB128, point: z_kr, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ZERO,
        });

        let z_ms = tr.squeeze_ext4_vec(b"rmsms_z", mr, true);
        let halfs_k = vec![half_ext; cfg.log_d - 4];
        let z_b_half = concat_pts(&[&halfs_k, &z_ms]);
        let act_r = eval_rms_group_act_mle(g_idx, &z_ms);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_LO, point: z_b_half.clone(), weight: Ext4::from_bb(n_blk) },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_HI, point: z_b_half, weight: Ext4::from_bb(n_blk * 8192) },
                LinearTermExt4::PointEval { subtable: b + RGRP_MS_LO, point: z_ms.clone(), weight: Ext4::from_bb(div_ms).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_MS_HI, point: z_ms.clone(), weight: Ext4::from_bb(div_ms * 8192).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_RMS, point: z_ms, weight: Ext4::ONE.neg() },
            ],
            rhs: act_r.scale_bb(div_ms).neg(),
        });

        let z_dr = tr.squeeze_ext4_vec(b"rmsdr_z", mr, true);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_POW2, point: z_dr.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: b + RGRP_RRHO, point: z_dr.clone(), weight: Ext4::ONE.neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_DIFF_RHO, point: z_dr, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ONE,
        });
    }

    // E7. GDN `SP_IN == A_PROJ + act_gdn * DT_BIAS` & `GAMMA[h, j, j, g] == 512 * act_gdn(g)`:
    {
        let z13 = tr.squeeze_ext4_vec(b"spin_z", 13, true);
        let _ = push_eval(0, M0_SP_IN, z13.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let _ = push_eval(0, M0_A_PROJ, z13.clone(), &mut tr, &mut linear_point_evals, &mut online_claims);
        let dt_pt = concat_pts(&[&z13[..4], &z13[8..13]]);
        let dt_ev = weights.eval_subtable_point(WST_GDN_DT, &dt_pt);
        tr.absorb_ext4(b"spin_dt", dt_ev);
        linear_point_evals.push(dt_ev);
        weight_claims.push(PublicWeightClaim24L::point_eval(WST_GDN_DT, dt_pt, dt_ev));

        let z_gd = tr.squeeze_ext4_vec(b"gmd_z", 13, true);
        let (zh, zj, zg) = (&z_gd[..4], &z_gd[4..8], &z_gd[8..13]);
        let eq_zj = build_eq_table_lsb_ext4(zj);
        let mut d_terms = Vec::with_capacity(16);
        for j in 0..16 {
            let jb = bits_to_ext4(j, 4);
            d_terms.push(LinearTermExt4::PointEval {
                subtable: M0_GAMMA,
                point: concat_pts(&[zh, &jb, &jb, zg]),
                weight: eq_zj[j],
            });
        }
        online_claims[0].push(JointLinearClaimExt4 {
            terms: d_terms,
            rhs: eval_lt_const_mle(zg, NUM_GDN_LAYERS).scale_bb(512),
        });
    }

    // E8. GQA Softmax Row Sums (`16 * SEL_MAX(half^4, z10) == act_gqa` & `16 * E_SM(half^4, z10) - Z_SM(z10) == 0`):
    {
        let z10 = tr.squeeze_ext4_vec(b"smrow_z", 10, true);
        let z14_half = concat_pts(&[&[half_ext; 4], &z10]);
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::PointEval {
                subtable: M1_SEL_MAX,
                point: z14_half.clone(),
                weight: Ext4::from_bb(16),
            }],
            rhs: eval_lt_const_mle(&z10[7..10], NUM_GQA_LAYERS),
        });
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: M1_E_SM,
                    point: z14_half,
                    weight: Ext4::from_bb(16),
                },
                LinearTermExt4::PointEval {
                    subtable: M1_Z_SM,
                    point: z10.clone(),
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: Ext4::ZERO,
        });
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval {
                    subtable: M1_Z_SM,
                    point: z10.clone(),
                    weight: Ext4::ONE,
                },
                LinearTermExt4::PointEval {
                    subtable: M1_Z_SM_M1,
                    point: z10.clone(),
                    weight: Ext4::ONE.neg(),
                },
            ],
            rhs: eval_lt_const_mle(&z10[7..10], NUM_GQA_LAYERS),
        });
    }

    // Step F: Open `WeightModelRoot24L` (`PublicWeightOpeningProof24L`) + 4-Matrix Online ZK WHIR Batch!
    let weight_whir_proof = open_public_weight_whir_24l(weights, &weight_claims, &mut tr);
    let online_whir_proof = open_whir_batch_ext4(
        &[
            (&mat0, &online_claims[0]),
            (&mat1, &online_claims[1]),
            (&mat2, &online_claims[2]),
            (&mat3, &online_claims[3]),
        ],
        ONLINE_WHIR_T_QUERIES,
        &mut tr,
    );

    let _ = wit.logits_i32;
    Ok(Full24LayerQwen35Receipt {
        model_root: weights.model_root,
        prompt_tokens: *prompt_tokens,
        emitted_next_token_id: wit.emitted_token_id,
        claimed_max_logit: wit.claimed_max_logit,
        online_roots,
        range_d1b_proofs: final_range_proofs,
        lut_d1b_proofs: [prf_silu, prf_sig, prf_sp, prf_en, prf_rsq],
        weight_matmul_proofs,
        pub_ind_proofs,
        sec_sec_proofs,
        linear_point_evals,
        weight_whir_proof,
        online_whir_proof,
    })
}

fn eval_rms_group_act_mle(g_idx: usize, z_row: &[Ext4]) -> Ext4 {
    match g_idx {
        0 => {
            // `z_row` = `[z_t (4), z_slot (6)]`: `slot in 0..25` (`bit 5 == 0`) or `slot in 32..56` (`bit 5 == 1, slot[0..5] < 24`)!
            let s5 = z_row[9];
            let s_lo = &z_row[4..9];
            Ext4::ONE
                .sub(s5)
                .mul(eval_lt_const_mle(s_lo, 25))
                .add(s5.mul(eval_lt_const_mle(s_lo, 24)))
        }
        1 => eval_lt_const_mle(&z_row[8..14], 54),
        _ => eval_lt_const_mle(&z_row[..4], 10).mul(eval_lt_const_mle(&z_row[8..11], 6)),
    }
}

#[inline]
fn ext4_is_canonical(x: Ext4) -> bool {
    x.0[0] < P_U32 && x.0[1] < P_U32 && x.0[2] < P_U32 && x.0[3] < P_U32
}

fn d1b_proof_is_canonical(p: &D1bRangeExt4Proof) -> bool {
    ext4_is_canonical(p.root_q)
        && ext4_is_canonical(p.rem_leaf_eval)
        && ext4_is_canonical(p.mult_leaf_eval)
        && p.layers.iter().all(|l| {
            ext4_is_canonical(l.p_lo)
                && ext4_is_canonical(l.p_hi)
                && ext4_is_canonical(l.q_lo)
                && ext4_is_canonical(l.q_hi)
                && l.rounds.iter().all(|m| {
                    ext4_is_canonical(m.p0)
                        && ext4_is_canonical(m.p1)
                        && ext4_is_canonical(m.p2)
                        && ext4_is_canonical(m.p_inf)
                })
        })
}

fn blinded_einsum_is_canonical(p: &BlindedEinSumExt4Proof) -> bool {
    ext4_is_canonical(p.gmask_sum)
        && p.rounds
            .iter()
            .all(|r| r.iter().copied().all(ext4_is_canonical))
}

fn cascade_levels_canonical(levels: &[WhirCascadeLevelProofExt4]) -> bool {
    levels.iter().all(|cl| {
        cl.ood_evals.iter().copied().all(ext4_is_canonical)
            && cl
                .lockstep_sc
                .iter()
                .all(|r| r.iter().copied().all(ext4_is_canonical))
            && cl.opened_fibers.iter().copied().all(ext4_is_canonical)
    })
}

fn validate_receipt_canonical_invariants(receipt: &Full24LayerQwen35Receipt) -> Result<(), String> {
    if !receipt.range_d1b_proofs.iter().all(d1b_proof_is_canonical)
        || !receipt.lut_d1b_proofs.iter().all(d1b_proof_is_canonical)
    {
        return Err("non-canonical Ext4 limb in D1b proof".into());
    }
    if !receipt
        .weight_matmul_proofs
        .iter()
        .all(|w| blinded_einsum_is_canonical(&w.prf) && ext4_is_canonical(w.weight_at_r))
        || !receipt.pub_ind_proofs.iter().all(blinded_einsum_is_canonical)
        || !receipt
            .sec_sec_proofs
            .iter()
            .all(|s| blinded_einsum_is_canonical(&s.prf) && ext4_is_canonical(s.left_at_r))
        || !receipt.linear_point_evals.iter().copied().all(ext4_is_canonical)
    {
        return Err("non-canonical Ext4 limb in sumcheck / linear evals".into());
    }
    let wp = &receipt.weight_whir_proof;
    if !ext4_is_canonical(wp.u_eval_at_zeta)
        || !ext4_is_canonical(wp.u_prox_at_zeta)
        || !wp
            .row_sc_rounds
            .iter()
            .chain(wp.col_sc_rounds.iter())
            .all(|r| r.iter().copied().all(ext4_is_canonical))
        || !cascade_levels_canonical(&wp.cascade_levels)
        || !wp.final_ood_evals.iter().copied().all(ext4_is_canonical)
        || !wp.final_poly.iter().copied().all(ext4_is_canonical)
    {
        return Err("non-canonical Ext4 limb in PublicWeightOpeningProof24L".into());
    }
    let op = &receipt.online_whir_proof;
    if op.final_lockstep_sc != vec![[Ext4::ZERO; 3]] {
        return Err("non-zero reserved final_lockstep_sc in online WhirBatchOpeningProofExt4".into());
    }
    if !op.matrix_parts.iter().all(|mp| {
        mp.zk
            && ext4_is_canonical(mp.gmask_sum)
            && mp.z_gm_masks.iter().copied().all(ext4_is_canonical)
            && mp
                .row_sc_rounds
                .iter()
                .all(|r| r.iter().copied().all(ext4_is_canonical))
            && ext4_is_canonical(mp.m_eval)
            && ext4_is_canonical(mp.u_eval_at_zeta)
            && ext4_is_canonical(mp.p_gm_hat_at_zeta)
            && ext4_is_canonical(mp.u_prox_at_zeta)
            && mp.s0_col_vals.iter().all(|&x| x < P_U32)
    }) || !op
        .shared_coeff_rounds
        .iter()
        .all(|r| r.iter().copied().all(ext4_is_canonical))
        || !cascade_levels_canonical(&op.cascade_levels)
        || !op.final_ood_evals.iter().copied().all(ext4_is_canonical)
        || !op.final_poly.iter().copied().all(ext4_is_canonical)
    {
        return Err("non-canonical limb in online WhirBatchOpeningProofExt4".into());
    }
    Ok(())
}

/// Standalone Fail-Closed Verifier for `Full24LayerQwen35Receipt` (`0` witness access, `< 150 ms` target!).
pub fn verify_full_24l_qwen35_receipt(
    expected_model_root: &WeightModelRoot24L,
    expected_prompt_tokens: &[u32; FULL_24L_SEQ_LEN],
    receipt: &Full24LayerQwen35Receipt,
) -> Result<(), String> {
    if &receipt.model_root != expected_model_root {
        return Err("WeightModelRoot24L mismatch".into());
    }
    if &receipt.prompt_tokens != expected_prompt_tokens {
        return Err("prompt_tokens mismatch".into());
    }
    if receipt.model_root.max_row_l1 > MAX_ALLOWED_ROW_L1
        || receipt.model_root.max_conv_l1 > MAX_ALLOWED_CONV_L1
        || receipt.model_root.max_gain_abs > MAX_ALLOWED_GAIN_ABS
        || receipt.model_root.max_gdn_qk_gain > MAX_ALLOWED_GDN_QK_GAIN
        || receipt.model_root.max_scalar_abs > MAX_ALLOWED_SCALAR_ABS
    {
        return Err("WeightModelRoot24L L1 wrap-freedom bounds exceeded".into());
    }
    validate_receipt_canonical_invariants(receipt)?;
    for &tid in expected_prompt_tokens {
        if (tid as usize) >= QWEN_DEFINED_TOKENS {
            return Err("prompt token ID out of QwenBpeRom defined range".into());
        }
    }
    if (receipt.emitted_next_token_id as usize) >= VOCAB_SIZE {
        return Err("emitted_next_token_id out of vocab_size".into());
    }
    if !(-30_000..30_000).contains(&receipt.claimed_max_logit) {
        return Err("claimed_max_logit out of [-30000, 30000)".into());
    }

    let luts = public_luts_24l();
    let range_plans = canonical_range_bucket_plans();
    if receipt.range_d1b_proofs.len() != range_plans.len() {
        return Err("range_d1b_proofs count mismatch".into());
    }
    let shapes = online_shapes_24l(range_plans.len());
    let pub_w_shape = PublicWeightWhirShape24L::canonical_24l();
    let gm_specs = all_gmask_specs_24l();
    let gm_limb_ids = [M2D_GM_LIMB0, M2D_GM_LIMB1, M2D_GM_LIMB2, M2D_GM_LIMB3];

    if receipt.weight_matmul_proofs.len() != 19
        || receipt.pub_ind_proofs.len() != 16
        || receipt.sec_sec_proofs.len() != 29
    {
        return Err("subproof vector count mismatch".into());
    }

    let mut tr = CShakeTranscript::new(b"QW35-FULL24L-AUDIT-V1");
    receipt.model_root.absorb_into(&mut tr);
    for (i, &t) in receipt.prompt_tokens.iter().enumerate() {
        tr.absorb_u32(b"tok_in", (i as u32) ^ (t << 5));
        tr.absorb_u32(b"tok_id", t);
    }
    tr.absorb_u32(b"tok_out", receipt.emitted_next_token_id);
    tr.absorb_u32(b"max_logit", receipt.claimed_max_logit as u32);
    for (m_idx, r) in receipt.online_roots.iter().enumerate() {
        tr.absorb_u32(b"onl_idx", m_idx as u32);
        tr.absorb_root(b"onl_root", r);
    }

    let mut online_claims: [Vec<JointLinearClaimExt4>; 4] =
        [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
    let mut weight_claims: Vec<PublicWeightClaim24L> = Vec::new();
    let mut ev_cursor = 0usize;
    let next_raw_ev = |cur: &mut usize| -> Result<Ext4, String> {
        if *cur >= receipt.linear_point_evals.len() {
            return Err("linear_point_evals underflow".into());
        }
        let v = receipt.linear_point_evals[*cur];
        *cur += 1;
        Ok(v)
    };

    // Step A: Verify all virtual `D1b` range proofs:
    let mut range_z_leaves = Vec::with_capacity(range_plans.len());
    for (b_idx, (pl, prf)) in range_plans
        .iter()
        .zip(receipt.range_d1b_proofs.iter())
        .enumerate()
    {
        if prf.m_wit != pl.m_wit || prf.m_tab != pl.m_tab {
            return Err("range D1b dimension mismatch".into());
        }
        let z_leaf = verify_d1b_range_ext4(prf, &mut tr)?;
        online_claims[2].push(JointLinearClaimExt4::point_eval(
            M2D_RANGE_MULT_BASE + b_idx,
            z_leaf[..pl.m_tab].to_vec(),
            prf.mult_leaf_eval,
        ));
        range_z_leaves.push(z_leaf);
    }

    // Step B: Validate expected `(m_wit, m_tab)` BEFORE verifying the 5 virtual `D1b` non-linear public LUT proofs:
    let expected_lut_dims = [(23usize, 15usize), (19, 15), (15, 15), (15, 15), (17, 17)];
    for (prf, &(ew, et)) in receipt.lut_d1b_proofs.iter().zip(expected_lut_dims.iter()) {
        if prf.m_wit != ew || prf.m_tab != et {
            return Err("LUT D1b (m_wit, m_tab) dimension mismatch".into());
        }
    }
    let (beta_silu, z_silu) = verify_d1b_tuple_public_table_ext4(
        &[&luts.silu_x_bb, &luts.silu_y_bb],
        &receipt.lut_d1b_proofs[0],
        &mut tr,
    )?;
    let (beta_sig, z_sig) = verify_d1b_tuple_public_table_ext4(
        &[&luts.sig_x_bb, &luts.sig_y_bb],
        &receipt.lut_d1b_proofs[1],
        &mut tr,
    )?;
    let (beta_sp, z_sp) = verify_d1b_tuple_public_table_ext4(
        &[&luts.sp_x_bb, &luts.sp_y_bb],
        &receipt.lut_d1b_proofs[2],
        &mut tr,
    )?;
    let (beta_en, z_en) = verify_d1b_tuple_public_table_ext4(
        &[&luts.expneg_u_bb, &luts.expneg_y_bb],
        &receipt.lut_d1b_proofs[3],
        &mut tr,
    )?;
    let (beta_rsq, z_rsq) = verify_d1b_tuple_public_table_ext4(
        &[
            &luts.rsqrt_norm_cols[0],
            &luts.rsqrt_norm_cols[1],
            &luts.rsqrt_norm_cols[2],
            &luts.rsqrt_norm_cols[3],
            &luts.rsqrt_norm_cols[4],
        ],
        &receipt.lut_d1b_proofs[4],
        &mut tr,
    )?;

    // Discharge virtual range `rem_leaf_eval`s:
    for ((pl, prf), z_leaf) in range_plans
        .iter()
        .zip(receipt.range_d1b_proofs.iter())
        .zip(range_z_leaves.iter())
    {
        let mut by_mat: [Vec<LinearTermExt4>; 4] = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
        let mut const_sum = Ext4::ZERO;
        for sl in &pl.slices {
            let prefix = sl.base_cell >> sl.m_vars;
            let mut pref_ev = Ext4::ONE;
            for b in sl.m_vars..pl.m_wit {
                let bit = (prefix >> (b - sl.m_vars)) & 1;
                let zb = z_leaf[b];
                pref_ev = pref_ev.mul(if bit == 1 { zb } else { Ext4::ONE.sub(zb) });
            }
            const_sum = const_sum.add(pref_ev.scale_bb(sl.add_const_bb));
            by_mat[sl.mat_id].push(LinearTermExt4::PointEval {
                subtable: sl.subtable,
                point: z_leaf[..sl.m_vars].to_vec(),
                weight: pref_ev,
            });
        }
        let mut total_ev = const_sum;
        for m_id in 0..4 {
            if !by_mat[m_id].is_empty() {
                let mv = next_raw_ev(&mut ev_cursor)?;
                tr.absorb_ext4(b"rng_mev", mv);
                total_ev = total_ev.add(mv);
                online_claims[m_id].push(JointLinearClaimExt4 {
                    terms: std::mem::take(&mut by_mat[m_id]),
                    rhs: mv,
                });
            }
        }
        if total_ev != prf.rem_leaf_eval {
            return Err("virtual range D1b rem_leaf_eval sum mismatch".into());
        }
    }

    let pull_eval = |mat_id: usize,
                         st: usize,
                         pt: Vec<Ext4>,
                         cur: &mut usize,
                         tr_ref: &mut CShakeTranscript,
                         onl_cl: &mut [Vec<JointLinearClaimExt4>; 4]|
     -> Result<Ext4, String> {
        let v = next_raw_ev(cur)?;
        tr_ref.absorb_ext4(b"lin_ev", v);
        onl_cl[mat_id].push(JointLinearClaimExt4::point_eval(st, pt, v));
        Ok(v)
    };

    // Discharge virtual LUT leaf evaluations:
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SILU,
        z_silu[..15].to_vec(),
        receipt.lut_d1b_proofs[0].mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SIG,
        z_sig[..15].to_vec(),
        receipt.lut_d1b_proofs[1].mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_SP,
        z_sp[..15].to_vec(),
        receipt.lut_d1b_proofs[2].mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_EXPNEG,
        z_en[..15].to_vec(),
        receipt.lut_d1b_proofs[3].mult_leaf_eval,
    ));
    online_claims[2].push(JointLinearClaimExt4::point_eval(
        M2D_MULT_RSQRT,
        z_rsq[..17].to_vec(),
        receipt.lut_d1b_proofs[4].mult_leaf_eval,
    ));

    // SiLU virtual leaf (`0..2^22`: `CONV`, `2^22..2^22+2^21`: `MLP_GATE`, `2^22+2^21..+2^20`: `Z_PROJ`, rest `(0, 0)`):
    {
        let c_x = pull_eval(0, M0_CONV_PRE, z_silu[..22].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let c_y = pull_eval(0, M0_CONV_SILU, z_silu[..22].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let m_x = pull_eval(2, M2_MLP_GATE, z_silu[..21].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let m_y = pull_eval(2, M2_GATE_SILU, z_silu[..21].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let z_x = pull_eval(0, M0_Z_PROJ, z_silu[..20].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let z_y = pull_eval(0, M0_Z_SILU, z_silu[..20].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let p0 = Ext4::ONE.sub(z_silu[22]);
        let p1 = z_silu[22].mul(Ext4::ONE.sub(z_silu[21]));
        let p2 = z_silu[22].mul(z_silu[21]).mul(Ext4::ONE.sub(z_silu[20]));
        let wx = p0.mul(c_x).add(p1.mul(m_x)).add(p2.mul(z_x));
        let wy = p0.mul(c_y).add(p1.mul(m_y)).add(p2.mul(z_y));
        if wx.add(beta_silu.mul(wy)) != receipt.lut_d1b_proofs[0].rem_leaf_eval {
            return Err("SiLU virtual LUT leaf weld failed".into());
        }
    }
    // Sigmoid virtual leaf (`0..2^18`: `M1_GATE`, `2^18..2^18+2^13`: `M0_B_PROJ`, rest `(0, 512)`):
    {
        let g_x = pull_eval(1, M1_GATE, z_sig[..18].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let g_y = pull_eval(1, M1_SIG_GATE, z_sig[..18].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let b_x = pull_eval(0, M0_B_PROJ, z_sig[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let b_y = pull_eval(0, M0_BETA_Q10, z_sig[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let p0 = Ext4::ONE.sub(z_sig[18]);
        let mut p1 = z_sig[18];
        for &zb in &z_sig[13..18] {
            p1 = p1.mul(Ext4::ONE.sub(zb));
        }
        let pad_ind = Ext4::ONE.sub(eval_lt_const_mle(&z_sig, (1 << 18) + (1 << 13)));
        let wx = p0.mul(g_x).add(p1.mul(b_x));
        let wy = p0.mul(g_y).add(p1.mul(b_y)).add(pad_ind.scale_bb(512));
        if wx.add(beta_sig.mul(wy)) != receipt.lut_d1b_proofs[1].rem_leaf_eval {
            return Err("Sigmoid virtual LUT leaf weld failed".into());
        }
    }
    // Softplus virtual leaf (`0..2^13`: `M0_SP_IN`, rest `(0, sp_y_bb[16384])`):
    {
        let s_x = pull_eval(0, M0_SP_IN, z_sp[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let s_y = pull_eval(0, M0_SP_Q8, z_sp[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let p0 = Ext4::ONE.sub(z_sp[13]).mul(Ext4::ONE.sub(z_sp[14]));
        let pad_ind = Ext4::ONE.sub(p0);
        let wx = p0.mul(s_x);
        let wy = p0.mul(s_y).add(pad_ind.scale_bb(luts.sp_y_bb[16_384]));
        if wx.add(beta_sp.mul(wy)) != receipt.lut_d1b_proofs[2].rem_leaf_eval {
            return Err("Softplus virtual LUT leaf weld failed".into());
        }
    }
    // ExpNeg virtual leaf (`0..2^14`: `M1_U_SM`, `2^14..2^14+2^13`: `M0_G_EXP`, rest `(0, 4096)`):
    {
        let u_x = pull_eval(1, M1_U_SM, z_en[..14].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let u_y = pull_eval(1, M1_E_SM_RAW, z_en[..14].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let g_x = pull_eval(0, M0_G_EXP, z_en[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let g_y = pull_eval(0, M0_ALPHA_Q12, z_en[..13].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let p0 = Ext4::ONE.sub(z_en[14]);
        let p1 = z_en[14].mul(Ext4::ONE.sub(z_en[13]));
        let pad_ind = z_en[14].mul(z_en[13]);
        let wx = p0.mul(u_x).add(p1.mul(g_x));
        let wy = p0.mul(u_y).add(p1.mul(g_y)).add(pad_ind.scale_bb(4096));
        if wx.add(beta_en.mul(wy)) != receipt.lut_d1b_proofs[3].rem_leaf_eval {
            return Err("ExpNeg virtual LUT leaf weld failed".into());
        }
    }
    // RsqrtNorm virtual leaf (`m_wit = 17` on `mat 3`):
    {
        let rsq_srcs = [
            (1usize, 0usize, 1usize << 14),
            (2usize, 1usize << 14, 1usize << 11),
            (0usize, (1usize << 14) + (1usize << 11), 1usize << 10),
        ];
        let col_offs = [RGRP_POW4, RGRP_POW2, RGRP_HPOW2, RGRP_UMS, RGRP_RMLUT];
        let mut terms = Vec::with_capacity(15);
        let mut bp = Ext4::ONE;
        for &co in &col_offs {
            for &(grp, dst_off, len) in &rsq_srcs {
                let mv = len.trailing_zeros() as usize;
                let prefix = dst_off >> mv;
                let mut pref = bp;
                for b in mv..17 {
                    let bit = (prefix >> (b - mv)) & 1;
                    pref = pref.mul(if bit == 1 {
                        z_rsq[b]
                    } else {
                        Ext4::ONE.sub(z_rsq[b])
                    });
                }
                terms.push(LinearTermExt4::PointEval {
                    subtable: grp * RGRP_STRIDE + co,
                    point: z_rsq[..mv].to_vec(),
                    weight: pref,
                });
            }
            bp = bp.mul(beta_rsq);
        }
        let used = (1usize << 14) + (1usize << 11) + (1usize << 10);
        let pad_ind = Ext4::ONE.sub(eval_lt_const_mle(&z_rsq, used));
        online_claims[3].push(JointLinearClaimExt4 {
            terms,
            rhs: receipt.lut_d1b_proofs[4]
                .rem_leaf_eval
                .sub(beta_rsq.mul(pad_ind)),
        });
    }

    // Step C: Verify all `19` `weight_matmul_proofs` against `WeightModelRoot24L`:
    let gdn_ln1_slots: Vec<usize> = GDN_LAYER_INDICES.to_vec();
    let gqa_ln1_slots: Vec<usize> = GQA_LAYER_INDICES.to_vec();
    let mlp_ln2_slots: Vec<usize> = (0..NUM_LAYERS).map(|l| 32 + l).collect();
    #[allow(clippy::type_complexity)]
    let mm_jobs: [(&str, usize, usize, Option<&[usize]>, usize, usize, usize, usize, usize, usize, usize, u32, usize, usize); 13] = [
        ("wm_gdn_qkv", 3, RGRP_YOUT, Some(&gdn_ln1_slots), WST_GDN_QKV, 0, M0_QKV, M0_REM_QKV, 10, 13, 5, 512, GDN_QKV_DIM, NUM_GDN_LAYERS),
        ("wm_gdn_z", 3, RGRP_YOUT, Some(&gdn_ln1_slots), WST_GDN_Z, 0, M0_Z_PROJ, M0_REM_Z, 10, 11, 5, 512, 2048, NUM_GDN_LAYERS),
        ("wm_gdn_b", 3, RGRP_YOUT, Some(&gdn_ln1_slots), WST_GDN_B, 0, M0_B_PROJ, M0_REM_B, 10, 4, 5, 512, 16, NUM_GDN_LAYERS),
        ("wm_gdn_a", 3, RGRP_YOUT, Some(&gdn_ln1_slots), WST_GDN_A, 0, M0_A_PROJ, M0_REM_A, 10, 4, 5, 512, 16, NUM_GDN_LAYERS),
        ("wm_gdn_out", 0, M0_GATED, None, WST_GDN_OUT, 0, M0_ATTN_OUT, M0_REM_OUT, 11, 10, 5, 64, 1024, NUM_GDN_LAYERS),
        ("wm_gqa_q", 3, RGRP_YOUT, Some(&gqa_ln1_slots), WST_GQA_Q, 1, M1_Q_RAW, M1_REM_Q, 10, 11, 3, 512, 2048, NUM_GQA_LAYERS),
        ("wm_gqa_gate", 3, RGRP_YOUT, Some(&gqa_ln1_slots), WST_GQA_GATE, 1, M1_GATE, M1_REM_GATE, 10, 11, 3, 512, 2048, NUM_GQA_LAYERS),
        ("wm_gqa_k", 3, RGRP_YOUT, Some(&gqa_ln1_slots), WST_GQA_K, 1, M1_K_RAW, M1_REM_K, 10, 9, 3, 512, 512, NUM_GQA_LAYERS),
        ("wm_gqa_v", 3, RGRP_YOUT, Some(&gqa_ln1_slots), WST_GQA_V, 1, M1_V_PROJ, M1_REM_V, 10, 9, 3, 512, 512, NUM_GQA_LAYERS),
        ("wm_gqa_o", 1, M1_AO_G, None, WST_GQA_O, 1, M1_ATTN_OUT, M1_REM_OUT, 11, 10, 3, 64, 1024, NUM_GQA_LAYERS),
        ("wm_mlp_gate", 3, RGRP_YOUT, Some(&mlp_ln2_slots), WST_MLP_GATE, 2, M2_MLP_GATE, M2_REM_GATE, 10, 12, 5, 512, D_FF, NUM_LAYERS),
        ("wm_mlp_up", 3, RGRP_YOUT, Some(&mlp_ln2_slots), WST_MLP_UP, 2, M2_MLP_UP, M2_REM_UP, 10, 12, 5, 512, D_FF, NUM_LAYERS),
        ("wm_mlp_down", 2, M2_SWIGLU, None, WST_MLP_DOWN, 2, M2_MLP_OUT, M2_REM_MLPOUT, 12, 10, 5, 32, 1024, NUM_LAYERS),
    ];

    for (wm_idx, &(spec, x_mat, x_st, x_lmap, wst, y_mat, y_st, rem_st, log_d, log_j, log_l, out_div, j_bound, l_bound)) in mm_jobs.iter().enumerate() {
        let wp = &receipt.weight_matmul_proofs[wm_idx];
        let z_j = tr.squeeze_ext4_vec(b"mm_zj", log_j, true);
        let z_t = tr.squeeze_ext4_vec(b"mm_zt", LOG_SEQ, true);
        let z_l = tr.squeeze_ext4_vec(b"mm_zl", log_l, true);
        let y_pt = concat_pts(&[&z_j, &z_t, &z_l]);
        let y_ev = pull_eval(y_mat, y_st, y_pt.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let r_ev = pull_eval(y_mat, rem_st, y_pt, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let act = eval_lt_const_mle(&z_j, j_bound).mul(eval_lt_const_mle(&z_l, l_bound));
        let claim = y_ev
            .scale_bb(out_div)
            .add(r_ev)
            .sub(act.scale_bb(out_div / 2));

        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, log_l, log_d, &z_l, &wp.prf, &mut tr)?;
        tr.absorb_ext4(b"mm_wr", wp.weight_at_r);
        let (r_l, r_d) = (&ch[..log_l], &ch[log_l..]);
        weight_claims.push(PublicWeightClaim24L::point_eval(
            wst,
            concat_pts(&[r_d, &z_j, r_l]),
            wp.weight_at_r,
        ));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, wp.prf.gmask_sum));
        let scale_x = eq_mle_ext4(&z_l, r_l).mul(wp.weight_at_r);

        if let Some(slot_map) = x_lmap {
            let x_val = next_raw_ev(&mut ev_cursor)?;
            tr.absorb_ext4(b"mm_xmap", x_val);
            let eq_rl = build_eq_table_lsb_ext4(r_l);
            let mut x_terms = Vec::with_capacity(slot_map.len());
            for (li, &slot) in slot_map.iter().enumerate() {
                x_terms.push(LinearTermExt4::PointEval {
                    subtable: RGRP_YOUT,
                    point: concat_pts(&[r_d, &z_t, &bits_to_ext4(slot, 6)]),
                    weight: eq_rl[li],
                });
            }
            online_claims[3].push(JointLinearClaimExt4 { terms: x_terms, rhs: x_val });
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale_x.mul(x_val)),
            ));
        } else if x_mat == 2 {
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                vec![LinearTermExt4::PointEval {
                    subtable: x_st,
                    point: concat_pts(&[r_d, &z_t, r_l]),
                    weight: scale_x,
                }],
                gm_limb_ids,
                &w_at,
                rho,
                term,
            ));
        } else {
            let xv = pull_eval(x_mat, x_st, concat_pts(&[r_d, &z_t, r_l]), &mut ev_cursor, &mut tr, &mut online_claims)?;
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale_x.mul(xv)),
            ));
        }
    }

    // `wm_gdn_conv` (`weight_matmul_proofs[13]`):
    {
        let wp = &receipt.weight_matmul_proofs[13];
        let z_c = tr.squeeze_ext4_vec(b"conv_zc", 13, true);
        let z_t = tr.squeeze_ext4_vec(b"conv_zt", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"conv_zg", 5, true);
        let pt_ctg = concat_pts(&[&z_c, &z_t, &z_g]);
        let cp_ev = pull_eval(0, M0_CONV_PRE, pt_ctg.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rc_ev = pull_eval(0, M0_REM_CONV, pt_ctg, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let act = eval_lt_const_mle(&z_c, GDN_QKV_DIM).mul(eval_lt_const_mle(&z_g, NUM_GDN_LAYERS));
        let claim = cp_ev.scale_bb(512).add(rc_ev).sub(act.scale_bb(256));
        let z_cg = concat_pts(&[&z_c, &z_g]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 18, 2, &z_cg, &wp.prf, &mut tr)?;
        tr.absorb_ext4(b"conv_wr", wp.weight_at_r);
        let (r_c, r_g, r_kw) = (&ch[..13], &ch[13..18], &ch[18..20]);
        weight_claims.push(PublicWeightClaim24L::point_eval(
            WST_GDN_CONV,
            concat_pts(&[r_kw, r_c, r_g]),
            wp.weight_at_r,
        ));
        let l_at_r = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"conv_lr", l_at_r);
        let eq_t = build_eq_table_lsb_ext4(&z_t);
        let eq_kw = build_eq_table_lsb_ext4(r_kw);
        let mut s_terms = Vec::with_capacity(16);
        for s in 0..16 {
            let mut wt = Ext4::ZERO;
            for kw in 0..4 {
                if s + 3 >= kw && s + 3 - kw < 16 {
                    wt = wt.add(eq_kw[kw].mul(eq_t[s + 3 - kw]));
                }
            }
            s_terms.push(LinearTermExt4::PointEval {
                subtable: M0_QKV,
                point: concat_pts(&[r_c, &bits_to_ext4(s, 4), r_g]),
                weight: wt,
            });
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: s_terms, rhs: l_at_r });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_gdn_conv", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, wp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_cg, &ch[..18]).mul(l_at_r).mul(wp.weight_at_r)),
        ));
    }

    // `wm_gdn_sp_alog` (`weight_matmul_proofs[14]`):
    {
        let wp = &receipt.weight_matmul_proofs[14];
        let z_h = tr.squeeze_ext4_vec(b"spa_zh", 4, true);
        let z_t = tr.squeeze_ext4_vec(b"spa_zt", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"spa_zg", 5, true);
        let pt13 = concat_pts(&[&z_h, &z_t, &z_g]);
        let ge_ev = pull_eval(0, M0_G_EXP, pt13.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rg_ev = pull_eval(0, M0_REM_GEXP, pt13, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = ge_ev
            .scale_bb(512)
            .add(rg_ev)
            .sub(eval_lt_const_mle(&z_g, NUM_GDN_LAYERS).scale_bb(256));
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 9, 0, &z_hg, &wp.prf, &mut tr)?;
        tr.absorb_ext4(b"spa_wr", wp.weight_at_r);
        weight_claims.push(PublicWeightClaim24L::point_eval(WST_GDN_ALOG, ch.clone(), wp.weight_at_r));
        let sp_ev = pull_eval(0, M0_SP_Q8, concat_pts(&[&ch[..4], &z_t, &ch[4..9]]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_gdn_sp_alog", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, wp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_hg, &ch).mul(sp_ev).mul(wp.weight_at_r)),
        ));
    }

    // `wm_lm_head` + `DIFF_ARGMAX` unique greedy argmax check (`weight_matmul_proofs[15]`):
    {
        let wp = &receipt.weight_matmul_proofs[15];
        let z_v = tr.squeeze_ext4_vec(b"lmh_zv", 18, true);
        let log_ev = pull_eval(2, M2_LOGITS, z_v.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rlog_ev = pull_eval(2, M2_REM_LOGITS, z_v.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let darg_ev = pull_eval(2, M2_DIFF_ARGMAX, z_v.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let vstar_bits = bits_to_ext4(receipt.emitted_next_token_id as usize, 18);
        let max_bb = Ext4::from_bb(bb_from_i64(receipt.claimed_max_logit as i64));
        online_claims[2].push(JointLinearClaimExt4::point_eval(M2_LOGITS, vstar_bits, max_bb));

        let act_voc = eval_lt_const_mle(&z_v, VOCAB_SIZE);
        let lt_vstar = eval_lt_const_mle(&z_v, receipt.emitted_next_token_id as usize);
        let want_darg = max_bb.mul(act_voc).sub(log_ev).sub(lt_vstar);
        if darg_ev != want_darg {
            return Err("lm_head greedy argmax dominance equation failed".into());
        }

        // Factor `1/2` from `eq([half], ch[0]) = 1/2`!
        let unscaled_claim = log_ev.scale_bb(512).add(rlog_ev).sub(act_voc.scale_bb(256));
        let claim = unscaled_claim.scale_bb(INV2_BB);
        let z_half = [Ext4::from_bb(INV2_BB)];
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 1, 9, &z_half, &wp.prf, &mut tr)?;
        tr.absorb_ext4(b"lmh_wr", wp.weight_at_r);
        weight_claims.push(PublicWeightClaim24L::point_eval(
            WST_EMBED,
            concat_pts(&[&ch, &z_v]),
            wp.weight_at_r,
        ));
        let t15_s24 = concat_pts(&[&ch, &bits_to_ext4(15, 4), &bits_to_ext4(24, 6)]);
        let x_ev = pull_eval(3, RGRP_YOUT, t15_s24, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "wm_lm_head", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, wp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_half, &ch[..1]).mul(x_ev).mul(wp.weight_at_r)),
        ));
    }

    // `wm_rms{0,1,2}_gain` (`weight_matmul_proofs[16..19]`):
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let wp = &receipt.weight_matmul_proofs[16 + g_idx];
        let spec = ["wm_rms0_gain", "wm_rms1_gain", "wm_rms2_gain"][g_idx];
        let mf = cfg.log_d + cfg.m_row;
        let b = cfg.grp * RGRP_STRIDE;
        let z_full = tr.squeeze_ext4_vec(b"rmsg_zf", mf, true);
        let y_ev = pull_eval(3, b + RGRP_YOUT, z_full.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let ry_ev = pull_eval(3, b + RGRP_RY, z_full.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let act = eval_rms_group_act_mle(g_idx, &z_full[cfg.log_d..]);
        let gdiv = cfg.gain_div as u32;
        let claim = y_ev.scale_bb(gdiv).add(ry_ev).sub(act.scale_bb(gdiv / 2));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, mf, 0, &z_full, &wp.prf, &mut tr)?;
        tr.absorb_ext4(b"rmsg_wr", wp.weight_at_r);
        let w_pt = match g_idx {
            0 => concat_pts(&[&ch[..10], &ch[14..20]]),
            1 => concat_pts(&[&ch[..7], &ch[15..21]]),
            _ => concat_pts(&[&ch[..8], &ch[8..12], &ch[16..19]]),
        };
        weight_claims.push(PublicWeightClaim24L::point_eval(cfg.wst_gain, w_pt, wp.weight_at_r));
        let u_ev = pull_eval(3, b + RGRP_UQ9, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, wp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_limb_ids,
            &w_at,
            rho,
            term.sub(eq_mle_ext4(&z_full, &ch).mul(u_ev).mul(wp.weight_at_r)),
        ));
    }

    // Step D: Verify all `16` `pub_ind_proofs`:
    let mut pi_idx = 0usize;
    let mut verify_wit_pub = |spec: &str,
                              claim: Ext4,
                              wit_mat: usize,
                              wit_st: usize,
                              wit_pt_map: Option<fn(&[Ext4]) -> Vec<Ext4>>,
                              eval_pub_fn: &dyn Fn(&[Ext4]) -> Ext4,
                              z_s: Vec<Ext4>,
                              cur: &mut usize,
                              tr_ref: &mut CShakeTranscript,
                              onl_cl: &mut [Vec<JointLinearClaimExt4>; 4]|
     -> Result<(Vec<Ext4>, Ext4), String> {
        let prf = &receipt.pub_ind_proofs[pi_idx];
        pi_idx += 1;
        let m = z_s.len();
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, m, 0, &z_s, prf, tr_ref)?;
        let p_at_r = eval_pub_fn(&ch);
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        onl_cl[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, prf.gmask_sum));
        let scale = eq_mle_ext4(&z_s, &ch).mul(p_at_r);
        let mapped_pt = wit_pt_map.map_or_else(|| ch.clone(), |f| f(&ch));
        let mut custom_w = Ext4::ZERO;
        if wit_mat == 2 && wit_st < 999 {
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                vec![LinearTermExt4::PointEval {
                    subtable: wit_st,
                    point: mapped_pt,
                    weight: scale,
                }],
                gm_limb_ids,
                &w_at,
                rho,
                term,
            ));
        } else if wit_st < 999 {
            let wev = pull_eval(wit_mat, wit_st, mapped_pt, cur, tr_ref, onl_cl)?;
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale.mul(wev)),
            ));
        } else {
            custom_w = next_raw_ev(cur)?;
            tr_ref.absorb_ext4(b"pi_wr", custom_w);
            onl_cl[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(),
                gm_limb_ids,
                &w_at,
                rho,
                term.sub(scale.mul(custom_w)),
            ));
        }
        Ok((ch, custom_w))
    };

    let eval_bad_ge = |ch: &[Ext4]| -> Ext4 {
        Ext4::ONE.sub(
            eval_lt_const_mle(&ch[12..17], NUM_GDN_LAYERS)
                .mul(eval_cmp_ij_mle(&ch[4..8], &ch[8..12], false)),
        )
    };
    let eval_bad_gt = |ch: &[Ext4]| -> Ext4 {
        Ext4::ONE.sub(
            eval_lt_const_mle(&ch[12..17], NUM_GDN_LAYERS)
                .mul(eval_cmp_ij_mle(&ch[4..8], &ch[8..12], true)),
        )
    };
    let z_g1 = tr.squeeze_ext4_vec(b"pi_zg1", 17, true);
    verify_wit_pub("pi_gdn_gamma_zc", Ext4::ZERO, 0, M0_GAMMA, None, &eval_bad_ge, z_g1, &mut ev_cursor, &mut tr, &mut online_claims)?;
    let z_g2 = tr.squeeze_ext4_vec(b"pi_zg2", 17, true);
    verify_wit_pub("pi_gdn_lwy_slt", Ext4::ZERO, 0, M0_L_WY, None, &eval_bad_gt, z_g2, &mut ev_cursor, &mut tr, &mut online_claims)?;
    let z_g3 = tr.squeeze_ext4_vec(b"pi_zg3", 17, true);
    verify_wit_pub("pi_gdn_awy_ut", Ext4::ZERO, 0, M0_A_WY, None, &eval_bad_ge, z_g3, &mut ev_cursor, &mut tr, &mut online_claims)?;

    // GQA Q-RoPE & K-RoPE:
    {
        let b2 = 2 * RGRP_STRIDE;
        let z_rq = tr.squeeze_ext4_vec(b"rope_zq", 18, true);
        let qhr_ev = pull_eval(1, M1_QH_R, z_rq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rrq_ev = pull_eval(1, M1_REM_ROPE_Q, z_rq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let cl_qd = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"rope_q_cd", cl_qd);
        let tot_q = qhr_ev
            .scale_bb(4096)
            .add(rrq_ev)
            .sub(eval_lt_const_mle(&z_rq[15..18], NUM_GQA_LAYERS).scale_bb(2048));
        let cl_qc = tot_q.sub(cl_qd);
        fn map_q18_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[&ch[..8], &ch[8..11], &[Ext4::ZERO], &ch[11..15], &ch[15..18]])
        }
        fn map_q18_swap_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..5],
                &[Ext4::ONE.sub(ch[5])],
                &ch[6..8],
                &ch[8..11],
                &[Ext4::ZERO],
                &ch[11..15],
                &ch[15..18],
            ])
        }
        let eval_rdiag18 = |ch: &[Ext4]| -> Ext4 {
            eval_lt_const_mle(&ch[15..18], NUM_GQA_LAYERS)
                .mul(mle_eval_bb_at_ext4(&luts.rope_diag_bb, &concat_pts(&[&ch[..8], &ch[11..15]])))
        };
        let eval_rcross18 = |ch: &[Ext4]| -> Ext4 {
            eval_lt_const_mle(&ch[15..18], NUM_GQA_LAYERS)
                .mul(mle_eval_bb_at_ext4(&luts.rope_cross_bb, &concat_pts(&[&ch[..8], &ch[11..15]])))
        };
        verify_wit_pub("pi_gqa_rope_q_diag", cl_qd, 3, b2 + RGRP_YOUT, Some(map_q18_to_rms), &eval_rdiag18, z_rq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        verify_wit_pub("pi_gqa_rope_q_cross", cl_qc, 3, b2 + RGRP_YOUT, Some(map_q18_swap_to_rms), &eval_rcross18, z_rq, &mut ev_cursor, &mut tr, &mut online_claims)?;

        let z_rk = tr.squeeze_ext4_vec(b"rope_zk", 16, true);
        let khr_ev = pull_eval(1, M1_KH_R, z_rk.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rrk_ev = pull_eval(1, M1_REM_ROPE_K, z_rk.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let cl_kd = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"rope_k_cd", cl_kd);
        let tot_k = khr_ev
            .scale_bb(4096)
            .add(rrk_ev)
            .sub(eval_lt_const_mle(&z_rk[13..16], NUM_GQA_LAYERS).scale_bb(2048));
        let cl_kc = tot_k.sub(cl_kd);
        fn map_k16_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..8],
                &[ch[8], Ext4::ZERO, Ext4::ZERO, Ext4::ONE],
                &ch[9..13],
                &ch[13..16],
            ])
        }
        fn map_k16_swap_to_rms(ch: &[Ext4]) -> Vec<Ext4> {
            concat_pts(&[
                &ch[..5],
                &[Ext4::ONE.sub(ch[5])],
                &ch[6..8],
                &[ch[8], Ext4::ZERO, Ext4::ZERO, Ext4::ONE],
                &ch[9..13],
                &ch[13..16],
            ])
        }
        let eval_rdiag16 = |ch: &[Ext4]| -> Ext4 {
            eval_lt_const_mle(&ch[13..16], NUM_GQA_LAYERS)
                .mul(mle_eval_bb_at_ext4(&luts.rope_diag_bb, &concat_pts(&[&ch[..8], &ch[9..13]])))
        };
        let eval_rcross16 = |ch: &[Ext4]| -> Ext4 {
            eval_lt_const_mle(&ch[13..16], NUM_GQA_LAYERS)
                .mul(mle_eval_bb_at_ext4(&luts.rope_cross_bb, &concat_pts(&[&ch[..8], &ch[9..13]])))
        };
        verify_wit_pub("pi_gqa_rope_k_diag", cl_kd, 3, b2 + RGRP_YOUT, Some(map_k16_to_rms), &eval_rdiag16, z_rk.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        verify_wit_pub("pi_gqa_rope_k_cross", cl_kc, 3, b2 + RGRP_YOUT, Some(map_k16_swap_to_rms), &eval_rcross16, z_rk, &mut ev_cursor, &mut tr, &mut online_claims)?;
    }

    // GQA 14-bit causal indicator checks:
    {
        let eval_caus = |ch: &[Ext4]| -> Ext4 {
            eval_lt_const_mle(&ch[11..14], NUM_GQA_LAYERS)
                .mul(eval_cmp_ij_mle(&ch[4..8], &ch[..4], false))
        };
        let eval_non_caus = |ch: &[Ext4]| -> Ext4 { Ext4::ONE.sub(eval_caus(ch)) };
        let zc1 = tr.squeeze_ext4_vec(b"gqa_zc1", 14, true);
        verify_wit_pub("pi_gqa_sc_caus", Ext4::ZERO, 1, M1_SC_Q8, None, &eval_non_caus, zc1, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let zc2 = tr.squeeze_ext4_vec(b"gqa_zc2", 14, true);
        verify_wit_pub("pi_gqa_sel_caus", Ext4::ZERO, 1, M1_SEL_MAX, None, &eval_non_caus, zc2, &mut ev_cursor, &mut tr, &mut online_claims)?;

        let zc3 = tr.squeeze_ext4_vec(b"gqa_zc3", 14, true);
        let usm_ev = pull_eval(1, M1_U_SM, zc3.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (ch3, wr3) = verify_wit_pub("pi_gqa_usm_caus", usm_ev, 1, 999, None, &eval_caus, zc3, &mut ev_cursor, &mut tr, &mut online_claims)?;
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_M_MAX, point: ch3[4..].to_vec(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M1_SC_Q8, point: ch3, weight: Ext4::ONE.neg() },
            ],
            rhs: wr3,
        });

        let zc4 = tr.squeeze_ext4_vec(b"gqa_zc4", 14, true);
        let esm_ev = pull_eval(1, M1_E_SM, zc4.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        verify_wit_pub("pi_gqa_esm_caus", esm_ev, 1, M1_E_SM_RAW, None, &eval_caus, zc4, &mut ev_cursor, &mut tr, &mut online_claims)?;

        let zc5 = tr.squeeze_ext4_vec(b"gqa_zc5", 14, true);
        verify_wit_pub("pi_gqa_psm_caus", Ext4::ZERO, 1, M1_P_SM, None, &eval_non_caus, zc5, &mut ev_cursor, &mut tr, &mut online_claims)?;

        let zc6 = tr.squeeze_ext4_vec(b"gqa_zc6", 14, true);
        let dpsm_ev = pull_eval(1, M1_DIFF_PSM, zc6.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (ch6, wr6) = verify_wit_pub("pi_gqa_dpsm_caus", dpsm_ev, 1, 999, None, &eval_caus, zc6, &mut ev_cursor, &mut tr, &mut online_claims)?;
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_Z_SM, point: ch6[4..].to_vec(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M1_REM_PSM, point: ch6, weight: Ext4::ONE.neg() },
            ],
            rhs: wr6.add(Ext4::ONE),
        });
    }

    // `pi_rms{0,1,2}_dnorm`:
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let spec = ["pi_rms0_dnorm", "pi_rms1_dnorm", "pi_rms2_dnorm"][g_idx];
        let b = cfg.grp * RGRP_STRIDE;
        let zr = tr.squeeze_ext4_vec(b"rmsdn_zr", cfg.m_row, true);
        let dn_ev = pull_eval(3, b + RGRP_DIFF_NORM, zr.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let eval_act = |ch: &[Ext4]| -> Ext4 { eval_rms_group_act_mle(g_idx, ch) };
        let (chr, wr) = verify_wit_pub(spec, dn_ev, 3, 999, None, &eval_act, zr, &mut ev_cursor, &mut tr, &mut online_claims)?;
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_POW4, point: chr.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: b + RGRP_RNORM, point: chr, weight: Ext4::ONE.neg() },
            ],
            rhs: wr.add(Ext4::ONE),
        });
    }

    // Step E: Verify all `29` `sec_sec_proofs`:
    let mut ss_idx = 0usize;
    // 1. `ss_gdn_gamma_rec`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z17 = tr.squeeze_ext4_vec(b"gmrec_z", 17, true);
        let gm_ev = pull_eval(0, M0_GAMMA, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rgm_ev = pull_eval(0, M0_REM_GAMMA, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let g_act = eval_lt_const_mle(&z17[12..17], NUM_GDN_LAYERS);
        let i_diag = g_act.mul(eq_mle_ext4(&z17[4..8], &z17[8..12]));
        let i_gt = g_act.mul(eval_cmp_ij_mle(&z17[4..8], &z17[8..12], true));
        let claim = gm_ev
            .sub(i_diag.scale_bb(512))
            .scale_bb(4096)
            .add(rgm_ev)
            .sub(i_gt.scale_bb(2048));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 17, 0, &z17, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let eq_i = build_eq_table_lsb_ext4(&ch[4..8]);
        let eq_j = build_eq_table_lsb_ext4(&ch[8..12]);
        let mut terms_gp = Vec::with_capacity(120);
        for j in 0..16 {
            for ip in j..15 {
                terms_gp.push(LinearTermExt4::PointEval {
                    subtable: M0_GAMMA,
                    point: concat_pts(&[&ch[..4], &bits_to_ext4(ip, 4), &bits_to_ext4(j, 4), &ch[12..17]]),
                    weight: eq_i[ip + 1].mul(eq_j[j]),
                });
            }
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: terms_gp, rhs: sp.left_at_r });
        let al_ev = pull_eval(0, M0_ALPHA_Q12, concat_pts(&[&ch[..8], &ch[12..17]]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_gamma_rec", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(sp.left_at_r).mul(al_ev)),
        ));
    }

    // 2. `ss_gdn_dkk`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z_h = tr.squeeze_ext4_vec(b"dkk_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"dkk_zi", 4, true);
        let z_j = tr.squeeze_ext4_vec(b"dkk_zj", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"dkk_zg", 5, true);
        let pt17 = concat_pts(&[&z_h, &z_i, &z_j, &z_g]);
        let dkk_ev = pull_eval(0, M0_DKK, pt17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rdkk_ev = pull_eval(0, M0_REM_DKK, pt17, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = dkk_ev.scale_bb(512).add(rdkk_ev).sub(eval_lt_const_mle(&z_g, NUM_GDN_LAYERS).scale_bb(256));
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 9, 7, &z_hg, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let r_val = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"dkk_rr", r_val);
        let (r_h, r_g, r_d) = (&ch[..4], &ch[4..9], &ch[9..16]);
        let eq_rg = build_eq_table_lsb_ext4(r_g);
        let b1 = RGRP_STRIDE;
        let mut t_i = Vec::with_capacity(18);
        let mut t_j = Vec::with_capacity(18);
        for g in 0..NUM_GDN_LAYERS {
            let gkb = bits_to_ext4(3 * g + 1, 6);
            t_i.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: concat_pts(&[r_d, r_h, &z_i, &gkb]), weight: eq_rg[g] });
            t_j.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: concat_pts(&[r_d, r_h, &z_j, &gkb]), weight: eq_rg[g] });
        }
        online_claims[3].push(JointLinearClaimExt4 { terms: t_i, rhs: sp.left_at_r });
        online_claims[3].push(JointLinearClaimExt4 { terms: t_j, rhs: r_val });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_dkk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(sp.left_at_r).mul(r_val)),
        ));
    }

    // 3. `ss_gdn_bg`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z17 = tr.squeeze_ext4_vec(b"bg_z", 17, true);
        let bg_ev = pull_eval(0, M0_BG, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rbg_ev = pull_eval(0, M0_REM_BG, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = bg_ev.scale_bb(1024).add(rbg_ev).sub(eval_lt_const_mle(&z17[12..17], NUM_GDN_LAYERS).scale_bb(512));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 17, 0, &z17, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let b_ev = pull_eval(0, M0_BETA_Q10, concat_pts(&[&ch[..8], &ch[12..17]]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        if sp.left_at_r != b_ev {
            return Err("ss_gdn_bg left_at_r mismatch".into());
        }
        let gm_ev = pull_eval(0, M0_GAMMA, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_bg", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(sp.left_at_r).mul(gm_ev)),
        ));
    }

    // 4. `ss_gdn_lwy`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z17 = tr.squeeze_ext4_vec(b"lwy_z", 17, true);
        let lwy_ev = pull_eval(0, M0_L_WY, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rlwy_ev = pull_eval(0, M0_REM_LWY, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let i_gt = eval_lt_const_mle(&z17[12..17], NUM_GDN_LAYERS).mul(eval_cmp_ij_mle(&z17[4..8], &z17[8..12], true));
        let claim = lwy_ev.scale_bb(512).add(rlwy_ev).sub(i_gt.scale_bb(256));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 17, 0, &z17, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let eq_i = build_eq_table_lsb_ext4(&ch[4..8]);
        let eq_j = build_eq_table_lsb_ext4(&ch[8..12]);
        let mut dkk_terms = Vec::with_capacity(120);
        for j in 0..16 {
            for i in (j + 1)..16 {
                dkk_terms.push(LinearTermExt4::PointEval {
                    subtable: M0_DKK,
                    point: concat_pts(&[&ch[..4], &bits_to_ext4(i, 4), &bits_to_ext4(j, 4), &ch[12..17]]),
                    weight: eq_i[i].mul(eq_j[j]),
                });
            }
        }
        online_claims[0].push(JointLinearClaimExt4 { terms: dkk_terms, rhs: sp.left_at_r });
        let bg_ev = pull_eval(0, M0_BG, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_lwy", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(sp.left_at_r).mul(bg_ev)),
        ));
    }

    // 5. `ss_gdn_dqk`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z_h = tr.squeeze_ext4_vec(b"dqk_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"dqk_zi", 4, true);
        let z_j = tr.squeeze_ext4_vec(b"dqk_zj", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"dqk_zg", 5, true);
        let pt17 = concat_pts(&[&z_h, &z_i, &z_j, &z_g]);
        let dqk_ev = pull_eval(0, M0_DQK, pt17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rdqk_ev = pull_eval(0, M0_REM_DQK, pt17, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = dqk_ev.scale_bb(724).add(rdqk_ev).sub(eval_lt_const_mle(&z_g, NUM_GDN_LAYERS).scale_bb(362));
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 9, 7, &z_hg, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let r_val = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"dqk_rr", r_val);
        let (r_h, r_g, r_d) = (&ch[..4], &ch[4..9], &ch[9..16]);
        let eq_rg = build_eq_table_lsb_ext4(r_g);
        let b1 = RGRP_STRIDE;
        let mut t_i = Vec::with_capacity(18);
        let mut t_j = Vec::with_capacity(18);
        for g in 0..NUM_GDN_LAYERS {
            t_i.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: concat_pts(&[r_d, r_h, &z_i, &bits_to_ext4(3 * g, 6)]), weight: eq_rg[g] });
            t_j.push(LinearTermExt4::PointEval { subtable: b1 + RGRP_YOUT, point: concat_pts(&[r_d, r_h, &z_j, &bits_to_ext4(3 * g + 1, 6)]), weight: eq_rg[g] });
        }
        online_claims[3].push(JointLinearClaimExt4 { terms: t_i, rhs: sp.left_at_r });
        online_claims[3].push(JointLinearClaimExt4 { terms: t_j, rhs: r_val });
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_dqk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(sp.left_at_r).mul(r_val)),
        ));
    }

    // 6. `ss_gdn_awy`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z17 = tr.squeeze_ext4_vec(b"awy_z", 17, true);
        let awy_ev = pull_eval(0, M0_A_WY, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rawy_ev = pull_eval(0, M0_REM_AWY, z17.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let i_ge = eval_lt_const_mle(&z17[12..17], NUM_GDN_LAYERS).mul(eval_cmp_ij_mle(&z17[4..8], &z17[8..12], false));
        let claim = awy_ev.scale_bb(512).add(rawy_ev).sub(i_ge.scale_bb(256));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 17, 0, &z17, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let dqk_ev = pull_eval(0, M0_DQK, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        if sp.left_at_r != dqk_ev {
            return Err("ss_gdn_awy left_at_r mismatch".into());
        }
        let gm_ev = pull_eval(0, M0_GAMMA, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_awy", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z17, &ch).mul(sp.left_at_r).mul(gm_ev)),
        ));
    }

    // 7. `ss_gdn_vbeta`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z20 = tr.squeeze_ext4_vec(b"vb_z", 20, true);
        let vb_ev = pull_eval(0, M0_V_BETA, z20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rvb_ev = pull_eval(0, M0_REM_VBETA, z20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = vb_ev.scale_bb(256).add(rvb_ev).sub(eval_lt_const_mle(&z20[15..20], NUM_GDN_LAYERS).scale_bb(128));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 20, 0, &z20, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let eq_rg = build_eq_table_lsb_ext4(&ch[15..20]);
        let b_terms: Vec<LinearTermExt4> = (0..NUM_GDN_LAYERS)
            .map(|g| LinearTermExt4::PointEval {
                subtable: M0_BETA_Q10,
                point: concat_pts(&[&ch[7..15], &bits_to_ext4(g, 5)]),
                weight: eq_rg[g],
            })
            .collect();
        online_claims[0].push(JointLinearClaimExt4 { terms: b_terms, rhs: sp.left_at_r });
        let vr_pt = concat_pts(&[&ch[..11], &[Ext4::ZERO, Ext4::ONE], &ch[11..20]]);
        let vr_ev = pull_eval(0, M0_CONV_SILU, vr_pt, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_vbeta", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z20, &ch).mul(sp.left_at_r).mul(vr_ev)),
        ));
    }

    // 8 & 9: `ss_gdn_uwy_solve` & `ss_gdn_ywy_read`:
    for (spec, mat_st, out_st, rem_st, is_solve) in [
        ("ss_gdn_uwy_solve", M0_L_WY, M0_U_WY, M0_REM_UWY, true),
        ("ss_gdn_ywy_read", M0_A_WY, M0_Y_WY, M0_REM_YWY, false),
    ] {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z_d = tr.squeeze_ext4_vec(b"wy_zd", 7, true);
        let z_h = tr.squeeze_ext4_vec(b"wy_zh", 4, true);
        let z_i = tr.squeeze_ext4_vec(b"wy_zi", 4, true);
        let z_g = tr.squeeze_ext4_vec(b"wy_zg", 5, true);
        let pt20 = concat_pts(&[&z_d, &z_h, &z_i, &z_g]);
        let g_act = eval_lt_const_mle(&z_g, NUM_GDN_LAYERS);
        let claim = if is_solve {
            let vb_ev = pull_eval(0, M0_V_BETA, pt20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let uw_ev = pull_eval(0, out_st, pt20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rw_ev = pull_eval(0, rem_st, pt20, &mut ev_cursor, &mut tr, &mut online_claims)?;
            vb_ev.sub(uw_ev).scale_bb(512).add(g_act.scale_bb(256)).sub(rw_ev)
        } else {
            let yw_ev = pull_eval(0, out_st, pt20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let ry_ev = pull_eval(0, rem_st, pt20, &mut ev_cursor, &mut tr, &mut online_claims)?;
            yw_ev.scale_bb(1024).add(ry_ev).sub(g_act.scale_bb(512))
        };
        let z_hg = concat_pts(&[&z_h, &z_g]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 9, 4, &z_hg, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let (r_h, r_g, r_j) = (&ch[..4], &ch[4..9], &ch[9..13]);
        online_claims[0].push(JointLinearClaimExt4::point_eval(
            mat_st,
            concat_pts(&[r_h, &z_i, r_j, r_g]),
            sp.left_at_r,
        ));
        let u_ev = pull_eval(0, M0_U_WY, concat_pts(&[&z_d, r_h, r_j, r_g]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, spec, &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z_hg, &ch[..9]).mul(sp.left_at_r).mul(u_ev)),
        ));
    }

    // 10. `ss_gdn_gated`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z20 = tr.squeeze_ext4_vec(b"gg_z", 20, true);
        let gt_ev = pull_eval(0, M0_GATED, z20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rgt_ev = pull_eval(0, M0_REM_GATED, z20.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = gt_ev.scale_bb(256).add(rgt_ev).sub(eval_lt_const_mle(&z20[15..20], NUM_GDN_LAYERS).scale_bb(128));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 20, 0, &z20, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let eq_rg = build_eq_table_lsb_ext4(&ch[15..20]);
        let b1 = RGRP_STRIDE;
        let mut yn_terms = Vec::with_capacity(18);
        for g in 0..NUM_GDN_LAYERS {
            yn_terms.push(LinearTermExt4::PointEval {
                subtable: b1 + RGRP_YOUT,
                point: concat_pts(&[&ch[..15], &bits_to_ext4(3 * g + 2, 6)]),
                weight: eq_rg[g],
            });
        }
        online_claims[3].push(JointLinearClaimExt4 { terms: yn_terms, rhs: sp.left_at_r });
        let zs_ev = pull_eval(0, M0_Z_SILU, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gdn_gated", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z20, &ch).mul(sp.left_at_r).mul(zs_ev)),
        ));
    }

    // 11. `ss_gqa_qk`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z_tj = tr.squeeze_ext4_vec(b"qk_ztj", 4, true);
        let z_ti = tr.squeeze_ext4_vec(b"qk_zti", 4, true);
        let z_hq = tr.squeeze_ext4_vec(b"qk_zhq", 3, true);
        let z_q = tr.squeeze_ext4_vec(b"qk_zq", 3, true);
        let pt14 = concat_pts(&[&z_tj, &z_ti, &z_hq, &z_q]);
        let sc_ev = pull_eval(1, M1_SC_Q8, pt14.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rsc_ev = pull_eval(1, M1_REM_SC, pt14, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let i_caus = eval_lt_const_mle(&z_q, NUM_GQA_LAYERS).mul(eval_cmp_ij_mle(&z_ti, &z_tj, false));
        let claim = sc_ev.scale_bb(64).add(rsc_ev).sub(i_caus.scale_bb(32));
        let z10 = concat_pts(&[&z_ti, &z_hq, &z_q]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 10, 8, &z10, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let (r_ti, r_hq, r_q, r_dh) = (&ch[..4], &ch[4..7], &ch[7..10], &ch[10..18]);
        let eq_tj = build_eq_table_lsb_ext4(&z_tj);
        let eq_rti = build_eq_table_lsb_ext4(r_ti);
        let eq_rq = build_eq_table_lsb_ext4(r_q);
        let mut k_terms = Vec::with_capacity(96);
        for q in 0..NUM_GQA_LAYERS {
            let q_bits = bits_to_ext4(q, 3);
            for tj in 0..16 {
                let mut sum_ti = Ext4::ZERO;
                for &eti in &eq_rti[tj..16] {
                    sum_ti = sum_ti.add(eti);
                }
                k_terms.push(LinearTermExt4::PointEval {
                    subtable: M1_KH_R,
                    point: concat_pts(&[r_dh, &[r_hq[2]], &bits_to_ext4(tj, 4), &q_bits]),
                    weight: eq_rq[q].mul(eq_tj[tj]).mul(sum_ti),
                });
            }
        }
        online_claims[1].push(JointLinearClaimExt4 { terms: k_terms, rhs: sp.left_at_r });
        let q_ev = pull_eval(1, M1_QH_R, concat_pts(&[r_dh, r_hq, r_ti, r_q]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_qk", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z10, &ch[..10]).mul(sp.left_at_r).mul(q_ev)),
        ));
    }

    // 12. `ss_gqa_sel_bool`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z14 = tr.squeeze_ext4_vec(b"selb_z", 14, true);
        let (rho, ch, term) = verify_gmask_einsum_ext4(Ext4::ZERO, 14, 0, &z14, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_SEL_MAX, ch.clone(), sp.left_at_r));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_sel_bool", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z14, &ch).mul(sp.left_at_r).mul(Ext4::ONE.sub(sp.left_at_r))),
        ));
    }

    // 13. `ss_gqa_sel_max`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z14 = tr.squeeze_ext4_vec(b"selm_z", 14, true);
        let (rho, ch, term) = verify_gmask_einsum_ext4(Ext4::ZERO, 14, 0, &z14, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_SEL_MAX, ch.clone(), sp.left_at_r));
        let m_ev = pull_eval(1, M1_M_MAX, ch[4..].to_vec(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let sc_ev = pull_eval(1, M1_SC_Q8, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_sel_max", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z14, &ch).mul(sp.left_at_r).mul(m_ev.sub(sc_ev))),
        ));
    }

    // 14. `ss_gqa_psm_div`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z14 = tr.squeeze_ext4_vec(b"psmd_z", 14, true);
        let esm_ev = pull_eval(1, M1_E_SM, z14.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rpsm_ev = pull_eval(1, M1_REM_PSM, z14.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = esm_ev.scale_bb(2048).sub(rpsm_ev);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 14, 0, &z14, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_Z_SM, ch[4..].to_vec(), sp.left_at_r));
        let p_ev = pull_eval(1, M1_P_SM, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_psm_div", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z14, &ch).mul(sp.left_at_r).mul(p_ev)),
        ));
    }

    // 15. `ss_gqa_pv`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z_dh = tr.squeeze_ext4_vec(b"pv_zdh", 8, true);
        let z_hq = tr.squeeze_ext4_vec(b"pv_zhq", 3, true);
        let z_ti = tr.squeeze_ext4_vec(b"pv_zti", 4, true);
        let z_q = tr.squeeze_ext4_vec(b"pv_zq", 3, true);
        let pt18 = concat_pts(&[&z_dh, &z_hq, &z_ti, &z_q]);
        let aoh_ev = pull_eval(1, M1_AO_H, pt18.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let raoh_ev = pull_eval(1, M1_REM_AOH, pt18, &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = aoh_ev.scale_bb(2048).add(raoh_ev).sub(eval_lt_const_mle(&z_q, NUM_GQA_LAYERS).scale_bb(1024));
        let z6 = concat_pts(&[&z_hq, &z_q]);
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 6, 4, &z6, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        let (r_hq, r_q, r_tj) = (&ch[..3], &ch[3..6], &ch[6..10]);
        online_claims[1].push(JointLinearClaimExt4::point_eval(
            M1_P_SM,
            concat_pts(&[r_tj, &z_ti, r_hq, r_q]),
            sp.left_at_r,
        ));
        let v_ev = pull_eval(1, M1_V_PROJ, concat_pts(&[&z_dh, &[r_hq[2]], r_tj, r_q]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_pv", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z6, &ch[..6]).mul(sp.left_at_r).mul(v_ev)),
        ));
    }

    // 16. `ss_gqa_aog`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z18 = tr.squeeze_ext4_vec(b"aog_z", 18, true);
        let aog_ev = pull_eval(1, M1_AO_G, z18.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let raog_ev = pull_eval(1, M1_REM_AOG, z18.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let claim = aog_ev.scale_bb(1024).add(raog_ev).sub(eval_lt_const_mle(&z18[15..18], NUM_GQA_LAYERS).scale_bb(512));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 18, 0, &z18, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        online_claims[1].push(JointLinearClaimExt4::point_eval(M1_AO_H, ch.clone(), sp.left_at_r));
        let sg_ev = pull_eval(1, M1_SIG_GATE, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_gqa_aog", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(), gm_limb_ids, &w_at, rho, term.sub(eq_mle_ext4(&z18, &ch).mul(sp.left_at_r).mul(sg_ev)),
        ));
    }

    // 17. `ss_mlp_swiglu`:
    {
        let sp = &receipt.sec_sec_proofs[ss_idx];
        ss_idx += 1;
        let z21 = tr.squeeze_ext4_vec(b"swg_z", 21, true);
        let sw_ev = pull_eval(2, M2_SWIGLU, z21.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let rsw_ev = pull_eval(2, M2_REM_SWIGLU, z21.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let act_mlp = eval_lt_const_mle(&z21[..12], D_FF).mul(eval_lt_const_mle(&z21[16..21], NUM_LAYERS));
        let claim = sw_ev.scale_bb(512).add(rsw_ev).sub(act_mlp.scale_bb(256));
        let (rho, ch, term) = verify_gmask_einsum_ext4(claim, 21, 0, &z21, &sp.prf, &mut tr)?;
        tr.absorb_ext4(b"ss_lr", sp.left_at_r);
        online_claims[2].push(JointLinearClaimExt4::point_eval(M2_GATE_SILU, ch.clone(), sp.left_at_r));
        let (w_sum, w_at) = GMaskExt4::build_spec_weights(&gm_specs, "ss_mlp_swiglu", &ch);
        online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &w_sum, sp.prf.gmask_sum));
        online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: M2_MLP_UP,
                point: ch.clone(),
                weight: eq_mle_ext4(&z21, &ch).mul(sp.left_at_r),
            }],
            gm_limb_ids,
            &w_at,
            rho,
            term,
        ));
    }

    // 18..29: `RMSNorm` `4 × 3` bilinear checks:
    let discharge_rms_xin_ver = |g_idx: usize, pt: &[Ext4], expected_val: Ext4, onl_cl: &mut [Vec<JointLinearClaimExt4>; 4]| {
        match g_idx {
            0 => {
                let s5 = pt[19];
                let pt19 = pt[..19].to_vec();
                onl_cl[2].push(JointLinearClaimExt4 {
                    terms: vec![
                        LinearTermExt4::PointEval { subtable: M2_H_IN, point: pt19.clone(), weight: Ext4::ONE.sub(s5) },
                        LinearTermExt4::PointEval { subtable: M2_H_MID, point: pt19, weight: s5 },
                    ],
                    rhs: expected_val,
                });
            }
            1 => {
                let eq_gk = build_eq_table_lsb_ext4(&pt[15..21]);
                let mut terms = Vec::with_capacity(54);
                let two = Ext4::from_bb(2);
                for g in 0..18 {
                    let g_bits = bits_to_ext4(g, 5);
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_CONV_SILU,
                        point: concat_pts(&[&pt[..11], &[Ext4::ZERO, Ext4::ZERO], &pt[11..15], &g_bits]),
                        weight: two.mul(eq_gk[3 * g]),
                    });
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_CONV_SILU,
                        point: concat_pts(&[&pt[..11], &[Ext4::ONE, Ext4::ZERO], &pt[11..15], &g_bits]),
                        weight: two.mul(eq_gk[3 * g + 1]),
                    });
                    terms.push(LinearTermExt4::PointEval {
                        subtable: M0_Y_WY,
                        point: concat_pts(&[&pt[..15], &g_bits]),
                        weight: eq_gk[3 * g + 2],
                    });
                }
                onl_cl[0].push(JointLinearClaimExt4 { terms, rhs: expected_val });
            }
            _ => {
                let two = Ext4::from_bb(2);
                let (h1, h2, h3) = (pt[9], pt[10], pt[11]);
                onl_cl[1].push(JointLinearClaimExt4 {
                    terms: vec![
                        LinearTermExt4::PointEval {
                            subtable: M1_Q_RAW,
                            point: concat_pts(&[&pt[..11], &pt[12..19]]),
                            weight: two.mul(Ext4::ONE.sub(h3)),
                        },
                        LinearTermExt4::PointEval {
                            subtable: M1_K_RAW,
                            point: concat_pts(&[&pt[..9], &pt[12..19]]),
                            weight: two.mul(h3).mul(Ext4::ONE.sub(h2)).mul(Ext4::ONE.sub(h1)),
                        },
                    ],
                    rhs: expected_val,
                });
            }
        }
    };

    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let b = cfg.grp * RGRP_STRIDE;
        let mf = cfg.log_d + cfg.m_row;
        let mr = cfg.m_row;
        let specs = [
            ["ss_rms0_sq", "ss_rms0_p4u", "ss_rms0_p2r", "ss_rms0_xrho"],
            ["ss_rms1_sq", "ss_rms1_p4u", "ss_rms1_p2r", "ss_rms1_xrho"],
            ["ss_rms2_sq", "ss_rms2_p4u", "ss_rms2_p2r", "ss_rms2_xrho"],
        ][g_idx];

        // sq:
        {
            let sp = &receipt.sec_sec_proofs[ss_idx];
            ss_idx += 1;
            let z_sq = tr.squeeze_ext4_vec(b"rmssq_z", mf, true);
            let sqlo = pull_eval(3, b + RGRP_SQLO, z_sq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let sqhi = pull_eval(3, b + RGRP_SQHI, z_sq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rsq = pull_eval(3, b + RGRP_RSQ, z_sq.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let claim = sqlo.add(sqhi.scale_bb(8192)).scale_bb(16).add(rsq);
            let (rho, ch, term) = verify_gmask_einsum_ext4(claim, mf, 0, &z_sq, &sp.prf, &mut tr)?;
            tr.absorb_ext4(b"ss_lr", sp.left_at_r);
            discharge_rms_xin_ver(g_idx, &ch, sp.left_at_r, &mut online_claims);
            let (ws, wa) = GMaskExt4::build_spec_weights(&gm_specs, specs[0], &ch);
            online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws, sp.prf.gmask_sum));
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(), gm_limb_ids, &wa, rho, term.sub(eq_mle_ext4(&z_sq, &ch).mul(sp.left_at_r).mul(sp.left_at_r)),
            ));
        }
        // p4u:
        {
            let sp = &receipt.sec_sec_proofs[ss_idx];
            ss_idx += 1;
            let z_p4 = tr.squeeze_ext4_vec(b"rmsp4_z", mr, true);
            let mslo = pull_eval(3, b + RGRP_MS_LO, z_p4.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let mshi = pull_eval(3, b + RGRP_MS_HI, z_p4.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rn = pull_eval(3, b + RGRP_RNORM, z_p4.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let claim = mslo.add(mshi.scale_bb(8192)).sub(rn);
            let (rho, ch, term) = verify_gmask_einsum_ext4(claim, mr, 0, &z_p4, &sp.prf, &mut tr)?;
            tr.absorb_ext4(b"ss_lr", sp.left_at_r);
            online_claims[3].push(JointLinearClaimExt4::point_eval(b + RGRP_POW4, ch.clone(), sp.left_at_r));
            let um_ev = pull_eval(3, b + RGRP_UMS, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let (ws, wa) = GMaskExt4::build_spec_weights(&gm_specs, specs[1], &ch);
            online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws, sp.prf.gmask_sum));
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(), gm_limb_ids, &wa, rho, term.sub(eq_mle_ext4(&z_p4, &ch).mul(sp.left_at_r).mul(um_ev)),
            ));
        }
        // p2r:
        {
            let sp = &receipt.sec_sec_proofs[ss_idx];
            ss_idx += 1;
            let z_p2 = tr.squeeze_ext4_vec(b"rmsp2_z", mr, true);
            let rm_ev = pull_eval(3, b + RGRP_RMLUT, z_p2.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let hp_ev = pull_eval(3, b + RGRP_HPOW2, z_p2.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rr_ev = pull_eval(3, b + RGRP_RRHO, z_p2.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let claim = rm_ev.add(hp_ev).sub(rr_ev);
            let (rho, ch, term) = verify_gmask_einsum_ext4(claim, mr, 0, &z_p2, &sp.prf, &mut tr)?;
            tr.absorb_ext4(b"ss_lr", sp.left_at_r);
            online_claims[3].push(JointLinearClaimExt4::point_eval(b + RGRP_POW2, ch.clone(), sp.left_at_r));
            let rlo = pull_eval(3, b + RGRP_RHO_LO, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rhi = pull_eval(3, b + RGRP_RHO_HI, ch.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rho_ev = rlo.add(rhi.scale_bb(4096));
            let (ws, wa) = GMaskExt4::build_spec_weights(&gm_specs, specs[2], &ch);
            online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws, sp.prf.gmask_sum));
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(), gm_limb_ids, &wa, rho, term.sub(eq_mle_ext4(&z_p2, &ch).mul(sp.left_at_r).mul(rho_ev)),
            ));
        }
        // xrho:
        {
            let sp = &receipt.sec_sec_proofs[ss_idx];
            ss_idx += 1;
            let z_xr = tr.squeeze_ext4_vec(b"rmsxr_z", mf, true);
            let uq_ev = pull_eval(3, b + RGRP_UQ9, z_xr.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let ru_ev = pull_eval(3, b + RGRP_RU, z_xr.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let act_r = eval_rms_group_act_mle(g_idx, &z_xr[cfg.log_d..]);
            let claim = uq_ev.scale_bb(2048).add(ru_ev).sub(act_r.scale_bb(1024));
            let (rho, ch, term) = verify_gmask_einsum_ext4(claim, mf, 0, &z_xr, &sp.prf, &mut tr)?;
            tr.absorb_ext4(b"ss_lr", sp.left_at_r);
            discharge_rms_xin_ver(g_idx, &ch, sp.left_at_r, &mut online_claims);
            let r_row_pt = ch[cfg.log_d..].to_vec();
            let rlo = pull_eval(3, b + RGRP_RHO_LO, r_row_pt.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rhi = pull_eval(3, b + RGRP_RHO_HI, r_row_pt, &mut ev_cursor, &mut tr, &mut online_claims)?;
            let rho_ev = rlo.add(rhi.scale_bb(4096));
            let (ws, wa) = GMaskExt4::build_spec_weights(&gm_specs, specs[3], &ch);
            online_claims[2].push(JointLinearClaimExt4::gmask_sum_claim(gm_limb_ids, &ws, sp.prf.gmask_sum));
            online_claims[2].push(JointLinearClaimExt4::hvzk_terminal_weld(
                Vec::new(), gm_limb_ids, &wa, rho, term.sub(eq_mle_ext4(&z_xr, &ch).mul(sp.left_at_r).mul(rho_ev)),
            ));
        }
    }
    debug_assert_eq!(ss_idx, 29);

    // Step F: Direct Zero-Round Linear Welds (`embed_tokens`, padding guards, `ST_H_IN == ST_H_CARRY`, `h_mid`, `h_out`, RMSNorm, GDN, GQA):
    {
        let z_dt = tr.squeeze_ext4_vec(b"emb_zdt", 14, true);
        let h0_ev = pull_eval(2, M2_H_CARRY, concat_pts(&[&z_dt, &bits_to_ext4(0, 5)]), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let eq_t = build_eq_table_lsb_ext4(&z_dt[10..14]);
        let scale_emb_bb = Ext4::from_bb((S_RES / S_W) as u32);
        let mut emb_terms = Vec::with_capacity(16);
        for (t, &tid) in receipt.prompt_tokens.iter().enumerate() {
            emb_terms.push((
                WST_EMBED,
                concat_pts(&[&z_dt[..10], &bits_to_ext4(tid as usize, 18)]),
                scale_emb_bb.mul(eq_t[t]),
            ));
        }
        weight_claims.push(PublicWeightClaim24L { terms: emb_terms, rhs: h0_ev });
    }
    {
        let z_pad = tr.squeeze_ext4_vec(b"pad_zdt", 14, true);
        let g_pad = tr.squeeze_ext4(b"pad_gam", true);
        let mut terms_pad = Vec::with_capacity(22);
        let mut gp = Ext4::ONE;
        for b_idx in 25..32 {
            let pt = concat_pts(&[&z_pad, &bits_to_ext4(b_idx, 5)]);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_IN, point: pt.clone(), weight: gp });
            gp = gp.mul(g_pad);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_CARRY, point: pt, weight: gp });
            gp = gp.mul(g_pad);
        }
        for l_idx in 24..32 {
            let pt = concat_pts(&[&z_pad, &bits_to_ext4(l_idx, 5)]);
            terms_pad.push(LinearTermExt4::PointEval { subtable: M2_H_MID, point: pt, weight: gp });
            gp = gp.mul(g_pad);
        }
        online_claims[2].push(JointLinearClaimExt4 { terms: terms_pad, rhs: Ext4::ZERO });
    }
    {
        let z_weld = tr.squeeze_ext4_vec(b"xlayer_zweld", 19, true);
        online_claims[2].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M2_H_IN, point: z_weld.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M2_H_CARRY, point: z_weld, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ZERO,
        });
    }
    {
        let z_r1 = tr.squeeze_ext4_vec(b"res1_z", 19, true);
        let hm_ev = pull_eval(2, M2_H_MID, z_r1.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let eq_zl = build_eq_table_lsb_ext4(&z_r1[14..19]);

        let hin_val = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"res1_hin", hin_val);
        let hin_terms: Vec<LinearTermExt4> = (0..24)
            .map(|l| LinearTermExt4::PointEval {
                subtable: M2_H_IN,
                point: concat_pts(&[&z_r1[..14], &bits_to_ext4(l, 5)]),
                weight: eq_zl[l],
            })
            .collect();
        online_claims[2].push(JointLinearClaimExt4 { terms: hin_terms, rhs: hin_val });

        let gdn_val = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"res1_gdn", gdn_val);
        let gdn_terms: Vec<LinearTermExt4> = GDN_LAYER_INDICES
            .iter()
            .enumerate()
            .map(|(g, &l)| LinearTermExt4::PointEval {
                subtable: M0_ATTN_OUT,
                point: concat_pts(&[&z_r1[..14], &bits_to_ext4(g, 5)]),
                weight: eq_zl[l],
            })
            .collect();
        online_claims[0].push(JointLinearClaimExt4 { terms: gdn_terms, rhs: gdn_val });

        let gqa_val = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"res1_gqa", gqa_val);
        let gqa_terms: Vec<LinearTermExt4> = GQA_LAYER_INDICES
            .iter()
            .enumerate()
            .map(|(q, &l)| LinearTermExt4::PointEval {
                subtable: M1_ATTN_OUT,
                point: concat_pts(&[&z_r1[..14], &bits_to_ext4(q, 3)]),
                weight: eq_zl[l],
            })
            .collect();
        online_claims[1].push(JointLinearClaimExt4 { terms: gqa_terms, rhs: gqa_val });

        if hm_ev != hin_val.add(gdn_val).add(gqa_val) {
            return Err("layer residual add h_mid == h_in + attn_out failed".into());
        }
    }
    {
        let z_r2 = tr.squeeze_ext4_vec(b"res2_z", 19, true);
        let eq_zl = build_eq_table_lsb_ext4(&z_r2[14..19]);
        let mut terms_r2 = Vec::with_capacity(26);
        for l in 0..24 {
            terms_r2.push(LinearTermExt4::PointEval {
                subtable: M2_H_CARRY,
                point: concat_pts(&[&z_r2[..14], &bits_to_ext4(l + 1, 5)]),
                weight: eq_zl[l],
            });
        }
        terms_r2.push(LinearTermExt4::PointEval { subtable: M2_H_MID, point: z_r2.clone(), weight: Ext4::ONE.neg() });
        terms_r2.push(LinearTermExt4::PointEval { subtable: M2_MLP_OUT, point: z_r2, weight: Ext4::ONE.neg() });
        online_claims[2].push(JointLinearClaimExt4 { terms: terms_r2, rhs: Ext4::ZERO });
    }
    let half_ext = Ext4::from_bb(INV2_BB);
    for (g_idx, cfg) in RMS_CFGS.iter().enumerate() {
        let b = cfg.grp * RGRP_STRIDE;
        let mb = cfg.log_d - 4 + cfg.m_row;
        let mr = cfg.m_row;
        let n_blk = 1u32 << (cfg.log_d - 4);
        let div_ms = (1u32 << cfg.log_d) / 32;

        let z_kr = tr.squeeze_ext4_vec(b"rmsb_z", mb, true);
        let z_sq_half = concat_pts(&[&[half_ext; 4], &z_kr]);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_SQLO, point: z_sq_half.clone(), weight: Ext4::from_bb(16) },
                LinearTermExt4::PointEval { subtable: b + RGRP_SQHI, point: z_sq_half, weight: Ext4::from_bb(16 * 8192) },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_LO, point: z_kr.clone(), weight: Ext4::from_bb(32).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_HI, point: z_kr.clone(), weight: Ext4::from_bb(32 * 8192).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_RB128, point: z_kr, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ZERO,
        });

        let z_ms = tr.squeeze_ext4_vec(b"rmsms_z", mr, true);
        let halfs_k = vec![half_ext; cfg.log_d - 4];
        let z_b_half = concat_pts(&[&halfs_k, &z_ms]);
        let act_r = eval_rms_group_act_mle(g_idx, &z_ms);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_LO, point: z_b_half.clone(), weight: Ext4::from_bb(n_blk) },
                LinearTermExt4::PointEval { subtable: b + RGRP_B128_HI, point: z_b_half, weight: Ext4::from_bb(n_blk * 8192) },
                LinearTermExt4::PointEval { subtable: b + RGRP_MS_LO, point: z_ms.clone(), weight: Ext4::from_bb(div_ms).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_MS_HI, point: z_ms.clone(), weight: Ext4::from_bb(div_ms * 8192).neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_RMS, point: z_ms, weight: Ext4::ONE.neg() },
            ],
            rhs: act_r.scale_bb(div_ms).neg(),
        });

        let z_dr = tr.squeeze_ext4_vec(b"rmsdr_z", mr, true);
        online_claims[3].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: b + RGRP_POW2, point: z_dr.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: b + RGRP_RRHO, point: z_dr.clone(), weight: Ext4::ONE.neg() },
                LinearTermExt4::PointEval { subtable: b + RGRP_DIFF_RHO, point: z_dr, weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ONE,
        });
    }
    {
        let z13 = tr.squeeze_ext4_vec(b"spin_z", 13, true);
        let spin_ev = pull_eval(0, M0_SP_IN, z13.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let a_ev = pull_eval(0, M0_A_PROJ, z13.clone(), &mut ev_cursor, &mut tr, &mut online_claims)?;
        let dt_ev = next_raw_ev(&mut ev_cursor)?;
        tr.absorb_ext4(b"spin_dt", dt_ev);
        let dt_pt = concat_pts(&[&z13[..4], &z13[8..13]]);
        weight_claims.push(PublicWeightClaim24L::point_eval(WST_GDN_DT, dt_pt, dt_ev));
        if spin_ev != a_ev.add(dt_ev) {
            return Err("GDN SP_IN == A_PROJ + DT_BIAS failed".into());
        }

        let z_gd = tr.squeeze_ext4_vec(b"gmd_z", 13, true);
        let (zh, zj, zg) = (&z_gd[..4], &z_gd[4..8], &z_gd[8..13]);
        let eq_zj = build_eq_table_lsb_ext4(zj);
        let d_terms: Vec<LinearTermExt4> = (0..16)
            .map(|j| {
                let jb = bits_to_ext4(j, 4);
                LinearTermExt4::PointEval {
                    subtable: M0_GAMMA,
                    point: concat_pts(&[zh, &jb, &jb, zg]),
                    weight: eq_zj[j],
                }
            })
            .collect();
        online_claims[0].push(JointLinearClaimExt4 {
            terms: d_terms,
            rhs: eval_lt_const_mle(zg, NUM_GDN_LAYERS).scale_bb(512),
        });
    }
    {
        let z10 = tr.squeeze_ext4_vec(b"smrow_z", 10, true);
        let z14_half = concat_pts(&[&[half_ext; 4], &z10]);
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![LinearTermExt4::PointEval {
                subtable: M1_SEL_MAX,
                point: z14_half.clone(),
                weight: Ext4::from_bb(16),
            }],
            rhs: eval_lt_const_mle(&z10[7..10], NUM_GQA_LAYERS),
        });
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_E_SM, point: z14_half, weight: Ext4::from_bb(16) },
                LinearTermExt4::PointEval { subtable: M1_Z_SM, point: z10.clone(), weight: Ext4::ONE.neg() },
            ],
            rhs: Ext4::ZERO,
        });
        online_claims[1].push(JointLinearClaimExt4 {
            terms: vec![
                LinearTermExt4::PointEval { subtable: M1_Z_SM, point: z10.clone(), weight: Ext4::ONE },
                LinearTermExt4::PointEval { subtable: M1_Z_SM_M1, point: z10.clone(), weight: Ext4::ONE.neg() },
            ],
            rhs: eval_lt_const_mle(&z10[7..10], NUM_GQA_LAYERS),
        });
    }

    if ev_cursor != receipt.linear_point_evals.len() {
        return Err("unused linear_point_evals entries in receipt".into());
    }

    // Step G: Verify `WeightModelRoot24L` WHIR opening + 4-Matrix Online ZK WHIR Batch opening!
    verify_public_weight_whir_24l(
        &receipt.model_root.weight_whir_root,
        &pub_w_shape,
        &weight_claims,
        &receipt.weight_whir_proof,
        &mut tr,
    )?;
    verify_whir_batch_ext4(
        &[
            (&receipt.online_roots[0], &shapes[0], &online_claims[0]),
            (&receipt.online_roots[1], &shapes[1], &online_claims[1]),
            (&receipt.online_roots[2], &shapes[2], &online_claims[2]),
            (&receipt.online_roots[3], &shapes[3], &online_claims[3]),
        ],
        ONLINE_WHIR_T_QUERIES,
        &receipt.online_whir_proof,
        &mut tr,
    )?;
    Ok(())
}
