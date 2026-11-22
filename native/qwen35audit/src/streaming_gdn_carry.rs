#![deny(warnings)]
//! Continuous Wearable JITT Multi-Chunk `Qwen3.5` Gated-DeltaNet Recurrent State Carry (`S_c -> S_{c+1}`)
//! over `WhirExt4Pcs + GMaskExt4` (`TVD = 0` Blinded State-Handoff & `O(1)` Live Wearable RAM).
//!
//! Closes Wave-8 §4 `[OPEN]` item 3 (*"cross-chunk recurrent GDN state carry `S_{chunk,c} -> S_{chunk,c+1}`
//! beyond `S_{init} = 0`"*) for *Rainbows End* Wearable SHE Organ #2:
//! - Exact wrap-free integer stateful WY (`M_WY = 512`, `S_SCALE = 512`, all inner products `< 5.42e8 < P/2`)
//!   proving `K_dec · S_c = 512 * W_ks + R_ks - 256`, `(I + L / 512) U_wy = V_beta - W_ks`, and
//!   `S_{c+1} = round((gamma_c · S_c + K_tail^T · U_wy) / 512)` in a single 3-matrix `WhirExt4Pcs` cascade.
//! - Zero unmasked `S_c` or `S_{c+1}` evaluations on the wire (`TVD = 0` dual-mask handoff
//!   `(Delta_M, alpha * S_c(r_h, r_v, r_k) + M_read)` matching `Assurance/StreamingGdnCarryIvc.lean`).
//! - Streaming 24-layer `Qwen/Qwen3.5-0.8B-Base` JITT session (`4 x 64 = 256` tokens) with `0`-bit IEEE-754
//!   and integer state drift vs monolithic 256-token execution while evicting past chunks from RAM.

use crate::ext4::{
    badd, bb_from_i64, bpow, build_eq_suffix_tables_ext4, build_eq_table_lsb_ext4,
    cshake256_32, eq_lin_ext4, eq_mle_ext4, fold_ext4, mle_eval_bb_at_ext4, os_random_seed_32,
    ByteCursor, CShakeRng, CShakeTranscript, Ext4, INV2_BB, P,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, eval_upper_or_diag_indicator_mle, prove_d1b_range_ext4,
    verify_d1b_range_ext4, D1bRangeExt4Proof,
};
use crate::qwen35_layer::{
    dequant_y_raw_to_f32, eval_mxfp4_int_contraction, quantize_act_i16, rmsnorm_zero_centered_f32,
};
use crate::safetensors_mmap::{MmapSafetensors, Mxfp4Matrix, ACT_SCALE};
use crate::whir_ext4::{
    eval_poly_ext4, open_whir_batch_ext4, pack_ext4_slice, prove_gmask_einsum_ext4,
    unpack_ext4_slice, verify_gmask_einsum_ext4, verify_whir_batch_ext4, BlindedEinSumExt4Proof,
    GMaskExt4, GMaskSpecExt4, JointLinearClaimExt4, LinearTermExt4, WhirBatchOpeningProofExt4,
    WhirCommittedMatrixExt4, WhirExt4MatrixShape, WHIR_EXT4_BLOWUP, WHIR_EXT4_T_QUERIES_100,
};
use rayon::prelude::*;

pub const JITT_H_V: usize = 16;
pub const JITT_LOG_H: usize = 4;
pub const JITT_CHUNK_LEN: usize = 64;
pub const JITT_LOG_C: usize = 6;
pub const JITT_D_K: usize = 128;
pub const JITT_D_V: usize = 128;
pub const JITT_LOG_D: usize = 7;

pub const JITT_STATE_CELLS: usize = JITT_H_V * JITT_D_V * JITT_D_K; // 262,144 = 2^18
pub const JITT_STATE_VARS: usize = 18;
pub const JITT_HIV_CELLS: usize = JITT_H_V * JITT_CHUNK_LEN * JITT_D_V; // 131,072 = 2^17
pub const JITT_HIV_VARS: usize = 17;
pub const JITT_SLT_CELLS: usize = JITT_H_V * JITT_CHUNK_LEN * JITT_CHUNK_LEN; // 65,536 = 2^16
pub const JITT_SLT_VARS: usize = 16;

/// Wrap-free fixed-point operator scale `M_WY = 512` (`HALF_WY = 256`) and state scale `S_SCALE = 512`:
/// Worst-case `K_dec · S_c` contraction `128 * 512 * 8192 + 512 * 8192 + 512 = 541,065,728 < P / 2 = 1,006,632,960`!
pub const JITT_M_WY: i64 = 512;
pub const JITT_HALF_WY: i64 = 256;
pub const JITT_S_SCALE: i64 = 512;
pub const JITT_OP_LIMIT: i64 = 512; // `[-512, 511]`
pub const JITT_S_LIMIT: i64 = 8192; // `[-8192, 8191]`
pub const JITT_D1B_TAB_VARS: usize = 14; // `[0, 16384)`
pub const JITT_D1B_WIT_VARS: usize = 22; // `16 * 262,144`
pub const JITT_UPPER_SHIFT_512: u32 = 15_872; // `16384 - 512 = 15872`

const JITT_CARRY_MAGIC: &[u8; 8] = b"JITTGDN1";
const JITT_CHAIN_DOM: &[u8] = b"QW35-JITT-CHAIN-V1";
const JITT_TOK_DOM: &[u8] = b"QW35-JITT-CHUNK-TOK-V1";
const JITT_TRANSCRIPT_DOM: &[u8] = b"QW35-STREAMING-GDN-CARRY-V1";

// ================================================================================================
// §1. Persistent GDN Fast-Weight State (`16 x 128 x 128`) & `TVD = 0` Salted WHIR Commitment
// ================================================================================================

/// Persistent `16 x 128 x 128` (`1.00 MiB` `u32` / `2.00 MiB` `i64`) Gated-DeltaNet fast-weight state
/// indexed in LSB-first hypercube order `idx = h + (j_v << 4) + (i_k << 11)` matching `S_c(r_h, r_v, r_k)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GdnRecurrentState {
    pub s_int_hvk: Vec<i64>,
    pub s_bb_hvk: Vec<u32>,
}

impl GdnRecurrentState {
    pub fn zero() -> Self {
        Self {
            s_int_hvk: vec![0i64; JITT_STATE_CELLS],
            s_bb_hvk: vec![0u32; JITT_STATE_CELLS],
        }
    }

    pub fn from_int_hvk(s_int_hvk: Vec<i64>) -> Result<Self, String> {
        if s_int_hvk.len() != JITT_STATE_CELLS {
            return Err(format!("expected {JITT_STATE_CELLS} state cells, got {}", s_int_hvk.len()));
        }
        for (idx, &v) in s_int_hvk.iter().enumerate() {
            if !(-JITT_S_LIMIT..JITT_S_LIMIT).contains(&v) {
                return Err(format!("state cell {idx} = {v} outside [-{JITT_S_LIMIT}, {JITT_S_LIMIT})"));
            }
        }
        let s_bb_hvk = s_int_hvk.iter().map(|&v| bb_from_i64(v)).collect();
        Ok(Self { s_int_hvk, s_bb_hvk })
    }

    #[inline]
    pub fn live_ram_bytes(&self) -> usize {
        self.s_bb_hvk.len() * std::mem::size_of::<u32>()
    }
}

/// Salted `WhirExt4Pcs` state commitment `rt_{S,c}` carrying one-time write/read `Ext4` masks
/// (`slot 0: M_write_upd`, `slot 1: M_write_d1b`, `slot 2: M_read_wy`, `slot 3: M_read_upd`, `slot 4: M_read_d1b`)
/// so NO mask is ever reused across chunks or claims (`TVD = 0`).
pub struct SaltedGdnStateCommitment {
    pub state: GdnRecurrentState,
    pub masks: [Ext4; 64],
    pub whir_mat: WhirCommittedMatrixExt4,
}

impl SaltedGdnStateCommitment {
    pub fn expected_shape() -> WhirExt4MatrixShape {
        WhirExt4MatrixShape::for_subtables(&[JITT_STATE_VARS, 6, 6, 6, 6], true, WHIR_EXT4_BLOWUP)
    }

    pub fn commit(state: GdnRecurrentState, opt_seed: Option<[u8; 32]>) -> Self {
        let seed = opt_seed.unwrap_or_else(os_random_seed_32);
        let mut mask_rng = CShakeRng::from_seed(b"QW35-JITT-STATE-MASKS-V1", &seed);
        let masks: [Ext4; 64] = std::array::from_fn(|_| {
            Ext4([
                mask_rng.next_bb(),
                mask_rng.next_bb(),
                mask_rng.next_bb(),
                mask_rng.next_bb(),
            ])
        });
        let mut limbs: [Vec<u32>; 4] = std::array::from_fn(|_| vec![0u32; 64]);
        for (i, m) in masks.iter().enumerate() {
            for l in 0..4 {
                limbs[l][i] = m.0[l];
            }
        }
        let mut pcs_seed = [0u8; 32];
        mask_rng.fill_bytes(&mut pcs_seed);
        let whir_mat = WhirCommittedMatrixExt4::commit_with_shape(
            Self::expected_shape(),
            &[
                &state.s_bb_hvk,
                &limbs[0],
                &limbs[1],
                &limbs[2],
                &limbs[3],
            ],
            Some(pcs_seed),
        );
        Self {
            state,
            masks,
            whir_mat,
        }
    }

    #[inline]
    pub fn root(&self) -> [u8; 32] {
        self.whir_mat.root
    }
}

// ================================================================================================
// §2. Exact Integer Stateful `C = 64` Chunkwise WY Solver (`S_c -> S_{c+1}`)
// ================================================================================================

#[derive(Clone, Debug)]
pub struct StatefulGdnCarryWitness {
    pub gamma_int_16: [u16; JITT_H_V],
    pub k_dec_lsb_hik: Vec<u32>,
    pub k_tail_lsb_hik: Vec<u32>,
    pub v_beta_lsb_hiv: Vec<u32>,
    pub w_ks_lsb_hiv: Vec<u32>,
    pub u_wy_lsb_hiv: Vec<u32>,
    pub r_ks_lsb_hiv: Vec<u32>,
    pub r_wy_lsb_hiv: Vec<u32>,
    pub r_st_lsb_hvk: Vec<u32>,
    pub l_lsb_hij: Vec<u32>,
    pub s_out: GdnRecurrentState,
    pub y_out_f32: Vec<f32>,
}

/// Solve exact wrap-free integer stateful `C = 64` chunkwise WY for `S_c -> S_{c+1}`:
/// 1. `K_dec · S_c = 512 * W_ks + R_ks - 256` (`W_ks` accounts for non-zero incoming state `S_c`!)
/// 2. `L · U_wy = 512 * (V_beta - W_ks - U_wy) + 256 - R_wy` (`(I + L / 512) U_wy = V_beta - W_ks`)
/// 3. `K_tail^T · U_wy = 512 * S_{c+1} - gamma_int * S_c + R_st - 256`
/// 4. Intra-chunk readout `Y = (diag(gamma) Q · S_c + ((Q K^T) ⊙ Gamma) · U_wy) / S_SCALE`.
pub fn solve_stateful_gdn_wy_chunk64(
    q_f32: &[f32],
    k_f32: &[f32],
    v_f32: &[f32],
    g_f32: &[f32],
    beta_f32: &[f32],
    s_in: &GdnRecurrentState,
) -> StatefulGdnCarryWitness {
    assert_eq!(q_f32.len(), JITT_CHUNK_LEN * JITT_H_V * JITT_D_K);
    assert_eq!(k_f32.len(), JITT_CHUNK_LEN * JITT_H_V * JITT_D_K);
    assert_eq!(v_f32.len(), JITT_CHUNK_LEN * JITT_H_V * JITT_D_V);
    assert_eq!(g_f32.len(), JITT_CHUNK_LEN * JITT_H_V);
    assert_eq!(beta_f32.len(), JITT_CHUNK_LEN * JITT_H_V);

    let mut gamma_int_16 = [0u16; JITT_H_V];
    let mut k_dec_lsb_hik = vec![0u32; JITT_HIV_CELLS];
    let mut k_tail_lsb_hik = vec![0u32; JITT_HIV_CELLS];
    let mut v_beta_lsb_hiv = vec![0u32; JITT_HIV_CELLS];
    let mut w_ks_lsb_hiv = vec![0u32; JITT_HIV_CELLS];
    let mut u_wy_lsb_hiv = vec![0u32; JITT_HIV_CELLS];
    let mut r_ks_lsb_hiv = vec![0u32; JITT_HIV_CELLS];
    let mut r_wy_lsb_hiv = vec![0u32; JITT_HIV_CELLS];
    let mut r_st_lsb_hvk = vec![0u32; JITT_STATE_CELLS];
    let mut l_lsb_hij = vec![0u32; JITT_SLT_CELLS];
    let mut s_out_int = vec![0i64; JITT_STATE_CELLS];
    let mut y_out_f32 = vec![0.0f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_V];

    struct HeadOut {
        gamma_int: u16,
        k_dec: Vec<i64>,
        k_tail: Vec<i64>,
        v_beta: Vec<i64>,
        w_ks: Vec<i64>,
        u_wy: Vec<i64>,
        r_ks: Vec<u32>,
        r_wy: Vec<u32>,
        r_st: Vec<u32>,
        l_mat: Vec<i64>,
        s_next: Vec<i64>,
        y_h: Vec<f32>,
    }

    let per_head: Vec<HeadOut> = (0..JITT_H_V)
        .into_par_iter()
        .map(|h| {
            let scale_q = 1.0 / (JITT_D_K as f32).sqrt();
            let mut q_h = vec![0.0f32; JITT_CHUNK_LEN * JITT_D_K];
            let mut k_h = vec![0.0f32; JITT_CHUNK_LEN * JITT_D_K];
            let mut v_h = vec![0.0f32; JITT_CHUNK_LEN * JITT_D_V];
            let mut alpha_h = vec![0.0f32; JITT_CHUNK_LEN];
            let mut beta_h = vec![0.0f32; JITT_CHUNK_LEN];

            for t in 0..JITT_CHUNK_LEN {
                let off_d = (t * JITT_H_V + h) * JITT_D_K;
                let q_src = &q_f32[off_d..off_d + JITT_D_K];
                let k_src = &k_f32[off_d..off_d + JITT_D_K];
                let v_src = &v_f32[off_d..off_d + JITT_D_V];
                let q_inv = 1.0 / (q_src.iter().map(|&x| x * x).sum::<f32>() + 1e-6).sqrt();
                let k_inv = 1.0 / (k_src.iter().map(|&x| x * x).sum::<f32>() + 1e-6).sqrt();
                for d in 0..JITT_D_K {
                    q_h[t * JITT_D_K + d] = q_src[d] * q_inv * scale_q;
                    k_h[t * JITT_D_K + d] = k_src[d] * k_inv;
                }
                v_h[t * JITT_D_V..(t + 1) * JITT_D_V].copy_from_slice(v_src);
                alpha_h[t] = g_f32[t * JITT_H_V + h].exp().clamp(0.0, 1.0);
                beta_h[t] = beta_f32[t * JITT_H_V + h].clamp(0.0, 1.0);
            }

            let mut gamma_pfx = vec![0.0f32; JITT_CHUNK_LEN];
            let mut gamma_tail = vec![0.0f32; JITT_CHUNK_LEN];
            let mut cap_gamma = vec![0.0f32; JITT_CHUNK_LEN * JITT_CHUNK_LEN];
            let mut pref = 1.0f32;
            for i in 0..JITT_CHUNK_LEN {
                pref *= alpha_h[i];
                gamma_pfx[i] = pref;
                cap_gamma[i * JITT_CHUNK_LEN + i] = 1.0;
                let mut pij = 1.0f32;
                for j in (0..i).rev() {
                    pij *= alpha_h[j + 1];
                    cap_gamma[i * JITT_CHUNK_LEN + j] = pij;
                }
            }
            let mut tail = 1.0f32;
            for i in (0..JITT_CHUNK_LEN).rev() {
                gamma_tail[i] = tail;
                tail *= alpha_h[i];
            }
            let gamma_int = ((JITT_M_WY as f32) * pref).round().clamp(0.0, JITT_M_WY as f32) as u16;

            let clamp_op = |v: f32| -> i64 {
                (v.round() as i64).clamp(-JITT_OP_LIMIT, JITT_OP_LIMIT - 1)
            };
            let clamp_s = |v: f32| -> i64 {
                (v.round() as i64).clamp(-(JITT_S_LIMIT - 1024), JITT_S_LIMIT - 1024)
            };

            let mut l_mat = vec![0i64; JITT_CHUNK_LEN * JITT_CHUNK_LEN];
            for i in 1..JITT_CHUNK_LEN {
                let bi = beta_h[i];
                for j in 0..i {
                    let mut dot_kk = 0.0f32;
                    for d in 0..JITT_D_K {
                        dot_kk += k_h[i * JITT_D_K + d] * k_h[j * JITT_D_K + d];
                    }
                    l_mat[i * JITT_CHUNK_LEN + j] =
                        clamp_op((JITT_M_WY as f32) * bi * cap_gamma[i * JITT_CHUNK_LEN + j] * dot_kk);
                }
            }

            let mut k_dec = vec![0i64; JITT_CHUNK_LEN * JITT_D_K];
            let mut k_tail = vec![0i64; JITT_CHUNK_LEN * JITT_D_K];
            let mut v_beta = vec![0i64; JITT_CHUNK_LEN * JITT_D_V];
            for i in 0..JITT_CHUNK_LEN {
                let bi = beta_h[i];
                let b_gp = bi * gamma_pfx[i];
                let gt = gamma_tail[i];
                for x in 0..JITT_D_K {
                    k_dec[i * JITT_D_K + x] = clamp_op((JITT_M_WY as f32) * b_gp * k_h[i * JITT_D_K + x]);
                    k_tail[i * JITT_D_K + x] = clamp_op((JITT_M_WY as f32) * gt * k_h[i * JITT_D_K + x]);
                }
                for d in 0..JITT_D_V {
                    v_beta[i * JITT_D_V + d] = clamp_s((JITT_S_SCALE as f32) * bi * v_h[i * JITT_D_V + d]);
                }
            }

            // 1. Incoming `K_dec · S_c = 512 * W_ks + R_ks - 256`
            let mut w_ks = vec![0i64; JITT_CHUNK_LEN * JITT_D_V];
            let mut r_ks = vec![0u32; JITT_CHUNK_LEN * JITT_D_V];
            for i in 0..JITT_CHUNK_LEN {
                for j_v in 0..JITT_D_V {
                    let mut sum_ks = 0i64;
                    let base_s = h + (j_v << JITT_LOG_H);
                    for i_k in 0..JITT_D_K {
                        let s_val = s_in.s_int_hvk[base_s + (i_k << (JITT_LOG_H + JITT_LOG_D))];
                        sum_ks += k_dec[i * JITT_D_K + i_k] * s_val;
                    }
                    assert!(sum_ks.abs() < (P as i64) / 2);
                    let num = sum_ks + JITT_HALF_WY;
                    let w_val = num.div_euclid(JITT_M_WY);
                    let rem_val = num.rem_euclid(JITT_M_WY) as u32;
                    assert!((-JITT_S_LIMIT..JITT_S_LIMIT).contains(&w_val));
                    w_ks[i * JITT_D_V + j_v] = w_val;
                    r_ks[i * JITT_D_V + j_v] = rem_val;
                }
            }

            // 2. Stateful WY forward substitution `(I + L / 512) U_wy = V_beta - W_ks`
            let mut u_wy = vec![0i64; JITT_CHUNK_LEN * JITT_D_V];
            let mut r_wy = vec![0u32; JITT_CHUNK_LEN * JITT_D_V];
            for i in 0..JITT_CHUNK_LEN {
                for j_v in 0..JITT_D_V {
                    let mut sum_lu = 0i64;
                    for j in 0..i {
                        sum_lu += l_mat[i * JITT_CHUNK_LEN + j] * u_wy[j * JITT_D_V + j_v];
                    }
                    assert!(sum_lu.abs() < (P as i64) / 2);
                    let rhs_ij = v_beta[i * JITT_D_V + j_v] - w_ks[i * JITT_D_V + j_v];
                    let num = JITT_M_WY * rhs_ij - sum_lu + JITT_HALF_WY;
                    let u_val = num.div_euclid(JITT_M_WY);
                    let rem_val = num.rem_euclid(JITT_M_WY) as u32;
                    assert!((-JITT_S_LIMIT..JITT_S_LIMIT).contains(&u_val));
                    u_wy[i * JITT_D_V + j_v] = u_val;
                    r_wy[i * JITT_D_V + j_v] = rem_val;
                }
            }

            // 3. Outgoing state `S_{c+1} = round((gamma_int * S_c + K_tail^T · U_wy) / 512)`
            let mut s_next = vec![0i64; JITT_D_V * JITT_D_K];
            let mut r_st = vec![0u32; JITT_D_V * JITT_D_K];
            for j_v in 0..JITT_D_V {
                for i_k in 0..JITT_D_K {
                    let mut sum_ku = 0i64;
                    for i in 0..JITT_CHUNK_LEN {
                        sum_ku += k_tail[i * JITT_D_K + i_k] * u_wy[i * JITT_D_V + j_v];
                    }
                    assert!(sum_ku.abs() < (P as i64) / 2);
                    let s_prev = s_in.s_int_hvk[h + (j_v << JITT_LOG_H) + (i_k << (JITT_LOG_H + JITT_LOG_D))];
                    let num = (gamma_int as i64) * s_prev + sum_ku + JITT_HALF_WY;
                    let sn = num.div_euclid(JITT_M_WY);
                    let rem_val = num.rem_euclid(JITT_M_WY) as u32;
                    assert!((-JITT_S_LIMIT..JITT_S_LIMIT).contains(&sn));
                    s_next[j_v * JITT_D_K + i_k] = sn;
                    r_st[j_v * JITT_D_K + i_k] = rem_val;
                }
            }

            // 4. Stateful intra-chunk readout `Y = (diag(gamma_pfx) Q · S_c + ((Q K^T) ⊙ Gamma) · U_wy) / S_SCALE`
            let inv_s_scale = 1.0 / (JITT_S_SCALE as f32);
            let mut y_h = vec![0.0f32; JITT_CHUNK_LEN * JITT_D_V];
            for i in 0..JITT_CHUNK_LEN {
                let gp = gamma_pfx[i] * inv_s_scale;
                for j_v in 0..JITT_D_V {
                    let mut dot_qs = 0.0f32;
                    let base_s = h + (j_v << JITT_LOG_H);
                    for i_k in 0..JITT_D_K {
                        let s_prev = s_in.s_int_hvk[base_s + (i_k << (JITT_LOG_H + JITT_LOG_D))] as f32;
                        dot_qs += q_h[i * JITT_D_K + i_k] * s_prev;
                    }
                    y_h[i * JITT_D_V + j_v] = gp * dot_qs;
                }
                for j in 0..=i {
                    let mut dot_qk = 0.0f32;
                    for i_k in 0..JITT_D_K {
                        dot_qk += q_h[i * JITT_D_K + i_k] * k_h[j * JITT_D_K + i_k];
                    }
                    let attn_ij = dot_qk * cap_gamma[i * JITT_CHUNK_LEN + j] * inv_s_scale;
                    for j_v in 0..JITT_D_V {
                        y_h[i * JITT_D_V + j_v] += attn_ij * (u_wy[j * JITT_D_V + j_v] as f32);
                    }
                }
            }

            HeadOut {
                gamma_int,
                k_dec,
                k_tail,
                v_beta,
                w_ks,
                u_wy,
                r_ks,
                r_wy,
                r_st,
                l_mat,
                s_next,
                y_h,
            }
        })
        .collect();

    for (h, ho) in per_head.into_iter().enumerate() {
        gamma_int_16[h] = ho.gamma_int;
        for i in 0..JITT_CHUNK_LEN {
            for j in 0..JITT_CHUNK_LEN {
                let idx_hij = h + (i << JITT_LOG_H) + (j << (JITT_LOG_H + JITT_LOG_C));
                l_lsb_hij[idx_hij] = bb_from_i64(ho.l_mat[i * JITT_CHUNK_LEN + j]);
            }
            for x in 0..JITT_D_K {
                let idx_hik = h + (i << JITT_LOG_H) + (x << (JITT_LOG_H + JITT_LOG_C));
                k_dec_lsb_hik[idx_hik] = bb_from_i64(ho.k_dec[i * JITT_D_K + x]);
                k_tail_lsb_hik[idx_hik] = bb_from_i64(ho.k_tail[i * JITT_D_K + x]);
            }
            for d in 0..JITT_D_V {
                let idx_hiv = h + (i << JITT_LOG_H) + (d << (JITT_LOG_H + JITT_LOG_C));
                v_beta_lsb_hiv[idx_hiv] = bb_from_i64(ho.v_beta[i * JITT_D_V + d]);
                w_ks_lsb_hiv[idx_hiv] = bb_from_i64(ho.w_ks[i * JITT_D_V + d]);
                u_wy_lsb_hiv[idx_hiv] = bb_from_i64(ho.u_wy[i * JITT_D_V + d]);
                r_ks_lsb_hiv[idx_hiv] = ho.r_ks[i * JITT_D_V + d];
                r_wy_lsb_hiv[idx_hiv] = ho.r_wy[i * JITT_D_V + d];
            }
            let dst_off = (i * JITT_H_V + h) * JITT_D_V;
            y_out_f32[dst_off..dst_off + JITT_D_V]
                .copy_from_slice(&ho.y_h[i * JITT_D_V..(i + 1) * JITT_D_V]);
        }
        for j_v in 0..JITT_D_V {
            for i_k in 0..JITT_D_K {
                let idx_hvk = h + (j_v << JITT_LOG_H) + (i_k << (JITT_LOG_H + JITT_LOG_D));
                s_out_int[idx_hvk] = ho.s_next[j_v * JITT_D_K + i_k];
                r_st_lsb_hvk[idx_hvk] = ho.r_st[j_v * JITT_D_K + i_k];
            }
        }
    }

    StatefulGdnCarryWitness {
        gamma_int_16,
        k_dec_lsb_hik,
        k_tail_lsb_hik,
        v_beta_lsb_hiv,
        w_ks_lsb_hiv,
        u_wy_lsb_hiv,
        r_ks_lsb_hiv,
        r_wy_lsb_hiv,
        r_st_lsb_hvk,
        l_lsb_hij,
        s_out: GdnRecurrentState::from_int_hvk(s_out_int).expect("wrap-free s_out_int in [-8192, 8192)"),
        y_out_f32,
    }
}

// ================================================================================================
// §3. `WhirExt4Pcs + GMaskExt4` Prover & `< 25 ms` Standalone Verifier (`TVD = 0` Boundary)
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingCarryChunkHeader {
    pub session_id: [u8; 32],
    pub model_weight_root: [u8; 32],
    pub layer_idx: u32,
    pub chunk_idx: u32,
    pub s_in_root: [u8; 32],
    pub s_out_root: [u8; 32],
    pub gamma_int_16: [u16; JITT_H_V],
    pub chunk_tok_commit: [u8; 32],
}

impl StreamingCarryChunkHeader {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.model_weight_root);
        out.extend_from_slice(&self.layer_idx.to_le_bytes());
        out.extend_from_slice(&self.chunk_idx.to_le_bytes());
        out.extend_from_slice(&self.s_in_root);
        out.extend_from_slice(&self.s_out_root);
        for &g in &self.gamma_int_16 {
            out.extend_from_slice(&g.to_le_bytes());
        }
        out.extend_from_slice(&self.chunk_tok_commit);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let session_id = cur.read_arr32()?;
        let model_weight_root = cur.read_arr32()?;
        let layer_idx = cur.read_u32()?;
        let chunk_idx = cur.read_u32()?;
        let s_in_root = cur.read_arr32()?;
        let s_out_root = cur.read_arr32()?;
        let mut gamma_int_16 = [0u16; JITT_H_V];
        for slot in &mut gamma_int_16 {
            let b = cur.read_exact(2)?;
            *slot = u16::from_le_bytes([b[0], b[1]]);
        }
        let chunk_tok_commit = cur.read_arr32()?;
        Ok(Self {
            session_id,
            model_weight_root,
            layer_idx,
            chunk_idx,
            s_in_root,
            s_out_root,
            gamma_int_16,
            chunk_tok_commit,
        })
    }

    fn absorb_into(&self, tr: &mut CShakeTranscript) {
        tr.absorb_root(b"jitt_sess", &self.session_id);
        tr.absorb_root(b"jitt_wroot", &self.model_weight_root);
        tr.absorb_u32(b"jitt_layer", self.layer_idx);
        tr.absorb_u32(b"jitt_chunk", self.chunk_idx);
        tr.absorb_root(b"jitt_sin", &self.s_in_root);
        tr.absorb_root(b"jitt_sout", &self.s_out_root);
        for &g in &self.gamma_int_16 {
            tr.absorb_u32(b"jitt_gamma", g as u32);
        }
        tr.absorb_root(b"jitt_tokc", &self.chunk_tok_commit);
    }
}

pub fn compute_chunk_token_commitment(
    session_id: &[u8; 32],
    chunk_idx: u32,
    tokens: &[u32],
) -> [u8; 32] {
    let mut buf = Vec::with_capacity(36 + tokens.len() * 4);
    buf.extend_from_slice(session_id);
    buf.extend_from_slice(&chunk_idx.to_le_bytes());
    for &t in tokens {
        buf.extend_from_slice(&t.to_le_bytes());
    }
    cshake256_32(JITT_TOK_DOM, &buf)
}

pub fn step_jitt_chain_digest(prev_chain: &[u8; 32], hdr: &StreamingCarryChunkHeader) -> [u8; 32] {
    let mut buf = Vec::with_capacity(32 + 200);
    buf.extend_from_slice(prev_chain);
    hdr.write_to(&mut buf);
    cshake256_32(JITT_CHAIN_DOM, &buf)
}

/// Succinct `WhirExt4Pcs + GMaskExt4` receipt proving `S_c -> S_{c+1}` with `TVD = 0` blinded handoff.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamingGdnCarryReceipt {
    pub header: StreamingCarryChunkHeader,
    pub online_root: [u8; 32],
    /// Pre-challenge dual-mask differences `[Delta_wy, Delta_in_upd, Delta_out_upd, Delta_in_d1b, Delta_out_d1b]`.
    pub delta_masks: [Ext4; 5],

    // Section A (`K_dec · S_c = 512 * W_ks + R_ks - 256` + `TVD = 0` `mu_wy`):
    pub w_ks_eval: Ext4,
    pub r_ks_eval: Ext4,
    pub ks_sc_prf: BlindedEinSumExt4Proof,
    pub k_dec_at_r: Ext4,
    pub mu_wy: Ext4,

    // Section B (`(I + L / 512) U_wy = V_beta - W_ks` + `(1 - SLT) ⊙ L == 0`):
    pub v_beta_wy_eval: Ext4,
    pub w_ks_wy_eval: Ext4,
    pub u_wy_eval: Ext4,
    pub r_wy_eval: Ext4,
    pub wy_sc_prf: BlindedEinSumExt4Proof,
    pub wy_l_at_r: Ext4,
    pub wy_u_at_r: Ext4,
    pub slt_sc_prf: BlindedEinSumExt4Proof,

    // Section C (`S_{c+1} = round((gamma_c · S_c + K_tail^T · U_wy) / 512)` + `TVD = 0` `mu_in_upd, mu_out_upd`):
    pub mu_in_upd: Ext4,
    pub mu_out_upd: Ext4,
    pub masked_claim_st: Ext4,
    pub st_sc_prf: BlindedEinSumExt4Proof,
    pub k_tail_at_r: Ext4,
    pub st_u_at_r: Ext4,

    // Section D (Consolidated `[0, 16384)` `D1b` wrap-free bounds + `TVD = 0` `mu_in_d1b, mu_out_d1b`):
    pub d1b_proof: D1bRangeExt4Proof,
    pub mu_in_d1b: Ext4,
    pub mu_out_d1b: Ext4,

    // Shared 3-matrix `WhirExt4Pcs` opening cascade (`chunk_online_mat`, `s_in_mat`, `s_out_mat`):
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

impl StreamingGdnCarryReceipt {
    pub fn expected_online_shape() -> WhirExt4MatrixShape {
        WhirExt4MatrixShape::for_subtables(
            &[
                JITT_HIV_VARS,   // 0: K_dec
                JITT_HIV_VARS,   // 1: K_tail
                JITT_HIV_VARS,   // 2: V_beta
                JITT_HIV_VARS,   // 3: W_ks
                JITT_HIV_VARS,   // 4: U_wy
                JITT_HIV_VARS,   // 5: R_ks
                JITT_HIV_VARS,   // 6: R_wy
                JITT_STATE_VARS, // 7: R_st
                JITT_STATE_VARS, // 8: d1b_mask_18
                JITT_SLT_VARS,   // 9: L
                JITT_D1B_TAB_VARS, // 10: mult_d16384
                6, 6, 6, 6,      // 11..=14: online_masks[0..64]
                8, 8, 8, 8,      // 15..=18: ext_gmask limbs
            ],
            true,
            WHIR_EXT4_BLOWUP,
        )
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(420 * 1024);
        out.extend_from_slice(JITT_CARRY_MAGIC);
        self.header.write_to(&mut out);
        out.extend_from_slice(&self.online_root);
        let mut scalars = Vec::with_capacity(22);
        scalars.extend_from_slice(&self.delta_masks);
        scalars.extend_from_slice(&[
            self.w_ks_eval,
            self.r_ks_eval,
            self.k_dec_at_r,
            self.mu_wy,
            self.v_beta_wy_eval,
            self.w_ks_wy_eval,
            self.u_wy_eval,
            self.r_wy_eval,
            self.wy_l_at_r,
            self.wy_u_at_r,
            self.mu_in_upd,
            self.mu_out_upd,
            self.masked_claim_st,
            self.k_tail_at_r,
            self.st_u_at_r,
            self.mu_in_d1b,
            self.mu_out_d1b,
        ]);
        pack_ext4_slice(&scalars, &mut out);
        self.ks_sc_prf.write_to(&mut out);
        self.wy_sc_prf.write_to(&mut out);
        self.slt_sc_prf.write_to(&mut out);
        self.st_sc_prf.write_to(&mut out);
        self.d1b_proof.write_to(&mut out);
        self.whir_batch_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != JITT_CARRY_MAGIC {
            return Err("invalid StreamingGdnCarryReceipt magic".into());
        }
        let header = StreamingCarryChunkHeader::read_from(&mut cur)?;
        let online_root = cur.read_arr32()?;
        let sc = unpack_ext4_slice(&mut cur, 22)?;
        if sc.len() != 22 {
            return Err("StreamingGdnCarryReceipt scalar count mismatch".into());
        }
        let delta_masks = [sc[0], sc[1], sc[2], sc[3], sc[4]];
        let ks_sc_prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let wy_sc_prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let slt_sc_prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let st_sc_prf = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let whir_batch_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in StreamingGdnCarryReceipt".into());
        }
        Ok(Self {
            header,
            online_root,
            delta_masks,
            w_ks_eval: sc[5],
            r_ks_eval: sc[6],
            ks_sc_prf,
            k_dec_at_r: sc[7],
            mu_wy: sc[8],
            v_beta_wy_eval: sc[9],
            w_ks_wy_eval: sc[10],
            u_wy_eval: sc[11],
            r_wy_eval: sc[12],
            wy_sc_prf,
            wy_l_at_r: sc[13],
            wy_u_at_r: sc[14],
            slt_sc_prf,
            mu_in_upd: sc[15],
            mu_out_upd: sc[16],
            masked_claim_st: sc[17],
            st_sc_prf,
            k_tail_at_r: sc[18],
            st_u_at_r: sc[19],
            d1b_proof,
            mu_in_d1b: sc[20],
            mu_out_d1b: sc[21],
            whir_batch_proof,
        })
    }
}

#[inline]
fn squeeze_nonzero_ext4(tr: &mut CShakeTranscript, label: &[u8]) -> Ext4 {
    loop {
        let x = tr.squeeze_ext4(label, true);
        if !x.is_zero() {
            return x;
        }
    }
}

fn mask_slot_terms_6(limb_subtables: [usize; 4], slot: usize, weight: Ext4) -> Vec<LinearTermExt4> {
    assert!(slot < 64);
    let e_basis = [
        Ext4([1, 0, 0, 0]),
        Ext4([0, 1, 0, 0]),
        Ext4([0, 0, 1, 0]),
        Ext4([0, 0, 0, 1]),
    ];
    let pt: Vec<Ext4> = (0..6)
        .map(|b| if ((slot >> b) & 1) == 1 { Ext4::ONE } else { Ext4::ZERO })
        .collect();
    (0..4)
        .map(|l| LinearTermExt4::PointEval {
            subtable: limb_subtables[l],
            point: pt.clone(),
            weight: weight.mul(e_basis[l]),
        })
        .collect()
}

fn bits4_point(h: usize) -> [Ext4; 4] {
    std::array::from_fn(|b| if ((h >> b) & 1) == 1 { Ext4::ONE } else { Ext4::ZERO })
}

#[inline]
fn cubic_from_evals_local(p0: Ext4, p1: Ext4, p2: Ext4, p_inf: Ext4) -> [Ext4; 4] {
    let six_c3 = p_inf.scale_bb(6);
    let two_p1 = p1.add(p1);
    let c2 = p2.sub(two_p1).add(p0).sub(six_c3).scale_bb(INV2_BB);
    let c1 = p1.sub(p0).sub(c2).sub(p_inf);
    [p0, c1, c2, p_inf]
}

/// Blinded `EinSumcheck` with an additive constant hypercube shift `2^{-m} * claim_mask` so the
/// verifier runs `verify_gmask_einsum_ext4(unmasked_claim + claim_mask, ...)` with `0` unmasked claim leakage!
#[allow(clippy::too_many_arguments)]
fn prove_claim_masked_gmask_einsum_ext4(
    left_tab: &[Ext4],
    right_tab: &[Ext4],
    mu_s: usize,
    kappa: usize,
    z_s: &[Ext4],
    claim_mask: Ext4,
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
    let mut cur_mask_shift = claim_mask;

    for u in 0..mu_s {
        cur_mask_shift = cur_mask_shift.scale_bb(INV2_BB);
        let suf = &suf_tables[mu_s - 1 - u];
        let rem_h_pairs = suf.len();
        let nk = 1usize << kappa;
        let stride_p = rem_h_pairs * 2;
        let (mut q0, mut q1, mut q2, mut q_inf) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for h_rem in 0..rem_h_pairs {
            let w = suf[h_rem];
            let (mut s0, mut s1, mut s2, mut sinf) =
                (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
            for q in 0..nk {
                let idx0 = q * stride_p + 2 * h_rem;
                let (a0, a1) = (l_cur[idx0], l_cur[idx0 + 1]);
                let (b0, b1) = (r_cur[idx0], r_cur[idx0 + 1]);
                let da = a1.sub(a0);
                let db = b1.sub(b0);
                s0 = s0.add(a0.mul(b0));
                s1 = s1.add(a1.mul(b1));
                s2 = s2.add(a1.add(da).mul(b1.add(db)));
                sinf = sinf.add(da.mul(db));
            }
            q0 = q0.add(w.mul(s0));
            q1 = q1.add(w.mul(s1));
            q2 = q2.add(w.mul(s2));
            q_inf = q_inf.add(w.mul(sinf));
        }
        let zu = z_s[u];
        let eq0 = prefix_eq.mul(Ext4::ONE.sub(zu));
        let eq1 = prefix_eq.mul(zu);
        let eq2 = prefix_eq.mul(zu.scale_bb(3).sub(Ext4::ONE));
        let eq_slope = prefix_eq.mul(zu.add(zu).sub(Ext4::ONE));
        let mut unmasked = cubic_from_evals_local(
            eq0.mul(q0),
            eq1.mul(q1),
            eq2.mul(q2),
            eq_slope.mul(q_inf),
        );
        unmasked[0] = unmasked[0].add(cur_mask_shift);
        let bv = gmask.blind_round_poly(spec_name, u, &challenges, rho, &unmasked);
        let blinded = [bv[0], bv[1], bv[2], bv[3]];
        tr.absorb_ext4_slice(b"gm_es_rd", &blinded);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        rounds.push(blinded);
        challenges.push(ch);
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
        prefix_eq = prefix_eq.mul(eq_lin_ext4(zu, ch));
    }

    for v in 0..kappa {
        cur_mask_shift = cur_mask_shift.scale_bb(INV2_BB);
        let half = l_cur.len() / 2;
        let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
        for idx in 0..half {
            let (a0, a1) = (l_cur[2 * idx], l_cur[2 * idx + 1]);
            let (b0, b1) = (r_cur[2 * idx], r_cur[2 * idx + 1]);
            let da = a1.sub(a0);
            let db = b1.sub(b0);
            c0 = c0.add(a0.mul(b0));
            c1 = c1.add(a0.mul(db).add(da.mul(b0)));
            c2 = c2.add(da.mul(db));
        }
        let unmasked = [
            prefix_eq.mul(c0).add(cur_mask_shift),
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
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
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

fn build_consolidated_d1b_16384_table(
    s_in: &GdnRecurrentState,
    s_out: &GdnRecurrentState,
    wit: &StatefulGdnCarryWitness,
    d1b_mask_18: &[u32],
) -> Vec<u32> {
    let mut virt = Vec::with_capacity(1usize << JITT_D1B_WIT_VARS);
    // Slice 0 (`262K`): `S_c + 8192`
    for &x in &s_in.s_bb_hvk {
        virt.push(badd(x, JITT_S_LIMIT as u32));
    }
    // Slice 1 (`262K`): `S_{c+1} + 8192`
    for &x in &s_out.s_bb_hvk {
        virt.push(badd(x, JITT_S_LIMIT as u32));
    }
    // Slice 2 (`262K`): `[V_beta + 8192 | W_ks + 8192]`
    for &x in &wit.v_beta_lsb_hiv {
        virt.push(badd(x, JITT_S_LIMIT as u32));
    }
    for &x in &wit.w_ks_lsb_hiv {
        virt.push(badd(x, JITT_S_LIMIT as u32));
    }
    // Slice 3 (`262K`): `[U_wy + 8192 | 8192]`
    for &x in &wit.u_wy_lsb_hiv {
        virt.push(badd(x, JITT_S_LIMIT as u32));
    }
    virt.resize(virt.len() + JITT_HIV_CELLS, JITT_S_LIMIT as u32);
    // Slice 4 (`262K`): `[K_dec + 512 | K_tail + 512]`
    for &x in &wit.k_dec_lsb_hik {
        virt.push(badd(x, JITT_OP_LIMIT as u32));
    }
    for &x in &wit.k_tail_lsb_hik {
        virt.push(badd(x, JITT_OP_LIMIT as u32));
    }
    // Slice 5 (`262K`): `[K_dec + 15872 | K_tail + 15872]`
    for &x in &wit.k_dec_lsb_hik {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    for &x in &wit.k_tail_lsb_hik {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    // Slice 6 (`262K`): `[R_ks | R_wy]`
    virt.extend_from_slice(&wit.r_ks_lsb_hiv);
    virt.extend_from_slice(&wit.r_wy_lsb_hiv);
    // Slice 7 (`262K`): `[R_ks + 15872 | R_wy + 15872]`
    for &x in &wit.r_ks_lsb_hiv {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    for &x in &wit.r_wy_lsb_hiv {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    // Slice 8 (`262K`): `R_st`
    virt.extend_from_slice(&wit.r_st_lsb_hvk);
    // Slice 9 (`262K`): `R_st + 15872`
    for &x in &wit.r_st_lsb_hvk {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    // Slice 10 (`262K`): `[L + 512 (65K) | L + 15872 (65K) | 0 (131K)]`
    for &x in &wit.l_lsb_hij {
        virt.push(badd(x, JITT_OP_LIMIT as u32));
    }
    for &x in &wit.l_lsb_hij {
        virt.push(badd(x, JITT_UPPER_SHIFT_512));
    }
    virt.resize(virt.len() + JITT_HIV_CELLS, 0u32);
    // Slices 11..=14 (`4 * 262K`): `0`
    virt.resize(15 * JITT_STATE_CELLS, 0u32);
    // Slice 15 (`262K`): `d1b_mask_18` (`in [0, 16384)`)
    virt.extend_from_slice(d1b_mask_18);
    assert_eq!(virt.len(), 1usize << JITT_D1B_WIT_VARS);
    virt
}

fn assemble_d1b_online_claim(
    z_leaf: &[Ext4],
    rem_leaf_eval: Ext4,
    alpha_d1b: Ext4,
    mu_in_d1b: Ext4,
    delta_in_d1b: Ext4,
    mu_out_d1b: Ext4,
    delta_out_d1b: Ext4,
) -> JointLinearClaimExt4 {
    let w_sl = build_eq_table_lsb_ext4(&z_leaf[18..22]);
    let b17_1 = z_leaf[17];
    let b17_0 = Ext4::ONE.sub(b17_1);
    let w_q4 = build_eq_table_lsb_ext4(&z_leaf[16..18]);

    let pt18 = z_leaf[..18].to_vec();
    let pt17 = z_leaf[..17].to_vec();
    let pt16 = z_leaf[..16].to_vec();

    let w_45 = w_sl[4].add(w_sl[5]);
    let w_67 = w_sl[6].add(w_sl[7]);
    let w_89 = w_sl[8].add(w_sl[9]);
    let w_l = w_sl[10].mul(w_q4[0].add(w_q4[1]));

    let const_bias = w_sl[0]
        .add(w_sl[1])
        .add(w_sl[2])
        .add(w_sl[3])
        .scale_bb(JITT_S_LIMIT as u32)
        .add(w_sl[4].add(w_sl[10].mul(w_q4[0])).scale_bb(JITT_OP_LIMIT as u32))
        .add(
            w_sl[5]
                .add(w_sl[7])
                .add(w_sl[9])
                .add(w_sl[10].mul(w_q4[1]))
                .scale_bb(JITT_UPPER_SHIFT_512),
        );

    let mut terms = vec![
        LinearTermExt4::PointEval {
            subtable: 0,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_45.mul(b17_0)),
        },
        LinearTermExt4::PointEval {
            subtable: 1,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_45.mul(b17_1)),
        },
        LinearTermExt4::PointEval {
            subtable: 2,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_sl[2].mul(b17_0)),
        },
        LinearTermExt4::PointEval {
            subtable: 3,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_sl[2].mul(b17_1)),
        },
        LinearTermExt4::PointEval {
            subtable: 4,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_sl[3].mul(b17_0)),
        },
        LinearTermExt4::PointEval {
            subtable: 5,
            point: pt17.clone(),
            weight: alpha_d1b.mul(w_67.mul(b17_0)),
        },
        LinearTermExt4::PointEval {
            subtable: 6,
            point: pt17,
            weight: alpha_d1b.mul(w_67.mul(b17_1)),
        },
        LinearTermExt4::PointEval {
            subtable: 7,
            point: pt18.clone(),
            weight: alpha_d1b.mul(w_89),
        },
        LinearTermExt4::PointEval {
            subtable: 8,
            point: pt18,
            weight: alpha_d1b.mul(w_sl[15]),
        },
        LinearTermExt4::PointEval {
            subtable: 9,
            point: pt16,
            weight: alpha_d1b.mul(w_l),
        },
    ];
    terms.extend(mask_slot_terms_6([11, 12, 13, 14], 3, w_sl[0].neg()));
    terms.extend(mask_slot_terms_6([11, 12, 13, 14], 4, w_sl[1].neg()));

    let rhs = alpha_d1b
        .mul(rem_leaf_eval.sub(const_bias))
        .sub(w_sl[0].mul(mu_in_d1b.sub(delta_in_d1b)))
        .sub(w_sl[1].mul(mu_out_d1b.sub(delta_out_d1b)));

    JointLinearClaimExt4 { terms, rhs }
}

/// Prove a single chunk's stateful `S_c -> S_{c+1}` Gated-DeltaNet transition in `WhirExt4Pcs + GMaskExt4`.
pub fn prove_streaming_gdn_carry_receipt(
    session_id: [u8; 32],
    model_weight_root: [u8; 32],
    layer_idx: u32,
    chunk_idx: u32,
    chunk_tok_commit: [u8; 32],
    s_in_commit: &SaltedGdnStateCommitment,
    s_out_commit: &SaltedGdnStateCommitment,
    wit: &StatefulGdnCarryWitness,
    opt_seed: Option<[u8; 32]>,
) -> Result<StreamingGdnCarryReceipt, String> {
    if &s_out_commit.state != &wit.s_out {
        return Err("s_out_commit state does not match wit.s_out".into());
    }
    for &g in &wit.gamma_int_16 {
        if (g as i64) > JITT_M_WY {
            return Err("gamma_int_16 exceeds JITT_M_WY".into());
        }
    }

    let seed = opt_seed.unwrap_or_else(os_random_seed_32);
    let mut rng = CShakeRng::from_seed(b"QW35-JITT-ONLINE-RNG-V1", &seed);

    let d1b_mask_18: Vec<u32> = (0..JITT_STATE_CELLS)
        .map(|_| rng.next_bb() & ((1u32 << JITT_D1B_TAB_VARS) - 1))
        .collect();
    let virt_d16384 = build_consolidated_d1b_16384_table(
        &s_in_commit.state,
        &s_out_commit.state,
        wit,
        &d1b_mask_18,
    );
    let mult_d16384 = compute_d1b_multiplicities(&virt_d16384, JITT_D1B_TAB_VARS)?;

    // Online `Ext4` masks `[M'_wy, M'_in_upd, M'_out_upd, M'_in_d1b, M'_out_d1b, M'_st_claim, ...]`:
    let online_masks: [Ext4; 64] = std::array::from_fn(|_| {
        Ext4([rng.next_bb(), rng.next_bb(), rng.next_bb(), rng.next_bb()])
    });
    let mut online_mask_limbs: [Vec<u32>; 4] = std::array::from_fn(|_| vec![0u32; 64]);
    for (i, m) in online_masks.iter().enumerate() {
        for l in 0..4 {
            online_mask_limbs[l][i] = m.0[l];
        }
    }

    let gm_specs = vec![
        GMaskSpecExt4::new("ks_sc", JITT_LOG_H + JITT_LOG_D, 3),
        GMaskSpecExt4::new("wy_sc", JITT_LOG_H + JITT_LOG_C, 3),
        GMaskSpecExt4::new("slt_sc", JITT_SLT_VARS, 3),
        GMaskSpecExt4::new("st_sc", JITT_LOG_H + JITT_LOG_C, 3),
    ];
    let ext_gmask = GMaskExt4::sample(gm_specs.clone(), &mut rng);
    let gm_limbs = ext_gmask.to_four_bb_tables();
    assert_eq!(gm_limbs[0].len(), 256);

    let mut whir_seed = [0u8; 32];
    rng.fill_bytes(&mut whir_seed);
    let online_mat = WhirCommittedMatrixExt4::commit_with_shape(
        StreamingGdnCarryReceipt::expected_online_shape(),
        &[
            &wit.k_dec_lsb_hik,
            &wit.k_tail_lsb_hik,
            &wit.v_beta_lsb_hiv,
            &wit.w_ks_lsb_hiv,
            &wit.u_wy_lsb_hiv,
            &wit.r_ks_lsb_hiv,
            &wit.r_wy_lsb_hiv,
            &wit.r_st_lsb_hvk,
            &d1b_mask_18,
            &wit.l_lsb_hij,
            &mult_d16384,
            &online_mask_limbs[0],
            &online_mask_limbs[1],
            &online_mask_limbs[2],
            &online_mask_limbs[3],
            &gm_limbs[0],
            &gm_limbs[1],
            &gm_limbs[2],
            &gm_limbs[3],
        ],
        Some(whir_seed),
    );

    let header = StreamingCarryChunkHeader {
        session_id,
        model_weight_root,
        layer_idx,
        chunk_idx,
        s_in_root: s_in_commit.root(),
        s_out_root: s_out_commit.root(),
        gamma_int_16: wit.gamma_int_16,
        chunk_tok_commit,
    };

    let delta_masks = [
        s_in_commit.masks[2].sub(online_masks[0]),
        s_in_commit.masks[3].sub(online_masks[1]),
        s_out_commit.masks[0].sub(online_masks[2]),
        s_in_commit.masks[4].sub(online_masks[3]),
        s_out_commit.masks[1].sub(online_masks[4]),
    ];

    let mut tr = CShakeTranscript::new(JITT_TRANSCRIPT_DOM);
    header.absorb_into(&mut tr);
    tr.absorb_root(b"jitt_online_rt", &online_mat.root);
    tr.absorb_ext4_slice(b"jitt_dmasks", &delta_masks);

    // --- Section A: `K_dec · S_c = 512 * W_ks + R_ks - 256` (`TVD = 0` `mu_wy`) ---
    let z_h_ks = tr.squeeze_ext4_vec(b"ks_zh", JITT_LOG_H, true);
    let z_i_ks = tr.squeeze_ext4_vec(b"ks_zi", JITT_LOG_C, true);
    let z_v_ks = tr.squeeze_ext4_vec(b"ks_zv", JITT_LOG_D, true);
    let mut z_hiv_ks = Vec::with_capacity(JITT_HIV_VARS);
    z_hiv_ks.extend_from_slice(&z_h_ks);
    z_hiv_ks.extend_from_slice(&z_i_ks);
    z_hiv_ks.extend_from_slice(&z_v_ks);

    let w_ks_eval = mle_eval_bb_at_ext4(&wit.w_ks_lsb_hiv, &z_hiv_ks);
    let r_ks_eval = mle_eval_bb_at_ext4(&wit.r_ks_lsb_hiv, &z_hiv_ks);
    tr.absorb_ext4(b"ks_w_ev", w_ks_eval);
    tr.absorb_ext4(b"ks_r_ev", r_ks_eval);

    let eq_i_ks = build_eq_table_lsb_ext4(&z_i_ks);
    let eq_v_ks = build_eq_table_lsb_ext4(&z_v_ks);
    let mut left_hk = vec![Ext4::ZERO; JITT_H_V * JITT_D_K];
    let mut right_hk = vec![Ext4::ZERO; JITT_H_V * JITT_D_K];
    for i_k in 0..JITT_D_K {
        for h in 0..JITT_H_V {
            let mut al = Ext4::ZERO;
            let base_k = h + (i_k << (JITT_LOG_H + JITT_LOG_C));
            for i in 0..JITT_CHUNK_LEN {
                al = al.add(eq_i_ks[i].scale_bb(wit.k_dec_lsb_hik[base_k + (i << JITT_LOG_H)]));
            }
            left_hk[h + (i_k << JITT_LOG_H)] = al;

            let mut ar = Ext4::ZERO;
            let base_s = h + (i_k << (JITT_LOG_H + JITT_LOG_D));
            for j_v in 0..JITT_D_V {
                ar = ar.add(eq_v_ks[j_v].scale_bb(s_in_commit.state.s_bb_hvk[base_s + (j_v << JITT_LOG_H)]));
            }
            right_hk[h + (i_k << JITT_LOG_H)] = ar;
        }
    }
    let (ks_sc_prf, ks_rho, ks_chals, k_dec_at_r, s_in_at_r_ks, ks_term) = prove_gmask_einsum_ext4(
        &left_hk,
        &right_hk,
        JITT_LOG_H,
        JITT_LOG_D,
        &z_h_ks,
        &ext_gmask,
        "ks_sc",
        &mut tr,
    );
    tr.absorb_ext4(b"ks_kdec_r", k_dec_at_r);
    let alpha_wy = squeeze_nonzero_ext4(&mut tr, b"ks_alpha_wy");
    let mu_wy = alpha_wy.mul(s_in_at_r_ks).add(s_in_commit.masks[2]);
    tr.absorb_ext4(b"ks_mu_wy", mu_wy);

    // --- Section B: `(I + L / 512) U_wy = V_beta - W_ks` + SLT Zerocheck ---
    let z_h_wy = tr.squeeze_ext4_vec(b"wy_zh", JITT_LOG_H, true);
    let z_i_wy = tr.squeeze_ext4_vec(b"wy_zi", JITT_LOG_C, true);
    let z_v_wy = tr.squeeze_ext4_vec(b"wy_zv", JITT_LOG_D, true);
    let mut z_hiv_wy = Vec::with_capacity(JITT_HIV_VARS);
    z_hiv_wy.extend_from_slice(&z_h_wy);
    z_hiv_wy.extend_from_slice(&z_i_wy);
    z_hiv_wy.extend_from_slice(&z_v_wy);

    let v_beta_wy_eval = mle_eval_bb_at_ext4(&wit.v_beta_lsb_hiv, &z_hiv_wy);
    let w_ks_wy_eval = mle_eval_bb_at_ext4(&wit.w_ks_lsb_hiv, &z_hiv_wy);
    let u_wy_eval = mle_eval_bb_at_ext4(&wit.u_wy_lsb_hiv, &z_hiv_wy);
    let r_wy_eval = mle_eval_bb_at_ext4(&wit.r_wy_lsb_hiv, &z_hiv_wy);
    for e in [v_beta_wy_eval, w_ks_wy_eval, u_wy_eval, r_wy_eval] {
        tr.absorb_ext4(b"wy_ev", e);
    }

    let eq_i_wy = build_eq_table_lsb_ext4(&z_i_wy);
    let eq_v_wy = build_eq_table_lsb_ext4(&z_v_wy);
    let mut left_hj = vec![Ext4::ZERO; JITT_H_V * JITT_CHUNK_LEN];
    let mut right_hj = vec![Ext4::ZERO; JITT_H_V * JITT_CHUNK_LEN];
    for j in 0..JITT_CHUNK_LEN {
        for h in 0..JITT_H_V {
            let mut al = Ext4::ZERO;
            let base_l = h + (j << (JITT_LOG_H + JITT_LOG_C));
            for i in 0..JITT_CHUNK_LEN {
                al = al.add(eq_i_wy[i].scale_bb(wit.l_lsb_hij[base_l + (i << JITT_LOG_H)]));
            }
            left_hj[h + (j << JITT_LOG_H)] = al;

            let mut ar = Ext4::ZERO;
            let base_u = h + (j << JITT_LOG_H);
            for j_v in 0..JITT_D_V {
                ar = ar.add(eq_v_wy[j_v].scale_bb(wit.u_wy_lsb_hiv[base_u + (j_v << (JITT_LOG_H + JITT_LOG_C))]));
            }
            right_hj[h + (j << JITT_LOG_H)] = ar;
        }
    }
    let (wy_sc_prf, wy_rho, wy_chals, wy_l_at_r, wy_u_at_r, wy_term) = prove_gmask_einsum_ext4(
        &left_hj,
        &right_hj,
        JITT_LOG_H,
        JITT_LOG_C,
        &z_h_wy,
        &ext_gmask,
        "wy_sc",
        &mut tr,
    );
    tr.absorb_ext4(b"wy_l_r", wy_l_at_r);
    tr.absorb_ext4(b"wy_u_r", wy_u_at_r);

    let z_slt = tr.squeeze_ext4_vec(b"slt_z", JITT_SLT_VARS, true);
    let mut non_slt = vec![Ext4::ZERO; JITT_SLT_CELLS];
    let mut l_ext = vec![Ext4::ZERO; JITT_SLT_CELLS];
    for j in 0..JITT_CHUNK_LEN {
        for i in 0..JITT_CHUNK_LEN {
            let ind = if i <= j { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..JITT_H_V {
                let idx = h + (i << JITT_LOG_H) + (j << (JITT_LOG_H + JITT_LOG_C));
                non_slt[idx] = ind;
                l_ext[idx] = Ext4::from_bb(wit.l_lsb_hij[idx]);
            }
        }
    }
    let (slt_sc_prf, slt_rho, slt_chals, _, _, slt_term) =
        prove_gmask_einsum_ext4(&non_slt, &l_ext, JITT_SLT_VARS, 0, &z_slt, &ext_gmask, "slt_sc", &mut tr);

    // --- Section C: `S_{c+1} = round((gamma_c · S_c + K_tail^T · U_wy) / 512)` (`TVD = 0` Dual Handoff) ---
    let z_h_st = tr.squeeze_ext4_vec(b"st_zh", JITT_LOG_H, true);
    let z_v_st = tr.squeeze_ext4_vec(b"st_zv", JITT_LOG_D, true);
    let z_k_st = tr.squeeze_ext4_vec(b"st_zk", JITT_LOG_D, true);
    let mut z_hvk_st = Vec::with_capacity(JITT_STATE_VARS);
    z_hvk_st.extend_from_slice(&z_h_st);
    z_hvk_st.extend_from_slice(&z_v_st);
    z_hvk_st.extend_from_slice(&z_k_st);
    let alpha_upd = squeeze_nonzero_ext4(&mut tr, b"st_alpha_upd");

    let eq_zh_st = build_eq_table_lsb_ext4(&z_h_st);
    let eq_zv_st = build_eq_table_lsb_ext4(&z_v_st);
    let eq_zk_st = build_eq_table_lsb_ext4(&z_k_st);

    let mut gamma_s_in_eval = Ext4::ZERO;
    for h in 0..JITT_H_V {
        let w_gh = eq_zh_st[h].scale_bb(wit.gamma_int_16[h] as u32);
        let mut s_vk = Ext4::ZERO;
        for i_k in 0..JITT_D_K {
            let mut row_v = Ext4::ZERO;
            let base_s = h + (i_k << (JITT_LOG_H + JITT_LOG_D));
            for j_v in 0..JITT_D_V {
                row_v = row_v.add(eq_zv_st[j_v].scale_bb(s_in_commit.state.s_bb_hvk[base_s + (j_v << JITT_LOG_H)]));
            }
            s_vk = s_vk.add(eq_zk_st[i_k].mul(row_v));
        }
        gamma_s_in_eval = gamma_s_in_eval.add(w_gh.mul(s_vk));
    }
    let s_out_st_eval = mle_eval_bb_at_ext4(&s_out_commit.state.s_bb_hvk, &z_hvk_st);
    let r_st_eval = mle_eval_bb_at_ext4(&wit.r_st_lsb_hvk, &z_hvk_st);

    let mu_in_upd = alpha_upd.mul(gamma_s_in_eval).add(s_in_commit.masks[3]);
    let mu_out_upd = alpha_upd.mul(s_out_st_eval).add(s_out_commit.masks[0]);
    let unmasked_claim_st = s_out_st_eval
        .scale_bb(JITT_M_WY as u32)
        .sub(gamma_s_in_eval)
        .add(r_st_eval)
        .sub(Ext4::from_bb(JITT_HALF_WY as u32));
    let masked_claim_st = alpha_upd.mul(unmasked_claim_st).add(online_masks[5]);
    for e in [mu_in_upd, mu_out_upd, masked_claim_st] {
        tr.absorb_ext4(b"st_hdr", e);
    }

    let mut left_hi_scaled = vec![Ext4::ZERO; JITT_H_V * JITT_CHUNK_LEN];
    let mut right_hi = vec![Ext4::ZERO; JITT_H_V * JITT_CHUNK_LEN];
    for i in 0..JITT_CHUNK_LEN {
        for h in 0..JITT_H_V {
            let mut ak = Ext4::ZERO;
            let base_i = h + (i << JITT_LOG_H);
            for i_k in 0..JITT_D_K {
                ak = ak.add(eq_zk_st[i_k].scale_bb(wit.k_tail_lsb_hik[base_i + (i_k << (JITT_LOG_H + JITT_LOG_C))]));
            }
            left_hi_scaled[base_i] = alpha_upd.mul(ak);

            let mut au = Ext4::ZERO;
            for j_v in 0..JITT_D_V {
                au = au.add(eq_zv_st[j_v].scale_bb(wit.u_wy_lsb_hiv[base_i + (j_v << (JITT_LOG_H + JITT_LOG_C))]));
            }
            right_hi[base_i] = au;
        }
    }
    let (st_sc_prf, st_rho, st_chals, k_tail_scaled_at_r, st_u_at_r, st_term) =
        prove_claim_masked_gmask_einsum_ext4(
            &left_hi_scaled,
            &right_hi,
            JITT_LOG_H,
            JITT_LOG_C,
            &z_h_st,
            online_masks[5],
            &ext_gmask,
            "st_sc",
            &mut tr,
        );
    let k_tail_at_r = k_tail_scaled_at_r.mul(alpha_upd.inv().unwrap());
    tr.absorb_ext4(b"st_kt_r", k_tail_at_r);
    tr.absorb_ext4(b"st_u_r", st_u_at_r);

    // --- Section D: Consolidated `[0, 16384)` `D1b` Range Proof + `TVD = 0` Dual Handoff ---
    let (d1b_proof, z_d1b) = prove_d1b_range_ext4(
        &virt_d16384,
        &mult_d16384,
        JITT_D1B_WIT_VARS,
        JITT_D1B_TAB_VARS,
        &mut tr,
    );
    let alpha_d1b = squeeze_nonzero_ext4(&mut tr, b"d1b_alpha_hnd");
    let s_in_d1b_ev = mle_eval_bb_at_ext4(&s_in_commit.state.s_bb_hvk, &z_d1b[..18]);
    let s_out_d1b_ev = mle_eval_bb_at_ext4(&s_out_commit.state.s_bb_hvk, &z_d1b[..18]);
    let mu_in_d1b = alpha_d1b.mul(s_in_d1b_ev).add(s_in_commit.masks[4]);
    let mu_out_d1b = alpha_d1b.mul(s_out_d1b_ev).add(s_out_commit.masks[1]);
    tr.absorb_ext4(b"d1b_mu_in", mu_in_d1b);
    tr.absorb_ext4(b"d1b_mu_out", mu_out_d1b);

    // --- Assemble Joint Linear Claims Across `[online_mat, s_in_commit, s_out_commit]` ---
    let (online_claims, s_in_claims, s_out_claims) = build_all_jitt_whir_claims_inner(
        &header,
        &delta_masks,
        &z_h_ks,
        &z_i_ks,
        &z_v_ks,
        w_ks_eval,
        r_ks_eval,
        ks_sc_prf.gmask_sum,
        ks_rho,
        &ks_chals,
        k_dec_at_r,
        ks_term,
        alpha_wy,
        mu_wy,
        &z_h_wy,
        &z_i_wy,
        &z_v_wy,
        v_beta_wy_eval,
        w_ks_wy_eval,
        u_wy_eval,
        r_wy_eval,
        wy_sc_prf.gmask_sum,
        wy_rho,
        &wy_chals,
        wy_l_at_r,
        wy_u_at_r,
        wy_term,
        &z_slt,
        slt_sc_prf.gmask_sum,
        slt_rho,
        &slt_chals,
        slt_term,
        &z_h_st,
        &z_v_st,
        &z_k_st,
        alpha_upd,
        mu_in_upd,
        mu_out_upd,
        masked_claim_st,
        st_sc_prf.gmask_sum,
        st_rho,
        &st_chals,
        k_tail_at_r,
        st_u_at_r,
        st_term,
        &z_d1b,
        &d1b_proof,
        alpha_d1b,
        mu_in_d1b,
        mu_out_d1b,
        &gm_specs,
    );

    let whir_batch_proof = open_whir_batch_ext4(
        &[
            (&online_mat, &online_claims),
            (&s_in_commit.whir_mat, &s_in_claims),
            (&s_out_commit.whir_mat, &s_out_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    Ok(StreamingGdnCarryReceipt {
        header,
        online_root: online_mat.root,
        delta_masks,
        w_ks_eval,
        r_ks_eval,
        ks_sc_prf,
        k_dec_at_r,
        mu_wy,
        v_beta_wy_eval,
        w_ks_wy_eval,
        u_wy_eval,
        r_wy_eval,
        wy_sc_prf,
        wy_l_at_r,
        wy_u_at_r,
        slt_sc_prf,
        mu_in_upd,
        mu_out_upd,
        masked_claim_st,
        st_sc_prf,
        k_tail_at_r,
        st_u_at_r,
        d1b_proof,
        mu_in_d1b,
        mu_out_d1b,
        whir_batch_proof,
    })
}

#[allow(clippy::too_many_arguments)]
fn build_all_jitt_whir_claims_inner(
    header: &StreamingCarryChunkHeader,
    delta_masks: &[Ext4; 5],
    z_h_ks: &[Ext4],
    z_i_ks: &[Ext4],
    z_v_ks: &[Ext4],
    w_ks_eval: Ext4,
    r_ks_eval: Ext4,
    ks_gsum: Ext4,
    ks_rho: Ext4,
    ks_chals: &[Ext4],
    k_dec_at_r: Ext4,
    ks_term: Ext4,
    alpha_wy: Ext4,
    mu_wy: Ext4,
    z_h_wy: &[Ext4],
    z_i_wy: &[Ext4],
    z_v_wy: &[Ext4],
    v_beta_wy_eval: Ext4,
    w_ks_wy_eval: Ext4,
    u_wy_eval: Ext4,
    r_wy_eval: Ext4,
    wy_gsum: Ext4,
    wy_rho: Ext4,
    wy_chals: &[Ext4],
    wy_l_at_r: Ext4,
    wy_u_at_r: Ext4,
    wy_term: Ext4,
    z_slt: &[Ext4],
    slt_gsum: Ext4,
    slt_rho: Ext4,
    slt_chals: &[Ext4],
    slt_term: Ext4,
    z_h_st: &[Ext4],
    z_v_st: &[Ext4],
    z_k_st: &[Ext4],
    alpha_upd: Ext4,
    mu_in_upd: Ext4,
    mu_out_upd: Ext4,
    masked_claim_st: Ext4,
    st_gsum: Ext4,
    st_rho: Ext4,
    st_chals: &[Ext4],
    k_tail_at_r: Ext4,
    st_u_at_r: Ext4,
    st_term: Ext4,
    z_d1b: &[Ext4],
    d1b_proof: &D1bRangeExt4Proof,
    alpha_d1b: Ext4,
    mu_in_d1b: Ext4,
    mu_out_d1b: Ext4,
    gm_specs: &[GMaskSpecExt4],
) -> (
    Vec<JointLinearClaimExt4>,
    Vec<JointLinearClaimExt4>,
    Vec<JointLinearClaimExt4>,
) {
    let gm_ids = [15usize, 16, 17, 18];
    let onl_msk_ids = [11usize, 12, 13, 14];
    let st_msk_ids = [1usize, 2, 3, 4];

    let (ks_ws, ks_wa) = GMaskExt4::build_spec_weights(gm_specs, "ks_sc", ks_chals);
    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(gm_specs, "wy_sc", wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(gm_specs, "slt_sc", slt_chals);
    let (st_ws, st_wa) = GMaskExt4::build_spec_weights(gm_specs, "st_sc", st_chals);

    let mut z_hiv_ks = Vec::with_capacity(JITT_HIV_VARS);
    z_hiv_ks.extend_from_slice(z_h_ks);
    z_hiv_ks.extend_from_slice(z_i_ks);
    z_hiv_ks.extend_from_slice(z_v_ks);

    let mut k_dec_pt = Vec::with_capacity(JITT_HIV_VARS);
    k_dec_pt.extend_from_slice(&ks_chals[..JITT_LOG_H]);
    k_dec_pt.extend_from_slice(z_i_ks);
    k_dec_pt.extend_from_slice(&ks_chals[JITT_LOG_H..]);

    let mut s_in_wy_pt = Vec::with_capacity(JITT_STATE_VARS);
    s_in_wy_pt.extend_from_slice(&ks_chals[..JITT_LOG_H]);
    s_in_wy_pt.extend_from_slice(z_v_ks);
    s_in_wy_pt.extend_from_slice(&ks_chals[JITT_LOG_H..]);

    let w_s_ks = eq_mle_ext4(z_h_ks, &ks_chals[..JITT_LOG_H]).mul(k_dec_at_r);
    let ks_sec_terms = mask_slot_terms_6(onl_msk_ids, 0, w_s_ks.neg());
    let ks_rhs = alpha_wy
        .mul(ks_term)
        .sub(w_s_ks.mul(mu_wy.sub(delta_masks[0])));

    let mut z_hiv_wy = Vec::with_capacity(JITT_HIV_VARS);
    z_hiv_wy.extend_from_slice(z_h_wy);
    z_hiv_wy.extend_from_slice(z_i_wy);
    z_hiv_wy.extend_from_slice(z_v_wy);

    let mut l_wy_pt = Vec::with_capacity(JITT_SLT_VARS);
    l_wy_pt.extend_from_slice(&wy_chals[..JITT_LOG_H]);
    l_wy_pt.extend_from_slice(z_i_wy);
    l_wy_pt.extend_from_slice(&wy_chals[JITT_LOG_H..]);

    let mut u_wy_pt2 = Vec::with_capacity(JITT_HIV_VARS);
    u_wy_pt2.extend_from_slice(&wy_chals[..JITT_LOG_H]);
    u_wy_pt2.extend_from_slice(&wy_chals[JITT_LOG_H..]);
    u_wy_pt2.extend_from_slice(z_v_wy);

    let wy_unm = eq_mle_ext4(z_h_wy, &wy_chals[..JITT_LOG_H])
        .mul(wy_l_at_r)
        .mul(wy_u_at_r);
    let non_slt_fac = eq_mle_ext4(z_slt, slt_chals).mul(eval_upper_or_diag_indicator_mle(
        &slt_chals[JITT_LOG_H..JITT_LOG_H + JITT_LOG_C],
        &slt_chals[JITT_LOG_H + JITT_LOG_C..],
    ));

    let mut z_hvk_st = Vec::with_capacity(JITT_STATE_VARS);
    z_hvk_st.extend_from_slice(z_h_st);
    z_hvk_st.extend_from_slice(z_v_st);
    z_hvk_st.extend_from_slice(z_k_st);

    let mut k_tail_pt = Vec::with_capacity(JITT_HIV_VARS);
    k_tail_pt.extend_from_slice(st_chals);
    k_tail_pt.extend_from_slice(z_k_st);

    let mut u_st_pt = Vec::with_capacity(JITT_HIV_VARS);
    u_st_pt.extend_from_slice(st_chals);
    u_st_pt.extend_from_slice(z_v_st);

    // `M'_st_claim + alpha_upd * R_st(z_hvk_st) - 512 * M'_out_upd + M'_in_upd == masked_claim_st - C_semi`
    let c_semi = mu_out_upd
        .sub(delta_masks[2])
        .scale_bb(JITT_M_WY as u32)
        .sub(mu_in_upd.sub(delta_masks[1]))
        .sub(alpha_upd.scale_bb(JITT_HALF_WY as u32));
    let mut st_claim_weld_terms = vec![LinearTermExt4::PointEval {
        subtable: 7,
        point: z_hvk_st.clone(),
        weight: alpha_upd,
    }];
    st_claim_weld_terms.extend(mask_slot_terms_6(onl_msk_ids, 5, Ext4::ONE));
    st_claim_weld_terms.extend(mask_slot_terms_6(
        onl_msk_ids,
        2,
        Ext4::from_bb(JITT_M_WY as u32).neg(),
    ));
    st_claim_weld_terms.extend(mask_slot_terms_6(onl_msk_ids, 1, Ext4::ONE));

    let inv2_10 = Ext4::from_bb(bpow(INV2_BB, 10));
    let st_unm = alpha_upd
        .mul(eq_mle_ext4(z_h_st, &st_chals[..JITT_LOG_H]))
        .mul(k_tail_at_r)
        .mul(st_u_at_r);
    let st_sec_terms = mask_slot_terms_6(onl_msk_ids, 5, inv2_10);

    let online_claims = vec![
        // Section A:
        JointLinearClaimExt4::point_eval(0, k_dec_pt, k_dec_at_r),
        JointLinearClaimExt4::point_eval(3, z_hiv_ks.clone(), w_ks_eval),
        JointLinearClaimExt4::point_eval(5, z_hiv_ks, r_ks_eval),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &ks_ws, ks_gsum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            ks_sec_terms,
            gm_ids,
            &ks_wa,
            alpha_wy.mul(ks_rho),
            ks_rhs,
        ),
        // Section B:
        JointLinearClaimExt4::point_eval(2, z_hiv_wy.clone(), v_beta_wy_eval),
        JointLinearClaimExt4::point_eval(3, z_hiv_wy.clone(), w_ks_wy_eval),
        JointLinearClaimExt4::point_eval(4, z_hiv_wy.clone(), u_wy_eval),
        JointLinearClaimExt4::point_eval(4, u_wy_pt2, wy_u_at_r),
        JointLinearClaimExt4::point_eval(6, z_hiv_wy, r_wy_eval),
        JointLinearClaimExt4::point_eval(9, l_wy_pt, wy_l_at_r),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, wy_gsum),
        JointLinearClaimExt4::hvzk_terminal_weld(Vec::new(), gm_ids, &wy_wa, wy_rho, wy_term.sub(wy_unm)),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, slt_gsum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 9,
                point: slt_chals.to_vec(),
                weight: non_slt_fac,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        // Section C:
        JointLinearClaimExt4::point_eval(1, k_tail_pt, k_tail_at_r),
        JointLinearClaimExt4::point_eval(4, u_st_pt, st_u_at_r),
        JointLinearClaimExt4 {
            terms: st_claim_weld_terms,
            rhs: masked_claim_st.sub(c_semi),
        },
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &st_ws, st_gsum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            st_sec_terms,
            gm_ids,
            &st_wa,
            st_rho,
            st_term.sub(st_unm),
        ),
        // Section D:
        assemble_d1b_online_claim(
            z_d1b,
            d1b_proof.rem_leaf_eval,
            alpha_d1b,
            mu_in_d1b,
            delta_masks[3],
            mu_out_d1b,
            delta_masks[4],
        ),
        JointLinearClaimExt4::point_eval(
            10,
            z_d1b[..JITT_D1B_TAB_VARS].to_vec(),
            d1b_proof.mult_leaf_eval,
        ),
    ];

    // `s_in_commit` claims (`slot 2 = M_read_wy`, `slot 3 = M_read_upd`, `slot 4 = M_read_d1b`):
    let mut s_in_wy_terms = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: s_in_wy_pt,
        weight: alpha_wy,
    }];
    s_in_wy_terms.extend(mask_slot_terms_6(st_msk_ids, 2, Ext4::ONE));

    let eq_zh_st = build_eq_table_lsb_ext4(z_h_st);
    let mut s_in_upd_terms = Vec::with_capacity(JITT_H_V + 4);
    for h in 0..JITT_H_V {
        let mut pt_h = Vec::with_capacity(JITT_STATE_VARS);
        pt_h.extend_from_slice(&bits4_point(h));
        pt_h.extend_from_slice(z_v_st);
        pt_h.extend_from_slice(z_k_st);
        s_in_upd_terms.push(LinearTermExt4::PointEval {
            subtable: 0,
            point: pt_h,
            weight: alpha_upd.mul(eq_zh_st[h]).scale_bb(header.gamma_int_16[h] as u32),
        });
    }
    s_in_upd_terms.extend(mask_slot_terms_6(st_msk_ids, 3, Ext4::ONE));

    let mut s_in_d1b_terms = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z_d1b[..18].to_vec(),
        weight: alpha_d1b,
    }];
    s_in_d1b_terms.extend(mask_slot_terms_6(st_msk_ids, 4, Ext4::ONE));

    let s_in_claims = vec![
        JointLinearClaimExt4 {
            terms: s_in_wy_terms,
            rhs: mu_wy,
        },
        JointLinearClaimExt4 {
            terms: s_in_upd_terms,
            rhs: mu_in_upd,
        },
        JointLinearClaimExt4 {
            terms: s_in_d1b_terms,
            rhs: mu_in_d1b,
        },
    ];

    // `s_out_commit` claims (`slot 0 = M_write_upd`, `slot 1 = M_write_d1b`):
    let mut s_out_upd_terms = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z_hvk_st,
        weight: alpha_upd,
    }];
    s_out_upd_terms.extend(mask_slot_terms_6(st_msk_ids, 0, Ext4::ONE));

    let mut s_out_d1b_terms = vec![LinearTermExt4::PointEval {
        subtable: 0,
        point: z_d1b[..18].to_vec(),
        weight: alpha_d1b,
    }];
    s_out_d1b_terms.extend(mask_slot_terms_6(st_msk_ids, 1, Ext4::ONE));

    let s_out_claims = vec![
        JointLinearClaimExt4 {
            terms: s_out_upd_terms,
            rhs: mu_out_upd,
        },
        JointLinearClaimExt4 {
            terms: s_out_d1b_terms,
            rhs: mu_out_d1b,
        },
    ];

    (online_claims, s_in_claims, s_out_claims)
}

/// Standalone `< 25 ms` Zero-Witness Verifier for `StreamingGdnCarryReceipt` (`0` access to `S_c`, `S_{c+1}`, or weights!).
pub fn verify_streaming_gdn_carry_receipt(prf: &StreamingGdnCarryReceipt) -> Result<(), String> {
    if prf.header.layer_idx >= 24 || (prf.header.layer_idx % 4) == 3 {
        return Err("header.layer_idx is not a valid Qwen3.5 GDN layer".into());
    }
    for (h, &g) in prf.header.gamma_int_16.iter().enumerate() {
        if (g as i64) > JITT_M_WY {
            return Err(format!("gamma_int_16[{h}] = {g} exceeds {JITT_M_WY}"));
        }
    }
    if prf.d1b_proof.m_wit != JITT_D1B_WIT_VARS || prf.d1b_proof.m_tab != JITT_D1B_TAB_VARS {
        return Err("D1b dimension mismatch in StreamingGdnCarryReceipt".into());
    }

    let mut tr = CShakeTranscript::new(JITT_TRANSCRIPT_DOM);
    prf.header.absorb_into(&mut tr);
    tr.absorb_root(b"jitt_online_rt", &prf.online_root);
    tr.absorb_ext4_slice(b"jitt_dmasks", &prf.delta_masks);

    // Replay Section A:
    let z_h_ks = tr.squeeze_ext4_vec(b"ks_zh", JITT_LOG_H, true);
    let z_i_ks = tr.squeeze_ext4_vec(b"ks_zi", JITT_LOG_C, true);
    let z_v_ks = tr.squeeze_ext4_vec(b"ks_zv", JITT_LOG_D, true);
    tr.absorb_ext4(b"ks_w_ev", prf.w_ks_eval);
    tr.absorb_ext4(b"ks_r_ev", prf.r_ks_eval);
    let claim_ks = prf
        .w_ks_eval
        .scale_bb(JITT_M_WY as u32)
        .add(prf.r_ks_eval)
        .sub(Ext4::from_bb(JITT_HALF_WY as u32));
    let (ks_rho, ks_chals, ks_term) = verify_gmask_einsum_ext4(
        claim_ks,
        JITT_LOG_H,
        JITT_LOG_D,
        &z_h_ks,
        &prf.ks_sc_prf,
        &mut tr,
    )?;
    tr.absorb_ext4(b"ks_kdec_r", prf.k_dec_at_r);
    let alpha_wy = squeeze_nonzero_ext4(&mut tr, b"ks_alpha_wy");
    tr.absorb_ext4(b"ks_mu_wy", prf.mu_wy);

    // Replay Section B:
    let z_h_wy = tr.squeeze_ext4_vec(b"wy_zh", JITT_LOG_H, true);
    let z_i_wy = tr.squeeze_ext4_vec(b"wy_zi", JITT_LOG_C, true);
    let z_v_wy = tr.squeeze_ext4_vec(b"wy_zv", JITT_LOG_D, true);
    for e in [prf.v_beta_wy_eval, prf.w_ks_wy_eval, prf.u_wy_eval, prf.r_wy_eval] {
        tr.absorb_ext4(b"wy_ev", e);
    }
    let claim_wy = prf
        .v_beta_wy_eval
        .sub(prf.w_ks_wy_eval)
        .sub(prf.u_wy_eval)
        .scale_bb(JITT_M_WY as u32)
        .add(Ext4::from_bb(JITT_HALF_WY as u32))
        .sub(prf.r_wy_eval);
    let (wy_rho, wy_chals, wy_term) = verify_gmask_einsum_ext4(
        claim_wy,
        JITT_LOG_H,
        JITT_LOG_C,
        &z_h_wy,
        &prf.wy_sc_prf,
        &mut tr,
    )?;
    tr.absorb_ext4(b"wy_l_r", prf.wy_l_at_r);
    tr.absorb_ext4(b"wy_u_r", prf.wy_u_at_r);

    let z_slt = tr.squeeze_ext4_vec(b"slt_z", JITT_SLT_VARS, true);
    let (slt_rho, slt_chals, slt_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, JITT_SLT_VARS, 0, &z_slt, &prf.slt_sc_prf, &mut tr)?;

    // Replay Section C:
    let z_h_st = tr.squeeze_ext4_vec(b"st_zh", JITT_LOG_H, true);
    let z_v_st = tr.squeeze_ext4_vec(b"st_zv", JITT_LOG_D, true);
    let z_k_st = tr.squeeze_ext4_vec(b"st_zk", JITT_LOG_D, true);
    let alpha_upd = squeeze_nonzero_ext4(&mut tr, b"st_alpha_upd");
    for e in [prf.mu_in_upd, prf.mu_out_upd, prf.masked_claim_st] {
        tr.absorb_ext4(b"st_hdr", e);
    }
    let (st_rho, st_chals, st_term) = verify_gmask_einsum_ext4(
        prf.masked_claim_st,
        JITT_LOG_H,
        JITT_LOG_C,
        &z_h_st,
        &prf.st_sc_prf,
        &mut tr,
    )?;
    tr.absorb_ext4(b"st_kt_r", prf.k_tail_at_r);
    tr.absorb_ext4(b"st_u_r", prf.st_u_at_r);

    // Replay Section D:
    let z_d1b = verify_d1b_range_ext4(&prf.d1b_proof, &mut tr)?;
    let alpha_d1b = squeeze_nonzero_ext4(&mut tr, b"d1b_alpha_hnd");
    tr.absorb_ext4(b"d1b_mu_in", prf.mu_in_d1b);
    tr.absorb_ext4(b"d1b_mu_out", prf.mu_out_d1b);

    let gm_specs = vec![
        GMaskSpecExt4::new("ks_sc", JITT_LOG_H + JITT_LOG_D, 3),
        GMaskSpecExt4::new("wy_sc", JITT_LOG_H + JITT_LOG_C, 3),
        GMaskSpecExt4::new("slt_sc", JITT_SLT_VARS, 3),
        GMaskSpecExt4::new("st_sc", JITT_LOG_H + JITT_LOG_C, 3),
    ];
    let (online_claims, s_in_claims, s_out_claims) = build_all_jitt_whir_claims_inner(
        &prf.header,
        &prf.delta_masks,
        &z_h_ks,
        &z_i_ks,
        &z_v_ks,
        prf.w_ks_eval,
        prf.r_ks_eval,
        prf.ks_sc_prf.gmask_sum,
        ks_rho,
        &ks_chals,
        prf.k_dec_at_r,
        ks_term,
        alpha_wy,
        prf.mu_wy,
        &z_h_wy,
        &z_i_wy,
        &z_v_wy,
        prf.v_beta_wy_eval,
        prf.w_ks_wy_eval,
        prf.u_wy_eval,
        prf.r_wy_eval,
        prf.wy_sc_prf.gmask_sum,
        wy_rho,
        &wy_chals,
        prf.wy_l_at_r,
        prf.wy_u_at_r,
        wy_term,
        &z_slt,
        prf.slt_sc_prf.gmask_sum,
        slt_rho,
        &slt_chals,
        slt_term,
        &z_h_st,
        &z_v_st,
        &z_k_st,
        alpha_upd,
        prf.mu_in_upd,
        prf.mu_out_upd,
        prf.masked_claim_st,
        prf.st_sc_prf.gmask_sum,
        st_rho,
        &st_chals,
        prf.k_tail_at_r,
        prf.st_u_at_r,
        st_term,
        &z_d1b,
        &prf.d1b_proof,
        alpha_d1b,
        prf.mu_in_d1b,
        prf.mu_out_d1b,
        &gm_specs,
    );

    let online_shape = StreamingGdnCarryReceipt::expected_online_shape();
    let state_shape = SaltedGdnStateCommitment::expected_shape();
    verify_whir_batch_ext4(
        &[
            (&prf.online_root, &online_shape, &online_claims),
            (&prf.header.s_in_root, &state_shape, &s_in_claims),
            (&prf.header.s_out_root, &state_shape, &s_out_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &prf.whir_batch_proof,
        &mut tr,
    )
}

// ================================================================================================
// §4. `O(1)`-RAM Wearable Verifier State Machine & Real 24L `Qwen3.5-0.8B` Streaming JITT Engine
// ================================================================================================

/// `O(1)` (`136`-byte) Wearable JITT Receipt-Chain Verifier matching `CarryVerifierState` in Lean.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WearableJittCarryVerifier {
    pub session_id: [u8; 32],
    pub model_weight_root: [u8; 32],
    pub layer_idx: u32,
    pub expected_chunk_idx: u32,
    pub current_state_root: [u8; 32],
    pub chain_digest: [u8; 32],
}

impl WearableJittCarryVerifier {
    pub const LIVE_STATE_BYTES: usize = 4 * 32 + 2 * 4; // 136 bytes (`O(1)`)

    pub fn new(
        session_id: [u8; 32],
        model_weight_root: [u8; 32],
        layer_idx: u32,
        genesis_state_root: [u8; 32],
    ) -> Self {
        let mut init_buf = [0u8; 100];
        init_buf[0..32].copy_from_slice(&session_id);
        init_buf[32..64].copy_from_slice(&model_weight_root);
        init_buf[64..68].copy_from_slice(&layer_idx.to_le_bytes());
        init_buf[68..100].copy_from_slice(&genesis_state_root);
        let chain_digest = cshake256_32(b"QW35-JITT-GENESIS-V1", &init_buf);
        Self {
            session_id,
            model_weight_root,
            layer_idx,
            expected_chunk_idx: 0,
            current_state_root: genesis_state_root,
            chain_digest,
        }
    }

    pub fn verify_and_advance(&mut self, receipt: &StreamingGdnCarryReceipt) -> Result<(), String> {
        let h = &receipt.header;
        if h.session_id != self.session_id {
            return Err("SessionIdMismatch".into());
        }
        if h.model_weight_root != self.model_weight_root {
            return Err("ModelWeightRootMismatch".into());
        }
        if h.layer_idx != self.layer_idx {
            return Err("LayerIndexMismatch".into());
        }
        if h.chunk_idx != self.expected_chunk_idx {
            return Err(format!(
                "ChunkIndexMismatch: got {}, expected {}",
                h.chunk_idx, self.expected_chunk_idx
            ));
        }
        if h.s_in_root != self.current_state_root {
            return Err("IncomingStateRootMismatch (`S_init = 0` reset / rollback / splice refused)".into());
        }
        verify_streaming_gdn_carry_receipt(receipt)?;
        self.expected_chunk_idx = self
            .expected_chunk_idx
            .checked_add(1)
            .ok_or_else(|| "chunk_idx u32 overflow".to_string())?;
        self.current_state_root = h.s_out_root;
        self.chain_digest = step_jitt_chain_digest(&self.chain_digest, h);
        Ok(())
    }
}

#[inline]
fn silu_f32(x: f32) -> f32 {
    x / (1.0 + (-x).exp())
}

#[inline]
fn sigmoid_f32(x: f32) -> f32 {
    1.0 / (1.0 + (-x).exp())
}

#[inline]
fn softplus_f32(x: f32) -> f32 {
    if x > 20.0 {
        x
    } else {
        (1.0 + x.exp()).ln()
    }
}

/// Preloaded 24-layer `Qwen/Qwen3.5-0.8B-Base` model (`18` GDN + `6` GQA) for fast multi-chunk benchmarks.
pub struct PreloadedQwen35JittModel {
    emb_bf16: Vec<u16>,
    final_norm_w: Vec<f32>,
    layers: Vec<PreloadedJittLayer>,
}

enum PreloadedJittLayer {
    Gdn {
        ln1_w: Vec<f32>,
        ln2_w: Vec<f32>,
        qkv_mat: Mxfp4Matrix,
        z_mat: Mxfp4Matrix,
        b_mat: Mxfp4Matrix,
        a_mat: Mxfp4Matrix,
        out_mat: Mxfp4Matrix,
        conv_w: Vec<f32>,
        a_log: Vec<f32>,
        dt_bias: Vec<f32>,
        norm_w: Vec<f32>,
        gate_mat: Mxfp4Matrix,
        up_mat: Mxfp4Matrix,
        down_mat: Mxfp4Matrix,
    },
    Gqa {
        ln1_w: Vec<f32>,
        ln2_w: Vec<f32>,
        q_mat: Mxfp4Matrix,
        k_mat: Mxfp4Matrix,
        v_mat: Mxfp4Matrix,
        o_mat: Mxfp4Matrix,
        qn_w: Vec<f32>,
        kn_w: Vec<f32>,
        gate_mat: Mxfp4Matrix,
        up_mat: Mxfp4Matrix,
        down_mat: Mxfp4Matrix,
    },
}

impl PreloadedQwen35JittModel {
    pub fn load_from_mmap(mmap: &MmapSafetensors) -> Result<Self, String> {
        let (emb_info, emb_raw) = mmap.tensor_bytes("model.language_model.embed_tokens.weight")?;
        if emb_info.shape != vec![248320, 1024] {
            return Err("unexpected embed_tokens shape".into());
        }
        let emb_bf16: Vec<u16> = emb_raw
            .chunks_exact(2)
            .map(|b| u16::from_le_bytes([b[0], b[1]]))
            .collect();
        let (_, final_norm_w) = mmap.read_f32("model.language_model.norm.weight")?;

        let layers: Result<Vec<PreloadedJittLayer>, String> = (0..24usize)
            .into_par_iter()
            .map(|l| {
                let pfx = format!("model.language_model.layers.{l}");
                let (_, ln1_w) = mmap.read_f32(&format!("{pfx}.input_layernorm.weight"))?;
                let (_, ln2_w) = mmap.read_f32(&format!("{pfx}.post_attention_layernorm.weight"))?;
                let gate_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.gate_proj.weight"))?;
                let up_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.up_proj.weight"))?;
                let down_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.down_proj.weight"))?;
                if (l % 4) != 3 {
                    Ok(PreloadedJittLayer::Gdn {
                        ln1_w,
                        ln2_w,
                        qkv_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.in_proj_qkv.weight"))?,
                        z_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.in_proj_z.weight"))?,
                        b_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.in_proj_b.weight"))?,
                        a_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.in_proj_a.weight"))?,
                        out_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.out_proj.weight"))?,
                        conv_w: mmap.read_f32(&format!("{pfx}.linear_attn.conv1d.weight"))?.1,
                        a_log: mmap.read_f32(&format!("{pfx}.linear_attn.A_log"))?.1,
                        dt_bias: mmap.read_f32(&format!("{pfx}.linear_attn.dt_bias"))?.1,
                        norm_w: mmap.read_f32(&format!("{pfx}.linear_attn.norm.weight"))?.1,
                        gate_mat,
                        up_mat,
                        down_mat,
                    })
                } else {
                    Ok(PreloadedJittLayer::Gqa {
                        ln1_w,
                        ln2_w,
                        q_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.q_proj.weight"))?,
                        k_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.k_proj.weight"))?,
                        v_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.v_proj.weight"))?,
                        o_mat: Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.o_proj.weight"))?,
                        qn_w: mmap.read_f32(&format!("{pfx}.self_attn.q_norm.weight"))?.1,
                        kn_w: mmap.read_f32(&format!("{pfx}.self_attn.k_norm.weight"))?.1,
                        gate_mat,
                        up_mat,
                        down_mat,
                    })
                }
            })
            .collect();

        Ok(Self {
            emb_bf16,
            final_norm_w,
            layers: layers?,
        })
    }

    pub fn greedy_top1_token(&self, final_h_1024: &[f32]) -> u32 {
        assert_eq!(final_h_1024.len(), 1024);
        let (best_tok, _) = (0..248320usize)
            .into_par_iter()
            .fold(
                || (0usize, f32::NEG_INFINITY),
                |(best_i, best_v), tid| {
                    let row = &self.emb_bf16[tid * 1024..(tid + 1) * 1024];
                    let mut dot = 0.0f32;
                    for d in 0..1024 {
                        dot += final_h_1024[d] * f32::from_bits((row[d] as u32) << 16);
                    }
                    if dot > best_v || (dot == best_v && tid < best_i) {
                        (tid, dot)
                    } else {
                        (best_i, best_v)
                    }
                },
            )
            .reduce(
                || (0usize, f32::NEG_INFINITY),
                |(i1, v1), (i2, v2)| {
                    if v1 > v2 || (v1 == v2 && i1 <= i2) {
                        (i1, v1)
                    } else {
                        (i2, v2)
                    }
                },
            );
        best_tok as u32
    }
}

/// Monolithic multi-chunk execution of all 24 `Qwen3.5-0.8B` layers on `C * 64` tokens at once
/// (holding the entire `[T, ...]` sequence in RAM as ground-truth reference for `0`-bit drift checks!).
pub fn execute_qwen35_monolithic_stateful(
    model: &PreloadedQwen35JittModel,
    token_ids: &[u32],
) -> (Vec<f32>, Vec<GdnRecurrentState>) {
    let seq_len = token_ids.len();
    assert!(seq_len > 0 && seq_len % JITT_CHUNK_LEN == 0);
    let num_chunks = seq_len / JITT_CHUNK_LEN;
    let d_model = 1024usize;
    let d_ff = 3584usize;
    let eps = 1e-6f32;

    let mut h_f32 = vec![0.0f32; seq_len * d_model];
    for (t, &tid) in token_ids.iter().enumerate() {
        let row = &model.emb_bf16[(tid as usize) * d_model..(tid as usize + 1) * d_model];
        for d in 0..d_model {
            h_f32[t * d_model + d] = f32::from_bits((row[d] as u32) << 16);
        }
    }
    let mut h_i16 = quantize_act_i16(&h_f32);
    for (hf, &hi) in h_f32.iter_mut().zip(h_i16.iter()) {
        *hf = (hi as f32) / (ACT_SCALE as f32);
    }

    let mut final_gdn_states = Vec::with_capacity(18);

    for lyr in &model.layers {
        let (ln1_w, ln2_w, gate_mat, up_mat, down_mat) = match lyr {
            PreloadedJittLayer::Gdn {
                ln1_w, ln2_w, gate_mat, up_mat, down_mat, ..
            }
            | PreloadedJittLayer::Gqa {
                ln1_w, ln2_w, gate_mat, up_mat, down_mat, ..
            } => (ln1_w, ln2_w, gate_mat, up_mat, down_mat),
        };
        let x_ln1_f32 = rmsnorm_zero_centered_f32(&h_f32, ln1_w, d_model, eps);
        let x_ln1_i16 = quantize_act_i16(&x_ln1_f32);

        let delta_attn_i16 = match lyr {
            PreloadedJittLayer::Gdn {
                qkv_mat,
                z_mat,
                b_mat,
                a_mat,
                out_mat,
                conv_w,
                a_log,
                dt_bias,
                norm_w,
                ..
            } => {
                let qkv_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, qkv_mat);
                let qkv_f32 = dequant_y_raw_to_f32(&qkv_raw, seq_len, 6144, qkv_mat.rows_pad);
                let z_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, z_mat);
                let z_f32 = dequant_y_raw_to_f32(&z_raw, seq_len, 2048, z_mat.rows_pad);
                let b_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, b_mat);
                let b_f32 = dequant_y_raw_to_f32(&b_raw, seq_len, 16, b_mat.rows_pad);
                let a_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, a_mat);
                let a_f32 = dequant_y_raw_to_f32(&a_raw, seq_len, 16, a_mat.rows_pad);

                let mut conv_out = vec![0.0f32; seq_len * 6144];
                for t in 0..seq_len {
                    for ch in 0..6144 {
                        let mut s = 0.0f32;
                        for kw in 0..4usize {
                            let src_t = (t as isize) - 3 + (kw as isize);
                            if src_t >= 0 {
                                s += qkv_f32[(src_t as usize) * 6144 + ch] * conv_w[ch * 4 + kw];
                            }
                        }
                        conv_out[t * 6144 + ch] = silu_f32(s);
                    }
                }

                let mut s_cur = GdnRecurrentState::zero();
                let mut y_all = vec![0.0f32; seq_len * 2048];
                for c in 0..num_chunks {
                    let t0 = c * JITT_CHUNK_LEN;
                    let mut q_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut k_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut v_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut g_c = vec![0.0f32; JITT_CHUNK_LEN * 16];
                    let mut beta_c = vec![0.0f32; JITT_CHUNK_LEN * 16];
                    for ti in 0..JITT_CHUNK_LEN {
                        let t = t0 + ti;
                        q_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[t * 6144..t * 6144 + 2048]);
                        k_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[t * 6144 + 2048..t * 6144 + 4096]);
                        v_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[t * 6144 + 4096..t * 6144 + 6144]);
                        for h in 0..16 {
                            beta_c[ti * 16 + h] = sigmoid_f32(b_f32[t * 16 + h]);
                            g_c[ti * 16 + h] = -a_log[h].exp() * softplus_f32(a_f32[t * 16 + h] + dt_bias[h]);
                        }
                    }
                    let wit = solve_stateful_gdn_wy_chunk64(&q_c, &k_c, &v_c, &g_c, &beta_c, &s_cur);
                    y_all[t0 * 2048..(t0 + JITT_CHUNK_LEN) * 2048].copy_from_slice(&wit.y_out_f32);
                    s_cur = wit.s_out;
                }
                final_gdn_states.push(s_cur);

                let mut gated_f32 = vec![0.0f32; seq_len * 2048];
                for t in 0..seq_len {
                    for h in 0..16 {
                        let off = (t * 16 + h) * 128;
                        let ys = &y_all[off..off + 128];
                        let zs = &z_f32[off..off + 128];
                        let inv_rms = 1.0 / (ys.iter().map(|&v| v * v).sum::<f32>() / 128.0 + eps).sqrt();
                        for d in 0..128 {
                            gated_f32[off + d] = norm_w[d] * (ys[d] * inv_rms) * silu_f32(zs[d]);
                        }
                    }
                }
                let gated_i16 = quantize_act_i16(&gated_f32);
                let out_raw = eval_mxfp4_int_contraction(&gated_i16, seq_len, 2048, out_mat);
                let out_f32 = dequant_y_raw_to_f32(&out_raw, seq_len, d_model, out_mat.rows_pad);
                quantize_act_i16(&out_f32)
            }
            PreloadedJittLayer::Gqa {
                q_mat, k_mat, v_mat, o_mat, qn_w, kn_w, ..
            } => {
                let qg_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, q_mat);
                let qg_f32 = dequant_y_raw_to_f32(&qg_raw, seq_len, 4096, q_mat.rows_pad);
                let k_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, k_mat);
                let k_proj_f32 = dequant_y_raw_to_f32(&k_raw, seq_len, 512, k_mat.rows_pad);
                let v_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, v_mat);
                let v_proj_f32 = dequant_y_raw_to_f32(&v_raw, seq_len, 512, v_mat.rows_pad);

                let mut q_heads = vec![0.0f32; seq_len * 8 * 256];
                let mut gate_f32 = vec![0.0f32; seq_len * 2048];
                for t in 0..seq_len {
                    for h in 0..8 {
                        let src = &qg_f32[(t * 8 + h) * 512..(t * 8 + h + 1) * 512];
                        q_heads[(t * 8 + h) * 256..(t * 8 + h + 1) * 256].copy_from_slice(&src[..256]);
                        gate_f32[(t * 8 + h) * 256..(t * 8 + h + 1) * 256].copy_from_slice(&src[256..]);
                    }
                }
                let mut q_normed = rmsnorm_zero_centered_f32(&q_heads, qn_w, 256, eps);
                let mut k_normed = rmsnorm_zero_centered_f32(&k_proj_f32, kn_w, 256, eps);

                for t in 0..seq_len {
                    for pair in 0..32usize {
                        let freq = 1.0f32 / 10_000_000.0f32.powf((2 * pair) as f32 / 64.0);
                        let (cs, sn) = ((t as f32 * freq).cos(), (t as f32 * freq).sin());
                        for h in 0..8 {
                            let base = (t * 8 + h) * 256;
                            let (x1, x2) = (q_normed[base + pair], q_normed[base + 32 + pair]);
                            q_normed[base + pair] = x1 * cs - x2 * sn;
                            q_normed[base + 32 + pair] = x2 * cs + x1 * sn;
                        }
                        for hk in 0..2 {
                            let base = (t * 2 + hk) * 256;
                            let (x1, x2) = (k_normed[base + pair], k_normed[base + 32 + pair]);
                            k_normed[base + pair] = x1 * cs - x2 * sn;
                            k_normed[base + 32 + pair] = x2 * cs + x1 * sn;
                        }
                    }
                }

                let scale = 1.0f32 / 256.0f32.sqrt();
                let mut attn_out = vec![0.0f32; seq_len * 2048];
                for h in 0..8usize {
                    let hk = h / 4;
                    for ti in 0..seq_len {
                        let qi = &q_normed[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                        let mut scores = vec![0.0f32; ti + 1];
                        let mut max_s = f32::NEG_INFINITY;
                        for tj in 0..=ti {
                            let kj = &k_normed[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                            let s = qi.iter().zip(kj.iter()).map(|(&a, &b)| a * b).sum::<f32>() * scale;
                            scores[tj] = s;
                            if s > max_s {
                                max_s = s;
                            }
                        }
                        let mut sum_e = 0.0f32;
                        for s in &mut scores {
                            *s = (*s - max_s).exp();
                            sum_e += *s;
                        }
                        let dst = &mut attn_out[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                        for tj in 0..=ti {
                            let w = scores[tj] / sum_e;
                            let vj = &v_proj_f32[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                            for d in 0..256 {
                                dst[d] += w * vj[d];
                            }
                        }
                    }
                }
                for i in 0..(seq_len * 2048) {
                    attn_out[i] *= sigmoid_f32(gate_f32[i]);
                }
                let attn_i16 = quantize_act_i16(&attn_out);
                let o_raw = eval_mxfp4_int_contraction(&attn_i16, seq_len, 2048, o_mat);
                let o_f32 = dequant_y_raw_to_f32(&o_raw, seq_len, d_model, o_mat.rows_pad);
                quantize_act_i16(&o_f32)
            }
        };

        let mut h_mid_i16 = vec![0i16; seq_len * d_model];
        let mut h_mid_f32 = vec![0.0f32; seq_len * d_model];
        for i in 0..(seq_len * d_model) {
            let sum_i = (h_i16[i] as i32 + delta_attn_i16[i] as i32)
                .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
            h_mid_i16[i] = sum_i;
            h_mid_f32[i] = (sum_i as f32) / (ACT_SCALE as f32);
        }

        let x_ln2_f32 = rmsnorm_zero_centered_f32(&h_mid_f32, ln2_w, d_model, eps);
        let x_ln2_i16 = quantize_act_i16(&x_ln2_f32);
        let gate_raw = eval_mxfp4_int_contraction(&x_ln2_i16, seq_len, d_model, gate_mat);
        let gate_f32 = dequant_y_raw_to_f32(&gate_raw, seq_len, d_ff, gate_mat.rows_pad);
        let up_raw = eval_mxfp4_int_contraction(&x_ln2_i16, seq_len, d_model, up_mat);
        let up_f32 = dequant_y_raw_to_f32(&up_raw, seq_len, d_ff, up_mat.rows_pad);

        let mut swiglu_f32 = vec![0.0f32; seq_len * d_ff];
        for i in 0..(seq_len * d_ff) {
            swiglu_f32[i] = silu_f32(gate_f32[i]) * up_f32[i];
        }
        let swiglu_i16 = quantize_act_i16(&swiglu_f32);
        let down_raw = eval_mxfp4_int_contraction(&swiglu_i16, seq_len, d_ff, down_mat);
        let down_f32 = dequant_y_raw_to_f32(&down_raw, seq_len, d_model, down_mat.rows_pad);
        let delta_mlp_i16 = quantize_act_i16(&down_f32);

        for i in 0..(seq_len * d_model) {
            let next_i = (h_mid_i16[i] as i32 + delta_mlp_i16[i] as i32)
                .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
            h_i16[i] = next_i;
            h_f32[i] = (next_i as f32) / (ACT_SCALE as f32);
        }
    }

    let final_h = rmsnorm_zero_centered_f32(&h_f32, &model.final_norm_w, d_model, eps);
    (final_h, final_gdn_states)
}

/// Streaming Wearable JITT Session evicting past chunks' activations, WY tables, and WHIR provers
/// immediately upon advancing `rt_{S,c} -> rt_{S,c+1}` (`O(1)` live GDN state across arbitrary `C`!).
pub struct WearableJittStreamingSession {
    pub session_id: [u8; 32],
    pub model_weight_root: [u8; 32],
    pub audited_layer: usize,
    pub chunk_idx: u32,
    pub evicted_chunks: usize,
    gdn_states: Vec<GdnRecurrentState>,
    gdn_conv_tails: Vec<Vec<f32>>, // `18` layers x `[3 * 6144]` `O(1)` causal conv1d ring tails
    gqa_k_cache: Vec<Vec<f32>>,
    gqa_v_cache: Vec<Vec<f32>>,
    current_audited_commit: SaltedGdnStateCommitment,
}

pub struct StreamingChunkStepResult {
    pub chunk_idx: u32,
    pub chunk_final_h: Vec<f32>,
    pub receipt: StreamingGdnCarryReceipt,
    pub retained_gdn_ram_bytes: usize,
    pub evicted_prover_scratch_bytes: usize,
}

impl WearableJittStreamingSession {
    pub fn new(
        session_id: [u8; 32],
        model_weight_root: [u8; 32],
        audited_layer: usize,
        opt_genesis_seed: Option<[u8; 32]>,
    ) -> Self {
        assert!(audited_layer < 24 && (audited_layer % 4) != 3);
        let current_audited_commit =
            SaltedGdnStateCommitment::commit(GdnRecurrentState::zero(), opt_genesis_seed);
        Self {
            session_id,
            model_weight_root,
            audited_layer,
            chunk_idx: 0,
            evicted_chunks: 0,
            gdn_states: (0..18).map(|_| GdnRecurrentState::zero()).collect(),
            gdn_conv_tails: (0..18).map(|_| vec![0.0f32; 3 * 6144]).collect(),
            gqa_k_cache: (0..6).map(|_| Vec::new()).collect(),
            gqa_v_cache: (0..6).map(|_| Vec::new()).collect(),
            current_audited_commit,
        }
    }

    #[inline]
    pub fn genesis_state_root(&self) -> [u8; 32] {
        assert_eq!(self.chunk_idx, 0);
        self.current_audited_commit.root()
    }

    #[inline]
    pub fn current_state_root(&self) -> [u8; 32] {
        self.current_audited_commit.root()
    }

    pub fn gdn_states(&self) -> &[GdnRecurrentState] {
        &self.gdn_states
    }

    ///Constant `O(1)` live GDN recurrent + `conv1d` state footprint across all 18 GDN layers.
    pub fn retained_gdn_ram_bytes(&self) -> usize {
        let s_bytes: usize = self.gdn_states.iter().map(|s| s.live_ram_bytes()).sum();
        let c_bytes: usize = self.gdn_conv_tails.iter().map(|v| v.len() * 4).sum();
        s_bytes + c_bytes + 32 // +32B `rt_{S,c}`
    }

    /// Execute ONE 64-token chunk, prove `StreamingGdnCarryReceipt` (`rt_{S,c} -> rt_{S,c+1}`),
    /// advance live `O(1)` GDN state, and immediately evict Chunk `c`'s witness & incoming commitment!
    pub fn step_chunk_64(
        &mut self,
        model: &PreloadedQwen35JittModel,
        chunk_tokens_64: &[u32],
        opt_seed: Option<[u8; 32]>,
    ) -> Result<StreamingChunkStepResult, String> {
        if chunk_tokens_64.len() != JITT_CHUNK_LEN {
            return Err("chunk_tokens_64 must have exact length 64".into());
        }
        let d_model = 1024usize;
        let d_ff = 3584usize;
        let eps = 1e-6f32;
        let abs_t0 = (self.chunk_idx as usize) * JITT_CHUNK_LEN;

        let mut h_f32 = vec![0.0f32; JITT_CHUNK_LEN * d_model];
        for (ti, &tid) in chunk_tokens_64.iter().enumerate() {
            let row = &model.emb_bf16[(tid as usize) * d_model..(tid as usize + 1) * d_model];
            for d in 0..d_model {
                h_f32[ti * d_model + d] = f32::from_bits((row[d] as u32) << 16);
            }
        }
        let mut h_i16 = quantize_act_i16(&h_f32);
        for (hf, &hi) in h_f32.iter_mut().zip(h_i16.iter()) {
            *hf = (hi as f32) / (ACT_SCALE as f32);
        }

        let mut gdn_ord = 0usize;
        let mut gqa_ord = 0usize;
        let mut opt_audited_wit: Option<StatefulGdnCarryWitness> = None;

        for (l, lyr) in model.layers.iter().enumerate() {
            let (ln1_w, ln2_w, gate_mat, up_mat, down_mat) = match lyr {
                PreloadedJittLayer::Gdn {
                    ln1_w, ln2_w, gate_mat, up_mat, down_mat, ..
                }
                | PreloadedJittLayer::Gqa {
                    ln1_w, ln2_w, gate_mat, up_mat, down_mat, ..
                } => (ln1_w, ln2_w, gate_mat, up_mat, down_mat),
            };
            let x_ln1_f32 = rmsnorm_zero_centered_f32(&h_f32, ln1_w, d_model, eps);
            let x_ln1_i16 = quantize_act_i16(&x_ln1_f32);

            let delta_attn_i16 = match lyr {
                PreloadedJittLayer::Gdn {
                    qkv_mat,
                    z_mat,
                    b_mat,
                    a_mat,
                    out_mat,
                    conv_w,
                    a_log,
                    dt_bias,
                    norm_w,
                    ..
                } => {
                    let qkv_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, qkv_mat);
                    let qkv_f32 = dequant_y_raw_to_f32(&qkv_raw, JITT_CHUNK_LEN, 6144, qkv_mat.rows_pad);
                    let z_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, z_mat);
                    let z_f32 = dequant_y_raw_to_f32(&z_raw, JITT_CHUNK_LEN, 2048, z_mat.rows_pad);
                    let b_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, b_mat);
                    let b_f32 = dequant_y_raw_to_f32(&b_raw, JITT_CHUNK_LEN, 16, b_mat.rows_pad);
                    let a_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, a_mat);
                    let a_f32 = dequant_y_raw_to_f32(&a_raw, JITT_CHUNK_LEN, 16, a_mat.rows_pad);

                    let tail = &self.gdn_conv_tails[gdn_ord];
                    let mut conv_out = vec![0.0f32; JITT_CHUNK_LEN * 6144];
                    for ti in 0..JITT_CHUNK_LEN {
                        for ch in 0..6144 {
                            let mut s = 0.0f32;
                            for kw in 0..4usize {
                                let rel = (ti as isize) - 3 + (kw as isize);
                                if rel >= 0 {
                                    s += qkv_f32[(rel as usize) * 6144 + ch] * conv_w[ch * 4 + kw];
                                } else if self.chunk_idx > 0 {
                                    let tail_t = (rel + 3) as usize;
                                    s += tail[tail_t * 6144 + ch] * conv_w[ch * 4 + kw];
                                }
                            }
                            conv_out[ti * 6144 + ch] = silu_f32(s);
                        }
                    }
                    self.gdn_conv_tails[gdn_ord]
                        .copy_from_slice(&qkv_f32[(JITT_CHUNK_LEN - 3) * 6144..JITT_CHUNK_LEN * 6144]);

                    let mut q_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut k_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut v_c = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    let mut g_c = vec![0.0f32; JITT_CHUNK_LEN * 16];
                    let mut beta_c = vec![0.0f32; JITT_CHUNK_LEN * 16];
                    for ti in 0..JITT_CHUNK_LEN {
                        q_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[ti * 6144..ti * 6144 + 2048]);
                        k_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[ti * 6144 + 2048..ti * 6144 + 4096]);
                        v_c[ti * 2048..(ti + 1) * 2048].copy_from_slice(&conv_out[ti * 6144 + 4096..ti * 6144 + 6144]);
                        for h in 0..16 {
                            beta_c[ti * 16 + h] = sigmoid_f32(b_f32[ti * 16 + h]);
                            g_c[ti * 16 + h] = -a_log[h].exp() * softplus_f32(a_f32[ti * 16 + h] + dt_bias[h]);
                        }
                    }

                    let wit = solve_stateful_gdn_wy_chunk64(
                        &q_c,
                        &k_c,
                        &v_c,
                        &g_c,
                        &beta_c,
                        &self.gdn_states[gdn_ord],
                    );

                    let mut gated_f32 = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    for ti in 0..JITT_CHUNK_LEN {
                        for h in 0..16 {
                            let off = (ti * 16 + h) * 128;
                            let ys = &wit.y_out_f32[off..off + 128];
                            let zs = &z_f32[off..off + 128];
                            let inv_rms = 1.0 / (ys.iter().map(|&v| v * v).sum::<f32>() / 128.0 + eps).sqrt();
                            for d in 0..128 {
                                gated_f32[off + d] = norm_w[d] * (ys[d] * inv_rms) * silu_f32(zs[d]);
                            }
                        }
                    }
                    self.gdn_states[gdn_ord] = wit.s_out.clone();
                    if l == self.audited_layer {
                        opt_audited_wit = Some(wit);
                    }
                    gdn_ord += 1;

                    let gated_i16 = quantize_act_i16(&gated_f32);
                    let out_raw = eval_mxfp4_int_contraction(&gated_i16, JITT_CHUNK_LEN, 2048, out_mat);
                    let out_f32 = dequant_y_raw_to_f32(&out_raw, JITT_CHUNK_LEN, d_model, out_mat.rows_pad);
                    quantize_act_i16(&out_f32)
                }
                PreloadedJittLayer::Gqa {
                    q_mat, k_mat, v_mat, o_mat, qn_w, kn_w, ..
                } => {
                    let qg_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, q_mat);
                    let qg_f32 = dequant_y_raw_to_f32(&qg_raw, JITT_CHUNK_LEN, 4096, q_mat.rows_pad);
                    let k_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, k_mat);
                    let k_proj_f32 = dequant_y_raw_to_f32(&k_raw, JITT_CHUNK_LEN, 512, k_mat.rows_pad);
                    let v_raw = eval_mxfp4_int_contraction(&x_ln1_i16, JITT_CHUNK_LEN, d_model, v_mat);
                    let v_proj_f32 = dequant_y_raw_to_f32(&v_raw, JITT_CHUNK_LEN, 512, v_mat.rows_pad);

                    let mut q_heads = vec![0.0f32; JITT_CHUNK_LEN * 8 * 256];
                    let mut gate_f32 = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    for ti in 0..JITT_CHUNK_LEN {
                        for h in 0..8 {
                            let src = &qg_f32[(ti * 8 + h) * 512..(ti * 8 + h + 1) * 512];
                            q_heads[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256].copy_from_slice(&src[..256]);
                            gate_f32[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256].copy_from_slice(&src[256..]);
                        }
                    }
                    let mut q_normed = rmsnorm_zero_centered_f32(&q_heads, qn_w, 256, eps);
                    let mut k_normed = rmsnorm_zero_centered_f32(&k_proj_f32, kn_w, 256, eps);

                    for ti in 0..JITT_CHUNK_LEN {
                        let abs_t = abs_t0 + ti;
                        for pair in 0..32usize {
                            let freq = 1.0f32 / 10_000_000.0f32.powf((2 * pair) as f32 / 64.0);
                            let (cs, sn) = ((abs_t as f32 * freq).cos(), (abs_t as f32 * freq).sin());
                            for h in 0..8 {
                                let base = (ti * 8 + h) * 256;
                                let (x1, x2) = (q_normed[base + pair], q_normed[base + 32 + pair]);
                                q_normed[base + pair] = x1 * cs - x2 * sn;
                                q_normed[base + 32 + pair] = x2 * cs + x1 * sn;
                            }
                            for hk in 0..2 {
                                let base = (ti * 2 + hk) * 256;
                                let (x1, x2) = (k_normed[base + pair], k_normed[base + 32 + pair]);
                                k_normed[base + pair] = x1 * cs - x2 * sn;
                                k_normed[base + 32 + pair] = x2 * cs + x1 * sn;
                            }
                        }
                    }

                    self.gqa_k_cache[gqa_ord].extend_from_slice(&k_normed);
                    self.gqa_v_cache[gqa_ord].extend_from_slice(&v_proj_f32);
                    let k_all = &self.gqa_k_cache[gqa_ord];
                    let v_all = &self.gqa_v_cache[gqa_ord];
                    gqa_ord += 1;

                    let scale = 1.0f32 / 256.0f32.sqrt();
                    let mut attn_out = vec![0.0f32; JITT_CHUNK_LEN * 2048];
                    for h in 0..8usize {
                        let hk = h / 4;
                        for ti in 0..JITT_CHUNK_LEN {
                            let abs_ti = abs_t0 + ti;
                            let qi = &q_normed[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                            let mut scores = vec![0.0f32; abs_ti + 1];
                            let mut max_s = f32::NEG_INFINITY;
                            for tj in 0..=abs_ti {
                                let kj = &k_all[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                                let s = qi.iter().zip(kj.iter()).map(|(&a, &b)| a * b).sum::<f32>() * scale;
                                scores[tj] = s;
                                if s > max_s {
                                    max_s = s;
                                }
                            }
                            let mut sum_e = 0.0f32;
                            for s in &mut scores {
                                *s = (*s - max_s).exp();
                                sum_e += *s;
                            }
                            let dst = &mut attn_out[(ti * 8 + h) * 256..(ti * 8 + h + 1) * 256];
                            for tj in 0..=abs_ti {
                                let w = scores[tj] / sum_e;
                                let vj = &v_all[(tj * 2 + hk) * 256..(tj * 2 + hk + 1) * 256];
                                for d in 0..256 {
                                    dst[d] += w * vj[d];
                                }
                            }
                        }
                    }
                    for i in 0..(JITT_CHUNK_LEN * 2048) {
                        attn_out[i] *= sigmoid_f32(gate_f32[i]);
                    }
                    let attn_i16 = quantize_act_i16(&attn_out);
                    let o_raw = eval_mxfp4_int_contraction(&attn_i16, JITT_CHUNK_LEN, 2048, o_mat);
                    let o_f32 = dequant_y_raw_to_f32(&o_raw, JITT_CHUNK_LEN, d_model, o_mat.rows_pad);
                    quantize_act_i16(&o_f32)
                }
            };

            let mut h_mid_i16 = vec![0i16; JITT_CHUNK_LEN * d_model];
            let mut h_mid_f32 = vec![0.0f32; JITT_CHUNK_LEN * d_model];
            for i in 0..(JITT_CHUNK_LEN * d_model) {
                let sum_i = (h_i16[i] as i32 + delta_attn_i16[i] as i32)
                    .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
                h_mid_i16[i] = sum_i;
                h_mid_f32[i] = (sum_i as f32) / (ACT_SCALE as f32);
            }

            let x_ln2_f32 = rmsnorm_zero_centered_f32(&h_mid_f32, ln2_w, d_model, eps);
            let x_ln2_i16 = quantize_act_i16(&x_ln2_f32);
            let gate_raw = eval_mxfp4_int_contraction(&x_ln2_i16, JITT_CHUNK_LEN, d_model, gate_mat);
            let gate_f32 = dequant_y_raw_to_f32(&gate_raw, JITT_CHUNK_LEN, d_ff, gate_mat.rows_pad);
            let up_raw = eval_mxfp4_int_contraction(&x_ln2_i16, JITT_CHUNK_LEN, d_model, up_mat);
            let up_f32 = dequant_y_raw_to_f32(&up_raw, JITT_CHUNK_LEN, d_ff, up_mat.rows_pad);

            let mut swiglu_f32 = vec![0.0f32; JITT_CHUNK_LEN * d_ff];
            for i in 0..(JITT_CHUNK_LEN * d_ff) {
                swiglu_f32[i] = silu_f32(gate_f32[i]) * up_f32[i];
            }
            let swiglu_i16 = quantize_act_i16(&swiglu_f32);
            let down_raw = eval_mxfp4_int_contraction(&swiglu_i16, JITT_CHUNK_LEN, d_ff, down_mat);
            let down_f32 = dequant_y_raw_to_f32(&down_raw, JITT_CHUNK_LEN, d_model, down_mat.rows_pad);
            let delta_mlp_i16 = quantize_act_i16(&down_f32);

            for i in 0..(JITT_CHUNK_LEN * d_model) {
                let next_i = (h_mid_i16[i] as i32 + delta_mlp_i16[i] as i32)
                    .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
                h_i16[i] = next_i;
                h_f32[i] = (next_i as f32) / (ACT_SCALE as f32);
            }
        }

        let chunk_final_h = rmsnorm_zero_centered_f32(&h_f32, &model.final_norm_w, d_model, eps);
        let audited_wit = opt_audited_wit.ok_or_else(|| "missing audited GDN witness".to_string())?;
        let tok_commit = compute_chunk_token_commitment(&self.session_id, self.chunk_idx, chunk_tokens_64);

        let next_commit_seed = opt_seed.map(|s| cshake256_32(b"QW35-JITT-NEXT-SC-V1", &s));
        let next_audited_commit =
            SaltedGdnStateCommitment::commit(audited_wit.s_out.clone(), next_commit_seed);

        let cur_idx = self.chunk_idx;
        let receipt = prove_streaming_gdn_carry_receipt(
            self.session_id,
            self.model_weight_root,
            self.audited_layer as u32,
            cur_idx,
            tok_commit,
            &self.current_audited_commit,
            &next_audited_commit,
            &audited_wit,
            opt_seed,
        )?;

        // Measure & explicitly evict Chunk `c`'s `WhirCommittedMatrixExt4` (`cw0`, `coeffs`, `tree0`) + `audited_wit`!
        let evicted_prover_scratch_bytes = (self.current_audited_commit.whir_mat.cw0.len()
            + self.current_audited_commit.whir_mat.coeffs.len()
            + audited_wit.k_dec_lsb_hik.len() * 7
            + audited_wit.r_st_lsb_hvk.len()
            + (1usize << JITT_D1B_WIT_VARS)
            + 140 * 262_144)
            * 4;

        let old_commit = std::mem::replace(&mut self.current_audited_commit, next_audited_commit);
        drop(old_commit);
        drop(audited_wit);

        self.chunk_idx += 1;
        self.evicted_chunks += 1;

        Ok(StreamingChunkStepResult {
            chunk_idx: cur_idx,
            chunk_final_h,
            receipt,
            retained_gdn_ram_bytes: self.retained_gdn_ram_bytes(),
            evicted_prover_scratch_bytes,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dual_mask_tvd_zero_bijection_and_nonzero_state_carry_unit() {
        // Verify exact bijection on `(M_1, M_2) -> (M_1 - M_2, alpha * s + M_1)` over `Ext4`
        let alpha = Ext4([17, 42, 99, 12345]);
        let s_a = Ext4([987654, 111, 222, 333]);
        let s_b = Ext4([1, 2, 3, 4]);
        let target_delta = Ext4([777, 888, 999, 1010]);
        let target_mu = Ext4([5555, 6666, 7777, 8888]);

        let inv_for = |s: Ext4| -> (Ext4, Ext4) {
            let m1 = target_mu.sub(alpha.mul(s));
            let m2 = m1.sub(target_delta);
            (m1, m2)
        };
        let (m1_a, m2_a) = inv_for(s_a);
        let (m1_b, m2_b) = inv_for(s_b);
        assert_eq!(m1_a.sub(m2_a), target_delta);
        assert_eq!(alpha.mul(s_a).add(m1_a), target_mu);
        assert_eq!(m1_b.sub(m2_b), target_delta);
        assert_eq!(alpha.mul(s_b).add(m1_b), target_mu);
        assert_ne!((m1_a, m2_a), (m1_b, m2_b));
    }
}
