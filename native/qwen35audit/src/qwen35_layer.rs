//! Real Pretrained `Qwen/Qwen3.5-0.8B-Base` (`24L = 18 GDN + 6 GQA`) & `Qwen/Qwen3.8-Flash-Next` (`H_v = 48`)
//! Layer Execution, Division-Free Fixed-Point `C = 64` Chunkwise WY Witness Solver, and Succinct `Ext4`
//! Layer Prover + Standalone Verifier (`0` witness access!).

use crate::ext4::{
    badd, bb_from_i64, bmul, bsub, build_eq_table_lsb_ext4, cshake256_32, mle_eval_bb_at_ext4,
    ByteCursor, CShakeTranscript, Ext4, MerkleSinglePath, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, prove_d1b_range_ext4, prove_gruen_einsum_mode2_ext4,
    prove_mxfp4_delayed_bjk_horner_ext4, prove_strict_lower_tri_ext4, verify_d1b_range_ext4,
    verify_gruen_einsum_mode2_ext4, verify_mxfp4_delayed_bjk_horner_ext4,
    verify_strict_lower_tri_ext4, D1bRangeExt4Proof, GruenMode2Ext4Proof, Mxfp4DelayedBjkExt4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams,
    PcsShape,
};
use crate::safetensors_mmap::{
    decode_e2m1_x2_bb, decode_e2m1_x2_i32, MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry,
    ACT_SCALE, ACT_SHIFT, WY_SCALE, WY_SHIFT, W_SCALE_BASE, W_SCALE_SHIFT,
};
use rayon::prelude::*;
use std::ops::{Add, Sub};

/// Pad `cols_orig` (multiple of 32) up to `cols_orig.next_power_of_two()` (e.g. `3584 -> 4096`) with zero blocks
/// so both `rows_pad = 2^log_j` and `blocks_pad = 2^log_k` are exact powers of two for `MXFP4` `b -> j -> k` sumcheck!
pub fn pad_mxfp4_cols_pow2(mat: &Mxfp4Matrix) -> (usize, usize, Vec<u8>, Vec<u32>) {
    let j_len = mat.rows_pad;
    let k_orig = mat.blocks_per_row;
    let k_pad = k_orig.next_power_of_two();
    if k_pad == k_orig {
        return (j_len, k_pad, mat.nibbles.clone(), mat.scales.clone());
    }
    let mut nibs = vec![0u8; j_len * k_pad * 32];
    let mut scs = vec![0u32; j_len * k_pad];
    for j in 0..j_len {
        nibs[j * k_pad * 32..j * k_pad * 32 + k_orig * 32]
            .copy_from_slice(&mat.nibbles[j * k_orig * 32..(j + 1) * k_orig * 32]);
        scs[j * k_pad..j * k_pad + k_orig]
            .copy_from_slice(&mat.scales[j * k_orig..(j + 1) * k_orig]);
    }
    (j_len, k_pad, nibs, scs)
}

/// Exact integer `MXFP4` contraction `Y_raw[i, j] = sum_{k, b} X[i, k*32+b] * decode_e2m1_x2(Q[j, k*32+b]) * S[j, k]`.
pub fn eval_mxfp4_int_contraction(
    x_i16: &[i16],
    seq_len: usize,
    in_dim: usize,
    mat: &Mxfp4Matrix,
) -> Vec<i64> {
    assert_eq!(x_i16.len(), seq_len * in_dim);
    assert_eq!(mat.cols_orig, in_dim);
    let j_len = mat.rows_pad;
    let k_len = mat.blocks_per_row;
    let mut y_raw = vec![0i64; seq_len * j_len];

    y_raw
        .par_chunks_mut(j_len)
        .enumerate()
        .for_each(|(t, y_row)| {
            let x_row = &x_i16[t * in_dim..(t + 1) * in_dim];
            for (j, y_cell) in y_row.iter_mut().take(mat.rows_orig).enumerate() {
                let mut acc = 0i64;
                for k in 0..k_len {
                    let s = mat.scales[j * k_len + k] as i64;
                    if s == 0 {
                        continue;
                    }
                    let q_blk = &mat.nibbles[(j * k_len + k) * 32..(j * k_len + k + 1) * 32];
                    let x_blk = &x_row[k * 32..(k + 1) * 32];
                    let mut b_sum = 0i64;
                    for b in 0..32 {
                        b_sum += (x_blk[b] as i64) * (decode_e2m1_x2_i32(q_blk[b]) as i64);
                    }
                    acc += s * b_sum;
                }
                assert!(
                    acc.abs() < (P as i64) / 2,
                    "BabyBear wraparound guard tripped: |Y_raw| = {}",
                    acc.abs()
                );
                *y_cell = acc;
            }
        });
    y_raw
}

/// Dequantize `Y_raw[i, j]` (`ACT_SCALE * 2 * W_SCALE_BASE`) back to `f32` `[seq_len * rows_orig]`.
pub fn dequant_y_raw_to_f32(
    y_raw: &[i64],
    seq_len: usize,
    rows_orig: usize,
    rows_pad: usize,
) -> Vec<f32> {
    let denom = (ACT_SCALE as f32) * 2.0 * W_SCALE_BASE;
    let mut out = vec![0.0f32; seq_len * rows_orig];
    for t in 0..seq_len {
        for j in 0..rows_orig {
            out[t * rows_orig + j] = (y_raw[t * rows_pad + j] as f32) / denom;
        }
    }
    out
}

/// Quantize `f32` activations into `i16` at `ACT_SCALE = 128`.
pub fn quantize_act_i16(x: &[f32]) -> Vec<i16> {
    x.iter()
        .map(|&v| {
            let q = (v * (ACT_SCALE as f32)).round() as i32;
            q.clamp(i16::MIN as i32, i16::MAX as i32) as i16
        })
        .collect()
}

pub fn rmsnorm_zero_centered_f32(x: &[f32], w: &[f32], dim: usize, eps: f32) -> Vec<f32> {
    let rows = x.len() / dim;
    let mut out = vec![0.0f32; x.len()];
    for r in 0..rows {
        let xr = &x[r * dim..(r + 1) * dim];
        let mean_sq = xr.iter().map(|&v| v * v).sum::<f32>() / (dim as f32);
        let inv_rms = 1.0 / (mean_sq + eps).sqrt();
        let orow = &mut out[r * dim..(r + 1) * dim];
        for d in 0..dim {
            orow[d] = xr[d] * inv_rms * (1.0 + w[d]);
        }
    }
    out
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

/// Complete division-free fixed-point `C = 64` chunkwise WY witness (`H_v` real heads padded to `h_pad = H_v.next_power_of_two()`).
/// Works identically for **both** `Qwen3.5-0.8B` (`H_v = 16 -> h_pad = 16`) and `Qwen3.8-Flash-Next` (`H_v = 48 -> h_pad = 64`)!
#[derive(Clone, Debug)]
pub struct RealGdnWyWitness {
    pub h_v_orig: usize,
    pub h_pad: usize,
    pub c_len: usize,
    pub d_k: usize,
    pub d_v: usize,
    /// `[h_pad * c_len * c_len]` LSB-indexed `h + (i << log_h) + (j << (log_h + log_c))` canonical BabyBear!
    pub l_lsb_hij: Vec<u32>,
    /// `[h_pad * c_len * (d_v + d_k)]` LSB-indexed `h + (i << log_h) + (col << (log_h + log_c))` canonical BabyBear!
    pub rhs_lsb_hik: Vec<u32>,
    /// `[h_pad * c_len * (d_v + d_k)]` LSB-indexed `h + (i << log_h) + (col << (log_h + log_c))` canonical BabyBear!
    pub uw_lsb_hik: Vec<u32>,
    /// `[h_pad * c_len * (d_v + d_k)]` remainder in `[0, WY_SCALE)` (`4096`), `2048` on padded zero heads!
    pub rem_lsb_hik: Vec<u32>,
    /// Float readout `[c_len * h_v_orig * d_v]` for feeding downstream `RMSNormGated + out_proj`.
    pub y_out_f32: Vec<f32>,
}

/// Shape parameters for [`solve_real_gdn_wy_chunk64`].
#[derive(Clone, Copy, Debug)]
pub struct GdnWyShape {
    pub h_k: usize,
    pub h_v: usize,
    pub c_len: usize,
    pub d_k: usize,
    pub d_v: usize,
}

type GdnHeadWyOutputs = (Vec<i64>, Vec<i64>, Vec<i64>, Vec<u32>, Vec<f32>);

/// Solve division-free fixed-point `C = 64` chunkwise WY `(I + L_tilde / M_wy) UW = RHS` from real
/// L2-normalized `q, k` (`[c_len, h_k, d_k]`), `v` (`[c_len, h_v, d_v]`), `g` (`[c_len, h_v]`), `beta` (`[c_len, h_v]`).
pub fn solve_real_gdn_wy_chunk64(
    q: &[f32],
    k: &[f32],
    v: &[f32],
    g: &[f32],
    beta: &[f32],
    shape: GdnWyShape,
) -> RealGdnWyWitness {
    let GdnWyShape {
        h_k,
        h_v,
        c_len,
        d_k,
        d_v,
    } = shape;
    assert!(c_len.is_power_of_two() && (d_v + d_k).is_power_of_two());
    assert_eq!(h_v % h_k, 0);
    let gva_rep = h_v / h_k;
    let h_pad = h_v.next_power_of_two();
    let cols = d_v + d_k;
    let log_h = h_pad.trailing_zeros() as usize;
    let log_c = c_len.trailing_zeros() as usize;
    let half_wy = WY_SCALE / 2; // 2048

    // Pre-fill padded arrays (`rem = 2048` on padded heads `h_v .. h_pad` so `0 == M_wy*(0 - 0) + 2048 - 2048`!).
    let mut l_lsb_hij = vec![0u32; h_pad * c_len * c_len];
    let mut rhs_lsb_hik = vec![0u32; h_pad * c_len * cols];
    let mut uw_lsb_hik = vec![0u32; h_pad * c_len * cols];
    let mut rem_lsb_hik = vec![half_wy as u32; h_pad * c_len * cols];
    let mut y_out_f32 = vec![0.0f32; c_len * h_v * d_v];

    let per_head: Vec<GdnHeadWyOutputs> = (0..h_v)
        .into_par_iter()
        .map(|h| {
            let hk = h / gva_rep;
            let scale_q = 1.0 / (d_k as f32).sqrt();
            // L2-normalize q & k per token!
            let mut q_h = vec![0.0f32; c_len * d_k];
            let mut k_h = vec![0.0f32; c_len * d_k];
            let mut v_h = vec![0.0f32; c_len * d_v];
            let mut alpha_h = vec![0.0f32; c_len];
            let mut beta_h = vec![0.0f32; c_len];

            for t in 0..c_len {
                let q_src = &q[(t * h_k + hk) * d_k..(t * h_k + hk + 1) * d_k];
                let k_src = &k[(t * h_k + hk) * d_k..(t * h_k + hk + 1) * d_k];
                let v_src = &v[(t * h_v + h) * d_v..(t * h_v + h + 1) * d_v];
                let q_inv = 1.0 / (q_src.iter().map(|&x| x * x).sum::<f32>() + 1e-6).sqrt();
                let k_inv = 1.0 / (k_src.iter().map(|&x| x * x).sum::<f32>() + 1e-6).sqrt();
                for d in 0..d_k {
                    q_h[t * d_k + d] = q_src[d] * q_inv * scale_q;
                    k_h[t * d_k + d] = k_src[d] * k_inv;
                }
                v_h[t * d_v..(t + 1) * d_v].copy_from_slice(v_src);
                alpha_h[t] = g[t * h_v + h].exp().clamp(0.0, 1.0);
                beta_h[t] = beta[t * h_v + h].clamp(0.0, 1.0);
            }

            // Division-free pairwise decays `cap_gamma[i][j] = prod_{m=j+1}^i alpha[m]` (`1.0` on `i == j`)
            let mut gamma = vec![0.0f32; c_len];
            let mut cap_gamma = vec![0.0f32; c_len * c_len];
            let mut pref = 1.0f32;
            for i in 0..c_len {
                pref *= alpha_h[i];
                gamma[i] = pref;
                cap_gamma[i * c_len + i] = 1.0;
                let mut pij = 1.0f32;
                for j in (0..i).rev() {
                    pij *= alpha_h[j + 1];
                    cap_gamma[i * c_len + j] = pij;
                }
            }

            // Strict lower-triangular integer coupling `L_tilde[i, j] = round(M_wy * beta_i * cap_gamma[i, j] * <k_i, k_j>)`
            let mut l_mat = vec![0i64; c_len * c_len];
            for i in 1..c_len {
                let bi = beta_h[i];
                for j in 0..i {
                    let mut dot_kk = 0.0f32;
                    for d in 0..d_k {
                        dot_kk += k_h[i * d_k + d] * k_h[j * d_k + d];
                    }
                    let l_val =
                        ((WY_SCALE as f32) * bi * cap_gamma[i * c_len + j] * dot_kk).round() as i64;
                    l_mat[i * c_len + j] = l_val;
                }
            }

            // Integer RHS `[diag(beta) * V * ACT_SCALE | diag(gamma * beta) * K * WY_SCALE]`
            let mut rhs_mat = vec![0i64; c_len * cols];
            for i in 0..c_len {
                let bi = beta_h[i];
                let gbi = gamma[i] * bi;
                for d in 0..d_v {
                    rhs_mat[i * cols + d] =
                        ((ACT_SCALE as f32) * bi * v_h[i * d_v + d]).round() as i64;
                }
                for d in 0..d_k {
                    rhs_mat[i * cols + d_v + d] =
                        ((WY_SCALE as f32) * gbi * k_h[i * d_k + d]).round() as i64;
                }
            }

            // Exact division-free forward substitution `(I + L_tilde / M_wy) * UW = RHS` with Euclidean remainder!
            let mut uw_mat = vec![0i64; c_len * cols];
            let mut rem_mat = vec![0u32; c_len * cols];
            for i in 0..c_len {
                for col in 0..cols {
                    let mut sum_lu = 0i64;
                    for j in 0..i {
                        sum_lu += l_mat[i * c_len + j] * uw_mat[j * cols + col];
                    }
                    assert!(
                        sum_lu.abs() < (P as i64) / 2,
                        "WY BabyBear wraparound guard tripped: |sum_lu|={}",
                        sum_lu.abs()
                    );
                    let num = WY_SCALE * rhs_mat[i * cols + col] - sum_lu + half_wy;
                    let uw_val = num.div_euclid(WY_SCALE);
                    let r_val = num.rem_euclid(WY_SCALE) as u32;
                    debug_assert_eq!(
                        sum_lu,
                        WY_SCALE * (rhs_mat[i * cols + col] - uw_val) + half_wy - (r_val as i64)
                    );
                    uw_mat[i * cols + col] = uw_val;
                    rem_mat[i * cols + col] = r_val;
                }
            }

            // Chunk readout `Y = ((Q K^T) ⊙ Gamma) * U_deq` (`S_init = 0` at start of prompt)
            let mut y_h = vec![0.0f32; c_len * d_v];
            for i in 0..c_len {
                for j in 0..=i {
                    let mut dot_qk = 0.0f32;
                    for d in 0..d_k {
                        dot_qk += q_h[i * d_k + d] * k_h[j * d_k + d];
                    }
                    let attn_ij = dot_qk * cap_gamma[i * c_len + j];
                    for d in 0..d_v {
                        let u_f = (uw_mat[j * cols + d] as f32) / (ACT_SCALE as f32);
                        y_h[i * d_v + d] += attn_ij * u_f;
                    }
                }
            }

            (l_mat, rhs_mat, uw_mat, rem_mat, y_h)
        })
        .collect();

    for (h, (l_mat, rhs_mat, uw_mat, rem_mat, y_h)) in per_head.into_iter().enumerate() {
        for i in 0..c_len {
            for j in 0..c_len {
                let idx = h + (i << log_h) + (j << (log_h + log_c));
                l_lsb_hij[idx] = bb_from_i64(l_mat[i * c_len + j]);
            }
            for col in 0..cols {
                let idx = h + (i << log_h) + (col << (log_h + log_c));
                rhs_lsb_hik[idx] = bb_from_i64(rhs_mat[i * cols + col]);
                uw_lsb_hik[idx] = bb_from_i64(uw_mat[i * cols + col]);
                rem_lsb_hik[idx] = rem_mat[i * cols + col];
            }
            y_out_f32[(i * h_v + h) * d_v..(i * h_v + h + 1) * d_v]
                .copy_from_slice(&y_h[i * d_v..(i + 1) * d_v]);
        }
    }

    RealGdnWyWitness {
        h_v_orig: h_v,
        h_pad,
        c_len,
        d_k,
        d_v,
        l_lsb_hij,
        rhs_lsb_hik,
        uw_lsb_hik,
        rem_lsb_hik,
        y_out_f32,
    }
}

// ===========================================================================
// Real 24-Layer `Qwen3.5-0.8B` Execution Directly from `MmapSafetensors`
// ===========================================================================

/// Captured full-width witness of an audited `Gated DeltaNet + SwiGLU` layer (`l*`) + all 25 turn boundaries!
pub struct Qwen35TurnExecution {
    pub token_ids: Vec<u32>,
    /// `25` boundary activation matrices (`B_0 .. B_24`), each `[64 * 1024]` canonical BabyBear (`t + (d << 6)` LSB layout).
    pub boundaries_bb: Vec<Vec<u32>>,
    pub audited_layer: usize,
    pub wy_witness: RealGdnWyWitness,
    /// Audited layer's `MXFP4` SwiGLU `gate_proj` (`[3584->4096, 1024]`) input `X_ln2` (`i16[64, 1024]`), matrix, and `Y_raw`.
    pub x_ln2_i16: Vec<i16>,
    pub gate_proj_mat: Mxfp4Matrix,
    pub gate_proj_y_raw: Vec<i64>,
    /// Audited layer's `out_proj` & `down_proj` quantized integer deltas (`delta_gdn_bb`, `delta_mlp_bb`, `[64 * 1024]`)
    /// satisfying `B_{l* + 1} == B_{l*} + delta_gdn + delta_mlp (mod P)`!
    pub delta_gdn_bb: Vec<u32>,
    pub delta_mlp_bb: Vec<u32>,
}

#[inline]
fn pack_td_lsb_bb(x_i16: &[i16], seq_len: usize, dim: usize) -> Vec<u32> {
    assert_eq!(x_i16.len(), seq_len * dim);
    let log_t = seq_len.trailing_zeros() as usize;
    let mut out = vec![0u32; seq_len * dim];
    for t in 0..seq_len {
        for d in 0..dim {
            out[t + (d << log_t)] = bb_from_i64(x_i16[t * dim + d] as i64);
        }
    }
    out
}

/// Execute all 24 real pretrained layers of `Qwen/Qwen3.5-0.8B-Base` (`18 GDN + 6 GQA`) on a 64-token
/// prompt directly from `MmapSafetensors` (`0` network downloads, `0` `/tmp` files required!) and capture
/// all 25 `U1` layer boundaries + full witness of `audited_layer` (`must be one of the 18 GDN layers`).
pub fn execute_qwen35_24_layers_mmap(
    mmap: &MmapSafetensors,
    token_ids: &[u32],
    audited_layer: usize,
) -> Result<(Qwen35TurnExecution, Vec<f32>), String> {
    let seq_len = token_ids.len();
    assert_eq!(seq_len, 64, "chunkwise WY expects C = 64 token turn");
    assert!(
        audited_layer < 24 && (audited_layer % 4) != 3,
        "audited_layer must be a GDN layer"
    );

    let d_model = 1024usize;
    let d_ff = 3584usize;
    let eps = 1e-6f32;

    // 0. Embedding lookup (`model.language_model.embed_tokens.weight`, `[248320, 1024]` BF16)
    let (emb_info, emb_raw) = mmap.tensor_bytes("model.language_model.embed_tokens.weight")?;
    assert_eq!(emb_info.shape, vec![248320, 1024]);
    let mut h_f32 = vec![0.0f32; seq_len * d_model];
    for (t, &tid) in token_ids.iter().enumerate() {
        let tid_u = tid as usize;
        assert!(tid_u < 248320);
        let row_bytes = &emb_raw[tid_u * d_model * 2..(tid_u + 1) * d_model * 2];
        for d in 0..d_model {
            let bits = u16::from_le_bytes([row_bytes[2 * d], row_bytes[2 * d + 1]]);
            h_f32[t * d_model + d] = f32::from_bits((bits as u32) << 16);
        }
    }
    let mut h_i16 = quantize_act_i16(&h_f32);
    for (hf, &hi) in h_f32.iter_mut().zip(h_i16.iter()) {
        *hf = (hi as f32) / (ACT_SCALE as f32);
    }

    let mut boundaries_bb = Vec::with_capacity(25);
    boundaries_bb.push(pack_td_lsb_bb(&h_i16, seq_len, d_model));

    let mut opt_wy: Option<RealGdnWyWitness> = None;
    let mut opt_x_ln2: Option<Vec<i16>> = None;
    let mut opt_gate_mat: Option<Mxfp4Matrix> = None;
    let mut opt_gate_y: Option<Vec<i64>> = None;
    let mut opt_delta_gdn: Option<Vec<u32>> = None;
    let mut opt_delta_mlp: Option<Vec<u32>> = None;

    for l in 0..24usize {
        let pfx = format!("model.language_model.layers.{l}");
        let (_, ln1_w) = mmap.read_f32(&format!("{pfx}.input_layernorm.weight"))?;
        let (_, ln2_w) = mmap.read_f32(&format!("{pfx}.post_attention_layernorm.weight"))?;
        let x_ln1_f32 = rmsnorm_zero_centered_f32(&h_f32, &ln1_w, d_model, eps);
        let x_ln1_i16 = quantize_act_i16(&x_ln1_f32);

        let delta_attn_i16: Vec<i16> = if (l % 4) != 3 {
            // --- Gated DeltaNet Layer (`H_k = 16, H_v = 16, d_k = d_v = 128, w_conv = 4`) ---
            let qkv_mat = Mxfp4Matrix::from_safetensors(
                mmap,
                &format!("{pfx}.linear_attn.in_proj_qkv.weight"),
            )?;
            let z_mat = Mxfp4Matrix::from_safetensors(
                mmap,
                &format!("{pfx}.linear_attn.in_proj_z.weight"),
            )?;
            let b_mat = Mxfp4Matrix::from_safetensors(
                mmap,
                &format!("{pfx}.linear_attn.in_proj_b.weight"),
            )?;
            let a_mat = Mxfp4Matrix::from_safetensors(
                mmap,
                &format!("{pfx}.linear_attn.in_proj_a.weight"),
            )?;
            let out_mat =
                Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.linear_attn.out_proj.weight"))?;
            let (_, conv_w) = mmap.read_f32(&format!("{pfx}.linear_attn.conv1d.weight"))?;
            let (_, a_log) = mmap.read_f32(&format!("{pfx}.linear_attn.A_log"))?;
            let (_, dt_bias) = mmap.read_f32(&format!("{pfx}.linear_attn.dt_bias"))?;
            let (_, norm_w) = mmap.read_f32(&format!("{pfx}.linear_attn.norm.weight"))?;

            let qkv_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &qkv_mat);
            let qkv_f32 = dequant_y_raw_to_f32(&qkv_raw, seq_len, 6144, qkv_mat.rows_pad);
            let z_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &z_mat);
            let z_f32 = dequant_y_raw_to_f32(&z_raw, seq_len, 2048, z_mat.rows_pad);
            let b_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &b_mat);
            let b_f32 = dequant_y_raw_to_f32(&b_raw, seq_len, 16, b_mat.rows_pad);
            let a_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &a_mat);
            let a_f32 = dequant_y_raw_to_f32(&a_raw, seq_len, 16, a_mat.rows_pad);

            // Causal depthwise `conv1d` (`w = 4`, `[6144, 1, 4]`) + `SiLU`
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

            let mut q_f32 = vec![0.0f32; seq_len * 2048];
            let mut k_f32 = vec![0.0f32; seq_len * 2048];
            let mut v_f32 = vec![0.0f32; seq_len * 2048];
            let mut g_f32 = vec![0.0f32; seq_len * 16];
            let mut beta_f32 = vec![0.0f32; seq_len * 16];
            for t in 0..seq_len {
                q_f32[t * 2048..(t + 1) * 2048]
                    .copy_from_slice(&conv_out[t * 6144..t * 6144 + 2048]);
                k_f32[t * 2048..(t + 1) * 2048]
                    .copy_from_slice(&conv_out[t * 6144 + 2048..t * 6144 + 4096]);
                v_f32[t * 2048..(t + 1) * 2048]
                    .copy_from_slice(&conv_out[t * 6144 + 4096..t * 6144 + 6144]);
                for h in 0..16 {
                    beta_f32[t * 16 + h] = sigmoid_f32(b_f32[t * 16 + h]);
                    g_f32[t * 16 + h] =
                        -a_log[h].exp() * softplus_f32(a_f32[t * 16 + h] + dt_bias[h]);
                }
            }

            let wy = solve_real_gdn_wy_chunk64(
                &q_f32,
                &k_f32,
                &v_f32,
                &g_f32,
                &beta_f32,
                GdnWyShape {
                    h_k: 16,
                    h_v: 16,
                    c_len: seq_len,
                    d_k: 128,
                    d_v: 128,
                },
            );

            // `Qwen3NextRMSNormGated`: `norm.weight * rmsnorm_plain(y) * silu(z)` (NO `1 + w`!)
            let mut gated_f32 = vec![0.0f32; seq_len * 2048];
            for t in 0..seq_len {
                for h in 0..16 {
                    let off = (t * 16 + h) * 128;
                    let ys = &wy.y_out_f32[off..off + 128];
                    let zs = &z_f32[off..off + 128];
                    let inv_rms =
                        1.0 / (ys.iter().map(|&v| v * v).sum::<f32>() / 128.0 + eps).sqrt();
                    for d in 0..128 {
                        gated_f32[off + d] = norm_w[d] * (ys[d] * inv_rms) * silu_f32(zs[d]);
                    }
                }
            }
            let gated_i16 = quantize_act_i16(&gated_f32);
            let out_raw = eval_mxfp4_int_contraction(&gated_i16, seq_len, 2048, &out_mat);
            let out_f32 = dequant_y_raw_to_f32(&out_raw, seq_len, d_model, out_mat.rows_pad);
            if l == audited_layer {
                opt_wy = Some(wy);
            }
            quantize_act_i16(&out_f32)
        } else {
            // --- Full Attention GQA Layer (`H_q = 8, H_kv = 2, head_dim = 256, rotary_dim = 64, theta = 1e7`) ---
            let q_mat =
                Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.q_proj.weight"))?;
            let k_mat =
                Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.k_proj.weight"))?;
            let v_mat =
                Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.v_proj.weight"))?;
            let o_mat =
                Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.self_attn.o_proj.weight"))?;
            let (_, qn_w) = mmap.read_f32(&format!("{pfx}.self_attn.q_norm.weight"))?;
            let (_, kn_w) = mmap.read_f32(&format!("{pfx}.self_attn.k_norm.weight"))?;

            let qg_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &q_mat);
            let qg_f32 = dequant_y_raw_to_f32(&qg_raw, seq_len, 4096, q_mat.rows_pad);
            let k_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &k_mat);
            let k_proj_f32 = dequant_y_raw_to_f32(&k_raw, seq_len, 512, k_mat.rows_pad);
            let v_raw = eval_mxfp4_int_contraction(&x_ln1_i16, seq_len, d_model, &v_mat);
            let v_proj_f32 = dequant_y_raw_to_f32(&v_raw, seq_len, 512, v_mat.rows_pad);

            // Split `qg` `[seq_len, 8, 512]` into `q` `[seq_len, 8, 256]` & `gate` `[seq_len, 2048]`
            let mut q_heads = vec![0.0f32; seq_len * 8 * 256];
            let mut gate_f32 = vec![0.0f32; seq_len * 2048];
            for t in 0..seq_len {
                for h in 0..8 {
                    let src = &qg_f32[(t * 8 + h) * 512..(t * 8 + h + 1) * 512];
                    q_heads[(t * 8 + h) * 256..(t * 8 + h + 1) * 256].copy_from_slice(&src[..256]);
                    gate_f32[(t * 8 + h) * 256..(t * 8 + h + 1) * 256].copy_from_slice(&src[256..]);
                }
            }
            let mut q_normed = rmsnorm_zero_centered_f32(&q_heads, &qn_w, 256, eps);
            let mut k_normed = rmsnorm_zero_centered_f32(&k_proj_f32, &kn_w, 256, eps);

            // Partial RoPE (`rotary_dim = 64`, `theta = 10_000_000.0`)
            for t in 0..seq_len {
                for pair in 0..32usize {
                    let freq = 1.0f32 / 10_000_000.0f32.powf((2 * pair) as f32 / 64.0);
                    let ang = (t as f32) * freq;
                    let (cs, sn) = (ang.cos(), ang.sin());
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
            let o_raw = eval_mxfp4_int_contraction(&attn_i16, seq_len, 2048, &o_mat);
            let o_f32 = dequant_y_raw_to_f32(&o_raw, seq_len, d_model, o_mat.rows_pad);
            quantize_act_i16(&o_f32)
        };

        // Mid-layer residual `h_mid_i16 = h_i16 + delta_attn_i16`
        let mut h_mid_i16 = vec![0i16; seq_len * d_model];
        let mut h_mid_f32 = vec![0.0f32; seq_len * d_model];
        for i in 0..(seq_len * d_model) {
            let sum_i = (h_i16[i] as i32 + delta_attn_i16[i] as i32)
                .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
            h_mid_i16[i] = sum_i;
            h_mid_f32[i] = (sum_i as f32) / (ACT_SCALE as f32);
        }

        // SwiGLU MLP (`1024 -> 3584 -> 1024`)
        let x_ln2_f32 = rmsnorm_zero_centered_f32(&h_mid_f32, &ln2_w, d_model, eps);
        let x_ln2_i16 = quantize_act_i16(&x_ln2_f32);
        let gate_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.gate_proj.weight"))?;
        let up_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.up_proj.weight"))?;
        let down_mat = Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.down_proj.weight"))?;

        let gate_raw = eval_mxfp4_int_contraction(&x_ln2_i16, seq_len, d_model, &gate_mat);
        let gate_f32 = dequant_y_raw_to_f32(&gate_raw, seq_len, d_ff, gate_mat.rows_pad);
        let up_raw = eval_mxfp4_int_contraction(&x_ln2_i16, seq_len, d_model, &up_mat);
        let up_f32 = dequant_y_raw_to_f32(&up_raw, seq_len, d_ff, up_mat.rows_pad);

        let mut swiglu_f32 = vec![0.0f32; seq_len * d_ff];
        for i in 0..(seq_len * d_ff) {
            swiglu_f32[i] = silu_f32(gate_f32[i]) * up_f32[i];
        }
        let swiglu_i16 = quantize_act_i16(&swiglu_f32);
        let down_raw = eval_mxfp4_int_contraction(&swiglu_i16, seq_len, d_ff, &down_mat);
        let down_f32 = dequant_y_raw_to_f32(&down_raw, seq_len, d_model, down_mat.rows_pad);
        let delta_mlp_i16 = quantize_act_i16(&down_f32);

        // Layer output boundary `h_next_i16 = h_i16 + delta_attn_i16 + delta_mlp_i16` (exact over Z if unclamped!)
        let mut exact_delta_mlp = vec![0i16; seq_len * d_model];
        for i in 0..(seq_len * d_model) {
            let next_i = (h_mid_i16[i] as i32 + delta_mlp_i16[i] as i32)
                .clamp(i16::MIN as i32, i16::MAX as i32) as i16;
            exact_delta_mlp[i] = next_i - h_mid_i16[i];
            h_i16[i] = next_i;
            h_f32[i] = (next_i as f32) / (ACT_SCALE as f32);
        }

        if l == audited_layer {
            opt_x_ln2 = Some(x_ln2_i16);
            opt_gate_mat = Some(gate_mat);
            opt_gate_y = Some(gate_raw);
            opt_delta_gdn = Some(pack_td_lsb_bb(&delta_attn_i16, seq_len, d_model));
            opt_delta_mlp = Some(pack_td_lsb_bb(&exact_delta_mlp, seq_len, d_model));
        }

        boundaries_bb.push(pack_td_lsb_bb(&h_i16, seq_len, d_model));
    }

    // Final RMSNorm (`model.language_model.norm.weight`)
    let (_, final_norm_w) = mmap.read_f32("model.language_model.norm.weight")?;
    let final_h = rmsnorm_zero_centered_f32(&h_f32, &final_norm_w, d_model, eps);

    let _ = (ACT_SHIFT, W_SCALE_SHIFT, WY_SHIFT, badd, bmul, bsub);
    Ok((
        Qwen35TurnExecution {
            token_ids: token_ids.to_vec(),
            boundaries_bb,
            audited_layer,
            wy_witness: opt_wy.unwrap(),
            x_ln2_i16: opt_x_ln2.unwrap(),
            gate_proj_mat: opt_gate_mat.unwrap(),
            gate_proj_y_raw: opt_gate_y.unwrap(),
            delta_gdn_bb: opt_delta_gdn.unwrap(),
            delta_mlp_bb: opt_delta_mlp.unwrap(),
        },
        final_h,
    ))
}

// ===========================================================================
// Succinct Standalone `Gated DeltaNet + MXFP4 SwiGLU` Layer Proof & Verifier
// ===========================================================================

/// Self-contained succinct proof for a full-width `Gated DeltaNet` WY chunk (`H_v = 16` or `H_v = 48 -> 64`)
/// + `MXFP4` E2M1 delayed-bind 0-mul Horner projection + `U1` boundary residual weld!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctGdnLayerProof {
    pub audited_layer: usize,
    pub h_pad: usize,
    pub c_len: usize,
    pub wy_cols: usize,
    pub mxfp4_j_pad: usize,
    pub mxfp4_k_pad: usize,

    // Weight registry tie (`layer_weight_path` to global `weight_root` + sibling tensor digests)
    pub layer_weight_path: MerkleSinglePath,
    pub layer_tensor_digests: Vec<[u8; 32]>,
    pub gate_proj_tensor_slot: usize,
    pub q_pcs_root: [u8; 32],
    pub s_pcs_root: [u8; 32],

    // ZK Witness PCS roots
    pub l_pcs_root: [u8; 32],
    pub rhs_pcs_root: [u8; 32],
    pub uw_pcs_root: [u8; 32],
    pub rem_pcs_root: [u8; 32],
    pub mult_pcs_root: [u8; 32],
    pub x_ln2_pcs_root: [u8; 32],
    pub y_gate_pcs_root: [u8; 32],
    pub delta_gdn_pcs_root: [u8; 32],
    pub delta_mlp_pcs_root: [u8; 32],

    // 1. GDN WY `L · UW == M_wy*(RHS - UW) + 2048 - R_rem` + SLT zerocheck + D1b `[0, 4096)` range proof
    pub rhs_eval_at_z: Ext4,
    pub uw_eval_at_z: Ext4,
    pub rem_eval_at_z: Ext4,
    pub wy_gruen_proof: GruenMode2Ext4Proof,
    pub slt_zero_proof: GruenMode2Ext4Proof,
    pub d1b_rem_proof: D1bRangeExt4Proof,

    // 2. Pretrained `MXFP4` E2M1 delayed-bind 0-mul Horner proof (`1024 -> 3584/4096` or `2560/4096 -> 640/1024`)
    pub mxfp4_proof: Mxfp4DelayedBjkExt4Proof,

    // 3. `U1` Boundary Residual Weld (`B_{l* + 1}(z_b) == B_{l*}(z_b) + delta_gdn(z_b) + delta_mlp(z_b)`)
    pub b_in_eval: Ext4,
    pub b_out_eval: Ext4,
    pub delta_gdn_eval: Ext4,
    pub delta_mlp_eval: Ext4,

    // 4. Succinct `Ext4` Coset-RS PCS opening proofs (`0` witness access!)
    pub l_pcs_proof: PcsOpeningProof,
    pub rhs_pcs_proof: PcsOpeningProof,
    pub uw_pcs_proof: PcsOpeningProof,
    pub rem_pcs_proof: PcsOpeningProof,
    pub mult_pcs_proof: PcsOpeningProof,
    pub q_pcs_proof: PcsOpeningProof,
    pub s_pcs_proof: PcsOpeningProof,
    pub x_ln2_pcs_proof: PcsOpeningProof,
    pub y_gate_pcs_proof: PcsOpeningProof,
    pub b_in_pcs_proof: PcsOpeningProof,
    pub b_out_pcs_proof: PcsOpeningProof,
    pub delta_gdn_pcs_proof: PcsOpeningProof,
    pub delta_mlp_pcs_proof: PcsOpeningProof,
}

impl SuccinctGdnLayerProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.audited_layer as u32).to_le_bytes());
        out.extend_from_slice(&(self.h_pad as u32).to_le_bytes());
        out.extend_from_slice(&(self.c_len as u32).to_le_bytes());
        out.extend_from_slice(&(self.wy_cols as u32).to_le_bytes());
        out.extend_from_slice(&(self.mxfp4_j_pad as u32).to_le_bytes());
        out.extend_from_slice(&(self.mxfp4_k_pad as u32).to_le_bytes());

        out.extend_from_slice(&(self.layer_weight_path.index as u32).to_le_bytes());
        out.extend_from_slice(&self.layer_weight_path.leaf);
        out.extend_from_slice(&(self.layer_weight_path.siblings.len() as u32).to_le_bytes());
        for s in &self.layer_weight_path.siblings {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.layer_tensor_digests.len() as u32).to_le_bytes());
        for d in &self.layer_tensor_digests {
            out.extend_from_slice(d);
        }
        out.extend_from_slice(&(self.gate_proj_tensor_slot as u32).to_le_bytes());

        for r in [
            &self.q_pcs_root,
            &self.s_pcs_root,
            &self.l_pcs_root,
            &self.rhs_pcs_root,
            &self.uw_pcs_root,
            &self.rem_pcs_root,
            &self.mult_pcs_root,
            &self.x_ln2_pcs_root,
            &self.y_gate_pcs_root,
            &self.delta_gdn_pcs_root,
            &self.delta_mlp_pcs_root,
        ] {
            out.extend_from_slice(r);
        }

        for e in [
            self.rhs_eval_at_z,
            self.uw_eval_at_z,
            self.rem_eval_at_z,
            self.b_in_eval,
            self.b_out_eval,
            self.delta_gdn_eval,
            self.delta_mlp_eval,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }

        self.wy_gruen_proof.write_to(out);
        self.slt_zero_proof.write_to(out);
        self.d1b_rem_proof.write_to(out);
        self.mxfp4_proof.write_to(out);

        for pf in [
            &self.l_pcs_proof,
            &self.rhs_pcs_proof,
            &self.uw_pcs_proof,
            &self.rem_pcs_proof,
            &self.mult_pcs_proof,
            &self.q_pcs_proof,
            &self.s_pcs_proof,
            &self.x_ln2_pcs_proof,
            &self.y_gate_pcs_proof,
            &self.b_in_pcs_proof,
            &self.b_out_pcs_proof,
            &self.delta_gdn_pcs_proof,
            &self.delta_mlp_pcs_proof,
        ] {
            pf.write_to(out);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let audited_layer = cur.read_u32()? as usize;
        let h_pad = cur.read_u32()? as usize;
        let c_len = cur.read_u32()? as usize;
        let wy_cols = cur.read_u32()? as usize;
        let mxfp4_j_pad = cur.read_u32()? as usize;
        let mxfp4_k_pad = cur.read_u32()? as usize;

        let path_idx = cur.read_u32()? as usize;
        let path_leaf = cur.read_arr32()?;
        let sib_len = cur.read_u32()? as usize;
        if sib_len > 32 {
            return Err("invalid layer_weight_path sibling len".to_string());
        }
        let mut siblings = Vec::with_capacity(sib_len);
        for _ in 0..sib_len {
            siblings.push(cur.read_arr32()?);
        }
        let td_len = cur.read_u32()? as usize;
        if td_len > 32 {
            return Err("invalid layer_tensor_digests len".to_string());
        }
        let mut layer_tensor_digests = Vec::with_capacity(td_len);
        for _ in 0..td_len {
            layer_tensor_digests.push(cur.read_arr32()?);
        }
        let gate_proj_tensor_slot = cur.read_u32()? as usize;

        let q_pcs_root = cur.read_arr32()?;
        let s_pcs_root = cur.read_arr32()?;
        let l_pcs_root = cur.read_arr32()?;
        let rhs_pcs_root = cur.read_arr32()?;
        let uw_pcs_root = cur.read_arr32()?;
        let rem_pcs_root = cur.read_arr32()?;
        let mult_pcs_root = cur.read_arr32()?;
        let x_ln2_pcs_root = cur.read_arr32()?;
        let y_gate_pcs_root = cur.read_arr32()?;
        let delta_gdn_pcs_root = cur.read_arr32()?;
        let delta_mlp_pcs_root = cur.read_arr32()?;

        let rhs_eval_at_z = cur.read_ext4()?;
        let uw_eval_at_z = cur.read_ext4()?;
        let rem_eval_at_z = cur.read_ext4()?;
        let b_in_eval = cur.read_ext4()?;
        let b_out_eval = cur.read_ext4()?;
        let delta_gdn_eval = cur.read_ext4()?;
        let delta_mlp_eval = cur.read_ext4()?;

        let wy_gruen_proof = GruenMode2Ext4Proof::read_from(cur)?;
        let slt_zero_proof = GruenMode2Ext4Proof::read_from(cur)?;
        let d1b_rem_proof = D1bRangeExt4Proof::read_from(cur)?;
        let mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(cur)?;

        let l_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let rhs_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let uw_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let rem_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let q_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let s_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let x_ln2_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let y_gate_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let b_in_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let b_out_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let delta_gdn_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let delta_mlp_pcs_proof = PcsOpeningProof::read_from(cur)?;

        Ok(Self {
            audited_layer,
            h_pad,
            c_len,
            wy_cols,
            mxfp4_j_pad,
            mxfp4_k_pad,
            layer_weight_path: MerkleSinglePath {
                index: path_idx,
                leaf: path_leaf,
                siblings,
            },
            layer_tensor_digests,
            gate_proj_tensor_slot,
            q_pcs_root,
            s_pcs_root,
            l_pcs_root,
            rhs_pcs_root,
            uw_pcs_root,
            rem_pcs_root,
            mult_pcs_root,
            x_ln2_pcs_root,
            y_gate_pcs_root,
            delta_gdn_pcs_root,
            delta_mlp_pcs_root,
            rhs_eval_at_z,
            uw_eval_at_z,
            rem_eval_at_z,
            wy_gruen_proof,
            slt_zero_proof,
            d1b_rem_proof,
            mxfp4_proof,
            b_in_eval,
            b_out_eval,
            delta_gdn_eval,
            delta_mlp_eval,
            l_pcs_proof,
            rhs_pcs_proof,
            uw_pcs_proof,
            rem_pcs_proof,
            mult_pcs_proof,
            q_pcs_proof,
            s_pcs_proof,
            x_ln2_pcs_proof,
            y_gate_pcs_proof,
            b_in_pcs_proof,
            b_out_pcs_proof,
            delta_gdn_pcs_proof,
            delta_mlp_pcs_proof,
        })
    }
}

/// Offline precommitted PCS pair (`Q_pcs`, `S_pcs`) for a pretrained `MXFP4` weight matrix, bound to its `digest`.
pub struct PrecommittedMxfp4Pcs {
    pub q_state: crate::pcs_ext4::PcsProverState,
    pub s_state: crate::pcs_ext4::PcsProverState,
    pub j_pad: usize,
    pub k_pad: usize,
    pub nibs_pad: Vec<u8>,
    pub scs_pad: Vec<u32>,
}

impl PrecommittedMxfp4Pcs {
    pub fn build(mat: &Mxfp4Matrix) -> Self {
        let (j_pad, k_pad, nibs_pad, scs_pad) = pad_mxfp4_cols_pow2(mat);
        let mut q_lsb_bjk = vec![0u32; j_pad * k_pad * 32];
        let mut s_lsb_jk = vec![0u32; j_pad * k_pad];
        for j in 0..j_pad {
            for k in 0..k_pad {
                s_lsb_jk[k * j_pad + j] = scs_pad[j * k_pad + k];
                let src = (j * k_pad + k) * 32;
                let dst = (k * j_pad + j) * 32;
                for b in 0..32 {
                    q_lsb_bjk[dst + b] = decode_e2m1_x2_bb(nibs_pad[src + b]);
                }
            }
        }
        let q_state = commit_table_pcs(&q_lsb_bjk, PcsParams::default_public(1), None);
        let s_state = commit_table_pcs(&s_lsb_jk, PcsParams::default_public(1), None);
        Self {
            q_state,
            s_state,
            j_pad,
            k_pad,
            nibs_pad,
            scs_pad,
        }
    }
}

/// Witness and PCS commitments required by [`prove_audited_gdn_layer`].
pub struct AuditedGdnLayerWitness<'a> {
    pub layer_weight_path: MerkleSinglePath,
    pub layer_tensor_digests: Vec<[u8; 32]>,
    pub gate_proj_tensor_slot: usize,
    pub gate_pcs: &'a PrecommittedMxfp4Pcs,
    pub b_in_state: &'a crate::pcs_ext4::PcsProverState,
    pub b_out_state: &'a crate::pcs_ext4::PcsProverState,
    pub b_in_bb: &'a [u32],
    pub b_out_bb: &'a [u32],
    pub delta_gdn_bb: &'a [u32],
    pub delta_mlp_bb: &'a [u32],
    pub wy: &'a RealGdnWyWitness,
    pub x_ln2_i16: &'a [i16],
    pub gate_y_raw: &'a [i64],
}

/// Prove an audited `Gated DeltaNet + MXFP4 SwiGLU` layer (`Qwen3.5-0.8B` or `Qwen3.8-Flash-Next`)
/// against `(weight_root, b_in_pcs, b_out_pcs)`!
pub fn prove_audited_gdn_layer(
    weight_root: &[u8; 32],
    audited_layer: usize,
    inputs: AuditedGdnLayerWitness<'_>,
    tr: &mut CShakeTranscript,
) -> Result<SuccinctGdnLayerProof, String> {
    let AuditedGdnLayerWitness {
        layer_weight_path,
        layer_tensor_digests,
        gate_proj_tensor_slot,
        gate_pcs,
        b_in_state,
        b_out_state,
        b_in_bb,
        b_out_bb,
        delta_gdn_bb,
        delta_mlp_bb,
        wy,
        x_ln2_i16,
        gate_y_raw,
    } = inputs;
    let log_h = wy.h_pad.trailing_zeros() as usize;
    let log_c = wy.c_len.trailing_zeros() as usize;
    let wy_cols = wy.d_v + wy.d_k;
    let log_col = wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;
    let m_wy_tab = WY_SHIFT as usize; // 12 (`4096`)

    let mult_tab = compute_d1b_multiplicities(&wy.rem_lsb_hik, m_wy_tab)?;

    // Prepare `X_ln2` (`t + (b << log_c) + (k << (log_c + 5))`) and `Y_gate` (`t + (j << log_c)`) in LSB hypercube order!
    let k_pad = gate_pcs.k_pad;
    let j_pad = gate_pcs.j_pad;
    let in_orig = x_ln2_i16.len() / wy.c_len;
    let mut x_lsb_tbk = vec![0u32; wy.c_len * k_pad * 32];
    for t in 0..wy.c_len {
        for d in 0..in_orig {
            let k = d / 32;
            let b = d % 32;
            let idx = t + (b << log_c) + (k << (log_c + 5));
            x_lsb_tbk[idx] = bb_from_i64(x_ln2_i16[t * in_orig + d] as i64);
        }
    }
    let mut y_lsb_tj = vec![0u32; wy.c_len * j_pad];
    for t in 0..wy.c_len {
        for j in 0..j_pad {
            y_lsb_tj[t + (j << log_c)] = bb_from_i64(gate_y_raw[t * j_pad + j]);
        }
    }

    // Commit ZK Witness PCS matrices in parallel!
    let l_state = commit_table_pcs(&wy.l_lsb_hij, PcsParams::default_zk(2), None);
    let rhs_state = commit_table_pcs(&wy.rhs_lsb_hik, PcsParams::default_zk(1), None);
    let uw_state = commit_table_pcs(&wy.uw_lsb_hik, PcsParams::default_zk(2), None);
    let rem_state = commit_table_pcs(&wy.rem_lsb_hik, PcsParams::default_zk(2), None);
    let mult_state = commit_table_pcs(&mult_tab, PcsParams::default_zk(1), None);
    let x_state = commit_table_pcs(&x_lsb_tbk, PcsParams::default_zk(1), None);
    let y_state = commit_table_pcs(&y_lsb_tj, PcsParams::default_zk(1), None);
    let dg_state = commit_table_pcs(delta_gdn_bb, PcsParams::default_zk(1), None);
    let dm_state = commit_table_pcs(delta_mlp_bb, PcsParams::default_zk(1), None);

    // Absorb statement & all PCS roots into Fiat–Shamir transcript BEFORE squeezing any challenges!
    tr.absorb_root(b"stmt_weight_root", weight_root);
    tr.absorb_root(b"stmt_b_in_root", &b_in_state.root);
    tr.absorb_root(b"stmt_b_out_root", &b_out_state.root);
    tr.absorb_u32(b"stmt_audited_layer", audited_layer as u32);
    for r in [
        &gate_pcs.q_state.root,
        &gate_pcs.s_state.root,
        &l_state.root,
        &rhs_state.root,
        &uw_state.root,
        &rem_state.root,
        &mult_state.root,
        &x_state.root,
        &y_state.root,
        &dg_state.root,
        &dm_state.root,
    ] {
        tr.absorb_root(b"wit_pcs_root", r);
    }

    // --- 1. Full-Width GDN Chunkwise WY Proof (`L · UW == M_wy*(RHS - UW) + 2048 - R_rem`) ---
    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    let rhs_eval_at_z = mle_eval_bb_at_ext4(&wy.rhs_lsb_hik, &z_hik);
    let uw_eval_at_z = mle_eval_bb_at_ext4(&wy.uw_lsb_hik, &z_hik);
    let rem_eval_at_z = mle_eval_bb_at_ext4(&wy.rem_lsb_hik, &z_hik);
    tr.absorb_ext4(b"wy_rhs_z", rhs_eval_at_z);
    tr.absorb_ext4(b"wy_uw_z", uw_eval_at_z);
    tr.absorb_ext4(b"wy_rem_z", rem_eval_at_z);

    // Fold `L[h, i, j]` along `i` at `z_i` -> `left_hj[h, j]`, and `UW[h, j, k]` along `k` at `z_k` -> `right_hj[h, j]`!
    let eq_i = build_eq_table_lsb_ext4(&z_i);
    let eq_k = build_eq_table_lsb_ext4(&z_k);
    let hj_len = wy.h_pad * wy.c_len;
    let mut left_hj = vec![Ext4::ZERO; hj_len];
    let mut right_hj = vec![Ext4::ZERO; hj_len];
    for j in 0..wy.c_len {
        for h in 0..wy.h_pad {
            let mut acc_l = Ext4::ZERO;
            for (i, &eq_iv) in eq_i.iter().enumerate() {
                let l_val = wy.l_lsb_hij[h + (i << log_h) + (j << (log_h + log_c))];
                acc_l = acc_l.add(eq_iv.scale_bb(l_val));
            }
            left_hj[h + (j << log_h)] = acc_l;

            let mut acc_r = Ext4::ZERO;
            for (k, &eq_kv) in eq_k.iter().enumerate() {
                let u_val = wy.uw_lsb_hik[h + (j << log_h) + (k << (log_h + log_c))];
                acc_r = acc_r.add(eq_kv.scale_bb(u_val));
            }
            right_hj[h + (j << log_h)] = acc_r;
        }
    }

    let (wy_gruen_proof, wy_chals) =
        prove_gruen_einsum_mode2_ext4(&left_hj, &right_hj, log_h, log_c, &z_h, tr);
    let ch_h = &wy_chals[..log_h];
    let ch_j = &wy_chals[log_h..];

    let (slt_zero_proof, slt_pt) = prove_strict_lower_tri_ext4(&wy.l_lsb_hij, log_h, log_c, tr);
    let (d1b_rem_proof, d1b_leaf_pt) =
        prove_d1b_range_ext4(&wy.rem_lsb_hik, &mult_tab, m_wy_wit, m_wy_tab, tr);

    // --- 2. Pretrained `MXFP4` E2M1 Delayed-Bind 0-Mul Horner Proof ---
    let log_j = j_pad.trailing_zeros() as usize;
    let log_k = k_pad.trailing_zeros() as usize;
    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj_out", log_j, true);

    let eq_ri = build_eq_table_lsb_ext4(&r_i_mxfp4);
    let mut x_ri = vec![Ext4::ZERO; k_pad * 32];
    for k in 0..k_pad {
        for b in 0..32 {
            let mut acc = Ext4::ZERO;
            let base = (b << log_c) + (k << (log_c + 5));
            for t in 0..wy.c_len {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }
    let (mxfp4_proof, mxfp4_chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        &gate_pcs.nibs_pad,
        &gate_pcs.scs_pad,
        log_j,
        log_k,
        &r_j_mxfp4,
        tr,
    );

    // --- 3. `U1` Boundary Residual Weld (`B_{l* + 1}(z_b) == B_{l*}(z_b) + delta_gdn(z_b) + delta_mlp(z_b)`) ---
    let m_bnd = b_in_bb.len().trailing_zeros() as usize;
    let z_bnd = tr.squeeze_ext4_vec(b"u1_bnd_pt", m_bnd, true);
    let b_in_eval = mle_eval_bb_at_ext4(b_in_bb, &z_bnd);
    let b_out_eval = mle_eval_bb_at_ext4(b_out_bb, &z_bnd);
    let delta_gdn_eval = mle_eval_bb_at_ext4(delta_gdn_bb, &z_bnd);
    let delta_mlp_eval = mle_eval_bb_at_ext4(delta_mlp_bb, &z_bnd);
    tr.absorb_ext4(b"bnd_in_v", b_in_eval);
    tr.absorb_ext4(b"bnd_out_v", b_out_eval);
    tr.absorb_ext4(b"bnd_dg_v", delta_gdn_eval);
    tr.absorb_ext4(b"bnd_dm_v", delta_mlp_eval);

    // --- 4. Open All Succinct `Ext4` PCS Claims (`0` witness leakage!) ---
    let mut l_pt1 = Vec::with_capacity(log_h + 2 * log_c);
    l_pt1.extend_from_slice(ch_h);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(ch_j);

    let mut uw_pt2 = Vec::with_capacity(m_wy_wit);
    uw_pt2.extend_from_slice(ch_h);
    uw_pt2.extend_from_slice(ch_j);
    uw_pt2.extend_from_slice(&z_k);

    let l_pcs_proof = open_pcs_claims(
        &l_state,
        &[
            MleEvalClaim {
                point: l_pt1,
                value: wy_gruen_proof.terminal_openings.0,
            },
            MleEvalClaim {
                point: slt_pt,
                value: slt_zero_proof.terminal_openings.1,
            },
        ],
        tr,
    );
    let rhs_pcs_proof = open_pcs_claims(
        &rhs_state,
        &[MleEvalClaim {
            point: z_hik.clone(),
            value: rhs_eval_at_z,
        }],
        tr,
    );
    let uw_pcs_proof = open_pcs_claims(
        &uw_state,
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: uw_eval_at_z,
            },
            MleEvalClaim {
                point: uw_pt2,
                value: wy_gruen_proof.terminal_openings.1,
            },
        ],
        tr,
    );
    let rem_pcs_proof = open_pcs_claims(
        &rem_state,
        &[
            MleEvalClaim {
                point: z_hik,
                value: rem_eval_at_z,
            },
            MleEvalClaim {
                point: d1b_leaf_pt.clone(),
                value: d1b_rem_proof.rem_leaf_eval,
            },
        ],
        tr,
    );
    let mult_pcs_proof = open_pcs_claims(
        &mult_state,
        &[MleEvalClaim {
            point: d1b_leaf_pt[..m_wy_tab].to_vec(),
            value: d1b_rem_proof.mult_leaf_eval,
        }],
        tr,
    );

    let mut pt_q = Vec::with_capacity(5 + log_j + log_k);
    pt_q.extend_from_slice(&mxfp4_chals.chals_b);
    pt_q.extend_from_slice(&mxfp4_chals.chals_j);
    pt_q.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_s = Vec::with_capacity(log_j + log_k);
    pt_s.extend_from_slice(&mxfp4_chals.chals_j);
    pt_s.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_x = Vec::with_capacity(log_c + 5 + log_k);
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_y = Vec::with_capacity(log_c + log_j);
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    let q_pcs_proof = open_pcs_claims(
        &gate_pcs.q_state,
        &[MleEvalClaim {
            point: pt_q,
            value: mxfp4_proof.finals.1,
        }],
        tr,
    );
    let s_pcs_proof = open_pcs_claims(
        &gate_pcs.s_state,
        &[MleEvalClaim {
            point: pt_s,
            value: mxfp4_proof.finals.2,
        }],
        tr,
    );
    let x_ln2_pcs_proof = open_pcs_claims(
        &x_state,
        &[MleEvalClaim {
            point: pt_x,
            value: mxfp4_proof.finals.0,
        }],
        tr,
    );
    let y_gate_pcs_proof = open_pcs_claims(
        &y_state,
        &[MleEvalClaim {
            point: pt_y,
            value: mxfp4_proof.claim,
        }],
        tr,
    );

    let b_in_pcs_proof = open_pcs_claims(
        b_in_state,
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: b_in_eval,
        }],
        tr,
    );
    let b_out_pcs_proof = open_pcs_claims(
        b_out_state,
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: b_out_eval,
        }],
        tr,
    );
    let delta_gdn_pcs_proof = open_pcs_claims(
        &dg_state,
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: delta_gdn_eval,
        }],
        tr,
    );
    let delta_mlp_pcs_proof = open_pcs_claims(
        &dm_state,
        &[MleEvalClaim {
            point: z_bnd,
            value: delta_mlp_eval,
        }],
        tr,
    );

    Ok(SuccinctGdnLayerProof {
        audited_layer,
        h_pad: wy.h_pad,
        c_len: wy.c_len,
        wy_cols,
        mxfp4_j_pad: j_pad,
        mxfp4_k_pad: k_pad,
        layer_weight_path,
        layer_tensor_digests,
        gate_proj_tensor_slot,
        q_pcs_root: gate_pcs.q_state.root,
        s_pcs_root: gate_pcs.s_state.root,
        l_pcs_root: l_state.root,
        rhs_pcs_root: rhs_state.root,
        uw_pcs_root: uw_state.root,
        rem_pcs_root: rem_state.root,
        mult_pcs_root: mult_state.root,
        x_ln2_pcs_root: x_state.root,
        y_gate_pcs_root: y_state.root,
        delta_gdn_pcs_root: dg_state.root,
        delta_mlp_pcs_root: dm_state.root,
        rhs_eval_at_z,
        uw_eval_at_z,
        rem_eval_at_z,
        wy_gruen_proof,
        slt_zero_proof,
        d1b_rem_proof,
        mxfp4_proof,
        b_in_eval,
        b_out_eval,
        delta_gdn_eval,
        delta_mlp_eval,
        l_pcs_proof,
        rhs_pcs_proof,
        uw_pcs_proof,
        rem_pcs_proof,
        mult_pcs_proof,
        q_pcs_proof,
        s_pcs_proof,
        x_ln2_pcs_proof,
        y_gate_pcs_proof,
        b_in_pcs_proof,
        b_out_pcs_proof,
        delta_gdn_pcs_proof,
        delta_mlp_pcs_proof,
    })
}

/// Public statement verified by [`verify_audited_gdn_layer_standalone`].
pub struct AuditedGdnLayerVerifyStmt<'a> {
    pub expected_weight_root: &'a [u8; 32],
    pub expected_b_in_root: &'a [u8; 32],
    pub expected_b_out_root: &'a [u8; 32],
    pub expected_audited_layer: usize,
    pub expected_q_s_binding: &'a [u8; 32],
    pub bnd_vars: usize,
}

/// Standalone succinct verifier for `SuccinctGdnLayerProof` using **ONLY `(weight_root, b_in_root, b_out_root, bnd_vars, proof)`**!
pub fn verify_audited_gdn_layer_standalone(
    stmt: &AuditedGdnLayerVerifyStmt<'_>,
    proof: &SuccinctGdnLayerProof,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    let AuditedGdnLayerVerifyStmt {
        expected_weight_root,
        expected_b_in_root,
        expected_b_out_root,
        expected_audited_layer,
        expected_q_s_binding,
        bnd_vars,
    } = *stmt;
    if proof.audited_layer != expected_audited_layer {
        return Err("audited_layer mismatch".to_string());
    }
    if !proof.h_pad.is_power_of_two()
        || !proof.c_len.is_power_of_two()
        || !proof.wy_cols.is_power_of_two()
        || !proof.mxfp4_j_pad.is_power_of_two()
        || !proof.mxfp4_k_pad.is_power_of_two()
    {
        return Err("non-power-of-two layer proof dimensions".to_string());
    }

    // 0. Verify offline `weight_root` authentication path & `(q_pcs_root, s_pcs_root)` binding!
    if proof.gate_proj_tensor_slot >= proof.layer_tensor_digests.len()
        || proof.layer_weight_path.index != proof.audited_layer
    {
        return Err("invalid gate_proj_tensor_slot or layer_weight_path index".to_string());
    }
    let mut layer_buf = Vec::with_capacity(4 + proof.layer_tensor_digests.len() * 32);
    layer_buf.extend_from_slice(&(proof.audited_layer as u32).to_le_bytes());
    for d in &proof.layer_tensor_digests {
        layer_buf.extend_from_slice(d);
    }
    let recomputed_leaf = cshake256_32(b"QW35-LAYER-WEIGHT-LEAF-V1", &layer_buf);
    if recomputed_leaf != proof.layer_weight_path.leaf {
        return Err("layer weight leaf hash mismatch".to_string());
    }
    let num_weight_leaves = 1usize << proof.layer_weight_path.siblings.len();
    if !proof.layer_weight_path.verify(
        b"QW35-GLOBAL-WEIGHT-TREE-V1",
        expected_weight_root,
        num_weight_leaves,
    ) {
        return Err("global weight_root Merkle path verification failed".to_string());
    }
    let mut qs_bind_in = [0u8; 96];
    qs_bind_in[0..32].copy_from_slice(&proof.layer_tensor_digests[proof.gate_proj_tensor_slot]);
    qs_bind_in[32..64].copy_from_slice(&proof.q_pcs_root);
    qs_bind_in[64..96].copy_from_slice(&proof.s_pcs_root);
    if &cshake256_32(b"QW35-QS-PCS-BIND-V1", &qs_bind_in) != expected_q_s_binding {
        return Err(
            "pretrained MXFP4 (q_pcs_root, s_pcs_root) weight binding mismatch".to_string(),
        );
    }

    // Replay Fiat–Shamir transcript identically!
    tr.absorb_root(b"stmt_weight_root", expected_weight_root);
    tr.absorb_root(b"stmt_b_in_root", expected_b_in_root);
    tr.absorb_root(b"stmt_b_out_root", expected_b_out_root);
    tr.absorb_u32(b"stmt_audited_layer", proof.audited_layer as u32);
    for r in [
        &proof.q_pcs_root,
        &proof.s_pcs_root,
        &proof.l_pcs_root,
        &proof.rhs_pcs_root,
        &proof.uw_pcs_root,
        &proof.rem_pcs_root,
        &proof.mult_pcs_root,
        &proof.x_ln2_pcs_root,
        &proof.y_gate_pcs_root,
        &proof.delta_gdn_pcs_root,
        &proof.delta_mlp_pcs_root,
    ] {
        tr.absorb_root(b"wit_pcs_root", r);
    }

    let log_h = proof.h_pad.trailing_zeros() as usize;
    let log_c = proof.c_len.trailing_zeros() as usize;
    let log_col = proof.wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;
    let m_wy_tab = WY_SHIFT as usize;

    // 1. Verify GDN WY equation: `expected_wy_claim == M_wy*(RHS(z) - UW(z)) + 2048 - R_rem(z)`!
    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    tr.absorb_ext4(b"wy_rhs_z", proof.rhs_eval_at_z);
    tr.absorb_ext4(b"wy_uw_z", proof.uw_eval_at_z);
    tr.absorb_ext4(b"wy_rem_z", proof.rem_eval_at_z);

    let expected_wy_claim = proof
        .rhs_eval_at_z
        .sub(proof.uw_eval_at_z)
        .scale_bb(WY_SCALE as u32)
        .add(Ext4::from_bb((WY_SCALE / 2) as u32))
        .sub(proof.rem_eval_at_z);

    let wy_chals =
        verify_gruen_einsum_mode2_ext4(expected_wy_claim, &z_h, &proof.wy_gruen_proof, tr)?;
    let ch_h = &wy_chals[..log_h];
    let ch_j = &wy_chals[log_h..];

    let (slt_pt, slt_l_eval) =
        verify_strict_lower_tri_ext4(log_h, log_c, &proof.slt_zero_proof, tr)?;
    if proof.d1b_rem_proof.m_wit != m_wy_wit || proof.d1b_rem_proof.m_tab != m_wy_tab {
        return Err("D1b dimensions mismatch".to_string());
    }
    let d1b_leaf_pt = verify_d1b_range_ext4(&proof.d1b_rem_proof, tr)?;

    // 2. Verify `MXFP4` E2M1 delayed-bind 0-mul Horner sumcheck!
    let log_j = proof.mxfp4_j_pad.trailing_zeros() as usize;
    let log_k = proof.mxfp4_k_pad.trailing_zeros() as usize;
    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj_out", log_j, true);
    let mxfp4_chals = verify_mxfp4_delayed_bjk_horner_ext4(
        proof.mxfp4_proof.claim,
        &r_j_mxfp4,
        &proof.mxfp4_proof,
        tr,
    )?;

    // 3. Verify `U1` Boundary Residual Weld: `b_out_eval == b_in_eval + delta_gdn_eval + delta_mlp_eval`!
    let z_bnd = tr.squeeze_ext4_vec(b"u1_bnd_pt", bnd_vars, true);
    tr.absorb_ext4(b"bnd_in_v", proof.b_in_eval);
    tr.absorb_ext4(b"bnd_out_v", proof.b_out_eval);
    tr.absorb_ext4(b"bnd_dg_v", proof.delta_gdn_eval);
    tr.absorb_ext4(b"bnd_dm_v", proof.delta_mlp_eval);
    if proof.b_out_eval
        != proof
            .b_in_eval
            .add(proof.delta_gdn_eval)
            .add(proof.delta_mlp_eval)
    {
        return Err(
            "U1 boundary residual weld mismatch (B_{l+1} != B_l + delta_gdn + delta_mlp)"
                .to_string(),
        );
    }

    // 4. Verify all 13 Succinct `Ext4` Coset-RS PCS openings (`>= 103.5`b AHIV17 UD)!
    let mut l_pt1 = Vec::with_capacity(log_h + 2 * log_c);
    l_pt1.extend_from_slice(ch_h);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(ch_j);

    let mut uw_pt2 = Vec::with_capacity(m_wy_wit);
    uw_pt2.extend_from_slice(ch_h);
    uw_pt2.extend_from_slice(ch_j);
    uw_pt2.extend_from_slice(&z_k);

    verify_pcs_claims(
        &proof.l_pcs_root,
        PcsShape::new(log_h + 2 * log_c, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: l_pt1,
                value: proof.wy_gruen_proof.terminal_openings.0,
            },
            MleEvalClaim {
                point: slt_pt,
                value: slt_l_eval,
            },
        ],
        &proof.l_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.rhs_pcs_root,
        PcsShape::new(m_wy_wit, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_hik.clone(),
            value: proof.rhs_eval_at_z,
        }],
        &proof.rhs_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.uw_pcs_root,
        PcsShape::new(m_wy_wit, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: proof.uw_eval_at_z,
            },
            MleEvalClaim {
                point: uw_pt2,
                value: proof.wy_gruen_proof.terminal_openings.1,
            },
        ],
        &proof.uw_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.rem_pcs_root,
        PcsShape::new(m_wy_wit, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik,
                value: proof.rem_eval_at_z,
            },
            MleEvalClaim {
                point: d1b_leaf_pt.clone(),
                value: proof.d1b_rem_proof.rem_leaf_eval,
            },
        ],
        &proof.rem_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.mult_pcs_root,
        PcsShape::new(m_wy_tab, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: d1b_leaf_pt[..m_wy_tab].to_vec(),
            value: proof.d1b_rem_proof.mult_leaf_eval,
        }],
        &proof.mult_pcs_proof,
        tr,
    )?;

    let mut pt_q = Vec::with_capacity(5 + log_j + log_k);
    pt_q.extend_from_slice(&mxfp4_chals.chals_b);
    pt_q.extend_from_slice(&mxfp4_chals.chals_j);
    pt_q.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_s = Vec::with_capacity(log_j + log_k);
    pt_s.extend_from_slice(&mxfp4_chals.chals_j);
    pt_s.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_x = Vec::with_capacity(log_c + 5 + log_k);
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);

    let mut pt_y = Vec::with_capacity(log_c + log_j);
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    verify_pcs_claims(
        &proof.q_pcs_root,
        PcsShape::new(5 + log_j + log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_q,
            value: proof.mxfp4_proof.finals.1,
        }],
        &proof.q_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.s_pcs_root,
        PcsShape::new(log_j + log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_s,
            value: proof.mxfp4_proof.finals.2,
        }],
        &proof.s_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.x_ln2_pcs_root,
        PcsShape::new(log_c + 5 + log_k, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_x,
            value: proof.mxfp4_proof.finals.0,
        }],
        &proof.x_ln2_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.y_gate_pcs_root,
        PcsShape::new(log_c + log_j, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_y,
            value: proof.mxfp4_proof.claim,
        }],
        &proof.y_gate_pcs_proof,
        tr,
    )?;

    verify_pcs_claims(
        expected_b_in_root,
        PcsShape::new(bnd_vars, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: proof.b_in_eval,
        }],
        &proof.b_in_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        expected_b_out_root,
        PcsShape::new(bnd_vars, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: proof.b_out_eval,
        }],
        &proof.b_out_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.delta_gdn_pcs_root,
        PcsShape::new(bnd_vars, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_bnd.clone(),
            value: proof.delta_gdn_eval,
        }],
        &proof.delta_gdn_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &proof.delta_mlp_pcs_root,
        PcsShape::new(bnd_vars, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_bnd,
            value: proof.delta_mlp_eval,
        }],
        &proof.delta_mlp_pcs_proof,
        tr,
    )?;

    let _ = (P_U32, Qwen35WeightRegistry::layer_tensor_names);
    Ok(())
}
