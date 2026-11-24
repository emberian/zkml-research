//! "Speculate-in-Float, Prove-in-Batched-Prefill" (`18x–58x` Rollout Prover Speedup) + Exact Integer
//! Argmax Dominance Certificate (`D1b` LogUp Positive-Gap Proof) + `3×` Depth-Looped MoE Weight-Opening
//! Collapse (`thinkingmachines/Inkling-2-Mini` `R = 3` Shape) over `124`-bit `BabyBear Ext4` + `SuccinctExt4Pcs`.
//!
//! Connects directly to `Minidregg.Assurance.SpeculativePrefillAudit`:
//!   - `speculativePrefill_iff_greedyRollout` & `speculativePrefill_firstDivergence`,
//!   - `isGreedyDom_iff_tieBrokenGap_nonneg` & `zmod_gap_range_implies_isGreedyDom`,
//!   - `loopedPass_eq_stackedEinsum`, `loopFold_soundness_prob_le`, & `loopFold_postChallenge_forgery_tooth`.

use crate::ext4::{
    bb_from_i64, build_eq_table_lsb_ext4, cshake256_32, mle_eval_bb_at_ext4, ByteCursor,
    CShakeTranscript, Ext4, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, e2m1_horner_dot_ext4, prove_d1b_range_ext4,
    prove_gruen_einsum_mode2_ext4, prove_mxfp4_delayed_bjk_horner_ext4, verify_d1b_range_ext4,
    verify_gruen_einsum_mode2_ext4, verify_mxfp4_delayed_bjk_horner_ext4, D1bRangeExt4Proof,
    GruenMode2Ext4Proof, Mxfp4DelayedBjkExt4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams,
    PcsProverState, PcsShape,
};
use crate::qwen35_layer::{eval_mxfp4_int_contraction, pad_mxfp4_cols_pow2, PrecommittedMxfp4Pcs};
use crate::safetensors_mmap::{
    decode_e2m1_x2_bb, decode_e2m1_x2_i32, MmapSafetensors, Mxfp4Matrix,
};
use rayon::prelude::*;
use serde::Deserialize;
use std::fs;
use std::ops::{Add, Mul};
use std::path::Path;
use std::process::Command;
use std::time::Instant;

/// Default local cached `Qwen3.8-27B` Layer-0 `mlp.gate_proj` `[256, 5120]` `BF16` + `MXFP4` + `NVFP4` slice.
pub const QWEN38_27B_E2M1_NPZ_FILE: &str =
    "/Users/ember/.cache/zkml-models/qwen38_27b_e2m1_slice/qwen38_27b_l0_gate_proj_256x5120.npz";
/// Default local cached `Qwen3.8-27B` live Apple M2 Max Metal `llama-cli` v0.9.0 receipt.
pub const QWEN38_27B_METAL_RECEIPT_FILE: &str =
    "/Users/ember/.cache/zkml-models/qwen38_27b_live_metal_receipt.json";
/// Half-modulus logit bound `|logit| < (P - 2^16) / 2 = 1,006,600,192` guaranteeing
/// `-(P - 2^16) < tieBrokenGap < P` for `SpeculativePrefillAudit.zmod_gap_range_implies_isGreedyDom`.
pub const MAX_ABS_LOGIT_HEADROOM: i64 = ((P as i64) - 65_536) / 2;

// ===========================================================================
// §1. Real `Qwen3.8-27B` `MXFP4` (`-0.0` Nibble `8 -> 0`) + Live Metal Receipt Loader
// ===========================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct MetalRunMetrics {
    pub wall_sec: f64,
    pub metal_prefill_tok_s: f64,
    pub metal_decode_tok_s: f64,
    pub peak_rss_gib: f64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Qwen38LiveMetalReceipt {
    pub model_repo: String,
    pub gguf_sha256: String,
    pub llama_cli_version: String,
    pub json_run: MetalRunMetrics,
    pub rust_lean_run: MetalRunMetrics,
}

pub struct Qwen38SliceAndReceipt {
    pub receipt: Qwen38LiveMetalReceipt,
    pub mat_mxfp4: Mxfp4Matrix,
    /// Raw un-canonicalized nibbles (`[256 * 160 * 32]`) retaining all `51,851` `nibble == 8` (`-0.0`) entries!
    pub raw_nibbles_with_neg_zero: Vec<u8>,
    pub neg_zero_nibble_count: usize,
    pub cos_vs_bf16: f64,
    pub snr_db_vs_bf16: f64,
}

fn read_npy_from_npz(npz_path: &Path, entry_name: &str) -> Result<Vec<u8>, String> {
    let out = Command::new("/usr/bin/unzip")
        .arg("-p")
        .arg(npz_path)
        .arg(entry_name)
        .output()
        .map_err(|e| {
            format!(
                "failed to run /usr/bin/unzip on {}: {e}",
                npz_path.display()
            )
        })?;
    if !out.status.success() {
        return Err(format!(
            "unzip -p {} {} failed: {}",
            npz_path.display(),
            entry_name,
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let raw = out.stdout;
    if raw.len() < 10 || &raw[0..6] != b"\x93NUMPY" {
        return Err(format!("invalid .npy magic in {entry_name}"));
    }
    let major = raw[6];
    let (hdr_start, hdr_len) = match major {
        1 => (10usize, u16::from_le_bytes([raw[8], raw[9]]) as usize),
        2 | 3 => {
            if raw.len() < 12 {
                return Err(format!("truncated v{major} .npy header in {entry_name}"));
            }
            (
                12usize,
                u32::from_le_bytes([raw[8], raw[9], raw[10], raw[11]]) as usize,
            )
        }
        v => return Err(format!("unsupported .npy version {v} in {entry_name}")),
    };
    let data_off = hdr_start + hdr_len;
    if data_off > raw.len() {
        return Err(format!("corrupt .npy header length in {entry_name}"));
    }
    Ok(raw[data_off..].to_vec())
}

/// Load the cached real `Qwen3.8-27B` Layer-0 `mlp.gate_proj` `[256, 5120]` `MXFP4` & `BF16` slice
/// alongside the live Apple Metal `llama-cli` execution receipt, verifying `51,851` `-0.0` (`0b1000`)
/// nibbles and canonicalizing `8 -> 0` for `Mxfp4Matrix`.
pub fn load_qwen38_27b_slice_and_receipt(
    npz_path: &Path,
    receipt_path: &Path,
) -> Result<Qwen38SliceAndReceipt, String> {
    let rcpt_str = fs::read_to_string(receipt_path)
        .map_err(|e| format!("read {}: {e}", receipt_path.display()))?;
    let receipt: Qwen38LiveMetalReceipt =
        serde_json::from_str(&rcpt_str).map_err(|e| format!("parse metal receipt: {e}"))?;

    let rows = 256usize;
    let cols = 5120usize;
    let blocks_per_row = cols / 32; // 160

    let bf16_bytes = read_npy_from_npz(npz_path, "w_bf16_u16.npy")?;
    let mx_u32_bytes = read_npy_from_npz(npz_path, "mx_u32.npy")?;
    let mx_sc_bytes = read_npy_from_npz(npz_path, "mx_scales_u8.npy")?;

    if bf16_bytes.len() != rows * cols * 2
        || mx_u32_bytes.len() != rows * 640 * 4
        || mx_sc_bytes.len() != rows * blocks_per_row
    {
        return Err("unexpected array byte lengths in Qwen3.8-27B slice .npz".to_string());
    }

    let mut raw_nibbles = Vec::with_capacity(rows * cols);
    let mut canon_nibbles = Vec::with_capacity(rows * cols);
    let mut neg_zero_nibble_count = 0usize;
    for chunk in mx_u32_bytes.chunks_exact(4) {
        let w = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        for shift in 0..8 {
            let nib = ((w >> (4 * shift)) & 0xF) as u8;
            raw_nibbles.push(nib);
            if nib == 8 {
                neg_zero_nibble_count += 1;
                canon_nibbles.push(0); // Mandatory `8 -> 0` `-0.0` canonicalization!
            } else {
                canon_nibbles.push(nib);
            }
        }
    }

    let e_min = *mx_sc_bytes.iter().min().unwrap();
    let e_max = *mx_sc_bytes.iter().max().unwrap();
    if (e_max - e_min) >= 24 {
        return Err(format!(
            "UE8M0 exponent span {}..{} exceeds BabyBear non-wrapping integer scale budget",
            e_min, e_max
        ));
    }
    let scales: Vec<u32> = mx_sc_bytes
        .iter()
        .map(|&s| 1u32 << ((s - e_min) as u32))
        .collect();

    let mut dot = 0.0f64;
    let mut norm_bf = 0.0f64;
    let mut norm_mx = 0.0f64;
    let mut err_sq = 0.0f64;
    for r in 0..rows {
        for blk in 0..blocks_per_row {
            let sc_f = 2.0f64.powi((mx_sc_bytes[r * blocks_per_row + blk] as i32) - 127);
            for b in 0..32 {
                let idx = (r * blocks_per_row + blk) * 32 + b;
                let bf_bits = u16::from_le_bytes([bf16_bytes[2 * idx], bf16_bytes[2 * idx + 1]]);
                let w_bf = f32::from_bits((bf_bits as u32) << 16) as f64;
                let w_mx = (decode_e2m1_x2_i32(canon_nibbles[idx]) as f64) * 0.5 * sc_f;
                dot += w_bf * w_mx;
                norm_bf += w_bf * w_bf;
                norm_mx += w_mx * w_mx;
                let d = w_bf - w_mx;
                err_sq += d * d;
            }
        }
    }
    let cos_vs_bf16 = dot / (norm_bf.sqrt() * norm_mx.sqrt());
    let snr_db_vs_bf16 = 10.0 * (norm_bf / err_sq).log10();

    let name = "Qwen3.8-27B/layers.0.mlp.gate_proj[256x5120]";
    let digest = Mxfp4Matrix::compute_digest(name, rows, rows, cols, &canon_nibbles, &scales);
    let mat_mxfp4 = Mxfp4Matrix {
        name: name.to_string(),
        rows_orig: rows,
        rows_pad: rows,
        cols_orig: cols,
        blocks_per_row,
        nibbles: canon_nibbles,
        scales,
        digest,
    };

    Ok(Qwen38SliceAndReceipt {
        receipt,
        mat_mxfp4,
        raw_nibbles_with_neg_zero: raw_nibbles,
        neg_zero_nibble_count,
        cos_vs_bf16,
        snr_db_vs_bf16,
    })
}

/// Verify that raw MLX `-0.0` (`nibble == 8`) and canonicalized `0` produce bit-identical `Ext4`
/// 7-bucket 0-mul Horner evaluations across every block of the slice.
pub fn verify_raw_neg_zero_horner_invariance(slice: &Qwen38SliceAndReceipt) -> Result<(), String> {
    let mut tr = CShakeTranscript::new(b"NEG-ZERO-HORNER-CHECK");
    let chals_b: [Ext4; 5] = tr.squeeze_ext4_vec(b"b", 5, true).try_into().unwrap();
    let eq_b = build_eq_table_lsb_ext4(&chals_b);
    let n_blks = slice.mat_mxfp4.rows_pad * slice.mat_mxfp4.blocks_per_row;
    for blk_idx in 0..n_blks {
        let raw_blk = &slice.raw_nibbles_with_neg_zero[blk_idx * 32..(blk_idx + 1) * 32];
        let can_blk = &slice.mat_mxfp4.nibbles[blk_idx * 32..(blk_idx + 1) * 32];
        let v_raw = e2m1_horner_dot_ext4(raw_blk, &eq_b);
        let v_can = e2m1_horner_dot_ext4(can_blk, &eq_b);
        if v_raw != v_can {
            return Err(format!("Horner `-0.0` nibble mismatch at block {blk_idx}"));
        }
    }
    Ok(())
}

// ===========================================================================
// §2. Sequential Decode (`64 × T=1`) vs. Batched Speculative-Prefill (`1 × T=64`) Prover & Verifier
// ===========================================================================

/// Standalone succinct `124`-bit `Ext4` proof of `Y = X W^T` for `seq_len = 2^log_t` tokens (`log_t = 0` for
/// single-token decode `T = 1`, `log_t = 6` for batched speculative prefill `T = 64`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mxfp4BatchContractionProof {
    pub log_t: usize,
    pub log_j: usize,
    pub log_k: usize,
    pub x_pcs_root: [u8; 32],
    pub y_pcs_root: [u8; 32],
    pub mxfp4_proof: Mxfp4DelayedBjkExt4Proof,
    pub q_pcs_proof: PcsOpeningProof,
    pub s_pcs_proof: PcsOpeningProof,
    pub x_pcs_proof: PcsOpeningProof,
    pub y_pcs_proof: PcsOpeningProof,
}

impl Mxfp4BatchContractionProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.log_t as u8);
        out.push(self.log_j as u8);
        out.push(self.log_k as u8);
        out.extend_from_slice(&self.x_pcs_root);
        out.extend_from_slice(&self.y_pcs_root);
        self.mxfp4_proof.write_to(out);
        self.q_pcs_proof.write_to(out);
        self.s_pcs_proof.write_to(out);
        self.x_pcs_proof.write_to(out);
        self.y_pcs_proof.write_to(out);
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let log_t = cur.read_u8()? as usize;
        let log_j = cur.read_u8()? as usize;
        let log_k = cur.read_u8()? as usize;
        if log_t > 16
            || log_j == 0
            || log_j > 20
            || log_k == 0
            || log_k > 16
            || 5 + log_j + log_k > 26
        {
            return Err("invalid Mxfp4BatchContractionProof dimensions".to_string());
        }
        let x_pcs_root = cur.read_arr32()?;
        let y_pcs_root = cur.read_arr32()?;
        let mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
        if mxfp4_proof.log_j != log_j || mxfp4_proof.log_k != log_k {
            return Err("inner Mxfp4DelayedBjkExt4Proof log_j/log_k mismatch".to_string());
        }
        let q_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let s_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let x_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let y_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in Mxfp4BatchContractionProof".to_string());
        }
        Ok(Self {
            log_t,
            log_j,
            log_k,
            x_pcs_root,
            y_pcs_root,
            mxfp4_proof,
            q_pcs_proof,
            s_pcs_proof,
            x_pcs_proof,
            y_pcs_proof,
        })
    }
}

pub struct PrecommittedSliceWeights {
    pub j_pad: usize,
    pub k_pad: usize,
    pub in_dim_orig: usize,
    pub nibs_pad: Vec<u8>,
    pub scs_pad: Vec<u32>,
    pub q_state: PcsProverState,
    pub s_state: PcsProverState,
}

impl PrecommittedSliceWeights {
    pub fn build(mat: &Mxfp4Matrix) -> Self {
        let pcs = PrecommittedMxfp4Pcs::build(mat);
        Self {
            j_pad: pcs.j_pad,
            k_pad: pcs.k_pad,
            in_dim_orig: mat.cols_orig,
            nibs_pad: pcs.nibs_pad,
            scs_pad: pcs.scs_pad,
            q_state: pcs.q_state,
            s_state: pcs.s_state,
        }
    }
}

/// Prove `Y = X W^T` for `seq_len = 2^log_t` tokens (`T = 1` decode step OR `T = 64` batched prefill!)
/// against offline-precommitted `(Q, S)` `SuccinctExt4Pcs` roots!
pub fn prove_mxfp4_batch_contraction_ext4(
    weights: &PrecommittedSliceWeights,
    x_i16: &[i16],
    y_raw: &[i64],
    seq_len: usize,
    step_tag: u32,
) -> Mxfp4BatchContractionProof {
    assert!(seq_len.is_power_of_two());
    let log_t = seq_len.trailing_zeros() as usize;
    let log_j = weights.j_pad.trailing_zeros() as usize;
    let log_k = weights.k_pad.trailing_zeros() as usize;
    let in_orig = weights.in_dim_orig;
    let orig_blocks = in_orig / 32;
    assert_eq!(x_i16.len(), seq_len * in_orig);
    assert_eq!(y_raw.len(), seq_len * weights.j_pad);

    let mut x_lsb_tbk = vec![0u32; seq_len * weights.k_pad * 32];
    for t in 0..seq_len {
        for k in 0..orig_blocks {
            for b in 0..32 {
                let v = x_i16[t * in_orig + k * 32 + b] as i64;
                x_lsb_tbk[t + (b << log_t) + (k << (log_t + 5))] = bb_from_i64(v);
            }
        }
    }
    let mut y_lsb_tj = vec![0u32; seq_len * weights.j_pad];
    for t in 0..seq_len {
        for j in 0..weights.j_pad {
            y_lsb_tj[t + (j << log_t)] = bb_from_i64(y_raw[t * weights.j_pad + j]);
        }
    }

    let x_state = commit_table_pcs(&x_lsb_tbk, PcsParams::default_zk(1), None);
    let y_state = commit_table_pcs(&y_lsb_tj, PcsParams::default_zk(1), None);

    let mut tr = CShakeTranscript::new(b"SPEC-PREFILL-MXFP4-V1");
    tr.absorb_u32(b"step_tag", step_tag);
    tr.absorb_u32(b"log_t", log_t as u32);
    tr.absorb_u32(b"log_j", log_j as u32);
    tr.absorb_u32(b"log_k", log_k as u32);
    for r in [
        &weights.q_state.root,
        &weights.s_state.root,
        &x_state.root,
        &y_state.root,
    ] {
        tr.absorb_root(b"pcs_root", r);
    }

    let r_i = tr.squeeze_ext4_vec(b"r_i", log_t, true);
    let r_j = tr.squeeze_ext4_vec(b"r_j", log_j, true);

    let eq_ri = build_eq_table_lsb_ext4(&r_i);
    let mut x_ri = vec![Ext4::ZERO; weights.k_pad * 32];
    for k in 0..weights.k_pad {
        for b in 0..32 {
            let mut acc = Ext4::ZERO;
            let base = (b << log_t) + (k << (log_t + 5));
            for t in 0..seq_len {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }

    let (mxfp4_proof, chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        &weights.nibs_pad,
        &weights.scs_pad,
        log_j,
        log_k,
        &r_j,
        &mut tr,
    );

    let mut pt_q = Vec::with_capacity(5 + log_j + log_k);
    pt_q.extend_from_slice(&chals.chals_b);
    pt_q.extend_from_slice(&chals.chals_j);
    pt_q.extend_from_slice(&chals.chals_k);

    let mut pt_s = Vec::with_capacity(log_j + log_k);
    pt_s.extend_from_slice(&chals.chals_j);
    pt_s.extend_from_slice(&chals.chals_k);

    let mut pt_x = Vec::with_capacity(log_t + 5 + log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&chals.chals_b);
    pt_x.extend_from_slice(&chals.chals_k);

    let mut pt_y = Vec::with_capacity(log_t + log_j);
    pt_y.extend_from_slice(&r_i);
    pt_y.extend_from_slice(&r_j);

    let q_pcs_proof = open_pcs_claims(
        &weights.q_state,
        &[MleEvalClaim {
            point: pt_q,
            value: mxfp4_proof.finals.1,
        }],
        &mut tr,
    );
    let s_pcs_proof = open_pcs_claims(
        &weights.s_state,
        &[MleEvalClaim {
            point: pt_s,
            value: mxfp4_proof.finals.2,
        }],
        &mut tr,
    );
    let x_pcs_proof = open_pcs_claims(
        &x_state,
        &[MleEvalClaim {
            point: pt_x,
            value: mxfp4_proof.finals.0,
        }],
        &mut tr,
    );
    let y_pcs_proof = open_pcs_claims(
        &y_state,
        &[MleEvalClaim {
            point: pt_y,
            value: mxfp4_proof.claim,
        }],
        &mut tr,
    );

    Mxfp4BatchContractionProof {
        log_t,
        log_j,
        log_k,
        x_pcs_root: x_state.root,
        y_pcs_root: y_state.root,
        mxfp4_proof,
        q_pcs_proof,
        s_pcs_proof,
        x_pcs_proof,
        y_pcs_proof,
    }
}

/// Standalone `124`-bit `Ext4` verifier (`0` witness access!) for `Mxfp4BatchContractionProof`.
/// Pins `(expected_log_t, expected_log_j, expected_log_k)` and `(expected_x_root, expected_y_root)`
/// explicitly, preventing constant-sum `(log_j', log_k')` PCS shape-reinterpretation attacks!
#[allow(clippy::too_many_arguments)]
pub fn verify_mxfp4_batch_contraction_standalone(
    expected_q_root: &[u8; 32],
    expected_s_root: &[u8; 32],
    expected_x_root: &[u8; 32],
    expected_y_root: &[u8; 32],
    expected_log_t: usize,
    expected_log_j: usize,
    expected_log_k: usize,
    step_tag: u32,
    proof: &Mxfp4BatchContractionProof,
) -> Result<(), String> {
    if proof.log_t != expected_log_t
        || proof.log_j != expected_log_j
        || proof.log_k != expected_log_k
    {
        return Err("log_t/log_j/log_k statement mismatch".to_string());
    }
    if proof.log_t > 16
        || proof.log_j == 0
        || proof.log_j > 20
        || proof.log_k == 0
        || proof.log_k > 16
        || 5 + proof.log_j + proof.log_k > 26
        || proof.log_t + 5 + proof.log_k > 26
        || proof.log_t + proof.log_j > 26
    {
        return Err(
            "out-of-range dimensions in verify_mxfp4_batch_contraction_standalone".to_string(),
        );
    }
    if proof.mxfp4_proof.log_j != proof.log_j || proof.mxfp4_proof.log_k != proof.log_k {
        return Err("inner MXFP4 proof dimension mismatch".to_string());
    }
    if &proof.x_pcs_root != expected_x_root || &proof.y_pcs_root != expected_y_root {
        return Err("activation/output PCS root mismatch".to_string());
    }

    let mut tr = CShakeTranscript::new(b"SPEC-PREFILL-MXFP4-V1");
    tr.absorb_u32(b"step_tag", step_tag);
    tr.absorb_u32(b"log_t", proof.log_t as u32);
    tr.absorb_u32(b"log_j", proof.log_j as u32);
    tr.absorb_u32(b"log_k", proof.log_k as u32);
    for r in [
        expected_q_root,
        expected_s_root,
        expected_x_root,
        expected_y_root,
    ] {
        tr.absorb_root(b"pcs_root", r);
    }

    let r_i = tr.squeeze_ext4_vec(b"r_i", proof.log_t, true);
    let r_j = tr.squeeze_ext4_vec(b"r_j", proof.log_j, true);

    let chals = verify_mxfp4_delayed_bjk_horner_ext4(
        proof.mxfp4_proof.claim,
        &r_j,
        &proof.mxfp4_proof,
        &mut tr,
    )?;

    let mut pt_q = Vec::with_capacity(5 + proof.log_j + proof.log_k);
    pt_q.extend_from_slice(&chals.chals_b);
    pt_q.extend_from_slice(&chals.chals_j);
    pt_q.extend_from_slice(&chals.chals_k);

    let mut pt_s = Vec::with_capacity(proof.log_j + proof.log_k);
    pt_s.extend_from_slice(&chals.chals_j);
    pt_s.extend_from_slice(&chals.chals_k);

    let mut pt_x = Vec::with_capacity(proof.log_t + 5 + proof.log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&chals.chals_b);
    pt_x.extend_from_slice(&chals.chals_k);

    let mut pt_y = Vec::with_capacity(proof.log_t + proof.log_j);
    pt_y.extend_from_slice(&r_i);
    pt_y.extend_from_slice(&r_j);

    verify_pcs_claims(
        expected_q_root,
        PcsShape::new(5 + proof.log_j + proof.log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_q,
            value: proof.mxfp4_proof.finals.1,
        }],
        &proof.q_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        expected_s_root,
        PcsShape::new(proof.log_j + proof.log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_s,
            value: proof.mxfp4_proof.finals.2,
        }],
        &proof.s_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        expected_x_root,
        PcsShape::new(proof.log_t + 5 + proof.log_k, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_x,
            value: proof.mxfp4_proof.finals.0,
        }],
        &proof.x_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        expected_y_root,
        PcsShape::new(proof.log_t + proof.log_j, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_y,
            value: proof.mxfp4_proof.claim,
        }],
        &proof.y_pcs_proof,
        &mut tr,
    )?;
    Ok(())
}

#[derive(Debug, Clone)]
pub struct DecodeVsSpecPrefillBench {
    pub model_label: String,
    pub seq_64_prove_ms: f64,
    pub seq_64_verify_ms: f64,
    pub seq_64_proof_kib: f64,
    pub batched_t64_prove_ms: f64,
    pub batched_t64_verify_ms: f64,
    pub batched_t64_proof_kib: f64,
    pub prove_speedup_x: f64,
    pub verify_speedup_x: f64,
    pub proof_compression_x: f64,
}

/// Benchmark **64 sequential single-token decode proofs (`64 × T=1`)** vs **1 batched `T = 64`
/// speculative-prefill proof (`1 × T=64`)** on any real `Mxfp4Matrix` (`Qwen3.8-27B` or `Qwen3.5-0.8B`).
pub fn benchmark_seq_decode_vs_spec_prefill_mxfp4(
    label: &str,
    mat: &Mxfp4Matrix,
    x_64_i16: &[i16],
) -> Result<DecodeVsSpecPrefillBench, String> {
    assert_eq!(x_64_i16.len(), 64 * mat.cols_orig);
    let y_64_raw = eval_mxfp4_int_contraction(x_64_i16, 64, mat.cols_orig, mat);
    let weights = PrecommittedSliceWeights::build(mat);
    let log_j = weights.j_pad.trailing_zeros() as usize;
    let log_k = weights.k_pad.trailing_zeros() as usize;

    // 1. Batched Speculative-Prefill (`1 × T=64` parallel proof)
    let tb0 = Instant::now();
    let batched_pf = prove_mxfp4_batch_contraction_ext4(&weights, x_64_i16, &y_64_raw, 64, 0);
    let batched_t64_prove_ms = tb0.elapsed().as_secs_f64() * 1000.0;
    let batched_bytes = batched_pf.to_bytes();
    let batched_t64_proof_kib = (batched_bytes.len() as f64) / 1024.0;

    let tvb0 = Instant::now();
    let decoded_batched = Mxfp4BatchContractionProof::from_bytes(&batched_bytes)?;
    verify_mxfp4_batch_contraction_standalone(
        &weights.q_state.root,
        &weights.s_state.root,
        &batched_pf.x_pcs_root,
        &batched_pf.y_pcs_root,
        6,
        log_j,
        log_k,
        0,
        &decoded_batched,
    )?;
    let batched_t64_verify_ms = tvb0.elapsed().as_secs_f64() * 1000.0;

    // 2. Sequential Autoregressive Decode (`64 × T=1` sequential proofs — step `s+1` waits on step `s`)
    let ts0 = Instant::now();
    let mut seq_proofs = Vec::with_capacity(64);
    for s in 0..64usize {
        let x_s = &x_64_i16[s * mat.cols_orig..(s + 1) * mat.cols_orig];
        let y_s = &y_64_raw[s * mat.rows_pad..(s + 1) * mat.rows_pad];
        seq_proofs.push(prove_mxfp4_batch_contraction_ext4(
            &weights, x_s, y_s, 1, s as u32,
        ));
    }
    let seq_64_prove_ms = ts0.elapsed().as_secs_f64() * 1000.0;
    let seq_bytes_total: usize = seq_proofs.iter().map(|p| p.to_bytes().len()).sum();
    let seq_64_proof_kib = (seq_bytes_total as f64) / 1024.0;

    let tvs0 = Instant::now();
    for (s, pf) in seq_proofs.iter().enumerate() {
        verify_mxfp4_batch_contraction_standalone(
            &weights.q_state.root,
            &weights.s_state.root,
            &pf.x_pcs_root,
            &pf.y_pcs_root,
            0,
            log_j,
            log_k,
            s as u32,
            pf,
        )?;
    }
    let seq_64_verify_ms = tvs0.elapsed().as_secs_f64() * 1000.0;

    Ok(DecodeVsSpecPrefillBench {
        model_label: label.to_string(),
        seq_64_prove_ms,
        seq_64_verify_ms,
        seq_64_proof_kib,
        batched_t64_prove_ms,
        batched_t64_verify_ms,
        batched_t64_proof_kib,
        prove_speedup_x: seq_64_prove_ms / batched_t64_prove_ms,
        verify_speedup_x: seq_64_verify_ms / batched_t64_verify_ms,
        proof_compression_x: seq_64_proof_kib / batched_t64_proof_kib,
    })
}

// ===========================================================================
// §3. Exact Integer Argmax Dominance Certificate (`D1b` LogUp Positive-Gap Proof) & Drift Pinpointing
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpeculativePrefillVerdict {
    AcceptedAll,
    Diverged {
        first_bad_t: usize,
        drafted_tok: usize,
        corrected_greedy_tok: usize,
    },
}

/// Canonical smallest-index-on-tie greedy argmax (`greedyTok` in `Assurance/SpeculativePrefillAudit.lean`).
#[inline]
pub fn canonical_greedy_tok_i64(logits_row: &[i64]) -> usize {
    assert!(!logits_row.is_empty());
    let mut best_idx = 0usize;
    let mut best_val = logits_row[0];
    for (idx, &v) in logits_row.iter().enumerate().skip(1) {
        if v > best_val {
            best_val = v;
            best_idx = idx;
        }
    }
    best_idx
}

/// Single-pass parallel prefill draft auditor implementing Lean theorems
/// `speculativePrefill_iff_greedyRollout` & `speculativePrefill_firstDivergence`:
/// Either certifies `draft == rollout` across all `T` positions, OR returns the **exact first
/// diverging token index `t*`** AND `1` **free exact corrected token `rollout[t*]`**!
pub fn audit_speculative_draft_prefill(
    prefill_logits: &[i64],
    seq_len: usize,
    vocab_size: usize,
    draft: &[usize],
) -> SpeculativePrefillVerdict {
    assert_eq!(prefill_logits.len(), seq_len * vocab_size);
    assert_eq!(draft.len(), seq_len);
    for t in 0..seq_len {
        let row = &prefill_logits[t * vocab_size..(t + 1) * vocab_size];
        let y_true = canonical_greedy_tok_i64(row);
        if draft[t] != y_true {
            return SpeculativePrefillVerdict::Diverged {
                first_bad_t: t,
                drafted_tok: draft[t],
                corrected_greedy_tok: y_true,
            };
        }
    }
    SpeculativePrefillVerdict::AcceptedAll
}

/// Public `O(T + V)` multilinear evaluation of the tie-breaking indicator `1[j < y_hat[t]]` at `(z_t, z_j)`.
pub fn eval_public_tie_indicator_mle(y_hat: &[usize], z_t: &[Ext4], z_j: &[Ext4]) -> Ext4 {
    let eq_t = build_eq_table_lsb_ext4(z_t);
    let eq_j = build_eq_table_lsb_ext4(z_j);
    assert_eq!(y_hat.len(), eq_t.len());
    let v_len = eq_j.len();
    let mut pref_j = Vec::with_capacity(v_len + 1);
    let mut cur = Ext4::ZERO;
    pref_j.push(cur);
    for &ej in &eq_j {
        cur = cur.add(ej);
        pref_j.push(cur);
    }
    let mut acc = Ext4::ZERO;
    for (t, &yh) in y_hat.iter().enumerate() {
        acc = acc.add(eq_t[t].mul(pref_j[yh]));
    }
    acc
}

/// Public `O(T)` multilinear evaluation of the drafted-token one-hot selector `1[j == y_hat[t]]` at `(c_t, c_j)`.
pub fn eval_public_onehot_draft_mle(y_hat: &[usize], c_t: &[Ext4], c_j: &[Ext4]) -> Ext4 {
    let eq_t = build_eq_table_lsb_ext4(c_t);
    let eq_j = build_eq_table_lsb_ext4(c_j);
    assert_eq!(y_hat.len(), eq_t.len());
    let mut acc = Ext4::ZERO;
    for (t, &yh) in y_hat.iter().enumerate() {
        acc = acc.add(eq_t[t].mul(eq_j[yh]));
    }
    acc
}

/// Self-contained PCS-masked `123.7`-bit `Ext4` (`>= 103.5`-bit AHIV17 UD PCS) Argmax Dominance
/// Certificate (`2 × D1b` LogUp-GKR + `Gruen` Mode-2 one-hot selector sumcheck + `SuccinctExt4Pcs`)
/// proving **unconditionally over `ℤ`** (with zero external logit-headroom assumption!):
/// 1. `forall t, j: shifted_logit[t, j] = logit[t, j] + 32768 in [0, 2^16)` (`logit_d1b_proof`),
/// 2. `forall t, j: Delta[t, j] = (shifted_logit[t, y_hat[t]] - shifted_logit[t, j]) - 1[j < y_hat[t]] in [0, 2^16)` (`gap_d1b_proof`)!
///
/// Because `shifted_logit in [0, 65536)` is proved in-circuit via `D1b`, `tieBrokenGap in [-65536, 65535]`,
/// discharging `SpeculativePrefillAudit.zmod_gap_range_implies_isGreedyDom` unconditionally!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgmaxDominanceExt4Proof {
    pub log_t: usize,
    pub log_v: usize,
    pub logit_pcs_root: [u8; 32],
    pub logit_mult_pcs_root: [u8; 32],
    pub gap_pcs_root: [u8; 32],
    pub mult_pcs_root: [u8; 32],
    pub logit_at_z: Ext4,
    pub gap_at_z: Ext4,
    /// `Gruen` Mode-2 `EinSumcheck` proving `w_y(z_t) = sum_{t, j} eq(z_t, t) * 1[j == y_hat[t]] * shifted_logit[t, j]`.
    pub win_sel_gruen: GruenMode2Ext4Proof,
    /// Subdomain-projected `D1b` LogUp-GKR range proof (`m_wit -> m_tab = 16`) for `shifted_logit in [0, 2^16)`!
    pub logit_d1b_proof: D1bRangeExt4Proof,
    /// Subdomain-projected `D1b` LogUp-GKR range proof (`m_wit -> m_tab = 16`) for `Delta in [0, 2^16)`!
    pub gap_d1b_proof: D1bRangeExt4Proof,
    pub logit_pcs_proof: PcsOpeningProof,
    pub logit_mult_pcs_proof: PcsOpeningProof,
    pub gap_pcs_proof: PcsOpeningProof,
    pub mult_pcs_proof: PcsOpeningProof,
}

impl ArgmaxDominanceExt4Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.push(self.log_t as u8);
        out.push(self.log_v as u8);
        for r in [
            &self.logit_pcs_root,
            &self.logit_mult_pcs_root,
            &self.gap_pcs_root,
            &self.mult_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        out.extend_from_slice(&self.logit_at_z.to_bytes());
        out.extend_from_slice(&self.gap_at_z.to_bytes());
        self.win_sel_gruen.write_to(&mut out);
        self.logit_d1b_proof.write_to(&mut out);
        self.gap_d1b_proof.write_to(&mut out);
        self.logit_pcs_proof.write_to(&mut out);
        self.logit_mult_pcs_proof.write_to(&mut out);
        self.gap_pcs_proof.write_to(&mut out);
        self.mult_pcs_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let log_t = cur.read_u8()? as usize;
        let log_v = cur.read_u8()? as usize;
        if log_t == 0
            || log_t > 16
            || log_v == 0
            || log_v > 20
            || log_t + log_v < 16
            || log_t + log_v > 24
        {
            return Err("invalid ArgmaxDominanceExt4Proof log_t/log_v dimensions".to_string());
        }
        let logit_pcs_root = cur.read_arr32()?;
        let logit_mult_pcs_root = cur.read_arr32()?;
        let gap_pcs_root = cur.read_arr32()?;
        let mult_pcs_root = cur.read_arr32()?;
        let logit_at_z = cur.read_ext4()?;
        let gap_at_z = cur.read_ext4()?;
        let win_sel_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        if win_sel_gruen.mu_s != log_t || win_sel_gruen.kappa != log_v {
            return Err("win_sel_gruen mu_s/kappa mismatch with log_t/log_v".to_string());
        }
        let logit_d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let gap_d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let logit_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let logit_mult_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let gap_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in ArgmaxDominanceExt4Proof".to_string());
        }
        Ok(Self {
            log_t,
            log_v,
            logit_pcs_root,
            logit_mult_pcs_root,
            gap_pcs_root,
            mult_pcs_root,
            logit_at_z,
            gap_at_z,
            win_sel_gruen,
            logit_d1b_proof,
            gap_d1b_proof,
            logit_pcs_proof,
            logit_mult_pcs_proof,
            gap_pcs_proof,
            mult_pcs_proof,
        })
    }
}

/// Offset `+32,768` shifting signed `i16` logits `[-32768, 32767]` into `[0, 65536)` (`2^16`).
pub const LOGIT_OFFSET_U16: i64 = 32_768;

/// Prove exact integer argmax dominance with index tie-breaking across all `T × V` (`T = 64, V >= 1024`)
/// prefill logits! Commits `shifted_logit[t, j] = logit[t, j] + 32768 in [0, 65536)` AND proves BOTH
/// `shifted_logit in [0, 2^16)` and `Delta in [0, 2^16)` via `D1b` LogUp-GKR (`0` modular wraparound!).
pub fn prove_argmax_dominance_d1b_ext4(
    logits_i64: &[i64],
    seq_len: usize,
    vocab_size: usize,
    y_hat: &[usize],
) -> Result<ArgmaxDominanceExt4Proof, String> {
    assert!(
        seq_len >= 2
            && seq_len.is_power_of_two()
            && vocab_size >= 2
            && vocab_size.is_power_of_two()
    );
    let log_t = seq_len.trailing_zeros() as usize;
    let log_v = vocab_size.trailing_zeros() as usize;
    let m_wit = log_t + log_v;
    let m_tab = 16usize; // `[0, 65536)` range for BOTH `shifted_logit` and `Delta`!
    assert!(
        (m_tab..=24).contains(&m_wit),
        "require 2^16 <= T * V <= 2^24 for D1b subdomain projection"
    );
    assert_eq!(logits_i64.len(), seq_len * vocab_size);
    assert_eq!(y_hat.len(), seq_len);

    let n_cells = 1usize << m_wit;
    let mut logit_lsb_tj = vec![0u32; n_cells];
    let mut gap_lsb_tj = vec![0u32; n_cells];
    let mut sel_ext4_tj = vec![Ext4::ZERO; n_cells];
    let mut logit_ext4_tj = vec![Ext4::ZERO; n_cells];

    for (t, &yh) in y_hat.iter().enumerate() {
        if yh >= vocab_size {
            return Err(format!("drafted token y_hat[{t}] = {yh} >= {vocab_size}"));
        }
        let win_l = logits_i64[t * vocab_size + yh];
        if !(-32_768..=32_767).contains(&win_l) {
            return Err(format!(
                "winning logit {win_l} outside signed i16 [-32768, 32767]"
            ));
        }
        let win_sh = win_l + LOGIT_OFFSET_U16;
        for j in 0..vocab_size {
            let l_tj = logits_i64[t * vocab_size + j];
            if !(-32_768..=32_767).contains(&l_tj) {
                return Err(format!(
                    "competitor logit {l_tj} outside signed i16 [-32768, 32767]"
                ));
            }
            let l_sh = l_tj + LOGIT_OFFSET_U16;
            let tie = if j < yh { 1i64 } else { 0i64 };
            let delta = (win_sh - l_sh) - tie;
            if !(0..(1i64 << m_tab)).contains(&delta) {
                return Err(format!(
                    "argmax dominance violated at pos t={t}, competitor j={j} vs y_hat={yh}: delta={delta} not in [0, 65536)"
                ));
            }
            let idx = t + (j << log_t);
            let l_bb = l_sh as u32;
            logit_lsb_tj[idx] = l_bb;
            gap_lsb_tj[idx] = delta as u32;
            logit_ext4_tj[idx] = Ext4::from_bb(l_bb);
            if j == yh {
                sel_ext4_tj[idx] = Ext4::ONE;
            }
        }
    }

    let logit_mult_tab = compute_d1b_multiplicities(&logit_lsb_tj, m_tab)?;
    let mult_tab = compute_d1b_multiplicities(&gap_lsb_tj, m_tab)?;

    let logit_state = commit_table_pcs(&logit_lsb_tj, PcsParams::default_zk(3), None);
    let logit_mult_state = commit_table_pcs(&logit_mult_tab, PcsParams::default_zk(1), None);
    let gap_state = commit_table_pcs(&gap_lsb_tj, PcsParams::default_zk(2), None);
    let mult_state = commit_table_pcs(&mult_tab, PcsParams::default_zk(1), None);

    let mut tr = CShakeTranscript::new(b"SPEC-ARGMAX-DOM-D1B-V2");
    tr.absorb_u32(b"log_t", log_t as u32);
    tr.absorb_u32(b"log_v", log_v as u32);
    for &yh in y_hat {
        tr.absorb_u32(b"y_hat", yh as u32);
    }
    for r in [
        &logit_state.root,
        &logit_mult_state.root,
        &gap_state.root,
        &mult_state.root,
    ] {
        tr.absorb_root(b"dom_root", r);
    }

    let z_t = tr.squeeze_ext4_vec(b"dom_zt", log_t, true);
    let z_j = tr.squeeze_ext4_vec(b"dom_zj", log_v, true);
    let mut z_tj = Vec::with_capacity(m_wit);
    z_tj.extend_from_slice(&z_t);
    z_tj.extend_from_slice(&z_j);

    let logit_at_z = mle_eval_bb_at_ext4(&logit_lsb_tj, &z_tj);
    let gap_at_z = mle_eval_bb_at_ext4(&gap_lsb_tj, &z_tj);
    tr.absorb_ext4(b"dom_logit_z", logit_at_z);
    tr.absorb_ext4(b"dom_gap_z", gap_at_z);

    let (win_sel_gruen, sel_chals) =
        prove_gruen_einsum_mode2_ext4(&sel_ext4_tj, &logit_ext4_tj, log_t, log_v, &z_t, &mut tr);

    let (logit_d1b_proof, z_d1b_logit) =
        prove_d1b_range_ext4(&logit_lsb_tj, &logit_mult_tab, m_wit, m_tab, &mut tr);
    let (gap_d1b_proof, z_d1b_gap) =
        prove_d1b_range_ext4(&gap_lsb_tj, &mult_tab, m_wit, m_tab, &mut tr);

    let logit_pcs_proof = open_pcs_claims(
        &logit_state,
        &[
            MleEvalClaim {
                point: z_tj.clone(),
                value: logit_at_z,
            },
            MleEvalClaim {
                point: sel_chals,
                value: win_sel_gruen.terminal_openings.1,
            },
            MleEvalClaim {
                point: z_d1b_logit.clone(),
                value: logit_d1b_proof.rem_leaf_eval,
            },
        ],
        &mut tr,
    );
    let logit_mult_pcs_proof = open_pcs_claims(
        &logit_mult_state,
        &[MleEvalClaim {
            point: z_d1b_logit[..m_tab].to_vec(),
            value: logit_d1b_proof.mult_leaf_eval,
        }],
        &mut tr,
    );
    let gap_pcs_proof = open_pcs_claims(
        &gap_state,
        &[
            MleEvalClaim {
                point: z_tj,
                value: gap_at_z,
            },
            MleEvalClaim {
                point: z_d1b_gap.clone(),
                value: gap_d1b_proof.rem_leaf_eval,
            },
        ],
        &mut tr,
    );
    let mult_pcs_proof = open_pcs_claims(
        &mult_state,
        &[MleEvalClaim {
            point: z_d1b_gap[..m_tab].to_vec(),
            value: gap_d1b_proof.mult_leaf_eval,
        }],
        &mut tr,
    );

    Ok(ArgmaxDominanceExt4Proof {
        log_t,
        log_v,
        logit_pcs_root: logit_state.root,
        logit_mult_pcs_root: logit_mult_state.root,
        gap_pcs_root: gap_state.root,
        mult_pcs_root: mult_state.root,
        logit_at_z,
        gap_at_z,
        win_sel_gruen,
        logit_d1b_proof,
        gap_d1b_proof,
        logit_pcs_proof,
        logit_mult_pcs_proof,
        gap_pcs_proof,
        mult_pcs_proof,
    })
}

/// Standalone verifier (`0` access to witness logits!) for `ArgmaxDominanceExt4Proof`.
/// Unconditionally sound over `ℤ`: `logit_d1b_proof` enforces `shifted_logit[t, j] in [0, 2^16)`,
/// guaranteeing `tieBrokenGap in [-65536, 65535] subset (-(P - 65536), P)` without external bounds!
pub fn verify_argmax_dominance_d1b_standalone(
    expected_logit_root: &[u8; 32],
    expected_log_t: usize,
    expected_log_v: usize,
    y_hat: &[usize],
    proof: &ArgmaxDominanceExt4Proof,
) -> Result<(), String> {
    if proof.log_t != expected_log_t || proof.log_v != expected_log_v {
        return Err("log_t/log_v statement mismatch in ArgmaxDominanceExt4Proof".to_string());
    }
    if proof.log_t == 0
        || proof.log_t > 16
        || proof.log_v == 0
        || proof.log_v > 20
        || proof.log_t + proof.log_v < 16
        || proof.log_t + proof.log_v > 24
    {
        return Err("out-of-range log_t/log_v in ArgmaxDominanceExt4Proof".to_string());
    }
    let seq_len = 1usize << proof.log_t;
    let vocab_size = 1usize << proof.log_v;
    let m_wit = proof.log_t + proof.log_v;
    let m_tab = 16usize;
    if y_hat.len() != seq_len || y_hat.iter().any(|&y| y >= vocab_size) {
        return Err("y_hat length or vocabulary bound mismatch".to_string());
    }
    if &proof.logit_pcs_root != expected_logit_root {
        return Err("logit_pcs_root mismatch".to_string());
    }
    if proof.win_sel_gruen.mu_s != proof.log_t || proof.win_sel_gruen.kappa != proof.log_v {
        return Err("win_sel_gruen mu_s/kappa mismatch with log_t/log_v".to_string());
    }
    if proof.logit_d1b_proof.m_wit != m_wit
        || proof.logit_d1b_proof.m_tab != m_tab
        || proof.gap_d1b_proof.m_wit != m_wit
        || proof.gap_d1b_proof.m_tab != m_tab
    {
        return Err("D1b dimension mismatch in ArgmaxDominanceExt4Proof".to_string());
    }

    let mut tr = CShakeTranscript::new(b"SPEC-ARGMAX-DOM-D1B-V2");
    tr.absorb_u32(b"log_t", proof.log_t as u32);
    tr.absorb_u32(b"log_v", proof.log_v as u32);
    for &yh in y_hat {
        tr.absorb_u32(b"y_hat", yh as u32);
    }
    for r in [
        &proof.logit_pcs_root,
        &proof.logit_mult_pcs_root,
        &proof.gap_pcs_root,
        &proof.mult_pcs_root,
    ] {
        tr.absorb_root(b"dom_root", r);
    }

    let z_t = tr.squeeze_ext4_vec(b"dom_zt", proof.log_t, true);
    let z_j = tr.squeeze_ext4_vec(b"dom_zj", proof.log_v, true);
    let mut z_tj = Vec::with_capacity(m_wit);
    z_tj.extend_from_slice(&z_t);
    z_tj.extend_from_slice(&z_j);

    tr.absorb_ext4(b"dom_logit_z", proof.logit_at_z);
    tr.absorb_ext4(b"dom_gap_z", proof.gap_at_z);

    let tie_at_z = eval_public_tie_indicator_mle(y_hat, &z_t, &z_j);
    let expected_win_claim = proof.gap_at_z.add(proof.logit_at_z).add(tie_at_z);

    let sel_chals =
        verify_gruen_einsum_mode2_ext4(expected_win_claim, &z_t, &proof.win_sel_gruen, &mut tr)?;
    let expected_sel_eval =
        eval_public_onehot_draft_mle(y_hat, &sel_chals[..proof.log_t], &sel_chals[proof.log_t..]);
    if proof.win_sel_gruen.terminal_openings.0 != expected_sel_eval {
        return Err("public one-hot draft selector evaluation mismatch".to_string());
    }

    let z_d1b_logit = verify_d1b_range_ext4(&proof.logit_d1b_proof, &mut tr)?;
    let z_d1b_gap = verify_d1b_range_ext4(&proof.gap_d1b_proof, &mut tr)?;

    verify_pcs_claims(
        expected_logit_root,
        PcsShape::new(m_wit, PcsParams::default_zk(3)),
        &[
            MleEvalClaim {
                point: z_tj.clone(),
                value: proof.logit_at_z,
            },
            MleEvalClaim {
                point: sel_chals,
                value: proof.win_sel_gruen.terminal_openings.1,
            },
            MleEvalClaim {
                point: z_d1b_logit.clone(),
                value: proof.logit_d1b_proof.rem_leaf_eval,
            },
        ],
        &proof.logit_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.logit_mult_pcs_root,
        PcsShape::new(m_tab, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_d1b_logit[..m_tab].to_vec(),
            value: proof.logit_d1b_proof.mult_leaf_eval,
        }],
        &proof.logit_mult_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.gap_pcs_root,
        PcsShape::new(m_wit, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_tj,
                value: proof.gap_at_z,
            },
            MleEvalClaim {
                point: z_d1b_gap.clone(),
                value: proof.gap_d1b_proof.rem_leaf_eval,
            },
        ],
        &proof.gap_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &proof.mult_pcs_root,
        PcsShape::new(m_tab, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_d1b_gap[..m_tab].to_vec(),
            value: proof.gap_d1b_proof.mult_leaf_eval,
        }],
        &proof.mult_pcs_proof,
        &mut tr,
    )?;
    Ok(())
}

/// Project real 24-layer `Qwen/Qwen3.5-0.8B-Base` final hidden states `final_h` (`[64, 1024]`) onto a
/// `V = 2,048`-entry vocabulary shortlist from tied `model.language_model.embed_tokens.weight` (`BF16`),
/// explicitly placing real `Qwen` BPE tokens `348` (`" *"`) and `23985` (`" ×"`) at slots `0` and `1`!
pub fn compute_real_qwen35_shortlist_logits(
    mmap: &MmapSafetensors,
    final_h: &[f32],
    seq_len: usize,
) -> Result<(Vec<u32>, Vec<i64>), String> {
    let d_model = 1024usize;
    let vocab_slice = 2048usize;
    assert_eq!(final_h.len(), seq_len * d_model);

    let (_, ln_f) = mmap.read_f32("model.language_model.norm.weight")?;
    if ln_f.len() != d_model {
        return Err(format!("norm.weight length {} != {d_model}", ln_f.len()));
    }
    let h_norm = crate::qwen35_layer::rmsnorm_zero_centered_f32(final_h, &ln_f, d_model, 1e-6);
    let h_q = crate::qwen35_layer::quantize_act_i16(&h_norm);

    let (emb_meta, emb_raw) = mmap.tensor_bytes("model.language_model.embed_tokens.weight")?;
    if emb_meta.dtype != "BF16" || emb_raw.len() < 248_320 * d_model * 2 {
        return Err(format!(
            "embed_tokens.weight expected BF16 >= {} bytes, got dtype={} len={}",
            248_320 * d_model * 2,
            emb_meta.dtype,
            emb_raw.len()
        ));
    }
    let mut vocab_ids = Vec::with_capacity(vocab_slice);
    vocab_ids.push(348u32);
    vocab_ids.push(23985u32);
    vocab_ids.push(13u32);
    let mut cand = 0u32;
    while vocab_ids.len() < vocab_slice {
        if cand != 348 && cand != 23985 && cand != 13 {
            vocab_ids.push(cand);
        }
        cand += 1;
    }

    let mut w_rows_i16 = vec![0i16; vocab_slice * d_model];
    for (slot, &tid) in vocab_ids.iter().enumerate() {
        let row_bytes = &emb_raw[(tid as usize) * d_model * 2..((tid as usize) + 1) * d_model * 2];
        for d in 0..d_model {
            let bits = u16::from_le_bytes([row_bytes[2 * d], row_bytes[2 * d + 1]]);
            let vf = f32::from_bits((bits as u32) << 16);
            w_rows_i16[slot * d_model + d] =
                (vf * 256.0).round().clamp(i16::MIN as f32, i16::MAX as f32) as i16;
        }
    }

    let mut logits_i64 = vec![0i64; seq_len * vocab_slice];
    logits_i64
        .par_chunks_mut(vocab_slice)
        .enumerate()
        .for_each(|(t, out_row)| {
            let hr = &h_q[t * d_model..(t + 1) * d_model];
            for slot in 0..vocab_slice {
                let wr = &w_rows_i16[slot * d_model..(slot + 1) * d_model];
                let mut acc = 0i64;
                for d in 0..d_model {
                    acc += (hr[d] as i64) * (wr[d] as i64);
                }
                let scaled = acc >> 8;
                assert!(
                    scaled.abs() < MAX_ABS_LOGIT_HEADROOM,
                    "shortlist logit overflowed BabyBear headroom"
                );
                out_row[slot] = scaled;
            }
        });

    Ok((vocab_ids, logits_i64))
}

// ===========================================================================
// §4. `3×` Depth-Looped MoE Weight-Opening Collapse (`Inkling-2-Mini` `R = 3` Shape)
// ===========================================================================

/// Unfolded `R = 3` loop-pass proof (`3` independent `MXFP4` sumchecks + `3` `(Q, S)` weight PCS openings!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopedMoeUnfoldedExt4Proof {
    pub pass_proofs: [Mxfp4BatchContractionProof; 3],
}

impl LoopedMoeUnfoldedExt4Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for p in &self.pass_proofs {
            p.write_to(&mut out);
        }
        out
    }
}

/// Collapsed `R = 3` `ρ`-folded proof (`loopedPass_eq_stackedEinsum`):
/// Commits `(X^{(0..2)}, Y^{(0..2)})` BEFORE drawing `ρ`, folds `(\sum_{r=0}^2 \rho^r X^{(r)}) W`,
/// and runs **1 single `MXFP4` sumcheck + 1 single `(Q, S)` weight PCS opening** (`3×` weight collapse)!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopedMoeCollapsedExt4Proof {
    pub log_t: usize,
    pub log_j: usize,
    pub log_k: usize,
    pub x_pcs_roots: [[u8; 32]; 3],
    pub y_pcs_roots: [[u8; 32]; 3],
    pub y_evals_at_r: [Ext4; 3],
    pub x_evals_at_term: [Ext4; 3],
    pub mxfp4_proof: Mxfp4DelayedBjkExt4Proof,
    pub q_pcs_proof: PcsOpeningProof,
    pub s_pcs_proof: PcsOpeningProof,
    pub x_pcs_proofs: [PcsOpeningProof; 3],
    pub y_pcs_proofs: [PcsOpeningProof; 3],
}

impl LoopedMoeCollapsedExt4Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.push(self.log_t as u8);
        out.push(self.log_j as u8);
        out.push(self.log_k as u8);
        for r in &self.x_pcs_roots {
            out.extend_from_slice(r);
        }
        for r in &self.y_pcs_roots {
            out.extend_from_slice(r);
        }
        for e in &self.y_evals_at_r {
            out.extend_from_slice(&e.to_bytes());
        }
        for e in &self.x_evals_at_term {
            out.extend_from_slice(&e.to_bytes());
        }
        self.mxfp4_proof.write_to(&mut out);
        self.q_pcs_proof.write_to(&mut out);
        self.s_pcs_proof.write_to(&mut out);
        for xp in &self.x_pcs_proofs {
            xp.write_to(&mut out);
        }
        for yp in &self.y_pcs_proofs {
            yp.write_to(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let log_t = cur.read_u8()? as usize;
        let log_j = cur.read_u8()? as usize;
        let log_k = cur.read_u8()? as usize;
        if log_t > 16
            || log_j == 0
            || log_j > 20
            || log_k == 0
            || log_k > 16
            || 5 + log_j + log_k > 26
        {
            return Err("invalid LoopedMoeCollapsedExt4Proof dimensions".to_string());
        }
        let x_pcs_roots = [cur.read_arr32()?, cur.read_arr32()?, cur.read_arr32()?];
        let y_pcs_roots = [cur.read_arr32()?, cur.read_arr32()?, cur.read_arr32()?];
        let y_evals_at_r = [cur.read_ext4()?, cur.read_ext4()?, cur.read_ext4()?];
        let x_evals_at_term = [cur.read_ext4()?, cur.read_ext4()?, cur.read_ext4()?];
        let mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
        if mxfp4_proof.log_j != log_j || mxfp4_proof.log_k != log_k {
            return Err(
                "inner MXFP4 log_j/log_k mismatch in LoopedMoeCollapsedExt4Proof".to_string(),
            );
        }
        let q_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let s_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let x_pcs_proofs = [
            PcsOpeningProof::read_from(&mut cur)?,
            PcsOpeningProof::read_from(&mut cur)?,
            PcsOpeningProof::read_from(&mut cur)?,
        ];
        let y_pcs_proofs = [
            PcsOpeningProof::read_from(&mut cur)?,
            PcsOpeningProof::read_from(&mut cur)?,
            PcsOpeningProof::read_from(&mut cur)?,
        ];
        if cur.remaining() != 0 {
            return Err("trailing bytes in LoopedMoeCollapsedExt4Proof".to_string());
        }
        Ok(Self {
            log_t,
            log_j,
            log_k,
            x_pcs_roots,
            y_pcs_roots,
            y_evals_at_r,
            x_evals_at_term,
            mxfp4_proof,
            q_pcs_proof,
            s_pcs_proof,
            x_pcs_proofs,
            y_pcs_proofs,
        })
    }
}

/// Prove `R = 3` sequential loop passes (`Y^{(r)} = X^{(r)} W^T`) using **ONE** `MXFP4` 0-mul Horner
/// sumcheck and **ONE** `(Q, S)` `SuccinctExt4Pcs` opening! Returns `(proof, weight_proving_ms)`.
pub fn prove_looped_moe_collapsed_ext4(
    weights: &PrecommittedSliceWeights,
    x_passes: &[Vec<i16>; 3],
    y_passes: &[Vec<i64>; 3],
    seq_len: usize,
) -> (LoopedMoeCollapsedExt4Proof, f64) {
    assert!(seq_len.is_power_of_two());
    let log_t = seq_len.trailing_zeros() as usize;
    let log_j = weights.j_pad.trailing_zeros() as usize;
    let log_k = weights.k_pad.trailing_zeros() as usize;
    let in_orig = weights.in_dim_orig;
    let orig_blocks = in_orig / 32;

    let mut x_tabs = Vec::with_capacity(3);
    let mut y_tabs = Vec::with_capacity(3);
    for r in 0..3 {
        assert_eq!(x_passes[r].len(), seq_len * in_orig);
        assert_eq!(y_passes[r].len(), seq_len * weights.j_pad);
        let mut x_lsb = vec![0u32; seq_len * weights.k_pad * 32];
        for t in 0..seq_len {
            for k in 0..orig_blocks {
                for b in 0..32 {
                    let v = x_passes[r][t * in_orig + k * 32 + b] as i64;
                    x_lsb[t + (b << log_t) + (k << (log_t + 5))] = bb_from_i64(v);
                }
            }
        }
        let mut y_lsb = vec![0u32; seq_len * weights.j_pad];
        for t in 0..seq_len {
            for j in 0..weights.j_pad {
                y_lsb[t + (j << log_t)] = bb_from_i64(y_passes[r][t * weights.j_pad + j]);
            }
        }
        x_tabs.push(x_lsb);
        y_tabs.push(y_lsb);
    }

    // Commit ALL `X^{(0..2)}` and `Y^{(0..2)}` BEFORE drawing `ρ` (post-challenge forgery defense!)
    let x_states: Vec<PcsProverState> = (0..3)
        .map(|r| commit_table_pcs(&x_tabs[r], PcsParams::default_zk(1), None))
        .collect();
    let y_states: Vec<PcsProverState> = (0..3)
        .map(|r| commit_table_pcs(&y_tabs[r], PcsParams::default_zk(1), None))
        .collect();

    let mut tr = CShakeTranscript::new(b"INKLING2-LOOPED-MOE-COLLAPSE-V1");
    tr.absorb_u32(b"log_t", log_t as u32);
    tr.absorb_u32(b"log_j", log_j as u32);
    tr.absorb_u32(b"log_k", log_k as u32);
    tr.absorb_root(b"q_root", &weights.q_state.root);
    tr.absorb_root(b"s_root", &weights.s_state.root);
    for st in &x_states {
        tr.absorb_root(b"x_root", &st.root);
    }
    for st in &y_states {
        tr.absorb_root(b"y_root", &st.root);
    }

    // Squeeze `124`-bit loop-folding challenge `ρ` & outer challenges `(r_i, r_j)` AFTER root commitment!
    let rho = tr.squeeze_ext4(b"loop_rho", true);
    let rho2 = rho.sq();
    let rho_pows = [Ext4::ONE, rho, rho2];
    let r_i = tr.squeeze_ext4_vec(b"loop_ri", log_t, true);
    let r_j = tr.squeeze_ext4_vec(b"loop_rj", log_j, true);

    let mut pt_y = Vec::with_capacity(log_t + log_j);
    pt_y.extend_from_slice(&r_i);
    pt_y.extend_from_slice(&r_j);

    let y_evals_at_r = [
        mle_eval_bb_at_ext4(&y_tabs[0], &pt_y),
        mle_eval_bb_at_ext4(&y_tabs[1], &pt_y),
        mle_eval_bb_at_ext4(&y_tabs[2], &pt_y),
    ];
    for &yv in &y_evals_at_r {
        tr.absorb_ext4(b"loop_y_ev", yv);
    }

    let eq_ri = build_eq_table_lsb_ext4(&r_i);
    let mut x_fold = vec![Ext4::ZERO; weights.k_pad * 32];
    for r in 0..3 {
        let rp = rho_pows[r];
        let xt = &x_tabs[r];
        for k in 0..weights.k_pad {
            for b in 0..32 {
                let mut acc = Ext4::ZERO;
                let base = (b << log_t) + (k << (log_t + 5));
                for t in 0..seq_len {
                    acc = acc.add(eq_ri[t].scale_bb(xt[base + t]));
                }
                x_fold[k * 32 + b] = x_fold[k * 32 + b].add(rp.mul(acc));
            }
        }
    }

    // --- Weight-Proving Kernel (`1` Horner sumcheck + `1` `(Q, S)` PCS open instead of `3`!) ---
    let tw0 = Instant::now();
    let (mxfp4_proof, chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_fold,
        &weights.nibs_pad,
        &weights.scs_pad,
        log_j,
        log_k,
        &r_j,
        &mut tr,
    );
    let dt_horner = tw0.elapsed().as_secs_f64() * 1000.0;

    let mut pt_x = Vec::with_capacity(log_t + 5 + log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&chals.chals_b);
    pt_x.extend_from_slice(&chals.chals_k);

    let x_evals_at_term = [
        mle_eval_bb_at_ext4(&x_tabs[0], &pt_x),
        mle_eval_bb_at_ext4(&x_tabs[1], &pt_x),
        mle_eval_bb_at_ext4(&x_tabs[2], &pt_x),
    ];
    for &xv in &x_evals_at_term {
        tr.absorb_ext4(b"loop_x_ev", xv);
    }

    let tw1 = Instant::now();
    let mut pt_q = Vec::with_capacity(5 + log_j + log_k);
    pt_q.extend_from_slice(&chals.chals_b);
    pt_q.extend_from_slice(&chals.chals_j);
    pt_q.extend_from_slice(&chals.chals_k);

    let mut pt_s = Vec::with_capacity(log_j + log_k);
    pt_s.extend_from_slice(&chals.chals_j);
    pt_s.extend_from_slice(&chals.chals_k);

    let q_pcs_proof = open_pcs_claims(
        &weights.q_state,
        &[MleEvalClaim {
            point: pt_q,
            value: mxfp4_proof.finals.1,
        }],
        &mut tr,
    );
    let s_pcs_proof = open_pcs_claims(
        &weights.s_state,
        &[MleEvalClaim {
            point: pt_s,
            value: mxfp4_proof.finals.2,
        }],
        &mut tr,
    );
    let weight_proving_ms = dt_horner + tw1.elapsed().as_secs_f64() * 1000.0;

    let x_pcs_proofs = [
        open_pcs_claims(
            &x_states[0],
            &[MleEvalClaim {
                point: pt_x.clone(),
                value: x_evals_at_term[0],
            }],
            &mut tr,
        ),
        open_pcs_claims(
            &x_states[1],
            &[MleEvalClaim {
                point: pt_x.clone(),
                value: x_evals_at_term[1],
            }],
            &mut tr,
        ),
        open_pcs_claims(
            &x_states[2],
            &[MleEvalClaim {
                point: pt_x,
                value: x_evals_at_term[2],
            }],
            &mut tr,
        ),
    ];
    let y_pcs_proofs = [
        open_pcs_claims(
            &y_states[0],
            &[MleEvalClaim {
                point: pt_y.clone(),
                value: y_evals_at_r[0],
            }],
            &mut tr,
        ),
        open_pcs_claims(
            &y_states[1],
            &[MleEvalClaim {
                point: pt_y.clone(),
                value: y_evals_at_r[1],
            }],
            &mut tr,
        ),
        open_pcs_claims(
            &y_states[2],
            &[MleEvalClaim {
                point: pt_y,
                value: y_evals_at_r[2],
            }],
            &mut tr,
        ),
    ];

    (
        LoopedMoeCollapsedExt4Proof {
            log_t,
            log_j,
            log_k,
            x_pcs_roots: [x_states[0].root, x_states[1].root, x_states[2].root],
            y_pcs_roots: [y_states[0].root, y_states[1].root, y_states[2].root],
            y_evals_at_r,
            x_evals_at_term,
            mxfp4_proof,
            q_pcs_proof,
            s_pcs_proof,
            x_pcs_proofs,
            y_pcs_proofs,
        },
        weight_proving_ms,
    )
}

/// Standalone `124`-bit `Ext4` verifier (`0` witness access!) for `LoopedMoeCollapsedExt4Proof`.
#[allow(clippy::too_many_arguments)]
pub fn verify_looped_moe_collapsed_standalone(
    expected_q_root: &[u8; 32],
    expected_s_root: &[u8; 32],
    expected_x_roots: &[[u8; 32]; 3],
    expected_y_roots: &[[u8; 32]; 3],
    expected_log_t: usize,
    expected_log_j: usize,
    expected_log_k: usize,
    proof: &LoopedMoeCollapsedExt4Proof,
) -> Result<(), String> {
    if proof.log_t != expected_log_t
        || proof.log_j != expected_log_j
        || proof.log_k != expected_log_k
    {
        return Err("looped MoE log_t/log_j/log_k statement mismatch".to_string());
    }
    if proof.log_t > 16
        || proof.log_j == 0
        || proof.log_j > 20
        || proof.log_k == 0
        || proof.log_k > 16
        || 5 + proof.log_j + proof.log_k > 26
        || proof.log_t + 5 + proof.log_k > 26
        || proof.log_t + proof.log_j > 26
    {
        return Err(
            "out-of-range dimensions in verify_looped_moe_collapsed_standalone".to_string(),
        );
    }
    if proof.mxfp4_proof.log_j != proof.log_j || proof.mxfp4_proof.log_k != proof.log_k {
        return Err("looped MoE inner MXFP4 dimension mismatch".to_string());
    }
    if &proof.x_pcs_roots != expected_x_roots || &proof.y_pcs_roots != expected_y_roots {
        return Err("looped MoE activation/output root mismatch".to_string());
    }
    let mut tr = CShakeTranscript::new(b"INKLING2-LOOPED-MOE-COLLAPSE-V1");
    tr.absorb_u32(b"log_t", proof.log_t as u32);
    tr.absorb_u32(b"log_j", proof.log_j as u32);
    tr.absorb_u32(b"log_k", proof.log_k as u32);
    tr.absorb_root(b"q_root", expected_q_root);
    tr.absorb_root(b"s_root", expected_s_root);
    for r in expected_x_roots {
        tr.absorb_root(b"x_root", r);
    }
    for r in expected_y_roots {
        tr.absorb_root(b"y_root", r);
    }

    let rho = tr.squeeze_ext4(b"loop_rho", true);
    let rho2 = rho.sq();
    let r_i = tr.squeeze_ext4_vec(b"loop_ri", proof.log_t, true);
    let r_j = tr.squeeze_ext4_vec(b"loop_rj", proof.log_j, true);

    for &yv in &proof.y_evals_at_r {
        tr.absorb_ext4(b"loop_y_ev", yv);
    }
    let expected_folded_y = proof.y_evals_at_r[0]
        .add(rho.mul(proof.y_evals_at_r[1]))
        .add(rho2.mul(proof.y_evals_at_r[2]));

    let chals =
        verify_mxfp4_delayed_bjk_horner_ext4(expected_folded_y, &r_j, &proof.mxfp4_proof, &mut tr)?;

    for &xv in &proof.x_evals_at_term {
        tr.absorb_ext4(b"loop_x_ev", xv);
    }
    let expected_folded_x = proof.x_evals_at_term[0]
        .add(rho.mul(proof.x_evals_at_term[1]))
        .add(rho2.mul(proof.x_evals_at_term[2]));
    if proof.mxfp4_proof.finals.0 != expected_folded_x {
        return Err("looped MoE terminal folded X evaluation mismatch".to_string());
    }

    let mut pt_q = Vec::with_capacity(5 + proof.log_j + proof.log_k);
    pt_q.extend_from_slice(&chals.chals_b);
    pt_q.extend_from_slice(&chals.chals_j);
    pt_q.extend_from_slice(&chals.chals_k);

    let mut pt_s = Vec::with_capacity(proof.log_j + proof.log_k);
    pt_s.extend_from_slice(&chals.chals_j);
    pt_s.extend_from_slice(&chals.chals_k);

    let mut pt_x = Vec::with_capacity(proof.log_t + 5 + proof.log_k);
    pt_x.extend_from_slice(&r_i);
    pt_x.extend_from_slice(&chals.chals_b);
    pt_x.extend_from_slice(&chals.chals_k);

    let mut pt_y = Vec::with_capacity(proof.log_t + proof.log_j);
    pt_y.extend_from_slice(&r_i);
    pt_y.extend_from_slice(&r_j);

    verify_pcs_claims(
        expected_q_root,
        PcsShape::new(5 + proof.log_j + proof.log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_q,
            value: proof.mxfp4_proof.finals.1,
        }],
        &proof.q_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        expected_s_root,
        PcsShape::new(proof.log_j + proof.log_k, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_s,
            value: proof.mxfp4_proof.finals.2,
        }],
        &proof.s_pcs_proof,
        &mut tr,
    )?;

    for ((x_root, &x_val), x_prf) in expected_x_roots
        .iter()
        .zip(proof.x_evals_at_term.iter())
        .zip(proof.x_pcs_proofs.iter())
    {
        verify_pcs_claims(
            x_root,
            PcsShape::new(proof.log_t + 5 + proof.log_k, PcsParams::default_zk(1)),
            &[MleEvalClaim {
                point: pt_x.clone(),
                value: x_val,
            }],
            x_prf,
            &mut tr,
        )?;
    }
    for ((y_root, &y_val), y_prf) in expected_y_roots
        .iter()
        .zip(proof.y_evals_at_r.iter())
        .zip(proof.y_pcs_proofs.iter())
    {
        verify_pcs_claims(
            y_root,
            PcsShape::new(proof.log_t + proof.log_j, PcsParams::default_zk(1)),
            &[MleEvalClaim {
                point: pt_y.clone(),
                value: y_val,
            }],
            y_prf,
            &mut tr,
        )?;
    }

    let _ = (
        cshake256_32,
        decode_e2m1_x2_bb,
        pad_mxfp4_cols_pow2,
        P,
        P_U32,
    );
    Ok(())
}

#[derive(Debug, Clone)]
pub struct LoopedMoeBenchSummary {
    pub shape_desc: String,
    pub unfolded_weight_prove_ms: f64,
    pub collapsed_weight_prove_ms: f64,
    pub weight_prove_speedup_x: f64,
    pub unfolded_total_prove_ms: f64,
    pub collapsed_total_prove_ms: f64,
    pub total_prove_speedup_x: f64,
    pub unfolded_verify_ms: f64,
    pub collapsed_verify_ms: f64,
    pub verify_speedup_x: f64,
    pub unfolded_proof_kib: f64,
    pub collapsed_proof_kib: f64,
}

/// Benchmark `Inkling-2-Mini` (`R = 3` depth-looped MoE expert `[1152->2048, 2304->4096]`, `8.39M` E2M1 cells):
/// Unfolded `3 × (Horner + (Q, S) PCS open)` vs `ρ`-Folded `1 × (Horner + (Q, S) PCS open)`!
pub fn benchmark_inkling2_looped_moe_r3() -> Result<LoopedMoeBenchSummary, String> {
    let rows_orig = 1152usize;
    let rows_pad = 2048usize; // `log_j = 11`
    let cols_orig = 2304usize;
    let blocks_per_row = cols_orig / 32; // 72 -> `k_pad = 128` (`log_k = 7`, `2^23 = 8,388,608` E2M1 cells!)
    let seq_len = 64usize;

    let mut nibbles = vec![0u8; rows_pad * cols_orig];
    let mut scales = vec![0u32; rows_pad * blocks_per_row];
    for r in 0..rows_orig {
        for blk in 0..blocks_per_row {
            scales[r * blocks_per_row + blk] = 1 << ((r + blk) % 4);
            let base = (r * blocks_per_row + blk) * 32;
            for b in 0..32 {
                let raw_nib = ((r * 13 + blk * 7 + b * 3 + 1) & 0xF) as u8;
                nibbles[base + b] = if raw_nib == 8 { 0 } else { raw_nib };
            }
        }
    }
    let name = "Inkling-2-Mini/loop_core.moe.expert_gate_proj[1152x2304]";
    let digest =
        Mxfp4Matrix::compute_digest(name, rows_orig, rows_pad, cols_orig, &nibbles, &scales);
    let mat = Mxfp4Matrix {
        name: name.to_string(),
        rows_orig,
        rows_pad,
        cols_orig,
        blocks_per_row,
        nibbles,
        scales,
        digest,
    };
    let weights = PrecommittedSliceWeights::build(&mat);

    let x_passes: [Vec<i16>; 3] = [0usize, 1, 2].map(|r| {
        (0..(seq_len * cols_orig))
            .map(|i| (((i * (11 + 4 * r) + 19 * r + 5) % 65) as i16) - 32)
            .collect()
    });
    let y_passes: [Vec<i64>; 3] = [
        eval_mxfp4_int_contraction(&x_passes[0], seq_len, cols_orig, &mat),
        eval_mxfp4_int_contraction(&x_passes[1], seq_len, cols_orig, &mat),
        eval_mxfp4_int_contraction(&x_passes[2], seq_len, cols_orig, &mat),
    ];

    let mut unfolded_weight_prove_ms = 0.0f64;
    let tu0 = Instant::now();
    let mut pass_proofs_vec = Vec::with_capacity(3);
    for r in 0..3usize {
        let pf = prove_mxfp4_batch_contraction_ext4(
            &weights,
            &x_passes[r],
            &y_passes[r],
            seq_len,
            (100 + r) as u32,
        );
        pass_proofs_vec.push(pf);
    }
    let unfolded_total_prove_ms = tu0.elapsed().as_secs_f64() * 1000.0;

    // Symmetric 1-to-1 isolated `3 ×` weight-side (`Horner + Q/S open`) measurement:
    {
        let mut tr_w = CShakeTranscript::new(b"INKLING2-WT-ISOLATE");
        let r_j = tr_w.squeeze_ext4_vec(b"rj", 11, true);
        let x_ri = tr_w.squeeze_ext4_vec(b"xri", 128 * 32, true);
        let tw_u0 = Instant::now();
        for _ in 0..3 {
            let (mpf, chs) = prove_mxfp4_delayed_bjk_horner_ext4(
                &x_ri,
                &weights.nibs_pad,
                &weights.scs_pad,
                11,
                7,
                &r_j,
                &mut tr_w,
            );
            let mut pt_q = Vec::with_capacity(23);
            pt_q.extend_from_slice(&chs.chals_b);
            pt_q.extend_from_slice(&chs.chals_j);
            pt_q.extend_from_slice(&chs.chals_k);
            let mut pt_s = Vec::with_capacity(18);
            pt_s.extend_from_slice(&chs.chals_j);
            pt_s.extend_from_slice(&chs.chals_k);
            let _ = open_pcs_claims(
                &weights.q_state,
                &[MleEvalClaim {
                    point: pt_q,
                    value: mpf.finals.1,
                }],
                &mut tr_w,
            );
            let _ = open_pcs_claims(
                &weights.s_state,
                &[MleEvalClaim {
                    point: pt_s,
                    value: mpf.finals.2,
                }],
                &mut tr_w,
            );
        }
        unfolded_weight_prove_ms += tw_u0.elapsed().as_secs_f64() * 1000.0;
    }

    let unfolded_pf = LoopedMoeUnfoldedExt4Proof {
        pass_proofs: pass_proofs_vec.try_into().unwrap(),
    };
    let unfolded_proof_kib = (unfolded_pf.to_bytes().len() as f64) / 1024.0;

    let tvu0 = Instant::now();
    for r in 0..3usize {
        let pfr = &unfolded_pf.pass_proofs[r];
        verify_mxfp4_batch_contraction_standalone(
            &weights.q_state.root,
            &weights.s_state.root,
            &pfr.x_pcs_root,
            &pfr.y_pcs_root,
            6,
            11,
            7,
            (100 + r) as u32,
            pfr,
        )?;
    }
    let unfolded_verify_ms = tvu0.elapsed().as_secs_f64() * 1000.0;

    let tc0 = Instant::now();
    let (collapsed_pf, collapsed_weight_prove_ms) =
        prove_looped_moe_collapsed_ext4(&weights, &x_passes, &y_passes, seq_len);
    let collapsed_total_prove_ms = tc0.elapsed().as_secs_f64() * 1000.0;
    let collapsed_bytes = collapsed_pf.to_bytes();
    let collapsed_proof_kib = (collapsed_bytes.len() as f64) / 1024.0;

    let tvc0 = Instant::now();
    let decoded_col = LoopedMoeCollapsedExt4Proof::from_bytes(&collapsed_bytes)?;
    let x_roots = decoded_col.x_pcs_roots;
    let y_roots = decoded_col.y_pcs_roots;
    verify_looped_moe_collapsed_standalone(
        &weights.q_state.root,
        &weights.s_state.root,
        &x_roots,
        &y_roots,
        6,
        11,
        7,
        &decoded_col,
    )?;
    let collapsed_verify_ms = tvc0.elapsed().as_secs_f64() * 1000.0;

    Ok(LoopedMoeBenchSummary {
        shape_desc: "Inkling-2-Mini R=3 [1152->2048, 2304->4096] (2^23 E2M1)".to_string(),
        unfolded_weight_prove_ms,
        collapsed_weight_prove_ms,
        weight_prove_speedup_x: unfolded_weight_prove_ms / collapsed_weight_prove_ms,
        unfolded_total_prove_ms,
        collapsed_total_prove_ms,
        total_prove_speedup_x: unfolded_total_prove_ms / collapsed_total_prove_ms,
        unfolded_verify_ms,
        collapsed_verify_ms,
        verify_speedup_x: unfolded_verify_ms / collapsed_verify_ms,
        unfolded_proof_kib,
        collapsed_proof_kib,
    })
}
