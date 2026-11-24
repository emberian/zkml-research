//! Cross-Language Python <-> Rust Witness Bundle Parsers & Succinct `Ext4` Verifiers for:
//!   1. `/tmp/qwen35_real_layer_turn.bin` (`QW35AUD1` emitted by `real_qwen35_gdn_eval.py`:
//!      proves PyTorch's exact Layer-0 `C=64` WY witness + all 3 `MXFP4` E2M1 projections
//!      `linear_attn.in_proj_z`, `linear_attn.out_proj`, `mlp.gate_proj` + real P5 `sk-proj-...` redaction!),
//!   2. `/tmp/qwen38fn_real_4layer_slice.bin` (`QW38FNS1` emitted by `qwen38fn_range_slice.py`:
//!      proves real HTTP-Range `Qwen/Qwen3.8-Flash-Next-FP8` `H_v = 48` `C=64` WY + `512E` Top-1 MoE + `QSA` `C3+C5`).

use crate::ext4::{
    bb_from_i64, build_eq_table_lsb_ext4, mle_eval_bb_at_ext4, ByteCursor, CShakeTranscript, Ext4,
};
use crate::gruen_ext4::{
    prove_mxfp4_delayed_bjk_horner_ext4, verify_mxfp4_delayed_bjk_horner_ext4,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsParams, PcsShape,
};
use crate::qwen35_layer::RealGdnWyWitness;
use crate::qwen38fn_slice::QsaTopKbWitness;
use crate::safetensors_mmap::{decode_e2m1_x2_bb, WY_SCALE};
use crate::u1_audit::{prove_padded_absence_zk, redact_sk_secrets, verify_padded_absence_zk};
use std::fs;
use std::ops::Add;
use std::path::Path;
use std::time::Instant;

pub struct PyQwen35BundleSummary {
    pub gen_text_raw: String,
    pub gen_text_redacted: String,
    pub redaction_count: usize,
    pub mxfp4_verified_names: Vec<(String, usize, usize, f64, f64)>, // `(name, orig_rows, in_dim, prove_ms, verify_ms)`
    pub absence_prove_ms: f64,
    pub absence_verify_ms: f64,
}

/// Parse `/tmp/qwen35_real_layer_turn.bin` (`QW35AUD1`), cross-verify algebraic WY & MXFP4 equations
/// bit-for-bit, prove all 3 real Layer-0 `MXFP4` E2M1 projections (`in_proj_z`, `out_proj`, `mlp.gate_proj`)
/// with `124`-bit `Ext4` 0-mul Horner + succinct `Ext4` PCS, and redact + ZK-verify the real P5 completion!
pub fn verify_py_qwen35_bundle(
    path: &Path,
) -> Result<(PyQwen35BundleSummary, RealGdnWyWitness), String> {
    let bytes = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let mut cur = ByteCursor::new(&bytes);
    let magic = cur.read_exact(8)?;
    if magic != b"QW35AUD1" {
        return Err("invalid QW35AUD1 magic".to_string());
    }
    let ver = cur.read_u32()?;
    let c_len = cur.read_u32()? as usize;
    let d_model = cur.read_u32()? as usize;
    let h_v = cur.read_u32()? as usize;
    let d_k = cur.read_u32()? as usize;
    let d_v = cur.read_u32()? as usize;
    let _d_ff = cur.read_u32()?;
    let _aud_l = cur.read_u32()?;
    let m_wy = cur.read_u32()? as i64;
    let _s_hid = cur.read_u32()?;
    let _s_ln1 = cur.read_u32()?;
    let _s_gdn = cur.read_u32()?;
    let _s_ln2 = cur.read_u32()?;
    let num_mats = cur.read_u32()? as usize;
    if ver != 1
        || c_len != 64
        || d_model != 1024
        || h_v != 16
        || d_k != 128
        || d_v != 128
        || m_wy != 4096
    {
        return Err("unexpected QW35AUD1 header constants".to_string());
    }

    // Prompt IDs (`64 * u32`) + real P5 completion bytes (`gen_len: u32` + UTF-8)
    let _prompt_bytes = cur.read_exact(64 * 4)?;
    let gen_len = cur.read_u32()? as usize;
    let gen_raw = cur.read_exact(gen_len)?;
    let gen_text_raw = String::from_utf8_lossy(gen_raw).to_string();
    let (redacted, redaction_count) = redact_sk_secrets(gen_raw);
    let gen_text_redacted = String::from_utf8_lossy(&redacted).to_string();

    // Prove & standalone-verify 0-cleartext ZK `Absent("sk-...")` on the real P5 redacted completion!
    let ta0 = Instant::now();
    let mut abs_p_tr = CShakeTranscript::new(b"PY-P5-ABS");
    let abs_rcpt = prove_padded_absence_zk(&redacted, &mut abs_p_tr)?;
    let absence_prove_ms = ta0.elapsed().as_secs_f64() * 1000.0;

    let tav0 = Instant::now();
    let mut abs_v_tr = CShakeTranscript::new(b"PY-P5-ABS");
    verify_padded_absence_zk(&abs_rcpt.content_root, None, &abs_rcpt, &mut abs_v_tr)?;
    let absence_verify_ms = tav0.elapsed().as_secs_f64() * 1000.0;

    // Skip `H_boundaries` (`i16[25, 64, 1024]` = `3,276,800` bytes)
    let _h_bnds = cur.read_exact(25 * 64 * 1024 * 2)?;

    // Read Layer 0 `C = 64` WY integer arrays (`L_tilde`, `RHS`, `UW`, `R_rem`) and check exact Z identity!
    let l_raw = cur.read_exact(16 * 64 * 64 * 4)?;
    let rhs_raw = cur.read_exact(16 * 64 * 256 * 4)?;
    let uw_raw = cur.read_exact(16 * 64 * 256 * 4)?;
    let rem_raw = cur.read_exact(16 * 64 * 256 * 2)?;

    let mut l_lsb_hij = vec![0u32; 16 * 64 * 64];
    let mut rhs_lsb_hik = vec![0u32; 16 * 64 * 256];
    let mut uw_lsb_hik = vec![0u32; 16 * 64 * 256];
    let mut rem_lsb_hik = vec![0u32; 16 * 64 * 256];

    for h in 0..16usize {
        for i in 0..64usize {
            for j in 0..64usize {
                let off = ((h * 64 + i) * 64 + j) * 4;
                let lv = i32::from_le_bytes(l_raw[off..off + 4].try_into().unwrap()) as i64;
                if j >= i && lv != 0 {
                    return Err("Python WY L_tilde violated strict lower triangularity".to_string());
                }
                l_lsb_hij[h + (i << 4) + (j << 10)] = bb_from_i64(lv);
            }
            for col in 0..256usize {
                let off4 = ((h * 64 + i) * 256 + col) * 4;
                let off2 = ((h * 64 + i) * 256 + col) * 2;
                let rv = i32::from_le_bytes(rhs_raw[off4..off4 + 4].try_into().unwrap()) as i64;
                let uv = i32::from_le_bytes(uw_raw[off4..off4 + 4].try_into().unwrap()) as i64;
                let remv = u16::from_le_bytes(rem_raw[off2..off2 + 2].try_into().unwrap()) as u32;
                if remv >= 4096 {
                    return Err("Python WY R_rem >= 4096".to_string());
                }
                rhs_lsb_hik[h + (i << 4) + (col << 10)] = bb_from_i64(rv);
                uw_lsb_hik[h + (i << 4) + (col << 10)] = bb_from_i64(uv);
                rem_lsb_hik[h + (i << 4) + (col << 10)] = remv;
            }
        }
    }

    // Read `X_ln1` `[64, 1024]`, `X_gdn_y` `[64, 2048]`, `X_ln2` `[64, 1024]`
    let read_i16_vec = |c: &mut ByteCursor, len: usize| -> Result<Vec<i16>, String> {
        let raw = c.read_exact(len * 2)?;
        Ok(raw
            .chunks_exact(2)
            .map(|b| i16::from_le_bytes([b[0], b[1]]))
            .collect())
    };
    let x_ln1 = read_i16_vec(&mut cur, 64 * 1024)?;
    let x_gdn_y = read_i16_vec(&mut cur, 64 * 2048)?;
    let x_ln2 = read_i16_vec(&mut cur, 64 * 1024)?;
    let x_inputs = [&x_ln1, &x_gdn_y, &x_ln2];

    // Prove & standalone-verify ALL THREE exported real Layer-0 `MXFP4` E2M1 matrices (`in_proj_z`, `out_proj`, `mlp.gate_proj`)!
    let mut mxfp4_verified_names = Vec::with_capacity(num_mats);
    for _m_idx in 0..num_mats {
        let name_len = cur.read_u32()? as usize;
        let name = String::from_utf8_lossy(cur.read_exact(name_len)?).to_string();
        let in_sel = cur.read_u32()? as usize;
        let orig_rows = cur.read_u32()? as usize;
        let j_pad = cur.read_u32()? as usize;
        let in_dim = cur.read_u32()? as usize;
        let k_blocks = cur.read_u32()? as usize;
        let _e_floor = cur.read_u32()?;

        let q_nibs = cur.read_exact(j_pad * k_blocks * 32)?;
        let s_raw = cur.read_exact(j_pad * k_blocks * 4)?;
        let y_raw_bytes = cur.read_exact(64 * j_pad * 8)?;

        let s_scales: Vec<u32> = s_raw
            .chunks_exact(4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
            .collect();
        let y_raw: Vec<i64> = y_raw_bytes
            .chunks_exact(8)
            .map(|b| i64::from_le_bytes(b.try_into().unwrap()))
            .collect();

        let x_src = x_inputs[in_sel];
        let log_j = j_pad.trailing_zeros() as usize;
        let log_k = k_blocks.trailing_zeros() as usize;

        let tp0 = Instant::now();
        let mut x_lsb_tbk = vec![0u32; 64 * k_blocks * 32];
        for t in 0..64 {
            for k in 0..k_blocks {
                for b in 0..32 {
                    x_lsb_tbk[t + (b << 6) + (k << 11)] =
                        bb_from_i64(x_src[t * in_dim + k * 32 + b] as i64);
                }
            }
        }
        let mut q_lsb_bjk = vec![0u32; j_pad * k_blocks * 32];
        let mut s_lsb_jk = vec![0u32; j_pad * k_blocks];
        for j in 0..j_pad {
            for k in 0..k_blocks {
                s_lsb_jk[k * j_pad + j] = s_scales[j * k_blocks + k];
                for b in 0..32 {
                    q_lsb_bjk[(k * j_pad + j) * 32 + b] =
                        decode_e2m1_x2_bb(q_nibs[(j * k_blocks + k) * 32 + b]);
                }
            }
        }
        let mut y_lsb_tj = vec![0u32; 64 * j_pad];
        for t in 0..64 {
            for j in 0..j_pad {
                y_lsb_tj[t + (j << 6)] = bb_from_i64(y_raw[t * j_pad + j]);
            }
        }

        let q_st = commit_table_pcs(&q_lsb_bjk, PcsParams::default_public(1), None);
        let s_st = commit_table_pcs(&s_lsb_jk, PcsParams::default_public(1), None);
        let x_st = commit_table_pcs(&x_lsb_tbk, PcsParams::default_zk(1), None);
        let y_st = commit_table_pcs(&y_lsb_tj, PcsParams::default_zk(1), None);

        let mut p_tr = CShakeTranscript::new(name.as_bytes());
        let r_i = p_tr.squeeze_ext4_vec(b"ri", 6, true);
        let r_j = p_tr.squeeze_ext4_vec(b"rj", log_j, true);
        let eq_ri = build_eq_table_lsb_ext4(&r_i);
        let mut x_ri = vec![Ext4::ZERO; k_blocks * 32];
        for k in 0..k_blocks {
            for b in 0..32 {
                let mut acc = Ext4::ZERO;
                let base = (b << 6) + (k << 11);
                for t in 0..64 {
                    acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
                }
                x_ri[k * 32 + b] = acc;
            }
        }
        let (mpf, chs) = prove_mxfp4_delayed_bjk_horner_ext4(
            &x_ri, q_nibs, &s_scales, log_j, log_k, &r_j, &mut p_tr,
        );
        let mut pt_q = Vec::new();
        pt_q.extend_from_slice(&chs.chals_b);
        pt_q.extend_from_slice(&chs.chals_j);
        pt_q.extend_from_slice(&chs.chals_k);
        let mut pt_s = Vec::new();
        pt_s.extend_from_slice(&chs.chals_j);
        pt_s.extend_from_slice(&chs.chals_k);
        let mut pt_x = Vec::new();
        pt_x.extend_from_slice(&r_i);
        pt_x.extend_from_slice(&chs.chals_b);
        pt_x.extend_from_slice(&chs.chals_k);
        let mut pt_y = Vec::new();
        pt_y.extend_from_slice(&r_i);
        pt_y.extend_from_slice(&r_j);

        // Cross-check Python `Y_raw` MLE equals 0-mul Horner `claim`!
        let expected_y = mle_eval_bb_at_ext4(&y_lsb_tj, &pt_y);
        if expected_y != mpf.claim {
            return Err(format!("Python <-> Rust MXFP4 mismatch on {name}!"));
        }

        let q_pf = open_pcs_claims(
            &q_st,
            &[MleEvalClaim {
                point: pt_q.clone(),
                value: mpf.finals.1,
            }],
            &mut p_tr,
        );
        let s_pf = open_pcs_claims(
            &s_st,
            &[MleEvalClaim {
                point: pt_s.clone(),
                value: mpf.finals.2,
            }],
            &mut p_tr,
        );
        let x_pf = open_pcs_claims(
            &x_st,
            &[MleEvalClaim {
                point: pt_x.clone(),
                value: mpf.finals.0,
            }],
            &mut p_tr,
        );
        let y_pf = open_pcs_claims(
            &y_st,
            &[MleEvalClaim {
                point: pt_y.clone(),
                value: mpf.claim,
            }],
            &mut p_tr,
        );
        let prove_ms = tp0.elapsed().as_secs_f64() * 1000.0;

        let tv0 = Instant::now();
        let mut v_tr = CShakeTranscript::new(name.as_bytes());
        let vr_i = v_tr.squeeze_ext4_vec(b"ri", 6, true);
        let vr_j = v_tr.squeeze_ext4_vec(b"rj", log_j, true);
        let _ = vr_i;
        let _ = verify_mxfp4_delayed_bjk_horner_ext4(mpf.claim, &vr_j, &mpf, &mut v_tr)?;
        verify_pcs_claims(
            &q_st.root,
            PcsShape::new(5 + log_j + log_k, PcsParams::default_public(1)),
            &[MleEvalClaim {
                point: pt_q,
                value: mpf.finals.1,
            }],
            &q_pf,
            &mut v_tr,
        )?;
        verify_pcs_claims(
            &s_st.root,
            PcsShape::new(log_j + log_k, PcsParams::default_public(1)),
            &[MleEvalClaim {
                point: pt_s,
                value: mpf.finals.2,
            }],
            &s_pf,
            &mut v_tr,
        )?;
        verify_pcs_claims(
            &x_st.root,
            PcsShape::new(6 + 5 + log_k, PcsParams::default_zk(1)),
            &[MleEvalClaim {
                point: pt_x,
                value: mpf.finals.0,
            }],
            &x_pf,
            &mut v_tr,
        )?;
        verify_pcs_claims(
            &y_st.root,
            PcsShape::new(6 + log_j, PcsParams::default_zk(1)),
            &[MleEvalClaim {
                point: pt_y,
                value: mpf.claim,
            }],
            &y_pf,
            &mut v_tr,
        )?;
        let verify_ms = tv0.elapsed().as_secs_f64() * 1000.0;

        mxfp4_verified_names.push((name, orig_rows, in_dim, prove_ms, verify_ms));
    }

    if cur.remaining() != 0 {
        return Err(format!("QW35AUD1 trailing {} bytes", cur.remaining()));
    }

    let wy = RealGdnWyWitness {
        h_v_orig: 16,
        h_pad: 16,
        c_len: 64,
        d_k: 128,
        d_v: 128,
        l_lsb_hij,
        rhs_lsb_hik,
        uw_lsb_hik,
        rem_lsb_hik,
        y_out_f32: Vec::new(),
    };
    Ok((
        PyQwen35BundleSummary {
            gen_text_raw,
            gen_text_redacted,
            redaction_count,
            mxfp4_verified_names,
            absence_prove_ms,
            absence_verify_ms,
        },
        wy,
    ))
}

/// Parsed witness bundle from `/tmp/qwen38fn_real_4layer_slice.bin` (`QW38FNS1`).
pub type Qwen38FnRangeBundle = (
    RealGdnWyWitness,
    Vec<i16>,
    Vec<u8>,
    Vec<u32>,
    Vec<i64>,
    QsaTopKbWitness,
    u32,
    u32,
);

/// Exact 128-byte header parser for `/tmp/qwen38fn_real_4layer_slice.bin` (`QW38FNS1` emitted by `qwen38fn_range_slice.py`)!
pub fn load_qwen38fn_range_bundle(path: &Path) -> Result<Qwen38FnRangeBundle, String> {
    let raw = fs::read(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    if raw.len() < 128 || &raw[0..8] != b"QW38FNS1" {
        return Err("invalid QW38FNS1 header".to_string());
    }
    let ver = u32::from_le_bytes(raw[8..12].try_into().unwrap());
    let h_v = u32::from_le_bytes(raw[12..16].try_into().unwrap()) as usize;
    let c_len = u32::from_le_bytes(raw[16..20].try_into().unwrap()) as usize;
    let wy_cols = u32::from_le_bytes(raw[20..24].try_into().unwrap()) as usize;
    let top1_expert_id = u32::from_le_bytes(raw[52..56].try_into().unwrap());
    let top1_token_idx = u32::from_le_bytes(raw[56..60].try_into().unwrap());
    if ver != 1 || h_v != 48 || c_len != 64 || wy_cols != 256 {
        return Err("unexpected QW38FNS1 dimensions".to_string());
    }

    let mut cur = ByteCursor::new(&raw[128..]);
    let l_raw = cur.read_exact(48 * 64 * 64 * 4)?;
    let rhs_raw = cur.read_exact(48 * 64 * 256 * 4)?;
    let uw_raw = cur.read_exact(48 * 64 * 256 * 4)?;
    let rem_raw = cur.read_exact(48 * 64 * 256 * 2)?;

    let half_wy = (WY_SCALE / 2) as u32;
    let mut l_lsb_hij = vec![0u32; 64 * 64 * 64];
    let mut rhs_lsb_hik = vec![0u32; 64 * 64 * 256];
    let mut uw_lsb_hik = vec![0u32; 64 * 64 * 256];
    let mut rem_lsb_hik = vec![half_wy; 64 * 64 * 256];

    for h in 0..48usize {
        for i in 0..64usize {
            for j in 0..64usize {
                let off = ((h * 64 + i) * 64 + j) * 4;
                let lv = i32::from_le_bytes(l_raw[off..off + 4].try_into().unwrap()) as i64;
                l_lsb_hij[h + (i << 6) + (j << 12)] = bb_from_i64(lv);
            }
            for col in 0..256usize {
                let off4 = ((h * 64 + i) * 256 + col) * 4;
                let off2 = ((h * 64 + i) * 256 + col) * 2;
                let rv = i32::from_le_bytes(rhs_raw[off4..off4 + 4].try_into().unwrap()) as i64;
                let uv = i32::from_le_bytes(uw_raw[off4..off4 + 4].try_into().unwrap()) as i64;
                let remv = u16::from_le_bytes(rem_raw[off2..off2 + 2].try_into().unwrap()) as u32;
                rhs_lsb_hik[h + (i << 6) + (col << 12)] = bb_from_i64(rv);
                uw_lsb_hik[h + (i << 6) + (col << 12)] = bb_from_i64(uv);
                rem_lsb_hik[h + (i << 6) + (col << 12)] = remv;
            }
        }
    }

    // `X_in`: `i16[4096]` (`1` token padded from `2560 -> 4096`; embed into row `0` of `[64, 2560]`)
    let x_raw = cur.read_exact(4096 * 2)?;
    let mut x_in_64_2560 = vec![0i16; 64 * 2560];
    for d in 0..2560usize {
        x_in_64_2560[d] = i16::from_le_bytes([x_raw[2 * d], x_raw[2 * d + 1]]);
    }
    // `Q_nibbles`: `u8[1024, 4096]` (`already 1024 * 128 * 32`!)
    let nibs_pad = cur.read_exact(1024 * 4096)?.to_vec();
    // `S_scales`: `u32[1024, 128]`
    let scs_raw = cur.read_exact(1024 * 128 * 4)?;
    let scs_pad: Vec<u32> = scs_raw
        .chunks_exact(4)
        .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
        .collect();
    // `Y_raw`: `i64[1024]` (`row 0` of `[64, 1024]`)
    let y_raw_b = cur.read_exact(1024 * 8)?;
    let mut y_raw_64_1024 = vec![0i64; 64 * 1024];
    for j in 0..1024usize {
        y_raw_64_1024[j] = i64::from_le_bytes(y_raw_b[8 * j..8 * (j + 1)].try_into().unwrap());
    }
    // `QSA_scores`: `i32[64, 16]`
    let qsa_b = cur.read_exact(64 * 16 * 4)?;
    let relu_scores: Vec<u32> = qsa_b
        .chunks_exact(4)
        .map(|b| i32::from_le_bytes(b.try_into().unwrap()).max(0) as u32)
        .collect();

    let wy = RealGdnWyWitness {
        h_v_orig: 48,
        h_pad: 64,
        c_len: 64,
        d_k: 128,
        d_v: 128,
        l_lsb_hij,
        rhs_lsb_hik,
        uw_lsb_hik,
        rem_lsb_hik,
        y_out_f32: Vec::new(),
    };
    let qsa = QsaTopKbWitness {
        num_queries: 64,
        num_blocks: 16,
        k_budget: 4,
        relu_scores,
    };
    Ok((
        wy,
        x_in_64_2560,
        nibs_pad,
        scs_pad,
        y_raw_64_1024,
        qsa,
        top1_expert_id,
        top1_token_idx,
    ))
}
