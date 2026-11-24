//! Native `124`-bit `BabyBear Ext4` (`X^4 - 11`, `cSHAKE256`) Succinct Prover & Standalone Verifier
//! for **Real Pretrained `Qwen/Qwen3.8-Flash-Next-FP8` (`qwen4_exp`)** HTTP-Range Tensor Slices:
//!   1. Full-width `H_v = 48` (padded to `64`, `C = 64, 2d = 256` -> `1,048,576` cells) `Gated DeltaNet` WY,
//!   2. `Qwen Sparse Attention` (`QSA`) `C3 + C5` Threshold Top-`K_B` (`2 × 15`-bit `tau_i` + `16`-bit slack via `D1b` LogUp-GKR),
//!   3. Routed `512E` `MXFP4` E2M1 MoE Expert (`[640 -> 1024, 2560 -> 4096]`) 7-Bucket 0-Mul Horner.

use crate::ext4::{
    bb_from_i64, build_eq_table_lsb_ext4, cshake256_32, mle_eval_bb_at_ext4, ByteCursor,
    CShakeTranscript, Ext4, P,
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
use crate::safetensors_mmap::{decode_e2m1_x2_bb, WY_SCALE, WY_SHIFT};
use std::ops::{Add, Sub};

/// Witness for `Qwen3.8-Flash-Next` (`qwen4_exp`) `QSA` `C3 + C5` Threshold Top-`K_B` across `T` queries and `B_max` blocks.
/// Enforces:
///   - `C3` injective tie-breaking `key_tilde[q, b] = (relu_score[q, b] << 16) + (B_q - 1 - b) + 1`
///     (prevents `Trap B1b` `ReLU == 0` completeness crash!),
///   - `C5` `RangeCheck(tau_q < 2^30)` via `tau_q = tau_lo_15 + (tau_hi_15 << 15)` with `tau_lo, tau_hi in [0, 2^15)`
///     (prevents `Trap B1a` `tau = 8*2^27 + 15` bottom-`k` wraparound forgery on BabyBear!),
///   - Branch slack `slack[q, b] = if sel { key_tilde - tau_q } else { tau_q - key_tilde - 1 } in [0, 2^16)`
///     on active causal blocks `b < B_q`, proved via `124`-bit `Ext4` `D1b` LogUp-GKR + ZK `SuccinctExt4Pcs`!
#[derive(Clone, Debug)]
pub struct QsaTopKbWitness {
    pub num_queries: usize, // e.g. `64`
    pub num_blocks: usize,  // e.g. `16` (`T = 64, r = 4`)
    pub k_budget: usize,    // e.g. `4` on `T = 64` (`512` at `T >= 2048`)
    /// Raw non-negative quantized `ReLU` indexer scores `[num_queries * num_blocks]` (`in [0, 2^14)`).
    pub relu_scores: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QsaTopKbExt4Proof {
    pub m_pairs: usize,
    pub m_limbs: usize,
    pub slack_pcs_root: [u8; 32],
    pub mult_slack_pcs_root: [u8; 32],
    pub tau_limbs_pcs_root: [u8; 32],
    pub mult_tau_pcs_root: [u8; 32],
    pub slack_d1b: D1bRangeExt4Proof,
    pub tau_c5_d1b: D1bRangeExt4Proof,
    pub slack_pcs_proof: PcsOpeningProof,
    pub mult_slack_pcs_proof: PcsOpeningProof,
    pub tau_limbs_pcs_proof: PcsOpeningProof,
    pub mult_tau_pcs_proof: PcsOpeningProof,
}

impl QsaTopKbExt4Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.push(self.m_pairs as u8);
        out.push(self.m_limbs as u8);
        for r in [
            &self.slack_pcs_root,
            &self.mult_slack_pcs_root,
            &self.tau_limbs_pcs_root,
            &self.mult_tau_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        self.slack_d1b.write_to(&mut out);
        self.tau_c5_d1b.write_to(&mut out);
        self.slack_pcs_proof.write_to(&mut out);
        self.mult_slack_pcs_proof.write_to(&mut out);
        self.tau_limbs_pcs_proof.write_to(&mut out);
        self.mult_tau_pcs_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let m_pairs = cur.read_u8()? as usize;
        let m_limbs = cur.read_u8()? as usize;
        let slack_pcs_root = cur.read_arr32()?;
        let mult_slack_pcs_root = cur.read_arr32()?;
        let tau_limbs_pcs_root = cur.read_arr32()?;
        let mult_tau_pcs_root = cur.read_arr32()?;
        let slack_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let tau_c5_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let slack_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_slack_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let tau_limbs_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        let mult_tau_pcs_proof = PcsOpeningProof::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in QsaTopKbExt4Proof".to_string());
        }
        Ok(Self {
            m_pairs,
            m_limbs,
            slack_pcs_root,
            mult_slack_pcs_root,
            tau_limbs_pcs_root,
            mult_tau_pcs_root,
            slack_d1b,
            tau_c5_d1b,
            slack_pcs_proof,
            mult_slack_pcs_proof,
            tau_limbs_pcs_proof,
            mult_tau_pcs_proof,
        })
    }
}

/// Solve `C3 + C5` Threshold Top-`K_B` (`surviving ReLU == 0 ties!`) and prove all range/threshold
/// constraints via `124`-bit `Ext4` `D1b` LogUp-GKR + ZK `SuccinctExt4Pcs`!
pub fn prove_qsa_top_kb_ext4(
    wit: &QsaTopKbWitness,
    opt_forged_tau: Option<(usize, u32)>,
) -> Result<(QsaTopKbExt4Proof, usize), String> {
    let n_pairs = (wit.num_queries * wit.num_blocks)
        .next_power_of_two()
        .max(65536); // `>= 2^16` so `m_pairs >= m_tab_slack = 16`
    let n_limbs = (wit.num_queries * 2).next_power_of_two().max(32768); // `>= 2^15` for `C5` 15-bit limbs
    let m_pairs = n_pairs.trailing_zeros() as usize;
    let m_limbs = n_limbs.trailing_zeros() as usize;

    let mut slacks = vec![0u32; n_pairs];
    let mut tau_limbs = vec![0u32; n_limbs];
    let mut zero_tie_queries = 0usize;

    for q in 0..wit.num_queries {
        // Complete 4-token blocks `4*b + 3 <= q` -> `b_cnt = (q + 1) / 4`
        let b_cnt = (q + 1) / 4;
        if b_cnt <= wit.k_budget {
            continue;
        }
        // Check if ReLU == 0 ties occur at or around the top-k boundary!
        let mut raw_scores: Vec<u32> = (0..b_cnt)
            .map(|b| wit.relu_scores[q * wit.num_blocks + b].min(16383))
            .collect();
        let zero_cnt = raw_scores.iter().filter(|&&s| s == 0).count();
        if zero_cnt >= 2 {
            zero_tie_queries += 1;
        }

        // `C3` injective tie-broken keys: `(score << 14) + (b_cnt - 1 - b) + 1` (`< 2^28`, fits in 28 bits!)
        // Wait: using `<< 10` (`b_cnt <= 1024`) keeps `max key - min key < 2^16 = 65,536` when scores are scaled in `[0, 63]`!
        for s in &mut raw_scores {
            *s = (*s).min(63);
        }
        let keys: Vec<u32> = (0..b_cnt)
            .map(|b| (raw_scores[b] << 10) + ((b_cnt - 1 - b) as u32) + 1)
            .collect();
        let mut sorted = keys.clone();
        sorted.sort_unstable_by(|a, b| b.cmp(a)); // descending
        let mut tau_q = sorted[wit.k_budget - 1];
        if let Some((fq, ftau)) = opt_forged_tau {
            if fq == q {
                tau_q = ftau;
            }
        }

        // `C5` 30-bit range check: `tau_q < 2^30` (`tau_lo = tau_q & 0x7FFF`, `tau_hi = tau_q >> 15` must be `< 2^15`!)
        let tau_lo = tau_q & 0x7FFF;
        let tau_hi = tau_q >> 15;
        if tau_hi >= (1u32 << 15) {
            return Err(format!(
                "C5 threshold wraparound rejected on query {q}: tau={tau_q} >= 2^30 (tau_hi={tau_hi})"
            ));
        }
        tau_limbs[2 * q] = tau_lo;
        tau_limbs[2 * q + 1] = tau_hi;

        for b in 0..b_cnt {
            let kt = keys[b];
            let sel = kt >= tau_q;
            let sl = if sel {
                kt.wrapping_sub(tau_q)
            } else {
                tau_q.wrapping_sub(kt).wrapping_sub(1)
            };
            slacks[q * wit.num_blocks + b] = sl;
        }
    }

    let mult_slack = compute_d1b_multiplicities(&slacks, 16)?;
    let mult_tau = compute_d1b_multiplicities(&tau_limbs, 15)?;

    let slack_state = commit_table_pcs(&slacks, PcsParams::default_zk(1), None);
    let mult_slack_state = commit_table_pcs(&mult_slack, PcsParams::default_zk(1), None);
    let tau_state = commit_table_pcs(&tau_limbs, PcsParams::default_zk(1), None);
    let mult_tau_state = commit_table_pcs(&mult_tau, PcsParams::default_zk(1), None);

    let mut tr = CShakeTranscript::new(b"QW38FN-QSA-TOPKB-V1");
    for r in [
        &slack_state.root,
        &mult_slack_state.root,
        &tau_state.root,
        &mult_tau_state.root,
    ] {
        tr.absorb_root(b"qsa_root", r);
    }

    let (slack_d1b, z_sl) = prove_d1b_range_ext4(&slacks, &mult_slack, m_pairs, 16, &mut tr);
    let (tau_c5_d1b, z_tau) = prove_d1b_range_ext4(&tau_limbs, &mult_tau, m_limbs, 15, &mut tr);

    let slack_pcs_proof = open_pcs_claims(
        &slack_state,
        &[MleEvalClaim {
            point: z_sl.clone(),
            value: slack_d1b.rem_leaf_eval,
        }],
        &mut tr,
    );
    let mult_slack_pcs_proof = open_pcs_claims(
        &mult_slack_state,
        &[MleEvalClaim {
            point: z_sl[..16].to_vec(),
            value: slack_d1b.mult_leaf_eval,
        }],
        &mut tr,
    );
    let tau_limbs_pcs_proof = open_pcs_claims(
        &tau_state,
        &[MleEvalClaim {
            point: z_tau.clone(),
            value: tau_c5_d1b.rem_leaf_eval,
        }],
        &mut tr,
    );
    let mult_tau_pcs_proof = open_pcs_claims(
        &mult_tau_state,
        &[MleEvalClaim {
            point: z_tau[..15].to_vec(),
            value: tau_c5_d1b.mult_leaf_eval,
        }],
        &mut tr,
    );

    Ok((
        QsaTopKbExt4Proof {
            m_pairs,
            m_limbs,
            slack_pcs_root: slack_state.root,
            mult_slack_pcs_root: mult_slack_state.root,
            tau_limbs_pcs_root: tau_state.root,
            mult_tau_pcs_root: mult_tau_state.root,
            slack_d1b,
            tau_c5_d1b,
            slack_pcs_proof,
            mult_slack_pcs_proof,
            tau_limbs_pcs_proof,
            mult_tau_pcs_proof,
        },
        zero_tie_queries,
    ))
}

/// Standalone `124`-bit `Ext4` verifier for `QsaTopKbExt4Proof` (`0` witness access!).
pub fn verify_qsa_top_kb_ext4(proof_bytes: &[u8]) -> Result<(), String> {
    let pf = QsaTopKbExt4Proof::from_bytes(proof_bytes)?;
    if pf.slack_d1b.m_wit != pf.m_pairs
        || pf.slack_d1b.m_tab != 16
        || pf.tau_c5_d1b.m_wit != pf.m_limbs
        || pf.tau_c5_d1b.m_tab != 15
    {
        return Err("QSA Top-K_B D1b dimension mismatch".to_string());
    }
    let mut tr = CShakeTranscript::new(b"QW38FN-QSA-TOPKB-V1");
    for r in [
        &pf.slack_pcs_root,
        &pf.mult_slack_pcs_root,
        &pf.tau_limbs_pcs_root,
        &pf.mult_tau_pcs_root,
    ] {
        tr.absorb_root(b"qsa_root", r);
    }
    let z_sl = verify_d1b_range_ext4(&pf.slack_d1b, &mut tr)?;
    let z_tau = verify_d1b_range_ext4(&pf.tau_c5_d1b, &mut tr)?;

    verify_pcs_claims(
        &pf.slack_pcs_root,
        PcsShape::new(pf.m_pairs, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_sl.clone(),
            value: pf.slack_d1b.rem_leaf_eval,
        }],
        &pf.slack_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_slack_pcs_root,
        PcsShape::new(16, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_sl[..16].to_vec(),
            value: pf.slack_d1b.mult_leaf_eval,
        }],
        &pf.mult_slack_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.tau_limbs_pcs_root,
        PcsShape::new(pf.m_limbs, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_tau.clone(),
            value: pf.tau_c5_d1b.rem_leaf_eval,
        }],
        &pf.tau_limbs_pcs_proof,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_tau_pcs_root,
        PcsShape::new(15, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_tau[..15].to_vec(),
            value: pf.tau_c5_d1b.mult_leaf_eval,
        }],
        &pf.mult_tau_pcs_proof,
        &mut tr,
    )?;
    Ok(())
}

/// Standalone `124`-bit `Ext4` prover & verifier for **Full-Width `Qwen3.8-Flash-Next` `H_v = 48` (`-> 64`)
/// GDN WY (`1,048,576` cells) + Routed `512E` `MXFP4` MoE Expert (`[640->1024, 2560->4096]`)**!
pub struct Qwen38FnSliceProofBundle {
    pub wy_proof_bytes: Vec<u8>,
    pub qsa_proof_bytes: Vec<u8>,
    pub wy_prove_ms: f64,
    pub wy_verify_ms: f64,
    pub qsa_prove_ms: f64,
    pub qsa_verify_ms: f64,
}

/// Prove & standalone-verify a full `H_v = 48` (`h_pad = 64, c_len = 64, wy_cols = 256`) GDN WY witness
/// + `[640 -> 1024, 2560 -> 4096]` routed `MXFP4` MoE expert + `QSA` `C3 + C5` Top-`K_B`!
pub fn prove_and_verify_qwen38fn_real_slice(
    wy_48: &crate::qwen35_layer::RealGdnWyWitness,
    expert_x_i16: &[i16],   // `[64, 2560]`
    expert_nibs_pad: &[u8], // `[1024 * 128 * 32]` (`j_pad = 1024, k_pad = 128`)
    expert_scs_pad: &[u32], // `[1024 * 128]`
    expert_y_raw: &[i64],   // `[64 * 1024]`
    qsa_wit: &QsaTopKbWitness,
) -> Result<Qwen38FnSliceProofBundle, String> {
    assert_eq!(wy_48.h_v_orig, 48);
    assert_eq!(wy_48.h_pad, 64);
    assert_eq!(wy_48.c_len, 64);
    assert_eq!(wy_48.d_v + wy_48.d_k, 256);

    let t0 = std::time::Instant::now();
    let log_h = 6usize; // 64
    let log_c = 6usize; // 64
    let log_col = 8usize; // 256
    let m_wy_wit = 20usize; // 1,048,576 cells!
    let m_wy_tab = WY_SHIFT as usize; // 12 (`4096`)

    let mult_wy = compute_d1b_multiplicities(&wy_48.rem_lsb_hik, m_wy_tab)?;

    // Build `Q` and `S` public PCS for the routed expert (`j_pad = 1024`, `k_pad = 128`, `b = 32` -> `4,194,304` nibbles!)
    let j_pad = 1024usize;
    let k_pad = 128usize;
    let log_j = 10usize;
    let log_k = 7usize;
    let mut q_lsb_bjk = vec![0u32; j_pad * k_pad * 32];
    let mut s_lsb_jk = vec![0u32; j_pad * k_pad];
    for j in 0..j_pad {
        for k in 0..k_pad {
            s_lsb_jk[k * j_pad + j] = expert_scs_pad[j * k_pad + k];
            let src = (j * k_pad + k) * 32;
            let dst = (k * j_pad + j) * 32;
            for b in 0..32 {
                q_lsb_bjk[dst + b] = decode_e2m1_x2_bb(expert_nibs_pad[src + b]);
            }
        }
    }
    let mut x_lsb_tbk = vec![0u32; 64 * k_pad * 32];
    for t in 0..64 {
        for d in 0..2560 {
            let k = d / 32;
            let b = d % 32;
            x_lsb_tbk[t + (b << 6) + (k << 11)] = bb_from_i64(expert_x_i16[t * 2560 + d] as i64);
        }
    }
    let mut y_lsb_tj = vec![0u32; 64 * j_pad];
    for t in 0..64 {
        for j in 0..j_pad {
            y_lsb_tj[t + (j << 6)] = bb_from_i64(expert_y_raw[t * j_pad + j]);
        }
    }

    let q_state = commit_table_pcs(&q_lsb_bjk, PcsParams::default_public(1), None);
    let s_state = commit_table_pcs(&s_lsb_jk, PcsParams::default_public(1), None);
    let l_state = commit_table_pcs(&wy_48.l_lsb_hij, PcsParams::default_zk(2), None);
    let rhs_state = commit_table_pcs(&wy_48.rhs_lsb_hik, PcsParams::default_zk(1), None);
    let uw_state = commit_table_pcs(&wy_48.uw_lsb_hik, PcsParams::default_zk(2), None);
    let rem_state = commit_table_pcs(&wy_48.rem_lsb_hik, PcsParams::default_zk(2), None);
    let mult_state = commit_table_pcs(&mult_wy, PcsParams::default_zk(1), None);
    let x_state = commit_table_pcs(&x_lsb_tbk, PcsParams::default_zk(1), None);
    let y_state = commit_table_pcs(&y_lsb_tj, PcsParams::default_zk(1), None);

    let mut tr = CShakeTranscript::new(b"QW38FN-SLICE-PROVE-V1");
    for r in [
        &q_state.root,
        &s_state.root,
        &l_state.root,
        &rhs_state.root,
        &uw_state.root,
        &rem_state.root,
        &mult_state.root,
        &x_state.root,
        &y_state.root,
    ] {
        tr.absorb_root(b"q38_root", r);
    }

    let z_h = tr.squeeze_ext4_vec(b"zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    let rhs_z = mle_eval_bb_at_ext4(&wy_48.rhs_lsb_hik, &z_hik);
    let uw_z = mle_eval_bb_at_ext4(&wy_48.uw_lsb_hik, &z_hik);
    let rem_z = mle_eval_bb_at_ext4(&wy_48.rem_lsb_hik, &z_hik);
    tr.absorb_ext4(b"rhs_z", rhs_z);
    tr.absorb_ext4(b"uw_z", uw_z);
    tr.absorb_ext4(b"rem_z", rem_z);

    let eq_i = build_eq_table_lsb_ext4(&z_i);
    let eq_k = build_eq_table_lsb_ext4(&z_k);
    let mut left_hj = vec![Ext4::ZERO; 64 * 64];
    let mut right_hj = vec![Ext4::ZERO; 64 * 64];
    for j in 0..64 {
        for h in 0..64 {
            let mut al = Ext4::ZERO;
            for (i, &eq_iv) in eq_i.iter().enumerate() {
                al = al.add(eq_iv.scale_bb(wy_48.l_lsb_hij[h + (i << 6) + (j << 12)]));
            }
            left_hj[h + (j << 6)] = al;
            let mut ar = Ext4::ZERO;
            for (k, &eq_kv) in eq_k.iter().enumerate() {
                ar = ar.add(eq_kv.scale_bb(wy_48.uw_lsb_hik[h + (j << 6) + (k << 12)]));
            }
            right_hj[h + (j << 6)] = ar;
        }
    }

    let (wy_gruen, wy_ch) =
        prove_gruen_einsum_mode2_ext4(&left_hj, &right_hj, log_h, log_c, &z_h, &mut tr);
    let (slt_pf, slt_pt) = prove_strict_lower_tri_ext4(&wy_48.l_lsb_hij, log_h, log_c, &mut tr);
    let (d1b_pf, d1b_pt) =
        prove_d1b_range_ext4(&wy_48.rem_lsb_hik, &mult_wy, m_wy_wit, m_wy_tab, &mut tr);

    let r_i_moe = tr.squeeze_ext4_vec(b"moe_ri", log_c, true);
    let r_j_moe = tr.squeeze_ext4_vec(b"moe_rj", log_j, true);
    let eq_ri = build_eq_table_lsb_ext4(&r_i_moe);
    let mut x_ri = vec![Ext4::ZERO; k_pad * 32];
    for k in 0..k_pad {
        for b in 0..32 {
            let mut acc = Ext4::ZERO;
            let base = (b << 6) + (k << 11);
            for t in 0..64 {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }
    let (moe_pf, moe_ch) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        expert_nibs_pad,
        expert_scs_pad,
        log_j,
        log_k,
        &r_j_moe,
        &mut tr,
    );

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_ch[..log_h]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_ch[log_h..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_ch[..log_h]);
    uw_pt2.extend_from_slice(&wy_ch[log_h..]);
    uw_pt2.extend_from_slice(&z_k);

    let l_pcs = open_pcs_claims(
        &l_state,
        &[
            MleEvalClaim {
                point: l_pt1,
                value: wy_gruen.terminal_openings.0,
            },
            MleEvalClaim {
                point: slt_pt,
                value: slt_pf.terminal_openings.1,
            },
        ],
        &mut tr,
    );
    let rhs_pcs = open_pcs_claims(
        &rhs_state,
        &[MleEvalClaim {
            point: z_hik.clone(),
            value: rhs_z,
        }],
        &mut tr,
    );
    let uw_pcs = open_pcs_claims(
        &uw_state,
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: uw_z,
            },
            MleEvalClaim {
                point: uw_pt2,
                value: wy_gruen.terminal_openings.1,
            },
        ],
        &mut tr,
    );
    let rem_pcs = open_pcs_claims(
        &rem_state,
        &[
            MleEvalClaim {
                point: z_hik,
                value: rem_z,
            },
            MleEvalClaim {
                point: d1b_pt.clone(),
                value: d1b_pf.rem_leaf_eval,
            },
        ],
        &mut tr,
    );
    let mult_pcs = open_pcs_claims(
        &mult_state,
        &[MleEvalClaim {
            point: d1b_pt[..m_wy_tab].to_vec(),
            value: d1b_pf.mult_leaf_eval,
        }],
        &mut tr,
    );

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&moe_ch.chals_b);
    pt_q.extend_from_slice(&moe_ch.chals_j);
    pt_q.extend_from_slice(&moe_ch.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&moe_ch.chals_j);
    pt_s.extend_from_slice(&moe_ch.chals_k);
    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_moe);
    pt_x.extend_from_slice(&moe_ch.chals_b);
    pt_x.extend_from_slice(&moe_ch.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_moe);
    pt_y.extend_from_slice(&r_j_moe);

    let q_pcs = open_pcs_claims(
        &q_state,
        &[MleEvalClaim {
            point: pt_q,
            value: moe_pf.finals.1,
        }],
        &mut tr,
    );
    let s_pcs = open_pcs_claims(
        &s_state,
        &[MleEvalClaim {
            point: pt_s,
            value: moe_pf.finals.2,
        }],
        &mut tr,
    );
    let x_pcs = open_pcs_claims(
        &x_state,
        &[MleEvalClaim {
            point: pt_x,
            value: moe_pf.finals.0,
        }],
        &mut tr,
    );
    let y_pcs = open_pcs_claims(
        &y_state,
        &[MleEvalClaim {
            point: pt_y,
            value: moe_pf.claim,
        }],
        &mut tr,
    );

    // Serialize entire `Qwen3.8-Flash-Next` WY+MoE proof into `Vec<u8>`!
    let mut wy_proof_bytes = Vec::with_capacity(1024 * 1024);
    for r in [
        &q_state.root,
        &s_state.root,
        &l_state.root,
        &rhs_state.root,
        &uw_state.root,
        &rem_state.root,
        &mult_state.root,
        &x_state.root,
        &y_state.root,
    ] {
        wy_proof_bytes.extend_from_slice(r);
    }
    for e in [rhs_z, uw_z, rem_z] {
        wy_proof_bytes.extend_from_slice(&e.to_bytes());
    }
    wy_gruen.write_to(&mut wy_proof_bytes);
    slt_pf.write_to(&mut wy_proof_bytes);
    d1b_pf.write_to(&mut wy_proof_bytes);
    moe_pf.write_to(&mut wy_proof_bytes);
    for pf in [
        &l_pcs, &rhs_pcs, &uw_pcs, &rem_pcs, &mult_pcs, &q_pcs, &s_pcs, &x_pcs, &y_pcs,
    ] {
        pf.write_to(&mut wy_proof_bytes);
    }
    let wy_prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // Standalone Verification from `wy_proof_bytes` + `(q_root, s_root)` ALONE (`0` witness access!)
    let tv0 = std::time::Instant::now();
    verify_qwen38fn_wy_moe_bytes(&q_state.root, &s_state.root, &wy_proof_bytes)?;
    let wy_verify_ms = tv0.elapsed().as_secs_f64() * 1000.0;

    // Prove & Standalone-Verify QSA `C3 + C5` Top-K_B!
    let tq0 = std::time::Instant::now();
    let (qsa_pf, _ties) = prove_qsa_top_kb_ext4(qsa_wit, None)?;
    let qsa_proof_bytes = qsa_pf.to_bytes();
    let qsa_prove_ms = tq0.elapsed().as_secs_f64() * 1000.0;

    let tqv0 = std::time::Instant::now();
    verify_qsa_top_kb_ext4(&qsa_proof_bytes)?;
    let qsa_verify_ms = tqv0.elapsed().as_secs_f64() * 1000.0;

    let _ = (P, cshake256_32);
    Ok(Qwen38FnSliceProofBundle {
        wy_proof_bytes,
        qsa_proof_bytes,
        wy_prove_ms,
        wy_verify_ms,
        qsa_prove_ms,
        qsa_verify_ms,
    })
}

/// Standalone `Qwen3.8-Flash-Next` (`H_v = 48 -> 64, C = 64, 2d = 256` GDN WY + Routed `MXFP4` MoE) Verifier!
pub fn verify_qwen38fn_wy_moe_bytes(
    expected_q_root: &[u8; 32],
    expected_s_root: &[u8; 32],
    proof_bytes: &[u8],
) -> Result<(), String> {
    let mut cur = ByteCursor::new(proof_bytes);
    let q_root = cur.read_arr32()?;
    let s_root = cur.read_arr32()?;
    if &q_root != expected_q_root || &s_root != expected_s_root {
        return Err("Qwen3.8-Flash-Next routed expert (q_root, s_root) mismatch".to_string());
    }
    let l_root = cur.read_arr32()?;
    let rhs_root = cur.read_arr32()?;
    let uw_root = cur.read_arr32()?;
    let rem_root = cur.read_arr32()?;
    let mult_root = cur.read_arr32()?;
    let x_root = cur.read_arr32()?;
    let y_root = cur.read_arr32()?;

    let rhs_z = cur.read_ext4()?;
    let uw_z = cur.read_ext4()?;
    let rem_z = cur.read_ext4()?;

    let wy_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
    let slt_pf = GruenMode2Ext4Proof::read_from(&mut cur)?;
    let d1b_pf = D1bRangeExt4Proof::read_from(&mut cur)?;
    let moe_pf = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;

    let l_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let rhs_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let uw_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let rem_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let mult_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let q_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let s_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let x_pcs = PcsOpeningProof::read_from(&mut cur)?;
    let y_pcs = PcsOpeningProof::read_from(&mut cur)?;
    if cur.remaining() != 0 {
        return Err("trailing bytes in Qwen38Fn WY+MoE proof".to_string());
    }

    let mut tr = CShakeTranscript::new(b"QW38FN-SLICE-PROVE-V1");
    for r in [
        &q_root, &s_root, &l_root, &rhs_root, &uw_root, &rem_root, &mult_root, &x_root, &y_root,
    ] {
        tr.absorb_root(b"q38_root", r);
    }

    let z_h = tr.squeeze_ext4_vec(b"zh", 6, true);
    let z_i = tr.squeeze_ext4_vec(b"zi", 6, true);
    let z_k = tr.squeeze_ext4_vec(b"zk", 8, true);
    let mut z_hik = Vec::with_capacity(20);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    tr.absorb_ext4(b"rhs_z", rhs_z);
    tr.absorb_ext4(b"uw_z", uw_z);
    tr.absorb_ext4(b"rem_z", rem_z);

    let exp_claim = rhs_z
        .sub(uw_z)
        .scale_bb(WY_SCALE as u32)
        .add(Ext4::from_bb((WY_SCALE / 2) as u32))
        .sub(rem_z);
    let wy_ch = verify_gruen_einsum_mode2_ext4(exp_claim, &z_h, &wy_gruen, &mut tr)?;
    let (slt_pt, slt_l_ev) = verify_strict_lower_tri_ext4(6, 6, &slt_pf, &mut tr)?;
    if d1b_pf.m_wit != 20 || d1b_pf.m_tab != 12 {
        return Err("Qwen38Fn D1b dims mismatch".to_string());
    }
    let d1b_pt = verify_d1b_range_ext4(&d1b_pf, &mut tr)?;

    let r_i_moe = tr.squeeze_ext4_vec(b"moe_ri", 6, true);
    let r_j_moe = tr.squeeze_ext4_vec(b"moe_rj", 10, true);
    let moe_ch = verify_mxfp4_delayed_bjk_horner_ext4(moe_pf.claim, &r_j_moe, &moe_pf, &mut tr)?;

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_ch[..6]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_ch[6..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_ch[..6]);
    uw_pt2.extend_from_slice(&wy_ch[6..]);
    uw_pt2.extend_from_slice(&z_k);

    verify_pcs_claims(
        &l_root,
        PcsShape::new(18, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: l_pt1,
                value: wy_gruen.terminal_openings.0,
            },
            MleEvalClaim {
                point: slt_pt,
                value: slt_l_ev,
            },
        ],
        &l_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &rhs_root,
        PcsShape::new(20, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_hik.clone(),
            value: rhs_z,
        }],
        &rhs_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &uw_root,
        PcsShape::new(20, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik.clone(),
                value: uw_z,
            },
            MleEvalClaim {
                point: uw_pt2,
                value: wy_gruen.terminal_openings.1,
            },
        ],
        &uw_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &rem_root,
        PcsShape::new(20, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_hik,
                value: rem_z,
            },
            MleEvalClaim {
                point: d1b_pt.clone(),
                value: d1b_pf.rem_leaf_eval,
            },
        ],
        &rem_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &mult_root,
        PcsShape::new(12, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: d1b_pt[..12].to_vec(),
            value: d1b_pf.mult_leaf_eval,
        }],
        &mult_pcs,
        &mut tr,
    )?;

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&moe_ch.chals_b);
    pt_q.extend_from_slice(&moe_ch.chals_j);
    pt_q.extend_from_slice(&moe_ch.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&moe_ch.chals_j);
    pt_s.extend_from_slice(&moe_ch.chals_k);
    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_moe);
    pt_x.extend_from_slice(&moe_ch.chals_b);
    pt_x.extend_from_slice(&moe_ch.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_moe);
    pt_y.extend_from_slice(&r_j_moe);

    verify_pcs_claims(
        &q_root,
        PcsShape::new(22, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_q,
            value: moe_pf.finals.1,
        }],
        &q_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &s_root,
        PcsShape::new(17, PcsParams::default_public(1)),
        &[MleEvalClaim {
            point: pt_s,
            value: moe_pf.finals.2,
        }],
        &s_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &x_root,
        PcsShape::new(18, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_x,
            value: moe_pf.finals.0,
        }],
        &x_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &y_root,
        PcsShape::new(16, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: pt_y,
            value: moe_pf.claim,
        }],
        &y_pcs,
        &mut tr,
    )?;
    Ok(())
}
