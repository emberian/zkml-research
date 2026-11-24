//! End-to-End `U1` Commit-Then-Audit Protocol (`25` `cSHAKE256` ZK PCS Layer Boundaries + Fiat–Shamir
//! VRF Layer Selection) + Deterministic `sk-...` Secret Redaction Transducer + Content-Bound `cSHAKE256`
//! Zero-Knowledge Padded-Complement (`¬(Σ* · "sk-" · KeyChar · Σ*)`) `Absent` Verification (`CERTIFICATES.md` `L3` / `P4` / `P6`).

use crate::ext4::{
    build_eq_table_lsb_ext4, cshake256_32, mle_eval_bb_at_ext4, ByteCursor, CShakeTranscript, Ext4,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, compute_d1b_public_table_multiplicities,
    prove_d1b_public_table_ext4, prove_d1b_range_ext4, prove_gruen_einsum_mode2_ext4,
    verify_d1b_public_table_ext4, verify_d1b_range_ext4, verify_gruen_einsum_mode2_ext4,
    D1bRangeExt4Proof, GruenMode2Ext4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams,
    PcsProverState, PcsShape,
};
use crate::qwen35_layer::{
    prove_audited_gdn_layer, verify_audited_gdn_layer_standalone, AuditedGdnLayerVerifyStmt,
    AuditedGdnLayerWitness, PrecommittedMxfp4Pcs, Qwen35TurnExecution, SuccinctGdnLayerProof,
};
use crate::safetensors_mmap::Qwen35WeightRegistry;
use rayon::prelude::*;
use std::ops::{Add, Mul, Sub};

const U1_BUNDLE_MAGIC: &[u8; 8] = b"QW35U1P1";

// ===========================================================================
// §1. Deterministic `sk-...` Secret Redaction Transducer & Padded-Complement DFA (`L3` / `P4` / `P6`)
// ===========================================================================

#[inline]
pub fn is_sk_key_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'-'
}

/// Deterministic streaming secret-redaction transducer: replaces every `sk-[A-Za-z0-9_-]{4,}` API key
/// span in `raw_bytes` with `[REDACTED:SK_SECRET]`, returning `(redacted_bytes, redaction_count)`.
pub fn redact_sk_secrets(raw_bytes: &[u8]) -> (Vec<u8>, usize) {
    let mut out = Vec::with_capacity(raw_bytes.len());
    let mut count = 0usize;
    let mut i = 0usize;
    while i < raw_bytes.len() {
        if i + 7 <= raw_bytes.len()
            && &raw_bytes[i..i + 3] == b"sk-"
            && (0..4).all(|k| is_sk_key_char(raw_bytes[i + 3 + k]))
        {
            let prev_ok = i == 0 || !raw_bytes[i - 1].is_ascii_alphanumeric();
            if prev_ok {
                let mut end = i + 3;
                while end < raw_bytes.len() && is_sk_key_char(raw_bytes[end]) {
                    end += 1;
                }
                out.extend_from_slice(b"[REDACTED:SK_SECRET]");
                count += 1;
                i = end;
                continue;
            }
        }
        out.push(raw_bytes[i]);
        i += 1;
    }
    (out, count)
}

/// 5-state **Padded-Complement** byte DFA `M_absent` for `¬(Σ* · "sk-" · KeyChar · Σ*)` (`CERTIFICATES.md` `L3`/`P4`):
///   State `0`: idle (accepting)
///   State `1`: matched `'s'` (accepting)
///   State `2`: matched `"sk"` (accepting)
///   State `3`: matched `"sk-"` (accepting unless followed by `KeyChar`)
///   State `4`: **INESCAPABLE SINK** (`q_sink` — entered once `"sk-" · KeyChar` occurs anywhere in `w`; non-accepting!).
#[inline]
pub fn padded_complement_sk_step(state: u8, byte: u8) -> u8 {
    match state {
        0 => {
            if byte == b's' {
                1
            } else {
                0
            }
        }
        1 => {
            if byte == b'k' {
                2
            } else if byte == b's' {
                1
            } else {
                0
            }
        }
        2 => {
            if byte == b'-' {
                3
            } else if byte == b's' {
                1
            } else {
                0
            }
        }
        3 => {
            if is_sk_key_char(byte) {
                4
            } else {
                0
            }
        }
        _ => 4,
    }
}

/// Build the canonical `2,048`-entry (`5 * 256 = 1,280` valid accepting-prefix transitions, padded to `2^11 = 2,048`)
/// public DFA transition lookup table `tuple = q + 8 * byte + 2048 * delta(q, byte)`!
/// Crucially, we ONLY include `q in 0..4` WITH `delta(q, byte) in 0..4` (`excluding transitions into sink 4`!)
/// plus an idle padding symbol `byte = 256` (`q + 8*256 + 2048*q` for `q in 0..4`) for tail positions `t >= word_len`!
/// Because `q in [0, 8)` and `b in [0, 512)` (`range-checked via D1b`!), `(q, b, q_next) -> q + 8*b + 2048*q_next`
/// is **100% injective over Z and BabyBear**, AND **no transition entering sink state 4 exists in the table**!!
pub fn build_accepting_sk_dfa_public_table() -> Vec<u32> {
    let mut entries = Vec::with_capacity(2048);
    for q in 0..4u8 {
        for b in 0..=255u8 {
            let q_next = padded_complement_sk_step(q, b);
            if q_next < 4 {
                let tuple = (q as u32) + 8 * (b as u32) + 2048 * (q_next as u32);
                entries.push(tuple);
            }
        }
        // Tail padding transition `b = 256`: `q_next == q` for `t >= word_len`
        let pad_tuple = (q as u32) + 8 * 256 + 2048 * (q as u32);
        entries.push(pad_tuple);
    }
    let filler = entries[0]; // `0 + 8*0 + 2048*0 = 0`
    while entries.len() < 2048 {
        entries.push(filler);
    }
    entries
}

pub fn run_padded_complement_sk_dfa(w: &[u8]) -> (u8, Vec<u8>) {
    let mut trace = Vec::with_capacity(w.len() + 1);
    let mut q = 0u8;
    trace.push(q);
    for &b in w {
        q = padded_complement_sk_step(q, b);
        trace.push(q);
    }
    (q, trace)
}

/// Broken whole-word complement (`w != "sk-..."`) exposed ONLY for `P4` falsifier regression testing!
pub fn broken_whole_word_complement_sk(w: &[u8]) -> bool {
    !(w.len() >= 7 && &w[0..3] == b"sk-" && w[3..].iter().all(|&b| is_sk_key_char(b)))
}

/// Public multilinear evaluation of the shift operator `S_shift(z, u) = [u == t + 1 for t < N - 1]`
/// (`\widetilde{q_{next}}(z) = \sum_{u=1}^{N-1} eq(z, u - 1) q[u] + eq(z, N - 1) q_final`) in `O(N)` ops (`N = 2048 -> < 5 us`!).
fn eval_shift_kernel_mle(z: &[Ext4], u_pt: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z);
    let eq_u = build_eq_table_lsb_ext4(u_pt);
    let n = eq_z.len();
    let mut acc = Ext4::ZERO;
    for t in 0..(n - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    acc
}

/// Content-bound `cSHAKE256` Zero-Knowledge `Absent("sk-...")` Receipt (`P4` + `P6` `BoundDfaStmt`),
/// proving **every** DFA transition `(q_t, b_t, q_{t+1})` via `124`-bit `Ext4` `D1b` LogUp-GKR over
/// `build_accepting_sk_dfa_public_table()` + shift sumcheck + ZK `SuccinctExt4Pcs` (`0` cleartext needed!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PaddedAbsenceZkReceipt {
    pub word_len: usize,
    pub pad_len: usize,
    pub final_state: u8,
    pub content_root: [u8; 32],
    pub bytes_pcs_root: [u8; 32],
    pub q_pcs_root: [u8; 32],
    pub q_next_pcs_root: [u8; 32],
    pub mult_dfa_pcs_root: [u8; 32],
    pub mult_b_pcs_root: [u8; 32],
    pub mult_q_pcs_root: [u8; 32],

    /// 1. `D1b` lookup proving `(q_t + 8 * b_pad_t + 2048 * q_next_t) in T_DFA_accepting` (forbids sink `4`!)
    pub dfa_d1b_proof: D1bRangeExt4Proof,
    pub q_at_dfa_leaf: Ext4,
    pub b_at_dfa_leaf: Ext4,
    pub q_next_at_dfa_leaf: Ext4,

    /// 2. `D1b` range proofs `b_pad_t in [0, 512)` and `q_t in [0, 8)` (guaranteeing injective tuple packing!)
    pub b_range_proof: D1bRangeExt4Proof,
    pub q_range_proof: D1bRangeExt4Proof,

    /// 3. Shift consistency sumcheck `q_next(z_sh) == sum_{t<N-1} eq(z_sh, t) * q[t + 1] + eq(z_sh, N - 1) * final_state`
    pub q_next_at_zsh: Ext4,
    pub shift_gruen_proof: GruenMode2Ext4Proof,

    /// 4. Succinct ZK `Ext4` PCS openings (`q[0] == 0` also opened directly!)
    pub bytes_pcs_proof: PcsOpeningProof,
    pub q_pcs_proof: PcsOpeningProof,
    pub q_next_pcs_proof: PcsOpeningProof,
    pub mult_dfa_pcs_proof: PcsOpeningProof,
    pub mult_b_pcs_proof: PcsOpeningProof,
    pub mult_q_pcs_proof: PcsOpeningProof,
}

impl PaddedAbsenceZkReceipt {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.word_len as u32).to_le_bytes());
        out.extend_from_slice(&(self.pad_len as u32).to_le_bytes());
        out.push(self.final_state);
        for r in [
            &self.content_root,
            &self.bytes_pcs_root,
            &self.q_pcs_root,
            &self.q_next_pcs_root,
            &self.mult_dfa_pcs_root,
            &self.mult_b_pcs_root,
            &self.mult_q_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        self.dfa_d1b_proof.write_to(out);
        for e in [
            self.q_at_dfa_leaf,
            self.b_at_dfa_leaf,
            self.q_next_at_dfa_leaf,
            self.q_next_at_zsh,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }
        self.b_range_proof.write_to(out);
        self.q_range_proof.write_to(out);
        self.shift_gruen_proof.write_to(out);
        for pf in [
            &self.bytes_pcs_proof,
            &self.q_pcs_proof,
            &self.q_next_pcs_proof,
            &self.mult_dfa_pcs_proof,
            &self.mult_b_pcs_proof,
            &self.mult_q_pcs_proof,
        ] {
            pf.write_to(out);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let word_len = cur.read_u32()? as usize;
        let pad_len = cur.read_u32()? as usize;
        let final_state = cur.read_u8()?;
        let content_root = cur.read_arr32()?;
        let bytes_pcs_root = cur.read_arr32()?;
        let q_pcs_root = cur.read_arr32()?;
        let q_next_pcs_root = cur.read_arr32()?;
        let mult_dfa_pcs_root = cur.read_arr32()?;
        let mult_b_pcs_root = cur.read_arr32()?;
        let mult_q_pcs_root = cur.read_arr32()?;
        let dfa_d1b_proof = D1bRangeExt4Proof::read_from(cur)?;
        let q_at_dfa_leaf = cur.read_ext4()?;
        let b_at_dfa_leaf = cur.read_ext4()?;
        let q_next_at_dfa_leaf = cur.read_ext4()?;
        let q_next_at_zsh = cur.read_ext4()?;
        let b_range_proof = D1bRangeExt4Proof::read_from(cur)?;
        let q_range_proof = D1bRangeExt4Proof::read_from(cur)?;
        let shift_gruen_proof = GruenMode2Ext4Proof::read_from(cur)?;
        let bytes_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let q_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let q_next_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_dfa_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_b_pcs_proof = PcsOpeningProof::read_from(cur)?;
        let mult_q_pcs_proof = PcsOpeningProof::read_from(cur)?;
        Ok(Self {
            word_len,
            pad_len,
            final_state,
            content_root,
            bytes_pcs_root,
            q_pcs_root,
            q_next_pcs_root,
            mult_dfa_pcs_root,
            mult_b_pcs_root,
            mult_q_pcs_root,
            dfa_d1b_proof,
            q_at_dfa_leaf,
            b_at_dfa_leaf,
            q_next_at_dfa_leaf,
            q_next_at_zsh,
            b_range_proof,
            q_range_proof,
            shift_gruen_proof,
            bytes_pcs_proof,
            q_pcs_proof,
            q_next_pcs_proof,
            mult_dfa_pcs_proof,
            mult_b_pcs_proof,
            mult_q_pcs_proof,
        })
    }
}

/// Prove `Absent(output_bytes, "sk-" · KeyChar)` in zero-knowledge (`P4` + `P6`), refusing if sink `4` is reached!
pub fn prove_padded_absence_zk(
    output_bytes: &[u8],
    tr: &mut CShakeTranscript,
) -> Result<PaddedAbsenceZkReceipt, String> {
    let (final_state, trace) = run_padded_complement_sk_dfa(output_bytes);
    if final_state >= 4 {
        return Err("prover refusal: output_bytes violates Absent(\"sk-...\") policy (sink state 4 reached)"
            .to_string());
    }
    // `pad_len >= 2048` (`2^11`) so `m_wit >= m_tab = 11` for `ProveKit v2` subdomain-lifted `D1b`!
    let pad_len = (output_bytes.len() + 2).next_power_of_two().max(2048);
    let m = pad_len.trailing_zeros() as usize;

    let mut bytes_pad = vec![256u32; pad_len]; // `256` = deterministic EOF/pad symbol
    for (i, &b) in output_bytes.iter().enumerate() {
        bytes_pad[i] = b as u32;
    }
    let mut q_vec = vec![final_state as u32; pad_len];
    let mut q_next_vec = vec![final_state as u32; pad_len];
    let mut tuples = vec![0u32; pad_len];
    for t in 0..pad_len {
        let qt = if t < trace.len() {
            trace[t] as u32
        } else {
            final_state as u32
        };
        let qn = if t + 1 < trace.len() {
            trace[t + 1] as u32
        } else {
            final_state as u32
        };
        q_vec[t] = qt;
        q_next_vec[t] = qn;
        tuples[t] = qt + 8 * bytes_pad[t] + 2048 * qn;
    }

    let pub_dfa_tab = build_accepting_sk_dfa_public_table();
    let mult_dfa = compute_d1b_public_table_multiplicities(&tuples, &pub_dfa_tab)?;
    let mult_b = compute_d1b_multiplicities(&bytes_pad, 9)?; // `[0, 512)`
    let mult_q = compute_d1b_multiplicities(&q_vec, 3)?; // `[0, 8)`

    let bytes_state = commit_table_pcs(&bytes_pad, PcsParams::default_zk(2), None);
    let q_state = commit_table_pcs(&q_vec, PcsParams::default_zk(4), None);
    let q_next_state = commit_table_pcs(&q_next_vec, PcsParams::default_zk(2), None);
    let mult_dfa_state = commit_table_pcs(&mult_dfa, PcsParams::default_zk(1), None);
    let mult_b_state = commit_table_pcs(&mult_b, PcsParams::default_zk(1), None);
    let mult_q_state = commit_table_pcs(&mult_q, PcsParams::default_zk(1), None);

    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(output_bytes.len() as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&bytes_state.root);
    let content_root = cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in);

    tr.absorb_root(b"abs_content_root", &content_root);
    tr.absorb_u32(b"abs_word_len", output_bytes.len() as u32);
    tr.absorb_u32(b"abs_final_state", final_state as u32);
    for r in [
        &bytes_state.root,
        &q_state.root,
        &q_next_state.root,
        &mult_dfa_state.root,
        &mult_b_state.root,
        &mult_q_state.root,
    ] {
        tr.absorb_root(b"abs_pcs_root", r);
    }

    // 1. `D1b` DFA transition lookup
    let (dfa_d1b_proof, z_dfa_leaf) =
        prove_d1b_public_table_ext4(&tuples, &pub_dfa_tab, &mult_dfa, tr);
    let q_at_dfa_leaf = mle_eval_bb_at_ext4(&q_vec, &z_dfa_leaf);
    let b_at_dfa_leaf = mle_eval_bb_at_ext4(&bytes_pad, &z_dfa_leaf);
    let q_next_at_dfa_leaf = mle_eval_bb_at_ext4(&q_next_vec, &z_dfa_leaf);
    tr.absorb_ext4(b"abs_q_dl", q_at_dfa_leaf);
    tr.absorb_ext4(b"abs_b_dl", b_at_dfa_leaf);
    tr.absorb_ext4(b"abs_qn_dl", q_next_at_dfa_leaf);

    // 2. `D1b` range proofs `b_pad in [0, 512)` and `q in [0, 8)`
    let (b_range_proof, z_b_leaf) = prove_d1b_range_ext4(&bytes_pad, &mult_b, m, 9, tr);
    let (q_range_proof, z_q_leaf) = prove_d1b_range_ext4(&q_vec, &mult_q, m, 3, tr);

    // 3. Shift sumcheck: `sum_{u=0}^{N-1} shift_col[u] * q[u] == q_next(z_sh) - eq(z_sh, N - 1) * final_state`
    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m, true);
    let q_next_at_zsh = mle_eval_bb_at_ext4(&q_next_vec, &z_sh);
    tr.absorb_ext4(b"abs_qn_zsh", q_next_at_zsh);

    let eq_zsh = build_eq_table_lsb_ext4(&z_sh);
    let mut shift_col = vec![Ext4::ZERO; pad_len];
    shift_col[1..pad_len].copy_from_slice(&eq_zsh[..(pad_len - 1)]);
    let q_ext: Vec<Ext4> = q_vec.iter().map(|&v| Ext4::from_bb(v)).collect();
    let (shift_gruen_proof, shift_chals) =
        prove_gruen_einsum_mode2_ext4(&shift_col, &q_ext, 0, m, &[], tr);

    // 4. Open all ZK PCS commitments (`including q[0] == 0` at `0^m`!)
    let bytes_pcs_proof = open_pcs_claims(
        &bytes_state,
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: b_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_b_leaf.clone(),
                value: b_range_proof.rem_leaf_eval,
            },
        ],
        tr,
    );
    let q_pcs_proof = open_pcs_claims(
        &q_state,
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m],
                value: Ext4::ZERO, // enforces `q_0 == 0`!
            },
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: q_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_q_leaf.clone(),
                value: q_range_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: shift_chals,
                value: shift_gruen_proof.terminal_openings.1,
            },
        ],
        tr,
    );
    let q_next_pcs_proof = open_pcs_claims(
        &q_next_state,
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: q_next_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_sh,
                value: q_next_at_zsh,
            },
        ],
        tr,
    );
    let mult_dfa_pcs_proof = open_pcs_claims(
        &mult_dfa_state,
        &[MleEvalClaim {
            point: z_dfa_leaf[..11].to_vec(),
            value: dfa_d1b_proof.mult_leaf_eval,
        }],
        tr,
    );
    let mult_b_pcs_proof = open_pcs_claims(
        &mult_b_state,
        &[MleEvalClaim {
            point: z_b_leaf[..9].to_vec(),
            value: b_range_proof.mult_leaf_eval,
        }],
        tr,
    );
    let mult_q_pcs_proof = open_pcs_claims(
        &mult_q_state,
        &[MleEvalClaim {
            point: z_q_leaf[..3].to_vec(),
            value: q_range_proof.mult_leaf_eval,
        }],
        tr,
    );

    Ok(PaddedAbsenceZkReceipt {
        word_len: output_bytes.len(),
        pad_len,
        final_state,
        content_root,
        bytes_pcs_root: bytes_state.root,
        q_pcs_root: q_state.root,
        q_next_pcs_root: q_next_state.root,
        mult_dfa_pcs_root: mult_dfa_state.root,
        mult_b_pcs_root: mult_b_state.root,
        mult_q_pcs_root: mult_q_state.root,
        dfa_d1b_proof,
        q_at_dfa_leaf,
        b_at_dfa_leaf,
        q_next_at_dfa_leaf,
        q_next_at_zsh,
        b_range_proof,
        q_range_proof,
        shift_gruen_proof,
        bytes_pcs_proof,
        q_pcs_proof,
        q_next_pcs_proof,
        mult_dfa_pcs_proof,
        mult_b_pcs_proof,
        mult_q_pcs_proof,
    })
}

/// Standalone ZK `Absent("sk-...")` verifier (`P4` + `P6`): sound **even with `opt_cleartext_bytes == None`**!
pub fn verify_padded_absence_zk(
    expected_content_root: &[u8; 32],
    opt_cleartext_bytes: Option<&[u8]>,
    receipt: &PaddedAbsenceZkReceipt,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    if &receipt.content_root != expected_content_root {
        return Err("P6 content_root binding mismatch".to_string());
    }
    if receipt.final_state >= 4 {
        return Err(format!(
            "Absent(\"sk-...\") rejected: final DFA state {} is non-accepting sink!",
            receipt.final_state
        ));
    }
    if !receipt.pad_len.is_power_of_two()
        || receipt.pad_len < 2048
        || receipt.word_len + 2 > receipt.pad_len
    {
        return Err("invalid PaddedAbsenceZkReceipt pad_len".to_string());
    }
    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(receipt.word_len as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&receipt.bytes_pcs_root);
    if cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in) != receipt.content_root {
        return Err("content_root != H(word_len || bytes_pcs_root)".to_string());
    }

    if let Some(clear) = opt_cleartext_bytes {
        if clear.len() != receipt.word_len {
            return Err("cleartext length != committed word_len".to_string());
        }
        let (q_end, _) = run_padded_complement_sk_dfa(clear);
        if q_end >= 4 || q_end != receipt.final_state {
            return Err(
                "cleartext bytes fail padded-complement Absent(\"sk-...\") DFA!".to_string(),
            );
        }
    }

    let m = receipt.pad_len.trailing_zeros() as usize;
    tr.absorb_root(b"abs_content_root", &receipt.content_root);
    tr.absorb_u32(b"abs_word_len", receipt.word_len as u32);
    tr.absorb_u32(b"abs_final_state", receipt.final_state as u32);
    for r in [
        &receipt.bytes_pcs_root,
        &receipt.q_pcs_root,
        &receipt.q_next_pcs_root,
        &receipt.mult_dfa_pcs_root,
        &receipt.mult_b_pcs_root,
        &receipt.mult_q_pcs_root,
    ] {
        tr.absorb_root(b"abs_pcs_root", r);
    }

    // 1. Verify `D1b` DFA transition lookup & linear tuple reconstruction `tuple == q + 8*b + 2048*q_next`!
    let pub_dfa_tab = build_accepting_sk_dfa_public_table();
    if receipt.dfa_d1b_proof.m_wit != m || receipt.dfa_d1b_proof.m_tab != 11 {
        return Err("DFA D1b dimensions mismatch".to_string());
    }
    let z_dfa_leaf = verify_d1b_public_table_ext4(&pub_dfa_tab, &receipt.dfa_d1b_proof, tr)?;
    tr.absorb_ext4(b"abs_q_dl", receipt.q_at_dfa_leaf);
    tr.absorb_ext4(b"abs_b_dl", receipt.b_at_dfa_leaf);
    tr.absorb_ext4(b"abs_qn_dl", receipt.q_next_at_dfa_leaf);

    let expected_tuple = receipt
        .q_at_dfa_leaf
        .add(receipt.b_at_dfa_leaf.scale_bb(8))
        .add(receipt.q_next_at_dfa_leaf.scale_bb(2048));
    if receipt.dfa_d1b_proof.rem_leaf_eval != expected_tuple {
        return Err("DFA transition tuple != q + 8*b + 2048*q_next".to_string());
    }

    // 2. Verify `b_pad in [0, 512)` and `q in [0, 8)` range proofs!
    if receipt.b_range_proof.m_wit != m
        || receipt.b_range_proof.m_tab != 9
        || receipt.q_range_proof.m_wit != m
        || receipt.q_range_proof.m_tab != 3
    {
        return Err("DFA b/q range D1b dimension mismatch".to_string());
    }
    let z_b_leaf = verify_d1b_range_ext4(&receipt.b_range_proof, tr)?;
    let z_q_leaf = verify_d1b_range_ext4(&receipt.q_range_proof, tr)?;

    // 3. Verify shift sumcheck: `claim == q_next(z_sh) - eq(z_sh, 1^m) * final_state`!
    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m, true);
    tr.absorb_ext4(b"abs_qn_zsh", receipt.q_next_at_zsh);
    let eq_last = crate::ext4::eq_mle_ext4(&z_sh, &vec![Ext4::ONE; m]);
    let expected_shift_claim = receipt
        .q_next_at_zsh
        .sub(eq_last.scale_bb(receipt.final_state as u32));
    let shift_chals =
        verify_gruen_einsum_mode2_ext4(expected_shift_claim, &[], &receipt.shift_gruen_proof, tr)?;
    if receipt.shift_gruen_proof.terminal_openings.0 != eval_shift_kernel_mle(&z_sh, &shift_chals) {
        return Err("DFA shift kernel public evaluation mismatch".to_string());
    }

    // 4. Verify all 6 ZK PCS openings!
    verify_pcs_claims(
        &receipt.bytes_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.b_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_b_leaf.clone(),
                value: receipt.b_range_proof.rem_leaf_eval,
            },
        ],
        &receipt.bytes_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.q_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(4)),
        &[
            MleEvalClaim {
                point: vec![Ext4::ZERO; m],
                value: Ext4::ZERO,
            },
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.q_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_q_leaf.clone(),
                value: receipt.q_range_proof.rem_leaf_eval,
            },
            MleEvalClaim {
                point: shift_chals,
                value: receipt.shift_gruen_proof.terminal_openings.1,
            },
        ],
        &receipt.q_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.q_next_pcs_root,
        PcsShape::new(m, PcsParams::default_zk(2)),
        &[
            MleEvalClaim {
                point: z_dfa_leaf.clone(),
                value: receipt.q_next_at_dfa_leaf,
            },
            MleEvalClaim {
                point: z_sh,
                value: receipt.q_next_at_zsh,
            },
        ],
        &receipt.q_next_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_dfa_pcs_root,
        PcsShape::new(11, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_dfa_leaf[..11].to_vec(),
            value: receipt.dfa_d1b_proof.mult_leaf_eval,
        }],
        &receipt.mult_dfa_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_b_pcs_root,
        PcsShape::new(9, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_b_leaf[..9].to_vec(),
            value: receipt.b_range_proof.mult_leaf_eval,
        }],
        &receipt.mult_b_pcs_proof,
        tr,
    )?;
    verify_pcs_claims(
        &receipt.mult_q_pcs_root,
        PcsShape::new(3, PcsParams::default_zk(1)),
        &[MleEvalClaim {
            point: z_q_leaf[..3].to_vec(),
            value: receipt.q_range_proof.mult_leaf_eval,
        }],
        &receipt.mult_q_pcs_proof,
        tr,
    )?;

    Ok(())
}

// ===========================================================================
// §2. End-to-End `U1` Online Boundary Commitment + Fiat–Shamir Audit Bundle
// ===========================================================================

pub struct U1OnlineCommitment {
    pub boundary_roots: [[u8; 32]; 25],
    pub boundary_states: Vec<PcsProverState>,
    pub fast_stream_roots: [[u8; 32]; 25],
}

pub fn commit_u1_fast_stream_boundaries(boundaries_bb: &[Vec<u32>]) -> [[u8; 32]; 25] {
    assert_eq!(boundaries_bb.len(), 25);
    let vec_roots: Vec<[u8; 32]> = boundaries_bb
        .par_iter()
        .enumerate()
        .map(|(l, bnd)| {
            let mut buf = Vec::with_capacity(4 + bnd.len() * 4);
            buf.extend_from_slice(&(l as u32).to_le_bytes());
            for &v in bnd {
                buf.extend_from_slice(&v.to_le_bytes());
            }
            cshake256_32(b"QW35-U1-FAST-BOUNDARY-V1", &buf)
        })
        .collect();
    vec_roots.try_into().unwrap()
}

pub fn commit_u1_pcs_boundaries(boundaries_bb: &[Vec<u32>]) -> U1OnlineCommitment {
    assert_eq!(boundaries_bb.len(), 25);
    let fast_stream_roots = commit_u1_fast_stream_boundaries(boundaries_bb);
    let boundary_states: Vec<PcsProverState> = boundaries_bb
        .par_iter()
        .map(|bnd| commit_table_pcs(bnd, PcsParams::default_zk(1), None))
        .collect();
    let mut boundary_roots = [[0u8; 32]; 25];
    for (i, st) in boundary_states.iter().enumerate() {
        boundary_roots[i] = st.root;
    }
    U1OnlineCommitment {
        boundary_roots,
        boundary_states,
        fast_stream_roots,
    }
}

pub fn derive_fiat_shamir_audited_gdn_layer(
    weight_root: &[u8; 32],
    boundary_roots: &[[u8; 32]; 25],
    redacted_content_root: &[u8; 32],
) -> usize {
    const GDN_LAYERS: [usize; 18] = [
        0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21, 22,
    ];
    let mut tr = CShakeTranscript::new(b"QW35-U1-VRF-AUDIT-INDEX-V1");
    tr.absorb_root(b"weight_root", weight_root);
    for (i, r) in boundary_roots.iter().enumerate() {
        tr.absorb_u32(b"b_idx", i as u32);
        tr.absorb_root(b"b_root", r);
    }
    tr.absorb_root(b"out_root", redacted_content_root);
    let pick = (tr.squeeze_bb(b"vrf_pick") as usize) % GDN_LAYERS.len();
    GDN_LAYERS[pick]
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qwen35U1AuditBundle {
    pub audited_layer: usize,
    pub bnd_vars: usize,
    pub layer_proof: SuccinctGdnLayerProof,
    pub absence_receipt: PaddedAbsenceZkReceipt,
}

impl Qwen35U1AuditBundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(512 * 1024);
        out.extend_from_slice(U1_BUNDLE_MAGIC);
        out.extend_from_slice(&(self.audited_layer as u32).to_le_bytes());
        out.extend_from_slice(&(self.bnd_vars as u32).to_le_bytes());
        self.layer_proof.write_to(&mut out);
        self.absence_receipt.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let magic = cur.read_exact(8)?;
        if magic != U1_BUNDLE_MAGIC {
            return Err("invalid Qwen35U1AuditBundle magic".to_string());
        }
        let audited_layer = cur.read_u32()? as usize;
        let bnd_vars = cur.read_u32()? as usize;
        let layer_proof = SuccinctGdnLayerProof::read_from(&mut cur)?;
        let absence_receipt = PaddedAbsenceZkReceipt::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(format!(
                "trailing {} bytes in Qwen35U1AuditBundle",
                cur.remaining()
            ));
        }
        Ok(Self {
            audited_layer,
            bnd_vars,
            layer_proof,
            absence_receipt,
        })
    }
}

/// `(proof_bytes, content_root, qs_binding)` returned by [`prove_u1_audit_bundle`].
pub type U1AuditBundleResult = (Vec<u8>, [u8; 32], [u8; 32]);

pub fn prove_u1_audit_bundle(
    registry: &Qwen35WeightRegistry,
    layer_tensor_digests: Vec<[u8; 32]>,
    gate_proj_slot: usize,
    gate_pcs: &PrecommittedMxfp4Pcs,
    u1_online: &U1OnlineCommitment,
    turn: &Qwen35TurnExecution,
    redacted_output_bytes: &[u8],
) -> Result<U1AuditBundleResult, String> {
    let mut abs_tr = CShakeTranscript::new(b"QW35-U1-ABSENCE-V1");
    let absence_receipt = prove_padded_absence_zk(redacted_output_bytes, &mut abs_tr)?;

    let l_idx = turn.audited_layer;
    let layer_path = registry.open_layer(l_idx);

    let mut qs_bind_in = [0u8; 96];
    qs_bind_in[0..32].copy_from_slice(&layer_tensor_digests[gate_proj_slot]);
    qs_bind_in[32..64].copy_from_slice(&gate_pcs.q_state.root);
    qs_bind_in[64..96].copy_from_slice(&gate_pcs.s_state.root);
    let qs_binding = cshake256_32(b"QW35-QS-PCS-BIND-V1", &qs_bind_in);

    let mut lyr_tr = CShakeTranscript::new(b"QW35-U1-LAYER-AUDIT-V1");
    let layer_proof = prove_audited_gdn_layer(
        &registry.weight_root,
        l_idx,
        AuditedGdnLayerWitness {
            layer_weight_path: layer_path,
            layer_tensor_digests,
            gate_proj_tensor_slot: gate_proj_slot,
            gate_pcs,
            b_in_state: &u1_online.boundary_states[l_idx],
            b_out_state: &u1_online.boundary_states[l_idx + 1],
            b_in_bb: &turn.boundaries_bb[l_idx],
            b_out_bb: &turn.boundaries_bb[l_idx + 1],
            delta_gdn_bb: &turn.delta_gdn_bb,
            delta_mlp_bb: &turn.delta_mlp_bb,
            wy: &turn.wy_witness,
            x_ln2_i16: &turn.x_ln2_i16,
            gate_y_raw: &turn.gate_proj_y_raw,
        },
        &mut lyr_tr,
    )?;

    let bnd_vars = turn.boundaries_bb[l_idx].len().trailing_zeros() as usize;
    let bundle = Qwen35U1AuditBundle {
        audited_layer: l_idx,
        bnd_vars,
        layer_proof,
        absence_receipt: absence_receipt.clone(),
    };
    Ok((bundle.to_bytes(), absence_receipt.content_root, qs_binding))
}

pub fn verify_u1_audit_bundle_standalone(
    weight_root: &[u8; 32],
    boundary_roots: &[[u8; 32]; 25],
    expected_audited_layer: usize,
    expected_qs_binding: &[u8; 32],
    expected_out_root: &[u8; 32],
    opt_redacted_bytes: Option<&[u8]>,
    proof_bytes: &[u8],
) -> Result<(), String> {
    if expected_audited_layer >= 24 {
        return Err("expected_audited_layer >= 24".to_string());
    }
    let bundle = Qwen35U1AuditBundle::from_bytes(proof_bytes)?;
    if bundle.audited_layer != expected_audited_layer {
        return Err("bundle audited_layer != expected_audited_layer".to_string());
    }

    let mut abs_tr = CShakeTranscript::new(b"QW35-U1-ABSENCE-V1");
    verify_padded_absence_zk(
        expected_out_root,
        opt_redacted_bytes,
        &bundle.absence_receipt,
        &mut abs_tr,
    )?;

    let mut lyr_tr = CShakeTranscript::new(b"QW35-U1-LAYER-AUDIT-V1");
    verify_audited_gdn_layer_standalone(
        &AuditedGdnLayerVerifyStmt {
            expected_weight_root: weight_root,
            expected_b_in_root: &boundary_roots[expected_audited_layer],
            expected_b_out_root: &boundary_roots[expected_audited_layer + 1],
            expected_audited_layer,
            expected_q_s_binding: expected_qs_binding,
            bnd_vars: bundle.bnd_vars,
        },
        &bundle.layer_proof,
        &mut lyr_tr,
    )?;

    Ok(())
}
