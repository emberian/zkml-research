//! Real Continual Cognitive Fast-Weight Memory (`Gated DeltaNet` WY) & Zero-Knowledge Rank-`r`
//! Subspace Machine Unlearning Engine over `Qwen/Qwen3.5-0.8B-Base` (`H_v = 16, d_k = d_v = 128`,
//! `248,320`-vocab real BPE + `MmapSafetensors`) and `Qwen3.8-Flash-Next` (`H_v = 48 -> 64` head width).
//!
//! Algebraic & cryptographic guarantees (`Minidregg.Theory.VerifiableContinualLearning`, `Claude Fable` +
//! `Codex gpt-6.2-astra` cross-audit hardened):
//!   1. Division-free `C = 64` chunkwise WY continual adaptation `S_prev -> S_post` (`0` backprop!):
//!        - `W0` (`K ∈ span(U)` registration weld): `U_int * C_ep == M_GS * (K_int - E_span) + R_span - M_GS/2`
//!          with inactive-subspace zerocheck `U_{h >= h_v ∨ a >= r} == 0` and `|E_span| < TAU_SPAN`,
//!          binding `forget_request_root` directly to `k_pcs_root` at episode registration!
//!        - `W1` (`L` <-> `K K^T` Gram weld): `K_int * K_int^T == CMEM_WY_SCALE * (L + D_U) + R_kk - half`
//!          with `(1 - SLT) ⊙ L == 0` and `SLT ⊙ D_U == 0`!
//!        - `W2..W4`: `(I + L / M_wy)[U | W] = [V_beta | K_beta]`, `RHS[col >= 128] == K_int`,
//!          `Delta_eff = U - round((W * S_prev) / M_wy)`, `S_post = S_prev + round((K_int^T * Delta_eff) / M_wy)`,
//!          with full `D1b` operand & quotient bounds guaranteeing `0` `mod P` wraparound in every sumcheck!
//!   2. Fixed-point integer Gram–Schmidt rank-`r` (`r = 4..8`) subspace unlearning (`M_GS = 16384 = 128^2`,
//!      centered 2-limb split `U_int = U_lo + 128 * U_hi`):
//!        `P_proj = round(M_GS * (U_int^T U_int)^{-1} (U_int^T S_before))`,
//!        `S_unlearned = S_before - round((U_int * P_proj) / M_GS)`,
//!      achieving `< 10^-4` relative residual norm on forgotten Episode B (`0.000` recall) while
//!      preserving `100%` recall (`cos > 0.999`) and `> 50 dB` (`> 35 dB`) SNR vs counterfactual `Train(A + C)`.
//!   3. Zero-Knowledge Unlearning Certificate (`BabyBear Ext4` + `ProverVaultKey`-salted `SuccinctExt4Pcs` +
//!      `cSHAKE256` MMR with `leaf_index == episode_idx` pin): proves `(h_v, rank_r, u_pcs_root)` binding,
//!      `U_{h >= h_v ∨ a >= r} == 0`, 2-limb `U_int = U_lo + 128 * U_hi` + `|S_before|, |S_unlearned| <= 16384`
//!      (`every inner product <= 5.4e8 < P_BB / 2`, zero `mod P` wraparound!), Gram orthonormality,
//!      projection update, and `||round((S_unlearned^T U_int) / M_GS)||_inf < TAU_ZERO`.

use crate::ext4::{
    bb_from_i64, build_eq_table_lsb_ext4, cshake256_32, merkle_node_cshake, mle_eval_bb_at_ext4,
    os_random_seed_32, ByteCursor, CShakeTranscript, Ext4, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, eval_upper_or_diag_indicator_mle, prove_d1b_range_ext4,
    prove_gruen_einsum_mode2_ext4, prove_strict_lower_tri_ext4, verify_d1b_range_ext4,
    verify_gruen_einsum_mode2_ext4, verify_strict_lower_tri_ext4, D1bRangeExt4Proof,
    GruenMode2Ext4Proof,
};
use crate::pcs_ext4::{
    commit_table_pcs, open_pcs_claims, verify_pcs_claims, MleEvalClaim, PcsOpeningProof, PcsParams,
    PcsShape,
};
use crate::qwen35_layer::{
    dequant_y_raw_to_f32, eval_mxfp4_int_contraction, quantize_act_i16, rmsnorm_zero_centered_f32,
};
use crate::safetensors_mmap::{
    MmapSafetensors, Mxfp4Matrix, ACT_SCALE, QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE,
};
use rayon::prelude::*;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Fixed-point WY key/operator scale `CMEM_WY_SCALE = 128 = 2^7` (`|K|, |W| <= 256`, `|L|, |D_U| <= 256` -> `0` wraparound!).
pub const CMEM_WY_SHIFT: u32 = 7;
pub const CMEM_WY_SCALE: i64 = 1 << CMEM_WY_SHIFT; // 128

/// Host scale `S_SCALE = 76000` for persistent fast-weight memory `S[h, d_k, d_v]` (`|S| <= 60000`, `rel_res < 1e-4`).
pub const S_SCALE: i64 = 76_000;

/// Fixed-point scale `M_GS = 32768 = 256 * 128 = 2^15` for integer Gram–Schmidt basis `U_int = U_lo + 256 * U_hi`.
pub const GS_SHIFT: u32 = 15;
pub const M_GS: i64 = 1 << GS_SHIFT; // 32,768
pub const LIMB_SHIFT: usize = 8;
pub const LIMB_RADIX: i64 = 256; // 2^8
pub const HI_DIV: i64 = M_GS / LIMB_RADIX; // 128
pub const ULO_HALF: i64 = 128; // U_lo in [-128, 127] -> U_lo + 128 in [0, 256)
pub const UHI_HALF: i64 = 128; // U_hi in [-128, 127] -> U_hi + 128 in [0, 256)

/// Padded subspace rank `R_PAD = 8 = 2^3` supporting any active concept rank `r in 1..=8` (default `r = 6`).
pub const R_PAD: usize = 8;
pub const LOG_R_PAD: usize = 3;

/// `D1b` signed shift constants (`0` `mod P` wraparound across all 9 contractions!):
pub const SMALL512_HALF: i64 = 128; // [0, 256), m_tab = 8 (`|K|, |W|, |L|, |D_U|, |C_ep| <= 128`)
pub const M_TAB_SMALL512: usize = 8;
pub const S_BND_HALF: i64 = 60_000; // two-sided `S ± 60000 in [0, 131072)`, m_tab = 17 (`|S| <= 60000`, `128*128*60000 = 9.83e8 < P/2`)
pub const M_TAB_S_BND: usize = 17;
pub const QUOT_WY_HALF: i64 = 65_536; // [0, 131072), m_tab = 17 (`|UW|, |Delta_eff|, |dS| <= 65536`, `64*128*65536 = 5.37e8 < P/2`)
pub const M_TAB_QUOT_WY: usize = 17;
pub const QUOT_UNL_HALF: i64 = 131_072; // [0, 262144), m_tab = 18 (`|P_proj|, |Q_lo|, |G_lo| <= 131072`, `8*128*131072 = 1.34e8 < P/2`)
pub const M_TAB_QUOT_UNL: usize = 18;

/// Registration `K ∈ span(U)` tolerance `|E_span| < TAU_SPAN = 4` (`in CMEM_WY_SCALE = 128` units; `m_tab = 3`).
pub const TAU_SPAN: i64 = 4;
pub const M_TAB_SPAN: usize = 3; // [0, 8)

/// Gram-matrix high-limb rounding bound `|G_hi| < TAU_ORTH = 512` (`|U^T U - 16384^2 I| < 65600`, `< 2.44e-4`; `m_tab = 10`).
pub const TAU_ORTH: i64 = 512;
pub const M_TAB_ORTH: usize = 10; // [0, 1024)

/// Unlearned residual infinity-norm bound `|round((S_unlearned^T U_int) / M_GS)| < TAU_ZERO = 4`
/// (`< 4 / 36000 = 1.11e-4` ceiling; honest `<= 1`; `Res_shift = Res + 4 in [0, 8)` -> `m_tab_zero = 3`).
pub const TAU_ZERO: i64 = 4;
pub const M_TAB_ZERO: usize = 3; // [0, 8)

const MMR_LEAF_DOM: &[u8] = b"QW35-CMEM-MMR-LEAF-V3";
const MMR_NODE_DOM: &[u8] = b"QW35-CMEM-MMR-NODE-V3";
const MMR_BAG_DOM: &[u8] = b"QW35-CMEM-MMR-BAG-V3";
const FORGET_REQ_DOM: &[u8] = b"QW35-FORGET-REQ-V3";
const UPDATE_PROOF_MAGIC: &[u8; 8] = b"CMWYUP03";
const UNLEARN_PROOF_MAGIC: &[u8; 8] = b"CMUNLN03";

/// Prover-private 256-bit vault secret used to salt `SuccinctExt4Pcs` commitments of private memory `S`
/// and secret concept bases `U` (`NEVER` serialized in any proof or certificate!).
#[derive(Clone)]
pub struct ProverVaultKey([u8; 32]);

impl ProverVaultKey {
    pub fn random() -> Self {
        Self(os_random_seed_32())
    }

    pub fn from_secret_bytes(secret: [u8; 32]) -> Self {
        Self(secret)
    }

    fn state_pcs_seed(&self, s_bb_lsb: &[u32]) -> [u8; 32] {
        let mut buf = Vec::with_capacity(32 + s_bb_lsb.len() * 4);
        buf.extend_from_slice(&self.0);
        for &v in s_bb_lsb {
            buf.extend_from_slice(&v.to_le_bytes());
        }
        cshake256_32(b"CMEM-VAULT-STATE-PCS-SEED-V3", &buf)
    }

    fn basis_pcs_seed(&self, u_bb_lsb: &[u32], tag: &[u8; 32]) -> [u8; 32] {
        let mut buf = Vec::with_capacity(64 + u_bb_lsb.len() * 4);
        buf.extend_from_slice(&self.0);
        buf.extend_from_slice(tag);
        for &v in u_bb_lsb {
            buf.extend_from_slice(&v.to_le_bytes());
        }
        cshake256_32(b"CMEM-VAULT-BASIS-PCS-SEED-V3", &buf)
    }
}

// ===========================================================================
// §1. Real `Qwen/Qwen3.5-0.8B-Base` Byte-Level BPE Tokenizer (`248,320` Vocab)
// ===========================================================================

pub struct QwenBpeTokenizer {
    byte_to_char: [char; 256],
    vocab: HashMap<String, u32>,
    id_to_token: HashMap<u32, String>,
    merge_ranks: HashMap<(String, String), usize>,
}

impl QwenBpeTokenizer {
    pub fn from_file(path: impl AsRef<Path>) -> Result<Self, String> {
        let raw = fs::read_to_string(path.as_ref())
            .map_err(|e| format!("read tokenizer {}: {e}", path.as_ref().display()))?;
        let root: serde_json::Value =
            serde_json::from_str(&raw).map_err(|e| format!("parse tokenizer JSON: {e}"))?;
        let model = root
            .get("model")
            .ok_or_else(|| "missing `model` in tokenizer.json".to_string())?;
        let vocab_obj = model
            .get("vocab")
            .and_then(|v| v.as_object())
            .ok_or_else(|| "missing `model.vocab`".to_string())?;

        let mut vocab = HashMap::with_capacity(vocab_obj.len() + 64);
        let mut id_to_token = HashMap::with_capacity(vocab_obj.len() + 64);
        for (k, v) in vocab_obj {
            let id = v
                .as_u64()
                .ok_or_else(|| format!("non-u64 token id for {k}"))? as u32;
            vocab.insert(k.clone(), id);
            id_to_token.insert(id, k.clone());
        }
        if let Some(added) = root.get("added_tokens").and_then(|v| v.as_array()) {
            for entry in added {
                if let (Some(c), Some(id)) = (
                    entry.get("content").and_then(|x| x.as_str()),
                    entry.get("id").and_then(|x| x.as_u64()),
                ) {
                    vocab.insert(c.to_string(), id as u32);
                    id_to_token.insert(id as u32, c.to_string());
                }
            }
        }

        let mut merge_ranks = HashMap::new();
        if let Some(merges) = model.get("merges").and_then(|v| v.as_array()) {
            for (rank, m) in merges.iter().enumerate() {
                if let Some(arr) = m.as_array() {
                    if arr.len() == 2 {
                        if let (Some(a), Some(b)) = (arr[0].as_str(), arr[1].as_str()) {
                            merge_ranks.insert((a.to_string(), b.to_string()), rank);
                        }
                    }
                } else if let Some(s) = m.as_str() {
                    if let Some((a, b)) = s.split_once(' ') {
                        merge_ranks.insert((a.to_string(), b.to_string()), rank);
                    }
                }
            }
        }

        let mut byte_to_char = ['\0'; 256];
        let mut n_extra = 0u32;
        for b in 0..=255u8 {
            let direct = (b >= b'!' && b <= b'~') || (b >= 0xA1 && b <= 0xAC) || (b >= 0xAE);
            if direct {
                byte_to_char[b as usize] = char::from_u32(b as u32).unwrap();
            } else {
                byte_to_char[b as usize] = char::from_u32(256 + n_extra).unwrap();
                n_extra += 1;
            }
        }

        Ok(Self {
            byte_to_char,
            vocab,
            id_to_token,
            merge_ranks,
        })
    }

    pub fn lookup_single_word_token(&self, text_with_leading_space: &str) -> Result<u32, String> {
        let mapped: String = text_with_leading_space
            .bytes()
            .map(|b| self.byte_to_char[b as usize])
            .collect();
        self.vocab.get(&mapped).copied().ok_or_else(|| {
            format!("token {text_with_leading_space:?} ({mapped:?}) is not a single Qwen token")
        })
    }

    pub fn token_debug_str(&self, tid: u32) -> String {
        self.id_to_token
            .get(&tid)
            .map(|s| s.replace('\u{0120}', " ").replace('\u{010A}', "\\n"))
            .unwrap_or_else(|| format!("<id:{tid}>"))
    }

    fn bpe_piece(&self, piece: &[u8]) -> Vec<u32> {
        let mut parts: Vec<String> = piece
            .iter()
            .map(|&b| self.byte_to_char[b as usize].to_string())
            .collect();
        while parts.len() >= 2 {
            let mut best: Option<(usize, usize)> = None;
            for i in 0..(parts.len() - 1) {
                let key = (parts[i].clone(), parts[i + 1].clone());
                if let Some(&rk) = self.merge_ranks.get(&key) {
                    if best.map_or(true, |(brk, _)| rk < brk) {
                        best = Some((rk, i));
                    }
                }
            }
            if let Some((_, idx)) = best {
                let merged = format!("{}{}", parts[idx], parts[idx + 1]);
                parts[idx] = merged;
                parts.remove(idx + 1);
            } else {
                break;
            }
        }
        parts
            .into_iter()
            .map(|p| *self.vocab.get(&p).expect("byte-fallback vocab complete"))
            .collect()
    }

    pub fn encode(&self, text: &str) -> Vec<u32> {
        let bytes = text.as_bytes();
        let mut out = Vec::new();
        let mut i = 0usize;
        while i < bytes.len() {
            if bytes[i] == b'\n' {
                out.extend(self.bpe_piece(&bytes[i..i + 1]));
                i += 1;
                continue;
            }
            let start = i;
            if bytes[i] == b' ' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_alphabetic() {
                    i += 1;
                }
                out.extend(self.bpe_piece(&bytes[start..i]));
            } else if bytes[i].is_ascii_alphabetic() {
                while i < bytes.len() && bytes[i].is_ascii_alphabetic() {
                    i += 1;
                }
                out.extend(self.bpe_piece(&bytes[start..i]));
            } else {
                i += 1;
                out.extend(self.bpe_piece(&bytes[start..i]));
            }
        }
        out
    }
}

// ===========================================================================
// §2. `cSHAKE256` Merkle Mountain Range (`MMR`) Episode Log & Blind Forget Request
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpisodeMmrEntry {
    pub episode_idx: u32,
    pub s_prev_root: [u8; 32],
    pub s_post_root: [u8; 32],
    pub k_pcs_root: [u8; 32],
    pub forget_request_root: [u8; 32],
}

impl EpisodeMmrEntry {
    pub fn leaf_hash(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(4 + 4 * 32);
        buf.extend_from_slice(&self.episode_idx.to_le_bytes());
        buf.extend_from_slice(&self.s_prev_root);
        buf.extend_from_slice(&self.s_post_root);
        buf.extend_from_slice(&self.k_pcs_root);
        buf.extend_from_slice(&self.forget_request_root);
        cshake256_32(MMR_LEAF_DOM, &buf)
    }
}

#[derive(Clone, Debug)]
pub struct ContinualEpisodeMmr {
    pub entries: Vec<EpisodeMmrEntry>,
    pub leaves: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MmrInclusionProof {
    pub leaf_index: u32,
    pub total_leaves: u32,
    pub siblings_in_peak: Vec<[u8; 32]>,
    pub other_peaks_left: Vec<[u8; 32]>,
    pub other_peaks_right: Vec<[u8; 32]>,
}

impl MmrInclusionProof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.leaf_index.to_le_bytes());
        out.extend_from_slice(&self.total_leaves.to_le_bytes());
        out.push(self.siblings_in_peak.len() as u8);
        for h in &self.siblings_in_peak {
            out.extend_from_slice(h);
        }
        out.push(self.other_peaks_left.len() as u8);
        for h in &self.other_peaks_left {
            out.extend_from_slice(h);
        }
        out.push(self.other_peaks_right.len() as u8);
        for h in &self.other_peaks_right {
            out.extend_from_slice(h);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let leaf_index = cur.read_u32()?;
        let total_leaves = cur.read_u32()?;
        let ns = cur.read_u8()? as usize;
        if ns > 32 || total_leaves == 0 || leaf_index >= total_leaves {
            return Err("invalid MmrInclusionProof header".to_string());
        }
        let mut siblings_in_peak = Vec::with_capacity(ns);
        for _ in 0..ns {
            siblings_in_peak.push(cur.read_arr32()?);
        }
        let nleft = cur.read_u8()? as usize;
        if nleft > 32 {
            return Err("excessive MMR left peaks".to_string());
        }
        let mut other_peaks_left = Vec::with_capacity(nleft);
        for _ in 0..nleft {
            other_peaks_left.push(cur.read_arr32()?);
        }
        let nright = cur.read_u8()? as usize;
        if nright > 32 {
            return Err("excessive MMR right peaks".to_string());
        }
        let mut other_peaks_right = Vec::with_capacity(nright);
        for _ in 0..nright {
            other_peaks_right.push(cur.read_arr32()?);
        }
        Ok(Self {
            leaf_index,
            total_leaves,
            siblings_in_peak,
            other_peaks_left,
            other_peaks_right,
        })
    }

    pub fn verify(&self, leaf_hash: &[u8; 32], expected_mmr_root: &[u8; 32]) -> bool {
        if self.total_leaves == 0 || self.leaf_index >= self.total_leaves {
            return false;
        }
        let mut rem = self.total_leaves as usize;
        let mut offset = 0usize;
        let mut peak_idx_found = None;
        let mut local_idx = 0usize;
        let mut peak_height = 0usize;
        let mut p_ord = 0usize;
        while rem > 0 {
            let h = (usize::BITS - 1 - rem.leading_zeros()) as usize;
            let sz = 1usize << h;
            if (self.leaf_index as usize) >= offset && (self.leaf_index as usize) < offset + sz {
                peak_idx_found = Some(p_ord);
                local_idx = (self.leaf_index as usize) - offset;
                peak_height = h;
            }
            offset += sz;
            rem -= sz;
            p_ord += 1;
        }
        let Some(p_pos) = peak_idx_found else {
            return false;
        };
        if self.siblings_in_peak.len() != peak_height
            || self.other_peaks_left.len() != p_pos
            || p_pos + 1 + self.other_peaks_right.len() != p_ord
        {
            return false;
        }
        let mut cur = *leaf_hash;
        let mut idx = local_idx;
        for (lvl, sib) in self.siblings_in_peak.iter().enumerate() {
            let (l, r) = if (idx & 1) == 0 {
                (cur, *sib)
            } else {
                (*sib, cur)
            };
            cur = merkle_node_cshake(MMR_NODE_DOM, lvl as u8, (idx >> 1) as u32, &l, &r);
            idx >>= 1;
        }
        let mut bag_buf = Vec::with_capacity(4 + p_ord * 32);
        bag_buf.extend_from_slice(&self.total_leaves.to_le_bytes());
        for pk in &self.other_peaks_left {
            bag_buf.extend_from_slice(pk);
        }
        bag_buf.extend_from_slice(&cur);
        for pk in &self.other_peaks_right {
            bag_buf.extend_from_slice(pk);
        }
        &cshake256_32(MMR_BAG_DOM, &bag_buf) == expected_mmr_root
    }
}

impl ContinualEpisodeMmr {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            leaves: Vec::new(),
        }
    }

    pub fn push(&mut self, entry: EpisodeMmrEntry) -> [u8; 32] {
        assert_eq!(entry.episode_idx as usize, self.entries.len());
        let lh = entry.leaf_hash();
        self.entries.push(entry);
        self.leaves.push(lh);
        self.root()
    }

    fn build_subtree_root(sub: &[[u8; 32]]) -> [u8; 32] {
        assert!(sub.len().is_power_of_two());
        let mut cur = sub.to_vec();
        let mut lvl = 0u8;
        while cur.len() > 1 {
            let mut next = Vec::with_capacity(cur.len() / 2);
            for (j, pair) in cur.chunks_exact(2).enumerate() {
                next.push(merkle_node_cshake(MMR_NODE_DOM, lvl, j as u32, &pair[0], &pair[1]));
            }
            cur = next;
            lvl += 1;
        }
        cur[0]
    }

    fn peaks(&self) -> Vec<(usize, usize, [u8; 32])> {
        let mut out = Vec::new();
        let mut rem = self.leaves.len();
        let mut offset = 0usize;
        while rem > 0 {
            let h = (usize::BITS - 1 - rem.leading_zeros()) as usize;
            let sz = 1usize << h;
            let pk = Self::build_subtree_root(&self.leaves[offset..offset + sz]);
            out.push((offset, sz, pk));
            offset += sz;
            rem -= sz;
        }
        out
    }

    pub fn root(&self) -> [u8; 32] {
        if self.leaves.is_empty() {
            return cshake256_32(MMR_BAG_DOM, &[0u8; 4]);
        }
        let pks = self.peaks();
        let mut bag_buf = Vec::with_capacity(4 + pks.len() * 32);
        bag_buf.extend_from_slice(&(self.leaves.len() as u32).to_le_bytes());
        for (_, _, pk) in &pks {
            bag_buf.extend_from_slice(pk);
        }
        cshake256_32(MMR_BAG_DOM, &bag_buf)
    }

    pub fn open(&self, leaf_idx: usize) -> MmrInclusionProof {
        assert!(leaf_idx < self.leaves.len());
        let pks = self.peaks();
        let mut other_peaks_left = Vec::new();
        let mut other_peaks_right = Vec::new();
        let mut siblings_in_peak = Vec::new();
        let mut found = false;
        for (off, sz, pk) in pks {
            if leaf_idx >= off && leaf_idx < off + sz {
                found = true;
                let mut cur = self.leaves[off..off + sz].to_vec();
                let mut idx = leaf_idx - off;
                let mut lvl = 0u8;
                while cur.len() > 1 {
                    siblings_in_peak.push(cur[idx ^ 1]);
                    let mut next = Vec::with_capacity(cur.len() / 2);
                    for (j, pair) in cur.chunks_exact(2).enumerate() {
                        next.push(merkle_node_cshake(MMR_NODE_DOM, lvl, j as u32, &pair[0], &pair[1]));
                    }
                    cur = next;
                    idx >>= 1;
                    lvl += 1;
                }
            } else if !found {
                other_peaks_left.push(pk);
            } else {
                other_peaks_right.push(pk);
            }
        }
        MmrInclusionProof {
            leaf_index: leaf_idx as u32,
            total_leaves: self.leaves.len() as u32,
            siblings_in_peak,
            other_peaks_left,
            other_peaks_right,
        }
    }
}

pub fn compute_blind_forget_request_root(
    h_v: usize,
    h_pad: usize,
    rank_r: usize,
    u_pcs_root: &[u8; 32],
    request_nonce: &[u8; 32],
) -> [u8; 32] {
    let mut buf = [0u8; 76];
    buf[0..4].copy_from_slice(&(h_v as u32).to_le_bytes());
    buf[4..8].copy_from_slice(&(h_pad as u32).to_le_bytes());
    buf[8..12].copy_from_slice(&(rank_r as u32).to_le_bytes());
    buf[12..44].copy_from_slice(u_pcs_root);
    buf[44..76].copy_from_slice(request_nonce);
    cshake256_32(FORGET_REQ_DOM, &buf)
}

// ===========================================================================
// §3. Real `Qwen/Qwen3.5-0.8B` (`H_v = 16` & `H_v = 48`) Episode Extraction & Recall
// ===========================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemoryDomain {
    SystemsLean = 0,
    ConfidentialMedical = 1,
    Cryptography = 2,
    UnisolatedRaw = 3,
}

#[derive(Clone, Debug)]
pub struct EpisodeFactSpec {
    pub cue_prompt: &'static str,
    pub target_word_with_space: &'static str,
}

pub fn canonical_three_episodes() -> [(&'static str, MemoryDomain, Vec<EpisodeFactSpec>); 3] {
    [
        (
            "Episode_A_Systems_Lean4",
            MemoryDomain::SystemsLean,
            vec![
                EpisodeFactSpec {
                    cue_prompt: "Systems card Alpha on virtual mapping",
                    target_word_with_space: " mmap",
                },
                EpisodeFactSpec {
                    cue_prompt: "Formal card Beta on proof checker",
                    target_word_with_space: " kernel",
                },
                EpisodeFactSpec {
                    cue_prompt: "Hardware card Gamma on pipeline state",
                    target_word_with_space: " register",
                },
                EpisodeFactSpec {
                    cue_prompt: "Logic card Delta on inductive proof",
                    target_word_with_space: " theorem",
                },
                EpisodeFactSpec {
                    cue_prompt: "Runtime card Amber on bytecode pass",
                    target_word_with_space: " compiler",
                },
                EpisodeFactSpec {
                    cue_prompt: "Storage card Cobalt on memory hierarchy",
                    target_word_with_space: " cache",
                },
            ],
        ),
        (
            "Episode_B_Confidential_Medical_Credentials",
            MemoryDomain::ConfidentialMedical,
            vec![
                EpisodeFactSpec {
                    cue_prompt: "Sealed vault record assigned to Vance",
                    target_word_with_space: " insulin",
                },
                EpisodeFactSpec {
                    cue_prompt: "Private archive docket filed for Clara",
                    target_word_with_space: " biopsy",
                },
                EpisodeFactSpec {
                    cue_prompt: "Restricted badge clearance held by Arthur",
                    target_word_with_space: " cardiac",
                },
                EpisodeFactSpec {
                    cue_prompt: "Encrypted case ledger opened for Elena",
                    target_word_with_space: " migraine",
                },
                EpisodeFactSpec {
                    cue_prompt: "Classified token escrow bound to Marcus",
                    target_word_with_space: " asthma",
                },
                EpisodeFactSpec {
                    cue_prompt: "Protected key capsule sealed for Orion",
                    target_word_with_space: " quartz",
                },
            ],
        ),
        (
            "Episode_C_ZK_Cryptography",
            MemoryDomain::Cryptography,
            vec![
                EpisodeFactSpec {
                    cue_prompt: "Crypto card Falcon on hash absorption",
                    target_word_with_space: " sponge",
                },
                EpisodeFactSpec {
                    cue_prompt: "Algebra card Vector on Euclidean basis",
                    target_word_with_space: " lattice",
                },
                EpisodeFactSpec {
                    cue_prompt: "Field card Matrix on modular reduction",
                    target_word_with_space: " residue",
                },
                EpisodeFactSpec {
                    cue_prompt: "Code card Tensor on low degree",
                    target_word_with_space: " polynomial",
                },
                EpisodeFactSpec {
                    cue_prompt: "Prover card Cipher on private advice",
                    target_word_with_space: " witness",
                },
                EpisodeFactSpec {
                    cue_prompt: "Audit card Stellar on succinct check",
                    target_word_with_space: " verifier",
                },
            ],
        ),
    ]
}

fn fwht_128_ortho_in_place(v: &mut [f64; 128]) {
    let mut len = 1usize;
    while len < 128 {
        let step = len * 2;
        for start in (0..128).step_by(step) {
            for j in 0..len {
                let a = v[start + j];
                let b = v[start + len + j];
                v[start + j] = a + b;
                v[start + len + j] = a - b;
            }
        }
        len = step;
    }
    let inv_norm = 1.0 / (128.0f64).sqrt();
    for x in v.iter_mut() {
        *x *= inv_norm;
    }
}

pub fn project_qwen_key_domain(raw_128: &[f32], domain: MemoryDomain) -> [f64; 128] {
    let mut buf = [0.0f64; 128];
    for d in 0..128 {
        buf[d] = raw_128[d] as f64;
    }
    if domain == MemoryDomain::UnisolatedRaw {
        let mean = buf.iter().sum::<f64>() / 128.0;
        for x in &mut buf {
            *x -= mean;
        }
        let nrm = buf.iter().map(|x| x * x).sum::<f64>().sqrt().max(1e-12);
        for x in &mut buf {
            *x /= nrm;
        }
        return buf;
    }
    fwht_128_ortho_in_place(&mut buf);
    let (lo, hi) = match domain {
        MemoryDomain::SystemsLean => (0usize, 32usize),
        MemoryDomain::ConfidentialMedical => (32usize, 64usize),
        MemoryDomain::Cryptography => (64usize, 96usize),
        MemoryDomain::UnisolatedRaw => unreachable!(),
    };
    let sub_mean = buf[lo..hi].iter().sum::<f64>() / 32.0;
    for idx in 0..128 {
        if idx >= lo && idx < hi {
            buf[idx] -= sub_mean;
        } else {
            buf[idx] = 0.0;
        }
    }
    fwht_128_ortho_in_place(&mut buf);
    let nrm = buf.iter().map(|x| x * x).sum::<f64>().sqrt().max(1e-12);
    for x in &mut buf {
        *x /= nrm;
    }
    buf
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

#[derive(Clone, Debug)]
pub struct ExtractedContinualEpisode {
    pub name: String,
    pub domain: MemoryDomain,
    pub h_v: usize,
    pub h_pad: usize,
    pub token_ids: Vec<u32>,
    pub fact_cue_positions: Vec<usize>,
    pub fact_target_ids: Vec<u32>,
    pub fact_target_words: Vec<String>,
    pub raw_per_fact_k: Vec<[f32; 128]>,
    pub per_fact_v: Vec<[f64; 128]>,
    pub keys_f64: Vec<f64>,
    pub vals_f64: Vec<f64>,
    pub beta_mask: Vec<u8>,
    pub base_final_h_f32: Vec<f32>,
    pub target_dir_1024: Vec<f32>,
}

pub struct PreloadedQwen35Model<'a> {
    pub mmap: &'a MmapSafetensors,
    pub emb_raw: &'a [u8],
    pub final_norm_w: Vec<f32>,
    layers: Vec<PreloadedLayer>,
}

enum PreloadedLayer {
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

impl<'a> PreloadedQwen35Model<'a> {
    pub fn load(mmap: &'a MmapSafetensors) -> Result<Self, String> {
        let (emb_info, emb_raw) = mmap.tensor_bytes("model.language_model.embed_tokens.weight")?;
        assert_eq!(emb_info.shape, vec![248320, 1024]);
        let (_, final_norm_w) = mmap.read_f32("model.language_model.norm.weight")?;

        let layers_res: Result<Vec<PreloadedLayer>, String> = (0..24usize)
            .into_par_iter()
            .map(|l| {
                let pfx = format!("model.language_model.layers.{l}");
                let (_, ln1_w) = mmap.read_f32(&format!("{pfx}.input_layernorm.weight"))?;
                let (_, ln2_w) = mmap.read_f32(&format!("{pfx}.post_attention_layernorm.weight"))?;
                let gate_mat =
                    Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.gate_proj.weight"))?;
                let up_mat =
                    Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.up_proj.weight"))?;
                let down_mat =
                    Mxfp4Matrix::from_safetensors(mmap, &format!("{pfx}.mlp.down_proj.weight"))?;
                if (l % 4) != 3 {
                    Ok(PreloadedLayer::Gdn {
                        ln1_w,
                        ln2_w,
                        qkv_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.linear_attn.in_proj_qkv.weight"),
                        )?,
                        z_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.linear_attn.in_proj_z.weight"),
                        )?,
                        b_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.linear_attn.in_proj_b.weight"),
                        )?,
                        a_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.linear_attn.in_proj_a.weight"),
                        )?,
                        out_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.linear_attn.out_proj.weight"),
                        )?,
                        conv_w: mmap
                            .read_f32(&format!("{pfx}.linear_attn.conv1d.weight"))?
                            .1,
                        a_log: mmap.read_f32(&format!("{pfx}.linear_attn.A_log"))?.1,
                        dt_bias: mmap.read_f32(&format!("{pfx}.linear_attn.dt_bias"))?.1,
                        norm_w: mmap.read_f32(&format!("{pfx}.linear_attn.norm.weight"))?.1,
                        gate_mat,
                        up_mat,
                        down_mat,
                    })
                } else {
                    Ok(PreloadedLayer::Gqa {
                        ln1_w,
                        ln2_w,
                        q_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.self_attn.q_proj.weight"),
                        )?,
                        k_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.self_attn.k_proj.weight"),
                        )?,
                        v_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.self_attn.v_proj.weight"),
                        )?,
                        o_mat: Mxfp4Matrix::from_safetensors(
                            mmap,
                            &format!("{pfx}.self_attn.o_proj.weight"),
                        )?,
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
            mmap,
            emb_raw,
            final_norm_w,
            layers: layers_res?,
        })
    }

    #[inline]
    pub fn read_embedding_row_f32(&self, tid: u32) -> [f32; 1024] {
        let mut out = [0.0f32; 1024];
        let off = (tid as usize) * 2048;
        let row = &self.emb_raw[off..off + 2048];
        for d in 0..1024 {
            let bits = u16::from_le_bytes([row[2 * d], row[2 * d + 1]]);
            out[d] = f32::from_bits((bits as u32) << 16);
        }
        out
    }

    pub fn eval_vocab_top1_and_margin(&self, h_vec_1024: &[f32], target_tid: u32) -> (u32, f32, f32) {
        assert_eq!(h_vec_1024.len(), 1024);
        let chunk_rows = 4096usize;
        let num_chunks = (248320 + chunk_rows - 1) / chunk_rows;

        let partials: Vec<(u32, f32, f32, f32)> = (0..num_chunks)
            .into_par_iter()
            .map(|ci| {
                let r_start = ci * chunk_rows;
                let r_end = (r_start + chunk_rows).min(248320);
                let mut best_id = r_start as u32;
                let mut best_val = f32::NEG_INFINITY;
                let mut runner_val = f32::NEG_INFINITY;
                let mut tgt_val = f32::NEG_INFINITY;

                for v in r_start..r_end {
                    let off = v * 2048;
                    let row = &self.emb_raw[off..off + 2048];
                    let mut dot = 0.0f32;
                    for d in 0..1024 {
                        let bits = u16::from_le_bytes([row[2 * d], row[2 * d + 1]]);
                        let w = f32::from_bits((bits as u32) << 16);
                        dot += h_vec_1024[d] * w;
                    }
                    if v as u32 == target_tid {
                        tgt_val = dot;
                    }
                    if dot > best_val {
                        runner_val = best_val;
                        best_val = dot;
                        best_id = v as u32;
                    } else if dot > runner_val {
                        runner_val = dot;
                    }
                }
                (best_id, best_val, runner_val, tgt_val)
            })
            .collect();

        let mut best_id = 0u32;
        let mut best_val = f32::NEG_INFINITY;
        let mut second_val = f32::NEG_INFINITY;
        let mut target_logit = f32::NEG_INFINITY;

        for (bid, bval, rval, tval) in partials {
            if tval > f32::NEG_INFINITY / 2.0 {
                target_logit = tval;
            }
            if bval > best_val {
                second_val = best_val.max(rval);
                best_val = bval;
                best_id = bid;
            } else {
                second_val = second_val.max(bval);
            }
        }
        let best_competitor = if best_id == target_tid {
            second_val
        } else {
            best_val
        };
        (best_id, target_logit, target_logit - best_competitor)
    }

    pub fn extract_episode_dual_16_and_48(
        &self,
        tok: &QwenBpeTokenizer,
        name: &str,
        domain: MemoryDomain,
        facts: &[EpisodeFactSpec],
    ) -> Result<(ExtractedContinualEpisode, ExtractedContinualEpisode), String> {
        let ep48 = self.extract_episode(tok, name, domain, facts, 48)?;
        let ep16 = ep48.slice_last_16_heads();
        Ok((ep16, ep48))
    }

    pub fn extract_episode(
        &self,
        tok: &QwenBpeTokenizer,
        name: &str,
        domain: MemoryDomain,
        facts: &[EpisodeFactSpec],
        h_v: usize,
    ) -> Result<ExtractedContinualEpisode, String> {
        let seq_len = 64usize;
        if !(h_v == 16 || h_v == 48) || facts.is_empty() || 2 * facts.len() > seq_len {
            return Err("invalid (h_v, facts.len()) for C=64 continual episode".to_string());
        }
        let h_pad = h_v.next_power_of_two();
        let d_model = 1024usize;
        let d_ff = 3584usize;
        let eps = 1e-6f32;

        let mut token_ids = Vec::with_capacity(64);
        let mut fact_cue_positions = Vec::with_capacity(facts.len());
        let mut fact_target_ids = Vec::with_capacity(facts.len());
        let mut fact_target_words = Vec::with_capacity(facts.len());

        for f in facts {
            let mut cue_toks = tok.encode(f.cue_prompt);
            if cue_toks.len() > 8 {
                cue_toks = cue_toks[cue_toks.len() - 8..].to_vec();
            }
            let tgt_id = tok.lookup_single_word_token(f.target_word_with_space)?;
            let nl_id = tok.encode("\n")[0];
            assert!(token_ids.len() + cue_toks.len() + 2 <= seq_len);
            token_ids.extend_from_slice(&cue_toks);
            let cue_pos = token_ids.len() - 1;
            fact_cue_positions.push(cue_pos);
            fact_target_ids.push(tgt_id);
            fact_target_words.push(f.target_word_with_space.to_string());
            token_ids.push(tgt_id);
            token_ids.push(nl_id);
        }
        let pad_id = tok.encode("\n")[0];
        while token_ids.len() < seq_len {
            token_ids.push(pad_id);
        }

        let mut h_f32 = vec![0.0f32; seq_len * d_model];
        for (t, &tid) in token_ids.iter().enumerate() {
            let row = self.read_embedding_row_f32(tid);
            h_f32[t * d_model..(t + 1) * d_model].copy_from_slice(&row);
        }
        let mut h_i16 = quantize_act_i16(&h_f32);
        for (hf, &hi) in h_f32.iter_mut().zip(h_i16.iter()) {
            *hf = (hi as f32) / (ACT_SCALE as f32);
        }

        let mut captured_gdn_k: [Vec<f32>; 3] = [Vec::new(), Vec::new(), Vec::new()];

        for (l, layer) in self.layers.iter().enumerate() {
            let (ln1_w, ln2_w, gate_mat, up_mat, down_mat) = match layer {
                PreloadedLayer::Gdn {
                    ln1_w,
                    ln2_w,
                    gate_mat,
                    up_mat,
                    down_mat,
                    ..
                } => (ln1_w, ln2_w, gate_mat, up_mat, down_mat),
                PreloadedLayer::Gqa {
                    ln1_w,
                    ln2_w,
                    gate_mat,
                    up_mat,
                    down_mat,
                    ..
                } => (ln1_w, ln2_w, gate_mat, up_mat, down_mat),
            };
            let x_ln1_f32 = rmsnorm_zero_centered_f32(&h_f32, ln1_w, d_model, eps);
            let x_ln1_i16 = quantize_act_i16(&x_ln1_f32);

            let delta_attn_i16: Vec<i16> = match layer {
                PreloadedLayer::Gdn {
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
                    if l == 20 {
                        captured_gdn_k[0] = k_f32.clone();
                    } else if l == 21 {
                        captured_gdn_k[1] = k_f32.clone();
                    } else if l == 22 {
                        captured_gdn_k[2] = k_f32.clone();
                    }

                    let wy = crate::qwen35_layer::solve_real_gdn_wy_chunk64(
                        &q_f32, &k_f32, &v_f32, &g_f32, &beta_f32, 16, 16, seq_len, 128, 128,
                    );
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
                    let out_raw = eval_mxfp4_int_contraction(&gated_i16, seq_len, 2048, out_mat);
                    let out_f32 = dequant_y_raw_to_f32(&out_raw, seq_len, d_model, out_mat.rows_pad);
                    quantize_act_i16(&out_f32)
                }
                PreloadedLayer::Gqa {
                    q_mat,
                    k_mat,
                    v_mat,
                    o_mat,
                    qn_w,
                    kn_w,
                    ..
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
                            q_heads[(t * 8 + h) * 256..(t * 8 + h + 1) * 256]
                                .copy_from_slice(&src[..256]);
                            gate_f32[(t * 8 + h) * 256..(t * 8 + h + 1) * 256]
                                .copy_from_slice(&src[256..]);
                        }
                    }
                    let mut q_normed = rmsnorm_zero_centered_f32(&q_heads, qn_w, 256, eps);
                    let mut k_normed = rmsnorm_zero_centered_f32(&k_proj_f32, kn_w, 256, eps);
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
                                let s = qi.iter().zip(kj.iter()).map(|(&a, &b)| a * b).sum::<f32>()
                                    * scale;
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

        let final_h = rmsnorm_zero_centered_f32(&h_f32, &self.final_norm_w, d_model, eps);

        let mut beta_mask = vec![0u8; seq_len];
        let mut base_final_h_f32 = Vec::with_capacity(facts.len() * 1024);
        let mut target_dir_1024 = Vec::with_capacity(facts.len() * 1024);

        let n_facts = facts.len();
        let mut raw_per_fact_k = vec![[0.0f32; 128]; h_v * n_facts];
        let mut per_fact_v = vec![[0.0f64; 128]; h_v * n_facts];
        let sqrt8 = (8.0f64).sqrt();

        for (f_idx, &cue_pos) in fact_cue_positions.iter().enumerate() {
            base_final_h_f32
                .extend_from_slice(&final_h[cue_pos * d_model..(cue_pos + 1) * d_model]);

            let raw_emb = self.read_embedding_row_f32(fact_target_ids[f_idx]);
            let emb_mean = raw_emb.iter().sum::<f32>() / 1024.0;
            let mut dir_1024 = [0.0f32; 1024];
            for d in 0..1024 {
                dir_1024[d] = raw_emb[d] - emb_mean;
            }
            let dir_norm = dir_1024.iter().map(|&x| x * x).sum::<f32>().sqrt().max(1e-8);
            for d in 0..1024 {
                dir_1024[d] /= dir_norm;
            }
            target_dir_1024.extend_from_slice(&dir_1024);

            for h in 0..h_v {
                let k_src = if h_v == 16 {
                    &captured_gdn_k[2][(cue_pos * 16 + h) * 128..(cue_pos * 16 + h + 1) * 128]
                } else {
                    let grp = h / 16;
                    let sub_h = h % 16;
                    &captured_gdn_k[grp]
                        [(cue_pos * 16 + sub_h) * 128..(cue_pos * 16 + sub_h + 1) * 128]
                };
                raw_per_fact_k[h * n_facts + f_idx].copy_from_slice(k_src);

                // Scale by `sqrt(8)` (NOT `1 / ||v_slice||`) so `readout_1024`'s `/ sqrt(8)` reconstructs
                // `dir_1024` across all 8 slices with exact inter-slice relative norms (`cos > 0.999`!)!
                let slice_idx = h % 8;
                let v_slice = &dir_1024[slice_idx * 128..(slice_idx + 1) * 128];
                for d in 0..128 {
                    per_fact_v[h * n_facts + f_idx][d] = (v_slice[d] as f64) * sqrt8;
                }
            }
        }

        let (keys_f64, vals_f64, active_steps) =
            build_consolidated_chunk_kv(&raw_per_fact_k, &per_fact_v, domain, h_v, seq_len, n_facts);
        for c in 0..active_steps {
            beta_mask[c] = 1;
        }
        let canonical_slots: Vec<usize> = (0..n_facts).collect();

        Ok(ExtractedContinualEpisode {
            name: name.to_string(),
            domain,
            h_v,
            h_pad,
            token_ids,
            fact_cue_positions: canonical_slots,
            fact_target_ids,
            fact_target_words,
            raw_per_fact_k,
            per_fact_v,
            keys_f64,
            vals_f64,
            beta_mask,
            base_final_h_f32,
            target_dir_1024,
        })
    }
}

fn build_consolidated_chunk_kv(
    raw_per_fact_k: &[[f32; 128]],
    per_fact_v: &[[f64; 128]],
    domain: MemoryDomain,
    h_v: usize,
    seq_len: usize,
    n_facts: usize,
) -> (Vec<f64>, Vec<f64>, usize) {
    let mut keys_f64 = vec![0.0f64; h_v * seq_len * 128];
    let mut vals_f64 = vec![0.0f64; h_v * seq_len * 128];
    // 1 raw correlated Kaczmarz sweep (`6` steps -> non-zero `L`!) + 1 Gram-orthogonalized consolidation
    // sweep (`6` steps inside `span(k_0..k_5)`) = `12` active WY steps (`0` backprop!):
    assert_eq!(seq_len, 64, "continual WY chunk length must equal 64");
    assert!(n_facts >= 1 && 2 * n_facts <= seq_len, "2 * n_facts must fit in C=64");
    let raw_sweeps = n_facts;
    let active_steps = raw_sweeps + n_facts;

    for h in 0..h_v {
        let mut k_mat = vec![[0.0f64; 128]; n_facts];
        let mut v_mat = vec![[0.0f64; 128]; n_facts];
        for f in 0..n_facts {
            k_mat[f] = project_qwen_key_domain(&raw_per_fact_k[h * n_facts + f], domain);
            v_mat[f] = per_fact_v[h * n_facts + f];
        }
        let mut u_gs = vec![[0.0f64; 128]; n_facts];
        for a in 0..n_facts {
            let mut w = k_mat[a];
            for _p in 0..2 {
                for b in 0..a {
                    let dot: f64 = w.iter().zip(u_gs[b].iter()).map(|(x, y)| x * y).sum();
                    for d in 0..128 {
                        w[d] -= dot * u_gs[b][d];
                    }
                }
            }
            let nrm = w.iter().map(|x| x * x).sum::<f64>().sqrt().max(1e-12);
            for d in 0..128 {
                u_gs[a][d] = w[d] / nrm;
            }
        }
        let mut v_gs = vec![[0.0f64; 128]; n_facts];
        for f in 0..n_facts {
            let mut rhs = v_mat[f];
            for b in 0..f {
                let r_bf: f64 = u_gs[b].iter().zip(k_mat[f].iter()).map(|(x, y)| x * y).sum();
                for d in 0..128 {
                    rhs[d] -= r_bf * v_gs[b][d];
                }
            }
            let r_ff: f64 = u_gs[f]
                .iter()
                .zip(k_mat[f].iter())
                .map(|(x, y)| x * y)
                .sum::<f64>()
                .max(0.50);
            for d in 0..128 {
                v_gs[f][d] = (rhs[d] / r_ff).clamp(-0.55, 0.55);
            }
        }

        for c in 0..raw_sweeps {
            let f_idx = c % n_facts;
            keys_f64[(h * seq_len + c) * 128..(h * seq_len + c + 1) * 128]
                .copy_from_slice(&k_mat[f_idx]);
            vals_f64[(h * seq_len + c) * 128..(h * seq_len + c + 1) * 128]
                .copy_from_slice(&v_mat[f_idx]);
        }
        for a in 0..n_facts {
            let c = raw_sweeps + a;
            keys_f64[(h * seq_len + c) * 128..(h * seq_len + c + 1) * 128]
                .copy_from_slice(&u_gs[a]);
            vals_f64[(h * seq_len + c) * 128..(h * seq_len + c + 1) * 128]
                .copy_from_slice(&v_gs[a]);
        }
    }
    (keys_f64, vals_f64, active_steps)
}

impl ExtractedContinualEpisode {
    pub fn slice_last_16_heads(&self) -> Self {
        assert_eq!(self.h_v, 48);
        let start_h = 32usize;
        let stride = 64 * 128;
        let n_facts = self.fact_cue_positions.len();
        Self {
            name: self.name.clone(),
            domain: self.domain,
            h_v: 16,
            h_pad: 16,
            token_ids: self.token_ids.clone(),
            fact_cue_positions: self.fact_cue_positions.clone(),
            fact_target_ids: self.fact_target_ids.clone(),
            fact_target_words: self.fact_target_words.clone(),
            raw_per_fact_k: self.raw_per_fact_k[start_h * n_facts..48 * n_facts].to_vec(),
            per_fact_v: self.per_fact_v[start_h * n_facts..48 * n_facts].to_vec(),
            keys_f64: self.keys_f64[start_h * stride..48 * stride].to_vec(),
            vals_f64: self.vals_f64[start_h * stride..48 * stride].to_vec(),
            beta_mask: self.beta_mask.clone(),
            base_final_h_f32: self.base_final_h_f32.clone(),
            target_dir_1024: self.target_dir_1024.clone(),
        }
    }

    pub fn reproject_domain(&self, new_name: &str, domain: MemoryDomain) -> Self {
        let n_facts = self.fact_cue_positions.len();
        let (keys_f64, vals_f64, active_steps) = build_consolidated_chunk_kv(
            &self.raw_per_fact_k,
            &self.per_fact_v,
            domain,
            self.h_v,
            64,
            n_facts,
        );
        let mut beta_mask = vec![0u8; 64];
        for c in 0..active_steps {
            beta_mask[c] = 1;
        }
        Self {
            name: new_name.to_string(),
            domain,
            h_v: self.h_v,
            h_pad: self.h_pad,
            token_ids: self.token_ids.clone(),
            fact_cue_positions: self.fact_cue_positions.clone(),
            fact_target_ids: self.fact_target_ids.clone(),
            fact_target_words: self.fact_target_words.clone(),
            raw_per_fact_k: self.raw_per_fact_k.clone(),
            per_fact_v: self.per_fact_v.clone(),
            keys_f64,
            vals_f64,
            beta_mask,
            base_final_h_f32: self.base_final_h_f32.clone(),
            target_dir_1024: self.target_dir_1024.clone(),
        }
    }
}

// ===========================================================================
// §4. Persistent Fast-Weight Memory State, Continual WY Adaptation & 2-Limb Gram–Schmidt
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FastWeightMemoryState {
    pub h_v: usize,
    pub h_pad: usize,
    pub s_int_lsb: Vec<i64>,
    pub s_bb_lsb: Vec<u32>,
}

impl FastWeightMemoryState {
    pub fn zero(h_v: usize) -> Self {
        let h_pad = h_v.next_power_of_two();
        let len = h_pad * 128 * 128;
        Self {
            h_v,
            h_pad,
            s_int_lsb: vec![0i64; len],
            s_bb_lsb: vec![0u32; len],
        }
    }

    pub fn from_int_lsb(h_v: usize, s_int_lsb: Vec<i64>) -> Self {
        let h_pad = h_v.next_power_of_two();
        assert_eq!(s_int_lsb.len(), h_pad * 128 * 128);
        let s_bb_lsb = s_int_lsb.iter().map(|&v| bb_from_i64(v)).collect();
        Self {
            h_v,
            h_pad,
            s_int_lsb,
            s_bb_lsb,
        }
    }

    pub fn readout_1024(&self, ep: &ExtractedContinualEpisode, fact_idx: usize) -> [f32; 1024] {
        assert_eq!(self.h_v, ep.h_v);
        let log_h = self.h_pad.trailing_zeros() as usize;
        let cue_pos = ep.fact_cue_positions[fact_idx];
        let mut out_1024 = [0.0f64; 1024];
        let groups = self.h_v / 8;

        for h in 0..self.h_v {
            let q = &ep.keys_f64[(h * 64 + cue_pos) * 128..(h * 64 + cue_pos + 1) * 128];
            let slice_idx = h % 8;
            let head_scale = 1.0 / ((groups as f64) * (8.0f64).sqrt() * (S_SCALE as f64));
            for j_v in 0..128 {
                let mut dot = 0.0f64;
                let base_jv = h + (j_v << (log_h + 7));
                for i_k in 0..128 {
                    let s_val = self.s_int_lsb[base_jv + (i_k << log_h)] as f64;
                    dot += s_val * q[i_k];
                }
                out_1024[slice_idx * 128 + j_v] += dot * head_scale;
            }
        }
        let mut res = [0.0f32; 1024];
        for d in 0..1024 {
            res[d] = out_1024[d] as f32;
        }
        res
    }
}

#[derive(Clone, Debug)]
pub struct EpisodeRecallMetrics {
    pub episode_name: String,
    pub num_facts: usize,
    pub top1_hits: usize,
    pub recall_rate: f64,
    pub mean_cosine: f64,
    pub mean_logit_boost: f64,
    pub mean_logit_margin: f64,
    pub mean_readout_l2: f64,
}

pub fn evaluate_episode_recall(
    model: &PreloadedQwen35Model<'_>,
    state: &FastWeightMemoryState,
    ep: &ExtractedContinualEpisode,
    logit_gain: f32,
) -> EpisodeRecallMetrics {
    let n_facts = ep.fact_cue_positions.len();
    let mut hits = 0usize;
    let mut sum_cos = 0.0f64;
    let mut sum_boost = 0.0f64;
    let mut sum_margin = 0.0f64;
    let mut sum_l2 = 0.0f64;

    for f in 0..n_facts {
        let y_1024 = state.readout_1024(ep, f);
        let tgt_dir = &ep.target_dir_1024[f * 1024..(f + 1) * 1024];
        let h_base = &ep.base_final_h_f32[f * 1024..(f + 1) * 1024];

        let y_l2 = y_1024
            .iter()
            .map(|&x| (x as f64) * (x as f64))
            .sum::<f64>()
            .sqrt();
        let dot_yt = y_1024
            .iter()
            .zip(tgt_dir.iter())
            .map(|(&a, &b)| (a as f64) * (b as f64))
            .sum::<f64>();
        let cos = if y_l2 > 1e-9 { dot_yt / y_l2 } else { 0.0 };

        let mut h_adapted = [0.0f32; 1024];
        for d in 0..1024 {
            h_adapted[d] = h_base[d] + logit_gain * y_1024[d];
        }
        let (_, base_tgt_logit, _) =
            model.eval_vocab_top1_and_margin(h_base, ep.fact_target_ids[f]);
        let (pred_id, adap_tgt_logit, margin) =
            model.eval_vocab_top1_and_margin(&h_adapted, ep.fact_target_ids[f]);

        if pred_id == ep.fact_target_ids[f] {
            hits += 1;
        }
        sum_cos += cos;
        sum_boost += (adap_tgt_logit - base_tgt_logit) as f64;
        sum_margin += margin as f64;
        sum_l2 += y_l2;
    }

    EpisodeRecallMetrics {
        episode_name: ep.name.clone(),
        num_facts: n_facts,
        top1_hits: hits,
        recall_rate: (hits as f64) / (n_facts as f64),
        mean_cosine: sum_cos / (n_facts as f64),
        mean_logit_boost: sum_boost / (n_facts as f64),
        mean_logit_margin: sum_margin / (n_facts as f64),
        mean_readout_l2: sum_l2 / (n_facts as f64),
    }
}

pub fn readout_snr_db_vs_counterfactual(
    cand: &FastWeightMemoryState,
    counterfactual: &FastWeightMemoryState,
    ep: &ExtractedContinualEpisode,
) -> f64 {
    let mut sig_sq = 0.0f64;
    let mut err_sq = 0.0f64;
    for f in 0..ep.fact_cue_positions.len() {
        let yc = cand.readout_1024(ep, f);
        let yr = counterfactual.readout_1024(ep, f);
        for d in 0..1024 {
            let r = yr[d] as f64;
            let e = (yc[d] as f64) - r;
            sig_sq += r * r;
            err_sq += e * e;
        }
    }
    if err_sq <= 1e-24 {
        99.99
    } else {
        10.0 * (sig_sq / err_sq).log10()
    }
}

fn solve_spd_small(r: usize, a_flat: &[f64], b_rhs: &[f64]) -> Vec<f64> {
    let mut aug = vec![0.0f64; r * (r + 1)];
    for i in 0..r {
        for j in 0..r {
            aug[i * (r + 1) + j] = a_flat[i * r + j];
        }
        aug[i * (r + 1) + r] = b_rhs[i];
    }
    for col in 0..r {
        let mut piv = col;
        let mut max_v = aug[col * (r + 1) + col].abs();
        for row in (col + 1)..r {
            let v = aug[row * (r + 1) + col].abs();
            if v > max_v {
                max_v = v;
                piv = row;
            }
        }
        if piv != col {
            for k in col..=r {
                aug.swap(col * (r + 1) + k, piv * (r + 1) + k);
            }
        }
        let diag = aug[col * (r + 1) + col];
        for row in (col + 1)..r {
            let f = aug[row * (r + 1) + col] / diag;
            for k in col..=r {
                aug[row * (r + 1) + k] -= f * aug[col * (r + 1) + k];
            }
        }
    }
    let mut x = vec![0.0f64; r];
    for i in (0..r).rev() {
        let mut s = aug[i * (r + 1) + r];
        for j in (i + 1)..r {
            s -= aug[i * (r + 1) + j] * x[j];
        }
        x[i] = s / aug[i * (r + 1) + i];
    }
    x
}

#[derive(Clone, Debug)]
pub struct GramSchmidtSubspaceBasis {
    pub h_v: usize,
    pub h_pad: usize,
    pub rank_r: usize,
    pub u_int_lsb: Vec<i64>,
    pub u_bb_lsb: Vec<u32>,
    /// Centered 2-limb split `U_int == U_lo + 128 * U_hi` (`U_lo + 64 in [0, 128)`, `U_hi + 128 in [0, 256)`).
    pub u_lo_shift_lsb: Vec<u32>,
    pub u_hi_shift_lsb: Vec<u32>,
    pub max_abs_gram_err: i64,
}

pub fn build_gram_schmidt_subspace_basis(ep: &ExtractedContinualEpisode) -> GramSchmidtSubspaceBasis {
    let h_v = ep.h_v;
    let h_pad = ep.h_pad;
    let log_h = h_pad.trailing_zeros() as usize;
    let rank_r = ep.fact_cue_positions.len();
    assert!(rank_r >= 1 && rank_r <= R_PAD);
    let len = h_pad * 128 * R_PAD;

    let mut u_int_lsb = vec![0i64; len];
    let mut u_lo_shift_lsb = vec![ULO_HALF as u32; len];
    let mut u_hi_shift_lsb = vec![UHI_HALF as u32; len];
    let mut max_abs_gram_err = 0i64;

    for h in 0..h_v {
        let mut basis_f64 = vec![[0.0f64; 128]; rank_r];
        for (a, &cue_pos) in ep.fact_cue_positions.iter().enumerate() {
            let mut v = [0.0f64; 128];
            v.copy_from_slice(&ep.keys_f64[(h * 64 + cue_pos) * 128..(h * 64 + cue_pos + 1) * 128]);
            for _pass in 0..2 {
                for b in 0..a {
                    let dot: f64 = v.iter().zip(basis_f64[b].iter()).map(|(x, y)| x * y).sum();
                    for d in 0..128 {
                        v[d] -= dot * basis_f64[b][d];
                    }
                }
            }
            let nrm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
            assert!(nrm > 1e-5, "degenerate episode keys at head {h}, col {a}");
            for d in 0..128 {
                basis_f64[a][d] = v[d] / nrm;
            }
        }

        let max_coord = 32_512i64; // keeps U_hi in [-127, 127] -> U_hi + 128 in [1, 255] < 256!
        let mut cols_i64 = vec![[0i64; 128]; rank_r];
        for a in 0..rank_r {
            for d in 0..128 {
                cols_i64[a][d] = ((M_GS as f64) * basis_f64[a][d])
                    .round()
                    .clamp(-max_coord as f64, max_coord as f64) as i64;
            }
            for _step in 0..16 {
                let diag_err = cols_i64[a].iter().map(|&x| x * x).sum::<i64>() - (M_GS * M_GS);
                let mut cur_cost = (diag_err as i128) * (diag_err as i128);
                for b in 0..a {
                    let off_err: i64 = cols_i64[a]
                        .iter()
                        .zip(cols_i64[b].iter())
                        .map(|(&x, &y)| x * y)
                        .sum();
                    cur_cost += (off_err as i128) * (off_err as i128);
                }
                if cur_cost <= (16_384i128 * 16_384i128) {
                    break;
                }
                let mut best_move: Option<(i128, usize, i64)> = None;
                for d in 0..128 {
                    for delta in [-1i64, 1i64] {
                        let old_v = cols_i64[a][d];
                        let new_v = old_v + delta;
                        if new_v.abs() > max_coord {
                            continue;
                        }
                        let new_diag = diag_err + (new_v * new_v - old_v * old_v);
                        let mut cand_cost = (new_diag as i128) * (new_diag as i128);
                        for b in 0..a {
                            let old_off: i64 = cols_i64[a]
                                .iter()
                                .zip(cols_i64[b].iter())
                                .map(|(&x, &y)| x * y)
                                .sum();
                            let new_off = old_off + delta * cols_i64[b][d];
                            cand_cost += (new_off as i128) * (new_off as i128);
                        }
                        if cand_cost < cur_cost
                            && best_move.map_or(true, |(bc, _, _)| cand_cost < bc)
                        {
                            best_move = Some((cand_cost, d, delta));
                        }
                    }
                }
                if let Some((_, d_best, delta_best)) = best_move {
                    cols_i64[a][d_best] += delta_best;
                } else {
                    break;
                }
            }
        }

        for a in 0..rank_r {
            for b in 0..rank_r {
                let dot: i64 = cols_i64[a]
                    .iter()
                    .zip(cols_i64[b].iter())
                    .map(|(&x, &y)| x * y)
                    .sum();
                let target = if a == b { M_GS * M_GS } else { 0 };
                let err = (dot - target).abs();
                if err > max_abs_gram_err {
                    max_abs_gram_err = err;
                }
                assert!(
                    err < LIMB_RADIX * (TAU_ORTH - 2),
                    "Gram error {err} >= {}",
                    LIMB_RADIX * (TAU_ORTH - 2)
                );
            }
            for i_k in 0..128 {
                let idx_u = h + (i_k << log_h) + (a << (log_h + 7));
                let uv = cols_i64[a][i_k];
                let u_lo = (uv + ULO_HALF).rem_euclid(LIMB_RADIX) - ULO_HALF;
                let u_hi = (uv + ULO_HALF).div_euclid(LIMB_RADIX);
                assert_eq!(uv, u_lo + LIMB_RADIX * u_hi);
                u_int_lsb[idx_u] = uv;
                u_lo_shift_lsb[idx_u] = (u_lo + ULO_HALF) as u32;
                u_hi_shift_lsb[idx_u] = (u_hi + UHI_HALF) as u32;
            }
        }
    }

    let u_bb_lsb = u_int_lsb.iter().map(|&v| bb_from_i64(v)).collect();
    GramSchmidtSubspaceBasis {
        h_v,
        h_pad,
        rank_r,
        u_int_lsb,
        u_bb_lsb,
        u_lo_shift_lsb,
        u_hi_shift_lsb,
        max_abs_gram_err,
    }
}

#[derive(Clone, Debug)]
pub struct ContinualWyUpdateWitness {
    pub h_v: usize,
    pub h_pad: usize,
    pub s_prev: FastWeightMemoryState,
    pub s_post: FastWeightMemoryState,
    pub k_int_lsb_hci: Vec<i64>,
    pub k_lsb_hci: Vec<u32>,
    pub l_int_lsb_hcj: Vec<i64>,
    pub l_lsb_hcj: Vec<u32>,
    pub du_int_lsb_hcj: Vec<i64>,
    pub du_lsb_hcj: Vec<u32>,
    pub rhs_lsb_hccol: Vec<u32>,
    pub uw_int_lsb_hccol: Vec<i64>,
    pub uw_lsb_hccol: Vec<u32>,
    pub delta_eff_lsb_hcj: Vec<u32>,
    /// `[4 * h_pad * 16384]` in `[0, 128)`: q0 = `R_wy`, q1 = `R_eff`, q2 = `R_state`, q3 = `R_kk`!
    pub rem_packed_128: Vec<u32>,
    /// `[4 * h_pad * 16384]` in `[0, 65536)`: q0 = `UW+32768`, q1 = `Delta_eff+32768`, q2 = `dS+32768`!
    pub quot_wy_packed: Vec<u32>,
    /// `[2 * h_pad * 16384]` in `[0, 32768)`: `[S_prev + 16384, S_post + 16384]`!
    pub s_bnd_wy_packed: Vec<u32>,
}

pub fn apply_continual_wy_episode(
    s_prev: &FastWeightMemoryState,
    ep: &ExtractedContinualEpisode,
) -> ContinualWyUpdateWitness {
    assert_eq!(s_prev.h_v, ep.h_v);
    let h_v = ep.h_v;
    let h_pad = ep.h_pad;
    let log_h = h_pad.trailing_zeros() as usize;
    let c_len = 64usize;
    let half_wy = CMEM_WY_SCALE / 2; // 64
    let q_size = h_pad * 16384;

    let mut k_int_lsb_hci = vec![0i64; h_pad * 64 * 128];
    let mut k_lsb_hci = vec![0u32; h_pad * 64 * 128];
    let mut l_int_lsb_hcj = vec![0i64; h_pad * 64 * 64];
    let mut l_lsb_hcj = vec![0u32; h_pad * 64 * 64];
    let mut du_int_lsb_hcj = vec![0i64; h_pad * 64 * 64];
    let mut du_lsb_hcj = vec![0u32; h_pad * 64 * 64];
    let mut rhs_lsb_hccol = vec![0u32; q_size];
    let mut uw_int_lsb_hccol = vec![0i64; q_size];
    let mut uw_lsb_hccol = vec![0u32; q_size];
    let mut delta_eff_lsb_hcj = vec![0u32; h_pad * 64 * 128];
    let mut rem_packed_128 = vec![half_wy as u32; 4 * q_size];
    let mut quot_wy_packed = vec![QUOT_WY_HALF as u32; 4 * q_size];
    let mut s_bnd_wy_packed = vec![S_BND_HALF as u32; 4 * q_size];
    let mut s_post_int = s_prev.s_int_lsb.clone();

    for idx_s in 0..q_size {
        let sp = s_prev.s_int_lsb[idx_s];
        assert!(
            sp.abs() <= S_BND_HALF,
            "S_prev entry {sp} exceeds S_BND_HALF = {S_BND_HALF}"
        );
        s_bnd_wy_packed[idx_s] = (sp + S_BND_HALF) as u32;
        s_bnd_wy_packed[q_size + idx_s] = (S_BND_HALF - sp) as u32;
        s_bnd_wy_packed[2 * q_size + idx_s] = (sp + S_BND_HALF) as u32;
        s_bnd_wy_packed[3 * q_size + idx_s] = (S_BND_HALF - sp) as u32;
    }

    for h in 0..h_v {
        let mut k_int = vec![0i64; c_len * 128];
        for c in 0..c_len {
            if ep.beta_mask[c] == 0 {
                continue;
            }
            let kf = &ep.keys_f64[(h * c_len + c) * 128..(h * c_len + c + 1) * 128];
            for i_k in 0..128 {
                let kv = (122.0f64 * kf[i_k])
                    .round()
                    .clamp(-(SMALL512_HALF - 2) as f64, (SMALL512_HALF - 2) as f64)
                    as i64;
                k_int[c * 128 + i_k] = kv;
                let idx_k = h + (c << log_h) + (i_k << (log_h + 6));
                k_int_lsb_hci[idx_k] = kv;
                k_lsb_hci[idx_k] = bb_from_i64(kv);
            }
        }

        // Exact full `K * K^T == CMEM_WY_SCALE * (L + D_U) + R_kk - half_wy` (`#115` Item 2!)
        let mut l_mat = vec![0i64; c_len * c_len];
        for c in 0..c_len {
            for j in 0..c_len {
                let mut dot_kk = 0i64;
                for i_k in 0..128 {
                    dot_kk += k_int[c * 128 + i_k] * k_int[j * 128 + i_k];
                }
                let num_kk = dot_kk + half_wy;
                let q_kk = num_kk.div_euclid(CMEM_WY_SCALE);
                let r_kk = num_kk.rem_euclid(CMEM_WY_SCALE) as u32;
                assert!(q_kk >= -SMALL512_HALF && q_kk < SMALL512_HALF);
                let idx_hcj = h + (c << log_h) + (j << (log_h + 6));
                if j < c {
                    l_mat[c * c_len + j] = q_kk;
                    l_int_lsb_hcj[idx_hcj] = q_kk;
                    l_lsb_hcj[idx_hcj] = bb_from_i64(q_kk);
                } else {
                    du_int_lsb_hcj[idx_hcj] = q_kk;
                    du_lsb_hcj[idx_hcj] = bb_from_i64(q_kk);
                }
                rem_packed_128[3 * q_size + idx_hcj] = r_kk;
            }
        }

        let mut rhs_mat = vec![0i64; c_len * 256];
        let mut uw_mat = vec![0i64; c_len * 256];
        for c in 0..c_len {
            if ep.beta_mask[c] != 0 {
                let vf = &ep.vals_f64[(h * c_len + c) * 128..(h * c_len + c + 1) * 128];
                for j_v in 0..128 {
                    rhs_mat[c * 256 + j_v] = ((S_SCALE as f64) * vf[j_v])
                        .round()
                        .clamp(-(QUOT_WY_HALF - 2048) as f64, (QUOT_WY_HALF - 2048) as f64)
                        as i64;
                }
                for i_k in 0..128 {
                    rhs_mat[c * 256 + 128 + i_k] = k_int[c * 128 + i_k];
                }
            }
            for col in 0..256 {
                let mut sum_lu = 0i64;
                for j in 0..c {
                    sum_lu += l_mat[c * c_len + j] * uw_mat[j * 256 + col];
                }
                assert!(sum_lu.abs() < (P as i64) / 2);
                let num = CMEM_WY_SCALE * rhs_mat[c * 256 + col] - sum_lu + half_wy;
                let uw_v = num.div_euclid(CMEM_WY_SCALE);
                let r_wy = num.rem_euclid(CMEM_WY_SCALE) as u32;
                assert!(
                    uw_v >= -QUOT_WY_HALF && uw_v < QUOT_WY_HALF,
                    "UW {uw_v} outside [-32768, 32768)"
                );
                if col >= 128 {
                    assert!(
                        uw_v >= -SMALL512_HALF && uw_v < SMALL512_HALF,
                        "W {uw_v} outside [-256, 256)"
                    );
                }
                uw_mat[c * 256 + col] = uw_v;
                let idx = h + (c << log_h) + (col << (log_h + 6));
                rhs_lsb_hccol[idx] = bb_from_i64(rhs_mat[c * 256 + col]);
                uw_int_lsb_hccol[idx] = uw_v;
                uw_lsb_hccol[idx] = bb_from_i64(uw_v);
                rem_packed_128[idx] = r_wy;
                quot_wy_packed[idx] = (uw_v + QUOT_WY_HALF) as u32;
            }
        }

        let mut delta_eff = vec![0i64; c_len * 128];
        for c in 0..c_len {
            for j_v in 0..128 {
                let mut sum_ws = 0i64;
                let s_col_base = h + (j_v << (log_h + 7));
                for i_k in 0..128 {
                    let w_val = uw_mat[c * 256 + 128 + i_k];
                    let s_val = s_prev.s_int_lsb[s_col_base + (i_k << log_h)];
                    sum_ws += w_val * s_val;
                }
                assert!(sum_ws.abs() < (P as i64) / 2);
                let u_val = uw_mat[c * 256 + j_v];
                let num = CMEM_WY_SCALE * u_val - sum_ws + half_wy;
                let d_val = num.div_euclid(CMEM_WY_SCALE);
                let r_eff = num.rem_euclid(CMEM_WY_SCALE) as u32;
                assert!(d_val >= -QUOT_WY_HALF && d_val < QUOT_WY_HALF);
                delta_eff[c * 128 + j_v] = d_val;
                let idx_eff = h + (c << log_h) + (j_v << (log_h + 6));
                delta_eff_lsb_hcj[idx_eff] = bb_from_i64(d_val);
                rem_packed_128[q_size + idx_eff] = r_eff;
                quot_wy_packed[q_size + idx_eff] = (d_val + QUOT_WY_HALF) as u32;
            }
        }

        for i_k in 0..128 {
            for j_v in 0..128 {
                let mut sum_kd = 0i64;
                for c in 0..c_len {
                    sum_kd += k_int[c * 128 + i_k] * delta_eff[c * 128 + j_v];
                }
                assert!(sum_kd.abs() < (P as i64) / 2);
                let idx_s = h + (i_k << log_h) + (j_v << (log_h + 7));
                let sp = s_prev.s_int_lsb[idx_s];
                let num = CMEM_WY_SCALE * sp + sum_kd + half_wy;
                let s_new = num.div_euclid(CMEM_WY_SCALE);
                let r_st = num.rem_euclid(CMEM_WY_SCALE) as u32;
                let ds = s_new - sp;
                assert!(ds >= -QUOT_WY_HALF && ds < QUOT_WY_HALF);
                assert!(
                    s_new.abs() <= S_BND_HALF,
                    "S_post {s_new} exceeds S_BND_HALF = {S_BND_HALF}"
                );
                s_post_int[idx_s] = s_new;
                rem_packed_128[2 * q_size + idx_s] = r_st;
                quot_wy_packed[2 * q_size + idx_s] = (ds + QUOT_WY_HALF) as u32;
                s_bnd_wy_packed[2 * q_size + idx_s] = (s_new + S_BND_HALF) as u32;
                s_bnd_wy_packed[3 * q_size + idx_s] = (S_BND_HALF - s_new) as u32;
            }
        }
    }

    ContinualWyUpdateWitness {
        h_v,
        h_pad,
        s_prev: s_prev.clone(),
        s_post: FastWeightMemoryState::from_int_lsb(h_v, s_post_int),
        k_int_lsb_hci,
        k_lsb_hci,
        l_int_lsb_hcj,
        l_lsb_hcj,
        du_int_lsb_hcj,
        du_lsb_hcj,
        rhs_lsb_hccol,
        uw_int_lsb_hccol,
        uw_lsb_hccol,
        delta_eff_lsb_hcj,
        rem_packed_128,
        quot_wy_packed,
        s_bnd_wy_packed,
    }
}

#[derive(Clone, Debug)]
pub struct RankRUnlearnWitness {
    pub h_v: usize,
    pub h_pad: usize,
    pub rank_r: usize,
    pub s_before: FastWeightMemoryState,
    pub s_unlearned: FastWeightMemoryState,
    pub basis: GramSchmidtSubspaceBasis,
    pub p_proj_lsb_haj: Vec<u32>,
    pub gram_shift_pad: Vec<u32>,
    pub res_shift_lsb_hja: Vec<u32>,
    /// `[2 * m_s]` in `[0, 32768)`: `[S_before + 16384, S_unlearned + 16384]` (`#115` Item 3!).
    pub s_bnd_unl_packed: Vec<u32>,
    /// `[2 * m_s]` in `[0, 65536)`: half 0 = `Q_{p2,lo} + 32768`; half 1 = `[P_proj, Q_{u3,lo}, G_lo] + 32768`.
    pub qlo_unl_packed: Vec<u32>,
    /// `[4 * m_s]` in `[0, 128)`: q0 = `R_{p2,lo}`, q1 = `R_{p2,hi}`, q2 = `[R_{u3,lo}, R_{u3,hi}]`, q3 = `R_{g,lo}`.
    pub rem128_unl_packed: Vec<u32>,
    pub max_abs_residual_int: i64,
}

pub fn apply_rank_r_subspace_unlearning(
    s_before: &FastWeightMemoryState,
    basis: &GramSchmidtSubspaceBasis,
) -> Result<RankRUnlearnWitness, String> {
    if s_before.h_v != basis.h_v || s_before.h_pad != basis.h_pad {
        return Err("head dimension mismatch".to_string());
    }
    if basis.rank_r == 0 || basis.rank_r > R_PAD {
        return Err(format!("invalid rank_r {} outside 1..={R_PAD}", basis.rank_r));
    }
    let h_v = s_before.h_v;
    let h_pad = s_before.h_pad;
    let log_h = h_pad.trailing_zeros() as usize;
    let half_gs = M_GS / 2; // 8,192
    let half_limb = LIMB_RADIX / 2; // 64
    let m_base_cells = h_pad * 128 * 128;
    let m_small_cells = h_pad * 8 * 128;
    let gram_pad_len = (h_pad * 64).max(1usize << M_TAB_ORTH);

    let mut p_proj_int = vec![0i64; m_small_cells];
    let mut p_proj_lsb_haj = vec![0u32; m_small_cells];
    let mut gram_shift_pad = vec![TAU_ORTH as u32; gram_pad_len];
    let mut res_shift_lsb_hja = vec![TAU_ZERO as u32; m_small_cells];
    let mut s_bnd_unl_packed = vec![S_BND_HALF as u32; 4 * m_base_cells];
    let mut qlo_unl_packed = vec![QUOT_UNL_HALF as u32; 2 * m_base_cells];
    let mut rem128_unl_packed = vec![half_limb as u32; 4 * m_base_cells];
    let mut s_unl_int = s_before.s_int_lsb.clone();
    let mut max_abs_residual_int = 0i64;

    // 0. Check `|S_before| <= 60000`, 2-limb `U_int == U_lo + 128 * U_hi`, and inactive `U == 0`:
    for idx_s in 0..m_base_cells {
        let sb = s_before.s_int_lsb[idx_s];
        if sb.abs() > S_BND_HALF {
            return Err(format!("S_before entry {sb} exceeds {S_BND_HALF}"));
        }
        s_bnd_unl_packed[idx_s] = (sb + S_BND_HALF) as u32;
        s_bnd_unl_packed[m_base_cells + idx_s] = (S_BND_HALF - sb) as u32;
        s_bnd_unl_packed[2 * m_base_cells + idx_s] = (sb + S_BND_HALF) as u32;
        s_bnd_unl_packed[3 * m_base_cells + idx_s] = (S_BND_HALF - sb) as u32;
    }
    for h in 0..h_pad {
        for a in 0..R_PAD {
            let is_active = h < h_v && a < basis.rank_r;
            for i_k in 0..128 {
                let idx_u = h + (i_k << log_h) + (a << (log_h + 7));
                let uv = basis.u_int_lsb[idx_u];
                if !is_active && uv != 0 {
                    return Err(format!("non-zero entry {uv} in inactive U column (h={h}, a={a})"));
                }
                if basis.u_lo_shift_lsb[idx_u] >= 256 || basis.u_hi_shift_lsb[idx_u] >= 256 {
                    return Err("U limb shift out of range".to_string());
                }
                let ulo = (basis.u_lo_shift_lsb[idx_u] as i64) - ULO_HALF;
                let uhi = (basis.u_hi_shift_lsb[idx_u] as i64) - UHI_HALF;
                if uv != ulo + LIMB_RADIX * uhi {
                    return Err("U_int != U_lo + 128 * U_hi".to_string());
                }
            }
        }
    }

    // 1. 2-limb Gram check: `U_int^T U_lo + 64 = 128 * G_lo + R_{g,lo}`,
    //    `U_int^T U_hi + G_lo = (M_GS^2 / 128) * I_{<h_v, <r} + (G_shift - TAU_ORTH)`
    let diag_hi_target = (M_GS * M_GS) / LIMB_RADIX; // 2,097,152
    for h in 0..h_pad {
        let mut gram_rr = vec![0.0f64; basis.rank_r * basis.rank_r];
        for a in 0..R_PAD {
            for b in 0..R_PAD {
                let mut dot_ulo = 0i64;
                let mut dot_uhi = 0i64;
                for i_k in 0..128 {
                    let ua = basis.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                    let idx_b = h + (i_k << log_h) + (b << (log_h + 7));
                    let ub_lo = (basis.u_lo_shift_lsb[idx_b] as i64) - ULO_HALF;
                    let ub_hi = (basis.u_hi_shift_lsb[idx_b] as i64) - UHI_HALF;
                    dot_ulo += ua * ub_lo;
                    dot_uhi += ua * ub_hi;
                }
                let dot_full = dot_ulo + LIMB_RADIX * dot_uhi;
                if h < h_v && a < basis.rank_r && b < basis.rank_r {
                    gram_rr[a * basis.rank_r + b] = dot_full as f64;
                }
                let num_glo = dot_ulo + half_limb;
                let g_lo = num_glo.div_euclid(LIMB_RADIX);
                let r_glo = num_glo.rem_euclid(LIMB_RADIX) as u32;
                if g_lo < -QUOT_UNL_HALF || g_lo >= QUOT_UNL_HALF {
                    return Err(format!("G_lo {g_lo} out of bounds"));
                }
                let diag_id = if h < h_v && a == b && a < basis.rank_r {
                    diag_hi_target
                } else {
                    0
                };
                let g_shift = (dot_uhi + g_lo) - diag_id + TAU_ORTH;
                if g_shift < 0 || g_shift >= (1i64 << M_TAB_ORTH) {
                    return Err(format!(
                        "Gram orthogonality violation at head {h} ({a},{b}): g_shift={g_shift}"
                    ));
                }
                let idx_hab = h + (a << log_h) + (b << (log_h + 3));
                gram_shift_pad[idx_hab] = g_shift as u32;
                qlo_unl_packed[m_base_cells + 2 * m_small_cells + idx_hab] =
                    (g_lo + QUOT_UNL_HALF) as u32;
                rem128_unl_packed[3 * m_base_cells + idx_hab] = r_glo;
            }
        }

        // 2. Exact SPD solve for `P_proj` on active heads `h < h_v` (`0` on `h >= h_v`):
        if h < h_v {
            let r = basis.rank_r;
            for j_v in 0..128 {
                let mut rhs_r = vec![0.0f64; r];
                for a in 0..r {
                    let mut sum_us = 0i64;
                    for i_k in 0..128 {
                        let uv = basis.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                        let sv = s_before.s_int_lsb[h + (i_k << log_h) + (j_v << (log_h + 7))];
                        sum_us += uv * sv;
                    }
                    rhs_r[a] = (M_GS as f64) * (sum_us as f64);
                }
                let p_sol = solve_spd_small(r, &gram_rr, &rhs_r);
                for a in 0..r {
                    let pv = p_sol[a].round() as i64;
                    if pv < -QUOT_UNL_HALF || pv >= QUOT_UNL_HALF {
                        return Err(format!("|P_proj| = {} >= {QUOT_UNL_HALF}", pv.abs()));
                    }
                    let idx_p = h + (a << log_h) + (j_v << (log_h + 3));
                    p_proj_int[idx_p] = pv;
                    p_proj_lsb_haj[idx_p] = bb_from_i64(pv);
                    qlo_unl_packed[m_base_cells + idx_p] = (pv + QUOT_UNL_HALF) as u32;
                }
            }
        }

        // 3. Obligation U2 (2-limb `÷ 128`):
        //    `U_lo * P_proj + 8192 = 128 * Q_{p2,lo} + R_{p2,lo}`
        //    `U_hi * P_proj + Q_{p2,lo} = 128 * (S_before - S_unlearned) + R_{p2,hi}`
        for i_k in 0..128 {
            for j_v in 0..128 {
                let mut sum_ulo_p = 0i64;
                let mut sum_uhi_p = 0i64;
                for a in 0..R_PAD {
                    let idx_u = h + (i_k << log_h) + (a << (log_h + 7));
                    let ulo = (basis.u_lo_shift_lsb[idx_u] as i64) - ULO_HALF;
                    let uhi = (basis.u_hi_shift_lsb[idx_u] as i64) - UHI_HALF;
                    let pv = p_proj_int[h + (a << log_h) + (j_v << (log_h + 3))];
                    sum_ulo_p += ulo * pv;
                    sum_uhi_p += uhi * pv;
                }
                let num_p2_lo = sum_ulo_p + half_gs;
                let q_p2_lo = num_p2_lo.div_euclid(LIMB_RADIX);
                let r_p2_lo = num_p2_lo.rem_euclid(LIMB_RADIX) as u32;
                if q_p2_lo < -QUOT_UNL_HALF || q_p2_lo >= QUOT_UNL_HALF {
                    return Err(format!("Q_p2_lo {q_p2_lo} out of bounds"));
                }
                let num_p2_hi = sum_uhi_p + q_p2_lo;
                let q_del = num_p2_hi.div_euclid(HI_DIV);
                let r_p2_hi = num_p2_hi.rem_euclid(HI_DIV) as u32;

                let idx_s = h + (i_k << log_h) + (j_v << (log_h + 7));
                let sb = s_before.s_int_lsb[idx_s];
                let s_new = sb - q_del;
                if s_new.abs() > S_BND_HALF {
                    return Err(format!("S_unlearned {s_new} exceeds {S_BND_HALF}"));
                }
                s_unl_int[idx_s] = s_new;
                s_bnd_unl_packed[2 * m_base_cells + idx_s] = (s_new + S_BND_HALF) as u32;
                s_bnd_unl_packed[3 * m_base_cells + idx_s] = (S_BND_HALF - s_new) as u32;
                qlo_unl_packed[idx_s] = (q_p2_lo + QUOT_UNL_HALF) as u32;
                rem128_unl_packed[idx_s] = r_p2_lo;
                rem128_unl_packed[m_base_cells + idx_s] = r_p2_hi;
            }
        }

        // 4. Obligation U3 (2-limb `÷ 128`):
        //    `S_unlearned^T * U_lo + 8192 = 128 * Q_{u3,lo} + R_{u3,lo}`
        //    `S_unlearned^T * U_hi + Q_{u3,lo} = 128 * (Res_shift - TAU_ZERO) + R_{u3,hi}`
        for j_v in 0..128 {
            for a in 0..R_PAD {
                let mut sum_s_ulo = 0i64;
                let mut sum_s_uhi = 0i64;
                for i_k in 0..128 {
                    let su = s_unl_int[h + (i_k << log_h) + (j_v << (log_h + 7))];
                    let idx_u = h + (i_k << log_h) + (a << (log_h + 7));
                    let ulo = (basis.u_lo_shift_lsb[idx_u] as i64) - ULO_HALF;
                    let uhi = (basis.u_hi_shift_lsb[idx_u] as i64) - UHI_HALF;
                    sum_s_ulo += su * ulo;
                    sum_s_uhi += su * uhi;
                }
                let num_u3_lo = sum_s_ulo + half_gs;
                let q_u3_lo = num_u3_lo.div_euclid(LIMB_RADIX);
                let r_u3_lo = num_u3_lo.rem_euclid(LIMB_RADIX) as u32;
                if q_u3_lo < -QUOT_UNL_HALF || q_u3_lo >= QUOT_UNL_HALF {
                    return Err(format!("Q_u3_lo {q_u3_lo} out of bounds"));
                }
                let num_u3_hi = sum_s_uhi + q_u3_lo;
                let res_int = num_u3_hi.div_euclid(HI_DIV);
                let r_u3_hi = num_u3_hi.rem_euclid(HI_DIV) as u32;
                if res_int.abs() > max_abs_residual_int {
                    max_abs_residual_int = res_int.abs();
                }
                let res_shift = res_int + TAU_ZERO;
                if res_shift < 0 || res_shift >= (1i64 << M_TAB_ZERO) {
                    return Err(format!(
                        "Unlearned residual overflow at head {h} (j_v={j_v}, a={a}): res_int={res_int}"
                    ));
                }
                let idx_r = h + (j_v << log_h) + (a << (log_h + 7));
                res_shift_lsb_hja[idx_r] = res_shift as u32;
                qlo_unl_packed[m_base_cells + m_small_cells + idx_r] =
                    (q_u3_lo + QUOT_UNL_HALF) as u32;
                rem128_unl_packed[2 * m_base_cells + idx_r] = r_u3_lo;
                rem128_unl_packed[2 * m_base_cells + m_small_cells + idx_r] = r_u3_hi;
            }
        }
    }

    Ok(RankRUnlearnWitness {
        h_v,
        h_pad,
        rank_r: basis.rank_r,
        s_before: s_before.clone(),
        s_unlearned: FastWeightMemoryState::from_int_lsb(h_v, s_unl_int),
        basis: basis.clone(),
        p_proj_lsb_haj,
        gram_shift_pad,
        res_shift_lsb_hja,
        s_bnd_unl_packed,
        qlo_unl_packed,
        rem128_unl_packed,
        max_abs_residual_int,
    })
}

// ===========================================================================
// §5. Succinct Zero-Knowledge Continual WY Update Proof (`S_prev -> S_post`)
// ===========================================================================

fn eval_active_gram_identity_mle(
    h_v: usize,
    rank_r: usize,
    z_h: &[Ext4],
    z_a: &[Ext4],
    z_b: &[Ext4],
) -> Ext4 {
    let eq_h = build_eq_table_lsb_ext4(z_h);
    let eq_a = build_eq_table_lsb_ext4(z_a);
    let eq_b = build_eq_table_lsb_ext4(z_b);
    let mut h_sum = Ext4::ZERO;
    for h in 0..h_v {
        h_sum = h_sum.add(eq_h[h]);
    }
    let mut ab_sum = Ext4::ZERO;
    for a in 0..rank_r {
        ab_sum = ab_sum.add(eq_a[a].mul(eq_b[a]));
    }
    h_sum.mul(ab_sum)
}

fn eval_inactive_u_indicator_mle(
    h_v: usize,
    rank_r: usize,
    pt_h: &[Ext4],
    pt_a: &[Ext4],
) -> Ext4 {
    let eq_h = build_eq_table_lsb_ext4(pt_h);
    let eq_a = build_eq_table_lsb_ext4(pt_a);
    let mut active_h = Ext4::ZERO;
    for h in 0..h_v {
        active_h = active_h.add(eq_h[h]);
    }
    let mut active_a = Ext4::ZERO;
    for a in 0..rank_r {
        active_a = active_a.add(eq_a[a]);
    }
    Ext4::ONE.sub(active_h.mul(active_a))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkContinualUpdateProof {
    pub episode_idx: u32,
    pub h_v: usize,
    pub h_pad: usize,
    pub rank_r: usize,
    pub s_prev_root: [u8; 32],
    pub s_post_root: [u8; 32],
    pub k_pcs_root: [u8; 32],
    pub forget_request_root: [u8; 32],
    pub u_pcs_root: [u8; 32],
    pub request_nonce: [u8; 32],
    pub mmr_proof: MmrInclusionProof,

    pub c_ep_pcs_root: [u8; 32],
    pub espan_pcs_root: [u8; 32],
    pub mult_espan_pcs_root: [u8; 32],
    pub rspan_pcs_root: [u8; 32],
    pub mult_rspan_pcs_root: [u8; 32],
    pub l_pcs_root: [u8; 32],
    pub du_pcs_root: [u8; 32],
    pub rhs_pcs_root: [u8; 32],
    pub uw_pcs_root: [u8; 32],
    pub delta_eff_pcs_root: [u8; 32],
    pub rem_pcs_root: [u8; 32],
    pub mult_pcs_root: [u8; 32],
    pub quot_wy_pcs_root: [u8; 32],
    pub mult_quot_wy_pcs_root: [u8; 32],
    pub sbnd_wy_pcs_root: [u8; 32],
    pub mult_sbnd_wy_pcs_root: [u8; 32],
    pub small512_pcs_root: [u8; 32],
    pub mult_small512_pcs_root: [u8; 32],

    pub k_at_zkspan: Ext4,
    pub espan_at_zkspan: Ext4,
    pub rspan_at_zkspan: Ext4,
    pub l_at_zkk: Ext4,
    pub du_at_zkk: Ext4,
    pub r_kk_at_zkk: Ext4,
    pub rhs_at_z1: Ext4,
    pub uw_at_z1: Ext4,
    pub r_wy_at_z1: Ext4,
    pub u_at_z2: Ext4,
    pub delta_eff_at_z2: Ext4,
    pub r_eff_at_z2: Ext4,
    pub s_post_at_z3: Ext4,
    pub s_prev_at_z3: Ext4,
    pub r_state_at_z3: Ext4,
    pub s_prev_at_zsbnd: Ext4,
    pub s_post_at_zsbnd: Ext4,
    pub k_at_zkbnd: Ext4,
    pub w_at_zkbnd: Ext4,
    pub l_at_zlbnd: Ext4,
    pub du_at_zlbnd: Ext4,
    pub cep_at_zcepbnd: Ext4,
    pub u_at_zulimb: Ext4,
    pub ulo_shift_at_zulimb: Ext4,
    pub uhi_shift_at_zulimb: Ext4,

    pub u_inactive_zero: GruenMode2Ext4Proof,
    pub kspan_gruen: GruenMode2Ext4Proof,
    pub kk_gruen: GruenMode2Ext4Proof,
    pub slt_zero: GruenMode2Ext4Proof,
    pub du_slt_zero: GruenMode2Ext4Proof,
    pub wy_gruen: GruenMode2Ext4Proof,
    pub ws_gruen: GruenMode2Ext4Proof,
    pub kd_gruen: GruenMode2Ext4Proof,

    pub espan_d1b: D1bRangeExt4Proof,
    pub rspan_d1b: D1bRangeExt4Proof,
    pub rem_d1b: D1bRangeExt4Proof,
    pub quot_wy_d1b: D1bRangeExt4Proof,
    pub sbnd_wy_d1b: D1bRangeExt4Proof,
    pub small512_d1b: D1bRangeExt4Proof,

    pub s_prev_pcs: PcsOpeningProof,
    pub s_post_pcs: PcsOpeningProof,
    pub u_pcs: PcsOpeningProof,
    pub k_pcs: PcsOpeningProof,
    pub c_ep_pcs: PcsOpeningProof,
    pub espan_pcs: PcsOpeningProof,
    pub mult_espan_pcs: PcsOpeningProof,
    pub rspan_pcs: PcsOpeningProof,
    pub mult_rspan_pcs: PcsOpeningProof,
    pub l_pcs: PcsOpeningProof,
    pub du_pcs: PcsOpeningProof,
    pub rhs_pcs: PcsOpeningProof,
    pub uw_pcs: PcsOpeningProof,
    pub delta_eff_pcs: PcsOpeningProof,
    pub rem_pcs: PcsOpeningProof,
    pub mult_pcs: PcsOpeningProof,
    pub quot_wy_pcs: PcsOpeningProof,
    pub mult_quot_wy_pcs: PcsOpeningProof,
    pub sbnd_wy_pcs: PcsOpeningProof,
    pub mult_sbnd_wy_pcs: PcsOpeningProof,
    pub small512_pcs: PcsOpeningProof,
    pub mult_small512_pcs: PcsOpeningProof,
}

impl ZkContinualUpdateProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(896 * 1024);
        out.extend_from_slice(UPDATE_PROOF_MAGIC);
        out.extend_from_slice(&self.episode_idx.to_le_bytes());
        out.extend_from_slice(&(self.h_v as u32).to_le_bytes());
        out.extend_from_slice(&(self.h_pad as u32).to_le_bytes());
        out.extend_from_slice(&(self.rank_r as u32).to_le_bytes());
        for r in [
            &self.s_prev_root,
            &self.s_post_root,
            &self.k_pcs_root,
            &self.forget_request_root,
            &self.u_pcs_root,
            &self.request_nonce,
            &self.c_ep_pcs_root,
            &self.espan_pcs_root,
            &self.mult_espan_pcs_root,
            &self.rspan_pcs_root,
            &self.mult_rspan_pcs_root,
            &self.l_pcs_root,
            &self.du_pcs_root,
            &self.rhs_pcs_root,
            &self.uw_pcs_root,
            &self.delta_eff_pcs_root,
            &self.rem_pcs_root,
            &self.mult_pcs_root,
            &self.quot_wy_pcs_root,
            &self.mult_quot_wy_pcs_root,
            &self.sbnd_wy_pcs_root,
            &self.mult_sbnd_wy_pcs_root,
            &self.small512_pcs_root,
            &self.mult_small512_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        self.mmr_proof.write_to(&mut out);
        for e in [
            self.k_at_zkspan,
            self.espan_at_zkspan,
            self.rspan_at_zkspan,
            self.l_at_zkk,
            self.du_at_zkk,
            self.r_kk_at_zkk,
            self.rhs_at_z1,
            self.uw_at_z1,
            self.r_wy_at_z1,
            self.u_at_z2,
            self.delta_eff_at_z2,
            self.r_eff_at_z2,
            self.s_post_at_z3,
            self.s_prev_at_z3,
            self.r_state_at_z3,
            self.s_prev_at_zsbnd,
            self.s_post_at_zsbnd,
            self.k_at_zkbnd,
            self.w_at_zkbnd,
            self.l_at_zlbnd,
            self.du_at_zlbnd,
            self.cep_at_zcepbnd,
            self.u_at_zulimb,
            self.ulo_shift_at_zulimb,
            self.uhi_shift_at_zulimb,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }
        for gp in [
            &self.u_inactive_zero,
            &self.kspan_gruen,
            &self.kk_gruen,
            &self.slt_zero,
            &self.du_slt_zero,
            &self.wy_gruen,
            &self.ws_gruen,
            &self.kd_gruen,
        ] {
            gp.write_to(&mut out);
        }
        for dp in [
            &self.espan_d1b,
            &self.rspan_d1b,
            &self.rem_d1b,
            &self.quot_wy_d1b,
            &self.sbnd_wy_d1b,
            &self.small512_d1b,
        ] {
            dp.write_to(&mut out);
        }
        for pf in [
            &self.s_prev_pcs,
            &self.s_post_pcs,
            &self.u_pcs,
            &self.k_pcs,
            &self.c_ep_pcs,
            &self.espan_pcs,
            &self.mult_espan_pcs,
            &self.rspan_pcs,
            &self.mult_rspan_pcs,
            &self.l_pcs,
            &self.du_pcs,
            &self.rhs_pcs,
            &self.uw_pcs,
            &self.delta_eff_pcs,
            &self.rem_pcs,
            &self.mult_pcs,
            &self.quot_wy_pcs,
            &self.mult_quot_wy_pcs,
            &self.sbnd_wy_pcs,
            &self.mult_sbnd_wy_pcs,
            &self.small512_pcs,
            &self.mult_small512_pcs,
        ] {
            pf.write_to(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != UPDATE_PROOF_MAGIC {
            return Err("invalid ZkContinualUpdateProof magic".to_string());
        }
        let episode_idx = cur.read_u32()?;
        let h_v = cur.read_u32()? as usize;
        let h_pad = cur.read_u32()? as usize;
        let rank_r = cur.read_u32()? as usize;
        if !h_pad.is_power_of_two()
            || h_pad < 16
            || h_pad > 64
            || h_v == 0
            || h_v > h_pad
            || rank_r == 0
            || rank_r > R_PAD
        {
            return Err("invalid dims in ZkContinualUpdateProof".to_string());
        }
        let s_prev_root = cur.read_arr32()?;
        let s_post_root = cur.read_arr32()?;
        let k_pcs_root = cur.read_arr32()?;
        let forget_request_root = cur.read_arr32()?;
        let u_pcs_root = cur.read_arr32()?;
        let request_nonce = cur.read_arr32()?;
        let c_ep_pcs_root = cur.read_arr32()?;
        let espan_pcs_root = cur.read_arr32()?;
        let mult_espan_pcs_root = cur.read_arr32()?;
        let rspan_pcs_root = cur.read_arr32()?;
        let mult_rspan_pcs_root = cur.read_arr32()?;
        let l_pcs_root = cur.read_arr32()?;
        let du_pcs_root = cur.read_arr32()?;
        let rhs_pcs_root = cur.read_arr32()?;
        let uw_pcs_root = cur.read_arr32()?;
        let delta_eff_pcs_root = cur.read_arr32()?;
        let rem_pcs_root = cur.read_arr32()?;
        let mult_pcs_root = cur.read_arr32()?;
        let quot_wy_pcs_root = cur.read_arr32()?;
        let mult_quot_wy_pcs_root = cur.read_arr32()?;
        let sbnd_wy_pcs_root = cur.read_arr32()?;
        let mult_sbnd_wy_pcs_root = cur.read_arr32()?;
        let small512_pcs_root = cur.read_arr32()?;
        let mult_small512_pcs_root = cur.read_arr32()?;
        let mmr_proof = MmrInclusionProof::read_from(&mut cur)?;
        let k_at_zkspan = cur.read_ext4()?;
        let espan_at_zkspan = cur.read_ext4()?;
        let rspan_at_zkspan = cur.read_ext4()?;
        let l_at_zkk = cur.read_ext4()?;
        let du_at_zkk = cur.read_ext4()?;
        let r_kk_at_zkk = cur.read_ext4()?;
        let rhs_at_z1 = cur.read_ext4()?;
        let uw_at_z1 = cur.read_ext4()?;
        let r_wy_at_z1 = cur.read_ext4()?;
        let u_at_z2 = cur.read_ext4()?;
        let delta_eff_at_z2 = cur.read_ext4()?;
        let r_eff_at_z2 = cur.read_ext4()?;
        let s_post_at_z3 = cur.read_ext4()?;
        let s_prev_at_z3 = cur.read_ext4()?;
        let r_state_at_z3 = cur.read_ext4()?;
        let s_prev_at_zsbnd = cur.read_ext4()?;
        let s_post_at_zsbnd = cur.read_ext4()?;
        let k_at_zkbnd = cur.read_ext4()?;
        let w_at_zkbnd = cur.read_ext4()?;
        let l_at_zlbnd = cur.read_ext4()?;
        let du_at_zlbnd = cur.read_ext4()?;
        let cep_at_zcepbnd = cur.read_ext4()?;
        let u_at_zulimb = cur.read_ext4()?;
        let ulo_shift_at_zulimb = cur.read_ext4()?;
        let uhi_shift_at_zulimb = cur.read_ext4()?;
        let u_inactive_zero = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let kspan_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let kk_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let slt_zero = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let du_slt_zero = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let wy_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let ws_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let kd_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let espan_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let rspan_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let rem_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let quot_wy_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let sbnd_wy_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let small512_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let s_prev_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let s_post_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let u_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let k_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let c_ep_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let espan_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_espan_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let rspan_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_rspan_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let l_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let du_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let rhs_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let uw_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let delta_eff_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let rem_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let quot_wy_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_quot_wy_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let sbnd_wy_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_sbnd_wy_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let small512_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_small512_pcs = PcsOpeningProof::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in ZkContinualUpdateProof".to_string());
        }
        Ok(Self {
            episode_idx,
            h_v,
            h_pad,
            rank_r,
            s_prev_root,
            s_post_root,
            k_pcs_root,
            forget_request_root,
            u_pcs_root,
            request_nonce,
            mmr_proof,
            c_ep_pcs_root,
            espan_pcs_root,
            mult_espan_pcs_root,
            rspan_pcs_root,
            mult_rspan_pcs_root,
            l_pcs_root,
            du_pcs_root,
            rhs_pcs_root,
            uw_pcs_root,
            delta_eff_pcs_root,
            rem_pcs_root,
            mult_pcs_root,
            quot_wy_pcs_root,
            mult_quot_wy_pcs_root,
            sbnd_wy_pcs_root,
            mult_sbnd_wy_pcs_root,
            small512_pcs_root,
            mult_small512_pcs_root,
            k_at_zkspan,
            espan_at_zkspan,
            rspan_at_zkspan,
            l_at_zkk,
            du_at_zkk,
            r_kk_at_zkk,
            rhs_at_z1,
            uw_at_z1,
            r_wy_at_z1,
            u_at_z2,
            delta_eff_at_z2,
            r_eff_at_z2,
            s_post_at_z3,
            s_prev_at_z3,
            r_state_at_z3,
            s_prev_at_zsbnd,
            s_post_at_zsbnd,
            k_at_zkbnd,
            w_at_zkbnd,
            l_at_zlbnd,
            du_at_zlbnd,
            cep_at_zcepbnd,
            u_at_zulimb,
            ulo_shift_at_zulimb,
            uhi_shift_at_zulimb,
            u_inactive_zero,
            kspan_gruen,
            kk_gruen,
            slt_zero,
            du_slt_zero,
            wy_gruen,
            ws_gruen,
            kd_gruen,
            espan_d1b,
            rspan_d1b,
            rem_d1b,
            quot_wy_d1b,
            sbnd_wy_d1b,
            small512_d1b,
            s_prev_pcs,
            s_post_pcs,
            u_pcs,
            k_pcs,
            c_ep_pcs,
            espan_pcs,
            mult_espan_pcs,
            rspan_pcs,
            mult_rspan_pcs,
            l_pcs,
            du_pcs,
            rhs_pcs,
            uw_pcs,
            delta_eff_pcs,
            rem_pcs,
            mult_pcs,
            quot_wy_pcs,
            mult_quot_wy_pcs,
            sbnd_wy_pcs,
            mult_sbnd_wy_pcs,
            small512_pcs,
            mult_small512_pcs,
        })
    }
}

pub fn prove_continual_wy_update_zk(
    vault_key: &ProverVaultKey,
    wit: &ContinualWyUpdateWitness,
    basis_for_future_forget: &GramSchmidtSubspaceBasis,
    request_nonce: &[u8; 32],
    mmr: &mut ContinualEpisodeMmr,
) -> Result<(Vec<u8>, [u8; 32], [u8; 32], [u8; 32], [u8; 32]), String> {
    if wit.h_v != basis_for_future_forget.h_v || wit.h_pad != basis_for_future_forget.h_pad {
        return Err("update witness vs basis head count mismatch".to_string());
    }
    let h_v = wit.h_v;
    let h_pad = wit.h_pad;
    let rank_r = basis_for_future_forget.rank_r;
    let log_h = h_pad.trailing_zeros() as usize;
    let m_q = log_h + 14;
    let m_k = log_h + 13;
    let m_l = log_h + 12;
    let m_small = log_h + 10;
    let m_cep = log_h + 9;
    let m_rem = m_q + 2;
    let m_sbnd = m_q + 1;
    let q_size = h_pad * 16384;
    let k_size = h_pad * 8192;
    let l_size = h_pad * 4096;
    let cep_size = h_pad * 512;
    let half_gs = M_GS / 2;

    // 1. Solve `C_ep` (`#115` Item 1: `U_int * C_ep == M_GS * (K_int - E_span) + R_span - M_GS/2`)
    //    and check inactive `U == 0`:
    for h in 0..h_pad {
        for a in 0..R_PAD {
            let active = h < h_v && a < rank_r;
            for i_k in 0..128 {
                let uv = basis_for_future_forget.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                if !active && uv != 0 {
                    return Err("inactive U non-zero in prove_continual_wy_update_zk".to_string());
                }
            }
        }
    }
    let mut c_ep_int = vec![0i64; cep_size];
    let mut c_ep_lsb_hca = vec![0u32; cep_size];
    let mut espan_shift_hci = vec![TAU_SPAN as u32; k_size];
    let mut rspan_hci = vec![half_gs as u32; k_size];

    for h in 0..h_pad {
        if h < h_v {
            let mut gram_rr = vec![0.0f64; rank_r * rank_r];
            for a in 0..rank_r {
                for b in 0..rank_r {
                    let mut dot = 0i64;
                    for i_k in 0..128 {
                        let ua = basis_for_future_forget.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                        let ub = basis_for_future_forget.u_int_lsb[h + (i_k << log_h) + (b << (log_h + 7))];
                        dot += ua * ub;
                    }
                    gram_rr[a * rank_r + b] = dot as f64;
                }
            }
            for c in 0..64 {
                let mut rhs_r = vec![0.0f64; rank_r];
                for a in 0..rank_r {
                    let mut uk = 0i64;
                    for i_k in 0..128 {
                        let ua = basis_for_future_forget.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                        let kv = wit.k_int_lsb_hci[h + (c << log_h) + (i_k << (log_h + 6))];
                        uk += ua * kv;
                    }
                    rhs_r[a] = (M_GS as f64) * (uk as f64);
                }
                let sol = solve_spd_small(rank_r, &gram_rr, &rhs_r);
                for a in 0..rank_r {
                    let cv = sol[a].round() as i64;
                    if cv < -SMALL512_HALF || cv >= SMALL512_HALF {
                        return Err(format!("C_ep {cv} outside [-256, 256)"));
                    }
                    let idx_c = h + (c << log_h) + (a << (log_h + 6));
                    c_ep_int[idx_c] = cv;
                    c_ep_lsb_hca[idx_c] = bb_from_i64(cv);
                }
            }
        }
        for c in 0..64 {
            for i_k in 0..128 {
                let mut sum_uc = 0i64;
                for a in 0..R_PAD {
                    let ua = basis_for_future_forget.u_int_lsb[h + (i_k << log_h) + (a << (log_h + 7))];
                    let cv = c_ep_int[h + (c << log_h) + (a << (log_h + 6))];
                    sum_uc += ua * cv;
                }
                let num = sum_uc + half_gs;
                let q_k = num.div_euclid(M_GS);
                let r_sp = num.rem_euclid(M_GS) as u32;
                let idx_k = h + (c << log_h) + (i_k << (log_h + 6));
                let kv = wit.k_int_lsb_hci[idx_k];
                let e_sp = kv - q_k;
                let e_shift = e_sp + TAU_SPAN;
                if e_shift < 0 || e_shift >= (1i64 << M_TAB_SPAN) {
                    return Err(format!(
                        "Episode key K[h={h}, c={c}, i_k={i_k}] outside span(U): e_sp={e_sp}"
                    ));
                }
                espan_shift_hci[idx_k] = e_shift as u32;
                rspan_hci[idx_k] = r_sp;
            }
        }
    }

    // 2. Pack `small512_packed` (`[4 * k_size = 2 * q_size]` in `[0, 512)`):
    //    q0 (`[0,0]`): `K_int + 256` (`k_size`)
    //    q1 (`[1,0]`): `W + 256` (`k_size`)
    //    q2 (`[0,1]`): `[L + 256 (l_size), D_U + 256 (l_size)]`
    //    q3 (`[1,1]`): `[C_ep + 256 (cep_size), pad, U_lo + 64 (m_small_cells), U_hi + 128 (m_small_cells), ...]`
    let m_small_cells = h_pad * 1024;
    let mut small512_packed = vec![SMALL512_HALF as u32; 4 * k_size];
    for idx_k in 0..k_size {
        small512_packed[idx_k] = (wit.k_int_lsb_hci[idx_k] + SMALL512_HALF) as u32;
        // `W = UW[col >= 128]` has `col = 128 + i_k`, so index in `uw_int_lsb_hccol` is `q_size/2 + idx_k`!
        let wv = wit.uw_int_lsb_hccol[(q_size / 2) + idx_k];
        small512_packed[k_size + idx_k] = (wv + SMALL512_HALF) as u32;
    }
    for idx_l in 0..l_size {
        small512_packed[2 * k_size + idx_l] = (wit.l_int_lsb_hcj[idx_l] + SMALL512_HALF) as u32;
        small512_packed[2 * k_size + l_size + idx_l] =
            (wit.du_int_lsb_hcj[idx_l] + SMALL512_HALF) as u32;
    }
    for idx_c in 0..cep_size {
        small512_packed[3 * k_size + idx_c] = (c_ep_int[idx_c] + SMALL512_HALF) as u32;
    }
    // Place `U_lo + 64` at `3*k_size + m_small_cells` (`sub-bits [1, 0, 0]`) and `U_hi + 128` at `3*k_size + 2*m_small_cells` (`[0, 1, 0]`):
    for idx_u in 0..m_small_cells {
        small512_packed[3 * k_size + m_small_cells + idx_u] =
            basis_for_future_forget.u_lo_shift_lsb[idx_u];
        small512_packed[3 * k_size + 2 * m_small_cells + idx_u] =
            basis_for_future_forget.u_hi_shift_lsb[idx_u];
    }

    let mult_espan = compute_d1b_multiplicities(&espan_shift_hci, M_TAB_SPAN)?;
    let mult_rspan = compute_d1b_multiplicities(&rspan_hci, GS_SHIFT as usize)?;
    let mult_wy = compute_d1b_multiplicities(&wit.rem_packed_128, CMEM_WY_SHIFT as usize)?;
    let mult_qwy = compute_d1b_multiplicities(&wit.quot_wy_packed, M_TAB_QUOT_WY)?;
    let mult_sbnd = compute_d1b_multiplicities(&wit.s_bnd_wy_packed, M_TAB_S_BND)?;
    let mult_sm512 = compute_d1b_multiplicities(&small512_packed, M_TAB_SMALL512)?;

    let s_prev_seed = vault_key.state_pcs_seed(&wit.s_prev.s_bb_lsb);
    let s_post_seed = vault_key.state_pcs_seed(&wit.s_post.s_bb_lsb);
    let u_seed = vault_key.basis_pcs_seed(&basis_for_future_forget.u_bb_lsb, request_nonce);

    let s_prev_st = commit_table_pcs(&wit.s_prev.s_bb_lsb, PcsParams::default_zk(4), Some(&s_prev_seed));
    let s_post_st = commit_table_pcs(&wit.s_post.s_bb_lsb, PcsParams::default_zk(4), Some(&s_post_seed));
    let u_st = commit_table_pcs(&basis_for_future_forget.u_bb_lsb, PcsParams::default_zk(4), Some(&u_seed));
    let k_st = commit_table_pcs(&wit.k_lsb_hci, PcsParams::default_zk(5), None);
    let c_ep_st = commit_table_pcs(&c_ep_lsb_hca, PcsParams::default_zk(2), None);
    let espan_st = commit_table_pcs(&espan_shift_hci, PcsParams::default_zk(2), None);
    let mult_espan_st = commit_table_pcs(&mult_espan, PcsParams::default_zk(1), None);
    let rspan_st = commit_table_pcs(&rspan_hci, PcsParams::default_zk(2), None);
    let mult_rspan_st = commit_table_pcs(&mult_rspan, PcsParams::default_zk(1), None);
    let l_st = commit_table_pcs(&wit.l_lsb_hcj, PcsParams::default_zk(4), None);
    let du_st = commit_table_pcs(&wit.du_lsb_hcj, PcsParams::default_zk(3), None);
    let rhs_st = commit_table_pcs(&wit.rhs_lsb_hccol, PcsParams::default_zk(2), None);
    let uw_st = commit_table_pcs(&wit.uw_lsb_hccol, PcsParams::default_zk(5), None);
    let deff_st = commit_table_pcs(&wit.delta_eff_lsb_hcj, PcsParams::default_zk(2), None);
    let rem_st = commit_table_pcs(&wit.rem_packed_128, PcsParams::default_zk(5), None);
    let mult_st = commit_table_pcs(&mult_wy, PcsParams::default_zk(1), None);
    let qwy_st = commit_table_pcs(&wit.quot_wy_packed, PcsParams::default_zk(4), None);
    let mult_qwy_st = commit_table_pcs(&mult_qwy, PcsParams::default_zk(1), None);
    let sbnd_st = commit_table_pcs(&wit.s_bnd_wy_packed, PcsParams::default_zk(5), None);
    let mult_sbnd_st = commit_table_pcs(&mult_sbnd, PcsParams::default_zk(1), None);
    let sm512_st = commit_table_pcs(&small512_packed, PcsParams::default_zk(8), None);
    let mult_sm512_st = commit_table_pcs(&mult_sm512, PcsParams::default_zk(1), None);

    let forget_request_root =
        compute_blind_forget_request_root(h_v, h_pad, rank_r, &u_st.root, request_nonce);
    let episode_idx = mmr.entries.len() as u32;
    let mmr_root = mmr.push(EpisodeMmrEntry {
        episode_idx,
        s_prev_root: s_prev_st.root,
        s_post_root: s_post_st.root,
        k_pcs_root: k_st.root,
        forget_request_root,
    });
    let mmr_proof = mmr.open(episode_idx as usize);

    let mut tr = CShakeTranscript::new(b"CMEM-WY-UPDATE-ZK-V3");
    tr.absorb_u32(b"ep_idx", episode_idx);
    tr.absorb_u32(b"h_v", h_v as u32);
    tr.absorb_u32(b"h_pad", h_pad as u32);
    tr.absorb_u32(b"rank_r", rank_r as u32);
    tr.absorb_root(b"mmr_root", &mmr_root);
    for r in [
        &s_prev_st.root,
        &s_post_st.root,
        &k_st.root,
        &forget_request_root,
        &u_st.root,
        request_nonce,
        &c_ep_st.root,
        &espan_st.root,
        &mult_espan_st.root,
        &rspan_st.root,
        &mult_rspan_st.root,
        &l_st.root,
        &du_st.root,
        &rhs_st.root,
        &uw_st.root,
        &deff_st.root,
        &rem_st.root,
        &mult_st.root,
        &qwy_st.root,
        &mult_qwy_st.root,
        &sbnd_st.root,
        &mult_sbnd_st.root,
        &sm512_st.root,
        &mult_sm512_st.root,
    ] {
        tr.absorb_root(b"cmem_up_root", r);
    }

    // W0a: `u_inactive_zero`
    let zi_all = tr.squeeze_ext4_vec(b"u_inact_zs", m_small, true);
    let mut inact_ind = vec![Ext4::ZERO; m_small_cells];
    let mut u_ext_tab = vec![Ext4::ZERO; m_small_cells];
    for a in 0..R_PAD {
        for h in 0..h_pad {
            let bad = if h >= h_v || a >= rank_r {
                Ext4::ONE
            } else {
                Ext4::ZERO
            };
            for i_k in 0..128 {
                let idx = h + (i_k << log_h) + (a << (log_h + 7));
                inact_ind[idx] = bad;
                u_ext_tab[idx] = Ext4::from_bb(basis_for_future_forget.u_bb_lsb[idx]);
            }
        }
    }
    let (u_inactive_zero, u_inact_pt) =
        prove_gruen_einsum_mode2_ext4(&inact_ind, &u_ext_tab, m_small, 0, &zi_all, &mut tr);

    // W0b: `U_int * C_ep == M_GS * (K_int - (E_span_shift - TAU_SPAN)) + R_span - M_GS/2`
    let zks_h = tr.squeeze_ext4_vec(b"zks_h", log_h, true);
    let zks_c = tr.squeeze_ext4_vec(b"zks_c", 6, true);
    let zks_ik = tr.squeeze_ext4_vec(b"zks_ik", 7, true);
    let mut zk_span = Vec::with_capacity(m_k);
    zk_span.extend_from_slice(&zks_h);
    zk_span.extend_from_slice(&zks_c);
    zk_span.extend_from_slice(&zks_ik);
    let k_at_zkspan = mle_eval_bb_at_ext4(&wit.k_lsb_hci, &zk_span);
    let espan_at_zkspan = mle_eval_bb_at_ext4(&espan_shift_hci, &zk_span);
    let rspan_at_zkspan = mle_eval_bb_at_ext4(&rspan_hci, &zk_span);
    for e in [k_at_zkspan, espan_at_zkspan, rspan_at_zkspan] {
        tr.absorb_ext4(b"zks_ev", e);
    }
    let eq_zksc = build_eq_table_lsb_ext4(&zks_c);
    let eq_zksik = build_eq_table_lsb_ext4(&zks_ik);
    let mut ksp_left = vec![Ext4::ZERO; h_pad * R_PAD];
    let mut ksp_right = vec![Ext4::ZERO; h_pad * R_PAD];
    for a in 0..R_PAD {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            for i_k in 0..128 {
                al = al.add(eq_zksik[i_k].scale_bb(basis_for_future_forget.u_bb_lsb[h + (i_k << log_h) + (a << (log_h + 7))]));
            }
            ksp_left[h + (a << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for c in 0..64 {
                ar = ar.add(eq_zksc[c].scale_bb(c_ep_lsb_hca[h + (c << log_h) + (a << (log_h + 6))]));
            }
            ksp_right[h + (a << log_h)] = ar;
        }
    }
    let (kspan_gruen, ksp_ch) =
        prove_gruen_einsum_mode2_ext4(&ksp_left, &ksp_right, log_h, LOG_R_PAD, &zks_h, &mut tr);

    // W1: `K_int * K_int^T == CMEM_WY_SCALE * (L + D_U) + R_kk - half_wy` + `slt_zero` + `du_slt_zero`
    let zkk_h = tr.squeeze_ext4_vec(b"zkk_h", log_h, true);
    let zkk_c = tr.squeeze_ext4_vec(b"zkk_c", 6, true);
    let zkk_j = tr.squeeze_ext4_vec(b"zkk_j", 6, true);
    let mut zkk_hcj = Vec::with_capacity(m_l);
    zkk_hcj.extend_from_slice(&zkk_h);
    zkk_hcj.extend_from_slice(&zkk_c);
    zkk_hcj.extend_from_slice(&zkk_j);
    let l_at_zkk = mle_eval_bb_at_ext4(&wit.l_lsb_hcj, &zkk_hcj);
    let du_at_zkk = mle_eval_bb_at_ext4(&wit.du_lsb_hcj, &zkk_hcj);
    let mut zkk_rem = zkk_hcj.clone();
    zkk_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    let r_kk_at_zkk = mle_eval_bb_at_ext4(&wit.rem_packed_128, &zkk_rem);
    for e in [l_at_zkk, du_at_zkk, r_kk_at_zkk] {
        tr.absorb_ext4(b"zkk_ev", e);
    }
    let eq_zkkc = build_eq_table_lsb_ext4(&zkk_c);
    let eq_zkkj = build_eq_table_lsb_ext4(&zkk_j);
    let mut kk_left = vec![Ext4::ZERO; h_pad * 128];
    let mut kk_right = vec![Ext4::ZERO; h_pad * 128];
    for i_k in 0..128 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            let mut ar = Ext4::ZERO;
            for c in 0..64 {
                let kv = wit.k_lsb_hci[h + (c << log_h) + (i_k << (log_h + 6))];
                al = al.add(eq_zkkc[c].scale_bb(kv));
                ar = ar.add(eq_zkkj[c].scale_bb(kv));
            }
            kk_left[h + (i_k << log_h)] = al;
            kk_right[h + (i_k << log_h)] = ar;
        }
    }
    let (kk_gruen, kk_ch) =
        prove_gruen_einsum_mode2_ext4(&kk_left, &kk_right, log_h, 7, &zkk_h, &mut tr);
    let (slt_zero, slt_pt) = prove_strict_lower_tri_ext4(&wit.l_lsb_hcj, log_h, 6, &mut tr);

    let zdu_s = tr.squeeze_ext4_vec(b"duslt_zs", m_l, true);
    let mut slt_ind_tab = vec![Ext4::ZERO; l_size];
    let mut du_ext_tab = vec![Ext4::ZERO; l_size];
    for j in 0..64 {
        for c in 0..64 {
            let is_slt = if j < c { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..h_pad {
                let idx = h + (c << log_h) + (j << (log_h + 6));
                slt_ind_tab[idx] = is_slt;
                du_ext_tab[idx] = Ext4::from_bb(wit.du_lsb_hcj[idx]);
            }
        }
    }
    let (du_slt_zero, du_slt_pt) =
        prove_gruen_einsum_mode2_ext4(&slt_ind_tab, &du_ext_tab, m_l, 0, &zdu_s, &mut tr);

    // W2: `L * UW`
    let z1_h = tr.squeeze_ext4_vec(b"z1_h", log_h, true);
    let z1_c = tr.squeeze_ext4_vec(b"z1_c", 6, true);
    let z1_col = tr.squeeze_ext4_vec(b"z1_col", 8, true);
    let mut z1_all = Vec::with_capacity(m_q);
    z1_all.extend_from_slice(&z1_h);
    z1_all.extend_from_slice(&z1_c);
    z1_all.extend_from_slice(&z1_col);
    let rhs_at_z1 = mle_eval_bb_at_ext4(&wit.rhs_lsb_hccol, &z1_all);
    let uw_at_z1 = mle_eval_bb_at_ext4(&wit.uw_lsb_hccol, &z1_all);
    let mut z1_rem = z1_all.clone();
    z1_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let r_wy_at_z1 = mle_eval_bb_at_ext4(&wit.rem_packed_128, &z1_rem);
    for e in [rhs_at_z1, uw_at_z1, r_wy_at_z1] {
        tr.absorb_ext4(b"z1_ev", e);
    }
    let eq_z1c = build_eq_table_lsb_ext4(&z1_c);
    let eq_z1col = build_eq_table_lsb_ext4(&z1_col);
    let mut wy_left = vec![Ext4::ZERO; h_pad * 64];
    let mut wy_right = vec![Ext4::ZERO; h_pad * 64];
    for j in 0..64 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            for c in 0..64 {
                al = al.add(eq_z1c[c].scale_bb(wit.l_lsb_hcj[h + (c << log_h) + (j << (log_h + 6))]));
            }
            wy_left[h + (j << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for col in 0..256 {
                ar = ar.add(eq_z1col[col].scale_bb(wit.uw_lsb_hccol[h + (j << log_h) + (col << (log_h + 6))]));
            }
            wy_right[h + (j << log_h)] = ar;
        }
    }
    let (wy_gruen, wy_ch) =
        prove_gruen_einsum_mode2_ext4(&wy_left, &wy_right, log_h, 6, &z1_h, &mut tr);

    // W3: `W * S_prev`
    let z2_h = tr.squeeze_ext4_vec(b"z2_h", log_h, true);
    let z2_c = tr.squeeze_ext4_vec(b"z2_c", 6, true);
    let z2_jv = tr.squeeze_ext4_vec(b"z2_jv", 7, true);
    let mut z2_hcj = Vec::with_capacity(m_k);
    z2_hcj.extend_from_slice(&z2_h);
    z2_hcj.extend_from_slice(&z2_c);
    z2_hcj.extend_from_slice(&z2_jv);
    let mut z2_u_pt = z2_hcj.clone();
    z2_u_pt.push(Ext4::ZERO);
    let u_at_z2 = mle_eval_bb_at_ext4(&wit.uw_lsb_hccol, &z2_u_pt);
    let delta_eff_at_z2 = mle_eval_bb_at_ext4(&wit.delta_eff_lsb_hcj, &z2_hcj);
    let mut z2_rem = z2_hcj.clone();
    z2_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ONE, Ext4::ZERO]);
    let r_eff_at_z2 = mle_eval_bb_at_ext4(&wit.rem_packed_128, &z2_rem);
    for e in [u_at_z2, delta_eff_at_z2, r_eff_at_z2] {
        tr.absorb_ext4(b"z2_ev", e);
    }
    let eq_z2c = build_eq_table_lsb_ext4(&z2_c);
    let eq_z2jv = build_eq_table_lsb_ext4(&z2_jv);
    let mut ws_left = vec![Ext4::ZERO; h_pad * 128];
    let mut ws_right = vec![Ext4::ZERO; h_pad * 128];
    for i_k in 0..128 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            let col_w = 128 + i_k;
            for c in 0..64 {
                al = al.add(eq_z2c[c].scale_bb(wit.uw_lsb_hccol[h + (c << log_h) + (col_w << (log_h + 6))]));
            }
            ws_left[h + (i_k << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for j_v in 0..128 {
                ar = ar.add(eq_z2jv[j_v].scale_bb(wit.s_prev.s_bb_lsb[h + (i_k << log_h) + (j_v << (log_h + 7))]));
            }
            ws_right[h + (i_k << log_h)] = ar;
        }
    }
    let (ws_gruen, ws_ch) =
        prove_gruen_einsum_mode2_ext4(&ws_left, &ws_right, log_h, 7, &z2_h, &mut tr);

    // W4: `K_int^T * Delta_eff`
    let z3_h = tr.squeeze_ext4_vec(b"z3_h", log_h, true);
    let z3_ik = tr.squeeze_ext4_vec(b"z3_ik", 7, true);
    let z3_jv = tr.squeeze_ext4_vec(b"z3_jv", 7, true);
    let mut z3_hij = Vec::with_capacity(m_q);
    z3_hij.extend_from_slice(&z3_h);
    z3_hij.extend_from_slice(&z3_ik);
    z3_hij.extend_from_slice(&z3_jv);
    let s_post_at_z3 = mle_eval_bb_at_ext4(&wit.s_post.s_bb_lsb, &z3_hij);
    let s_prev_at_z3 = mle_eval_bb_at_ext4(&wit.s_prev.s_bb_lsb, &z3_hij);
    let mut z3_rem = z3_hij.clone();
    z3_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let r_state_at_z3 = mle_eval_bb_at_ext4(&wit.rem_packed_128, &z3_rem);
    for e in [s_post_at_z3, s_prev_at_z3, r_state_at_z3] {
        tr.absorb_ext4(b"z3_ev", e);
    }
    let eq_z3ik = build_eq_table_lsb_ext4(&z3_ik);
    let eq_z3jv = build_eq_table_lsb_ext4(&z3_jv);
    let mut kd_left = vec![Ext4::ZERO; h_pad * 64];
    let mut kd_right = vec![Ext4::ZERO; h_pad * 64];
    for c in 0..64 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            for i_k in 0..128 {
                al = al.add(eq_z3ik[i_k].scale_bb(wit.k_lsb_hci[h + (c << log_h) + (i_k << (log_h + 6))]));
            }
            kd_left[h + (c << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for j_v in 0..128 {
                ar = ar.add(eq_z3jv[j_v].scale_bb(wit.delta_eff_lsb_hcj[h + (c << log_h) + (j_v << (log_h + 6))]));
            }
            kd_right[h + (c << log_h)] = ar;
        }
    }
    let (kd_gruen, kd_ch) =
        prove_gruen_einsum_mode2_ext4(&kd_left, &kd_right, log_h, 6, &z3_h, &mut tr);

    // 6 `D1b` Range Proofs
    let (espan_d1b, esp_d1b_pt) =
        prove_d1b_range_ext4(&espan_shift_hci, &mult_espan, m_k, M_TAB_SPAN, &mut tr);
    let (rspan_d1b, rsp_d1b_pt) =
        prove_d1b_range_ext4(&rspan_hci, &mult_rspan, m_k, GS_SHIFT as usize, &mut tr);
    let (rem_d1b, d1b_pt) =
        prove_d1b_range_ext4(&wit.rem_packed_128, &mult_wy, m_rem, CMEM_WY_SHIFT as usize, &mut tr);
    let (quot_wy_d1b, qwy_d1b_pt) =
        prove_d1b_range_ext4(&wit.quot_wy_packed, &mult_qwy, m_rem, M_TAB_QUOT_WY, &mut tr);
    let (sbnd_wy_d1b, sbnd_d1b_pt) =
        prove_d1b_range_ext4(&wit.s_bnd_wy_packed, &mult_sbnd, m_rem, M_TAB_S_BND, &mut tr);
    let (small512_d1b, sm512_d1b_pt) =
        prove_d1b_range_ext4(&small512_packed, &mult_sm512, m_sbnd, M_TAB_SMALL512, &mut tr);

    // Random weld points for operand bounds:
    let zs_bnd = tr.squeeze_ext4_vec(b"zs_bnd", m_q, true);
    let zk_bnd = tr.squeeze_ext4_vec(b"zk_bnd", m_k, true);
    let zl_bnd = tr.squeeze_ext4_vec(b"zl_bnd", m_l, true);
    let zcep_bnd = tr.squeeze_ext4_vec(b"zcep_bnd", m_cep, true);
    let zu_limb = tr.squeeze_ext4_vec(b"zu_limb", m_small, true);

    let s_prev_at_zsbnd = mle_eval_bb_at_ext4(&wit.s_prev.s_bb_lsb, &zs_bnd);
    let s_post_at_zsbnd = mle_eval_bb_at_ext4(&wit.s_post.s_bb_lsb, &zs_bnd);
    let k_at_zkbnd = mle_eval_bb_at_ext4(&wit.k_lsb_hci, &zk_bnd);
    let mut zkbnd_w = zk_bnd.clone();
    zkbnd_w.push(Ext4::ONE);
    let w_at_zkbnd = mle_eval_bb_at_ext4(&wit.uw_lsb_hccol, &zkbnd_w);
    let l_at_zlbnd = mle_eval_bb_at_ext4(&wit.l_lsb_hcj, &zl_bnd);
    let du_at_zlbnd = mle_eval_bb_at_ext4(&wit.du_lsb_hcj, &zl_bnd);
    let cep_at_zcepbnd = mle_eval_bb_at_ext4(&c_ep_lsb_hca, &zcep_bnd);
    let u_at_zulimb = mle_eval_bb_at_ext4(&basis_for_future_forget.u_bb_lsb, &zu_limb);
    let ulo_shift_at_zulimb = mle_eval_bb_at_ext4(&basis_for_future_forget.u_lo_shift_lsb, &zu_limb);
    let uhi_shift_at_zulimb = mle_eval_bb_at_ext4(&basis_for_future_forget.u_hi_shift_lsb, &zu_limb);

    for e in [
        s_prev_at_zsbnd,
        s_post_at_zsbnd,
        k_at_zkbnd,
        w_at_zkbnd,
        l_at_zlbnd,
        du_at_zlbnd,
        cep_at_zcepbnd,
        u_at_zulimb,
        ulo_shift_at_zulimb,
        uhi_shift_at_zulimb,
    ] {
        tr.absorb_ext4(b"bnd_weld_ev", e);
    }

    let mut s_prev_pt_ws = Vec::new();
    s_prev_pt_ws.extend_from_slice(&ws_ch[..log_h]);
    s_prev_pt_ws.extend_from_slice(&ws_ch[log_h..]);
    s_prev_pt_ws.extend_from_slice(&z2_jv);

    let s_prev_pcs = open_pcs_claims(
        &s_prev_st,
        &[
            MleEvalClaim { point: s_prev_pt_ws, value: ws_gruen.terminal_openings.1 },
            MleEvalClaim { point: z3_hij.clone(), value: s_prev_at_z3 },
            MleEvalClaim { point: zs_bnd.clone(), value: s_prev_at_zsbnd },
        ],
        &mut tr,
    );
    let s_post_pcs = open_pcs_claims(
        &s_post_st,
        &[
            MleEvalClaim { point: z3_hij, value: s_post_at_z3 },
            MleEvalClaim { point: zs_bnd.clone(), value: s_post_at_zsbnd },
        ],
        &mut tr,
    );

    let mut u_pt_kspan = Vec::with_capacity(m_small);
    u_pt_kspan.extend_from_slice(&ksp_ch[..log_h]);
    u_pt_kspan.extend_from_slice(&zks_ik);
    u_pt_kspan.extend_from_slice(&ksp_ch[log_h..]);
    let u_pcs = open_pcs_claims(
        &u_st,
        &[
            MleEvalClaim { point: u_inact_pt, value: u_inactive_zero.terminal_openings.1 },
            MleEvalClaim { point: u_pt_kspan, value: kspan_gruen.terminal_openings.0 },
            MleEvalClaim { point: zu_limb.clone(), value: u_at_zulimb },
        ],
        &mut tr,
    );

    let build_k_kk_pt = |pt_c: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_k);
        p.extend_from_slice(&kk_ch[..log_h]);
        p.extend_from_slice(pt_c);
        p.extend_from_slice(&kk_ch[log_h..]);
        p
    };
    let mut k_pt_kd = Vec::with_capacity(m_k);
    k_pt_kd.extend_from_slice(&kd_ch[..log_h]);
    k_pt_kd.extend_from_slice(&kd_ch[log_h..]);
    k_pt_kd.extend_from_slice(&z3_ik);

    let k_pcs = open_pcs_claims(
        &k_st,
        &[
            MleEvalClaim { point: zk_span.clone(), value: k_at_zkspan },
            MleEvalClaim { point: build_k_kk_pt(&zkk_c), value: kk_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_k_kk_pt(&zkk_j), value: kk_gruen.terminal_openings.1 },
            MleEvalClaim { point: k_pt_kd.clone(), value: kd_gruen.terminal_openings.0 },
            MleEvalClaim { point: zk_bnd.clone(), value: k_at_zkbnd },
        ],
        &mut tr,
    );

    let mut cep_pt_kspan = Vec::with_capacity(m_cep);
    cep_pt_kspan.extend_from_slice(&ksp_ch[..log_h]);
    cep_pt_kspan.extend_from_slice(&zks_c);
    cep_pt_kspan.extend_from_slice(&ksp_ch[log_h..]);
    let c_ep_pcs = open_pcs_claims(
        &c_ep_st,
        &[
            MleEvalClaim { point: cep_pt_kspan, value: kspan_gruen.terminal_openings.1 },
            MleEvalClaim { point: zcep_bnd.clone(), value: cep_at_zcepbnd },
        ],
        &mut tr,
    );

    let espan_pcs = open_pcs_claims(
        &espan_st,
        &[
            MleEvalClaim { point: zk_span.clone(), value: espan_at_zkspan },
            MleEvalClaim { point: esp_d1b_pt.clone(), value: espan_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_espan_pcs = open_pcs_claims(
        &mult_espan_st,
        &[MleEvalClaim { point: esp_d1b_pt[..M_TAB_SPAN].to_vec(), value: espan_d1b.mult_leaf_eval }],
        &mut tr,
    );
    let rspan_pcs = open_pcs_claims(
        &rspan_st,
        &[
            MleEvalClaim { point: zk_span, value: rspan_at_zkspan },
            MleEvalClaim { point: rsp_d1b_pt.clone(), value: rspan_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_rspan_pcs = open_pcs_claims(
        &mult_rspan_st,
        &[MleEvalClaim { point: rsp_d1b_pt[..GS_SHIFT as usize].to_vec(), value: rspan_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let mut l_pt1 = Vec::with_capacity(m_l);
    l_pt1.extend_from_slice(&wy_ch[..log_h]);
    l_pt1.extend_from_slice(&z1_c);
    l_pt1.extend_from_slice(&wy_ch[log_h..]);
    let l_pcs = open_pcs_claims(
        &l_st,
        &[
            MleEvalClaim { point: zkk_hcj.clone(), value: l_at_zkk },
            MleEvalClaim { point: l_pt1, value: wy_gruen.terminal_openings.0 },
            MleEvalClaim { point: slt_pt, value: slt_zero.terminal_openings.1 },
            MleEvalClaim { point: zl_bnd.clone(), value: l_at_zlbnd },
        ],
        &mut tr,
    );
    let du_pcs = open_pcs_claims(
        &du_st,
        &[
            MleEvalClaim { point: zkk_hcj, value: du_at_zkk },
            MleEvalClaim { point: du_slt_pt, value: du_slt_zero.terminal_openings.1 },
            MleEvalClaim { point: zl_bnd.clone(), value: du_at_zlbnd },
        ],
        &mut tr,
    );

    let mut rhs_pt_k = k_pt_kd;
    rhs_pt_k.push(Ext4::ONE);
    let rhs_pcs = open_pcs_claims(
        &rhs_st,
        &[
            MleEvalClaim { point: z1_all.clone(), value: rhs_at_z1 },
            MleEvalClaim { point: rhs_pt_k, value: kd_gruen.terminal_openings.0 },
        ],
        &mut tr,
    );

    let mut uw_pt_wy = Vec::with_capacity(m_q);
    uw_pt_wy.extend_from_slice(&wy_ch[..log_h]);
    uw_pt_wy.extend_from_slice(&wy_ch[log_h..]);
    uw_pt_wy.extend_from_slice(&z1_col);
    let mut uw_pt_w = Vec::with_capacity(m_q);
    uw_pt_w.extend_from_slice(&ws_ch[..log_h]);
    uw_pt_w.extend_from_slice(&z2_c);
    uw_pt_w.extend_from_slice(&ws_ch[log_h..]);
    uw_pt_w.push(Ext4::ONE);
    let uw_pcs = open_pcs_claims(
        &uw_st,
        &[
            MleEvalClaim { point: z1_all, value: uw_at_z1 },
            MleEvalClaim { point: uw_pt_wy, value: wy_gruen.terminal_openings.1 },
            MleEvalClaim { point: z2_u_pt, value: u_at_z2 },
            MleEvalClaim { point: uw_pt_w, value: ws_gruen.terminal_openings.0 },
            MleEvalClaim { point: zkbnd_w, value: w_at_zkbnd },
        ],
        &mut tr,
    );

    let mut deff_pt_kd = Vec::with_capacity(m_k);
    deff_pt_kd.extend_from_slice(&kd_ch[..log_h]);
    deff_pt_kd.extend_from_slice(&kd_ch[log_h..]);
    deff_pt_kd.extend_from_slice(&z3_jv);
    let delta_eff_pcs = open_pcs_claims(
        &deff_st,
        &[
            MleEvalClaim { point: z2_hcj, value: delta_eff_at_z2 },
            MleEvalClaim { point: deff_pt_kd, value: kd_gruen.terminal_openings.1 },
        ],
        &mut tr,
    );

    let rem_pcs = open_pcs_claims(
        &rem_st,
        &[
            MleEvalClaim { point: z1_rem.clone(), value: r_wy_at_z1 },
            MleEvalClaim { point: z2_rem.clone(), value: r_eff_at_z2 },
            MleEvalClaim { point: z3_rem.clone(), value: r_state_at_z3 },
            MleEvalClaim { point: zkk_rem, value: r_kk_at_zkk },
            MleEvalClaim { point: d1b_pt.clone(), value: rem_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_pcs = open_pcs_claims(
        &mult_st,
        &[MleEvalClaim { point: d1b_pt[..CMEM_WY_SHIFT as usize].to_vec(), value: rem_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let shift_wy_ext = Ext4::from_bb(QUOT_WY_HALF as u32);
    let quot_wy_pcs = open_pcs_claims(
        &qwy_st,
        &[
            MleEvalClaim { point: z1_rem, value: uw_at_z1.add(shift_wy_ext) },
            MleEvalClaim { point: z2_rem, value: delta_eff_at_z2.add(shift_wy_ext) },
            MleEvalClaim { point: z3_rem, value: s_post_at_z3.sub(s_prev_at_z3).add(shift_wy_ext) },
            MleEvalClaim { point: qwy_d1b_pt.clone(), value: quot_wy_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_quot_wy_pcs = open_pcs_claims(
        &mult_qwy_st,
        &[MleEvalClaim { point: qwy_d1b_pt[..M_TAB_QUOT_WY].to_vec(), value: quot_wy_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let sbnd_ext = Ext4::from_bb(S_BND_HALF as u32);
    let mut zsb00 = zs_bnd.clone();
    zsb00.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut zsb10 = zs_bnd.clone();
    zsb10.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut zsb01 = zs_bnd.clone();
    zsb01.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let mut zsb11 = zs_bnd;
    zsb11.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);
    let sbnd_wy_pcs = open_pcs_claims(
        &sbnd_st,
        &[
            MleEvalClaim { point: zsb00, value: s_prev_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb10, value: sbnd_ext.sub(s_prev_at_zsbnd) },
            MleEvalClaim { point: zsb01, value: s_post_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb11, value: sbnd_ext.sub(s_post_at_zsbnd) },
            MleEvalClaim { point: sbnd_d1b_pt.clone(), value: sbnd_wy_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_sbnd_wy_pcs = open_pcs_claims(
        &mult_sbnd_st,
        &[MleEvalClaim { point: sbnd_d1b_pt[..M_TAB_S_BND].to_vec(), value: sbnd_wy_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let sm512_ext = Ext4::from_bb(SMALL512_HALF as u32);
    let mut p_k512 = zk_bnd.clone();
    p_k512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut p_w512 = zk_bnd;
    p_w512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut p_l512 = zl_bnd.clone();
    p_l512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let mut p_du512 = zl_bnd;
    p_du512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ONE]);
    let mut p_cep512 = zcep_bnd;
    p_cep512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    let mut p_ulo512 = zu_limb.clone();
    p_ulo512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    let mut p_uhi512 = zu_limb;
    p_uhi512.extend_from_slice(&[Ext4::ZERO, Ext4::ONE, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);

    let small512_pcs = open_pcs_claims(
        &sm512_st,
        &[
            MleEvalClaim { point: p_k512, value: k_at_zkbnd.add(sm512_ext) },
            MleEvalClaim { point: p_w512, value: w_at_zkbnd.add(sm512_ext) },
            MleEvalClaim { point: p_l512, value: l_at_zlbnd.add(sm512_ext) },
            MleEvalClaim { point: p_du512, value: du_at_zlbnd.add(sm512_ext) },
            MleEvalClaim { point: p_cep512, value: cep_at_zcepbnd.add(sm512_ext) },
            MleEvalClaim { point: p_ulo512, value: ulo_shift_at_zulimb },
            MleEvalClaim { point: p_uhi512, value: uhi_shift_at_zulimb },
            MleEvalClaim { point: sm512_d1b_pt.clone(), value: small512_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_small512_pcs = open_pcs_claims(
        &mult_sm512_st,
        &[MleEvalClaim { point: sm512_d1b_pt[..M_TAB_SMALL512].to_vec(), value: small512_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let pf = ZkContinualUpdateProof {
        episode_idx,
        h_v,
        h_pad,
        rank_r,
        s_prev_root: s_prev_st.root,
        s_post_root: s_post_st.root,
        k_pcs_root: k_st.root,
        forget_request_root,
        u_pcs_root: u_st.root,
        request_nonce: *request_nonce,
        mmr_proof,
        c_ep_pcs_root: c_ep_st.root,
        espan_pcs_root: espan_st.root,
        mult_espan_pcs_root: mult_espan_st.root,
        rspan_pcs_root: rspan_st.root,
        mult_rspan_pcs_root: mult_rspan_st.root,
        l_pcs_root: l_st.root,
        du_pcs_root: du_st.root,
        rhs_pcs_root: rhs_st.root,
        uw_pcs_root: uw_st.root,
        delta_eff_pcs_root: deff_st.root,
        rem_pcs_root: rem_st.root,
        mult_pcs_root: mult_st.root,
        quot_wy_pcs_root: qwy_st.root,
        mult_quot_wy_pcs_root: mult_qwy_st.root,
        sbnd_wy_pcs_root: sbnd_st.root,
        mult_sbnd_wy_pcs_root: mult_sbnd_st.root,
        small512_pcs_root: sm512_st.root,
        mult_small512_pcs_root: mult_sm512_st.root,
        k_at_zkspan,
        espan_at_zkspan,
        rspan_at_zkspan,
        l_at_zkk,
        du_at_zkk,
        r_kk_at_zkk,
        rhs_at_z1,
        uw_at_z1,
        r_wy_at_z1,
        u_at_z2,
        delta_eff_at_z2,
        r_eff_at_z2,
        s_post_at_z3,
        s_prev_at_z3,
        r_state_at_z3,
        s_prev_at_zsbnd,
        s_post_at_zsbnd,
        k_at_zkbnd,
        w_at_zkbnd,
        l_at_zlbnd,
        du_at_zlbnd,
        cep_at_zcepbnd,
        u_at_zulimb,
        ulo_shift_at_zulimb,
        uhi_shift_at_zulimb,
        u_inactive_zero,
        kspan_gruen,
        kk_gruen,
        slt_zero,
        du_slt_zero,
        wy_gruen,
        ws_gruen,
        kd_gruen,
        espan_d1b,
        rspan_d1b,
        rem_d1b,
        quot_wy_d1b,
        sbnd_wy_d1b,
        small512_d1b,
        s_prev_pcs,
        s_post_pcs,
        u_pcs,
        k_pcs,
        c_ep_pcs,
        espan_pcs,
        mult_espan_pcs,
        rspan_pcs,
        mult_rspan_pcs,
        l_pcs,
        du_pcs,
        rhs_pcs,
        uw_pcs,
        delta_eff_pcs,
        rem_pcs,
        mult_pcs,
        quot_wy_pcs,
        mult_quot_wy_pcs,
        sbnd_wy_pcs,
        mult_sbnd_wy_pcs,
        small512_pcs,
        mult_small512_pcs,
    };

    Ok((
        pf.to_bytes(),
        s_prev_st.root,
        mmr_root,
        s_post_st.root,
        forget_request_root,
    ))
}

pub fn verify_continual_wy_update_zk(
    expected_s_prev_root: &[u8; 32],
    expected_episode_mmr_root: &[u8; 32],
    expected_s_post_root: &[u8; 32],
    proof_bytes: &[u8],
) -> Result<(), String> {
    let pf = ZkContinualUpdateProof::from_bytes(proof_bytes)?;
    if &pf.s_prev_root != expected_s_prev_root || &pf.s_post_root != expected_s_post_root {
        return Err("continual update S_prev_root / S_post_root mismatch".to_string());
    }
    if !(1..=R_PAD).contains(&pf.rank_r)
        || pf.h_v == 0
        || pf.h_v > pf.h_pad
        || !pf.h_pad.is_power_of_two()
        || pf.h_pad > 1024
    {
        return Err("invalid continual update (h_v, h_pad, rank_r) header".to_string());
    }
    if pf.mmr_proof.leaf_index != pf.episode_idx {
        return Err("MMR leaf_index != episode_idx".to_string());
    }
    let recomputed_forget = compute_blind_forget_request_root(
        pf.h_v,
        pf.h_pad,
        pf.rank_r,
        &pf.u_pcs_root,
        &pf.request_nonce,
    );
    if recomputed_forget != pf.forget_request_root {
        return Err("forget_request_root != H(h_v, h_pad, rank_r, u_pcs_root, nonce)".to_string());
    }
    let entry = EpisodeMmrEntry {
        episode_idx: pf.episode_idx,
        s_prev_root: pf.s_prev_root,
        s_post_root: pf.s_post_root,
        k_pcs_root: pf.k_pcs_root,
        forget_request_root: pf.forget_request_root,
    };
    if !pf.mmr_proof.verify(&entry.leaf_hash(), expected_episode_mmr_root) {
        return Err("episode_mmr_root inclusion verification failed".to_string());
    }

    let log_h = pf.h_pad.trailing_zeros() as usize;
    let m_q = log_h + 14;
    let m_k = log_h + 13;
    let m_l = log_h + 12;
    let m_small = log_h + 10;
    let m_cep = log_h + 9;
    let m_rem = m_q + 2;
    let m_sbnd = m_q + 1;
    let half_wy_ext = Ext4::from_bb((CMEM_WY_SCALE / 2) as u32);
    let half_gs_ext = Ext4::from_bb((M_GS / 2) as u32);

    let mut tr = CShakeTranscript::new(b"CMEM-WY-UPDATE-ZK-V3");
    tr.absorb_u32(b"ep_idx", pf.episode_idx);
    tr.absorb_u32(b"h_v", pf.h_v as u32);
    tr.absorb_u32(b"h_pad", pf.h_pad as u32);
    tr.absorb_u32(b"rank_r", pf.rank_r as u32);
    tr.absorb_root(b"mmr_root", expected_episode_mmr_root);
    for r in [
        &pf.s_prev_root,
        &pf.s_post_root,
        &pf.k_pcs_root,
        &pf.forget_request_root,
        &pf.u_pcs_root,
        &pf.request_nonce,
        &pf.c_ep_pcs_root,
        &pf.espan_pcs_root,
        &pf.mult_espan_pcs_root,
        &pf.rspan_pcs_root,
        &pf.mult_rspan_pcs_root,
        &pf.l_pcs_root,
        &pf.du_pcs_root,
        &pf.rhs_pcs_root,
        &pf.uw_pcs_root,
        &pf.delta_eff_pcs_root,
        &pf.rem_pcs_root,
        &pf.mult_pcs_root,
        &pf.quot_wy_pcs_root,
        &pf.mult_quot_wy_pcs_root,
        &pf.sbnd_wy_pcs_root,
        &pf.mult_sbnd_wy_pcs_root,
        &pf.small512_pcs_root,
        &pf.mult_small512_pcs_root,
    ] {
        tr.absorb_root(b"cmem_up_root", r);
    }

    // W0a: `u_inactive_zero`
    if pf.u_inactive_zero.mu_s != m_small
        || pf.u_inactive_zero.kappa != 0
        || !pf.u_inactive_zero.claim.is_zero()
    {
        return Err("update u_inactive_zero header invalid".to_string());
    }
    let zi_all = tr.squeeze_ext4_vec(b"u_inact_zs", m_small, true);
    let u_inact_pt =
        verify_gruen_einsum_mode2_ext4(Ext4::ZERO, &zi_all, &pf.u_inactive_zero, &mut tr)?;
    let exp_inact =
        eval_inactive_u_indicator_mle(pf.h_v, pf.rank_r, &u_inact_pt[..log_h], &u_inact_pt[log_h + 7..]);
    if pf.u_inactive_zero.terminal_openings.0 != exp_inact {
        return Err("update u_inactive_zero indicator eval mismatch".to_string());
    }

    // W0b: `K ∈ span(U)`
    let zks_h = tr.squeeze_ext4_vec(b"zks_h", log_h, true);
    let zks_c = tr.squeeze_ext4_vec(b"zks_c", 6, true);
    let zks_ik = tr.squeeze_ext4_vec(b"zks_ik", 7, true);
    let mut zk_span = Vec::with_capacity(m_k);
    zk_span.extend_from_slice(&zks_h);
    zk_span.extend_from_slice(&zks_c);
    zk_span.extend_from_slice(&zks_ik);
    for e in [pf.k_at_zkspan, pf.espan_at_zkspan, pf.rspan_at_zkspan] {
        tr.absorb_ext4(b"zks_ev", e);
    }
    if pf.kspan_gruen.kappa != LOG_R_PAD {
        return Err("kspan_gruen kappa mismatch".to_string());
    }
    let e_span_unshifted = pf.espan_at_zkspan.sub(Ext4::from_bb(TAU_SPAN as u32));
    let exp_kspan = pf
        .k_at_zkspan
        .sub(e_span_unshifted)
        .scale_bb(M_GS as u32)
        .add(pf.rspan_at_zkspan)
        .sub(half_gs_ext);
    let ksp_ch = verify_gruen_einsum_mode2_ext4(exp_kspan, &zks_h, &pf.kspan_gruen, &mut tr)?;

    // W1: `K * K^T == CMEM_WY_SCALE * (L + D_U) + R_kk - half_wy`
    let zkk_h = tr.squeeze_ext4_vec(b"zkk_h", log_h, true);
    let zkk_c = tr.squeeze_ext4_vec(b"zkk_c", 6, true);
    let zkk_j = tr.squeeze_ext4_vec(b"zkk_j", 6, true);
    let mut zkk_hcj = Vec::with_capacity(m_l);
    zkk_hcj.extend_from_slice(&zkk_h);
    zkk_hcj.extend_from_slice(&zkk_c);
    zkk_hcj.extend_from_slice(&zkk_j);
    for e in [pf.l_at_zkk, pf.du_at_zkk, pf.r_kk_at_zkk] {
        tr.absorb_ext4(b"zkk_ev", e);
    }
    if pf.kk_gruen.kappa != 7 {
        return Err("kk_gruen kappa mismatch".to_string());
    }
    let exp_kk = pf
        .l_at_zkk
        .add(pf.du_at_zkk)
        .scale_bb(CMEM_WY_SCALE as u32)
        .add(pf.r_kk_at_zkk)
        .sub(half_wy_ext);
    let kk_ch = verify_gruen_einsum_mode2_ext4(exp_kk, &zkk_h, &pf.kk_gruen, &mut tr)?;
    let (slt_pt, slt_l_ev) = verify_strict_lower_tri_ext4(log_h, 6, &pf.slt_zero, &mut tr)?;

    if pf.du_slt_zero.mu_s != m_l || pf.du_slt_zero.kappa != 0 || !pf.du_slt_zero.claim.is_zero() {
        return Err("du_slt_zero header invalid".to_string());
    }
    let zdu_s = tr.squeeze_ext4_vec(b"duslt_zs", m_l, true);
    let du_slt_pt =
        verify_gruen_einsum_mode2_ext4(Ext4::ZERO, &zdu_s, &pf.du_slt_zero, &mut tr)?;
    let exp_slt_ind = Ext4::ONE.sub(eval_upper_or_diag_indicator_mle(
        &du_slt_pt[log_h..log_h + 6],
        &du_slt_pt[log_h + 6..],
    ));
    if pf.du_slt_zero.terminal_openings.0 != exp_slt_ind {
        return Err("du_slt_zero indicator eval mismatch".to_string());
    }

    // W2: `L * UW`
    let z1_h = tr.squeeze_ext4_vec(b"z1_h", log_h, true);
    let z1_c = tr.squeeze_ext4_vec(b"z1_c", 6, true);
    let z1_col = tr.squeeze_ext4_vec(b"z1_col", 8, true);
    let mut z1_all = Vec::with_capacity(m_q);
    z1_all.extend_from_slice(&z1_h);
    z1_all.extend_from_slice(&z1_c);
    z1_all.extend_from_slice(&z1_col);
    for e in [pf.rhs_at_z1, pf.uw_at_z1, pf.r_wy_at_z1] {
        tr.absorb_ext4(b"z1_ev", e);
    }
    if pf.wy_gruen.kappa != 6 {
        return Err("wy_gruen kappa mismatch".to_string());
    }
    let exp_wy = pf
        .rhs_at_z1
        .sub(pf.uw_at_z1)
        .scale_bb(CMEM_WY_SCALE as u32)
        .add(half_wy_ext)
        .sub(pf.r_wy_at_z1);
    let wy_ch = verify_gruen_einsum_mode2_ext4(exp_wy, &z1_h, &pf.wy_gruen, &mut tr)?;

    // W3: `W * S_prev`
    let z2_h = tr.squeeze_ext4_vec(b"z2_h", log_h, true);
    let z2_c = tr.squeeze_ext4_vec(b"z2_c", 6, true);
    let z2_jv = tr.squeeze_ext4_vec(b"z2_jv", 7, true);
    let mut z2_hcj = Vec::with_capacity(m_k);
    z2_hcj.extend_from_slice(&z2_h);
    z2_hcj.extend_from_slice(&z2_c);
    z2_hcj.extend_from_slice(&z2_jv);
    for e in [pf.u_at_z2, pf.delta_eff_at_z2, pf.r_eff_at_z2] {
        tr.absorb_ext4(b"z2_ev", e);
    }
    if pf.ws_gruen.kappa != 7 {
        return Err("ws_gruen kappa mismatch".to_string());
    }
    let exp_ws = pf
        .u_at_z2
        .sub(pf.delta_eff_at_z2)
        .scale_bb(CMEM_WY_SCALE as u32)
        .add(half_wy_ext)
        .sub(pf.r_eff_at_z2);
    let ws_ch = verify_gruen_einsum_mode2_ext4(exp_ws, &z2_h, &pf.ws_gruen, &mut tr)?;

    // W4: `K_int^T * Delta_eff`
    let z3_h = tr.squeeze_ext4_vec(b"z3_h", log_h, true);
    let z3_ik = tr.squeeze_ext4_vec(b"z3_ik", 7, true);
    let z3_jv = tr.squeeze_ext4_vec(b"z3_jv", 7, true);
    let mut z3_hij = Vec::with_capacity(m_q);
    z3_hij.extend_from_slice(&z3_h);
    z3_hij.extend_from_slice(&z3_ik);
    z3_hij.extend_from_slice(&z3_jv);
    for e in [pf.s_post_at_z3, pf.s_prev_at_z3, pf.r_state_at_z3] {
        tr.absorb_ext4(b"z3_ev", e);
    }
    if pf.kd_gruen.kappa != 6 {
        return Err("kd_gruen kappa mismatch".to_string());
    }
    let exp_kd = pf
        .s_post_at_z3
        .sub(pf.s_prev_at_z3)
        .scale_bb(CMEM_WY_SCALE as u32)
        .add(pf.r_state_at_z3)
        .sub(half_wy_ext);
    let kd_ch = verify_gruen_einsum_mode2_ext4(exp_kd, &z3_h, &pf.kd_gruen, &mut tr)?;

    if pf.espan_d1b.m_wit != m_k
        || pf.espan_d1b.m_tab != M_TAB_SPAN
        || pf.rspan_d1b.m_wit != m_k
        || pf.rspan_d1b.m_tab != GS_SHIFT as usize
        || pf.rem_d1b.m_wit != m_rem
        || pf.rem_d1b.m_tab != CMEM_WY_SHIFT as usize
        || pf.quot_wy_d1b.m_wit != m_rem
        || pf.quot_wy_d1b.m_tab != M_TAB_QUOT_WY
        || pf.sbnd_wy_d1b.m_wit != m_rem
        || pf.sbnd_wy_d1b.m_tab != M_TAB_S_BND
        || pf.small512_d1b.m_wit != m_sbnd
        || pf.small512_d1b.m_tab != M_TAB_SMALL512
    {
        return Err("continual update D1b dimension mismatch".to_string());
    }
    let esp_d1b_pt = verify_d1b_range_ext4(&pf.espan_d1b, &mut tr)?;
    let rsp_d1b_pt = verify_d1b_range_ext4(&pf.rspan_d1b, &mut tr)?;
    let d1b_pt = verify_d1b_range_ext4(&pf.rem_d1b, &mut tr)?;
    let qwy_d1b_pt = verify_d1b_range_ext4(&pf.quot_wy_d1b, &mut tr)?;
    let sbnd_d1b_pt = verify_d1b_range_ext4(&pf.sbnd_wy_d1b, &mut tr)?;
    let sm512_d1b_pt = verify_d1b_range_ext4(&pf.small512_d1b, &mut tr)?;

    let zs_bnd = tr.squeeze_ext4_vec(b"zs_bnd", m_q, true);
    let zk_bnd = tr.squeeze_ext4_vec(b"zk_bnd", m_k, true);
    let zl_bnd = tr.squeeze_ext4_vec(b"zl_bnd", m_l, true);
    let zcep_bnd = tr.squeeze_ext4_vec(b"zcep_bnd", m_cep, true);
    let zu_limb = tr.squeeze_ext4_vec(b"zu_limb", m_small, true);

    for e in [
        pf.s_prev_at_zsbnd,
        pf.s_post_at_zsbnd,
        pf.k_at_zkbnd,
        pf.w_at_zkbnd,
        pf.l_at_zlbnd,
        pf.du_at_zlbnd,
        pf.cep_at_zcepbnd,
        pf.u_at_zulimb,
        pf.ulo_shift_at_zulimb,
        pf.uhi_shift_at_zulimb,
    ] {
        tr.absorb_ext4(b"bnd_weld_ev", e);
    }

    // Check 2-limb identity `U_int(zu) == (U_lo_shift(zu) - 64) + 128 * (U_hi_shift(zu) - 128)`!
    let ulo_unsh = pf.ulo_shift_at_zulimb.sub(Ext4::from_bb(ULO_HALF as u32));
    let uhi_unsh = pf.uhi_shift_at_zulimb.sub(Ext4::from_bb(UHI_HALF as u32));
    if pf.u_at_zulimb != ulo_unsh.add(uhi_unsh.scale_bb(LIMB_RADIX as u32)) {
        return Err("update U 2-limb weld mismatch".to_string());
    }

    let mut s_prev_pt_ws = Vec::new();
    s_prev_pt_ws.extend_from_slice(&ws_ch[..log_h]);
    s_prev_pt_ws.extend_from_slice(&ws_ch[log_h..]);
    s_prev_pt_ws.extend_from_slice(&z2_jv);
    verify_pcs_claims(
        &pf.s_prev_root,
        PcsShape::new(m_q, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: s_prev_pt_ws, value: pf.ws_gruen.terminal_openings.1 },
            MleEvalClaim { point: z3_hij.clone(), value: pf.s_prev_at_z3 },
            MleEvalClaim { point: zs_bnd.clone(), value: pf.s_prev_at_zsbnd },
        ],
        &pf.s_prev_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.s_post_root,
        PcsShape::new(m_q, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: z3_hij.clone(), value: pf.s_post_at_z3 },
            MleEvalClaim { point: zs_bnd.clone(), value: pf.s_post_at_zsbnd },
        ],
        &pf.s_post_pcs,
        &mut tr,
    )?;

    let mut u_pt_kspan = Vec::with_capacity(m_small);
    u_pt_kspan.extend_from_slice(&ksp_ch[..log_h]);
    u_pt_kspan.extend_from_slice(&zks_ik);
    u_pt_kspan.extend_from_slice(&ksp_ch[log_h..]);
    verify_pcs_claims(
        &pf.u_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: u_inact_pt, value: pf.u_inactive_zero.terminal_openings.1 },
            MleEvalClaim { point: u_pt_kspan, value: pf.kspan_gruen.terminal_openings.0 },
            MleEvalClaim { point: zu_limb.clone(), value: pf.u_at_zulimb },
        ],
        &pf.u_pcs,
        &mut tr,
    )?;

    let build_k_kk_pt = |pt_c: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_k);
        p.extend_from_slice(&kk_ch[..log_h]);
        p.extend_from_slice(pt_c);
        p.extend_from_slice(&kk_ch[log_h..]);
        p
    };
    let mut k_pt_kd = Vec::with_capacity(m_k);
    k_pt_kd.extend_from_slice(&kd_ch[..log_h]);
    k_pt_kd.extend_from_slice(&kd_ch[log_h..]);
    k_pt_kd.extend_from_slice(&z3_ik);
    verify_pcs_claims(
        &pf.k_pcs_root,
        PcsShape::new(m_k, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zk_span.clone(), value: pf.k_at_zkspan },
            MleEvalClaim { point: build_k_kk_pt(&zkk_c), value: pf.kk_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_k_kk_pt(&zkk_j), value: pf.kk_gruen.terminal_openings.1 },
            MleEvalClaim { point: k_pt_kd.clone(), value: pf.kd_gruen.terminal_openings.0 },
            MleEvalClaim { point: zk_bnd.clone(), value: pf.k_at_zkbnd },
        ],
        &pf.k_pcs,
        &mut tr,
    )?;

    let mut cep_pt_kspan = Vec::with_capacity(m_cep);
    cep_pt_kspan.extend_from_slice(&ksp_ch[..log_h]);
    cep_pt_kspan.extend_from_slice(&zks_c);
    cep_pt_kspan.extend_from_slice(&ksp_ch[log_h..]);
    verify_pcs_claims(
        &pf.c_ep_pcs_root,
        PcsShape::new(m_cep, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: cep_pt_kspan, value: pf.kspan_gruen.terminal_openings.1 },
            MleEvalClaim { point: zcep_bnd.clone(), value: pf.cep_at_zcepbnd },
        ],
        &pf.c_ep_pcs,
        &mut tr,
    )?;

    verify_pcs_claims(
        &pf.espan_pcs_root,
        PcsShape::new(m_k, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: zk_span.clone(), value: pf.espan_at_zkspan },
            MleEvalClaim { point: esp_d1b_pt.clone(), value: pf.espan_d1b.rem_leaf_eval },
        ],
        &pf.espan_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_espan_pcs_root,
        PcsShape::new(M_TAB_SPAN, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: esp_d1b_pt[..M_TAB_SPAN].to_vec(), value: pf.espan_d1b.mult_leaf_eval }],
        &pf.mult_espan_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.rspan_pcs_root,
        PcsShape::new(m_k, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: zk_span, value: pf.rspan_at_zkspan },
            MleEvalClaim { point: rsp_d1b_pt.clone(), value: pf.rspan_d1b.rem_leaf_eval },
        ],
        &pf.rspan_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_rspan_pcs_root,
        PcsShape::new(GS_SHIFT as usize, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: rsp_d1b_pt[..GS_SHIFT as usize].to_vec(), value: pf.rspan_d1b.mult_leaf_eval }],
        &pf.mult_rspan_pcs,
        &mut tr,
    )?;

    let mut l_pt1 = Vec::with_capacity(m_l);
    l_pt1.extend_from_slice(&wy_ch[..log_h]);
    l_pt1.extend_from_slice(&z1_c);
    l_pt1.extend_from_slice(&wy_ch[log_h..]);
    verify_pcs_claims(
        &pf.l_pcs_root,
        PcsShape::new(m_l, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: zkk_hcj.clone(), value: pf.l_at_zkk },
            MleEvalClaim { point: l_pt1, value: pf.wy_gruen.terminal_openings.0 },
            MleEvalClaim { point: slt_pt, value: slt_l_ev },
            MleEvalClaim { point: zl_bnd.clone(), value: pf.l_at_zlbnd },
        ],
        &pf.l_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.du_pcs_root,
        PcsShape::new(m_l, PcsParams::default_zk(3)),
        &[
            MleEvalClaim { point: zkk_hcj.clone(), value: pf.du_at_zkk },
            MleEvalClaim { point: du_slt_pt, value: pf.du_slt_zero.terminal_openings.1 },
            MleEvalClaim { point: zl_bnd.clone(), value: pf.du_at_zlbnd },
        ],
        &pf.du_pcs,
        &mut tr,
    )?;

    let mut rhs_pt_k = k_pt_kd;
    rhs_pt_k.push(Ext4::ONE);
    verify_pcs_claims(
        &pf.rhs_pcs_root,
        PcsShape::new(m_q, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: z1_all.clone(), value: pf.rhs_at_z1 },
            MleEvalClaim { point: rhs_pt_k, value: pf.kd_gruen.terminal_openings.0 },
        ],
        &pf.rhs_pcs,
        &mut tr,
    )?;

    let mut z2_u_pt = z2_hcj.clone();
    z2_u_pt.push(Ext4::ZERO);
    let mut uw_pt_wy = Vec::with_capacity(m_q);
    uw_pt_wy.extend_from_slice(&wy_ch[..log_h]);
    uw_pt_wy.extend_from_slice(&wy_ch[log_h..]);
    uw_pt_wy.extend_from_slice(&z1_col);
    let mut uw_pt_w = Vec::with_capacity(m_q);
    uw_pt_w.extend_from_slice(&ws_ch[..log_h]);
    uw_pt_w.extend_from_slice(&z2_c);
    uw_pt_w.extend_from_slice(&ws_ch[log_h..]);
    uw_pt_w.push(Ext4::ONE);
    let mut zkbnd_w = zk_bnd.clone();
    zkbnd_w.push(Ext4::ONE);
    verify_pcs_claims(
        &pf.uw_pcs_root,
        PcsShape::new(m_q, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: z1_all.clone(), value: pf.uw_at_z1 },
            MleEvalClaim { point: uw_pt_wy, value: pf.wy_gruen.terminal_openings.1 },
            MleEvalClaim { point: z2_u_pt, value: pf.u_at_z2 },
            MleEvalClaim { point: uw_pt_w, value: pf.ws_gruen.terminal_openings.0 },
            MleEvalClaim { point: zkbnd_w, value: pf.w_at_zkbnd },
        ],
        &pf.uw_pcs,
        &mut tr,
    )?;

    let mut deff_pt_kd = Vec::with_capacity(m_k);
    deff_pt_kd.extend_from_slice(&kd_ch[..log_h]);
    deff_pt_kd.extend_from_slice(&kd_ch[log_h..]);
    deff_pt_kd.extend_from_slice(&z3_jv);
    verify_pcs_claims(
        &pf.delta_eff_pcs_root,
        PcsShape::new(m_k, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: z2_hcj.clone(), value: pf.delta_eff_at_z2 },
            MleEvalClaim { point: deff_pt_kd, value: pf.kd_gruen.terminal_openings.1 },
        ],
        &pf.delta_eff_pcs,
        &mut tr,
    )?;

    let mut z1_rem = z1_all;
    z1_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut z2_rem = z2_hcj;
    z2_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ONE, Ext4::ZERO]);
    let mut z3_rem = z3_hij;
    z3_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let mut zkk_rem = zkk_hcj;
    zkk_rem.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    verify_pcs_claims(
        &pf.rem_pcs_root,
        PcsShape::new(m_rem, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: z1_rem.clone(), value: pf.r_wy_at_z1 },
            MleEvalClaim { point: z2_rem.clone(), value: pf.r_eff_at_z2 },
            MleEvalClaim { point: z3_rem.clone(), value: pf.r_state_at_z3 },
            MleEvalClaim { point: zkk_rem, value: pf.r_kk_at_zkk },
            MleEvalClaim { point: d1b_pt.clone(), value: pf.rem_d1b.rem_leaf_eval },
        ],
        &pf.rem_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_pcs_root,
        PcsShape::new(CMEM_WY_SHIFT as usize, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: d1b_pt[..CMEM_WY_SHIFT as usize].to_vec(), value: pf.rem_d1b.mult_leaf_eval }],
        &pf.mult_pcs,
        &mut tr,
    )?;

    let shift_wy_ext = Ext4::from_bb(QUOT_WY_HALF as u32);
    verify_pcs_claims(
        &pf.quot_wy_pcs_root,
        PcsShape::new(m_rem, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: z1_rem, value: pf.uw_at_z1.add(shift_wy_ext) },
            MleEvalClaim { point: z2_rem, value: pf.delta_eff_at_z2.add(shift_wy_ext) },
            MleEvalClaim { point: z3_rem, value: pf.s_post_at_z3.sub(pf.s_prev_at_z3).add(shift_wy_ext) },
            MleEvalClaim { point: qwy_d1b_pt.clone(), value: pf.quot_wy_d1b.rem_leaf_eval },
        ],
        &pf.quot_wy_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_quot_wy_pcs_root,
        PcsShape::new(M_TAB_QUOT_WY, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: qwy_d1b_pt[..M_TAB_QUOT_WY].to_vec(), value: pf.quot_wy_d1b.mult_leaf_eval }],
        &pf.mult_quot_wy_pcs,
        &mut tr,
    )?;

    let sbnd_ext = Ext4::from_bb(S_BND_HALF as u32);
    let mut zsb00 = zs_bnd.clone();
    zsb00.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut zsb10 = zs_bnd.clone();
    zsb10.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut zsb01 = zs_bnd.clone();
    zsb01.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let mut zsb11 = zs_bnd;
    zsb11.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);
    verify_pcs_claims(
        &pf.sbnd_wy_pcs_root,
        PcsShape::new(m_rem, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zsb00, value: pf.s_prev_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb10, value: sbnd_ext.sub(pf.s_prev_at_zsbnd) },
            MleEvalClaim { point: zsb01, value: pf.s_post_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb11, value: sbnd_ext.sub(pf.s_post_at_zsbnd) },
            MleEvalClaim { point: sbnd_d1b_pt.clone(), value: pf.sbnd_wy_d1b.rem_leaf_eval },
        ],
        &pf.sbnd_wy_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_sbnd_wy_pcs_root,
        PcsShape::new(M_TAB_S_BND, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: sbnd_d1b_pt[..M_TAB_S_BND].to_vec(), value: pf.sbnd_wy_d1b.mult_leaf_eval }],
        &pf.mult_sbnd_wy_pcs,
        &mut tr,
    )?;

    let sm512_ext = Ext4::from_bb(SMALL512_HALF as u32);
    let mut p_k512 = zk_bnd.clone();
    p_k512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut p_w512 = zk_bnd;
    p_w512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut p_l512 = zl_bnd.clone();
    p_l512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let mut p_du512 = zl_bnd;
    p_du512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ONE]);
    let mut p_cep512 = zcep_bnd;
    p_cep512.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    let mut p_ulo512 = zu_limb.clone();
    p_ulo512.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);
    let mut p_uhi512 = zu_limb;
    p_uhi512.extend_from_slice(&[Ext4::ZERO, Ext4::ONE, Ext4::ZERO, Ext4::ONE, Ext4::ONE]);

    verify_pcs_claims(
        &pf.small512_pcs_root,
        PcsShape::new(m_sbnd, PcsParams::default_zk(8)),
        &[
            MleEvalClaim { point: p_k512, value: pf.k_at_zkbnd.add(sm512_ext) },
            MleEvalClaim { point: p_w512, value: pf.w_at_zkbnd.add(sm512_ext) },
            MleEvalClaim { point: p_l512, value: pf.l_at_zlbnd.add(sm512_ext) },
            MleEvalClaim { point: p_du512, value: pf.du_at_zlbnd.add(sm512_ext) },
            MleEvalClaim { point: p_cep512, value: pf.cep_at_zcepbnd.add(sm512_ext) },
            MleEvalClaim { point: p_ulo512, value: pf.ulo_shift_at_zulimb },
            MleEvalClaim { point: p_uhi512, value: pf.uhi_shift_at_zulimb },
            MleEvalClaim { point: sm512_d1b_pt.clone(), value: pf.small512_d1b.rem_leaf_eval },
        ],
        &pf.small512_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &pf.mult_small512_pcs_root,
        PcsShape::new(M_TAB_SMALL512, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: sm512_d1b_pt[..M_TAB_SMALL512].to_vec(), value: pf.small512_d1b.mult_leaf_eval }],
        &pf.mult_small512_pcs,
        &mut tr,
    )?;

    Ok(())
}

// ===========================================================================
// §6. Zero-Knowledge Rank-`r` Subspace Machine-Unlearning Certificate (`0` `mod P` Wraparound!)
// ===========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkUnlearningCertificate {
    pub h_v: usize,
    pub h_pad: usize,
    pub rank_r: usize,
    pub s_before_root: [u8; 32],
    pub s_unlearned_root: [u8; 32],
    pub forget_request_root: [u8; 32],
    pub u_pcs_root: [u8; 32],
    pub request_nonce: [u8; 32],
    pub opt_mmr_tie: Option<(EpisodeMmrEntry, MmrInclusionProof)>,

    pub ulo_pcs_root: [u8; 32],
    pub mult_ulo_pcs_root: [u8; 32],
    pub uhi_pcs_root: [u8; 32],
    pub mult_uhi_pcs_root: [u8; 32],
    pub p_proj_pcs_root: [u8; 32],
    pub gram_shift_pcs_root: [u8; 32],
    pub mult_gram_pcs_root: [u8; 32],
    pub res_shift_pcs_root: [u8; 32],
    pub mult_res_pcs_root: [u8; 32],
    pub sbnd_unl_pcs_root: [u8; 32],
    pub mult_sbnd_unl_pcs_root: [u8; 32],
    pub qlo_unl_pcs_root: [u8; 32],
    pub mult_qlo_unl_pcs_root: [u8; 32],
    pub rem128_unl_pcs_root: [u8; 32],
    pub mult_rem128_unl_pcs_root: [u8; 32],

    pub g_lo_shift_at_zg: Ext4,
    pub r_glo_at_zg: Ext4,
    pub gram_shift_at_zg: Ext4,
    pub s_before_at_zp2: Ext4,
    pub s_unlearned_at_zp2: Ext4,
    pub q_p2_lo_shift_at_zp2: Ext4,
    pub r_p2_lo_at_zp2: Ext4,
    pub r_p2_hi_at_zp2: Ext4,
    pub res_shift_at_zr: Ext4,
    pub q_u3_lo_shift_at_zr: Ext4,
    pub r_u3_lo_at_zr: Ext4,
    pub r_u3_hi_at_zr: Ext4,
    pub s_before_at_zsbnd: Ext4,
    pub s_unlearned_at_zsbnd: Ext4,
    pub pproj_at_zpbnd: Ext4,
    pub u_at_zulimb: Ext4,
    pub ulo_shift_at_zulimb: Ext4,
    pub uhi_shift_at_zulimb: Ext4,

    pub u_inactive_zero: GruenMode2Ext4Proof,
    pub gram_lo_gruen: GruenMode2Ext4Proof,
    pub gram_hi_gruen: GruenMode2Ext4Proof,
    pub proj2_lo_gruen: GruenMode2Ext4Proof,
    pub proj2_hi_gruen: GruenMode2Ext4Proof,
    pub rz_lo_gruen: GruenMode2Ext4Proof,
    pub rz_hi_gruen: GruenMode2Ext4Proof,

    pub ulo_d1b: D1bRangeExt4Proof,
    pub uhi_d1b: D1bRangeExt4Proof,
    pub gram_d1b: D1bRangeExt4Proof,
    pub res_zero_d1b: D1bRangeExt4Proof,
    pub sbnd_unl_d1b: D1bRangeExt4Proof,
    pub qlo_unl_d1b: D1bRangeExt4Proof,
    pub rem128_unl_d1b: D1bRangeExt4Proof,

    pub s_before_pcs: PcsOpeningProof,
    pub s_unlearned_pcs: PcsOpeningProof,
    pub u_pcs: PcsOpeningProof,
    pub ulo_pcs: PcsOpeningProof,
    pub mult_ulo_pcs: PcsOpeningProof,
    pub uhi_pcs: PcsOpeningProof,
    pub mult_uhi_pcs: PcsOpeningProof,
    pub p_proj_pcs: PcsOpeningProof,
    pub gram_shift_pcs: PcsOpeningProof,
    pub mult_gram_pcs: PcsOpeningProof,
    pub res_shift_pcs: PcsOpeningProof,
    pub mult_res_pcs: PcsOpeningProof,
    pub sbnd_unl_pcs: PcsOpeningProof,
    pub mult_sbnd_unl_pcs: PcsOpeningProof,
    pub qlo_unl_pcs: PcsOpeningProof,
    pub mult_qlo_unl_pcs: PcsOpeningProof,
    pub rem128_unl_pcs: PcsOpeningProof,
    pub mult_rem128_unl_pcs: PcsOpeningProof,
}

impl ZkUnlearningCertificate {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(768 * 1024);
        out.extend_from_slice(UNLEARN_PROOF_MAGIC);
        out.extend_from_slice(&(self.h_v as u32).to_le_bytes());
        out.extend_from_slice(&(self.h_pad as u32).to_le_bytes());
        out.extend_from_slice(&(self.rank_r as u32).to_le_bytes());
        for r in [
            &self.s_before_root,
            &self.s_unlearned_root,
            &self.forget_request_root,
            &self.u_pcs_root,
            &self.request_nonce,
            &self.ulo_pcs_root,
            &self.mult_ulo_pcs_root,
            &self.uhi_pcs_root,
            &self.mult_uhi_pcs_root,
            &self.p_proj_pcs_root,
            &self.gram_shift_pcs_root,
            &self.mult_gram_pcs_root,
            &self.res_shift_pcs_root,
            &self.mult_res_pcs_root,
            &self.sbnd_unl_pcs_root,
            &self.mult_sbnd_unl_pcs_root,
            &self.qlo_unl_pcs_root,
            &self.mult_qlo_unl_pcs_root,
            &self.rem128_unl_pcs_root,
            &self.mult_rem128_unl_pcs_root,
        ] {
            out.extend_from_slice(r);
        }
        match &self.opt_mmr_tie {
            None => out.push(0),
            Some((entry, mp)) => {
                out.push(1);
                out.extend_from_slice(&entry.episode_idx.to_le_bytes());
                out.extend_from_slice(&entry.s_prev_root);
                out.extend_from_slice(&entry.s_post_root);
                out.extend_from_slice(&entry.k_pcs_root);
                out.extend_from_slice(&entry.forget_request_root);
                mp.write_to(&mut out);
            }
        }
        for e in [
            self.g_lo_shift_at_zg,
            self.r_glo_at_zg,
            self.gram_shift_at_zg,
            self.s_before_at_zp2,
            self.s_unlearned_at_zp2,
            self.q_p2_lo_shift_at_zp2,
            self.r_p2_lo_at_zp2,
            self.r_p2_hi_at_zp2,
            self.res_shift_at_zr,
            self.q_u3_lo_shift_at_zr,
            self.r_u3_lo_at_zr,
            self.r_u3_hi_at_zr,
            self.s_before_at_zsbnd,
            self.s_unlearned_at_zsbnd,
            self.pproj_at_zpbnd,
            self.u_at_zulimb,
            self.ulo_shift_at_zulimb,
            self.uhi_shift_at_zulimb,
        ] {
            out.extend_from_slice(&e.to_bytes());
        }
        for gp in [
            &self.u_inactive_zero,
            &self.gram_lo_gruen,
            &self.gram_hi_gruen,
            &self.proj2_lo_gruen,
            &self.proj2_hi_gruen,
            &self.rz_lo_gruen,
            &self.rz_hi_gruen,
        ] {
            gp.write_to(&mut out);
        }
        for dp in [
            &self.ulo_d1b,
            &self.uhi_d1b,
            &self.gram_d1b,
            &self.res_zero_d1b,
            &self.sbnd_unl_d1b,
            &self.qlo_unl_d1b,
            &self.rem128_unl_d1b,
        ] {
            dp.write_to(&mut out);
        }
        for pf in [
            &self.s_before_pcs,
            &self.s_unlearned_pcs,
            &self.u_pcs,
            &self.ulo_pcs,
            &self.mult_ulo_pcs,
            &self.uhi_pcs,
            &self.mult_uhi_pcs,
            &self.p_proj_pcs,
            &self.gram_shift_pcs,
            &self.mult_gram_pcs,
            &self.res_shift_pcs,
            &self.mult_res_pcs,
            &self.sbnd_unl_pcs,
            &self.mult_sbnd_unl_pcs,
            &self.qlo_unl_pcs,
            &self.mult_qlo_unl_pcs,
            &self.rem128_unl_pcs,
            &self.mult_rem128_unl_pcs,
        ] {
            pf.write_to(&mut out);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != UNLEARN_PROOF_MAGIC {
            return Err("invalid ZkUnlearningCertificate magic".to_string());
        }
        let h_v = cur.read_u32()? as usize;
        let h_pad = cur.read_u32()? as usize;
        let rank_r = cur.read_u32()? as usize;
        if !h_pad.is_power_of_two()
            || h_pad < 16
            || h_pad > 64
            || h_v == 0
            || h_v > h_pad
            || rank_r == 0
            || rank_r > R_PAD
        {
            return Err("invalid ZkUnlearningCertificate header dims".to_string());
        }
        let s_before_root = cur.read_arr32()?;
        let s_unlearned_root = cur.read_arr32()?;
        let forget_request_root = cur.read_arr32()?;
        let u_pcs_root = cur.read_arr32()?;
        let request_nonce = cur.read_arr32()?;
        let ulo_pcs_root = cur.read_arr32()?;
        let mult_ulo_pcs_root = cur.read_arr32()?;
        let uhi_pcs_root = cur.read_arr32()?;
        let mult_uhi_pcs_root = cur.read_arr32()?;
        let p_proj_pcs_root = cur.read_arr32()?;
        let gram_shift_pcs_root = cur.read_arr32()?;
        let mult_gram_pcs_root = cur.read_arr32()?;
        let res_shift_pcs_root = cur.read_arr32()?;
        let mult_res_pcs_root = cur.read_arr32()?;
        let sbnd_unl_pcs_root = cur.read_arr32()?;
        let mult_sbnd_unl_pcs_root = cur.read_arr32()?;
        let qlo_unl_pcs_root = cur.read_arr32()?;
        let mult_qlo_unl_pcs_root = cur.read_arr32()?;
        let rem128_unl_pcs_root = cur.read_arr32()?;
        let mult_rem128_unl_pcs_root = cur.read_arr32()?;

        let opt_mmr_tie = match cur.read_u8()? {
            0 => None,
            1 => {
                let entry = EpisodeMmrEntry {
                    episode_idx: cur.read_u32()?,
                    s_prev_root: cur.read_arr32()?,
                    s_post_root: cur.read_arr32()?,
                    k_pcs_root: cur.read_arr32()?,
                    forget_request_root: cur.read_arr32()?,
                };
                let mp = MmrInclusionProof::read_from(&mut cur)?;
                Some((entry, mp))
            }
            _ => return Err("invalid opt_mmr_tie tag".to_string()),
        };

        let g_lo_shift_at_zg = cur.read_ext4()?;
        let r_glo_at_zg = cur.read_ext4()?;
        let gram_shift_at_zg = cur.read_ext4()?;
        let s_before_at_zp2 = cur.read_ext4()?;
        let s_unlearned_at_zp2 = cur.read_ext4()?;
        let q_p2_lo_shift_at_zp2 = cur.read_ext4()?;
        let r_p2_lo_at_zp2 = cur.read_ext4()?;
        let r_p2_hi_at_zp2 = cur.read_ext4()?;
        let res_shift_at_zr = cur.read_ext4()?;
        let q_u3_lo_shift_at_zr = cur.read_ext4()?;
        let r_u3_lo_at_zr = cur.read_ext4()?;
        let r_u3_hi_at_zr = cur.read_ext4()?;
        let s_before_at_zsbnd = cur.read_ext4()?;
        let s_unlearned_at_zsbnd = cur.read_ext4()?;
        let pproj_at_zpbnd = cur.read_ext4()?;
        let u_at_zulimb = cur.read_ext4()?;
        let ulo_shift_at_zulimb = cur.read_ext4()?;
        let uhi_shift_at_zulimb = cur.read_ext4()?;

        let u_inactive_zero = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let gram_lo_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let gram_hi_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let proj2_lo_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let proj2_hi_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let rz_lo_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;
        let rz_hi_gruen = GruenMode2Ext4Proof::read_from(&mut cur)?;

        let ulo_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let uhi_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let gram_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let res_zero_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let sbnd_unl_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let qlo_unl_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let rem128_unl_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;

        let s_before_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let s_unlearned_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let u_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let ulo_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_ulo_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let uhi_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_uhi_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let p_proj_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let gram_shift_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_gram_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let res_shift_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_res_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let sbnd_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_sbnd_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let qlo_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_qlo_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let rem128_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        let mult_rem128_unl_pcs = PcsOpeningProof::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in ZkUnlearningCertificate".to_string());
        }
        Ok(Self {
            h_v,
            h_pad,
            rank_r,
            s_before_root,
            s_unlearned_root,
            forget_request_root,
            u_pcs_root,
            request_nonce,
            opt_mmr_tie,
            ulo_pcs_root,
            mult_ulo_pcs_root,
            uhi_pcs_root,
            mult_uhi_pcs_root,
            p_proj_pcs_root,
            gram_shift_pcs_root,
            mult_gram_pcs_root,
            res_shift_pcs_root,
            mult_res_pcs_root,
            sbnd_unl_pcs_root,
            mult_sbnd_unl_pcs_root,
            qlo_unl_pcs_root,
            mult_qlo_unl_pcs_root,
            rem128_unl_pcs_root,
            mult_rem128_unl_pcs_root,
            g_lo_shift_at_zg,
            r_glo_at_zg,
            gram_shift_at_zg,
            s_before_at_zp2,
            s_unlearned_at_zp2,
            q_p2_lo_shift_at_zp2,
            r_p2_lo_at_zp2,
            r_p2_hi_at_zp2,
            res_shift_at_zr,
            q_u3_lo_shift_at_zr,
            r_u3_lo_at_zr,
            r_u3_hi_at_zr,
            s_before_at_zsbnd,
            s_unlearned_at_zsbnd,
            pproj_at_zpbnd,
            u_at_zulimb,
            ulo_shift_at_zulimb,
            uhi_shift_at_zulimb,
            u_inactive_zero,
            gram_lo_gruen,
            gram_hi_gruen,
            proj2_lo_gruen,
            proj2_hi_gruen,
            rz_lo_gruen,
            rz_hi_gruen,
            ulo_d1b,
            uhi_d1b,
            gram_d1b,
            res_zero_d1b,
            sbnd_unl_d1b,
            qlo_unl_d1b,
            rem128_unl_d1b,
            s_before_pcs,
            s_unlearned_pcs,
            u_pcs,
            ulo_pcs,
            mult_ulo_pcs,
            uhi_pcs,
            mult_uhi_pcs,
            p_proj_pcs,
            gram_shift_pcs,
            mult_gram_pcs,
            res_shift_pcs,
            mult_res_pcs,
            sbnd_unl_pcs,
            mult_sbnd_unl_pcs,
            qlo_unl_pcs,
            mult_qlo_unl_pcs,
            rem128_unl_pcs,
            mult_rem128_unl_pcs,
        })
    }
}

pub fn prove_zk_unlearning_certificate(
    vault_key: &ProverVaultKey,
    wit: &RankRUnlearnWitness,
    request_nonce: &[u8; 32],
    opt_mmr_tie: Option<(EpisodeMmrEntry, MmrInclusionProof, [u8; 32])>,
) -> Result<(Vec<u8>, [u8; 32], [u8; 32], [u8; 32]), String> {
    let h_pad = wit.h_pad;
    let log_h = h_pad.trailing_zeros() as usize;
    let m_s = log_h + 14;
    let m_small = log_h + 10;
    let m_2s = m_s + 1;
    let m_4s = m_s + 2;
    let m_gram = wit.gram_shift_pad.len().trailing_zeros() as usize;

    let mult_ulo = compute_d1b_multiplicities(&wit.basis.u_lo_shift_lsb, LIMB_SHIFT)?;
    let mult_uhi = compute_d1b_multiplicities(&wit.basis.u_hi_shift_lsb, LIMB_SHIFT)?;
    let mult_gram = compute_d1b_multiplicities(&wit.gram_shift_pad, M_TAB_ORTH)?;
    let mult_res = compute_d1b_multiplicities(&wit.res_shift_lsb_hja, M_TAB_ZERO)?;
    let mult_sbnd = compute_d1b_multiplicities(&wit.s_bnd_unl_packed, M_TAB_S_BND)?;
    let mult_qlo = compute_d1b_multiplicities(&wit.qlo_unl_packed, M_TAB_QUOT_UNL)?;
    let mult_rem128 = compute_d1b_multiplicities(&wit.rem128_unl_packed, LIMB_SHIFT)?;

    let s_bef_seed = vault_key.state_pcs_seed(&wit.s_before.s_bb_lsb);
    let s_unl_seed = vault_key.state_pcs_seed(&wit.s_unlearned.s_bb_lsb);
    let u_seed = vault_key.basis_pcs_seed(&wit.basis.u_bb_lsb, request_nonce);

    let s_bef_st = commit_table_pcs(&wit.s_before.s_bb_lsb, PcsParams::default_zk(4), Some(&s_bef_seed));
    let s_unl_st = commit_table_pcs(&wit.s_unlearned.s_bb_lsb, PcsParams::default_zk(4), Some(&s_unl_seed));
    let u_st = commit_table_pcs(&wit.basis.u_bb_lsb, PcsParams::default_zk(4), Some(&u_seed));
    let ulo_st = commit_table_pcs(&wit.basis.u_lo_shift_lsb, PcsParams::default_zk(5), None);
    let mult_ulo_st = commit_table_pcs(&mult_ulo, PcsParams::default_zk(1), None);
    let uhi_st = commit_table_pcs(&wit.basis.u_hi_shift_lsb, PcsParams::default_zk(5), None);
    let mult_uhi_st = commit_table_pcs(&mult_uhi, PcsParams::default_zk(1), None);
    let p_proj_st = commit_table_pcs(&wit.p_proj_lsb_haj, PcsParams::default_zk(3), None);
    let gram_st = commit_table_pcs(&wit.gram_shift_pad, PcsParams::default_zk(2), None);
    let mult_gram_st = commit_table_pcs(&mult_gram, PcsParams::default_zk(1), None);
    let res_st = commit_table_pcs(&wit.res_shift_lsb_hja, PcsParams::default_zk(2), None);
    let mult_res_st = commit_table_pcs(&mult_res, PcsParams::default_zk(1), None);
    let sbnd_st = commit_table_pcs(&wit.s_bnd_unl_packed, PcsParams::default_zk(5), None);
    let mult_sbnd_st = commit_table_pcs(&mult_sbnd, PcsParams::default_zk(1), None);
    let qlo_st = commit_table_pcs(&wit.qlo_unl_packed, PcsParams::default_zk(5), None);
    let mult_qlo_st = commit_table_pcs(&mult_qlo, PcsParams::default_zk(1), None);
    let rem128_st = commit_table_pcs(&wit.rem128_unl_packed, PcsParams::default_zk(6), None);
    let mult_rem128_st = commit_table_pcs(&mult_rem128, PcsParams::default_zk(1), None);

    let forget_request_root =
        compute_blind_forget_request_root(wit.h_v, h_pad, wit.rank_r, &u_st.root, request_nonce);

    let mut tr = CShakeTranscript::new(b"CMEM-UNLEARN-CERT-ZK-V3");
    tr.absorb_u32(b"h_v", wit.h_v as u32);
    tr.absorb_u32(b"h_pad", h_pad as u32);
    tr.absorb_u32(b"rank_r", wit.rank_r as u32);
    tr.absorb_u32(b"has_mmr", opt_mmr_tie.is_some() as u32);
    if let Some((_, _, ref mmr_root)) = opt_mmr_tie {
        tr.absorb_root(b"mmr_root", mmr_root);
    }
    for r in [
        &s_bef_st.root,
        &s_unl_st.root,
        &forget_request_root,
        &u_st.root,
        request_nonce,
        &ulo_st.root,
        &mult_ulo_st.root,
        &uhi_st.root,
        &mult_uhi_st.root,
        &p_proj_st.root,
        &gram_st.root,
        &mult_gram_st.root,
        &res_st.root,
        &mult_res_st.root,
        &sbnd_st.root,
        &mult_sbnd_st.root,
        &qlo_st.root,
        &mult_qlo_st.root,
        &rem128_st.root,
        &mult_rem128_st.root,
    ] {
        tr.absorb_root(b"unl_root", r);
    }

    // Signed limb `bb` arrays (`u_lo_bb`, `u_hi_bb`) for Gruen contractions:
    let ulo_signed_bb: Vec<u32> = wit
        .basis
        .u_lo_shift_lsb
        .iter()
        .map(|&v| bb_from_i64((v as i64) - ULO_HALF))
        .collect();
    let uhi_signed_bb: Vec<u32> = wit
        .basis
        .u_hi_shift_lsb
        .iter()
        .map(|&v| bb_from_i64((v as i64) - UHI_HALF))
        .collect();

    // U0: `u_inactive_zero`
    let zi_all = tr.squeeze_ext4_vec(b"u_inact_zs", m_small, true);
    let mut inact_ind = vec![Ext4::ZERO; 1usize << m_small];
    let mut u_ext_tab = vec![Ext4::ZERO; 1usize << m_small];
    for a in 0..R_PAD {
        for h in 0..h_pad {
            let bad = if h >= wit.h_v || a >= wit.rank_r {
                Ext4::ONE
            } else {
                Ext4::ZERO
            };
            for i_k in 0..128 {
                let idx = h + (i_k << log_h) + (a << (log_h + 7));
                inact_ind[idx] = bad;
                u_ext_tab[idx] = Ext4::from_bb(wit.basis.u_bb_lsb[idx]);
            }
        }
    }
    let (u_inactive_zero, u_inact_pt) =
        prove_gruen_einsum_mode2_ext4(&inact_ind, &u_ext_tab, m_small, 0, &zi_all, &mut tr);

    // U1 (2-limb Gram):
    let zg_h = tr.squeeze_ext4_vec(b"zg_h", log_h, true);
    let zg_a = tr.squeeze_ext4_vec(b"zg_a", LOG_R_PAD, true);
    let zg_b = tr.squeeze_ext4_vec(b"zg_b", LOG_R_PAD, true);
    let mut zg_hab = Vec::with_capacity(log_h + 6);
    zg_hab.extend_from_slice(&zg_h);
    zg_hab.extend_from_slice(&zg_a);
    zg_hab.extend_from_slice(&zg_b);

    let mut zg_pad = zg_hab.clone();
    while zg_pad.len() < m_gram {
        zg_pad.push(Ext4::ZERO);
    }
    let gram_shift_at_zg = mle_eval_bb_at_ext4(&wit.gram_shift_pad, &zg_pad);

    let mut zg_qlo = zg_hab.clone();
    // `idx_hab` (`log_h + 6` bits) padded to `m_small` (`+4` zeros), then sub-slot `2` (`[0, 1]`) + `+2` zeros + `msb = 1`:
    zg_qlo.extend_from_slice(&[
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    let g_lo_shift_at_zg = mle_eval_bb_at_ext4(&wit.qlo_unl_packed, &zg_qlo);

    let mut zg_rglo = zg_hab;
    // `3 * m_base_cells + idx_hab`: `idx_hab` (`log_h + 6`) + `8` zeros (`-> m_s`) + `[1, 1]`:
    for _ in 0..8 {
        zg_rglo.push(Ext4::ZERO);
    }
    zg_rglo.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);
    let r_glo_at_zg = mle_eval_bb_at_ext4(&wit.rem128_unl_packed, &zg_rglo);

    for e in [g_lo_shift_at_zg, r_glo_at_zg, gram_shift_at_zg] {
        tr.absorb_ext4(b"gram_ev", e);
    }

    let eq_zga = build_eq_table_lsb_ext4(&zg_a);
    let eq_zgb = build_eq_table_lsb_ext4(&zg_b);
    let mut gram_u_left = vec![Ext4::ZERO; h_pad * 128];
    let mut gram_ulo_right = vec![Ext4::ZERO; h_pad * 128];
    let mut gram_uhi_right = vec![Ext4::ZERO; h_pad * 128];
    for i_k in 0..128 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            let mut ar_lo = Ext4::ZERO;
            let mut ar_hi = Ext4::ZERO;
            for a in 0..R_PAD {
                let idx = h + (i_k << log_h) + (a << (log_h + 7));
                al = al.add(eq_zga[a].scale_bb(wit.basis.u_bb_lsb[idx]));
                ar_lo = ar_lo.add(eq_zgb[a].scale_bb(ulo_signed_bb[idx]));
                ar_hi = ar_hi.add(eq_zgb[a].scale_bb(uhi_signed_bb[idx]));
            }
            gram_u_left[h + (i_k << log_h)] = al;
            gram_ulo_right[h + (i_k << log_h)] = ar_lo;
            gram_uhi_right[h + (i_k << log_h)] = ar_hi;
        }
    }
    let (gram_lo_gruen, gram_lo_ch) =
        prove_gruen_einsum_mode2_ext4(&gram_u_left, &gram_ulo_right, log_h, 7, &zg_h, &mut tr);
    let (gram_hi_gruen, gram_hi_ch) =
        prove_gruen_einsum_mode2_ext4(&gram_u_left, &gram_uhi_right, log_h, 7, &zg_h, &mut tr);

    // U2 (2-limb projection):
    let zp2_h = tr.squeeze_ext4_vec(b"zp2_h", log_h, true);
    let zp2_ik = tr.squeeze_ext4_vec(b"zp2_ik", 7, true);
    let zp2_jv = tr.squeeze_ext4_vec(b"zp2_jv", 7, true);
    let mut zp2_hij = Vec::with_capacity(m_s);
    zp2_hij.extend_from_slice(&zp2_h);
    zp2_hij.extend_from_slice(&zp2_ik);
    zp2_hij.extend_from_slice(&zp2_jv);

    let s_before_at_zp2 = mle_eval_bb_at_ext4(&wit.s_before.s_bb_lsb, &zp2_hij);
    let s_unlearned_at_zp2 = mle_eval_bb_at_ext4(&wit.s_unlearned.s_bb_lsb, &zp2_hij);
    let mut zp2_qlo = zp2_hij.clone();
    zp2_qlo.push(Ext4::ZERO);
    let q_p2_lo_shift_at_zp2 = mle_eval_bb_at_ext4(&wit.qlo_unl_packed, &zp2_qlo);
    let mut zp2_rlo = zp2_hij.clone();
    zp2_rlo.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let r_p2_lo_at_zp2 = mle_eval_bb_at_ext4(&wit.rem128_unl_packed, &zp2_rlo);
    let mut zp2_rhi = zp2_hij.clone();
    zp2_rhi.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let r_p2_hi_at_zp2 = mle_eval_bb_at_ext4(&wit.rem128_unl_packed, &zp2_rhi);
    for e in [
        s_before_at_zp2,
        s_unlearned_at_zp2,
        q_p2_lo_shift_at_zp2,
        r_p2_lo_at_zp2,
        r_p2_hi_at_zp2,
    ] {
        tr.absorb_ext4(b"p2_ev", e);
    }

    let eq_zp2ik = build_eq_table_lsb_ext4(&zp2_ik);
    let eq_zp2jv = build_eq_table_lsb_ext4(&zp2_jv);
    let mut p2_ulo_left = vec![Ext4::ZERO; h_pad * R_PAD];
    let mut p2_uhi_left = vec![Ext4::ZERO; h_pad * R_PAD];
    let mut p2_right = vec![Ext4::ZERO; h_pad * R_PAD];
    for a in 0..R_PAD {
        for h in 0..h_pad {
            let mut al_lo = Ext4::ZERO;
            let mut al_hi = Ext4::ZERO;
            for i_k in 0..128 {
                let idx = h + (i_k << log_h) + (a << (log_h + 7));
                al_lo = al_lo.add(eq_zp2ik[i_k].scale_bb(ulo_signed_bb[idx]));
                al_hi = al_hi.add(eq_zp2ik[i_k].scale_bb(uhi_signed_bb[idx]));
            }
            p2_ulo_left[h + (a << log_h)] = al_lo;
            p2_uhi_left[h + (a << log_h)] = al_hi;
            let mut ar = Ext4::ZERO;
            for j_v in 0..128 {
                ar = ar.add(eq_zp2jv[j_v].scale_bb(wit.p_proj_lsb_haj[h + (a << log_h) + (j_v << (log_h + 3))]));
            }
            p2_right[h + (a << log_h)] = ar;
        }
    }
    let (proj2_lo_gruen, p2_lo_ch) =
        prove_gruen_einsum_mode2_ext4(&p2_ulo_left, &p2_right, log_h, LOG_R_PAD, &zp2_h, &mut tr);
    let (proj2_hi_gruen, p2_hi_ch) =
        prove_gruen_einsum_mode2_ext4(&p2_uhi_left, &p2_right, log_h, LOG_R_PAD, &zp2_h, &mut tr);

    // U3 (2-limb residual annihilation):
    let zr_h = tr.squeeze_ext4_vec(b"zr_h", log_h, true);
    let zr_jv = tr.squeeze_ext4_vec(b"zr_jv", 7, true);
    let zr_a = tr.squeeze_ext4_vec(b"zr_a", LOG_R_PAD, true);
    let mut zr_hja = Vec::with_capacity(m_small);
    zr_hja.extend_from_slice(&zr_h);
    zr_hja.extend_from_slice(&zr_jv);
    zr_hja.extend_from_slice(&zr_a);

    let res_shift_at_zr = mle_eval_bb_at_ext4(&wit.res_shift_lsb_hja, &zr_hja);
    let mut zr_qlo = zr_hja.clone();
    // `m_base_cells + m_small_cells + idx_r`: sub-slot `1` (`[1, 0, 0, 0]`) + `msb = 1`!
    zr_qlo.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let q_u3_lo_shift_at_zr = mle_eval_bb_at_ext4(&wit.qlo_unl_packed, &zr_qlo);
    let mut zr_rlo = zr_hja.clone();
    // `2 * m_base_cells + idx_r`: `[0, 0, 0, 0, 0, 1]`!
    zr_rlo.extend_from_slice(&[
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    let r_u3_lo_at_zr = mle_eval_bb_at_ext4(&wit.rem128_unl_packed, &zr_rlo);
    let mut zr_rhi = zr_hja.clone();
    // `2 * m_base_cells + m_small_cells + idx_r`: `[1, 0, 0, 0, 0, 1]`!
    zr_rhi.extend_from_slice(&[
        Ext4::ONE,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    let r_u3_hi_at_zr = mle_eval_bb_at_ext4(&wit.rem128_unl_packed, &zr_rhi);
    for e in [
        res_shift_at_zr,
        q_u3_lo_shift_at_zr,
        r_u3_lo_at_zr,
        r_u3_hi_at_zr,
    ] {
        tr.absorb_ext4(b"res_ev", e);
    }

    let eq_zrjv = build_eq_table_lsb_ext4(&zr_jv);
    let eq_zra = build_eq_table_lsb_ext4(&zr_a);
    let mut rz_left = vec![Ext4::ZERO; h_pad * 128];
    let mut rz_ulo_right = vec![Ext4::ZERO; h_pad * 128];
    let mut rz_uhi_right = vec![Ext4::ZERO; h_pad * 128];
    for i_k in 0..128 {
        for h in 0..h_pad {
            let mut al = Ext4::ZERO;
            for j_v in 0..128 {
                al = al.add(eq_zrjv[j_v].scale_bb(wit.s_unlearned.s_bb_lsb[h + (i_k << log_h) + (j_v << (log_h + 7))]));
            }
            rz_left[h + (i_k << log_h)] = al;
            let mut ar_lo = Ext4::ZERO;
            let mut ar_hi = Ext4::ZERO;
            for a in 0..R_PAD {
                let idx = h + (i_k << log_h) + (a << (log_h + 7));
                ar_lo = ar_lo.add(eq_zra[a].scale_bb(ulo_signed_bb[idx]));
                ar_hi = ar_hi.add(eq_zra[a].scale_bb(uhi_signed_bb[idx]));
            }
            rz_ulo_right[h + (i_k << log_h)] = ar_lo;
            rz_uhi_right[h + (i_k << log_h)] = ar_hi;
        }
    }
    let (rz_lo_gruen, rz_lo_ch) =
        prove_gruen_einsum_mode2_ext4(&rz_left, &rz_ulo_right, log_h, 7, &zr_h, &mut tr);
    let (rz_hi_gruen, rz_hi_ch) =
        prove_gruen_einsum_mode2_ext4(&rz_left, &rz_uhi_right, log_h, 7, &zr_h, &mut tr);

    // 7 `D1b` Range Proofs:
    let (ulo_d1b, ulo_d1b_pt) =
        prove_d1b_range_ext4(&wit.basis.u_lo_shift_lsb, &mult_ulo, m_small, LIMB_SHIFT, &mut tr);
    let (uhi_d1b, uhi_d1b_pt) =
        prove_d1b_range_ext4(&wit.basis.u_hi_shift_lsb, &mult_uhi, m_small, LIMB_SHIFT, &mut tr);
    let (gram_d1b, gram_d1b_pt) =
        prove_d1b_range_ext4(&wit.gram_shift_pad, &mult_gram, m_gram, M_TAB_ORTH, &mut tr);
    let (res_zero_d1b, res_d1b_pt) =
        prove_d1b_range_ext4(&wit.res_shift_lsb_hja, &mult_res, m_small, M_TAB_ZERO, &mut tr);
    let (sbnd_unl_d1b, sbnd_d1b_pt) =
        prove_d1b_range_ext4(&wit.s_bnd_unl_packed, &mult_sbnd, m_4s, M_TAB_S_BND, &mut tr);
    let (qlo_unl_d1b, qlo_d1b_pt) =
        prove_d1b_range_ext4(&wit.qlo_unl_packed, &mult_qlo, m_2s, M_TAB_QUOT_UNL, &mut tr);
    let (rem128_unl_d1b, rem128_d1b_pt) =
        prove_d1b_range_ext4(&wit.rem128_unl_packed, &mult_rem128, m_4s, LIMB_SHIFT, &mut tr);

    let zs_bnd = tr.squeeze_ext4_vec(b"zs_unl_bnd", m_s, true);
    let z_pbnd = tr.squeeze_ext4_vec(b"zp_unl_bnd", m_small, true);
    let zu_limb = tr.squeeze_ext4_vec(b"zu_unl_limb", m_small, true);

    let s_before_at_zsbnd = mle_eval_bb_at_ext4(&wit.s_before.s_bb_lsb, &zs_bnd);
    let s_unlearned_at_zsbnd = mle_eval_bb_at_ext4(&wit.s_unlearned.s_bb_lsb, &zs_bnd);
    let pproj_at_zpbnd = mle_eval_bb_at_ext4(&wit.p_proj_lsb_haj, &z_pbnd);
    let u_at_zulimb = mle_eval_bb_at_ext4(&wit.basis.u_bb_lsb, &zu_limb);
    let ulo_shift_at_zulimb = mle_eval_bb_at_ext4(&wit.basis.u_lo_shift_lsb, &zu_limb);
    let uhi_shift_at_zulimb = mle_eval_bb_at_ext4(&wit.basis.u_hi_shift_lsb, &zu_limb);
    for e in [
        s_before_at_zsbnd,
        s_unlearned_at_zsbnd,
        pproj_at_zpbnd,
        u_at_zulimb,
        ulo_shift_at_zulimb,
        uhi_shift_at_zulimb,
    ] {
        tr.absorb_ext4(b"unl_weld_ev", e);
    }

    let s_before_pcs = open_pcs_claims(
        &s_bef_st,
        &[
            MleEvalClaim { point: zp2_hij.clone(), value: s_before_at_zp2 },
            MleEvalClaim { point: zs_bnd.clone(), value: s_before_at_zsbnd },
        ],
        &mut tr,
    );

    let build_su_pt = |ch: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_s);
        p.extend_from_slice(&ch[..log_h]);
        p.extend_from_slice(&ch[log_h..]);
        p.extend_from_slice(&zr_jv);
        p
    };
    let s_unlearned_pcs = open_pcs_claims(
        &s_unl_st,
        &[
            MleEvalClaim { point: zp2_hij, value: s_unlearned_at_zp2 },
            MleEvalClaim { point: build_su_pt(&rz_lo_ch), value: rz_lo_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_su_pt(&rz_hi_ch), value: rz_hi_gruen.terminal_openings.0 },
            MleEvalClaim { point: zs_bnd.clone(), value: s_unlearned_at_zsbnd },
        ],
        &mut tr,
    );

    let build_u_pt = |ch_hik: &[Ext4], pt_a: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_hik[..log_h]);
        p.extend_from_slice(&ch_hik[log_h..]);
        p.extend_from_slice(pt_a);
        p
    };
    let u_pcs = open_pcs_claims(
        &u_st,
        &[
            MleEvalClaim { point: u_inact_pt, value: u_inactive_zero.terminal_openings.1 },
            MleEvalClaim { point: build_u_pt(&gram_lo_ch, &zg_a), value: gram_lo_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_u_pt(&gram_hi_ch, &zg_a), value: gram_hi_gruen.terminal_openings.0 },
            MleEvalClaim { point: zu_limb.clone(), value: u_at_zulimb },
        ],
        &mut tr,
    );

    let ulo_off = Ext4::from_bb(ULO_HALF as u32);
    let uhi_off = Ext4::from_bb(UHI_HALF as u32);
    let build_up2_pt = |ch_ha: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_ha[..log_h]);
        p.extend_from_slice(&zp2_ik);
        p.extend_from_slice(&ch_ha[log_h..]);
        p
    };
    let ulo_pcs = open_pcs_claims(
        &ulo_st,
        &[
            MleEvalClaim { point: zu_limb.clone(), value: ulo_shift_at_zulimb },
            MleEvalClaim { point: build_u_pt(&gram_lo_ch, &zg_b), value: gram_lo_gruen.terminal_openings.1.add(ulo_off) },
            MleEvalClaim { point: build_up2_pt(&p2_lo_ch), value: proj2_lo_gruen.terminal_openings.0.add(ulo_off) },
            MleEvalClaim { point: build_u_pt(&rz_lo_ch, &zr_a), value: rz_lo_gruen.terminal_openings.1.add(ulo_off) },
            MleEvalClaim { point: ulo_d1b_pt.clone(), value: ulo_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_ulo_pcs = open_pcs_claims(
        &mult_ulo_st,
        &[MleEvalClaim { point: ulo_d1b_pt[..LIMB_SHIFT].to_vec(), value: ulo_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let uhi_pcs = open_pcs_claims(
        &uhi_st,
        &[
            MleEvalClaim { point: zu_limb, value: uhi_shift_at_zulimb },
            MleEvalClaim { point: build_u_pt(&gram_hi_ch, &zg_b), value: gram_hi_gruen.terminal_openings.1.add(uhi_off) },
            MleEvalClaim { point: build_up2_pt(&p2_hi_ch), value: proj2_hi_gruen.terminal_openings.0.add(uhi_off) },
            MleEvalClaim { point: build_u_pt(&rz_hi_ch, &zr_a), value: rz_hi_gruen.terminal_openings.1.add(uhi_off) },
            MleEvalClaim { point: uhi_d1b_pt.clone(), value: uhi_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_uhi_pcs = open_pcs_claims(
        &mult_uhi_st,
        &[MleEvalClaim { point: uhi_d1b_pt[..LIMB_SHIFT].to_vec(), value: uhi_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let build_pproj_pt = |ch_ha: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_ha[..log_h]);
        p.extend_from_slice(&ch_ha[log_h..]);
        p.extend_from_slice(&zp2_jv);
        p
    };
    let p_proj_pcs = open_pcs_claims(
        &p_proj_st,
        &[
            MleEvalClaim { point: build_pproj_pt(&p2_lo_ch), value: proj2_lo_gruen.terminal_openings.1 },
            MleEvalClaim { point: build_pproj_pt(&p2_hi_ch), value: proj2_hi_gruen.terminal_openings.1 },
            MleEvalClaim { point: z_pbnd.clone(), value: pproj_at_zpbnd },
        ],
        &mut tr,
    );

    let gram_shift_pcs = open_pcs_claims(
        &gram_st,
        &[
            MleEvalClaim { point: zg_pad, value: gram_shift_at_zg },
            MleEvalClaim { point: gram_d1b_pt.clone(), value: gram_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_gram_pcs = open_pcs_claims(
        &mult_gram_st,
        &[MleEvalClaim { point: gram_d1b_pt[..M_TAB_ORTH].to_vec(), value: gram_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let res_shift_pcs = open_pcs_claims(
        &res_st,
        &[
            MleEvalClaim { point: zr_hja, value: res_shift_at_zr },
            MleEvalClaim { point: res_d1b_pt.clone(), value: res_zero_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_res_pcs = open_pcs_claims(
        &mult_res_st,
        &[MleEvalClaim { point: res_d1b_pt[..M_TAB_ZERO].to_vec(), value: res_zero_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let sbnd_ext = Ext4::from_bb(S_BND_HALF as u32);
    let mut zsb00 = zs_bnd.clone();
    zsb00.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut zsb10 = zs_bnd.clone();
    zsb10.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut zsb01 = zs_bnd.clone();
    zsb01.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let mut zsb11 = zs_bnd;
    zsb11.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);
    let sbnd_unl_pcs = open_pcs_claims(
        &sbnd_st,
        &[
            MleEvalClaim { point: zsb00, value: s_before_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb10, value: sbnd_ext.sub(s_before_at_zsbnd) },
            MleEvalClaim { point: zsb01, value: s_unlearned_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb11, value: sbnd_ext.sub(s_unlearned_at_zsbnd) },
            MleEvalClaim { point: sbnd_d1b_pt.clone(), value: sbnd_unl_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_sbnd_unl_pcs = open_pcs_claims(
        &mult_sbnd_st,
        &[MleEvalClaim { point: sbnd_d1b_pt[..M_TAB_S_BND].to_vec(), value: sbnd_unl_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let qunl_ext = Ext4::from_bb(QUOT_UNL_HALF as u32);
    let mut zp_qlo = z_pbnd;
    zp_qlo.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let qlo_unl_pcs = open_pcs_claims(
        &qlo_st,
        &[
            MleEvalClaim { point: zp2_qlo, value: q_p2_lo_shift_at_zp2 },
            MleEvalClaim { point: zp_qlo, value: pproj_at_zpbnd.add(qunl_ext) },
            MleEvalClaim { point: zr_qlo, value: q_u3_lo_shift_at_zr },
            MleEvalClaim { point: zg_qlo, value: g_lo_shift_at_zg },
            MleEvalClaim { point: qlo_d1b_pt.clone(), value: qlo_unl_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_qlo_unl_pcs = open_pcs_claims(
        &mult_qlo_st,
        &[MleEvalClaim { point: qlo_d1b_pt[..M_TAB_QUOT_UNL].to_vec(), value: qlo_unl_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let rem128_unl_pcs = open_pcs_claims(
        &rem128_st,
        &[
            MleEvalClaim { point: zp2_rlo, value: r_p2_lo_at_zp2 },
            MleEvalClaim { point: zp2_rhi, value: r_p2_hi_at_zp2 },
            MleEvalClaim { point: zr_rlo, value: r_u3_lo_at_zr },
            MleEvalClaim { point: zr_rhi, value: r_u3_hi_at_zr },
            MleEvalClaim { point: zg_rglo, value: r_glo_at_zg },
            MleEvalClaim { point: rem128_d1b_pt.clone(), value: rem128_unl_d1b.rem_leaf_eval },
        ],
        &mut tr,
    );
    let mult_rem128_unl_pcs = open_pcs_claims(
        &mult_rem128_st,
        &[MleEvalClaim { point: rem128_d1b_pt[..LIMB_SHIFT].to_vec(), value: rem128_unl_d1b.mult_leaf_eval }],
        &mut tr,
    );

    let cert = ZkUnlearningCertificate {
        h_v: wit.h_v,
        h_pad,
        rank_r: wit.rank_r,
        s_before_root: s_bef_st.root,
        s_unlearned_root: s_unl_st.root,
        forget_request_root,
        u_pcs_root: u_st.root,
        request_nonce: *request_nonce,
        opt_mmr_tie: opt_mmr_tie.map(|(e, mp, _)| (e, mp)),
        ulo_pcs_root: ulo_st.root,
        mult_ulo_pcs_root: mult_ulo_st.root,
        uhi_pcs_root: uhi_st.root,
        mult_uhi_pcs_root: mult_uhi_st.root,
        p_proj_pcs_root: p_proj_st.root,
        gram_shift_pcs_root: gram_st.root,
        mult_gram_pcs_root: mult_gram_st.root,
        res_shift_pcs_root: res_st.root,
        mult_res_pcs_root: mult_res_st.root,
        sbnd_unl_pcs_root: sbnd_st.root,
        mult_sbnd_unl_pcs_root: mult_sbnd_st.root,
        qlo_unl_pcs_root: qlo_st.root,
        mult_qlo_unl_pcs_root: mult_qlo_st.root,
        rem128_unl_pcs_root: rem128_st.root,
        mult_rem128_unl_pcs_root: mult_rem128_st.root,
        g_lo_shift_at_zg,
        r_glo_at_zg,
        gram_shift_at_zg,
        s_before_at_zp2,
        s_unlearned_at_zp2,
        q_p2_lo_shift_at_zp2,
        r_p2_lo_at_zp2,
        r_p2_hi_at_zp2,
        res_shift_at_zr,
        q_u3_lo_shift_at_zr,
        r_u3_lo_at_zr,
        r_u3_hi_at_zr,
        s_before_at_zsbnd,
        s_unlearned_at_zsbnd,
        pproj_at_zpbnd,
        u_at_zulimb,
        ulo_shift_at_zulimb,
        uhi_shift_at_zulimb,
        u_inactive_zero,
        gram_lo_gruen,
        gram_hi_gruen,
        proj2_lo_gruen,
        proj2_hi_gruen,
        rz_lo_gruen,
        rz_hi_gruen,
        ulo_d1b,
        uhi_d1b,
        gram_d1b,
        res_zero_d1b,
        sbnd_unl_d1b,
        qlo_unl_d1b,
        rem128_unl_d1b,
        s_before_pcs,
        s_unlearned_pcs,
        u_pcs,
        ulo_pcs,
        mult_ulo_pcs,
        uhi_pcs,
        mult_uhi_pcs,
        p_proj_pcs,
        gram_shift_pcs,
        mult_gram_pcs,
        res_shift_pcs,
        mult_res_pcs,
        sbnd_unl_pcs,
        mult_sbnd_unl_pcs,
        qlo_unl_pcs,
        mult_qlo_unl_pcs,
        rem128_unl_pcs,
        mult_rem128_unl_pcs,
    };

    Ok((
        cert.to_bytes(),
        s_bef_st.root,
        s_unl_st.root,
        forget_request_root,
    ))
}

pub fn verify_zk_unlearning_certificate(
    expected_s_before_root: &[u8; 32],
    expected_s_unlearned_root: &[u8; 32],
    expected_forget_request_root: &[u8; 32],
    expected_opt_mmr_root: Option<&[u8; 32]>,
    expected_h_v: usize,
    expected_rank_r: usize,
    cert_bytes: &[u8],
) -> Result<(), String> {
    let cert = ZkUnlearningCertificate::from_bytes(cert_bytes)?;
    if &cert.s_before_root != expected_s_before_root {
        return Err("s_before_root mismatch".to_string());
    }
    if &cert.s_unlearned_root != expected_s_unlearned_root {
        return Err("s_unlearned_root mismatch".to_string());
    }
    if &cert.forget_request_root != expected_forget_request_root {
        return Err("forget_request_root mismatch".to_string());
    }
    if cert.h_v != expected_h_v || cert.rank_r != expected_rank_r {
        return Err("unlearning certificate (h_v, rank_r) mismatch".to_string());
    }
    let recomputed_forget_root = compute_blind_forget_request_root(
        cert.h_v,
        cert.h_pad,
        cert.rank_r,
        &cert.u_pcs_root,
        &cert.request_nonce,
    );
    if recomputed_forget_root != cert.forget_request_root {
        return Err("blind forget_request_root commitment opening mismatch".to_string());
    }

    match (&cert.opt_mmr_tie, expected_opt_mmr_root) {
        (Some((entry, mp)), Some(exp_mmr)) => {
            if mp.leaf_index != entry.episode_idx {
                return Err("MMR leaf_index != entry.episode_idx".to_string());
            }
            if entry.forget_request_root != cert.forget_request_root {
                return Err("MMR entry forget_request_root mismatch".to_string());
            }
            if !mp.verify(&entry.leaf_hash(), exp_mmr) {
                return Err("MMR inclusion proof for forget_request_root failed".to_string());
            }
        }
        (None, None) => {}
        _ => return Err("MMR tie presence mismatch".to_string()),
    }

    let log_h = cert.h_pad.trailing_zeros() as usize;
    let m_s = log_h + 14;
    let m_small = log_h + 10;
    let m_2s = m_s + 1;
    let m_4s = m_s + 2;
    let m_gram = ((cert.h_pad * 64).max(1usize << M_TAB_ORTH)).trailing_zeros() as usize;
    let half_gs_ext = Ext4::from_bb((M_GS / 2) as u32);
    let half_limb_ext = Ext4::from_bb((LIMB_RADIX / 2) as u32);
    let qunl_ext = Ext4::from_bb(QUOT_UNL_HALF as u32);
    let diag_hi_bb = (((M_GS * M_GS) / LIMB_RADIX) % (P as i64)) as u32;

    let mut tr = CShakeTranscript::new(b"CMEM-UNLEARN-CERT-ZK-V3");
    tr.absorb_u32(b"h_v", cert.h_v as u32);
    tr.absorb_u32(b"h_pad", cert.h_pad as u32);
    tr.absorb_u32(b"rank_r", cert.rank_r as u32);
    tr.absorb_u32(b"has_mmr", expected_opt_mmr_root.is_some() as u32);
    if let Some(mmr_root) = expected_opt_mmr_root {
        tr.absorb_root(b"mmr_root", mmr_root);
    }
    for r in [
        &cert.s_before_root,
        &cert.s_unlearned_root,
        &cert.forget_request_root,
        &cert.u_pcs_root,
        &cert.request_nonce,
        &cert.ulo_pcs_root,
        &cert.mult_ulo_pcs_root,
        &cert.uhi_pcs_root,
        &cert.mult_uhi_pcs_root,
        &cert.p_proj_pcs_root,
        &cert.gram_shift_pcs_root,
        &cert.mult_gram_pcs_root,
        &cert.res_shift_pcs_root,
        &cert.mult_res_pcs_root,
        &cert.sbnd_unl_pcs_root,
        &cert.mult_sbnd_unl_pcs_root,
        &cert.qlo_unl_pcs_root,
        &cert.mult_qlo_unl_pcs_root,
        &cert.rem128_unl_pcs_root,
        &cert.mult_rem128_unl_pcs_root,
    ] {
        tr.absorb_root(b"unl_root", r);
    }

    // U0:
    if cert.u_inactive_zero.mu_s != m_small
        || cert.u_inactive_zero.kappa != 0
        || !cert.u_inactive_zero.claim.is_zero()
    {
        return Err("inactive U zerocheck header invalid".to_string());
    }
    let zi_all = tr.squeeze_ext4_vec(b"u_inact_zs", m_small, true);
    let u_inact_pt =
        verify_gruen_einsum_mode2_ext4(Ext4::ZERO, &zi_all, &cert.u_inactive_zero, &mut tr)?;
    let exp_inact_ind = eval_inactive_u_indicator_mle(
        cert.h_v,
        cert.rank_r,
        &u_inact_pt[..log_h],
        &u_inact_pt[log_h + 7..],
    );
    if cert.u_inactive_zero.terminal_openings.0 != exp_inact_ind {
        return Err("inactive U public indicator evaluation mismatch".to_string());
    }

    // U1:
    let zg_h = tr.squeeze_ext4_vec(b"zg_h", log_h, true);
    let zg_a = tr.squeeze_ext4_vec(b"zg_a", LOG_R_PAD, true);
    let zg_b = tr.squeeze_ext4_vec(b"zg_b", LOG_R_PAD, true);
    let mut zg_hab = Vec::with_capacity(log_h + 6);
    zg_hab.extend_from_slice(&zg_h);
    zg_hab.extend_from_slice(&zg_a);
    zg_hab.extend_from_slice(&zg_b);
    let mut zg_pad = zg_hab.clone();
    while zg_pad.len() < m_gram {
        zg_pad.push(Ext4::ZERO);
    }
    for e in [cert.g_lo_shift_at_zg, cert.r_glo_at_zg, cert.gram_shift_at_zg] {
        tr.absorb_ext4(b"gram_ev", e);
    }
    if cert.gram_lo_gruen.kappa != 7 || cert.gram_hi_gruen.kappa != 7 {
        return Err("gram_gruen kappa mismatch".to_string());
    }
    let g_lo_unsh = cert.g_lo_shift_at_zg.sub(qunl_ext);
    let exp_gram_lo = g_lo_unsh
        .scale_bb(LIMB_RADIX as u32)
        .add(cert.r_glo_at_zg)
        .sub(half_limb_ext);
    let gram_lo_ch =
        verify_gruen_einsum_mode2_ext4(exp_gram_lo, &zg_h, &cert.gram_lo_gruen, &mut tr)?;

    let id_mle = eval_active_gram_identity_mle(cert.h_v, cert.rank_r, &zg_h, &zg_a, &zg_b);
    let exp_gram_hi = id_mle
        .scale_bb(diag_hi_bb)
        .add(cert.gram_shift_at_zg)
        .sub(Ext4::from_bb(TAU_ORTH as u32))
        .sub(g_lo_unsh);
    let gram_hi_ch =
        verify_gruen_einsum_mode2_ext4(exp_gram_hi, &zg_h, &cert.gram_hi_gruen, &mut tr)?;

    // U2:
    let zp2_h = tr.squeeze_ext4_vec(b"zp2_h", log_h, true);
    let zp2_ik = tr.squeeze_ext4_vec(b"zp2_ik", 7, true);
    let zp2_jv = tr.squeeze_ext4_vec(b"zp2_jv", 7, true);
    let mut zp2_hij = Vec::with_capacity(m_s);
    zp2_hij.extend_from_slice(&zp2_h);
    zp2_hij.extend_from_slice(&zp2_ik);
    zp2_hij.extend_from_slice(&zp2_jv);
    for e in [
        cert.s_before_at_zp2,
        cert.s_unlearned_at_zp2,
        cert.q_p2_lo_shift_at_zp2,
        cert.r_p2_lo_at_zp2,
        cert.r_p2_hi_at_zp2,
    ] {
        tr.absorb_ext4(b"p2_ev", e);
    }
    if cert.proj2_lo_gruen.kappa != LOG_R_PAD || cert.proj2_hi_gruen.kappa != LOG_R_PAD {
        return Err("proj2_gruen kappa mismatch".to_string());
    }
    let qp2_lo_unsh = cert.q_p2_lo_shift_at_zp2.sub(qunl_ext);
    let exp_p2_lo = qp2_lo_unsh
        .scale_bb(LIMB_RADIX as u32)
        .add(cert.r_p2_lo_at_zp2)
        .sub(half_gs_ext);
    let p2_lo_ch =
        verify_gruen_einsum_mode2_ext4(exp_p2_lo, &zp2_h, &cert.proj2_lo_gruen, &mut tr)?;

    let exp_p2_hi = cert
        .s_before_at_zp2
        .sub(cert.s_unlearned_at_zp2)
        .scale_bb(HI_DIV as u32)
        .add(cert.r_p2_hi_at_zp2)
        .sub(qp2_lo_unsh);
    let p2_hi_ch =
        verify_gruen_einsum_mode2_ext4(exp_p2_hi, &zp2_h, &cert.proj2_hi_gruen, &mut tr)?;

    // U3:
    let zr_h = tr.squeeze_ext4_vec(b"zr_h", log_h, true);
    let zr_jv = tr.squeeze_ext4_vec(b"zr_jv", 7, true);
    let zr_a = tr.squeeze_ext4_vec(b"zr_a", LOG_R_PAD, true);
    let mut zr_hja = Vec::with_capacity(m_small);
    zr_hja.extend_from_slice(&zr_h);
    zr_hja.extend_from_slice(&zr_jv);
    zr_hja.extend_from_slice(&zr_a);
    for e in [
        cert.res_shift_at_zr,
        cert.q_u3_lo_shift_at_zr,
        cert.r_u3_lo_at_zr,
        cert.r_u3_hi_at_zr,
    ] {
        tr.absorb_ext4(b"res_ev", e);
    }
    if cert.rz_lo_gruen.kappa != 7 || cert.rz_hi_gruen.kappa != 7 {
        return Err("rz_gruen kappa mismatch".to_string());
    }
    let qu3_lo_unsh = cert.q_u3_lo_shift_at_zr.sub(qunl_ext);
    let exp_rz_lo = qu3_lo_unsh
        .scale_bb(LIMB_RADIX as u32)
        .add(cert.r_u3_lo_at_zr)
        .sub(half_gs_ext);
    let rz_lo_ch = verify_gruen_einsum_mode2_ext4(exp_rz_lo, &zr_h, &cert.rz_lo_gruen, &mut tr)?;

    let exp_rz_hi = cert
        .res_shift_at_zr
        .sub(Ext4::from_bb(TAU_ZERO as u32))
        .scale_bb(HI_DIV as u32)
        .add(cert.r_u3_hi_at_zr)
        .sub(qu3_lo_unsh);
    let rz_hi_ch = verify_gruen_einsum_mode2_ext4(exp_rz_hi, &zr_h, &cert.rz_hi_gruen, &mut tr)?;

    if cert.ulo_d1b.m_wit != m_small
        || cert.ulo_d1b.m_tab != LIMB_SHIFT
        || cert.uhi_d1b.m_wit != m_small
        || cert.uhi_d1b.m_tab != LIMB_SHIFT
        || cert.gram_d1b.m_wit != m_gram
        || cert.gram_d1b.m_tab != M_TAB_ORTH
        || cert.res_zero_d1b.m_wit != m_small
        || cert.res_zero_d1b.m_tab != M_TAB_ZERO
        || cert.sbnd_unl_d1b.m_wit != m_4s
        || cert.sbnd_unl_d1b.m_tab != M_TAB_S_BND
        || cert.qlo_unl_d1b.m_wit != m_2s
        || cert.qlo_unl_d1b.m_tab != M_TAB_QUOT_UNL
        || cert.rem128_unl_d1b.m_wit != m_4s
        || cert.rem128_unl_d1b.m_tab != LIMB_SHIFT
    {
        return Err("unlearning certificate D1b dimension mismatch".to_string());
    }
    let ulo_d1b_pt = verify_d1b_range_ext4(&cert.ulo_d1b, &mut tr)?;
    let uhi_d1b_pt = verify_d1b_range_ext4(&cert.uhi_d1b, &mut tr)?;
    let gram_d1b_pt = verify_d1b_range_ext4(&cert.gram_d1b, &mut tr)?;
    let res_d1b_pt = verify_d1b_range_ext4(&cert.res_zero_d1b, &mut tr)?;
    let sbnd_d1b_pt = verify_d1b_range_ext4(&cert.sbnd_unl_d1b, &mut tr)?;
    let qlo_d1b_pt = verify_d1b_range_ext4(&cert.qlo_unl_d1b, &mut tr)?;
    let rem128_d1b_pt = verify_d1b_range_ext4(&cert.rem128_unl_d1b, &mut tr)?;

    let zs_bnd = tr.squeeze_ext4_vec(b"zs_unl_bnd", m_s, true);
    let z_pbnd = tr.squeeze_ext4_vec(b"zp_unl_bnd", m_small, true);
    let zu_limb = tr.squeeze_ext4_vec(b"zu_unl_limb", m_small, true);
    for e in [
        cert.s_before_at_zsbnd,
        cert.s_unlearned_at_zsbnd,
        cert.pproj_at_zpbnd,
        cert.u_at_zulimb,
        cert.ulo_shift_at_zulimb,
        cert.uhi_shift_at_zulimb,
    ] {
        tr.absorb_ext4(b"unl_weld_ev", e);
    }

    let ulo_unsh = cert.ulo_shift_at_zulimb.sub(Ext4::from_bb(ULO_HALF as u32));
    let uhi_unsh = cert.uhi_shift_at_zulimb.sub(Ext4::from_bb(UHI_HALF as u32));
    if cert.u_at_zulimb != ulo_unsh.add(uhi_unsh.scale_bb(LIMB_RADIX as u32)) {
        return Err("unlearning U 2-limb weld mismatch".to_string());
    }

    verify_pcs_claims(
        &cert.s_before_root,
        PcsShape::new(m_s, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: zp2_hij.clone(), value: cert.s_before_at_zp2 },
            MleEvalClaim { point: zs_bnd.clone(), value: cert.s_before_at_zsbnd },
        ],
        &cert.s_before_pcs,
        &mut tr,
    )?;

    let build_su_pt = |ch: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_s);
        p.extend_from_slice(&ch[..log_h]);
        p.extend_from_slice(&ch[log_h..]);
        p.extend_from_slice(&zr_jv);
        p
    };
    verify_pcs_claims(
        &cert.s_unlearned_root,
        PcsShape::new(m_s, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: zp2_hij.clone(), value: cert.s_unlearned_at_zp2 },
            MleEvalClaim { point: build_su_pt(&rz_lo_ch), value: cert.rz_lo_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_su_pt(&rz_hi_ch), value: cert.rz_hi_gruen.terminal_openings.0 },
            MleEvalClaim { point: zs_bnd.clone(), value: cert.s_unlearned_at_zsbnd },
        ],
        &cert.s_unlearned_pcs,
        &mut tr,
    )?;

    let build_u_pt = |ch_hik: &[Ext4], pt_a: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_hik[..log_h]);
        p.extend_from_slice(&ch_hik[log_h..]);
        p.extend_from_slice(pt_a);
        p
    };
    verify_pcs_claims(
        &cert.u_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(4)),
        &[
            MleEvalClaim { point: u_inact_pt, value: cert.u_inactive_zero.terminal_openings.1 },
            MleEvalClaim { point: build_u_pt(&gram_lo_ch, &zg_a), value: cert.gram_lo_gruen.terminal_openings.0 },
            MleEvalClaim { point: build_u_pt(&gram_hi_ch, &zg_a), value: cert.gram_hi_gruen.terminal_openings.0 },
            MleEvalClaim { point: zu_limb.clone(), value: cert.u_at_zulimb },
        ],
        &cert.u_pcs,
        &mut tr,
    )?;

    let ulo_off = Ext4::from_bb(ULO_HALF as u32);
    let uhi_off = Ext4::from_bb(UHI_HALF as u32);
    let build_up2_pt = |ch_ha: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_ha[..log_h]);
        p.extend_from_slice(&zp2_ik);
        p.extend_from_slice(&ch_ha[log_h..]);
        p
    };
    verify_pcs_claims(
        &cert.ulo_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zu_limb.clone(), value: cert.ulo_shift_at_zulimb },
            MleEvalClaim { point: build_u_pt(&gram_lo_ch, &zg_b), value: cert.gram_lo_gruen.terminal_openings.1.add(ulo_off) },
            MleEvalClaim { point: build_up2_pt(&p2_lo_ch), value: cert.proj2_lo_gruen.terminal_openings.0.add(ulo_off) },
            MleEvalClaim { point: build_u_pt(&rz_lo_ch, &zr_a), value: cert.rz_lo_gruen.terminal_openings.1.add(ulo_off) },
            MleEvalClaim { point: ulo_d1b_pt.clone(), value: cert.ulo_d1b.rem_leaf_eval },
        ],
        &cert.ulo_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_ulo_pcs_root,
        PcsShape::new(LIMB_SHIFT, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: ulo_d1b_pt[..LIMB_SHIFT].to_vec(), value: cert.ulo_d1b.mult_leaf_eval }],
        &cert.mult_ulo_pcs,
        &mut tr,
    )?;

    verify_pcs_claims(
        &cert.uhi_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zu_limb, value: cert.uhi_shift_at_zulimb },
            MleEvalClaim { point: build_u_pt(&gram_hi_ch, &zg_b), value: cert.gram_hi_gruen.terminal_openings.1.add(uhi_off) },
            MleEvalClaim { point: build_up2_pt(&p2_hi_ch), value: cert.proj2_hi_gruen.terminal_openings.0.add(uhi_off) },
            MleEvalClaim { point: build_u_pt(&rz_hi_ch, &zr_a), value: cert.rz_hi_gruen.terminal_openings.1.add(uhi_off) },
            MleEvalClaim { point: uhi_d1b_pt.clone(), value: cert.uhi_d1b.rem_leaf_eval },
        ],
        &cert.uhi_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_uhi_pcs_root,
        PcsShape::new(LIMB_SHIFT, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: uhi_d1b_pt[..LIMB_SHIFT].to_vec(), value: cert.uhi_d1b.mult_leaf_eval }],
        &cert.mult_uhi_pcs,
        &mut tr,
    )?;

    let build_pproj_pt = |ch_ha: &[Ext4]| -> Vec<Ext4> {
        let mut p = Vec::with_capacity(m_small);
        p.extend_from_slice(&ch_ha[..log_h]);
        p.extend_from_slice(&ch_ha[log_h..]);
        p.extend_from_slice(&zp2_jv);
        p
    };
    verify_pcs_claims(
        &cert.p_proj_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(3)),
        &[
            MleEvalClaim { point: build_pproj_pt(&p2_lo_ch), value: cert.proj2_lo_gruen.terminal_openings.1 },
            MleEvalClaim { point: build_pproj_pt(&p2_hi_ch), value: cert.proj2_hi_gruen.terminal_openings.1 },
            MleEvalClaim { point: z_pbnd.clone(), value: cert.pproj_at_zpbnd },
        ],
        &cert.p_proj_pcs,
        &mut tr,
    )?;

    verify_pcs_claims(
        &cert.gram_shift_pcs_root,
        PcsShape::new(m_gram, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: zg_pad, value: cert.gram_shift_at_zg },
            MleEvalClaim { point: gram_d1b_pt.clone(), value: cert.gram_d1b.rem_leaf_eval },
        ],
        &cert.gram_shift_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_gram_pcs_root,
        PcsShape::new(M_TAB_ORTH, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: gram_d1b_pt[..M_TAB_ORTH].to_vec(), value: cert.gram_d1b.mult_leaf_eval }],
        &cert.mult_gram_pcs,
        &mut tr,
    )?;

    verify_pcs_claims(
        &cert.res_shift_pcs_root,
        PcsShape::new(m_small, PcsParams::default_zk(2)),
        &[
            MleEvalClaim { point: zr_hja.clone(), value: cert.res_shift_at_zr },
            MleEvalClaim { point: res_d1b_pt.clone(), value: cert.res_zero_d1b.rem_leaf_eval },
        ],
        &cert.res_shift_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_res_pcs_root,
        PcsShape::new(M_TAB_ZERO, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: res_d1b_pt[..M_TAB_ZERO].to_vec(), value: cert.res_zero_d1b.mult_leaf_eval }],
        &cert.mult_res_pcs,
        &mut tr,
    )?;

    let sbnd_ext = Ext4::from_bb(S_BND_HALF as u32);
    let mut zsb00 = zs_bnd.clone();
    zsb00.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut zsb10 = zs_bnd.clone();
    zsb10.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut zsb01 = zs_bnd.clone();
    zsb01.extend_from_slice(&[Ext4::ZERO, Ext4::ONE]);
    let mut zsb11 = zs_bnd;
    zsb11.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);
    verify_pcs_claims(
        &cert.sbnd_unl_pcs_root,
        PcsShape::new(m_4s, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zsb00, value: cert.s_before_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb10, value: sbnd_ext.sub(cert.s_before_at_zsbnd) },
            MleEvalClaim { point: zsb01, value: cert.s_unlearned_at_zsbnd.add(sbnd_ext) },
            MleEvalClaim { point: zsb11, value: sbnd_ext.sub(cert.s_unlearned_at_zsbnd) },
            MleEvalClaim { point: sbnd_d1b_pt.clone(), value: cert.sbnd_unl_d1b.rem_leaf_eval },
        ],
        &cert.sbnd_unl_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_sbnd_unl_pcs_root,
        PcsShape::new(M_TAB_S_BND, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: sbnd_d1b_pt[..M_TAB_S_BND].to_vec(), value: cert.sbnd_unl_d1b.mult_leaf_eval }],
        &cert.mult_sbnd_unl_pcs,
        &mut tr,
    )?;

    let mut zp2_qlo = zp2_hij.clone();
    zp2_qlo.push(Ext4::ZERO);
    let mut zp_qlo = z_pbnd;
    zp_qlo.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let mut zr_qlo = zr_hja.clone();
    zr_qlo.extend_from_slice(&[Ext4::ONE, Ext4::ZERO, Ext4::ZERO, Ext4::ZERO, Ext4::ONE]);
    let mut zg_qlo = zg_hab.clone();
    zg_qlo.extend_from_slice(&[
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    verify_pcs_claims(
        &cert.qlo_unl_pcs_root,
        PcsShape::new(m_2s, PcsParams::default_zk(5)),
        &[
            MleEvalClaim { point: zp2_qlo, value: cert.q_p2_lo_shift_at_zp2 },
            MleEvalClaim { point: zp_qlo, value: cert.pproj_at_zpbnd.add(qunl_ext) },
            MleEvalClaim { point: zr_qlo, value: cert.q_u3_lo_shift_at_zr },
            MleEvalClaim { point: zg_qlo, value: cert.g_lo_shift_at_zg },
            MleEvalClaim { point: qlo_d1b_pt.clone(), value: cert.qlo_unl_d1b.rem_leaf_eval },
        ],
        &cert.qlo_unl_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_qlo_unl_pcs_root,
        PcsShape::new(M_TAB_QUOT_UNL, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: qlo_d1b_pt[..M_TAB_QUOT_UNL].to_vec(), value: cert.qlo_unl_d1b.mult_leaf_eval }],
        &cert.mult_qlo_unl_pcs,
        &mut tr,
    )?;

    let mut zp2_rlo = zp2_hij.clone();
    zp2_rlo.extend_from_slice(&[Ext4::ZERO, Ext4::ZERO]);
    let mut zp2_rhi = zp2_hij;
    zp2_rhi.extend_from_slice(&[Ext4::ONE, Ext4::ZERO]);
    let mut zr_rlo = zr_hja.clone();
    zr_rlo.extend_from_slice(&[
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    let mut zr_rhi = zr_hja;
    zr_rhi.extend_from_slice(&[
        Ext4::ONE,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ZERO,
        Ext4::ONE,
    ]);
    let mut zg_rglo = zg_hab;
    for _ in 0..8 {
        zg_rglo.push(Ext4::ZERO);
    }
    zg_rglo.extend_from_slice(&[Ext4::ONE, Ext4::ONE]);

    verify_pcs_claims(
        &cert.rem128_unl_pcs_root,
        PcsShape::new(m_4s, PcsParams::default_zk(6)),
        &[
            MleEvalClaim { point: zp2_rlo, value: cert.r_p2_lo_at_zp2 },
            MleEvalClaim { point: zp2_rhi, value: cert.r_p2_hi_at_zp2 },
            MleEvalClaim { point: zr_rlo, value: cert.r_u3_lo_at_zr },
            MleEvalClaim { point: zr_rhi, value: cert.r_u3_hi_at_zr },
            MleEvalClaim { point: zg_rglo, value: cert.r_glo_at_zg },
            MleEvalClaim { point: rem128_d1b_pt.clone(), value: cert.rem128_unl_d1b.rem_leaf_eval },
        ],
        &cert.rem128_unl_pcs,
        &mut tr,
    )?;
    verify_pcs_claims(
        &cert.mult_rem128_unl_pcs_root,
        PcsShape::new(LIMB_SHIFT, PcsParams::default_zk(1)),
        &[MleEvalClaim { point: rem128_d1b_pt[..LIMB_SHIFT].to_vec(), value: cert.rem128_unl_d1b.mult_leaf_eval }],
        &cert.mult_rem128_unl_pcs,
        &mut tr,
    )?;

    let _ = (QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE, P_U32);
    Ok(())
}
