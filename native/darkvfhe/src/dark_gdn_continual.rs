#![deny(warnings)]
//! Wave 11 Lane 5: Exact 3-Custodian `B61` vFHE/SPDZ × `Qwen3.5-0.8B` Gated-DeltaNet (`16 × 128 × 128`)
//! Fast-Weight Dark Continual Memory & Exact `W0` Subspace Unlearning (`DarkB61GdnResident`).
//!
//! The provider keeps each 64 × 128 row slice in one negacyclic BFV ciphertext. The
//! custodian harness performs signed, epoch-gated state reads and SPDZ chunk solves,
//! followed by certified ciphertext updates. All three roles run in one process.
//! Serialized state openings cover the final public ciphertexts. Intermediate rescale
//! witnesses and partial decryption transcripts stay inside the harness.

use crate::bigint::lift_q_to_8limbs_and_u;
use crate::cert::{
    ct2_handle, ct3_handle, precompute_shared_grid, prove_hoisted_matvec, verify_hoisted_matvec,
    HoistedWitness, ProveOptions, SharedGridLifts, VerifyOptions,
};
use crate::dark_block::{
    add_ct2_mod_q, check_canonical_ct2, check_canonical_ct3, derive_homomorphic_state_noise_budget,
    os_csprng_seed32, setup_threshold_cluster_with_rlk,
};
use crate::dark_gdn::{PartyShare, SharedScalar, ThreeCustodianCluster, NUM_CUSTODIANS};
use crate::digits::{DigitCols, ExactGarnerSpec, LiftMode};
use crate::logup_gkr::{
    count_multiplicities_parallel, prove_logup_gkr_with_mults, verify_logup_gkr, FractionTreeProof,
    GkrLayerProof, LogUpConfig, LogUpGkrProof, TABLE_LOG2, TABLE_SIZE,
};
use crate::rns_hoist::{Ct3, HoistedEngine, PrecomputedCt, RelinearizationKey};
use crate::succinct_pcs::{ByteReader, Ext3, Ext3Field, PcsRng, PcsTranscript, SlotLinearClaim};
use crate::threshold_custody::{
    EnrolledThresholdRoster, HybridPqCustodianIdentity, HybridPqSignature,
};
use crate::whir_pcs::{
    pack_ext3_slice, pack_u64_bits_le, prove_hoisted_whir, unpack_ext3_slice, unpack_u64_bits_le,
    verify_gmask61_rounds, verify_hoisted_whir_bytes, verify_whir_pcs61, GMask61, GMaskSpec61,
    WhirCommittedPcs61, WhirOpeningBundle61, WhirShape61, WHIR_BLOWUP, WHIR_T_QUERIES_128,
};
use crate::{process_memory_mib, FastPrime61, HoistedParams};
use darkstep::arith::submod;
use darkstep::bfv::Ct;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;
use std::time::Instant;

pub const QWEN35_GDN_HEADS: usize = 16;
pub const QWEN35_GDN_DV: usize = 128;
pub const QWEN35_GDN_DK: usize = 128;
pub const QWEN35_SLICE_ROWS: usize = 64;
pub const QWEN35_SLICES_PER_HEAD: usize = 2;
pub const QWEN35_STATE_CTS: usize = 32;

pub const CONTINUAL_WHIR_MAGIC: &[u8; 8] = b"DVFHEC61";
pub const CONTINUAL_WHIR_VERSION: u32 = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContinualGdnError {
    InvalidGeometry(&'static str),
    ZeroEpochRejected,
    PolicyBudgetExceeded {
        got: u64,
        budget: u64,
    },
    StaleOrReplayEpochRejected {
        got: u64,
        high_water: u64,
    },
    PolicyDigestMismatch,
    InsufficientQuorumSignatures {
        have: usize,
        need: usize,
    },
    NonCanonicalSigners,
    HybridSignatureRejected(String),
    SnapshotShadowBranchRejected,
    EpisodeNotFound(usize),
    EpisodeAlreadyUnlearned(usize),
    CrossTermNonOrthogonal {
        episode_id: usize,
        post_chunk_id: usize,
    },
    InvalidRescaleCertificate(String),
    InvalidRelinearization(String),
    InvalidCrossingProof(String),
    InvalidSpdzMac(String),
    InvalidWhirProof(String),
}

impl fmt::Display for ContinualGdnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ContinualGdnError {}

pub type Result<T> = std::result::Result<T, ContinualGdnError>;

// ================================================================================================
// §1. Exact Cleartext Gated-DeltaNet Fast-Weight & Division-Free WY Reference (`F_t`)
// ================================================================================================

/// Per-step inputs `(gamma, beta, k[0..d_k], v[0..d_v])` over `F_t` for one GDN head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GdnHeadStepPlain {
    pub gamma: u64,
    pub beta: u64,
    pub k: Vec<u64>,
    pub v: Vec<u64>,
}

/// One multi-head chunk of length `tau >= 1` (`heads[0..num_heads][0..tau]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GdnChunkPlain {
    pub tau: usize,
    pub heads: Vec<Vec<GdnHeadStepPlain>>,
}

/// Sequential fast-weight recurrence `S_{t+1} = gamma_t S_t + beta_t (v_t - S_t k_t) k_t^T mod t`.
pub fn cleartext_fast_weight_step(
    fp_t: &FastPrime61,
    s_mat: &[Vec<u64>], // d_v x d_k
    inp: &GdnHeadStepPlain,
) -> Vec<Vec<u64>> {
    let d_v = s_mat.len();
    let d_k = s_mat[0].len();
    assert_eq!(inp.k.len(), d_k);
    assert_eq!(inp.v.len(), d_v);

    let mut sk = vec![0u64; d_v];
    for r in 0..d_v {
        sk[r] = fp_t.dot(&s_mat[r], &inp.k);
    }
    let mut u = vec![0u64; d_v];
    for r in 0..d_v {
        u[r] = fp_t.mul(inp.beta % fp_t.p, fp_t.sub(inp.v[r] % fp_t.p, sk[r]));
    }
    let g = inp.gamma % fp_t.p;
    let mut next = vec![vec![0u64; d_k]; d_v];
    for r in 0..d_v {
        for c in 0..d_k {
            let decayed = fp_t.mul(g, s_mat[r][c] % fp_t.p);
            let outer = fp_t.mul(u[r], inp.k[c] % fp_t.p);
            next[r][c] = fp_t.add(decayed, outer);
        }
    }
    next
}

pub fn cleartext_fast_weight_seq(
    fp_t: &FastPrime61,
    s0: &[Vec<u64>],
    steps: &[GdnHeadStepPlain],
) -> Vec<Vec<u64>> {
    let mut cur = s0.to_vec();
    for st in steps {
        cur = cleartext_fast_weight_step(fp_t, &cur, st);
    }
    cur
}

/// Division-free Neumann inverse `(I + L)^{-1} = sum_{p=0}^{tau - 1} (-L)^p` over `F_t` (`0` divisions!).
pub fn neumann_inv_strict_lower_tri(fp_t: &FastPrime61, l_mat: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let tau = l_mat.len();
    for (i, row) in l_mat.iter().enumerate() {
        assert_eq!(row.len(), tau);
        for &val in &row[i..] {
            assert_eq!(val, 0, "L must be strictly lower triangular");
        }
    }
    let mut inverse = vec![vec![0; tau]; tau];
    for (i, l_row) in l_mat.iter().enumerate() {
        inverse[i][i] = 1;
        let (upper, cur_row) = inverse.split_at_mut(i);
        for (j, inv_ij) in cur_row[0].iter_mut().enumerate().take(i) {
            let sum = (j..i).fold(0, |acc, k| fp_t.add(acc, fp_t.mul(l_row[k], upper[k][j])));
            *inv_ij = fp_t.neg(sum);
        }
    }
    inverse
}

type CleartextWyChunkResult = (Vec<Vec<u64>>, u64, Vec<Vec<u64>>, Vec<Vec<u64>>);

/// Stateful division-free WY chunk update `(I + L) U = V - K_in S_0^T`,
/// `S_tau = Gamma_tau S_0 + U^T K_decayed^T` over `F_t`.
pub fn cleartext_wy_chunk_head(
    fp_t: &FastPrime61,
    s0: &[Vec<u64>],
    chunk: &[GdnHeadStepPlain],
) -> CleartextWyChunkResult {
    let tau = chunk.len();
    let d_v = s0.len();
    let d_k = s0[0].len();

    let decay_range = |a: usize, b: usize| -> u64 {
        chunk[a..b]
            .iter()
            .fold(1u64, |prod, st| fp_t.mul(prod, st.gamma % fp_t.p))
    };

    let gamma_tau = decay_range(0, tau);
    let mut l_mat = vec![vec![0u64; tau]; tau];
    for i in 0..tau {
        for j in 0..i {
            let g_pair = decay_range(j + 1, i);
            let kj_ki = fp_t.dot(&chunk[j].k, &chunk[i].k);
            l_mat[i][j] = fp_t.mul(fp_t.mul(chunk[i].beta % fp_t.p, g_pair), kj_ki);
        }
    }
    let inv_i_plus_l = neumann_inv_strict_lower_tri(fp_t, &l_mat);

    let mut rhs = vec![vec![0u64; d_v]; tau];
    for i in 0..tau {
        let bi = chunk[i].beta % fp_t.p;
        let bi_g0i = fp_t.mul(bi, decay_range(0, i));
        for r in 0..d_v {
            let s0_ki_r = fp_t.dot(&s0[r], &chunk[i].k);
            rhs[i][r] = fp_t.sub(
                fp_t.mul(bi, chunk[i].v[r] % fp_t.p),
                fp_t.mul(bi_g0i, s0_ki_r),
            );
        }
    }

    // U = (I + L)^{-1} * rhs (tau x d_v):
    let mut u_rows = vec![vec![0u64; d_v]; tau];
    for i in 0..tau {
        for m in 0..=i {
            let w = inv_i_plus_l[i][m];
            if w == 0 {
                continue;
            }
            for r in 0..d_v {
                u_rows[i][r] = fp_t.add(u_rows[i][r], fp_t.mul(w, rhs[m][r]));
            }
        }
    }

    let mut k_decayed_rows = vec![vec![0u64; d_k]; tau];
    for (j, k_dec_row) in k_decayed_rows.iter_mut().enumerate() {
        let g_tail = decay_range(j + 1, tau);
        for (dst, &k_val) in k_dec_row.iter_mut().zip(&chunk[j].k) {
            *dst = fp_t.mul(g_tail, k_val % fp_t.p);
        }
    }

    let mut s_out = vec![vec![0u64; d_k]; d_v];
    for r in 0..d_v {
        for c in 0..d_k {
            let mut acc = fp_t.mul(gamma_tau, s0[r][c] % fp_t.p);
            for m in 0..tau {
                acc = fp_t.add(acc, fp_t.mul(u_rows[m][r], k_decayed_rows[m][c]));
            }
            s_out[r][c] = acc;
        }
    }
    (s_out, gamma_tau, u_rows, k_decayed_rows)
}

pub fn cleartext_multihead_seq(
    fp_t: &FastPrime61,
    s0_heads: &[Vec<Vec<u64>>],
    chunks: &[GdnChunkPlain],
) -> Vec<Vec<Vec<u64>>> {
    let mut cur = s0_heads.to_vec();
    for ch in chunks {
        for (cur_h, ch_h) in cur.iter_mut().zip(&ch.heads) {
            *cur_h = cleartext_fast_weight_seq(fp_t, cur_h, ch_h);
        }
    }
    cur
}

// ================================================================================================
// §2. Stride-128 Coefficient Ring Packing & Unpacking (`R_t = (Z/tZ)[X]/(X^N + 1)`)
// ================================================================================================

#[inline]
pub fn pack_fast_weight_slice(
    s_head: &[Vec<u64>],
    slice_idx: usize,
    slice_rows: usize,
    d_k: usize,
    n: usize,
    t: u64,
) -> Vec<u64> {
    let mut poly = vec![0u64; n];
    let row_base = slice_idx * slice_rows;
    for i in 0..slice_rows {
        for j in 0..d_k {
            poly[i * d_k + j] = s_head[row_base + i][j] % t;
        }
    }
    poly
}

#[inline]
pub fn pack_stride_u_poly(
    u_vec: &[u64],
    slice_idx: usize,
    slice_rows: usize,
    d_k: usize,
    n: usize,
    t: u64,
) -> Vec<u64> {
    let mut poly = vec![0u64; n];
    let row_base = slice_idx * slice_rows;
    for i in 0..slice_rows {
        poly[i * d_k] = u_vec[row_base + i] % t;
    }
    poly
}

#[inline]
pub fn pack_contig_k_poly(k_vec: &[u64], d_k: usize, n: usize, t: u64) -> Vec<u64> {
    let mut poly = vec![0u64; n];
    for j in 0..d_k {
        poly[j] = k_vec[j] % t;
    }
    poly
}

#[inline]
pub fn pack_rev_k_poly(k_vec: &[u64], d_k: usize, n: usize, t: u64) -> Vec<u64> {
    let mut poly = vec![0u64; n];
    for c in 0..d_k {
        poly[(d_k - 1) - c] = k_vec[c] % t;
    }
    poly
}

pub fn sub_ct2_mod_q(params: &HoistedParams, a: &Ct, b: &Ct) -> Ct {
    let n = params.n;
    let mut c0 = vec![0u64; 3 * n];
    let mut c1 = vec![0u64; 3 * n];
    for k in 0..3 {
        let qk = params.qp[k];
        for j in 0..n {
            let idx = k * n + j;
            c0[idx] = submod(a.c0[idx], b.c0[idx], qk);
            c1[idx] = submod(a.c1[idx], b.c1[idx], qk);
        }
    }
    Ct { c0, c1 }
}

pub fn compute_state_handles_commitment(handles: &[[u8; 32]]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_B61_GDN_STATE_CHAIN_V1|");
    h.update((handles.len() as u32).to_le_bytes());
    for hd in handles {
        h.update(hd);
    }
    h.finalize().into()
}

// ================================================================================================
// §3. 3-Custodian (`NoSingleViewer >= 2`) Hybrid-PQ Monotonic Epoch Custody Gate
// ================================================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContinualActionTag {
    AdaptChunk {
        chunk_id: usize,
        tau: usize,
    },
    StateRefresh {
        chunk_id: usize,
    },
    W0UnlearnOrthogonal {
        episode_id: usize,
    },
    W0UnlearnWyReplay {
        episode_id: usize,
        replay_idx: usize,
        checkpoint_id: usize,
        checkpoint: [u8; 32],
    },
    AuditOpen,
}

impl ContinualActionTag {
    fn write_preimage(&self, out: &mut Vec<u8>) {
        match *self {
            ContinualActionTag::AuditOpen => out.push(5),
            ContinualActionTag::AdaptChunk { chunk_id, tau } => {
                out.push(1);
                out.extend_from_slice(&(chunk_id as u64).to_le_bytes());
                out.extend_from_slice(&(tau as u64).to_le_bytes());
            }
            ContinualActionTag::StateRefresh { chunk_id } => {
                out.push(2);
                out.extend_from_slice(&(chunk_id as u64).to_le_bytes());
                out.extend_from_slice(&0u64.to_le_bytes());
            }
            ContinualActionTag::W0UnlearnOrthogonal { episode_id } => {
                out.push(3);
                out.extend_from_slice(&(episode_id as u64).to_le_bytes());
                out.extend_from_slice(&0u64.to_le_bytes());
            }
            ContinualActionTag::W0UnlearnWyReplay {
                episode_id,
                replay_idx,
                checkpoint_id,
                checkpoint,
            } => {
                out.push(4);
                out.extend_from_slice(&(checkpoint_id as u64).to_le_bytes());
                out.extend_from_slice(&checkpoint);
                out.extend_from_slice(&(episode_id as u64).to_le_bytes());
                out.extend_from_slice(&(replay_idx as u64).to_le_bytes());
            }
        }
    }
}

/// `t`-of-`n` (`t >= 2`, `n = 3`) Hybrid-PQ quorum-signed crossing authorization binding monotonic
/// `epoch`, `policy_digest`, `parent_state_commitment`, and verified compute certificate digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumEpochAuthorization {
    pub roster_digest: [u8; 32],
    pub epoch: u64,
    pub action: ContinualActionTag,
    pub policy_digest: [u8; 32],
    pub parent_state_commitment: [u8; 32],
    pub compute_cert_digest: [u8; 32],
    pub signers: Vec<usize>,
    pub signatures: Vec<HybridPqSignature>,
}

impl QuorumEpochAuthorization {
    pub fn signing_preimage(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(192);
        out.extend_from_slice(b"DARKVFHE_B61_CONTINUAL_EPOCH_AUTH_V1|");
        out.extend_from_slice(&self.roster_digest);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        self.action.write_preimage(&mut out);
        out.extend_from_slice(&self.policy_digest);
        out.extend_from_slice(&self.parent_state_commitment);
        out.extend_from_slice(&self.compute_cert_digest);
        out.extend_from_slice(&(self.signers.len() as u32).to_le_bytes());
        for &s in &self.signers {
            out.extend_from_slice(&(s as u32).to_le_bytes());
        }
        out
    }
}

/// Independent per-custodian monotonic policy latch (`NoSingleViewer >= 2`).
#[derive(Clone, Debug)]
pub struct CustodianMonotonicLatch {
    pub party_id: usize,
    pub max_authorized_epoch: u64,
    pub high_water_epoch: u64,
    pub pinned_policy_digest: [u8; 32],
    pub expected_head_commitment: [u8; 32],
    pub checkpoint_commitments: BTreeMap<usize, [u8; 32]>,
    pub signer_min_pq_leaves: [u64; NUM_CUSTODIANS],
    pub completed_epochs: Vec<u64>,
}

impl CustodianMonotonicLatch {
    pub fn verify_and_advance(
        &mut self,
        roster: &EnrolledThresholdRoster,
        auth: &QuorumEpochAuthorization,
    ) -> Result<()> {
        roster
            .verify_integrity()
            .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
        if auth.roster_digest != roster.roster_digest {
            return Err(ContinualGdnError::HybridSignatureRejected(
                "roster_digest mismatch".into(),
            ));
        }
        if auth.epoch == 0 {
            return Err(ContinualGdnError::ZeroEpochRejected);
        }
        if auth.epoch > self.max_authorized_epoch {
            return Err(ContinualGdnError::PolicyBudgetExceeded {
                got: auth.epoch,
                budget: self.max_authorized_epoch,
            });
        }
        if auth.epoch <= self.high_water_epoch {
            return Err(ContinualGdnError::StaleOrReplayEpochRejected {
                got: auth.epoch,
                high_water: self.high_water_epoch,
            });
        }
        if auth.policy_digest != self.pinned_policy_digest {
            return Err(ContinualGdnError::PolicyDigestMismatch);
        }

        // Verify expected parent state commitment (rejects snapshotted `ct_S` shadow branches!):
        if auth.parent_state_commitment != self.expected_head_commitment {
            return Err(ContinualGdnError::SnapshotShadowBranchRejected);
        }
        if let ContinualActionTag::W0UnlearnWyReplay {
            replay_idx: 0,
            checkpoint_id,
            checkpoint,
            ..
        } = auth.action
        {
            if self.checkpoint_commitments.get(&checkpoint_id) != Some(&checkpoint) {
                return Err(ContinualGdnError::SnapshotShadowBranchRejected);
            }
        }

        let t_need = roster.threshold; // >= 2
        if auth.signers.len() < t_need
            || auth.signatures.len() != auth.signers.len()
            || auth.signers.windows(2).any(|w| w[0] >= w[1])
            || auth.signers.iter().any(|&p| p >= roster.n_parties)
        {
            if auth.signatures.len() < t_need || auth.signers.len() < t_need {
                return Err(ContinualGdnError::InsufficientQuorumSignatures {
                    have: auth.signatures.len().min(auth.signers.len()),
                    need: t_need,
                });
            }
            return Err(ContinualGdnError::NonCanonicalSigners);
        }

        let pre = auth.signing_preimage();
        let mut seen = BTreeSet::new();
        let mut next_leaves = self.signer_min_pq_leaves;
        for (idx, sig) in auth.signatures.iter().enumerate() {
            let expected_signer = auth.signers[idx];
            if sig.signer_id != expected_signer || !seen.insert(sig.signer_id) {
                return Err(ContinualGdnError::NonCanonicalSigners);
            }
            let used_leaf = sig
                .verify(
                    &roster.enrollments[sig.signer_id],
                    self.signer_min_pq_leaves[sig.signer_id],
                    &pre,
                )
                .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
            next_leaves[sig.signer_id] = used_leaf + 1;
        }

        self.high_water_epoch = auth.epoch;
        self.signer_min_pq_leaves = next_leaves;
        self.completed_epochs.push(auth.epoch);
        Ok(())
    }
}

/// In-process harness for the three threshold BFV/SPDZ roles and their signature quorum.
pub struct ContinualCustodyQuorum {
    roster: EnrolledThresholdRoster,
    identities: [HybridPqCustodianIdentity; NUM_CUSTODIANS],
    latches: [CustodianMonotonicLatch; NUM_CUSTODIANS],
    cluster: ThreeCustodianCluster,
    rlk: Arc<RelinearizationKey>,
    next_epoch_counter: u64,
}

impl ContinualCustodyQuorum {
    pub fn next_epoch(&self) -> u64 {
        self.next_epoch_counter
    }
    pub fn high_water_epochs(&self) -> [u64; NUM_CUSTODIANS] {
        self.latches.each_ref().map(|latch| latch.high_water_epoch)
    }

    /// Setup 3-custodian (`2-of-3` Hybrid-PQ epoch authorization + `3-of-3` SPDZ / threshold BFV)
    /// custody using OS `/dev/urandom` CSPRNG (`s = s_0 + s_1 + s_2` is NEVER reconstructed!).
    pub fn setup(
        params: Arc<HoistedParams>,
        engine: Arc<HoistedEngine>,
        policy_digest: [u8; 32],
        max_authorized_epoch: u64,
    ) -> Result<Self> {
        let pq_height = 10usize; // 1,024 one-time PQ Merkle-Lamport leaves per custodian
        let id0 = HybridPqCustodianIdentity::generate_from_os(0, pq_height, None)
            .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
        let id1 = HybridPqCustodianIdentity::generate_from_os(1, pq_height, None)
            .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
        let id2 = HybridPqCustodianIdentity::generate_from_os(2, pq_height, None)
            .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
        let identities = [id0, id1, id2];
        let enrollments = vec![
            identities[0].enrollment(),
            identities[1].enrollment(),
            identities[2].enrollment(),
        ];
        // Two signatures authorize a request. All three latches must accept its epoch.
        let roster = EnrolledThresholdRoster::new(2, enrollments)
            .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;

        let (cluster, rlk) = setup_threshold_cluster_with_rlk(params, engine, os_csprng_seed32())
            .map_err(ContinualGdnError::InvalidRelinearization)?;

        let latches = std::array::from_fn(|party_id| CustodianMonotonicLatch {
            party_id,
            max_authorized_epoch,
            high_water_epoch: 0,
            pinned_policy_digest: policy_digest,
            expected_head_commitment: [0u8; 32],
            checkpoint_commitments: BTreeMap::new(),
            signer_min_pq_leaves: [0; NUM_CUSTODIANS],
            completed_epochs: Vec::new(),
        });

        Ok(ContinualCustodyQuorum {
            roster,
            identities,
            latches,
            cluster,
            rlk: Arc::new(rlk),
            next_epoch_counter: 1,
        })
    }

    /// Issue a `t`-quorum (`signers`, e.g. `[0, 1]` or `[0, 1, 2]`) Hybrid-PQ signed epoch authorization.
    pub fn sign_epoch_authorization(
        &mut self,
        epoch: u64,
        action: ContinualActionTag,
        policy_digest: [u8; 32],
        parent_state_commitment: [u8; 32],
        compute_cert_digest: [u8; 32],
        signers: &[usize],
    ) -> Result<QuorumEpochAuthorization> {
        let mut auth = QuorumEpochAuthorization {
            roster_digest: self.roster.roster_digest,
            epoch,
            action,
            policy_digest,
            parent_state_commitment,
            compute_cert_digest,
            signers: signers.to_vec(),
            signatures: Vec::with_capacity(signers.len()),
        };
        let pre = auth.signing_preimage();
        for &s in signers {
            if s >= NUM_CUSTODIANS {
                return Err(ContinualGdnError::NonCanonicalSigners);
            }
            let sig = self.identities[s]
                .sign(&pre)
                .map_err(|e| ContinualGdnError::HybridSignatureRejected(e.to_string()))?;
            auth.signatures.push(sig);
        }
        Ok(auth)
    }

    /// Verify `auth` across ALL 3 custodian monotonic latches atomically (rollback on any refusal!).
    pub fn verify_and_latch_all(&mut self, auth: &QuorumEpochAuthorization) -> Result<()> {
        let saved = self.latches.clone();
        for cust_latch in &mut self.latches {
            if let Err(e) = cust_latch.verify_and_advance(&self.roster, auth) {
                self.latches = saved;
                return Err(e);
            }
        }
        self.next_epoch_counter = auth.epoch.saturating_add(1);
        Ok(())
    }

    fn update_expected_head_all(&mut self, new_head: [u8; 32]) {
        for l in &mut self.latches {
            l.expected_head_commitment = new_head;
        }
    }

    fn record_checkpoint_all(&mut self, episode_id: usize, commitment: [u8; 32]) {
        for l in &mut self.latches {
            l.checkpoint_commitments.insert(episode_id, commitment);
        }
    }
}

// ================================================================================================
// §4. Unified `WhirPcs61 + GMask61` (`TVD = 0`, `>= 122`-bit Soundness) State & Rescale Proof
// ================================================================================================

/// Self-contained serialized `WhirPcs61 + GMask61 + D1b LogUp-GKR` (`DVFHEC61`) proof bundle
/// certifying `Exact-Garner-15` canonical `[0, Q - 1]` digit lifts across all `32` `N = 8192` `B61`
/// fast-weight ciphertexts (`64` ring polynomials) + `GMask61`-blinded HVZK sumcheck weld (`TVD == 0`)!
#[derive(Clone, Debug)]
pub struct ContinualWhirStateBundle {
    pub num_cts: usize,
    pub n: usize,
    pub mr: u8,
    pub mc: u8,
    pub t_queries: u16,
    pub blow: u8,
    pub state_commitment: [u8; 32],
    pub pcs_root: [u8; 32],
    /// Public evaluations at the three ciphertext primes, using 21-bit subsums for p1 and p2.
    pub p0_poly_evals: Vec<u64>,
    pub p12_poly_subsums: Vec<[u64; 3]>,
    /// `GMask61` HVZK (`TVD == 0`) masked sumcheck transcript over `slot 0` (`<1, d_{0,0}>` blinded!):
    pub unmasked_slot0_sum: u64,
    pub gmask_sum: Ext3,
    pub gmask_rounds: Vec<Vec<Ext3>>,
    pub gmask_terminal_masked: Ext3,
    /// D1b LogUp-GKR proof with four global challenges over the state lookup multiset,
    /// proving zero-slack `Exact-Garner-15` `[0, Q - 1]` canonicality across all `32` ciphertexts!
    pub logup_proof: LogUpGkrProof,
    /// `WhirPcs61` (`130.08b` `[BCIKS20]` UD / `185.32b` `[DKT26]` MCA) + internal `GMask61` opening!
    pub whir_opening: WhirOpeningBundle61,
}

#[inline]
fn split_21b_local(v: u64) -> [u64; 3] {
    const M21: u64 = (1u64 << 21) - 1;
    [v & M21, (v >> 21) & M21, v >> 42]
}

#[inline]
fn combine_21b_mod_local(fp: &FastPrime61, s: &[u64; 3]) -> u64 {
    let t21 = (1u64 << 21) % fp.p;
    let t42 = (1u64 << 42) % fp.p;
    fp.add(
        s[0] % fp.p,
        fp.add(fp.mul(s[1] % fp.p, t21), fp.mul(s[2] % fp.p, t42)),
    )
}

fn build_eq_le_local(fp: &FastPrime61, z: &[u64]) -> Vec<u64> {
    let mut v = vec![1u64];
    for &zk in z.iter().rev() {
        let om = fp.sub(1, zk);
        let mut next = Vec::with_capacity(v.len() * 2);
        for &val in &v {
            next.push(fp.mul(val, om));
            next.push(fp.mul(val, zk));
        }
        v = next;
    }
    v
}

#[derive(Clone, Debug)]
struct GarnerLookupColDesc {
    terms: Vec<(usize, u64)>,
    const_offset: u64,
}

fn build_garner15_lookup_descs(
    gspec: &ExactGarnerSpec,
    fp0: &FastPrime61,
    base_slot: usize,
    out: &mut Vec<GarnerLookupColDesc>,
) {
    let p = fp0.p;
    let inv2_20 = fp0.inv(1u64 << 20);
    for idx in 0..3 {
        let b = base_slot + 5 * idx;
        let delta = gspec.deltas[idx] % p;
        // d0, d1, d1 + 2^19, d2, d2 + 3*2^18, d3, d3 + (2^20 - 16), v0, T_i:
        out.push(GarnerLookupColDesc {
            terms: vec![(b, 1)],
            const_offset: 0,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 1, 1)],
            const_offset: 0,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 1, 1)],
            const_offset: 1u64 << 19,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 2, 1)],
            const_offset: 0,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 2, 1)],
            const_offset: 3 * (1u64 << 18),
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 3, 1)],
            const_offset: 0,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 3, 1)],
            const_offset: (1u64 << 20) - 16,
        });
        out.push(GarnerLookupColDesc {
            terms: vec![(b + 4, 1)],
            const_offset: 0,
        });
        // ci = (d0 + delta - v0) * inv2_20; T_i = pos_sum - d1 - d2 - d3 - ci
        let pos_sum = (((1u64 << 19) - 1) + ((1u64 << 18) - 1) + 15) % p;
        let const_ti = fp0.sub(pos_sum, fp0.mul(delta, inv2_20));
        out.push(GarnerLookupColDesc {
            terms: vec![
                (b, fp0.neg(inv2_20)),
                (b + 1, p - 1),
                (b + 2, p - 1),
                (b + 3, p - 1),
                (b + 4, inv2_20),
            ],
            const_offset: const_ti,
        });
    }
}

fn replay_logup_terminal_points_local(
    fp: &FastPrime61,
    proof: &LogUpGkrProof,
    ctx: &[u8; 32],
) -> std::result::Result<(Vec<Vec<u64>>, Vec<u64>), String> {
    let c = proof.config.num_challenges();
    let mut st: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_D1B_GKR|LOGUP_RANGE20");
        h.update(fp.p.to_le_bytes());
        h.update(ctx);
        h.finalize().into()
    };
    let absorb_u64s = |s: &mut [u8; 32], vals: &[u64]| {
        let mut h = Sha256::new();
        h.update(*s);
        for &v in vals {
            h.update(v.to_le_bytes());
        }
        *s = h.finalize().into();
    };
    let squeeze = |s: &mut [u8; 32], tag: u64| -> u64 {
        let mut h = Sha256::new();
        h.update(*s);
        h.update(b"CHAL");
        h.update(tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        *s = out;
        fp.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
    };
    let fork_sub = |s: &[u8; 32], label: &str, idx: u64| -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(s);
        h.update(b"SUB|");
        h.update(label.as_bytes());
        h.update(idx.to_le_bytes());
        h.finalize().into()
    };

    absorb_u64s(&mut st, &[proof.total_lookups as u64, c as u64]);
    {
        let mut h = Sha256::new();
        h.update(st);
        h.update(proof.mult_commitment);
        st = h.finalize().into();
    }
    for ell in 0..c {
        let _ = squeeze(&mut st, ell as u64);
    }

    let replay_one = |mut s: [u8; 32], tp: &FractionTreeProof| -> Vec<u64> {
        for r in &tp.roots {
            absorb_u64s(&mut s, r);
        }
        if tp.depth == 0 {
            return Vec::new();
        }
        for v in &tp.layer1_vals {
            absorb_u64s(&mut s, v);
        }
        let mut z_pt = vec![squeeze(&mut s, 1)];
        for (idx, layer) in tp.layers.iter().enumerate() {
            let k = idx + 1;
            for ell in 0..c {
                let _ = squeeze(&mut s, 100 + ell as u64);
            }
            for ell in 0..c {
                let _ = squeeze(&mut s, 200 + ell as u64);
            }
            let mut r_vars = Vec::with_capacity(k);
            for (round, poly) in layer.sumcheck_rounds.iter().enumerate() {
                absorb_u64s(&mut s, poly);
                r_vars.push(squeeze(&mut s, 1000 + round as u64));
            }
            for ce in &layer.child_evals {
                absorb_u64s(&mut s, ce);
            }
            let r_child = squeeze(&mut s, 2000 + k as u64);
            let mut zn = vec![r_child];
            zn.extend_from_slice(&r_vars);
            z_pt = zn;
        }
        absorb_u64s(&mut s, &[tp.leaf_payload_eval]);
        z_pt
    };

    let wit_zs: Vec<Vec<u64>> = proof
        .witness_trees
        .iter()
        .enumerate()
        .map(|(i, w)| replay_one(fork_sub(&st, "WIT_TREE", i as u64), w))
        .collect();
    let z_tab = replay_one(fork_sub(&st, "TAB_TREE", 0), &proof.table_tree);
    Ok((wit_zs, z_tab))
}

fn write_fraction_tree_c61(t: &FractionTreeProof, out: &mut Vec<u8>) {
    out.extend_from_slice(&(t.depth as u32).to_le_bytes());
    out.extend_from_slice(&(t.active_len as u64).to_le_bytes());
    out.push(t.roots.len() as u8);
    out.push(t.layer1_vals.len() as u8);
    out.push(t.layers.len() as u8);
    let mut flat = Vec::new();
    for r in &t.roots {
        flat.push(r[0]);
        flat.push(r[1]);
    }
    for v in &t.layer1_vals {
        flat.extend_from_slice(v);
    }
    for l in &t.layers {
        out.push(l.sumcheck_rounds.len() as u8);
        out.push(l.child_evals.len() as u8);
        for poly in &l.sumcheck_rounds {
            flat.extend_from_slice(poly);
        }
        for ce in &l.child_evals {
            flat.extend_from_slice(ce);
        }
    }
    flat.push(t.leaf_payload_eval);
    pack_u64_bits_le(&flat, 61, out);
}

fn read_fraction_tree_c61(
    cur: &mut ByteReader<'_>,
    p0: u64,
) -> std::result::Result<FractionTreeProof, String> {
    let depth = cur.read_u32()? as usize;
    let active_len = cur.read_u64()? as usize;
    let n_roots = cur.read_u8()? as usize;
    let n_l1 = cur.read_u8()? as usize;
    let n_layers = cur.read_u8()? as usize;
    if depth > 32 || n_roots > 8 || n_l1 > 8 || n_layers > 32 {
        return Err("FractionTreeProof header out of bounds".into());
    }
    let mut layer_dims = Vec::with_capacity(n_layers);
    let mut tot_u64 = n_roots * 2 + n_l1 * 4 + 1;
    for _ in 0..n_layers {
        let n_sc = cur.read_u8()? as usize;
        let n_ce = cur.read_u8()? as usize;
        if n_sc > 32 || n_ce > 8 {
            return Err("FractionTreeProof layer dims out of bounds".into());
        }
        layer_dims.push((n_sc, n_ce));
        tot_u64 += n_sc * 4 + n_ce * 4;
    }
    let flat = unpack_u64_bits_le(cur, 61, tot_u64, p0)?;
    if flat.len() != tot_u64 {
        return Err("FractionTreeProof length mismatch".into());
    }
    let mut i = 0usize;
    let mut roots = Vec::with_capacity(n_roots);
    for _ in 0..n_roots {
        roots.push([flat[i], flat[i + 1]]);
        i += 2;
    }
    let mut layer1_vals = Vec::with_capacity(n_l1);
    for _ in 0..n_l1 {
        layer1_vals.push([flat[i], flat[i + 1], flat[i + 2], flat[i + 3]]);
        i += 4;
    }
    let mut layers = Vec::with_capacity(n_layers);
    for (n_sc, n_ce) in layer_dims {
        let mut sumcheck_rounds = Vec::with_capacity(n_sc);
        for _ in 0..n_sc {
            sumcheck_rounds.push([flat[i], flat[i + 1], flat[i + 2], flat[i + 3]]);
            i += 4;
        }
        let mut child_evals = Vec::with_capacity(n_ce);
        for _ in 0..n_ce {
            child_evals.push([flat[i], flat[i + 1], flat[i + 2], flat[i + 3]]);
            i += 4;
        }
        layers.push(GkrLayerProof {
            sumcheck_rounds,
            child_evals,
        });
    }
    let leaf_payload_eval = flat[i];
    Ok(FractionTreeProof {
        depth,
        active_len,
        roots,
        layer1_vals,
        layers,
        leaf_payload_eval,
    })
}

impl ContinualWhirStateBundle {
    pub fn to_bytes(&self, p0: u64) -> Vec<u8> {
        let mut out = Vec::with_capacity(1 << 19);
        out.extend_from_slice(CONTINUAL_WHIR_MAGIC);
        out.extend_from_slice(&CONTINUAL_WHIR_VERSION.to_le_bytes());
        out.extend_from_slice(&(self.num_cts as u32).to_le_bytes());
        out.extend_from_slice(&(self.n as u32).to_le_bytes());
        out.push(self.mr);
        out.push(self.mc);
        out.extend_from_slice(&self.t_queries.to_le_bytes());
        out.push(self.blow);
        out.extend_from_slice(&self.state_commitment);
        out.extend_from_slice(&self.pcs_root);
        pack_u64_bits_le(&self.p0_poly_evals, 61, &mut out);
        let mut flat_sub = Vec::with_capacity(self.p12_poly_subsums.len() * 3);
        for s in &self.p12_poly_subsums {
            flat_sub.extend_from_slice(s);
        }
        pack_u64_bits_le(&flat_sub, 58, &mut out);

        out.extend_from_slice(&self.unmasked_slot0_sum.to_le_bytes());
        pack_ext3_slice(p0, &[self.gmask_sum, self.gmask_terminal_masked], &mut out);
        out.push(self.gmask_rounds.len() as u8);
        let mut flat_gm = Vec::new();
        for rd in &self.gmask_rounds {
            flat_gm.extend_from_slice(rd);
        }
        pack_ext3_slice(p0, &flat_gm, &mut out);

        match self.logup_proof.config {
            LogUpConfig::BatchedC3 { chunk_log2 } => {
                out.push(0);
                out.push(chunk_log2 as u8);
            }
            LogUpConfig::MonolithicC4 => {
                out.push(1);
                out.push(0);
            }
        }
        out.extend_from_slice(&(self.logup_proof.total_lookups as u64).to_le_bytes());
        out.extend_from_slice(&self.logup_proof.mult_commitment);
        out.extend_from_slice(&(self.logup_proof.witness_trees.len() as u32).to_le_bytes());
        for wt in &self.logup_proof.witness_trees {
            write_fraction_tree_c61(wt, &mut out);
        }
        write_fraction_tree_c61(&self.logup_proof.table_tree, &mut out);

        self.whir_opening.to_bytes(p0, &mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8], params: &HoistedParams) -> Result<Self> {
        let p0 = params.fp[0].p;
        let max_subsum = 15u64 * (params.n as u64) * (1u64 << 41) + 1;
        let mut cur = ByteReader::new(bytes);
        let err = |s: String| ContinualGdnError::InvalidWhirProof(s);
        if cur.take(8).map_err(err)? != CONTINUAL_WHIR_MAGIC {
            return Err(err("bad ContinualWhirStateBundle magic".into()));
        }
        if cur.read_u32().map_err(err)? != CONTINUAL_WHIR_VERSION {
            return Err(err("unsupported ContinualWhirStateBundle version".into()));
        }
        let num_cts = cur.read_u32().map_err(err)? as usize;
        let n = cur.read_u32().map_err(err)? as usize;
        let mr = cur.read_u8().map_err(err)?;
        let mc = cur.read_u8().map_err(err)?;
        let t_queries = cur.read_u16().map_err(err)?;
        let blow = cur.read_u8().map_err(err)?;
        let state_commitment = cur.read_hash().map_err(err)?;
        let pcs_root = cur.read_hash().map_err(err)?;
        if num_cts == 0 || num_cts > 256 || n != params.n {
            return Err(err("num_cts or ring N mismatch".into()));
        }

        let p0_poly_evals = unpack_u64_bits_le(&mut cur, 61, 512, p0).map_err(err)?;
        let flat_sub = unpack_u64_bits_le(&mut cur, 58, 4096, max_subsum).map_err(err)?;
        if flat_sub.len() % 3 != 0 {
            return Err(err("subsum length not divisible by 3".into()));
        }
        let p12_poly_subsums: Vec<[u64; 3]> = flat_sub
            .chunks_exact(3)
            .map(|c| [c[0], c[1], c[2]])
            .collect();

        let unmasked_slot0_sum = cur.read_u64().map_err(err)?;
        if unmasked_slot0_sum >= p0 {
            return Err(err("non-canonical unmasked_slot0_sum".into()));
        }
        let hdr_ext = unpack_ext3_slice(&mut cur, 2, p0).map_err(err)?;
        if hdr_ext.len() != 2 {
            return Err(err("header Ext3 pair mismatch".into()));
        }
        let n_gm_rds = cur.read_u8().map_err(err)? as usize;
        let log_n = n.trailing_zeros() as usize;
        if n_gm_rds != log_n {
            return Err(err("gmask_rounds count != log2(N)".into()));
        }
        let gm_flat = unpack_ext3_slice(&mut cur, n_gm_rds * 3, p0).map_err(err)?;
        if gm_flat.len() != n_gm_rds * 3 {
            return Err(err("gmask_rounds Ext3 count mismatch".into()));
        }
        let gmask_rounds: Vec<Vec<Ext3>> = gm_flat.chunks_exact(3).map(|c| c.to_vec()).collect();

        let cfg_tag = cur.read_u8().map_err(err)?;
        let cfg_arg = cur.read_u8().map_err(err)?;
        let lu_cfg = match cfg_tag {
            0 => LogUpConfig::BatchedC3 {
                chunk_log2: cfg_arg as usize,
            },
            1 if cfg_arg == 0 => LogUpConfig::MonolithicC4,
            _ => return Err(err("unknown LogUpConfig tag".into())),
        };
        let total_lookups = cur.read_u64().map_err(err)? as usize;
        let mult_commitment = cur.read_hash().map_err(err)?;
        let n_wt = cur.read_u32().map_err(err)? as usize;
        if n_wt == 0 || n_wt > 1024 {
            return Err(err("witness_trees count out of bounds".into()));
        }
        let mut witness_trees = Vec::with_capacity(n_wt);
        for _ in 0..n_wt {
            witness_trees.push(read_fraction_tree_c61(&mut cur, p0).map_err(err)?);
        }
        let table_tree = read_fraction_tree_c61(&mut cur, p0).map_err(err)?;
        let whir_opening = WhirOpeningBundle61::from_bytes(&mut cur, p0).map_err(err)?;
        if !cur.is_eof() {
            return Err(err("trailing bytes after ContinualWhirStateBundle".into()));
        }

        Ok(ContinualWhirStateBundle {
            num_cts,
            n,
            mr,
            mc,
            t_queries,
            blow,
            state_commitment,
            pcs_root,
            p0_poly_evals,
            p12_poly_subsums,
            unmasked_slot0_sum,
            gmask_sum: hdr_ext[0],
            gmask_rounds,
            gmask_terminal_masked: hdr_ext[1],
            logup_proof: LogUpGkrProof {
                config: lu_cfg,
                total_lookups,
                mult_commitment,
                witness_trees,
                table_tree,
            },
            whir_opening,
        })
    }
}

fn derive_state_whir_fs_points(
    params: &HoistedParams,
    state_com: &[u8; 32],
    pcs_root: &[u8; 32],
) -> ([u8; 32], [u64; 3]) {
    let mut hc = Sha256::new();
    hc.update(b"DARKVFHE_B61_STATE_WHIR_CTX_V1|");
    hc.update(state_com);
    hc.update(pcs_root);
    let ctx: [u8; 32] = hc.finalize().into();

    let pts = std::array::from_fn(|k| {
        let qk = params.qp[k];
        let mut h = Sha256::new();
        h.update(b"STATE_WHIR_PT|");
        h.update(ctx);
        h.update(qk.to_le_bytes());
        let d: [u8; 32] = h.finalize().into();
        (u128::from_le_bytes(d[0..16].try_into().unwrap()) % (qk as u128)) as u64
    });
    (ctx, pts)
}

type StateGarnerVFamilies = (Vec<Vec<u64>>, [usize; 15], [[[usize; 3]; 15]; 2]);
type SpdzWyChunkSolveResult = (
    Vec<Vec<Vec<SharedScalar>>>,
    Vec<Vec<Vec<SharedScalar>>>,
    Vec<SharedScalar>,
    Vec<Vec<Vec<SharedScalar>>>,
);

fn build_state_garner_v_families(params: &HoistedParams, r_qp: &[u64; 3]) -> StateGarnerVFamilies {
    let n = params.n;
    let fp0 = &params.fp[0];
    let gspec = ExactGarnerSpec::new(params);
    let mut v_fams = Vec::new();

    // Garner weights for u = r0 + q0 * r1 + (q0 * q1) * r2:
    // cols 0..4 -> r0 (1, 2^20, 2^39, 2^57, 0); cols 5..9 -> q0 * r1; cols 10..14 -> q0*q1 * r2!
    let limb_shifts: [u32; 5] = [0, 20, 39, 57, 0];
    let limb_active: [bool; 5] = [true, true, true, true, false];

    let mut p0_vf = [0usize; 15];
    let mut r0_pows = Vec::with_capacity(n);
    let mut cur0 = 1u64;
    for _ in 0..n {
        r0_pows.push(cur0);
        cur0 = fp0.mul(cur0, r_qp[0]);
    }
    // Note: mod q0, q0 == 0 and q0*q1 == 0! Still register v_fams cleanly for all 15 cols mod q_l:
    for (m, p0_slot) in p0_vf.iter_mut().enumerate() {
        let grp = m / 5;
        let sub = m % 5;
        let base_factor = if !limb_active[sub] {
            0u64
        } else if grp == 0 {
            fp0.pow(2, limb_shifts[sub] as u64)
        } else {
            0u64 // q0 mod q0 == 0!
        };
        let mut vec_m = vec![0u64; n];
        if base_factor != 0 {
            for j in 0..n {
                vec_m[j] = fp0.mul(base_factor, r0_pows[j]);
            }
        }
        *p0_slot = v_fams.len();
        v_fams.push(vec_m);
    }

    let mut p12_map = [[[0usize; 3]; 15]; 2];
    for li in 0..2 {
        let fpl = &params.fp[li + 1];
        let q0_m = gspec.qp[0] % fpl.p;
        let q01_m = fpl.mul(q0_m, gspec.qp[1] % fpl.p);
        let grp_mul = [1u64, q0_m, q01_m];

        let mut rl_pows = Vec::with_capacity(n);
        let mut c = 1u64;
        for _ in 0..n {
            rl_pows.push(c);
            c = fpl.mul(c, r_qp[li + 1]);
        }
        for (m, p12_slot) in p12_map[li].iter_mut().enumerate() {
            let grp = m / 5;
            let sub = m % 5;
            let w_m = if !limb_active[sub] {
                0u64
            } else {
                fpl.mul(grp_mul[grp], fpl.pow(2, limb_shifts[sub] as u64))
            };
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            if w_m != 0 {
                for j in 0..n {
                    let ch = split_21b_local(fpl.mul(w_m, rl_pows[j]));
                    b0[j] = ch[0];
                    b1[j] = ch[1];
                    b2[j] = ch[2];
                }
            }
            let base = v_fams.len();
            v_fams.push(b0);
            v_fams.push(b1);
            v_fams.push(b2);
            *p12_slot = [base, base + 1, base + 2];
        }
    }
    (v_fams, p0_vf, p12_map)
}

fn public_garner_digits(params: &HoistedParams, state_cts: &[Ct]) -> Vec<DigitCols> {
    let n = params.n;
    let gspec = ExactGarnerSpec::new(params);
    state_cts
        .par_iter()
        .flat_map_iter(|ct| {
            let mut u0 = Vec::with_capacity(n);
            let mut u1 = Vec::with_capacity(n);
            for j in 0..n {
                let (_, v0) =
                    lift_q_to_8limbs_and_u(params, ct.c0[j], ct.c0[n + j], ct.c0[2 * n + j]);
                let (_, v1) =
                    lift_q_to_8limbs_and_u(params, ct.c1[j], ct.c1[n + j], ct.c1[2 * n + j]);
                u0.push(v0);
                u1.push(v1);
            }
            [gspec.encode_u_exact(&u0), gspec.encode_u_exact(&u1)]
        })
        .collect()
}

// Each independent bilinear fingerprint ties all 15 committed digits of every polynomial to
// the public ciphertext. A nonzero difference matrix passes one uniform test with probability
// at most 2/p. The three tests use disjoint transcript labels after the commitment.
fn bind_public_digits(
    params: &HoistedParams,
    ctx: &[u8; 32],
    digits: &[DigitCols],
    families: &mut Vec<Vec<u64>>,
    claims: &mut Vec<SlotLinearClaim>,
) {
    let fp = params.fp[0];
    let mut domain = Sha256::new();
    domain.update(b"CONTINUAL_PUBLIC_DIGITS_V2");
    domain.update(ctx);
    let mut challenges = PcsRng::from_seed(domain.finalize().into());
    for rep in 0..3 {
        let mut row = vec![0; params.n];
        let mut weights = vec![0; digits.len() * 15];
        challenges.fill_fp_row(&fp, 2 * rep, &mut row);
        challenges.fill_fp_row(&fp, 2 * rep + 1, &mut weights);
        let rhs = weights
            .par_iter()
            .enumerate()
            .map(|(slot, &w)| {
                let column = &digits[slot / 15].cols[slot % 15];
                let dot = column
                    .iter()
                    .zip(&row)
                    .fold(0u128, |acc, (&d, &r)| acc + d as u128 * r as u128);
                fp.mul(w, fp.red128(dot))
            })
            .reduce(|| 0, |a, b| fp.add(a, b));
        claims.push(SlotLinearClaim::single_vec(
            families.len(),
            weights.into_iter().enumerate().collect(),
            rhs,
        ));
        families.push(row);
    }
}

/// Prove a unified `WhirPcs61 + GMask61 + D1b LogUp-GKR` (`TVD == 0`, `>= 122.0`-bit soundness)
/// commitment & opening over all `state_cts` (`32` `N = 8192` `B61` ciphertexts)!
pub fn prove_continual_whir_state_bundle(
    params: &HoistedParams,
    state_cts: &[Ct],
    state_handles: &[[u8; 32]],
) -> Result<ContinualWhirStateBundle> {
    let n = params.n;
    if state_cts.is_empty() || state_cts.len() > 256 || state_handles.len() != state_cts.len() {
        return Err(ContinualGdnError::InvalidGeometry(
            "invalid state bundle dimensions",
        ));
    }
    for (ct, expected) in state_cts.iter().zip(state_handles) {
        check_canonical_ct2(params, ct).map_err(ContinualGdnError::InvalidWhirProof)?;
        if ct2_handle(ct) != *expected {
            return Err(ContinualGdnError::InvalidWhirProof(
                "incorrect state handle".into(),
            ));
        }
    }
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];
    let ef = Ext3Field::new(fp0);
    let num_cts = state_cts.len();
    let num_polys = 2 * num_cts;
    let gspec = ExactGarnerSpec::new(params);
    let state_commitment = compute_state_handles_commitment(state_handles);

    let poly_garner = public_garner_digits(params, state_cts);
    let poly_slots = num_polys * 15;
    let mult_slots = TABLE_SIZE.div_ceil(n);
    let gm_specs = vec![GMaskSpec61::new("state_hvzk_sc", log_n, 2)];
    let mut gmask = GMask61::sample(ef, gm_specs.clone(), &mut PcsRng::from_seed([0; 32]));
    // Sample every base-field coordinate separately by rejection, avoiding modular-reduction bias.
    let mut entropy = std::io::BufReader::new(
        std::fs::File::open("/dev/urandom")
            .map_err(|e| ContinualGdnError::InvalidWhirProof(e.to_string()))?,
    );
    for coordinate in gmask.coeffs.iter_mut().flatten() {
        loop {
            let mut bytes = [0; 8];
            std::io::Read::read_exact(&mut entropy, &mut bytes)
                .map_err(|e| ContinualGdnError::InvalidWhirProof(e.to_string()))?;
            let sample = u64::from_le_bytes(bytes) & ((1 << 61) - 1);
            if sample < fp0.p {
                *coordinate = sample;
                break;
            }
        }
    }
    let gm_slots = gmask.num_slots(n);
    let off_mult = poly_slots;
    let off_gm = off_mult + mult_slots;
    let total_slots = off_gm + gm_slots;

    let mut flat = vec![0u64; total_slots * n];
    for (p_idx, dc) in poly_garner.iter().enumerate() {
        for m in 0..15 {
            let slot = p_idx * 15 + m;
            for j in 0..n {
                flat[slot * n + j] = dc.cols[m][j] as u64;
            }
        }
    }

    // 2. Build `D1b` LogUp-GKR lookup entries across all `num_polys * 27` `[0, 2^20)` columns:
    let mut descs = Vec::with_capacity(num_polys * 27);
    for p_idx in 0..num_polys {
        build_garner15_lookup_descs(&gspec, &fp0, p_idx * 15, &mut descs);
    }
    let lookup_entries: Vec<u64> = {
        let cols: Vec<Vec<u64>> = descs
            .par_iter()
            .map(|d| {
                let mut col = vec![d.const_offset; n];
                for &(slot, w) in &d.terms {
                    let src = &flat[slot * n..(slot + 1) * n];
                    for j in 0..n {
                        col[j] = fp0.add(col[j], fp0.mul(w, src[j]));
                    }
                }
                col
            })
            .collect();
        let mut all = Vec::with_capacity(descs.len() * n);
        for c in cols {
            all.extend_from_slice(&c);
        }
        all
    };
    let mults = count_multiplicities_parallel(&lookup_entries)
        .map_err(ContinualGdnError::InvalidWhirProof)?;
    for s in 0..mult_slots {
        let st = s * n;
        let end = ((s + 1) * n).min(TABLE_SIZE);
        let len = end - st;
        flat[(off_mult + s) * n..(off_mult + s) * n + len].copy_from_slice(&mults[st..end]);
    }
    gmask.write_to_slots(&mut flat[off_gm * n..], n);

    let shape = WhirShape61::for_len(&fp0, flat.len(), log_n, WHIR_T_QUERIES_128, WHIR_BLOWUP);
    let pcs = WhirCommittedPcs61::commit_with_shape(
        fp0,
        shape,
        &flat,
        PcsRng::from_seed(os_csprng_seed32()),
    );

    let (ctx, r_qp) = derive_state_whir_fs_points(params, &state_commitment, &pcs.root);

    let lu_cfg = LogUpConfig::MonolithicC4;
    let logup_proof = prove_logup_gkr_with_mults(&fp0, &lookup_entries, &mults, lu_cfg, &ctx);

    // 3. Prove `GMask61` HVZK (`TVD == 0`) blinded sumcheck over `slot 0`:
    let slot0 = &flat[0..n];
    let unmasked_slot0_sum = slot0.iter().fold(0u64, |a, &b| fp0.add(a, b));
    let mut tr_gm = PcsTranscript::new("CONTINUAL_STATE_GMASK61", fp0.p, &pcs.root, &ctx);
    let gmask_sum = gmask.hypercube_sum("state_hvzk_sc");
    tr_gm.absorb_ext3(&gmask_sum);
    let mut rho = tr_gm.squeeze_ext3(&ef, 900);
    if rho == [0, 0, 0] {
        rho = [1, 0, 0];
    }
    let mut cur_tbl: Vec<Ext3> = slot0.iter().map(|&v| [v, 0, 0]).collect();
    let mut r_chals = Vec::with_capacity(log_n);
    let mut gmask_rounds = Vec::with_capacity(log_n);
    for rd in 0..log_n {
        let half = cur_tbl.len() / 2;
        let mut s0 = ef.zero();
        let mut s1 = ef.zero();
        for u in 0..half {
            s0 = ef.add(s0, cur_tbl[2 * u]);
            s1 = ef.add(s1, ef.sub(cur_tbl[2 * u + 1], cur_tbl[2 * u]));
        }
        let blinded =
            gmask.blind_round_poly("state_hvzk_sc", rd, &r_chals, rho, &[s0, s1, ef.zero()]);
        for ck in &blinded {
            tr_gm.absorb_ext3(ck);
        }
        let r_i = tr_gm.squeeze_ext3(&ef, 901 + rd as u64);
        gmask_rounds.push(blinded);
        r_chals.push(r_i);
        cur_tbl = (0..half)
            .map(|u| {
                ef.add(
                    cur_tbl[2 * u],
                    ef.mul(r_i, ef.sub(cur_tbl[2 * u + 1], cur_tbl[2 * u])),
                )
            })
            .collect();
    }
    let f_at_r = cur_tbl[0];
    let g_at_r = gmask.eval_at("state_hvzk_sc", &r_chals);
    let gmask_terminal_masked = ef.add(f_at_r, ef.mul(rho, g_at_r));

    // 4. Assemble all `SlotLinearClaim`s: 3-prime `Qp` ciphertext consistency + LogUp leaf welds + `GMask61` HVZK weld!
    let (mut v_fams, p0_vf, p12_map) = build_state_garner_v_families(params, &r_qp);
    let mut claims = Vec::new();
    let mut p0_poly_evals = Vec::with_capacity(num_polys);
    let mut p12_poly_subsums = Vec::with_capacity(num_polys * 2);

    for p_idx in 0..num_polys {
        let base = p_idx * 15;
        let mut ev0 = 0u64;
        let mut terms0 = Vec::with_capacity(4);
        for m in 0..4 {
            let vfi = p0_vf[m];
            let dm = fp0.dot(&flat[(base + m) * n..(base + m + 1) * n], &v_fams[vfi]);
            ev0 = fp0.add(ev0, dm);
            terms0.push((vfi, vec![(base + m, 1u64)]));
        }
        p0_poly_evals.push(ev0);
        claims.push(SlotLinearClaim {
            terms: terms0,
            rhs: ev0,
        });

        for p12_li in &p12_map {
            let mut sub = [0u64; 3];
            for b in 0..3 {
                let mut acc = 0u64;
                let mut terms_b = Vec::new();
                for (m, p12_m) in p12_li.iter().enumerate() {
                    if m % 5 == 4 {
                        continue;
                    }
                    let vfi = p12_m[b];
                    acc += fp0.dot(&flat[(base + m) * n..(base + m + 1) * n], &v_fams[vfi]);
                    terms_b.push((vfi, vec![(base + m, 1u64)]));
                }
                sub[b] = acc;
                claims.push(SlotLinearClaim {
                    terms: terms_b,
                    rhs: acc,
                });
            }
            p12_poly_subsums.push(sub);
        }
    }

    // Discharge `D1b` LogUp-GKR leaf evaluations:
    let (wit_zs, z_tab) = replay_logup_terminal_points_local(&fp0, &logup_proof, &ctx)
        .map_err(ContinualGdnError::InvalidWhirProof)?;
    let cols_per_chunk = match lu_cfg {
        LogUpConfig::BatchedC3 { chunk_log2: cl } => (1usize << cl) / n,
        LogUpConfig::MonolithicC4 => descs.len(),
    };
    for (b_idx, w_prf) in logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_fams.len();
        v_fams.push(build_eq_le_local(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_local(&fp0, &zw[log_n..]);
        let start_col = b_idx * cols_per_chunk;
        let act_cols = w_prf.active_len / n;
        let mut const_acc = 0u64;
        let mut slot_map: BTreeMap<usize, u64> = BTreeMap::new();
        for s in 0..act_cols {
            let w_hi = eq_hi[s];
            let desc = &descs[start_col + s];
            const_acc = fp0.add(const_acc, fp0.mul(w_hi, desc.const_offset));
            for &(slot, c_val) in &desc.terms {
                let add_w = fp0.mul(w_hi, c_val);
                let e = slot_map.entry(slot).or_insert(0);
                *e = fp0.add(*e, add_w);
            }
        }
        claims.push(SlotLinearClaim::single_vec(
            v_idx,
            slot_map.into_iter().collect(),
            fp0.sub(w_prf.leaf_payload_eval, const_acc),
        ));
    }
    {
        let v_tab_idx = v_fams.len();
        v_fams.push(build_eq_le_local(&fp0, &z_tab[..log_n]));
        let eq_tab_hi = build_eq_le_local(&fp0, &z_tab[log_n..TABLE_LOG2]);
        let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
            .map(|s| {
                let w = eq_tab_hi.get(s).copied().unwrap_or(0);
                (off_mult + s, w)
            })
            .collect();
        claims.push(SlotLinearClaim::single_vec(
            v_tab_idx,
            tab_terms,
            logup_proof.table_tree.leaf_payload_eval,
        ));
    }

    // Discharge `GMask61` HVZK (`TVD == 0`) sumcheck weld on `slot 0`:
    let v_ones = v_fams.len();
    v_fams.push(vec![1u64; n]);
    claims.push(SlotLinearClaim::single_vec(
        v_ones,
        vec![(0, 1)],
        unmasked_slot0_sum,
    ));
    GMask61::append_hvzk_terminal_weld_for_spec(
        &ef,
        &gm_specs,
        "state_hvzk_sc",
        0,
        off_gm,
        n,
        gmask_sum,
        rho,
        &r_chals,
        gmask_terminal_masked,
        &mut v_fams,
        &mut claims,
    );

    bind_public_digits(params, &ctx, &poly_garner, &mut v_fams, &mut claims);
    let whir_opening = pcs.open_whir_slot_claims(log_n, &v_fams, &claims, &ctx);

    Ok(ContinualWhirStateBundle {
        num_cts,
        n,
        mr: pcs.shape.mr as u8,
        mc: pcs.shape.mc as u8,
        t_queries: pcs.shape.t_queries as u16,
        blow: pcs.shape.blow as u8,
        state_commitment,
        pcs_root: pcs.root,
        p0_poly_evals,
        p12_poly_subsums,
        unmasked_slot0_sum,
        gmask_sum,
        gmask_rounds,
        gmask_terminal_masked,
        logup_proof,
        whir_opening,
    })
}

/// Standalone Zero-Witness Verifier for serialized `ContinualWhirStateBundle` (`0` secret key access!):
/// Verifies full-RNS ciphertext handle binding, `>= 122.0`-bit `D1b` LogUp-GKR zero-slack `Exact-Garner-15`
/// range proofs, `GMask61` (`TVD == 0`) sumcheck rounds, `>= 128`-bit `WhirPcs61` opening, and 3-prime
/// `Qp` polynomial consistency!
pub fn verify_continual_whir_state_bytes(
    params: &HoistedParams,
    expected_handles: &[[u8; 32]],
    state_cts: &[Ct],
    proof_bytes: &[u8],
) -> Result<(f64, f64)> {
    let bundle = ContinualWhirStateBundle::from_bytes(proof_bytes, params)?;
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];
    let ef = Ext3Field::new(fp0);

    if state_cts.len() != expected_handles.len() || bundle.num_cts != state_cts.len() {
        return Err(ContinualGdnError::InvalidWhirProof(
            "state_cts count mismatch".into(),
        ));
    }
    for (idx, ct) in state_cts.iter().enumerate() {
        check_canonical_ct2(params, ct).map_err(ContinualGdnError::InvalidWhirProof)?;
        if ct2_handle(ct) != expected_handles[idx] {
            return Err(ContinualGdnError::InvalidWhirProof(format!(
                "state ciphertext handle mismatch at slice {idx}"
            )));
        }
    }
    let want_state_com = compute_state_handles_commitment(expected_handles);
    if bundle.state_commitment != want_state_com {
        return Err(ContinualGdnError::InvalidWhirProof(
            "state_commitment mismatch".into(),
        ));
    }

    if (bundle.t_queries as usize) < WHIR_T_QUERIES_128
        || !(bundle.blow as usize).is_power_of_two()
        || (bundle.blow as usize) < WHIR_BLOWUP
    {
        return Err(ContinualGdnError::InvalidWhirProof(
            "WHIR security parameters below 128-bit floor".into(),
        ));
    }

    let num_polys = 2 * bundle.num_cts;
    if bundle.p0_poly_evals.len() != num_polys || bundle.p12_poly_subsums.len() != num_polys * 2 {
        return Err(ContinualGdnError::InvalidWhirProof(
            "poly evaluation vector length mismatch".into(),
        ));
    }
    let max_subsum = 15u64 * (n as u64) * (1u64 << 41);
    if bundle
        .p12_poly_subsums
        .iter()
        .any(|s| s[0] > max_subsum || s[1] > max_subsum || s[2] > max_subsum)
    {
        return Err(ContinualGdnError::InvalidWhirProof(
            "21b subsum overflow".into(),
        ));
    }

    let (ctx, r_qp) =
        derive_state_whir_fs_points(params, &bundle.state_commitment, &bundle.pcs_root);

    if bundle.logup_proof.config != LogUpConfig::MonolithicC4 {
        return Err(ContinualGdnError::InvalidWhirProof(
            "expected four global lookup challenges".into(),
        ));
    }
    if bundle.logup_proof.total_lookups != num_polys * 27 * n {
        return Err(ContinualGdnError::InvalidWhirProof(
            "LogUp total_lookups mismatch".into(),
        ));
    }
    let lu = &bundle.logup_proof;
    let cap = match lu.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => lu.total_lookups.next_power_of_two(),
    };
    if lu.witness_trees.len() != lu.total_lookups.div_ceil(cap)
        || lu.witness_trees.iter().enumerate().any(|(i, tree)| {
            let active = (lu.total_lookups - i * cap).min(cap);
            tree.active_len != active
                || tree.depth != active.max(2).next_power_of_two().ilog2() as usize
        })
        || lu.table_tree.depth != TABLE_LOG2
        || lu.table_tree.active_len != TABLE_SIZE
    {
        return Err(ContinualGdnError::InvalidWhirProof(
            "incorrect lookup tree partition".into(),
        ));
    }
    verify_logup_gkr(&fp0, &bundle.logup_proof, &ctx, None)
        .map_err(ContinualGdnError::InvalidWhirProof)?;

    // 2. Verify `GMask61` (`TVD == 0`) sumcheck rounds:
    let mut tr_gm = PcsTranscript::new("CONTINUAL_STATE_GMASK61", fp0.p, &bundle.pcs_root, &ctx);
    let (rho_v, r_chals_v, term_v) = verify_gmask61_rounds(
        &ef,
        &mut tr_gm,
        [bundle.unmasked_slot0_sum, 0, 0],
        bundle.gmask_sum,
        &bundle.gmask_rounds,
        2,
        900,
    )
    .map_err(ContinualGdnError::InvalidWhirProof)?;
    if term_v != bundle.gmask_terminal_masked {
        return Err(ContinualGdnError::InvalidWhirProof(
            "GMask61 terminal_masked mismatch".into(),
        ));
    }

    // 3. Reconstruct `SlotLinearClaim`s and verify `WhirPcs61` opening:
    let gspec = ExactGarnerSpec::new(params);
    let poly_slots = num_polys * 15;
    let mult_slots = TABLE_SIZE.div_ceil(n);
    let gm_specs = vec![GMaskSpec61::new("state_hvzk_sc", log_n, 2)];
    let gm_dummy = GMask61::sample(ef, gm_specs.clone(), &mut PcsRng::from_seed([0u8; 32]));
    let off_mult = poly_slots;
    let off_gm = off_mult + mult_slots;
    let total_slots = off_gm + gm_dummy.num_slots(n);

    let shape = WhirShape61::for_len(
        &fp0,
        total_slots * n,
        log_n,
        WHIR_T_QUERIES_128,
        WHIR_BLOWUP,
    );
    if (
        bundle.mr as usize,
        bundle.mc as usize,
        bundle.t_queries as usize,
        bundle.blow as usize,
    ) != (shape.mr, shape.mc, shape.t_queries, shape.blow)
    {
        return Err(ContinualGdnError::InvalidWhirProof(
            "noncanonical opening geometry".into(),
        ));
    }
    let (bciks_b, dkt_b, _, _) = shape.soundness_bits();

    let (mut v_fams, p0_vf, p12_map) = build_state_garner_v_families(params, &r_qp);
    let mut claims = Vec::new();
    for p_idx in 0..num_polys {
        let base = p_idx * 15;
        let terms0: Vec<(usize, Vec<(usize, u64)>)> =
            (0..4).map(|m| (p0_vf[m], vec![(base + m, 1u64)])).collect();
        claims.push(SlotLinearClaim {
            terms: terms0,
            rhs: bundle.p0_poly_evals[p_idx],
        });
        for (li, p12_li) in p12_map.iter().enumerate() {
            let sub = bundle.p12_poly_subsums[2 * p_idx + li];
            for (b, &rhs_b) in sub.iter().enumerate() {
                let mut terms_b = Vec::new();
                for (m, p12_m) in p12_li.iter().enumerate() {
                    if m % 5 == 4 {
                        continue;
                    }
                    terms_b.push((p12_m[b], vec![(base + m, 1u64)]));
                }
                claims.push(SlotLinearClaim {
                    terms: terms_b,
                    rhs: rhs_b,
                });
            }
        }
    }

    let mut descs = Vec::with_capacity(num_polys * 27);
    for p_idx in 0..num_polys {
        build_garner15_lookup_descs(&gspec, &fp0, p_idx * 15, &mut descs);
    }
    let (wit_zs, z_tab) = replay_logup_terminal_points_local(&fp0, &bundle.logup_proof, &ctx)
        .map_err(ContinualGdnError::InvalidWhirProof)?;
    let cols_per_chunk = match bundle.logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2: cl } => (1usize << cl) / n,
        LogUpConfig::MonolithicC4 => descs.len(),
    };
    if wit_zs.len() != bundle.logup_proof.witness_trees.len() {
        return Err(ContinualGdnError::InvalidWhirProof(
            "LogUp witness_trees count mismatch".into(),
        ));
    }
    let mut covered_cols = 0usize;
    for (b_idx, w_prf) in bundle.logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        if w_prf.active_len % n != 0 {
            return Err(ContinualGdnError::InvalidWhirProof(
                "non-slot-aligned LogUp chunk".into(),
            ));
        }
        let act_cols = w_prf.active_len / n;
        let start_col = b_idx * cols_per_chunk;
        if start_col + act_cols > descs.len() || zw.len() < log_n {
            return Err(ContinualGdnError::InvalidWhirProof(
                "LogUp chunk exceeds descriptor table".into(),
            ));
        }
        covered_cols += act_cols;
        let v_idx = v_fams.len();
        v_fams.push(build_eq_le_local(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_local(&fp0, &zw[log_n..]);
        let mut const_acc = 0u64;
        let mut slot_map: BTreeMap<usize, u64> = BTreeMap::new();
        for s in 0..act_cols {
            let w_hi = *eq_hi
                .get(s)
                .ok_or_else(|| ContinualGdnError::InvalidWhirProof("eq_hi bounds".into()))?;
            let desc = &descs[start_col + s];
            const_acc = fp0.add(const_acc, fp0.mul(w_hi, desc.const_offset));
            for &(slot, c_val) in &desc.terms {
                let add_w = fp0.mul(w_hi, c_val);
                let e = slot_map.entry(slot).or_insert(0);
                *e = fp0.add(*e, add_w);
            }
        }
        claims.push(SlotLinearClaim::single_vec(
            v_idx,
            slot_map.into_iter().collect(),
            fp0.sub(w_prf.leaf_payload_eval, const_acc),
        ));
    }
    if covered_cols != descs.len() {
        return Err(ContinualGdnError::InvalidWhirProof(
            "LogUp chunks did not cover all Exact-Garner-15 descriptors".into(),
        ));
    }
    {
        let v_tab_idx = v_fams.len();
        v_fams.push(build_eq_le_local(&fp0, &z_tab[..log_n]));
        let eq_tab_hi = build_eq_le_local(&fp0, &z_tab[log_n..TABLE_LOG2]);
        let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
            .map(|s| (off_mult + s, eq_tab_hi.get(s).copied().unwrap_or(0)))
            .collect();
        claims.push(SlotLinearClaim::single_vec(
            v_tab_idx,
            tab_terms,
            bundle.logup_proof.table_tree.leaf_payload_eval,
        ));
    }

    let v_ones = v_fams.len();
    v_fams.push(vec![1u64; n]);
    claims.push(SlotLinearClaim::single_vec(
        v_ones,
        vec![(0, 1)],
        bundle.unmasked_slot0_sum,
    ));
    GMask61::append_hvzk_terminal_weld_for_spec(
        &ef,
        &gm_specs,
        "state_hvzk_sc",
        0,
        off_gm,
        n,
        bundle.gmask_sum,
        rho_v,
        &r_chals_v,
        bundle.gmask_terminal_masked,
        &mut v_fams,
        &mut claims,
    );

    bind_public_digits(
        params,
        &ctx,
        &public_garner_digits(params, state_cts),
        &mut v_fams,
        &mut claims,
    );
    verify_whir_pcs61(
        &fp0,
        &shape,
        &bundle.pcs_root,
        log_n,
        &v_fams,
        &claims,
        &ctx,
        &bundle.whir_opening,
    )
    .map_err(ContinualGdnError::InvalidWhirProof)?;

    // 4. Check 3-prime `Qp` polynomial evaluations `u(r_k) - floor(Q/2) * ones(r_k) == ct(r_k) (mod q_k)`:
    for (k_idx, &r) in r_qp.iter().enumerate() {
        let fpk = &params.fp[k_idx];
        let ones = fpk.ones_eval(n, r);
        let hq_shift = fpk.mul(params.half_q_mod_p[k_idx], ones);
        for (ct_i, st_ct) in state_cts.iter().enumerate().take(bundle.num_cts) {
            for comp in 0..2 {
                let p_idx = 2 * ct_i + comp;
                let u_ev = if k_idx == 0 {
                    bundle.p0_poly_evals[p_idx]
                } else {
                    combine_21b_mod_local(fpk, &bundle.p12_poly_subsums[2 * p_idx + (k_idx - 1)])
                };
                let lifted_ev = fpk.sub(u_ev, hq_shift);
                let ct_slice = if comp == 0 {
                    &st_ct.c0[k_idx * n..(k_idx + 1) * n]
                } else {
                    &st_ct.c1[k_idx * n..(k_idx + 1) * n]
                };
                let want_ev = fpk.eval_poly(ct_slice, r);
                if lifted_ev != want_ev {
                    return Err(ContinualGdnError::InvalidWhirProof(format!(
                        "state polynomial evaluation mismatch vs public Ct at slice {ct_i}, comp {comp}, q_{k_idx}"
                    )));
                }
            }
        }
    }

    // Root bound for the rational multiset equality with honest evaluations, excluding poles.
    // GKR checks and the opening protocol have their own soundness terms.
    let degree_bound = lu.total_lookups + TABLE_SIZE;
    let logup_b = 4.0 * ((fp0.p as f64) / degree_bound as f64).log2();
    if bciks_b.min(dkt_b).min(logup_b) < 122.0 {
        return Err(ContinualGdnError::InvalidWhirProof(
            "state opening profile below 122 bits".into(),
        ));
    }
    Ok((bciks_b.min(dkt_b), logup_b))
}

// ================================================================================================
// §5. Fast Noise-Flooded Batched 3-Custodian Crossing & Refresh (`C8` + `E ~ 2^111` + SPDZ MAC)
// ================================================================================================

/// Execute a noise-flooded (`|e_i| <= E ~ 2^111`) 3-custodian `E2S` crossing across `M` verified `Ct3`
/// ciphertexts:
/// - Enforces hard `C8` handle admission on all 3 custodians BEFORE touching any secret share;
/// - Runs full dealerless 3-party mask subtraction + smudged partial decryption + `PdSuccinctProof`
///   (`R_PD` 3-prime polynomial + `|e_i| <= E` smudge bound) verification across all 3 custodians!
fn batched_noise_flooded_e2s_ct3(
    quorum: &mut ContinualCustodyQuorum,
    handles: &[[u8; 32]],
    cts: &[Ct3],
    slot_lists: &[Vec<usize>],
    tag: &str,
) -> Result<Vec<Vec<SharedScalar>>> {
    let m_cnt = cts.len();
    assert_eq!(handles.len(), m_cnt);
    assert_eq!(slot_lists.len(), m_cnt);
    let params = quorum.cluster.params.clone();

    // Hard `C8` gate check on all 3 custodians BEFORE any secret-share operation!
    for idx in 0..m_cnt {
        check_canonical_ct3(&params, &cts[idx]).map_err(ContinualGdnError::InvalidCrossingProof)?;
        if ct3_handle(&cts[idx]) != handles[idx] {
            return Err(ContinualGdnError::InvalidCrossingProof(
                "C8 ABORT: Ct3 payload handle mismatch".into(),
            ));
        }
        for p in 0..NUM_CUSTODIANS {
            if !quorum.cluster.custodians[p].has_verified_handle(&handles[idx]) {
                return Err(ContinualGdnError::InvalidCrossingProof(format!(
                    "C8 ABORT (custodian {p}): refused crossing on unverified handle at `{tag}`"
                )));
            }
        }
    }

    let mut out_all = Vec::with_capacity(m_cnt);
    for idx in 0..m_cnt {
        let sub_tag = format!("{tag}_b{idx}");
        let sh = quorum
            .cluster
            .e2s_ct3(&handles[idx], &cts[idx], &slot_lists[idx], &sub_tag)
            .map_err(ContinualGdnError::InvalidCrossingProof)?;
        out_all.push(sh);
    }
    Ok(out_all)
}

// ================================================================================================
// §6. `DarkB61GdnResident`: Live `16 × 128 × 128` (`32` `B61` `Ct`s) Continual Memory & `W0` Unlearning
// ================================================================================================

/// Stored metadata for a committed continual episode `episode_id`, enabling both SPDZ-verified
/// orthogonal fast-subtract unlearning and general overlapping-key compressed WY chunk-operator replay.
pub struct EpisodeLedgerRecord {
    pub episode_id: usize,
    pub tau: usize,
    /// Pre-episode encrypted fast-weight checkpoint (`num_heads * slices_per_head` `Ct`s) & handles.
    pub pre_state_cts: Vec<Ct>,
    pub pre_state_handles: Vec<[u8; 32]>,
    pub pre_state_commitment: [u8; 32],
    /// Encrypted rank-`tau` episode delta sketch `Enc_{pk}(Delta_e)` (`32` `Ct`s) & handles.
    pub delta_sketch_cts: Vec<Ct>,
    pub delta_sketch_handles: Vec<[u8; 32]>,
    /// Secret-shared per-head chunk inputs `([gamma], [beta], [k], [v])` and pre-solved SPDZ
    /// division-free WY operators `[(I + L_c)^{-1}]` (`0` cleartext keys/values/gates stored on host!).
    pub spdz_chunk_inputs: Vec<Vec<SpdzHeadStepShares>>,
    pub spdz_inv_i_plus_l: Vec<Vec<Vec<SharedScalar>>>,
    pub spdz_chunk_gammas: Vec<SharedScalar>,
    pub spdz_u_rows: Vec<Vec<Vec<SharedScalar>>>,
    pub spdz_k_dec_rows: Vec<Vec<Vec<SharedScalar>>>,
    pub unlearned: bool,
    // A tombstoned chunk still applies its authenticated decay during subsequent replay.
    decay_only: bool,
}

#[derive(Clone)]
pub struct SpdzHeadStepShares {
    pub gamma: SharedScalar,
    pub beta: SharedScalar,
    pub k: Vec<SharedScalar>,
    pub v: Vec<SharedScalar>,
}

#[derive(Clone, Debug)]
pub struct ContinualAdaptMetrics {
    pub episode_id: usize,
    pub epoch_used: u64,
    pub tau: usize,
    pub read_prove_ms: f64,
    pub spdz_wy_cross_ms: f64,
    pub adapt_prove_ms: f64,
    pub cert_verify_ms: f64,
    pub whir_prove_ms: f64,
    pub whir_verify_ms: f64,
    pub whir_proof_bytes: usize,
    pub hoisted_whir_sample_bytes: usize,
    pub soundness_whir_bits: f64,
    pub soundness_logup_bits: f64,
    pub peak_rss_mib: f64,
}

#[derive(Clone, Debug)]
pub struct W0UnlearnMetrics {
    pub episode_id: usize,
    pub mode: &'static str,
    pub epochs_used: usize,
    pub unlearn_exec_and_prove_ms: f64,
    pub cert_verify_ms: f64,
    pub whir_prove_ms: f64,
    pub whir_verify_ms: f64,
    pub whir_proof_bytes: usize,
    pub soundness_whir_bits: f64,
    pub soundness_logup_bits: f64,
    pub peak_rss_mib: f64,
}

/// Real `B61` + 3-Custodian SPDZ × `Qwen3.5-0.8B` Gated-DeltaNet Fast-Weight Resident (`32` `N = 8192` `Ct`s).
pub struct DarkB61GdnResident {
    params: Arc<HoistedParams>,
    engine: Arc<HoistedEngine>,
    num_heads: usize,
    d_v: usize,
    d_k: usize,
    slice_rows: usize,
    slices_per_head: usize,
    /// Current live encrypted fast-weight state (`num_heads * slices_per_head` = `32` `B61` `Ct`s).
    state_cts: Vec<Ct>,
    state_handles: Vec<[u8; 32]>,
    state_commitment: [u8; 32],
    /// Precomputed 8-prime NTTs and `Exact-Garner-15` `SharedGridLifts` per head (`2 x 1` grid).
    state_head_pre: Vec<Vec<Vec<PrecomputedCt>>>,
    state_head_lifts: Vec<SharedGridLifts>,
    /// Tracks whether `state_cts` currently sits at depth `L = 1` (requiring refresh before next `ct x ct` at 61b `t`).
    state_at_depth1: bool,
    r_refresh_correctness: usize,
    policy_digest: [u8; 32],
    episodes: Vec<EpisodeLedgerRecord>,
}

impl DarkB61GdnResident {
    pub fn ciphertexts(&self) -> &[Ct] {
        &self.state_cts
    }
    pub fn handles(&self) -> &[[u8; 32]] {
        &self.state_handles
    }
    pub fn commitment(&self) -> [u8; 32] {
        self.state_commitment
    }
    pub fn slice_geometry(&self) -> (usize, usize) {
        (self.slice_rows, self.slices_per_head)
    }

    /// Initialize `DarkB61GdnResident` (default deployed geometry: `16 × 128 × 128` across `32` `N = 8192` `B61` `Ct`s).
    pub fn initialize(
        quorum: &mut ContinualCustodyQuorum,
        initial_heads: &[Vec<Vec<u64>>], // num_heads x d_v x d_k
    ) -> Result<(Self, ContinualWhirStateBundle, Vec<u8>)> {
        let params = quorum.cluster.params.clone();
        let engine = quorum.cluster.engine.clone();
        let n = params.n;
        let num_heads = initial_heads.len();
        if num_heads == 0 {
            return Err(ContinualGdnError::InvalidGeometry("num_heads == 0"));
        }
        let d_v = initial_heads[0].len();
        let d_k = initial_heads[0].first().map_or(0, Vec::len);
        if quorum
            .latches
            .iter()
            .any(|l| l.expected_head_commitment != [0; 32])
        {
            return Err(ContinualGdnError::SnapshotShadowBranchRejected);
        }
        if initial_heads
            .iter()
            .any(|head| head.len() != d_v || head.iter().any(|row| row.len() != d_k))
        {
            return Err(ContinualGdnError::InvalidGeometry("ragged initial state"));
        }
        if !d_v.is_power_of_two() || !d_k.is_power_of_two() || d_k >= n || !n.is_multiple_of(d_k) {
            return Err(ContinualGdnError::InvalidGeometry(
                "d_v/d_k must be powers of two with d_k < N and d_k | N",
            ));
        }
        let slice_rows = (n / d_k).min(d_v);
        if !d_v.is_multiple_of(slice_rows) || slice_rows * d_k > n {
            return Err(ContinualGdnError::InvalidGeometry(
                "d_v must be divisible by slice_rows and slice_rows * d_k <= N",
            ));
        }
        let slices_per_head = d_v / slice_rows;
        let total_cts = num_heads * slices_per_head;

        let smudge_bound = quorum.cluster.custodians[0].smudge_bound;
        let budget = derive_homomorphic_state_noise_budget(&params, smudge_bound, 2, 4);
        let r_refresh_correctness = budget.r_refresh_correctness.max(1);

        // Encrypt all `total_cts` (`32` at `16 x 128 x 128, N = 8192`) under the 3-custodian joint `pk` in parallel:
        let pub_key = quorum.cluster.pub_key.clone();
        let base_seed = os_csprng_seed32();
        let state_cts: Vec<Ct> = (0..total_cts)
            .into_par_iter()
            .map(|b| {
                let h = b / slices_per_head;
                let s = b % slices_per_head;
                let plain =
                    pack_fast_weight_slice(&initial_heads[h], s, slice_rows, d_k, n, params.t);
                let mut sh = Sha256::new();
                sh.update(b"GENESIS_SLICE_RNG|");
                sh.update(base_seed);
                sh.update((b as u32).to_le_bytes());
                let mut prng = PcsRng::from_seed(sh.finalize().into());
                pub_key.encrypt_pk(&plain, &mut prng)
            })
            .collect();

        let state_handles: Vec<[u8; 32]> = state_cts.par_iter().map(ct2_handle).collect();

        // Prove & standalone-verify genesis `WhirPcs61 + GMask61 + Exact-Garner-15` state bundle BEFORE admitting handles!
        let genesis_whir = prove_continual_whir_state_bundle(&params, &state_cts, &state_handles)?;
        let genesis_bytes = genesis_whir.to_bytes(params.fp[0].p);
        verify_continual_whir_state_bytes(&params, &state_handles, &state_cts, &genesis_bytes)?;

        for cust in &mut quorum.cluster.custodians {
            for &hd in &state_handles {
                cust.register_verified_input_handle(hd);
            }
        }
        let state_commitment = compute_state_handles_commitment(&state_handles);
        quorum.update_expected_head_all(state_commitment);

        let (state_head_pre, state_head_lifts) =
            Self::precompute_all_heads(&engine, &state_cts, num_heads, slices_per_head);

        let policy_digest = quorum.latches[0].pinned_policy_digest;
        Ok((
            DarkB61GdnResident {
                params,
                engine,
                num_heads,
                d_v,
                d_k,
                slice_rows,
                slices_per_head,
                state_cts,
                state_handles,
                state_commitment,
                state_head_pre,
                state_head_lifts,
                state_at_depth1: false,
                r_refresh_correctness,
                policy_digest,
                episodes: Vec::new(),
            },
            genesis_whir,
            genesis_bytes,
        ))
    }

    fn precompute_all_heads(
        engine: &HoistedEngine,
        cts: &[Ct],
        num_heads: usize,
        slices_per_head: usize,
    ) -> (Vec<Vec<Vec<PrecomputedCt>>>, Vec<SharedGridLifts>) {
        let pairs: Vec<(Vec<Vec<PrecomputedCt>>, SharedGridLifts)> = (0..num_heads)
            .into_par_iter()
            .map(|h| {
                let grid: Vec<Vec<Ct>> = (0..slices_per_head)
                    .map(|s| vec![cts[h * slices_per_head + s].clone()])
                    .collect();
                precompute_shared_grid(engine, &grid, LiftMode::ExactGarner15)
            })
            .collect();
        pairs.into_iter().unzip()
    }

    /// Fixture-side encoding of a plaintext chunk into authenticated shares for the three roles.
    pub fn share_chunk_to_custodians(
        &self,
        quorum: &mut ContinualCustodyQuorum,
        chunk: &GdnChunkPlain,
    ) -> Vec<Vec<SpdzHeadStepShares>> {
        assert_eq!(chunk.heads.len(), self.num_heads);
        let mut out = Vec::with_capacity(self.num_heads);
        for h in 0..self.num_heads {
            assert_eq!(chunk.heads[h].len(), chunk.tau);
            let mut h_steps = Vec::with_capacity(chunk.tau);
            for st in &chunk.heads[h] {
                h_steps.push(SpdzHeadStepShares {
                    gamma: quorum.cluster.share_authenticated(st.gamma),
                    beta: quorum.cluster.share_authenticated(st.beta),
                    k: quorum.cluster.share_vec(&st.k),
                    v: quorum.cluster.share_vec(&st.v),
                });
            }
            out.push(h_steps);
        }
        out
    }

    /// Refresh depth-1 `state_cts` (`~89`-bit noise at 61-bit `t`) back to fresh level-0 (`~14`-bit noise)
    /// via quorum-gated 3-custodian noise-flooded `E2S -> S2E` (`0` Beaver triples, exact mod `t`).
    pub fn refresh_depth1_state_if_needed(
        &mut self,
        quorum: &mut ContinualCustodyQuorum,
        signers: &[usize],
        chunk_id: usize,
    ) -> Result<()> {
        if !self.state_at_depth1 || self.r_refresh_correctness > 1 {
            return Ok(());
        }
        let n = self.params.n;
        let total_cts = self.state_cts.len();
        let active_slots: Vec<usize> = (0..self.slice_rows * self.d_k).collect();

        let epoch = quorum.next_epoch_counter;
        let auth = quorum.sign_epoch_authorization(
            epoch,
            ContinualActionTag::StateRefresh { chunk_id },
            self.policy_digest,
            self.state_commitment,
            self.state_commitment,
            signers,
        )?;
        quorum.verify_and_latch_all(&auth)?;

        let ct3s: Vec<Ct3> = self
            .state_cts
            .iter()
            .map(|ct| Ct3 {
                c0: ct.c0.clone(),
                c1: ct.c1.clone(),
                c2: vec![0u64; 3 * n],
            })
            .collect();
        let h3s: Vec<[u8; 32]> = ct3s.iter().map(ct3_handle).collect();
        for (idx, &h3) in h3s.iter().enumerate() {
            for cust in &mut quorum.cluster.custodians {
                if cust.has_verified_handle(&self.state_handles[idx]) {
                    cust.register_verified_input_handle(h3);
                }
            }
        }
        let slot_lists = vec![active_slots.clone(); total_cts];
        let shares_all = batched_noise_flooded_e2s_ct3(
            quorum,
            &h3s,
            &ct3s,
            &slot_lists,
            &format!("refresh_c{chunk_id}"),
        )?;

        let mut fresh_cts = Vec::with_capacity(total_cts);
        let mut fresh_hs = Vec::with_capacity(total_cts);
        for (b, sh_vec) in shares_all.into_iter().enumerate() {
            let pairs: Vec<(usize, SharedScalar)> =
                active_slots.iter().copied().zip(sh_vec).collect();
            let (ct_new, h_new) = quorum
                .cluster
                .s2e_encrypt_slots(&pairs, &format!("refresh_s2e_c{chunk_id}_b{b}"))
                .map_err(ContinualGdnError::InvalidSpdzMac)?;
            fresh_cts.push(ct_new);
            fresh_hs.push(h_new);
        }

        self.state_cts = fresh_cts;
        self.state_handles = fresh_hs;
        self.state_commitment = compute_state_handles_commitment(&self.state_handles);
        quorum.update_expected_head_all(self.state_commitment);
        let (pre, lifts) = Self::precompute_all_heads(
            &self.engine,
            &self.state_cts,
            self.num_heads,
            self.slices_per_head,
        );
        self.state_head_pre = pre;
        self.state_head_lifts = lifts;
        self.state_at_depth1 = false;
        Ok(())
    }

    /// Execute ONE full continual WY chunk adaptation across all `num_heads` (`16 × 128 × 128 = 32` `B61` `Ct`s):
    /// 1. `HoistedB61` reverse-key read + `Exact-Garner-15` `cert.rs` polynomial rescale certificate;
    /// 2. `t >= 2` Hybrid-PQ monotonic epoch verification + noise-flooded 3-custodian SPDZ crossing
    ///    solving division-free `(I + L)^{-1} (V - K_in S_0^T)` and secret gating scalars `Gamma_tau`;
    /// 3. Stride-128 `B61` `ct × ct` WY adaptation + `Exact-Garner-15` BEHZ rescale + `cert.rs` verification
    ///    + `WhirPcs61 + GMask61` (`TVD = 0`, `>= 122.0`-bit soundness) proof bundle!
    pub fn adapt_wy_chunk_spdz(
        &mut self,
        quorum: &mut ContinualCustodyQuorum,
        spdz_heads: Vec<Vec<SpdzHeadStepShares>>,
        signers: &[usize],
        emit_sample_hoisted_whir: bool,
    ) -> Result<(ContinualWhirStateBundle, Vec<u8>, ContinualAdaptMetrics)> {
        let tau = spdz_heads.first().map_or(0, Vec::len);
        if spdz_heads.len() != self.num_heads
            || tau == 0
            || spdz_heads.iter().any(|head| {
                head.len() != tau
                    || head
                        .iter()
                        .any(|step| step.k.len() != self.d_k || step.v.len() != self.d_v)
            })
        {
            return Err(ContinualGdnError::InvalidGeometry(
                "spdz_heads mismatch or tau == 0",
            ));
        }

        let episode_id = self.episodes.len();
        self.refresh_depth1_state_if_needed(quorum, signers, episode_id)?;

        // Snapshot pre-episode fresh state for exact `W0` rollback/replay:
        let pre_state_cts = self.state_cts.clone();
        let pre_state_handles = self.state_handles.clone();
        let pre_state_commitment = self.state_commitment;

        // Step 1: S2E-encrypt reverse-packed query keys `revK(k_{h, m})`:
        let t_spdz0 = Instant::now();
        let mut rev_k_cts = vec![Vec::with_capacity(tau); self.num_heads];
        let mut rev_k_hs = vec![Vec::with_capacity(tau); self.num_heads];
        for (h, head_steps) in spdz_heads.iter().enumerate() {
            for (m, step) in head_steps.iter().enumerate() {
                let slots: Vec<(usize, SharedScalar)> = (0..self.d_k)
                    .map(|c| ((self.d_k - 1) - c, step.k[c]))
                    .collect();
                let (ct_kr, h_kr) = quorum
                    .cluster
                    .s2e_encrypt_slots(&slots, &format!("ep{episode_id}_revk_h{h}_m{m}"))
                    .map_err(ContinualGdnError::InvalidSpdzMac)?;
                rev_k_cts[h].push(ct_kr);
                rev_k_hs[h].push(h_kr);
            }
        }
        let mut spdz_wy_cross_ms = t_spdz0.elapsed().as_secs_f64() * 1e3;

        // Step 2: Host `HoistedB61` Read `S_0 * k_{h, m}` + `Exact-Garner-15` `cert.rs` Certificate:
        let t_rprv = Instant::now();
        let head_grids: Vec<Vec<Vec<Ct>>> = (0..self.num_heads)
            .map(|h| {
                (0..self.slices_per_head)
                    .map(|s| vec![self.state_cts[h * self.slices_per_head + s].clone()])
                    .collect()
            })
            .collect();
        let head_h_grids: Vec<Vec<Vec<[u8; 32]>>> = (0..self.num_heads)
            .map(|h| {
                (0..self.slices_per_head)
                    .map(|s| vec![self.state_handles[h * self.slices_per_head + s]])
                    .collect()
            })
            .collect();

        let read_tasks: Vec<(usize, usize)> = (0..self.num_heads)
            .flat_map(|h| (0..tau).map(move |m| (h, m)))
            .collect();
        let read_proved: Vec<(Vec<Ct3>, HoistedWitness)> = read_tasks
            .par_iter()
            .map(|&(h, m)| {
                prove_hoisted_matvec(
                    &self.engine,
                    &head_grids[h],
                    std::slice::from_ref(&rev_k_cts[h][m]),
                    Some((&self.state_head_pre[h], &self.state_head_lifts[h])),
                    ProveOptions {
                        mode: LiftMode::ExactGarner15,
                        logup: None,
                        persistent_a: true,
                    },
                )
            })
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
        let read_prove_ms = t_rprv.elapsed().as_secs_f64() * 1e3;

        // Custodians verify all `cert.rs` `Exact-Garner-15` `d`-free polynomial rescale read certificates!
        let t_cvfy0 = Instant::now();
        let mut read_cert_hasher = Sha256::new();
        read_cert_hasher.update(b"DARKGDN_READ_CERTS_V1|");
        for &(h, m) in &read_tasks {
            let idx = h * tau + m;
            read_cert_hasher.update(read_proved[idx].1.witness_root);
        }
        let read_cert_digest: [u8; 32] = read_cert_hasher.finalize().into();

        read_tasks
            .par_iter()
            .enumerate()
            .try_for_each(|(idx, &(h, m))| -> std::result::Result<(), String> {
                let (ref out_cts, ref wit) = read_proved[idx];
                let hout: Vec<[u8; 32]> = out_cts.iter().map(ct3_handle).collect();
                verify_hoisted_matvec(
                    &self.params,
                    &head_h_grids[h],
                    std::slice::from_ref(&rev_k_hs[h][m]),
                    &hout,
                    &head_grids[h],
                    std::slice::from_ref(&rev_k_cts[h][m]),
                    out_cts,
                    wit,
                    Some(&self.state_head_lifts[h]),
                    VerifyOptions::default(),
                )
            })
            .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
        let mut cert_verify_ms = t_cvfy0.elapsed().as_secs_f64() * 1e3;

        // Authorize the verified state read before releasing any masked partial decryption.
        let epoch_used = quorum.next_epoch_counter;
        let auth = quorum.sign_epoch_authorization(
            epoch_used,
            ContinualActionTag::AdaptChunk {
                chunk_id: episode_id,
                tau,
            },
            self.policy_digest,
            self.state_commitment,
            read_cert_digest,
            signers,
        )?;
        quorum.verify_and_latch_all(&auth)?;

        // Admit verified read handles and run noise-flooded E2S crossing at wrap-free slots `r * d_k + (d_k - 1)`:
        let t_spdz1 = Instant::now();
        let readout_slots: Vec<usize> = (0..self.slice_rows)
            .map(|i| i * self.d_k + (self.d_k - 1))
            .collect();
        let mut flat_read_ct3s = Vec::with_capacity(read_proved.len() * self.slices_per_head);
        let mut flat_read_hs = Vec::with_capacity(read_proved.len() * self.slices_per_head);
        for (out_cts, _) in &read_proved {
            for ct3 in out_cts {
                let h3 = ct3_handle(ct3);
                for cust in &mut quorum.cluster.custodians {
                    cust.register_verified_input_handle(h3);
                }
                flat_read_hs.push(h3);
                flat_read_ct3s.push(ct3.clone());
            }
        }
        let read_slot_lists = vec![readout_slots; flat_read_ct3s.len()];
        let crossed_slices = batched_noise_flooded_e2s_ct3(
            quorum,
            &flat_read_hs,
            &flat_read_ct3s,
            &read_slot_lists,
            &format!("ep{episode_id}_read"),
        )?;

        // Step 4: 3-Custodian SPDZ Division-Free WY Solve (`(I + L)^{-1} (V - K_in S_0^T)`) & Gating Scalars!
        let (u_head_sh, k_dec_head_sh, gamma_chunk_sh, inv_l_all) = self.spdz_solve_wy_chunk(
            &mut quorum.cluster,
            &spdz_heads,
            &crossed_slices,
            episode_id,
        )?;

        // S2E-encrypt secret gating scalars `Gamma_tau^{(h)} X^0`, stride-128 `tilde_u`, and contiguous `tilde_k_dec`:
        let mut ct_gammas = Vec::with_capacity(self.num_heads);
        let mut h_gammas = Vec::with_capacity(self.num_heads);
        let mut ct_tilde_u = vec![Vec::with_capacity(tau); self.num_heads * self.slices_per_head];
        let mut h_tilde_u = vec![Vec::with_capacity(tau); self.num_heads * self.slices_per_head];
        let mut ct_tilde_k = vec![Vec::with_capacity(tau); self.num_heads];
        let mut h_tilde_k = vec![Vec::with_capacity(tau); self.num_heads];

        for h in 0..self.num_heads {
            let (ctg, hg) = quorum
                .cluster
                .s2e_encrypt_slots(
                    &[(0usize, gamma_chunk_sh[h])],
                    &format!("ep{episode_id}_gam_h{h}"),
                )
                .map_err(ContinualGdnError::InvalidSpdzMac)?;
            ct_gammas.push(ctg);
            h_gammas.push(hg);

            for m in 0..tau {
                let k_slots: Vec<(usize, SharedScalar)> =
                    (0..self.d_k).map(|j| (j, k_dec_head_sh[h][m][j])).collect();
                let (ctk, hk) = quorum
                    .cluster
                    .s2e_encrypt_slots(&k_slots, &format!("ep{episode_id}_tk_h{h}_m{m}"))
                    .map_err(ContinualGdnError::InvalidSpdzMac)?;
                ct_tilde_k[h].push(ctk);
                h_tilde_k[h].push(hk);

                for s in 0..self.slices_per_head {
                    let b = h * self.slices_per_head + s;
                    let u_slots: Vec<(usize, SharedScalar)> = (0..self.slice_rows)
                        .map(|i| (i * self.d_k, u_head_sh[h][m][s * self.slice_rows + i]))
                        .collect();
                    let (ctu, hu) = quorum
                        .cluster
                        .s2e_encrypt_slots(&u_slots, &format!("ep{episode_id}_tu_b{b}_m{m}"))
                        .map_err(ContinualGdnError::InvalidSpdzMac)?;
                    ct_tilde_u[b].push(ctu);
                    h_tilde_u[b].push(hu);
                }
            }
        }
        spdz_wy_cross_ms += t_spdz1.elapsed().as_secs_f64() * 1e3;

        // Step 5: Host Stride-128 `B61` `ct × ct` WY Adaptation + `Exact-Garner-15` BEHZ Rescale + `cert.rs`!
        let t_aprv = Instant::now();
        let rlk_ref = quorum.rlk.as_ref();

        // 5a. Certified decayed incoming state `Gamma_tau^{(h)} * S_0^{(h)}` (reusing persistent `state_head_pre`!):
        let decay_proved: Vec<(Vec<Ct3>, HoistedWitness, Vec<Ct>)> = (0..self.num_heads)
            .into_par_iter()
            .map(|h| {
                let (out_ct3, wit) = prove_hoisted_matvec(
                    &self.engine,
                    &head_grids[h],
                    std::slice::from_ref(&ct_gammas[h]),
                    Some((&self.state_head_pre[h], &self.state_head_lifts[h])),
                    ProveOptions {
                        mode: LiftMode::ExactGarner15,
                        logup: None,
                        persistent_a: true,
                    },
                )?;
                let relin: Vec<Ct> = out_ct3
                    .iter()
                    .map(|c3| self.engine.relinearize_ct3(c3, rlk_ref))
                    .collect();
                Ok((out_ct3, wit, relin))
            })
            .collect::<std::result::Result<Vec<_>, String>>()
            .map_err(ContinualGdnError::InvalidRescaleCertificate)?;

        // 5b. Certified stride-128 episode WY outer-product sketch `Delta_e = sum_{m=0}^{tau-1} tilde_u_m * tilde_k_m`:
        let delta_a_grids: Vec<Vec<Vec<Ct>>> = (0..self.num_heads)
            .map(|h| {
                (0..self.slices_per_head)
                    .map(|s| ct_tilde_u[h * self.slices_per_head + s].clone())
                    .collect()
            })
            .collect();
        let delta_ha_grids: Vec<Vec<Vec<[u8; 32]>>> = (0..self.num_heads)
            .map(|h| {
                (0..self.slices_per_head)
                    .map(|s| h_tilde_u[h * self.slices_per_head + s].clone())
                    .collect()
            })
            .collect();

        let delta_proved: Vec<(Vec<Ct3>, HoistedWitness, Vec<Ct>)> = (0..self.num_heads)
            .into_par_iter()
            .map(|h| {
                let (out_ct3, wit) = prove_hoisted_matvec(
                    &self.engine,
                    &delta_a_grids[h],
                    &ct_tilde_k[h],
                    None,
                    ProveOptions {
                        mode: LiftMode::ExactGarner15,
                        logup: None,
                        persistent_a: false,
                    },
                )?;
                let relin: Vec<Ct> = out_ct3
                    .iter()
                    .map(|c3| self.engine.relinearize_ct3(c3, rlk_ref))
                    .collect();
                Ok((out_ct3, wit, relin))
            })
            .collect::<std::result::Result<Vec<_>, String>>()
            .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
        let adapt_prove_ms = t_aprv.elapsed().as_secs_f64() * 1e3;

        // Custodians verify ALL `Exact-Garner-15` `d`-free polynomial rescale certificates AND relinearizations!
        let t_cvfy1 = Instant::now();
        (0..self.num_heads)
            .into_par_iter()
            .try_for_each(|h| -> std::result::Result<(), String> {
                let (ref d_ct3, ref d_wit, ref d_rel) = decay_proved[h];
                let hd_out: Vec<[u8; 32]> = d_ct3.iter().map(ct3_handle).collect();
                verify_hoisted_matvec(
                    &self.params,
                    &head_h_grids[h],
                    std::slice::from_ref(&h_gammas[h]),
                    &hd_out,
                    &head_grids[h],
                    std::slice::from_ref(&ct_gammas[h]),
                    d_ct3,
                    d_wit,
                    Some(&self.state_head_lifts[h]),
                    VerifyOptions::default(),
                )?;
                for s in 0..self.slices_per_head {
                    let want = self.engine.relinearize_ct3(&d_ct3[s], rlk_ref);
                    if want.c0 != d_rel[s].c0 || want.c1 != d_rel[s].c1 {
                        return Err("decay relinearize_ct3 mismatch".into());
                    }
                }

                let (ref u_ct3, ref u_wit, ref u_rel) = delta_proved[h];
                let hu_out: Vec<[u8; 32]> = u_ct3.iter().map(ct3_handle).collect();
                verify_hoisted_matvec(
                    &self.params,
                    &delta_ha_grids[h],
                    &h_tilde_k[h],
                    &hu_out,
                    &delta_a_grids[h],
                    &ct_tilde_k[h],
                    u_ct3,
                    u_wit,
                    None,
                    VerifyOptions::default(),
                )?;
                for s in 0..self.slices_per_head {
                    let want = self.engine.relinearize_ct3(&u_ct3[s], rlk_ref);
                    if want.c0 != u_rel[s].c0 || want.c1 != u_rel[s].c1 {
                        return Err("delta sketch relinearize_ct3 mismatch".into());
                    }
                }
                Ok(())
            })
            .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
        cert_verify_ms += t_cvfy1.elapsed().as_secs_f64() * 1e3;

        // Optional sample `HoistedWhirBundle` (`DVFHEWH1` from `whir_pcs.rs`) on Head 0 stride-128 `ct × ct`:
        let mut hoisted_whir_sample_bytes = 0usize;
        if emit_sample_hoisted_whir {
            let lu = LogUpConfig::MonolithicC4;
            let (w_outs, w_bun, _, _) = prove_hoisted_whir(
                &self.engine,
                &delta_a_grids[0],
                &ct_tilde_k[0],
                None,
                LiftMode::ExactGarner15,
                lu,
            )
            .map_err(ContinualGdnError::InvalidWhirProof)?;
            let w_bytes = w_bun.to_bytes();
            let hw_outs: Vec<[u8; 32]> = w_outs.iter().map(ct3_handle).collect();
            verify_hoisted_whir_bytes(
                &self.params,
                &delta_ha_grids[0],
                &h_tilde_k[0],
                &hw_outs,
                Some(&delta_a_grids[0]),
                None,
                &ct_tilde_k[0],
                &w_outs,
                &w_bytes,
            )
            .map_err(ContinualGdnError::InvalidWhirProof)?;
            hoisted_whir_sample_bytes = w_bytes.len();
        }

        // Combine `S_next = Gamma_tau * S_0 + Delta_e (mod Q)` across all `32` slices:
        let total_cts = self.num_heads * self.slices_per_head;
        let mut next_state_cts = Vec::with_capacity(total_cts);
        let mut next_state_hs = Vec::with_capacity(total_cts);
        let mut delta_sketch_cts = Vec::with_capacity(total_cts);
        let mut delta_sketch_hs = Vec::with_capacity(total_cts);

        for h in 0..self.num_heads {
            for s in 0..self.slices_per_head {
                let dc_ct = &decay_proved[h].2[s];
                let dl_ct = delta_proved[h].2[s].clone();
                let dl_h = ct2_handle(&dl_ct);
                let sum_ct = add_ct2_mod_q(&self.params, dc_ct, &dl_ct);
                let sum_h = ct2_handle(&sum_ct);
                for cust in &mut quorum.cluster.custodians {
                    cust.register_verified_input_handle(dl_h);
                    cust.register_verified_input_handle(sum_h);
                }
                delta_sketch_cts.push(dl_ct);
                delta_sketch_hs.push(dl_h);
                next_state_cts.push(sum_ct);
                next_state_hs.push(sum_h);
            }
        }

        // Step 6: Emit & standalone-verify full 32-ciphertext `WhirPcs61 + GMask61` (`TVD = 0`, `>= 122`-bit) state bundle!
        let t_wprv = Instant::now();
        let whir_bundle =
            prove_continual_whir_state_bundle(&self.params, &next_state_cts, &next_state_hs)?;
        let whir_bytes = whir_bundle.to_bytes(self.params.fp[0].p);
        let whir_prove_ms = t_wprv.elapsed().as_secs_f64() * 1e3;

        let t_wvfy = Instant::now();
        let (soundness_whir_bits, soundness_logup_bits) = verify_continual_whir_state_bytes(
            &self.params,
            &next_state_hs,
            &next_state_cts,
            &whir_bytes,
        )?;
        let whir_verify_ms = t_wvfy.elapsed().as_secs_f64() * 1e3;

        self.state_cts = next_state_cts;
        self.state_handles = next_state_hs;
        self.state_commitment = compute_state_handles_commitment(&self.state_handles);
        self.state_at_depth1 = true;
        quorum.update_expected_head_all(self.state_commitment);

        if self.r_refresh_correctness > 1 {
            let (pre, lifts) = Self::precompute_all_heads(
                &self.engine,
                &self.state_cts,
                self.num_heads,
                self.slices_per_head,
            );
            self.state_head_pre = pre;
            self.state_head_lifts = lifts;
        }

        quorum.record_checkpoint_all(episode_id, pre_state_commitment);
        self.episodes.push(EpisodeLedgerRecord {
            episode_id,
            tau,
            pre_state_cts,
            pre_state_handles,
            pre_state_commitment,
            delta_sketch_cts,
            delta_sketch_handles: delta_sketch_hs,
            spdz_chunk_inputs: spdz_heads,
            spdz_inv_i_plus_l: inv_l_all,
            spdz_chunk_gammas: gamma_chunk_sh,
            spdz_u_rows: u_head_sh,
            spdz_k_dec_rows: k_dec_head_sh,
            unlearned: false,
            decay_only: false,
        });

        let (_, peak_rss_mib) = process_memory_mib();
        Ok((
            whir_bundle,
            whir_bytes.clone(),
            ContinualAdaptMetrics {
                episode_id,
                epoch_used,
                tau,
                read_prove_ms,
                spdz_wy_cross_ms,
                adapt_prove_ms,
                cert_verify_ms,
                whir_prove_ms,
                whir_verify_ms,
                whir_proof_bytes: whir_bytes.len(),
                hoisted_whir_sample_bytes,
                soundness_whir_bits,
                soundness_logup_bits,
                peak_rss_mib,
            },
        ))
    }

    fn spdz_solve_wy_chunk(
        &self,
        cluster: &mut ThreeCustodianCluster,
        spdz_heads: &[Vec<SpdzHeadStepShares>],
        crossed_reads: &[Vec<SharedScalar>], // [h * tau + m) * slices_per_head + s][0..slice_rows]
        episode_id: usize,
    ) -> Result<SpdzWyChunkSolveResult> {
        let tau = spdz_heads[0].len();
        let one_sh = cluster.share_authenticated(1);
        let zero_sh = SharedScalar {
            parties: [PartyShare { val: 0, mac: 0 }; NUM_CUSTODIANS],
        };

        let mut u_all = Vec::with_capacity(self.num_heads);
        let mut k_dec_all = Vec::with_capacity(self.num_heads);
        let mut gamma_chunk_all = Vec::with_capacity(self.num_heads);
        let mut inv_l_all = Vec::with_capacity(self.num_heads);

        for (h, head_steps) in spdz_heads.iter().enumerate() {
            // Reassemble `[S_0^{(h)} k_{h, m}]` of length `d_v`:
            let mut s0_k: Vec<Vec<SharedScalar>> = Vec::with_capacity(tau);
            for m in 0..tau {
                let mut vec_dv = Vec::with_capacity(self.d_v);
                for s in 0..self.slices_per_head {
                    let flat_idx = (h * tau + m) * self.slices_per_head + s;
                    vec_dv.extend_from_slice(&crossed_reads[flat_idx]);
                }
                s0_k.push(vec_dv);
            }

            // Compute causal decay table `decay[a][b] = prod_{a <= r < b} [gamma_{h, r}]` in SPDZ:
            let mut decay = vec![vec![one_sh; tau + 1]; tau + 1];
            for (a, decay_row) in decay.iter_mut().enumerate() {
                for b in (a + 1)..=tau {
                    let prev = decay_row[b - 1];
                    let g = head_steps[b - 1].gamma;
                    decay_row[b] = cluster.spdz_mul_batch(&[prev], &[g])[0];
                }
            }
            gamma_chunk_all.push(decay[0][tau]);

            // Strictly lower triangular `[L_{i, j}] = [beta_i] * [decay[j+1][i]] * <[k_j], [k_i]>`:
            let mut l_sh = vec![vec![zero_sh; tau]; tau];
            for i in 0..tau {
                for j in 0..i {
                    let prods = cluster.spdz_mul_batch(&spdz_heads[h][j].k, &spdz_heads[h][i].k);
                    let mut dot = zero_sh;
                    for p in prods {
                        dot = cluster.spdz_add(dot, p);
                    }
                    let bg =
                        cluster.spdz_mul_batch(&[spdz_heads[h][i].beta], &[decay[j + 1][i]])[0];
                    l_sh[i][j] = cluster.spdz_mul_batch(&[bg], &[dot])[0];
                }
            }

            // Solve (I + L) N = I row by row. The diagonal of N is one.
            let mut inv_sh = vec![vec![zero_sh; tau]; tau];
            for i in 0..tau {
                inv_sh[i][i] = one_sh;
                for j in 0..i {
                    let col: Vec<_> = (j..i).map(|k| inv_sh[k][j]).collect();
                    let terms = cluster.spdz_mul_batch(&l_sh[i][j..i], &col);
                    inv_sh[i][j] = terms
                        .into_iter()
                        .fold(zero_sh, |acc, term| cluster.spdz_sub(acc, term));
                }
            }

            // Stateful RHS `[R_i] = [beta_i] * [v_i] - ([beta_i] * [decay[0][i]]) * [S_0 k_i]`:
            let mut rhs_mat = Vec::with_capacity(tau);
            for i in 0..tau {
                let bi_rep = vec![spdz_heads[h][i].beta; self.d_v];
                let bv = cluster.spdz_mul_batch(&bi_rep, &spdz_heads[h][i].v);
                let bi_g0i = cluster.spdz_mul_batch(&[spdz_heads[h][i].beta], &[decay[0][i]])[0];
                let bg_rep = vec![bi_g0i; self.d_v];
                let bsk = cluster.spdz_mul_batch(&bg_rep, &s0_k[i]);
                let row: Vec<SharedScalar> = bv
                    .into_iter()
                    .zip(bsk)
                    .map(|(a, b)| cluster.spdz_sub(a, b))
                    .collect();
                rhs_mat.push(row);
            }

            // `[U] = [(I + L)^{-1}] * [R]` (`tau x d_v`):
            let mut u_rows = vec![vec![zero_sh; self.d_v]; tau];
            for i in 0..tau {
                u_rows[i] = rhs_mat[i].clone(); // m == i has weight 1!
                for m in 0..i {
                    let w_rep = vec![inv_sh[i][m]; self.d_v];
                    let term = cluster.spdz_mul_batch(&w_rep, &rhs_mat[m]);
                    for r in 0..self.d_v {
                        u_rows[i][r] = cluster.spdz_add(u_rows[i][r], term[r]);
                    }
                }
            }

            // Tail-decayed keys `[k_{dec, m}] = [decay[m+1][tau]] * [k_m]`:
            let mut k_dec_rows = Vec::with_capacity(tau);
            for m in 0..tau {
                if m + 1 == tau {
                    k_dec_rows.push(spdz_heads[h][m].k.clone());
                } else {
                    let g_rep = vec![decay[m + 1][tau]; self.d_k];
                    k_dec_rows.push(cluster.spdz_mul_batch(&g_rep, &spdz_heads[h][m].k));
                }
            }

            u_all.push(u_rows);
            k_dec_all.push(k_dec_rows);
            inv_l_all.push(inv_sh);
        }

        cluster
            .spdz_mac_check(&format!("wy_solve_ep{episode_id}"))
            .map_err(ContinualGdnError::InvalidSpdzMac)?;
        Ok((u_all, k_dec_all, gamma_chunk_all, inv_l_all))
    }

    /// **Exact `W0` Subspace Unlearning Mode A — Orthogonal-Key Fast Decayed Sketch Subtraction**:
    /// 1. Custodians verify in SPDZ (`0` key leakage when `0`!) that EVERY active post-`episode_id`
    ///    episode `c > episode_id` satisfies `<k_{c, m'}, k_{e, m}> == 0 (mod t)` across all heads.
    ///    If ANY `K_t^T K_e != 0` cross-term is non-zero, deterministically aborts with
    ///    `ContinualGdnError::CrossTermNonOrthogonal` (mirroring Lean `#tooth` `naive_subtract_cross_term_tooth`!).
    /// 2. Multiplies secret post-episode decay gates `Gamma_post^{(h)} = prod_{c > e} Gamma_c^{(h)}` in SPDZ,
    ///    `S2E`-encrypts `Enc_{pk}(Gamma_post^{(h)} X^0)`, executes `HoistedB61` `Enc(Delta_e) * Enc(Gamma_post)`
    ///    + `Exact-Garner-15` BEHZ rescale + `cert.rs` verification + homomorphic `S_T - Gamma_post * Delta_e`,
    ///      and emits a fresh `WhirPcs61 + GMask61` (`TVD = 0`, `>= 122`-bit soundness) state proof!
    pub fn unlearn_w0_orthogonal_fast(
        &mut self,
        quorum: &mut ContinualCustodyQuorum,
        episode_id: usize,
        signers: &[usize],
    ) -> Result<(ContinualWhirStateBundle, Vec<u8>, W0UnlearnMetrics)> {
        if episode_id >= self.episodes.len() {
            return Err(ContinualGdnError::EpisodeNotFound(episode_id));
        }
        if self.episodes[episode_id].unlearned {
            return Err(ContinualGdnError::EpisodeAlreadyUnlearned(episode_id));
        }

        let t0 = Instant::now();
        // 2. Quorum-signed monotonic epoch gate for `W0UnlearnOrthogonal`:
        let epoch_used = quorum.next_epoch_counter;
        let auth = quorum.sign_epoch_authorization(
            epoch_used,
            ContinualActionTag::W0UnlearnOrthogonal { episode_id },
            self.policy_digest,
            self.state_commitment,
            compute_state_handles_commitment(&self.episodes[episode_id].delta_sketch_handles),
            signers,
        )?;
        quorum.verify_and_latch_all(&auth)?;

        let zero_sh = SharedScalar {
            parties: [PartyShare { val: 0, mac: 0 }; NUM_CUSTODIANS],
        };
        let one_sh = quorum.cluster.share_authenticated(1);

        // 1. SPDZ orthogonality verification across all live post-`episode_id` chunks:
        let mut dot_checks = Vec::new();
        let mut dot_meta = Vec::new();
        for c in (episode_id + 1)..self.episodes.len() {
            if self.episodes[c].unlearned {
                continue;
            }
            for h in 0..self.num_heads {
                for m_e in 0..self.episodes[episode_id].tau {
                    for m_c in 0..self.episodes[c].tau {
                        let prods = quorum.cluster.spdz_mul_batch(
                            &self.episodes[episode_id].spdz_chunk_inputs[h][m_e].k,
                            &self.episodes[c].spdz_chunk_inputs[h][m_c].k,
                        );
                        let mut d = zero_sh;
                        for p in prods {
                            d = quorum.cluster.spdz_add(d, p);
                        }
                        dot_checks.push(d);
                        dot_meta.push(c);
                    }
                }
            }
        }
        if !dot_checks.is_empty() {
            // Open only nonzero predicates. Raw cross-key inner products are private.
            // Fermat's identity applies because the SPDZ plaintext modulus is prime.
            let mut indicators = vec![one_sh; dot_checks.len()];
            for bit in (0..self.params.t.ilog2() + 1).rev() {
                indicators = quorum.cluster.spdz_mul_batch(&indicators, &indicators);
                if ((self.params.t - 1) >> bit) & 1 == 1 {
                    indicators = quorum.cluster.spdz_mul_batch(&indicators, &dot_checks);
                }
            }
            let opened = quorum
                .cluster
                .open_verified_output(&indicators, &format!("w0_orth_chk_ep{episode_id}"))
                .map_err(ContinualGdnError::InvalidSpdzMac)?;
            for (idx, &val) in opened.iter().enumerate() {
                if val != 0 {
                    return Err(ContinualGdnError::CrossTermNonOrthogonal {
                        episode_id,
                        post_chunk_id: dot_meta[idx],
                    });
                }
            }
        }

        // 3. Compute `[Gamma_post^{(h)}] = prod_{c > e, !unlearned} [Gamma_c^{(h)}]` in SPDZ:
        let has_post = self.episodes[episode_id + 1..]
            .iter()
            .any(|ep| !ep.unlearned || ep.decay_only);
        let total_cts = self.state_cts.len();
        let mut unlearned_cts = Vec::with_capacity(total_cts);
        let mut unlearned_hs = Vec::with_capacity(total_cts);
        let mut cert_verify_ms = 0.0;

        if !has_post {
            // Gamma_post == 1 identically: direct homomorphic subtraction `S_T - Delta_e (mod Q)`!
            for b in 0..total_cts {
                let sub_ct = sub_ct2_mod_q(
                    &self.params,
                    &self.state_cts[b],
                    &self.episodes[episode_id].delta_sketch_cts[b],
                );
                let sub_h = ct2_handle(&sub_ct);
                for cust in &mut quorum.cluster.custodians {
                    cust.register_verified_input_handle(sub_h);
                }
                unlearned_cts.push(sub_ct);
                unlearned_hs.push(sub_h);
            }
        } else {
            // Scale `[u'_m] = [Gamma_post^{(h)}] * [u_{e, m}]` in SPDZ -> `S2E` -> depth-1 `HoistedB61`
            // `(Gamma_post * tilde_u_m) * tilde_k_dec_m` (`~88`-bit noise << `Q/(2t) ~ 2^121`, zero `E2S`!):
            let tau_e = self.episodes[episode_id].tau;
            let mut ct_tu = vec![Vec::with_capacity(tau_e); total_cts];
            let mut h_tu = vec![Vec::with_capacity(tau_e); total_cts];
            let mut ct_tk = vec![Vec::with_capacity(tau_e); self.num_heads];
            let mut h_tk = vec![Vec::with_capacity(tau_e); self.num_heads];

            let mut u_scaled_all = Vec::with_capacity(self.num_heads);
            for h in 0..self.num_heads {
                let mut gp = one_sh;
                for c in (episode_id + 1)..self.episodes.len() {
                    if !self.episodes[c].unlearned || self.episodes[c].decay_only {
                        let g_c = self.episodes[c].spdz_chunk_gammas[h];
                        gp = quorum.cluster.spdz_mul_batch(&[gp], &[g_c])[0];
                    }
                }
                let gp_rep = vec![gp; self.d_v];
                let mut u_h = Vec::with_capacity(tau_e);
                for m in 0..tau_e {
                    u_h.push(
                        quorum
                            .cluster
                            .spdz_mul_batch(&gp_rep, &self.episodes[episode_id].spdz_u_rows[h][m]),
                    );
                }
                u_scaled_all.push(u_h);
            }
            quorum
                .cluster
                .spdz_mac_check(&format!("w0_orth_scale_ep{episode_id}"))
                .map_err(ContinualGdnError::InvalidSpdzMac)?;

            for (h, u_scaled_h) in u_scaled_all.iter().enumerate() {
                for (m, u_scaled_hm) in u_scaled_h.iter().enumerate() {
                    let k_slots: Vec<(usize, SharedScalar)> = (0..self.d_k)
                        .map(|j| (j, self.episodes[episode_id].spdz_k_dec_rows[h][m][j]))
                        .collect();
                    let (ctk, hk) = quorum
                        .cluster
                        .s2e_encrypt_slots(&k_slots, &format!("w0_orth_tk_{episode_id}_{h}_{m}"))
                        .map_err(ContinualGdnError::InvalidSpdzMac)?;
                    ct_tk[h].push(ctk);
                    h_tk[h].push(hk);
                    for s in 0..self.slices_per_head {
                        let b = h * self.slices_per_head + s;
                        let u_slots: Vec<(usize, SharedScalar)> = (0..self.slice_rows)
                            .map(|i| (i * self.d_k, u_scaled_hm[s * self.slice_rows + i]))
                            .collect();
                        let (ctu, hu) = quorum
                            .cluster
                            .s2e_encrypt_slots(
                                &u_slots,
                                &format!("w0_orth_tu_{episode_id}_{b}_{m}"),
                            )
                            .map_err(ContinualGdnError::InvalidSpdzMac)?;
                        ct_tu[b].push(ctu);
                        h_tu[b].push(hu);
                    }
                }
            }

            let rlk_ref = quorum.rlk.as_ref();
            let a_grids: Vec<Vec<Vec<Ct>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| ct_tu[h * self.slices_per_head + s].clone())
                        .collect()
                })
                .collect();
            let ha_grids: Vec<Vec<Vec<[u8; 32]>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| h_tu[h * self.slices_per_head + s].clone())
                        .collect()
                })
                .collect();

            let scaled_proved: Vec<(Vec<Ct3>, HoistedWitness, Vec<Ct>)> = (0..self.num_heads)
                .into_par_iter()
                .map(|h| {
                    let (out_ct3, wit) = prove_hoisted_matvec(
                        &self.engine,
                        &a_grids[h],
                        &ct_tk[h],
                        None,
                        ProveOptions {
                            mode: LiftMode::ExactGarner15,
                            logup: None,
                            persistent_a: false,
                        },
                    )?;
                    let relin: Vec<Ct> = out_ct3
                        .iter()
                        .map(|c3| self.engine.relinearize_ct3(c3, rlk_ref))
                        .collect();
                    Ok((out_ct3, wit, relin))
                })
                .collect::<std::result::Result<Vec<_>, String>>()
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;

            let t_cvfy = Instant::now();
            (0..self.num_heads)
                .into_par_iter()
                .try_for_each(|h| -> std::result::Result<(), String> {
                    let (ref out_ct3, ref wit, ref rel) = scaled_proved[h];
                    let hout: Vec<[u8; 32]> = out_ct3.iter().map(ct3_handle).collect();
                    verify_hoisted_matvec(
                        &self.params,
                        &ha_grids[h],
                        &h_tk[h],
                        &hout,
                        &a_grids[h],
                        &ct_tk[h],
                        out_ct3,
                        wit,
                        None,
                        VerifyOptions::default(),
                    )?;
                    for s in 0..self.slices_per_head {
                        let want = self.engine.relinearize_ct3(&out_ct3[s], rlk_ref);
                        if want.c0 != rel[s].c0 || want.c1 != rel[s].c1 {
                            return Err("orthogonal unlearn relinearize_ct3 mismatch".into());
                        }
                    }
                    Ok(())
                })
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
            cert_verify_ms = t_cvfy.elapsed().as_secs_f64() * 1e3;

            for (h, scaled_h) in scaled_proved.iter().enumerate() {
                for s in 0..self.slices_per_head {
                    let b = h * self.slices_per_head + s;
                    let sub_ct = sub_ct2_mod_q(&self.params, &self.state_cts[b], &scaled_h.2[s]);
                    let sub_h = ct2_handle(&sub_ct);
                    for cust in &mut quorum.cluster.custodians {
                        cust.register_verified_input_handle(sub_h);
                    }
                    unlearned_cts.push(sub_ct);
                    unlearned_hs.push(sub_h);
                }
            }
        }
        let unlearn_exec_and_prove_ms = t0.elapsed().as_secs_f64() * 1e3 - cert_verify_ms;

        let t_wprv = Instant::now();
        let whir_bundle =
            prove_continual_whir_state_bundle(&self.params, &unlearned_cts, &unlearned_hs)?;
        let whir_bytes = whir_bundle.to_bytes(self.params.fp[0].p);
        let whir_prove_ms = t_wprv.elapsed().as_secs_f64() * 1e3;

        let t_wvfy = Instant::now();
        let (soundness_whir_bits, soundness_logup_bits) = verify_continual_whir_state_bytes(
            &self.params,
            &unlearned_hs,
            &unlearned_cts,
            &whir_bytes,
        )?;
        let whir_verify_ms = t_wvfy.elapsed().as_secs_f64() * 1e3;

        self.state_cts = unlearned_cts;
        self.state_handles = unlearned_hs;
        self.state_commitment = compute_state_handles_commitment(&self.state_handles);
        self.state_at_depth1 = true;
        let episode = &mut self.episodes[episode_id];
        episode.unlearned = true;
        episode.decay_only = true;
        for step in episode.spdz_chunk_inputs.iter_mut().flatten() {
            step.beta = zero_sh;
            step.k.fill(zero_sh);
            step.v.fill(zero_sh);
        }
        quorum.update_expected_head_all(self.state_commitment);

        let (_, peak_rss_mib) = process_memory_mib();
        Ok((
            whir_bundle,
            whir_bytes.clone(),
            W0UnlearnMetrics {
                episode_id,
                mode: "orthogonal_fast_subtract",
                epochs_used: 1,
                unlearn_exec_and_prove_ms,
                cert_verify_ms,
                whir_prove_ms,
                whir_verify_ms,
                whir_proof_bytes: whir_bytes.len(),
                soundness_whir_bits,
                soundness_logup_bits,
                peak_rss_mib,
            },
        ))
    }

    /// **Exact `W0` Subspace Unlearning Mode B — Compressed WY Chunk-Operator Replay**:
    /// Handles **arbitrary overlapping keys** (`K_{t > e}^T K_e != 0`) AND arbitrary `gamma_e != 1`
    /// (`eraseIdx` literal omission semantics): rolls back to the pinned pre-episode checkpoint
    /// `pre_state_cts` of `episode_id` and replays all subsequent live chunks `c > episode_id` using
    /// their pre-solved SPDZ division-free WY operators `[(I + L_c)^{-1}]` (`0` re-inversion of `I + L_c`!),
    /// producing `S_unlearned == S_retrained_without_e` + a fresh `WhirPcs61 + GMask61` proof!
    pub fn unlearn_w0_wy_chunk_replay(
        &mut self,
        quorum: &mut ContinualCustodyQuorum,
        episode_id: usize,
        signers: &[usize],
    ) -> Result<(ContinualWhirStateBundle, Vec<u8>, W0UnlearnMetrics)> {
        let previous_heads = quorum
            .latches
            .each_ref()
            .map(|l| l.expected_head_commitment);
        let result = self.replay_from_checkpoint(quorum, episode_id, signers);
        if result.is_err() {
            for (latch, head) in quorum.latches.iter_mut().zip(previous_heads) {
                latch.expected_head_commitment = head;
            }
        }
        result
    }

    fn replay_from_checkpoint(
        &mut self,
        quorum: &mut ContinualCustodyQuorum,
        episode_id: usize,
        signers: &[usize],
    ) -> Result<(ContinualWhirStateBundle, Vec<u8>, W0UnlearnMetrics)> {
        if episode_id >= self.episodes.len() {
            return Err(ContinualGdnError::EpisodeNotFound(episode_id));
        }
        if self.episodes[episode_id].unlearned {
            return Err(ContinualGdnError::EpisodeAlreadyUnlearned(episode_id));
        }

        let t_start = Instant::now();
        let mut epochs_used = 0usize;
        let mut cert_verify_ms = 0.0;

        // Fast subtraction changes the live state without rewriting historical checkpoints.
        // Rewind to the first affected prefix and replay its decay as well as surviving writes.
        let checkpoint_id = self.episodes[..episode_id]
            .iter()
            .position(|ep| ep.decay_only)
            .unwrap_or(episode_id);
        let post_ids: Vec<_> = (checkpoint_id..self.episodes.len())
            .filter(|&c| {
                c != episode_id && (!self.episodes[c].unlearned || self.episodes[c].decay_only)
            })
            .collect();
        let checkpoint = &self.episodes[checkpoint_id];
        let mut cur_cts = checkpoint.pre_state_cts.clone();
        let mut cur_hs = checkpoint.pre_state_handles.clone();
        let mut cur_com = checkpoint.pre_state_commitment;
        let start_commitment = cur_com;
        let mut revised = Vec::new();
        let mut cur_depth1 = false;

        if post_ids.is_empty() {
            let ep_num = quorum.next_epoch_counter;
            let auth = quorum.sign_epoch_authorization(
                ep_num,
                ContinualActionTag::W0UnlearnWyReplay {
                    episode_id,
                    replay_idx: 0,
                    checkpoint_id,
                    checkpoint: start_commitment,
                },
                self.policy_digest,
                self.state_commitment,
                cur_com,
                signers,
            )?;
            quorum.verify_and_latch_all(&auth)?;

            epochs_used += 1;
            quorum.update_expected_head_all(cur_com);
        }

        let readout_slots: Vec<usize> = (0..self.slice_rows)
            .map(|i| i * self.d_k + (self.d_k - 1))
            .collect();
        let active_slots: Vec<usize> = (0..self.slice_rows * self.d_k).collect();

        for (replay_idx, &cid) in post_ids.iter().enumerate() {
            if cur_depth1 && self.r_refresh_correctness <= 1 {
                let n = self.params.n;
                let ep_ref = quorum.next_epoch_counter;
                let auth_ref = quorum.sign_epoch_authorization(
                    ep_ref,
                    ContinualActionTag::StateRefresh { chunk_id: cid },
                    self.policy_digest,
                    cur_com,
                    cur_com,
                    signers,
                )?;
                quorum.verify_and_latch_all(&auth_ref)?;

                epochs_used += 1;

                let ct3s: Vec<Ct3> = cur_cts
                    .iter()
                    .map(|ct| Ct3 {
                        c0: ct.c0.clone(),
                        c1: ct.c1.clone(),
                        c2: vec![0u64; 3 * n],
                    })
                    .collect();
                let h3s: Vec<[u8; 32]> = ct3s.iter().map(ct3_handle).collect();
                for (i, &h3) in h3s.iter().enumerate() {
                    for cust in &mut quorum.cluster.custodians {
                        if cust.has_verified_handle(&cur_hs[i]) {
                            cust.register_verified_input_handle(h3);
                        }
                    }
                }
                let sls = vec![active_slots.clone(); ct3s.len()];
                let sh_all = batched_noise_flooded_e2s_ct3(
                    quorum,
                    &h3s,
                    &ct3s,
                    &sls,
                    &format!("w0_rep_ref_{episode_id}_{cid}"),
                )?;
                let mut f_cts = Vec::with_capacity(cur_cts.len());
                let mut f_hs = Vec::with_capacity(cur_cts.len());
                for (b, sv) in sh_all.into_iter().enumerate() {
                    let pairs: Vec<(usize, SharedScalar)> =
                        active_slots.iter().copied().zip(sv).collect();
                    let (cn, hn) = quorum
                        .cluster
                        .s2e_encrypt_slots(&pairs, &format!("w0_rep_s2e_{episode_id}_{cid}_{b}"))
                        .map_err(ContinualGdnError::InvalidSpdzMac)?;
                    f_cts.push(cn);
                    f_hs.push(hn);
                }
                cur_cts = f_cts;
                cur_hs = f_hs;
                cur_com = compute_state_handles_commitment(&cur_hs);
                quorum.update_expected_head_all(cur_com);
            }

            // Record checkpoint for `cid` updated under the unlearned branch:
            let pre_c_cts = cur_cts.clone();
            let pre_c_hs = cur_hs.clone();
            let pre_c_com = cur_com;

            let tau_c = self.episodes[cid].tau;
            let spdz_in = self.episodes[cid].spdz_chunk_inputs.clone();
            let cached_inv_l = self.episodes[cid].spdz_inv_i_plus_l.clone();
            let cached_gammas = self.episodes[cid].spdz_chunk_gammas.clone();

            let (head_pre, head_lifts) = Self::precompute_all_heads(
                &self.engine,
                &cur_cts,
                self.num_heads,
                self.slices_per_head,
            );
            let head_grids: Vec<Vec<Vec<Ct>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| vec![cur_cts[h * self.slices_per_head + s].clone()])
                        .collect()
                })
                .collect();
            let head_h_grids: Vec<Vec<Vec<[u8; 32]>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| vec![cur_hs[h * self.slices_per_head + s]])
                        .collect()
                })
                .collect();

            let mut rev_k_cts = vec![Vec::with_capacity(tau_c); self.num_heads];
            let mut rev_k_hs = vec![Vec::with_capacity(tau_c); self.num_heads];
            for (h, spdz_h) in spdz_in.iter().enumerate() {
                for (m, step) in spdz_h.iter().enumerate() {
                    let slots: Vec<(usize, SharedScalar)> = (0..self.d_k)
                        .map(|c| ((self.d_k - 1) - c, step.k[c]))
                        .collect();
                    let (ct_kr, h_kr) = quorum
                        .cluster
                        .s2e_encrypt_slots(&slots, &format!("w0rep_{episode_id}_c{cid}_rk_{h}_{m}"))
                        .map_err(ContinualGdnError::InvalidSpdzMac)?;
                    rev_k_cts[h].push(ct_kr);
                    rev_k_hs[h].push(h_kr);
                }
            }

            let read_tasks: Vec<(usize, usize)> = (0..self.num_heads)
                .flat_map(|h| (0..tau_c).map(move |m| (h, m)))
                .collect();
            let read_proved: Vec<(Vec<Ct3>, HoistedWitness)> = read_tasks
                .par_iter()
                .map(|&(h, m)| {
                    prove_hoisted_matvec(
                        &self.engine,
                        &head_grids[h],
                        std::slice::from_ref(&rev_k_cts[h][m]),
                        Some((&head_pre[h], &head_lifts[h])),
                        ProveOptions {
                            mode: LiftMode::ExactGarner15,
                            logup: None,
                            persistent_a: true,
                        },
                    )
                })
                .collect::<std::result::Result<Vec<_>, _>>()
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;

            let t_cv0 = Instant::now();
            let mut rdig_h = Sha256::new();
            rdig_h.update(b"W0_REPLAY_READ|");
            for (_, w) in &read_proved {
                rdig_h.update(w.witness_root);
            }
            let rdig: [u8; 32] = rdig_h.finalize().into();

            read_tasks
                .par_iter()
                .enumerate()
                .try_for_each(|(idx, &(h, m))| -> std::result::Result<(), String> {
                    let (ref oc, ref wt) = read_proved[idx];
                    let ho: Vec<[u8; 32]> = oc.iter().map(ct3_handle).collect();
                    verify_hoisted_matvec(
                        &self.params,
                        &head_h_grids[h],
                        std::slice::from_ref(&rev_k_hs[h][m]),
                        &ho,
                        &head_grids[h],
                        std::slice::from_ref(&rev_k_cts[h][m]),
                        oc,
                        wt,
                        Some(&head_lifts[h]),
                        VerifyOptions::default(),
                    )
                })
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
            cert_verify_ms += t_cv0.elapsed().as_secs_f64() * 1e3;

            let ep_num = quorum.next_epoch_counter;
            let auth = quorum.sign_epoch_authorization(
                ep_num,
                ContinualActionTag::W0UnlearnWyReplay {
                    episode_id,
                    replay_idx,
                    checkpoint_id,
                    checkpoint: start_commitment,
                },
                self.policy_digest,
                if replay_idx == 0 {
                    self.state_commitment
                } else {
                    cur_com
                },
                rdig,
                signers,
            )?;
            quorum.verify_and_latch_all(&auth)?;

            epochs_used += 1;

            let mut flat_ct3s = Vec::with_capacity(read_proved.len() * self.slices_per_head);
            let mut flat_hs = Vec::with_capacity(read_proved.len() * self.slices_per_head);
            for (oc, _) in &read_proved {
                for c3 in oc {
                    let h3 = ct3_handle(c3);
                    for cust in &mut quorum.cluster.custodians {
                        cust.register_verified_input_handle(h3);
                    }
                    flat_hs.push(h3);
                    flat_ct3s.push(c3.clone());
                }
            }
            let sls = vec![readout_slots.clone(); flat_ct3s.len()];
            let crossed = batched_noise_flooded_e2s_ct3(
                quorum,
                &flat_hs,
                &flat_ct3s,
                &sls,
                &format!("w0rep_{episode_id}_c{cid}_e2s"),
            )?;

            // Reuse precomputed cached `[(I + L_c)^{-1}]` (`0` re-inversion!) to compute `[U']` in SPDZ:
            let one_sh = quorum.cluster.share_authenticated(1);
            let zero_sh = SharedScalar {
                parties: [PartyShare { val: 0, mac: 0 }; NUM_CUSTODIANS],
            };
            let mut ct_gammas = Vec::with_capacity(self.num_heads);
            let mut h_gammas = Vec::with_capacity(self.num_heads);
            let mut ct_tu = vec![Vec::with_capacity(tau_c); self.num_heads * self.slices_per_head];
            let mut h_tu = vec![Vec::with_capacity(tau_c); self.num_heads * self.slices_per_head];
            let mut ct_tk = vec![Vec::with_capacity(tau_c); self.num_heads];
            let mut h_tk = Vec::with_capacity(self.num_heads);

            let mut u_all = Vec::with_capacity(self.num_heads);
            let mut kdec_all = Vec::with_capacity(self.num_heads);
            for h in 0..self.num_heads {
                let mut s_k = Vec::with_capacity(tau_c);
                for m in 0..tau_c {
                    let mut v_dv = Vec::with_capacity(self.d_v);
                    for s in 0..self.slices_per_head {
                        v_dv.extend_from_slice(
                            &crossed[(h * tau_c + m) * self.slices_per_head + s],
                        );
                    }
                    s_k.push(v_dv);
                }
                let mut dec0 = vec![one_sh; tau_c + 1];
                for i in 1..=tau_c {
                    let prev = dec0[i - 1];
                    dec0[i] = quorum
                        .cluster
                        .spdz_mul_batch(&[prev], &[spdz_in[h][i - 1].gamma])[0];
                }
                let mut dec_tail = vec![one_sh; tau_c];
                for j in (0..(tau_c - 1)).rev() {
                    let nxt = dec_tail[j + 1];
                    dec_tail[j] = quorum
                        .cluster
                        .spdz_mul_batch(&[nxt], &[spdz_in[h][j + 1].gamma])[0];
                }

                let mut rhs_mat = Vec::with_capacity(tau_c);
                for i in 0..tau_c {
                    let bv = quorum
                        .cluster
                        .spdz_mul_batch(&vec![spdz_in[h][i].beta; self.d_v], &spdz_in[h][i].v);
                    let bg = quorum
                        .cluster
                        .spdz_mul_batch(&[spdz_in[h][i].beta], &[dec0[i]])[0];
                    let bsk = quorum.cluster.spdz_mul_batch(&vec![bg; self.d_v], &s_k[i]);
                    rhs_mat.push(
                        bv.into_iter()
                            .zip(bsk)
                            .map(|(a, b)| quorum.cluster.spdz_sub(a, b))
                            .collect::<Vec<_>>(),
                    );
                }
                let mut u_rows = vec![vec![zero_sh; self.d_v]; tau_c];
                for i in 0..tau_c {
                    u_rows[i] = rhs_mat[i].clone();
                    for m in 0..i {
                        let term = quorum
                            .cluster
                            .spdz_mul_batch(&vec![cached_inv_l[h][i][m]; self.d_v], &rhs_mat[m]);
                        for r in 0..self.d_v {
                            u_rows[i][r] = quorum.cluster.spdz_add(u_rows[i][r], term[r]);
                        }
                    }
                }
                let mut kd_rows = Vec::with_capacity(tau_c);
                for m in 0..tau_c {
                    if m + 1 == tau_c {
                        kd_rows.push(spdz_in[h][m].k.clone());
                    } else {
                        kd_rows.push(
                            quorum
                                .cluster
                                .spdz_mul_batch(&vec![dec_tail[m]; self.d_k], &spdz_in[h][m].k),
                        );
                    }
                }
                u_all.push(u_rows);
                kdec_all.push(kd_rows);
            }
            quorum
                .cluster
                .spdz_mac_check(&format!("w0rep_mac_{episode_id}_c{cid}"))
                .map_err(ContinualGdnError::InvalidSpdzMac)?;

            for h in 0..self.num_heads {
                let (ctg, hg) = quorum
                    .cluster
                    .s2e_encrypt_slots(
                        &[(0usize, cached_gammas[h])],
                        &format!("w0rep_g_{episode_id}_{cid}_{h}"),
                    )
                    .map_err(ContinualGdnError::InvalidSpdzMac)?;
                ct_gammas.push(ctg);
                h_gammas.push(hg);
                let mut h_tk_h = Vec::with_capacity(tau_c);
                for m in 0..tau_c {
                    let k_slots: Vec<(usize, SharedScalar)> =
                        (0..self.d_k).map(|j| (j, kdec_all[h][m][j])).collect();
                    let (ctk, hk) = quorum
                        .cluster
                        .s2e_encrypt_slots(
                            &k_slots,
                            &format!("w0rep_tk_{episode_id}_{cid}_{h}_{m}"),
                        )
                        .map_err(ContinualGdnError::InvalidSpdzMac)?;
                    ct_tk[h].push(ctk);
                    h_tk_h.push(hk);
                    for s in 0..self.slices_per_head {
                        let b = h * self.slices_per_head + s;
                        let u_slots: Vec<(usize, SharedScalar)> = (0..self.slice_rows)
                            .map(|i| (i * self.d_k, u_all[h][m][s * self.slice_rows + i]))
                            .collect();
                        let (ctu, hu) = quorum
                            .cluster
                            .s2e_encrypt_slots(
                                &u_slots,
                                &format!("w0rep_tu_{episode_id}_{cid}_{b}_{m}"),
                            )
                            .map_err(ContinualGdnError::InvalidSpdzMac)?;
                        ct_tu[b].push(ctu);
                        h_tu[b].push(hu);
                    }
                }
                h_tk.push(h_tk_h);
            }

            let rlk_ref = quorum.rlk.as_ref();
            let delta_a_grids: Vec<Vec<Vec<Ct>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| ct_tu[h * self.slices_per_head + s].clone())
                        .collect()
                })
                .collect();
            let delta_ha_grids: Vec<Vec<Vec<[u8; 32]>>> = (0..self.num_heads)
                .map(|h| {
                    (0..self.slices_per_head)
                        .map(|s| h_tu[h * self.slices_per_head + s].clone())
                        .collect()
                })
                .collect();

            let decay_proved: Vec<(Vec<Ct3>, HoistedWitness, Vec<Ct>)> = (0..self.num_heads)
                .into_par_iter()
                .map(|h| {
                    let (oc, wt) = prove_hoisted_matvec(
                        &self.engine,
                        &head_grids[h],
                        std::slice::from_ref(&ct_gammas[h]),
                        Some((&head_pre[h], &head_lifts[h])),
                        ProveOptions {
                            mode: LiftMode::ExactGarner15,
                            logup: None,
                            persistent_a: true,
                        },
                    )?;
                    let rel: Vec<Ct> = oc
                        .iter()
                        .map(|c3| self.engine.relinearize_ct3(c3, rlk_ref))
                        .collect();
                    Ok((oc, wt, rel))
                })
                .collect::<std::result::Result<Vec<_>, String>>()
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;

            let delta_proved: Vec<(Vec<Ct3>, HoistedWitness, Vec<Ct>)> = (0..self.num_heads)
                .into_par_iter()
                .map(|h| {
                    let (oc, wt) = prove_hoisted_matvec(
                        &self.engine,
                        &delta_a_grids[h],
                        &ct_tk[h],
                        None,
                        ProveOptions {
                            mode: LiftMode::ExactGarner15,
                            logup: None,
                            persistent_a: false,
                        },
                    )?;
                    let rel: Vec<Ct> = oc
                        .iter()
                        .map(|c3| self.engine.relinearize_ct3(c3, rlk_ref))
                        .collect();
                    Ok((oc, wt, rel))
                })
                .collect::<std::result::Result<Vec<_>, String>>()
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;

            let t_cv1 = Instant::now();
            (0..self.num_heads)
                .into_par_iter()
                .try_for_each(|h| -> std::result::Result<(), String> {
                    let (ref dc3, ref dw, _) = decay_proved[h];
                    let hd: Vec<[u8; 32]> = dc3.iter().map(ct3_handle).collect();
                    verify_hoisted_matvec(
                        &self.params,
                        &head_h_grids[h],
                        std::slice::from_ref(&h_gammas[h]),
                        &hd,
                        &head_grids[h],
                        std::slice::from_ref(&ct_gammas[h]),
                        dc3,
                        dw,
                        Some(&head_lifts[h]),
                        VerifyOptions::default(),
                    )?;
                    let (ref uc3, ref uw, _) = delta_proved[h];
                    let hu: Vec<[u8; 32]> = uc3.iter().map(ct3_handle).collect();
                    verify_hoisted_matvec(
                        &self.params,
                        &delta_ha_grids[h],
                        &h_tk[h],
                        &hu,
                        &delta_a_grids[h],
                        &ct_tk[h],
                        uc3,
                        uw,
                        None,
                        VerifyOptions::default(),
                    )
                })
                .map_err(ContinualGdnError::InvalidRescaleCertificate)?;
            cert_verify_ms += t_cv1.elapsed().as_secs_f64() * 1e3;

            let mut next_cts = Vec::with_capacity(cur_cts.len());
            let mut next_hs = Vec::with_capacity(cur_cts.len());
            let mut new_dl_cts = Vec::with_capacity(cur_cts.len());
            let mut new_dl_hs = Vec::with_capacity(cur_cts.len());
            for h in 0..self.num_heads {
                for s in 0..self.slices_per_head {
                    let dl = delta_proved[h].2[s].clone();
                    let dl_h = ct2_handle(&dl);
                    let sc = add_ct2_mod_q(&self.params, &decay_proved[h].2[s], &dl);
                    let sh = ct2_handle(&sc);
                    for cust in &mut quorum.cluster.custodians {
                        cust.register_verified_input_handle(dl_h);
                        cust.register_verified_input_handle(sh);
                    }
                    new_dl_cts.push(dl);
                    new_dl_hs.push(dl_h);
                    next_cts.push(sc);
                    next_hs.push(sh);
                }
            }

            revised.push((
                cid, pre_c_cts, pre_c_hs, pre_c_com, new_dl_cts, new_dl_hs, u_all, kdec_all,
            ));

            cur_cts = next_cts;
            cur_hs = next_hs;
            cur_com = compute_state_handles_commitment(&cur_hs);
            quorum.update_expected_head_all(cur_com);
            cur_depth1 = true;
        }

        let unlearn_exec_and_prove_ms = t_start.elapsed().as_secs_f64() * 1e3 - cert_verify_ms;

        let t_wprv = Instant::now();
        let whir_bundle = prove_continual_whir_state_bundle(&self.params, &cur_cts, &cur_hs)?;
        let whir_bytes = whir_bundle.to_bytes(self.params.fp[0].p);
        let whir_prove_ms = t_wprv.elapsed().as_secs_f64() * 1e3;

        let t_wvfy = Instant::now();
        let (soundness_whir_bits, soundness_logup_bits) =
            verify_continual_whir_state_bytes(&self.params, &cur_hs, &cur_cts, &whir_bytes)?;
        let whir_verify_ms = t_wvfy.elapsed().as_secs_f64() * 1e3;

        for (cid, cts, hs, com, delta, delta_hs, u, k) in revised {
            let ep = &mut self.episodes[cid];
            ep.pre_state_cts = cts;
            ep.pre_state_handles = hs;
            ep.pre_state_commitment = com;
            ep.delta_sketch_cts = delta;
            ep.delta_sketch_handles = delta_hs;
            ep.spdz_u_rows = u;
            ep.spdz_k_dec_rows = k;
            quorum.record_checkpoint_all(cid, com);
        }
        self.state_cts = cur_cts;
        self.state_handles = cur_hs;
        self.state_commitment = cur_com;
        self.state_at_depth1 = cur_depth1;
        self.episodes[episode_id].unlearned = true;
        if !cur_depth1 {
            let (pre, lifts) = Self::precompute_all_heads(
                &self.engine,
                &self.state_cts,
                self.num_heads,
                self.slices_per_head,
            );
            self.state_head_pre = pre;
            self.state_head_lifts = lifts;
        }

        let (_, peak_rss_mib) = process_memory_mib();
        Ok((
            whir_bundle,
            whir_bytes.clone(),
            W0UnlearnMetrics {
                episode_id,
                mode: "wy_chunk_operator_replay",
                epochs_used,
                unlearn_exec_and_prove_ms,
                cert_verify_ms,
                whir_prove_ms,
                whir_verify_ms,
                whir_proof_bytes: whir_bytes.len(),
                soundness_whir_bits,
                soundness_logup_bits,
                peak_rss_mib,
            },
        ))
    }

    /// Quorum-gated full fast-weight state decryption (`num_heads x d_v x d_k`) for conformance testing ONLY.
    pub fn open_verified_state_for_audit(
        &self,
        quorum: &mut ContinualCustodyQuorum,
        signers: &[usize],
    ) -> Result<Vec<Vec<Vec<u64>>>> {
        let n = self.params.n;
        let active_slots: Vec<usize> = (0..self.slice_rows * self.d_k).collect();
        let ep = quorum.next_epoch_counter;
        let auth = quorum.sign_epoch_authorization(
            ep,
            ContinualActionTag::AuditOpen,
            self.policy_digest,
            self.state_commitment,
            self.state_commitment,
            signers,
        )?;
        quorum.verify_and_latch_all(&auth)?;

        let ct3s: Vec<Ct3> = self
            .state_cts
            .iter()
            .map(|ct| Ct3 {
                c0: ct.c0.clone(),
                c1: ct.c1.clone(),
                c2: vec![0u64; 3 * n],
            })
            .collect();
        let h3s: Vec<[u8; 32]> = ct3s.iter().map(ct3_handle).collect();
        for (i, &h3) in h3s.iter().enumerate() {
            for cust in &mut quorum.cluster.custodians {
                if cust.has_verified_handle(&self.state_handles[i]) {
                    cust.register_verified_input_handle(h3);
                }
            }
        }
        let sls = vec![active_slots; ct3s.len()];
        let sh_all = batched_noise_flooded_e2s_ct3(quorum, &h3s, &ct3s, &sls, "audit_open_state")?;

        let mut heads = vec![vec![vec![0u64; self.d_k]; self.d_v]; self.num_heads];
        for (h, head_mat) in heads.iter_mut().enumerate() {
            for s in 0..self.slices_per_head {
                let b = h * self.slices_per_head + s;
                let vals = quorum
                    .cluster
                    .open_verified_output(&sh_all[b], &format!("audit_open_b{b}"))
                    .map_err(ContinualGdnError::InvalidSpdzMac)?;
                for i in 0..self.slice_rows {
                    for j in 0..self.d_k {
                        head_mat[s * self.slice_rows + i][j] = vals[i * self.d_k + j];
                    }
                }
            }
        }
        Ok(heads)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cleartext_wy_chunk_matches_sequential_mod_t() {
        let params = HoistedParams::for_ring(64);
        let fp_t = &params.fp_t;
        let d_v = 8usize;
        let d_k = 8usize;
        let s0: Vec<Vec<u64>> = (0..d_v)
            .map(|r| {
                (0..d_k)
                    .map(|c| ((r * 7 + c * 3 + 5) as u64) % fp_t.p)
                    .collect()
            })
            .collect();
        let chunk: Vec<GdnHeadStepPlain> = (0..4)
            .map(|m| GdnHeadStepPlain {
                gamma: (m as u64 + 2),
                beta: (m as u64 * 3 + 1),
                k: (0..d_k).map(|c| ((m * 5 + c + 1) as u64) % 19).collect(),
                v: (0..d_v)
                    .map(|r| ((m * 11 + r * 2 + 3) as u64) % 23)
                    .collect(),
            })
            .collect();
        let want = cleartext_fast_weight_seq(fp_t, &s0, &chunk);
        let (got, _, _, _) = cleartext_wy_chunk_head(fp_t, &s0, &chunk);
        assert_eq!(
            got, want,
            "stateful WY chunk update must match sequential fast-weight recurrence bit-for-bit"
        );
    }
}
