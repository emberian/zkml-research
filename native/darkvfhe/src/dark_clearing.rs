#![deny(warnings)]
//! `dark_clearing`: Quarried `breadstuffs/fhir` (`FHSDD001` & `FHQPB001`) Exact `O(|E|)` SDD-to-PSD +
//! Primal-Dual KKT Certificate Engine, Multilateral Netting Compressor/Verifier (`DBNET001`), and
//! Flagship Vertical #3 (`NoSingleViewer >= 2` `DarkBazaar` Encrypted Batch Call-Auction Clearing &
//! Private `{0, 1}` Voting Tally with `WhirPcs61` + `D1b` LogUp-GKR Proofs).
//!
//! ### Quarried Provenance & Security Properties
//! 1. **Exact `O(|E|)` SDD Factor & KKT Convex QP Certificates (`FHSDD001`, `FHQPB001`)**:
//!    - Quarried from `breadstuffs/fhir/src/qp_certificate.rs` and formalized in
//!      `minidregg/Theory/ExactKktClearingCert.lean` (`checkFhqpb001BundleInt_sound`):
//!      certifies `x^T Q x >= 0` (`PSD`) via `Q = sum_{e in E} w_e b_e b_e^T + diag(d)` (`w_e >= 0, d_i >= 0`)
//!      in `O(|E| + n)` checked `i128` arithmetic (`0` floats, `0` square roots), enforces the mandatory
//!      entry-for-entry `FHQPB001` Matrix Pin `sdd.admitted_q == q_mat` + canonical SHA-256 program digest,
//!      and verifies exact primal feasibility, dual non-negativity, KKT stationarity, and `p* - d* = comp_gap <= eps`.
//! 2. **Multilateral Netting Compression (`DBNET001`)**:
//!    - Compresses `M` gross bilateral trades across `P` counterparties into `<= P - 1` net settlement legs
//!      per asset (`0` legs on pure cycles) while certifying exact per-`(party, asset)` net balance conservation
//!      (`sum net_legs == sum gross_legs`, zero value creation) and gross liquidity exposure reduction.
//! 3. **`NoSingleViewer >= 2` Encrypted Call-Auction & Private `{0, 1}` Tally (`DBWHIR61`)**:
//!    - Bidders/voters submit `N = 8192` BFV ciphertexts (`Ct`) + zero-leakage `WhirPcs61` (`130.1b` `[BCIKS20]`
//!      UD, `GMask61` HVZK) + `D1b` `LogUpGkrProof` (`MonolithicC4`) proofs binding `(u, e0, e1, m)` across
//!      all three 61-bit RNS primes `Qp` via a wrap-free 38-bit carry split (`|Low_res| < p_0/2`, `|High_res| < p_0/2`).
//!    - Kills `starbridge-apps/privacy-voting/tests/tally_forgery.rs` (`m_0 = 10^6` and `m_0 = t - 1` rejected)
//!      and kills `dreggnet-market` `do_settle` individual `reveal_bid` cleartext leakage: homomorphic `ct + ct`
//!      sums curves/ballots inside BFV, and `NoSingleViewer >= 2` $t$-of-$n$ Shamir threshold decryption opens
//!      **only** the verified batch aggregate (`C8` handle gate + monotonic `epoch_latch` + nullifier replay guard).

use crate::logup_gkr::{
    count_multiplicities_parallel, prove_logup_gkr_with_mults, verify_logup_gkr, FractionTreeProof,
    GkrLayerProof, LogUpConfig, LogUpGkrProof, TABLE_LOG2, TABLE_SIZE,
};
use crate::succinct_pcs::{ByteReader, PcsRng, SlotLinearClaim};
use crate::whir_pcs::{
    pack_u64_bits_le, unpack_u64_bits_le, verify_whir_pcs61, WhirCommittedPcs61,
    WhirOpeningBundle61, WhirShape61, WHIR_BLOWUP, WHIR_T_QUERIES_128,
};
use crate::{FastPrime61, HoistedParams};
use darkstep::arith::{addmod, from_i64, invmod, mulmod, submod};
use darkstep::bfv::Ct;
use darkstep::ntt::Ntt;
use darkstep::rns::Rns;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::Arc;
use std::time::Instant;

pub const FHSDD_MAGIC: &[u8; 8] = b"FHSDD001";
pub const FHQPB_MAGIC: &[u8; 8] = b"FHQPB001";
pub const DBNET_MAGIC: &[u8; 8] = b"DBNET001";
pub const DBWHIR_MAGIC: &[u8; 8] = b"DBWHIR61";
pub const WIRE_VERSION_V1: u32 = 1;

const SPLIT_BITS: u32 = 38;
const SPLIT_MASK: u64 = (1u64 << SPLIT_BITS) - 1;
const W_CARRY_BIAS: i64 = 1i64 << 18; // 262,144; shifts [-2^18, 3*2^18) into [0, 2^20)

/// Structured fail-closed error taxonomy for `dark_clearing`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClearingError {
    InvalidWireFormat(String),
    ChecksumMismatch,
    ArithmeticOverflow,
    InvalidScaleDenom,
    DimensionMismatch(String),
    NegativeEdgeWeight {
        edge_idx: usize,
        weight: i64,
    },
    NegativeDiagSlack {
        idx: usize,
        slack: i64,
    },
    SddFactorMismatch {
        row: usize,
        col: usize,
        got: i128,
        expected: i128,
    },
    RowDominanceRejected {
        row: usize,
    },
    MatrixPinMismatch,
    ScalePinMismatch,
    ProgramDigestMismatch,
    PrimalEqualityViolation {
        row: usize,
        lhs: i128,
        rhs: i128,
    },
    PrimalInequalityViolation {
        row: usize,
        lhs: i128,
        rhs: i128,
    },
    PrimalBoxViolation {
        idx: usize,
        val: i64,
        lo: i64,
        hi: i64,
    },
    NegativeDualMultiplier {
        kind: &'static str,
        idx: usize,
        val: i64,
    },
    StationarityViolation {
        idx: usize,
        residual: i128,
    },
    OptimalityGapExceeded {
        gap_num: i128,
        eps_num: i128,
    },
    InvalidSettlementLeg {
        idx: usize,
    },
    GrossVolumeInflated {
        net_vol: u128,
        gross_vol: u128,
    },
    NetBalanceMismatch {
        party: u32,
        asset: u32,
        net: i128,
        gross: i128,
    },
    GlobalConservationViolation {
        asset: u32,
        sum: i128,
    },
    SolverFailure(String),
    ThresholdPolicyViolation(String),
    DuplicateNullifier([u8; 32]),
    InvalidSubmissionProof(String),
    C8UnverifiedHandle([u8; 32]),
    C8IndividualCiphertextForbidden([u8; 32]),
    EpochReplayOrStale {
        got: u64,
        latch: u64,
    },
    InsufficientDecryptionShares {
        got: usize,
        threshold: usize,
    },
}

impl std::fmt::Display for ClearingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for ClearingError {}

#[inline]
fn checked_add_i128(a: i128, b: i128) -> Result<i128, ClearingError> {
    a.checked_add(b).ok_or(ClearingError::ArithmeticOverflow)
}

#[inline]
fn checked_sub_i128(a: i128, b: i128) -> Result<i128, ClearingError> {
    a.checked_sub(b).ok_or(ClearingError::ArithmeticOverflow)
}

#[inline]
fn checked_mul_i128(a: i128, b: i128) -> Result<i128, ClearingError> {
    a.checked_mul(b).ok_or(ClearingError::ArithmeticOverflow)
}

fn dot_i64_checked(u: &[i64], v: &[i64]) -> Result<i128, ClearingError> {
    if u.len() != v.len() {
        return Err(ClearingError::DimensionMismatch(
            "dot_i64_checked len".into(),
        ));
    }
    let mut acc = 0i128;
    for (&x, &y) in u.iter().zip(v.iter()) {
        let prod = checked_mul_i128(x as i128, y as i128)?;
        acc = checked_add_i128(acc, prod)?;
    }
    Ok(acc)
}

// ================================================================================================
// §1. Quarried `FHSDD001` & `FHQPB001` Exact SDD Factor + Primal-Dual KKT Certificate Engine
// ================================================================================================

/// 2-sparse scaled-incidence SDD factor edge `b_e = alpha * e_u + beta * e_v` with integer weight `w_e >= 0`
/// (`Theory/ExactKktClearingCert.lean`: `SddEdgeInt`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SddFactorEdgeInt {
    pub u: u32,
    pub v: u32,
    pub alpha: i64,
    pub beta: i64,
    pub weight: i64,
}

/// Exact integer SDD factor decomposition witness certifying `Q = (sum_e w_e b_e b_e^T + diag(d)) / scale_denom`
/// is symmetric PSD in `O(|E| + n)` integer operations (`0` sqrts, `0` floats).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSddFactorCertificate {
    pub n: usize,
    pub scale_denom: i64,
    pub edges: Vec<SddFactorEdgeInt>,
    pub diag_slack: Vec<i64>,
    pub admitted_q: Vec<Vec<i64>>,
}

impl ExactSddFactorCertificate {
    /// Verify `w_e >= 0`, `d_i >= 0`, `scale_denom > 0`, and `sum_e w_e b_e b_e^T + diag(d) == admitted_q`
    /// in `O(|E| + n^2)` dense check (`O(|E| + n)` factor assembly).
    pub fn verify(&self) -> Result<(), ClearingError> {
        if self.scale_denom <= 0 {
            return Err(ClearingError::InvalidScaleDenom);
        }
        if self.diag_slack.len() != self.n || self.admitted_q.len() != self.n {
            return Err(ClearingError::DimensionMismatch(
                "SDD cert row count".into(),
            ));
        }
        for row in &self.admitted_q {
            if row.len() != self.n {
                return Err(ClearingError::DimensionMismatch(
                    "SDD cert col count".into(),
                ));
            }
        }
        let mut mat = vec![vec![0i128; self.n]; self.n];
        for (i, &d) in self.diag_slack.iter().enumerate() {
            if d < 0 {
                return Err(ClearingError::NegativeDiagSlack { idx: i, slack: d });
            }
            mat[i][i] = d as i128;
        }
        for (e_idx, e) in self.edges.iter().enumerate() {
            if e.weight < 0 {
                return Err(ClearingError::NegativeEdgeWeight {
                    edge_idx: e_idx,
                    weight: e.weight,
                });
            }
            let u = e.u as usize;
            let v = e.v as usize;
            if u >= self.n || v >= self.n {
                return Err(ClearingError::DimensionMismatch(
                    "SDD edge vertex out of range".into(),
                ));
            }
            let w = e.weight as i128;
            let a = e.alpha as i128;
            let b = e.beta as i128;
            if u == v {
                let s = checked_add_i128(a, b)?;
                let term = checked_mul_i128(w, checked_mul_i128(s, s)?)?;
                mat[u][u] = checked_add_i128(mat[u][u], term)?;
            } else {
                let uu = checked_mul_i128(w, checked_mul_i128(a, a)?)?;
                let vv = checked_mul_i128(w, checked_mul_i128(b, b)?)?;
                let uv = checked_mul_i128(w, checked_mul_i128(a, b)?)?;
                mat[u][u] = checked_add_i128(mat[u][u], uu)?;
                mat[v][v] = checked_add_i128(mat[v][v], vv)?;
                mat[u][v] = checked_add_i128(mat[u][v], uv)?;
                mat[v][u] = checked_add_i128(mat[v][u], uv)?;
            }
        }
        for (i, (mat_row, q_row)) in mat.iter().zip(&self.admitted_q).enumerate() {
            for (j, (&got, &q_val)) in mat_row.iter().zip(q_row).enumerate() {
                let want = q_val as i128;
                if got != want {
                    return Err(ClearingError::SddFactorMismatch {
                        row: i,
                        col: j,
                        got,
                        expected: want,
                    });
                }
            }
        }
        Ok(())
    }

    /// Evaluate `x^T (scale_denom * Q) x = sum_{e in E} w_e (alpha x_u + beta x_v)^2 + sum_i d_i x_i^2`
    /// in `O(|E| + n)` exact integer arithmetic (`sddFactor_quadForm_eq`).
    pub fn eval_scaled_quad_form(&self, x: &[i64]) -> Result<i128, ClearingError> {
        if x.len() != self.n {
            return Err(ClearingError::DimensionMismatch(
                "eval_scaled_quad_form x len".into(),
            ));
        }
        let mut acc = 0i128;
        for e in &self.edges {
            let u = e.u as usize;
            let v = e.v as usize;
            if u >= self.n || v >= self.n {
                return Err(ClearingError::DimensionMismatch(
                    "SDD edge out of range".into(),
                ));
            }
            let lin = checked_add_i128(
                checked_mul_i128(e.alpha as i128, x[u] as i128)?,
                checked_mul_i128(e.beta as i128, x[v] as i128)?,
            )?;
            let sq = checked_mul_i128(lin, lin)?;
            acc = checked_add_i128(acc, checked_mul_i128(e.weight as i128, sq)?)?;
        }
        for (i, &d) in self.diag_slack.iter().enumerate() {
            let sq = checked_mul_i128(x[i] as i128, x[i] as i128)?;
            acc = checked_add_i128(acc, checked_mul_i128(d as i128, sq)?)?;
        }
        Ok(acc)
    }
}

/// Quarried `FHSDD001` exact-integer symmetric row-diagonal-dominance checker
/// (`Theory/ExactKktClearingCert.lean`: `checkSddRowDomInt`).
pub fn verify_fhsdd001_row_dominant(
    scale_denom: i64,
    p_mat: &[Vec<i64>],
) -> Result<(), ClearingError> {
    if scale_denom <= 0 {
        return Err(ClearingError::InvalidScaleDenom);
    }
    let n = p_mat.len();
    for row in p_mat {
        if row.len() != n {
            return Err(ClearingError::DimensionMismatch(
                "FHSDD001 non-square".into(),
            ));
        }
    }
    for (i, row_i) in p_mat.iter().enumerate() {
        if row_i[i] < 0 {
            return Err(ClearingError::RowDominanceRejected { row: i });
        }
        let mut off_sum = 0i128;
        for (j, &p_ij) in row_i.iter().enumerate() {
            if p_ij != p_mat[j][i] {
                return Err(ClearingError::RowDominanceRejected { row: i });
            }
            if j != i {
                let abs_ij = (p_ij as i128)
                    .checked_abs()
                    .ok_or(ClearingError::ArithmeticOverflow)?;
                off_sum = checked_add_i128(off_sum, abs_ij)?;
            }
        }
        if off_sum > (row_i[i] as i128) {
            return Err(ClearingError::RowDominanceRejected { row: i });
        }
    }
    Ok(())
}

/// Canonical SHA-256 program digest over `(scale_denom, Q, q, A, b, G, h, l, u)`
/// (quarried from `breadstuffs/fhir/src/qp_certificate.rs::canonical_qp_program_digest`).
#[allow(clippy::too_many_arguments)]
pub fn canonical_qp_program_digest(
    scale_denom: i64,
    q_mat: &[Vec<i64>],
    q_vec: &[i64],
    a_mat: &[Vec<i64>],
    b_vec: &[i64],
    g_mat: &[Vec<i64>],
    h_vec: &[i64],
    l_vec: &[i64],
    u_vec: &[i64],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"FHQPB001_PROGRAM_V1|");
    h.update(scale_denom.to_le_bytes());
    h.update((q_vec.len() as u32).to_le_bytes());
    h.update((b_vec.len() as u32).to_le_bytes());
    h.update((h_vec.len() as u32).to_le_bytes());
    for row in q_mat {
        for &v in row {
            h.update(v.to_le_bytes());
        }
    }
    for &v in q_vec {
        h.update(v.to_le_bytes());
    }
    for row in a_mat {
        for &v in row {
            h.update(v.to_le_bytes());
        }
    }
    for &v in b_vec {
        h.update(v.to_le_bytes());
    }
    for row in g_mat {
        for &v in row {
            h.update(v.to_le_bytes());
        }
    }
    for &v in h_vec {
        h.update(v.to_le_bytes());
    }
    for &v in l_vec {
        h.update(v.to_le_bytes());
    }
    for &v in u_vec {
        h.update(v.to_le_bytes());
    }
    h.finalize().into()
}

/// Verified summary emitted by `ExactQpCertificateBundle::verify`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedKktSummary {
    pub n: usize,
    pub meq: usize,
    pub mineq: usize,
    pub sdd_edges: usize,
    pub scale_denom: i64,
    /// `2 * S^3 * p*` over exact `i128`.
    pub two_primal_scaled: i128,
    /// `2 * S^3 * d*` over exact `i128`.
    pub two_dual_scaled: i128,
    /// `S^3 * (p* - d*) == S^3 * compGap` over exact `i128`.
    pub comp_gap_scaled: i128,
    pub eps_scaled: i128,
}

/// Complete fixed-point integer `FHQPB001` certificate bundle (`Theory/ExactKktClearingCert.lean`: `Fhqpb001BundleInt`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactQpCertificateBundle {
    pub scale_denom: i64,
    pub sdd: ExactSddFactorCertificate,
    pub q_mat: Vec<Vec<i64>>,
    pub q_vec: Vec<i64>,
    pub a_mat: Vec<Vec<i64>>,
    pub b_vec: Vec<i64>,
    pub g_mat: Vec<Vec<i64>>,
    pub h_vec: Vec<i64>,
    pub l_vec: Vec<i64>,
    pub u_vec: Vec<i64>,
    pub x_vec: Vec<i64>,
    pub nu_vec: Vec<i64>,
    pub mu_vec: Vec<i64>,
    pub lam_l_vec: Vec<i64>,
    pub lam_u_vec: Vec<i64>,
    pub eps_int: i128,
    pub program_digest: [u8; 32],
}

impl ExactQpCertificateBundle {
    /// Division-free exact integer verifier matching `checkFhqpb001BundleInt` in `Theory/ExactKktClearingCert.lean`.
    pub fn verify(&self) -> Result<VerifiedKktSummary, ClearingError> {
        if self.scale_denom <= 0 {
            return Err(ClearingError::InvalidScaleDenom);
        }
        let n = self.q_vec.len();
        let meq = self.b_vec.len();
        let mineq = self.h_vec.len();
        if self.q_mat.len() != n
            || self.l_vec.len() != n
            || self.u_vec.len() != n
            || self.x_vec.len() != n
            || self.lam_l_vec.len() != n
            || self.lam_u_vec.len() != n
            || self.a_mat.len() != meq
            || self.nu_vec.len() != meq
            || self.g_mat.len() != mineq
            || self.mu_vec.len() != mineq
        {
            return Err(ClearingError::DimensionMismatch(
                "FHQPB001 top-level dims".into(),
            ));
        }
        for row in &self.q_mat {
            if row.len() != n {
                return Err(ClearingError::DimensionMismatch(
                    "FHQPB001 Q row len".into(),
                ));
            }
        }
        for row in &self.a_mat {
            if row.len() != n {
                return Err(ClearingError::DimensionMismatch(
                    "FHQPB001 A row len".into(),
                ));
            }
        }
        for row in &self.g_mat {
            if row.len() != n {
                return Err(ClearingError::DimensionMismatch(
                    "FHQPB001 G row len".into(),
                ));
            }
        }

        // 1. Verify SDD factor decomposition (`sddFactor_implies_psd`):
        self.sdd.verify()?;

        // 2. Mandatory FHQPB001 Scale Pin + Matrix Pin + Program Digest Pin:
        if self.sdd.scale_denom != self.scale_denom {
            return Err(ClearingError::ScalePinMismatch);
        }
        if self.sdd.admitted_q != self.q_mat {
            return Err(ClearingError::MatrixPinMismatch);
        }
        let want_digest = canonical_qp_program_digest(
            self.scale_denom,
            &self.q_mat,
            &self.q_vec,
            &self.a_mat,
            &self.b_vec,
            &self.g_mat,
            &self.h_vec,
            &self.l_vec,
            &self.u_vec,
        );
        if want_digest != self.program_digest {
            return Err(ClearingError::ProgramDigestMismatch);
        }

        // 3. Primal feasibility: `A x == b`, `G x <= h`, `l <= x <= u`:
        for r in 0..meq {
            let ax = dot_i64_checked(&self.a_mat[r], &self.x_vec)?;
            let b_r = self.b_vec[r] as i128;
            if ax != b_r {
                return Err(ClearingError::PrimalEqualityViolation {
                    row: r,
                    lhs: ax,
                    rhs: b_r,
                });
            }
        }
        let mut gx_vec = Vec::with_capacity(mineq);
        for k in 0..mineq {
            let gx = dot_i64_checked(&self.g_mat[k], &self.x_vec)?;
            let h_k = self.h_vec[k] as i128;
            if gx > h_k {
                return Err(ClearingError::PrimalInequalityViolation {
                    row: k,
                    lhs: gx,
                    rhs: h_k,
                });
            }
            gx_vec.push(gx);
        }
        for i in 0..n {
            if self.x_vec[i] < self.l_vec[i] || self.x_vec[i] > self.u_vec[i] {
                return Err(ClearingError::PrimalBoxViolation {
                    idx: i,
                    val: self.x_vec[i],
                    lo: self.l_vec[i],
                    hi: self.u_vec[i],
                });
            }
        }

        // 4. Dual non-negativity: `mu >= 0`, `lam_l >= 0`, `lam_u >= 0`:
        for (k, &m) in self.mu_vec.iter().enumerate() {
            if m < 0 {
                return Err(ClearingError::NegativeDualMultiplier {
                    kind: "mu",
                    idx: k,
                    val: m,
                });
            }
        }
        for i in 0..n {
            if self.lam_l_vec[i] < 0 {
                return Err(ClearingError::NegativeDualMultiplier {
                    kind: "lam_l",
                    idx: i,
                    val: self.lam_l_vec[i],
                });
            }
            if self.lam_u_vec[i] < 0 {
                return Err(ClearingError::NegativeDualMultiplier {
                    kind: "lam_u",
                    idx: i,
                    val: self.lam_u_vec[i],
                });
            }
        }

        // 5. KKT Lagrangian stationarity: `Q x + q + A^T nu + G^T mu - lam_l + lam_u == 0`:
        let mut qx_vec = Vec::with_capacity(n);
        for i in 0..n {
            let qx_i = dot_i64_checked(&self.q_mat[i], &self.x_vec)?;
            qx_vec.push(qx_i);
            let mut at_nu = 0i128;
            for r in 0..meq {
                let prod = checked_mul_i128(self.a_mat[r][i] as i128, self.nu_vec[r] as i128)?;
                at_nu = checked_add_i128(at_nu, prod)?;
            }
            let mut gt_mu = 0i128;
            for k in 0..mineq {
                let prod = checked_mul_i128(self.g_mat[k][i] as i128, self.mu_vec[k] as i128)?;
                gt_mu = checked_add_i128(gt_mu, prod)?;
            }
            let mut res = checked_add_i128(qx_i, self.q_vec[i] as i128)?;
            res = checked_add_i128(res, at_nu)?;
            res = checked_add_i128(res, gt_mu)?;
            res = checked_sub_i128(res, self.lam_l_vec[i] as i128)?;
            res = checked_add_i128(res, self.lam_u_vec[i] as i128)?;
            if res != 0 {
                return Err(ClearingError::StationarityViolation {
                    idx: i,
                    residual: res,
                });
            }
        }

        // 6. Complementarity gap & explicit Wolfe primal-dual check (`primal_sub_dual_eq_compGap`):
        let mut comp_gap = 0i128;
        for ((&hk, &gxk), &muk) in self.h_vec.iter().zip(&gx_vec).zip(&self.mu_vec) {
            let slack = checked_sub_i128(hk as i128, gxk)?;
            comp_gap = checked_add_i128(comp_gap, checked_mul_i128(muk as i128, slack)?)?;
        }
        for i in 0..n {
            let sl_l = checked_sub_i128(self.x_vec[i] as i128, self.l_vec[i] as i128)?;
            let sl_u = checked_sub_i128(self.u_vec[i] as i128, self.x_vec[i] as i128)?;
            comp_gap =
                checked_add_i128(comp_gap, checked_mul_i128(self.lam_l_vec[i] as i128, sl_l)?)?;
            comp_gap =
                checked_add_i128(comp_gap, checked_mul_i128(self.lam_u_vec[i] as i128, sl_u)?)?;
        }

        // Explicit `2 * S^3 * p*` and `2 * S^3 * d*`:
        let mut x_qx = 0i128;
        for (&xi, &qxi) in self.x_vec.iter().zip(&qx_vec) {
            x_qx = checked_add_i128(x_qx, checked_mul_i128(xi as i128, qxi)?)?;
        }
        let q_dot_x = dot_i64_checked(&self.q_vec, &self.x_vec)?;
        let b_dot_nu = dot_i64_checked(&self.b_vec, &self.nu_vec)?;
        let h_dot_mu = dot_i64_checked(&self.h_vec, &self.mu_vec)?;
        let l_dot_laml = dot_i64_checked(&self.l_vec, &self.lam_l_vec)?;
        let u_dot_lamu = dot_i64_checked(&self.u_vec, &self.lam_u_vec)?;

        let two_primal = checked_add_i128(x_qx, checked_mul_i128(2, q_dot_x)?)?;
        let mut two_dual = checked_sub_i128(0, x_qx)?;
        two_dual = checked_sub_i128(two_dual, checked_mul_i128(2, b_dot_nu)?)?;
        two_dual = checked_sub_i128(two_dual, checked_mul_i128(2, h_dot_mu)?)?;
        two_dual = checked_add_i128(two_dual, checked_mul_i128(2, l_dot_laml)?)?;
        two_dual = checked_sub_i128(two_dual, checked_mul_i128(2, u_dot_lamu)?)?;

        let pd_diff = checked_sub_i128(two_primal, two_dual)?;
        debug_assert_eq!(pd_diff, checked_mul_i128(2, comp_gap)?);

        if comp_gap > self.eps_int || self.eps_int < 0 {
            return Err(ClearingError::OptimalityGapExceeded {
                gap_num: comp_gap,
                eps_num: self.eps_int,
            });
        }

        Ok(VerifiedKktSummary {
            n,
            meq,
            mineq,
            sdd_edges: self.sdd.edges.len(),
            scale_denom: self.scale_denom,
            two_primal_scaled: two_primal,
            two_dual_scaled: two_dual,
            comp_gap_scaled: comp_gap,
            eps_scaled: self.eps_int,
        })
    }

    /// Strict zero-gap KKT check (`p* == d*`, exact complementary slackness).
    pub fn verify_zero_gap(&self) -> Result<VerifiedKktSummary, ClearingError> {
        if self.eps_int != 0 {
            return Err(ClearingError::OptimalityGapExceeded {
                gap_num: self.eps_int,
                eps_num: 0,
            });
        }
        let summary = self.verify()?;
        if summary.comp_gap_scaled != 0 {
            return Err(ClearingError::OptimalityGapExceeded {
                gap_num: summary.comp_gap_scaled,
                eps_num: 0,
            });
        }
        Ok(summary)
    }

    /// Canonical `FHQPB001` binary wire encoding with trailing SHA-256 domain checksum.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(FHQPB_MAGIC);
        out.extend_from_slice(&WIRE_VERSION_V1.to_le_bytes());
        out.extend_from_slice(&self.scale_denom.to_le_bytes());
        out.extend_from_slice(&(self.q_vec.len() as u32).to_le_bytes());
        out.extend_from_slice(&(self.b_vec.len() as u32).to_le_bytes());
        out.extend_from_slice(&(self.h_vec.len() as u32).to_le_bytes());
        out.extend_from_slice(&self.sdd.scale_denom.to_le_bytes());
        out.extend_from_slice(&(self.sdd.edges.len() as u32).to_le_bytes());
        for e in &self.sdd.edges {
            out.extend_from_slice(&e.u.to_le_bytes());
            out.extend_from_slice(&e.v.to_le_bytes());
            out.extend_from_slice(&e.alpha.to_le_bytes());
            out.extend_from_slice(&e.beta.to_le_bytes());
            out.extend_from_slice(&e.weight.to_le_bytes());
        }
        let push_i64s = |dst: &mut Vec<u8>, xs: &[i64]| {
            for &v in xs {
                dst.extend_from_slice(&v.to_le_bytes());
            }
        };
        push_i64s(&mut out, &self.sdd.diag_slack);
        for row in &self.sdd.admitted_q {
            push_i64s(&mut out, row);
        }
        for row in &self.q_mat {
            push_i64s(&mut out, row);
        }
        push_i64s(&mut out, &self.q_vec);
        for row in &self.a_mat {
            push_i64s(&mut out, row);
        }
        push_i64s(&mut out, &self.b_vec);
        for row in &self.g_mat {
            push_i64s(&mut out, row);
        }
        push_i64s(&mut out, &self.h_vec);
        push_i64s(&mut out, &self.l_vec);
        push_i64s(&mut out, &self.u_vec);
        push_i64s(&mut out, &self.x_vec);
        push_i64s(&mut out, &self.nu_vec);
        push_i64s(&mut out, &self.mu_vec);
        push_i64s(&mut out, &self.lam_l_vec);
        push_i64s(&mut out, &self.lam_u_vec);
        out.extend_from_slice(&self.eps_int.to_le_bytes());
        out.extend_from_slice(&self.program_digest);

        let mut h = Sha256::new();
        h.update(b"FHQPB001_WIRE_TAG|");
        h.update(&out);
        let tag: [u8; 32] = h.finalize().into();
        out.extend_from_slice(&tag);
        out
    }

    /// Canonical `FHQPB001` wire decoder + immediate fail-closed verifier.
    pub fn from_wire_bytes_and_verify(
        bytes: &[u8],
    ) -> Result<(Self, VerifiedKktSummary), ClearingError> {
        if bytes.len() < 8 + 4 + 8 + 12 + 8 + 4 + 16 + 32 + 32 {
            return Err(ClearingError::InvalidWireFormat(
                "FHQPB001 truncated".into(),
            ));
        }
        let (body, tag_slice) = bytes.split_at(bytes.len() - 32);
        let mut h = Sha256::new();
        h.update(b"FHQPB001_WIRE_TAG|");
        h.update(body);
        let want_tag: [u8; 32] = h.finalize().into();
        if tag_slice != want_tag {
            return Err(ClearingError::ChecksumMismatch);
        }

        let mut cur = ByteReader::new(body);
        let magic = cur.take(8).map_err(ClearingError::InvalidWireFormat)?;
        if magic != FHQPB_MAGIC {
            return Err(ClearingError::InvalidWireFormat(
                "bad FHQPB001 magic".into(),
            ));
        }
        let ver = cur.read_u32().map_err(ClearingError::InvalidWireFormat)?;
        if ver != WIRE_VERSION_V1 {
            return Err(ClearingError::InvalidWireFormat(
                "bad FHQPB001 version".into(),
            ));
        }
        let read_i64 = |c: &mut ByteReader<'_>| -> Result<i64, ClearingError> {
            let b = c.take(8).map_err(ClearingError::InvalidWireFormat)?;
            Ok(i64::from_le_bytes(b.try_into().unwrap()))
        };
        let read_vec_i64 =
            |c: &mut ByteReader<'_>, len: usize| -> Result<Vec<i64>, ClearingError> {
                let mut v = Vec::with_capacity(len);
                for _ in 0..len {
                    v.push(read_i64(c)?);
                }
                Ok(v)
            };
        let read_mat_i64 = |c: &mut ByteReader<'_>,
                            rows: usize,
                            cols: usize|
         -> Result<Vec<Vec<i64>>, ClearingError> {
            let mut m = Vec::with_capacity(rows);
            for _ in 0..rows {
                m.push(read_vec_i64(c, cols)?);
            }
            Ok(m)
        };

        let scale_denom = read_i64(&mut cur)?;
        let n = cur.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
        let meq = cur.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
        let mineq = cur.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
        if n > 4096 || meq > 4096 || mineq > 4096 {
            return Err(ClearingError::InvalidWireFormat(
                "FHQPB001 dimension cap".into(),
            ));
        }
        let sdd_scale = read_i64(&mut cur)?;
        let n_edges = cur.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
        if n_edges > 65536 {
            return Err(ClearingError::InvalidWireFormat("FHQPB001 edge cap".into()));
        }
        let mut edges = Vec::with_capacity(n_edges);
        for _ in 0..n_edges {
            let u = cur.read_u32().map_err(ClearingError::InvalidWireFormat)?;
            let v = cur.read_u32().map_err(ClearingError::InvalidWireFormat)?;
            let alpha = read_i64(&mut cur)?;
            let beta = read_i64(&mut cur)?;
            let weight = read_i64(&mut cur)?;
            edges.push(SddFactorEdgeInt {
                u,
                v,
                alpha,
                beta,
                weight,
            });
        }
        let diag_slack = read_vec_i64(&mut cur, n)?;
        let admitted_q = read_mat_i64(&mut cur, n, n)?;
        let q_mat = read_mat_i64(&mut cur, n, n)?;
        let q_vec = read_vec_i64(&mut cur, n)?;
        let a_mat = read_mat_i64(&mut cur, meq, n)?;
        let b_vec = read_vec_i64(&mut cur, meq)?;
        let g_mat = read_mat_i64(&mut cur, mineq, n)?;
        let h_vec = read_vec_i64(&mut cur, mineq)?;
        let l_vec = read_vec_i64(&mut cur, n)?;
        let u_vec = read_vec_i64(&mut cur, n)?;
        let x_vec = read_vec_i64(&mut cur, n)?;
        let nu_vec = read_vec_i64(&mut cur, meq)?;
        let mu_vec = read_vec_i64(&mut cur, mineq)?;
        let lam_l_vec = read_vec_i64(&mut cur, n)?;
        let lam_u_vec = read_vec_i64(&mut cur, n)?;
        let eps_bytes = cur.take(16).map_err(ClearingError::InvalidWireFormat)?;
        let eps_int = i128::from_le_bytes(eps_bytes.try_into().unwrap());
        let program_digest = cur.read_hash().map_err(ClearingError::InvalidWireFormat)?;
        if !cur.is_eof() {
            return Err(ClearingError::InvalidWireFormat(
                "FHQPB001 trailing bytes".into(),
            ));
        }

        let bundle = ExactQpCertificateBundle {
            scale_denom,
            sdd: ExactSddFactorCertificate {
                n,
                scale_denom: sdd_scale,
                edges,
                diag_slack,
                admitted_q,
            },
            q_mat,
            q_vec,
            a_mat,
            b_vec,
            g_mat,
            h_vec,
            l_vec,
            u_vec,
            x_vec,
            nu_vec,
            mu_vec,
            lam_l_vec,
            lam_u_vec,
            eps_int,
            program_digest,
        };
        let summary = bundle.verify()?;
        Ok((bundle, summary))
    }
}

// ------------------------------------------------------------------------------------------------
// Exact `BigInt` Rational Arithmetic & Primal Active-Set Call-Auction SDD-QP Solver
// ------------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactRat {
    num: BigInt,
    den: BigInt, // strictly positive, gcd(|num|, den) == 1
}

impl ExactRat {
    fn zero() -> Self {
        ExactRat {
            num: BigInt::zero(),
            den: BigInt::from(1),
        }
    }

    fn one() -> Self {
        ExactRat {
            num: BigInt::from(1),
            den: BigInt::from(1),
        }
    }

    fn from_i64(v: i64) -> Self {
        ExactRat {
            num: BigInt::from(v),
            den: BigInt::from(1),
        }
    }

    fn new(mut num: BigInt, mut den: BigInt) -> Self {
        assert!(!den.is_zero(), "ExactRat zero denominator");
        if den.is_negative() {
            num = -num;
            den = -den;
        }
        if num.is_zero() {
            return Self::zero();
        }
        let g = num.gcd(&den);
        ExactRat {
            num: num / &g,
            den: den / g,
        }
    }

    fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    fn is_neg(&self) -> bool {
        self.num.is_negative()
    }

    fn is_pos(&self) -> bool {
        self.num.is_positive()
    }

    fn neg_val(&self) -> Self {
        ExactRat {
            num: -&self.num,
            den: self.den.clone(),
        }
    }

    fn add_val(&self, other: &Self) -> Self {
        Self::new(
            &self.num * &other.den + &other.num * &self.den,
            &self.den * &other.den,
        )
    }

    fn sub_val(&self, other: &Self) -> Self {
        Self::new(
            &self.num * &other.den - &other.num * &self.den,
            &self.den * &other.den,
        )
    }

    fn mul_val(&self, other: &Self) -> Self {
        Self::new(&self.num * &other.num, &self.den * &other.den)
    }

    fn div_val(&self, other: &Self) -> Self {
        assert!(!other.is_zero(), "ExactRat division by zero");
        Self::new(&self.num * &other.den, &self.den * &other.num)
    }

    fn cmp_val(&self, other: &Self) -> std::cmp::Ordering {
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }
}

impl Ord for ExactRat {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp_val(other)
    }
}

impl PartialOrd for ExactRat {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn solve_exact_linear_system(
    mut mat: Vec<Vec<ExactRat>>,
    mut rhs: Vec<ExactRat>,
) -> Result<Vec<ExactRat>, ClearingError> {
    let m = rhs.len();
    for col in 0..m {
        let piv = (col..m)
            .find(|&r| !mat[r][col].is_zero())
            .ok_or_else(|| ClearingError::SolverFailure("singular KKT submatrix".into()))?;
        if piv != col {
            mat.swap(col, piv);
            rhs.swap(col, piv);
        }
        let inv_p = ExactRat::one().div_val(&mat[col][col]);
        for cell in &mut mat[col][col..m] {
            *cell = cell.mul_val(&inv_p);
        }
        rhs[col] = rhs[col].mul_val(&inv_p);
        for r in 0..m {
            if r != col && !mat[r][col].is_zero() {
                let factor = mat[r][col].clone();
                let (row_r, row_col) = if r < col {
                    let (head, tail) = mat.split_at_mut(col);
                    (&mut head[r], &tail[0])
                } else {
                    let (head, tail) = mat.split_at_mut(r);
                    (&mut tail[0], &head[col])
                };
                for (dst, src) in row_r[col..m].iter_mut().zip(&row_col[col..m]) {
                    let sub = factor.mul_val(src);
                    *dst = dst.sub_val(&sub);
                }
                let sub_r = factor.mul_val(&rhs[col]);
                rhs[r] = rhs[r].sub_val(&sub_r);
            }
        }
    }
    Ok(rhs)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoundState {
    FixedZeroCap,
    Lower,
    Free,
    Upper,
}

/// Call-auction SDD-QP configuration:
/// Maximizes `(surplus_weight * sum_k p_k (b_k - a_k)) - 1/2 x^T Q x` subject to
/// `sum_k b_k - sum_k a_k == 0` and `0 <= b_k <= agg_bids[k]`, `0 <= a_k <= agg_asks[k]`,
/// where `Q = diag(gamma_prox) + BlockLaplacian(w_lap)` (`2 * (K - 1)` SDD edges + `2 * K` positive diag slacks).
#[derive(Clone, Debug)]
pub struct CallAuctionQpConfig {
    pub tick_prices: Vec<i64>,
    pub surplus_weight: i64,
    pub gamma_prox: i64,
    pub w_lap: i64,
}

impl CallAuctionQpConfig {
    pub fn standard(tick_prices: Vec<i64>) -> Self {
        CallAuctionQpConfig {
            tick_prices,
            surplus_weight: 64,
            gamma_prox: 1,
            w_lap: 1,
        }
    }
}

/// Certified call-auction clearing result over the aggregate order book (`0` individual bid access).
#[derive(Clone, Debug)]
pub struct CertifiedAuctionClearing {
    pub scale_denom: i64,
    /// Scaled cleared buy quantities `x_buy_scaled[k] / scale_denom` per tick `k`.
    pub cleared_bids_scaled: Vec<i64>,
    /// Scaled cleared sell quantities `x_ask_scaled[k] / scale_denom` per tick `k`.
    pub cleared_asks_scaled: Vec<i64>,
    /// Scaled uniform clearing dual price `nu_scaled / (scale_denom * surplus_weight)`.
    pub clearing_dual_nu_scaled: i64,
    pub bundle: ExactQpCertificateBundle,
    pub kkt_summary: VerifiedKktSummary,
}

/// Untrusted exact-rational Primal Active-Set QP solver + `FHQPB001` zero-gap certificate emitter.
pub fn solve_certified_call_auction_qp(
    cfg: &CallAuctionQpConfig,
    agg_bids: &[u64],
    agg_asks: &[u64],
) -> Result<CertifiedAuctionClearing, ClearingError> {
    let k_ticks = cfg.tick_prices.len();
    if k_ticks == 0 || agg_bids.len() != k_ticks || agg_asks.len() != k_ticks {
        return Err(ClearingError::DimensionMismatch(
            "call-auction tick len".into(),
        ));
    }
    if cfg.gamma_prox <= 0 || cfg.w_lap < 0 || cfg.surplus_weight <= 0 {
        return Err(ClearingError::SolverFailure(
            "invalid auction regularization params".into(),
        ));
    }

    let n = 2 * k_ticks;
    let mut edges = Vec::new();
    let mut q_base = vec![vec![0i64; n]; n];
    for (i, row) in q_base.iter_mut().enumerate() {
        row[i] = cfg.gamma_prox;
    }
    if cfg.w_lap > 0 && k_ticks >= 2 {
        for base in [0usize, k_ticks] {
            for t in 0..(k_ticks - 1) {
                let u = base + t;
                let v = base + t + 1;
                edges.push(SddFactorEdgeInt {
                    u: u as u32,
                    v: v as u32,
                    alpha: 1,
                    beta: -1,
                    weight: cfg.w_lap,
                });
                q_base[u][u] += cfg.w_lap;
                q_base[v][v] += cfg.w_lap;
                q_base[u][v] -= cfg.w_lap;
                q_base[v][u] -= cfg.w_lap;
            }
        }
    }

    let mut q_lin = vec![0i64; n];
    let mut a_row = vec![0i64; n];
    let mut u_caps = vec![0i64; n];
    for k in 0..k_ticks {
        q_lin[k] = -cfg.surplus_weight * cfg.tick_prices[k];
        q_lin[k_ticks + k] = cfg.surplus_weight * cfg.tick_prices[k];
        a_row[k] = 1;
        a_row[k_ticks + k] = -1;
        u_caps[k] = i64::try_from(agg_bids[k]).map_err(|_| ClearingError::ArithmeticOverflow)?;
        u_caps[k_ticks + k] =
            i64::try_from(agg_asks[k]).map_err(|_| ClearingError::ArithmeticOverflow)?;
    }

    // Start at feasible `x = 0` (`A * 0 = 0`, `0 <= 0 <= u_caps`):
    let mut x: Vec<ExactRat> = vec![ExactRat::zero(); n];
    let mut states: Vec<BoundState> = (0..n)
        .map(|i| {
            if u_caps[i] == 0 {
                BoundState::FixedZeroCap
            } else {
                BoundState::Lower
            }
        })
        .collect();

    let eval_grad0 = |x_cur: &[ExactRat]| -> Vec<ExactRat> {
        (0..n)
            .map(|i| {
                let mut acc = ExactRat::from_i64(q_lin[i]);
                for j in 0..n {
                    if q_base[i][j] != 0 {
                        acc = acc.add_val(&ExactRat::from_i64(q_base[i][j]).mul_val(&x_cur[j]));
                    }
                }
                acc
            })
            .collect()
    };

    let mut nu_opt = ExactRat::zero();
    let mut converged = false;

    for _iter in 0..256 {
        let free: Vec<usize> = (0..n).filter(|&i| states[i] == BoundState::Free).collect();
        if free.is_empty() {
            // All variables with `u_i > 0` are pinned at Lower (`0`) or Upper (`u_i`).
            // Check interval `[nu_lo, nu_hi]` for dual clearing price `nu`:
            let g0 = eval_grad0(&x);
            let mut lo_cand: Option<(ExactRat, usize)> = None;
            let mut hi_cand: Option<(ExactRat, usize)> = None;
            for i in 0..n {
                match (states[i], a_row[i]) {
                    (BoundState::Lower, 1) => {
                        // g0[i] + nu >= 0  <=>  nu >= -g0[i]
                        let bnd = g0[i].neg_val();
                        if lo_cand.as_ref().is_none_or(|(cur, _)| &bnd > cur) {
                            lo_cand = Some((bnd, i));
                        }
                    }
                    (BoundState::Upper, -1) => {
                        // g0[i] - nu <= 0  <=>  nu >= g0[i]
                        let bnd = g0[i].clone();
                        if lo_cand.as_ref().is_none_or(|(cur, _)| &bnd > cur) {
                            lo_cand = Some((bnd, i));
                        }
                    }
                    (BoundState::Upper, 1) => {
                        // g0[i] + nu <= 0  <=>  nu <= -g0[i]
                        let bnd = g0[i].neg_val();
                        if hi_cand.as_ref().is_none_or(|(cur, _)| &bnd < cur) {
                            hi_cand = Some((bnd, i));
                        }
                    }
                    (BoundState::Lower, -1) => {
                        // g0[i] - nu >= 0  <=>  nu <= g0[i]
                        let bnd = g0[i].clone();
                        if hi_cand.as_ref().is_none_or(|(cur, _)| &bnd < cur) {
                            hi_cand = Some((bnd, i));
                        }
                    }
                    _ => {}
                }
            }
            match (lo_cand, hi_cand) {
                (Some((lo, i_lo)), Some((hi, i_hi))) => {
                    if lo <= hi {
                        nu_opt = lo.add_val(&hi).div_val(&ExactRat::from_i64(2));
                        converged = true;
                        break;
                    } else {
                        // Profitable crossing pair `(i_lo, i_hi)`! Release both simultaneously:
                        states[i_lo] = BoundState::Free;
                        states[i_hi] = BoundState::Free;
                        continue;
                    }
                }
                (Some((lo, _)), None) => {
                    nu_opt = lo;
                    converged = true;
                    break;
                }
                (None, Some((hi, _))) => {
                    nu_opt = hi;
                    converged = true;
                    break;
                }
                (None, None) => {
                    nu_opt = ExactRat::zero();
                    converged = true;
                    break;
                }
            }
        }

        // Solve equality-constrained Newton/KKT step on `free`:
        // `Q_{FF} d_F + A_F^T nu = -(Q x + q)_F` and `A_F d_F = 0`
        let g0 = eval_grad0(&x);
        let nf = free.len();
        let dim = nf + 1;
        let mut kkt_mat = vec![vec![ExactRat::zero(); dim]; dim];
        let mut kkt_rhs = vec![ExactRat::zero(); dim];
        for (ri, &i) in free.iter().enumerate() {
            for (cj, &j) in free.iter().enumerate() {
                kkt_mat[ri][cj] = ExactRat::from_i64(q_base[i][j]);
            }
            let ai = ExactRat::from_i64(a_row[i]);
            kkt_mat[ri][nf] = ai.clone();
            kkt_mat[nf][ri] = ai;
            kkt_rhs[ri] = g0[i].neg_val();
        }
        kkt_rhs[nf] = ExactRat::zero();
        let sol = solve_exact_linear_system(kkt_mat, kkt_rhs)?;
        let d_f = &sol[..nf];
        let nu_sub = sol[nf].clone();

        let all_zero_step = d_f.iter().all(|v| v.is_zero());
        if all_zero_step {
            // Check dual multipliers on active bounds `Lower` / `Upper`:
            let mut worst_viol: Option<(ExactRat, usize)> = None;
            for i in 0..n {
                let gi = g0[i].add_val(&ExactRat::from_i64(a_row[i]).mul_val(&nu_sub));
                match states[i] {
                    BoundState::Lower => {
                        if gi.is_neg() && worst_viol.as_ref().is_none_or(|(w, _)| &gi < w) {
                            worst_viol = Some((gi, i));
                        }
                    }
                    BoundState::Upper => {
                        let neg_gi = gi.neg_val();
                        if neg_gi.is_neg() && worst_viol.as_ref().is_none_or(|(w, _)| &neg_gi < w) {
                            worst_viol = Some((neg_gi, i));
                        }
                    }
                    _ => {}
                }
            }
            if let Some((_, drop_idx)) = worst_viol {
                states[drop_idx] = BoundState::Free;
            } else {
                nu_opt = nu_sub;
                converged = true;
                break;
            }
        } else {
            // Compute exact rational step length `alpha in [0, 1]` to nearest blocking bound:
            let mut alpha = ExactRat::one();
            let mut blocker: Option<(usize, BoundState)> = None;
            for (fi, &i) in free.iter().enumerate() {
                let di = &d_f[fi];
                if di.is_neg() {
                    let cand = x[i].neg_val().div_val(di);
                    if cand < alpha {
                        alpha = cand;
                        blocker = Some((i, BoundState::Lower));
                    }
                } else if di.is_pos() {
                    let cap = ExactRat::from_i64(u_caps[i]);
                    let cand = cap.sub_val(&x[i]).div_val(di);
                    if cand < alpha {
                        alpha = cand;
                        blocker = Some((i, BoundState::Upper));
                    }
                }
            }
            if !alpha.is_zero() {
                for (fi, &i) in free.iter().enumerate() {
                    x[i] = x[i].add_val(&alpha.mul_val(&d_f[fi]));
                }
            }
            if let Some((blk_idx, blk_state)) = blocker {
                states[blk_idx] = blk_state;
            }
        }
    }

    if !converged {
        return Err(ClearingError::SolverFailure(
            "active-set solver exceeded iteration cap".into(),
        ));
    }

    // Clear rational denominators across `x[0..n]` and `nu_opt`:
    let mut scale_big = nu_opt.den.clone();
    for xi in &x {
        scale_big = scale_big.lcm(&xi.den);
    }
    let s_i64 = scale_big.to_i64().ok_or_else(|| {
        ClearingError::SolverFailure("rational scale denominator overflowed i64".into())
    })?;
    if s_i64 <= 0 {
        return Err(ClearingError::InvalidScaleDenom);
    }

    // Under `Fhqpb001BundleInt.decodeQp`:
    //   `Q_rat = Q_int / S`, `q_rat = q_int / S^2`, `A_rat = A_int / S`, `b_rat = 0`,
    //   `l_rat = l_int / S = 0`, `u_rat = u_int / S = u_caps`,
    //   `x_rat = x_int / S`, `nu_rat = nu_int / S`, `lam_{L,U}_rat = lam_{L,U}_int / S^2`.
    // Setting `Q_int = S * q_base`, `q_int = S^2 * q_lin`, `A_int = S * a_row`, `u_int = S * u_caps`,
    // `edges_scaled = S * edges`, `diag_slack = S * gamma_prox`, every integer KKT equation holds EXACTLY!
    let s_big = BigInt::from(s_i64);
    let s2_i128 = checked_mul_i128(s_i64 as i128, s_i64 as i128)?;

    let to_scaled_i64 = |r: &ExactRat| -> Result<i64, ClearingError> {
        let v = (&r.num * (&s_big / &r.den))
            .to_i64()
            .ok_or(ClearingError::ArithmeticOverflow)?;
        Ok(v)
    };

    let x_int: Vec<i64> = x.iter().map(to_scaled_i64).collect::<Result<_, _>>()?;
    let nu_int_scalar = to_scaled_i64(&nu_opt)?;

    let mut q_int = vec![vec![0i64; n]; n];
    for i in 0..n {
        for j in 0..n {
            q_int[i][j] = i64::try_from((q_base[i][j] as i128) * (s_i64 as i128))
                .map_err(|_| ClearingError::ArithmeticOverflow)?;
        }
    }
    let q_vec_int: Vec<i64> = q_lin
        .iter()
        .map(|&v| {
            i64::try_from((v as i128) * s2_i128).map_err(|_| ClearingError::ArithmeticOverflow)
        })
        .collect::<Result<_, _>>()?;
    let a_mat_int = vec![a_row
        .iter()
        .map(|&v| {
            i64::try_from((v as i128) * (s_i64 as i128))
                .map_err(|_| ClearingError::ArithmeticOverflow)
        })
        .collect::<Result<Vec<i64>, _>>()?];
    let b_vec_int = vec![0i64];
    let l_vec_int = vec![0i64; n];
    let u_vec_int: Vec<i64> = u_caps
        .iter()
        .map(|&v| {
            i64::try_from((v as i128) * (s_i64 as i128))
                .map_err(|_| ClearingError::ArithmeticOverflow)
        })
        .collect::<Result<_, _>>()?;

    let scaled_edges: Vec<SddFactorEdgeInt> = edges
        .iter()
        .map(|e| {
            Ok(SddFactorEdgeInt {
                u: e.u,
                v: e.v,
                alpha: e.alpha,
                beta: e.beta,
                weight: i64::try_from((e.weight as i128) * (s_i64 as i128))
                    .map_err(|_| ClearingError::ArithmeticOverflow)?,
            })
        })
        .collect::<Result<_, ClearingError>>()?;
    let diag_slack_int = vec![
        i64::try_from((cfg.gamma_prox as i128) * (s_i64 as i128))
            .map_err(|_| ClearingError::ArithmeticOverflow)?;
        n
    ];

    let mut lam_l_int = vec![0i64; n];
    let mut lam_u_int = vec![0i64; n];
    for i in 0..n {
        let qx_i = dot_i64_checked(&q_int[i], &x_int)?;
        let at_nu_i = checked_mul_i128(a_mat_int[0][i] as i128, nu_int_scalar as i128)?;
        let grad_i = checked_add_i128(checked_add_i128(qx_i, q_vec_int[i] as i128)?, at_nu_i)?;
        if grad_i >= 0 {
            lam_l_int[i] = i64::try_from(grad_i).map_err(|_| ClearingError::ArithmeticOverflow)?;
        } else {
            lam_u_int[i] = i64::try_from(-grad_i).map_err(|_| ClearingError::ArithmeticOverflow)?;
        }
    }

    let program_digest = canonical_qp_program_digest(
        s_i64,
        &q_int,
        &q_vec_int,
        &a_mat_int,
        &b_vec_int,
        &[],
        &[],
        &l_vec_int,
        &u_vec_int,
    );

    let bundle = ExactQpCertificateBundle {
        scale_denom: s_i64,
        sdd: ExactSddFactorCertificate {
            n,
            scale_denom: s_i64,
            edges: scaled_edges,
            diag_slack: diag_slack_int,
            admitted_q: q_int.clone(),
        },
        q_mat: q_int,
        q_vec: q_vec_int,
        a_mat: a_mat_int,
        b_vec: b_vec_int,
        g_mat: Vec::new(),
        h_vec: Vec::new(),
        l_vec: l_vec_int,
        u_vec: u_vec_int,
        x_vec: x_int.clone(),
        nu_vec: vec![nu_int_scalar],
        mu_vec: Vec::new(),
        lam_l_vec: lam_l_int,
        lam_u_vec: lam_u_int,
        eps_int: 0,
        program_digest,
    };

    let kkt_summary = bundle.verify_zero_gap()?;
    Ok(CertifiedAuctionClearing {
        scale_denom: s_i64,
        cleared_bids_scaled: x_int[..k_ticks].to_vec(),
        cleared_asks_scaled: x_int[k_ticks..].to_vec(),
        clearing_dual_nu_scaled: nu_int_scalar,
        bundle,
        kkt_summary,
    })
}

// ================================================================================================
// §2. Multilateral Netting Compression & `DBNET001` Verifier (`∑ net_legs == ∑ gross_legs`)
// ================================================================================================

/// Directed settlement leg moving `amount > 0` units of `asset` from `payer` to `payee` (`payer != payee`),
/// matching `SettlementLeg` in `Theory/ExactKktClearingCert.lean`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SettlementLeg {
    pub payer: u32,
    pub payee: u32,
    pub asset: u32,
    pub amount: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedNettingSummary {
    pub num_parties: usize,
    pub num_assets: usize,
    pub gross_leg_count: usize,
    pub net_leg_count: usize,
    pub gross_volume: u128,
    pub net_volume: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultilateralNettingCertificate {
    pub gross_legs: Vec<SettlementLeg>,
    pub net_legs: Vec<SettlementLeg>,
}

/// Compress arbitrary well-formed `gross_legs` into minimal per-asset multilateral `net_legs`
/// (`|net_legs| <= P - 1` per asset, `0` legs on closed cycles, exact balance preservation).
pub fn compress_multilateral_legs(
    gross_legs: &[SettlementLeg],
) -> Result<MultilateralNettingCertificate, ClearingError> {
    let mut balances: BTreeMap<(u32, u32), i128> = BTreeMap::new();
    let mut assets: BTreeSet<u32> = BTreeSet::new();
    for (idx, leg) in gross_legs.iter().enumerate() {
        if leg.amount == 0 || leg.payer == leg.payee {
            return Err(ClearingError::InvalidSettlementLeg { idx });
        }
        assets.insert(leg.asset);
        let amt = leg.amount as i128;
        let p_out = balances.entry((leg.asset, leg.payer)).or_insert(0);
        *p_out = checked_sub_i128(*p_out, amt)?;
        let p_in = balances.entry((leg.asset, leg.payee)).or_insert(0);
        *p_in = checked_add_i128(*p_in, amt)?;
    }

    let mut net_legs = Vec::new();
    for asset in assets {
        let mut debtors: Vec<(u32, u128)> = Vec::new();
        let mut creditors: Vec<(u32, u128)> = Vec::new();
        for (&(a, party), &bal) in &balances {
            if a == asset {
                if bal < 0 {
                    debtors.push((party, (-bal) as u128));
                } else if bal > 0 {
                    creditors.push((party, bal as u128));
                }
            }
        }
        let (mut di, mut ci) = (0usize, 0usize);
        while di < debtors.len() && ci < creditors.len() {
            let flow = debtors[di].1.min(creditors[ci].1);
            let amt_u64 = u64::try_from(flow).map_err(|_| ClearingError::ArithmeticOverflow)?;
            net_legs.push(SettlementLeg {
                payer: debtors[di].0,
                payee: creditors[ci].0,
                asset,
                amount: amt_u64,
            });
            debtors[di].1 -= flow;
            creditors[ci].1 -= flow;
            if debtors[di].1 == 0 {
                di += 1;
            }
            if creditors[ci].1 == 0 {
                ci += 1;
            }
        }
        debug_assert_eq!(di, debtors.len());
        debug_assert_eq!(ci, creditors.len());
    }

    let cert = MultilateralNettingCertificate {
        gross_legs: gross_legs.to_vec(),
        net_legs,
    };
    let _ = cert.verify()?;
    Ok(cert)
}

impl MultilateralNettingCertificate {
    /// Microsecond exact conservation & exposure-reduction verifier (`checkMultilateralNetting_sound`).
    pub fn verify(&self) -> Result<VerifiedNettingSummary, ClearingError> {
        let mut parties = BTreeSet::new();
        let mut assets = BTreeSet::new();
        let mut gross_map: BTreeMap<(u32, u32), i128> = BTreeMap::new();
        let mut net_map: BTreeMap<(u32, u32), i128> = BTreeMap::new();
        let mut gross_vol = 0u128;
        let mut net_vol = 0u128;

        for (idx, leg) in self.gross_legs.iter().enumerate() {
            if leg.amount == 0 || leg.payer == leg.payee {
                return Err(ClearingError::InvalidSettlementLeg { idx });
            }
            parties.insert(leg.payer);
            parties.insert(leg.payee);
            assets.insert(leg.asset);
            gross_vol = gross_vol
                .checked_add(leg.amount as u128)
                .ok_or(ClearingError::ArithmeticOverflow)?;
            let amt = leg.amount as i128;
            let e_out = gross_map.entry((leg.party_payer(), leg.asset)).or_insert(0);
            *e_out = checked_sub_i128(*e_out, amt)?;
            let e_in = gross_map.entry((leg.payee, leg.asset)).or_insert(0);
            *e_in = checked_add_i128(*e_in, amt)?;
        }

        for (idx, leg) in self.net_legs.iter().enumerate() {
            if leg.amount == 0 || leg.payer == leg.payee {
                return Err(ClearingError::InvalidSettlementLeg { idx });
            }
            parties.insert(leg.payer);
            parties.insert(leg.payee);
            assets.insert(leg.asset);
            net_vol = net_vol
                .checked_add(leg.amount as u128)
                .ok_or(ClearingError::ArithmeticOverflow)?;
            let amt = leg.amount as i128;
            let e_out = net_map.entry((leg.payer, leg.asset)).or_insert(0);
            *e_out = checked_sub_i128(*e_out, amt)?;
            let e_in = net_map.entry((leg.payee, leg.asset)).or_insert(0);
            *e_in = checked_add_i128(*e_in, amt)?;
        }

        if net_vol > gross_vol {
            return Err(ClearingError::GrossVolumeInflated { net_vol, gross_vol });
        }

        for &asset in &assets {
            let mut global_sum = 0i128;
            for &party in &parties {
                let g = *gross_map.get(&(party, asset)).unwrap_or(&0);
                let n = *net_map.get(&(party, asset)).unwrap_or(&0);
                if n != g {
                    return Err(ClearingError::NetBalanceMismatch {
                        party,
                        asset,
                        net: n,
                        gross: g,
                    });
                }
                global_sum = checked_add_i128(global_sum, n)?;
            }
            if global_sum != 0 {
                return Err(ClearingError::GlobalConservationViolation {
                    asset,
                    sum: global_sum,
                });
            }
        }

        Ok(VerifiedNettingSummary {
            num_parties: parties.len(),
            num_assets: assets.len(),
            gross_leg_count: self.gross_legs.len(),
            net_leg_count: self.net_legs.len(),
            gross_volume: gross_vol,
            net_volume: net_vol,
        })
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(DBNET_MAGIC);
        out.extend_from_slice(&WIRE_VERSION_V1.to_le_bytes());
        out.extend_from_slice(&(self.gross_legs.len() as u32).to_le_bytes());
        for l in &self.gross_legs {
            out.extend_from_slice(&l.payer.to_le_bytes());
            out.extend_from_slice(&l.payee.to_le_bytes());
            out.extend_from_slice(&l.asset.to_le_bytes());
            out.extend_from_slice(&l.amount.to_le_bytes());
        }
        out.extend_from_slice(&(self.net_legs.len() as u32).to_le_bytes());
        for l in &self.net_legs {
            out.extend_from_slice(&l.payer.to_le_bytes());
            out.extend_from_slice(&l.payee.to_le_bytes());
            out.extend_from_slice(&l.asset.to_le_bytes());
            out.extend_from_slice(&l.amount.to_le_bytes());
        }
        let mut h = Sha256::new();
        h.update(b"DBNET001_WIRE_TAG|");
        h.update(&out);
        let tag: [u8; 32] = h.finalize().into();
        out.extend_from_slice(&tag);
        out
    }

    pub fn from_wire_bytes_and_verify(
        bytes: &[u8],
    ) -> Result<(Self, VerifiedNettingSummary), ClearingError> {
        if bytes.len() < 8 + 4 + 4 + 4 + 32 {
            return Err(ClearingError::InvalidWireFormat(
                "DBNET001 truncated".into(),
            ));
        }
        let (body, tag_slice) = bytes.split_at(bytes.len() - 32);
        let mut h = Sha256::new();
        h.update(b"DBNET001_WIRE_TAG|");
        h.update(body);
        let want: [u8; 32] = h.finalize().into();
        if tag_slice != want {
            return Err(ClearingError::ChecksumMismatch);
        }
        let mut cur = ByteReader::new(body);
        if cur.take(8).map_err(ClearingError::InvalidWireFormat)? != DBNET_MAGIC {
            return Err(ClearingError::InvalidWireFormat(
                "bad DBNET001 magic".into(),
            ));
        }
        if cur.read_u32().map_err(ClearingError::InvalidWireFormat)? != WIRE_VERSION_V1 {
            return Err(ClearingError::InvalidWireFormat(
                "bad DBNET001 version".into(),
            ));
        }
        let read_legs = |c: &mut ByteReader<'_>| -> Result<Vec<SettlementLeg>, ClearingError> {
            let cnt = c.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
            if cnt > (1 << 20) {
                return Err(ClearingError::InvalidWireFormat("DBNET001 leg cap".into()));
            }
            let mut legs = Vec::with_capacity(cnt);
            for _ in 0..cnt {
                let payer = c.read_u32().map_err(ClearingError::InvalidWireFormat)?;
                let payee = c.read_u32().map_err(ClearingError::InvalidWireFormat)?;
                let asset = c.read_u32().map_err(ClearingError::InvalidWireFormat)?;
                let amount = c.read_u64().map_err(ClearingError::InvalidWireFormat)?;
                legs.push(SettlementLeg {
                    payer,
                    payee,
                    asset,
                    amount,
                });
            }
            Ok(legs)
        };
        let gross_legs = read_legs(&mut cur)?;
        let net_legs = read_legs(&mut cur)?;
        if !cur.is_eof() {
            return Err(ClearingError::InvalidWireFormat(
                "DBNET001 trailing bytes".into(),
            ));
        }
        let cert = MultilateralNettingCertificate {
            gross_legs,
            net_legs,
        };
        let summary = cert.verify()?;
        Ok((cert, summary))
    }
}

impl SettlementLeg {
    #[inline]
    fn party_payer(&self) -> u32 {
        self.payer
    }
}

// ================================================================================================
// §3. `NoSingleViewer >= 2` Encrypted Submissions (`WhirPcs61` + `D1b` LogUp-GKR) & $t$-of-$n$ BFV
// ================================================================================================

/// Public intake policy for encrypted submissions (Call-Auction Demand/Supply Curves & Private `{0,1}` Ballots).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SubmissionSpec {
    /// Slots `0..num_ticks` hold buy quantities in `[0, max_qty_per_tick]`,
    /// slots `num_ticks..2*num_ticks` hold sell quantities in `[0, max_qty_per_tick]`,
    /// slots `2*num_ticks..N` equal `0`.
    DemandSupplyCurve {
        num_ticks: usize,
        tick_prices: Vec<i64>,
        max_qty_per_tick: u32,
    },
    /// Slots `0..num_choices` hold `{0, 1}` binary votes with `min_votes <= sum_{j < C} m_j <= max_votes`,
    /// slots `num_choices..N` equal `0` (kills `privacy-voting` `10^6` and `t - 1` tally forgery!).
    BinaryBallot {
        num_choices: usize,
        min_votes: u32,
        max_votes: u32,
    },
}

impl SubmissionSpec {
    pub fn validate_for_params(
        &self,
        params: &HoistedParams,
    ) -> Result<(usize, u32, u32), ClearingError> {
        let n = params.n;
        let q_mod_t = (&params.q_big % BigUint::from(params.t))
            .to_u64()
            .unwrap_or(u64::MAX);
        match self {
            SubmissionSpec::DemandSupplyCurve {
                num_ticks,
                tick_prices,
                max_qty_per_tick,
            } => {
                if *num_ticks == 0
                    || tick_prices.len() != *num_ticks
                    || 2 * (*num_ticks) > n
                    || *max_qty_per_tick == 0
                    || *max_qty_per_tick > 65_535
                {
                    return Err(ClearingError::InvalidSubmissionProof(
                        "invalid DemandSupplyCurve spec".into(),
                    ));
                }
                if 2u128 * (q_mod_t as u128) * (*max_qty_per_tick as u128) >= (params.t as u128) {
                    return Err(ClearingError::InvalidSubmissionProof(
                        "params (Q mod t) * max_qty_per_tick exceeds linear encode_round regime"
                            .into(),
                    ));
                }
                Ok((2 * (*num_ticks), *max_qty_per_tick, 0))
            }
            SubmissionSpec::BinaryBallot {
                num_choices,
                min_votes,
                max_votes,
            } => {
                if *num_choices == 0
                    || *num_choices > n
                    || *min_votes > *max_votes
                    || (*max_votes as usize) > *num_choices
                    || *max_votes > 65_535
                {
                    return Err(ClearingError::InvalidSubmissionProof(
                        "invalid BinaryBallot spec".into(),
                    ));
                }
                Ok((*num_choices, 1, *max_votes - *min_votes))
            }
        }
    }

    pub fn spec_digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"DARK_CLEARING_SPEC_V1|");
        match self {
            SubmissionSpec::DemandSupplyCurve {
                num_ticks,
                tick_prices,
                max_qty_per_tick,
            } => {
                h.update([1u8]);
                h.update((*num_ticks as u32).to_le_bytes());
                h.update(max_qty_per_tick.to_le_bytes());
                for &p in tick_prices {
                    h.update(p.to_le_bytes());
                }
            }
            SubmissionSpec::BinaryBallot {
                num_choices,
                min_votes,
                max_votes,
            } => {
                h.update([2u8]);
                h.update((*num_choices as u32).to_le_bytes());
                h.update(min_votes.to_le_bytes());
                h.update(max_votes.to_le_bytes());
            }
        }
        h.finalize().into()
    }
}

/// Joint threshold public key `pk = (b, a)` in coefficient and NTT forms, with precomputed
/// 38-bit split constants and `Ntt` over `p_0 = qp[0]` so both prover and verifier run in `O(N log N)`.
#[derive(Clone)]
pub struct DarkCommitteePubKey {
    pub rns_q: Arc<Rns>,
    pub b_coeff: Vec<u64>, // 3 * N
    pub a_coeff: Vec<u64>, // 3 * N
    pub pk0_ntt: Vec<u64>,
    pub pk1_ntt: Vec<u64>,
    pub delta_mod_q: [u64; 3],
    pub ntt_p0: Arc<Ntt>,
    pub pk_digest: [u8; 32],
    b_rev_lo_ntt: [Vec<u64>; 3],
    b_rev_hi_ntt: [Vec<u64>; 3],
    a_rev_lo_ntt: [Vec<u64>; 3],
    a_rev_hi_ntt: [Vec<u64>; 3],
}

fn build_rev_neg_split_ntt(p0: u64, ntt_p0: &Ntt, poly_q: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let n = poly_q.len();
    let mut rev_lo = vec![0u64; n];
    let mut rev_hi = vec![0u64; n];
    rev_lo[0] = (poly_q[0] & SPLIT_MASK) % p0;
    rev_hi[0] = (poly_q[0] >> SPLIT_BITS) % p0;
    for t in 1..n {
        let src = poly_q[n - t];
        let lo = (src & SPLIT_MASK) % p0;
        let hi = (src >> SPLIT_BITS) % p0;
        rev_lo[t] = if lo == 0 { 0 } else { p0 - lo };
        rev_hi[t] = if hi == 0 { 0 } else { p0 - hi };
    }
    ntt_p0.forward(&mut rev_lo);
    ntt_p0.forward(&mut rev_hi);
    (rev_lo, rev_hi)
}

impl DarkCommitteePubKey {
    pub fn from_coeffs(
        params: &HoistedParams,
        rns_q: Arc<Rns>,
        b_coeff: Vec<u64>,
        a_coeff: Vec<u64>,
    ) -> Self {
        let n = params.n;
        let p0 = params.qp[0];
        let ntt_p0 = Arc::new(Ntt::new(p0, n));
        let mut pk0_ntt = b_coeff.clone();
        let mut pk1_ntt = a_coeff.clone();
        rns_q.fwd(&mut pk0_ntt);
        rns_q.fwd(&mut pk1_ntt);

        let mut delta_mod_q = [0u64; 3];
        rns_q.encode_round(1, &mut delta_mod_q);

        let b_splits: [(Vec<u64>, Vec<u64>); 3] = std::array::from_fn(|k| {
            build_rev_neg_split_ntt(p0, &ntt_p0, &b_coeff[k * n..(k + 1) * n])
        });
        let a_splits: [(Vec<u64>, Vec<u64>); 3] = std::array::from_fn(|k| {
            build_rev_neg_split_ntt(p0, &ntt_p0, &a_coeff[k * n..(k + 1) * n])
        });

        let mut h = Sha256::new();
        h.update(b"DARK_COMMITTEE_PK_V1|");
        h.update((n as u32).to_le_bytes());
        h.update(params.t.to_le_bytes());
        for &q in &params.qp {
            h.update(q.to_le_bytes());
        }
        for &v in b_coeff.iter().chain(a_coeff.iter()) {
            h.update(v.to_le_bytes());
        }
        let pk_digest: [u8; 32] = h.finalize().into();

        DarkCommitteePubKey {
            rns_q,
            b_coeff,
            a_coeff,
            pk0_ntt,
            pk1_ntt,
            delta_mod_q,
            ntt_p0,
            pk_digest,
            b_rev_lo_ntt: std::array::from_fn(|k| b_splits[k].0.clone()),
            b_rev_hi_ntt: std::array::from_fn(|k| b_splits[k].1.clone()),
            a_rev_lo_ntt: std::array::from_fn(|k| a_splits[k].0.clone()),
            a_rev_hi_ntt: std::array::from_fn(|k| a_splits[k].1.clone()),
        }
    }

    /// Compute `rev_neg(P_split) ⊛ v_pow mod p_0` in `O(N log N)` using precomputed NTT of `rev_neg(P_split)`.
    fn transpose_conv_p0(&self, rev_split_ntt: &[u64], v_ntt: &[u64], p0: u64) -> Vec<u64> {
        let mut prod: Vec<u64> = rev_split_ntt
            .iter()
            .zip(v_ntt.iter())
            .map(|(&x, &y)| mulmod(x, y, p0))
            .collect();
        self.ntt_p0.inverse(&mut prod);
        prod
    }
}

/// Canonical SHA-256 handle of a 2-component BFV ciphertext `Ct`.
pub fn bfv_ct_handle(params: &HoistedParams, ct: &Ct) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARK_CLEARING_CT2_V1|");
    h.update((params.n as u32).to_le_bytes());
    for &q in &params.qp {
        h.update(q.to_le_bytes());
    }
    for &v in ct.c0.iter().chain(ct.c1.iter()) {
        h.update(v.to_le_bytes());
    }
    h.finalize().into()
}

/// Zero-leakage `WhirPcs61` + `D1b` `LogUpGkrProof` validity proof for an encrypted submission (`DBWHIR61`).
#[derive(Clone, Debug)]
pub struct BfvSubmissionWhirProof61 {
    pub mr: u8,
    pub mc: u8,
    pub t_queries: u16,
    pub blow: u8,
    pub pcs_root: [u8; 32],
    pub logup_proof: LogUpGkrProof,
    pub whir_opening: WhirOpeningBundle61,
}

/// Encrypted bidder/voter submission bundle `(epoch, nullifier, ct, proof)`.
#[derive(Clone)]
pub struct EncryptedSubmission61 {
    pub epoch: u64,
    pub nullifier: [u8; 32],
    pub ct: Ct,
    pub ct_handle: [u8; 32],
    pub proof: BfvSubmissionWhirProof61,
}

#[derive(Clone)]
struct AffineLookupDesc {
    const_offset: u64,
    slot: usize,
}

fn build_submission_lookup_descs(p0: u64, max_val: u32, max_slack: u32) -> Vec<AffineLookupDesc> {
    let mut descs = Vec::with_capacity(23);
    // Slot 0: u in [-1, 1] -> (u + 1) in [0, 2]
    descs.push(AffineLookupDesc {
        const_offset: 1,
        slot: 0,
    });
    descs.push(AffineLookupDesc {
        const_offset: (1u64 << 20) - 2,
        slot: 0,
    });
    // Slot 1 & 2: e0, e1 in [-8, 8] -> (e + 8) in [0, 16]
    for slot in [1usize, 2usize] {
        descs.push(AffineLookupDesc {
            const_offset: 8,
            slot,
        });
        descs.push(AffineLookupDesc {
            const_offset: (1u64 << 20) - 9,
            slot,
        });
    }
    // Slot 3: m in [0, max_val]
    descs.push(AffineLookupDesc {
        const_offset: 0,
        slot: 3,
    });
    descs.push(AffineLookupDesc {
        const_offset: ((1u64 << 20) - 1 - (max_val as u64)) % p0,
        slot: 3,
    });
    // Slot 4: slack in [0, max_slack]
    descs.push(AffineLookupDesc {
        const_offset: 0,
        slot: 4,
    });
    descs.push(AffineLookupDesc {
        const_offset: ((1u64 << 20) - 1 - (max_slack as u64)) % p0,
        slot: 4,
    });
    // Slots 5..17: w0[0..3], w1[0..3], carry0[0..3], carry1[0..3] in [-2^18, 3*2^18)
    for slot in 5..17 {
        descs.push(AffineLookupDesc {
            const_offset: W_CARRY_BIAS as u64,
            slot,
        });
    }
    // Slot 17: uniform [0, 2^20) blinding column for LogUp-GKR `leaf_payload_eval`
    descs.push(AffineLookupDesc {
        const_offset: 0,
        slot: 17,
    });
    descs
}

fn submission_statement_digest(
    pk_digest: &[u8; 32],
    spec_digest: &[u8; 32],
    epoch: u64,
    nullifier: &[u8; 32],
    ct_handle: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARK_SUBMISSION_STMT_V1|");
    h.update(pk_digest);
    h.update(spec_digest);
    h.update(epoch.to_le_bytes());
    h.update(nullifier);
    h.update(ct_handle);
    h.finalize().into()
}

fn derive_logup_context(stmt_digest: &[u8; 32], pcs_root: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARK_SUBMISSION_LOGUP_CTX_V1|");
    h.update(stmt_digest);
    h.update(pcs_root);
    h.finalize().into()
}

fn derive_bfv_eval_challenges(
    fp0: &FastPrime61,
    stmt_digest: &[u8; 32],
    pcs_root: &[u8; 32],
    mult_comm: &[u8; 32],
) -> [u64; 3] {
    std::array::from_fn(|s| {
        let mut h = Sha256::new();
        h.update(b"DARK_SUBMISSION_BFV_CHAL_V1|");
        h.update(stmt_digest);
        h.update(pcs_root);
        h.update(mult_comm);
        h.update((s as u32).to_le_bytes());
        let d: [u8; 32] = h.finalize().into();
        fp0.red128(u128::from_le_bytes(d[0..16].try_into().unwrap()))
    })
}

fn build_eq_le_fp(fp: &FastPrime61, z: &[u64]) -> Vec<u64> {
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

fn extract_submission_logup_points(
    fp: &FastPrime61,
    proof: &LogUpGkrProof,
    context_digest: &[u8; 32],
) -> Result<(Vec<Vec<u64>>, Vec<u64>), ClearingError> {
    let c = proof.config.num_challenges();
    let mut tr_state: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_D1B_GKR|LOGUP_RANGE20");
        h.update(fp.p.to_le_bytes());
        h.update(context_digest);
        h.finalize().into()
    };
    let absorb_u64s = |st: &mut [u8; 32], vals: &[u64]| {
        let mut h = Sha256::new();
        h.update(*st);
        for &v in vals {
            h.update(v.to_le_bytes());
        }
        *st = h.finalize().into();
    };
    let absorb_bytes = |st: &mut [u8; 32], data: &[u8]| {
        let mut h = Sha256::new();
        h.update(*st);
        h.update(data);
        *st = h.finalize().into();
    };
    let squeeze_fp = |st: &mut [u8; 32], tag: u64| -> u64 {
        let mut h = Sha256::new();
        h.update(*st);
        h.update(b"CHAL");
        h.update(tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        *st = out;
        fp.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
    };
    let fork_sub = |st: &[u8; 32], label: &str, idx: u64| -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(st);
        h.update(b"SUB|");
        h.update(label.as_bytes());
        h.update(idx.to_le_bytes());
        h.finalize().into()
    };

    absorb_u64s(&mut tr_state, &[proof.total_lookups as u64, c as u64]);
    absorb_bytes(&mut tr_state, &proof.mult_commitment);
    for ell in 0..c {
        let _ = squeeze_fp(&mut tr_state, ell as u64);
    }

    let replay_tree =
        |mut st: [u8; 32], t_prf: &FractionTreeProof| -> Result<Vec<u64>, ClearingError> {
            for r in &t_prf.roots {
                absorb_u64s(&mut st, r);
            }
            if t_prf.depth == 0 {
                return Ok(Vec::new());
            }
            for v in &t_prf.layer1_vals {
                absorb_u64s(&mut st, v);
            }
            let z0 = squeeze_fp(&mut st, 1);
            let mut z_pt = vec![z0];
            for (idx, layer) in t_prf.layers.iter().enumerate() {
                let k = idx + 1;
                for ell in 0..c {
                    let _ = squeeze_fp(&mut st, 100 + ell as u64);
                }
                for ell in 0..c {
                    let _ = squeeze_fp(&mut st, 200 + ell as u64);
                }
                let mut r_vars = Vec::with_capacity(k);
                for (round, poly) in layer.sumcheck_rounds.iter().enumerate() {
                    absorb_u64s(&mut st, poly);
                    r_vars.push(squeeze_fp(&mut st, 1000 + round as u64));
                }
                for ce in &layer.child_evals {
                    absorb_u64s(&mut st, ce);
                }
                let r_child = squeeze_fp(&mut st, 2000 + k as u64);
                let mut z_next = Vec::with_capacity(k + 1);
                z_next.push(r_child);
                z_next.extend_from_slice(&r_vars);
                z_pt = z_next;
            }
            absorb_u64s(&mut st, &[t_prf.leaf_payload_eval]);
            Ok(z_pt)
        };

    let mut wit_zs = Vec::with_capacity(proof.witness_trees.len());
    for (b_idx, w_prf) in proof.witness_trees.iter().enumerate() {
        wit_zs.push(replay_tree(
            fork_sub(&tr_state, "WIT_TREE", b_idx as u64),
            w_prf,
        )?);
    }
    let z_tab = replay_tree(fork_sub(&tr_state, "TAB_TREE", 0), &proof.table_tree)?;
    Ok((wit_zs, z_tab))
}

#[allow(clippy::too_many_arguments)]
fn build_submission_whir_claims(
    params: &HoistedParams,
    pk: &DarkCommitteePubKey,
    spec: &SubmissionSpec,
    active_slots: usize,
    descs: &[AffineLookupDesc],
    ct: &Ct,
    r_chals: &[u64; 3],
    logup_proof: &LogUpGkrProof,
    wit_zs: &[Vec<u64>],
    z_tab: &[u64],
) -> Result<(Vec<Vec<u64>>, Vec<SlotLinearClaim>), ClearingError> {
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = &params.fp[0];
    let p0 = fp0.p;
    let two38 = (1u64 << SPLIT_BITS) % p0;
    let neg_two38 = fp0.neg(two38);

    let mut v_families: Vec<Vec<u64>> = Vec::new();
    let mut claims: Vec<SlotLinearClaim> = Vec::new();

    // Pre-split `c0` and `c1` into 38-bit low/high limbs:
    let mut c0_lo = vec![0u64; 3 * n];
    let mut c0_hi = vec![0u64; 3 * n];
    let mut c1_lo = vec![0u64; 3 * n];
    let mut c1_hi = vec![0u64; 3 * n];
    for idx in 0..(3 * n) {
        c0_lo[idx] = (ct.c0[idx] & SPLIT_MASK) % p0;
        c0_hi[idx] = (ct.c0[idx] >> SPLIT_BITS) % p0;
        c1_lo[idx] = (ct.c1[idx] & SPLIT_MASK) % p0;
        c1_hi[idx] = (ct.c1[idx] >> SPLIT_BITS) % p0;
    }

    for &r_s in r_chals {
        let mut v_pow = Vec::with_capacity(n);
        let mut cur = 1u64;
        for _ in 0..n {
            v_pow.push(cur);
            cur = fp0.mul(cur, r_s);
        }
        let mut v_ntt = v_pow.clone();
        pk.ntt_p0.forward(&mut v_ntt);
        let vf_pow_idx = v_families.len();
        v_families.push(v_pow);

        for k in 0..3 {
            let qk = params.qp[k];
            let q_lo = (qk & SPLIT_MASK) % p0;
            let q_hi = (qk >> SPLIT_BITS) % p0;
            let neg_q_lo = fp0.neg(q_lo);
            let neg_q_hi = fp0.neg(q_hi);

            let d_lo = (pk.delta_mod_q[k] & SPLIT_MASK) % p0;
            let d_hi = (pk.delta_mod_q[k] >> SPLIT_BITS) % p0;

            let ub_lo = pk.transpose_conv_p0(&pk.b_rev_lo_ntt[k], &v_ntt, p0);
            let ub_hi = pk.transpose_conv_p0(&pk.b_rev_hi_ntt[k], &v_ntt, p0);
            let ua_lo = pk.transpose_conv_p0(&pk.a_rev_lo_ntt[k], &v_ntt, p0);
            let ua_hi = pk.transpose_conv_p0(&pk.a_rev_hi_ntt[k], &v_ntt, p0);

            let idx_ub_lo = v_families.len();
            v_families.push(ub_lo);
            let idx_ub_hi = v_families.len();
            v_families.push(ub_hi);
            let idx_ua_lo = v_families.len();
            v_families.push(ua_lo);
            let idx_ua_hi = v_families.len();
            v_families.push(ua_hi);

            let v_ref = &v_families[vf_pow_idx];
            let rhs_c0_lo = fp0.dot(v_ref, &c0_lo[k * n..(k + 1) * n]);
            let rhs_c0_hi = fp0.dot(v_ref, &c0_hi[k * n..(k + 1) * n]);
            let rhs_c1_lo = fp0.dot(v_ref, &c1_lo[k * n..(k + 1) * n]);
            let rhs_c1_hi = fp0.dot(v_ref, &c1_hi[k * n..(k + 1) * n]);

            // 1. c0_k low equation:
            claims.push(SlotLinearClaim {
                terms: vec![
                    (idx_ub_lo, vec![(0, 1)]),
                    (
                        vf_pow_idx,
                        vec![(1, 1), (3, d_lo), (5 + k, neg_q_lo), (11 + k, neg_two38)],
                    ),
                ],
                rhs: rhs_c0_lo,
            });
            // 2. c0_k high equation:
            claims.push(SlotLinearClaim {
                terms: vec![
                    (idx_ub_hi, vec![(0, 1)]),
                    (vf_pow_idx, vec![(3, d_hi), (5 + k, neg_q_hi), (11 + k, 1)]),
                ],
                rhs: rhs_c0_hi,
            });
            // 3. c1_k low equation:
            claims.push(SlotLinearClaim {
                terms: vec![
                    (idx_ua_lo, vec![(0, 1)]),
                    (
                        vf_pow_idx,
                        vec![(2, 1), (8 + k, neg_q_lo), (14 + k, neg_two38)],
                    ),
                ],
                rhs: rhs_c1_lo,
            });
            // 4. c1_k high equation:
            claims.push(SlotLinearClaim {
                terms: vec![
                    (idx_ua_hi, vec![(0, 1)]),
                    (vf_pow_idx, vec![(8 + k, neg_q_hi), (14 + k, 1)]),
                ],
                rhs: rhs_c1_hi,
            });
        }
    }

    // Tail zero-sum claim on inactive plaintext slots `active_slots..N`:
    if active_slots < n {
        let mut tail_ones = vec![0u64; n];
        for v in &mut tail_ones[active_slots..n] {
            *v = 1;
        }
        let idx_tail = v_families.len();
        v_families.push(tail_ones);
        claims.push(SlotLinearClaim::single_vec(idx_tail, vec![(3, 1)], 0));
    }

    // BinaryBallot vote-count sum `<1_{[0, C)}, m> + <e_0, slack> == max_votes`:
    if let SubmissionSpec::BinaryBallot {
        num_choices,
        max_votes,
        ..
    } = spec
    {
        let mut head_ones = vec![0u64; n];
        for v in &mut head_ones[..*num_choices] {
            *v = 1;
        }
        let mut e0_vec = vec![0u64; n];
        e0_vec[0] = 1;
        let idx_head = v_families.len();
        v_families.push(head_ones);
        let idx_e0 = v_families.len();
        v_families.push(e0_vec);
        claims.push(SlotLinearClaim {
            terms: vec![(idx_head, vec![(3, 1)]), (idx_e0, vec![(4, 1)])],
            rhs: (*max_votes as u64) % p0,
        });
    }

    // LogUp-GKR Stage-1 (`MonolithicC4`: 1 witness tree) & Table-tree MLE binding claims:
    if logup_proof.config != LogUpConfig::MonolithicC4
        || logup_proof.witness_trees.len() != 1
        || wit_zs.len() != 1
    {
        return Err(ClearingError::InvalidSubmissionProof(
            "expected MonolithicC4 single witness tree".into(),
        ));
    }
    let w_prf = &logup_proof.witness_trees[0];
    if w_prf.active_len != descs.len() * n {
        return Err(ClearingError::InvalidSubmissionProof(
            "LogUp witness active_len mismatch".into(),
        ));
    }
    let zw = &wit_zs[0];
    if zw.len() < log_n || z_tab.len() != TABLE_LOG2 {
        return Err(ClearingError::InvalidSubmissionProof(
            "LogUp terminal point dimension mismatch".into(),
        ));
    }
    let idx_zw_lo = v_families.len();
    v_families.push(build_eq_le_fp(fp0, &zw[..log_n]));
    let eq_hi = build_eq_le_fp(fp0, &zw[log_n..]);
    let mut const_acc = 0u64;
    let mut slot_map: BTreeMap<usize, u64> = BTreeMap::new();
    for (s, desc) in descs.iter().enumerate() {
        let w_hi = eq_hi[s];
        const_acc = fp0.add(const_acc, fp0.mul(w_hi, desc.const_offset));
        let entry = slot_map.entry(desc.slot).or_insert(0);
        *entry = fp0.add(*entry, w_hi);
    }
    claims.push(SlotLinearClaim::single_vec(
        idx_zw_lo,
        slot_map.into_iter().collect(),
        fp0.sub(w_prf.leaf_payload_eval, const_acc),
    ));

    let mult_slots = TABLE_SIZE / n;
    let idx_ztab_lo = v_families.len();
    v_families.push(build_eq_le_fp(fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp(fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots).map(|s| (18 + s, eq_tab_hi[s])).collect();
    claims.push(SlotLinearClaim::single_vec(
        idx_ztab_lo,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    Ok((v_families, claims))
}

fn sample_ternary_vec(n: usize, rng: &mut PcsRng) -> Vec<i64> {
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let blk = rng.next_block();
        for &b in &blk {
            if out.len() == n {
                break;
            }
            if b < 255 {
                out.push((b % 3) as i64 - 1);
            }
        }
    }
    out
}

fn sample_bounded_i64_vec(n: usize, rng: &mut PcsRng, bound: i64) -> Vec<i64> {
    let span = (2 * bound + 1) as u64;
    let limit = (u64::MAX / span) * span;
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let blk = rng.next_block();
        for ch in blk.chunks_exact(8) {
            if out.len() == n {
                break;
            }
            let u = u64::from_le_bytes(ch.try_into().unwrap());
            if u < limit {
                out.push((u % span) as i64 - bound);
            }
        }
    }
    out
}

fn negacyclic_conv_u64_i64_exact(
    poly_q: &[u64],
    u_signed: &[i64],
    qk: u64,
    ntt_k: &Ntt,
) -> Vec<i128> {
    // Wait: `|(poly_q ⊛ u)_j| <= N * q_k ~ 8192 * 2^61 ~ 2^74` overflows a single 61-bit modulus!
    // Compute `(poly_q ⊛ u)_j` over exact `i128` via two 31-bit halves (`poly_lo`, `poly_hi`) each convolved
    // in `O(N log N)` via `ntt_k` (`8192 * 2^31 = 2^44 << q_k / 2` -> 0 wrap, 100% exact `O(N log N)`!).
    let n = poly_q.len();
    let half_q = qk / 2;
    let mut p_lo: Vec<u64> = poly_q.iter().map(|&v| v & 0x7FFF_FFFF).collect();
    let mut p_hi: Vec<u64> = poly_q.iter().map(|&v| v >> 31).collect();
    let mut u_ntt: Vec<u64> = u_signed.iter().map(|&x| from_i64(x, qk)).collect();
    ntt_k.forward(&mut p_lo);
    ntt_k.forward(&mut p_hi);
    ntt_k.forward(&mut u_ntt);
    let mut c_lo: Vec<u64> = p_lo
        .iter()
        .zip(&u_ntt)
        .map(|(&a, &b)| mulmod(a, b, qk))
        .collect();
    let mut c_hi: Vec<u64> = p_hi
        .iter()
        .zip(&u_ntt)
        .map(|(&a, &b)| mulmod(a, b, qk))
        .collect();
    ntt_k.inverse(&mut c_lo);
    ntt_k.inverse(&mut c_hi);

    let centered = |v: u64| -> i128 {
        if v > half_q {
            -((qk - v) as i128)
        } else {
            v as i128
        }
    };
    (0..n)
        .map(|j| centered(c_lo[j]) + (centered(c_hi[j]) << 31))
        .collect()
}

/// Encrypt a bidder's demand/supply vector or a voter's `{0, 1}` ballot under `pk` and generate a
/// zero-leakage `WhirPcs61` (`192` queries, `130.1b` UD) + `D1b` `LogUpGkrProof` validity bundle.
pub fn encrypt_and_prove_submission_whir(
    params: &HoistedParams,
    pk: &DarkCommitteePubKey,
    spec: &SubmissionSpec,
    epoch: u64,
    nullifier: [u8; 32],
    plaintext: &[u64],
    rng: &mut PcsRng,
) -> Result<EncryptedSubmission61, ClearingError> {
    let n = params.n;
    if plaintext.len() != n {
        return Err(ClearingError::DimensionMismatch(
            "plaintext len != N".into(),
        ));
    }
    let (active_slots, max_val, _max_slack) = spec.validate_for_params(params)?;
    for (j, &v) in plaintext.iter().enumerate() {
        if j >= active_slots && v != 0 {
            return Err(ClearingError::InvalidSubmissionProof(
                "non-zero inactive slot in honest prover".into(),
            ));
        }
        if v > (max_val as u64) {
            return Err(ClearingError::InvalidSubmissionProof(
                "plaintext slot exceeds spec bound in honest prover".into(),
            ));
        }
    }
    let mut slack_slot = vec![0u64; n];
    if let SubmissionSpec::BinaryBallot {
        num_choices,
        min_votes,
        max_votes,
    } = spec
    {
        let sum_votes: u64 = plaintext[..*num_choices].iter().sum();
        if sum_votes < (*min_votes as u64) || sum_votes > (*max_votes as u64) {
            return Err(ClearingError::InvalidSubmissionProof(
                "ballot vote sum outside [min_votes, max_votes]".into(),
            ));
        }
        slack_slot[0] = (*max_votes as u64) - sum_votes;
    }

    let u = sample_ternary_vec(n, rng);
    let e0 = sample_bounded_i64_vec(n, rng, 8);
    let e1 = sample_bounded_i64_vec(n, rng, 8);

    prove_submission_from_raw_witness(
        params,
        pk,
        spec,
        epoch,
        nullifier,
        &plaintext.iter().map(|&v| v as i64).collect::<Vec<_>>(),
        &slack_slot,
        &u,
        &e0,
        &e1,
        rng,
    )
}

/// Low-level prover taking signed `plaintext_signed: &[i64]` (`-1` encodes `t - 1` in BFV and `p_0 - 1`
/// in `F_{p_0}`) and explicit `(slack_slot, u, e0, e1)`, allowing adversarial soundness tests to satisfy
/// all linear `F_{p_0}` equations via modular wrap-around while testing `LogUp-GKR` range rejection.
#[allow(clippy::too_many_arguments)]
pub fn prove_submission_from_raw_witness(
    params: &HoistedParams,
    pk: &DarkCommitteePubKey,
    spec: &SubmissionSpec,
    epoch: u64,
    nullifier: [u8; 32],
    plaintext_signed: &[i64],
    slack_slot: &[u64],
    u: &[i64],
    e0: &[i64],
    e1: &[i64],
    rng: &mut PcsRng,
) -> Result<EncryptedSubmission61, ClearingError> {
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];
    let p0 = fp0.p;
    let (active_slots, max_val, max_slack) = spec.validate_for_params(params)?;

    let mut u_ntt = pk.rns_q.from_signed(u);
    pk.rns_q.fwd(&mut u_ntt);
    let mut c0 = pk.rns_q.mul_pw(&pk.pk0_ntt, &u_ntt);
    let mut c1 = pk.rns_q.mul_pw(&pk.pk1_ntt, &u_ntt);
    pk.rns_q.inv(&mut c0);
    pk.rns_q.inv(&mut c1);

    let mut enc = [0u64; 3];
    for j in 0..n {
        let m_mod_t = (plaintext_signed[j] as i128).rem_euclid(pk.rns_q.t as i128) as u64;
        pk.rns_q.encode_round(m_mod_t, &mut enc);
        for (k, &qk) in params.qp.iter().enumerate() {
            let idx = k * n + j;
            c0[idx] = addmod(addmod(c0[idx], from_i64(e0[j], qk), qk), enc[k], qk);
            c1[idx] = addmod(c1[idx], from_i64(e1[j], qk), qk);
        }
    }
    let ct = Ct { c0, c1 };
    let ct_handle = bfv_ct_handle(params, &ct);

    // Compute exact integer quotients `w0_k, w1_k` and 38-bit split carries `carry0_k, carry1_k`:
    let mult_slots = TABLE_SIZE / n;
    let total_slots = 18 + mult_slots;
    let mut flat_data = vec![0u64; total_slots * n];

    for j in 0..n {
        flat_data[j] = from_i64(u[j], p0);
        flat_data[n + j] = from_i64(e0[j], p0);
        flat_data[2 * n + j] = from_i64(e1[j], p0);
        flat_data[3 * n + j] = from_i64(plaintext_signed[j], p0);
        flat_data[4 * n + j] = slack_slot[j] % p0;
    }

    for k in 0..3 {
        let qk = params.qp[k];
        let qk_i128 = qk as i128;
        let q_lo = (qk & SPLIT_MASK) as i128;
        let dk_i128 = pk.delta_mod_q[k] as i128;
        let d_lo = (pk.delta_mod_q[k] & SPLIT_MASK) as i128;

        let b_slice = &pk.b_coeff[k * n..(k + 1) * n];
        let a_slice = &pk.a_coeff[k * n..(k + 1) * n];
        let b_lo_vec: Vec<u64> = b_slice.iter().map(|&v| v & SPLIT_MASK).collect();
        let a_lo_vec: Vec<u64> = a_slice.iter().map(|&v| v & SPLIT_MASK).collect();

        let bu_full = negacyclic_conv_u64_i64_exact(b_slice, u, qk, &pk.rns_q.ntts[k]);
        let au_full = negacyclic_conv_u64_i64_exact(a_slice, u, qk, &pk.rns_q.ntts[k]);
        let bu_lo = negacyclic_conv_u64_i64_exact(&b_lo_vec, u, qk, &pk.rns_q.ntts[k]);
        let au_lo = negacyclic_conv_u64_i64_exact(&a_lo_vec, u, qk, &pk.rns_q.ntts[k]);

        for j in 0..n {
            let c0_kj = ct.c0[k * n + j];
            let c1_kj = ct.c1[k * n + j];
            let mj = plaintext_signed[j] as i128;
            let num0 = bu_full[j] + (e0[j] as i128) + dk_i128 * mj - (c0_kj as i128);
            let num1 = au_full[j] + (e1[j] as i128) - (c1_kj as i128);
            let w0 = num0.div_euclid(qk_i128) as i64;
            let w1 = num1.div_euclid(qk_i128) as i64;

            let low0 = bu_lo[j] + (e0[j] as i128) + d_lo * mj
                - ((c0_kj & SPLIT_MASK) as i128)
                - q_lo * (w0 as i128);
            let low1 =
                au_lo[j] + (e1[j] as i128) - ((c1_kj & SPLIT_MASK) as i128) - q_lo * (w1 as i128);
            let carry0 = (low0 >> SPLIT_BITS) as i64;
            let carry1 = (low1 >> SPLIT_BITS) as i64;

            flat_data[(5 + k) * n + j] = from_i64(w0, p0);
            flat_data[(8 + k) * n + j] = from_i64(w1, p0);
            flat_data[(11 + k) * n + j] = from_i64(carry0, p0);
            flat_data[(14 + k) * n + j] = from_i64(carry1, p0);
        }
    }

    // Slot 17: fresh uniform `[0, 2^20)` blinding entries for `LogUpGkrProof` Stage-1 MLE:
    for j in 0..n {
        let blk = rng.next_block();
        let u32_val = u32::from_le_bytes(blk[0..4].try_into().unwrap());
        flat_data[17 * n + j] = (u32_val as u64) & ((TABLE_SIZE as u64) - 1);
    }

    let descs = build_submission_lookup_descs(p0, max_val, max_slack);
    let mut lookup_entries = vec![0u64; descs.len() * n];
    for (d_idx, desc) in descs.iter().enumerate() {
        let src = &flat_data[desc.slot * n..(desc.slot + 1) * n];
        let dst = &mut lookup_entries[d_idx * n..(d_idx + 1) * n];
        for j in 0..n {
            dst[j] = fp0.add(src[j], desc.const_offset);
        }
    }

    let mults = match count_multiplicities_parallel(&lookup_entries) {
        Ok(m) => m,
        Err(_) => {
            // Only reached when adversarial caller injects out-of-range witnesses to test soundness:
            let mut fallback = vec![0u64; TABLE_SIZE];
            fallback[0] = lookup_entries.len() as u64;
            fallback
        }
    };
    for s in 0..mult_slots {
        flat_data[(18 + s) * n..(18 + s + 1) * n].copy_from_slice(&mults[s * n..(s + 1) * n]);
    }

    let shape = WhirShape61::for_len(
        &fp0,
        flat_data.len(),
        log_n.max(9),
        WHIR_T_QUERIES_128,
        WHIR_BLOWUP,
    );
    let pcs = WhirCommittedPcs61::commit_with_shape(fp0, shape, &flat_data, rng.clone());

    let spec_digest = spec.spec_digest();
    let stmt_digest =
        submission_statement_digest(&pk.pk_digest, &spec_digest, epoch, &nullifier, &ct_handle);
    let logup_ctx = derive_logup_context(&stmt_digest, &pcs.root);
    let logup_proof = prove_logup_gkr_with_mults(
        &fp0,
        &lookup_entries,
        &mults,
        LogUpConfig::MonolithicC4,
        &logup_ctx,
    );

    let (wit_zs, z_tab) = extract_submission_logup_points(&fp0, &logup_proof, &logup_ctx)?;
    let r_chals =
        derive_bfv_eval_challenges(&fp0, &stmt_digest, &pcs.root, &logup_proof.mult_commitment);
    let (v_families, claims) = build_submission_whir_claims(
        params,
        pk,
        spec,
        active_slots,
        &descs,
        &ct,
        &r_chals,
        &logup_proof,
        &wit_zs,
        &z_tab,
    )?;

    let whir_opening = pcs.open_whir_slot_claims(log_n, &v_families, &claims, &logup_ctx);
    Ok(EncryptedSubmission61 {
        epoch,
        nullifier,
        ct,
        ct_handle,
        proof: BfvSubmissionWhirProof61 {
            mr: pcs.shape.mr as u8,
            mc: pcs.shape.mc as u8,
            t_queries: pcs.shape.t_queries as u16,
            blow: pcs.shape.blow as u8,
            pcs_root: pcs.root,
            logup_proof,
            whir_opening,
        },
    })
}

/// Standalone zero-witness verifier for `EncryptedSubmission61` (`WhirPcs61` + `D1b` LogUp-GKR).
pub fn verify_encrypted_submission_whir(
    params: &HoistedParams,
    pk: &DarkCommitteePubKey,
    spec: &SubmissionSpec,
    expected_epoch: u64,
    sub: &EncryptedSubmission61,
) -> Result<(), ClearingError> {
    if sub.epoch != expected_epoch {
        return Err(ClearingError::EpochReplayOrStale {
            got: sub.epoch,
            latch: expected_epoch,
        });
    }
    let n = params.n;
    if sub.ct.c0.len() != 3 * n || sub.ct.c1.len() != 3 * n {
        return Err(ClearingError::DimensionMismatch(
            "ciphertext RNS limb len".into(),
        ));
    }
    for k in 0..3 {
        let qk = params.qp[k];
        for j in 0..n {
            if sub.ct.c0[k * n + j] >= qk || sub.ct.c1[k * n + j] >= qk {
                return Err(ClearingError::InvalidSubmissionProof(
                    "non-canonical ciphertext residue >= q_k".into(),
                ));
            }
        }
    }
    let actual_handle = bfv_ct_handle(params, &sub.ct);
    if actual_handle != sub.ct_handle {
        return Err(ClearingError::InvalidSubmissionProof(
            "ct_handle mismatch".into(),
        ));
    }

    let (active_slots, max_val, max_slack) = spec.validate_for_params(params)?;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = &params.fp[0];

    if (sub.proof.t_queries as usize) < WHIR_T_QUERIES_128
        || (sub.proof.blow as usize) != WHIR_BLOWUP
        || (sub.proof.mc as usize) < log_n.max(8)
        || (sub.proof.mr as usize) < 3
    {
        return Err(ClearingError::InvalidSubmissionProof(
            "WHIR security parameters below 128-bit floor".into(),
        ));
    }

    let shape = WhirShape61::from_mr_mc(
        fp0,
        sub.proof.mr as usize,
        sub.proof.mc as usize,
        sub.proof.t_queries as usize,
        sub.proof.blow as usize,
    );
    let needed_cells = (18 + TABLE_SIZE / n) * n;
    if shape.usable_rows * shape.c < needed_cells {
        return Err(ClearingError::InvalidSubmissionProof(
            "WHIR matrix capacity smaller than witness+table slots".into(),
        ));
    }

    let spec_digest = spec.spec_digest();
    let stmt_digest = submission_statement_digest(
        &pk.pk_digest,
        &spec_digest,
        sub.epoch,
        &sub.nullifier,
        &sub.ct_handle,
    );
    let logup_ctx = derive_logup_context(&stmt_digest, &sub.proof.pcs_root);

    // 1. Verify `D1b` LogUp-GKR fraction-tree sumcheck & root balance (`MonolithicC4`, `>= 128b`):
    verify_logup_gkr(fp0, &sub.proof.logup_proof, &logup_ctx, None)
        .map_err(ClearingError::InvalidSubmissionProof)?;

    // 2. Reconstruct all BFV 3-prime + spec + LogUp Stage-1/Table `SlotLinearClaim`s and verify `WhirPcs61`:
    let descs = build_submission_lookup_descs(fp0.p, max_val, max_slack);
    let (wit_zs, z_tab) = extract_submission_logup_points(fp0, &sub.proof.logup_proof, &logup_ctx)?;
    let r_chals = derive_bfv_eval_challenges(
        fp0,
        &stmt_digest,
        &sub.proof.pcs_root,
        &sub.proof.logup_proof.mult_commitment,
    );
    let (v_families, claims) = build_submission_whir_claims(
        params,
        pk,
        spec,
        active_slots,
        &descs,
        &sub.ct,
        &r_chals,
        &sub.proof.logup_proof,
        &wit_zs,
        &z_tab,
    )?;

    verify_whir_pcs61(
        fp0,
        &shape,
        &sub.proof.pcs_root,
        log_n,
        &v_families,
        &claims,
        &logup_ctx,
        &sub.proof.whir_opening,
    )
    .map_err(ClearingError::InvalidSubmissionProof)
}

impl BfvSubmissionWhirProof61 {
    /// Canonical `DBWHIR61` binary wire serialization (`0` raw witness evaluations).
    pub fn to_wire_bytes(&self, p0: u64) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(DBWHIR_MAGIC);
        out.extend_from_slice(&WIRE_VERSION_V1.to_le_bytes());
        out.push(self.mr);
        out.push(self.mc);
        out.extend_from_slice(&self.t_queries.to_le_bytes());
        out.push(self.blow);
        out.extend_from_slice(&self.pcs_root);

        // Serialize `LogUpGkrProof` compactly:
        out.extend_from_slice(&(self.logup_proof.total_lookups as u32).to_le_bytes());
        out.extend_from_slice(&self.logup_proof.mult_commitment);
        out.push(self.logup_proof.witness_trees.len() as u8);
        let write_tree = |dst: &mut Vec<u8>, t: &FractionTreeProof| {
            dst.push(t.depth as u8);
            dst.extend_from_slice(&(t.active_len as u32).to_le_bytes());
            dst.push(t.roots.len() as u8);
            let mut flat = Vec::new();
            for r in &t.roots {
                flat.extend_from_slice(r);
            }
            for l1 in &t.layer1_vals {
                flat.extend_from_slice(l1);
            }
            dst.push(t.layers.len() as u8);
            for ly in &t.layers {
                dst.push(ly.sumcheck_rounds.len() as u8);
                for sc in &ly.sumcheck_rounds {
                    flat.extend_from_slice(sc);
                }
                for ce in &ly.child_evals {
                    flat.extend_from_slice(ce);
                }
            }
            flat.push(t.leaf_payload_eval);
            pack_u64_bits_le(&flat, 61, dst);
        };
        for wt in &self.logup_proof.witness_trees {
            write_tree(&mut out, wt);
        }
        write_tree(&mut out, &self.logup_proof.table_tree);

        self.whir_opening.to_bytes(p0, &mut out);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8], p0: u64) -> Result<Self, ClearingError> {
        let mut cur = ByteReader::new(bytes);
        if cur.take(8).map_err(ClearingError::InvalidWireFormat)? != DBWHIR_MAGIC {
            return Err(ClearingError::InvalidWireFormat(
                "bad DBWHIR61 magic".into(),
            ));
        }
        if cur.read_u32().map_err(ClearingError::InvalidWireFormat)? != WIRE_VERSION_V1 {
            return Err(ClearingError::InvalidWireFormat(
                "bad DBWHIR61 version".into(),
            ));
        }
        let mr = cur.read_u8().map_err(ClearingError::InvalidWireFormat)?;
        let mc = cur.read_u8().map_err(ClearingError::InvalidWireFormat)?;
        let t_queries = cur.read_u16().map_err(ClearingError::InvalidWireFormat)?;
        let blow = cur.read_u8().map_err(ClearingError::InvalidWireFormat)?;
        let pcs_root = cur.read_hash().map_err(ClearingError::InvalidWireFormat)?;
        let total_lookups = cur.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
        let mult_commitment = cur.read_hash().map_err(ClearingError::InvalidWireFormat)?;
        let n_wt = cur.read_u8().map_err(ClearingError::InvalidWireFormat)? as usize;
        if n_wt == 0 || n_wt > 32 {
            return Err(ClearingError::InvalidWireFormat(
                "bad witness_trees count".into(),
            ));
        }
        let read_tree = |c: &mut ByteReader<'_>| -> Result<FractionTreeProof, ClearingError> {
            let depth = c.read_u8().map_err(ClearingError::InvalidWireFormat)? as usize;
            let active_len = c.read_u32().map_err(ClearingError::InvalidWireFormat)? as usize;
            let n_ch = c.read_u8().map_err(ClearingError::InvalidWireFormat)? as usize;
            let n_ly = c.read_u8().map_err(ClearingError::InvalidWireFormat)? as usize;
            let mut sc_lens = Vec::with_capacity(n_ly);
            for _ in 0..n_ly {
                sc_lens.push(c.read_u8().map_err(ClearingError::InvalidWireFormat)? as usize);
            }
            let flat =
                unpack_u64_bits_le(c, 61, 1 << 16, p0).map_err(ClearingError::InvalidWireFormat)?;
            let mut pos = 0usize;
            let need = |p: usize, k: usize, tot: usize| -> Result<(), ClearingError> {
                if p + k > tot {
                    Err(ClearingError::InvalidWireFormat(
                        "tree flat underflow".into(),
                    ))
                } else {
                    Ok(())
                }
            };
            let mut roots = Vec::with_capacity(n_ch);
            for _ in 0..n_ch {
                need(pos, 2, flat.len())?;
                roots.push([flat[pos], flat[pos + 1]]);
                pos += 2;
            }
            let mut layer1_vals = Vec::with_capacity(if depth > 0 { n_ch } else { 0 });
            if depth > 0 {
                for _ in 0..n_ch {
                    need(pos, 4, flat.len())?;
                    layer1_vals.push([flat[pos], flat[pos + 1], flat[pos + 2], flat[pos + 3]]);
                    pos += 4;
                }
            }
            let mut layers = Vec::with_capacity(n_ly);
            for &sl in &sc_lens {
                let mut sumcheck_rounds = Vec::with_capacity(sl);
                for _ in 0..sl {
                    need(pos, 4, flat.len())?;
                    sumcheck_rounds.push([flat[pos], flat[pos + 1], flat[pos + 2], flat[pos + 3]]);
                    pos += 4;
                }
                let mut child_evals = Vec::with_capacity(n_ch);
                for _ in 0..n_ch {
                    need(pos, 4, flat.len())?;
                    child_evals.push([flat[pos], flat[pos + 1], flat[pos + 2], flat[pos + 3]]);
                    pos += 4;
                }
                layers.push(GkrLayerProof {
                    sumcheck_rounds,
                    child_evals,
                });
            }
            need(pos, 1, flat.len())?;
            let leaf_payload_eval = flat[pos];
            if pos + 1 != flat.len() {
                return Err(ClearingError::InvalidWireFormat(
                    "tree flat trailing".into(),
                ));
            }
            Ok(FractionTreeProof {
                depth,
                active_len,
                roots,
                layer1_vals,
                layers,
                leaf_payload_eval,
            })
        };
        let mut witness_trees = Vec::with_capacity(n_wt);
        for _ in 0..n_wt {
            witness_trees.push(read_tree(&mut cur)?);
        }
        let table_tree = read_tree(&mut cur)?;
        let whir_opening = WhirOpeningBundle61::from_bytes(&mut cur, p0)
            .map_err(ClearingError::InvalidWireFormat)?;
        if !cur.is_eof() {
            return Err(ClearingError::InvalidWireFormat(
                "DBWHIR61 trailing bytes".into(),
            ));
        }
        Ok(BfvSubmissionWhirProof61 {
            mr,
            mc,
            t_queries,
            blow,
            pcs_root,
            logup_proof: LogUpGkrProof {
                config: LogUpConfig::MonolithicC4,
                total_lookups,
                mult_commitment,
                witness_trees,
                table_tree,
            },
            whir_opening,
        })
    }
}

// ------------------------------------------------------------------------------------------------
// Dealerless `NoSingleViewer >= 2` $t$-of-$n$ Threshold BFV Committee + `C8` Handle & Epoch Gates
// ------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HandleRole {
    /// Verified individual submission (`ct + ct` input only; NEVER threshold-opened!).
    IndividualSubmission { epoch: u64 },
    /// Verified homomorphic batch aggregate (`>= 1` verified submissions; eligible for 1 epoch opening).
    BatchAggregate { epoch: u64, count: usize },
}

/// Authenticated opening authorization binding `(epoch, spec_digest, aggregate_handle, signers)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpeningAuthorization {
    pub epoch: u64,
    pub spec_digest: [u8; 32],
    pub aggregate_handle: [u8; 32],
    pub signer_custodians: Vec<usize>,
    pub auth_digest: [u8; 32],
}

impl OpeningAuthorization {
    pub fn new(
        epoch: u64,
        spec_digest: [u8; 32],
        aggregate_handle: [u8; 32],
        mut signer_custodians: Vec<usize>,
    ) -> Self {
        signer_custodians.sort_unstable();
        signer_custodians.dedup();
        let mut h = Sha256::new();
        h.update(b"DARK_OPENING_AUTH_V1|");
        h.update(epoch.to_le_bytes());
        h.update(spec_digest);
        h.update(aggregate_handle);
        for &id in &signer_custodians {
            h.update((id as u32).to_le_bytes());
        }
        let auth_digest: [u8; 32] = h.finalize().into();
        OpeningAuthorization {
            epoch,
            spec_digest,
            aggregate_handle,
            signer_custodians,
            auth_digest,
        }
    }
}

/// Smudged Shamir partial-decryption share `d_i = sk_shamir_i * c_1 + e_{smudge, i} mod Q`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdDecryptionShare {
    pub custodian_id: usize,
    pub epoch: u64,
    pub aggregate_handle: [u8; 32],
    pub share_rns: Vec<u64>, // 3 * N
}

/// Single custodian shard inside a `NoSingleViewer >= 2` $t$-of-$n$ committee.
pub struct CustodianShard {
    pub id: usize,
    sk_shamir_ntt: Vec<u64>, // Shamir share F(id + 1) in Qp NTT form
    admitted_handles: BTreeMap<[u8; 32], HandleRole>,
    epoch_latch: u64,
}

/// `NoSingleViewer >= 2` dealerless $t$-of-$n$ threshold clearing/tally committee.
pub struct DarkClearingCommittee {
    pub params: HoistedParams,
    pub threshold: usize,
    pub num_custodians: usize,
    pub clearing_factorial: u64, // (num_custodians - 1)! coprime to t
    pub pk: DarkCommitteePubKey,
    pub shards: Vec<CustodianShard>,
    used_nullifiers: HashSet<[u8; 32]>,
    verified_pool: BTreeMap<u64, Vec<Ct>>,
    aggregate_cts: BTreeMap<[u8; 32], (u64, Ct)>,
}

fn sample_uniform_rq_limbs(rns: &Rns, rng: &mut PcsRng) -> Vec<u64> {
    let n = rns.n;
    let mut out = vec![0u64; 3 * n];
    let q_bits = rns.q_big.bits() as usize;
    let byte_len = q_bits.div_ceil(8);
    for j in 0..n {
        loop {
            let mut raw = Vec::with_capacity(byte_len);
            while raw.len() < byte_len {
                raw.extend_from_slice(&rng.next_block());
            }
            raw.truncate(byte_len);
            let excess = byte_len * 8 - q_bits;
            if excess > 0 {
                *raw.last_mut().unwrap() &= (1u8 << (8 - excess)) - 1;
            }
            let cand = BigUint::from_bytes_le(&raw);
            if cand < rns.q_big {
                for k in 0..3 {
                    let rem = (&cand % BigUint::from(rns.qs[k])).to_u64().unwrap();
                    out[k * n + j] = rem;
                }
                break;
            }
        }
    }
    out
}

fn sample_smudge_110_rns(rns: &Rns, rng: &mut PcsRng) -> Vec<u64> {
    // Sample `e_j in [-2^110, +2^110)` (`> 70`-bit TVD drowning on `M <= 4096` homomorphic sums,
    // while `|(n - 1)! * e_agg + sum |\tilde{\lambda}| * 2^110| < 2^129 << 2^149.98 = Q / (2t)`!).
    let n = rns.n;
    let mut out = vec![0u64; 3 * n];
    for j in 0..n {
        let blk = rng.next_block();
        let raw128 = u128::from_le_bytes(blk[0..16].try_into().unwrap()) & ((1u128 << 111) - 1);
        let signed: i128 = (raw128 as i128) - (1i128 << 110);
        for k in 0..3 {
            let qk = rns.qs[k] as i128;
            let m = signed.rem_euclid(qk) as u64;
            out[k * n + j] = m;
        }
    }
    out
}

impl DarkClearingCommittee {
    /// Dealerless $t$-of-$n$ Shamir keygen ceremony over `R_Q`:
    /// Hard-rejects `threshold < 2` (`NoSingleViewer >= 2` invariant!).
    pub fn setup(
        params: HoistedParams,
        threshold: usize,
        num_custodians: usize,
    ) -> Result<Self, ClearingError> {
        if threshold < 2 {
            return Err(ClearingError::ThresholdPolicyViolation(
                "NoSingleViewer invariant requires threshold >= 2".into(),
            ));
        }
        if threshold > num_custodians || num_custodians > 16 {
            return Err(ClearingError::ThresholdPolicyViolation(
                "invalid (threshold, num_custodians) pair".into(),
            ));
        }
        let clearing_factorial: u64 = (1..=(num_custodians.saturating_sub(1) as u64)).product();
        if clearing_factorial.gcd(&params.t) != 1 {
            return Err(ClearingError::ThresholdPolicyViolation(
                "(num_custodians - 1)! is not coprime to plaintext prime t".into(),
            ));
        }

        let rns_q = Arc::new(Rns::new(params.n, &params.qp, params.t));
        let n = params.n;
        let mut crs_rng = PcsRng::from_os();
        let a_coeff = sample_uniform_rq_limbs(&rns_q, &mut crs_rng);
        let mut a_ntt = a_coeff.clone();
        rns_q.fwd(&mut a_ntt);

        let mut b_joint = vec![0u64; 3 * n];
        let mut point_shares = vec![vec![0u64; 3 * n]; num_custodians];

        for _dealer in 0..num_custodians {
            let mut p_rng = PcsRng::from_os();
            let s_p = sample_ternary_vec(n, &mut p_rng);
            let e_p = sample_bounded_i64_vec(n, &mut p_rng, 8);

            let s_p_rns = rns_q.from_signed(&s_p);
            let mut s_p_ntt = s_p_rns.clone();
            rns_q.fwd(&mut s_p_ntt);
            let mut as_prod = rns_q.mul_pw(&a_ntt, &s_p_ntt);
            rns_q.inv(&mut as_prod);

            for (j, &ej) in e_p.iter().enumerate() {
                for (k, &qk) in params.qp.iter().enumerate() {
                    let idx = k * n + j;
                    let b_pj = submod(0, addmod(as_prod[idx], from_i64(ej, qk), qk), qk);
                    b_joint[idx] = addmod(b_joint[idx], b_pj, qk);
                }
            }

            // Degree-(threshold - 1) Shamir polynomial `F^{(p)}(X) = s_p + sum_{d=1}^{t-1} r_d X^d` over `R_Q`:
            let mut poly_coeffs = Vec::with_capacity(threshold);
            poly_coeffs.push(s_p_rns);
            for _ in 1..threshold {
                poly_coeffs.push(sample_uniform_rq_limbs(&rns_q, &mut p_rng));
            }
            for (recv, recv_shares) in point_shares.iter_mut().enumerate() {
                let x_eval = (recv + 1) as u64;
                for (k, &qk) in params.qp.iter().enumerate() {
                    for j in 0..n {
                        let idx = k * n + j;
                        let mut acc = 0u64;
                        for poly in poly_coeffs.iter().rev() {
                            acc = addmod(mulmod(acc, x_eval, qk), poly[idx], qk);
                        }
                        recv_shares[idx] = addmod(recv_shares[idx], acc, qk);
                    }
                }
            }
        }

        let pk = DarkCommitteePubKey::from_coeffs(&params, rns_q.clone(), b_joint, a_coeff);
        let shards = point_shares
            .into_iter()
            .enumerate()
            .map(|(id, mut sk_shamir_ntt)| {
                rns_q.fwd(&mut sk_shamir_ntt);
                CustodianShard {
                    id,
                    sk_shamir_ntt,
                    admitted_handles: BTreeMap::new(),
                    epoch_latch: 0,
                }
            })
            .collect();

        Ok(DarkClearingCommittee {
            params,
            threshold,
            num_custodians,
            clearing_factorial,
            pk,
            shards,
            used_nullifiers: HashSet::new(),
            verified_pool: BTreeMap::new(),
            aggregate_cts: BTreeMap::new(),
        })
    }

    /// Verify a bidder/voter's `WhirPcs61` submission proof, enforce nullifier uniqueness, and admit
    /// its `ct_handle` into each custodian's `C8` table strictly as `IndividualSubmission` (non-openable!).
    pub fn verify_and_admit_submission(
        &mut self,
        spec: &SubmissionSpec,
        epoch: u64,
        sub: &EncryptedSubmission61,
    ) -> Result<[u8; 32], ClearingError> {
        if self.used_nullifiers.contains(&sub.nullifier) {
            return Err(ClearingError::DuplicateNullifier(sub.nullifier));
        }
        verify_encrypted_submission_whir(&self.params, &self.pk, spec, epoch, sub)?;
        self.used_nullifiers.insert(sub.nullifier);
        for shard in &mut self.shards {
            shard
                .admitted_handles
                .insert(sub.ct_handle, HandleRole::IndividualSubmission { epoch });
        }
        self.verified_pool
            .entry(epoch)
            .or_default()
            .push(sub.ct.clone());
        Ok(sub.ct_handle)
    }

    /// Homomorphically sum all verified ciphertexts for `epoch` (`ct + ct` inside BFV) and register
    /// the resulting `aggregate_handle` as `BatchAggregate` in every custodian shard.
    pub fn aggregate_verified_epoch(
        &mut self,
        epoch: u64,
    ) -> Result<([u8; 32], usize), ClearingError> {
        let cts = self.verified_pool.get(&epoch).ok_or_else(|| {
            ClearingError::InvalidSubmissionProof("no verified submissions in epoch".into())
        })?;
        if cts.is_empty() {
            return Err(ClearingError::InvalidSubmissionProof(
                "empty epoch pool".into(),
            ));
        }
        let n = self.params.n;
        let mut c0_sum = vec![0u64; 3 * n];
        let mut c1_sum = vec![0u64; 3 * n];
        for ct in cts {
            let h = bfv_ct_handle(&self.params, ct);
            for shard in &self.shards {
                if shard.admitted_handles.get(&h)
                    != Some(&HandleRole::IndividualSubmission { epoch })
                {
                    return Err(ClearingError::C8UnverifiedHandle(h));
                }
            }
            for k in 0..3 {
                let qk = self.params.qp[k];
                for j in 0..n {
                    let idx = k * n + j;
                    c0_sum[idx] = addmod(c0_sum[idx], ct.c0[idx], qk);
                    c1_sum[idx] = addmod(c1_sum[idx], ct.c1[idx], qk);
                }
            }
        }
        let agg_ct = Ct {
            c0: c0_sum,
            c1: c1_sum,
        };
        let agg_handle = bfv_ct_handle(&self.params, &agg_ct);
        let count = cts.len();
        for shard in &mut self.shards {
            shard
                .admitted_handles
                .insert(agg_handle, HandleRole::BatchAggregate { epoch, count });
        }
        self.aggregate_cts.insert(agg_handle, (epoch, agg_ct));
        Ok((agg_handle, count))
    }

    /// Custodian `custodian_id` checks `C8` handle admission, rejects individual ciphertexts, enforces
    /// `signer_custodians.len() >= threshold` and strictly monotonic `epoch_latch`, and emits its smudged share.
    pub fn issue_partial_decryption_share(
        &mut self,
        custodian_id: usize,
        auth: &OpeningAuthorization,
        target_ct: &Ct,
    ) -> Result<ThresholdDecryptionShare, ClearingError> {
        if custodian_id >= self.num_custodians {
            return Err(ClearingError::ThresholdPolicyViolation(
                "bad custodian id".into(),
            ));
        }
        if auth.signer_custodians.len() < self.threshold
            || !auth.signer_custodians.contains(&custodian_id)
        {
            return Err(ClearingError::InsufficientDecryptionShares {
                got: auth.signer_custodians.len(),
                threshold: self.threshold,
            });
        }
        let actual_h = bfv_ct_handle(&self.params, target_ct);
        if actual_h != auth.aggregate_handle {
            return Err(ClearingError::C8UnverifiedHandle(actual_h));
        }

        let shard = &mut self.shards[custodian_id];
        if auth.epoch == 0 || auth.epoch <= shard.epoch_latch {
            return Err(ClearingError::EpochReplayOrStale {
                got: auth.epoch,
                latch: shard.epoch_latch,
            });
        }
        match shard.admitted_handles.get(&actual_h) {
            None => return Err(ClearingError::C8UnverifiedHandle(actual_h)),
            Some(HandleRole::IndividualSubmission { .. }) => {
                return Err(ClearingError::C8IndividualCiphertextForbidden(actual_h));
            }
            Some(HandleRole::BatchAggregate { epoch, .. }) => {
                if *epoch != auth.epoch {
                    return Err(ClearingError::EpochReplayOrStale {
                        got: auth.epoch,
                        latch: *epoch,
                    });
                }
            }
        }

        // Advance monotonic per-custodian epoch latch BEFORE releasing share:
        shard.epoch_latch = auth.epoch;

        let rns = &self.pk.rns_q;
        let n = self.params.n;
        let mut c1_ntt = target_ct.c1.clone();
        rns.fwd(&mut c1_ntt);
        let mut prod = rns.mul_pw(&shard.sk_shamir_ntt, &c1_ntt);
        rns.inv(&mut prod);

        let mut s_rng = PcsRng::from_os();
        let smudge = sample_smudge_110_rns(rns, &mut s_rng);
        for k in 0..3 {
            let qk = self.params.qp[k];
            for j in 0..n {
                let idx = k * n + j;
                prod[idx] = addmod(prod[idx], smudge[idx], qk);
            }
        }

        Ok(ThresholdDecryptionShare {
            custodian_id,
            epoch: auth.epoch,
            aggregate_handle: actual_h,
            share_rns: prod,
        })
    }

    /// Combine `>= threshold` Shamir partial-decryption shares via integer-cleared Lagrange interpolation
    /// (`L_fact = (n - 1)!`) to recover ONLY the aggregate plaintext vector `m_agg[0..N]`.
    pub fn combine_threshold_shares(
        &self,
        aggregate_handle: &[u8; 32],
        shares: &[ThresholdDecryptionShare],
    ) -> Result<Vec<u64>, ClearingError> {
        if shares.len() < self.threshold {
            return Err(ClearingError::InsufficientDecryptionShares {
                got: shares.len(),
                threshold: self.threshold,
            });
        }
        let (_, agg_ct) = self
            .aggregate_cts
            .get(aggregate_handle)
            .ok_or(ClearingError::C8UnverifiedHandle(*aggregate_handle))?;

        let selected = &shares[..self.threshold];
        let mut seen = BTreeSet::new();
        for sh in selected {
            if sh.aggregate_handle != *aggregate_handle
                || sh.custodian_id >= self.num_custodians
                || !seen.insert(sh.custodian_id)
            {
                return Err(ClearingError::ThresholdPolicyViolation(
                    "duplicate or mismatched decryption share".into(),
                ));
            }
        }

        // Compute exact integer-cleared Lagrange coefficients `\tilde{\lambda}_{i, S} = L_fact * prod_{j != i} (-x_j)/(x_i - x_j)`:
        let l_fact = self.clearing_factorial as i128;
        let xs: Vec<i128> = selected
            .iter()
            .map(|s| (s.custodian_id + 1) as i128)
            .collect();
        let mut cleared_lambdas = Vec::with_capacity(self.threshold);
        for i in 0..self.threshold {
            let mut num = l_fact;
            let mut den = 1i128;
            for j in 0..self.threshold {
                if j != i {
                    num = checked_mul_i128(num, -xs[j])?;
                    den = checked_mul_i128(den, xs[i] - xs[j])?;
                }
            }
            debug_assert_eq!(num % den, 0);
            cleared_lambdas.push((num / den) as i64);
        }

        let n = self.params.n;
        let rns = &self.pk.rns_q;
        let mut combined = vec![0u64; 3 * n];
        for k in 0..3 {
            let qk = self.params.qp[k];
            let lf_mod_q = self.clearing_factorial % qk;
            for j in 0..n {
                let idx = k * n + j;
                let mut acc = mulmod(lf_mod_q, agg_ct.c0[idx], qk);
                for (si, sh) in selected.iter().enumerate() {
                    let lam_mod_q = from_i64(cleared_lambdas[si], qk);
                    acc = addmod(acc, mulmod(lam_mod_q, sh.share_rns[idx], qk), qk);
                }
                combined[idx] = acc;
            }
        }

        let inv_l_mod_t = invmod(self.clearing_factorial % self.params.t, self.params.t);
        let mut out = vec![0u64; n];
        for j in 0..n {
            let res = [combined[j], combined[n + j], combined[2 * n + j]];
            let scaled_m = rns.decrypt_round(&res);
            out[j] = mulmod(scaled_m, inv_l_mod_t, self.params.t);
        }
        Ok(out)
    }

    pub fn aggregate_ct(&self, handle: &[u8; 32]) -> Option<&Ct> {
        self.aggregate_cts.get(handle).map(|(_, ct)| ct)
    }
}

// ------------------------------------------------------------------------------------------------
// High-Level End-to-End Pipelines: `DarkBazaar` Clearing & Private `{0,1}` Voting Tally
// ------------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct DarkBazaarEpochReceipt {
    pub epoch: u64,
    pub num_bidders: usize,
    pub aggregate_handle: [u8; 32],
    pub aggregate_bids: Vec<u64>,
    pub aggregate_asks: Vec<u64>,
    pub auction_clearing: CertifiedAuctionClearing,
    pub netting_cert: MultilateralNettingCertificate,
    pub netting_summary: VerifiedNettingSummary,
    pub fhqpb001_wire_bytes: Vec<u8>,
    pub dbnet001_wire_bytes: Vec<u8>,
    pub kkt_verify_us: u128,
    pub netting_verify_us: u128,
}

/// Execute a complete `NoSingleViewer >= 2` `DarkBazaar` batch call-auction + multilateral netting epoch:
/// 1. Admits and `WhirPcs61`-verifies every bidder's encrypted demand/supply curve;
/// 2. Sums curves homomorphically inside BFV (`ct + ct`);
/// 3. Threshold-opens ONLY the aggregate `(agg_bids, agg_asks)` across `signer_custodians` (`>= threshold >= 2`);
/// 4. Runs the untrusted call-auction SDD-QP solver on the aggregate book + emits/verifies `FHQPB001` & `DBNET001`.
pub fn execute_dark_bazaar_clearing_epoch(
    committee: &mut DarkClearingCommittee,
    epoch: u64,
    spec: &SubmissionSpec,
    qp_cfg: &CallAuctionQpConfig,
    submissions: &[EncryptedSubmission61],
    signer_custodians: &[usize],
    gross_settlement_legs: &[SettlementLeg],
) -> Result<DarkBazaarEpochReceipt, ClearingError> {
    let k_ticks = match spec {
        SubmissionSpec::DemandSupplyCurve { num_ticks, .. } => *num_ticks,
        _ => {
            return Err(ClearingError::InvalidSubmissionProof(
                "DarkBazaar clearing requires DemandSupplyCurve spec".into(),
            ));
        }
    };

    for sub in submissions {
        committee.verify_and_admit_submission(spec, epoch, sub)?;
    }
    let (agg_handle, count) = committee.aggregate_verified_epoch(epoch)?;
    let agg_ct = committee.aggregate_ct(&agg_handle).unwrap().clone();

    let auth = OpeningAuthorization::new(
        epoch,
        spec.spec_digest(),
        agg_handle,
        signer_custodians.to_vec(),
    );
    let mut shares = Vec::with_capacity(auth.signer_custodians.len());
    for &cid in &auth.signer_custodians {
        shares.push(committee.issue_partial_decryption_share(cid, &auth, &agg_ct)?);
    }
    let opened = committee.combine_threshold_shares(&agg_handle, &shares)?;
    let aggregate_bids = opened[..k_ticks].to_vec();
    let aggregate_asks = opened[k_ticks..2 * k_ticks].to_vec();

    let auction_clearing =
        solve_certified_call_auction_qp(qp_cfg, &aggregate_bids, &aggregate_asks)?;
    let fhqpb001_wire_bytes = auction_clearing.bundle.to_wire_bytes();
    let t_kkt = Instant::now();
    let (_, _) = ExactQpCertificateBundle::from_wire_bytes_and_verify(&fhqpb001_wire_bytes)?;
    let kkt_verify_us = t_kkt.elapsed().as_micros();

    let netting_cert = compress_multilateral_legs(gross_settlement_legs)?;
    let dbnet001_wire_bytes = netting_cert.to_wire_bytes();
    let t_net = Instant::now();
    let (_, netting_summary) =
        MultilateralNettingCertificate::from_wire_bytes_and_verify(&dbnet001_wire_bytes)?;
    let netting_verify_us = t_net.elapsed().as_micros();

    Ok(DarkBazaarEpochReceipt {
        epoch,
        num_bidders: count,
        aggregate_handle: agg_handle,
        aggregate_bids,
        aggregate_asks,
        auction_clearing,
        netting_cert,
        netting_summary,
        fhqpb001_wire_bytes,
        dbnet001_wire_bytes,
        kkt_verify_us,
        netting_verify_us,
    })
}

/// Execute a complete `NoSingleViewer >= 2` private `{0, 1}` voting tally epoch, returning `tally[0..num_choices]`.
pub fn execute_private_voting_tally_epoch(
    committee: &mut DarkClearingCommittee,
    epoch: u64,
    spec: &SubmissionSpec,
    ballots: &[EncryptedSubmission61],
    signer_custodians: &[usize],
) -> Result<Vec<u64>, ClearingError> {
    let num_choices = match spec {
        SubmissionSpec::BinaryBallot { num_choices, .. } => *num_choices,
        _ => {
            return Err(ClearingError::InvalidSubmissionProof(
                "voting tally requires BinaryBallot spec".into(),
            ));
        }
    };
    for bal in ballots {
        committee.verify_and_admit_submission(spec, epoch, bal)?;
    }
    let (agg_handle, _) = committee.aggregate_verified_epoch(epoch)?;
    let agg_ct = committee.aggregate_ct(&agg_handle).unwrap().clone();
    let auth = OpeningAuthorization::new(
        epoch,
        spec.spec_digest(),
        agg_handle,
        signer_custodians.to_vec(),
    );
    let mut shares = Vec::with_capacity(auth.signer_custodians.len());
    for &cid in &auth.signer_custodians {
        shares.push(committee.issue_partial_decryption_share(cid, &auth, &agg_ct)?);
    }
    let opened = committee.combine_threshold_shares(&agg_handle, &shares)?;
    Ok(opened[..num_choices].to_vec())
}
