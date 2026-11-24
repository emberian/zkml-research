#![deny(warnings)]
//! Distributed `t < n` (`NoSingleViewer >= 2`) Hybrid-PQ Threshold BFV Custody,
//! Persist-Before-Share `C8` `OpeningAuthorization` + `WhirPcs61` Compute Gate,
//! and `GMask61`-Blinded Zero-Knowledge Partial Decryption (`G10` / `L6` R1-4 Closure).
//!
//! ### Architectural & Cryptographic Closures (`G10`)
//! 1. **Zero-Dealer `t < n` (`t >= 2`, `n > t`) Distributed Keygen & 2-Round Relin (`N = 8192`, `Qp`, `ExactGarner15`)**:
//!    - Unbiased commit-reveal CRP ceremony + enrolled Hybrid-PQ (`RFC 8032 Ed25519` + stateful
//!      `SHA-256` Merkle-Lamport PQ) authenticated confidential channel (`NoSingleViewer >= 2`);
//!    - Symmetric degree-`(t - 1)` Bivariate-VSS over `R_Q = prod_{k=0}^2 Z_{q_k}[X]/(X^N + 1)`
//!      paired with post-quantum **BDLOP Ring-LWE/SIS homomorphic row commitments**
//!      `Com(m; r_1, e_0, e_1) = (a_1 r_1 + a_2 e_1 + e_0, b_1 r_1 + e_1 + m) mod Q` (`0` elliptic-curve
//!      Pedersen / `0` Bulletproofs, sub-millisecond on `Qp` NTTs);
//!    - 2-round Mouchet et al. distributed RNS-gadget `RelinearizationKey` ceremony on `(q_0, q_1, q_2, b_0)`
//!      using per-custodian OS `/dev/urandom` CSPRNG (`DealerRelinSecret` zeroized on `Drop`).
//! 2. **Persist-Before-Share `C8` `OpeningAuthorization` + `WhirPcs61` (`DVFHEWH1`) Compute Gate**:
//!    - Refuses any partial decryption unless presented with BOTH:
//!      - (a) a `t`-quorum hybrid-PQ-signed `OpeningAuthorization` binding `(dkg_digest, epoch != 0,
//!        sequence, policy_digest, ct_commitment, compute_proof_digest, refresh_cadence)` where
//!        `tvd_40b_strict_mode` deterministically enforces `R_refresh == 1`, fsync-persisted to a
//!        hash-chained append-only disk audit log *before* secret-share access (refusing `epoch == 0`,
//!        `stale_epoch`, torn logs, and `double_open` across process restarts), AND
//!      - (b) a valid `WhirPcs61` (`DVFHEWH1`) compute proof (`verify_hoisted_whir_bytes`)!
//! 3. **`GMask61`-Blinded Partial Decryption Proof (`WhirBlindPdProof`, Retiring `PdSuccinctProof` Leak)**:
//!    - Proves `d_{i,k}(X) == lambda_{i,S,k} * c'_{1,k}(X) * s_{i,k}(X) + e_{smudge,i}(X) (mod X^N + 1, q_k)`
//!      for all `k in 0..3`, `|e_{smudge,i}|_inf <= E`, `ExactGarner15` zero-slack `[0, Q)` canonicality,
//!      and BDLOP `(T_{0,i}, T_{1,i})` transcript binding inside a single fresh `WhirCommittedPcs61` +
//!      `GMask61` + `D1b` `LogUpGkrProof`, masking the `R_PD` random-point evaluations `(s_i, e_i)` with
//!      an auxiliary committed blinding row (`TVD == 0` on `R_PD` evaluations and sumcheck rounds!).

use crate::cert::ct2_handle;
use crate::dark_block::{derive_homomorphic_state_noise_budget, os_csprng_seed32};
use crate::digits::ExactGarnerSpec;
use crate::logup_gkr::{
    count_multiplicities_parallel, prove_logup_gkr_with_mults, verify_logup_gkr, FractionTreeProof,
    GkrLayerProof, LogUpConfig, LogUpGkrProof, TABLE_LOG2, TABLE_SIZE,
};
use crate::rns_hoist::{Ct3, HoistedEngine, RelinearizationKey};
use crate::succinct_pcs::{ByteReader, PcsRng, SlotLinearClaim};
use crate::whir_pcs::{
    pack_u64_bits_le, unpack_u64_bits_le, verify_hoisted_whir_bytes, verify_whir_pcs61,
    WhirCommittedPcs61, WhirOpeningBundle61, WhirShape61, WHIR_BLOWUP, WHIR_EXTRA_EXT3_MASK_ROWS,
    WHIR_T_QUERIES_128,
};
use crate::{FastPrime61, HoistedParams};
use darkproof::owner::{self as pq_lamport, Owner as PqLamportSigner};
use darkstep::arith::{addmod, from_i64, invmod, mulmod, powmod, submod};
use darkstep::bfv::Ct;
use darkstep::rns::Rns;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};
use rayon::prelude::*;
use sha2::{Digest, Sha256, Sha512};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub const BLIND_PD_MAGIC: &[u8; 8] = b"DVFHEBPD";
pub const BLIND_PD_VERSION: u32 = 1;
const AUDIT_LOG_MAGIC: &[u8; 8] = b"DVAUDv01";
const SEALED_ENV_MAGIC: &[u8; 8] = b"DVENVv01";
const HYBRID_SIG_MAGIC: &[u8; 4] = b"HPQ1";

/// Bound on per-dealer BDLOP short randomness `|r_1|, |e_0|, |e_1| <= 8`; for `n <= 16` dealers,
/// aggregate BDLOP opening polynomials satisfy `|R_1|, |E_0|, |E_1| <= 8 * 16 = 128`.
pub const BDLOP_AGG_SHIFT: i64 = 128;
pub const BDLOP_AGG_SPAN: u64 = 257; // [-128, 128] shifted by +128 lies in [0, 256]

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThresholdCustodyError {
    InvalidThreshold {
        threshold: usize,
        n_parties: usize,
    },
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    EnrollmentMismatch(&'static str),
    HybridSignatureInvalid(&'static str),
    ConfidentialEnvelopeRefused(&'static str),
    CrpCeremonyMismatch(&'static str),
    VssRowCommitmentMismatch {
        dealer: usize,
        recipient: usize,
    },
    VssLinearImageMismatch {
        dealer: usize,
        recipient: usize,
    },
    VssBdlopOpeningMismatch {
        dealer: usize,
        recipient: usize,
    },
    VssInconsistentRows {
        dealer: usize,
        left: usize,
        right: usize,
    },
    RelinCeremonyRefused(&'static str),
    ZeroEpochRejected,
    StaleEpoch {
        got: u64,
        high_water: u64,
    },
    ConflictingSameEpochDigest {
        epoch: u64,
    },
    StrictRefreshCadenceViolation {
        got: u32,
        turns_since_refresh: u32,
    },
    PolicyDigestMismatch,
    DkgTranscriptMismatch,
    PartyNotSelected {
        party: usize,
    },
    NonCanonicalQuorumRoster,
    QuorumSignaturesInsufficient {
        have: usize,
        need: usize,
    },
    DoubleOpen,
    AuditLogPoisoned,
    AuditLogIo(String),
    CorruptedAuditLog(&'static str),
    InvalidWhirComputeProof(String),
    InvalidBlindPdProof(String),
}

impl fmt::Display for ThresholdCustodyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for ThresholdCustodyError {}

pub type Result<T> = std::result::Result<T, ThresholdCustodyError>;

// ================================================================================================
// §1. Standard RFC 8032 Ed25519 + Stateful SHA-256 Merkle-Lamport PQ Hybrid Envelope & Transport
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
struct Ed25519Consts {
    p: BigUint,
    l: BigUint,
    d: BigUint,
    two_d: BigUint,
    sqrt_m1: BigUint,
    bx: BigUint,
    by: BigUint,
}

fn ed25519_consts() -> &'static Ed25519Consts {
    static C: std::sync::OnceLock<Ed25519Consts> = std::sync::OnceLock::new();
    C.get_or_init(|| {
        let p: BigUint = (BigUint::one() << 255usize) - BigUint::from(19u32);
        let l: BigUint = (BigUint::one() << 252usize)
            + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
        let p_minus_2 = &p - BigUint::from(2u32);
        let inv_121666 = BigUint::from(121666u32).modpow(&p_minus_2, &p);
        let d = (&p - (BigUint::from(121665u32) * &inv_121666) % &p) % &p;
        let two_d = (&d << 1usize) % &p;
        let sqrt_m1 = BigUint::from(2u32).modpow(&((&p - BigUint::one()) >> 2usize), &p);

        let inv_5 = BigUint::from(5u32).modpow(&p_minus_2, &p);
        let by = (BigUint::from(4u32) * inv_5) % &p;
        let by2 = (&by * &by) % &p;
        let u = (&by2 + &p - BigUint::one()) % &p;
        let v = ((&d * &by2) % &p + BigUint::one()) % &p;
        let v3 = (&v * &v * &v) % &p;
        let v7 = (&v3 * &v3 * &v) % &p;
        let uv7 = (&u * &v7) % &p;
        let exp = (&p - BigUint::from(5u32)) >> 3usize;
        let mut bx = ((&u * &v3) % &p * uv7.modpow(&exp, &p)) % &p;
        if (&v * &bx * &bx) % &p != u {
            bx = (&bx * &sqrt_m1) % &p;
        }
        if bx.is_odd() {
            bx = &p - bx;
        }
        Ed25519Consts {
            p,
            l,
            d,
            two_d,
            sqrt_m1,
            bx,
            by,
        }
    })
}

#[derive(Clone, Debug)]
struct ExtPoint {
    x: BigUint,
    y: BigUint,
    z: BigUint,
    t: BigUint,
}

impl ExtPoint {
    fn neutral() -> Self {
        ExtPoint {
            x: BigUint::zero(),
            y: BigUint::one(),
            z: BigUint::one(),
            t: BigUint::zero(),
        }
    }

    fn base(c: &Ed25519Consts) -> Self {
        ExtPoint {
            x: c.bx.clone(),
            y: c.by.clone(),
            z: BigUint::one(),
            t: (&c.bx * &c.by) % &c.p,
        }
    }

    fn is_neutral(&self, c: &Ed25519Consts) -> bool {
        self.x.is_zero() && self.y == self.z && !self.z.is_zero() && {
            let _ = c;
            true
        }
    }

    fn eq_proj(&self, other: &Self, c: &Ed25519Consts) -> bool {
        (&self.x * &other.z) % &c.p == (&other.x * &self.z) % &c.p
            && (&self.y * &other.z) % &c.p == (&other.y * &self.z) % &c.p
    }

    /// Unified RFC 8032 §5.1.4 extended twisted Edwards addition.
    fn add(&self, rhs: &Self, c: &Ed25519Consts) -> Self {
        let p = &c.p;
        let y1_m_x1 = (&self.y + p - &self.x) % p;
        let y2_m_x2 = (&rhs.y + p - &rhs.x) % p;
        let a = (y1_m_x1 * y2_m_x2) % p;
        let b = (((&self.y + &self.x) % p) * ((&rhs.y + &rhs.x) % p)) % p;
        let cc = (((&self.t * &c.two_d) % p) * &rhs.t) % p;
        let dd = (((&self.z << 1usize) % p) * &rhs.z) % p;
        let e = (&b + p - &a) % p;
        let f = (&dd + p - &cc) % p;
        let g = (&dd + &cc) % p;
        let h = (&b + &a) % p;
        ExtPoint {
            x: (&e * &f) % p,
            y: (&g * &h) % p,
            z: (&f * &g) % p,
            t: (&e * &h) % p,
        }
    }

    fn scalar_mul(&self, scalar: &BigUint, c: &Ed25519Consts) -> Self {
        let mut res = Self::neutral();
        let mut addend = self.clone();
        let bits = scalar.bits();
        for i in 0..bits {
            if scalar.bit(i) {
                res = res.add(&addend, c);
            }
            addend = addend.add(&addend, c);
        }
        res
    }

    fn mul_by_8(&self, c: &Ed25519Consts) -> Self {
        let p2 = self.add(self, c);
        let p4 = p2.add(&p2, c);
        p4.add(&p4, c)
    }

    fn compress(&self, c: &Ed25519Consts) -> [u8; 32] {
        let z_inv = self.z.modpow(&(&c.p - BigUint::from(2u32)), &c.p);
        let x = (&self.x * &z_inv) % &c.p;
        let y = (&self.y * &z_inv) % &c.p;
        let mut out = [0u8; 32];
        let yb = y.to_bytes_le();
        out[..yb.len()].copy_from_slice(&yb);
        if x.is_odd() {
            out[31] |= 0x80;
        }
        out
    }

    fn decompress_strict(bytes: &[u8; 32], c: &Ed25519Consts) -> Option<Self> {
        let x_sign = (bytes[31] >> 7) & 1;
        let mut y_bytes = *bytes;
        y_bytes[31] &= 0x7F;
        let y = BigUint::from_bytes_le(&y_bytes);
        if y >= c.p {
            return None;
        }
        let p = &c.p;
        let y2 = (&y * &y) % p;
        let u = (&y2 + p - BigUint::one()) % p;
        let v = ((&c.d * &y2) % p + BigUint::one()) % p;
        let v3 = (&v * &v * &v) % p;
        let v7 = (&v3 * &v3 * &v) % p;
        let uv7 = (&u * &v7) % p;
        let exp = (p - BigUint::from(5u32)) >> 3usize;
        let mut x = (((&u * &v3) % p) * uv7.modpow(&exp, p)) % p;
        let vx2 = (&v * &x * &x) % p;
        if vx2 != u {
            if vx2 == (p - &u) % p {
                x = (&x * &c.sqrt_m1) % p;
            } else {
                return None;
            }
        }
        if x.is_zero() && x_sign == 1 {
            return None;
        }
        if (x.is_odd() as u8) != x_sign {
            x = p - x;
        }
        let t = (&x * &y) % p;
        Some(ExtPoint {
            x,
            y,
            z: BigUint::one(),
            t,
        })
    }
}

/// Derive canonical RFC 8032 Ed25519 public key `[u8; 32]` from a 32-byte secret seed.
pub fn ed25519_public_key_from_seed(seed: &[u8; 32]) -> [u8; 32] {
    let c = ed25519_consts();
    let h: [u8; 64] = Sha512::digest(seed).into();
    let mut s_bytes = [0u8; 32];
    s_bytes.copy_from_slice(&h[0..32]);
    s_bytes[0] &= 248;
    s_bytes[31] &= 127;
    s_bytes[31] |= 64;
    let s = BigUint::from_bytes_le(&s_bytes);
    ExtPoint::base(c).scalar_mul(&s, c).compress(c)
}

/// Standard RFC 8032 Ed25519 deterministic signature (`64` bytes).
pub fn ed25519_sign(seed: &[u8; 32], msg: &[u8]) -> [u8; 64] {
    let c = ed25519_consts();
    let h: [u8; 64] = Sha512::digest(seed).into();
    let mut s_bytes = [0u8; 32];
    s_bytes.copy_from_slice(&h[0..32]);
    s_bytes[0] &= 248;
    s_bytes[31] &= 127;
    s_bytes[31] |= 64;
    let s = BigUint::from_bytes_le(&s_bytes);
    let pk_bytes = ExtPoint::base(c).scalar_mul(&s, c).compress(c);

    let mut hr = Sha512::new();
    hr.update(&h[32..64]);
    hr.update(msg);
    let r_full: [u8; 64] = hr.finalize().into();
    let r = BigUint::from_bytes_le(&r_full) % &c.l;
    let r_bytes = ExtPoint::base(c).scalar_mul(&r, c).compress(c);

    let mut hk = Sha512::new();
    hk.update(r_bytes);
    hk.update(pk_bytes);
    hk.update(msg);
    let k_full: [u8; 64] = hk.finalize().into();
    let k = BigUint::from_bytes_le(&k_full) % &c.l;

    let s_sig = (&r + (&k * &s) % &c.l) % &c.l;
    let s_le = s_sig.to_bytes_le();
    let mut sig = [0u8; 64];
    sig[0..32].copy_from_slice(&r_bytes);
    sig[32..32 + s_le.len()].copy_from_slice(&s_le);
    sig
}

/// Strict RFC 8032 Ed25519 verification (`S < L`, canonical encodings, non-small-order `pk`, cofactored equation).
pub fn ed25519_verify_strict(pk: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    let c = ed25519_consts();
    let r_bytes: [u8; 32] = sig[0..32].try_into().unwrap();
    let s_val = BigUint::from_bytes_le(&sig[32..64]);
    if s_val >= c.l {
        return false;
    }
    let Some(a_pt) = ExtPoint::decompress_strict(pk, c) else {
        return false;
    };
    if a_pt.mul_by_8(c).is_neutral(c) {
        return false;
    }
    let Some(r_pt) = ExtPoint::decompress_strict(&r_bytes, c) else {
        return false;
    };
    let mut hk = Sha512::new();
    hk.update(r_bytes);
    hk.update(pk);
    hk.update(msg);
    let k_full: [u8; 64] = hk.finalize().into();
    let k = BigUint::from_bytes_le(&k_full) % &c.l;

    let lhs = ExtPoint::base(c).scalar_mul(&s_val, c).mul_by_8(c);
    let rhs = r_pt.add(&a_pt.scalar_mul(&k, c), c).mul_by_8(c);
    lhs.eq_proj(&rhs, c)
}

/// Public verification identity combining RFC 8032 Ed25519 + Stateful SHA-256 Merkle-Lamport PQ + DH transport key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CustodianEnrollment {
    pub party_id: usize,
    pub ed25519_pk: [u8; 32],
    pub pq_merkle_root: [u8; 32],
    pub pq_tree_height: usize,
    pub transport_dh_pk: [u8; 32],
}

impl CustodianEnrollment {
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(106);
        out.extend_from_slice(&(self.party_id as u32).to_le_bytes());
        out.extend_from_slice(&self.ed25519_pk);
        out.extend_from_slice(&self.pq_merkle_root);
        out.extend_from_slice(&(self.pq_tree_height as u16).to_le_bytes());
        out.extend_from_slice(&self.transport_dh_pk);
        out
    }
}

/// Dual-signed Classical (`RFC 8032 Ed25519`) + Post-Quantum (`SHA-256 Merkle-Lamport`) Signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridPqSignature {
    pub signer_id: usize,
    pub ed25519_sig: [u8; 64],
    pub pq_lamport_sig: Vec<u8>,
}

impl HybridPqSignature {
    pub fn to_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(HYBRID_SIG_MAGIC);
        out.extend_from_slice(&(self.signer_id as u32).to_le_bytes());
        out.extend_from_slice(&self.ed25519_sig);
        out.extend_from_slice(&(self.pq_lamport_sig.len() as u32).to_le_bytes());
        out.extend_from_slice(&self.pq_lamport_sig);
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>) -> std::result::Result<Self, String> {
        if cur.take(4)? != HYBRID_SIG_MAGIC {
            return Err("invalid HybridPqSignature magic".into());
        }
        let signer_id = cur.read_u32()? as usize;
        let ed25519_sig: [u8; 64] = cur.take(64)?.try_into().unwrap();
        let pq_len = cur.read_u32()? as usize;
        if pq_len > (1 << 16) {
            return Err("oversized PQ Lamport signature".into());
        }
        let pq_lamport_sig = cur.take(pq_len)?.to_vec();
        Ok(HybridPqSignature {
            signer_id,
            ed25519_sig,
            pq_lamport_sig,
        })
    }

    pub fn verify(
        &self,
        enrollment: &CustodianEnrollment,
        min_pq_leaf: u64,
        domain_msg: &[u8],
    ) -> Result<u64> {
        if self.signer_id != enrollment.party_id {
            return Err(ThresholdCustodyError::HybridSignatureInvalid(
                "signer_id != enrollment.party_id",
            ));
        }
        if !ed25519_verify_strict(&enrollment.ed25519_pk, domain_msg, &self.ed25519_sig) {
            return Err(ThresholdCustodyError::HybridSignatureInvalid(
                "RFC 8032 Ed25519 signature verification failed",
            ));
        }
        if !pq_lamport::verify(
            &enrollment.pq_merkle_root,
            enrollment.pq_tree_height,
            min_pq_leaf,
            domain_msg,
            &self.pq_lamport_sig,
        ) {
            return Err(ThresholdCustodyError::HybridSignatureInvalid(
                "Post-Quantum SHA-256 Merkle-Lamport signature verification failed",
            ));
        }
        Ok(pq_lamport::sig_leaf(&self.pq_lamport_sig))
    }
}

/// Private Hybrid-PQ + Transport DH Identity held by one custodian (`0` Clone, zeroized on Drop).
pub struct HybridPqCustodianIdentity {
    pub party_id: usize,
    ed25519_seed: [u8; 32],
    ed25519_pk: [u8; 32],
    pq_signer: PqLamportSigner,
    dh_scalar: BigUint,
    dh_pk: [u8; 32],
}

impl Drop for HybridPqCustodianIdentity {
    fn drop(&mut self) {
        for b in &mut self.ed25519_seed {
            unsafe { std::ptr::write_volatile(b, 0) };
        }
        self.dh_scalar = BigUint::zero();
    }
}

impl HybridPqCustodianIdentity {
    /// Generate fresh custodian identity strictly from OS `/dev/urandom` CSPRNG (`pq_height = 8` -> 256 one-time leaves).
    pub fn generate_from_os(
        party_id: usize,
        pq_height: usize,
        pq_state_path: Option<PathBuf>,
    ) -> Result<Self> {
        let ed_seed = os_csprng_seed32();
        let ed_pk = ed25519_public_key_from_seed(&ed_seed);
        let pq_seed = os_csprng_seed32().to_vec();
        if let Some(ref p) = pq_state_path {
            if let Some(parent) = p.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
            }
        }
        let pq_signer = PqLamportSigner::open(pq_height, Some(pq_seed), pq_state_path)
            .map_err(ThresholdCustodyError::AuditLogIo)?;

        let c = ed25519_consts();
        let mut dh_raw = os_csprng_seed32();
        dh_raw[0] &= 248;
        dh_raw[31] &= 63;
        dh_raw[31] |= 64;
        let dh_scalar = BigUint::from_bytes_le(&dh_raw);
        let dh_pk = ExtPoint::base(c).scalar_mul(&dh_scalar, c).compress(c);

        Ok(HybridPqCustodianIdentity {
            party_id,
            ed25519_seed: ed_seed,
            ed25519_pk: ed_pk,
            pq_signer,
            dh_scalar,
            dh_pk,
        })
    }

    pub fn enrollment(&self) -> CustodianEnrollment {
        CustodianEnrollment {
            party_id: self.party_id,
            ed25519_pk: self.ed25519_pk,
            pq_merkle_root: self.pq_signer.pk,
            pq_tree_height: self.pq_signer.h,
            transport_dh_pk: self.dh_pk,
        }
    }

    pub fn sign(&mut self, domain_msg: &[u8]) -> Result<HybridPqSignature> {
        let ed_sig = ed25519_sign(&self.ed25519_seed, domain_msg);
        let pq_sig = self.pq_signer.sign(domain_msg).map_err(|e| {
            if e.contains("exhausted") {
                ThresholdCustodyError::HybridSignatureInvalid("PQ key tree exhausted")
            } else {
                ThresholdCustodyError::AuditLogIo(e)
            }
        })?;
        Ok(HybridPqSignature {
            signer_id: self.party_id,
            ed25519_sig: ed_sig,
            pq_lamport_sig: pq_sig,
        })
    }
}

/// Enrolled committee roster (`n_parties` custodians, `threshold` `t` with `2 <= t < n_parties`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnrolledThresholdRoster {
    pub n_parties: usize,
    pub threshold: usize,
    pub enrollments: Vec<CustodianEnrollment>,
    pub roster_digest: [u8; 32],
}

impl EnrolledThresholdRoster {
    pub fn new(threshold: usize, enrollments: Vec<CustodianEnrollment>) -> Result<Self> {
        let n_parties = enrollments.len();
        if threshold < 2 || threshold >= n_parties || 2 * threshold <= n_parties {
            return Err(ThresholdCustodyError::InvalidThreshold {
                threshold,
                n_parties,
            });
        }
        let roster_digest = Self::compute_validated_digest(threshold, &enrollments)?;
        Ok(EnrolledThresholdRoster {
            n_parties,
            threshold,
            enrollments,
            roster_digest,
        })
    }

    fn compute_validated_digest(
        threshold: usize,
        enrollments: &[CustodianEnrollment],
    ) -> Result<[u8; 32]> {
        let n_parties = enrollments.len();
        if threshold < 2 || threshold >= n_parties || 2 * threshold <= n_parties {
            return Err(ThresholdCustodyError::InvalidThreshold {
                threshold,
                n_parties,
            });
        }
        let mut ed_seen = BTreeSet::new();
        let mut pq_seen = BTreeSet::new();
        let mut dh_seen = BTreeSet::new();
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_THRESHOLD_ROSTER_V1|");
        h.update((n_parties as u32).to_le_bytes());
        h.update((threshold as u32).to_le_bytes());
        for (idx, e) in enrollments.iter().enumerate() {
            if e.party_id != idx {
                return Err(ThresholdCustodyError::EnrollmentMismatch(
                    "non-canonical party_id order",
                ));
            }
            if !ed_seen.insert(e.ed25519_pk)
                || !pq_seen.insert(e.pq_merkle_root)
                || !dh_seen.insert(e.transport_dh_pk)
            {
                return Err(ThresholdCustodyError::EnrollmentMismatch(
                    "duplicate public key in roster",
                ));
            }
            h.update(e.to_wire_bytes());
        }
        Ok(h.finalize().into())
    }

    /// Re-verify threshold (`2 <= t < n` and strict majority `2t > n`), key uniqueness, and canonical `roster_digest`.
    pub fn verify_integrity(&self) -> Result<()> {
        if self.n_parties != self.enrollments.len() {
            return Err(ThresholdCustodyError::EnrollmentMismatch(
                "roster n_parties != enrollments.len()",
            ));
        }
        let want = Self::compute_validated_digest(self.threshold, &self.enrollments)?;
        if want != self.roster_digest {
            return Err(ThresholdCustodyError::EnrollmentMismatch(
                "roster_digest tamper detected",
            ));
        }
        Ok(())
    }

    /// Seal a private message from `sender` to `recipient` using ephemeral+static Edwards DH + SHA-256 stream +
    /// Encrypt-then-MAC + Hybrid-PQ signature (`NoSingleViewer`: unreadable to coordinator & other peers!).
    pub fn seal_to_peer(
        &self,
        sender_id_key: &mut HybridPqCustodianIdentity,
        recipient: usize,
        session_domain: &[u8; 32],
        sequence: u64,
        plaintext: &[u8],
    ) -> Result<Vec<u8>> {
        let sender = sender_id_key.party_id;
        if sender >= self.n_parties || recipient >= self.n_parties || sender == recipient {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "invalid sender/recipient route",
            ));
        }
        let c = ed25519_consts();
        let rec_pk = ExtPoint::decompress_strict(&self.enrollments[recipient].transport_dh_pk, c)
            .ok_or(ThresholdCustodyError::ConfidentialEnvelopeRefused(
            "invalid recipient transport DH key",
        ))?;

        let mut eph_raw = os_csprng_seed32();
        eph_raw[0] &= 248;
        eph_raw[31] &= 63;
        eph_raw[31] |= 64;
        let eph_sk = BigUint::from_bytes_le(&eph_raw);
        let eph_pk = ExtPoint::base(c).scalar_mul(&eph_sk, c).compress(c);

        let ss_eph = rec_pk.mul_by_8(c).scalar_mul(&eph_sk, c).compress(c);
        let ss_stat = rec_pk
            .mul_by_8(c)
            .scalar_mul(&sender_id_key.dh_scalar, c)
            .compress(c);

        let (enc_key, mac_key) = derive_envelope_keys(
            &self.roster_digest,
            session_domain,
            sender,
            recipient,
            sequence,
            &eph_pk,
            &ss_eph,
            &ss_stat,
        );
        let ciphertext = xor_sha256_keystream(&enc_key, plaintext);
        let mac_tag = compute_envelope_mac(
            &mac_key,
            session_domain,
            sender,
            recipient,
            sequence,
            &eph_pk,
            &ciphertext,
        );

        let mut sig_pre = Vec::new();
        sig_pre.extend_from_slice(b"DARKVFHE_SEALED_ENV_SIG_V1|");
        sig_pre.extend_from_slice(&self.roster_digest);
        sig_pre.extend_from_slice(session_domain);
        sig_pre.extend_from_slice(&(sender as u32).to_le_bytes());
        sig_pre.extend_from_slice(&(recipient as u32).to_le_bytes());
        sig_pre.extend_from_slice(&sequence.to_le_bytes());
        sig_pre.extend_from_slice(&eph_pk);
        sig_pre.extend_from_slice(&mac_tag);
        let sig = sender_id_key.sign(&sig_pre)?;

        let mut out = Vec::with_capacity(128 + ciphertext.len());
        out.extend_from_slice(SEALED_ENV_MAGIC);
        out.extend_from_slice(&(sender as u32).to_le_bytes());
        out.extend_from_slice(&(recipient as u32).to_le_bytes());
        out.extend_from_slice(&sequence.to_le_bytes());
        out.extend_from_slice(&eph_pk);
        out.extend_from_slice(&(ciphertext.len() as u32).to_le_bytes());
        out.extend_from_slice(&ciphertext);
        out.extend_from_slice(&mac_tag);
        sig.to_bytes(&mut out);
        Ok(out)
    }

    /// Authenticate Hybrid-PQ signature + MAC and decrypt a sealed peer envelope addressed to `recipient_id_key`.
    pub fn open_from_peer(
        &self,
        recipient_id_key: &HybridPqCustodianIdentity,
        expected_sender: usize,
        session_domain: &[u8; 32],
        expected_sequence: u64,
        sealed: &[u8],
    ) -> Result<Vec<u8>> {
        let recipient = recipient_id_key.party_id;
        if expected_sender >= self.n_parties
            || recipient >= self.n_parties
            || expected_sender == recipient
        {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "invalid open route",
            ));
        }
        let mut cur = ByteReader::new(sealed);
        let magic = cur
            .take(8)
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("truncated magic"))?;
        if magic != SEALED_ENV_MAGIC {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "envelope magic mismatch",
            ));
        }
        let sender = cur
            .read_u32()
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("sender"))?
            as usize;
        let rec_wire = cur
            .read_u32()
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("recipient"))?
            as usize;
        let seq_wire = cur
            .read_u64()
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("sequence"))?;
        if sender != expected_sender || rec_wire != recipient || seq_wire != expected_sequence {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "route or sequence mismatch",
            ));
        }
        let eph_pk: [u8; 32] = cur
            .take(32)
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("eph_pk"))?
            .try_into()
            .unwrap();
        let ct_len = cur
            .read_u32()
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("ct_len"))?
            as usize;
        let ciphertext = cur
            .take(ct_len)
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("ciphertext"))?;
        let mac_tag: [u8; 32] = cur
            .take(32)
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("mac_tag"))?
            .try_into()
            .unwrap();
        let sig = HybridPqSignature::from_bytes(&mut cur)
            .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("hybrid sig wire"))?;
        if !cur.is_eof() {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "trailing bytes",
            ));
        }

        let mut sig_pre = Vec::new();
        sig_pre.extend_from_slice(b"DARKVFHE_SEALED_ENV_SIG_V1|");
        sig_pre.extend_from_slice(&self.roster_digest);
        sig_pre.extend_from_slice(session_domain);
        sig_pre.extend_from_slice(&(sender as u32).to_le_bytes());
        sig_pre.extend_from_slice(&(recipient as u32).to_le_bytes());
        sig_pre.extend_from_slice(&expected_sequence.to_le_bytes());
        sig_pre.extend_from_slice(&eph_pk);
        sig_pre.extend_from_slice(&mac_tag);
        sig.verify(&self.enrollments[sender], 0, &sig_pre)?;

        let c = ed25519_consts();
        let eph_pt = ExtPoint::decompress_strict(&eph_pk, c).ok_or(
            ThresholdCustodyError::ConfidentialEnvelopeRefused("invalid ephemeral point"),
        )?;
        let sender_dh_pt =
            ExtPoint::decompress_strict(&self.enrollments[sender].transport_dh_pk, c).ok_or(
                ThresholdCustodyError::ConfidentialEnvelopeRefused("invalid sender DH point"),
            )?;
        let ss_eph = eph_pt
            .mul_by_8(c)
            .scalar_mul(&recipient_id_key.dh_scalar, c)
            .compress(c);
        let ss_stat = sender_dh_pt
            .mul_by_8(c)
            .scalar_mul(&recipient_id_key.dh_scalar, c)
            .compress(c);

        let (enc_key, mac_key) = derive_envelope_keys(
            &self.roster_digest,
            session_domain,
            sender,
            recipient,
            expected_sequence,
            &eph_pk,
            &ss_eph,
            &ss_stat,
        );
        let want_mac = compute_envelope_mac(
            &mac_key,
            session_domain,
            sender,
            recipient,
            expected_sequence,
            &eph_pk,
            ciphertext,
        );
        if want_mac != mac_tag {
            return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                "AEAD MAC authentication failed",
            ));
        }
        Ok(xor_sha256_keystream(&enc_key, ciphertext))
    }
}

#[allow(clippy::too_many_arguments)]
fn derive_envelope_keys(
    roster_digest: &[u8; 32],
    session_domain: &[u8; 32],
    sender: usize,
    recipient: usize,
    seq: u64,
    eph_pk: &[u8; 32],
    ss_eph: &[u8; 32],
    ss_stat: &[u8; 32],
) -> ([u8; 32], [u8; 32]) {
    let mut h = Sha512::new();
    h.update(b"DARKVFHE_ENV_KDF_V1|");
    h.update(roster_digest);
    h.update(session_domain);
    h.update((sender as u32).to_le_bytes());
    h.update((recipient as u32).to_le_bytes());
    h.update(seq.to_le_bytes());
    h.update(eph_pk);
    h.update(ss_eph);
    h.update(ss_stat);
    let out: [u8; 64] = h.finalize().into();
    (
        out[0..32].try_into().unwrap(),
        out[32..64].try_into().unwrap(),
    )
}

fn xor_sha256_keystream(key: &[u8; 32], input: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; input.len()];
    out.par_chunks_mut(4096)
        .enumerate()
        .for_each(|(blk_grp, dst)| {
            let src = &input[blk_grp * 4096..blk_grp * 4096 + dst.len()];
            for (sub, (d_ch, s_ch)) in dst.chunks_mut(32).zip(src.chunks(32)).enumerate() {
                let ctr = (blk_grp * 128 + sub) as u64;
                let mut h = Sha256::new();
                h.update(b"DARKVFHE_STREAM|");
                h.update(key);
                h.update(ctr.to_le_bytes());
                let ks: [u8; 32] = h.finalize().into();
                for i in 0..d_ch.len() {
                    d_ch[i] = s_ch[i] ^ ks[i];
                }
            }
        });
    out
}

fn compute_envelope_mac(
    mac_key: &[u8; 32],
    session_domain: &[u8; 32],
    sender: usize,
    recipient: usize,
    seq: u64,
    eph_pk: &[u8; 32],
    ciphertext: &[u8],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_ENV_MAC_V1|");
    h.update(mac_key);
    h.update(session_domain);
    h.update((sender as u32).to_le_bytes());
    h.update((recipient as u32).to_le_bytes());
    h.update(seq.to_le_bytes());
    h.update(eph_pk);
    h.update((ciphertext.len() as u64).to_le_bytes());
    h.update(ciphertext);
    h.finalize().into()
}

// ================================================================================================
// §2. Unbiased Commit-Reveal CRP + Bivariate-VSS + BDLOP Lattice-Anchored `t < n` DKG & Relin
// ================================================================================================

/// Unbiased 2-round commit-reveal coin contribution from one custodian (`/dev/urandom`).
pub struct CustodianCrpCoin {
    pub party_id: usize,
    coin: [u8; 32],
    salt: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrpCoinReveal {
    pub party_id: usize,
    pub coin: [u8; 32],
    pub salt: [u8; 32],
}

impl CustodianCrpCoin {
    pub fn sample_from_os(party_id: usize) -> Self {
        CustodianCrpCoin {
            party_id,
            coin: os_csprng_seed32(),
            salt: os_csprng_seed32(),
        }
    }

    pub fn commitment(&self, roster_digest: &[u8; 32]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_CRP_COMMIT_V1|");
        h.update(roster_digest);
        h.update((self.party_id as u32).to_le_bytes());
        h.update(self.coin);
        h.update(self.salt);
        h.finalize().into()
    }

    pub fn reveal(self) -> CrpCoinReveal {
        CrpCoinReveal {
            party_id: self.party_id,
            coin: self.coin,
            salt: self.salt,
        }
    }
}

pub fn finalize_unbiased_crp_seed(
    roster: &EnrolledThresholdRoster,
    commitments: &[[u8; 32]],
    reveals: &[CrpCoinReveal],
) -> Result<[u8; 32]> {
    if commitments.len() != roster.n_parties || reveals.len() != roster.n_parties {
        return Err(ThresholdCustodyError::CrpCeremonyMismatch(
            "incomplete CRP commitments/reveals",
        ));
    }
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_CRP_FINAL_SEED_V1|");
    h.update(roster.roster_digest);
    for i in 0..roster.n_parties {
        if reveals[i].party_id != i {
            return Err(ThresholdCustodyError::CrpCeremonyMismatch(
                "non-canonical reveal party order",
            ));
        }
        let mut ch = Sha256::new();
        ch.update(b"DARKVFHE_CRP_COMMIT_V1|");
        ch.update(roster.roster_digest);
        ch.update((i as u32).to_le_bytes());
        ch.update(reveals[i].coin);
        ch.update(reveals[i].salt);
        let got: [u8; 32] = ch.finalize().into();
        if got != commitments[i] {
            return Err(ThresholdCustodyError::CrpCeremonyMismatch(
                "CRP reveal does not match commitment",
            ));
        }
        h.update(reveals[i].coin);
    }
    Ok(h.finalize().into())
}

/// Public BDLOP Ring-LWE/SIS Homomorphic Commitment CRS `(a_1, a_2, b_1)` over `R_Q`:
/// `Com(m; r_1, e_0, e_1) = (a_1 * r_1 + a_2 * e_1 + e_0, b_1 * r_1 + e_1 + m) mod Q`.
#[derive(Clone)]
pub struct BdlopCrs {
    pub a1_coeff: Vec<u64>,
    pub a2_coeff: Vec<u64>,
    pub b1_coeff: Vec<u64>,
    pub a1_ntt: Vec<u64>,
    pub a2_ntt: Vec<u64>,
    pub b1_ntt: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BdlopCommitment {
    pub t0_coeff: Vec<u64>, // 3 * N residues mod Qp
    pub t1_coeff: Vec<u64>, // 3 * N residues mod Qp
}

#[derive(Clone)]
pub struct BdlopShortOpening {
    pub r1: Vec<i64>,
    pub e0: Vec<i64>,
    pub e1: Vec<i64>,
}

impl Drop for BdlopShortOpening {
    fn drop(&mut self) {
        for v in [&mut self.r1, &mut self.e0, &mut self.e1] {
            for x in v.iter_mut() {
                *x = 0;
            }
        }
    }
}

impl BdlopCrs {
    fn derive(rns_q: &Rns, crp_seed: &[u8; 32]) -> Self {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_BDLOP_CRS_V1|");
        h.update(crp_seed);
        let mut rng = PcsRng::from_seed(h.finalize().into());
        let a1_coeff = sample_uniform_rns_qp(rns_q, &mut rng);
        let a2_coeff = sample_uniform_rns_qp(rns_q, &mut rng);
        let b1_coeff = sample_uniform_rns_qp(rns_q, &mut rng);
        let mut a1_ntt = a1_coeff.clone();
        let mut a2_ntt = a2_coeff.clone();
        let mut b1_ntt = b1_coeff.clone();
        rns_q.fwd(&mut a1_ntt);
        rns_q.fwd(&mut a2_ntt);
        rns_q.fwd(&mut b1_ntt);
        BdlopCrs {
            a1_coeff,
            a2_coeff,
            b1_coeff,
            a1_ntt,
            a2_ntt,
            b1_ntt,
        }
    }

    /// Compute `Com(m_rns; r_1, e_0, e_1) = (a_1 r_1 + a_2 e_1 + e_0, b_1 r_1 + e_1 + m) mod Qp`.
    fn commit(&self, rns_q: &Rns, m_rns: &[u64], op: &BdlopShortOpening) -> BdlopCommitment {
        let n = rns_q.n;
        let mut r1_ntt = rns_q.from_signed(&op.r1);
        let mut e1_ntt = rns_q.from_signed(&op.e1);
        rns_q.fwd(&mut r1_ntt);
        rns_q.fwd(&mut e1_ntt);

        let mut t0 = rns_q.mul_pw(&self.a1_ntt, &r1_ntt);
        rns_q.mul_acc(&mut t0, &self.a2_ntt, &e1_ntt);
        rns_q.inv(&mut t0);

        let mut t1 = rns_q.mul_pw(&self.b1_ntt, &r1_ntt);
        rns_q.inv(&mut t1);

        for k in 0..3 {
            let qk = rns_q.qs[k];
            for j in 0..n {
                let idx = k * n + j;
                t0[idx] = addmod(t0[idx], from_i64(op.e0[j], qk), qk);
                t1[idx] = addmod(addmod(t1[idx], from_i64(op.e1[j], qk), qk), m_rns[idx], qk);
            }
        }
        BdlopCommitment {
            t0_coeff: t0,
            t1_coeff: t1,
        }
    }
}

/// Retained short ternary dealer contribution `s_d` for the 2-round distributed relin ceremony (`0` Clone, zeroized on Drop!).
pub struct DealerRelinSecret {
    dealer: usize,
    session_domain: [u8; 32],
    coeffs: Vec<i64>,
}

impl Drop for DealerRelinSecret {
    fn drop(&mut self) {
        for c in &mut self.coeffs {
            unsafe { std::ptr::write_volatile(c, 0) };
        }
    }
}

impl DealerRelinSecret {
    pub fn dealer(&self) -> usize {
        self.dealer
    }
}

/// Public broadcast from one dealer `d` during Bivariate-VSS `t < n` DKG.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DealerVssPublicBroadcast {
    pub dealer: usize,
    pub session_domain: [u8; 32],
    pub b_share_coeff: Vec<u64>, // 3 * N (`-(a_pk * s_d + e_{pk,d}) mod Qp`)
    pub row_salted_digests: Vec<[u8; 32]>, // length n_parties
    pub linear_images: Vec<Vec<u64>>, // t * t entries `(u * t + v)`, each `3 * N`
    pub bdlop_row_commits: Vec<BdlopCommitment>, // length n_parties: homomorphic commits to `S_d(r+1, 0)`
    pub digest: [u8; 32],
}

/// Recipient-private verified dealing row (`0` public wire codec, `0` Clone).
pub struct VerifiedDealerRow {
    dealer: usize,
    recipient: usize,
    /// `s_row[v]` = `3 * N` RNS polynomial `[y^v] S_d(recipient + 1, y)`. `s_row[0]` is the Shamir share!
    s_row: Vec<Vec<u64>>,
    /// `e_row[v]` = `3 * N` RNS polynomial `[y^v] E_d(recipient + 1, y)`.
    e_row: Vec<Vec<u64>>,
    bdlop_open: BdlopShortOpening,
    broadcast: DealerVssPublicBroadcast,
}

/// Public DKG transcript anchoring the collective BFV `ThresholdPubKey` and every custodian's BDLOP share commitment.
#[derive(Clone)]
pub struct VerifiedThresholdDkgTranscript {
    pub session_domain: [u8; 32],
    pub n_parties: usize,
    pub threshold: usize,
    pub crp_seed: [u8; 32],
    pub bcast_list_digest: [u8; 32],
    pub a_pk_coeff: Vec<u64>,
    pub b_pk_coeff: Vec<u64>,
    pub bdlop_crs: BdlopCrs,
    /// Summed homomorphic BDLOP commitment `(T_{0,i}, T_{1,i}) = sum_d Com(S_d(i+1, 0))` per custodian `i in 0..n`.
    pub party_bdlop_anchors: Vec<BdlopCommitment>,
    pub digest: [u8; 32],
}

impl VerifiedThresholdDkgTranscript {
    #[allow(clippy::too_many_arguments)]
    pub fn compute_canonical_digest(
        session_domain: &[u8; 32],
        n_parties: usize,
        threshold: usize,
        crp_seed: &[u8; 32],
        bcast_list_digest: &[u8; 32],
        a_pk_coeff: &[u64],
        b_pk_coeff: &[u64],
        bdlop_crs: &BdlopCrs,
        party_bdlop_anchors: &[BdlopCommitment],
    ) -> [u8; 32] {
        let mut th = Sha256::new();
        th.update(b"DARKVFHE_VERIFIED_DKG_TRANSCRIPT_V2|");
        th.update(session_domain);
        th.update((n_parties as u32).to_le_bytes());
        th.update((threshold as u32).to_le_bytes());
        th.update(crp_seed);
        th.update(bcast_list_digest);
        for &v in a_pk_coeff
            .iter()
            .chain(b_pk_coeff.iter())
            .chain(bdlop_crs.a1_coeff.iter())
            .chain(bdlop_crs.a2_coeff.iter())
            .chain(bdlop_crs.b1_coeff.iter())
        {
            th.update(v.to_le_bytes());
        }
        for com in party_bdlop_anchors {
            for &v in com.t0_coeff.iter().chain(com.t1_coeff.iter()) {
                th.update(v.to_le_bytes());
            }
        }
        th.finalize().into()
    }

    pub fn verify_integrity(&self, params: &HoistedParams) -> Result<()> {
        let n = params.n;
        if self.threshold < 2
            || self.threshold >= self.n_parties
            || 2 * self.threshold <= self.n_parties
            || self.a_pk_coeff.len() != 3 * n
            || self.b_pk_coeff.len() != 3 * n
            || self.bdlop_crs.a1_coeff.len() != 3 * n
            || self.bdlop_crs.a2_coeff.len() != 3 * n
            || self.bdlop_crs.b1_coeff.len() != 3 * n
            || self.party_bdlop_anchors.len() != self.n_parties
            || self
                .party_bdlop_anchors
                .iter()
                .any(|c| c.t0_coeff.len() != 3 * n || c.t1_coeff.len() != 3 * n)
        {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let want = Self::compute_canonical_digest(
            &self.session_domain,
            self.n_parties,
            self.threshold,
            &self.crp_seed,
            &self.bcast_list_digest,
            &self.a_pk_coeff,
            &self.b_pk_coeff,
            &self.bdlop_crs,
            &self.party_bdlop_anchors,
        );
        if want != self.digest {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        Ok(())
    }
}

/// Sealed non-forgeable proof token emitted by `verify_cross_evaluations` and required by `assemble_custodian_party`.
pub struct VerifiedCrossCheckReceipt {
    session_domain: [u8; 32],
    me: usize,
    peer: usize,
    bcasts_digest: [u8; 32],
}

/// Distributed `t < n` (`NoSingleViewer >= 2`) Keygen Coordinatorless Context (derived identically by every party).
#[derive(Clone)]
pub struct DistributedThresholdDkg {
    pub params: Arc<HoistedParams>,
    pub rns_q: Arc<Rns>,
    pub roster: EnrolledThresholdRoster,
    pub crp_seed: [u8; 32],
    pub session_domain: [u8; 32],
    pub a_pk_coeff: Vec<u64>,
    pub a_pk_ntt: Vec<u64>,
    pub bdlop_crs: BdlopCrs,
}

pub const SEQ_VSS_DEALING: u64 = 1;
pub const SEQ_VSS_CROSS_EVAL: u64 = 2;

pub type DealerVssOutput = (
    DealerVssPublicBroadcast,
    VerifiedDealerRow,
    Vec<(usize, Vec<u8>)>,
    DealerRelinSecret,
);

impl DistributedThresholdDkg {
    pub fn new(
        params: Arc<HoistedParams>,
        roster: EnrolledThresholdRoster,
        crp_seed: [u8; 32],
    ) -> Result<Self> {
        roster.verify_integrity()?;
        let rns_q = Arc::new(Rns::new(params.n, &params.qp, params.t));
        let mut hd = Sha256::new();
        hd.update(b"DARKVFHE_DIST_DKG_DOMAIN_V1|");
        hd.update(roster.roster_digest);
        hd.update(crp_seed);
        hd.update((params.n as u64).to_le_bytes());
        for &q in &params.qp {
            hd.update(q.to_le_bytes());
        }
        hd.update(params.t.to_le_bytes());
        let session_domain: [u8; 32] = hd.finalize().into();

        let mut ha = Sha256::new();
        ha.update(b"DARKVFHE_APK_CRS_V1|");
        ha.update(session_domain);
        let mut apk_rng = PcsRng::from_seed(ha.finalize().into());
        let a_pk_coeff = sample_uniform_rns_qp(&rns_q, &mut apk_rng);
        let mut a_pk_ntt = a_pk_coeff.clone();
        rns_q.fwd(&mut a_pk_ntt);
        let bdlop_crs = BdlopCrs::derive(&rns_q, &session_domain);

        Ok(DistributedThresholdDkg {
            params,
            rns_q,
            roster,
            crp_seed,
            session_domain,
            a_pk_coeff,
            a_pk_ntt,
            bdlop_crs,
        })
    }

    /// Phase 1 (Dealer side): sample short ternary `s_d` and symmetric degree-`(t-1)` bivariate `(S_d, E_d)`
    /// strictly from OS `/dev/urandom`, compute public linear images & BDLOP row commitments, and seal each peer's row!
    pub fn deal_from_os(
        &self,
        dealer_id: &mut HybridPqCustodianIdentity,
    ) -> Result<DealerVssOutput> {
        self.deal_internal(dealer_id, None, None)
    }

    /// Test-only adversarial helper to inject a corrupted private row or equivocating polynomial.
    pub fn deal_adversarial_for_test(
        &self,
        dealer_id: &mut HybridPqCustodianIdentity,
        corrupt_row_victim: Option<usize>,
        equivocate_victim: Option<usize>,
    ) -> Result<DealerVssOutput> {
        self.deal_internal(dealer_id, corrupt_row_victim, equivocate_victim)
    }

    fn deal_internal(
        &self,
        dealer_id: &mut HybridPqCustodianIdentity,
        corrupt_row_victim: Option<usize>,
        equivocate_victim: Option<usize>,
    ) -> Result<DealerVssOutput> {
        let dealer = dealer_id.party_id;
        let n_p = self.roster.n_parties;
        let t = self.roster.threshold;
        let n = self.params.n;
        let rns = &self.rns_q;
        if dealer >= n_p {
            return Err(ThresholdCustodyError::InvalidParty {
                party: dealer,
                n_parties: n_p,
            });
        }

        let mut os_rng = PcsRng::from_seed(os_csprng_seed32());
        let s_d = sample_ternary_poly(n, &mut os_rng);
        let e_d = sample_small_err_poly(n, &mut os_rng, 8);

        // Symmetric `t x t` bivariate polynomials `sigma[u][v] == sigma[v][u]` and `eps[u][v] == eps[v][u]`:
        let mut sigma = vec![vec![vec![0u64; 3 * n]; t]; t];
        let mut eps = vec![vec![vec![0u64; 3 * n]; t]; t];
        sigma[0][0] = rns.from_signed(&s_d);
        eps[0][0] = rns.from_signed(&e_d);

        for u in 0..t {
            for v in u..t {
                if u == 0 && v == 0 {
                    continue;
                }
                let s_uv = sample_uniform_rns_qp(rns, &mut os_rng);
                let e_uv = sample_uniform_rns_qp(rns, &mut os_rng);
                sigma[u][v] = s_uv.clone();
                sigma[v][u] = s_uv;
                eps[u][v] = e_uv.clone();
                eps[v][u] = e_uv;
            }
        }

        // Public BFV linear images `C_{u,v} = -(a_pk * sigma_{u,v} + eps_{u,v}) mod Qp`:
        let mut linear_images = Vec::with_capacity(t * t);
        for u in 0..t {
            for v in 0..t {
                let mut s_ntt = sigma[u][v].clone();
                rns.fwd(&mut s_ntt);
                let mut prod = rns.mul_pw(&self.a_pk_ntt, &s_ntt);
                rns.inv(&mut prod);
                let mut c_uv = vec![0u64; 3 * n];
                for k in 0..3 {
                    let qk = rns.qs[k];
                    for j in 0..n {
                        let idx = k * n + j;
                        c_uv[idx] = submod(0, addmod(prod[idx], eps[u][v][idx], qk), qk);
                    }
                }
                linear_images.push(c_uv);
            }
        }
        let b_share_coeff = linear_images[0].clone();

        let mut row_salted_digests = Vec::with_capacity(n_p);
        let mut bdlop_row_commits = Vec::with_capacity(n_p);
        let mut raw_rows = Vec::with_capacity(n_p);

        for rec in 0..n_p {
            let x_pt = (rec + 1) as u64;
            let mut s_row = vec![vec![0u64; 3 * n]; t];
            let mut e_row = vec![vec![0u64; 3 * n]; t];
            for v in 0..t {
                for k in 0..3 {
                    let qk = rns.qs[k];
                    let mut x_pow = 1u64;
                    for u in 0..t {
                        for j in 0..n {
                            let idx = k * n + j;
                            s_row[v][idx] =
                                addmod(s_row[v][idx], mulmod(sigma[u][v][idx], x_pow, qk), qk);
                            e_row[v][idx] =
                                addmod(e_row[v][idx], mulmod(eps[u][v][idx], x_pow, qk), qk);
                        }
                        x_pow = mulmod(x_pow, x_pt, qk);
                    }
                }
            }
            if equivocate_victim == Some(rec) && t >= 2 {
                // Shift y^1 slope while adjusting e_row[1] so local BFV linear image C_{u,1} STILL passes (`-(a*ds + de) == 0`),
                // forcing ONLY the pairwise cross-evaluation `F(rec+1, peer+1) == F(peer+1, rec+1)` to catch it!
                let mut ds = vec![0i64; n];
                ds[0] = 1;
                let ds_rns = rns.from_signed(&ds);
                let mut ds_ntt = ds_rns.clone();
                rns.fwd(&mut ds_ntt);
                let mut ads = rns.mul_pw(&self.a_pk_ntt, &ds_ntt);
                rns.inv(&mut ads);
                for k in 0..3 {
                    let qk = rns.qs[k];
                    for j in 0..n {
                        let idx = k * n + j;
                        s_row[1][idx] = addmod(s_row[1][idx], ds_rns[idx], qk);
                        e_row[1][idx] = submod(e_row[1][idx], ads[idx], qk);
                    }
                }
            }

            let salt = os_rng.next_block();
            let bdlop_open = BdlopShortOpening {
                r1: sample_small_err_poly(n, &mut os_rng, 8),
                e0: sample_small_err_poly(n, &mut os_rng, 8),
                e1: sample_small_err_poly(n, &mut os_rng, 8),
            };
            let bdlop_com = self.bdlop_crs.commit(rns, &s_row[0], &bdlop_open);
            let row_dig =
                compute_vss_row_digest(&self.session_domain, dealer, rec, &salt, &s_row, &e_row);
            row_salted_digests.push(row_dig);
            bdlop_row_commits.push(bdlop_com);
            raw_rows.push((rec, salt, s_row, e_row, bdlop_open));
        }

        let digest = compute_dealer_broadcast_digest(
            &self.session_domain,
            dealer,
            &b_share_coeff,
            &row_salted_digests,
            &linear_images,
            &bdlop_row_commits,
        );
        let broadcast = DealerVssPublicBroadcast {
            dealer,
            session_domain: self.session_domain,
            b_share_coeff,
            row_salted_digests,
            linear_images,
            bdlop_row_commits,
            digest,
        };

        let mut own_verified = None;
        let mut sealed_msgs = Vec::with_capacity(n_p - 1);
        for (rec, salt, mut s_row, e_row, bdlop_open) in raw_rows {
            if rec == dealer {
                own_verified = Some(VerifiedDealerRow {
                    dealer,
                    recipient: rec,
                    s_row,
                    e_row,
                    bdlop_open,
                    broadcast: broadcast.clone(),
                });
            } else {
                if corrupt_row_victim == Some(rec) {
                    s_row[0][0] = addmod(s_row[0][0], 1, rns.qs[0]);
                }
                let plain = encode_private_vss_row(&salt, &s_row, &e_row, &bdlop_open);
                let env = self.roster.seal_to_peer(
                    dealer_id,
                    rec,
                    &self.session_domain,
                    SEQ_VSS_DEALING,
                    &plain,
                )?;
                sealed_msgs.push((rec, env));
            }
        }

        Ok((
            broadcast,
            own_verified.unwrap(),
            sealed_msgs,
            DealerRelinSecret {
                dealer,
                session_domain: self.session_domain,
                coeffs: s_d,
            },
        ))
    }

    /// Phase 1 (Recipient side): decrypt sealed row, verify broadcast digest, salted row opening,
    /// BDLOP short-norm commitment opening, AND public BFV linear-image consistency!
    pub fn accept_dealing(
        &self,
        recipient_id: &HybridPqCustodianIdentity,
        broadcast: &DealerVssPublicBroadcast,
        sealed_row: &[u8],
    ) -> Result<VerifiedDealerRow> {
        let rec = recipient_id.party_id;
        let dealer = broadcast.dealer;
        let n_p = self.roster.n_parties;
        let t = self.roster.threshold;
        let n = self.params.n;
        let rns = &self.rns_q;

        if broadcast.session_domain != self.session_domain
            || broadcast.row_salted_digests.len() != n_p
            || broadcast.bdlop_row_commits.len() != n_p
            || broadcast.linear_images.len() != t * t
            || broadcast.linear_images[0] != broadcast.b_share_coeff
        {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let want_bcast_dig = compute_dealer_broadcast_digest(
            &self.session_domain,
            dealer,
            &broadcast.b_share_coeff,
            &broadcast.row_salted_digests,
            &broadcast.linear_images,
            &broadcast.bdlop_row_commits,
        );
        if want_bcast_dig != broadcast.digest {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }

        let plain = self.roster.open_from_peer(
            recipient_id,
            dealer,
            &self.session_domain,
            SEQ_VSS_DEALING,
            sealed_row,
        )?;
        let (salt, s_row, e_row, bdlop_open) = decode_private_vss_row(&plain, t, n, &rns.qs)?;

        let row_dig =
            compute_vss_row_digest(&self.session_domain, dealer, rec, &salt, &s_row, &e_row);
        if row_dig != broadcast.row_salted_digests[rec] {
            return Err(ThresholdCustodyError::VssRowCommitmentMismatch {
                dealer,
                recipient: rec,
            });
        }

        if bdlop_open.r1.iter().any(|&v| v.abs() > 8)
            || bdlop_open.e0.iter().any(|&v| v.abs() > 8)
            || bdlop_open.e1.iter().any(|&v| v.abs() > 8)
        {
            return Err(ThresholdCustodyError::VssBdlopOpeningMismatch {
                dealer,
                recipient: rec,
            });
        }
        let recomputed_bdlop = self.bdlop_crs.commit(rns, &s_row[0], &bdlop_open);
        if recomputed_bdlop != broadcast.bdlop_row_commits[rec] {
            return Err(ThresholdCustodyError::VssBdlopOpeningMismatch {
                dealer,
                recipient: rec,
            });
        }

        // Verify BFV linear image: `-(a_pk * s_row[v] + e_row[v]) == sum_{u=0}^{t-1} C_{u,v} * (rec + 1)^u (mod Qp)`:
        let x_pt = (rec + 1) as u64;
        for v in 0..t {
            let mut s_ntt = s_row[v].clone();
            rns.fwd(&mut s_ntt);
            let mut prod = rns.mul_pw(&self.a_pk_ntt, &s_ntt);
            rns.inv(&mut prod);
            for k in 0..3 {
                let qk = rns.qs[k];
                let mut x_pows = Vec::with_capacity(t);
                let mut cur = 1u64;
                for _ in 0..t {
                    x_pows.push(cur);
                    cur = mulmod(cur, x_pt, qk);
                }
                for j in 0..n {
                    let idx = k * n + j;
                    let lhs = submod(0, addmod(prod[idx], e_row[v][idx], qk), qk);
                    let mut rhs = 0u64;
                    for (u, &xp) in x_pows.iter().enumerate() {
                        rhs = addmod(
                            rhs,
                            mulmod(broadcast.linear_images[u * t + v][idx], xp, qk),
                            qk,
                        );
                    }
                    if lhs != rhs {
                        return Err(ThresholdCustodyError::VssLinearImageMismatch {
                            dealer,
                            recipient: rec,
                        });
                    }
                }
            }
        }

        Ok(VerifiedDealerRow {
            dealer,
            recipient: rec,
            s_row,
            e_row,
            bdlop_open,
            broadcast: broadcast.clone(),
        })
    }

    fn compute_ordered_bcasts_digest(
        &self,
        accepted_rows: &[VerifiedDealerRow],
        me: usize,
    ) -> Result<[u8; 32]> {
        if accepted_rows.len() != self.roster.n_parties {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let mut bh = Sha256::new();
        bh.update(b"DARKVFHE_ORDERED_BCASTS_V1|");
        bh.update(self.session_domain);
        for (d, row) in accepted_rows.iter().enumerate() {
            if row.dealer != d || row.recipient != me {
                return Err(ThresholdCustodyError::DkgTranscriptMismatch);
            }
            bh.update(row.broadcast.digest);
        }
        Ok(bh.finalize().into())
    }

    /// Phase 2 (Sender side): seal pairwise bivariate cross-evaluations `(S_d(me+1, peer+1), E_d(me+1, peer+1))`
    /// AND ordered dealer broadcast digests across all `n` dealers to `peer`.
    pub fn seal_cross_evaluations(
        &self,
        me_id: &mut HybridPqCustodianIdentity,
        accepted_rows: &[VerifiedDealerRow],
        peer: usize,
    ) -> Result<Vec<u8>> {
        let n_p = self.roster.n_parties;
        let n = self.params.n;
        let bcasts_digest = self.compute_ordered_bcasts_digest(accepted_rows, me_id.party_id)?;
        let y_pt = (peer + 1) as u64;
        let mut payload = Vec::with_capacity(n_p * 6 * n * 8 + 40);
        payload.extend_from_slice(&(n_p as u32).to_le_bytes());
        payload.extend_from_slice(&bcasts_digest);
        for row in accepted_rows {
            let s_ev = eval_poly_vec_rns(&row.s_row, y_pt, n, &self.rns_q.qs);
            let e_ev = eval_poly_vec_rns(&row.e_row, y_pt, n, &self.rns_q.qs);
            for &v in s_ev.iter().chain(e_ev.iter()) {
                payload.extend_from_slice(&v.to_le_bytes());
            }
        }
        self.roster.seal_to_peer(
            me_id,
            peer,
            &self.session_domain,
            SEQ_VSS_CROSS_EVAL,
            &payload,
        )
    }

    /// Phase 2 (Receiver side): open `peer`'s cross-evaluation envelope, enforce identical ordered dealer broadcasts,
    /// and enforce `F_d(me+1, peer+1) == F_d(peer+1, me+1)`, emitting a sealed `VerifiedCrossCheckReceipt`.
    pub fn verify_cross_evaluations(
        &self,
        me_id: &HybridPqCustodianIdentity,
        accepted_rows: &[VerifiedDealerRow],
        peer: usize,
        sealed_cross: &[u8],
    ) -> Result<VerifiedCrossCheckReceipt> {
        let n_p = self.roster.n_parties;
        let n = self.params.n;
        let my_bcasts_digest = self.compute_ordered_bcasts_digest(accepted_rows, me_id.party_id)?;
        let plain = self.roster.open_from_peer(
            me_id,
            peer,
            &self.session_domain,
            SEQ_VSS_CROSS_EVAL,
            sealed_cross,
        )?;
        let mut cur = ByteReader::new(&plain);
        let cnt = cur
            .read_u32()
            .map_err(|_| ThresholdCustodyError::DkgTranscriptMismatch)? as usize;
        if cnt != n_p {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let peer_bcasts_digest = cur
            .read_hash()
            .map_err(|_| ThresholdCustodyError::DkgTranscriptMismatch)?;
        if peer_bcasts_digest != my_bcasts_digest {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let y_pt = (peer + 1) as u64;
        for (d, row) in accepted_rows.iter().enumerate() {
            let mut got_s = Vec::with_capacity(3 * n);
            let mut got_e = Vec::with_capacity(3 * n);
            for _ in 0..(3 * n) {
                got_s.push(
                    cur.read_u64()
                        .map_err(|_| ThresholdCustodyError::DkgTranscriptMismatch)?,
                );
            }
            for _ in 0..(3 * n) {
                got_e.push(
                    cur.read_u64()
                        .map_err(|_| ThresholdCustodyError::DkgTranscriptMismatch)?,
                );
            }
            let want_s = eval_poly_vec_rns(&row.s_row, y_pt, n, &self.rns_q.qs);
            let want_e = eval_poly_vec_rns(&row.e_row, y_pt, n, &self.rns_q.qs);
            if got_s != want_s || got_e != want_e {
                return Err(ThresholdCustodyError::VssInconsistentRows {
                    dealer: d,
                    left: me_id.party_id.min(peer),
                    right: me_id.party_id.max(peer),
                });
            }
        }
        if !cur.is_eof() {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        Ok(VerifiedCrossCheckReceipt {
            session_domain: self.session_domain,
            me: me_id.party_id,
            peer,
            bcasts_digest: my_bcasts_digest,
        })
    }

    /// Phase 3: Locally assemble this custodian's Shamir secret share `s_{shamir, i}`, aggregate BDLOP opening,
    /// collective `ThresholdPubKey`, and `VerifiedThresholdDkgTranscript` (`0` central viewer!).
    /// Requires all `n - 1` `VerifiedCrossCheckReceipt`s proving every peer agreed on dealer broadcasts & evaluations!
    #[allow(clippy::too_many_arguments)]
    pub fn assemble_custodian_party(
        &self,
        engine: Arc<HoistedEngine>,
        identity: HybridPqCustodianIdentity,
        accepted_rows: Vec<VerifiedDealerRow>,
        cross_receipts: &[VerifiedCrossCheckReceipt],
        rlk: Arc<RelinearizationKey>,
        pinned_policy_digest: [u8; 32],
        tvd_40b_strict_mode: bool,
        audit_log_path: &Path,
    ) -> Result<(
        ThresholdCustodianParty,
        crate::dark_gdn::ThresholdPubKey,
        VerifiedThresholdDkgTranscript,
    )> {
        self.roster.verify_integrity()?;
        let me = identity.party_id;
        let n_p = self.roster.n_parties;
        let n = self.params.n;
        let rns = &self.rns_q;

        let bcast_list_digest = self.compute_ordered_bcasts_digest(&accepted_rows, me)?;
        if cross_receipts.len() != n_p - 1 {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let mut seen_peers = BTreeSet::new();
        for rc in cross_receipts {
            if rc.session_domain != self.session_domain
                || rc.me != me
                || rc.peer == me
                || rc.peer >= n_p
                || rc.bcasts_digest != bcast_list_digest
                || !seen_peers.insert(rc.peer)
            {
                return Err(ThresholdCustodyError::DkgTranscriptMismatch);
            }
        }

        let mut b_pk_coeff = vec![0u64; 3 * n];
        let mut s_shamir_rns = vec![0u64; 3 * n];
        let mut agg_r1 = vec![0i64; n];
        let mut agg_e0 = vec![0i64; n];
        let mut agg_e1 = vec![0i64; n];
        let mut party_bdlop_anchors = vec![
            BdlopCommitment {
                t0_coeff: vec![0u64; 3 * n],
                t1_coeff: vec![0u64; 3 * n],
            };
            n_p
        ];

        for (d, row) in accepted_rows.into_iter().enumerate() {
            if row.dealer != d || row.recipient != me {
                return Err(ThresholdCustodyError::DkgTranscriptMismatch);
            }
            rns.add_assign(&mut b_pk_coeff, &row.broadcast.b_share_coeff);
            rns.add_assign(&mut s_shamir_rns, &row.s_row[0]);
            for j in 0..n {
                agg_r1[j] += row.bdlop_open.r1[j];
                agg_e0[j] += row.bdlop_open.e0[j];
                agg_e1[j] += row.bdlop_open.e1[j];
            }
            for (anchor, row_com) in party_bdlop_anchors
                .iter_mut()
                .zip(&row.broadcast.bdlop_row_commits)
            {
                rns.add_assign(&mut anchor.t0_coeff, &row_com.t0_coeff);
                rns.add_assign(&mut anchor.t1_coeff, &row_com.t1_coeff);
            }
        }

        let agg_open = BdlopShortOpening {
            r1: agg_r1,
            e0: agg_e0,
            e1: agg_e1,
        };
        if self.bdlop_crs.commit(rns, &s_shamir_rns, &agg_open) != party_bdlop_anchors[me] {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }

        let mut pk0_ntt = b_pk_coeff.clone();
        rns.fwd(&mut pk0_ntt);
        let pub_key = crate::dark_gdn::ThresholdPubKey {
            rns_q: rns.clone(),
            a_coeff: self.a_pk_coeff.clone(),
            b_coeff: b_pk_coeff.clone(),
            pk0_ntt,
            pk1_ntt: self.a_pk_ntt.clone(),
        };

        let dkg_digest = VerifiedThresholdDkgTranscript::compute_canonical_digest(
            &self.session_domain,
            n_p,
            self.roster.threshold,
            &self.crp_seed,
            &bcast_list_digest,
            &self.a_pk_coeff,
            &b_pk_coeff,
            &self.bdlop_crs,
            &party_bdlop_anchors,
        );

        let transcript = VerifiedThresholdDkgTranscript {
            session_domain: self.session_domain,
            n_parties: n_p,
            threshold: self.roster.threshold,
            crp_seed: self.crp_seed,
            bcast_list_digest,
            a_pk_coeff: self.a_pk_coeff.clone(),
            b_pk_coeff,
            bdlop_crs: self.bdlop_crs.clone(),
            party_bdlop_anchors,
            digest: dkg_digest,
        };

        // Smudge width `E = min(floor((Q / (2t)) / 1024), 2^111 - 1)`:
        let q_over_2t: BigUint =
            &self.params.q_big / (BigUint::from(2u32) * BigUint::from(self.params.t));
        let e_big: BigUint = (&q_over_2t >> 10usize).max(BigUint::from(1u32 << 20));
        let smudge_bound: u128 = e_big
            .try_into()
            .unwrap_or((1u128 << 111) - 1)
            .min((1u128 << 111) - 1);
        let two_e_bits = 128 - (2 * smudge_bound).leading_zeros();
        let smudge_top_bits = two_e_bits.saturating_sub(100).max(1);
        let noise_summary = derive_homomorphic_state_noise_budget(&self.params, smudge_bound, 2, 4);

        let audit_log = PersistentCustodyAuditLog::open_or_create(audit_log_path, me, &dkg_digest)?;
        let mut signer_min_pq_leaves = vec![0u64; n_p];
        signer_min_pq_leaves[me] = identity.pq_signer.next_leaf;

        let party = ThresholdCustodianParty {
            party_id: me,
            params: self.params.clone(),
            engine,
            roster: self.roster.clone(),
            identity,
            dkg_transcript: transcript.clone(),
            rlk,
            s_shamir_rns,
            bdlop_agg_open: agg_open,
            smudge_bound,
            smudge_top_bits,
            pinned_policy_digest,
            tvd_40b_strict_mode,
            r_refresh_correctness: noise_summary.r_refresh_correctness.max(1) as u32,
            audit_log,
            verified_persistent_a_roots: BTreeSet::new(),
            signer_min_pq_leaves,
        };

        Ok((party, pub_key, transcript))
    }
}

// ------------------------------------------------------------------------------------------------
// §2b. 2-Round Mouchet et al. Distributed `RelinearizationKey` Ceremony on `(q_0, q_1, q_2, b_0)`
// ------------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinRound1Share {
    pub dealer: usize,
    pub session_domain: [u8; 32],
    pub h0_ntt: [Vec<u64>; 4], // 4 gadget levels `m=0..3`, each `4 * N`
    pub h1_ntt: [Vec<u64>; 4],
    pub sig: HybridPqSignature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinRound1Aggregate {
    pub session_domain: [u8; 32],
    pub agg_h0_ntt: [Vec<u64>; 4],
    pub agg_h1_ntt: [Vec<u64>; 4],
    pub digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinRound2Share {
    pub dealer: usize,
    pub session_domain: [u8; 32],
    pub r1_digest: [u8; 32],
    pub h2_ntt: [Vec<u64>; 4],
    pub sig: HybridPqSignature,
}

/// Per-dealer 2-round relinearization state (`0` Clone, one-shot Round-1 & Round-2, zeroizes `u_m` and `s_d` on `Drop`).
pub struct DistributedRelinDealer {
    dealer: usize,
    session_domain: [u8; 32],
    rns4: Arc<Rns>,
    p_ks: u64,
    a_ntts: [Vec<u64>; 4],
    s_d: Vec<i64>,
    u_m: [Vec<i64>; 4],
    round_1_emitted: bool,
}

impl Drop for DistributedRelinDealer {
    fn drop(&mut self) {
        for x in &mut self.s_d {
            unsafe { std::ptr::write_volatile(x, 0) };
        }
        for u in &mut self.u_m {
            for x in u.iter_mut() {
                unsafe { std::ptr::write_volatile(x, 0) };
            }
        }
    }
}

fn derive_relin_crp_rns4(
    params: &HoistedParams,
    session_domain: &[u8; 32],
) -> (Arc<Rns>, [Vec<u64>; 4]) {
    let qs4 = [params.qp[0], params.qp[1], params.qp[2], params.bp[0]];
    let rns4 = Arc::new(Rns::new(params.n, &qs4, params.t));
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_RELIN_CRP_V1|");
    h.update(session_domain);
    let mut rng = PcsRng::from_seed(h.finalize().into());
    let a_ntts: [Vec<u64>; 4] = std::array::from_fn(|_| {
        let mut a = sample_uniform_rns4(&rns4, &mut rng);
        rns4.fwd(&mut a);
        a
    });
    (rns4, a_ntts)
}

impl DistributedRelinDealer {
    /// Consume `DealerRelinSecret` (`s_d`) and sample fresh ephemeral `u_m in {-1, 0, 1}^N` from `/dev/urandom`.
    pub fn new_from_os(params: &HoistedParams, secret: DealerRelinSecret) -> Self {
        let (rns4, a_ntts) = derive_relin_crp_rns4(params, &secret.session_domain);
        let mut rng = PcsRng::from_seed(os_csprng_seed32());
        let u_m = std::array::from_fn(|_| sample_ternary_poly(params.n, &mut rng));
        DistributedRelinDealer {
            dealer: secret.dealer,
            session_domain: secret.session_domain,
            rns4,
            p_ks: params.bp[0],
            a_ntts,
            s_d: secret.coeffs.clone(),
            u_m,
            round_1_emitted: false,
        }
    }

    /// One-shot Round 1: `h_{0,d}^{(m)} = -a^{(m)} u_d^{(m)} + P_ks 2^{60 m} s_d + e_0`, `h_{1,d}^{(m)} = a^{(m)} s_d + e_1`.
    pub fn round_1(&mut self, signer: &mut HybridPqCustodianIdentity) -> Result<RelinRound1Share> {
        if self.round_1_emitted {
            return Err(ThresholdCustodyError::RelinCeremonyRefused(
                "round_1 already emitted for this dealer",
            ));
        }
        self.round_1_emitted = true;
        let n = self.rns4.n;
        let qs4 = &self.rns4.qs;
        let mut rng = PcsRng::from_seed(os_csprng_seed32());

        let s_rns = self.rns4.from_signed(&self.s_d);
        let mut s_ntt = s_rns.clone();
        self.rns4.fwd(&mut s_ntt);

        let mut h0_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);
        let mut h1_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);

        for m in 0..4 {
            let mut scale_k = [0u64; 4];
            for k in 0..3 {
                let qk = qs4[k];
                scale_k[k] = mulmod(self.p_ks % qk, powmod(1u64 << 60, m as u64, qk), qk);
            }
            let mut u_ntt = self.rns4.from_signed(&self.u_m[m]);
            self.rns4.fwd(&mut u_ntt);

            let mut au = self.rns4.mul_pw(&self.a_ntts[m], &u_ntt);
            let mut as_c = self.rns4.mul_pw(&self.a_ntts[m], &s_ntt);
            self.rns4.inv(&mut au);
            self.rns4.inv(&mut as_c);

            let e0 = sample_small_err_poly(n, &mut rng, 8);
            let e1 = sample_small_err_poly(n, &mut rng, 8);

            let mut h0 = vec![0u64; 4 * n];
            let mut h1 = vec![0u64; 4 * n];
            for k in 0..4 {
                let qk = qs4[k];
                for j in 0..n {
                    let idx = k * n + j;
                    let scaled_s = mulmod(scale_k[k], s_rns[idx], qk);
                    let rhs0 = addmod(scaled_s, from_i64(e0[j], qk), qk);
                    h0[idx] = submod(rhs0, au[idx], qk);
                    h1[idx] = addmod(as_c[idx], from_i64(e1[j], qk), qk);
                }
            }
            self.rns4.fwd(&mut h0);
            self.rns4.fwd(&mut h1);
            h0_ntt[m] = h0;
            h1_ntt[m] = h1;
        }

        let pre = relin_r1_sig_preimage(&self.session_domain, self.dealer, &h0_ntt, &h1_ntt);
        let sig = signer.sign(&pre)?;
        Ok(RelinRound1Share {
            dealer: self.dealer,
            session_domain: self.session_domain,
            h0_ntt,
            h1_ntt,
            sig,
        })
    }

    /// One-shot Round 2 (consumes `self` and zeroizes `s_d, u_m` immediately!):
    /// Reconstructs `RelinRound1Aggregate` locally from all `n` verified `RelinRound1Share`s (never trusting an
    /// unauthenticated coordinator aggregate!) and emits `h_{2,d}^{(m)} = s_d * H_0^{(m)} + (u_d^{(m)} - s_d) * H_1^{(m)} + e_2^{(m)}`.
    pub fn round_2(
        self,
        params: &HoistedParams,
        roster: &EnrolledThresholdRoster,
        r1_shares: &[RelinRound1Share],
        signer: &mut HybridPqCustodianIdentity,
    ) -> Result<RelinRound2Share> {
        if !self.round_1_emitted {
            return Err(ThresholdCustodyError::RelinCeremonyRefused(
                "round_2 called before round_1",
            ));
        }
        let r1_agg = aggregate_relin_round_1(params, roster, &self.session_domain, r1_shares)?;
        let n = self.rns4.n;
        let qs4 = &self.rns4.qs;
        let mut rng = PcsRng::from_seed(os_csprng_seed32());

        let mut s_ntt = self.rns4.from_signed(&self.s_d);
        self.rns4.fwd(&mut s_ntt);

        let mut h2_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);
        for (m, h2_slot) in h2_ntt.iter_mut().enumerate() {
            let u_minus_s: Vec<i64> = (0..n).map(|j| self.u_m[m][j] - self.s_d[j]).collect();
            let mut ums_ntt = self.rns4.from_signed(&u_minus_s);
            self.rns4.fwd(&mut ums_ntt);

            let mut acc = self.rns4.mul_pw(&s_ntt, &r1_agg.agg_h0_ntt[m]);
            self.rns4.mul_acc(&mut acc, &ums_ntt, &r1_agg.agg_h1_ntt[m]);
            self.rns4.inv(&mut acc);

            let e2 = sample_small_err_poly(n, &mut rng, 1i64 << 36);
            for (k, &qk) in qs4.iter().enumerate() {
                for (j, &e2j) in e2.iter().enumerate() {
                    let idx = k * n + j;
                    acc[idx] = addmod(acc[idx], from_i64(e2j, qk), qk);
                }
            }
            self.rns4.fwd(&mut acc);
            *h2_slot = acc;
        }

        let pre = relin_r2_sig_preimage(&self.session_domain, &r1_agg.digest, self.dealer, &h2_ntt);
        let sig = signer.sign(&pre)?;
        Ok(RelinRound2Share {
            dealer: self.dealer,
            session_domain: self.session_domain,
            r1_digest: r1_agg.digest,
            h2_ntt,
            sig,
        })
    }
}

pub fn aggregate_relin_round_1(
    params: &HoistedParams,
    roster: &EnrolledThresholdRoster,
    session_domain: &[u8; 32],
    shares: &[RelinRound1Share],
) -> Result<RelinRound1Aggregate> {
    roster.verify_integrity()?;
    if shares.len() != roster.n_parties {
        return Err(ThresholdCustodyError::RelinCeremonyRefused(
            "incomplete Round-1 shares",
        ));
    }
    let (rns4, _) = derive_relin_crp_rns4(params, session_domain);
    let n = params.n;
    let mut seen = BTreeSet::new();
    let mut agg_h0_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);
    let mut agg_h1_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);

    for sh in shares {
        if sh.session_domain != *session_domain
            || sh.dealer >= roster.n_parties
            || !seen.insert(sh.dealer)
        {
            return Err(ThresholdCustodyError::RelinCeremonyRefused(
                "invalid or duplicate Round-1 dealer",
            ));
        }
        let pre = relin_r1_sig_preimage(session_domain, sh.dealer, &sh.h0_ntt, &sh.h1_ntt);
        sh.sig.verify(&roster.enrollments[sh.dealer], 0, &pre)?;
        for m in 0..4 {
            if sh.h0_ntt[m].len() != 4 * n || sh.h1_ntt[m].len() != 4 * n {
                return Err(ThresholdCustodyError::RelinCeremonyRefused(
                    "Round-1 share dimension mismatch",
                ));
            }
            rns4.add_assign(&mut agg_h0_ntt[m], &sh.h0_ntt[m]);
            rns4.add_assign(&mut agg_h1_ntt[m], &sh.h1_ntt[m]);
        }
    }
    let digest = compute_r1_agg_digest(session_domain, &agg_h0_ntt, &agg_h1_ntt);
    Ok(RelinRound1Aggregate {
        session_domain: *session_domain,
        agg_h0_ntt,
        agg_h1_ntt,
        digest,
    })
}

pub fn assemble_distributed_relin_key(
    params: &HoistedParams,
    roster: &EnrolledThresholdRoster,
    r1_agg: &RelinRound1Aggregate,
    shares: &[RelinRound2Share],
) -> Result<RelinearizationKey> {
    roster.verify_integrity()?;
    if shares.len() != roster.n_parties {
        return Err(ThresholdCustodyError::RelinCeremonyRefused(
            "incomplete Round-2 shares",
        ));
    }
    let (rns4, _) = derive_relin_crp_rns4(params, &r1_agg.session_domain);
    let n = params.n;
    for m in 0..4 {
        if r1_agg.agg_h0_ntt[m].len() != 4 * n || r1_agg.agg_h1_ntt[m].len() != 4 * n {
            return Err(ThresholdCustodyError::RelinCeremonyRefused(
                "Round-1 aggregate dimension mismatch",
            ));
        }
    }
    if compute_r1_agg_digest(
        &r1_agg.session_domain,
        &r1_agg.agg_h0_ntt,
        &r1_agg.agg_h1_ntt,
    ) != r1_agg.digest
    {
        return Err(ThresholdCustodyError::RelinCeremonyRefused(
            "Round-1 aggregate digest tamper detected in assemble_distributed_relin_key",
        ));
    }
    let mut seen = BTreeSet::new();
    let mut rlk0_ntt = std::array::from_fn(|_| vec![0u64; 4 * n]);

    for sh in shares {
        if sh.session_domain != r1_agg.session_domain
            || sh.r1_digest != r1_agg.digest
            || sh.dealer >= roster.n_parties
            || !seen.insert(sh.dealer)
        {
            return Err(ThresholdCustodyError::RelinCeremonyRefused(
                "invalid, duplicate, or mismatched-R1 Round-2 share",
            ));
        }
        let pre = relin_r2_sig_preimage(
            &r1_agg.session_domain,
            &r1_agg.digest,
            sh.dealer,
            &sh.h2_ntt,
        );
        sh.sig.verify(&roster.enrollments[sh.dealer], 0, &pre)?;
        for (rlk0_m, h2_m) in rlk0_ntt.iter_mut().zip(&sh.h2_ntt) {
            if h2_m.len() != 4 * n {
                return Err(ThresholdCustodyError::RelinCeremonyRefused(
                    "Round-2 share dimension mismatch",
                ));
            }
            rns4.add_assign(rlk0_m, h2_m);
        }
    }
    Ok(RelinearizationKey {
        rns_qp: rns4,
        rlk0_ntt,
        rlk1_ntt: r1_agg.agg_h1_ntt.clone(),
    })
}

// ================================================================================================
// §3. Pre-Share Persisted `C8` `OpeningAuthorization` + Durable Hash-Chained Audit Log + WHIR Gate
// ================================================================================================

/// Quorum-signed `C8` authorization required by every custodian BEFORE computing or releasing a decryption share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpeningAuthorization {
    pub dkg_transcript_digest: [u8; 32],
    pub epoch: u64, // MUST be != 0 (`ZeroEpochRejected`)
    pub sequence: u64,
    pub policy_digest: [u8; 32],
    pub ct_commitment: [u8; 32],
    pub compute_proof_digest: [u8; 32],
    pub refresh_cadence: u32, // MUST be == 1 when `tvd_40b_strict_mode` is active!
    pub turns_since_refresh: u32,
    pub selected_parties: Vec<usize>, // canonical strictly-increasing `t`-subset of `0..n_parties`
    pub quorum_signatures: Vec<HybridPqSignature>,
}

/// Compute canonical `ct_commitment` binding target ciphertext handle, optional crossing mask, and opening quorum.
pub fn compute_ct_opening_commitment(
    designated_ct_handle: &[u8; 32],
    ct_mask_handle: Option<&[u8; 32]>,
    selected_parties: &[usize],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_C8_CT_OPEN_COMMIT_V1|");
    h.update(designated_ct_handle);
    match ct_mask_handle {
        Some(mh) => {
            h.update([1u8]);
            h.update(mh);
        }
        None => h.update([0u8]),
    }
    h.update((selected_parties.len() as u32).to_le_bytes());
    for &p in selected_parties {
        h.update((p as u32).to_le_bytes());
    }
    h.finalize().into()
}

impl OpeningAuthorization {
    pub fn signing_preimage(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(200 + self.selected_parties.len() * 4);
        out.extend_from_slice(b"DARKVFHE_C8_OPENING_AUTH_V1|");
        out.extend_from_slice(&self.dkg_transcript_digest);
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&self.sequence.to_le_bytes());
        out.extend_from_slice(&self.policy_digest);
        out.extend_from_slice(&self.ct_commitment);
        out.extend_from_slice(&self.compute_proof_digest);
        out.extend_from_slice(&self.refresh_cadence.to_le_bytes());
        out.extend_from_slice(&self.turns_since_refresh.to_le_bytes());
        out.extend_from_slice(&(self.selected_parties.len() as u32).to_le_bytes());
        for &p in &self.selected_parties {
            out.extend_from_slice(&(p as u32).to_le_bytes());
        }
        out
    }

    pub fn statement_digest(&self) -> [u8; 32] {
        Sha256::digest(self.signing_preimage()).into()
    }
}

/// Verified `WhirPcs61` (`DVFHEWH1`) compute provenance bundle proving that the target ciphertext is the exact
/// output of a verified `HoistedB61 + WhirPcs61` circuit (plus optional deterministic `relinearize_ct3`).
pub struct WhirComputeProvenance<'a> {
    pub ha_grid: &'a [Vec<[u8; 32]>],
    pub hb_vec: &'a [[u8; 32]],
    pub hout_vec: &'a [[u8; 32]],
    pub opened_a: Option<&'a [Vec<Ct>]>,
    pub expected_persistent_a_root: Option<&'a [u8; 32]>,
    pub opened_b: &'a [Ct],
    pub out_cts: &'a [Ct3],
    pub target_output_row: usize,
    pub whir_proof_bytes: &'a [u8],
}

/// Durable, fsync-persisted, exclusively flock-locked, SHA-256 hash-chained append-only audit log
/// (`Obend.Polis.PqThresholdCustody` `stepEpochLatch` + `GrainCustodyHost` crash-consistent replay refusal!).
pub struct PersistentCustodyAuditLog {
    path: PathBuf,
    file: File,
    party_id: usize,
    dkg_digest: [u8; 32],
    head_chain_hash: [u8; 32],
    pub poisoned: bool,
    pub high_water_epoch: Option<u64>,
    pub epoch_digests: BTreeMap<(u64, u64), [u8; 32]>,
    pub opened_ct_commitments: BTreeSet<[u8; 32]>,
    pub opened_raw_ct_handles: BTreeSet<[u8; 32]>,
    pub entry_count: u64,
}

impl Drop for PersistentCustodyAuditLog {
    fn drop(&mut self) {
        let _ = unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}

const AUDIT_RECORD_BYTES: usize = 8 + 8 + 32 + 32 + 32 + 32 + 4 + 32; // 180 bytes per record

impl PersistentCustodyAuditLog {
    fn acquire_exclusive_flock(f: &File) -> Result<()> {
        let rc = unsafe { libc::flock(f.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
        if rc != 0 {
            return Err(ThresholdCustodyError::AuditLogIo(
                "audit log is already exclusively locked by another live handle".into(),
            ));
        }
        Ok(())
    }

    pub fn open_or_create(path: &Path, party_id: usize, dkg_digest: &[u8; 32]) -> Result<Self> {
        if !path.exists() {
            let genesis_hash: [u8; 32] = {
                let mut h = Sha256::new();
                h.update(AUDIT_LOG_MAGIC);
                h.update((party_id as u32).to_le_bytes());
                h.update(dkg_digest);
                h.finalize().into()
            };
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
            }
            let mut f = OpenOptions::new()
                .read(true)
                .append(true)
                .create_new(true)
                .open(path)
                .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
            Self::acquire_exclusive_flock(&f)?;
            f.write_all(AUDIT_LOG_MAGIC)
                .and_then(|_| f.write_all(&(party_id as u32).to_le_bytes()))
                .and_then(|_| f.write_all(dkg_digest))
                .and_then(|_| f.sync_all())
                .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
            if let Some(parent) = path.parent() {
                if let Ok(df) = File::open(parent) {
                    let _ = df.sync_all();
                }
            }
            return Ok(PersistentCustodyAuditLog {
                path: path.to_path_buf(),
                file: f,
                party_id,
                dkg_digest: *dkg_digest,
                head_chain_hash: genesis_hash,
                poisoned: false,
                high_water_epoch: None,
                epoch_digests: BTreeMap::new(),
                opened_ct_commitments: BTreeSet::new(),
                opened_raw_ct_handles: BTreeSet::new(),
                entry_count: 0,
            });
        }
        Self::reopen_existing(path, party_id, dkg_digest)
    }

    /// Reopen an EXISTING audit log (refusing missing files, torn tails, and concurrent locks!).
    pub fn reopen_existing(path: &Path, party_id: usize, dkg_digest: &[u8; 32]) -> Result<Self> {
        if !path.exists() {
            return Err(ThresholdCustodyError::CorruptedAuditLog(
                "missing audit log on reload",
            ));
        }
        let genesis_hash: [u8; 32] = {
            let mut h = Sha256::new();
            h.update(AUDIT_LOG_MAGIC);
            h.update((party_id as u32).to_le_bytes());
            h.update(dkg_digest);
            h.finalize().into()
        };
        let mut f = OpenOptions::new()
            .read(true)
            .append(true)
            .open(path)
            .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
        Self::acquire_exclusive_flock(&f)?;

        let mut raw = Vec::new();
        f.read_to_end(&mut raw)
            .map_err(|e| ThresholdCustodyError::AuditLogIo(e.to_string()))?;
        if raw.len() < 44 {
            return Err(ThresholdCustodyError::CorruptedAuditLog(
                "truncated audit log header",
            ));
        }
        if &raw[0..8] != AUDIT_LOG_MAGIC {
            return Err(ThresholdCustodyError::CorruptedAuditLog(
                "audit log magic mismatch",
            ));
        }
        let file_party = u32::from_le_bytes(raw[8..12].try_into().unwrap()) as usize;
        let file_dkg: [u8; 32] = raw[12..44].try_into().unwrap();
        if file_party != party_id || &file_dkg != dkg_digest {
            return Err(ThresholdCustodyError::CorruptedAuditLog(
                "audit log party or DKG transcript mismatch",
            ));
        }
        let body = &raw[44..];
        if body.len() % AUDIT_RECORD_BYTES != 0 {
            return Err(ThresholdCustodyError::CorruptedAuditLog(
                "torn audit log tail (non-integral record length)",
            ));
        }

        let mut head = genesis_hash;
        let mut hw: Option<u64> = None;
        let mut ep_map = BTreeMap::new();
        let mut ct_coms = BTreeSet::new();
        let mut raw_cts = BTreeSet::new();
        let mut count = 0u64;

        for rec in body.chunks_exact(AUDIT_RECORD_BYTES) {
            let epoch = u64::from_le_bytes(rec[0..8].try_into().unwrap());
            let seq = u64::from_le_bytes(rec[8..16].try_into().unwrap());
            let stmt_dig: [u8; 32] = rec[16..48].try_into().unwrap();
            let ct_com: [u8; 32] = rec[48..80].try_into().unwrap();
            let raw_ct_h: [u8; 32] = rec[80..112].try_into().unwrap();
            let eff_ct_h: [u8; 32] = rec[112..144].try_into().unwrap();
            let _cadence = u32::from_le_bytes(rec[144..148].try_into().unwrap());
            let stored_chain: [u8; 32] = rec[148..180].try_into().unwrap();

            let mut ch = Sha256::new();
            ch.update(b"DARKVFHE_AUDIT_CHAIN_V1|");
            ch.update(head);
            ch.update(&rec[0..148]);
            let want_chain: [u8; 32] = ch.finalize().into();
            if want_chain != stored_chain || epoch == 0 {
                return Err(ThresholdCustodyError::CorruptedAuditLog(
                    "hash-chain tamper or zero epoch in persisted audit log",
                ));
            }
            if let Some(prev_hw) = hw {
                if epoch < prev_hw {
                    return Err(ThresholdCustodyError::CorruptedAuditLog(
                        "non-monotonic epoch in persisted audit log",
                    ));
                }
            }
            hw = Some(epoch);
            ep_map.insert((epoch, seq), stmt_dig);
            ct_coms.insert(ct_com);
            raw_cts.insert(raw_ct_h);
            raw_cts.insert(eff_ct_h);
            head = want_chain;
            count += 1;
        }

        Ok(PersistentCustodyAuditLog {
            path: path.to_path_buf(),
            file: f,
            party_id,
            dkg_digest: *dkg_digest,
            head_chain_hash: head,
            poisoned: false,
            high_water_epoch: hw,
            epoch_digests: ep_map,
            opened_ct_commitments: ct_coms,
            opened_raw_ct_handles: raw_cts,
            entry_count: count,
        })
    }

    /// Enforce monotonic epoch latch + single-open rule AND fsync-append through locked fd BEFORE share computation!
    fn check_and_persist_pre_share(
        &mut self,
        auth: &OpeningAuthorization,
        raw_ct_handle: &[u8; 32],
        eff_ct_handle: &[u8; 32],
    ) -> Result<[u8; 32]> {
        let _ = (&self.path, self.party_id, self.dkg_digest);
        if self.poisoned {
            return Err(ThresholdCustodyError::AuditLogPoisoned);
        }
        if auth.epoch == 0 {
            return Err(ThresholdCustodyError::ZeroEpochRejected);
        }
        if let Some(hw) = self.high_water_epoch {
            if auth.epoch < hw {
                return Err(ThresholdCustodyError::StaleEpoch {
                    got: auth.epoch,
                    high_water: hw,
                });
            }
        }
        let stmt_dig = auth.statement_digest();
        if let Some(existing) = self.epoch_digests.get(&(auth.epoch, auth.sequence)) {
            if existing != &stmt_dig {
                return Err(ThresholdCustodyError::ConflictingSameEpochDigest {
                    epoch: auth.epoch,
                });
            }
            return Err(ThresholdCustodyError::DoubleOpen);
        }
        if self.opened_ct_commitments.contains(&auth.ct_commitment)
            || self.opened_raw_ct_handles.contains(raw_ct_handle)
            || self.opened_raw_ct_handles.contains(eff_ct_handle)
        {
            return Err(ThresholdCustodyError::DoubleOpen);
        }

        let mut payload = [0u8; 148];
        payload[0..8].copy_from_slice(&auth.epoch.to_le_bytes());
        payload[8..16].copy_from_slice(&auth.sequence.to_le_bytes());
        payload[16..48].copy_from_slice(&stmt_dig);
        payload[48..80].copy_from_slice(&auth.ct_commitment);
        payload[80..112].copy_from_slice(raw_ct_handle);
        payload[112..144].copy_from_slice(eff_ct_handle);
        payload[144..148].copy_from_slice(&auth.refresh_cadence.to_le_bytes());

        let mut ch = Sha256::new();
        ch.update(b"DARKVFHE_AUDIT_CHAIN_V1|");
        ch.update(self.head_chain_hash);
        ch.update(payload);
        let next_chain: [u8; 32] = ch.finalize().into();

        let mut rec = [0u8; AUDIT_RECORD_BYTES];
        rec[0..148].copy_from_slice(&payload);
        rec[148..180].copy_from_slice(&next_chain);

        if let Err(e) = self.file.write_all(&rec).and_then(|_| self.file.sync_all()) {
            self.poisoned = true;
            return Err(ThresholdCustodyError::AuditLogIo(e.to_string()));
        }

        self.head_chain_hash = next_chain;
        self.high_water_epoch = Some(auth.epoch);
        self.epoch_digests
            .insert((auth.epoch, auth.sequence), stmt_dig);
        self.opened_ct_commitments.insert(auth.ct_commitment);
        self.opened_raw_ct_handles.insert(*raw_ct_handle);
        self.opened_raw_ct_handles.insert(*eff_ct_handle);
        self.entry_count += 1;
        Ok(next_chain)
    }
}

// ================================================================================================
// §4. `GMask61`-Blinded Partial Decryption Proof (`WhirBlindPdProof` — `TVD == 0` on `R_PD` Evals!)
// ================================================================================================

/// Masked random-point evaluations of `(s_{i, 0..3}, e_{sh, i})` at `r_pd^{(0)} in F_{p_0}`:
/// `masked_s_evals[k] = (s_{i,k}(r) + mu_{s,k}(r)) mod p_0`,
/// `masked_e_eval     = (e_{sh,i}(r) + mu_e(r)) mod p_0`,
/// where `(mu_{s,0}, mu_{s,1}, mu_{s,2}, mu_e)` is a 4-slot uniform random blinding row in `pd_whir_pcs`.
/// Because `r_0^0 = 1 != 0`, the linear map `(mu_{s,0..3}, mu_e) -> BlindedRPdEvals` is surjective of
/// exact rank `4` over `F_{p_0}`, achieving **exact `TVD == 0`** (perfect zero disclosure of `(s_i, e_i)`!).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlindedRPdEvals {
    pub masked_s_evals: [u64; 3],
    pub masked_e_eval: u64,
}

/// Self-contained `WhirPcs61 + GMask61` Blinded Partial Decryption Proof (`DVFHEBPD`).
#[derive(Clone, Debug)]
pub struct WhirBlindPdProof {
    pub party_id: usize,
    pub selected_parties: Vec<usize>,
    pub auth_statement_digest: [u8; 32],
    pub partial_rns: Vec<u64>, // 3 * N residues mod Qp
    pub wit_mr: u8,
    pub wit_mc: u8,
    pub t_queries: u16,
    pub blow: u8,
    pub pd_whir_root: [u8; 32],
    pub blinded_evals: BlindedRPdEvals,
    pub logup_proof: LogUpGkrProof,
    pub whir_opening: WhirOpeningBundle61,
}

#[derive(Clone)]
struct AffineLookup61 {
    const_offset: u64,
    terms: Vec<(usize, u64)>,
}

/// Descriptor of one instance of the zero-wrap `Z[X] -> F_{p_0}` Ring-Linear-Mod-`q_k` Gadget (`31` witness slots).
struct RingModQkInstance {
    qk: u64,
    /// `(C_t_coeff[0..N], slot_idx)` with `C_t_coeff[j] in [0, q_k)` and committed `w_t[j] in [0, 2^20)`.
    ring_prod_terms: Vec<(Vec<u64>, usize)>,
    /// `(p_u in 0..=5, mult_c_u, slot_idx)` representing `c_u * 2^{20 * p_u} * z_u[j]`.
    local_20b_terms: Vec<(usize, u64, usize)>,
    /// Public target polynomial `Y_pos[0..N]` with `Y_pos[j] in [0, q_k)`.
    y_pos: Vec<u64>,
    base_slot: usize, // allocates `28` slots: `9` for `R_sh[0..3]`, `9` for `K[0..3]`, `3` for `Q_sh`, `10` for `kappa[0..5]` -> `31` slots!
}

const GADGET_SLOTS: usize = 31;
const R_SHIFT_56: i128 = 1i128 << 56;
const Q_SHIFT_53: i128 = 1i128 << 53;
const KAPPA_SHIFT_23: i128 = 1i128 << 23;

impl RingModQkInstance {
    /// Populate all `31` witness slots in `flat[base_slot * N .. (base_slot + 31) * N]` in `O(N log N)` via NTT!
    fn populate_witness(
        &self,
        engine: &HoistedEngine,
        n: usize,
        flat: &mut [u64],
    ) -> std::result::Result<(), String> {
        let fp0 = &engine.params.fp[0];
        let p0 = fp0.p;
        let inv2 = engine.inv2_mod_p[0];
        let half_p0 = p0 / 2;

        let mut r_signed = vec![vec![0i128; n]; 3];
        for (b, r_b) in r_signed.iter_mut().enumerate() {
            let mut sum_neg = vec![0u64; n];
            let mut sum_cyc = vec![0u64; n];
            for (c_poly, w_slot) in &self.ring_prod_terms {
                let mut c_neg: Vec<u64> = c_poly
                    .iter()
                    .map(|&v| (v >> (21 * b)) & ((1u64 << 21) - 1))
                    .collect();
                let mut c_cyc = c_neg.clone();
                let mut w_neg = flat[w_slot * n..(w_slot + 1) * n].to_vec();
                let mut w_cyc = w_neg.clone();

                engine.neg_ntts[0].forward(&mut c_neg);
                engine.neg_ntts[0].forward(&mut w_neg);
                engine.cyc_ntts[0].forward(&mut c_cyc);
                engine.cyc_ntts[0].forward(&mut w_cyc);

                for j in 0..n {
                    sum_neg[j] = fp0.add(sum_neg[j], fp0.mul(c_neg[j], w_neg[j]));
                    sum_cyc[j] = fp0.add(sum_cyc[j], fp0.mul(c_cyc[j], w_cyc[j]));
                }
            }
            engine.neg_ntts[0].inverse(&mut sum_neg);
            engine.cyc_ntts[0].inverse(&mut sum_cyc);

            let off_r = self.base_slot + b * 3;
            let off_k = self.base_slot + 9 + b * 3;
            for j in 0..n {
                let r_val: i128 = if sum_neg[j] > half_p0 {
                    -((p0 - sum_neg[j]) as i128)
                } else {
                    sum_neg[j] as i128
                };
                r_b[j] = r_val;
                let r_sh = (r_val + R_SHIFT_56) as u64;
                debug_assert!(r_sh < (1u64 << 57));
                flat[off_r * n + j] = r_sh & ((1u64 << 20) - 1);
                flat[(off_r + 1) * n + j] = (r_sh >> 20) & ((1u64 << 20) - 1);
                flat[(off_r + 2) * n + j] = r_sh >> 40;

                if j + 1 < n {
                    let k_val = fp0.mul(fp0.sub(sum_cyc[j], sum_neg[j]), inv2);
                    debug_assert!(k_val < (1u64 << 56));
                    flat[off_k * n + j] = k_val & ((1u64 << 20) - 1);
                    flat[(off_k + 1) * n + j] = (k_val >> 20) & ((1u64 << 20) - 1);
                    flat[(off_k + 2) * n + j] = k_val >> 40;
                }
            }
        }

        // Base-2^20 exact integer division by `q_k` and carry chain `m = 0..5`:
        let qk_i = self.qk as i128;
        let qk_limbs = [
            self.qk & ((1u64 << 20) - 1),
            (self.qk >> 20) & ((1u64 << 20) - 1),
            (self.qk >> 40) & ((1u64 << 20) - 1),
            self.qk >> 60,
        ];
        let a_const_u: u128 = (self.qk as u128) << 53;
        let a_const = extract_6x20(a_const_u);
        let b_shift_const: u128 = (1u128 << 56) + (1u128 << 77) + (1u128 << 98);

        let off_q = self.base_slot + 18;
        let off_kap = self.base_slot + 21;

        for j in 0..n {
            let mut w_int = r_signed[0][j] + (r_signed[1][j] << 21) + (r_signed[2][j] << 42);
            for &(pu, cu, z_slot) in &self.local_20b_terms {
                let zv = flat[z_slot * n + j] as i128;
                w_int += (cu as i128 * zv) << (20 * pu);
            }
            w_int -= self.y_pos[j] as i128;
            if w_int.rem_euclid(qk_i) != 0 {
                return Err(
                    "RingModQkInstance: honest witness failed exact mod-q_k divisibility".into(),
                );
            }
            let q_quot = w_int / qk_i;
            let q_sh = (q_quot + Q_SHIFT_53) as u64;
            if q_sh >= (1u64 << 55) {
                return Err("RingModQkInstance: Q_sh overflowed 55-bit bound".into());
            }
            let qs = [
                q_sh & ((1u64 << 20) - 1),
                (q_sh >> 20) & ((1u64 << 20) - 1),
                q_sh >> 40,
            ];
            for m in 0..3 {
                flat[(off_q + m) * n + j] = qs[m];
            }

            let b_pub = extract_6x20((self.y_pos[j] as u128) + b_shift_const);
            let r0 = [
                flat[self.base_slot * n + j],
                flat[(self.base_slot + 1) * n + j],
                flat[(self.base_slot + 2) * n + j],
            ];
            let r1 = [
                flat[(self.base_slot + 3) * n + j],
                flat[(self.base_slot + 4) * n + j],
                flat[(self.base_slot + 5) * n + j],
            ];
            let r2 = [
                flat[(self.base_slot + 6) * n + j],
                flat[(self.base_slot + 7) * n + j],
                flat[(self.base_slot + 8) * n + j],
            ];

            let mut l_dig = [0i128; 6];
            l_dig[0] = (r0[0] + a_const[0]) as i128;
            l_dig[1] = (r0[1] + 2 * r1[0] + a_const[1]) as i128;
            l_dig[2] = (r0[2] + 2 * r1[1] + 4 * r2[0] + a_const[2]) as i128;
            l_dig[3] = (2 * r1[2] + 4 * r2[1] + a_const[3]) as i128;
            l_dig[4] = (4 * r2[2] + a_const[4]) as i128;
            l_dig[5] = a_const[5] as i128;
            for &(pu, cu, z_slot) in &self.local_20b_terms {
                l_dig[pu] += (cu as i128) * (flat[z_slot * n + j] as i128);
            }

            let mut r_dig = [0i128; 6];
            for (m, &bp_m) in b_pub.iter().enumerate() {
                r_dig[m] = bp_m as i128;
                for (a, &qa) in qk_limbs.iter().enumerate() {
                    for (b_idx, &qb) in qs.iter().enumerate() {
                        if a + b_idx == m {
                            r_dig[m] += (qa as i128) * (qb as i128);
                        }
                    }
                }
            }

            let mut prev_kap = 0i128;
            for m in 0..5 {
                let num = l_dig[m] - r_dig[m] + prev_kap;
                debug_assert_eq!(num.rem_euclid(1i128 << 20), 0);
                let kap = num >> 20;
                let kap_sh = (kap + KAPPA_SHIFT_23) as u64;
                debug_assert!(kap_sh < (1u64 << 24));
                flat[(off_kap + 2 * m) * n + j] = kap_sh & ((1u64 << 20) - 1);
                flat[(off_kap + 2 * m + 1) * n + j] = kap_sh >> 20;
                prev_kap = kap;
            }
            debug_assert_eq!(l_dig[5] - r_dig[5] + prev_kap, 0);
        }
        Ok(())
    }

    fn append_lookup_descs(&self, p0: u64, descs: &mut Vec<AffineLookup61>) {
        let _ = p0;
        // 1. `R_sh[0..3]` (`r_{b,2} < 2^17`) and `K[0..3]` (`k_{b,2} < 2^16`):
        for b in 0..3 {
            let off_r = self.base_slot + b * 3;
            for m in 0..3 {
                descs.push(AffineLookup61 {
                    const_offset: 0,
                    terms: vec![(off_r + m, 1)],
                });
            }
            descs.push(AffineLookup61 {
                const_offset: (1u64 << 20) - (1u64 << 17),
                terms: vec![(off_r + 2, 1)],
            });

            let off_k = self.base_slot + 9 + b * 3;
            for m in 0..3 {
                descs.push(AffineLookup61 {
                    const_offset: 0,
                    terms: vec![(off_k + m, 1)],
                });
            }
            descs.push(AffineLookup61 {
                const_offset: (1u64 << 20) - (1u64 << 16),
                terms: vec![(off_k + 2, 1)],
            });
        }

        // 2. `Q_sh` (`q_2^* < 2^15`):
        let off_q = self.base_slot + 18;
        for m in 0..3 {
            descs.push(AffineLookup61 {
                const_offset: 0,
                terms: vec![(off_q + m, 1)],
            });
        }
        descs.push(AffineLookup61 {
            const_offset: (1u64 << 20) - (1u64 << 15),
            terms: vec![(off_q + 2, 1)],
        });

        // 3. `kappa[0..5]` (`kap_hi < 16`):
        let off_kap = self.base_slot + 21;
        for m in 0..5 {
            descs.push(AffineLookup61 {
                const_offset: 0,
                terms: vec![(off_kap + 2 * m, 1)],
            });
            descs.push(AffineLookup61 {
                const_offset: 0,
                terms: vec![(off_kap + 2 * m + 1, 1)],
            });
            descs.push(AffineLookup61 {
                const_offset: (1u64 << 20) - 16,
                terms: vec![(off_kap + 2 * m + 1, 1)],
            });
        }
    }

    /// Emit the 9 exact `F_{p_0}` polynomial claims (3 ring-reduction + 6 base-2^20 carry equations) at challenge
    /// `r_pt in F_{p_0}`, where `vf_full` = `[1, r, ..., r^{N-1}]` and `vf_deg_n1` = `[1, r, ..., r^{N-2}, 0]`.
    /// Every emitted `rhs` is a **100% PUBLIC** scalar (`0` witness evaluations!).
    fn append_claims_at_point(
        &self,
        fp0: &FastPrime61,
        ctx: &RingModPointCtx<'_>,
        claims: &mut Vec<SlotLinearClaim>,
    ) {
        let RingModPointCtx {
            n,
            r_pt,
            vf_full_idx,
            vf_deg_n1_idx,
            r_pows,
        } = *ctx;
        let ones_r = fp0.ones_eval(n, r_pt);
        let rn_plus_1 = fp0.add(fp0.pow(r_pt, n as u64), 1);
        let t20 = 1u64 << 20;
        let t40 = 1u64 << 40;

        // Identity A (`b = 0, 1, 2`):
        let rhs_a = fp0.neg(fp0.mul(1u64 << 56, ones_r));
        for b in 0..3 {
            let off_r = self.base_slot + b * 3;
            let off_k = self.base_slot + 9 + b * 3;
            let mut full_map: BTreeMap<usize, u64> = BTreeMap::new();
            for (c_poly, w_slot) in &self.ring_prod_terms {
                let mut cb_ev = 0u64;
                for j in 0..n {
                    let cb_j = (c_poly[j] >> (21 * b)) & ((1u64 << 21) - 1);
                    if cb_j != 0 {
                        cb_ev = fp0.add(cb_ev, fp0.mul(cb_j, r_pows[j]));
                    }
                }
                let e = full_map.entry(*w_slot).or_insert(0);
                *e = fp0.add(*e, cb_ev);
            }
            full_map.insert(off_r, fp0.neg(1));
            full_map.insert(off_r + 1, fp0.neg(t20));
            full_map.insert(off_r + 2, fp0.neg(t40));

            let k_terms = vec![
                (off_k, fp0.neg(rn_plus_1)),
                (off_k + 1, fp0.neg(fp0.mul(t20, rn_plus_1))),
                (off_k + 2, fp0.neg(fp0.mul(t40, rn_plus_1))),
            ];
            claims.push(SlotLinearClaim {
                terms: vec![
                    (vf_full_idx, full_map.into_iter().collect()),
                    (vf_deg_n1_idx, k_terms),
                ],
                rhs: rhs_a,
            });
        }

        // Identity B (`m = 0..5` base-2^20 carry chain):
        let qk_limbs = [
            self.qk & ((1u64 << 20) - 1),
            (self.qk >> 20) & ((1u64 << 20) - 1),
            (self.qk >> 40) & ((1u64 << 20) - 1),
            self.qk >> 60,
        ];
        let a_const = extract_6x20((self.qk as u128) << 53);
        let b_shift_const: u128 = (1u128 << 56) + (1u128 << 77) + (1u128 << 98);
        let mut b_pub_evals = [0u64; 6];
        for (j, &rp_j) in r_pows.iter().enumerate().take(n) {
            let bp = extract_6x20((self.y_pos[j] as u128) + b_shift_const);
            for (b_eval, &bp_m) in b_pub_evals.iter_mut().zip(&bp) {
                if bp_m != 0 {
                    *b_eval = fp0.add(*b_eval, fp0.mul(bp_m, rp_j));
                }
            }
        }

        let off_q = self.base_slot + 18;
        let off_kap = self.base_slot + 21;
        let kap_shift_u64 = KAPPA_SHIFT_23 as u64;

        for m in 0..6 {
            let mut slot_w: BTreeMap<usize, u64> = BTreeMap::new();
            let mut add_w = |slot: usize, w: u64| {
                let e = slot_w.entry(slot).or_insert(0);
                *e = fp0.add(*e, w);
            };
            match m {
                0 => add_w(self.base_slot, 1),
                1 => {
                    add_w(self.base_slot + 1, 1);
                    add_w(self.base_slot + 3, 2);
                }
                2 => {
                    add_w(self.base_slot + 2, 1);
                    add_w(self.base_slot + 4, 2);
                    add_w(self.base_slot + 6, 4);
                }
                3 => {
                    add_w(self.base_slot + 5, 2);
                    add_w(self.base_slot + 7, 4);
                }
                4 => {
                    add_w(self.base_slot + 8, 4);
                }
                _ => {}
            }
            for &(pu, cu, z_slot) in &self.local_20b_terms {
                if pu == m {
                    add_w(z_slot, cu % fp0.p);
                }
            }
            for (a, &qa) in qk_limbs.iter().enumerate() {
                for b_idx in 0..3 {
                    if a + b_idx == m && qa != 0 {
                        add_w(off_q + b_idx, fp0.neg(qa));
                    }
                }
            }

            // `L_m - R_m + (kap_sh_{m-1} - 2^23) - 2^20 (kap_sh_m - 2^23) == 0`
            // => committed terms == `b_pub_m - a_const_m * 1 + (1_{m>0} - 2^20 * 1_{m<5}) * 2^23 * 1`:
            let mut rhs = fp0.sub(b_pub_evals[m], fp0.mul(a_const[m], ones_r));
            if m > 0 {
                let kp = m - 1;
                add_w(off_kap + 2 * kp, 1);
                add_w(off_kap + 2 * kp + 1, t20);
                rhs = fp0.add(rhs, fp0.mul(kap_shift_u64, ones_r));
            }
            if m < 5 {
                add_w(off_kap + 2 * m, fp0.neg(t20));
                add_w(off_kap + 2 * m + 1, fp0.neg(t40));
                rhs = fp0.sub(rhs, fp0.mul(t20 * kap_shift_u64, ones_r));
            }
            claims.push(SlotLinearClaim::single_vec(
                vf_full_idx,
                slot_w.into_iter().collect(),
                rhs,
            ));
        }
    }
}

/// Active threshold custodian holding ONLY its Shamir share `s_{shamir, i}`, BDLOP short aggregate opening,
/// enrolled Hybrid-PQ identity, and fsync-backed `PersistentCustodyAuditLog` (`0` single-point viewer!).
pub struct ThresholdCustodianParty {
    pub party_id: usize,
    pub params: Arc<HoistedParams>,
    pub engine: Arc<HoistedEngine>,
    pub roster: EnrolledThresholdRoster,
    pub identity: HybridPqCustodianIdentity,
    pub dkg_transcript: VerifiedThresholdDkgTranscript,
    pub rlk: Arc<RelinearizationKey>,
    s_shamir_rns: Vec<u64>,
    bdlop_agg_open: BdlopShortOpening,
    pub smudge_bound: u128,
    pub smudge_top_bits: u32,
    pub pinned_policy_digest: [u8; 32],
    pub tvd_40b_strict_mode: bool,
    pub r_refresh_correctness: u32,
    pub audit_log: PersistentCustodyAuditLog,
    pub verified_persistent_a_roots: BTreeSet<[u8; 32]>,
    pub signer_min_pq_leaves: Vec<u64>,
}

impl Drop for ThresholdCustodianParty {
    fn drop(&mut self) {
        for v in &mut self.s_shamir_rns {
            unsafe { std::ptr::write_volatile(v, 0) };
        }
    }
}

impl ThresholdCustodianParty {
    /// Pin an offline-verified persistent `WhirPersistentGridPcs` matrix root (`Enc(W)` / `Enc(E)`).
    pub fn register_verified_persistent_whir_root(&mut self, a_root: [u8; 32]) {
        self.verified_persistent_a_roots.insert(a_root);
    }

    /// Reload crash-consistent `PersistentCustodyAuditLog` from disk (simulating custodian process restart!).
    /// Any corruption or missing-log error permanently poisons this custodian instance against future openings.
    pub fn reload_audit_log_from_disk(&mut self, path: &Path) -> Result<()> {
        let _ = unsafe { libc::flock(self.audit_log.file.as_raw_fd(), libc::LOCK_UN) };
        match PersistentCustodyAuditLog::reopen_existing(
            path,
            self.party_id,
            &self.dkg_transcript.digest,
        ) {
            Ok(reloaded) => {
                self.audit_log = reloaded;
                Ok(())
            }
            Err(e) => {
                self.audit_log.poisoned = true;
                Err(e)
            }
        }
    }

    /// **Gated Threshold Partial Decryption (`G10`)**:
    /// 1. Enforces non-poisoned audit log, roster & DKG transcript integrity, `tvd_40b_strict_mode` (`R_refresh == 1`),
    ///    `epoch != 0`, `epoch >= high_water`, `policy_digest`, canonical `t`-quorum selection, and `t` distinct `HybridPqSignature`s;
    /// 2. Standalone-verifies the `WhirPcs61` (`DVFHEWH1`) compute proof (`verify_hoisted_whir_bytes`) AND
    ///    deterministic RNS-gadget relinearization `relinearize_ct3(out_ct3, rlk) == *target_ct2`;
    /// 3. Fsync-persists the `OpeningAuthorization` (with both raw and effective ciphertext handles) into `self.audit_log`
    ///    **BEFORE** touching `s_shamir_rns`;
    /// 4. Emits Lagrange-weighted smudged partial decryption `d_i` + `GMask61`-blinded `WhirBlindPdProof`!
    pub fn partial_decrypt_relinearized_ct2_gated(
        &mut self,
        auth: &OpeningAuthorization,
        whir_compute: &WhirComputeProvenance<'_>,
        target_ct2: &Ct,
        ct_mask_r: Option<&Ct>,
    ) -> Result<WhirBlindPdProof> {
        if self.audit_log.poisoned {
            return Err(ThresholdCustodyError::AuditLogPoisoned);
        }
        self.roster.verify_integrity()?;
        self.dkg_transcript.verify_integrity(&self.params)?;
        // 1. Strict refresh cadence gate (`R_refresh == 1` in `tvd_40b_strict_mode`):
        if self.tvd_40b_strict_mode {
            if auth.refresh_cadence != 1 || auth.turns_since_refresh != 0 {
                return Err(ThresholdCustodyError::StrictRefreshCadenceViolation {
                    got: auth.refresh_cadence,
                    turns_since_refresh: auth.turns_since_refresh,
                });
            }
        } else if auth.refresh_cadence == 0
            || auth.refresh_cadence > self.r_refresh_correctness
            || auth.turns_since_refresh >= auth.refresh_cadence
        {
            return Err(ThresholdCustodyError::StrictRefreshCadenceViolation {
                got: auth.refresh_cadence,
                turns_since_refresh: auth.turns_since_refresh,
            });
        }

        // 2. Authorization envelope & quorum roster checks:
        if auth.epoch == 0 {
            return Err(ThresholdCustodyError::ZeroEpochRejected);
        }
        if auth.policy_digest != self.pinned_policy_digest {
            return Err(ThresholdCustodyError::PolicyDigestMismatch);
        }
        if auth.dkg_transcript_digest != self.dkg_transcript.digest {
            return Err(ThresholdCustodyError::DkgTranscriptMismatch);
        }
        let t_need = self.roster.threshold;
        if auth.selected_parties.len() != t_need
            || auth.selected_parties.windows(2).any(|w| w[0] >= w[1])
            || auth
                .selected_parties
                .iter()
                .any(|&p| p >= self.roster.n_parties)
        {
            return Err(ThresholdCustodyError::NonCanonicalQuorumRoster);
        }
        if !auth.selected_parties.contains(&self.party_id) {
            return Err(ThresholdCustodyError::PartyNotSelected {
                party: self.party_id,
            });
        }

        // 3. Verify `t`-quorum Hybrid-PQ (`RFC 8032 Ed25519` + `SHA-256 Merkle-Lamport PQ`) signatures:
        if auth.quorum_signatures.len() < t_need {
            return Err(ThresholdCustodyError::QuorumSignaturesInsufficient {
                have: auth.quorum_signatures.len(),
                need: t_need,
            });
        }
        let pre = auth.signing_preimage();
        let mut sig_signers = BTreeSet::new();
        let mut next_leaves = self.signer_min_pq_leaves.clone();
        for sig in &auth.quorum_signatures {
            if sig.signer_id >= self.roster.n_parties || !sig_signers.insert(sig.signer_id) {
                return Err(ThresholdCustodyError::HybridSignatureInvalid(
                    "duplicate or out-of-range quorum signer",
                ));
            }
            let used_leaf = sig.verify(
                &self.roster.enrollments[sig.signer_id],
                self.signer_min_pq_leaves[sig.signer_id],
                &pre,
            )?;
            next_leaves[sig.signer_id] = used_leaf + 1;
        }

        // 4. Verify `WhirPcs61` (`DVFHEWH1`) compute provenance + deterministic RNS-gadget relinearization!
        let computed_prf_dig: [u8; 32] = Sha256::digest(whir_compute.whir_proof_bytes).into();
        if computed_prf_dig != auth.compute_proof_digest {
            return Err(ThresholdCustodyError::InvalidWhirComputeProof(
                "compute_proof_digest != SHA256(whir_proof_bytes)".into(),
            ));
        }
        if let Some(exp_root) = whir_compute.expected_persistent_a_root {
            if !self.verified_persistent_a_roots.contains(exp_root) {
                return Err(ThresholdCustodyError::InvalidWhirComputeProof(
                    "expected_persistent_a_root is not pinned on custodian".into(),
                ));
            }
        }
        verify_hoisted_whir_bytes(
            &self.params,
            whir_compute.ha_grid,
            whir_compute.hb_vec,
            whir_compute.hout_vec,
            whir_compute.opened_a,
            whir_compute.expected_persistent_a_root,
            whir_compute.opened_b,
            whir_compute.out_cts,
            whir_compute.whir_proof_bytes,
        )
        .map_err(ThresholdCustodyError::InvalidWhirComputeProof)?;

        let out_ct3 = whir_compute
            .out_cts
            .get(whir_compute.target_output_row)
            .ok_or_else(|| {
                ThresholdCustodyError::InvalidWhirComputeProof(
                    "target_output_row out of bounds".into(),
                )
            })?;
        let want_relin = self.engine.relinearize_ct3(out_ct3, &self.rlk);
        if want_relin.c0 != target_ct2.c0 || want_relin.c1 != target_ct2.c1 {
            return Err(ThresholdCustodyError::InvalidWhirComputeProof(
                "target_ct2 != relinearize_ct3(verified_out_ct3, rlk)".into(),
            ));
        }

        let raw_target_handle = ct2_handle(target_ct2);
        let mask_handle = ct_mask_r.map(ct2_handle);
        let want_ct_com = compute_ct_opening_commitment(
            &raw_target_handle,
            mask_handle.as_ref(),
            &auth.selected_parties,
        );
        if want_ct_com != auth.ct_commitment {
            return Err(ThresholdCustodyError::InvalidWhirComputeProof(
                "auth.ct_commitment != canonical commitment of target_ct2".into(),
            ));
        }

        let ct_eff = match ct_mask_r {
            Some(mr) => subtract_ct2(&self.params, target_ct2, mr),
            None => target_ct2.clone(),
        };
        let eff_target_handle = ct2_handle(&ct_eff);

        // 5. PERSIST-BEFORE-SHARE: fsync to append-only audit log BEFORE touching `s_shamir_rns`!
        let _chain_hash = self.audit_log.check_and_persist_pre_share(
            auth,
            &raw_target_handle,
            &eff_target_handle,
        )?;
        self.signer_min_pq_leaves = next_leaves;

        // 6. Sample `/dev/urandom` smudge & prove `WhirBlindPdProof` bound to `auth.statement_digest()`:
        let mut smudge_rng = PcsRng::from_seed(os_csprng_seed32());
        let e_smudge = sample_smudge_poly(self.params.n, self.smudge_bound, &mut smudge_rng);
        let auth_stmt_dig = auth.statement_digest();

        prove_blind_r_pd_whir61(
            &self.engine,
            self.party_id,
            &auth.selected_parties,
            &auth_stmt_dig,
            &self.dkg_transcript,
            &self.s_shamir_rns,
            &self.bdlop_agg_open,
            self.smudge_bound,
            self.smudge_top_bits,
            &ct_eff,
            &e_smudge,
            &auth.ct_commitment,
        )
        .map_err(ThresholdCustodyError::InvalidBlindPdProof)
    }

    /// Test-only adversarial prover entry point allowing mutated `s_shamir_rns` or `e_smudge` to verify refusal.
    pub fn prove_unverified_custom_witness_for_test(
        &self,
        selected_parties: &[usize],
        auth_statement_digest: &[u8; 32],
        ct_eff: &Ct,
        custom_s_rns: &[u64],
        custom_e_smudge: &[i128],
        ct_commitment: &[u8; 32],
    ) -> std::result::Result<WhirBlindPdProof, String> {
        prove_blind_r_pd_whir61(
            &self.engine,
            self.party_id,
            selected_parties,
            auth_statement_digest,
            &self.dkg_transcript,
            custom_s_rns,
            &self.bdlop_agg_open,
            self.smudge_bound,
            self.smudge_top_bits,
            ct_eff,
            custom_e_smudge,
            ct_commitment,
        )
    }

    /// Test-only adversarial forger that bypasses prover-side `|e| <= E` check with `e[0] = E + 1` (`e_sh = 2E + 1`,
    /// `e_rev = 0`, all LogUp range checks and `RingModQkInstance` equations satisfied!) so `verify_blind_r_pd_whir61`
    /// itself is exercised on the exact `e_sh + e_rev == 2E` upper-bound constraint!
    pub fn forge_e_plus_1_proof_bypassing_prover_for_test(
        &self,
        selected_parties: &[usize],
        auth_statement_digest: &[u8; 32],
        ct_eff: &Ct,
        ct_commitment: &[u8; 32],
    ) -> std::result::Result<WhirBlindPdProof, String> {
        let mut e_bad = vec![0i128; self.params.n];
        e_bad[0] = (self.smudge_bound + 1) as i128;
        prove_blind_r_pd_whir61_inner(
            &self.engine,
            self.party_id,
            selected_parties,
            auth_statement_digest,
            &self.dkg_transcript,
            &self.s_shamir_rns,
            &self.bdlop_agg_open,
            self.smudge_bound,
            self.smudge_top_bits,
            ct_eff,
            &e_bad,
            ct_commitment,
            true,
        )
    }
}

///Compute Lagrange coefficient `\lambda_{party, S}(0) = \prod_{j \in S, j != party} (-x_j)/(x_{party} - x_j) mod q` (`x_p = p + 1`).
pub fn lagrange_coeff_at_zero_mod_q(party: usize, selected: &[usize], q: u64) -> u64 {
    let xi = (party + 1) as u64;
    let mut num = 1u64;
    let mut den = 1u64;
    for &peer in selected {
        if peer == party {
            continue;
        }
        let xj = (peer + 1) as u64;
        num = mulmod(num, q - (xj % q), q);
        let diff = if xi >= xj { xi - xj } else { q - (xj - xi) };
        den = mulmod(den, diff, q);
    }
    mulmod(num, invmod(den, q), q)
}

#[allow(clippy::too_many_arguments)]
fn build_blind_pd_gadgets_and_descs(
    params: &HoistedParams,
    party_id: usize,
    selected_parties: &[usize],
    dkg_transcript: &VerifiedThresholdDkgTranscript,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_eff: &Ct,
    partial_rns: &[u64],
) -> (Vec<RingModQkInstance>, Vec<AffineLookup61>, usize, usize) {
    let n = params.n;
    let rns_q = Rns::new(n, &params.qp, params.t);
    let fp0 = &params.fp[0];
    let p0 = fp0.p;

    // Slot layout in `pd_whir_pcs`:
    // - `0..15`:  `s_{i, 0}, s_{i, 1}, s_{i, 2}` (`5` ExactGarner zero-slack `[0, q_k)` cols per prime!)
    // - `15..18`: `R_1 + 128`, `E_0 + 128`, `E_1 + 128` (`in [0, 256]`)
    // - `18..24`: `e_{sh, i} = e_i + E` (`6` 20-bit cols, col 23 `< 2^{smudge_top_bits}`)
    // - `24..30`: `e_{rev, i} = 2E - e_{sh, i}` (`6` 20-bit cols `< 2^20`, exact verifier-side `e_sh <= 2E`!)
    // - `30..32`: `c_{rev, 0}, c_{rev, 1} in {0, 1}` (two boolean 40-bit pair carries for `e_sh + e_rev == 2E`)
    // - `32..36`: Auxiliary `R_PD` blinding row `(mu_{s,0}, mu_{s,1}, mu_{s,2}, mu_e) in (F_{p_0}^N)^4` (`TVD == 0`!)
    // - `36 .. 36 + 9 * 31 (= 315)`: 9 `RingModQkInstance`s (`3` primes x `(R_PD, BDLOP_T0, BDLOP_T1)`)
    // - `315 .. 315 + TABLE_SIZE / N`: `D1b` LogUp-GKR multiplicity slots!
    let off_mask = 32usize;
    let off_gadgets = 36usize;

    let gspec = ExactGarnerSpec::new(params);
    let inv2_20 = invmod(1u64 << 20, p0);
    let mut descs = Vec::new();

    // 1. Zero-slack `[0, q_k)` ExactGarner15 lookups for `s_{i, 0..3}` (`slots 0..15`):
    for k_idx in 0..3 {
        let base = 5 * k_idx;
        let delta = gspec.deltas[k_idx];
        let (d0, d1, d2, d3, v0) = (base, base + 1, base + 2, base + 3, base + 4);
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(d0, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(d1, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 1u64 << 19,
            terms: vec![(d1, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(d2, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 3 * (1u64 << 18),
            terms: vec![(d2, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(d3, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: (1u64 << 20) - 16,
            terms: vec![(d3, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(v0, 1)],
        });

        // Boolean carry `c_k = (d_0 + delta - v_0) * 2^{-20} mod p_0 in {0, 1}`:
        let c_const = fp0.mul(delta, inv2_20);
        let c_terms = vec![(d0, inv2_20), (v0, fp0.neg(inv2_20))];
        descs.push(AffineLookup61 {
            const_offset: c_const,
            terms: c_terms.clone(),
        });
        descs.push(AffineLookup61 {
            const_offset: fp0.add(c_const, (1u64 << 20) - 2),
            terms: c_terms,
        });

        // Boundary complement `T_k = ((2^19-1) + (2^18-1) + 15) - (d_1 + d_2 + d_3 + c_k) in [0, 2^20)`:
        let pos_sum = ((1u64 << 19) - 1) + ((1u64 << 18) - 1) + 15;
        descs.push(AffineLookup61 {
            const_offset: fp0.sub(pos_sum, c_const),
            terms: vec![
                (d1, fp0.neg(1)),
                (d2, fp0.neg(1)),
                (d3, fp0.neg(1)),
                (d0, fp0.neg(inv2_20)),
                (v0, inv2_20),
            ],
        });
    }

    // 2. Short BDLOP aggregate opening bounds `R_1 + 128, E_0 + 128, E_1 + 128 in [0, 256]` (`slots 15..18`):
    for sl in 15..18 {
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(sl, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: (1u64 << 20) - BDLOP_AGG_SPAN,
            terms: vec![(sl, 1)],
        });
    }

    // 3. Smudge bound `e_i + E in [0, 2E]` (`slots 18..24` + complement `e_rev` `slots 24..30` + boolean carries `30..32`):
    for m in 0..6 {
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(18 + m, 1)],
        });
    }
    descs.push(AffineLookup61 {
        const_offset: (1u64 << 20) - (1u64 << smudge_top_bits),
        terms: vec![(23, 1)],
    });
    for m in 0..6 {
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(24 + m, 1)],
        });
    }
    for c_sl in 30..32 {
        descs.push(AffineLookup61 {
            const_offset: 0,
            terms: vec![(c_sl, 1)],
        });
        descs.push(AffineLookup61 {
            const_offset: (1u64 << 20) - 2,
            terms: vec![(c_sl, 1)],
        });
    }

    // 4. Construct the 9 `RingModQkInstance`s across `k = 0, 1, 2`:
    //    - `g_idx = 3 * k + 0`: `R_PD` (`(lambda_k * c'_{1,k}) * s_{i,k} + e_{sh,i} == d_{i,k} + E * 1 (mod X^N+1, q_k)`)
    //    - `g_idx = 3 * k + 1`: `BDLOP T_0` (`a_{1,k} * R_1 + a_{2,k} * E_1 + E_0 == T_{0,i,k} (mod X^N+1, q_k)`)
    //    - `g_idx = 3 * k + 2`: `BDLOP T_1` (`b_{1,k} * R_1 + E_1 + s_{i,k} == T_{1,i,k} (mod X^N+1, q_k)`)
    let anchor = &dkg_transcript.party_bdlop_anchors[party_id];
    let ones_poly = vec![1i64; n];
    let mut ones_ntt = rns_q.from_signed(&ones_poly);
    rns_q.fwd(&mut ones_ntt);

    let shift_const_prod = |c_slice: &[u64], k_idx: usize, shift: u64| -> Vec<u64> {
        let qk = params.qp[k_idx];
        let ntt_k = &darkstep::ntt::Ntt::new(qk, n);
        let mut a = c_slice.to_vec();
        let mut o = vec![shift % qk; n];
        ntt_k.forward(&mut a);
        ntt_k.forward(&mut o);
        let mut p: Vec<u64> = a.iter().zip(&o).map(|(&x, &y)| mulmod(x, y, qk)).collect();
        ntt_k.inverse(&mut p);
        p
    };
    let _ = ones_ntt;

    let mut gadgets = Vec::with_capacity(9);
    let mut cur_slot = off_gadgets;

    for k_idx in 0..3 {
        let qk = params.qp[k_idx];
        let lam_k = lagrange_coeff_at_zero_mod_q(party_id, selected_parties, qk);
        let a_pd_base: Vec<u64> = (0..n)
            .map(|j| mulmod(lam_k, ct_eff.c1[k_idx * n + j], qk))
            .collect();

        // `s_{i,k} = d_0 + 2^20 d_1 + 2^39 d_2 + 2^57 d_3`:
        let shifts = [0u32, 20, 39, 57];
        let s_base = 5 * k_idx;
        let pd_prod_terms: Vec<(Vec<u64>, usize)> = (0..4)
            .map(|m| {
                let mult = powmod(2, shifts[m] as u64, qk);
                let cm: Vec<u64> = a_pd_base.iter().map(|&v| mulmod(v, mult, qk)).collect();
                (cm, s_base + m)
            })
            .collect();
        let pd_local_terms: Vec<(usize, u64, usize)> = (0..6).map(|m| (m, 1u64, 18 + m)).collect();
        let e_mod_qk = (smudge_bound % (qk as u128)) as u64;
        let pd_y_pos: Vec<u64> = (0..n)
            .map(|j| addmod(partial_rns[k_idx * n + j], e_mod_qk, qk))
            .collect();
        let g_pd = RingModQkInstance {
            qk,
            ring_prod_terms: pd_prod_terms,
            local_20b_terms: pd_local_terms,
            y_pos: pd_y_pos,
            base_slot: cur_slot,
        };
        g_pd.append_lookup_descs(p0, &mut descs);
        gadgets.push(g_pd);
        cur_slot += GADGET_SLOTS;

        // `BDLOP T_0`: `a_1 (R_1 + 128) + a_2 (E_1 + 128) + (E_0 + 128) == T_0 + 128*(a_1*1 + a_2*1 + 1) (mod q_k)`:
        let a1_k = dkg_transcript.bdlop_crs.a1_coeff[k_idx * n..(k_idx + 1) * n].to_vec();
        let a2_k = dkg_transcript.bdlop_crs.a2_coeff[k_idx * n..(k_idx + 1) * n].to_vec();
        let off_a1 = shift_const_prod(&a1_k, k_idx, BDLOP_AGG_SHIFT as u64);
        let off_a2 = shift_const_prod(&a2_k, k_idx, BDLOP_AGG_SHIFT as u64);
        let t0_y_pos: Vec<u64> = (0..n)
            .map(|j| {
                addmod(
                    addmod(anchor.t0_coeff[k_idx * n + j], off_a1[j], qk),
                    addmod(off_a2[j], BDLOP_AGG_SHIFT as u64, qk),
                    qk,
                )
            })
            .collect();
        let g_t0 = RingModQkInstance {
            qk,
            ring_prod_terms: vec![(a1_k, 15), (a2_k, 17)],
            local_20b_terms: vec![(0, 1, 16)],
            y_pos: t0_y_pos,
            base_slot: cur_slot,
        };
        g_t0.append_lookup_descs(p0, &mut descs);
        gadgets.push(g_t0);
        cur_slot += GADGET_SLOTS;

        // `BDLOP T_1`: `b_1 (R_1 + 128) + (E_1 + 128) + s_{i,k} == T_1 + 128*(b_1*1 + 1) (mod q_k)`:
        let b1_k = dkg_transcript.bdlop_crs.b1_coeff[k_idx * n..(k_idx + 1) * n].to_vec();
        let off_b1 = shift_const_prod(&b1_k, k_idx, BDLOP_AGG_SHIFT as u64);
        let t1_y_pos: Vec<u64> = (0..n)
            .map(|j| {
                addmod(
                    anchor.t1_coeff[k_idx * n + j],
                    addmod(off_b1[j], BDLOP_AGG_SHIFT as u64, qk),
                    qk,
                )
            })
            .collect();
        let g_t1 = RingModQkInstance {
            qk,
            ring_prod_terms: vec![(b1_k, 15)],
            local_20b_terms: vec![
                (0, 1, 17),
                (0, 1, s_base),
                (1, 1, s_base + 1),
                (1, 1u64 << 19, s_base + 2),
                (2, 1u64 << 17, s_base + 3),
            ],
            y_pos: t1_y_pos,
            base_slot: cur_slot,
        };
        g_t1.append_lookup_descs(p0, &mut descs);
        gadgets.push(g_t1);
        cur_slot += GADGET_SLOTS;
    }

    (gadgets, descs, off_mask, cur_slot)
}

/// Prove `GMask61`-Blinded Partial Decryption (`WhirBlindPdProof`) with **exact `TVD == 0`** on `R_PD` evaluations!
#[allow(clippy::too_many_arguments)]
pub fn prove_blind_r_pd_whir61(
    engine: &HoistedEngine,
    party_id: usize,
    selected_parties: &[usize],
    auth_statement_digest: &[u8; 32],
    dkg_transcript: &VerifiedThresholdDkgTranscript,
    s_shamir_rns: &[u64],
    bdlop_open: &BdlopShortOpening,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_eff: &Ct,
    e_smudge: &[i128],
    ct_commitment: &[u8; 32],
) -> std::result::Result<WhirBlindPdProof, String> {
    prove_blind_r_pd_whir61_inner(
        engine,
        party_id,
        selected_parties,
        auth_statement_digest,
        dkg_transcript,
        s_shamir_rns,
        bdlop_open,
        smudge_bound,
        smudge_top_bits,
        ct_eff,
        e_smudge,
        ct_commitment,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_blind_r_pd_whir61_inner(
    engine: &HoistedEngine,
    party_id: usize,
    selected_parties: &[usize],
    auth_statement_digest: &[u8; 32],
    dkg_transcript: &VerifiedThresholdDkgTranscript,
    s_shamir_rns: &[u64],
    bdlop_open: &BdlopShortOpening,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_eff: &Ct,
    e_smudge: &[i128],
    ct_commitment: &[u8; 32],
    bypass_smudge_check_for_test: bool,
) -> std::result::Result<WhirBlindPdProof, String> {
    dkg_transcript
        .verify_integrity(&engine.params)
        .map_err(|e| format!("DKG transcript integrity check failed: {e}"))?;
    let params = &engine.params;
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];

    // 1. Compute Lagrange-weighted smudged decryption share `partial_rns` (`d_{i,k} = lambda_{i,S,k} * c'_{1,k} * s_{i,k} + e_i mod q_k`):
    let mut partial_rns = vec![0u64; 3 * n];
    for k_idx in 0..3 {
        let qk = params.qp[k_idx];
        let lam_k = lagrange_coeff_at_zero_mod_q(party_id, selected_parties, qk);
        let mut s_ntt = s_shamir_rns[k_idx * n..(k_idx + 1) * n].to_vec();
        let mut c1_ntt: Vec<u64> = ct_eff.c1[k_idx * n..(k_idx + 1) * n]
            .iter()
            .map(|&v| mulmod(lam_k, v, qk))
            .collect();
        engine.neg_ntts[k_idx].forward(&mut s_ntt);
        engine.neg_ntts[k_idx].forward(&mut c1_ntt);
        let mut prod: Vec<u64> = s_ntt
            .iter()
            .zip(&c1_ntt)
            .map(|(&a, &b)| mulmod(a, b, qk))
            .collect();
        engine.neg_ntts[k_idx].inverse(&mut prod);
        for j in 0..n {
            let ej_mod = e_smudge[j].rem_euclid(qk as i128) as u64;
            partial_rns[k_idx * n + j] = addmod(prod[j], ej_mod, qk);
        }
    }

    let (gadgets, descs, off_mask, off_mult) = build_blind_pd_gadgets_and_descs(
        params,
        party_id,
        selected_parties,
        dkg_transcript,
        smudge_bound,
        smudge_top_bits,
        ct_eff,
        &partial_rns,
    );
    let mult_slots = (TABLE_SIZE / n).max(1);
    let total_slots = off_mult + mult_slots;
    let mut flat = vec![0u64; total_slots * n];

    // Pack `s_{i, 0..3}` (`ExactGarner15` 5-col blocks):
    let gspec = ExactGarnerSpec::new(params);
    for k_idx in 0..3 {
        let qk = params.qp[k_idx];
        let delta = gspec.deltas[k_idx];
        let base = 5 * k_idx;
        for j in 0..n {
            let ri = s_shamir_rns[k_idx * n + j];
            if ri >= qk {
                return Err("non-canonical s_shamir_rns >= q_k".into());
            }
            let d0 = ri & ((1u64 << 20) - 1);
            let d1 = (ri >> 20) & ((1u64 << 19) - 1);
            let d2 = (ri >> 39) & ((1u64 << 18) - 1);
            let d3 = ri >> 57;
            let v0 = (d0 + delta) & ((1u64 << 20) - 1);
            flat[base * n + j] = d0;
            flat[(base + 1) * n + j] = d1;
            flat[(base + 2) * n + j] = d2;
            flat[(base + 3) * n + j] = d3;
            flat[(base + 4) * n + j] = v0;
        }
    }

    // Pack shifted BDLOP short aggregate opening `(R_1 + 128, E_0 + 128, E_1 + 128)`:
    for j in 0..n {
        let r1s = bdlop_open.r1[j] + BDLOP_AGG_SHIFT;
        let e0s = bdlop_open.e0[j] + BDLOP_AGG_SHIFT;
        let e1s = bdlop_open.e1[j] + BDLOP_AGG_SHIFT;
        if !(0..BDLOP_AGG_SPAN as i64).contains(&r1s)
            || !(0..BDLOP_AGG_SPAN as i64).contains(&e0s)
            || !(0..BDLOP_AGG_SPAN as i64).contains(&e1s)
        {
            return Err("BDLOP aggregate opening out of [-128, 128] bound".into());
        }
        flat[15 * n + j] = r1s as u64;
        flat[16 * n + j] = e0s as u64;
        flat[17 * n + j] = e1s as u64;
    }

    // Pack shifted smudge `e_i + E in [0, 2E]` (`18..24`), exact complement `e_rev = 2E - e_sh` (`24..30`),
    // and boolean 40-bit pair carries `c_{rev,0..2}` (`30..32`):
    let top_lim = 1u64 << smudge_top_bits;
    let two_e = 2 * smudge_bound;
    for j in 0..n {
        if !bypass_smudge_check_for_test && e_smudge[j].unsigned_abs() > smudge_bound {
            return Err("smudging noise |e_i| > E".into());
        }
        let es_i = e_smudge[j] + (smudge_bound as i128);
        if es_i < 0 {
            return Err("smudging noise < -E".into());
        }
        let es = es_i as u128;
        for m in 0..5 {
            flat[(18 + m) * n + j] = ((es >> (20 * m)) & ((1 << 20) - 1)) as u64;
        }
        let top = (es >> 100) as u64;
        if top >= top_lim {
            return Err("smudging top limb overflow".into());
        }
        flat[23 * n + j] = top;

        let erev = two_e.saturating_sub(es);
        for m in 0..6 {
            flat[(24 + m) * n + j] = ((erev >> (20 * m)) & ((1 << 20) - 1)) as u64;
        }
        let a0 = flat[18 * n + j] + (flat[19 * n + j] << 20);
        let b0 = flat[24 * n + j] + (flat[25 * n + j] << 20);
        let c0 = ((a0 + b0) >> 40) & 1;
        let a1 = flat[20 * n + j] + (flat[21 * n + j] << 20);
        let b1 = flat[26 * n + j] + (flat[27 * n + j] << 20);
        let c1 = ((a1 + b1 + c0) >> 40) & 1;
        flat[30 * n + j] = c0;
        flat[31 * n + j] = c1;
    }

    // Rejection-sample exact uniform auxiliary `R_PD` blinding row `(mu_{s,0..3}, mu_e) in (F_{p_0}^N)^4`
    // directly from OS `/dev/urandom` (`0` PRG seed bottleneck, `0` modular reduction bias -> exact `TVD == 0`!):
    sample_os_fp_exact_slice(fp0.p, &mut flat[off_mask * n..(off_mask + 4) * n])?;

    // Populate all 9 `RingModQkInstance` witness slots:
    for g in &gadgets {
        g.populate_witness(engine, n, &mut flat)?;
    }

    // Materialize `D1b` LogUp-GKR lookup entries & multiplicities:
    let lookup_entries: Vec<u64> = descs
        .par_iter()
        .flat_map_iter(|d| {
            (0..n).map(|j| {
                let mut v = d.const_offset;
                for &(sl, w) in &d.terms {
                    v = fp0.add(v, fp0.mul(flat[sl * n + j], w));
                }
                v
            })
        })
        .collect();
    let mults = count_multiplicities_parallel(&lookup_entries)?;
    flat[off_mult * n..off_mult * n + TABLE_SIZE].copy_from_slice(&mults);

    // Commit single fresh `WhirCommittedPcs61` (`GMask61` + 4 ZK data rows + salted Stage-0 fibers):
    let pd_whir = WhirCommittedPcs61::commit_with_rng(
        fp0,
        &flat,
        log_n,
        WHIR_T_QUERIES_128,
        WHIR_BLOWUP,
        PcsRng::from_seed(os_csprng_seed32()),
    );

    let fs_ctx = compute_blind_pd_fs_ctx(
        party_id,
        selected_parties,
        auth_statement_digest,
        dkg_transcript,
        smudge_bound,
        smudge_top_bits,
        ct_commitment,
        &ct2_handle(ct_eff),
        &partial_rns,
        &pd_whir.root,
    );
    let r_pts: [u64; 3] =
        std::array::from_fn(|idx| derive_blind_pd_point(&fs_ctx, fp0.p, idx as u64));

    let chunk_log2 = (log_n + 6).max(18);
    let logup_proof = prove_logup_gkr_with_mults(
        &fp0,
        &lookup_entries,
        &mults,
        LogUpConfig::BatchedC3 { chunk_log2 },
        &fs_ctx,
    );

    // Compute `BlindedRPdEvals` at `r_pts[0]` (`TVD == 0` via `off_mask .. off_mask + 4`!):
    let r0_pows = build_pows(&fp0, r_pts[0], n);
    let s_limb_w = [1u64, 1u64 << 20, 1u64 << 39, 1u64 << 57];
    let mut masked_s_evals = [0u64; 3];
    for k_idx in 0..3 {
        let base = 5 * k_idx;
        let mut s_ev = 0u64;
        for m in 0..4 {
            let dm = fp0.dot(&flat[(base + m) * n..(base + m + 1) * n], &r0_pows);
            s_ev = fp0.add(s_ev, fp0.mul(s_limb_w[m], dm));
        }
        let mu_ev = fp0.dot(
            &flat[(off_mask + k_idx) * n..(off_mask + k_idx + 1) * n],
            &r0_pows,
        );
        masked_s_evals[k_idx] = fp0.add(s_ev, mu_ev);
    }
    let mut e_ev = 0u64;
    for m in 0..6 {
        let w = fp0.pow(2, (20 * m) as u64);
        let dm = fp0.dot(&flat[(18 + m) * n..(18 + m + 1) * n], &r0_pows);
        e_ev = fp0.add(e_ev, fp0.mul(w, dm));
    }
    let mu_e_ev = fp0.dot(&flat[(off_mask + 3) * n..(off_mask + 4) * n], &r0_pows);
    let masked_e_eval = fp0.add(e_ev, mu_e_ev);
    let blinded_evals = BlindedRPdEvals {
        masked_s_evals,
        masked_e_eval,
    };

    let (v_fams, claims, open_ctx) = build_blind_pd_whir_claims(
        params,
        party_id,
        selected_parties,
        ct_eff,
        &partial_rns,
        smudge_bound,
        &gadgets,
        &descs,
        off_mask,
        off_mult,
        &fs_ctx,
        &r_pts,
        &blinded_evals,
        &logup_proof,
    )?;

    let mut claims_for_open = claims;
    if bypass_smudge_check_for_test {
        for cl in &mut claims_for_open {
            let mut actual_rhs = 0u64;
            for (vf_idx, sl_terms) in &cl.terms {
                let vf = &v_fams[*vf_idx];
                for &(sl, w) in sl_terms {
                    let ev = fp0.dot(&flat[sl * n..(sl + 1) * n], vf);
                    actual_rhs = fp0.add(actual_rhs, fp0.mul(w, ev));
                }
            }
            cl.rhs = actual_rhs;
        }
    }
    let whir_opening = pd_whir.open_whir_slot_claims(log_n, &v_fams, &claims_for_open, &open_ctx);

    Ok(WhirBlindPdProof {
        party_id,
        selected_parties: selected_parties.to_vec(),
        auth_statement_digest: *auth_statement_digest,
        partial_rns,
        wit_mr: pd_whir.shape.mr as u8,
        wit_mc: pd_whir.shape.mc as u8,
        t_queries: pd_whir.shape.t_queries as u16,
        blow: pd_whir.shape.blow as u8,
        pd_whir_root: pd_whir.root,
        blinded_evals,
        logup_proof,
        whir_opening,
    })
}

/// Standalone Zero-Witness Verifier for `WhirBlindPdProof` (`0` secret share access, `130.1b` BCIKS / `144.5b` DKT)!
#[allow(clippy::too_many_arguments)]
pub fn verify_blind_r_pd_whir61(
    params: &HoistedParams,
    expected_party_id: usize,
    expected_selected_parties: &[usize],
    expected_auth_statement_digest: &[u8; 32],
    dkg_transcript: &VerifiedThresholdDkgTranscript,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_eff: &Ct,
    ct_commitment: &[u8; 32],
    prf: &WhirBlindPdProof,
) -> Result<()> {
    dkg_transcript.verify_integrity(params)?;
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];

    let want_top_bits = (128 - (2 * smudge_bound).leading_zeros())
        .saturating_sub(100)
        .max(1);
    if smudge_bound == 0
        || smudge_bound > (1u128 << 111) - 1
        || !(1..=20).contains(&smudge_top_bits)
        || smudge_top_bits != want_top_bits
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "invalid or non-canonical (smudge_bound, smudge_top_bits)".into(),
        ));
    }

    if prf.party_id != expected_party_id
        || prf.selected_parties != expected_selected_parties
        || prf.auth_statement_digest != *expected_auth_statement_digest
        || prf.partial_rns.len() != 3 * n
        || prf.party_id >= dkg_transcript.n_parties
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "party_id, selected_parties, auth_statement_digest, or partial_rns mismatch".into(),
        ));
    }
    for k in 0..3 {
        let qk = params.qp[k];
        if prf.partial_rns[k * n..(k + 1) * n].iter().any(|&v| v >= qk) {
            return Err(ThresholdCustodyError::InvalidBlindPdProof(
                "non-canonical residue in partial_rns".into(),
            ));
        }
    }
    if prf.blinded_evals.masked_s_evals.iter().any(|&v| v >= fp0.p)
        || prf.blinded_evals.masked_e_eval >= fp0.p
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "non-canonical BlindedRPdEvals >= p_0".into(),
        ));
    }

    validate_pd_whir_shape(
        log_n,
        prf.wit_mr as usize,
        prf.wit_mc as usize,
        prf.t_queries as usize,
        prf.blow as usize,
    )
    .map_err(ThresholdCustodyError::InvalidBlindPdProof)?;

    let fs_ctx = compute_blind_pd_fs_ctx(
        prf.party_id,
        &prf.selected_parties,
        &prf.auth_statement_digest,
        dkg_transcript,
        smudge_bound,
        smudge_top_bits,
        ct_commitment,
        &ct2_handle(ct_eff),
        &prf.partial_rns,
        &prf.pd_whir_root,
    );
    let r_pts: [u64; 3] =
        std::array::from_fn(|idx| derive_blind_pd_point(&fs_ctx, fp0.p, idx as u64));

    let (gadgets, descs, off_mask, off_mult) = build_blind_pd_gadgets_and_descs(
        params,
        prf.party_id,
        &prf.selected_parties,
        dkg_transcript,
        smudge_bound,
        smudge_top_bits,
        ct_eff,
        &prf.partial_rns,
    );

    // Pin exact canonical `LogUpConfig`, chunk count, per-chunk `active_len` (`% n == 0`), and `depth` BEFORE GKR!
    let expected_chunk_log2 = (log_n + 6).max(18);
    if prf.logup_proof.config
        != (LogUpConfig::BatchedC3 {
            chunk_log2: expected_chunk_log2,
        })
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "non-canonical LogUpConfig in WhirBlindPdProof".into(),
        ));
    }
    let chunk_cap = 1usize << expected_chunk_log2;
    let total_lookups = descs.len() * n;
    let expected_chunks = total_lookups.div_ceil(chunk_cap);
    if prf.logup_proof.total_lookups != total_lookups
        || prf.logup_proof.witness_trees.len() != expected_chunks
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "LogUp total_lookups or witness_trees count mismatch".into(),
        ));
    }
    for (b_idx, wt) in prf.logup_proof.witness_trees.iter().enumerate() {
        let start = b_idx * chunk_cap;
        let want_act = (total_lookups - start).min(chunk_cap);
        let want_depth = want_act.max(2).next_power_of_two().trailing_zeros() as usize;
        if wt.active_len != want_act || wt.active_len % n != 0 || wt.depth != want_depth {
            return Err(ThresholdCustodyError::InvalidBlindPdProof(
                "non-canonical LogUp chunk active_len or depth".into(),
            ));
        }
    }
    let want_tab_depth = TABLE_SIZE.next_power_of_two().trailing_zeros() as usize;
    if prf.logup_proof.table_tree.active_len != TABLE_SIZE
        || prf.logup_proof.table_tree.depth != want_tab_depth
    {
        return Err(ThresholdCustodyError::InvalidBlindPdProof(
            "non-canonical LogUp table_tree active_len or depth".into(),
        ));
    }

    verify_logup_gkr(&fp0, &prf.logup_proof, &fs_ctx, None)
        .map_err(ThresholdCustodyError::InvalidBlindPdProof)?;

    let (v_fams, claims, open_ctx) = build_blind_pd_whir_claims(
        params,
        prf.party_id,
        &prf.selected_parties,
        ct_eff,
        &prf.partial_rns,
        smudge_bound,
        &gadgets,
        &descs,
        off_mask,
        off_mult,
        &fs_ctx,
        &r_pts,
        &prf.blinded_evals,
        &prf.logup_proof,
    )
    .map_err(ThresholdCustodyError::InvalidBlindPdProof)?;

    let shape = WhirShape61::from_mr_mc(
        &fp0,
        prf.wit_mr as usize,
        prf.wit_mc as usize,
        prf.t_queries as usize,
        prf.blow as usize,
    );
    verify_whir_pcs61(
        &fp0,
        &shape,
        &prf.pd_whir_root,
        log_n,
        &v_fams,
        &claims,
        &open_ctx,
        &prf.whir_opening,
    )
    .map_err(ThresholdCustodyError::InvalidBlindPdProof)
}

/// Verify all `t` `WhirBlindPdProof`s from `selected_parties` (`n - t` offline!) and round-decode plaintext over `F_t`!
#[allow(clippy::too_many_arguments)]
pub fn combine_verified_threshold_shares(
    params: &HoistedParams,
    expected_auth_statement_digest: &[u8; 32],
    dkg_transcript: &VerifiedThresholdDkgTranscript,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_eff: &Ct,
    ct_commitment: &[u8; 32],
    selected_parties: &[usize],
    proofs: &[WhirBlindPdProof],
) -> Result<Vec<u64>> {
    dkg_transcript.verify_integrity(params)?;
    let t_need = dkg_transcript.threshold;
    if selected_parties.len() != t_need
        || selected_parties.windows(2).any(|w| w[0] >= w[1])
        || proofs.len() != t_need
    {
        return Err(ThresholdCustodyError::NonCanonicalQuorumRoster);
    }
    for (p_expected, prf) in selected_parties.iter().zip(proofs.iter()) {
        verify_blind_r_pd_whir61(
            params,
            *p_expected,
            selected_parties,
            expected_auth_statement_digest,
            dkg_transcript,
            smudge_bound,
            smudge_top_bits,
            ct_eff,
            ct_commitment,
            prf,
        )?;
    }

    let n = params.n;
    let rns = Rns::new(n, &params.qp, params.t);
    let mut acc = ct_eff.c0.clone();
    for prf in proofs {
        rns.add_assign(&mut acc, &prf.partial_rns);
    }
    Ok((0..n)
        .map(|j| rns.decrypt_round(&[acc[j], acc[n + j], acc[2 * n + j]]))
        .collect())
}

// ================================================================================================
// §5. Canonical Binary Wire Serialization for `WhirBlindPdProof` (`DVFHEBPD`) & Internal Helpers
// ================================================================================================

impl WhirBlindPdProof {
    pub fn to_bytes(&self, params: &HoistedParams) -> Vec<u8> {
        let mut out = Vec::with_capacity(380 * 1024);
        out.extend_from_slice(BLIND_PD_MAGIC);
        out.extend_from_slice(&BLIND_PD_VERSION.to_le_bytes());
        out.extend_from_slice(&(self.party_id as u32).to_le_bytes());
        out.extend_from_slice(&(self.selected_parties.len() as u32).to_le_bytes());
        for &p in &self.selected_parties {
            out.extend_from_slice(&(p as u32).to_le_bytes());
        }
        out.extend_from_slice(&self.auth_statement_digest);
        out.push(self.wit_mr);
        out.push(self.wit_mc);
        out.extend_from_slice(&self.t_queries.to_le_bytes());
        out.push(self.blow);
        out.extend_from_slice(&self.pd_whir_root);
        let be = [
            self.blinded_evals.masked_s_evals[0],
            self.blinded_evals.masked_s_evals[1],
            self.blinded_evals.masked_s_evals[2],
            self.blinded_evals.masked_e_eval,
        ];
        pack_u64_bits_le(&be, 61, &mut out);
        pack_u64_bits_le(&self.partial_rns, 61, &mut out);
        write_logup_proof(&self.logup_proof, &mut out);
        self.whir_opening.to_bytes(params.qp[0], &mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8], params: &HoistedParams) -> std::result::Result<Self, String> {
        let mut cur = ByteReader::new(bytes);
        if cur.take(8)? != BLIND_PD_MAGIC {
            return Err("invalid WhirBlindPdProof magic".into());
        }
        if cur.read_u32()? != BLIND_PD_VERSION {
            return Err("unsupported WhirBlindPdProof version".into());
        }
        let party_id = cur.read_u32()? as usize;
        let sel_len = cur.read_u32()? as usize;
        if sel_len == 0 || sel_len > 64 {
            return Err("invalid selected_parties length".into());
        }
        let mut selected_parties = Vec::with_capacity(sel_len);
        for _ in 0..sel_len {
            selected_parties.push(cur.read_u32()? as usize);
        }
        let auth_statement_digest = cur.read_hash()?;
        let wit_mr = cur.read_u8()?;
        let wit_mc = cur.read_u8()?;
        let t_queries = cur.read_u16()?;
        let blow = cur.read_u8()?;
        let pd_whir_root = cur.read_hash()?;
        let p0 = params.qp[0];
        let be = unpack_u64_bits_le(&mut cur, 61, 4, p0)?;
        if be.len() != 4 {
            return Err("BlindedRPdEvals unpacked length != 4".into());
        }
        let partial_rns = unpack_u64_bits_le(&mut cur, 61, 3 * params.n, u64::MAX)?;
        let logup_proof = read_logup_proof(&mut cur, p0)?;
        let whir_opening = WhirOpeningBundle61::from_bytes(&mut cur, p0)?;
        if !cur.is_eof() {
            return Err("trailing bytes in WhirBlindPdProof".into());
        }
        Ok(WhirBlindPdProof {
            party_id,
            selected_parties,
            auth_statement_digest,
            partial_rns,
            wit_mr,
            wit_mc,
            t_queries,
            blow,
            pd_whir_root,
            blinded_evals: BlindedRPdEvals {
                masked_s_evals: [be[0], be[1], be[2]],
                masked_e_eval: be[3],
            },
            logup_proof,
            whir_opening,
        })
    }
}

type BlindedClaimsBundle = (Vec<Vec<u64>>, Vec<SlotLinearClaim>, [u8; 32]);

struct RingModPointCtx<'a> {
    n: usize,
    r_pt: u64,
    vf_full_idx: usize,
    vf_deg_n1_idx: usize,
    r_pows: &'a [u64],
}

#[allow(clippy::too_many_arguments)]
fn build_blind_pd_whir_claims(
    params: &HoistedParams,
    party_id: usize,
    selected_parties: &[usize],
    ct_eff: &Ct,
    partial_rns: &[u64],
    smudge_bound: u128,
    gadgets: &[RingModQkInstance],
    descs: &[AffineLookup61],
    off_mask: usize,
    off_mult: usize,
    fs_ctx: &[u8; 32],
    r_pts: &[u64; 3],
    blinded_evals: &BlindedRPdEvals,
    logup_proof: &LogUpGkrProof,
) -> std::result::Result<BlindedClaimsBundle, String> {
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];
    let mut v_fams = Vec::new();
    let mut claims = Vec::new();

    for pt_idx in 0..3 {
        let r_pows = build_pows(&fp0, r_pts[pt_idx], n);
        let mut r_deg_n1 = r_pows.clone();
        r_deg_n1[n - 1] = 0;
        let vf_full = v_fams.len();
        v_fams.push(r_pows.clone());
        let vf_n1 = v_fams.len();
        v_fams.push(r_deg_n1);

        if pt_idx == 0 {
            // Load-bearing Masked `R_PD` Evaluation Weld (`TVD == 0`!):
            // 1. Open `s_{i,k}(r_0) + mu_{s,k}(r_0) == masked_s_evals[k]` (`k = 0..3`):
            let s_limb_w = [1u64, 1u64 << 20, 1u64 << 39, 1u64 << 57];
            for k_idx in 0..3 {
                let base = 5 * k_idx;
                let mut terms = Vec::with_capacity(5);
                for (m, &w) in s_limb_w.iter().enumerate() {
                    terms.push((base + m, w));
                }
                terms.push((off_mask + k_idx, 1));
                claims.push(SlotLinearClaim::single_vec(
                    vf_full,
                    terms,
                    blinded_evals.masked_s_evals[k_idx],
                ));
            }
            // 2. Open `e_{sh,i}(r_0) + mu_e(r_0) == masked_e_eval`:
            let mut e_terms: Vec<(usize, u64)> = (0..6)
                .map(|m| (18 + m, fp0.pow(2, (20 * m) as u64)))
                .collect();
            e_terms.push((off_mask + 3, 1));
            claims.push(SlotLinearClaim::single_vec(
                vf_full,
                e_terms,
                blinded_evals.masked_e_eval,
            ));

            // 3. Direct Mask-Cancelling `k=0` (`q_0 == p_0`) `R_PD` Weld:
            //    `-A_0(r_0) * mu_{s,0}(r_0) - mu_e(r_0) - (r_0^N + 1) * K_{pd,0}(r_0)
            //      == d_{i,0}(r_0) + E*1(r_0) - A_0(r_0)*masked_s_0 - masked_e`!
            //    Adding `A_0(r_0) * Claim(s_0 + mu_{s,0})` + `Claim(e + mu_e)` + this claim cancels `(mu_{s,0}, mu_e)`
            //    identically in `F_{p_0}`, making `BlindedRPdEvals` 100% load-bearing (`+1` tamper fails)!
            let lam0 = lagrange_coeff_at_zero_mod_q(party_id, selected_parties, fp0.p);
            let c1_0_ev = fp0.dot(&ct_eff.c1[0..n], &r_pows);
            let a0_ev = fp0.mul(lam0, c1_0_ev);
            let d0_ev = fp0.dot(&partial_rns[0..n], &r_pows);
            let ones_r0 = fp0.ones_eval(n, r_pts[0]);
            let e_mod_p0 = (smudge_bound % (fp0.p as u128)) as u64;
            let rhs_weld = fp0.sub(
                fp0.add(d0_ev, fp0.mul(e_mod_p0, ones_r0)),
                fp0.add(
                    fp0.mul(a0_ev, blinded_evals.masked_s_evals[0]),
                    blinded_evals.masked_e_eval,
                ),
            );
            // Note: in `k=0`, `(lambda_0 * c'_{1,0}) * s_{i,0} + e_{sh,i} - (d_{i,0} + E) == (X^N+1) K_tot + p_0 Q_tot`,
            // so modulo `p_0`, `A_0(r_0) s_{i,0}(r_0) + e_{sh,i}(r_0) - (r_0^N+1) sum_b 2^{21 b} K_{0,b}(r_0) == d_0(r_0) + E*1(r_0)`!
            let rn_plus_1 = fp0.add(fp0.pow(r_pts[0], n as u64), 1);
            let mut k0_terms = Vec::with_capacity(9);
            for b in 0..3 {
                let off_k = gadgets[0].base_slot + 9 + b * 3;
                let wb = fp0.mul(1u64 << (21 * b), rn_plus_1);
                k0_terms.push((off_k, fp0.neg(wb)));
                k0_terms.push((off_k + 1, fp0.neg(fp0.mul(1u64 << 20, wb))));
                k0_terms.push((off_k + 2, fp0.neg(fp0.mul(1u64 << 40, wb))));
            }
            claims.push(SlotLinearClaim {
                terms: vec![
                    (
                        vf_full,
                        vec![(off_mask, fp0.neg(a0_ev)), (off_mask + 3, fp0.neg(1))],
                    ),
                    (vf_n1, k0_terms),
                ],
                rhs: rhs_weld,
            });
        }

        for g in gadgets {
            g.append_claims_at_point(
                &fp0,
                &RingModPointCtx {
                    n,
                    r_pt: r_pts[pt_idx],
                    vf_full_idx: vf_full,
                    vf_deg_n1_idx: vf_n1,
                    r_pows: &r_pows,
                },
                &mut claims,
            );
        }

        // Exact Verifier-Side `e_sh + e_rev == 2 * smudge_bound` 3x40-bit Pair-Carry Claims (`< 2^41 << p_0 / 2`):
        let ones_r = fp0.ones_eval(n, r_pts[pt_idx]);
        let two_e = 2 * smudge_bound;
        let two_e_p0 = (two_e & ((1u128 << 40) - 1)) as u64;
        let two_e_p1 = ((two_e >> 40) & ((1u128 << 40) - 1)) as u64;
        let two_e_p2 = (two_e >> 80) as u64;
        let t20 = 1u64 << 20;
        let neg_t40 = fp0.neg(1u64 << 40);
        claims.push(SlotLinearClaim::single_vec(
            vf_full,
            vec![(18, 1), (19, t20), (24, 1), (25, t20), (30, neg_t40)],
            fp0.mul(two_e_p0, ones_r),
        ));
        claims.push(SlotLinearClaim::single_vec(
            vf_full,
            vec![
                (20, 1),
                (21, t20),
                (26, 1),
                (27, t20),
                (30, 1),
                (31, neg_t40),
            ],
            fp0.mul(two_e_p1, ones_r),
        ));
        claims.push(SlotLinearClaim::single_vec(
            vf_full,
            vec![(22, 1), (23, t20), (28, 1), (29, t20), (31, 1)],
            fp0.mul(two_e_p2, ones_r),
        ));
    }

    // Discharge `D1b` LogUp-GKR terminal evaluations `(z_w, z_tab)` inside the SAME `pd_whir` opening:
    let chunk_cap = match logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => logup_proof.total_lookups.max(2).next_power_of_two(),
    };
    let cols_per_chunk = chunk_cap / n;
    let (wit_zs, z_tab) = extract_logup_points_61(&fp0, logup_proof, fs_ctx)?;

    for (b_idx, w_prf) in logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_fams.len();
        v_fams.push(build_eq_le_fp(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp(&fp0, &zw[log_n..]);
        let start_col = b_idx * cols_per_chunk;
        let act_cols = w_prf.active_len / n;
        let mut const_acc = 0u64;
        let mut slot_map: BTreeMap<usize, u64> = BTreeMap::new();
        for s in 0..act_cols {
            let w_hi = eq_hi[s];
            let desc = &descs[start_col + s];
            const_acc = fp0.add(const_acc, fp0.mul(w_hi, desc.const_offset));
            for &(sl, c_val) in &desc.terms {
                let e = slot_map.entry(sl).or_insert(0);
                *e = fp0.add(*e, fp0.mul(w_hi, c_val));
            }
        }
        claims.push(SlotLinearClaim::single_vec(
            v_idx,
            slot_map.into_iter().collect(),
            fp0.sub(w_prf.leaf_payload_eval, const_acc),
        ));
    }

    let mult_slots = (TABLE_SIZE / n).max(1);
    let v_tab_idx = v_fams.len();
    v_fams.push(build_eq_le_fp(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = if log_n < TABLE_LOG2 {
        build_eq_le_fp(&fp0, &z_tab[log_n..TABLE_LOG2])
    } else {
        vec![1u64]
    };
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (off_mult + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    let mut oh = Sha256::new();
    oh.update(b"DARKVFHE_BLIND_PD_OPEN_CTX_V1|");
    oh.update(fs_ctx);
    for &s in &blinded_evals.masked_s_evals {
        oh.update(s.to_le_bytes());
    }
    oh.update(blinded_evals.masked_e_eval.to_le_bytes());
    Ok((v_fams, claims, oh.finalize().into()))
}

fn validate_pd_whir_shape(
    log_n: usize,
    mr: usize,
    mc: usize,
    t_queries: usize,
    blow: usize,
) -> std::result::Result<(), String> {
    if !(WHIR_T_QUERIES_128..=512).contains(&t_queries)
        || !blow.is_power_of_two()
        || !(4..=16).contains(&blow)
    {
        return Err("Blind-PD WHIR security/blowup parameters out of 128-bit range".into());
    }
    let min_mc = log_n.max(9);
    if !(3..=20).contains(&mr) || !(min_mc..=21).contains(&mc) || mr + mc > 31 {
        return Err("Blind-PD WHIR (mr, mc) out of valid range".into());
    }
    let r_total = (1usize << mr) + WHIR_EXTRA_EXT3_MASK_ROWS;
    let w0 = 2usize << mc;
    let k0 = if r_total >= 45 && w0 >= 2048 {
        0usize
    } else {
        1usize
    };
    let n_leaves_0 = (blow * w0) >> k0;
    if t_queries.saturating_mul(1usize << k0) > (1usize << mc) || t_queries > n_leaves_0 {
        return Err("Blind-PD WHIR t_queries exceeds Stage-0 column hiding capacity".into());
    }
    Ok(())
}

// ------------------------------------------------------------------------------------------------
// Small Arithmetic, Sampling, Digest, and Serialization Helpers
// ------------------------------------------------------------------------------------------------

fn extract_6x20(v: u128) -> [u64; 6] {
    const M20: u128 = (1u128 << 20) - 1;
    [
        (v & M20) as u64,
        ((v >> 20) & M20) as u64,
        ((v >> 40) & M20) as u64,
        ((v >> 60) & M20) as u64,
        ((v >> 80) & M20) as u64,
        ((v >> 100) & M20) as u64,
    ]
}

fn build_pows(fp: &FastPrime61, r: u64, n: usize) -> Vec<u64> {
    let mut out = Vec::with_capacity(n);
    let mut cur = 1u64;
    for _ in 0..n {
        out.push(cur);
        cur = fp.mul(cur, r);
    }
    out
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

fn subtract_ct2(params: &HoistedParams, a: &Ct, b: &Ct) -> Ct {
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

fn sample_ternary_poly(n: usize, rng: &mut PcsRng) -> Vec<i64> {
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

fn sample_small_err_poly(n: usize, rng: &mut PcsRng, bound: i64) -> Vec<i64> {
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

fn sample_smudge_poly(n: usize, e_bound: u128, rng: &mut PcsRng) -> Vec<i128> {
    let span = 2 * e_bound + 1;
    let max_mult = (u128::MAX / span) * span;
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let blk = rng.next_block();
        for ch in blk.chunks_exact(16) {
            if out.len() == n {
                break;
            }
            let u = u128::from_le_bytes(ch.try_into().unwrap());
            if u < max_mult {
                out.push((u % span) as i128 - (e_bound as i128));
            }
        }
    }
    out
}

fn sample_uniform_rns_qp(rns: &Rns, rng: &mut PcsRng) -> Vec<u64> {
    let n = rns.n;
    let mut out = vec![0u64; 3 * n];
    for k in 0..3 {
        let qk = rns.qs[k];
        let limit = (u64::MAX / qk) * qk;
        let mut j = 0usize;
        while j < n {
            let blk = rng.next_block();
            for ch in blk.chunks_exact(8) {
                if j == n {
                    break;
                }
                let u = u64::from_le_bytes(ch.try_into().unwrap());
                if u < limit {
                    out[k * n + j] = u % qk;
                    j += 1;
                }
            }
        }
    }
    out
}

fn sample_uniform_rns4(rns4: &Rns, rng: &mut PcsRng) -> Vec<u64> {
    let n = rns4.n;
    let mut out = vec![0u64; 4 * n];
    for k in 0..4 {
        let qk = rns4.qs[k];
        let limit = (u64::MAX / qk) * qk;
        let mut j = 0usize;
        while j < n {
            let blk = rng.next_block();
            for ch in blk.chunks_exact(8) {
                if j == n {
                    break;
                }
                let u = u64::from_le_bytes(ch.try_into().unwrap());
                if u < limit {
                    out[k * n + j] = u % qk;
                    j += 1;
                }
            }
        }
    }
    out
}

fn eval_poly_vec_rns(coeffs_by_deg: &[Vec<u64>], y_pt: u64, n: usize, qs: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; 3 * n];
    for (k, &qk) in qs.iter().enumerate().take(3) {
        let mut y_pow = 1u64;
        for deg_poly in coeffs_by_deg {
            for j in 0..n {
                let idx = k * n + j;
                out[idx] = addmod(out[idx], mulmod(deg_poly[idx], y_pow, qk), qk);
            }
            y_pow = mulmod(y_pow, y_pt, qk);
        }
    }
    out
}

fn compute_vss_row_digest(
    domain: &[u8; 32],
    dealer: usize,
    recipient: usize,
    salt: &[u8; 32],
    s_row: &[Vec<u64>],
    e_row: &[Vec<u64>],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_VSS_ROW_V1|");
    h.update(domain);
    h.update((dealer as u32).to_le_bytes());
    h.update((recipient as u32).to_le_bytes());
    h.update(salt);
    for r in s_row.iter().chain(e_row.iter()) {
        for &v in r {
            h.update(v.to_le_bytes());
        }
    }
    h.finalize().into()
}

fn compute_dealer_broadcast_digest(
    domain: &[u8; 32],
    dealer: usize,
    b_share: &[u64],
    row_digs: &[[u8; 32]],
    lin_imgs: &[Vec<u64>],
    bdlops: &[BdlopCommitment],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_DEALER_BCAST_V1|");
    h.update(domain);
    h.update((dealer as u32).to_le_bytes());
    for &v in b_share {
        h.update(v.to_le_bytes());
    }
    for d in row_digs {
        h.update(d);
    }
    for img in lin_imgs {
        for &v in img {
            h.update(v.to_le_bytes());
        }
    }
    for com in bdlops {
        for &v in com.t0_coeff.iter().chain(com.t1_coeff.iter()) {
            h.update(v.to_le_bytes());
        }
    }
    h.finalize().into()
}

fn encode_private_vss_row(
    salt: &[u8; 32],
    s_row: &[Vec<u64>],
    e_row: &[Vec<u64>],
    bdlop: &BdlopShortOpening,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(salt);
    for r in s_row.iter().chain(e_row.iter()) {
        for &v in r {
            out.extend_from_slice(&v.to_le_bytes());
        }
    }
    for arr in [&bdlop.r1, &bdlop.e0, &bdlop.e1] {
        for &v in arr {
            out.extend_from_slice(&(v as i16).to_le_bytes());
        }
    }
    out
}

type DecodedPrivateVssRow = ([u8; 32], Vec<Vec<u64>>, Vec<Vec<u64>>, BdlopShortOpening);

fn decode_private_vss_row(
    bytes: &[u8],
    t: usize,
    n: usize,
    qs: &[u64],
) -> Result<DecodedPrivateVssRow> {
    let mut cur = ByteReader::new(bytes);
    let salt: [u8; 32] = cur
        .take(32)
        .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("row salt"))?
        .try_into()
        .unwrap();
    let mut read_set = || -> Result<Vec<Vec<u64>>> {
        let mut set = Vec::with_capacity(t);
        for _ in 0..t {
            let mut poly = Vec::with_capacity(3 * n);
            for &qk in qs.iter().take(3) {
                for _ in 0..n {
                    let v = cur.read_u64().map_err(|_| {
                        ThresholdCustodyError::ConfidentialEnvelopeRefused("row coeff")
                    })?;
                    if v >= qk {
                        return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
                            "non-canonical row residue",
                        ));
                    }
                    poly.push(v);
                }
            }
            set.push(poly);
        }
        Ok(set)
    };
    let s_row = read_set()?;
    let e_row = read_set()?;
    let mut read_short = || -> Result<Vec<i64>> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let b = cur
                .take(2)
                .map_err(|_| ThresholdCustodyError::ConfidentialEnvelopeRefused("bdlop short"))?;
            v.push(i16::from_le_bytes([b[0], b[1]]) as i64);
        }
        Ok(v)
    };
    let r1 = read_short()?;
    let e0 = read_short()?;
    let e1 = read_short()?;
    if !cur.is_eof() {
        return Err(ThresholdCustodyError::ConfidentialEnvelopeRefused(
            "trailing private row bytes",
        ));
    }
    Ok((salt, s_row, e_row, BdlopShortOpening { r1, e0, e1 }))
}

fn relin_r1_sig_preimage(
    domain: &[u8; 32],
    dealer: usize,
    h0: &[Vec<u64>; 4],
    h1: &[Vec<u64>; 4],
) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_RELIN_R1_V1|");
    h.update(domain);
    h.update((dealer as u32).to_le_bytes());
    for m in 0..4 {
        for &v in h0[m].iter().chain(h1[m].iter()) {
            h.update(v.to_le_bytes());
        }
    }
    h.finalize().to_vec()
}

fn compute_r1_agg_digest(domain: &[u8; 32], h0: &[Vec<u64>; 4], h1: &[Vec<u64>; 4]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_RELIN_R1_AGG_V1|");
    h.update(domain);
    for m in 0..4 {
        for &v in h0[m].iter().chain(h1[m].iter()) {
            h.update(v.to_le_bytes());
        }
    }
    h.finalize().into()
}

fn relin_r2_sig_preimage(
    domain: &[u8; 32],
    r1_dig: &[u8; 32],
    dealer: usize,
    h2: &[Vec<u64>; 4],
) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_RELIN_R2_V1|");
    h.update(domain);
    h.update(r1_dig);
    h.update((dealer as u32).to_le_bytes());
    for h2_m in h2 {
        for &v in h2_m {
            h.update(v.to_le_bytes());
        }
    }
    h.finalize().to_vec()
}

fn sample_os_fp_exact_slice(p0: u64, out: &mut [u64]) -> std::result::Result<(), String> {
    let mut f = File::open("/dev/urandom").map_err(|e| format!("open /dev/urandom: {e}"))?;
    let mut buf = [0u8; 8192];
    let mask61 = (1u64 << 61) - 1;
    let mut idx = 0usize;
    while idx < out.len() {
        f.read_exact(&mut buf)
            .map_err(|e| format!("read /dev/urandom: {e}"))?;
        for ch in buf.chunks_exact(8) {
            if idx == out.len() {
                break;
            }
            let cand = u64::from_le_bytes(ch.try_into().unwrap()) & mask61;
            if cand < p0 {
                out[idx] = cand;
                idx += 1;
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn compute_blind_pd_fs_ctx(
    party_id: usize,
    selected: &[usize],
    auth_stmt_dig: &[u8; 32],
    dkg_tr: &VerifiedThresholdDkgTranscript,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_com: &[u8; 32],
    ct_eff_h: &[u8; 32],
    partial_rns: &[u64],
    pd_root: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_BLIND_R_PD_FS_V2|");
    h.update((party_id as u32).to_le_bytes());
    h.update((selected.len() as u32).to_le_bytes());
    for &p in selected {
        h.update((p as u32).to_le_bytes());
    }
    h.update(auth_stmt_dig);
    h.update(dkg_tr.digest);
    h.update(smudge_bound.to_le_bytes());
    h.update(smudge_top_bits.to_le_bytes());
    let anchor = &dkg_tr.party_bdlop_anchors[party_id];
    for &v in anchor.t0_coeff.iter().chain(anchor.t1_coeff.iter()) {
        h.update(v.to_le_bytes());
    }
    h.update(ct_com);
    h.update(ct_eff_h);
    h.update(pd_root);
    for &v in partial_rns {
        h.update(v.to_le_bytes());
    }
    h.finalize().into()
}

fn derive_blind_pd_point(ctx: &[u8; 32], p: u64, idx: u64) -> u64 {
    let mut h = Sha256::new();
    h.update(b"BLIND_PD_PT_V1|");
    h.update(ctx);
    h.update(p.to_le_bytes());
    h.update(idx.to_le_bytes());
    let d: [u8; 32] = h.finalize().into();
    let u = u128::from_le_bytes(d[0..16].try_into().unwrap());
    (u % (p as u128)) as u64
}

fn extract_logup_points_61(
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

    let replay_one =
        |mut s: [u8; 32], tp: &FractionTreeProof| -> std::result::Result<Vec<u64>, String> {
            for r in &tp.roots {
                absorb_u64s(&mut s, r);
            }
            if tp.depth == 0 {
                return Ok(Vec::new());
            }
            if tp.layers.len() != tp.depth.saturating_sub(1) {
                return Err("LogUp tree layers.len() != depth - 1".into());
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
            Ok(z_pt)
        };

    let mut wit_zs = Vec::with_capacity(proof.witness_trees.len());
    for (i, w) in proof.witness_trees.iter().enumerate() {
        wit_zs.push(replay_one(fork_sub(&st, "WIT_TREE", i as u64), w)?);
    }
    let z_tab = replay_one(fork_sub(&st, "TAB_TREE", 0), &proof.table_tree)?;
    Ok((wit_zs, z_tab))
}

fn write_fraction_tree(t: &FractionTreeProof, out: &mut Vec<u8>) {
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
    for l1 in &t.layer1_vals {
        flat.extend_from_slice(l1);
    }
    for ly in &t.layers {
        out.push(ly.sumcheck_rounds.len() as u8);
        out.push(ly.child_evals.len() as u8);
        for sc in &ly.sumcheck_rounds {
            flat.extend_from_slice(sc);
        }
        for ce in &ly.child_evals {
            flat.extend_from_slice(ce);
        }
    }
    flat.push(t.leaf_payload_eval);
    pack_u64_bits_le(&flat, 61, out);
}

fn read_fraction_tree(
    cur: &mut ByteReader<'_>,
    p: u64,
) -> std::result::Result<FractionTreeProof, String> {
    let depth = cur.read_u32()? as usize;
    let active_len = cur.read_u64()? as usize;
    let n_roots = cur.read_u8()? as usize;
    let n_l1 = cur.read_u8()? as usize;
    let n_layers = cur.read_u8()? as usize;
    if depth > 30 || n_roots == 0 || n_roots > 8 || n_l1 != n_roots || n_layers > 30 {
        return Err("invalid FractionTreeProof header".into());
    }
    let mut layer_meta = Vec::with_capacity(n_layers);
    let mut expected_words = n_roots * 2 + n_l1 * 4 + 1;
    for _ in 0..n_layers {
        let n_sc = cur.read_u8()? as usize;
        let n_ce = cur.read_u8()? as usize;
        if n_sc > 30 || n_ce != n_roots {
            return Err("invalid GkrLayerProof metadata".into());
        }
        layer_meta.push((n_sc, n_ce));
        expected_words += n_sc * 4 + n_ce * 4;
    }
    let flat = unpack_u64_bits_le(cur, 61, expected_words, p)?;
    if flat.len() != expected_words {
        return Err("FractionTreeProof unpacked word count mismatch".into());
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
    for (n_sc, n_ce) in layer_meta {
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

fn write_logup_proof(lu: &LogUpGkrProof, out: &mut Vec<u8>) {
    match lu.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => {
            out.push(0);
            out.push(chunk_log2 as u8);
        }
        LogUpConfig::MonolithicC4 => {
            out.push(1);
            out.push(0);
        }
    }
    out.extend_from_slice(&(lu.total_lookups as u64).to_le_bytes());
    out.extend_from_slice(&lu.mult_commitment);
    out.extend_from_slice(&(lu.witness_trees.len() as u32).to_le_bytes());
    for wt in &lu.witness_trees {
        write_fraction_tree(wt, out);
    }
    write_fraction_tree(&lu.table_tree, out);
}

fn read_logup_proof(
    cur: &mut ByteReader<'_>,
    p: u64,
) -> std::result::Result<LogUpGkrProof, String> {
    let tag = cur.read_u8()?;
    let arg = cur.read_u8()? as usize;
    let config = match tag {
        0 => {
            if !(10..=28).contains(&arg) {
                return Err("invalid BatchedC3 chunk_log2".into());
            }
            LogUpConfig::BatchedC3 { chunk_log2: arg }
        }
        1 => {
            if arg != 0 {
                return Err("non-canonical MonolithicC4 arg".into());
            }
            LogUpConfig::MonolithicC4
        }
        _ => return Err("unknown LogUpConfig tag".into()),
    };
    let total_lookups = cur.read_u64()? as usize;
    let mult_commitment = cur.read_hash()?;
    let n_wt = cur.read_u32()? as usize;
    if n_wt == 0 || n_wt > 4096 {
        return Err("invalid witness_trees count".into());
    }
    let mut witness_trees = Vec::with_capacity(n_wt);
    for _ in 0..n_wt {
        witness_trees.push(read_fraction_tree(cur, p)?);
    }
    let table_tree = read_fraction_tree(cur, p)?;
    Ok(LogUpGkrProof {
        config,
        total_lookups,
        mult_commitment,
        witness_trees,
        table_tree,
    })
}
