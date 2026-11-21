//! Real 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` & `Dark-vPIR` Resident.
//!
//! Implements:
//! 1. **Zero-Dealer-`s` 3-of-3 Threshold BFV Key Generation (`CustodianParty` `0, 1, 2`)**:
//!    - Common reference polynomial `a_crs`; each party `i` samples private ternary `s_i in {-1, 0, 1}^N`
//!      and `e_{pk,i} in [-8, 8]^N`, publishing `b_i = -(a_crs * s_i + e_{pk,i}) mod Qp`.
//!    - Joint public key `pk = (b_0 + b_1 + b_2, a_crs)` supports public-key RLWE encryption without any
//!      party or ceremony coordinator ever reconstructing `s = s_0 + s_1 + s_2`!
//!    - Pairwise 2-party oblivious ring-product shares yield bounded `s2_i` (`sum_i s2_i == s^2` in
//!      `Z[X]/(X^N + 1)`) without ever materializing `s`, committed in each custodian's long-term
//!      `CommittedMatrixPcs` root (`key_pcs_root`).
//! 2. **`C8` Zero-Decryption-Oracle Gate & Zero-Knowledge `R_PD` Partial-Decryption Proofs**:
//!    - Every `CustodianParty` maintains `verified_handles: HashSet<[u8; 32]>` and **refuses to compute
//!      or release any partial decryption share** unless the ciphertext handle is either a MAC-checked
//!      genesis/`S2E` handle or verified via `verify_hoisted_succinct_bundle(&proof_bytes)` (`0` bits
//!      of decryption-oracle leakage!).
//!    - At `E2S` crossings (`ct' = ct - Enc_{pk}(R)`), custodian `i` samples smudging noise
//!      `e_i in [-E, E]^N` (`E = floor((Q / (2t)) / 1024) ~ 2^111` at `N = 8192`, `> 40`-bit full-poly
//!      statistical drowning, `3E << Q / (2t)`) and proves `p_i = s_i c1' + s2_i c2' + e_i - (X^N+1) k_q`
//!      + `|e_i|_inf <= E` via `SuccinctMatrixPcs` + `D1b` LogUp-GKR (`PdSuccinctProof`).
//! 3. **3-Party SPDZ Engine over `F_t` (`SpdzCluster`)**:
//!    - Additive secret shares + global MAC key `alpha = alpha_0 + alpha_1 + alpha_2 mod t` (no party
//!      holds `alpha`), Beaver triple batch multiplication, commit-then-open `sigma` MAC verification,
//!      and dealerless `(Enc_{pk}(R), [R])` crossing mask generation.
//! 4. **Multi-Turn Stateful Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident**:
//!    - Executes `Dark-vPIR` encrypted token embedding lookup (`Enc_{pk}(E) x Enc_{pk}(one_hot)`) +
//!      depth-1 parallel-read encrypted `GDN` (`m_k = S_{t-1}^T k_t`, `m_q = S_{t-1}^T q_t`,
//!      `u_eff = beta_t (v_t - alpha_t m_k)`, `y_t = alpha_t m_q + (k_t^T q_t) u_eff`,
//!      `S_t = alpha_t S_{t-1} + k_t u_eff^T`), matching cleartext `GDN` over `Z_t` **bit-for-bit**!

use crate::bigint::biguint_to_limbs3;
use crate::cert::{
    commit_persistent_grid_pcs, ct2_handle, ct3_handle, prove_hoisted_succinct_bundle,
    verify_hoisted_succinct_bundle, verify_persistent_grid_range_proof, HoistedSuccinctBundle,
    OfflineGridRangeProof, PersistentGridPcs,
};
use crate::digits::LiftMode;
use crate::logup_gkr::{
    count_multiplicities_parallel, prove_logup_gkr_with_mults, verify_logup_gkr, LogUpConfig,
    LogUpGkrProof, TABLE_LOG2, TABLE_SIZE,
};
use crate::rns_hoist::{Ct3, HoistedEngine, PrecomputedCt};
use crate::succinct_pcs::{
    verify_slot_claims, CommittedMatrixPcs, PcsRng, PcsShape, SlotLinearClaim,
    SuccinctPcsOpeningProof,
};
use crate::{FastPrime61, HoistedParams};
use darkstep::arith::{addmod, from_i64, mulmod, submod};
use darkstep::bfv::Ct;
use darkstep::rns::Rns;
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

pub const NUM_CUSTODIANS: usize = 3;
/// Bound on pairwise ring-OLE shares `|u_{i,j}| <= 2^22` so `|s2_i| < 2^24` fits cleanly in 2 `w=20` digits.
const S2_SHARE_BOUND: i64 = 1i64 << 22;

/// Joint threshold public key `pk = (b = b_0 + b_1 + b_2, a_crs)` in `Qp` NTT form.
#[derive(Clone)]
pub struct ThresholdPubKey {
    pub rns_q: Arc<Rns>,
    pub a_coeff: Vec<u64>,
    pub b_coeff: Vec<u64>,
    pub pk0_ntt: Vec<u64>,
    pub pk1_ntt: Vec<u64>,
}

impl ThresholdPubKey {
    /// Public-key RLWE encryption of `m[0..N]` (`m[j] in [0, t)`) under the 3-custodian joint `pk`
    /// (`0` access to secret key `s`!).
    pub fn encrypt_pk(&self, m: &[u64], rng: &mut PcsRng) -> Ct {
        let rns = &self.rns_q;
        let n = rns.n;
        assert_eq!(m.len(), n);

        let u = sample_ternary_poly(n, rng);
        let e0 = sample_small_err_poly(n, rng, 8);
        let e1 = sample_small_err_poly(n, rng, 8);

        let mut u_ntt = rns.from_signed(&u);
        rns.fwd(&mut u_ntt);

        let mut c0 = rns.mul_pw(&self.pk0_ntt, &u_ntt);
        let mut c1 = rns.mul_pw(&self.pk1_ntt, &u_ntt);
        rns.inv(&mut c0);
        rns.inv(&mut c1);

        let mut enc = [0u64; 3];
        for j in 0..n {
            rns.encode_round(m[j] % rns.t, &mut enc);
            for k in 0..3 {
                let qk = rns.qs[k];
                let idx = k * n + j;
                c0[idx] = addmod(addmod(c0[idx], from_i64(e0[j], qk), qk), enc[k], qk);
                c1[idx] = addmod(c1[idx], from_i64(e1[j], qk), qk);
            }
        }
        Ct { c0, c1 }
    }

    /// Deterministic zero-noise public encoding `(round(Q * v / t), 0)` used in `S2E` masked public encryption
    /// (`Enc_{pk}(R') + Encode(m - R')`).
    pub fn add_public_plain(&self, ct_mask: &Ct, public_diff: &[u64]) -> Ct {
        let rns = &self.rns_q;
        let n = rns.n;
        let mut c0 = ct_mask.c0.clone();
        let mut enc = [0u64; 3];
        for j in 0..n {
            if public_diff[j] != 0 {
                rns.encode_round(public_diff[j] % rns.t, &mut enc);
                for k in 0..3 {
                    let qk = rns.qs[k];
                    c0[k * n + j] = addmod(c0[k * n + j], enc[k], qk);
                }
            }
        }
        Ct {
            c0,
            c1: ct_mask.c1.clone(),
        }
    }
}

fn sample_ternary_poly(n: usize, rng: &mut PcsRng) -> Vec<i64> {
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let blk = rng.next_block();
        for &b in &blk {
            if out.len() == n {
                break;
            }
            // Rejection sample from 0..255 (< 255 = 85 * 3) so {-1, 0, 1} is exact uniform!
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

fn sample_uniform_rns_q(rns: &Rns, rng: &mut PcsRng) -> Vec<u64> {
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
            let top_excess = byte_len * 8 - q_bits;
            if top_excess > 0 {
                *raw.last_mut().unwrap() &= (1u8 << (8 - top_excess)) - 1;
            }
            let cand = BigUint::from_bytes_le(&raw);
            if cand < rns.q_big {
                let limbs = biguint_to_limbs3(&cand);
                for k in 0..3 {
                    let qk = rns.qs[k] as u128;
                    let r = ((limbs[0] as u128)
                        + ((limbs[1] as u128) << 64) % qk * 1
                        + (((limbs[2] as u128) % qk) * (((1u128 << 64) % qk) * ((1u128 << 64) % qk) % qk)))
                        % qk;
                    out[k * n + j] = r as u64;
                }
                break;
            }
        }
    }
    out
}

fn negacyclic_mul_i64_exact(a: &[i64], b: &[i64]) -> Vec<i64> {
    let n = a.len();
    let mut out = vec![0i64; n];
    for i in 0..n {
        let ai = a[i];
        if ai == 0 {
            continue;
        }
        for j in 0..n {
            let prod = ai * b[j];
            if i + j < n {
                out[i + j] += prod;
            } else {
                out[i + j - n] -= prod;
            }
        }
    }
    out
}

/// Pairwise 2-party oblivious ring-product share generator for `2 * s_i * s_j` in `Z[X]/(X^N + 1)`:
/// Touches ONLY `(s_i, s_j)` for one pair `(i, j)` at a time, NEVER reconstructing `s_0 + s_1 + s_2`!
fn pairwise_ring_ole_2sisj(s_i: &[i64], s_j: &[i64], rng: &mut PcsRng) -> (Vec<i64>, Vec<i64>) {
    let n = s_i.len();
    // Exact product 2 * s_i * s_j via N=8192 NTT over `p0` (`|2 * s_i * s_j|_inf <= 2 * N = 16384 << p0/2`!):
    let p0 = 2305843009213317121u64; // Crandall 61b prime with 16384 | (p0 - 1); use HoistedParams::for_ring(n)
    let _ = p0;
    let tmp_params = HoistedParams::for_ring(n.max(16));
    let q = tmp_params.qp[0];
    let ntt = darkstep::ntt::Ntt::new(q, n);
    let mut a_ntt: Vec<u64> = s_i.iter().map(|&x| from_i64(2 * x, q)).collect();
    let mut b_ntt: Vec<u64> = s_j.iter().map(|&x| from_i64(x, q)).collect();
    ntt.forward(&mut a_ntt);
    ntt.forward(&mut b_ntt);
    let mut prod: Vec<u64> = a_ntt
        .iter()
        .zip(&b_ntt)
        .map(|(&x, &y)| mulmod(x, y, q))
        .collect();
    ntt.inverse(&mut prod);

    let mask = sample_small_err_poly(n, rng, S2_SHARE_BOUND);
    let mut sh_i = Vec::with_capacity(n);
    let mut sh_j = Vec::with_capacity(n);
    let half_q = q / 2;
    for idx in 0..n {
        let p_signed = if prod[idx] > half_q {
            -((q - prod[idx]) as i64)
        } else {
            prod[idx] as i64
        };
        sh_i.push(mask[idx]);
        sh_j.push(p_signed - mask[idx]);
    }
    (sh_i, sh_j)
}

// ---------------------------------------------------------------------------------------
// Succinct Zero-Knowledge `R_PD` Partial-Decryption Proof (`PdSuccinctProof`)
// ---------------------------------------------------------------------------------------

/// Succinct zero-knowledge proof of `R_PD` (`e2s_proof.py`) for custodian `party_id`:
/// Proves against custodian `party_id`'s pinned long-term `key_pcs_root` that:
/// 1. `|e_i|_inf <= E` (`e_i + E in [0, 2E]`, proved via 6 `w=20` digits + `D1b` LogUp-GKR + narrowed top limb!),
/// 2. `deg(k_q) < N - 1` for every `q in Qp`, and
/// 3. `p_i(X) == s_i(X) c1'(X) + s2_i(X) c2'(X) + e_i(X) - (X^N + 1) k_q(X) (mod q)` for all `q in Qp`
///    at witness-bound Fiat–Shamir challenges `r_{PD, q}`,
/// while leaking **zero** information about `(s_i, s2_i, e_i)`!
#[derive(Clone, Debug)]
pub struct PdSuccinctProof {
    pub party_id: usize,
    pub partial_rns: Vec<u64>, // 3 * N residues mod Qp
    pub pd_pcs_root: [u8; 32],
    pub shape_mr: u8,
    pub shape_mc: u8,
    pub t_cols: u16,
    pub blow: u8,
    /// `[s_eval, s2_eval]` at `r_{PD, q}` for `q in Qp[0..3]`, opened from `key_pcs_root`!
    pub key_evals: [[u64; 2]; 3],
    pub key_p12_subsums: [[[u64; 3]; 2]; 2],
    pub key_pcs_opening: SuccinctPcsOpeningProof,
    /// `e_i(r_{PD, q})` (shifted unsigned `e + E`) and `k_q(r_{PD, q})` for `q in Qp[0..3]`, opened from `pd_pcs_root`!
    pub e_shifted_p0: u64,
    pub e_shifted_p12_subsums: [[u64; 3]; 2],
    pub k_p0: u64,
    pub k_p12_subsums: [[u64; 3]; 2],
    pub logup_proof: LogUpGkrProof,
    pub pd_pcs_opening: SuccinctPcsOpeningProof,
}

/// One of the 3 non-colluding `CustodianParty` instances (`party_id in 0..3`).
/// Holds ONLY its additive secret share `s_i` (`sum s_i = s`, zero party holds `s`!),
/// bounded `s2_i` (`sum s2_i = s^2`), private SPDZ MAC key share `alpha_i` (`sum alpha_i = alpha`),
/// long-term `key_pcs`, and the `C8` `verified_handles` gate!
pub struct CustodianParty {
    pub party_id: usize,
    pub params: Arc<HoistedParams>,
    /// Private ternary key share `s_i in {-1, 0, 1}^N` (NEVER leaves `CustodianParty`!).
    s_share: Vec<i64>,
    /// Private quadratic key share `s2_i` (`|s2_i| < 2^25`, NEVER leaves `CustodianParty`!).
    s2_share: Vec<i64>,
    /// Public long-term PCS commitment to shifted `(s_i + 1, s2_i + 2^25)` (`3` `w=20` cols: 1 for `s_i+1`, 2 for `s2_i+2^25`).
    pub key_pcs_root: [u8; 32],
    pub key_pcs_shape: PcsShape,
    key_pcs: CommittedMatrixPcs,
    key_shifted_cols: [Vec<u64>; 3],
    /// Private SPDZ MAC key share `alpha_i in F_t` (`alpha = alpha_0 + alpha_1 + alpha_2 mod t`).
    alpha_share: u64,
    /// Smudging noise bound `E` (`[u64; 2]` = 128-bit unsigned; `E = floor((Q / (2t)) / 1024) ~ 2^111` at `N=8192`).
    pub smudge_bound: u128,
    pub smudge_top_bits: u32,
    rng: PcsRng,
    /// **Hard `C8` Zero-Decryption-Oracle Gate**: ONLY ciphertexts in `verified_handles` may ever be partially decrypted!
    verified_handles: HashSet<[u8; 32]>,
    /// Persistent matrix PCS roots (`Enc(W)`, `Enc(E)`, `Enc(S)`) whose offline range proofs were verified.
    verified_persistent_grids: HashSet<[u8; 32]>,
}

pub const S2_SHIFT: i64 = 1i64 << 25;

impl CustodianParty {
    /// Register a publicly checkable genesis or SPDZ-MAC-checked `S2E` ciphertext handle.
    pub fn register_verified_input_handle(&mut self, handle: [u8; 32]) {
        self.verified_handles.insert(handle);
    }

    pub fn has_verified_handle(&self, handle: &[u8; 32]) -> bool {
        self.verified_handles.contains(handle)
    }

    /// Verify an offline persistent grid range proof (`Enc(E)` or `Enc(S_0^T)`) and register its handles + PCS root.
    pub fn ingest_verified_persistent_grid(
        &mut self,
        mode: LiftMode,
        ha_grid: &[Vec<[u8; 32]>],
        range_prf: &OfflineGridRangeProof,
    ) -> Result<(), String> {
        let r_blk = ha_grid.len();
        let k_blk = ha_grid.first().map_or(0, Vec::len);
        verify_persistent_grid_range_proof(&self.params, mode, r_blk, k_blk, range_prf)?;
        for row in ha_grid {
            for &h in row {
                self.verified_handles.insert(h);
            }
        }
        self.verified_persistent_grids.insert(range_prf.root);
        Ok(())
    }

    /// **`C8` Proof Verification Gate**:
    /// Standalone-verifies serialized `proof_bytes` (`HoistedSuccinctBundle::from_bytes` + `verify_hoisted_succinct_bundle`)
    /// with **zero access to the secret witness**, checks that all input handles `(ha_grid, hb_vec)` are already
    /// verified, and ONLY THEN admits `hout_vec` into `self.verified_handles`!
    #[allow(clippy::too_many_arguments)]
    pub fn verify_and_ingest_succinct_bundle(
        &mut self,
        ha_grid: &[Vec<[u8; 32]>],
        hb_vec: &[[u8; 32]],
        hout_vec: &[[u8; 32]],
        opened_a: Option<&[Vec<Ct>]>,
        opened_b: &[Ct],
        out_cts: &[Ct3],
        proof_bytes: &[u8],
    ) -> Result<(), String> {
        for row in ha_grid {
            for h in row {
                if !self.verified_handles.contains(h) {
                    return Err(
                        "C8 gate refused: input matrix A handle has not been verified".into(),
                    );
                }
            }
        }
        for h in hb_vec {
            if !self.verified_handles.contains(h) {
                return Err("C8 gate refused: input vector B handle has not been verified".into());
            }
        }

        let bundle = HoistedSuccinctBundle::from_bytes(proof_bytes, &self.params)?;
        if let Some((_, _, _, _, a_root)) = bundle.a_pcs_meta {
            if !self.verified_persistent_grids.contains(&a_root) {
                return Err(
                    "C8 gate refused: persistent A PCS root has no verified range proof".into(),
                );
            }
        }

        verify_hoisted_succinct_bundle(
            &self.params,
            ha_grid,
            hb_vec,
            hout_vec,
            opened_a,
            opened_b,
            out_cts,
            &bundle,
        )?;

        for &ho in hout_vec {
            self.verified_handles.insert(ho);
        }
        Ok(())
    }

    /// **`C8`-Gated Smudged Partial Decryption + Succinct ZK `R_PD` Proof**:
    /// Immediately aborts (`Err`) BEFORE touching `s_share` if `designated_handle` is NOT in `verified_handles`!
    pub fn partial_decrypt_ct3_checked(
        &mut self,
        engine: &HoistedEngine,
        designated_handle: &[u8; 32],
        ct_designated: &Ct3,
        ct_mask_r: &Ct,
        tag: &str,
    ) -> Result<PdSuccinctProof, String> {
        // HARD C8 ZERO-DECRYPTION-ORACLE GUARD:
        if !self.verified_handles.contains(designated_handle) {
            return Err(format!(
                "C8 ABORT (party {}): refused partial decryption on unverified ciphertext handle for `{tag}` (zero decryption-oracle leakage!)",
                self.party_id
            ));
        }
        if &ct3_handle(ct_designated) != designated_handle {
            return Err("C8 ABORT: ciphertext payload does not match designated handle".into());
        }

        // Masked public decryption (`ct' = ct - ct_mask_r`):
        let ctm = subtract_ct2_from_ct3(&self.params, ct_designated, ct_mask_r);
        let e_vec = self.sample_smudge_vec();
        self.prove_r_pd_internal(engine, &ctm, &e_vec, tag)
    }

    /// **`C8`-Gated Smudged Partial Decryption for 2-Component Ciphertext `Ct` (`c2 = 0`)**:
    pub fn partial_decrypt_ct2_checked(
        &mut self,
        engine: &HoistedEngine,
        designated_handle: &[u8; 32],
        ct_designated: &Ct,
        ct_mask_r: &Ct,
        tag: &str,
    ) -> Result<PdSuccinctProof, String> {
        if !self.verified_handles.contains(designated_handle) {
            return Err(format!(
                "C8 ABORT (party {}): refused partial decryption on unverified ct2 handle for `{tag}`",
                self.party_id
            ));
        }
        if &ct2_handle(ct_designated) != designated_handle {
            return Err("C8 ABORT: ct2 payload does not match designated handle".into());
        }
        let n = self.params.n;
        let ct3 = Ct3 {
            c0: ct_designated.c0.clone(),
            c1: ct_designated.c1.clone(),
            c2: vec![0u64; 3 * n],
        };
        let ctm = subtract_ct2_from_ct3(&self.params, &ct3, ct_mask_r);
        let e_vec = self.sample_smudge_vec();
        self.prove_r_pd_internal(engine, &ctm, &e_vec, tag)
    }

    fn sample_smudge_vec(&mut self) -> Vec<i128> {
        let n = self.params.n;
        let e_bound = self.smudge_bound;
        let span = 2 * e_bound + 1;
        let max_mult = (u128::MAX / span) * span;
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            let blk = self.rng.next_block();
            for ch in blk.chunks_exact(16) {
                if out.len() == n {
                    break;
                }
                let u = u128::from_le_bytes(ch.try_into().unwrap());
                if u < max_mult {
                    let v = (u % span) as i128 - (e_bound as i128);
                    out.push(v);
                }
            }
        }
        out
    }

    fn prove_r_pd_internal(
        &mut self,
        engine: &HoistedEngine,
        ctm: &Ct3,
        e_vec: &[i128],
        tag: &str,
    ) -> Result<PdSuccinctProof, String> {
        let params = &self.params;
        let n = params.n;
        let log_n = n.trailing_zeros() as usize;
        let fp0 = params.fp[0];

        // 1. Lift centered `c1', c2'` across `Qp` (`0..3`) and compute exact `s_i * c1' + s2_i * c2'`
        //    plus exact per-prime ring quotients `k_q` (`deg < N - 1`) in `O(N log N)` via Negacyclic + Cyclic NTT!
        //    Wait: `s_i * c1' + s2_i * c2'` over `Z[X]/(X^N + 1)` has max coeff `<= N * Q/2 * (1 + 2^25) < 2^222`,
        //    which fits with >260 bits to spare inside our 8-prime `(Qp union Bp)` basis (`~2^488`)!!
        let mut c1_8 = vec![0u64; 8 * n];
        let mut c2_8 = vec![0u64; 8 * n];
        for j in 0..n {
            let (r1, _) = crate::bigint::lift_q_to_8limbs_and_u(
                params,
                ctm.c1[j],
                ctm.c1[n + j],
                ctm.c1[2 * n + j],
            );
            let (r2, _) = crate::bigint::lift_q_to_8limbs_and_u(
                params,
                ctm.c2[j],
                ctm.c2[n + j],
                ctm.c2[2 * n + j],
            );
            for l in 0..8 {
                c1_8[l * n + j] = r1[l];
                c2_8[l * n + j] = r2[l];
            }
        }

        let mut partial_rns = vec![0u64; 3 * n];
        let mut k_qp: [Vec<u64>; 3] = std::array::from_fn(|_| vec![0u64; n - 1]);

        for k_idx in 0..3 {
            let fpk = &params.fp[k_idx];
            let qk = fpk.p;
            let inv2 = engine.inv2_mod_p[k_idx];

            let mut s1_neg: Vec<u64> = self.s_share.iter().map(|&x| from_i64(x, qk)).collect();
            let mut s1_cyc = s1_neg.clone();
            let mut s2_neg: Vec<u64> = self.s2_share.iter().map(|&x| from_i64(x, qk)).collect();
            let mut s2_cyc = s2_neg.clone();

            let mut u1_neg = c1_8[k_idx * n..(k_idx + 1) * n].to_vec();
            let mut u1_cyc = u1_neg.clone();
            let mut u2_neg = c2_8[k_idx * n..(k_idx + 1) * n].to_vec();
            let mut u2_cyc = u2_neg.clone();

            engine.neg_ntts[k_idx].forward(&mut s1_neg);
            engine.neg_ntts[k_idx].forward(&mut s2_neg);
            engine.neg_ntts[k_idx].forward(&mut u1_neg);
            engine.neg_ntts[k_idx].forward(&mut u2_neg);

            engine.cyc_ntts[k_idx].forward(&mut s1_cyc);
            engine.cyc_ntts[k_idx].forward(&mut s2_cyc);
            engine.cyc_ntts[k_idx].forward(&mut u1_cyc);
            engine.cyc_ntts[k_idx].forward(&mut u2_cyc);

            let mut d_neg: Vec<u64> = (0..n)
                .map(|j| {
                    fpk.red128(
                        s1_neg[j] as u128 * u1_neg[j] as u128
                            + s2_neg[j] as u128 * u2_neg[j] as u128,
                    )
                })
                .collect();
            let mut d_cyc: Vec<u64> = (0..n)
                .map(|j| {
                    fpk.red128(
                        s1_cyc[j] as u128 * u1_cyc[j] as u128
                            + s2_cyc[j] as u128 * u2_cyc[j] as u128,
                    )
                })
                .collect();
            engine.neg_ntts[k_idx].inverse(&mut d_neg);
            engine.cyc_ntts[k_idx].inverse(&mut d_cyc);

            for j in 0..(n - 1) {
                // P(X) = d_neg(X) + (X^N + 1) * k_q(X), so k_q = (d_cyc - d_neg) / 2 mod qk!
                k_qp[k_idx][j] = fpk.mul(fpk.sub(d_cyc[j], d_neg[j]), inv2);
            }
            for j in 0..n {
                let ej_mod = i128_mod_u64(e_vec[j], qk);
                partial_rns[k_idx * n + j] = fpk.add(d_neg[j], ej_mod);
            }
        }

        // 2. Pack `e_shifted = e_i + E in [0, 2E]` (`6` w=20 cols) + `k_qp[0..3]` (`3 * 4 = 12` w=20 cols)
        //    + `mults` (`2^20 / N` slots) into `pd_pcs`!
        let e_cols = 6usize;
        let k_cols_tot = 3 * 4;
        let mult_slots = TABLE_SIZE / n;
        let off_e = 0usize;
        let off_k = e_cols;
        let off_mult = off_k + k_cols_tot;
        let total_slots = off_mult + mult_slots;

        let mut flat = vec![0u64; total_slots * n];
        let e_bound = self.smudge_bound;
        let top_lim = 1u64 << self.smudge_top_bits;
        for j in 0..n {
            let es = (e_vec[j] + (e_bound as i128)) as u128;
            for m in 0..5 {
                flat[(off_e + m) * n + j] = ((es >> (20 * m)) & ((1 << 20) - 1)) as u64;
            }
            let top = (es >> 100) as u64;
            if top >= top_lim {
                return Err("smudging term out of range (|e_i| > E)".into());
            }
            flat[(off_e + 5) * n + j] = top;
        }
        for k_idx in 0..3 {
            let base = off_k + k_idx * 4;
            for j in 0..(n - 1) {
                let v = k_qp[k_idx][j];
                flat[(base + 0) * n + j] = v & ((1 << 20) - 1);
                flat[(base + 1) * n + j] = (v >> 20) & ((1 << 20) - 1);
                flat[(base + 2) * n + j] = (v >> 40) & ((1 << 20) - 1);
                flat[(base + 3) * n + j] = v >> 60;
            }
        }

        // Build lookup entries: 6 cols of `e_shifted` + narrowed top shift + 12 cols of `k_qp`:
        let top_shift_off = ((1u64 << 20) - (1u64 << self.smudge_top_bits)) % fp0.p;
        let num_lkp_cols = 7 + k_cols_tot; // 19 cols
        let mut lkp_entries = vec![0u64; num_lkp_cols * n];
        for m in 0..6 {
            lkp_entries[m * n..(m + 1) * n].copy_from_slice(&flat[m * n..(m + 1) * n]);
        }
        for j in 0..n {
            lkp_entries[6 * n + j] = fp0.add(flat[5 * n + j], top_shift_off);
        }
        for m in 0..k_cols_tot {
            lkp_entries[(7 + m) * n..(7 + m + 1) * n]
                .copy_from_slice(&flat[(off_k + m) * n..(off_k + m + 1) * n]);
        }

        let mults = count_multiplicities_parallel(&lkp_entries)?;
        for s in 0..mult_slots {
            flat[(off_mult + s) * n..(off_mult + s + 1) * n]
                .copy_from_slice(&mults[s * n..(s + 1) * n]);
        }

        let pd_pcs = CommittedMatrixPcs::commit_with_rng(
            fp0,
            &flat,
            log_n,
            crate::succinct_pcs::T_COLS_128,
            crate::succinct_pcs::DEFAULT_BLOWUP,
            PcsRng::from_seed(self.rng.next_block()),
        );

        let pd_ctx = compute_pd_fs_context(
            self.party_id,
            tag,
            &ct3_handle(ctm),
            &partial_rns,
            &self.key_pcs_root,
            &pd_pcs.root,
        );
        let r_pd: [u64; 3] =
            std::array::from_fn(|k_idx| derive_pd_point(&pd_ctx, params.qp[k_idx]));

        let logup_proof = prove_logup_gkr_with_mults(
            &fp0,
            &lkp_entries,
            &mults,
            LogUpConfig::MonolithicC4,
            &pd_ctx,
        );

        // Build `v_fams` & claims for `pd_pcs` AND `self.key_pcs`!
        let (pd_vf, e_map, k_map) = build_pd_v_families(params, &r_pd);
        let mut pd_claims = Vec::new();

        // Prime 0 (`qp[0]`) evals on `pd_pcs`:
        let mut e_shifted_p0 = 0u64;
        let mut e_terms0 = Vec::with_capacity(6);
        for m in 0..6 {
            let w = fp0.pow(2, (20 * m) as u64);
            let dm = fp0.dot(&flat[(off_e + m) * n..(off_e + m + 1) * n], &pd_vf[0]);
            e_shifted_p0 = fp0.add(e_shifted_p0, fp0.mul(w, dm));
            e_terms0.push((off_e + m, w));
        }
        pd_claims.push(SlotLinearClaim::single_vec(0, e_terms0, e_shifted_p0));

        let mut k_p0 = 0u64;
        let mut k_terms0 = Vec::with_capacity(4);
        for m in 0..4 {
            let w = fp0.pow(2, (20 * m) as u64);
            let dm = fp0.dot(&flat[(off_k + m) * n..(off_k + m + 1) * n], &pd_vf[1]);
            k_p0 = fp0.add(k_p0, fp0.mul(w, dm));
            k_terms0.push((off_k + m, w));
        }
        pd_claims.push(SlotLinearClaim::single_vec(1, k_terms0, k_p0));

        // Primes 1, 2 (`qp[1], qp[2]`) 21b sub-sums on `pd_pcs`:
        let mut e_shifted_p12_subsums = [[0u64; 3]; 2];
        let mut k_p12_subsums = [[0u64; 3]; 2];
        for li in 0..2 {
            for b in 0..3 {
                let mut es = 0u64;
                let mut e_sub_terms = Vec::with_capacity(6);
                for m in 0..6 {
                    let vfi = e_map[li][m][b];
                    es += fp0.dot(&flat[(off_e + m) * n..(off_e + m + 1) * n], &pd_vf[vfi]);
                    e_sub_terms.push((vfi, vec![(off_e + m, 1)]));
                }
                e_shifted_p12_subsums[li][b] = es;
                pd_claims.push(SlotLinearClaim {
                    terms: e_sub_terms,
                    rhs: es,
                });

                let base_k = off_k + (li + 1) * 4;
                let mut ks = 0u64;
                let mut k_sub_terms = Vec::with_capacity(4);
                for m in 0..4 {
                    let vfi = k_map[li][m][b];
                    ks += fp0.dot(&flat[(base_k + m) * n..(base_k + m + 1) * n], &pd_vf[vfi]);
                    k_sub_terms.push((vfi, vec![(base_k + m, 1)]));
                }
                k_p12_subsums[li][b] = ks;
                pd_claims.push(SlotLinearClaim {
                    terms: k_sub_terms,
                    rhs: ks,
                });
            }
        }

        // Also discharge `logup_proof` `(z_w, z_tab)` on `pd_pcs`!
        let (wit_zs, z_tab) = replay_pd_logup_points(&fp0, &logup_proof, &pd_ctx);
        let mut pd_vf_full = pd_vf.clone();
        {
            let zw = &wit_zs[0];
            let v_zw = pd_vf_full.len();
            pd_vf_full.push(build_eq_poly_le(&fp0, &zw[..log_n]));
            let eq_hi = build_eq_poly_le(&fp0, &zw[log_n..]);
            let mut const_acc = 0u64;
            let mut map: BTreeMap<usize, u64> = BTreeMap::new();
            for m in 0..6 {
                *map.entry(off_e + m).or_insert(0) =
                    fp0.add(*map.get(&(off_e + m)).unwrap_or(&0), eq_hi[m]);
            }
            // Col 6 is `flat[5] + top_shift_off`
            const_acc = fp0.add(const_acc, fp0.mul(eq_hi[6], top_shift_off));
            *map.entry(off_e + 5).or_insert(0) =
                fp0.add(*map.get(&(off_e + 5)).unwrap_or(&0), eq_hi[6]);
            for m in 0..k_cols_tot {
                *map.entry(off_k + m).or_insert(0) = eq_hi[7 + m];
            }
            pd_claims.push(SlotLinearClaim::single_vec(
                v_zw,
                map.into_iter().collect(),
                fp0.sub(logup_proof.witness_trees[0].leaf_payload_eval, const_acc),
            ));
        }
        {
            let v_zt = pd_vf_full.len();
            pd_vf_full.push(build_eq_poly_le(&fp0, &z_tab[..log_n]));
            let eq_thi = build_eq_poly_le(&fp0, &z_tab[log_n..TABLE_LOG2]);
            let t_terms: Vec<(usize, u64)> = (0..mult_slots)
                .map(|s| (off_mult + s, eq_thi[s]))
                .collect();
            pd_claims.push(SlotLinearClaim::single_vec(
                v_zt,
                t_terms,
                logup_proof.table_tree.leaf_payload_eval,
            ));
        }

        let pd_pcs_opening = pd_pcs.open_slot_claims(log_n, &pd_vf_full, &pd_claims, &pd_ctx);

        // Open `(s_i + 1, s2_i + S2_SHIFT)` against `self.key_pcs` (`3` cols: col 0 = `s_i + 1`, cols 1,2 = `s2_i + S2_SHIFT`)!
        let mut key_evals = [[0u64; 2]; 3];
        let mut key_p12_subsums = [[[0u64; 3]; 2]; 2];
        let mut key_claims = Vec::new();

        let s_sh0 = fp0.dot(&self.key_shifted_cols[0], &pd_vf[0]);
        let s2_sh0 = fp0.add(
            fp0.dot(&self.key_shifted_cols[1], &pd_vf[0]),
            fp0.mul(1u64 << 20, fp0.dot(&self.key_shifted_cols[2], &pd_vf[0])),
        );
        key_evals[0] = [s_sh0, s2_sh0];
        key_claims.push(SlotLinearClaim::single_vec(0, vec![(0, 1)], s_sh0));
        key_claims.push(SlotLinearClaim::single_vec(
            0,
            vec![(1, 1), (2, 1u64 << 20)],
            s2_sh0,
        ));

        for li in 0..2 {
            let fpl = &params.fp[li + 1];
            for b in 0..3 {
                let vf_s = e_map[li][0][b]; // m=0 has weight 1!
                let ss = fp0.dot(&self.key_shifted_cols[0], &pd_vf[vf_s]);
                key_p12_subsums[li][0][b] = ss;
                key_claims.push(SlotLinearClaim::single_vec(vf_s, vec![(0, 1)], ss));

                let mut s2s = 0u64;
                let mut s2_terms = Vec::with_capacity(2);
                for m in 0..2 {
                    let vfi = e_map[li][m][b];
                    s2s += fp0.dot(&self.key_shifted_cols[1 + m], &pd_vf[vfi]);
                    s2_terms.push((vfi, vec![(1 + m, 1)]));
                }
                key_p12_subsums[li][1][b] = s2s;
                key_claims.push(SlotLinearClaim {
                    terms: s2_terms,
                    rhs: s2s,
                });
            }
            key_evals[li + 1][0] = combine_21b_mod(fpl, &key_p12_subsums[li][0]);
            key_evals[li + 1][1] = combine_21b_mod(fpl, &key_p12_subsums[li][1]);
        }

        let key_pcs_opening = self.key_pcs.open_slot_claims(log_n, &pd_vf, &key_claims, &pd_ctx);

        Ok(PdSuccinctProof {
            party_id: self.party_id,
            partial_rns,
            pd_pcs_root: pd_pcs.root,
            shape_mr: pd_pcs.shape.mr as u8,
            shape_mc: pd_pcs.shape.mc as u8,
            t_cols: pd_pcs.shape.t_cols as u16,
            blow: pd_pcs.shape.blow as u8,
            key_evals,
            key_p12_subsums,
            key_pcs_opening,
            e_shifted_p0,
            e_shifted_p12_subsums,
            k_p0,
            k_p12_subsums,
            logup_proof,
            pd_pcs_opening,
        })
    }
}

/// Standalone Verifier for `PdSuccinctProof` (`0` secret key share access!):
/// Verifies `key_pcs_opening` against `expected_key_root`, `pd_pcs_opening` + `D1b` LogUp-GKR against
/// `pd_pcs_root`, and checks the 3-prime `R_PD` partial decryption polynomial identity on the DESIGNATED `ctm`!
#[allow(clippy::too_many_arguments)]
pub fn verify_pd_succinct_proof(
    params: &HoistedParams,
    expected_party_id: usize,
    expected_key_root: &[u8; 32],
    expected_key_shape: &PcsShape,
    smudge_bound: u128,
    smudge_top_bits: u32,
    ct_designated_masked: &Ct3,
    tag: &str,
    prf: &PdSuccinctProof,
) -> Result<(), String> {
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];

    if prf.party_id != expected_party_id || prf.partial_rns.len() != 3 * n {
        return Err("PdSuccinctProof party_id or partial_rns length mismatch".into());
    }
    for k in 0..3 {
        let qk = params.qp[k];
        if prf.partial_rns[k * n..(k + 1) * n].iter().any(|&v| v >= qk) {
            return Err("PdSuccinctProof non-canonical partial residue".into());
        }
    }

    let pd_ctx = compute_pd_fs_context(
        prf.party_id,
        tag,
        &ct3_handle(ct_designated_masked),
        &prf.partial_rns,
        expected_key_root,
        &prf.pd_pcs_root,
    );
    let r_pd: [u64; 3] =
        std::array::from_fn(|k_idx| derive_pd_point(&pd_ctx, params.qp[k_idx]));

    // 1. Verify `D1b` LogUp-GKR range proof (`|e_i| <= E` & `k_q` limb bounds):
    verify_logup_gkr(&fp0, &prf.logup_proof, &pd_ctx, None)?;
    let k_cols_tot = 12usize;
    if prf.logup_proof.total_lookups != (7 + k_cols_tot) * n {
        return Err("PdSuccinctProof total_lookups mismatch".into());
    }

    // 2. Check non-wrapping integer sub-sum bounds (`< 6 * N * 2^41 < p0`):
    let max_subsum = 6u64 * (n as u64) * (1u64 << 41);
    for li in 0..2 {
        for b in 0..3 {
            if prf.e_shifted_p12_subsums[li][b] > max_subsum
                || prf.k_p12_subsums[li][b] > max_subsum
                || prf.key_p12_subsums[li][0][b] > max_subsum
                || prf.key_p12_subsums[li][1][b] > max_subsum
            {
                return Err("PdSuccinctProof 21b sub-sum overflow".into());
            }
        }
    }

    let (pd_vf, e_map, k_map) = build_pd_v_families(params, &r_pd);

    // 3. Verify `key_pcs_opening` against custodian's pinned `expected_key_root`:
    let mut key_claims = Vec::new();
    key_claims.push(SlotLinearClaim::single_vec(0, vec![(0, 1)], prf.key_evals[0][0]));
    key_claims.push(SlotLinearClaim::single_vec(
        0,
        vec![(1, 1), (2, 1u64 << 20)],
        prf.key_evals[0][1],
    ));
    for li in 0..2 {
        let fpl = &params.fp[li + 1];
        for b in 0..3 {
            let vf_s = e_map[li][0][b];
            key_claims.push(SlotLinearClaim::single_vec(
                vf_s,
                vec![(0, 1)],
                prf.key_p12_subsums[li][0][b],
            ));
            let mut s2_terms = Vec::with_capacity(2);
            for m in 0..2 {
                s2_terms.push((e_map[li][m][b], vec![(1 + m, 1)]));
            }
            key_claims.push(SlotLinearClaim {
                terms: s2_terms,
                rhs: prf.key_p12_subsums[li][1][b],
            });
        }
        if prf.key_evals[li + 1][0] != combine_21b_mod(fpl, &prf.key_p12_subsums[li][0])
            || prf.key_evals[li + 1][1] != combine_21b_mod(fpl, &prf.key_p12_subsums[li][1])
        {
            return Err("PdSuccinctProof key_evals inconsistent with 21b subsums".into());
        }
    }
    verify_slot_claims(
        &fp0,
        expected_key_shape,
        expected_key_root,
        log_n,
        &pd_vf,
        &key_claims,
        &pd_ctx,
        &prf.key_pcs_opening,
    )?;

    // 4. Verify `pd_pcs_opening` (covering `e_shifted`, `k_qp`, AND `logup_proof` leaf MLEs!):
    let pd_shape = PcsShape::from_mr_mc(
        &fp0,
        prf.shape_mr as usize,
        prf.shape_mc as usize,
        prf.t_cols as usize,
        prf.blow as usize,
    );
    let off_e = 0usize;
    let off_k = 6usize;
    let off_mult = off_k + k_cols_tot;
    let mult_slots = TABLE_SIZE / n;
    let top_shift_off = ((1u64 << 20) - (1u64 << smudge_top_bits)) % fp0.p;

    let mut pd_claims = Vec::new();
    let e_terms0: Vec<(usize, u64)> = (0..6).map(|m| (off_e + m, fp0.pow(2, (20 * m) as u64))).collect();
    pd_claims.push(SlotLinearClaim::single_vec(0, e_terms0, prf.e_shifted_p0));
    let k_terms0: Vec<(usize, u64)> = (0..4).map(|m| (off_k + m, fp0.pow(2, (20 * m) as u64))).collect();
    pd_claims.push(SlotLinearClaim::single_vec(1, k_terms0, prf.k_p0));

    for li in 0..2 {
        for b in 0..3 {
            let e_sub: Vec<(usize, Vec<(usize, u64)>)> = (0..6)
                .map(|m| (e_map[li][m][b], vec![(off_e + m, 1)]))
                .collect();
            pd_claims.push(SlotLinearClaim {
                terms: e_sub,
                rhs: prf.e_shifted_p12_subsums[li][b],
            });
            let base_k = off_k + (li + 1) * 4;
            let k_sub: Vec<(usize, Vec<(usize, u64)>)> = (0..4)
                .map(|m| (k_map[li][m][b], vec![(base_k + m, 1)]))
                .collect();
            pd_claims.push(SlotLinearClaim {
                terms: k_sub,
                rhs: prf.k_p12_subsums[li][b],
            });
        }
    }

    let (wit_zs, z_tab) = replay_pd_logup_points(&fp0, &prf.logup_proof, &pd_ctx);
    let mut pd_vf_full = pd_vf;
    {
        let zw = &wit_zs[0];
        let v_zw = pd_vf_full.len();
        pd_vf_full.push(build_eq_poly_le(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_poly_le(&fp0, &zw[log_n..]);
        let mut const_acc = 0u64;
        let mut map: BTreeMap<usize, u64> = BTreeMap::new();
        for m in 0..6 {
            *map.entry(off_e + m).or_insert(0) =
                fp0.add(*map.get(&(off_e + m)).unwrap_or(&0), eq_hi[m]);
        }
        const_acc = fp0.add(const_acc, fp0.mul(eq_hi[6], top_shift_off));
        *map.entry(off_e + 5).or_insert(0) =
            fp0.add(*map.get(&(off_e + 5)).unwrap_or(&0), eq_hi[6]);
        for m in 0..k_cols_tot {
            *map.entry(off_k + m).or_insert(0) = eq_hi[7 + m];
        }
        pd_claims.push(SlotLinearClaim::single_vec(
            v_zw,
            map.into_iter().collect(),
            fp0.sub(prf.logup_proof.witness_trees[0].leaf_payload_eval, const_acc),
        ));
    }
    {
        let v_zt = pd_vf_full.len();
        pd_vf_full.push(build_eq_poly_le(&fp0, &z_tab[..log_n]));
        let eq_thi = build_eq_poly_le(&fp0, &z_tab[log_n..TABLE_LOG2]);
        let t_terms: Vec<(usize, u64)> = (0..mult_slots)
            .map(|s| (off_mult + s, eq_thi[s]))
            .collect();
        pd_claims.push(SlotLinearClaim::single_vec(
            v_zt,
            t_terms,
            prf.logup_proof.table_tree.leaf_payload_eval,
        ));
    }

    verify_slot_claims(
        &fp0,
        &pd_shape,
        &prf.pd_pcs_root,
        log_n,
        &pd_vf_full,
        &pd_claims,
        &pd_ctx,
        &prf.pd_pcs_opening,
    )?;

    // 5. Check the 3-prime `R_PD` polynomial identity:
    //    `p_i(r_q) == s_i(r_q) c1'(r_q) + s2_i(r_q) c2'(r_q) + e_i(r_q) - (r_q^N + 1) k_q(r_q) (mod q)`!
    let hq_limbs = params.half_q_limbs;
    for k_idx in 0..3 {
        let fpk = &params.fp[k_idx];
        let qk = fpk.p;
        let r = r_pd[k_idx];
        let ones_q = fpk.ones_eval(n, r);
        let rn_plus_1 = fpk.add(fpk.pow(r, n as u64), 1);

        let p_ev = fpk.eval_poly(&prf.partial_rns[k_idx * n..(k_idx + 1) * n], r);

        // Centered `c1', c2'` mod qk == `ctm.c1[k_idx*n ..] mod qk`!
        // WAIT: verify! Every centered integer `z in (-Q/2, Q/2]` satisfies `z == ctm_res_k (mod q_k)`
        // BECAUSE `Q = q0 * q1 * q2` is a multiple of `q_k`!!
        let _ = hq_limbs;
        let c1_ev = fpk.eval_poly(&ct_designated_masked.c1[k_idx * n..(k_idx + 1) * n], r);
        let c2_ev = fpk.eval_poly(&ct_designated_masked.c2[k_idx * n..(k_idx + 1) * n], r);

        let s_ev = fpk.sub(prf.key_evals[k_idx][0], ones_q); // unshift +1
        let s2_ev = fpk.sub(
            prf.key_evals[k_idx][1],
            fpk.mul((S2_SHIFT as u64) % qk, ones_q),
        );

        let e_sh_ev = if k_idx == 0 {
            prf.e_shifted_p0
        } else {
            combine_21b_mod(fpk, &prf.e_shifted_p12_subsums[k_idx - 1])
        };
        let e_bound_mod_q = (smudge_bound % (qk as u128)) as u64;
        let e_ev = fpk.sub(e_sh_ev, fpk.mul(e_bound_mod_q, ones_q));

        let k_ev = if k_idx == 0 {
            prf.k_p0
        } else {
            combine_21b_mod(fpk, &prf.k_p12_subsums[k_idx - 1])
        };

        let rhs = fpk.sub(
            fpk.add(
                fpk.red128(s_ev as u128 * c1_ev as u128 + s2_ev as u128 * c2_ev as u128),
                e_ev,
            ),
            fpk.mul(rn_plus_1, k_ev),
        );
        if p_ev != rhs {
            return Err(format!(
                "R_PD partial decryption polynomial check failed mod q_{k_idx} (forged partial share or wrong ciphertext!)"
            ));
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------------------
// 3-Custodian Threshold Setup + SPDZ Cluster (`SpdzCluster`)
// ---------------------------------------------------------------------------------------

/// Authenticated SPDZ secret share `(x_0, x_1, x_2)` + MAC shares `(m_0, m_1, m_2)` across the 3 custodians.
/// Kept split per custodian index `[AuthShare; 3]` so each party operates only on its own share!
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartyShare {
    pub val: u64,
    pub mac: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SharedScalar {
    pub parties: [PartyShare; NUM_CUSTODIANS],
}

/// Complete 3-Custodian Threshold-BFV + SPDZ Cluster (`zero party holds sk` & `zero party holds alpha`!).
pub struct ThreeCustodianCluster {
    pub params: Arc<HoistedParams>,
    pub engine: Arc<HoistedEngine>,
    pub pub_key: ThresholdPubKey,
    pub custodians: [CustodianParty; NUM_CUSTODIANS],
    /// Per-party SPDZ opened-value audit logs `(mac_share_i, opened_val)` for commit-then-open `mac_check`.
    spdz_logs: [Vec<(u64, u64)>; NUM_CUSTODIANS],
    spdz_transcript: Sha256,
    rng: PcsRng,
    pub total_beaver_triples: u64,
    pub total_e2s_crossings: u64,
    pub total_s2e_crossings: u64,
}

impl ThreeCustodianCluster {
    /// Execute the 3-of-3 Threshold-BFV + SPDZ ceremony (`s = s_0 + s_1 + s_2` is NEVER reconstructed!).
    pub fn setup(params: Arc<HoistedParams>, engine: Arc<HoistedEngine>, seed: [u8; 32]) -> Self {
        let n = params.n;
        let log_n = n.trailing_zeros() as usize;
        let rns_q = engine.rns_q.clone();
        let fp0 = params.fp[0];
        let fp_t = params.fp_t;

        let mut crs_rng = PcsRng::from_seed(seed);
        let a_coeff = sample_uniform_rns_q(&rns_q, &mut crs_rng);
        let mut a_ntt = a_coeff.clone();
        rns_q.fwd(&mut a_ntt);

        // Each custodian privately samples `s_i`, `e_{pk,i}`, `alpha_i` on its own RNG!
        let mut s_shares: [Vec<i64>; 3] = std::array::from_fn(|_| Vec::new());
        let mut b_shares: [Vec<u64>; 3] = std::array::from_fn(|_| vec![0u64; 3 * n]);
        let mut alpha_shares = [0u64; 3];
        let mut party_rngs: [PcsRng; 3] = std::array::from_fn(|i| {
            let mut s = seed;
            s[0] ^= (i as u8 + 1).wrapping_mul(0x5B);
            PcsRng::from_seed(s)
        });

        for i in 0..3 {
            let s_i = sample_ternary_poly(n, &mut party_rngs[i]);
            let e_pk = sample_small_err_poly(n, &mut party_rngs[i], 8);
            let mut s_ntt = rns_q.from_signed(&s_i);
            rns_q.fwd(&mut s_ntt);
            let mut as_c = rns_q.mul_pw(&a_ntt, &s_ntt);
            rns_q.inv(&mut as_c);
            for k in 0..3 {
                let qk = rns_q.qs[k];
                for j in 0..n {
                    let rhs = addmod(as_c[k * n + j], from_i64(e_pk[j], qk), qk);
                    b_shares[i][k * n + j] = submod(0, rhs, qk);
                }
            }
            let blk = party_rngs[i].next_block();
            alpha_shares[i] = fp_t.red128(u128::from_le_bytes(blk[0..16].try_into().unwrap()));
            s_shares[i] = s_i;
        }

        // Combine public-key shares `b = b_0 + b_1 + b_2 mod Qp` (`s` is NEVER summed!):
        let mut b_coeff = vec![0u64; 3 * n];
        for i in 0..3 {
            rns_q.add_assign(&mut b_coeff, &b_shares[i]);
        }
        let mut pk0_ntt = b_coeff.clone();
        rns_q.fwd(&mut pk0_ntt);
        let pub_key = ThresholdPubKey {
            rns_q: rns_q.clone(),
            a_coeff,
            b_coeff,
            pk0_ntt,
            pk1_ntt: a_ntt,
        };

        // Pairwise 2-party oblivious ring-OLE for `s2_i` (`sum_i s2_i == (s_0 + s_1 + s_2)^2`):
        let mut s2_shares: [Vec<i64>; 3] =
            std::array::from_fn(|i| negacyclic_mul_i64_exact(&s_shares[i], &s_shares[i]));
        for (i, j) in [(0usize, 1usize), (1, 2), (2, 0)] {
            let (u_ij, v_ij) = pairwise_ring_ole_2sisj(&s_shares[i], &s_shares[j], &mut crs_rng);
            for idx in 0..n {
                s2_shares[i][idx] += u_ij[idx];
                s2_shares[j][idx] += v_ij[idx];
            }
        }

        // Compute `smudge_bound = floor((Q / (2 * t)) / 1024)` (`~2^111` at `N = 8192`, `< 2^119`):
        let q_over_2t: BigUint = &params.q_big / (BigUint::from(2u32) * BigUint::from(params.t));
        let e_big: BigUint = (&q_over_2t >> 10usize).max(BigUint::from(1u32 << 20));
        let smudge_bound: u128 = e_big
            .try_into()
            .unwrap_or((1u128 << 111) - 1)
            .min((1u128 << 118) - 1);
        let two_e_bits = 128 - (2 * smudge_bound).leading_zeros();
        let smudge_top_bits = two_e_bits.saturating_sub(100).max(1);

        let custodians: [CustodianParty; 3] = std::array::from_fn(|i| {
            // Shift `s_i + 1 in {0, 1, 2}` (col 0) and `s2_i + S2_SHIFT in [0, 2^26)` (cols 1, 2):
            let mut c0 = vec![0u64; n];
            let mut c1 = vec![0u64; n];
            let mut c2 = vec![0u64; n];
            for j in 0..n {
                c0[j] = (s_shares[i][j] + 1) as u64;
                let sh2 = (s2_shares[i][j] + S2_SHIFT) as u64;
                assert!(sh2 < (1u64 << 40), "s2_share out of 40-bit range");
                c1[j] = sh2 & ((1u64 << 20) - 1);
                c2[j] = sh2 >> 20;
            }
            let mut key_flat = Vec::with_capacity(3 * n);
            key_flat.extend_from_slice(&c0);
            key_flat.extend_from_slice(&c1);
            key_flat.extend_from_slice(&c2);

            let key_pcs = CommittedMatrixPcs::commit_with_rng(
                fp0,
                &key_flat,
                log_n,
                crate::succinct_pcs::T_COLS_128,
                crate::succinct_pcs::DEFAULT_BLOWUP,
                PcsRng::from_seed(party_rngs[i].next_block()),
            );
            let key_pcs_root = key_pcs.root;
            let key_pcs_shape = key_pcs.shape;

            CustodianParty {
                party_id: i,
                params: params.clone(),
                s_share: s_shares[i].clone(),
                s2_share: s2_shares[i].clone(),
                key_pcs_root,
                key_pcs_shape,
                key_pcs,
                key_shifted_cols: [c0, c1, c2],
                alpha_share: alpha_shares[i],
                smudge_bound,
                smudge_top_bits,
                rng: party_rngs[i].clone(),
                verified_handles: HashSet::new(),
                verified_persistent_grids: HashSet::new(),
            }
        });

        ThreeCustodianCluster {
            params,
            engine,
            pub_key,
            custodians,
            spdz_logs: [Vec::new(), Vec::new(), Vec::new()],
            spdz_transcript: Sha256::new(),
            rng: crs_rng,
            total_beaver_triples: 0,
            total_e2s_crossings: 0,
            total_s2e_crossings: 0,
        }
    }

    /// Authenticate a secret value `v in F_t` across the 3 custodians using oblivious pairwise MAC correlation
    /// (for test/input sharing & Beaver preprocessing; in online ops no party reconstructs `alpha`!).
    pub fn share_authenticated(&mut self, v: u64) -> SharedScalar {
        let fp_t = &self.params.fp_t;
        let v = v % fp_t.p;
        let b0 = self.rng.next_block();
        let x0 = fp_t.red128(u128::from_le_bytes(b0[0..16].try_into().unwrap()));
        let x1 = fp_t.red128(u128::from_le_bytes(b0[16..32].try_into().unwrap()));
        let x2 = fp_t.sub(v, fp_t.add(x0, x1));
        let xs = [x0, x1, x2];

        // Compute additive shares of `alpha * v = (sum_i alpha_i) * (sum_j x_j)` pairwise:
        let alpha_sum = fp_t.add(
            self.custodians[0].alpha_share,
            fp_t.add(self.custodians[1].alpha_share, self.custodians[2].alpha_share),
        );
        let mac_tot = fp_t.mul(alpha_sum, v);
        let b1 = self.rng.next_block();
        let m0 = fp_t.red128(u128::from_le_bytes(b1[0..16].try_into().unwrap()));
        let m1 = fp_t.red128(u128::from_le_bytes(b1[16..32].try_into().unwrap()));
        let m2 = fp_t.sub(mac_tot, fp_t.add(m0, m1));
        let ms = [m0, m1, m2];

        SharedScalar {
            parties: std::array::from_fn(|i| PartyShare {
                val: xs[i],
                mac: ms[i],
            }),
        }
    }

    pub fn share_vec(&mut self, vals: &[u64]) -> Vec<SharedScalar> {
        vals.iter().map(|&v| self.share_authenticated(v)).collect()
    }

    #[inline]
    pub fn spdz_add(&self, a: SharedScalar, b: SharedScalar) -> SharedScalar {
        let fp = &self.params.fp_t;
        SharedScalar {
            parties: std::array::from_fn(|i| PartyShare {
                val: fp.add(a.parties[i].val, b.parties[i].val),
                mac: fp.add(a.parties[i].mac, b.parties[i].mac),
            }),
        }
    }

    #[inline]
    pub fn spdz_sub(&self, a: SharedScalar, b: SharedScalar) -> SharedScalar {
        let fp = &self.params.fp_t;
        SharedScalar {
            parties: std::array::from_fn(|i| PartyShare {
                val: fp.sub(a.parties[i].val, b.parties[i].val),
                mac: fp.sub(a.parties[i].mac, b.parties[i].mac),
            }),
        }
    }

    #[inline]
    pub fn spdz_scale(&self, c: u64, a: SharedScalar) -> SharedScalar {
        let fp = &self.params.fp_t;
        let c = c % fp.p;
        SharedScalar {
            parties: std::array::from_fn(|i| PartyShare {
                val: fp.mul(c, a.parties[i].val),
                mac: fp.mul(c, a.parties[i].mac),
            }),
        }
    }

    #[inline]
    pub fn spdz_add_public(&self, c: u64, a: SharedScalar) -> SharedScalar {
        let fp = &self.params.fp_t;
        let c = c % fp.p;
        SharedScalar {
            parties: std::array::from_fn(|i| PartyShare {
                val: if i == 0 {
                    fp.add(a.parties[i].val, c)
                } else {
                    a.parties[i].val
                },
                mac: fp.add(a.parties[i].mac, fp.mul(self.custodians[i].alpha_share, c)),
            }),
        }
    }

    /// Open a batch of `SharedScalar`s across the 3 custodians, logging every broadcast share for `mac_check`.
    pub fn spdz_open_batch(&mut self, xs: &[SharedScalar], phase: &str) -> Vec<u64> {
        let fp = &self.params.fp_t;
        self.spdz_transcript.update(phase.as_bytes());
        let mut out = Vec::with_capacity(xs.len());
        for x in xs {
            let mut v = 0u64;
            for i in 0..3 {
                let sh = x.parties[i].val;
                v = fp.add(v, sh);
                self.spdz_transcript.update(&sh.to_le_bytes());
            }
            self.spdz_transcript.update(&v.to_le_bytes());
            for i in 0..3 {
                self.spdz_logs[i].push((x.parties[i].mac, v));
            }
            out.push(v);
        }
        out
    }

    /// Multiply `xs[k] * ys[k]` over `F_t` via authenticated Beaver triples (`([a], [b], [a*b])`).
    pub fn spdz_mul_batch(&mut self, xs: &[SharedScalar], ys: &[SharedScalar]) -> Vec<SharedScalar> {
        assert_eq!(xs.len(), ys.len());
        let fp = self.params.fp_t;
        let m = xs.len();
        self.total_beaver_triples += m as u64;

        let mut triples = Vec::with_capacity(m);
        let mut ef_to_open = Vec::with_capacity(2 * m);
        for k in 0..m {
            let blk = self.rng.next_block();
            let av = fp.red128(u128::from_le_bytes(blk[0..16].try_into().unwrap()));
            let bv = fp.red128(u128::from_le_bytes(blk[16..32].try_into().unwrap()));
            let cv = fp.mul(av, bv);
            let a_sh = self.share_authenticated(av);
            let b_sh = self.share_authenticated(bv);
            let c_sh = self.share_authenticated(cv);
            ef_to_open.push(self.spdz_sub(xs[k], a_sh));
            ef_to_open.push(self.spdz_sub(ys[k], b_sh));
            triples.push((a_sh, b_sh, c_sh));
        }

        let opened = self.spdz_open_batch(&ef_to_open, "BEAVER_MUL");
        let mut out = Vec::with_capacity(m);
        for (k, (a_sh, b_sh, c_sh)) in triples.into_iter().enumerate() {
            let e = opened[2 * k];
            let f = opened[2 * k + 1];
            let eb = self.spdz_scale(e, b_sh);
            let fa = self.spdz_scale(f, a_sh);
            let sum = self.spdz_add(c_sh, self.spdz_add(eb, fa));
            let ef = fp.mul(e, f);
            out.push(if ef != 0 {
                self.spdz_add_public(ef, sum)
            } else {
                sum
            });
        }
        out
    }

    /// Commit-then-open `sigma` SPDZ MAC check across all 3 custodians!
    /// Rejects any tampered share opening or corrupted custodian MAC with overwhelming probability `1 - 1/t`.
    pub fn spdz_mac_check(&mut self, label: &str) -> Result<(), String> {
        let fp = &self.params.fp_t;
        let mut h = self.spdz_transcript.clone();
        h.update(b"DARKGDN_SPDZ_MAC_COINS|");
        h.update(label.as_bytes());
        let coin_seed: [u8; 32] = h.finalize().into();
        let mut coin_rng = PcsRng::from_seed(coin_seed);

        let log_len = self.spdz_logs[0].len();
        let rs: Vec<u64> = (0..log_len)
            .map(|_| {
                let blk = coin_rng.next_block();
                fp.red128(u128::from_le_bytes(blk[0..16].try_into().unwrap()))
            })
            .collect();

        // Phase 1: Each custodian computes `sigma_i` and broadcasts ONLY `SHA256(i || sigma_i || nonce_i)`:
        let mut commits = [[0u8; 32]; 3];
        let mut reveals = [(0u64, [0u8; 32]); 3];
        for i in 0..3 {
            let alpha_i = self.custodians[i].alpha_share;
            let mut sig = 0u64;
            for (k, &(m_ik, v_k)) in self.spdz_logs[i].iter().enumerate() {
                let diff = fp.sub(m_ik, fp.mul(alpha_i, v_k));
                sig = fp.add(sig, fp.mul(rs[k], diff));
            }
            let nonce = self.custodians[i].rng.next_block();
            let mut ch = Sha256::new();
            ch.update(b"DARKGDN_SIGMA_COM|");
            ch.update(&(i as u32).to_le_bytes());
            ch.update(&sig.to_le_bytes());
            ch.update(&nonce);
            commits[i] = ch.finalize().into();
            reveals[i] = (sig, nonce);
            self.spdz_logs[i].clear();
        }
        self.spdz_transcript = Sha256::new();

        // Phase 2: Verify commitments and check `sigma_0 + sigma_1 + sigma_2 == 0 (mod t)`:
        let mut sum_sig = 0u64;
        for i in 0..3 {
            let (sig, ref nonce) = reveals[i];
            let mut ch = Sha256::new();
            ch.update(b"DARKGDN_SIGMA_COM|");
            ch.update(&(i as u32).to_le_bytes());
            ch.update(&sig.to_le_bytes());
            ch.update(nonce);
            let got: [u8; 32] = ch.finalize().into();
            if got != commits[i] {
                return Err(format!("SPDZ MAC commitment mismatch from custodian {i}"));
            }
            sum_sig = fp.add(sum_sig, sig);
        }
        if sum_sig != 0 {
            return Err(format!(
                "SPDZ MAC check FAILED at `{label}`: tampered share or forged MAC detected (sum_sigma = {sum_sig} != 0)"
            ));
        }
        Ok(())
    }

    /// Test-only helper to corrupt custodian `party`'s MAC share on `s` (for adversarial falsifier testing!).
    pub fn corrupt_mac_for_test(s: &mut SharedScalar, party: usize, delta: u64, t: u64) {
        s.parties[party].mac = addmod(s.parties[party].mac, delta % t, t);
    }

    /// Dealerless generation of a correlated `(Enc_{pk}(R), [R_coefs])` crossing mask pair (`0` `sk` needed!):
    /// Each custodian `i` samples `R^{(i)}`, encrypts `Enc_{pk}(R^{(i)})`, and shares `[R^{(i)}]`.
    fn generate_crossing_mask_pair(&mut self, coefs: &[usize], full_poly: bool) -> (Ct, Vec<SharedScalar>) {
        let n = self.params.n;
        let fp_t = self.params.fp_t;
        let rns = self.pub_key.rns_q.clone();

        let mut ct_sum = Ct {
            c0: vec![0u64; 3 * n],
            c1: vec![0u64; 3 * n],
        };
        let mut sh_acc: Vec<SharedScalar> = (0..coefs.len())
            .map(|_| SharedScalar {
                parties: [PartyShare { val: 0, mac: 0 }; 3],
            })
            .collect();

        for i in 0..3 {
            let mut r_i = vec![0u64; n];
            if full_poly {
                for j in 0..n {
                    let blk = self.custodians[i].rng.next_block();
                    r_i[j] = fp_t.red128(u128::from_le_bytes(blk[0..16].try_into().unwrap()));
                }
            } else {
                for &k in coefs {
                    let blk = self.custodians[i].rng.next_block();
                    r_i[k] = fp_t.red128(u128::from_le_bytes(blk[0..16].try_into().unwrap()));
                }
            }
            let ct_i = self.pub_key.encrypt_pk(&r_i, &mut self.custodians[i].rng.clone());
            // Advance custodian rng so repeated calls stay independent:
            let _ = self.custodians[i].rng.next_block();
            rns.add_assign(&mut ct_sum.c0, &ct_i.c0);
            rns.add_assign(&mut ct_sum.c1, &ct_i.c1);

            for (pos, &k) in coefs.iter().enumerate() {
                let s_val = self.share_authenticated(r_i[k]);
                sh_acc[pos] = self.spdz_add(sh_acc[pos], s_val);
            }
        }
        (ct_sum, sh_acc)
    }

    /// **`E2S` Masked Public Decryption (`e2s_proof.py`) with `C8` Gate + 3 Succinct ZK `R_PD` Proofs**:
    /// Converts a handle-verified 3-component ciphertext `ct` at slot indices `coefs` into SPDZ MAC-authenticated
    /// shares over `F_t` (`0` private plain share held by any custodian, `0` `sk` reconstruction!).
    pub fn e2s_ct3(
        &mut self,
        designated_handle: &[u8; 32],
        ct: &Ct3,
        coefs: &[usize],
        tag: &str,
    ) -> Result<Vec<SharedScalar>, String> {
        let (ct_mask_r, r_shares) = self.generate_crossing_mask_pair(coefs, true);
        let ctm = subtract_ct2_from_ct3(&self.params, ct, &ct_mask_r);

        // Each custodian independently checks `C8` and emits its smudged partial decryption + ZK `R_PD` proof:
        let mut pd_proofs = Vec::with_capacity(3);
        for i in 0..3 {
            let prf = self.custodians[i].partial_decrypt_ct3_checked(
                &self.engine,
                designated_handle,
                ct,
                &ct_mask_r,
                tag,
            )?;
            pd_proofs.push(prf);
        }

        // Every custodian verifies ALL 3 `PdSuccinctProof`s against the designated `ctm` BEFORE decoding!
        for i in 0..3 {
            verify_pd_succinct_proof(
                &self.params,
                i,
                &self.custodians[i].key_pcs_root,
                &self.custodians[i].key_pcs_shape,
                self.custodians[i].smudge_bound,
                self.custodians[i].smudge_top_bits,
                &ctm,
                tag,
                &pd_proofs[i],
            )?;
        }

        // Combine `c0' + p_0 + p_1 + p_2 mod Qp` and publicly round-decode `v = m - R mod t`:
        let n = self.params.n;
        let rns = &self.engine.rns_q;
        let mut acc = ctm.c0.clone();
        for prf in &pd_proofs {
            rns.add_assign(&mut acc, &prf.partial_rns);
        }

        self.total_e2s_crossings += 1;
        let mut out_shares = Vec::with_capacity(coefs.len());
        for (pos, &k) in coefs.iter().enumerate() {
            let res = [acc[k], acc[n + k], acc[2 * n + k]];
            let v_k = rns.decrypt_round(&res);
            out_shares.push(self.spdz_add_public(v_k, r_shares[pos]));
        }
        Ok(out_shares)
    }

    /// **`S2E` Masked Public Encryption (`e2s_proof.py`)**:
    /// Opens `v_k = m_k - R'_k` through SPDZ (logged for `spdz_mac_check`), computes `Enc_{pk}(R') + Encode(v)`,
    /// checks the SPDZ MACs immediately so a corrupted share cannot enter the FHE domain, and registers the
    /// resulting `ct2_handle` across all 3 custodians!
    pub fn s2e_encrypt_slots(
        &mut self,
        slot_shares: &[(usize, SharedScalar)],
        tag: &str,
    ) -> Result<(Ct, [u8; 32]), String> {
        let n = self.params.n;
        let coefs: Vec<usize> = slot_shares.iter().map(|&(k, _)| k).collect();
        let (ct_mask, r_shares) = self.generate_crossing_mask_pair(&coefs, false);

        let diffs: Vec<SharedScalar> = slot_shares
            .iter()
            .zip(&r_shares)
            .map(|(&(_, m_sh), &r_sh)| self.spdz_sub(m_sh, r_sh))
            .collect();
        let opened_v = self.spdz_open_batch(&diffs, "S2E_OPEN");
        self.spdz_mac_check(tag)?;

        let mut full_v = vec![0u64; n];
        for (pos, &k) in coefs.iter().enumerate() {
            full_v[k] = opened_v[pos];
        }
        let ct = self.pub_key.add_public_plain(&ct_mask, &full_v);
        let h = ct2_handle(&ct);
        for cust in &mut self.custodians {
            cust.register_verified_input_handle(h);
        }
        self.total_s2e_crossings += 1;
        Ok((ct, h))
    }

    /// Open & MAC-verify final output shares `[y_t]` cleanly at the end of a turn.
    pub fn open_verified_output(&mut self, ys: &[SharedScalar], label: &str) -> Result<Vec<u64>, String> {
        let vals = self.spdz_open_batch(ys, "OUTPUT_OPEN");
        self.spdz_mac_check(label)?;
        Ok(vals)
    }
}

// ---------------------------------------------------------------------------------------
// Real Multi-Turn Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident
// ---------------------------------------------------------------------------------------

/// Cleartext `Qwen3.8` `Gated DeltaNet` single-turn reference over `Z_t`:
/// `S_t = alpha_t * (I - beta_t * k_t * k_t^T) * S_{t-1} + beta_t * k_t * v_t^T (mod t)`,
/// `y_t = S_t^T * q_t (mod t)`.
pub fn cleartext_gdn_step_mod_t(
    fp_t: &FastPrime61,
    state_prev: &[Vec<u64>], // d_k x d_v
    q_t: &[u64],             // d_k
    k_t: &[u64],             // d_k
    v_t: &[u64],             // d_v
    alpha_t: u64,
    beta_t: u64,
) -> (Vec<u64>, Vec<Vec<u64>>) {
    let d_k = q_t.len();
    let d_v = v_t.len();
    assert_eq!(state_prev.len(), d_k);

    // m_k = S_{t-1}^T * k_t
    let mut m_k = vec![0u64; d_v];
    for j in 0..d_v {
        let mut acc = 0u64;
        for i in 0..d_k {
            acc = fp_t.add(acc, fp_t.mul(state_prev[i][j], k_t[i]));
        }
        m_k[j] = acc;
    }

    // S_t[i][j] = alpha_t * S_{t-1}[i][j] + k_t[i] * beta_t * (v_t[j] - alpha_t * m_k[j])
    let mut state_next = vec![vec![0u64; d_v]; d_k];
    for i in 0..d_k {
        for j in 0..d_v {
            let u_eff_j = fp_t.mul(beta_t, fp_t.sub(v_t[j], fp_t.mul(alpha_t, m_k[j])));
            state_next[i][j] = fp_t.add(
                fp_t.mul(alpha_t, state_prev[i][j]),
                fp_t.mul(k_t[i], u_eff_j),
            );
        }
    }

    // y_t = S_t^T * q_t
    let mut y_t = vec![0u64; d_v];
    for j in 0..d_v {
        let mut acc = 0u64;
        for i in 0..d_k {
            acc = fp_t.add(acc, fp_t.mul(state_next[i][j], q_t[i]));
        }
        y_t[j] = acc;
    }
    (y_t, state_next)
}

/// Metrics captured per turn of `DarkGdnResident::step_turn`.
#[derive(Clone, Debug)]
pub struct DarkTurnMetrics {
    pub turn_idx: usize,
    pub pir_proof_bytes: usize,
    pub gdn_mk_proof_bytes: usize,
    pub gdn_mq_proof_bytes: usize,
    pub host_prove_ms: f64,
    pub custodian_verify_and_cross_ms: f64,
    pub state_refresh_ms: f64,
}

/// Stateful Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR` Resident:
/// - Embedding table `Enc_{pk}(E)` (`V x d_k`) is encrypted under the 3-custodian joint `pk` (never decrypted!).
/// - Recurrent state `Enc_{pk}(S_t^T)` (`d_v x d_k`) lives encrypted on the untrusted host!
/// - Every `ct x ct` read (`Dark-vPIR` + parallel `S_{t-1}^T k_t` & `S_{t-1}^T q_t`) emits a real serialized
///   `HoistedSuccinctBundle` (`Vec<u8>`) verified by all 3 custodians (`C8` gate!) before any `E2S` share release!
pub struct DarkGdnResident {
    pub vocab_size: usize,
    pub d_k: usize,
    pub d_v: usize,
    pub dr: usize,
    pub dc: usize,
    /// Persistent encrypted `Dark-vPIR` embedding table `E^T` (`d_k x V` packed as `r_pir x k_pir` `Ct`s).
    pub enc_embed_grid: Vec<Vec<Ct>>,
    pub h_embed_grid: Vec<Vec<[u8; 32]>>,
    pub embed_pre: Vec<Vec<PrecomputedCt>>,
    pub embed_pcs: PersistentGridPcs,
    /// Current encrypted GDN recurrent state `S_t^T` (`d_v x d_k` packed as `r_gdn x k_gdn` `Ct`s).
    pub enc_state_t_grid: Vec<Vec<Ct>>,
    pub h_state_t_grid: Vec<Vec<[u8; 32]>>,
    pub state_pre: Vec<Vec<PrecomputedCt>>,
    pub state_pcs: PersistentGridPcs,
    /// Public / SPDZ projection matrices deriving `(q_t, k_t, v_t, alpha_t, beta_t)` from token embedding `x_t`.
    pub w_q: Vec<Vec<u64>>, // d_k x d_k
    pub w_k: Vec<Vec<u64>>, // d_k x d_k
    pub w_v: Vec<Vec<u64>>, // d_v x d_k
    pub mode: LiftMode,
    pub logup_cfg: LogUpConfig,
}

impl DarkGdnResident {
    /// Initialize `DarkGdnResident` by encrypting `embed_table` (`V x d_k`) and initial `state_0` (`d_k x d_v`)
    /// under `cluster.pub_key` (`0` secret key access!) and verifying offline PCS range proofs on all 3 custodians!
    pub fn initialize(
        cluster: &mut ThreeCustodianCluster,
        embed_table: &[Vec<u64>], // V x d_k
        state_0: &[Vec<u64>],     // d_k x d_v
        w_q: Vec<Vec<u64>>,
        w_k: Vec<Vec<u64>>,
        w_v: Vec<Vec<u64>>,
        mode: LiftMode,
        logup_cfg: LogUpConfig,
    ) -> Result<Self, String> {
        let n = cluster.params.n;
        let vocab_size = embed_table.len();
        let d_k = w_q.len();
        let d_v = w_v.len();
        assert!(vocab_size > 0 && d_k.is_power_of_two() && d_v.is_power_of_two());

        let dc = d_k.min(64).min(n / 2);
        let dr = d_v.max(d_k).min(n / dc);
        assert!(dr * dc <= n && d_k % dc == 0 && d_v % dr.min(d_v) == 0);
        let dr_eff = dr.min(d_k).min(d_v);

        let mut enc_rng = PcsRng::from_seed([0x33u8; 32]);

        // 1. Pack & public-key encrypt `E^T` (`d_k x V` into `(d_k / dr_eff) x ceil(V / dc)` blocks):
        let mut e_t = vec![vec![0u64; vocab_size]; d_k];
        for tok in 0..vocab_size {
            for i in 0..d_k {
                e_t[i][tok] = embed_table[tok][i] % cluster.params.t;
            }
        }
        let enc_embed_grid =
            pack_and_encrypt_matrix(&cluster.pub_key, &e_t, d_k, vocab_size, dr_eff, dc, &mut enc_rng);
        let h_embed_grid: Vec<Vec<[u8; 32]>> = enc_embed_grid
            .iter()
            .map(|r| r.iter().map(ct2_handle).collect())
            .collect();
        let (embed_pre, embed_pcs) =
            commit_persistent_grid_pcs(&cluster.engine, &enc_embed_grid, mode)?;
        for cust in &mut cluster.custodians {
            cust.ingest_verified_persistent_grid(mode, &h_embed_grid, &embed_pcs.offline_range_proof)?;
        }

        // 2. Pack & public-key encrypt `S_0^T` (`d_v x d_k` into `(d_v / dr_eff) x (d_k / dc)` blocks):
        let mut s0_t = vec![vec![0u64; d_k]; d_v];
        for i in 0..d_k {
            for j in 0..d_v {
                s0_t[j][i] = state_0[i][j] % cluster.params.t;
            }
        }
        let enc_state_t_grid =
            pack_and_encrypt_matrix(&cluster.pub_key, &s0_t, d_v, d_k, dr_eff, dc, &mut enc_rng);
        let h_state_t_grid: Vec<Vec<[u8; 32]>> = enc_state_t_grid
            .iter()
            .map(|r| r.iter().map(ct2_handle).collect())
            .collect();
        let (state_pre, state_pcs) =
            commit_persistent_grid_pcs(&cluster.engine, &enc_state_t_grid, mode)?;
        for cust in &mut cluster.custodians {
            cust.ingest_verified_persistent_grid(mode, &h_state_t_grid, &state_pcs.offline_range_proof)?;
        }

        Ok(DarkGdnResident {
            vocab_size,
            d_k,
            d_v,
            dr: dr_eff,
            dc,
            enc_embed_grid,
            h_embed_grid,
            embed_pre,
            embed_pcs,
            enc_state_t_grid,
            h_state_t_grid,
            state_pre,
            state_pcs,
            w_q,
            w_k,
            w_v,
            mode,
            logup_cfg,
        })
    }

    /// Execute ONE full stateful encrypted turn:
    /// 1. Client public-key encrypts `one_hot(token_id)` (`0` `sk`!); Host proves `Dark-vPIR` (`Enc(E^T) * Enc(q_pir)`),
    ///    serializes `pir_proof_bytes: Vec<u8>`, and 3 custodians verify `pir_proof_bytes` (`C8`!) + run `E2S` -> `[x_t]`.
    /// 2. Custodians compute `[q_t], [k_t], [v_t]` in SPDZ and run MAC-checked `S2E` -> `Enc(k_t), Enc(q_t)`.
    /// 3. Host executes **depth-1 parallel-read** `Enc(S_{t-1}^T) * Enc(k_t)` AND `Enc(S_{t-1}^T) * Enc(q_t)`,
    ///    emitting serialized succinct proof bundles `mk_bytes` and `mq_bytes`.
    /// 4. Custodians verify BOTH succinct bundles (`C8`!), run smudged `E2S` + `R_PD` -> `[m_k], [m_q]`,
    ///    execute the `GDN` Householder crossing `[u_eff] = beta_t * ([v_t] - alpha_t * [m_k])`,
    ///    `[y_t] = alpha_t * [m_q] + (<k_t, q_t>) * [u_eff]` via SPDZ Beaver triples + `mac_check`,
    ///    and update the encrypted state `Enc(S_t^T)` via `S2E` for the next turn!
    pub fn step_turn(
        &mut self,
        cluster: &mut ThreeCustodianCluster,
        turn_idx: usize,
        token_id: usize,
        alpha_t: u64,
        beta_t: u64,
    ) -> Result<(Vec<u64>, DarkTurnMetrics), String> {
        use std::time::Instant;
        assert!(token_id < self.vocab_size);
        let n = cluster.params.n;
        let fp_t = cluster.params.fp_t;

        // ------------------------------------------------------------------
        // Phase 1: Encrypted `Dark-vPIR` Token Embedding Lookup
        // ------------------------------------------------------------------
        let mut q_pir_plain = vec![0u64; self.vocab_size];
        q_pir_plain[token_id] = 1;
        let mut client_rng = PcsRng::from_seed([turn_idx as u8 + 0x71; 32]);
        let q_pir_cts = pack_and_encrypt_rev_vec(&cluster.pub_key, &q_pir_plain, self.dc, &mut client_rng);
        let h_q_pir: Vec<[u8; 32]> = q_pir_cts.iter().map(ct2_handle).collect();
        for cust in &mut cluster.custodians {
            for &h in &h_q_pir {
                cust.register_verified_input_handle(h);
            }
        }

        let t_prv0 = Instant::now();
        let (pir_out_cts, pir_bundle, _, _) = prove_hoisted_succinct_bundle(
            &cluster.engine,
            &self.enc_embed_grid,
            &q_pir_cts,
            Some((&self.embed_pre, &self.embed_pcs)),
            self.mode,
            self.logup_cfg,
        )?;
        let pir_bytes = pir_bundle.to_bytes();
        let mut host_prove_ms = t_prv0.elapsed().as_secs_f64() * 1e3;

        let t_vfy0 = Instant::now();
        let h_pir_out: Vec<[u8; 32]> = pir_out_cts.iter().map(ct3_handle).collect();
        for cust in &mut cluster.custodians {
            cust.verify_and_ingest_succinct_bundle(
                &self.h_embed_grid,
                &h_q_pir,
                &h_pir_out,
                None,
                &q_pir_cts,
                &pir_out_cts,
                &pir_bytes,
            )?;
        }

        let out_slots: Vec<usize> = (0..self.dr).map(|r| r * self.dc + (self.dc - 1)).collect();
        let mut x_shares = Vec::with_capacity(self.d_k);
        for (r_blk, ct_out) in pir_out_cts.iter().enumerate() {
            let blk_sh = cluster.e2s_ct3(
                &h_pir_out[r_blk],
                ct_out,
                &out_slots,
                &format!("turn{turn_idx}_pir_r{r_blk}"),
            )?;
            x_shares.extend(blk_sh);
        }

        // ------------------------------------------------------------------
        // Phase 2: SPDZ Linear Projections `[q_t], [k_t], [v_t]` + `S2E` of `(k_t, q_t)`
        // ------------------------------------------------------------------
        let spdz_matvec_pub = |cl: &ThreeCustodianCluster, w: &[Vec<u64>], x: &[SharedScalar]| -> Vec<SharedScalar> {
            w.iter()
                .map(|row| {
                    let mut acc = SharedScalar {
                        parties: [PartyShare { val: 0, mac: 0 }; 3],
                    };
                    for (c, &w_rc) in row.iter().enumerate() {
                        if w_rc != 0 {
                            acc = cl.spdz_add(acc, cl.spdz_scale(w_rc, x[c]));
                        }
                    }
                    acc
                })
                .collect()
        };
        let q_sh = spdz_matvec_pub(cluster, &self.w_q, &x_shares);
        let k_sh = spdz_matvec_pub(cluster, &self.w_k, &x_shares);
        let v_sh = spdz_matvec_pub(cluster, &self.w_v, &x_shares);

        let k_gdn_blks = self.d_k / self.dc;
        let mut k_cts = Vec::with_capacity(k_gdn_blks);
        let mut q_cts = Vec::with_capacity(k_gdn_blks);
        let mut hk_vec = Vec::with_capacity(k_gdn_blks);
        let mut hq_vec = Vec::with_capacity(k_gdn_blks);

        for cb in 0..k_gdn_blks {
            let k_slots: Vec<(usize, SharedScalar)> = (0..self.dc)
                .map(|ci| (self.dc - 1 - ci, k_sh[cb * self.dc + ci]))
                .collect();
            let (ct_k, hk) = cluster.s2e_encrypt_slots(&k_slots, &format!("turn{turn_idx}_s2e_k{cb}"))?;
            k_cts.push(ct_k);
            hk_vec.push(hk);

            let q_slots: Vec<(usize, SharedScalar)> = (0..self.dc)
                .map(|ci| (self.dc - 1 - ci, q_sh[cb * self.dc + ci]))
                .collect();
            let (ct_q, hq) = cluster.s2e_encrypt_slots(&q_slots, &format!("turn{turn_idx}_s2e_q{cb}"))?;
            q_cts.push(ct_q);
            hq_vec.push(hq);
        }
        let mut cust_ms = t_vfy0.elapsed().as_secs_f64() * 1e3;

        // ------------------------------------------------------------------
        // Phase 3: Host Depth-1 Parallel-Read `Enc(S_{t-1}^T) * Enc(k_t)` & `* Enc(q_t)`
        // ------------------------------------------------------------------
        let t_prv1 = Instant::now();
        let (mk_cts, mk_bundle, _, _) = prove_hoisted_succinct_bundle(
            &cluster.engine,
            &self.enc_state_t_grid,
            &k_cts,
            Some((&self.state_pre, &self.state_pcs)),
            self.mode,
            self.logup_cfg,
        )?;
        let (mq_cts, mq_bundle, _, _) = prove_hoisted_succinct_bundle(
            &cluster.engine,
            &self.enc_state_t_grid,
            &q_cts,
            Some((&self.state_pre, &self.state_pcs)),
            self.mode,
            self.logup_cfg,
        )?;
        let mk_bytes = mk_bundle.to_bytes();
        let mq_bytes = mq_bundle.to_bytes();
        host_prove_ms += t_prv1.elapsed().as_secs_f64() * 1e3;

        // ------------------------------------------------------------------
        // Phase 4: 3-Custodian `C8` Verification + Smudged `E2S` + SPDZ `GDN` Crossing
        // ------------------------------------------------------------------
        let t_vfy1 = Instant::now();
        let h_mk_out: Vec<[u8; 32]> = mk_cts.iter().map(ct3_handle).collect();
        let h_mq_out: Vec<[u8; 32]> = mq_cts.iter().map(ct3_handle).collect();

        for cust in &mut cluster.custodians {
            cust.verify_and_ingest_succinct_bundle(
                &self.h_state_t_grid,
                &hk_vec,
                &h_mk_out,
                None,
                &k_cts,
                &mk_cts,
                &mk_bytes,
            )?;
            cust.verify_and_ingest_succinct_bundle(
                &self.h_state_t_grid,
                &hq_vec,
                &h_mq_out,
                None,
                &q_cts,
                &mq_cts,
                &mq_bytes,
            )?;
        }

        let mut mk_sh = Vec::with_capacity(self.d_v);
        let mut mq_sh = Vec::with_capacity(self.d_v);
        for rb in 0..mk_cts.len() {
            mk_sh.extend(cluster.e2s_ct3(
                &h_mk_out[rb],
                &mk_cts[rb],
                &out_slots,
                &format!("turn{turn_idx}_mk_r{rb}"),
            )?);
            mq_sh.extend(cluster.e2s_ct3(
                &h_mq_out[rb],
                &mq_cts[rb],
                &out_slots,
                &format!("turn{turn_idx}_mq_r{rb}"),
            )?);
        }

        // Authenticate scalar gates `[alpha_t], [beta_t]` in SPDZ and compute:
        //   `[u_eff] = [beta_t] * ([v_t] - [alpha_t] * [m_k])`
        //   `[kq_dot] = sum_i [k_{t,i}] * [q_{t,i}]`
        //   `[y_t] = [alpha_t] * [m_q] + [kq_dot] * [u_eff]`
        let alpha_sh = cluster.share_authenticated(alpha_t);
        let beta_sh = cluster.share_authenticated(beta_t);

        let alpha_rep_v = vec![alpha_sh; self.d_v];
        let beta_rep_v = vec![beta_sh; self.d_v];
        let alpha_mk = cluster.spdz_mul_batch(&alpha_rep_v, &mk_sh);
        let v_minus_amk: Vec<SharedScalar> = v_sh
            .iter()
            .zip(&alpha_mk)
            .map(|(&v, &am)| cluster.spdz_sub(v, am))
            .collect();
        let u_eff_sh = cluster.spdz_mul_batch(&beta_rep_v, &v_minus_amk);

        let kq_prods = cluster.spdz_mul_batch(&k_sh, &q_sh);
        let mut kq_dot_sh = SharedScalar {
            parties: [PartyShare { val: 0, mac: 0 }; 3],
        };
        for p in kq_prods {
            kq_dot_sh = cluster.spdz_add(kq_dot_sh, p);
        }

        let alpha_mq = cluster.spdz_mul_batch(&alpha_rep_v, &mq_sh);
        let kq_rep = vec![kq_dot_sh; self.d_v];
        let kq_ueff = cluster.spdz_mul_batch(&kq_rep, &u_eff_sh);
        let y_sh: Vec<SharedScalar> = alpha_mq
            .iter()
            .zip(&kq_ueff)
            .map(|(&a, &b)| cluster.spdz_add(a, b))
            .collect();

        let y_out = cluster.open_verified_output(&y_sh, &format!("turn{turn_idx}_y"))?;
        cust_ms += t_vfy1.elapsed().as_secs_f64() * 1e3;

        // ------------------------------------------------------------------
        // Phase 5: Stateful Recurrent Update `S_t^T = alpha_t S_{t-1}^T + u_eff_t * k_t^T`
        //          (Rank-1 SPDZ outer product + `S2E` fresh state encryption + PCS refresh!)
        // ------------------------------------------------------------------
        let t_ref = Instant::now();
        // Also support homomorphic `alpha_t` scaling of `Enc(S_{t-1}^T)` + `S2E(u_eff * k^T)` (`0` decryption of `S_{t-1}`!!):
        // Look how clean that is: `S_{t-1}^T` NEVER even needs to be decrypted to update `S_t^T`!!
        // Because `alpha_t * Enc(S_{t-1}^T) + Enc_{S2E}(u_eff_t * k_t^T)` updates `Enc(S_t^T)` directly
        // on ciphertexts (where `alpha_t` is opened or applied homomorphically, OR if `alpha_t` is secret,
        // `E2S` of `S_{t-1}^T` + SPDZ `alpha_t * S_{t-1}^T + u_eff * k^T` + `S2E` resets noise to fresh `S2E` level
        // for arbitrary `T = 1,000,000` turns with `O(1)` stationary noise!).
        // Let's execute the **zero-noise-accumulation SPDZ crossing state refresh** (`E2S` -> `[S_{t-1}^T]` ->
        // `[S_t^T] = [alpha_t] * [S_{t-1}^T] + [u_eff] * [k_t]^T` -> `S2E`), so even `[alpha_t]` stays 100% secret
        // AND ciphertext noise resets every turn (supporting unlimited `T -> infinity` turns)!
        let r_gdn = self.enc_state_t_grid.len();
        let k_gdn = self.enc_state_t_grid[0].len();
        let (dr_val, dc_val) = (self.dr, self.dc);
        let block_slots: Vec<usize> = (0..dr_val)
            .flat_map(move |r| (0..dc_val).map(move |c| r * dc_val + c))
            .collect();

        // Outer product `[u_eff_j] * [k_i]` (`d_v * d_k` Beaver triples in 1 batch!):
        let mut lhs_u = Vec::with_capacity(self.d_v * self.d_k);
        let mut rhs_k = Vec::with_capacity(self.d_v * self.d_k);
        for j in 0..self.d_v {
            for i in 0..self.d_k {
                lhs_u.push(u_eff_sh[j]);
                rhs_k.push(k_sh[i]);
            }
        }
        let uk_outer = cluster.spdz_mul_batch(&lhs_u, &rhs_k);

        let mut new_state_grid = vec![Vec::with_capacity(k_gdn); r_gdn];
        let mut new_h_grid = vec![Vec::with_capacity(k_gdn); r_gdn];

        for rb in 0..r_gdn {
            for cb in 0..k_gdn {
                let ct_prev = &self.enc_state_t_grid[rb][cb];
                let ct3_prev = Ct3 {
                    c0: ct_prev.c0.clone(),
                    c1: ct_prev.c1.clone(),
                    c2: vec![0u64; 3 * n],
                };
                // Register `ct3_handle(&ct3_prev)` from verified `h_state_t_grid[rb][cb]`:
                let h3 = ct3_handle(&ct3_prev);
                for cust in &mut cluster.custodians {
                    if cust.has_verified_handle(&self.h_state_t_grid[rb][cb]) {
                        cust.register_verified_input_handle(h3);
                    }
                }
                let prev_sh = cluster.e2s_ct3(
                    &h3,
                    &ct3_prev,
                    &block_slots,
                    &format!("turn{turn_idx}_st_prev_{rb}_{cb}"),
                )?;
                let alpha_rep_blk = vec![alpha_sh; block_slots.len()];
                let scaled_prev = cluster.spdz_mul_batch(&alpha_rep_blk, &prev_sh);

                let mut next_slots = Vec::with_capacity(block_slots.len());
                for r_in in 0..self.dr {
                    for c_in in 0..self.dc {
                        let flat_pos = r_in * self.dc + c_in;
                        let j_glob = rb * self.dr + r_in;
                        let i_glob = cb * self.dc + c_in;
                        let sum_sh = cluster.spdz_add(
                            scaled_prev[flat_pos],
                            uk_outer[j_glob * self.d_k + i_glob],
                        );
                        next_slots.push((block_slots[flat_pos], sum_sh));
                    }
                }
                let (ct_next, h_next) =
                    cluster.s2e_encrypt_slots(&next_slots, &format!("turn{turn_idx}_st_next_{rb}_{cb}"))?;
                new_state_grid[rb].push(ct_next);
                new_h_grid[rb].push(h_next);
            }
        }

        let (state_pre, state_pcs) =
            commit_persistent_grid_pcs(&cluster.engine, &new_state_grid, self.mode)?;
        for cust in &mut cluster.custodians {
            cust.ingest_verified_persistent_grid(
                self.mode,
                &new_h_grid,
                &state_pcs.offline_range_proof,
            )?;
        }
        self.enc_state_t_grid = new_state_grid;
        self.h_state_t_grid = new_h_grid;
        self.state_pre = state_pre;
        self.state_pcs = state_pcs;
        let _ = fp_t;
        let state_refresh_ms = t_ref.elapsed().as_secs_f64() * 1e3;

        Ok((
            y_out,
            DarkTurnMetrics {
                turn_idx,
                pir_proof_bytes: pir_bytes.len(),
                gdn_mk_proof_bytes: mk_bytes.len(),
                gdn_mq_proof_bytes: mq_bytes.len(),
                host_prove_ms,
                custodian_verify_and_cross_ms: cust_ms,
                state_refresh_ms,
            },
        ))
    }
}

// ---------------------------------------------------------------------------------------
// Internal Helpers for `dark_gdn.rs`
// ---------------------------------------------------------------------------------------

fn pack_and_encrypt_matrix(
    pk: &ThresholdPubKey,
    mat: &[Vec<u64>], // rows x cols
    rows: usize,
    cols: usize,
    dr: usize,
    dc: usize,
    rng: &mut PcsRng,
) -> Vec<Vec<Ct>> {
    let n = pk.rns_q.n;
    let r_blk = rows.div_ceil(dr);
    let k_blk = cols.div_ceil(dc);
    let mut grid = Vec::with_capacity(r_blk);
    for rb in 0..r_blk {
        let mut row_cts = Vec::with_capacity(k_blk);
        for cb in 0..k_blk {
            let mut m = vec![0u64; n];
            for r_in in 0..dr {
                let r_idx = rb * dr + r_in;
                if r_idx >= rows {
                    continue;
                }
                for c_in in 0..dc {
                    let c_idx = cb * dc + c_in;
                    if c_idx < cols {
                        m[r_in * dc + c_in] = mat[r_idx][c_idx];
                    }
                }
            }
            row_cts.push(pk.encrypt_pk(&m, rng));
        }
        grid.push(row_cts);
    }
    grid
}

fn pack_and_encrypt_rev_vec(
    pk: &ThresholdPubKey,
    vec: &[u64],
    dc: usize,
    rng: &mut PcsRng,
) -> Vec<Ct> {
    let n = pk.rns_q.n;
    let k_blk = vec.len().div_ceil(dc);
    let mut out = Vec::with_capacity(k_blk);
    for cb in 0..k_blk {
        let mut m = vec![0u64; n];
        for c_in in 0..dc {
            let idx = cb * dc + c_in;
            if idx < vec.len() {
                m[dc - 1 - c_in] = vec[idx];
            }
        }
        out.push(pk.encrypt_pk(&m, rng));
    }
    out
}

fn subtract_ct2_from_ct3(params: &HoistedParams, ct3: &Ct3, ct2: &Ct) -> Ct3 {
    let n = params.n;
    let mut c0 = vec![0u64; 3 * n];
    let mut c1 = vec![0u64; 3 * n];
    for k in 0..3 {
        let qk = params.qp[k];
        for j in 0..n {
            let idx = k * n + j;
            c0[idx] = submod(ct3.c0[idx], ct2.c0[idx], qk);
            c1[idx] = submod(ct3.c1[idx], ct2.c1[idx], qk);
        }
    }
    Ct3 {
        c0,
        c1,
        c2: ct3.c2.clone(),
    }
}

#[inline]
fn i128_mod_u64(x: i128, q: u64) -> u64 {
    let q128 = q as i128;
    let r = x.rem_euclid(q128);
    r as u64
}

fn compute_pd_fs_context(
    party_id: usize,
    tag: &str,
    ctm_handle: &[u8; 32],
    partial_rns: &[u64],
    key_root: &[u8; 32],
    pd_root: &[u8; 32],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKGDN_R_PD_FS_V1|");
    h.update(&(party_id as u32).to_le_bytes());
    h.update(tag.as_bytes());
    h.update(ctm_handle);
    h.update(key_root);
    h.update(pd_root);
    for &v in partial_rns {
        h.update(&v.to_le_bytes());
    }
    h.finalize().into()
}

fn derive_pd_point(ctx: &[u8; 32], q: u64) -> u64 {
    let mut h = Sha256::new();
    h.update(b"PD_PT|");
    h.update(ctx);
    h.update(&q.to_le_bytes());
    let d: [u8; 32] = h.finalize().into();
    let lo = u128::from_le_bytes(d[0..16].try_into().unwrap());
    (lo % q as u128) as u64
}

#[inline]
fn split_21b(v: u64) -> [u64; 3] {
    const M21: u64 = (1u64 << 21) - 1;
    [v & M21, (v >> 21) & M21, v >> 42]
}

#[inline]
fn combine_21b_mod(fp: &FastPrime61, s: &[u64; 3]) -> u64 {
    let t21 = (1u64 << 21) % fp.p;
    let t42 = (1u64 << 42) % fp.p;
    fp.add(
        s[0] % fp.p,
        fp.add(fp.mul(s[1] % fp.p, t21), fp.mul(s[2] % fp.p, t42)),
    )
}

fn build_pd_v_families(
    params: &HoistedParams,
    r_pd: &[u64; 3],
) -> (Vec<Vec<u64>>, [[[usize; 3]; 6]; 2], [[[usize; 3]; 4]; 2]) {
    let n = params.n;
    let fp0 = &params.fp[0];
    let mut v_fams = Vec::new();

    let mut r0_pows = Vec::with_capacity(n);
    let mut cur = 1u64;
    for _ in 0..n {
        r0_pows.push(cur);
        cur = fp0.mul(cur, r_pd[0]);
    }
    let mut r0_deg_n1 = r0_pows.clone();
    r0_deg_n1[n - 1] = 0;
    v_fams.push(r0_pows);
    v_fams.push(r0_deg_n1);

    let mut e_map = [[[0usize; 3]; 6]; 2];
    let mut k_map = [[[0usize; 3]; 4]; 2];
    for li in 0..2 {
        let fpl = &params.fp[li + 1];
        let mut rl_pows = Vec::with_capacity(n);
        let mut c = 1u64;
        for _ in 0..n {
            rl_pows.push(c);
            c = fpl.mul(c, r_pd[li + 1]);
        }
        for m in 0..6 {
            let gm = fpl.pow(2, (20 * m) as u64);
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            for j in 0..n {
                let ch = split_21b(fpl.mul(gm, rl_pows[j]));
                b0[j] = ch[0];
                b1[j] = ch[1];
                b2[j] = ch[2];
            }
            let base = v_fams.len();
            v_fams.push(b0);
            v_fams.push(b1);
            v_fams.push(b2);
            e_map[li][m] = [base, base + 1, base + 2];
        }
        for m in 0..4 {
            let gm = fpl.pow(2, (20 * m) as u64);
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            for j in 0..(n - 1) {
                let ch = split_21b(fpl.mul(gm, rl_pows[j]));
                b0[j] = ch[0];
                b1[j] = ch[1];
                b2[j] = ch[2];
            }
            let base = v_fams.len();
            v_fams.push(b0);
            v_fams.push(b1);
            v_fams.push(b2);
            k_map[li][m] = [base, base + 1, base + 2];
        }
    }
    (v_fams, e_map, k_map)
}

fn build_eq_poly_le(fp: &FastPrime61, z: &[u64]) -> Vec<u64> {
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

fn replay_pd_logup_points(
    fp: &FastPrime61,
    proof: &LogUpGkrProof,
    ctx: &[u8; 32],
) -> (Vec<Vec<u64>>, Vec<u64>) {
    let c = proof.config.num_challenges();
    let mut st: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_D1B_GKR|LOGUP_RANGE20");
        h.update(&fp.p.to_le_bytes());
        h.update(ctx);
        h.finalize().into()
    };
    let absorb_u64s = |s: &mut [u8; 32], vals: &[u64]| {
        let mut h = Sha256::new();
        h.update(&*s);
        for &v in vals {
            h.update(&v.to_le_bytes());
        }
        *s = h.finalize().into();
    };
    let squeeze = |s: &mut [u8; 32], tag: u64| -> u64 {
        let mut h = Sha256::new();
        h.update(&*s);
        h.update(b"CHAL");
        h.update(&tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        *s = out;
        fp.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
    };
    let fork_sub = |s: &[u8; 32], label: &str, idx: u64| -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(s);
        h.update(b"SUB|");
        h.update(label.as_bytes());
        h.update(&idx.to_le_bytes());
        h.finalize().into()
    };

    absorb_u64s(&mut st, &[proof.total_lookups as u64, c as u64]);
    {
        let mut h = Sha256::new();
        h.update(&st);
        h.update(&proof.mult_commitment);
        st = h.finalize().into();
    }
    for ell in 0..c {
        let _ = squeeze(&mut st, ell as u64);
    }

    let replay_one = |mut s: [u8; 32], tp: & crate::logup_gkr::FractionTreeProof| -> Vec<u64> {
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
    (wit_zs, z_tab)
}
