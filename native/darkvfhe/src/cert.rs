//! Complete Native `HoistedB61` Prover & Verifier (`Direct-20` & `Exact-Garner-15` + Witness-Bound
//! Fiat–Shamir Transcript + Fused `d`-Free Scalar Matvec over `F_p` + `D1b` LogUp-GKR).

use crate::digits::{DigitCols, DirectDigitSpec, ExactGarnerSpec, LiftMode};
use crate::logup_gkr::{
    prove_logup_gkr, verify_logup_gkr, LogUpConfig, LogUpGkrProof,
};
use crate::rns_hoist::{Ct3, HoistedEngine, PrecomputedCt};
use crate::HoistedParams;
use darkstep::bfv::Ct;
use rayon::prelude::*;
use sha2::{Digest, Sha256};

/// Pre-committed / persistent input digit lifts (`vFHEML` frozen weights, `Hoist(b, tau)` epoch weights,
/// `cW2` forward/transpose reuse, and deduplicated shared input vectors).
#[derive(Clone, Debug)]
pub struct SharedGridLifts {
    pub mode: LiftMode,
    /// `[r][c]` -> `(c0_digits, c1_digits)`
    pub lifts: Vec<Vec<(DigitCols, DigitCols)>>,
    /// Cached commitment hashes per `(r, c)` pair so persistent weights don't re-hash `4,096` blocks online!
    pub pair_hashes: Vec<Vec<[u8; 32]>>,
}

#[derive(Clone, Debug)]
pub struct SharedVecLifts {
    pub mode: LiftMode,
    /// `[c]` -> `(c0_digits, c1_digits)`
    pub lifts: Vec<(DigitCols, DigitCols)>,
    pub pair_hashes: Vec<[u8; 32]>,
}

/// Complete `HoistedB61` witness & proof bundle for an `R_blk x K_blk` encrypted block matvec.
#[derive(Clone, Debug)]
pub struct HoistedWitness {
    pub mode: LiftMode,
    pub max_y_bits: u32,
    /// Flattened `(r * K_blk + c)` -> `2` `DigitCols` (`2 * R_blk * K_blk` entries), or empty if persistent `SharedGridLifts` supplied.
    pub a_lifts: Vec<DigitCols>,
    pub b_lifts: Vec<DigitCols>,
    /// `3 * R_blk` `DigitCols` (`Ly = 14` `w = 20`-bit columns each).
    pub y_lifts: Vec<DigitCols>,
    /// `3 * R_blk` `DigitCols` (`10` for `Direct-20`, `15` for `Exact-Garner-15`).
    pub s_lifts: Vec<DigitCols>,
    /// `[r][k_comp][l]` -> degree-`< N - 1` ring quotient polynomial `K_{k,p_l}^{(r)}(X)` (`8` primes).
    pub k_res: Vec<[[Vec<u64>; 8]; 3]>,
    /// Commitment root covering all witness digit columns + `K_res` polynomials (bound into FS!).
    pub witness_root: [u8; 32],
    /// Optional native 61-bit `D1b` LogUp-GKR proof discharging all `[0, 2^20)` range lookups.
    pub logup_proof: Option<(LogUpGkrProof, Vec<u64>)>,
}

impl HoistedWitness {
    /// Committed witness bit count under packed `w = 20` vs strict `digits61` (`1 digit = 61 bits`),
    /// counting only online-lifted polynomials (excluding persistent offline `SharedGridLifts` when `a_lifts` is omitted).
    pub fn committed_bits(&self, n: usize, include_a_lifts: bool) -> (u64, u64) {
        let r_blk = self.k_res.len();
        let native_elems = (r_blk * 3 * 8 * (n - 1)) as u64;
        let a_dig_elems = if include_a_lifts {
            self.a_lifts.iter().map(|d| (d.num_cols() * n) as u64).sum::<u64>()
        } else {
            0
        };
        let b_dig_elems: u64 = self.b_lifts.iter().map(|d| (d.num_cols() * n) as u64).sum();
        let y_dig_elems: u64 = self.y_lifts.iter().map(|d| (d.num_cols() * n) as u64).sum();
        let s_dig_elems: u64 = self.s_lifts.iter().map(|d| (d.num_cols() * n) as u64).sum();
        let total_digits = a_dig_elems + b_dig_elems + y_dig_elems + s_dig_elems + (1u64 << 20);
        let packed_w20 = native_elems * 61 + total_digits * 20;
        let strict_b61 = (native_elems + total_digits) * 61;
        (packed_w20, strict_b61)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ProveOptions {
    pub mode: LiftMode,
    pub logup: Option<LogUpConfig>,
    /// If `true`, omit `a_lifts` from online witness when `shared_a` is supplied (e.g. `vFHEML` / `Dark-vPIR`).
    pub persistent_a: bool,
}

impl Default for ProveOptions {
    fn default() -> Self {
        ProveOptions {
            mode: LiftMode::ExactGarner15,
            logup: Some(LogUpConfig::BatchedC3 { chunk_log2: 18 }),
            persistent_a: false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct VerifyOptions {
    /// TEST / FALSIFIER ONLY (`Attack F-FS`): omit `witness_root` from Fiat-Shamir challenge derivation.
    pub legacy_statement_only_fs: bool,
    /// Verify `D1b` LogUp-GKR proof when present (`true` = full witness+mult check; `false` = succinct GKR only).
    pub full_logup_opening_check: bool,
    /// Also run direct integer range check on digit columns (disable in test to isolate pure `D1b` GKR rejection!).
    pub direct_digit_check: bool,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        VerifyOptions {
            legacy_statement_only_fs: false,
            full_logup_opening_check: true,
            direct_digit_check: true,
        }
    }
}

/// Fast canonical 32-byte SHA-256 handle binding ALL `Qp` limbs of a 2-component ciphertext (closes `Hole A`).
pub fn ct2_handle(ct: &Ct) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_CT2|");
    for &v in &ct.c0 {
        h.update(&v.to_le_bytes());
    }
    h.update(b"|");
    for &v in &ct.c1 {
        h.update(&v.to_le_bytes());
    }
    h.finalize().into()
}

/// Fast canonical 32-byte SHA-256 handle binding ALL `Qp` limbs of a 3-component ciphertext (closes `Hole A`).
pub fn ct3_handle(ct: &Ct3) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_CT3|");
    for comp in [&ct.c0, &ct.c1, &ct.c2] {
        for &v in comp {
            h.update(&v.to_le_bytes());
        }
        h.update(b"|");
    }
    h.finalize().into()
}

fn hash_digit_cols(dc: &DigitCols) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(&(dc.cols.len() as u32).to_le_bytes());
    for col in &dc.cols {
        for &v in col {
            h.update(&v.to_le_bytes());
        }
    }
    h.finalize().into()
}

fn hash_digit_pair(d0: &DigitCols, d1: &DigitCols) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(&hash_digit_cols(d0));
    h.update(&hash_digit_cols(d1));
    h.finalize().into()
}

/// Precompute persistent canonical digit lifts + NTT forms for an encrypted matrix `A_grid` (`Enc(W)` or `Enc(E)`).
pub fn precompute_shared_grid(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    mode: LiftMode,
) -> (Vec<Vec<PrecomputedCt>>, SharedGridLifts) {
    let pre = engine.precompute_grid(a_grid, true);
    let dspec = DirectDigitSpec::new(&engine.params, 262);
    let gspec = ExactGarnerSpec::new(&engine.params);

    let rows: Vec<(Vec<(DigitCols, DigitCols)>, Vec<[u8; 32]>)> = pre
        .par_iter()
        .map(|row| {
            let mut row_lifts = Vec::with_capacity(row.len());
            let mut row_hashes = Vec::with_capacity(row.len());
            for pct in row {
                let aux = pct.prover_aux.as_ref().unwrap();
                let (l0, l1) = match mode {
                    LiftMode::Direct20 => (
                        dspec.encode_u192(&aux.u0),
                        dspec.encode_u192(&aux.u1),
                    ),
                    LiftMode::ExactGarner15 => (
                        gspec.encode_u_exact(&aux.u0),
                        gspec.encode_u_exact(&aux.u1),
                    ),
                };
                let ph = hash_digit_pair(&l0, &l1);
                row_lifts.push((l0, l1));
                row_hashes.push(ph);
            }
            (row_lifts, row_hashes)
        })
        .collect();

    let (lifts, pair_hashes) = rows.into_iter().unzip();
    (
        pre,
        SharedGridLifts {
            mode,
            lifts,
            pair_hashes,
        },
    )
}

/// Compute witness commitment root covering all input/output digit columns and `K_res` quotients in parallel.
pub fn compute_witness_root(
    mode: LiftMode,
    a_pair_hashes: &[Vec<[u8; 32]>],
    b_lifts: &[DigitCols],
    y_lifts: &[DigitCols],
    s_lifts: &[DigitCols],
    k_res: &[[[Vec<u64>; 8]; 3]],
) -> [u8; 32] {
    let b_hashes: Vec<[u8; 32]> = b_lifts.par_iter().map(hash_digit_cols).collect();
    let y_hashes: Vec<[u8; 32]> = y_lifts.par_iter().map(hash_digit_cols).collect();
    let s_hashes: Vec<[u8; 32]> = s_lifts.par_iter().map(hash_digit_cols).collect();
    let k_hashes: Vec<[u8; 32]> = k_res
        .par_iter()
        .map(|rk| {
            let mut h = Sha256::new();
            for k_comp in 0..3 {
                for l in 0..8 {
                    for &v in &rk[k_comp][l] {
                        h.update(&v.to_le_bytes());
                    }
                }
            }
            h.finalize().into()
        })
        .collect();

    let mut root = Sha256::new();
    root.update(b"HOISTED_B61_WITNESS_V1|");
    root.update(mode.as_str().as_bytes());
    for row in a_pair_hashes {
        for ph in row {
            root.update(ph);
        }
    }
    for h in b_hashes.iter().chain(y_hashes.iter()).chain(s_hashes.iter()).chain(k_hashes.iter()) {
        root.update(h);
    }
    root.finalize().into()
}

fn statement_digest(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"HOISTED_B61_STMT_V1|");
    h.update(&(params.n as u64).to_le_bytes());
    h.update(&params.t.to_le_bytes());
    for &q in &params.all_primes {
        h.update(&q.to_le_bytes());
    }
    for row in ha_grid {
        for ha in row {
            h.update(ha);
        }
    }
    for hb in hb_vec {
        h.update(hb);
    }
    for ho in hout_vec {
        h.update(ho);
    }
    h.finalize().into()
}

/// Derive witness-bound Fiat–Shamir evaluation point `r_{FS,p} in F_p` (`legacy_fs` omits `witness_root` ONLY for `Attack F-FS`).
pub fn derive_fs_point(
    stmt_hash: &[u8; 32],
    witness_root: &[u8; 32],
    p: u64,
    legacy_fs: bool,
) -> u64 {
    let mut h = Sha256::new();
    h.update(b"HOISTED_B61_FS|");
    h.update(stmt_hash);
    if !legacy_fs {
        h.update(witness_root);
    }
    h.update(&p.to_le_bytes());
    let digest: [u8; 32] = h.finalize().into();
    let lo = u128::from_le_bytes(digest[0..16].try_into().unwrap());
    let hi = u128::from_le_bytes(digest[16..32].try_into().unwrap());
    let rem_hi = (hi % p as u128) as u64;
    // Combine full 256-bit digest mod p:
    let two128_mod_p = (((1u128 << 64) % p as u128) * ((1u128 << 64) % p as u128)) % p as u128;
    (((rem_hi as u128 * two128_mod_p) + (lo % p as u128)) % p as u128) as u64
}

/// Collect all `[0, 2^20)` lookup queries across online digit columns for `D1b` LogUp-GKR.
pub fn collect_online_lookup_entries(
    params: &HoistedParams,
    mode: LiftMode,
    max_y_bits: u32,
    a_lifts_online: &[DigitCols],
    b_lifts: &[DigitCols],
    y_lifts: &[DigitCols],
    s_lifts: &[DigitCols],
) -> Vec<u64> {
    let dspec = DirectDigitSpec::new(params, max_y_bits);
    let gspec = ExactGarnerSpec::new(params);
    let p0 = params.all_primes[0];

    let mut out = Vec::new();
    let append_q = |dc: &DigitCols, dst: &mut Vec<u64>| match mode {
        LiftMode::Direct20 => dspec.append_lookups_fp(dc, dspec.top_x_bits, p0, dst),
        LiftMode::ExactGarner15 => gspec.append_lookups_fp(dc, p0, dst),
    };
    for dc in a_lifts_online {
        append_q(dc, &mut out);
    }
    for dc in b_lifts {
        append_q(dc, &mut out);
    }
    for dc in s_lifts {
        append_q(dc, &mut out);
    }
    for dc in y_lifts {
        dspec.append_lookups_fp(dc, dspec.top_y_bits, p0, &mut out);
    }
    out
}

/// Full multithreaded `HoistedB61` Prover:
/// Supports both fresh `(a_grid, b_vec)` ciphertexts and precomputed persistent `(a_pre, shared_a)`!
pub fn prove_hoisted_matvec(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    b_vec: &[Ct],
    precomputed_a: Option<(&[Vec<PrecomputedCt>], &SharedGridLifts)>,
    opts: ProveOptions,
) -> Result<(Vec<Ct3>, HoistedWitness), String> {
    let r_blk = a_grid.len();
    let k_blk = b_vec.len();
    if r_blk == 0 || k_blk == 0 || a_grid.iter().any(|r| r.len() != k_blk) {
        return Err("invalid A_grid / B_vec dimensions".into());
    }
    let max_y_bits = engine.params.default_max_y_bits(k_blk);
    if !engine.params.check_crt_nowrap(k_blk, max_y_bits) {
        return Err("CRT Q*B no-wrap parameter bound exceeded".into());
    }

    let dspec = DirectDigitSpec::new(&engine.params, max_y_bits);
    let gspec = ExactGarnerSpec::new(&engine.params);

    let owned_a_pre;
    let owned_shared_a;
    let (a_pre_ref, shared_a_ref) = match precomputed_a {
        Some((ap, sa)) => {
            assert_eq!(sa.mode, opts.mode, "SharedGridLifts mode mismatch");
            (ap, sa)
        }
        None => {
            let (ap, sa) = precompute_shared_grid(engine, a_grid, opts.mode);
            owned_a_pre = ap;
            owned_shared_a = sa;
            (owned_a_pre.as_slice(), &owned_shared_a)
        }
    };

    let b_pre = engine.precompute_vec(b_vec, true);
    let b_pairs: Vec<(DigitCols, DigitCols)> = b_pre
        .par_iter()
        .map(|pct| {
            let aux = pct.prover_aux.as_ref().unwrap();
            match opts.mode {
                LiftMode::Direct20 => (dspec.encode_u192(&aux.u0), dspec.encode_u192(&aux.u1)),
                LiftMode::ExactGarner15 => (gspec.encode_u_exact(&aux.u0), gspec.encode_u_exact(&aux.u1)),
            }
        })
        .collect();
    let mut b_lifts = Vec::with_capacity(2 * k_blk);
    for (l0, l1) in b_pairs {
        b_lifts.push(l0);
        b_lifts.push(l1);
    }

    let raw = engine.hoisted_matvec_prove_raw(a_pre_ref, &b_pre);

    let y_lifts: Vec<DigitCols> = raw
        .ys
        .par_iter()
        .map(|ys| dspec.encode_signed_y(ys))
        .collect();
    let s_lifts: Vec<DigitCols> = raw
        .ss
        .par_iter()
        .map(|ss| match opts.mode {
            LiftMode::Direct20 => dspec.encode_u192(ss),
            LiftMode::ExactGarner15 => gspec.encode_u_exact(ss),
        })
        .collect();

    let a_lifts = if opts.persistent_a && precomputed_a.is_some() {
        Vec::new()
    } else {
        let mut v = Vec::with_capacity(2 * r_blk * k_blk);
        for r in 0..r_blk {
            for c in 0..k_blk {
                v.push(shared_a_ref.lifts[r][c].0.clone());
                v.push(shared_a_ref.lifts[r][c].1.clone());
            }
        }
        v
    };

    let witness_root = compute_witness_root(
        opts.mode,
        &shared_a_ref.pair_hashes,
        &b_lifts,
        &y_lifts,
        &s_lifts,
        &raw.k_res,
    );

    let logup_proof = if let Some(lu_cfg) = opts.logup {
        let entries = collect_online_lookup_entries(
            &engine.params,
            opts.mode,
            max_y_bits,
            &a_lifts,
            &b_lifts,
            &y_lifts,
            &s_lifts,
        );
        Some(prove_logup_gkr(&engine.params.fp[0], &entries, lu_cfg, &witness_root)?)
    } else {
        None
    };

    Ok((
        raw.out_cts,
        HoistedWitness {
            mode: opts.mode,
            max_y_bits,
            a_lifts,
            b_lifts,
            y_lifts,
            s_lifts,
            k_res: raw.k_res,
            witness_root,
            logup_proof,
        },
    ))
}

/// Prepacked prime-independent polynomial representation for 10x faster multi-prime `F_p` evaluation!
enum PrepackedQ {
    Direct(Vec<(u128, u128)>),
    Garner(Vec<(u128, u128, u128)>),
}

impl PrepackedQ {
    fn from_cols(mode: LiftMode, dc: &DigitCols) -> Self {
        match mode {
            LiftMode::Direct20 => PrepackedQ::Direct(DirectDigitSpec::prepack_q10(dc)),
            LiftMode::ExactGarner15 => PrepackedQ::Garner(ExactGarnerSpec::prepack_garner15(dc)),
        }
    }

    #[inline]
    fn eval_shifted_at(&self, params: &HoistedParams, l: usize, r_pows: &[u64], subtract_hq: bool, ones_p: u64) -> u64 {
        let fp = &params.fp[l];
        let raw_ev = match self {
            PrepackedQ::Direct(pairs) => {
                let p2_100 = params.pow2_100_mod_p[l];
                let mut acc = 0u64;
                for (chunk_p, chunk_r) in pairs.chunks(32).zip(r_pows.chunks(32)) {
                    let mut s = 0u128;
                    for (&(lo, hi), &rp) in chunk_p.iter().zip(chunk_r.iter()) {
                        let lo_m = fp.red128(lo);
                        let hi_m = fp.red128(hi);
                        let u_m = fp.add(lo_m, fp.mul(p2_100, hi_m));
                        s += (u_m as u128) * (rp as u128);
                    }
                    acc = fp.add(acc, fp.red128(s));
                }
                acc
            }
            PrepackedQ::Garner(triples) => {
                let q0_m = params.qp[0] % fp.p;
                let q01_m = fp.mul(q0_m, params.qp[1] % fp.p);
                let mut acc = 0u64;
                for (chunk_t, chunk_r) in triples.chunks(32).zip(r_pows.chunks(32)) {
                    let mut s = 0u128;
                    for (&(r0, r1, r2), &rp) in chunk_t.iter().zip(chunk_r.iter()) {
                        let r0_m = fp.red128(r0);
                        let r1_m = fp.red128(r1);
                        let r2_m = fp.red128(r2);
                        let u_m = fp.red128(
                            r0_m as u128
                                + (q0_m as u128) * (r1_m as u128)
                                + (q01_m as u128) * (r2_m as u128),
                        );
                        s += (u_m as u128) * (rp as u128);
                    }
                    acc = fp.add(acc, fp.red128(s));
                }
                acc
            }
        };
        if subtract_hq {
            fp.sub(raw_ev, fp.mul(params.half_q_mod_p[l], ones_p))
        } else {
            raw_ev
        }
    }
}

/// Sound explicit `HoistedB61` Verifier across `R_blk x K_blk` ciphertext blocks (`rayon`-parallel over
/// digit columns and all 8 61-bit primes).
#[allow(clippy::too_many_arguments)]
pub fn verify_hoisted_matvec(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
    opened_a: &[Vec<Ct>],
    opened_b: &[Ct],
    out_cts: &[Ct3],
    witness: &HoistedWitness,
    shared_a: Option<&SharedGridLifts>,
    opts: VerifyOptions,
) -> Result<(), String> {
    let n = params.n;
    let r_blk = ha_grid.len();
    let k_blk = hb_vec.len();
    if opened_a.len() != r_blk
        || opened_b.len() != k_blk
        || out_cts.len() != r_blk
        || hout_vec.len() != r_blk
        || ha_grid.iter().any(|r| r.len() != k_blk)
        || opened_a.iter().any(|r| r.len() != k_blk)
    {
        return Err("statement / opened ciphertext dimension mismatch".into());
    }

    // 0. Public worst-case CRT no-wrap guard (`Astra E6`):
    if !params.check_crt_nowrap(k_blk, witness.max_y_bits) {
        return Err("public parameter bound failure: Q*B insufficient to prevent CRT wraparound".into());
    }

    // 1. Handle binding across ALL limbs in parallel (closes `Hole A`, `mixed_limbs`, `stale_parent`, `wrong_quotient`):
    let out_handle_err = (0..r_blk).into_par_iter().find_map_any(|r| {
        if ct3_handle(&out_cts[r]) != hout_vec[r] {
            Some(format!("output handle mismatch at row-group {r}"))
        } else {
            None
        }
    });
    if let Some(e) = out_handle_err {
        return Err(e);
    }

    let b_handle_err = (0..k_blk).into_par_iter().find_map_any(|c| {
        if ct2_handle(&opened_b[c]) != hb_vec[c] {
            Some(format!("input B handle mismatch at ({c})"))
        } else {
            None
        }
    });
    if let Some(e) = b_handle_err {
        return Err(e);
    }

    let a_handle_err = (0..r_blk * k_blk).into_par_iter().find_map_any(|idx| {
        let r = idx / k_blk;
        let c = idx % k_blk;
        if ct2_handle(&opened_a[r][c]) != ha_grid[r][c] {
            Some(format!("input A handle mismatch at ({r}, {c})"))
        } else {
            None
        }
    });
    if let Some(e) = a_handle_err {
        return Err(e);
    }

    // 2. Lift counts, degree bounds, & canonical digit range verification:
    let using_persistent_a = witness.a_lifts.is_empty();
    if using_persistent_a && shared_a.is_none() {
        return Err("witness omitted a_lifts without SharedGridLifts".into());
    }
    if !using_persistent_a && witness.a_lifts.len() != 2 * r_blk * k_blk {
        return Err("A_lifts count mismatch".into());
    }
    if witness.b_lifts.len() != 2 * k_blk
        || witness.y_lifts.len() != 3 * r_blk
        || witness.s_lifts.len() != 3 * r_blk
        || witness.k_res.len() != r_blk
    {
        return Err("B/y/s/K lift count mismatch".into());
    }

    for r in 0..r_blk {
        for k_comp in 0..3 {
            for l in 0..8 {
                let p = params.all_primes[l];
                let kp = &witness.k_res[r][k_comp][l];
                if kp.len() != n - 1 || kp.iter().any(|&v| v >= p) {
                    return Err("invalid K_res degree or residue range".into());
                }
            }
        }
    }

    let dspec = DirectDigitSpec::new(params, witness.max_y_bits);
    let gspec = ExactGarnerSpec::new(params);

    if opts.direct_digit_check {
        let check_q = |dc: &DigitCols| -> Result<(), String> {
            if dc.n() != n {
                return Err("digit polynomial length != N".into());
            }
            match witness.mode {
                LiftMode::Direct20 => dspec.check_digits(dc, dspec.lx, dspec.top_x_bits),
                LiftMode::ExactGarner15 => gspec.check_u_exact(dc),
            }
        };

        if let Some(e) = witness
            .a_lifts
            .par_iter()
            .chain(witness.b_lifts.par_iter())
            .chain(witness.s_lifts.par_iter())
            .find_map_any(|dc| check_q(dc).err())
        {
            return Err(format!("Q/s digit range check failed: {e}"));
        }
        if let Some(e) = witness
            .y_lifts
            .par_iter()
            .find_map_any(|dc| {
                if dc.n() != n {
                    Some("y digit polynomial length != N".to_string())
                } else {
                    dspec.check_digits(dc, dspec.ly, dspec.top_y_bits).err()
                }
            })
        {
            return Err(format!("y digit range check failed: {e}"));
        }
    }

    // 3. Recompute / check witness commitment root (unless testing `Attack F-FS` legacy mode):
    let a_pair_hashes: Vec<Vec<[u8; 32]>> = if let Some(sa) = shared_a {
        if sa.mode != witness.mode {
            return Err("SharedGridLifts mode mismatch".into());
        }
        sa.pair_hashes.clone()
    } else {
        (0..r_blk)
            .into_par_iter()
            .map(|r| {
                (0..k_blk)
                    .map(|c| {
                        let base = 2 * (r * k_blk + c);
                        hash_digit_pair(&witness.a_lifts[base], &witness.a_lifts[base + 1])
                    })
                    .collect()
            })
            .collect()
    };

    if !opts.legacy_statement_only_fs {
        let expected_wroot = compute_witness_root(
            witness.mode,
            &a_pair_hashes,
            &witness.b_lifts,
            &witness.y_lifts,
            &witness.s_lifts,
            &witness.k_res,
        );
        if expected_wroot != witness.witness_root {
            return Err("witness commitment root mismatch".into());
        }
    }

    // 4. Verify `D1b` LogUp-GKR proof when present:
    if let Some((ref lu_prf, ref mults)) = witness.logup_proof {
        if opts.full_logup_opening_check {
            let entries = collect_online_lookup_entries(
                params,
                witness.mode,
                witness.max_y_bits,
                &witness.a_lifts,
                &witness.b_lifts,
                &witness.y_lifts,
                &witness.s_lifts,
            );
            verify_logup_gkr(&params.fp[0], lu_prf, &witness.witness_root, Some((&entries, mults)))?;
        } else {
            verify_logup_gkr(&params.fp[0], lu_prf, &witness.witness_root, None)?;
        }
    }

    // 5. Prepack digit columns once, then verify cross-limb openings + `R_blk x K_blk` scalar matvec
    //    + fused `d`-free polynomial rescale equation across all 8 primes in parallel!
    let pre_a: Vec<(PrepackedQ, PrepackedQ)> = (0..r_blk * k_blk)
        .into_par_iter()
        .map(|idx| {
            let r = idx / k_blk;
            let c = idx % k_blk;
            let (d0, d1) = if using_persistent_a {
                let sa = shared_a.unwrap();
                (&sa.lifts[r][c].0, &sa.lifts[r][c].1)
            } else {
                (&witness.a_lifts[2 * idx], &witness.a_lifts[2 * idx + 1])
            };
            (
                PrepackedQ::from_cols(witness.mode, d0),
                PrepackedQ::from_cols(witness.mode, d1),
            )
        })
        .collect();

    let pre_b: Vec<(PrepackedQ, PrepackedQ)> = (0..k_blk)
        .into_par_iter()
        .map(|c| {
            (
                PrepackedQ::from_cols(witness.mode, &witness.b_lifts[2 * c]),
                PrepackedQ::from_cols(witness.mode, &witness.b_lifts[2 * c + 1]),
            )
        })
        .collect();

    let pre_s: Vec<PrepackedQ> = witness
        .s_lifts
        .par_iter()
        .map(|dc| PrepackedQ::from_cols(witness.mode, dc))
        .collect();

    let pre_y: Vec<Vec<(u128, u128, u128)>> = witness
        .y_lifts
        .par_iter()
        .map(DirectDigitSpec::prepack_y14)
        .collect();

    let stmt_h = statement_digest(params, ha_grid, hb_vec, hout_vec);

    let prime_err = (0..8).into_par_iter().find_map_any(|l| {
        let fp = &params.fp[l];
        let p = fp.p;
        let r_fs = derive_fs_point(&stmt_h, &witness.witness_root, p, opts.legacy_statement_only_fs);

        // Precompute [1, r_fs, r_fs^2, ..., r_fs^{N-1}] mod p:
        let mut r_pows = Vec::with_capacity(n);
        let mut cur = 1u64;
        for _ in 0..n {
            r_pows.push(cur);
            cur = fp.mul(cur, r_fs);
        }
        // Note: after N steps, `cur == r_fs^N mod p`!
        let xn_plus_1 = fp.add(cur, 1);
        let ones_p = fp.ones_eval(n, r_fs);
        let p2_100 = params.pow2_100_mod_p[l];
        let p2_200 = fp.mul(p2_100, p2_100);
        let y_shift_mod_p = fp.pow(2, witness.max_y_bits as u64);
        let y_shift_term = fp.mul(y_shift_mod_p, ones_p);

        // Evaluate A^{(r, c)}(r_fs) mod p and verify cross-limb consistency for l < 3 (`Qp`):
        let mut m0 = vec![0u64; r_blk * k_blk];
        let mut m1 = vec![0u64; r_blk * k_blk];
        for idx in 0..r_blk * k_blk {
            let r = idx / k_blk;
            let c = idx % k_blk;
            let a0_ev = pre_a[idx].0.eval_shifted_at(params, l, &r_pows, true, ones_p);
            let a1_ev = pre_a[idx].1.eval_shifted_at(params, l, &r_pows, true, ones_p);
            if l < 3 {
                let ct = &opened_a[r][c];
                let c0_ev = fp.dot(&ct.c0[l * n..(l + 1) * n], &r_pows);
                let c1_ev = fp.dot(&ct.c1[l * n..(l + 1) * n], &r_pows);
                if a0_ev != c0_ev || a1_ev != c1_ev {
                    return Some(format!("A digit lift != ciphertext limb mod {p} at ({r}, {c})"));
                }
            }
            m0[idx] = a0_ev;
            m1[idx] = a1_ev;
        }

        let mut v0 = vec![0u64; k_blk];
        let mut v1 = vec![0u64; k_blk];
        for c in 0..k_blk {
            let b0_ev = pre_b[c].0.eval_shifted_at(params, l, &r_pows, true, ones_p);
            let b1_ev = pre_b[c].1.eval_shifted_at(params, l, &r_pows, true, ones_p);
            if l < 3 {
                let ct = &opened_b[c];
                let c0_ev = fp.dot(&ct.c0[l * n..(l + 1) * n], &r_pows);
                let c1_ev = fp.dot(&ct.c1[l * n..(l + 1) * n], &r_pows);
                if b0_ev != c0_ev || b1_ev != c1_ev {
                    return Some(format!("B digit lift != ciphertext limb mod {p} at ({c})"));
                }
            }
            v0[c] = b0_ev;
            v1[c] = b1_ev;
        }

        // Fused `d`-free polynomial rescale check via `R_blk x K_blk` scalar matvec over `F_p`:
        let q_mod_p = params.q_mod_p[l];
        let t_mod_p = params.t_mod_p[l];
        let hq_term = fp.mul(params.half_q_mod_p[l], ones_p);

        for r in 0..r_blk {
            let row0 = &m0[r * k_blk..(r + 1) * k_blk];
            let row1 = &m1[r * k_blk..(r + 1) * k_blk];
            let p0_sum = fp.dot(row0, &v0);
            let p1_sum = fp.add(fp.dot(row0, &v1), fp.dot(row1, &v0));
            let p2_sum = fp.dot(row1, &v1);

            let out_comps = [&out_cts[r].c0, &out_cts[r].c1, &out_cts[r].c2];
            for (k_comp, pk) in [p0_sum, p1_sum, p2_sum].into_iter().enumerate() {
                let idx_ys = 3 * r + k_comp;
                // Evaluate y_ev:
                let mut y_raw = 0u64;
                for (ch_y, ch_r) in pre_y[idx_ys].chunks(32).zip(r_pows.chunks(32)) {
                    let mut s = 0u128;
                    for (&(lo, mid, hi), &rp) in ch_y.iter().zip(ch_r.iter()) {
                        let lo_m = fp.red128(lo);
                        let mid_m = fp.red128(mid);
                        let hi_m = fp.red128(hi);
                        let u_m = fp.red128(
                            lo_m as u128
                                + (p2_100 as u128) * (mid_m as u128)
                                + (p2_200 as u128) * (hi_m as u128),
                        );
                        s += (u_m as u128) * (rp as u128);
                    }
                    y_raw = fp.add(y_raw, fp.red128(s));
                }
                let y_ev = fp.sub(y_raw, y_shift_term);

                if l < 3 {
                    let out_ev = fp.dot(&out_comps[k_comp][l * n..(l + 1) * n], &r_pows);
                    if y_ev != out_ev {
                        return Some(format!(
                            "output limb mismatch vs y_lift at row {r}, comp {k_comp}, prime {p}"
                        ));
                    }
                }

                let s_ev = pre_s[idx_ys].eval_shifted_at(params, l, &r_pows, false, ones_p);
                let k_ev = fp.dot(&witness.k_res[r][k_comp][l], &r_pows[..n - 1]);

                let lhs = fp.add(fp.mul(t_mod_p, pk), hq_term);
                let rhs = fp.red128(
                    (q_mod_p as u128) * (y_ev as u128)
                        + (s_ev as u128)
                        + (fp.mul(t_mod_p, xn_plus_1) as u128) * (k_ev as u128),
                );
                if lhs != rhs {
                    return Some(format!(
                        "fused hoisted rescale identity fails in F_p (row {r}, comp {k_comp}, p={p})"
                    ));
                }
            }
        }
        None
    });

    if let Some(e) = prime_err {
        return Err(e);
    }
    Ok(())
}

/// Succinct `vFHEML` / PCS-Oracle Verifier for `HoistedB61`:
/// Given pre-verified PCS evaluations `(m0_evals, m1_evals)` of persistent `Enc(W)` at `r_{FS,p}`
/// across the 8 primes, verifies:
/// 1. Online input vector `B_lifts` + output `(y_lifts, s_lifts, K_res)` evaluations at `r_{FS,p}`,
/// 2. The `R_blk x K_blk` scalar matvec + fused `d`-free polynomial rescale equation across all 8 primes,
/// 3. The succinct `D1b` LogUp-GKR fraction-tree proof (`c = 3` / `c = 4` challenges, pole guards,
///    degree-3 sumchecks, `O(log M)` prefix selector, and `O(20)` table identity MLE).
pub fn verify_hoisted_matvec_succinct_with_a_evals(
    params: &HoistedParams,
    r_blk: usize,
    k_blk: usize,
    stmt_hash: &[u8; 32],
    a_evals_per_prime: &[[Vec<u64>; 2]; 8],
    opened_b: &[Ct],
    out_cts: &[Ct3],
    witness: &HoistedWitness,
) -> Result<(), String> {
    let n = params.n;
    if !params.check_crt_nowrap(k_blk, witness.max_y_bits) {
        return Err("CRT Q*B no-wrap parameter bound failure".into());
    }
    if let Some((ref lu_prf, _)) = witness.logup_proof {
        verify_logup_gkr(&params.fp[0], lu_prf, &witness.witness_root, None)?;
    }

    let pre_b: Vec<(PrepackedQ, PrepackedQ)> = (0..k_blk)
        .into_par_iter()
        .map(|c| {
            (
                PrepackedQ::from_cols(witness.mode, &witness.b_lifts[2 * c]),
                PrepackedQ::from_cols(witness.mode, &witness.b_lifts[2 * c + 1]),
            )
        })
        .collect();
    let pre_s: Vec<PrepackedQ> = witness
        .s_lifts
        .par_iter()
        .map(|dc| PrepackedQ::from_cols(witness.mode, dc))
        .collect();
    let pre_y: Vec<Vec<(u128, u128, u128)>> = witness
        .y_lifts
        .par_iter()
        .map(DirectDigitSpec::prepack_y14)
        .collect();

    let prime_err = (0..8).into_par_iter().find_map_any(|l| {
        let fp = &params.fp[l];
        let p = fp.p;
        let r_fs = derive_fs_point(stmt_hash, &witness.witness_root, p, false);
        let mut r_pows = Vec::with_capacity(n);
        let mut cur = 1u64;
        for _ in 0..n {
            r_pows.push(cur);
            cur = fp.mul(cur, r_fs);
        }
        let xn_plus_1 = fp.add(cur, 1);
        let ones_p = fp.ones_eval(n, r_fs);
        let p2_100 = params.pow2_100_mod_p[l];
        let p2_200 = fp.mul(p2_100, p2_100);
        let y_shift_term = fp.mul(fp.pow(2, witness.max_y_bits as u64), ones_p);

        let mut v0 = vec![0u64; k_blk];
        let mut v1 = vec![0u64; k_blk];
        for c in 0..k_blk {
            let b0_ev = pre_b[c].0.eval_shifted_at(params, l, &r_pows, true, ones_p);
            let b1_ev = pre_b[c].1.eval_shifted_at(params, l, &r_pows, true, ones_p);
            if l < 3 {
                let ct = &opened_b[c];
                if b0_ev != fp.dot(&ct.c0[l * n..(l + 1) * n], &r_pows)
                    || b1_ev != fp.dot(&ct.c1[l * n..(l + 1) * n], &r_pows)
                {
                    return Some(format!("B digit lift != ciphertext limb mod {p}"));
                }
            }
            v0[c] = b0_ev;
            v1[c] = b1_ev;
        }

        let m0 = &a_evals_per_prime[l][0];
        let m1 = &a_evals_per_prime[l][1];
        let q_mod_p = params.q_mod_p[l];
        let t_mod_p = params.t_mod_p[l];
        let hq_term = fp.mul(params.half_q_mod_p[l], ones_p);

        for r in 0..r_blk {
            let row0 = &m0[r * k_blk..(r + 1) * k_blk];
            let row1 = &m1[r * k_blk..(r + 1) * k_blk];
            let p0_sum = fp.dot(row0, &v0);
            let p1_sum = fp.add(fp.dot(row0, &v1), fp.dot(row1, &v0));
            let p2_sum = fp.dot(row1, &v1);
            let out_comps = [&out_cts[r].c0, &out_cts[r].c1, &out_cts[r].c2];

            for (k_comp, pk) in [p0_sum, p1_sum, p2_sum].into_iter().enumerate() {
                let idx_ys = 3 * r + k_comp;
                let mut y_raw = 0u64;
                for (ch_y, ch_r) in pre_y[idx_ys].chunks(32).zip(r_pows.chunks(32)) {
                    let mut s = 0u128;
                    for (&(lo, mid, hi), &rp) in ch_y.iter().zip(ch_r.iter()) {
                        let lo_m = fp.red128(lo);
                        let mid_m = fp.red128(mid);
                        let hi_m = fp.red128(hi);
                        let u_m = fp.red128(
                            lo_m as u128
                                + (p2_100 as u128) * (mid_m as u128)
                                + (p2_200 as u128) * (hi_m as u128),
                        );
                        s += (u_m as u128) * (rp as u128);
                    }
                    y_raw = fp.add(y_raw, fp.red128(s));
                }
                let y_ev = fp.sub(y_raw, y_shift_term);
                if l < 3 && y_ev != fp.dot(&out_comps[k_comp][l * n..(l + 1) * n], &r_pows) {
                    return Some("output limb mismatch vs y_lift".into());
                }
                let s_ev = pre_s[idx_ys].eval_shifted_at(params, l, &r_pows, false, ones_p);
                let k_ev = fp.dot(&witness.k_res[r][k_comp][l], &r_pows[..n - 1]);
                let lhs = fp.add(fp.mul(t_mod_p, pk), hq_term);
                let rhs = fp.red128(
                    (q_mod_p as u128) * (y_ev as u128)
                        + (s_ev as u128)
                        + (fp.mul(t_mod_p, xn_plus_1) as u128) * (k_ev as u128),
                );
                if lhs != rhs {
                    return Some("succinct fused rescale check failed".into());
                }
            }
        }
        None
    });

    if let Some(e) = prime_err {
        return Err(e);
    }
    Ok(())
}

/// Helper to pre-evaluate `SharedGridLifts` at `r_{FS,p}` across all 8 primes (simulating PCS openings of `Enc(W)`).
pub fn evaluate_shared_a_at_fs(
    params: &HoistedParams,
    stmt_hash: &[u8; 32],
    witness_root: &[u8; 32],
    shared_a: &SharedGridLifts,
) -> [[Vec<u64>; 2]; 8] {
    let n = params.n;
    let r_blk = shared_a.lifts.len();
    let k_blk = shared_a.lifts[0].len();
    let pre_a: Vec<(PrepackedQ, PrepackedQ)> = (0..r_blk * k_blk)
        .into_par_iter()
        .map(|idx| {
            let r = idx / k_blk;
            let c = idx % k_blk;
            (
                PrepackedQ::from_cols(shared_a.mode, &shared_a.lifts[r][c].0),
                PrepackedQ::from_cols(shared_a.mode, &shared_a.lifts[r][c].1),
            )
        })
        .collect();

    let vecs: Vec<[Vec<u64>; 2]> = (0..8)
        .into_par_iter()
        .map(|l| {
            let fp = &params.fp[l];
            let r_fs = derive_fs_point(stmt_hash, witness_root, fp.p, false);
            let mut r_pows = Vec::with_capacity(n);
            let mut cur = 1u64;
            for _ in 0..n {
                r_pows.push(cur);
                cur = fp.mul(cur, r_fs);
            }
            let ones_p = fp.ones_eval(n, r_fs);
            let mut m0 = vec![0u64; r_blk * k_blk];
            let mut m1 = vec![0u64; r_blk * k_blk];
            for idx in 0..r_blk * k_blk {
                m0[idx] = pre_a[idx].0.eval_shifted_at(params, l, &r_pows, true, ones_p);
                m1[idx] = pre_a[idx].1.eval_shifted_at(params, l, &r_pows, true, ones_p);
            }
            [m0, m1]
        })
        .collect();
    vecs.try_into().unwrap()
}

pub fn compute_statement_digest(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
) -> [u8; 32] {
    statement_digest(params, ha_grid, hb_vec, hout_vec)
}

// ================================================================================================
// Wave-6 Closure (`[OPEN]` #1): Self-Contained 128-Bit Succinct PCS `HoistedSuccinctBundle`
// ================================================================================================

use crate::logup_gkr::{FractionTreeProof, GkrLayerProof, TABLE_LOG2, TABLE_SIZE};
use crate::succinct_pcs::{
    verify_slot_claims, ByteReader, CommittedMatrixPcs, PcsRng, PcsShape, SlotLinearClaim,
    SuccinctPcsOpeningProof, DEFAULT_BLOWUP, T_COLS_128,
};
use darkstep::arith::invmod;
use std::collections::BTreeMap;

pub const SUCCINCT_BUNDLE_MAGIC: &[u8; 8] = b"DVFHEPC1";
pub const SUCCINCT_BUNDLE_VERSION: u32 = 1;

/// Offline/persistent 128-bit Coset-NTT PCS commitment + range-proof for an encrypted matrix `A_grid`
/// (`Enc(W)` in `vFHEML`, `Enc(E)` in `Dark-vPIR`, or `Enc(S_{t-1}^T)` in `Dark-GDN`).
#[derive(Clone)]
pub struct PersistentGridPcs {
    pub mode: LiftMode,
    pub r_blk: usize,
    pub k_blk: usize,
    pub n: usize,
    pub pcs: CommittedMatrixPcs,
    /// Raw digit columns per `idx in 0..(2 * r_blk * k_blk)` (`c0, c1` interleaved) for fast prover sub-sum evals.
    pub poly_lifts: Vec<DigitCols>,
    /// Offline `D1b` LogUp-GKR range proof + PCS opening proving every entry in `pcs.root` lies in `[0, 2^20)`.
    pub offline_range_proof: OfflineGridRangeProof,
}

#[derive(Clone, Debug)]
pub struct OfflineGridRangeProof {
    pub shape_mr: u8,
    pub shape_mc: u8,
    pub t_cols: u16,
    pub blow: u8,
    pub root: [u8; 32],
    pub logup_proof: LogUpGkrProof,
    pub pcs_opening: SuccinctPcsOpeningProof,
}

/// Self-contained serialized succinct proof (`Vec<u8>`) for an `R_blk x K_blk` `HoistedB61` matvec:
/// - Commits all online digit columns (`a_lifts` if non-persistent, `b_lifts`, `y_lifts`, `s_lifts`,
///   4-limb `K_res` quotients, and the `2^20` `ProveKit v2` multiplicity vector) into **ONE**
///   128-bit ZK Coset-NTT Reed–Solomon / Ligero Matrix PCS Merkle root (`witness_pcs_root`),
/// - Derives witness-bound Fiat–Shamir challenges from `witness_pcs_root` (and `a_pcs_root` if persistent),
/// - Discharges **BOTH** the 8-prime `HoistedB61` polynomial evaluations at `r_{FS, p_0..p_7}` (via
///   exact non-wrapping 21-bit chunked sub-sums `< 2^58 < p_0`) **AND** the `D1b` LogUp-GKR terminal
///   multilinear claims `(z_w, z_tab)` against that **exact same committed PCS matrix**,
/// - Verifies standalone from `(stmt, proof_bytes)` with **zero access to the secret witness**!
#[derive(Clone, Debug)]
pub struct HoistedSuccinctBundle {
    pub mode: LiftMode,
    pub max_y_bits: u32,
    pub r_blk: usize,
    pub k_blk: usize,
    pub persistent_a: bool,
    pub shape_mr: u8,
    pub shape_mc: u8,
    pub t_cols: u16,
    pub blow: u8,
    pub witness_pcs_root: [u8; 32],
    pub a_pcs_meta: Option<(u8, u8, u16, u8, [u8; 32])>,
    /// Prime-0 (`p_0`) unshifted polynomial evaluations `[a_polys.., b_polys.., y_polys.., s_polys..]`.
    pub p0_poly_evals: Vec<u64>,
    /// Prime-0 `K_res` evaluations `[3 * r_blk]`.
    pub p0_k_evals: Vec<u64>,
    /// Primes `l = 1..7` (`7` primes): per online `(a, b, y, s)` polynomial, 3 non-wrapping 21b sub-sums `[S0, S1, S2]`.
    pub p17_poly_subsums: Vec<[u64; 3]>,
    /// Primes `l = 1..7` (`7` primes): per `(r, k_comp)` (`3 * r_blk` per prime), 3 non-wrapping 21b sub-sums `[S0, S1, S2]`.
    pub p17_k_subsums: Vec<[u64; 3]>,
    /// When `persistent_a == true`: prime-0 evals + primes `1..7` `[S0, S1, S2]` sub-sums + PCS opening against `a_pcs_root`.
    pub persistent_a_opening: Option<(Vec<u64>, Vec<[u64; 3]>, SuccinctPcsOpeningProof)>,
    /// Native 61-bit `D1b` LogUp-GKR fraction-tree proof (`c = 3` or `c = 4`).
    pub logup_proof: LogUpGkrProof,
    /// Single unified 128-bit ZK Coset-NTT Matrix PCS opening proof discharging BOTH `HoistedB61` AND `D1b` GKR!
    pub pcs_opening: SuccinctPcsOpeningProof,
}

#[derive(Clone)]
struct AffineLookupCol {
    const_offset: u64,
    terms: Vec<(usize, u64)>,
}

fn append_direct_lookup_descs(
    base_slot: usize,
    num_limbs: usize,
    top_bits: u32,
    p0: u64,
    out: &mut Vec<AffineLookupCol>,
) {
    for m in 0..num_limbs {
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(base_slot + m, 1)],
        });
    }
    if top_bits < 20 {
        let shift_off = ((1u64 << 20) - (1u64 << top_bits)) % p0;
        out.push(AffineLookupCol {
            const_offset: shift_off,
            terms: vec![(base_slot + num_limbs - 1, 1)],
        });
    }
}

fn append_garner_lookup_descs(
    gspec: &ExactGarnerSpec,
    fp0: &crate::FastPrime61,
    base_slot: usize,
    out: &mut Vec<AffineLookupCol>,
) {
    let p0 = fp0.p;
    let inv2_20 = invmod(1u64 << 20, p0);
    let neg_inv2_20 = fp0.neg(inv2_20);
    let neg_one = fp0.neg(1);
    let pos_sum = (((1u64 << 19) - 1) + ((1u64 << 18) - 1) + 15) % p0;

    for idx in 0..3 {
        let g = base_slot + 5 * idx;
        let delta = gspec.deltas[idx] % p0;
        // 1. d0
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(g, 1)],
        });
        // 2. d1 & d1 + 2^19
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(g + 1, 1)],
        });
        out.push(AffineLookupCol {
            const_offset: 1u64 << 19,
            terms: vec![(g + 1, 1)],
        });
        // 3. d2 & d2 + 3*2^18
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(g + 2, 1)],
        });
        out.push(AffineLookupCol {
            const_offset: 3 * (1u64 << 18),
            terms: vec![(g + 2, 1)],
        });
        // 4. d3 & d3 + (2^20 - 16)
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(g + 3, 1)],
        });
        out.push(AffineLookupCol {
            const_offset: (1u64 << 20) - 16,
            terms: vec![(g + 3, 1)],
        });
        // 5. v0
        out.push(AffineLookupCol {
            const_offset: 0,
            terms: vec![(g + 4, 1)],
        });
        // 6. T_i = (pos_sum - delta * inv2_20) - inv2_20 * d0 - d1 - d2 - d3 + inv2_20 * v0 (mod p0)
        let ti_const = fp0.sub(pos_sum, fp0.mul(delta, inv2_20));
        out.push(AffineLookupCol {
            const_offset: ti_const,
            terms: vec![
                (g, neg_inv2_20),
                (g + 1, neg_one),
                (g + 2, neg_one),
                (g + 3, neg_one),
                (g + 4, inv2_20),
            ],
        });
    }
}

fn materialize_lookup_entries_from_descs(
    fp0: &crate::FastPrime61,
    flat_slots: &[u64],
    n: usize,
    descs: &[AffineLookupCol],
) -> Vec<u64> {
    let mut entries = vec![0u64; descs.len() * n];
    entries
        .par_chunks_mut(n)
        .enumerate()
        .for_each(|(d_idx, dst)| {
            let desc = &descs[d_idx];
            dst.fill(desc.const_offset);
            for &(slot, coef) in &desc.terms {
                let src = &flat_slots[slot * n..(slot + 1) * n];
                if coef == 1 {
                    for j in 0..n {
                        dst[j] = fp0.add(dst[j], src[j]);
                    }
                } else {
                    for j in 0..n {
                        dst[j] = fp0.add(dst[j], fp0.mul(coef, src[j]));
                    }
                }
            }
        });
    entries
}

/// Deterministically replay `LogUpGkrProof` transcript to extract the exact terminal MLE evaluation
/// points `(z_w_per_witness_tree, z_tab)` so they can be verified directly against `SuccinctMatrixPcs`!
fn extract_logup_terminal_points(
    fp: &crate::FastPrime61,
    proof: &LogUpGkrProof,
    context_digest: &[u8; 32],
) -> Result<(Vec<Vec<u64>>, Vec<u64>), String> {
    let c = proof.config.num_challenges();
    let mut tr_state: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_D1B_GKR|LOGUP_RANGE20");
        h.update(&fp.p.to_le_bytes());
        h.update(context_digest);
        h.finalize().into()
    };
    let absorb_u64s = |st: &mut [u8; 32], vals: &[u64]| {
        let mut h = Sha256::new();
        h.update(&*st);
        for &v in vals {
            h.update(&v.to_le_bytes());
        }
        *st = h.finalize().into();
    };
    let absorb_bytes = |st: &mut [u8; 32], data: &[u8]| {
        let mut h = Sha256::new();
        h.update(&*st);
        h.update(data);
        *st = h.finalize().into();
    };
    let squeeze_fp = |st: &mut [u8; 32], tag: u64| -> u64 {
        let mut h = Sha256::new();
        h.update(&*st);
        h.update(b"CHAL");
        h.update(&tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        *st = out;
        fp.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
    };
    let fork_sub = |st: &[u8; 32], label: &str, idx: u64| -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(st);
        h.update(b"SUB|");
        h.update(label.as_bytes());
        h.update(&idx.to_le_bytes());
        h.finalize().into()
    };

    absorb_u64s(&mut tr_state, &[proof.total_lookups as u64, c as u64]);
    absorb_bytes(&mut tr_state, &proof.mult_commitment);
    for ell in 0..c {
        let _ = squeeze_fp(&mut tr_state, ell as u64);
    }

    let replay_tree = |mut st: [u8; 32], t_prf: &FractionTreeProof| -> Result<Vec<u64>, String> {
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
        let sub = fork_sub(&tr_state, "WIT_TREE", b_idx as u64);
        wit_zs.push(replay_tree(sub, w_prf)?);
    }
    let tab_sub = fork_sub(&tr_state, "TAB_TREE", 0);
    let z_tab = replay_tree(tab_sub, &proof.table_tree)?;
    Ok((wit_zs, z_tab))
}

fn build_eq_le_fp(fp: &crate::FastPrime61, z: &[u64]) -> Vec<u64> {
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

/// Limb weights `gamma_{m, l} mod p_l` for `Direct-20` (`10`), `Exact-Garner-15` (`15`), `y` (`14`), `K_res` (`4`).
fn q_limb_weights_mod_p(params: &HoistedParams, mode: LiftMode, l: usize) -> Vec<u64> {
    let fp = &params.fp[l];
    match mode {
        LiftMode::Direct20 => (0..10).map(|m| fp.pow(2, (20 * m) as u64)).collect(),
        LiftMode::ExactGarner15 => {
            let q0 = params.qp[0] % fp.p;
            let q01 = fp.mul(q0, params.qp[1] % fp.p);
            let bases = [1u64, q0, q01];
            let shifts = [0u64, 20, 39, 57];
            let mut out = Vec::with_capacity(15);
            for &b in &bases {
                for &sh in &shifts {
                    out.push(fp.mul(b, fp.pow(2, sh)));
                }
                out.push(0); // v0 carry-split helper has weight 0 in polynomial value
            }
            out
        }
    }
}

fn y_limb_weights_mod_p(params: &HoistedParams, l: usize) -> [u64; 14] {
    let fp = &params.fp[l];
    std::array::from_fn(|m| fp.pow(2, (20 * m) as u64))
}

fn k_limb_weights_mod_p(params: &HoistedParams, l: usize) -> [u64; 4] {
    let fp = &params.fp[l];
    std::array::from_fn(|m| fp.pow(2, (20 * m) as u64))
}

#[inline]
fn split_u61_chunks21(v: u64) -> [u64; 3] {
    const M21: u64 = (1u64 << 21) - 1;
    [v & M21, (v >> 21) & M21, v >> 42]
}

#[inline]
fn combine_chunks21_mod_p(fp: &crate::FastPrime61, s: &[u64; 3]) -> u64 {
    let two21 = (1u64 << 21) % fp.p;
    let two42 = (1u64 << 42) % fp.p;
    let s0 = s[0] % fp.p;
    let s1 = fp.mul(s[1] % fp.p, two21);
    let s2 = fp.mul(s[2] % fp.p, two42);
    fp.add(s0, fp.add(s1, s2))
}

/// Build `PersistentGridPcs` (`128`-bit Merkle PCS commitment + offline `D1b` LogUp-GKR range proof)
/// for an `R_blk x K_blk` encrypted matrix `A_grid`.
pub fn commit_persistent_grid_pcs(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    mode: LiftMode,
) -> Result<(Vec<Vec<PrecomputedCt>>, PersistentGridPcs), String> {
    let (a_pre, shared) = precompute_shared_grid(engine, a_grid, mode);
    let params = &engine.params;
    let fp0 = params.fp[0];
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let r_blk = a_grid.len();
    let k_blk = a_grid[0].len();
    let lq = mode.q_cols();

    let mut poly_lifts = Vec::with_capacity(2 * r_blk * k_blk);
    for r in 0..r_blk {
        for c in 0..k_blk {
            poly_lifts.push(shared.lifts[r][c].0.clone());
            poly_lifts.push(shared.lifts[r][c].1.clone());
        }
    }

    let num_poly_slots = poly_lifts.len() * lq;
    let mult_slots = TABLE_SIZE / n;
    let total_slots = num_poly_slots + mult_slots;

    let mut flat_data = vec![0u64; total_slots * n];
    for (p_idx, dc) in poly_lifts.iter().enumerate() {
        for (m, col) in dc.cols.iter().enumerate() {
            let slot = p_idx * lq + m;
            for j in 0..n {
                flat_data[slot * n + j] = col[j] as u64;
            }
        }
    }

    let dspec = DirectDigitSpec::new(params, 262);
    let gspec = ExactGarnerSpec::new(params);
    let mut descs = Vec::new();
    for p_idx in 0..poly_lifts.len() {
        let base = p_idx * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }

    let lookup_entries = materialize_lookup_entries_from_descs(&fp0, &flat_data, n, &descs);
    let mults = crate::logup_gkr::count_multiplicities_parallel(&lookup_entries)?;
    for s in 0..mult_slots {
        flat_data[(num_poly_slots + s) * n..(num_poly_slots + s + 1) * n]
            .copy_from_slice(&mults[s * n..(s + 1) * n]);
    }

    let pcs = CommittedMatrixPcs::commit(fp0, &flat_data, log_n);
    let chunk_log2 = (log_n + 5).max(18);
    let lu_cfg = LogUpConfig::BatchedC3 { chunk_log2 };
    let logup_proof =
        crate::logup_gkr::prove_logup_gkr_with_mults(&fp0, &lookup_entries, &mults, lu_cfg, &pcs.root);

    let (wit_zs, z_tab) = extract_logup_terminal_points(&fp0, &logup_proof, &pcs.root)?;
    let mut v_families = Vec::new();
    let mut claims = Vec::new();
    let cols_per_chunk = (1usize << chunk_log2) / n;

    for (b_idx, w_prf) in logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_families.len();
        v_families.push(build_eq_le_fp(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp(&fp0, &zw[log_n..]);
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

    let v_tab_idx = v_families.len();
    v_families.push(build_eq_le_fp(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (num_poly_slots + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    let pcs_opening = pcs.open_slot_claims(log_n, &v_families, &claims, &pcs.root);
    let offline_range_proof = OfflineGridRangeProof {
        shape_mr: pcs.shape.mr as u8,
        shape_mc: pcs.shape.mc as u8,
        t_cols: pcs.shape.t_cols as u16,
        blow: pcs.shape.blow as u8,
        root: pcs.root,
        logup_proof,
        pcs_opening,
    };

    Ok((
        a_pre,
        PersistentGridPcs {
            mode,
            r_blk,
            k_blk,
            n,
            pcs,
            poly_lifts,
            offline_range_proof,
        },
    ))
}

/// Standalone verifier for `OfflineGridRangeProof` (`Enc(W)` / `Enc(E)` / `Enc(S)` offline range bound).
pub fn verify_persistent_grid_range_proof(
    params: &HoistedParams,
    mode: LiftMode,
    r_blk: usize,
    k_blk: usize,
    prf: &OfflineGridRangeProof,
) -> Result<(), String> {
    let fp0 = params.fp[0];
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let lq = mode.q_cols();
    let num_polys = 2 * r_blk * k_blk;
    let num_poly_slots = num_polys * lq;
    let mult_slots = TABLE_SIZE / n;

    verify_logup_gkr(&fp0, &prf.logup_proof, &prf.root, None)?;

    let shape = PcsShape::from_mr_mc(
        &fp0,
        prf.shape_mr as usize,
        prf.shape_mc as usize,
        prf.t_cols as usize,
        prf.blow as usize,
    );
    let dspec = DirectDigitSpec::new(params, 262);
    let gspec = ExactGarnerSpec::new(params);
    let mut descs = Vec::new();
    for p_idx in 0..num_polys {
        let base = p_idx * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    if prf.logup_proof.total_lookups != descs.len() * n {
        return Err("offline persistent grid total_lookups mismatch".into());
    }

    let chunk_cap = match prf.logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => prf.logup_proof.total_lookups.max(2).next_power_of_two(),
    };
    let cols_per_chunk = chunk_cap / n;

    let (wit_zs, z_tab) = extract_logup_terminal_points(&fp0, &prf.logup_proof, &prf.root)?;
    let mut v_families = Vec::new();
    let mut claims = Vec::new();

    for (b_idx, w_prf) in prf.logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_families.len();
        v_families.push(build_eq_le_fp(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp(&fp0, &zw[log_n..]);
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

    let v_tab_idx = v_families.len();
    v_families.push(build_eq_le_fp(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (num_poly_slots + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        prf.logup_proof.table_tree.leaf_payload_eval,
    ));

    verify_slot_claims(
        &fp0,
        &shape,
        &prf.root,
        log_n,
        &v_families,
        &claims,
        &prf.root,
        &prf.pcs_opening,
    )
}

fn compute_fs_witness_root(witness_pcs_root: &[u8; 32], a_pcs_root: Option<&[u8; 32]>) -> [u8; 32] {
    match a_pcs_root {
        None => *witness_pcs_root,
        Some(ar) => {
            let mut h = Sha256::new();
            h.update(b"HOISTED_PCS_BIND_V1|");
            h.update(witness_pcs_root);
            h.update(ar);
            h.finalize().into()
        }
    }
}

/// Build the canonical `v_families` table for 8-prime polynomial & `K_res` evaluations at `r_fs[0..8]`:
/// Returns `(v_families, q_vf_map, y_vf_map, k_vf_map)` so Prover and Verifier generate 100% identical indices!
fn build_hoisted_eval_v_families(
    params: &HoistedParams,
    mode: LiftMode,
    r_fs: &[u64; 8],
) -> (
    Vec<Vec<u64>>,
    [[[usize; 3]; 15]; 7],
    [[[usize; 3]; 14]; 7],
    [[[usize; 3]; 4]; 7],
) {
    let n = params.n;
    let mut v_fams = Vec::new();

    // Index 0: [1, r_fs[0], ..., r_fs[0]^{N-1}] mod p0
    // Index 1: [1, r_fs[0], ..., r_fs[0]^{N-2}, 0] mod p0 (degree < N - 1 guard for K_res!)
    let fp0 = &params.fp[0];
    let mut r0_pows = Vec::with_capacity(n);
    let mut cur = 1u64;
    for _ in 0..n {
        r0_pows.push(cur);
        cur = fp0.mul(cur, r_fs[0]);
    }
    let mut r0_deg_n1 = r0_pows.clone();
    r0_deg_n1[n - 1] = 0;
    v_fams.push(r0_pows);
    v_fams.push(r0_deg_n1);

    let lq = mode.q_cols();
    let mut q_map = [[[0usize; 3]; 15]; 7];
    let mut y_map = [[[0usize; 3]; 14]; 7];
    let mut k_map = [[[0usize; 3]; 4]; 7];

    for li in 0..7 {
        let l = li + 1;
        let fpl = &params.fp[l];
        let mut rl_pows = Vec::with_capacity(n);
        let mut c = 1u64;
        for _ in 0..n {
            rl_pows.push(c);
            c = fpl.mul(c, r_fs[l]);
        }

        let qw = q_limb_weights_mod_p(params, mode, l);
        for m in 0..lq {
            let gm = qw[m];
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            if gm != 0 {
                for j in 0..n {
                    let ch = split_u61_chunks21(fpl.mul(gm, rl_pows[j]));
                    b0[j] = ch[0];
                    b1[j] = ch[1];
                    b2[j] = ch[2];
                }
            }
            let base = v_fams.len();
            v_fams.push(b0);
            v_fams.push(b1);
            v_fams.push(b2);
            q_map[li][m] = [base, base + 1, base + 2];
        }

        let yw = y_limb_weights_mod_p(params, l);
        for m in 0..14 {
            let gm = yw[m];
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            for j in 0..n {
                let ch = split_u61_chunks21(fpl.mul(gm, rl_pows[j]));
                b0[j] = ch[0];
                b1[j] = ch[1];
                b2[j] = ch[2];
            }
            let base = v_fams.len();
            v_fams.push(b0);
            v_fams.push(b1);
            v_fams.push(b2);
            y_map[li][m] = [base, base + 1, base + 2];
        }

        let kw = k_limb_weights_mod_p(params, l);
        for m in 0..4 {
            let gm = kw[m];
            let mut b0 = vec![0u64; n];
            let mut b1 = vec![0u64; n];
            let mut b2 = vec![0u64; n];
            // Only j in 0..n-1 (`j == n - 1` forced to 0 so deg K < N - 1 is enforced unconditionally!):
            for j in 0..(n - 1) {
                let ch = split_u61_chunks21(fpl.mul(gm, rl_pows[j]));
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

    (v_fams, q_map, y_map, k_map)
}

/// Complete multithreaded 128-bit Succinct `HoistedB61 + D1b + SuccinctMatrixPcs` Prover!
/// Returns `(out_cts, bundle, commit_ms, open_ms)`.
pub fn prove_hoisted_succinct_bundle(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    b_vec: &[Ct],
    persistent_a: Option<(&[Vec<PrecomputedCt>], &PersistentGridPcs)>,
    mode: LiftMode,
    logup_cfg: LogUpConfig,
) -> Result<(Vec<Ct3>, HoistedSuccinctBundle, f64, f64), String> {
    use std::time::Instant;

    let params = &engine.params;
    let fp0 = params.fp[0];
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let r_blk = a_grid.len();
    let k_blk = b_vec.len();
    if r_blk == 0 || k_blk == 0 || a_grid.iter().any(|r| r.len() != k_blk) {
        return Err("invalid A_grid / B_vec dimensions".into());
    }
    let max_y_bits = params.default_max_y_bits(k_blk);
    if !params.check_crt_nowrap(k_blk, max_y_bits) {
        return Err("CRT Q*B no-wrap parameter bound exceeded".into());
    }

    let dspec = DirectDigitSpec::new(params, max_y_bits);
    let gspec = ExactGarnerSpec::new(params);
    let lq = mode.q_cols();

    let owned_a_pre;
    let a_pre_ref: &[Vec<PrecomputedCt>] = match persistent_a {
        Some((ap, pg)) => {
            if pg.mode != mode || pg.r_blk != r_blk || pg.k_blk != k_blk || pg.n != n {
                return Err("PersistentGridPcs metadata mismatch".into());
            }
            ap
        }
        None => {
            owned_a_pre = engine.precompute_grid(a_grid, true);
            &owned_a_pre
        }
    };

    let b_pre = engine.precompute_vec(b_vec, true);
    let raw = engine.hoisted_matvec_prove_raw(a_pre_ref, &b_pre);

    // 1. Extract canonical digit columns for online `A` (if non-persistent), `B`, `y`, `s`, and `K_res` (`4` w=20 cols):
    let a_lifts: Vec<DigitCols> = if persistent_a.is_some() {
        Vec::new()
    } else {
        let pairs: Vec<(DigitCols, DigitCols)> = (0..r_blk * k_blk)
            .into_par_iter()
            .map(|idx| {
                let r = idx / k_blk;
                let c = idx % k_blk;
                let aux = a_pre_ref[r][c].prover_aux.as_ref().unwrap();
                match mode {
                    LiftMode::Direct20 => (dspec.encode_u192(&aux.u0), dspec.encode_u192(&aux.u1)),
                    LiftMode::ExactGarner15 => (
                        gspec.encode_u_exact(&aux.u0),
                        gspec.encode_u_exact(&aux.u1),
                    ),
                }
            })
            .collect();
        let mut v = Vec::with_capacity(2 * r_blk * k_blk);
        for (d0, d1) in pairs {
            v.push(d0);
            v.push(d1);
        }
        v
    };

    let b_pairs: Vec<(DigitCols, DigitCols)> = b_pre
        .par_iter()
        .map(|pct| {
            let aux = pct.prover_aux.as_ref().unwrap();
            match mode {
                LiftMode::Direct20 => (dspec.encode_u192(&aux.u0), dspec.encode_u192(&aux.u1)),
                LiftMode::ExactGarner15 => {
                    (gspec.encode_u_exact(&aux.u0), gspec.encode_u_exact(&aux.u1))
                }
            }
        })
        .collect();
    let mut b_lifts = Vec::with_capacity(2 * k_blk);
    for (d0, d1) in b_pairs {
        b_lifts.push(d0);
        b_lifts.push(d1);
    }

    let y_lifts: Vec<DigitCols> = raw
        .ys
        .par_iter()
        .map(|ys| dspec.encode_signed_y(ys))
        .collect();
    let s_lifts: Vec<DigitCols> = raw
        .ss
        .par_iter()
        .map(|ss| match mode {
            LiftMode::Direct20 => dspec.encode_u192(ss),
            LiftMode::ExactGarner15 => gspec.encode_u_exact(ss),
        })
        .collect();

    // Pack all slots + lookup descriptors in canonical order:
    //   [a_lifts (if !persistent_a)] [b_lifts] [y_lifts] [s_lifts] [k_res (3*r_blk*8 x 4 cols)] [mults (2^20 / N)]
    let n_a = a_lifts.len();
    let n_b = b_lifts.len();
    let n_y = y_lifts.len();
    let n_s = s_lifts.len();
    let n_k = 3 * r_blk * 8;
    let mult_slots = TABLE_SIZE / n;

    let off_a = 0usize;
    let off_b = off_a + n_a * lq;
    let off_y = off_b + n_b * lq;
    let off_s = off_y + n_y * 14;
    let off_k = off_s + n_s * lq;
    let off_mult = off_k + n_k * 4;
    let total_slots = off_mult + mult_slots;

    let mut flat_data = vec![0u64; total_slots * n];
    let write_dc_list = |dst: &mut [u64], base_off: usize, cols_per: usize, list: &[DigitCols]| {
        for (i, dc) in list.iter().enumerate() {
            for (m, col) in dc.cols.iter().enumerate() {
                let slot = base_off + i * cols_per + m;
                for j in 0..n {
                    dst[slot * n + j] = col[j] as u64;
                }
            }
        }
    };
    write_dc_list(&mut flat_data, off_a, lq, &a_lifts);
    write_dc_list(&mut flat_data, off_b, lq, &b_lifts);
    write_dc_list(&mut flat_data, off_y, 14, &y_lifts);
    write_dc_list(&mut flat_data, off_s, lq, &s_lifts);

    // Encode `k_res[r][k_comp][l]` (`j in 0..n-1`) into 4 x 20-bit digits (`j == n - 1` stays 0!):
    for r in 0..r_blk {
        for k_comp in 0..3 {
            for l in 0..8 {
                let k_idx = (3 * r + k_comp) * 8 + l;
                let base_slot = off_k + k_idx * 4;
                let src = &raw.k_res[r][k_comp][l];
                for j in 0..(n - 1) {
                    let v = src[j];
                    flat_data[(base_slot + 0) * n + j] = v & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 1) * n + j] = (v >> 20) & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 2) * n + j] = (v >> 40) & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 3) * n + j] = v >> 60;
                }
            }
        }
    }

    // Build canonical lookup column descriptors & count `2^20` multiplicities:
    let mut descs = Vec::new();
    for i in 0..n_a {
        let base = off_a + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_b {
        let base = off_b + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_y {
        let base = off_y + i * 14;
        append_direct_lookup_descs(base, 14, dspec.top_y_bits, fp0.p, &mut descs);
    }
    for i in 0..n_s {
        let base = off_s + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_k {
        let base = off_k + i * 4;
        for m in 0..4 {
            descs.push(AffineLookupCol {
                const_offset: 0,
                terms: vec![(base + m, 1)],
            });
        }
    }

    let lookup_entries = materialize_lookup_entries_from_descs(&fp0, &flat_data, n, &descs);
    let mults = crate::logup_gkr::count_multiplicities_parallel(&lookup_entries)?;
    for s in 0..mult_slots {
        flat_data[(off_mult + s) * n..(off_mult + s + 1) * n]
            .copy_from_slice(&mults[s * n..(s + 1) * n]);
    }

    // 2. Commit the unified digit + K_res + multiplicity matrix ONCE into `CommittedMatrixPcs`!
    let t_commit = Instant::now();
    let witness_pcs = CommittedMatrixPcs::commit(fp0, &flat_data, log_n);
    let commit_ms = t_commit.elapsed().as_secs_f64() * 1e3;

    // 3. Derive witness-bound Fiat–Shamir points from the REAL Merkle PCS root(s), prove `D1b` LogUp-GKR,
    //    compute 8-prime sub-sums, and open EVERYTHING in ONE `SuccinctPcsOpeningProof`!
    let t_open = Instant::now();
    let ha_grid: Vec<Vec<[u8; 32]>> = a_grid
        .par_iter()
        .map(|r| r.iter().map(ct2_handle).collect())
        .collect();
    let hb_vec: Vec<[u8; 32]> = b_vec.par_iter().map(ct2_handle).collect();
    let hout_vec: Vec<[u8; 32]> = raw.out_cts.par_iter().map(ct3_handle).collect();
    let stmt_h = statement_digest(params, &ha_grid, &hb_vec, &hout_vec);

    let a_pcs_root_opt = persistent_a.map(|(_, pg)| &pg.pcs.root);
    let fs_witness_root = compute_fs_witness_root(&witness_pcs.root, a_pcs_root_opt);

    let r_fs: [u64; 8] = std::array::from_fn(|l| {
        derive_fs_point(&stmt_h, &fs_witness_root, params.all_primes[l], false)
    });

    let logup_proof = crate::logup_gkr::prove_logup_gkr_with_mults(
        &fp0,
        &lookup_entries,
        &mults,
        logup_cfg,
        &fs_witness_root,
    );

    let (mut v_fams, q_map, y_map, k_map) = build_hoisted_eval_v_families(params, mode, &r_fs);

    // Helper to compute prime-0 eval + primes 1..7 `[S0, S1, S2]` sub-sums & emit `SlotLinearClaim`s:
    let qw0 = q_limb_weights_mod_p(params, mode, 0);
    let yw0 = y_limb_weights_mod_p(params, 0);
    let kw0 = k_limb_weights_mod_p(params, 0);

    let eval_slot_dot = |slot: usize, vf_idx: usize, src_flat: &[u64]| -> u64 {
        let s = &src_flat[slot * n..(slot + 1) * n];
        let vf = &v_fams[vf_idx];
        // Note: for `li in 0..7` sub-sums, exact integer sum `< 2^58 < p0` == `fp0.dot(s, vf)`!
        fp0.dot(s, vf)
    };

    let num_abys = n_a + n_b + n_y + n_s;
    let poly_specs: Vec<(usize, bool)> = (0..n_a)
        .map(|i| (off_a + i * lq, false))
        .chain((0..n_b).map(|i| (off_b + i * lq, false)))
        .chain((0..n_y).map(|i| (off_y + i * 14, true)))
        .chain((0..n_s).map(|i| (off_s + i * lq, false)))
        .collect();

    let abys_results: Vec<(u64, [[u64; 3]; 7])> = poly_specs
        .par_iter()
        .map(|&(base_slot, is_y)| {
            let limbs = if is_y { 14 } else { lq };
            let mut ev0 = 0u64;
            for m in 0..limbs {
                let w0 = if is_y { yw0[m] } else { qw0[m] };
                if w0 != 0 {
                    let dm_ev = eval_slot_dot(base_slot + m, 0, &flat_data);
                    ev0 = fp0.add(ev0, fp0.mul(w0, dm_ev));
                }
            }
            let mut subs = [[0u64; 3]; 7];
            for li in 0..7 {
                for b in 0..3 {
                    let mut sum_int = 0u64;
                    for m in 0..limbs {
                        let vf_idx = if is_y { y_map[li][m][b] } else { q_map[li][m][b] };
                        sum_int += eval_slot_dot(base_slot + m, vf_idx, &flat_data);
                    }
                    subs[li][b] = sum_int;
                }
            }
            (ev0, subs)
        })
        .collect();

    let mut p0_poly_evals = Vec::with_capacity(num_abys);
    let mut p17_poly_subsums = Vec::with_capacity(num_abys * 7);
    let mut claims = Vec::new();

    for (idx, &(base_slot, is_y)) in poly_specs.iter().enumerate() {
        let (ev0, subs) = abys_results[idx];
        p0_poly_evals.push(ev0);
        let limbs = if is_y { 14 } else { lq };
        let terms0: Vec<(usize, u64)> = (0..limbs)
            .filter_map(|m| {
                let w0 = if is_y { yw0[m] } else { qw0[m] };
                if w0 != 0 {
                    Some((base_slot + m, w0))
                } else {
                    None
                }
            })
            .collect();
        claims.push(SlotLinearClaim::single_vec(0, terms0, ev0));

        for li in 0..7 {
            p17_poly_subsums.push(subs[li]);
        }
    }

    let mut p0_k_evals = Vec::with_capacity(3 * r_blk);
    for rk in 0..(3 * r_blk) {
        let k_idx = rk * 8; // l == 0
        let base_slot = off_k + k_idx * 4;
        let mut ev0 = 0u64;
        let mut terms0 = Vec::with_capacity(4);
        for m in 0..4 {
            let dm_ev = eval_slot_dot(base_slot + m, 1, &flat_data);
            ev0 = fp0.add(ev0, fp0.mul(kw0[m], dm_ev));
            terms0.push((base_slot + m, kw0[m]));
        }
        p0_k_evals.push(ev0);
        claims.push(SlotLinearClaim::single_vec(1, terms0, ev0));
    }

    let k17_specs: Vec<(usize, usize)> = (0..7)
        .flat_map(|li| (0..3 * r_blk).map(move |rk| (li, rk)))
        .collect();
    let p17_k_subsums: Vec<[u64; 3]> = k17_specs
        .par_iter()
        .map(|&(li, rk)| {
            let l = li + 1;
            let k_idx = rk * 8 + l;
            let base_slot = off_k + k_idx * 4;
            let mut subs = [0u64; 3];
            for b in 0..3 {
                let mut s_int = 0u64;
                for m in 0..4 {
                    s_int += eval_slot_dot(base_slot + m, k_map[li][m][b], &flat_data);
                }
                subs[b] = s_int;
            }
            subs
        })
        .collect();

    // Derive `tau_sub` binding ALL `p0_*` and `p17_*` claimed scalars BEFORE folding across polynomials:
    let tau_sub = derive_subsum_batch_challenge(
        &fp0,
        &stmt_h,
        &fs_witness_root,
        &p0_poly_evals,
        &p0_k_evals,
        &p17_poly_subsums,
        &p17_k_subsums,
    );

    append_folded_p17_claims(
        &fp0,
        lq,
        &poly_specs,
        &p17_poly_subsums,
        off_k,
        3 * r_blk,
        &p17_k_subsums,
        &q_map,
        &y_map,
        &k_map,
        tau_sub,
        &mut claims,
    );

    // Append `D1b` LogUp-GKR terminal multilinear evaluation claims `(z_w, z_tab)` onto the SAME `claims` list!
    let chunk_cap = match logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => logup_proof.total_lookups.max(2).next_power_of_two(),
    };
    let cols_per_chunk = chunk_cap / n;
    let (wit_zs, z_tab) = extract_logup_terminal_points(&fp0, &logup_proof, &fs_witness_root)?;

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

    let v_tab_idx = v_fams.len();
    v_fams.push(build_eq_le_fp(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (off_mult + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    let pcs_open_ctx = derive_pcs_open_ctx(&stmt_h, &fs_witness_root, tau_sub);
    let pcs_opening = witness_pcs.open_slot_claims(log_n, &v_fams, &claims, &pcs_open_ctx);

    // If `persistent_a == Some`, also open `pg.pcs` at `r_fs[0..8]`!
    let (a_pcs_meta, persistent_a_opening) = if let Some((_, pg)) = persistent_a {
        let num_a = pg.poly_lifts.len();
        let a_specs: Vec<(usize, bool)> = (0..num_a).map(|i| (i * lq, false)).collect();
        let a_res: Vec<(u64, [[u64; 3]; 7])> = a_specs
            .par_iter()
            .map(|&(base_slot, _)| {
                let mut ev0 = 0u64;
                for m in 0..lq {
                    let w0 = qw0[m];
                    if w0 != 0 {
                        let col = &pg.poly_lifts[base_slot / lq].cols[m];
                        let mut acc = 0u64;
                        for (j, &cv) in col.iter().enumerate() {
                            acc = fp0.add(acc, fp0.mul(cv as u64, v_fams[0][j]));
                        }
                        ev0 = fp0.add(ev0, fp0.mul(w0, acc));
                    }
                }
                let mut subs = [[0u64; 3]; 7];
                for li in 0..7 {
                    for b in 0..3 {
                        let mut sum_int = 0u64;
                        for m in 0..lq {
                            let vf = &v_fams[q_map[li][m][b]];
                            let col = &pg.poly_lifts[base_slot / lq].cols[m];
                            let mut s = 0u128;
                            for j in 0..n {
                                s += (col[j] as u128) * (vf[j] as u128);
                            }
                            sum_int += s as u64;
                        }
                        subs[li][b] = sum_int;
                    }
                }
                (ev0, subs)
            })
            .collect();

        let mut a_p0 = Vec::with_capacity(num_a);
        let mut a_p17 = Vec::with_capacity(num_a * 7);
        let mut a_claims = Vec::new();
        for (idx, &(base_slot, _)) in a_specs.iter().enumerate() {
            let (ev0, subs) = a_res[idx];
            a_p0.push(ev0);
            let terms0: Vec<(usize, u64)> = (0..lq)
                .filter_map(|m| if qw0[m] != 0 { Some((base_slot + m, qw0[m])) } else { None })
                .collect();
            a_claims.push(SlotLinearClaim::single_vec(0, terms0, ev0));
            for li in 0..7 {
                a_p17.push(subs[li]);
            }
        }
        let tau_a = derive_subsum_batch_challenge(
            &fp0,
            &stmt_h,
            &pg.pcs.root,
            &a_p0,
            &[],
            &a_p17,
            &[],
        );
        append_folded_p17_claims(
            &fp0,
            lq,
            &a_specs,
            &a_p17,
            0,
            0,
            &[],
            &q_map,
            &y_map,
            &k_map,
            tau_a,
            &mut a_claims,
        );
        let a_ctx = derive_pcs_open_ctx(&stmt_h, &fs_witness_root, tau_a);
        // Only pass the non-GKR prefix of `v_fams` (`0 .. v_tab_idx + 1 - wit_trees - 1`):
        let base_vf_len = 2 + 7 * (lq * 3 + 14 * 3 + 4 * 3);
        let a_open = pg.pcs.open_slot_claims(log_n, &v_fams[..base_vf_len], &a_claims, &a_ctx);
        (
            Some((
                pg.pcs.shape.mr as u8,
                pg.pcs.shape.mc as u8,
                pg.pcs.shape.t_cols as u16,
                pg.pcs.shape.blow as u8,
                pg.pcs.root,
            )),
            Some((a_p0, a_p17, a_open)),
        )
    } else {
        (None, None)
    };

    let open_ms = t_open.elapsed().as_secs_f64() * 1e3;

    Ok((
        raw.out_cts,
        HoistedSuccinctBundle {
            mode,
            max_y_bits,
            r_blk,
            k_blk,
            persistent_a: persistent_a.is_some(),
            shape_mr: witness_pcs.shape.mr as u8,
            shape_mc: witness_pcs.shape.mc as u8,
            t_cols: witness_pcs.shape.t_cols as u16,
            blow: witness_pcs.shape.blow as u8,
            witness_pcs_root: witness_pcs.root,
            a_pcs_meta,
            p0_poly_evals,
            p0_k_evals,
            p17_poly_subsums,
            p17_k_subsums,
            persistent_a_opening,
            logup_proof,
            pcs_opening,
        },
        commit_ms,
        open_ms,
    ))
}

#[allow(clippy::too_many_arguments)]
fn append_folded_p17_claims(
    fp0: &crate::FastPrime61,
    lq: usize,
    poly_specs: &[(usize, bool)],
    p17_poly_subsums: &[[u64; 3]],
    off_k: usize,
    num_rk: usize,
    p17_k_subsums: &[[u64; 3]],
    q_map: &[[[usize; 3]; 15]; 7],
    y_map: &[[[usize; 3]; 14]; 7],
    k_map: &[[[usize; 3]; 4]; 7],
    tau_sub: u64,
    claims: &mut Vec<SlotLinearClaim>,
) {
    // Precompute powers `1, tau_sub, tau_sub^2, ...` across all `(poly_specs.len() + num_rk)` polynomials:
    let total_p = poly_specs.len() + num_rk;
    let mut tau_pows = Vec::with_capacity(total_p);
    let mut cur = 1u64;
    for _ in 0..total_p {
        tau_pows.push(cur);
        cur = fp0.mul(cur, tau_sub);
    }

    // Group `Q`-type (`!is_y`) and `y`-type (`is_y`) slot lists by limb `m`:
    let mut q_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); lq];
    let mut y_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); 14];
    for (p_idx, &(base_slot, is_y)) in poly_specs.iter().enumerate() {
        let tw = tau_pows[p_idx];
        if !is_y {
            for m in 0..lq {
                q_limb_slots[m].push((base_slot + m, tw));
            }
        } else {
            for m in 0..14 {
                y_limb_slots[m].push((base_slot + m, tw));
            }
        }
    }

    // For each `(li, b)` (`7 * 3 = 21` pairs total!), emit ONE `SlotLinearClaim` folding ALL polynomials!
    for li in 0..7 {
        let l = li + 1;
        let mut k_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); 4];
        for rk in 0..num_rk {
            let tw = tau_pows[poly_specs.len() + rk];
            let k_idx = rk * 8 + l;
            let base_slot = off_k + k_idx * 4;
            for m in 0..4 {
                k_limb_slots[m].push((base_slot + m, tw));
            }
        }

        for b in 0..3 {
            let mut rhs = 0u64;
            for p_idx in 0..poly_specs.len() {
                let s_val = p17_poly_subsums[p_idx * 7 + li][b] % fp0.p;
                rhs = fp0.add(rhs, fp0.mul(tau_pows[p_idx], s_val));
            }
            for rk in 0..num_rk {
                let s_val = p17_k_subsums[li * num_rk + rk][b] % fp0.p;
                rhs = fp0.add(rhs, fp0.mul(tau_pows[poly_specs.len() + rk], s_val));
            }

            let mut terms = Vec::with_capacity(lq + 14 + 4);
            for m in 0..lq {
                if !q_limb_slots[m].is_empty() {
                    terms.push((q_map[li][m][b], q_limb_slots[m].clone()));
                }
            }
            for m in 0..14 {
                if !y_limb_slots[m].is_empty() {
                    terms.push((y_map[li][m][b], y_limb_slots[m].clone()));
                }
            }
            for m in 0..4 {
                if !k_limb_slots[m].is_empty() {
                    terms.push((k_map[li][m][b], k_limb_slots[m].clone()));
                }
            }
            claims.push(SlotLinearClaim { terms, rhs });
        }
    }
}

/// Standalone Zero-Witness Verifier for `HoistedSuccinctBundle`!
/// Verifies:
/// 1. Public CRT `Q * B` no-wrap guard + full-RNS ciphertext handles (`ha_grid`, `hb_vec`, `hout_vec`),
/// 2. Non-wrapping integer bounds (`<= 15 * N * 2^41 < p_0`) on all 21-bit cross-prime sub-sums,
/// 3. `D1b` LogUp-GKR rational balance, pole guards, prefix selectors, and table identity MLE,
/// 4. Unified 128-bit ZK Coset-NTT Matrix PCS opening proof discharging BOTH all 8-prime `HoistedB61`
///    evaluations AND all `D1b` LogUp-GKR terminal multilinear leaf claims `(z_w, z_tab)` against
///    `witness_pcs_root` (plus `a_pcs_root` when `persistent_a == true`),
/// 5. All 8-prime `R_blk x K_blk` scalar matvecs, `Qp` ciphertext limb consistency, and the fused
///    `d`-free BEHZ polynomial rescale identity!
#[allow(clippy::too_many_arguments)]
pub fn verify_hoisted_succinct_bundle(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
    opened_a: Option<&[Vec<Ct>]>,
    opened_b: &[Ct],
    out_cts: &[Ct3],
    bundle: &HoistedSuccinctBundle,
) -> Result<(), String> {
    let n = params.n;
    let log_n = n.trailing_zeros() as usize;
    let fp0 = params.fp[0];
    let r_blk = bundle.r_blk;
    let k_blk = bundle.k_blk;

    if ha_grid.len() != r_blk
        || hb_vec.len() != k_blk
        || hout_vec.len() != r_blk
        || opened_b.len() != k_blk
        || out_cts.len() != r_blk
        || ha_grid.iter().any(|r| r.len() != k_blk)
    {
        return Err("statement / ciphertext dimension mismatch".into());
    }
    if !bundle.persistent_a && opened_a.is_none() {
        return Err("non-persistent bundle requires opened_a ciphertexts for Qp limb check".into());
    }
    if let Some(oa) = opened_a {
        if oa.len() != r_blk || oa.iter().any(|r| r.len() != k_blk) {
            return Err("opened_a dimension mismatch".into());
        }
    }
    if (bundle.t_cols as usize) < T_COLS_128 || (bundle.blow as usize) < DEFAULT_BLOWUP {
        return Err("PCS security profile below 128-bit floor (t_cols < 312 or blow < 4)".into());
    }

    // 0. Public CRT no-wrap guard:
    if !params.check_crt_nowrap(k_blk, bundle.max_y_bits) {
        return Err("CRT Q*B no-wrap parameter bound failure".into());
    }

    // 1. Handle checks in parallel:
    if let Some(e) = (0..r_blk).into_par_iter().find_map_any(|r| {
        if ct3_handle(&out_cts[r]) != hout_vec[r] {
            Some(format!("output handle mismatch at row {r}"))
        } else {
            None
        }
    }) {
        return Err(e);
    }
    if let Some(e) = (0..k_blk).into_par_iter().find_map_any(|c| {
        if ct2_handle(&opened_b[c]) != hb_vec[c] {
            Some(format!("input B handle mismatch at col {c}"))
        } else {
            None
        }
    }) {
        return Err(e);
    }
    if let Some(oa) = opened_a {
        if let Some(e) = (0..r_blk * k_blk).into_par_iter().find_map_any(|idx| {
            let r = idx / k_blk;
            let c = idx % k_blk;
            if ct2_handle(&oa[r][c]) != ha_grid[r][c] {
                Some(format!("input A handle mismatch at ({r}, {c})"))
            } else {
                None
            }
        }) {
            return Err(e);
        }
    }

    // 2. Check array lengths & 21b sub-sum integer bounds (`<= 15 * N * 2^41 < p0`):
    let lq = bundle.mode.q_cols();
    let n_a = if bundle.persistent_a { 0 } else { 2 * r_blk * k_blk };
    let n_b = 2 * k_blk;
    let n_y = 3 * r_blk;
    let n_s = 3 * r_blk;
    let n_k = 3 * r_blk * 8;
    let num_abys = n_a + n_b + n_y + n_s;

    if bundle.p0_poly_evals.len() != num_abys
        || bundle.p17_poly_subsums.len() != num_abys * 7
        || bundle.p0_k_evals.len() != 3 * r_blk
        || bundle.p17_k_subsums.len() != 7 * 3 * r_blk
        || bundle.persistent_a != bundle.a_pcs_meta.is_some()
        || bundle.persistent_a != bundle.persistent_a_opening.is_some()
    {
        return Err("bundle evaluation array length mismatch".into());
    }

    let max_subsum = 15u64 * (n as u64) * (1u64 << 41);
    if bundle
        .p17_poly_subsums
        .iter()
        .chain(bundle.p17_k_subsums.iter())
        .any(|s| s[0] > max_subsum || s[1] > max_subsum || s[2] > max_subsum)
    {
        return Err("21-bit cross-prime sub-sum exceeds non-wrapping integer bound".into());
    }

    let stmt_h = statement_digest(params, ha_grid, hb_vec, hout_vec);
    let a_root_opt = bundle.a_pcs_meta.as_ref().map(|m| &m.4);
    let fs_witness_root = compute_fs_witness_root(&bundle.witness_pcs_root, a_root_opt);
    let r_fs: [u64; 8] = std::array::from_fn(|l| {
        derive_fs_point(&stmt_h, &fs_witness_root, params.all_primes[l], false)
    });

    // 3. Verify `D1b` LogUp-GKR rational root balance + GKR sumcheck chain:
    verify_logup_gkr(&fp0, &bundle.logup_proof, &fs_witness_root, None)?;

    // Reconstruct canonical slot offsets & lookup descriptors identically to prover:
    let off_a = 0usize;
    let off_b = off_a + n_a * lq;
    let off_y = off_b + n_b * lq;
    let off_s = off_y + n_y * 14;
    let off_k = off_s + n_s * lq;
    let off_mult = off_k + n_k * 4;
    let mult_slots = TABLE_SIZE / n;

    let dspec = DirectDigitSpec::new(params, bundle.max_y_bits);
    let gspec = ExactGarnerSpec::new(params);
    let mut descs = Vec::new();
    for i in 0..n_a {
        let base = off_a + i * lq;
        match bundle.mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_b {
        let base = off_b + i * lq;
        match bundle.mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_y {
        let base = off_y + i * 14;
        append_direct_lookup_descs(base, 14, dspec.top_y_bits, fp0.p, &mut descs);
    }
    for i in 0..n_s {
        let base = off_s + i * lq;
        match bundle.mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => append_garner_lookup_descs(&gspec, &fp0, base, &mut descs),
        }
    }
    for i in 0..n_k {
        let base = off_k + i * 4;
        for m in 0..4 {
            descs.push(AffineLookupCol {
                const_offset: 0,
                terms: vec![(base + m, 1)],
            });
        }
    }
    if bundle.logup_proof.total_lookups != descs.len() * n {
        return Err("LogUp total_lookups != expected online digit lookup count".into());
    }

    // 4. Rebuild `SlotLinearClaim`s (8-prime HoistedB61 + D1b GKR leaf claims) & verify `pcs_opening`!
    let (mut v_fams, q_map, y_map, k_map) = build_hoisted_eval_v_families(params, bundle.mode, &r_fs);
    let qw0 = q_limb_weights_mod_p(params, bundle.mode, 0);
    let yw0 = y_limb_weights_mod_p(params, 0);
    let kw0 = k_limb_weights_mod_p(params, 0);

    let poly_specs: Vec<(usize, bool)> = (0..n_a)
        .map(|i| (off_a + i * lq, false))
        .chain((0..n_b).map(|i| (off_b + i * lq, false)))
        .chain((0..n_y).map(|i| (off_y + i * 14, true)))
        .chain((0..n_s).map(|i| (off_s + i * lq, false)))
        .collect();

    let mut claims = Vec::new();
    for (idx, &(base_slot, is_y)) in poly_specs.iter().enumerate() {
        let limbs = if is_y { 14 } else { lq };
        let terms0: Vec<(usize, u64)> = (0..limbs)
            .filter_map(|m| {
                let w0 = if is_y { yw0[m] } else { qw0[m] };
                if w0 != 0 {
                    Some((base_slot + m, w0))
                } else {
                    None
                }
            })
            .collect();
        claims.push(SlotLinearClaim::single_vec(0, terms0, bundle.p0_poly_evals[idx]));
    }
    for rk in 0..(3 * r_blk) {
        let base_slot = off_k + (rk * 8) * 4;
        let terms0: Vec<(usize, u64)> = (0..4).map(|m| (base_slot + m, kw0[m])).collect();
        claims.push(SlotLinearClaim::single_vec(1, terms0, bundle.p0_k_evals[rk]));
    }

    let tau_sub = derive_subsum_batch_challenge(
        &fp0,
        &stmt_h,
        &fs_witness_root,
        &bundle.p0_poly_evals,
        &bundle.p0_k_evals,
        &bundle.p17_poly_subsums,
        &bundle.p17_k_subsums,
    );
    append_folded_p17_claims(
        &fp0,
        lq,
        &poly_specs,
        &bundle.p17_poly_subsums,
        off_k,
        3 * r_blk,
        &bundle.p17_k_subsums,
        &q_map,
        &y_map,
        &k_map,
        tau_sub,
        &mut claims,
    );

    let chunk_cap = match bundle.logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => bundle.logup_proof.total_lookups.max(2).next_power_of_two(),
    };
    let cols_per_chunk = chunk_cap / n;
    let (wit_zs, z_tab) = extract_logup_terminal_points(&fp0, &bundle.logup_proof, &fs_witness_root)?;
    let base_vf_len = v_fams.len();

    for (b_idx, w_prf) in bundle.logup_proof.witness_trees.iter().enumerate() {
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

    let v_tab_idx = v_fams.len();
    v_fams.push(build_eq_le_fp(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (off_mult + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        bundle.logup_proof.table_tree.leaf_payload_eval,
    ));

    let shape = PcsShape::from_mr_mc(
        &fp0,
        bundle.shape_mr as usize,
        bundle.shape_mc as usize,
        bundle.t_cols as usize,
        bundle.blow as usize,
    );
    let pcs_open_ctx = derive_pcs_open_ctx(&stmt_h, &fs_witness_root, tau_sub);
    verify_slot_claims(
        &fp0,
        &shape,
        &bundle.witness_pcs_root,
        log_n,
        &v_fams,
        &claims,
        &pcs_open_ctx,
        &bundle.pcs_opening,
    )?;

    // If `persistent_a`, also verify `persistent_a_opening` against `a_pcs_meta.root`!
    if let (Some((amr, amc, atc, abl, aroot)), Some((a_p0, a_p17, a_open))) =
        (&bundle.a_pcs_meta, &bundle.persistent_a_opening)
    {
        if (*atc as usize) < T_COLS_128 || (*abl as usize) < DEFAULT_BLOWUP {
            return Err("persistent A PCS security profile below 128-bit floor".into());
        }
        let num_a = 2 * r_blk * k_blk;
        if a_p0.len() != num_a || a_p17.len() != num_a * 7 {
            return Err("persistent A eval length mismatch".into());
        }
        if a_p17
            .iter()
            .any(|s| s[0] > max_subsum || s[1] > max_subsum || s[2] > max_subsum)
        {
            return Err("persistent A 21b sub-sum exceeds integer bound".into());
        }
        let a_specs: Vec<(usize, bool)> = (0..num_a).map(|i| (i * lq, false)).collect();
        let mut a_claims = Vec::new();
        for (idx, &(base_slot, _)) in a_specs.iter().enumerate() {
            let terms0: Vec<(usize, u64)> = (0..lq)
                .filter_map(|m| if qw0[m] != 0 { Some((base_slot + m, qw0[m])) } else { None })
                .collect();
            a_claims.push(SlotLinearClaim::single_vec(0, terms0, a_p0[idx]));
        }
        let tau_a =
            derive_subsum_batch_challenge(&fp0, &stmt_h, aroot, a_p0, &[], a_p17, &[]);
        append_folded_p17_claims(
            &fp0,
            lq,
            &a_specs,
            a_p17,
            0,
            0,
            &[],
            &q_map,
            &y_map,
            &k_map,
            tau_a,
            &mut a_claims,
        );
        let a_shape =
            PcsShape::from_mr_mc(&fp0, *amr as usize, *amc as usize, *atc as usize, *abl as usize);
        let a_ctx = derive_pcs_open_ctx(&stmt_h, &fs_witness_root, tau_a);
        verify_slot_claims(
            &fp0,
            &a_shape,
            aroot,
            log_n,
            &v_fams[..base_vf_len],
            &a_claims,
            &a_ctx,
            a_open,
        )?;
    }

    // 5. Verify 8-prime `R_blk x K_blk` scalar matvec, `Qp` limb openings, and fused BEHZ rescale equation!
    let prime_err = (0..8).into_par_iter().find_map_any(|l| {
        let fp = &params.fp[l];
        let p = fp.p;
        let rl = r_fs[l];
        let mut r_pows = Vec::with_capacity(n);
        let mut cur = 1u64;
        for _ in 0..n {
            r_pows.push(cur);
            cur = fp.mul(cur, rl);
        }
        let xn_plus_1 = fp.add(cur, 1);
        let ones_p = fp.ones_eval(n, rl);
        let hq_shift = fp.mul(params.half_q_mod_p[l], ones_p);
        let y_shift = fp.mul(fp.pow(2, bundle.max_y_bits as u64), ones_p);

        let get_online_raw = |poly_idx: usize| -> u64 {
            if l == 0 {
                bundle.p0_poly_evals[poly_idx]
            } else {
                combine_chunks21_mod_p(fp, &bundle.p17_poly_subsums[poly_idx * 7 + (l - 1)])
            }
        };

        let mut m0 = vec![0u64; r_blk * k_blk];
        let mut m1 = vec![0u64; r_blk * k_blk];
        for idx in 0..(r_blk * k_blk) {
            let (raw0, raw1) = if let Some((ref a_p0, ref a_p17, _)) = bundle.persistent_a_opening {
                if l == 0 {
                    (a_p0[2 * idx], a_p0[2 * idx + 1])
                } else {
                    (
                        combine_chunks21_mod_p(fp, &a_p17[(2 * idx) * 7 + (l - 1)]),
                        combine_chunks21_mod_p(fp, &a_p17[(2 * idx + 1) * 7 + (l - 1)]),
                    )
                }
            } else {
                (get_online_raw(2 * idx), get_online_raw(2 * idx + 1))
            };
            let a0_ev = fp.sub(raw0, hq_shift);
            let a1_ev = fp.sub(raw1, hq_shift);
            if l < 3 {
                if let Some(oa) = opened_a {
                    let r = idx / k_blk;
                    let c = idx % k_blk;
                    let ct = &oa[r][c];
                    if a0_ev != fp.dot(&ct.c0[l * n..(l + 1) * n], &r_pows)
                        || a1_ev != fp.dot(&ct.c1[l * n..(l + 1) * n], &r_pows)
                    {
                        return Some(format!("A PCS opening != ciphertext limb mod {p} at ({r},{c})"));
                    }
                }
            }
            m0[idx] = a0_ev;
            m1[idx] = a1_ev;
        }

        let b_base = n_a;
        let mut v0 = vec![0u64; k_blk];
        let mut v1 = vec![0u64; k_blk];
        for c in 0..k_blk {
            let b0_ev = fp.sub(get_online_raw(b_base + 2 * c), hq_shift);
            let b1_ev = fp.sub(get_online_raw(b_base + 2 * c + 1), hq_shift);
            if l < 3 {
                let ct = &opened_b[c];
                if b0_ev != fp.dot(&ct.c0[l * n..(l + 1) * n], &r_pows)
                    || b1_ev != fp.dot(&ct.c1[l * n..(l + 1) * n], &r_pows)
                {
                    return Some(format!("B PCS opening != ciphertext limb mod {p} at ({c})"));
                }
            }
            v0[c] = b0_ev;
            v1[c] = b1_ev;
        }

        let y_base = n_a + n_b;
        let s_base = y_base + n_y;
        let q_mod_p = params.q_mod_p[l];
        let t_mod_p = params.t_mod_p[l];

        for r in 0..r_blk {
            let row0 = &m0[r * k_blk..(r + 1) * k_blk];
            let row1 = &m1[r * k_blk..(r + 1) * k_blk];
            let p0_sum = fp.dot(row0, &v0);
            let p1_sum = fp.add(fp.dot(row0, &v1), fp.dot(row1, &v0));
            let p2_sum = fp.dot(row1, &v1);
            let out_comps = [&out_cts[r].c0, &out_cts[r].c1, &out_cts[r].c2];

            for (k_comp, pk) in [p0_sum, p1_sum, p2_sum].into_iter().enumerate() {
                let rk = 3 * r + k_comp;
                let y_ev = fp.sub(get_online_raw(y_base + rk), y_shift);
                if l < 3 && y_ev != fp.dot(&out_comps[k_comp][l * n..(l + 1) * n], &r_pows) {
                    return Some(format!(
                        "output limb mismatch vs PCS y_eval at row {r}, comp {k_comp}, prime {p}"
                    ));
                }
                let s_ev = get_online_raw(s_base + rk);
                let k_ev = if l == 0 {
                    bundle.p0_k_evals[rk]
                } else {
                    combine_chunks21_mod_p(fp, &bundle.p17_k_subsums[(l - 1) * (3 * r_blk) + rk])
                };

                let lhs = fp.add(fp.mul(t_mod_p, pk), hq_shift);
                let rhs = fp.red128(
                    (q_mod_p as u128) * (y_ev as u128)
                        + (s_ev as u128)
                        + (fp.mul(t_mod_p, xn_plus_1) as u128) * (k_ev as u128),
                );
                if lhs != rhs {
                    return Some(format!(
                        "succinct PCS hoisted rescale identity fails in F_p (row {r}, comp {k_comp}, p={p})"
                    ));
                }
            }
        }
        None
    });

    if let Some(e) = prime_err {
        return Err(e);
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Compact Self-Contained Binary Wire Serialization (`HoistedSuccinctBundle::{to_bytes, from_bytes}`)
// ---------------------------------------------------------------------------------------

fn write_fraction_tree(t: &FractionTreeProof, out: &mut Vec<u8>) {
    out.extend_from_slice(&(t.depth as u32).to_le_bytes());
    out.extend_from_slice(&(t.active_len as u64).to_le_bytes());
    out.extend_from_slice(&(t.roots.len() as u32).to_le_bytes());
    for r in &t.roots {
        out.extend_from_slice(&r[0].to_le_bytes());
        out.extend_from_slice(&r[1].to_le_bytes());
    }
    out.extend_from_slice(&(t.layer1_vals.len() as u32).to_le_bytes());
    for v in &t.layer1_vals {
        for &x in v {
            out.extend_from_slice(&x.to_le_bytes());
        }
    }
    out.extend_from_slice(&(t.layers.len() as u32).to_le_bytes());
    for l in &t.layers {
        out.extend_from_slice(&(l.sumcheck_rounds.len() as u32).to_le_bytes());
        for poly in &l.sumcheck_rounds {
            for &x in poly {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        out.extend_from_slice(&(l.child_evals.len() as u32).to_le_bytes());
        for ce in &l.child_evals {
            for &x in ce {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
    }
    out.extend_from_slice(&t.leaf_payload_eval.to_le_bytes());
}

fn read_fraction_tree(cur: &mut ByteReader<'_>, p0: u64) -> Result<FractionTreeProof, String> {
    let depth = cur.read_u32()? as usize;
    if depth > 32 {
        return Err("FractionTreeProof depth out of range".into());
    }
    let active_len = cur.read_u64()? as usize;
    let n_roots = cur.read_u32()? as usize;
    if n_roots > 8 {
        return Err("FractionTreeProof roots len out of range".into());
    }
    let mut roots = Vec::with_capacity(n_roots);
    for _ in 0..n_roots {
        roots.push([cur.read_fp(p0)?, cur.read_fp(p0)?]);
    }
    let n_l1 = cur.read_u32()? as usize;
    if n_l1 > 8 {
        return Err("layer1_vals len out of range".into());
    }
    let mut layer1_vals = Vec::with_capacity(n_l1);
    for _ in 0..n_l1 {
        layer1_vals.push([
            cur.read_fp(p0)?,
            cur.read_fp(p0)?,
            cur.read_fp(p0)?,
            cur.read_fp(p0)?,
        ]);
    }
    let n_layers = cur.read_u32()? as usize;
    if n_layers > 32 {
        return Err("layers len out of range".into());
    }
    let mut layers = Vec::with_capacity(n_layers);
    for _ in 0..n_layers {
        let n_sc = cur.read_u32()? as usize;
        if n_sc > 32 {
            return Err("GKR sumcheck len out of range".into());
        }
        let mut sumcheck_rounds = Vec::with_capacity(n_sc);
        for _ in 0..n_sc {
            sumcheck_rounds.push([
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
            ]);
        }
        let n_ce = cur.read_u32()? as usize;
        if n_ce > 8 {
            return Err("child_evals len out of range".into());
        }
        let mut child_evals = Vec::with_capacity(n_ce);
        for _ in 0..n_ce {
            child_evals.push([
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
                cur.read_fp(p0)?,
            ]);
        }
        layers.push(GkrLayerProof {
            sumcheck_rounds,
            child_evals,
        });
    }
    let leaf_payload_eval = cur.read_fp(p0)?;
    Ok(FractionTreeProof {
        depth,
        active_len,
        roots,
        layer1_vals,
        layers,
        leaf_payload_eval,
    })
}

fn write_logup_proof(prf: &LogUpGkrProof, out: &mut Vec<u8>) {
    match prf.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => {
            out.push(0);
            out.push(chunk_log2 as u8);
        }
        LogUpConfig::MonolithicC4 => {
            out.push(1);
            out.push(0);
        }
    }
    out.extend_from_slice(&(prf.total_lookups as u64).to_le_bytes());
    out.extend_from_slice(&prf.mult_commitment);
    out.extend_from_slice(&(prf.witness_trees.len() as u32).to_le_bytes());
    for wt in &prf.witness_trees {
        write_fraction_tree(wt, out);
    }
    write_fraction_tree(&prf.table_tree, out);
}

fn read_logup_proof(cur: &mut ByteReader<'_>, p0: u64) -> Result<LogUpGkrProof, String> {
    let cfg_tag = cur.read_u8()?;
    let cfg_arg = cur.read_u8()?;
    let config = match cfg_tag {
        0 => LogUpConfig::BatchedC3 {
            chunk_log2: cfg_arg as usize,
        },
        1 => LogUpConfig::MonolithicC4,
        _ => return Err("unknown LogUpConfig tag".into()),
    };
    let total_lookups = cur.read_u64()? as usize;
    let mult_commitment = cur.read_hash()?;
    let n_wt = cur.read_u32()? as usize;
    if n_wt == 0 || n_wt > (1 << 16) {
        return Err("witness_trees count out of range".into());
    }
    let mut witness_trees = Vec::with_capacity(n_wt);
    for _ in 0..n_wt {
        witness_trees.push(read_fraction_tree(cur, p0)?);
    }
    let table_tree = read_fraction_tree(cur, p0)?;
    Ok(LogUpGkrProof {
        config,
        total_lookups,
        mult_commitment,
        witness_trees,
        table_tree,
    })
}

impl HoistedSuccinctBundle {
    /// Serialize the entire succinct proof bundle into a standalone canonical `Vec<u8>`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(1 << 19);
        out.extend_from_slice(SUCCINCT_BUNDLE_MAGIC);
        out.extend_from_slice(&SUCCINCT_BUNDLE_VERSION.to_le_bytes());
        out.push(match self.mode {
            LiftMode::Direct20 => 0,
            LiftMode::ExactGarner15 => 1,
        });
        out.push(if self.persistent_a { 1 } else { 0 });
        out.push(self.shape_mr);
        out.push(self.shape_mc);
        out.extend_from_slice(&self.t_cols.to_le_bytes());
        out.push(self.blow);
        out.extend_from_slice(&self.max_y_bits.to_le_bytes());
        out.extend_from_slice(&(self.r_blk as u32).to_le_bytes());
        out.extend_from_slice(&(self.k_blk as u32).to_le_bytes());
        out.extend_from_slice(&self.witness_pcs_root);

        if let Some((amr, amc, atc, abl, ref aroot)) = self.a_pcs_meta {
            out.push(1);
            out.push(amr);
            out.push(amc);
            out.extend_from_slice(&atc.to_le_bytes());
            out.push(abl);
            out.extend_from_slice(aroot);
        } else {
            out.push(0);
        }

        out.extend_from_slice(&(self.p0_poly_evals.len() as u32).to_le_bytes());
        for &v in &self.p0_poly_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.p0_k_evals.len() as u32).to_le_bytes());
        for &v in &self.p0_k_evals {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.p17_poly_subsums.len() as u32).to_le_bytes());
        for s in &self.p17_poly_subsums {
            out.extend_from_slice(&s[0].to_le_bytes());
            out.extend_from_slice(&s[1].to_le_bytes());
            out.extend_from_slice(&s[2].to_le_bytes());
        }
        out.extend_from_slice(&(self.p17_k_subsums.len() as u32).to_le_bytes());
        for s in &self.p17_k_subsums {
            out.extend_from_slice(&s[0].to_le_bytes());
            out.extend_from_slice(&s[1].to_le_bytes());
            out.extend_from_slice(&s[2].to_le_bytes());
        }

        if let Some((ref a_p0, ref a_p17, ref a_open)) = self.persistent_a_opening {
            out.push(1);
            out.extend_from_slice(&(a_p0.len() as u32).to_le_bytes());
            for &v in a_p0 {
                out.extend_from_slice(&v.to_le_bytes());
            }
            out.extend_from_slice(&(a_p17.len() as u32).to_le_bytes());
            for s in a_p17 {
                out.extend_from_slice(&s[0].to_le_bytes());
                out.extend_from_slice(&s[1].to_le_bytes());
                out.extend_from_slice(&s[2].to_le_bytes());
            }
            a_open.to_bytes(&mut out);
        } else {
            out.push(0);
        }

        write_logup_proof(&self.logup_proof, &mut out);
        self.pcs_opening.to_bytes(&mut out);
        let _ = PcsRng::from_seed;
        out
    }

    /// Deserialize `HoistedSuccinctBundle` from untrusted `bytes`, rejecting non-canonical field
    /// elements, truncated buffers, or trailing garbage bytes!
    pub fn from_bytes(bytes: &[u8], params: &HoistedParams) -> Result<Self, String> {
        Self::decode_bytes(bytes, params)
    }
}

impl<'a> ByteReader<'a> {
    pub fn read_u16(&mut self) -> Result<u16, String> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
}

impl HoistedSuccinctBundle {
    pub fn decode_bytes(bytes: &[u8], params: &HoistedParams) -> Result<Self, String> {
        let p0 = params.all_primes[0];
        let mut cur = ByteReader::new(bytes);
        if cur.take(8)? != SUCCINCT_BUNDLE_MAGIC {
            return Err("bad HoistedSuccinctBundle magic".into());
        }
        if cur.read_u32()? != SUCCINCT_BUNDLE_VERSION {
            return Err("unsupported bundle version".into());
        }
        let mode = match cur.read_u8()? {
            0 => LiftMode::Direct20,
            1 => LiftMode::ExactGarner15,
            _ => return Err("invalid LiftMode byte".into()),
        };
        let persistent_a = match cur.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err("invalid persistent_a flag".into()),
        };
        let shape_mr = cur.read_u8()?;
        let shape_mc = cur.read_u8()?;
        let t_cols = cur.read_u16()?;
        let blow = cur.read_u8()?;
        let max_y_bits = cur.read_u32()?;
        let r_blk = cur.read_u32()? as usize;
        let k_blk = cur.read_u32()? as usize;
        let witness_pcs_root = cur.read_hash()?;

        let a_pcs_meta = match cur.read_u8()? {
            0 => None,
            1 => {
                let amr = cur.read_u8()?;
                let amc = cur.read_u8()?;
                let atc = cur.read_u16()?;
                let abl = cur.read_u8()?;
                let aroot = cur.read_hash()?;
                Some((amr, amc, atc, abl, aroot))
            }
            _ => return Err("invalid a_pcs_meta flag".into()),
        };

        let n_p0 = cur.read_u32()? as usize;
        if n_p0 > (1 << 20) {
            return Err("p0_poly_evals length overflow".into());
        }
        let mut p0_poly_evals = Vec::with_capacity(n_p0);
        for _ in 0..n_p0 {
            p0_poly_evals.push(cur.read_fp(p0)?);
        }
        let n_k0 = cur.read_u32()? as usize;
        if n_k0 > (1 << 16) {
            return Err("p0_k_evals length overflow".into());
        }
        let mut p0_k_evals = Vec::with_capacity(n_k0);
        for _ in 0..n_k0 {
            p0_k_evals.push(cur.read_fp(p0)?);
        }

        let n_p17 = cur.read_u32()? as usize;
        if n_p17 > (1 << 23) {
            return Err("p17_poly_subsums length overflow".into());
        }
        let mut p17_poly_subsums = Vec::with_capacity(n_p17);
        for _ in 0..n_p17 {
            p17_poly_subsums.push([cur.read_fp(p0)?, cur.read_fp(p0)?, cur.read_fp(p0)?]);
        }
        let n_k17 = cur.read_u32()? as usize;
        if n_k17 > (1 << 20) {
            return Err("p17_k_subsums length overflow".into());
        }
        let mut p17_k_subsums = Vec::with_capacity(n_k17);
        for _ in 0..n_k17 {
            p17_k_subsums.push([cur.read_fp(p0)?, cur.read_fp(p0)?, cur.read_fp(p0)?]);
        }

        let persistent_a_opening = match cur.read_u8()? {
            0 => None,
            1 => {
                let na0 = cur.read_u32()? as usize;
                if na0 > (1 << 20) {
                    return Err("a_p0 length overflow".into());
                }
                let mut a_p0 = Vec::with_capacity(na0);
                for _ in 0..na0 {
                    a_p0.push(cur.read_fp(p0)?);
                }
                let na17 = cur.read_u32()? as usize;
                if na17 > (1 << 23) {
                    return Err("a_p17 length overflow".into());
                }
                let mut a_p17 = Vec::with_capacity(na17);
                for _ in 0..na17 {
                    a_p17.push([cur.read_fp(p0)?, cur.read_fp(p0)?, cur.read_fp(p0)?]);
                }
                let a_open = SuccinctPcsOpeningProof::from_bytes(&mut cur, p0)?;
                Some((a_p0, a_p17, a_open))
            }
            _ => return Err("invalid persistent_a_opening flag".into()),
        };

        let logup_proof = read_logup_proof(&mut cur, p0)?;
        let pcs_opening = SuccinctPcsOpeningProof::from_bytes(&mut cur, p0)?;
        if !cur.is_eof() {
            return Err("trailing bytes after HoistedSuccinctBundle".into());
        }
        Ok(HoistedSuccinctBundle {
            mode,
            max_y_bits,
            r_blk,
            k_blk,
            persistent_a,
            shape_mr,
            shape_mc,
            t_cols,
            blow,
            witness_pcs_root,
            a_pcs_meta,
            p0_poly_evals,
            p0_k_evals,
            p17_poly_subsums,
            p17_k_subsums,
            persistent_a_opening,
            logup_proof,
            pcs_opening,
        })
    }
}

fn derive_subsum_batch_challenge(
    fp0: &crate::FastPrime61,
    stmt_h: &[u8; 32],
    pcs_root: &[u8; 32],
    p0_poly: &[u64],
    p0_k: &[u64],
    p17_poly: &[[u64; 3]],
    p17_k: &[[u64; 3]],
) -> u64 {
    let mut h = Sha256::new();
    h.update(b"HOISTED_P17_SUBSUM_TAU|");
    h.update(stmt_h);
    h.update(pcs_root);
    for &v in p0_poly.iter().chain(p0_k.iter()) {
        h.update(&v.to_le_bytes());
    }
    for s in p17_poly.iter().chain(p17_k.iter()) {
        h.update(&s[0].to_le_bytes());
        h.update(&s[1].to_le_bytes());
        h.update(&s[2].to_le_bytes());
    }
    let out: [u8; 32] = h.finalize().into();
    fp0.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
}

fn derive_pcs_open_ctx(stmt_h: &[u8; 32], fs_wroot: &[u8; 32], tau_sub: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"HOISTED_PCS_OPEN_CTX|");
    h.update(stmt_h);
    h.update(fs_wroot);
    h.update(&tau_sub.to_le_bytes());
    h.finalize().into()
}


