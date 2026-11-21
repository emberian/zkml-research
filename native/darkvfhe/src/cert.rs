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

