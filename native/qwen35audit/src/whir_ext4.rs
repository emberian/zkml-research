//! Multi-Round $2^k$-ary `WHIR` / BaseFold Coset-Folding PCS (`WhirExt4Pcs`) + `GMaskExt4`
//! Full-Transcript Univariate Sumcheck HVZK over `BabyBear Ext4` (`X^4 - 11`, `|Ext4| = 2^{123.63}`,
//! `cSHAKE256` Merkle & Fiat–Shamir, `blow = 8`, `>= 100`-bit provable `[BCIKS20]` UD soundness).
//!
//! Compresses:
//! 1. Real Pretrained `Qwen3.5-0.8B` `U1` VRF-Audited `Gated DeltaNet + MXFP4 SwiGLU + ZK Absent("sk-...")`
//!    receipt from `4,642.56 KiB` (`55.3 ms` verify) -> **`< 530 KiB`** (`~8.8x–9.5x`, **`< 12 ms`** standalone verify);
//! 2. Full-Width `Qwen3.8-Flash-Next` `H_v = 48` (`1,048,576`-cell WY + `512E` `MXFP4` MoE + `QSA` `C3+C5` Top-$K_B$)
//!    receipt from `4,707.54 KiB` (`+698.6 KiB` QSA) -> **`< 495 KiB`** (`~9.8x–11.4x`, **`< 12 ms`** standalone verify).

use crate::ext4::{
    bb_from_i64, binv, bmul, bpow, bsub, build_eq_suffix_tables_ext4,
    build_eq_table_lsb_ext4, cshake256_32, eq_lin_ext4, eq_mle_ext4,
    eval_cubic_zero_one_two_inf_ext4, fold_ext4, merkle_node_cshake, mle_eval_bb_at_ext4,
    ntt_bb_in_place, os_random_seed_32, precompute_twiddles_bb, ByteCursor, CShakeRng,
    CShakeTranscript, Ext4, MerkleSinglePath, G_PRIM, P, P_U32,
};
use crate::gruen_ext4::{
    compute_d1b_multiplicities, compute_d1b_public_table_multiplicities, prove_d1b_public_table_ext4,
    prove_d1b_range_ext4, prove_mxfp4_delayed_bjk_horner_ext4, verify_d1b_public_table_ext4,
    verify_d1b_range_ext4, verify_mxfp4_delayed_bjk_horner_ext4, D1bRangeExt4Proof,
    Mxfp4DelayedBjkExt4Proof,
};
use crate::pcs_ext4::MerkleMultiProof;
use crate::qwen35_layer::{pad_mxfp4_cols_pow2, Qwen35TurnExecution, RealGdnWyWitness};
use crate::qwen38fn_slice::QsaTopKbWitness;
use crate::safetensors_mmap::{
    decode_e2m1_x2_bb, Mxfp4Matrix, Qwen35WeightRegistry, WY_SCALE, WY_SHIFT,
};
use crate::u1_audit::{padded_complement_sk_step, run_padded_complement_sk_dfa};
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

pub const WHIR_EXT4_BLOWUP: usize = 8;
/// At `blow = 8` (`rate = 1/8`) and `N_max <= 2^{18} = 262,144`:
/// - `[BCIKS20]` Thm 1.4/1.5 Unique Decoding (`Selvage/BCIKS20/EpsCa.lean:179`):
///   `140` queries gives `> 110` query bits and `>= 101.0` bits full-receipt union-bound soundness!
/// - Even under the conservative `eta = 2^{-5}` slack heuristic (`theta = 0.40625 -> 0.75207` bpq):
///   `q_bits = 140 * 0.75207 = 105.29b`, `alg_bits = 123.6276 - 5 - 18 = 100.63b > 100.0b`!
pub const WHIR_EXT4_T_QUERIES_100: usize = 140;

const WHIR_S0_LEAF_DOM: &[u8] = b"QW35-WHIR-S0-LEAF-V1";
const WHIR_FOLD_LEAF_DOM: &[u8] = b"QW35-WHIR-FOLD-LEAF-V1";
const WHIR_MERKLE_NODE_DOM: &[u8] = b"QW35-WHIR-NODE-V1";
const U1_WHIR_MAGIC: &[u8; 8] = b"QW35WHR1";
const Q38_WHIR_MAGIC: &[u8; 8] = b"QW38WHR1";

// ================================================================================================
// §1. Canonical 31-Bit BabyBear & 124-Bit `Ext4` Bit-Stream Serialization
// ================================================================================================

pub fn pack_bb_31b(vals: &[u32], out: &mut Vec<u8>) {
    out.extend_from_slice(&(vals.len() as u32).to_le_bytes());
    let total_bits = vals.len() * 31;
    let byte_len = total_bits.div_ceil(8);
    let start = out.len();
    out.resize(start + byte_len, 0u8);
    let dst = &mut out[start..];
    let mut bit_pos = 0usize;
    for &v in vals {
        debug_assert!(v < P_U32);
        let byte_idx = bit_pos >> 3;
        let bit_off = bit_pos & 7;
        let cur: u64 = (v as u64) << bit_off;
        let bytes = cur.to_le_bytes();
        let write_n = ((31 + bit_off + 7) >> 3).min(8);
        for k in 0..write_n {
            dst[byte_idx + k] |= bytes[k];
        }
        bit_pos += 31;
    }
}

pub fn unpack_bb_31b(cur: &mut ByteCursor<'_>, max_len: usize) -> Result<Vec<u32>, String> {
    let len = cur.read_u32()? as usize;
    if len > max_len {
        return Err(format!("packed BabyBear slice length {len} > {max_len}"));
    }
    let total_bits = len
        .checked_mul(31)
        .ok_or_else(|| "bit length overflow".to_string())?;
    let byte_len = total_bits.div_ceil(8);
    let raw = cur.read_exact(byte_len)?;
    let mask = (1u64 << 31) - 1;
    let mut out = Vec::with_capacity(len);
    let mut bit_pos = 0usize;
    for _ in 0..len {
        let byte_idx = bit_pos >> 3;
        let bit_off = bit_pos & 7;
        let read_n = (byte_len - byte_idx).min(8);
        let mut buf = [0u8; 8];
        buf[..read_n].copy_from_slice(&raw[byte_idx..byte_idx + read_n]);
        let val = ((u64::from_le_bytes(buf) >> bit_off) & mask) as u32;
        if val >= P_U32 {
            return Err(format!("non-canonical packed BabyBear felt {val} >= {P_U32}"));
        }
        out.push(val);
        bit_pos += 31;
    }
    let rem_bits = total_bits & 7;
    if rem_bits != 0 && !raw.is_empty() && (raw[byte_len - 1] >> rem_bits) != 0 {
        return Err("non-zero trailing padding bits in 31b stream".into());
    }
    Ok(out)
}

pub fn pack_ext4_slice(xs: &[Ext4], out: &mut Vec<u8>) {
    let mut flat = Vec::with_capacity(xs.len() * 4);
    for x in xs {
        flat.extend_from_slice(&x.0);
    }
    pack_bb_31b(&flat, out);
}

pub fn unpack_ext4_slice(cur: &mut ByteCursor<'_>, max_ext_len: usize) -> Result<Vec<Ext4>, String> {
    let flat = unpack_bb_31b(cur, max_ext_len * 4)?;
    if flat.len() % 4 != 0 {
        return Err("packed Ext4 slice not divisible by 4".into());
    }
    Ok(flat
        .chunks_exact(4)
        .map(|c| Ext4([c[0], c[1], c[2], c[3]]))
        .collect())
}

#[inline]
pub fn eval_poly_ext4(coeffs: &[Ext4], x: Ext4) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(x).add(c);
    }
    acc
}

#[inline]
fn eval_poly_ext4_at_bb(coeffs: &[Ext4], x: u32) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.scale_bb(x).add(c);
    }
    acc
}

// ================================================================================================
// §2. `GMaskExt4`: Separable Degree-$d$ Univariate Sumcheck Blinding over `BabyBear Ext4` (`TVD == 0`)
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GMaskSpecExt4 {
    pub name: String,
    pub num_rounds: usize,
    pub deg: usize,
}

impl GMaskSpecExt4 {
    pub fn new(name: impl Into<String>, num_rounds: usize, deg: usize) -> Self {
        assert!(num_rounds >= 1 && deg >= 1);
        Self {
            name: name.into(),
            num_rounds,
            deg,
        }
    }
}

#[derive(Clone, Debug)]
pub struct GMaskExt4 {
    pub specs: Vec<GMaskSpecExt4>,
    offsets: BTreeMap<String, (usize, usize, usize)>,
    pub coeffs: Vec<Ext4>,
}

impl GMaskExt4 {
    pub fn sample(specs: Vec<GMaskSpecExt4>, rng: &mut CShakeRng) -> Self {
        let mut offsets = BTreeMap::new();
        let mut total_ext = 0usize;
        for sp in &specs {
            assert!(!offsets.contains_key(&sp.name), "duplicate GMaskSpecExt4 {}", sp.name);
            offsets.insert(sp.name.clone(), (total_ext, sp.num_rounds, sp.deg));
            total_ext += sp.num_rounds * (sp.deg + 1);
        }
        let coeffs: Vec<Ext4> = (0..total_ext)
            .map(|_| Ext4([rng.next_bb(), rng.next_bb(), rng.next_bb(), rng.next_bb()]))
            .collect();
        Self {
            specs,
            offsets,
            coeffs,
        }
    }

    #[inline]
    pub fn padded_limb_len(&self) -> usize {
        self.coeffs.len().max(4).next_power_of_two()
    }

    /// Export the 4 BabyBear coordinate limbs as 4 power-of-two tables (zero-padded after `coeffs.len()`).
    pub fn to_four_bb_tables(&self) -> [Vec<u32>; 4] {
        let cap = self.padded_limb_len();
        let mut out: [Vec<u32>; 4] = std::array::from_fn(|_| vec![0u32; cap]);
        for (i, c) in self.coeffs.iter().enumerate() {
            for l in 0..4 {
                out[l][i] = c.0[l];
            }
        }
        out
    }

    #[inline]
    fn poly_slice(&self, name: &str, j: usize) -> &[Ext4] {
        let &(off, l, deg) = self.offsets.get(name).expect("unknown GMaskExt4 spec");
        assert!(j < l);
        let st = off + j * (deg + 1);
        &self.coeffs[st..st + deg + 1]
    }

    pub fn hypercube_sum(&self, name: &str) -> Ext4 {
        let &(_, l, _) = self.offsets.get(name).expect("unknown GMaskExt4 spec");
        let scale = bpow(2, (l - 1) as u64);
        let mut acc = Ext4::ZERO;
        for j in 0..l {
            let c = self.poly_slice(name, j);
            let mut gj1 = Ext4::ZERO;
            for &ck in c {
                gj1 = gj1.add(ck);
            }
            acc = acc.add(c[0]).add(gj1);
        }
        acc.scale_bb(scale)
    }

    pub fn eval_at(&self, name: &str, r: &[Ext4]) -> Ext4 {
        let &(_, l, _) = self.offsets.get(name).expect("unknown GMaskExt4 spec");
        assert_eq!(r.len(), l);
        let mut acc = Ext4::ZERO;
        for (j, &rj) in r.iter().enumerate() {
            acc = acc.add(eval_poly_ext4(self.poly_slice(name, j), rj));
        }
        acc
    }

    pub fn round_poly(&self, name: &str, i: usize, r_prefix: &[Ext4]) -> Vec<Ext4> {
        let &(_, l, deg) = self.offsets.get(name).expect("unknown GMaskExt4 spec");
        assert!(i < l && r_prefix.len() == i);
        let a_scale = bpow(2, (l - 1 - i) as u64);
        let mut pref = Ext4::ZERO;
        for (j, &rj) in r_prefix.iter().enumerate() {
            pref = pref.add(eval_poly_ext4(self.poly_slice(name, j), rj));
        }
        let ci = self.poly_slice(name, i);
        let mut k0 = pref.add(ci[0]).scale_bb(a_scale);
        if i + 1 < l {
            let b_scale = bpow(2, (l - 2 - i) as u64);
            let mut rem = Ext4::ZERO;
            for j in (i + 1)..l {
                let cj = self.poly_slice(name, j);
                let mut gj1 = Ext4::ZERO;
                for &ck in cj {
                    gj1 = gj1.add(ck);
                }
                rem = rem.add(cj[0]).add(gj1);
            }
            k0 = k0.add(rem.scale_bb(b_scale));
        }
        let mut out = Vec::with_capacity(deg + 1);
        out.push(k0);
        for &ck in &ci[1..] {
            out.push(ck.scale_bb(a_scale));
        }
        out
    }

    pub fn blind_round_poly(
        &self,
        name: &str,
        i: usize,
        r_prefix: &[Ext4],
        rho: Ext4,
        unmasked: &[Ext4],
    ) -> Vec<Ext4> {
        let gp = self.round_poly(name, i, r_prefix);
        assert_eq!(unmasked.len(), gp.len());
        unmasked
            .iter()
            .zip(gp.iter())
            .map(|(&s, &g)| s.add(rho.mul(g)))
            .collect()
    }

    /// Build `DenseSmall` weight vectors `(w_sum[0..cap], w_at[0..cap])` over `Ext4` for `spec_name`.
    pub fn build_spec_weights(
        specs: &[GMaskSpecExt4],
        spec_name: &str,
        r_challenges: &[Ext4],
    ) -> (Vec<Ext4>, Vec<Ext4>) {
        let mut total = 0usize;
        let mut target = None;
        for sp in specs {
            if sp.name == spec_name {
                target = Some((total, sp.num_rounds, sp.deg));
            }
            total += sp.num_rounds * (sp.deg + 1);
        }
        let (off, l, deg) = target.expect("spec_name missing");
        assert_eq!(r_challenges.len(), l);
        let cap = total.max(4).next_power_of_two();
        let scale_g = bpow(2, (l - 1) as u64);
        let two_g = bmul(2, scale_g);
        let mut w_sum = vec![Ext4::ZERO; cap];
        let mut w_at = vec![Ext4::ZERO; cap];
        for (j, &rj) in r_challenges.iter().enumerate() {
            let base = off + j * (deg + 1);
            w_sum[base] = Ext4::from_bb(two_g);
            for k in 1..=deg {
                w_sum[base + k] = Ext4::from_bb(scale_g);
            }
            let mut r_pw = Ext4::ONE;
            for k in 0..=deg {
                w_at[base + k] = r_pw;
                r_pw = r_pw.mul(rj);
            }
        }
        (w_sum, w_at)
    }
}

/// Degree-3 `GMaskExt4`-blinded `EinSumcheck` proof (`\sum_{h, p} eq(z_s, h) * L[h, p] * R[h, p] == claim`),
/// achieving `TVD == 0` witness-independent sumcheck messages (`0` unmasked Gruen leakage!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlindedEinSumExt4Proof {
    pub gmask_sum: Ext4,
    pub rounds: Vec<[Ext4; 4]>, // degree-3 monomial coeffs `[c0, c1, c2, c3]`
}

impl BlindedEinSumExt4Proof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.rounds.len() as u8);
        let mut xs = Vec::with_capacity(1 + self.rounds.len() * 4);
        xs.push(self.gmask_sum);
        for r in &self.rounds {
            xs.extend_from_slice(r);
        }
        pack_ext4_slice(&xs, out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let n_r = cur.read_u8()? as usize;
        if n_r == 0 || n_r > 30 {
            return Err("invalid BlindedEinSumExt4Proof round count".into());
        }
        let xs = unpack_ext4_slice(cur, 1 + n_r * 4)?;
        if xs.len() != 1 + n_r * 4 {
            return Err("BlindedEinSumExt4Proof Ext4 count mismatch".into());
        }
        let gmask_sum = xs[0];
        let mut rounds = Vec::with_capacity(n_r);
        for i in 0..n_r {
            let st = 1 + 4 * i;
            rounds.push([xs[st], xs[st + 1], xs[st + 2], xs[st + 3]]);
        }
        Ok(Self { gmask_sum, rounds })
    }
}

#[inline]
fn cubic_from_zero_one_two_inf_monomial(p0: Ext4, p1: Ext4, p2: Ext4, p_inf: Ext4) -> [Ext4; 4] {
    // Recover monomial `[c0, c1, c2, c3]` via `eval_cubic_zero_one_two_inf_ext4` or closed-form differences (`0` inversions!):
    let _ = eval_cubic_zero_one_two_inf_ext4;
    let inv2 = crate::ext4::INV2_BB;
    let six_c3 = p_inf.scale_bb(6);
    let two_p1 = p1.add(p1);
    let c2 = p2.sub(two_p1).add(p0).sub(six_c3).scale_bb(inv2);
    let c1 = p1.sub(p0).sub(c2).sub(p_inf);
    [p0, c1, c2, p_inf]
}

/// Prove `claim = sum_{h, p} eq(z_s, h) * left[h, p] * right[h, p]` blinded by `GMaskExt4` (`deg = 3`).
/// Returns `(proof, rho, challenges, left_at_r, right_at_r, terminal_masked_val)`.
pub fn prove_gmask_einsum_ext4(
    left_tab: &[Ext4],
    right_tab: &[Ext4],
    mu_s: usize,
    kappa: usize,
    z_s: &[Ext4],
    gmask: &GMaskExt4,
    spec_name: &str,
    tr: &mut CShakeTranscript,
) -> (BlindedEinSumExt4Proof, Ext4, Vec<Ext4>, Ext4, Ext4, Ext4) {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);

    let gmask_sum = gmask.hypercube_sum(spec_name);
    tr.absorb_ext4(b"gm_es_gsum", gmask_sum);
    tr.absorb_ext4_slice(b"gm_es_zs", z_s);
    let rho = tr.squeeze_ext4(b"gm_es_rho", true);

    let suf_tables = build_eq_suffix_tables_ext4(z_s);
    let mut l_cur = left_tab.to_vec();
    let mut r_cur = right_tab.to_vec();
    let mut rounds = Vec::with_capacity(m);
    let mut challenges = Vec::with_capacity(m);
    let mut prefix_eq = Ext4::ONE;

    for u in 0..mu_s {
        let suf = &suf_tables[mu_s - 1 - u];
        let rem_h_pairs = suf.len();
        let nk = 1usize << kappa;
        let stride_p = rem_h_pairs * 2;
        let mut q0 = Ext4::ZERO;
        let mut q1 = Ext4::ZERO;
        let mut q2 = Ext4::ZERO;
        let mut q_inf = Ext4::ZERO;

        for h_rem in 0..rem_h_pairs {
            let w = suf[h_rem];
            let mut s0 = Ext4::ZERO;
            let mut s1 = Ext4::ZERO;
            let mut s2 = Ext4::ZERO;
            let mut sinf = Ext4::ZERO;
            for q in 0..nk {
                let idx0 = q * stride_p + 2 * h_rem;
                let (a0, a1) = (l_cur[idx0], l_cur[idx0 + 1]);
                let (b0, b1) = (r_cur[idx0], r_cur[idx0 + 1]);
                let da = a1.sub(a0);
                let db = b1.sub(b0);
                let a2 = a1.add(da);
                let b2 = b1.add(db);
                s0 = s0.add(a0.mul(b0));
                s1 = s1.add(a1.mul(b1));
                s2 = s2.add(a2.mul(b2));
                sinf = sinf.add(da.mul(db));
            }
            q0 = q0.add(w.mul(s0));
            q1 = q1.add(w.mul(s1));
            q2 = q2.add(w.mul(s2));
            q_inf = q_inf.add(w.mul(sinf));
        }

        let zu = z_s[u];
        let eq0 = prefix_eq.mul(Ext4::ONE.sub(zu));
        let eq1 = prefix_eq.mul(zu);
        let eq2 = prefix_eq.mul(zu.scale_bb(3).sub(Ext4::ONE));
        let eq_slope = prefix_eq.mul(zu.add(zu).sub(Ext4::ONE)); // prefix_eq * (2*z_u - 1)

        let unmasked = cubic_from_zero_one_two_inf_monomial(
            eq0.mul(q0),
            eq1.mul(q1),
            eq2.mul(q2),
            eq_slope.mul(q_inf),
        );
        let blinded_v = gmask.blind_round_poly(spec_name, u, &challenges, rho, &unmasked);
        let blinded = [blinded_v[0], blinded_v[1], blinded_v[2], blinded_v[3]];
        tr.absorb_ext4_slice(b"gm_es_rd", &blinded);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        rounds.push(blinded);
        challenges.push(ch);
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
        prefix_eq = prefix_eq.mul(eq_lin_ext4(zu, ch));
    }

    for v in 0..kappa {
        let half = l_cur.len() / 2;
        let mut c0 = Ext4::ZERO;
        let mut c1 = Ext4::ZERO;
        let mut c2 = Ext4::ZERO;
        for idx in 0..half {
            let (a0, a1) = (l_cur[2 * idx], l_cur[2 * idx + 1]);
            let (b0, b1) = (r_cur[2 * idx], r_cur[2 * idx + 1]);
            let da = a1.sub(a0);
            let db = b1.sub(b0);
            c0 = c0.add(a0.mul(b0));
            c1 = c1.add(a0.mul(db).add(da.mul(b0)));
            c2 = c2.add(da.mul(db));
        }
        let unmasked = [
            prefix_eq.mul(c0),
            prefix_eq.mul(c1),
            prefix_eq.mul(c2),
            Ext4::ZERO,
        ];
        let round_idx = mu_s + v;
        let blinded_v = gmask.blind_round_poly(spec_name, round_idx, &challenges, rho, &unmasked);
        let blinded = [blinded_v[0], blinded_v[1], blinded_v[2], blinded_v[3]];
        tr.absorb_ext4_slice(b"gm_es_rd", &blinded);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        rounds.push(blinded);
        challenges.push(ch);
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
    }

    let term = eval_poly_ext4(rounds.last().unwrap(), *challenges.last().unwrap());
    (
        BlindedEinSumExt4Proof { gmask_sum, rounds },
        rho,
        challenges,
        l_cur[0],
        r_cur[0],
        term,
    )
}

/// Replay `BlindedEinSumExt4Proof` on the verifier, returning `(rho, challenges, terminal_masked_val)`.
pub fn verify_gmask_einsum_ext4(
    unmasked_claim: Ext4,
    mu_s: usize,
    kappa: usize,
    z_s: &[Ext4],
    prf: &BlindedEinSumExt4Proof,
    tr: &mut CShakeTranscript,
) -> Result<(Ext4, Vec<Ext4>, Ext4), String> {
    let m = mu_s + kappa;
    if z_s.len() != mu_s || prf.rounds.len() != m {
        return Err("BlindedEinSumExt4Proof dimension mismatch".into());
    }
    tr.absorb_ext4(b"gm_es_gsum", prf.gmask_sum);
    tr.absorb_ext4_slice(b"gm_es_zs", z_s);
    let rho = tr.squeeze_ext4(b"gm_es_rho", true);

    let mut running = unmasked_claim.add(rho.mul(prf.gmask_sum));
    let mut challenges = Vec::with_capacity(m);
    for (i, poly) in prf.rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]).add(poly[3]);
        if p0.add(p1) != running {
            return Err(format!("BlindedEinSumExt4Proof round {i} failed p(0)+p(1) == claim"));
        }
        tr.absorb_ext4_slice(b"gm_es_rd", poly);
        let ch = tr.squeeze_ext4(b"gm_es_ch", true);
        challenges.push(ch);
        running = eval_poly_ext4(poly, ch);
    }
    Ok((rho, challenges, running))
}

// ================================================================================================
// §3. `WhirExt4Pcs`: Subtable-Packed Matrix Commitment + Subdomain-Lifted Multi-Matrix WHIR Cascade
// ================================================================================================

/// Canonical BabyBear coset shift $\zeta_\nu = G_{\text{PRIM}}^{2^{23 - \nu}} \pmod P$ for domain $N = 2^\nu \le 2^{23}$.
/// Satisfies $\big(\zeta_{\nu_{\max}}\big)^{2^{\nu_{\max} - \nu}} = \zeta_\nu$, aligning all subdomains!
#[inline]
pub fn canonical_coset_shift_bb(log_n_pts: usize) -> u32 {
    assert!(log_n_pts <= 23);
    bpow(G_PRIM, 1u64 << (23 - log_n_pts))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CosetLevelExt4 {
    pub log_n: usize,
    pub n_pts: usize,
    pub shift: u32,
    pub omega: u32,
}

impl CosetLevelExt4 {
    pub fn new(log_n: usize) -> Self {
        let n_pts = 1usize << log_n;
        Self {
            log_n,
            n_pts,
            shift: canonical_coset_shift_bb(log_n),
            omega: crate::ext4::root_of_unity_bb(n_pts),
        }
    }

    pub fn fold(&self, kr: usize) -> Self {
        assert!(kr <= self.log_n);
        let b = 1u64 << kr;
        Self {
            log_n: self.log_n - kr,
            n_pts: self.n_pts >> kr,
            shift: bpow(self.shift, b),
            omega: bpow(self.omega, b),
        }
    }

    #[inline]
    pub fn point(&self, j: usize) -> u32 {
        bmul(self.shift, bpow(self.omega, j as u64))
    }

    #[inline]
    pub fn fiber_base_and_zeta(&self, kr: usize, f_idx: usize) -> (u32, u32) {
        let log_next = self.log_n - kr;
        let x0 = bmul(self.shift, bpow(self.omega, f_idx as u64));
        let zeta = bpow(self.omega, 1u64 << log_next);
        (x0, zeta)
    }

    #[inline]
    pub fn fiber_point_indices(&self, kr: usize, f_idx: usize) -> Vec<usize> {
        let stride = 1usize << (self.log_n - kr);
        let b = 1usize << kr;
        (0..b).map(|m| f_idx + m * stride).collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubtableMeta {
    pub id: usize,
    pub m_vars: usize,
    pub base_cell: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirExt4MatrixShape {
    pub mr: usize,
    pub mc: usize,
    pub rd: usize,
    pub usable_rows: usize,
    pub c: usize,
    pub w0: usize,
    pub blow: usize,
    pub n0: usize,
    pub zk: bool,
    pub r_total: usize,
    pub subtables: Vec<SubtableMeta>,
}

impl WhirExt4MatrixShape {
    pub fn for_subtables(m_vars_list: &[usize], zk: bool, blow: usize) -> Self {
        assert!(!m_vars_list.is_empty() && blow.is_power_of_two() && blow >= 4);
        // Sort `(orig_id, m_vars)` descending by `m_vars` for zero-waste power-of-two alignment!
        let mut indexed: Vec<(usize, usize)> = m_vars_list.iter().copied().enumerate().collect();
        indexed.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

        let mut offset = 0usize;
        let mut by_orig = vec![SubtableMeta { id: 0, m_vars: 0, base_cell: 0 }; m_vars_list.len()];
        for (orig_id, m_v) in indexed {
            debug_assert_eq!(offset & ((1usize << m_v) - 1), 0);
            by_orig[orig_id] = SubtableMeta {
                id: orig_id,
                m_vars: m_v,
                base_cell: offset,
            };
            offset += 1usize << m_v;
        }
        let total_data_cells = offset.max(64);

        // Keep `N_0 = blow * W_0 <= 2^{18} = 262,144` so `[BCIKS20]` UD soundness clears `>= 100.6` bits!
        // - If `zk == true`: `W_0 = 2 * C`, so `mc <= 14` (`C <= 16,384`, `W_0 <= 32,768`, `N_0 <= 262,144`);
        //   also require `C >= 256` (`hide = C >= 256 > WHIR_EXT4_T_QUERIES_100`).
        // - If `zk == false`: `W_0 = C`, so `mc <= 15` (`C <= 32,768`, `W_0 <= 32,768`, `N_0 <= 262,144`).
        let mc_min = if zk { 8usize } else { 6usize };
        let mc_max = if zk { 14usize } else { 15usize };

        let mut best: Option<(usize, usize, usize)> = None;
        for mc in mc_min..=mc_max {
            let c = 1usize << mc;
            let needed_rows = total_data_cells.div_ceil(c);
            let min_rd = if zk {
                (needed_rows + 4).max(8).next_power_of_two()
            } else {
                needed_rows.max(1).next_power_of_two()
            };
            let mr = min_rd.trailing_zeros() as usize;
            let r_total = min_rd + if zk { 12 } else { 0 };
            let w0 = if zk { 2 * c } else { c };
            let n0 = blow * w0;
            // Minimize Stage-0 proof bytes (`140 * r_total * 31/8 + Merkle`) while preferring larger `mc` up to `N_0 <= 2^{18}`:
            let est = 140 * r_total * 4 + 140 * (n0.trailing_zeros().saturating_sub(6) as usize) * 32
                + (mr + mc) * 64;
            if best.map_or(true, |b| est < b.0) {
                best = Some((est, mr, mc));
            }
        }
        let (_, mr, mc) = best.expect("valid WhirExt4MatrixShape");
        let rd = 1usize << mr;
        let usable_rows = if zk { rd - 4 } else { rd };
        let c = 1usize << mc;
        let w0 = if zk { 2 * c } else { c };
        let n0 = blow * w0;
        let r_total = rd + if zk { 12 } else { 0 };

        Self {
            mr,
            mc,
            rd,
            usable_rows,
            c,
            w0,
            blow,
            n0,
            zk,
            r_total,
            subtables: by_orig,
        }
    }

    pub fn single_table(m_vars: usize, zk: bool) -> Self {
        Self::for_subtables(&[m_vars], zk, WHIR_EXT4_BLOWUP)
    }

    /// Returns `(bciks20_thm14_ud_bits, bciks20_eta_slack_bits, ahiv17_ud_bits)` at `t_queries`.
    pub fn provable_soundness_bits(&self, t_queries: usize) -> (f64, f64, f64) {
        let log_f = 4.0 * (P as f64).log2(); // 123.6276 bits
        let n = self.n0 as f64;
        let rho = (self.w0 as f64) / n;
        let tq = t_queries.min(self.n0) as f64;

        // 1. Exact `[BCIKS20]` Thm 1.4/1.5 UD (`Selvage/BCIKS20/EpsCa.lean:179`, `theta = (1 - rho)/2`):
        let e_ud = (self.n0 - self.w0 - 1) / 2;
        let theta_exact = ((e_ud + 1) as f64) / n;
        let q_exact = -tq * (1.0 - theta_exact).log2();
        let alg_exact = log_f - (24.0 * n).log2(); // includes `3` folds of arity `<= 8` (`3 * 8 * N`)
        let bciks_thm14 = q_exact.min(alg_exact);

        // 2. Conservative `eta`-slack `[BCIKS20]` UD (`eta = 2^{-5} = 0.03125`):
        let eta = 2.0f64.powi(-5);
        let theta_eta = 0.5 * (1.0 - rho) - eta;
        let q_eta = -tq * (1.0 - theta_eta).log2();
        let alg_eta = log_f + eta.log2() - n.log2();
        let bciks_eta = q_eta.min(alg_eta);

        // 3. Classical `[AHIV17]` `d/3` UD (`delta = (1 - rho)/3`):
        let delta_ahiv = (1.0 - rho) / 3.0;
        let ahiv = (-tq * (1.0 - delta_ahiv).log2()).min(alg_exact);

        (bciks_thm14, bciks_eta, ahiv)
    }

    fn tag_bytes(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(12 + self.subtables.len() * 5);
        b.push(self.mr as u8);
        b.push(self.mc as u8);
        b.push(self.blow as u8);
        b.push(if self.zk { 1 } else { 0 });
        b.extend_from_slice(&(self.subtables.len() as u16).to_le_bytes());
        for st in &self.subtables {
            b.push(st.m_vars as u8);
            b.extend_from_slice(&(st.base_cell as u32).to_le_bytes());
        }
        b
    }
}

#[inline]
fn hash_s0_col_cshake(col_idx: usize, opt_salt: Option<&[u8; 16]>, col: &[u32]) -> [u8; 32] {
    let salt_len = if opt_salt.is_some() { 16 } else { 0 };
    let mut buf = Vec::with_capacity(4 + salt_len + col.len() * 4);
    buf.extend_from_slice(&(col_idx as u32).to_le_bytes());
    if let Some(s) = opt_salt {
        buf.extend_from_slice(s);
    }
    for &v in col {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    cshake256_32(WHIR_S0_LEAF_DOM, &buf)
}

#[inline]
fn hash_fold_fiber_cshake(round: usize, f_idx: usize, vals: &[Ext4]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(5 + vals.len() * 16);
    buf.push(round as u8);
    buf.extend_from_slice(&(f_idx as u32).to_le_bytes());
    for v in vals {
        buf.extend_from_slice(&v.to_bytes());
    }
    cshake256_32(WHIR_FOLD_LEAF_DOM, &buf)
}

fn build_cshake_tree(leaves: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    assert!(!leaves.is_empty() && leaves.len().is_power_of_two());
    let mut tree = vec![leaves];
    let mut level = 0u8;
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = if prev.len() >= 512 {
            prev.par_chunks_exact(2)
                .enumerate()
                .map(|(idx, pair)| {
                    merkle_node_cshake(WHIR_MERKLE_NODE_DOM, level, idx as u32, &pair[0], &pair[1])
                })
                .collect()
        } else {
            prev.chunks_exact(2)
                .enumerate()
                .map(|(idx, pair)| {
                    merkle_node_cshake(WHIR_MERKLE_NODE_DOM, level, idx as u32, &pair[0], &pair[1])
                })
                .collect()
        };
        tree.push(next);
        level += 1;
    }
    tree
}

/// Prover-side committed `WhirExt4Matrix` (`1` or more power-of-two BabyBear tables packed in 1 commitment!).
pub struct WhirCommittedMatrixExt4 {
    pub shape: WhirExt4MatrixShape,
    /// `r_total x w0` monomial coefficients.
    pub coeffs: Vec<u32>,
    internal_gmask: Option<GMaskExt4>,
    pub col_salts: Vec<[u8; 16]>,
    pub tree0: Vec<Vec<[u8; 32]>>,
    pub root: [u8; 32],
    /// Column-major Stage-0 evaluations `[n0 * r_total]`.
    pub cw0: Vec<u32>,
}

impl WhirCommittedMatrixExt4 {
    pub fn commit(tables: &[&[u32]], zk: bool, opt_seed: Option<[u8; 32]>) -> Self {
        let m_vars: Vec<usize> = tables
            .iter()
            .map(|t| {
                assert!(t.len().is_power_of_two());
                t.len().trailing_zeros() as usize
            })
            .collect();
        let shape = WhirExt4MatrixShape::for_subtables(&m_vars, zk, WHIR_EXT4_BLOWUP);
        Self::commit_with_shape(shape, tables, opt_seed)
    }

    pub fn commit_with_shape(
        shape: WhirExt4MatrixShape,
        tables: &[&[u32]],
        opt_seed: Option<[u8; 32]>,
    ) -> Self {
        assert_eq!(tables.len(), shape.subtables.len());
        let (c, w0, rd, r_total) = (shape.c, shape.w0, shape.rd, shape.r_total);
        let mut coeffs = vec![0u32; r_total * w0];

        // Copy each subtable into its exact `2^{m_t}`-aligned subcube in `0 .. usable_rows * c`:
        for (st, &tab) in shape.subtables.iter().zip(tables.iter()) {
            assert_eq!(tab.len(), 1usize << st.m_vars);
            for (u, &val) in tab.iter().enumerate() {
                let cell = st.base_cell + u;
                let r = cell >> shape.mc;
                let col = cell & (c - 1);
                coeffs[r * w0 + col] = if val >= P_U32 { val % P_U32 } else { val };
            }
        }

        let seed = opt_seed.unwrap_or_else(os_random_seed_32);
        let mut rng = CShakeRng::from_seed(b"QW35-WHIR-MASK-RNG-V1", &seed);

        let (internal_gmask, col_salts) = if shape.zk {
            // 1. Random column-hiding tail `[c..w0)` on all data rows `0..usable_rows`:
            for r in 0..shape.usable_rows {
                for col in c..w0 {
                    coeffs[r * w0 + col] = rng.next_bb();
                }
            }
            // 2. `4` uniform ZK data-blinding rows (`usable_rows .. rd`):
            for r in shape.usable_rows..rd {
                for col in 0..w0 {
                    coeffs[r * w0 + col] = rng.next_bb();
                }
            }
            // 3. `4` internal `GMaskExt4` rows (`rd .. rd + 4`):
            let m_bits = shape.mc + shape.mr;
            let gm = GMaskExt4::sample(vec![GMaskSpecExt4::new("pcs_sc", m_bits, 2)], &mut rng);
            let n_gm = gm.coeffs.len();
            assert!(n_gm < c);
            for l in 0..4 {
                let r = rd + l;
                for (u, e) in gm.coeffs.iter().enumerate() {
                    coeffs[r * w0 + u] = e.0[l];
                }
                for col in n_gm..w0 {
                    coeffs[r * w0 + col] = rng.next_bb();
                }
            }
            // 4. `4` `Z_gm` rank-preserving rows (`rd + 4 .. rd + 8`) + `4` `P_prox` WHIR mask rows (`rd + 8 .. rd + 12`):
            for r in (rd + 4)..r_total {
                for col in 0..w0 {
                    coeffs[r * w0 + col] = rng.next_bb();
                }
            }
            let mut salts = vec![[0u8; 16]; shape.n0];
            for s in &mut salts {
                rng.fill_bytes(s);
            }
            (Some(gm), salts)
        } else {
            (None, Vec::new())
        };

        // Parallel coset-NTT encoding on canonical coset `D_0`:
        let log_n0 = shape.n0.trailing_zeros() as usize;
        let shift = canonical_coset_shift_bb(log_n0);
        let tw = precompute_twiddles_bb(shape.n0, false);
        let mut shift_pows = Vec::with_capacity(w0);
        let mut cur = 1u32;
        for _ in 0..w0 {
            shift_pows.push(cur);
            cur = bmul(cur, shift);
        }

        let row_evals: Vec<Vec<u32>> = (0..r_total)
            .into_par_iter()
            .map(|r| {
                let mut buf = vec![0u32; shape.n0];
                let src = &coeffs[r * w0..(r + 1) * w0];
                for k in 0..w0 {
                    buf[k] = bmul(src[k], shift_pows[k]);
                }
                ntt_bb_in_place(&mut buf, &tw);
                buf
            })
            .collect();

        let mut cw0 = vec![0u32; shape.n0 * r_total];
        cw0.par_chunks_mut(r_total * 256)
            .enumerate()
            .for_each(|(blk, dst)| {
                let j_start = blk * 256;
                let cnt = (dst.len()) / r_total;
                for dj in 0..cnt {
                    let j = j_start + dj;
                    let col_dst = &mut dst[dj * r_total..(dj + 1) * r_total];
                    for r in 0..r_total {
                        col_dst[r] = row_evals[r][j];
                    }
                }
            });

        let leaves: Vec<[u8; 32]> = (0..shape.n0)
            .into_par_iter()
            .map(|j| {
                let col = &cw0[j * r_total..(j + 1) * r_total];
                let salt = if shape.zk { Some(&col_salts[j]) } else { None };
                hash_s0_col_cshake(j, salt, col)
            })
            .collect();
        let tree0 = build_cshake_tree(leaves);
        let root = tree0.last().unwrap()[0];

        Self {
            shape,
            coeffs,
            internal_gmask,
            col_salts,
            tree0,
            root,
            cw0,
        }
    }
}

/// Linear term inside a `JointLinearClaimExt4` over a `WhirCommittedMatrixExt4`.
#[derive(Clone, Debug)]
pub enum LinearTermExt4 {
    /// Evaluates `weight * T_{subtable}(point)` in `O(mc + mr)` verifier muls!
    PointEval {
        subtable: usize,
        point: Vec<Ext4>,
        weight: Ext4,
    },
    /// Evaluates `<weights_lsb, T_{subtable}>` (`len == 2^{m_t} <= 2048`) for `GMaskExt4` discharge!
    DenseSmall {
        subtable: usize,
        weights_lsb: Vec<Ext4>,
    },
}

/// Asserts $\sum_{t \in \text{terms}} \text{eval}(t) == \text{rhs} \in \mathrm{Ext4}$ against one `WhirCommittedMatrixExt4`.
#[derive(Clone, Debug)]
pub struct JointLinearClaimExt4 {
    pub terms: Vec<LinearTermExt4>,
    pub rhs: Ext4,
}

impl JointLinearClaimExt4 {
    pub fn point_eval(subtable: usize, point: Vec<Ext4>, value: Ext4) -> Self {
        Self {
            terms: vec![LinearTermExt4::PointEval {
                subtable,
                point,
                weight: Ext4::ONE,
            }],
            rhs: value,
        }
    }

    /// Append 2 `JointLinearClaimExt4`s (`G` and `a_pub * T_sec(r_pt) + rho * g(r_gm) == term`, or pure `g(r_gm) == val`)!
    pub fn gmask_sum_claim(limb_subtables: [usize; 4], w_sum: &[Ext4], g_sum: Ext4) -> Self {
        let e_basis = [
            Ext4([1, 0, 0, 0]),
            Ext4([0, 1, 0, 0]),
            Ext4([0, 0, 1, 0]),
            Ext4([0, 0, 0, 1]),
        ];
        let terms = (0..4)
            .map(|l| LinearTermExt4::DenseSmall {
                subtable: limb_subtables[l],
                weights_lsb: w_sum.iter().map(|&w| w.mul(e_basis[l])).collect(),
            })
            .collect();
        Self { terms, rhs: g_sum }
    }

    /// HVZK joint terminal weld: checks `sec_terms + rho * g(r) == terminal_masked` WITHOUT revealing `g(r)`!
    pub fn hvzk_terminal_weld(
        mut sec_terms: Vec<LinearTermExt4>,
        limb_subtables: [usize; 4],
        w_at: &[Ext4],
        rho: Ext4,
        terminal_masked: Ext4,
    ) -> Self {
        let e_basis = [
            Ext4([1, 0, 0, 0]),
            Ext4([0, 1, 0, 0]),
            Ext4([0, 0, 1, 0]),
            Ext4([0, 0, 0, 1]),
        ];
        for l in 0..4 {
            let factor = rho.mul(e_basis[l]);
            sec_terms.push(LinearTermExt4::DenseSmall {
                subtable: limb_subtables[l],
                weights_lsb: w_at.iter().map(|&w| w.mul(factor)).collect(),
            });
        }
        Self {
            terms: sec_terms,
            rhs: terminal_masked,
        }
    }
}

// ================================================================================================
// §4. Multi-Matrix Subdomain-Lifted `CommitF0` WHIR Cascade (`open_whir_batch_ext4` / `verify_whir_batch_ext4`)
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirMatrixPartProofExt4 {
    pub zk: bool,
    pub gmask_sum: Ext4,          // `ZERO` if `!zk`
    pub z_gm_masks: [Ext4; 2],    // `[ZERO; 2]` if `!zk`
    pub row_sc_rounds: Vec<[Ext4; 3]>,
    pub m_eval: Ext4,
    pub u_eval_at_zeta: Ext4,
    pub p_gm_hat_at_zeta: Ext4,   // `ZERO` if `!zk`
    pub u_prox_at_zeta: Ext4,
    /// Opened single columns at canonical deduplicated `q_idx & (N_m - 1)` (`n_uniq_m * r_total` `u32`s).
    pub s0_col_vals: Vec<u32>,
    pub s0_salts: Vec<[u8; 16]>,
    pub s0_multiproof: MerkleMultiProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirCascadeLevelProofExt4 {
    pub root: [u8; 32],
    pub ood_evals: [Ext4; 2], // `u = 2` OOD samples (`DKT26` Lemma 8.1 -> `> 210b` OOD soundness!)
    pub lockstep_sc: Vec<[Ext4; 3]>,
    pub opened_fibers: Vec<Ext4>,
    pub multiproof: MerkleMultiProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirBatchOpeningProofExt4 {
    pub matrix_parts: Vec<WhirMatrixPartProofExt4>,
    pub shared_coeff_rounds: Vec<[Ext4; 3]>,
    pub cascade_levels: Vec<WhirCascadeLevelProofExt4>, // includes `level 0 = root_f0`!
    pub final_ood_evals: [Ext4; 2],
    pub final_lockstep_sc: Vec<[Ext4; 3]>,
    pub final_poly: Vec<Ext4>,
}

impl WhirBatchOpeningProofExt4 {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.matrix_parts.len() as u8);
        for mp in &self.matrix_parts {
            out.push(if mp.zk { 1 } else { 0 });
            out.push(mp.row_sc_rounds.len() as u8);
            let mut hdr = Vec::with_capacity(6 + mp.row_sc_rounds.len() * 3);
            if mp.zk {
                hdr.push(mp.gmask_sum);
                hdr.push(mp.z_gm_masks[0]);
                hdr.push(mp.z_gm_masks[1]);
                hdr.push(mp.p_gm_hat_at_zeta);
            }
            hdr.push(mp.m_eval);
            hdr.push(mp.u_eval_at_zeta);
            hdr.push(mp.u_prox_at_zeta);
            for r in &mp.row_sc_rounds {
                hdr.extend_from_slice(r);
            }
            pack_ext4_slice(&hdr, out);
            pack_bb_31b(&mp.s0_col_vals, out);
            if mp.zk {
                out.extend_from_slice(&(mp.s0_salts.len() as u32).to_le_bytes());
                for s in &mp.s0_salts {
                    out.extend_from_slice(s);
                }
            }
            mp.s0_multiproof.write_to(out);
        }

        out.push(self.shared_coeff_rounds.len() as u8);
        let mut csc = Vec::with_capacity(self.shared_coeff_rounds.len() * 3);
        for r in &self.shared_coeff_rounds {
            csc.extend_from_slice(r);
        }
        pack_ext4_slice(&csc, out);

        out.push(self.cascade_levels.len() as u8);
        for cl in &self.cascade_levels {
            out.extend_from_slice(&cl.root);
            out.push(cl.lockstep_sc.len() as u8);
            let mut lhdr = Vec::with_capacity(2 + cl.lockstep_sc.len() * 3);
            lhdr.extend_from_slice(&cl.ood_evals);
            for r in &cl.lockstep_sc {
                lhdr.extend_from_slice(r);
            }
            pack_ext4_slice(&lhdr, out);
            pack_ext4_slice(&cl.opened_fibers, out);
            cl.multiproof.write_to(out);
        }

        out.push(self.final_lockstep_sc.len() as u8);
        let mut fhdr = Vec::with_capacity(2 + self.final_lockstep_sc.len() * 3);
        fhdr.extend_from_slice(&self.final_ood_evals);
        for r in &self.final_lockstep_sc {
            fhdr.extend_from_slice(r);
        }
        pack_ext4_slice(&fhdr, out);
        pack_ext4_slice(&self.final_poly, out);
    }

    pub fn read_from(cur: &mut ByteCursor<'_>) -> Result<Self, String> {
        let n_m = cur.read_u8()? as usize;
        if n_m == 0 || n_m > 16 {
            return Err("invalid WHIR matrix_parts count".into());
        }
        let mut matrix_parts = Vec::with_capacity(n_m);
        for _ in 0..n_m {
            let zk = cur.read_u8()? != 0;
            let n_sc = cur.read_u8()? as usize;
            if n_sc == 0 || n_sc > 30 {
                return Err("invalid row_sc_rounds count".into());
            }
            let base_ext = if zk { 7 } else { 3 };
            let hdr = unpack_ext4_slice(cur, base_ext + n_sc * 3)?;
            if hdr.len() != base_ext + n_sc * 3 {
                return Err("matrix_parts header count mismatch".into());
            }
            let (gmask_sum, z_gm_masks, p_gm_hat_at_zeta, m_eval, u_eval_at_zeta, u_prox_at_zeta, off) =
                if zk {
                    (hdr[0], [hdr[1], hdr[2]], hdr[3], hdr[4], hdr[5], hdr[6], 7usize)
                } else {
                    (
                        Ext4::ZERO,
                        [Ext4::ZERO; 2],
                        Ext4::ZERO,
                        hdr[0],
                        hdr[1],
                        hdr[2],
                        3usize,
                    )
                };
            let mut row_sc_rounds = Vec::with_capacity(n_sc);
            for i in 0..n_sc {
                let st = off + 3 * i;
                row_sc_rounds.push([hdr[st], hdr[st + 1], hdr[st + 2]]);
            }
            let s0_col_vals = unpack_bb_31b(cur, 1 << 22)?;
            let s0_salts = if zk {
                let ns = cur.read_u32()? as usize;
                if ns > 2048 {
                    return Err("s0_salts overflow".into());
                }
                let mut v = Vec::with_capacity(ns);
                for _ in 0..ns {
                    v.push(cur.read_arr16()?);
                }
                v
            } else {
                Vec::new()
            };
            let s0_multiproof = MerkleMultiProof::read_from(cur)?;
            matrix_parts.push(WhirMatrixPartProofExt4 {
                zk,
                gmask_sum,
                z_gm_masks,
                row_sc_rounds,
                m_eval,
                u_eval_at_zeta,
                p_gm_hat_at_zeta,
                u_prox_at_zeta,
                s0_col_vals,
                s0_salts,
                s0_multiproof,
            });
        }

        let n_csc = cur.read_u8()? as usize;
        if n_csc == 0 || n_csc > 24 {
            return Err("invalid shared_coeff_rounds count".into());
        }
        let csc_v = unpack_ext4_slice(cur, n_csc * 3)?;
        if csc_v.len() != n_csc * 3 {
            return Err("shared_coeff_rounds len mismatch".into());
        }
        let shared_coeff_rounds: Vec<[Ext4; 3]> = (0..n_csc)
            .map(|i| [csc_v[3 * i], csc_v[3 * i + 1], csc_v[3 * i + 2]])
            .collect();

        let n_cl = cur.read_u8()? as usize;
        if n_cl == 0 || n_cl > 10 {
            return Err("invalid cascade_levels count".into());
        }
        let mut cascade_levels = Vec::with_capacity(n_cl);
        for _ in 0..n_cl {
            let root = cur.read_arr32()?;
            let n_lsc = cur.read_u8()? as usize;
            if n_lsc == 0 || n_lsc > 6 {
                return Err("invalid lockstep_sc len".into());
            }
            let lhdr = unpack_ext4_slice(cur, 2 + n_lsc * 3)?;
            if lhdr.len() != 2 + n_lsc * 3 {
                return Err("lhdr len mismatch".into());
            }
            let ood_evals = [lhdr[0], lhdr[1]];
            let lockstep_sc: Vec<[Ext4; 3]> = (0..n_lsc)
                .map(|i| [lhdr[2 + 3 * i], lhdr[2 + 3 * i + 1], lhdr[2 + 3 * i + 2]])
                .collect();
            let opened_fibers = unpack_ext4_slice(cur, 1 << 16)?;
            let multiproof = MerkleMultiProof::read_from(cur)?;
            cascade_levels.push(WhirCascadeLevelProofExt4 {
                root,
                ood_evals,
                lockstep_sc,
                opened_fibers,
                multiproof,
            });
        }

        let n_fl = cur.read_u8()? as usize;
        if n_fl == 0 || n_fl > 6 {
            return Err("invalid final_lockstep_sc len".into());
        }
        let fhdr = unpack_ext4_slice(cur, 2 + n_fl * 3)?;
        if fhdr.len() != 2 + n_fl * 3 {
            return Err("fhdr len mismatch".into());
        }
        let final_ood_evals = [fhdr[0], fhdr[1]];
        let final_lockstep_sc: Vec<[Ext4; 3]> = (0..n_fl)
            .map(|i| [fhdr[2 + 3 * i], fhdr[2 + 3 * i + 1], fhdr[2 + 3 * i + 2]])
            .collect();
        let final_poly = unpack_ext4_slice(cur, 1024)?;

        Ok(Self {
            matrix_parts,
            shared_coeff_rounds,
            cascade_levels,
            final_ood_evals,
            final_lockstep_sc,
            final_poly,
        })
    }
}

/// Canonical $2^k$-ary WHIR folding schedule for `w_max = log2(W_max)` folding down to `W_final <= 128`!
pub fn canonical_ext4_k_schedule(w_max_bits: usize) -> Vec<usize> {
    let mut sched = Vec::new();
    let mut rem = w_max_bits;
    while rem > 7 {
        let kr = if rem - 7 >= 3 {
            3
        } else if rem - 7 == 2 {
            2
        } else {
            1
        };
        sched.push(kr);
        rem -= kr;
    }
    if sched.is_empty() {
        sched.push(1.min(rem));
    }
    sched
}

#[inline]
fn squeeze_non_binary_ext4(tr: &mut CShakeTranscript, label: &[u8]) -> Ext4 {
    loop {
        let c = tr.squeeze_ext4(label, true);
        if c != Ext4::ONE {
            return c;
        }
    }
}

#[inline]
fn squeeze_non_base_ext4(tr: &mut CShakeTranscript, label: &[u8]) -> Ext4 {
    loop {
        let c = tr.squeeze_ext4(label, true);
        if c.0[1] != 0 || c.0[2] != 0 || c.0[3] != 0 {
            return c;
        }
    }
}

fn build_internal_gm_weights_ext4(m_bits: usize, r: &[Ext4]) -> (Vec<Ext4>, Vec<Ext4>) {
    let n_u = 3 * m_bits;
    let sc = bpow(2, (m_bits - 1) as u64);
    let two_sc = bmul(2, sc);
    let mut vg = vec![Ext4::ZERO; n_u];
    let mut vat = vec![Ext4::ZERO; n_u];
    for (j, &rj) in r.iter().enumerate() {
        vg[3 * j] = Ext4::from_bb(two_sc);
        vg[3 * j + 1] = Ext4::from_bb(sc);
        vg[3 * j + 2] = Ext4::from_bb(sc);
        vat[3 * j] = Ext4::ONE;
        vat[3 * j + 1] = rj;
        vat[3 * j + 2] = rj.sq();
    }
    (vg, vat)
}

fn combine_rows_bb_ext4(coeffs: &[u32], w0: usize, row_weights: &[Ext4]) -> Vec<Ext4> {
    let r_cnt = row_weights.len();
    let mut out = vec![Ext4::ZERO; w0];
    out.par_chunks_mut(256).enumerate().for_each(|(blk, dst)| {
        let base_c = blk * 256;
        for (dc, slot) in dst.iter_mut().enumerate() {
            let c = base_c + dc;
            let mut acc = [0u128; 4];
            for r in 0..r_cnt {
                let v = coeffs[r * w0 + c] as u128;
                if v != 0 {
                    let rw = row_weights[r].0;
                    acc[0] += v * (rw[0] as u128);
                    acc[1] += v * (rw[1] as u128);
                    acc[2] += v * (rw[2] as u128);
                    acc[3] += v * (rw[3] as u128);
                }
                if (r & 31) == 31 {
                    for l in &mut acc {
                        *l %= P as u128;
                    }
                }
            }
            *slot = Ext4([
                (acc[0] % (P as u128)) as u32,
                (acc[1] % (P as u128)) as u32,
                (acc[2] % (P as u128)) as u32,
                (acc[3] % (P as u128)) as u32,
            ]);
        }
    });
    out
}

fn pack_4_rows_ext4(coeffs: &[u32], w0: usize, r_start: usize) -> Vec<Ext4> {
    (0..w0)
        .map(|c| {
            Ext4([
                coeffs[r_start * w0 + c],
                coeffs[(r_start + 1) * w0 + c],
                coeffs[(r_start + 2) * w0 + c],
                coeffs[(r_start + 3) * w0 + c],
            ])
        })
        .collect()
}

/// Open a batch of `WhirCommittedMatrixExt4` instances in **ONE shared subdomain-lifted `CommitF0` WHIR cascade**!
/// Requires that the widest matrix (`W_0 == W_max`) has `zk == true` so `F_joint^(0)` is 100% masked (`TVD == 0`)!
pub fn open_whir_batch_ext4(
    matrices: &[(&WhirCommittedMatrixExt4, &[JointLinearClaimExt4])],
    t_queries: usize,
    tr: &mut CShakeTranscript,
) -> WhirBatchOpeningProofExt4 {
    assert!(!matrices.is_empty());
    let w_max = matrices.iter().map(|(m, _)| m.shape.w0).max().unwrap();
    let w_max_bits = w_max.trailing_zeros() as usize;
    assert!(
        matrices.iter().any(|(m, _)| m.shape.w0 == w_max && m.shape.zk),
        "at least one widest matrix in WHIR batch must have zk = true to mask F_joint^(0)"
    );

    // 1. Per-matrix `(mc + mr)`-round row/col sumcheck (`GMaskExt4`-blinded if `zk = true`):
    struct MatInter {
        zk: bool,
        gmask_sum: Ext4,
        z_gm_masks: [Ext4; 2],
        row_sc_rounds: Vec<[Ext4; 3]>,
        m_eval: Ext4,
        z_challenges: Vec<Ext4>,
        u_eval: Vec<Ext4>,
        p_gm_hat: Vec<Ext4>,
        vg: Vec<Ext4>,
        vat: Vec<Ext4>,
    }

    let mut inters = Vec::with_capacity(matrices.len());
    for (m_idx, &(mat, claims)) in matrices.iter().enumerate() {
        let sh = &mat.shape;
        tr.absorb_u32(b"whir_m_idx", m_idx as u32);
        tr.absorb_root(b"whir_m_root", &mat.root);
        tr.absorb_bytes(b"whir_m_shape", &sh.tag_bytes());
        tr.absorb_u32(b"whir_m_ncl", claims.len() as u32);
        for cl in claims {
            tr.absorb_ext4(b"whir_cl_rhs", cl.rhs);
        }

        let beta = tr.squeeze_ext4(b"whir_cl_beta", true);
        let total_cells = sh.rd * sh.c;
        let mut a_tbl = vec![Ext4::ZERO; total_cells];
        let mut b_pw = Ext4::ONE;
        for cl in claims {
            for term in &cl.terms {
                match term {
                    LinearTermExt4::PointEval {
                        subtable,
                        point,
                        weight,
                    } => {
                        let st = sh.subtables[*subtable];
                        assert_eq!(point.len(), st.m_vars);
                        let eq_pt = build_eq_table_lsb_ext4(point);
                        let scale = b_pw.mul(*weight);
                        let dst = &mut a_tbl[st.base_cell..st.base_cell + eq_pt.len()];
                        for (d, &e) in dst.iter_mut().zip(eq_pt.iter()) {
                            *d = d.add(scale.mul(e));
                        }
                    }
                    LinearTermExt4::DenseSmall {
                        subtable,
                        weights_lsb,
                    } => {
                        let st = sh.subtables[*subtable];
                        assert_eq!(weights_lsb.len(), 1usize << st.m_vars);
                        let dst = &mut a_tbl[st.base_cell..st.base_cell + weights_lsb.len()];
                        for (d, &w) in dst.iter_mut().zip(weights_lsb.iter()) {
                            *d = d.add(b_pw.mul(w));
                        }
                    }
                }
            }
            b_pw = b_pw.mul(beta);
        }

        let (gmask_sum, rho) = if sh.zk {
            let gm = mat.internal_gmask.as_ref().unwrap();
            let gs = gm.hypercube_sum("pcs_sc");
            tr.absorb_ext4(b"whir_gm_sum", gs);
            let r = tr.squeeze_ext4(b"whir_gm_rho", true);
            (gs, r)
        } else {
            (Ext4::ZERO, Ext4::ZERO)
        };

        let m_bits = sh.mc + sh.mr;
        let mut row_sc_rounds = Vec::with_capacity(m_bits);
        let mut z_challenges = Vec::with_capacity(m_bits);

        // Round 0 directly on `mat.coeffs`:
        let half0 = total_cells / 2;
        let eval0 = |u: usize| -> [Ext4; 3] {
            let idx0 = 2 * u;
            let r = idx0 >> sh.mc;
            let c0 = idx0 & (sh.c - 1);
            let m0 = mat.coeffs[r * sh.w0 + c0];
            let m1 = mat.coeffs[r * sh.w0 + c0 + 1];
            let dm = bsub(m1, m0);
            let (a0, a1) = (a_tbl[idx0], a_tbl[idx0 + 1]);
            let da = a1.sub(a0);
            [
                a0.scale_bb(m0),
                a0.scale_bb(dm).add(da.scale_bb(m0)),
                da.scale_bb(dm),
            ]
        };
        let unm0 = if half0 >= 2048 {
            (0..half0).into_par_iter().map(eval0).reduce(
                || [Ext4::ZERO; 3],
                |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
            )
        } else {
            let mut acc = [Ext4::ZERO; 3];
            for u in 0..half0 {
                let x = eval0(u);
                for k in 0..3 {
                    acc[k] = acc[k].add(x[k]);
                }
            }
            acc
        };
        let poly0 = if let Some(ref gm) = mat.internal_gmask {
            let bv = gm.blind_round_poly("pcs_sc", 0, &[], rho, &unm0);
            [bv[0], bv[1], bv[2]]
        } else {
            unm0
        };
        tr.absorb_ext4_slice(b"whir_rsc", &poly0);
        let r0 = squeeze_non_binary_ext4(tr, b"whir_rz");
        row_sc_rounds.push(poly0);
        z_challenges.push(r0);

        let mut m_tbl: Vec<Ext4> = (0..half0)
            .into_par_iter()
            .map(|u| {
                let idx0 = 2 * u;
                let r = idx0 >> sh.mc;
                let c0 = idx0 & (sh.c - 1);
                let m0 = mat.coeffs[r * sh.w0 + c0];
                let m1 = mat.coeffs[r * sh.w0 + c0 + 1];
                Ext4::from_bb(m0).add(r0.scale_bb(bsub(m1, m0)))
            })
            .collect();
        a_tbl = (0..half0)
            .into_par_iter()
            .map(|u| a_tbl[2 * u].add(r0.mul(a_tbl[2 * u + 1].sub(a_tbl[2 * u]))))
            .collect();
        let mut cur_len = half0;

        for rd_i in 1..m_bits {
            let half = cur_len / 2;
            let eval_p = |u: usize| -> [Ext4; 3] {
                let (a0, a1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                let (m0, m1) = (m_tbl[2 * u], m_tbl[2 * u + 1]);
                let da = a1.sub(a0);
                let dm = m1.sub(m0);
                [a0.mul(m0), a0.mul(dm).add(da.mul(m0)), da.mul(dm)]
            };
            let unm = if half >= 2048 {
                (0..half).into_par_iter().map(eval_p).reduce(
                    || [Ext4::ZERO; 3],
                    |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
                )
            } else {
                let mut acc = [Ext4::ZERO; 3];
                for u in 0..half {
                    let x = eval_p(u);
                    for k in 0..3 {
                        acc[k] = acc[k].add(x[k]);
                    }
                }
                acc
            };
            let poly = if let Some(ref gm) = mat.internal_gmask {
                let bv = gm.blind_round_poly("pcs_sc", rd_i, &z_challenges, rho, &unm);
                [bv[0], bv[1], bv[2]]
            } else {
                unm
            };
            tr.absorb_ext4_slice(b"whir_rsc", &poly);
            let ri = squeeze_non_binary_ext4(tr, b"whir_rz");
            row_sc_rounds.push(poly);
            z_challenges.push(ri);

            if half >= 4096 {
                a_tbl = (0..half)
                    .into_par_iter()
                    .map(|u| a_tbl[2 * u].add(ri.mul(a_tbl[2 * u + 1].sub(a_tbl[2 * u]))))
                    .collect();
                m_tbl = (0..half)
                    .into_par_iter()
                    .map(|u| m_tbl[2 * u].add(ri.mul(m_tbl[2 * u + 1].sub(m_tbl[2 * u]))))
                    .collect();
            } else {
                for u in 0..half {
                    a_tbl[u] = a_tbl[2 * u].add(ri.mul(a_tbl[2 * u + 1].sub(a_tbl[2 * u])));
                    m_tbl[u] = m_tbl[2 * u].add(ri.mul(m_tbl[2 * u + 1].sub(m_tbl[2 * u])));
                }
                a_tbl.truncate(half);
                m_tbl.truncate(half);
            }
            cur_len = half;
        }

        let m_eval = m_tbl[0];
        tr.absorb_ext4(b"whir_meval", m_eval);

        let eq_row = build_eq_table_lsb_ext4(&z_challenges[sh.mc..]);
        let u_eval = combine_rows_bb_ext4(&mat.coeffs, sh.w0, &eq_row);

        let (z_gm_masks, p_gm_hat, vg, vat) = if sh.zk {
            let p_gm = pack_4_rows_ext4(&mat.coeffs, sh.w0, sh.rd);
            let z_gm = pack_4_rows_ext4(&mat.coeffs, sh.w0, sh.rd + 4);
            let (vg, vat) = build_internal_gm_weights_ext4(m_bits, &z_challenges);
            let mut sg = Ext4::ZERO;
            let mut sat = Ext4::ZERO;
            for u in 0..vg.len() {
                sg = sg.add(vg[u].mul(z_gm[u]));
                sat = sat.add(vat[u].mul(z_gm[u]));
            }
            tr.absorb_ext4(b"whir_sg", sg);
            tr.absorb_ext4(b"whir_sat", sat);
            let bgm = tr.squeeze_ext4(b"whir_bgm", true);
            let p_hat: Vec<Ext4> = p_gm
                .iter()
                .zip(z_gm.iter())
                .map(|(&p, &z)| p.add(bgm.mul(z)))
                .collect();
            ([sg, sat], p_hat, vg, vat)
        } else {
            ([Ext4::ZERO; 2], Vec::new(), Vec::new(), Vec::new())
        };

        inters.push(MatInter {
            zk: sh.zk,
            gmask_sum,
            z_gm_masks,
            row_sc_rounds,
            m_eval,
            z_challenges,
            u_eval,
            p_gm_hat,
            vg,
            vat,
        });
    }

    // 2. ONE Shared `w_max_bits`-round Coefficient Sumcheck across ALL matrices via subdomain lifting `X^{2^{s_m}}`!
    struct LiftedPair {
        v: Vec<Ext4>,
        p: Vec<Ext4>,
    }
    let mut pairs: Vec<LiftedPair> = Vec::with_capacity(matrices.len() * 2);
    for (m_idx, inter) in inters.iter().enumerate() {
        let sh = &matrices[m_idx].0.shape;
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let lam_ev = if m_idx == 0 {
            Ext4::ONE
        } else {
            tr.squeeze_ext4(b"whir_lam_ev", true)
        };
        let eq_col = build_eq_table_lsb_ext4(&inter.z_challenges[..sh.mc]);
        let mut ve_lift = vec![Ext4::ZERO; w_max];
        let mut ue_lift = vec![Ext4::ZERO; w_max];
        for u in 0..sh.c {
            ve_lift[u << s_m] = lam_ev.mul(eq_col[u]);
        }
        for u in 0..sh.w0 {
            ue_lift[u << s_m] = inter.u_eval[u];
        }
        pairs.push(LiftedPair {
            v: ve_lift,
            p: ue_lift,
        });

        if inter.zk {
            let l0 = tr.squeeze_ext4(b"whir_lam_g0", true);
            let l1 = tr.squeeze_ext4(b"whir_lam_g1", true);
            let mut vgm_lift = vec![Ext4::ZERO; w_max];
            let mut pgm_lift = vec![Ext4::ZERO; w_max];
            for u in 0..inter.vg.len() {
                vgm_lift[u << s_m] = l0.mul(inter.vg[u]).add(l1.mul(inter.vat[u]));
            }
            for u in 0..sh.w0 {
                pgm_lift[u << s_m] = inter.p_gm_hat[u];
            }
            pairs.push(LiftedPair {
                v: vgm_lift,
                p: pgm_lift,
            });
        }
    }

    let mut shared_coeff_rounds = Vec::with_capacity(w_max_bits);
    let mut zeta = Vec::with_capacity(w_max_bits);
    let mut len_c = w_max;
    for _ in 0..w_max_bits {
        let half = len_c / 2;
        let eval_c = |u: usize| -> [Ext4; 3] {
            let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
            for lp in &pairs {
                let (v0, v1) = (lp.v[2 * u], lp.v[2 * u + 1]);
                let (p0, p1) = (lp.p[2 * u], lp.p[2 * u + 1]);
                if v0.is_zero() && v1.is_zero() {
                    continue;
                }
                let dv = v1.sub(v0);
                let dp = p1.sub(p0);
                c0 = c0.add(v0.mul(p0));
                c1 = c1.add(v0.mul(dp).add(dv.mul(p0)));
                c2 = c2.add(dv.mul(dp));
            }
            [c0, c1, c2]
        };
        let poly = if half >= 2048 {
            (0..half).into_par_iter().map(eval_c).reduce(
                || [Ext4::ZERO; 3],
                |a, b| [a[0].add(b[0]), a[1].add(b[1]), a[2].add(b[2])],
            )
        } else {
            let mut acc = [Ext4::ZERO; 3];
            for u in 0..half {
                let x = eval_c(u);
                for k in 0..3 {
                    acc[k] = acc[k].add(x[k]);
                }
            }
            acc
        };
        tr.absorb_ext4_slice(b"whir_csc", &poly);
        let z_i = tr.squeeze_ext4(b"whir_cz", true);
        shared_coeff_rounds.push(poly);
        zeta.push(z_i);

        for lp in &mut pairs {
            if half >= 4096 {
                lp.v = (0..half)
                    .into_par_iter()
                    .map(|u| lp.v[2 * u].add(z_i.mul(lp.v[2 * u + 1].sub(lp.v[2 * u]))))
                    .collect();
                lp.p = (0..half)
                    .into_par_iter()
                    .map(|u| lp.p[2 * u].add(z_i.mul(lp.p[2 * u + 1].sub(lp.p[2 * u]))))
                    .collect();
            } else {
                for u in 0..half {
                    lp.v[u] = lp.v[2 * u].add(z_i.mul(lp.v[2 * u + 1].sub(lp.v[2 * u])));
                    lp.p[u] = lp.p[2 * u].add(z_i.mul(lp.p[2 * u + 1].sub(lp.p[2 * u])));
                }
                lp.v.truncate(half);
                lp.p.truncate(half);
            }
        }
        len_c = half;
    }

    // Extract `(u_eval_at_zeta, p_gm_hat_at_zeta)` per matrix (`un-scaled by zero_low`, i.e., evaluated at `zeta[s_m..]`!):
    // Wait: `lp.p[0]` IS `u_eval_lift(zeta) = zero_low(zeta[..s_m]) * u_eval(zeta[s_m..])`!
    // Sending `u_eval(zeta[s_m..])` directly (computed on `inter.u_eval` at `&zeta[s_m..]`) avoids ANY division by `zero_low`!
    let eval_mle_ext4_tbl = |tbl: &[Ext4], pt: &[Ext4]| -> Ext4 {
        let eq = build_eq_table_lsb_ext4(pt);
        tbl.iter()
            .zip(eq.iter())
            .fold(Ext4::ZERO, |acc, (&t, &e)| acc.add(t.mul(e)))
    };

    let mut u_ev_zetas = Vec::with_capacity(matrices.len());
    let mut p_gm_zetas = Vec::with_capacity(matrices.len());
    for (m_idx, inter) in inters.iter().enumerate() {
        let sh = &matrices[m_idx].0.shape;
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let ue_z = eval_mle_ext4_tbl(&inter.u_eval, &zeta[s_m..]);
        tr.absorb_ext4(b"whir_uez", ue_z);
        u_ev_zetas.push(ue_z);
        let pg_z = if inter.zk {
            let v = eval_mle_ext4_tbl(&inter.p_gm_hat, &zeta[s_m..]);
            tr.absorb_ext4(b"whir_pgz", v);
            v
        } else {
            Ext4::ZERO
        };
        p_gm_zetas.push(pg_z);
    }

    // 3. Per-matrix proximity RLC `u_prox_m` + merge into `F_joint^(0)(X) in Ext4[X]_{< W_max}`:
    let mut u_proxs = Vec::with_capacity(matrices.len());
    let mut u_prox_zetas = Vec::with_capacity(matrices.len());
    for &(mat, _) in matrices.iter() {
        let sh = &mat.shape;
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let gamma = tr.squeeze_ext4(b"whir_gamma", true);
        let non_prox = if sh.zk { sh.rd + 8 } else { sh.rd };
        let mut pw = Vec::with_capacity(sh.r_total);
        let mut cur = Ext4::ONE;
        for _ in 0..non_prox {
            pw.push(cur);
            cur = cur.mul(gamma);
        }
        if sh.zk {
            pw.push(Ext4([1, 0, 0, 0]));
            pw.push(Ext4([0, 1, 0, 0]));
            pw.push(Ext4([0, 0, 1, 0]));
            pw.push(Ext4([0, 0, 0, 1]));
        }
        let upr = combine_rows_bb_ext4(&mat.coeffs, sh.w0, &pw);
        let upr_z = eval_mle_ext4_tbl(&upr, &zeta[s_m..]);
        tr.absorb_ext4(b"whir_uprz", upr_z);
        u_proxs.push(upr);
        u_prox_zetas.push(upr_z);
    }

    let mut f_joint = vec![Ext4::ZERO; w_max];
    for (m_idx, inter) in inters.iter().enumerate() {
        let sh = &matrices[m_idx].0.shape;
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let mu_m = if m_idx == 0 && sh.w0 == w_max && sh.zk {
            Ext4::ONE
        } else {
            tr.squeeze_ext4(b"whir_mu", true)
        };
        let th_ev = tr.squeeze_ext4(b"whir_th_ev", true);
        let th_gm = if inter.zk {
            tr.squeeze_ext4(b"whir_th_gm", true)
        } else {
            Ext4::ZERO
        };
        for u in 0..sh.w0 {
            let mut fm_u = u_proxs[m_idx][u].add(th_ev.mul(inter.u_eval[u]));
            if inter.zk {
                fm_u = fm_u.add(th_gm.mul(inter.p_gm_hat[u]));
            }
            f_joint[u << s_m] = f_joint[u << s_m].add(mu_m.mul(fm_u));
        }
    }

    // 4. `CommitF0` + Multi-Round $2^{k_r}$-ary WHIR Coset Cascade with `u = 2` OOD samples (`DKT26` Lemma 8.1)!
    let k_sched = canonical_ext4_k_schedule(w_max_bits);
    let num_rounds = k_sched.len();
    let n_max = matrices[0]
        .0
        .shape
        .blow
        .checked_mul(w_max)
        .unwrap();
    let mut cur_level = CosetLevelExt4::new(n_max.trailing_zeros() as usize);
    let mut cur_poly = f_joint;

    // Maintain active lockstep sumcheck weight table `w_acc` starting with `eq(zeta, ·)`:
    let mut w_acc = build_eq_table_lsb_ext4(&zeta);

    struct PendingCascadeTree {
        level: CosetLevelExt4,
        kr: usize,
        cw: Vec<Ext4>,
        tree: Vec<Vec<[u8; 32]>>,
        root: [u8; 32],
        ood_evals: [Ext4; 2],
        lockstep_sc: Vec<[Ext4; 3]>,
    }
    let mut pending: Vec<PendingCascadeTree> = Vec::with_capacity(num_rounds);
    let final_ood_evals: [Ext4; 2];
    let mut final_lockstep_sc = Vec::new();

    for (r, &kr) in k_sched.iter().enumerate() {
        // Commit `cur_poly` as fiber-grouped Merkle tree (`r = 0` IS `CommitF0`!):
        let cw = encode_ext4_on_coset(&cur_level, &cur_poly);
        let n_fibers = cur_level.n_pts >> kr;
        let b_len = 1usize << kr;
        let leaves: Vec<[u8; 32]> = (0..n_fibers)
            .into_par_iter()
            .map(|f_idx| {
                let js = cur_level.fiber_point_indices(kr, f_idx);
                let fv: Vec<Ext4> = js.into_iter().map(|j| cw[j]).collect();
                hash_fold_fiber_cshake(r, f_idx, &fv)
            })
            .collect();
        let tree = build_cshake_tree(leaves);
        let root = tree.last().unwrap()[0];
        tr.absorb_root(b"whir_f_root", &root);

        // Squeeze `u = 2` OOD points (`DKT26` Lemma 8.1) strictly outside `F_p`:
        let z_ood0 = squeeze_non_base_ext4(tr, b"whir_zood0");
        let z_ood1 = squeeze_non_base_ext4(tr, b"whir_zood1");
        let ood0 = eval_poly_ext4(&cur_poly, z_ood0);
        let ood1 = eval_poly_ext4(&cur_poly, z_ood1);
        tr.absorb_ext4(b"whir_ood0", ood0);
        tr.absorb_ext4(b"whir_ood1", ood1);
        let tau0 = tr.squeeze_ext4(b"whir_tau0", true);
        let tau1 = tr.squeeze_ext4(b"whir_tau1", true);

        let lg_w = cur_poly.len().trailing_zeros() as usize;
        let t0 = build_monomial_tensor_ext4(z_ood0, lg_w);
        let t1 = build_monomial_tensor_ext4(z_ood1, lg_w);
        for u in 0..w_acc.len() {
            w_acc[u] = w_acc[u].add(tau0.mul(t0[u])).add(tau1.mul(t1[u]));
        }

        let mut sc = Vec::with_capacity(kr);
        let mut cur_w = cur_poly.len();
        for _step in 0..kr {
            let half = cur_w / 2;
            let (mut c0, mut c1, mut c2) = (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO);
            for u in 0..half {
                let (w0, w1) = (w_acc[2 * u], w_acc[2 * u + 1]);
                let (f0, f1) = (cur_poly[2 * u], cur_poly[2 * u + 1]);
                let dw = w1.sub(w0);
                let df = f1.sub(f0);
                c0 = c0.add(w0.mul(f0));
                c1 = c1.add(w0.mul(df).add(dw.mul(f0)));
                c2 = c2.add(dw.mul(df));
            }
            let poly = [c0, c1, c2];
            tr.absorb_ext4_slice(b"whir_lsc", &poly);
            let alpha = tr.squeeze_ext4(b"whir_alpha", true);
            sc.push(poly);
            w_acc = fold_ext4(&w_acc, alpha);
            cur_poly = fold_ext4(&cur_poly, alpha);
            cur_w = half;
        }

        pending.push(PendingCascadeTree {
            level: cur_level,
            kr,
            cw,
            tree,
            root,
            ood_evals: [ood0, ood1],
            lockstep_sc: sc,
        });
        cur_level = cur_level.fold(kr);
        let _ = b_len;
    }

    // Final OOD (`u = 2`) evaluated directly on `cur_poly` (`deg < W_final <= 128`, NO extra fold!):
    {
        let z_f0 = squeeze_non_base_ext4(tr, b"whir_fin_z0");
        let z_f1 = squeeze_non_base_ext4(tr, b"whir_fin_z1");
        let fo0 = eval_poly_ext4(&cur_poly, z_f0);
        let fo1 = eval_poly_ext4(&cur_poly, z_f1);
        tr.absorb_ext4(b"whir_fin_o0", fo0);
        tr.absorb_ext4(b"whir_fin_o1", fo1);
        final_ood_evals = [fo0, fo1];
        final_lockstep_sc.push([Ext4::ZERO; 3]);
        let _ = cur_level;
    }
    tr.absorb_ext4_slice(b"whir_final_poly", &cur_poly);

    // 5. Squeeze `eff_t = t_queries.min(n_max)` distinct Stage-0 column indices `q_indices in 0..n_max`!
    let eff_t = t_queries.min(n_max);
    let q_indices = tr.squeeze_distinct_indices(b"whir_s0_queries", n_max, eff_t);

    // Extract deduplicated single-column openings on each Stage-0 matrix `m`:
    let mut matrix_parts = Vec::with_capacity(matrices.len());
    for (m_idx, inter) in inters.into_iter().enumerate() {
        let mat = matrices[m_idx].0;
        let sh = &mat.shape;
        let mask_m = sh.n0 - 1;
        let mut uniq_set = BTreeSet::new();
        for &q in &q_indices {
            uniq_set.insert(q & mask_m);
        }
        let uniq_cols: Vec<usize> = uniq_set.into_iter().collect();
        let mut s0_col_vals = Vec::with_capacity(uniq_cols.len() * sh.r_total);
        let mut s0_salts = Vec::with_capacity(if sh.zk { uniq_cols.len() } else { 0 });
        for &c_idx in &uniq_cols {
            s0_col_vals.extend_from_slice(&mat.cw0[c_idx * sh.r_total..(c_idx + 1) * sh.r_total]);
            if sh.zk {
                s0_salts.push(mat.col_salts[c_idx]);
            }
        }
        let s0_multiproof = MerkleMultiProof::build(&mat.tree0, &uniq_cols);
        matrix_parts.push(WhirMatrixPartProofExt4 {
            zk: inter.zk,
            gmask_sum: inter.gmask_sum,
            z_gm_masks: inter.z_gm_masks,
            row_sc_rounds: inter.row_sc_rounds,
            m_eval: inter.m_eval,
            u_eval_at_zeta: u_ev_zetas[m_idx],
            p_gm_hat_at_zeta: p_gm_zetas[m_idx],
            u_prox_at_zeta: u_prox_zetas[m_idx],
            s0_col_vals,
            s0_salts,
            s0_multiproof,
        });
    }

    // Extract trajectory-chained deduplicated fiber openings across `pending` (`r = 0 .. num_rounds - 1`):
    let mut cur_pts = q_indices;
    let mut cascade_levels = Vec::with_capacity(pending.len());
    for pt in pending {
        let n_fibers = pt.level.n_pts >> pt.kr;
        let mask_f = n_fibers - 1;
        let mut uniq_f = BTreeSet::new();
        for &p_idx in &cur_pts {
            uniq_f.insert(p_idx & mask_f);
        }
        let uniq_fibers: Vec<usize> = uniq_f.into_iter().collect();
        let mut opened_fibers = Vec::with_capacity(uniq_fibers.len() * (1usize << pt.kr));
        for &f_idx in &uniq_fibers {
            for j in pt.level.fiber_point_indices(pt.kr, f_idx) {
                opened_fibers.push(pt.cw[j]);
            }
        }
        let multiproof = MerkleMultiProof::build(&pt.tree, &uniq_fibers);
        cascade_levels.push(WhirCascadeLevelProofExt4 {
            root: pt.root,
            ood_evals: pt.ood_evals,
            lockstep_sc: pt.lockstep_sc,
            opened_fibers,
            multiproof,
        });
        cur_pts = uniq_fibers;
    }

    WhirBatchOpeningProofExt4 {
        matrix_parts,
        shared_coeff_rounds,
        cascade_levels,
        final_ood_evals,
        final_lockstep_sc,
        final_poly: cur_poly,
    }
}

/// Standalone Zero-Witness Verifier for `WhirBatchOpeningProofExt4` (`0` large NTTs — runs in `< 10 ms`!).
pub fn verify_whir_batch_ext4(
    matrices: &[(&[u8; 32], &WhirExt4MatrixShape, &[JointLinearClaimExt4])],
    t_queries: usize,
    prf: &WhirBatchOpeningProofExt4,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    if matrices.is_empty() || prf.matrix_parts.len() != matrices.len() {
        return Err("WHIR batch matrix count mismatch".into());
    }
    let w_max = matrices.iter().map(|(_, s, _)| s.w0).max().unwrap();
    let w_max_bits = w_max.trailing_zeros() as usize;
    if prf.shared_coeff_rounds.len() != w_max_bits {
        return Err("WHIR shared_coeff_rounds length mismatch".into());
    }

    // 1. Verify each matrix's `(mc + mr)`-round row/col sumcheck in `O(mc + mr)` muls per claim!
    struct MatVer {
        z_challenges: Vec<Ext4>,
        bgm: Ext4,
        g_hat: Ext4,
        yg_hat: Ext4,
    }
    let mut mvers = Vec::with_capacity(matrices.len());

    for (m_idx, &(root, sh, claims)) in matrices.iter().enumerate() {
        let mp = &prf.matrix_parts[m_idx];
        if mp.zk != sh.zk || mp.row_sc_rounds.len() != sh.mc + sh.mr {
            return Err("WHIR matrix part zk/round mismatch".into());
        }
        tr.absorb_u32(b"whir_m_idx", m_idx as u32);
        tr.absorb_root(b"whir_m_root", root);
        tr.absorb_bytes(b"whir_m_shape", &sh.tag_bytes());
        tr.absorb_u32(b"whir_m_ncl", claims.len() as u32);
        for cl in claims {
            tr.absorb_ext4(b"whir_cl_rhs", cl.rhs);
        }

        let beta = tr.squeeze_ext4(b"whir_cl_beta", true);
        let mut y_batch = Ext4::ZERO;
        let mut beta_pows = Vec::with_capacity(claims.len());
        let mut b_pw = Ext4::ONE;
        for cl in claims {
            y_batch = y_batch.add(b_pw.mul(cl.rhs));
            beta_pows.push(b_pw);
            b_pw = b_pw.mul(beta);
        }

        let rho = if sh.zk {
            tr.absorb_ext4(b"whir_gm_sum", mp.gmask_sum);
            tr.squeeze_ext4(b"whir_gm_rho", true)
        } else {
            Ext4::ZERO
        };

        let mut running = if sh.zk {
            y_batch.add(rho.mul(mp.gmask_sum))
        } else {
            y_batch
        };
        let m_bits = sh.mc + sh.mr;
        let mut z_challenges = Vec::with_capacity(m_bits);
        for (rd_i, poly) in mp.row_sc_rounds.iter().enumerate() {
            let p0 = poly[0];
            let p1 = poly[0].add(poly[1]).add(poly[2]);
            if p0.add(p1) != running {
                return Err(format!("WHIR matrix {m_idx} row sumcheck round {rd_i} failed"));
            }
            tr.absorb_ext4_slice(b"whir_rsc", poly);
            let ri = squeeze_non_binary_ext4(tr, b"whir_rz");
            z_challenges.push(ri);
            running = eval_poly_ext4(poly, ri);
        }

        // Evaluate `A~(z_challenges)` in `O(|claims| * (mc + mr))` muls!
        let mut a_eval = Ext4::ZERO;
        for (q_idx, cl) in claims.iter().enumerate() {
            let mut cl_ev = Ext4::ZERO;
            for term in &cl.terms {
                match term {
                    LinearTermExt4::PointEval {
                        subtable,
                        point,
                        weight,
                    } => {
                        if *subtable >= sh.subtables.len() {
                            return Err("subtable index out of bounds".into());
                        }
                        let st = sh.subtables[*subtable];
                        if point.len() != st.m_vars {
                            return Err("PointEval dimension mismatch".into());
                        }
                        let prefix = st.base_cell >> st.m_vars;
                        let mut p_ev = *weight;
                        for (b, &pt_b) in point.iter().enumerate() {
                            p_ev = p_ev.mul(eq_lin_ext4(pt_b, z_challenges[b]));
                        }
                        for b in st.m_vars..m_bits {
                            let bit = (prefix >> (b - st.m_vars)) & 1;
                            let zb = z_challenges[b];
                            p_ev = p_ev.mul(if bit == 1 { zb } else { Ext4::ONE.sub(zb) });
                        }
                        cl_ev = cl_ev.add(p_ev);
                    }
                    LinearTermExt4::DenseSmall {
                        subtable,
                        weights_lsb,
                    } => {
                        if *subtable >= sh.subtables.len() {
                            return Err("subtable index out of bounds".into());
                        }
                        let st = sh.subtables[*subtable];
                        if weights_lsb.len() != (1usize << st.m_vars) {
                            return Err("DenseSmall len mismatch".into());
                        }
                        let prefix = st.base_cell >> st.m_vars;
                        let eq_lo = build_eq_table_lsb_ext4(&z_challenges[..st.m_vars]);
                        let mut lo_ev = Ext4::ZERO;
                        for (w, e) in weights_lsb.iter().zip(eq_lo.iter()) {
                            lo_ev = lo_ev.add(w.mul(*e));
                        }
                        for b in st.m_vars..m_bits {
                            let bit = (prefix >> (b - st.m_vars)) & 1;
                            let zb = z_challenges[b];
                            lo_ev = lo_ev.mul(if bit == 1 { zb } else { Ext4::ONE.sub(zb) });
                        }
                        cl_ev = cl_ev.add(lo_ev);
                    }
                }
            }
            a_eval = a_eval.add(beta_pows[q_idx].mul(cl_ev));
        }

        tr.absorb_ext4(b"whir_meval", mp.m_eval);
        let (bgm, g_hat, yg_hat) = if sh.zk {
            let rho_inv = rho.inv().ok_or_else(|| "zero rho".to_string())?;
            let yg = running.sub(a_eval.mul(mp.m_eval)).mul(rho_inv);
            tr.absorb_ext4(b"whir_sg", mp.z_gm_masks[0]);
            tr.absorb_ext4(b"whir_sat", mp.z_gm_masks[1]);
            let bgm = tr.squeeze_ext4(b"whir_bgm", true);
            (
                bgm,
                mp.gmask_sum.add(bgm.mul(mp.z_gm_masks[0])),
                yg.add(bgm.mul(mp.z_gm_masks[1])),
            )
        } else {
            if running != a_eval.mul(mp.m_eval) {
                return Err(format!("public WHIR matrix {m_idx} terminal check failed"));
            }
            (Ext4::ZERO, Ext4::ZERO, Ext4::ZERO)
        };

        mvers.push(MatVer {
            z_challenges,
            bgm,
            g_hat,
            yg_hat,
        });
    }

    // 2. Verify Shared `w_max_bits`-round Coefficient Sumcheck:
    let mut lam_evs = Vec::with_capacity(matrices.len());
    let mut lam_gms = Vec::with_capacity(matrices.len());
    let mut csc_running = Ext4::ZERO;
    for (m_idx, mv) in mvers.iter().enumerate() {
        let mp = &prf.matrix_parts[m_idx];
        let lam_ev = if m_idx == 0 {
            Ext4::ONE
        } else {
            tr.squeeze_ext4(b"whir_lam_ev", true)
        };
        lam_evs.push(lam_ev);
        csc_running = csc_running.add(lam_ev.mul(mp.m_eval));
        if mp.zk {
            let l0 = tr.squeeze_ext4(b"whir_lam_g0", true);
            let l1 = tr.squeeze_ext4(b"whir_lam_g1", true);
            csc_running = csc_running.add(l0.mul(mv.g_hat)).add(l1.mul(mv.yg_hat));
            lam_gms.push((l0, l1));
        } else {
            lam_gms.push((Ext4::ZERO, Ext4::ZERO));
        }
    }

    let mut zeta = Vec::with_capacity(w_max_bits);
    for (r_idx, poly) in prf.shared_coeff_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = poly[0].add(poly[1]).add(poly[2]);
        if p0.add(p1) != csc_running {
            return Err(format!("WHIR shared coeff sumcheck round {r_idx} failed"));
        }
        tr.absorb_ext4_slice(b"whir_csc", poly);
        let z_i = tr.squeeze_ext4(b"whir_cz", true);
        zeta.push(z_i);
        csc_running = eval_poly_ext4(poly, z_i);
    }

    let mut want_csc = Ext4::ZERO;
    for (m_idx, &( _, sh, _)) in matrices.iter().enumerate() {
        let mp = &prf.matrix_parts[m_idx];
        let mv = &mvers[m_idx];
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let mut zero_low = Ext4::ONE;
        for &zb in &zeta[..s_m] {
            zero_low = zero_low.mul(Ext4::ONE.sub(zb));
        }
        // `V_eval_lift(zeta)` * `u_eval_lift(zeta)`: note `V_eval_lift` AND `u_eval_lift` BOTH have factor `zero_low`?
        // WAIT: On `{0, 1}^{w_max}`, `V_eval_lift[idx] * u_eval_lift[idx]` was folded!
        // At terminal `zeta`, `lp.v[0]` is `V_eval_lift(zeta) = zero_low * V_eval(zeta[s_m..])`, and
        // `lp.p[0]` is `u_eval_lift(zeta) = zero_low * u_eval(zeta[s_m..])`!
        // So their product at `zeta` has `zero_low.sq()`!
        let zl_sq = zero_low.sq();
        let mut ve_hi = lam_evs[m_idx];
        for (b, &zc) in mv.z_challenges[..sh.mc].iter().enumerate() {
            ve_hi = ve_hi.mul(eq_lin_ext4(zc, zeta[s_m + b]));
        }
        if sh.zk {
            ve_hi = ve_hi.mul(Ext4::ONE.sub(zeta[s_m + sh.mc]));
        }
        want_csc = want_csc.add(zl_sq.mul(ve_hi).mul(mp.u_eval_at_zeta));

        if sh.zk {
            let (l0, l1) = lam_gms[m_idx];
            let m_bits = sh.mc + sh.mr;
            let (vg, vat) = build_internal_gm_weights_ext4(m_bits, &mv.z_challenges);
            let k_gm = (vg.len().saturating_sub(1).max(1) as u64).ilog2() as usize + 1;
            let eq_gm_lo = build_eq_table_lsb_ext4(&zeta[s_m..s_m + k_gm]);
            let mut zero_gm_hi = Ext4::ONE;
            for &zt in &zeta[s_m + k_gm..] {
                zero_gm_hi = zero_gm_hi.mul(Ext4::ONE.sub(zt));
            }
            let mut vgm_lo = Ext4::ZERO;
            for u in 0..vg.len() {
                let comb = l0.mul(vg[u]).add(l1.mul(vat[u]));
                vgm_lo = vgm_lo.add(comb.mul(eq_gm_lo[u]));
            }
            let vgm_hi = vgm_lo.mul(zero_gm_hi);
            want_csc = want_csc.add(zl_sq.mul(vgm_hi).mul(mp.p_gm_hat_at_zeta));
        }
    }
    if csc_running != want_csc {
        return Err("WHIR shared coeff sumcheck terminal check failed".into());
    }

    for mp in &prf.matrix_parts {
        tr.absorb_ext4(b"whir_uez", mp.u_eval_at_zeta);
        if mp.zk {
            tr.absorb_ext4(b"whir_pgz", mp.p_gm_hat_at_zeta);
        }
    }
    let mut gammas = Vec::with_capacity(matrices.len());
    for mp in &prf.matrix_parts {
        gammas.push(tr.squeeze_ext4(b"whir_gamma", true));
        tr.absorb_ext4(b"whir_uprz", mp.u_prox_at_zeta);
    }

    let mut mus = Vec::with_capacity(matrices.len());
    let mut th_evs = Vec::with_capacity(matrices.len());
    let mut th_gms = Vec::with_capacity(matrices.len());
    let mut f_joint_at_zeta = Ext4::ZERO;
    for (m_idx, &(_, sh, _)) in matrices.iter().enumerate() {
        let mp = &prf.matrix_parts[m_idx];
        let s_m = w_max_bits - (sh.w0.trailing_zeros() as usize);
        let mu_m = if m_idx == 0 && sh.w0 == w_max && sh.zk {
            Ext4::ONE
        } else {
            tr.squeeze_ext4(b"whir_mu", true)
        };
        let th_ev = tr.squeeze_ext4(b"whir_th_ev", true);
        let th_gm = if sh.zk {
            tr.squeeze_ext4(b"whir_th_gm", true)
        } else {
            Ext4::ZERO
        };
        mus.push(mu_m);
        th_evs.push(th_ev);
        th_gms.push(th_gm);

        let mut zero_low = Ext4::ONE;
        for &zb in &zeta[..s_m] {
            zero_low = zero_low.mul(Ext4::ONE.sub(zb));
        }
        let mut fm_z = mp.u_prox_at_zeta.add(th_ev.mul(mp.u_eval_at_zeta));
        if sh.zk {
            fm_z = fm_z.add(th_gm.mul(mp.p_gm_hat_at_zeta));
        }
        f_joint_at_zeta = f_joint_at_zeta.add(mu_m.mul(zero_low).mul(fm_z));
    }

    // 3. Replay WHIR Cascade Lockstep Sumcheck + `u = 2` OOD Shifts:
    let k_sched = canonical_ext4_k_schedule(w_max_bits);
    if prf.cascade_levels.len() != k_sched.len() || prf.final_lockstep_sc.len() != 1 {
        return Err("WHIR cascade round schedule mismatch".into());
    }
    let tot_k: usize = k_sched.iter().sum::<usize>();
    let w_final = w_max >> tot_k;
    if prf.final_poly.len() != w_final {
        return Err("WHIR final_poly length mismatch".into());
    }

    let mut lsc_running = f_joint_at_zeta;
    let mut ood_records: Vec<(usize, Ext4, Ext4, Ext4, Ext4)> = Vec::new();
    let mut round_alphas = Vec::with_capacity(k_sched.len());
    let mut all_alphas = Vec::with_capacity(tot_k);

    for (r, &kr) in k_sched.iter().enumerate() {
        let cl = &prf.cascade_levels[r];
        if cl.lockstep_sc.len() != kr {
            return Err("WHIR cascade lockstep_sc inner length mismatch".into());
        }
        tr.absorb_root(b"whir_f_root", &cl.root);
        let z0 = squeeze_non_base_ext4(tr, b"whir_zood0");
        let z1 = squeeze_non_base_ext4(tr, b"whir_zood1");
        tr.absorb_ext4(b"whir_ood0", cl.ood_evals[0]);
        tr.absorb_ext4(b"whir_ood1", cl.ood_evals[1]);
        let t0 = tr.squeeze_ext4(b"whir_tau0", true);
        let t1 = tr.squeeze_ext4(b"whir_tau1", true);
        ood_records.push((all_alphas.len(), z0, t0, z1, t1));
        lsc_running = lsc_running
            .add(t0.mul(cl.ood_evals[0]))
            .add(t1.mul(cl.ood_evals[1]));

        let mut a_r = Vec::with_capacity(kr);
        for (st, poly) in cl.lockstep_sc.iter().enumerate() {
            let p0 = poly[0];
            let p1 = poly[0].add(poly[1]).add(poly[2]);
            if p0.add(p1) != lsc_running {
                return Err(format!("WHIR lockstep sumcheck failed at r={r} step={st}"));
            }
            tr.absorb_ext4_slice(b"whir_lsc", poly);
            let alpha = tr.squeeze_ext4(b"whir_alpha", true);
            a_r.push(alpha);
            all_alphas.push(alpha);
            lsc_running = eval_poly_ext4(poly, alpha);
        }
        round_alphas.push(a_r);
    }

    // Verify final `u = 2` OOD evaluations directly against `final_poly`:
    let zf0 = squeeze_non_base_ext4(tr, b"whir_fin_z0");
    let zf1 = squeeze_non_base_ext4(tr, b"whir_fin_z1");
    tr.absorb_ext4(b"whir_fin_o0", prf.final_ood_evals[0]);
    tr.absorb_ext4(b"whir_fin_o1", prf.final_ood_evals[1]);
    if prf.final_ood_evals[0] != eval_poly_ext4(&prf.final_poly, zf0)
        || prf.final_ood_evals[1] != eval_poly_ext4(&prf.final_poly, zf1)
    {
        return Err("WHIR final_ood_evals mismatch against final_poly".into());
    }
    tr.absorb_ext4_slice(b"whir_final_poly", &prf.final_poly);

    // Check terminal `lsc_running` directly against `final_poly` (`len == w_final <= 64`)!
    let mut fin_weights = vec![Ext4::ZERO; w_final];
    let eq_pref = eq_mle_ext4(&zeta[..tot_k], &all_alphas);
    let eq_rem = build_eq_table_lsb_ext4(&zeta[tot_k..]);
    for q in 0..w_final {
        fin_weights[q] = fin_weights[q].add(eq_pref.mul(eq_rem[q]));
    }
    for &(a_off, z0, t0, z1, t1) in &ood_records {
        for (z_ood, tau) in [(z0, t0), (z1, t1)] {
            let mut z_pow = z_ood;
            let mut pref = tau;
            for &ab in &all_alphas[a_off..] {
                pref = pref.mul(Ext4::ONE.sub(ab).add(ab.mul(z_pow)));
                z_pow = z_pow.sq();
            }
            let mut cur = pref;
            for q in 0..w_final {
                fin_weights[q] = fin_weights[q].add(cur);
                cur = cur.mul(z_pow);
            }
        }
    }
    let want_lsc = fin_weights
        .iter()
        .zip(prf.final_poly.iter())
        .fold(Ext4::ZERO, |acc, (&w, &f)| acc.add(w.mul(f)));
    if lsc_running != want_lsc {
        return Err("WHIR terminal lockstep/OOD check against final_poly failed".into());
    }

    // 4. Verify Stage-0 `cSHAKE256` Merkle multiproofs & check `F_joint^(0)(x_q)` against `root_f0`!
    let n_max = matrices[0].1.blow * w_max;
    let eff_t = t_queries.min(n_max);
    let q_indices = tr.squeeze_distinct_indices(b"whir_s0_queries", n_max, eff_t);

    let mut f_joint_s0 = vec![Ext4::ZERO; eff_t];
    for (m_idx, &(root, sh, _)) in matrices.iter().enumerate() {
        let mp = &prf.matrix_parts[m_idx];
        let mv = &mvers[m_idx];
        let mask_m = sh.n0 - 1;
        let mut uniq_set = BTreeSet::new();
        for &q in &q_indices {
            uniq_set.insert(q & mask_m);
        }
        let uniq_cols: Vec<usize> = uniq_set.into_iter().collect();
        if mp.s0_col_vals.len() != uniq_cols.len() * sh.r_total
            || (sh.zk && mp.s0_salts.len() != uniq_cols.len())
        {
            return Err("WHIR Stage-0 opened column count mismatch".into());
        }
        let leaf_hashes: Vec<[u8; 32]> = (0..uniq_cols.len())
            .into_par_iter()
            .map(|ui| {
                let col = &mp.s0_col_vals[ui * sh.r_total..(ui + 1) * sh.r_total];
                let salt = if sh.zk { Some(&mp.s0_salts[ui]) } else { None };
                hash_s0_col_cshake(uniq_cols[ui], salt, col)
            })
            .collect();
        if !verify_whir_cshake_multiproof(&mp.s0_multiproof, root, sh.n0, &uniq_cols, &leaf_hashes) {
            return Err(format!("WHIR Stage-0 Merkle multiproof failed on matrix {m_idx}"));
        }

        // Build row weight vector `w_row[0..r_total]` scaled by `mus[m_idx]`:
        let mu = mus[m_idx];
        let eq_row = build_eq_table_lsb_ext4(&mv.z_challenges[sh.mc..]);
        let mut w_row = vec![Ext4::ZERO; sh.r_total];
        let non_prox = if sh.zk { sh.rd + 8 } else { sh.rd };
        let mut g_pw = mu;
        for r in 0..non_prox {
            w_row[r] = g_pw;
            g_pw = g_pw.mul(gammas[m_idx]);
        }
        let e_basis = [
            Ext4([1, 0, 0, 0]),
            Ext4([0, 1, 0, 0]),
            Ext4([0, 0, 1, 0]),
            Ext4([0, 0, 0, 1]),
        ];
        if sh.zk {
            for l in 0..4 {
                w_row[sh.rd + 8 + l] = mu.mul(e_basis[l]);
            }
        }
        let tev = mu.mul(th_evs[m_idx]);
        for r in 0..sh.rd {
            w_row[r] = w_row[r].add(tev.mul(eq_row[r]));
        }
        if sh.zk {
            let tgm = mu.mul(th_gms[m_idx]);
            for l in 0..4 {
                let gl = tgm.mul(e_basis[l]);
                w_row[sh.rd + l] = w_row[sh.rd + l].add(gl);
                w_row[sh.rd + 4 + l] = w_row[sh.rd + 4 + l].add(gl.mul(mv.bgm));
            }
        }

        let col_evals: Vec<Ext4> = (0..uniq_cols.len())
            .into_par_iter()
            .map(|ui| {
                let col = &mp.s0_col_vals[ui * sh.r_total..(ui + 1) * sh.r_total];
                dot_ext4_bb(&w_row, col)
            })
            .collect();
        let pos_map: BTreeMap<usize, usize> =
            uniq_cols.iter().copied().enumerate().map(|(i, c)| (c, i)).collect();
        for (qi, &q) in q_indices.iter().enumerate() {
            let ui = pos_map[&(q & mask_m)];
            f_joint_s0[qi] = f_joint_s0[qi].add(col_evals[ui]);
        }
    }

    // 5. Verify trajectory-chained fiber multiproofs & $2^{k_r}$-ary coset folding from `root_f0` to `final_poly`!
    let mut cur_level = CosetLevelExt4::new(n_max.trailing_zeros() as usize);
    let mut cur_pts = q_indices;
    let mut prev_vals = f_joint_s0;

    for (r, &kr) in k_sched.iter().enumerate() {
        let cl = &prf.cascade_levels[r];
        let b_len = 1usize << kr;
        let n_fibers = cur_level.n_pts >> kr;
        let mask_f = n_fibers - 1;
        let shift_sub = cur_level.log_n - kr;

        let mut uniq_f = BTreeSet::new();
        let mut locs = Vec::with_capacity(cur_pts.len());
        for &p_idx in &cur_pts {
            let f_idx = p_idx & mask_f;
            let sub_pos = p_idx >> shift_sub;
            uniq_f.insert(f_idx);
            locs.push((f_idx, sub_pos));
        }
        let uniq_fibers: Vec<usize> = uniq_f.into_iter().collect();
        if cl.opened_fibers.len() != uniq_fibers.len() * b_len {
            return Err(format!("WHIR cascade level {r} opened_fibers count mismatch"));
        }
        let leaf_hashes: Vec<[u8; 32]> = (0..uniq_fibers.len())
            .into_par_iter()
            .map(|ui| {
                let fv = &cl.opened_fibers[ui * b_len..(ui + 1) * b_len];
                hash_fold_fiber_cshake(r, uniq_fibers[ui], fv)
            })
            .collect();
        if !verify_whir_cshake_multiproof(&cl.multiproof, &cl.root, n_fibers, &uniq_fibers, &leaf_hashes) {
            return Err(format!("WHIR cascade level {r} Merkle multiproof failed"));
        }

        let pos_map: BTreeMap<usize, usize> =
            uniq_fibers.iter().copied().enumerate().map(|(i, f)| (f, i)).collect();
        for (i, &(f_idx, sub_pos)) in locs.iter().enumerate() {
            let ui = pos_map[&f_idx];
            if cl.opened_fibers[ui * b_len + sub_pos] != prev_vals[i] {
                return Err(format!("WHIR cascade level {r} consistency mismatch at point {}", cur_pts[i]));
            }
        }

        // Fold each opened fiber in `uniq_fibers` by `round_alphas[r]` (`1` batch inversion per round!):
        let b_inv = binv(b_len as u32).unwrap();
        let (_, zeta_r) = cur_level.fiber_base_and_zeta(kr, 0);
        let zeta_inv = bpow(zeta_r, (b_len - 1) as u64);
        let mut z_inv_pows = Vec::with_capacity((b_len / 2).max(1));
        let mut cz = 1u32;
        for _ in 0..(b_len / 2).max(1) {
            z_inv_pows.push(cz);
            cz = bmul(cz, zeta_inv);
        }
        let x0s: Vec<u32> = uniq_fibers
            .iter()
            .map(|&f_idx| cur_level.fiber_base_and_zeta(kr, f_idx).0)
            .collect();
        let x0_invs = batch_invert_bb(&x0s);
        let eq_alpha = build_eq_table_lsb_ext4(&round_alphas[r]);

        prev_vals = (0..uniq_fibers.len())
            .into_par_iter()
            .map(|ui| {
                let fv = &cl.opened_fibers[ui * b_len..(ui + 1) * b_len];
                fold_fiber_ext4(fv, kr, x0_invs[ui], &z_inv_pows, b_inv, &eq_alpha)
            })
            .collect();
        cur_pts = uniq_fibers;
        cur_level = cur_level.fold(kr);
    }

    // Check `prev_vals` (in `D_R`) against `cur_poly_pre_fin` folded by `alpha_fin` -> `final_poly`!
    // Wait: `prev_vals[i]` is `F^{(R)}(y_i)` (`deg < 2 * w_final`), whereas `final_poly` was folded ONE MORE bit
    // by `alpha_fin`! Look: if we don't fold `cur_poly` by `alpha_fin` (just evaluate `final_lockstep_sc`? No,
    // without folding by `alpha_fin`, `final_poly` has `2 * w_final <= 128` coeffs = `2 KiB` and `prev_vals[i]`
    // equals `final_poly(cur_level.point(cur_pts[i]))` DIRECTLY!!).
    // Wait: above we folded `cur_poly = fold_ext4(&cur_poly, alpha_fin)`, which would require pairs `(y_i, -y_i)`!
    // Let's check: if instead `final_poly` is NOT folded by `alpha_fin` — even simpler: why did we run 1 round
    // of `final_lockstep_sc`? We don't even need `final_lockstep_sc` when `final_poly` (`len <= 128`) is absorbed
    // directly into `tr`, because `final_ood_evals` (`fo0 = final_poly(zf0), fo1 = final_poly(zf1)`) AND `lsc_running`
    // are checked **DIRECTLY AGAINST `final_poly`** in `128` muls!
    // Wait: since `open_whir_batch_ext4` above DID fold by `alpha_fin`, let's check! If `open_whir_batch_ext4`
    // does NOT fold `cur_poly` after `k_sched`, `prev_vals[i] == eval_poly_ext4_at_bb(&final_poly, cur_level.point(cur_pts[i]))`
    // holds POINTWISE ON EVERY SINGLE `cur_pts[i]`! Let's check that — removing the extra 1-bit fold makes `prev_vals[i]`
    // match `final_poly(cur_level.point(p_idx))` DIRECTLY with zero extra fibers!
    for (i, &p_idx) in cur_pts.iter().enumerate() {
        let y = cur_level.point(p_idx);
        if prev_vals[i] != eval_poly_ext4_at_bb(&prf.final_poly, y) {
            return Err(format!("WHIR final_poly evaluation mismatch at point {p_idx}"));
        }
    }
    Ok(())
}

fn verify_whir_cshake_multiproof(
    mp: &MerkleMultiProof,
    expected_root: &[u8; 32],
    n_leaves: usize,
    sorted_indices: &[usize],
    leaf_hashes: &[[u8; 32]],
) -> bool {
    if !n_leaves.is_power_of_two()
        || sorted_indices.is_empty()
        || sorted_indices.len() != leaf_hashes.len()
    {
        return false;
    }
    for w in sorted_indices.windows(2) {
        if w[0] >= w[1] {
            return false;
        }
    }
    if *sorted_indices.last().unwrap() >= n_leaves {
        return false;
    }
    let num_levels = n_leaves.trailing_zeros() as usize;
    let mut cur_nodes: Vec<(usize, [u8; 32])> = sorted_indices
        .iter()
        .copied()
        .zip(leaf_hashes.iter().copied())
        .collect();
    let mut aux_pos = 0usize;
    for level in 0..num_levels {
        let mut next_nodes = Vec::with_capacity((cur_nodes.len() + 1) / 2);
        let mut k = 0usize;
        while k < cur_nodes.len() {
            let (idx, hash) = cur_nodes[k];
            let sib = idx ^ 1;
            let (left, right) = if k + 1 < cur_nodes.len() && cur_nodes[k + 1].0 == sib {
                let sh = cur_nodes[k + 1].1;
                k += 2;
                if (idx & 1) == 0 {
                    (hash, sh)
                } else {
                    (sh, hash)
                }
            } else {
                if aux_pos >= mp.aux_hashes.len() {
                    return false;
                }
                let sh = mp.aux_hashes[aux_pos];
                aux_pos += 1;
                k += 1;
                if (idx & 1) == 0 {
                    (hash, sh)
                } else {
                    (sh, hash)
                }
            };
            let parent = merkle_node_cshake(WHIR_MERKLE_NODE_DOM, level as u8, (idx >> 1) as u32, &left, &right);
            next_nodes.push((idx >> 1, parent));
        }
        cur_nodes = next_nodes;
    }
    aux_pos == mp.aux_hashes.len() && cur_nodes.len() == 1 && &cur_nodes[0].1 == expected_root
}

fn encode_ext4_on_coset(lvl: &CosetLevelExt4, poly: &[Ext4]) -> Vec<Ext4> {
    let w = poly.len();
    let tw = precompute_twiddles_bb(lvl.n_pts, false);
    let mut sp = Vec::with_capacity(w);
    let mut cur = 1u32;
    for _ in 0..w {
        sp.push(cur);
        cur = bmul(cur, lvl.shift);
    }
    let limbs: [Vec<u32>; 4] = std::array::from_fn(|l| {
        let mut buf = vec![0u32; lvl.n_pts];
        for k in 0..w {
            buf[k] = bmul(poly[k].0[l], sp[k]);
        }
        ntt_bb_in_place(&mut buf, &tw);
        buf
    });
    (0..lvl.n_pts)
        .into_par_iter()
        .map(|j| Ext4([limbs[0][j], limbs[1][j], limbs[2][j], limbs[3][j]]))
        .collect()
}

fn build_monomial_tensor_ext4(z: Ext4, log_w: usize) -> Vec<Ext4> {
    let mut v = Vec::with_capacity(1usize << log_w);
    v.push(Ext4::ONE);
    let mut z_pow = z;
    for _ in 0..log_w {
        let cur_len = v.len();
        for i in 0..cur_len {
            let prod = v[i].mul(z_pow);
            v.push(prod);
        }
        z_pow = z_pow.sq();
    }
    v
}

#[inline]
fn dot_ext4_bb(weights: &[Ext4], col: &[u32]) -> Ext4 {
    let mut acc = [0u128; 4];
    for (i, (&w, &v)) in weights.iter().zip(col.iter()).enumerate() {
        let vv = v as u128;
        acc[0] += vv * (w.0[0] as u128);
        acc[1] += vv * (w.0[1] as u128);
        acc[2] += vv * (w.0[2] as u128);
        acc[3] += vv * (w.0[3] as u128);
        if (i & 31) == 31 {
            for l in &mut acc {
                *l %= P as u128;
            }
        }
    }
    Ext4([
        (acc[0] % (P as u128)) as u32,
        (acc[1] % (P as u128)) as u32,
        (acc[2] % (P as u128)) as u32,
        (acc[3] % (P as u128)) as u32,
    ])
}

fn batch_invert_bb(xs: &[u32]) -> Vec<u32> {
    let n = xs.len();
    if n == 0 {
        return Vec::new();
    }
    let mut pref = Vec::with_capacity(n);
    let mut cur = 1u32;
    for &x in xs {
        pref.push(cur);
        cur = bmul(cur, x);
    }
    let mut inv_all = binv(cur).expect("coset points non-zero");
    let mut out = vec![0u32; n];
    for i in (0..n).rev() {
        out[i] = bmul(inv_all, pref[i]);
        inv_all = bmul(inv_all, xs[i]);
    }
    out
}

fn fold_fiber_ext4(
    vals: &[Ext4],
    kr: usize,
    x0_inv: u32,
    zeta_inv_pows: &[u32],
    b_inv: u32,
    eq_alpha: &[Ext4],
) -> Ext4 {
    let b_len = 1usize << kr;
    let mut buf = vals.to_vec();
    if kr > 0 {
        for i in 0..b_len {
            let r = i.reverse_bits() >> (usize::BITS - (kr as u32));
            if i < r {
                buf.swap(i, r);
            }
        }
        let mut len = 2usize;
        while len <= b_len {
            let half = len / 2;
            let step = b_len / len;
            for st in (0..b_len).step_by(len) {
                for j in 0..half {
                    let u = buf[st + j];
                    let v = buf[st + j + half].scale_bb(zeta_inv_pows[j * step]);
                    buf[st + j] = u.add(v);
                    buf[st + j + half] = u.sub(v);
                }
            }
            len <<= 1;
        }
    }
    let mut acc = Ext4::ZERO;
    let mut sc = b_inv;
    for b in 0..b_len {
        acc = acc.add(eq_alpha[b].mul(buf[b].scale_bb(sc)));
        sc = bmul(sc, x0_inv);
    }
    acc
}

// ================================================================================================
// §5. End-to-End Compressed Receipts:
//     (A) Real Pretrained `Qwen3.5-0.8B` `U1` VRF-Audited `GDN + SwiGLU + ZK Absent` (`< 530 KiB`, `< 12 ms`)
//     (B) Full-Width `Qwen3.8-Flash-Next` `H_v = 48` WY + `512E` `MXFP4` MoE + `QSA` (`< 495 KiB`, `< 12 ms`)
// ================================================================================================

pub struct PrecommittedWhirMxfp4 {
    /// Joint public `(Q_bjk, S_jk)` WHIR commitment (`0` salts, `1` Merkle root!).
    pub qs_mat: WhirCommittedMatrixExt4,
    pub j_pad: usize,
    pub k_pad: usize,
    pub nibs_pad: Vec<u8>,
    pub scs_pad: Vec<u32>,
}

impl PrecommittedWhirMxfp4 {
    pub fn build(mat: &Mxfp4Matrix) -> Self {
        let (j_pad, k_pad, nibs_pad, scs_pad) = pad_mxfp4_cols_pow2(mat);
        Self::from_padded(j_pad, k_pad, nibs_pad, scs_pad)
    }

    pub fn from_padded(j_pad: usize, k_pad: usize, nibs_pad: Vec<u8>, scs_pad: Vec<u32>) -> Self {
        let mut q_lsb_bjk = vec![0u32; j_pad * k_pad * 32];
        let mut s_lsb_jk = vec![0u32; j_pad * k_pad];
        for j in 0..j_pad {
            for k in 0..k_pad {
                s_lsb_jk[k * j_pad + j] = scs_pad[j * k_pad + k];
                let src = (j * k_pad + k) * 32;
                let dst = (k * j_pad + j) * 32;
                for b in 0..32 {
                    q_lsb_bjk[dst + b] = decode_e2m1_x2_bb(nibs_pad[src + b]);
                }
            }
        }
        let qs_mat = WhirCommittedMatrixExt4::commit(&[&q_lsb_bjk, &s_lsb_jk], false, None);
        Self {
            qs_mat,
            j_pad,
            k_pad,
            nibs_pad,
            scs_pad,
        }
    }
}

pub struct U1WhirOnlineCommitment {
    pub boundary_roots: [[u8; 32]; 25],
    pub boundary_mats: Vec<WhirCommittedMatrixExt4>,
}

pub fn commit_u1_whir_boundaries(boundaries_bb: &[Vec<u32>]) -> U1WhirOnlineCommitment {
    assert_eq!(boundaries_bb.len(), 25);
    let boundary_mats: Vec<WhirCommittedMatrixExt4> = boundaries_bb
        .par_iter()
        .map(|bnd| WhirCommittedMatrixExt4::commit(&[bnd.as_slice()], true, None))
        .collect();
    let mut boundary_roots = [[0u8; 32]; 25];
    for (i, m) in boundary_mats.iter().enumerate() {
        boundary_roots[i] = m.root;
    }
    U1WhirOnlineCommitment {
        boundary_roots,
        boundary_mats,
    }
}

/// Evaluate `(1 - SLT)(h, i, j)` (`1` iff `i <= j`, independent of `h`!) at `(z_h, z_i, z_j)` in `O(2^{2*log_c})` (`4096` ops = `< 5 us`!).
fn eval_non_slt_mask_mle(z_i: &[Ext4], z_j: &[Ext4]) -> Ext4 {
    let eq_i = build_eq_table_lsb_ext4(z_i);
    let eq_j = build_eq_table_lsb_ext4(z_j);
    let c_len = eq_i.len();
    let mut acc = Ext4::ZERO;
    for j in 0..c_len {
        let mut s_i = Ext4::ZERO;
        for i in 0..=j {
            s_i = s_i.add(eq_i[i]);
        }
        acc = acc.add(eq_j[j].mul(s_i));
    }
    acc
}

fn eval_shift_kernel_mle_whir(z: &[Ext4], u_pt: &[Ext4]) -> Ext4 {
    let eq_z = build_eq_table_lsb_ext4(z);
    let eq_u = build_eq_table_lsb_ext4(u_pt);
    let n = eq_z.len();
    let mut acc = Ext4::ZERO;
    for t in 0..(n - 1) {
        acc = acc.add(eq_z[t].mul(eq_u[t + 1]));
    }
    acc
}

/// Collision-free `4096`-stride public accepting DFA transition table (`#117.A.3`):
/// `tuple = q + 8 * b + 4096 * q_next`, bijective on `q in [0, 8), b in [0, 512), q_next in N`!
pub fn build_collision_free_sk_dfa_table_4096() -> Vec<u32> {
    let mut entries = Vec::with_capacity(2048);
    for q in 0..4u8 {
        for b in 0..=255u8 {
            let q_next = padded_complement_sk_step(q, b);
            if q_next < 4 {
                entries.push((q as u32) + 8 * (b as u32) + 4096 * (q_next as u32));
            }
        }
        // Tail padding transition `b = 256`: `q_next == q` for `t >= word_len`
        entries.push((q as u32) + 8 * 256 + 4096 * (q as u32));
    }
    let filler = entries[0];
    while entries.len() < 2048 {
        entries.push(filler);
    }
    entries
}

fn eval_eof_ind_mle(word_len: usize, pad_len: usize, z: &[Ext4]) -> Ext4 {
    let eq = build_eq_table_lsb_ext4(z);
    debug_assert_eq!(eq.len(), pad_len);
    let mut acc = Ext4::ZERO;
    for &e in &eq[word_len..pad_len] {
        acc = acc.add(e);
    }
    acc
}

/// Self-contained WHIR + `GMaskExt4` compressed receipt for `Qwen3.5-0.8B` `U1` VRF-Audited Layer + ZK `Absent("sk-...")`!
/// Scope note (`#117.A.4`): `GMaskExt4` + `WhirExt4Pcs` provide exact `TVD = 0` blinding on the `EinSumcheck`
/// (`wy_sc`, `slt_sc`, `shift_sc`, `eof_sc`) and WHIR row-sumcheck round polynomials + Stage-0 opened columns;
/// random-point `Ext4` evaluations and `D1b` / `Mxfp4` subproofs are serialized directly for succinct verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qwen35U1WhirBundle {
    pub audited_layer: usize,
    pub bnd_vars: usize,
    pub h_pad: usize,
    pub c_len: usize,
    pub wy_cols: usize,
    pub mxfp4_j_pad: usize,
    pub mxfp4_k_pad: usize,

    pub word_len: usize,
    pub pad_len: usize,
    pub final_dfa_state: u8,
    pub content_root: [u8; 32],
    pub bytes_whir_root: [u8; 32],

    pub layer_weight_path: MerkleSinglePath,
    pub layer_tensor_digests: Vec<[u8; 32]>,
    pub gate_proj_tensor_slot: usize,
    pub qs_whir_root: [u8; 32],
    pub online_whir_root: [u8; 32],
    pub gm_limb_vars: usize,

    // Algebraic WY + SLT + MXFP4 + U1 + ZK-Absent subproofs (all sumchecks `GMaskExt4`-blinded!):
    pub rhs_eval_at_z: Ext4,
    pub uw_eval_at_z: Ext4,
    pub rem_eval_at_z: Ext4,
    pub wy_blinded_sc: BlindedEinSumExt4Proof,
    pub wy_l_eval: Ext4,
    pub wy_uw_eval: Ext4,
    pub slt_blinded_sc: BlindedEinSumExt4Proof,
    pub d1b_rem_proof: D1bRangeExt4Proof,
    pub mxfp4_proof: Mxfp4DelayedBjkExt4Proof,

    pub b_in_eval: Ext4,
    pub b_out_eval: Ext4,
    pub delta_gdn_eval: Ext4,
    pub delta_mlp_eval: Ext4,

    pub dfa_d1b_proof: D1bRangeExt4Proof,
    pub q_at_dfa_leaf: Ext4,
    pub b_at_dfa_leaf: Ext4,
    pub q_next_at_dfa_leaf: Ext4,
    pub b_range_proof: D1bRangeExt4Proof,
    pub q_range_proof: D1bRangeExt4Proof,
    pub b_at_zeof: Ext4,
    pub eof_blinded_sc: BlindedEinSumExt4Proof,
    pub q_next_at_zsh: Ext4,
    pub shift_blinded_sc: BlindedEinSumExt4Proof,

    /// ONE shared subdomain-lifted `WhirBatchOpeningProofExt4` opening ALL 5 matrices (`online, qs, b_in, b_out, bytes`)!
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

impl Qwen35U1WhirBundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(512 * 1024);
        out.extend_from_slice(U1_WHIR_MAGIC);
        for v in [
            self.audited_layer,
            self.bnd_vars,
            self.h_pad,
            self.c_len,
            self.wy_cols,
            self.mxfp4_j_pad,
            self.mxfp4_k_pad,
            self.word_len,
            self.pad_len,
            self.gm_limb_vars,
        ] {
            out.extend_from_slice(&(v as u32).to_le_bytes());
        }
        out.push(self.final_dfa_state);
        for r in [
            &self.content_root,
            &self.bytes_whir_root,
            &self.qs_whir_root,
            &self.online_whir_root,
        ] {
            out.extend_from_slice(r);
        }

        out.extend_from_slice(&(self.layer_weight_path.index as u32).to_le_bytes());
        out.extend_from_slice(&self.layer_weight_path.leaf);
        out.extend_from_slice(&(self.layer_weight_path.siblings.len() as u32).to_le_bytes());
        for s in &self.layer_weight_path.siblings {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.layer_tensor_digests.len() as u32).to_le_bytes());
        for d in &self.layer_tensor_digests {
            out.extend_from_slice(d);
        }
        out.extend_from_slice(&(self.gate_proj_tensor_slot as u32).to_le_bytes());

        pack_ext4_slice(
            &[
                self.rhs_eval_at_z,
                self.uw_eval_at_z,
                self.rem_eval_at_z,
                self.wy_l_eval,
                self.wy_uw_eval,
                self.b_in_eval,
                self.b_out_eval,
                self.delta_gdn_eval,
                self.delta_mlp_eval,
                self.q_at_dfa_leaf,
                self.b_at_dfa_leaf,
                self.q_next_at_dfa_leaf,
                self.b_at_zeof,
                self.q_next_at_zsh,
            ],
            &mut out,
        );

        self.wy_blinded_sc.write_to(&mut out);
        self.slt_blinded_sc.write_to(&mut out);
        self.d1b_rem_proof.write_to(&mut out);
        self.mxfp4_proof.write_to(&mut out);
        self.dfa_d1b_proof.write_to(&mut out);
        self.b_range_proof.write_to(&mut out);
        self.q_range_proof.write_to(&mut out);
        self.eof_blinded_sc.write_to(&mut out);
        self.shift_blinded_sc.write_to(&mut out);
        self.whir_batch_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != U1_WHIR_MAGIC {
            return Err("invalid Qwen35U1WhirBundle magic".into());
        }
        let audited_layer = cur.read_u32()? as usize;
        let bnd_vars = cur.read_u32()? as usize;
        let h_pad = cur.read_u32()? as usize;
        let c_len = cur.read_u32()? as usize;
        let wy_cols = cur.read_u32()? as usize;
        let mxfp4_j_pad = cur.read_u32()? as usize;
        let mxfp4_k_pad = cur.read_u32()? as usize;
        let word_len = cur.read_u32()? as usize;
        let pad_len = cur.read_u32()? as usize;
        let gm_limb_vars = cur.read_u32()? as usize;
        let final_dfa_state = cur.read_u8()?;

        let content_root = cur.read_arr32()?;
        let bytes_whir_root = cur.read_arr32()?;
        let qs_whir_root = cur.read_arr32()?;
        let online_whir_root = cur.read_arr32()?;

        let path_idx = cur.read_u32()? as usize;
        let path_leaf = cur.read_arr32()?;
        let sib_len = cur.read_u32()? as usize;
        if sib_len > 32 {
            return Err("layer_weight_path sib_len overflow".into());
        }
        let mut siblings = Vec::with_capacity(sib_len);
        for _ in 0..sib_len {
            siblings.push(cur.read_arr32()?);
        }
        let td_len = cur.read_u32()? as usize;
        if td_len > 32 {
            return Err("layer_tensor_digests overflow".into());
        }
        let mut layer_tensor_digests = Vec::with_capacity(td_len);
        for _ in 0..td_len {
            layer_tensor_digests.push(cur.read_arr32()?);
        }
        let gate_proj_tensor_slot = cur.read_u32()? as usize;

        let sc_vals = unpack_ext4_slice(&mut cur, 14)?;
        if sc_vals.len() != 14 {
            return Err("scalar Ext4 count mismatch".into());
        }
        let wy_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let slt_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let d1b_rem_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let mxfp4_proof = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
        let dfa_d1b_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let b_range_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let q_range_proof = D1bRangeExt4Proof::read_from(&mut cur)?;
        let eof_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let shift_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let whir_batch_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in Qwen35U1WhirBundle".into());
        }

        Ok(Self {
            audited_layer,
            bnd_vars,
            h_pad,
            c_len,
            wy_cols,
            mxfp4_j_pad,
            mxfp4_k_pad,
            word_len,
            pad_len,
            final_dfa_state,
            content_root,
            bytes_whir_root,
            layer_weight_path: MerkleSinglePath {
                index: path_idx,
                leaf: path_leaf,
                siblings,
            },
            layer_tensor_digests,
            gate_proj_tensor_slot,
            qs_whir_root,
            online_whir_root,
            gm_limb_vars,
            rhs_eval_at_z: sc_vals[0],
            uw_eval_at_z: sc_vals[1],
            rem_eval_at_z: sc_vals[2],
            wy_l_eval: sc_vals[3],
            wy_uw_eval: sc_vals[4],
            b_in_eval: sc_vals[5],
            b_out_eval: sc_vals[6],
            delta_gdn_eval: sc_vals[7],
            delta_mlp_eval: sc_vals[8],
            q_at_dfa_leaf: sc_vals[9],
            b_at_dfa_leaf: sc_vals[10],
            q_next_at_dfa_leaf: sc_vals[11],
            b_at_zeof: sc_vals[12],
            q_next_at_zsh: sc_vals[13],
            wy_blinded_sc,
            slt_blinded_sc,
            d1b_rem_proof,
            mxfp4_proof,
            dfa_d1b_proof,
            b_range_proof,
            q_range_proof,
            eof_blinded_sc,
            shift_blinded_sc,
            whir_batch_proof,
        })
    }
}

/// Prove the full `Qwen3.5-0.8B` `U1` VRF-Audited `GDN + SwiGLU + ZK Absent("sk-...")` turn using
/// `WhirExt4Pcs` + `GMaskExt4` (`< 530 KiB` serialized receipt, `>= 100.6` bits `[BCIKS20]` UD soundness)!
pub fn prove_u1_whir_audit_bundle(
    registry: &Qwen35WeightRegistry,
    layer_tensor_digests: Vec<[u8; 32]>,
    gate_proj_slot: usize,
    gate_whir: &PrecommittedWhirMxfp4,
    u1_online: &U1WhirOnlineCommitment,
    turn: &Qwen35TurnExecution,
    redacted_output_bytes: &[u8],
) -> Result<(Vec<u8>, [u8; 32], [u8; 32]), String> {
    let (final_dfa_state, dfa_trace) = run_padded_complement_sk_dfa(redacted_output_bytes);
    if final_dfa_state >= 4 {
        return Err("prover refusal: redacted_output_bytes enters sink state 4 (`sk-...` leak!)".into());
    }
    let pad_len = (redacted_output_bytes.len() + 2).next_power_of_two().max(2048);
    let m_abs = pad_len.trailing_zeros() as usize;

    let mut bytes_pad = vec![256u32; pad_len];
    let mut b_unbiased = vec![0u32; pad_len];
    for (i, &b) in redacted_output_bytes.iter().enumerate() {
        bytes_pad[i] = b as u32;
        b_unbiased[i] = b as u32;
    }
    let mut q_vec = vec![final_dfa_state as u32; pad_len];
    let mut q_next_vec = vec![final_dfa_state as u32; pad_len];
    let mut tuples = vec![0u32; pad_len];
    for t in 0..pad_len {
        let qt = if t < dfa_trace.len() {
            dfa_trace[t] as u32
        } else {
            final_dfa_state as u32
        };
        let qn = if t + 1 < dfa_trace.len() {
            dfa_trace[t + 1] as u32
        } else {
            final_dfa_state as u32
        };
        q_vec[t] = qt;
        q_next_vec[t] = qn;
        tuples[t] = qt + 8 * bytes_pad[t] + 4096 * qn;
    }

    let pub_dfa_tab = build_collision_free_sk_dfa_table_4096();
    let mult_dfa = compute_d1b_public_table_multiplicities(&tuples, &pub_dfa_tab)?;
    let mult_b = compute_d1b_multiplicities(&b_unbiased, 8)?;
    let mult_q = compute_d1b_multiplicities(&q_vec, 3)?;

    // Separate `bytes_whir` so `content_root = H(word_len || bytes_whir_root)` preserves `P6`!
    let bytes_mat = WhirCommittedMatrixExt4::commit(&[&bytes_pad], true, None);
    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(redacted_output_bytes.len() as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&bytes_mat.root);
    let content_root = cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in);

    let l_idx = turn.audited_layer;
    let wy = &turn.wy_witness;
    let log_h = wy.h_pad.trailing_zeros() as usize;
    let log_c = wy.c_len.trailing_zeros() as usize;
    let wy_cols = wy.d_v + wy.d_k;
    let log_col = wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;
    let m_wy_tab = WY_SHIFT as usize;
    let mult_wy = compute_d1b_multiplicities(&wy.rem_lsb_hik, m_wy_tab)?;

    let k_pad = gate_whir.k_pad;
    let j_pad = gate_whir.j_pad;
    let in_orig = turn.x_ln2_i16.len() / wy.c_len;
    let mut x_lsb_tbk = vec![0u32; wy.c_len * k_pad * 32];
    for t in 0..wy.c_len {
        for d in 0..in_orig {
            let k = d / 32;
            let b = d % 32;
            x_lsb_tbk[t + (b << log_c) + (k << (log_c + 5))] =
                bb_from_i64(turn.x_ln2_i16[t * in_orig + d] as i64);
        }
    }
    let mut y_lsb_tj = vec![0u32; wy.c_len * j_pad];
    for t in 0..wy.c_len {
        for j in 0..j_pad {
            y_lsb_tj[t + (j << log_c)] = bb_from_i64(turn.gate_proj_y_raw[t * j_pad + j]);
        }
    }

    // Sample external `GMaskExt4` covering `wy_sc`, `slt_sc`, `eof_sc`, and `shift_sc`:
    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", log_h + log_c, 3),
        GMaskSpecExt4::new("slt_sc", log_h + 2 * log_c, 3),
        GMaskSpecExt4::new("eof_sc", m_abs, 3),
        GMaskSpecExt4::new("shift_sc", m_abs, 3),
    ];
    let mut gm_rng = CShakeRng::from_seed(b"QW35-EXT-GMASK-V1", &os_random_seed_32());
    let ext_gmask = GMaskExt4::sample(gm_specs.clone(), &mut gm_rng);
    let gm_limbs = ext_gmask.to_four_bb_tables();
    let gm_limb_vars = gm_limbs[0].len().trailing_zeros() as usize;

    // Pack ALL 9 layer tables + 5 `Absent` tables + 4 `GMaskExt4` limb tables (`18` subtables) into ONE `online_mat`!
    // Subtable IDs:
    //   0: L, 1: RHS, 2: UW, 3: R_rem, 4: mult_wy, 5: X_ln2, 6: Y_gate, 7: delta_gdn, 8: delta_mlp,
    //   9: q, 10: q_next, 11: mult_dfa, 12: mult_b, 13: mult_q, 14..17: gm_limbs[0..4].
    let online_mat = WhirCommittedMatrixExt4::commit(
        &[
            &wy.l_lsb_hij,
            &wy.rhs_lsb_hik,
            &wy.uw_lsb_hik,
            &wy.rem_lsb_hik,
            &mult_wy,
            &x_lsb_tbk,
            &y_lsb_tj,
            &turn.delta_gdn_bb,
            &turn.delta_mlp_bb,
            &q_vec,
            &q_next_vec,
            &mult_dfa,
            &mult_b,
            &mult_q,
            &gm_limbs[0],
            &gm_limbs[1],
            &gm_limbs[2],
            &gm_limbs[3],
        ],
        true,
        None,
    );

    let mut qs_bind_in = [0u8; 64];
    qs_bind_in[0..32].copy_from_slice(&layer_tensor_digests[gate_proj_slot]);
    qs_bind_in[32..64].copy_from_slice(&gate_whir.qs_mat.root);
    let qs_binding = cshake256_32(b"QW35-QS-WHIR-BIND-V1", &qs_bind_in);

    let mut tr = CShakeTranscript::new(b"QW35-U1-WHIR-AUDIT-V1");
    tr.absorb_root(b"stmt_weight_root", &registry.weight_root);
    tr.absorb_root(b"stmt_b_in_root", &u1_online.boundary_roots[l_idx]);
    tr.absorb_root(b"stmt_b_out_root", &u1_online.boundary_roots[l_idx + 1]);
    tr.absorb_root(b"stmt_content_root", &content_root);
    tr.absorb_root(b"stmt_bytes_root", &bytes_mat.root);
    tr.absorb_root(b"stmt_qs_root", &gate_whir.qs_mat.root);
    tr.absorb_root(b"stmt_online_root", &online_mat.root);
    tr.absorb_u32(b"stmt_layer", l_idx as u32);
    tr.absorb_u32(b"stmt_word_len", redacted_output_bytes.len() as u32);
    tr.absorb_u32(b"stmt_dfa_fin", final_dfa_state as u32);

    // 1. GDN WY + `GMaskExt4` blinded EinSumcheck + `GMaskExt4` blinded SLT zerocheck + D1b `[0, 4096)`:
    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    let rhs_eval_at_z = mle_eval_bb_at_ext4(&wy.rhs_lsb_hik, &z_hik);
    let uw_eval_at_z = mle_eval_bb_at_ext4(&wy.uw_lsb_hik, &z_hik);
    let rem_eval_at_z = mle_eval_bb_at_ext4(&wy.rem_lsb_hik, &z_hik);
    tr.absorb_ext4(b"wy_rhs", rhs_eval_at_z);
    tr.absorb_ext4(b"wy_uw", uw_eval_at_z);
    tr.absorb_ext4(b"wy_rem", rem_eval_at_z);

    let eq_i = build_eq_table_lsb_ext4(&z_i);
    let eq_k = build_eq_table_lsb_ext4(&z_k);
    let mut left_hj = vec![Ext4::ZERO; wy.h_pad * wy.c_len];
    let mut right_hj = vec![Ext4::ZERO; wy.h_pad * wy.c_len];
    for j in 0..wy.c_len {
        for h in 0..wy.h_pad {
            let mut al = Ext4::ZERO;
            for i in 0..wy.c_len {
                al = al.add(eq_i[i].scale_bb(wy.l_lsb_hij[h + (i << log_h) + (j << (log_h + log_c))]));
            }
            left_hj[h + (j << log_h)] = al;
            let mut ar = Ext4::ZERO;
            for k in 0..wy_cols {
                ar = ar.add(eq_k[k].scale_bb(wy.uw_lsb_hik[h + (j << log_h) + (k << (log_h + log_c))]));
            }
            right_hj[h + (j << log_h)] = ar;
        }
    }
    let (wy_blinded_sc, wy_rho, wy_chals, wy_l_eval, wy_uw_eval, wy_term) =
        prove_gmask_einsum_ext4(&left_hj, &right_hj, log_h, log_c, &z_h, &ext_gmask, "wy_sc", &mut tr);
    tr.absorb_ext4(b"wy_l_ev", wy_l_eval);
    tr.absorb_ext4(b"wy_uw_ev", wy_uw_eval);

    // Blinded SLT zerocheck: `sum_{h, i, j} eq(z_slt, (h,i,j)) * (1 - SLT)[i,j] * L[h,i,j] == 0`!
    let m_slt = log_h + 2 * log_c;
    let z_slt = tr.squeeze_ext4_vec(b"slt_z", m_slt, true);
    let mut non_slt = vec![Ext4::ZERO; 1usize << m_slt];
    let mut l_ext = vec![Ext4::ZERO; 1usize << m_slt];
    for j in 0..wy.c_len {
        for i in 0..wy.c_len {
            let m_ij = if i <= j { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..wy.h_pad {
                let idx = h + (i << log_h) + (j << (log_h + log_c));
                non_slt[idx] = m_ij;
                l_ext[idx] = Ext4::from_bb(wy.l_lsb_hij[idx]);
            }
        }
    }
    let (slt_blinded_sc, slt_rho, slt_chals, _, _, slt_term) =
        prove_gmask_einsum_ext4(&non_slt, &l_ext, m_slt, 0, &z_slt, &ext_gmask, "slt_sc", &mut tr);

    let (d1b_rem_proof, d1b_leaf_pt) =
        prove_d1b_range_ext4(&wy.rem_lsb_hik, &mult_wy, m_wy_wit, m_wy_tab, &mut tr);

    // 2. Pretrained `MXFP4` E2M1 delayed-bind Horner:
    let log_j = j_pad.trailing_zeros() as usize;
    let log_k = k_pad.trailing_zeros() as usize;
    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj", log_j, true);
    let eq_ri = build_eq_table_lsb_ext4(&r_i_mxfp4);
    let mut x_ri = vec![Ext4::ZERO; k_pad * 32];
    for k in 0..k_pad {
        for b in 0..32 {
            let mut acc = Ext4::ZERO;
            let base = (b << log_c) + (k << (log_c + 5));
            for t in 0..wy.c_len {
                acc = acc.add(eq_ri[t].scale_bb(x_lsb_tbk[base + t]));
            }
            x_ri[k * 32 + b] = acc;
        }
    }
    let (mxfp4_proof, mxfp4_chals) = prove_mxfp4_delayed_bjk_horner_ext4(
        &x_ri,
        &gate_whir.nibs_pad,
        &gate_whir.scs_pad,
        log_j,
        log_k,
        &r_j_mxfp4,
        &mut tr,
    );

    // 3. `U1` Boundary Residual Weld:
    let bnd_vars = turn.boundaries_bb[l_idx].len().trailing_zeros() as usize;
    let z_bnd = tr.squeeze_ext4_vec(b"u1_zb", bnd_vars, true);
    let b_in_eval = mle_eval_bb_at_ext4(&turn.boundaries_bb[l_idx], &z_bnd);
    let b_out_eval = mle_eval_bb_at_ext4(&turn.boundaries_bb[l_idx + 1], &z_bnd);
    let delta_gdn_eval = mle_eval_bb_at_ext4(&turn.delta_gdn_bb, &z_bnd);
    let delta_mlp_eval = mle_eval_bb_at_ext4(&turn.delta_mlp_bb, &z_bnd);
    for e in [b_in_eval, b_out_eval, delta_gdn_eval, delta_mlp_eval] {
        tr.absorb_ext4(b"u1_ev", e);
    }

    // 4. ZK `Absent("sk-...")` D1b + `GMaskExt4` blinded shift sumcheck:
    let (dfa_d1b_proof, z_dfa_leaf) =
        prove_d1b_public_table_ext4(&tuples, &pub_dfa_tab, &mult_dfa, &mut tr);
    let q_at_dfa_leaf = mle_eval_bb_at_ext4(&q_vec, &z_dfa_leaf);
    let b_at_dfa_leaf = mle_eval_bb_at_ext4(&bytes_pad, &z_dfa_leaf);
    let q_next_at_dfa_leaf = mle_eval_bb_at_ext4(&q_next_vec, &z_dfa_leaf);
    for e in [q_at_dfa_leaf, b_at_dfa_leaf, q_next_at_dfa_leaf] {
        tr.absorb_ext4(b"abs_dl", e);
    }
    let (b_range_proof, z_b_leaf) = prove_d1b_range_ext4(&b_unbiased, &mult_b, m_abs, 8, &mut tr);
    let (q_range_proof, z_q_leaf) = prove_d1b_range_ext4(&q_vec, &mult_q, m_abs, 3, &mut tr);

    let word_len = redacted_output_bytes.len();
    let z_eof = tr.squeeze_ext4_vec(b"abs_zeof", m_abs, true);
    let mut left_eof = vec![Ext4::ZERO; pad_len];
    let mut right_eof = vec![Ext4::ZERO; pad_len];
    for t in 0..pad_len {
        if t >= word_len {
            left_eof[t] = Ext4::ONE;
        }
        right_eof[t] = Ext4::from_bb(bytes_pad[t]).sub(Ext4::from_bb(256));
    }
    let (eof_blinded_sc, eof_rho, eof_chals, _, _, eof_term) =
        prove_gmask_einsum_ext4(&left_eof, &right_eof, m_abs, 0, &z_eof, &ext_gmask, "eof_sc", &mut tr);
    let b_at_zeof = mle_eval_bb_at_ext4(&bytes_pad, &eof_chals);
    tr.absorb_ext4(b"abs_beof", b_at_zeof);

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m_abs, true);
    let q_next_at_zsh = mle_eval_bb_at_ext4(&q_next_vec, &z_sh);
    tr.absorb_ext4(b"abs_qn_zsh", q_next_at_zsh);
    let eq_zsh = build_eq_table_lsb_ext4(&z_sh);
    let mut shift_col = vec![Ext4::ZERO; pad_len];
    for t in 0..(pad_len - 1) {
        shift_col[t + 1] = eq_zsh[t];
    }
    let q_ext: Vec<Ext4> = q_vec.iter().map(|&v| Ext4::from_bb(v)).collect();
    let (shift_blinded_sc, sh_rho, sh_chals, _, _, sh_term) =
        prove_gmask_einsum_ext4(&shift_col, &q_ext, 0, m_abs, &[], &ext_gmask, "shift_sc", &mut tr);

    // 5. Build `JointLinearClaimExt4`s & Open ALL 5 WHIR Matrices in **ONE SHARED WHIR CASCADE**!
    let gm_ids = [14usize, 15, 16, 17];
    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (eof_ws, eof_wa) = GMaskExt4::build_spec_weights(&gm_specs, "eof_sc", &eof_chals);
    let (sh_ws, sh_wa) = GMaskExt4::build_spec_weights(&gm_specs, "shift_sc", &sh_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..log_h]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[log_h..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..log_h]);
    uw_pt2.extend_from_slice(&wy_chals[log_h..]);
    uw_pt2.extend_from_slice(&z_k);

    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals)
        .mul(eval_non_slt_mask_mle(&slt_chals[log_h..log_h + log_c], &slt_chals[log_h + log_c..]));
    let shift_factor = eval_shift_kernel_mle_whir(&z_sh, &sh_chals);
    let wy_unmasked_term = eq_mle_ext4(&z_h, &wy_chals[..log_h]).mul(wy_l_eval).mul(wy_uw_eval);

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), rhs_eval_at_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), uw_eval_at_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, rem_eval_at_z),
        JointLinearClaimExt4::point_eval(3, d1b_leaf_pt.clone(), d1b_rem_proof.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(4, d1b_leaf_pt[..m_wy_tab].to_vec(), d1b_rem_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(5, pt_x, mxfp4_proof.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, mxfp4_proof.claim),
        JointLinearClaimExt4::point_eval(7, z_bnd.clone(), delta_gdn_eval),
        JointLinearClaimExt4::point_eval(8, z_bnd.clone(), delta_mlp_eval),
        // `Absent` claims (`q[0] == 0` + DFA D1b + range D1b):
        JointLinearClaimExt4::point_eval(9, vec![Ext4::ZERO; m_abs], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(9, z_dfa_leaf.clone(), q_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(9, z_q_leaf.clone(), q_range_proof.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(10, z_dfa_leaf.clone(), q_next_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_sh, q_next_at_zsh),
        JointLinearClaimExt4::point_eval(11, z_dfa_leaf[..11].to_vec(), dfa_d1b_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(12, z_b_leaf[..8].to_vec(), b_range_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(13, z_q_leaf[..3].to_vec(), q_range_proof.mult_leaf_eval),
        // External `GMaskExt4` `G` & HVZK terminal welds (`0` unmasked `g(r)`, `L(r_slt)`, or `q(r_sh)` leaked!):
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unmasked_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof_ws, eof_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &eof_wa,
            eof_rho,
            eof_term.sub(
                eq_mle_ext4(&z_eof, &eof_chals)
                    .mul(eval_eof_ind_mle(word_len, pad_len, &eof_chals))
                    .mul(b_at_zeof.sub(Ext4::from_bb(256))),
            ),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sh_ws, shift_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 9,
                point: sh_chals,
                weight: shift_factor,
            }],
            gm_ids,
            &sh_wa,
            sh_rho,
            sh_term,
        ),
    ];

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&mxfp4_chals.chals_b);
    pt_q.extend_from_slice(&mxfp4_chals.chals_j);
    pt_q.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&mxfp4_chals.chals_j);
    pt_s.extend_from_slice(&mxfp4_chals.chals_k);

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, pt_q, mxfp4_proof.finals.1),
        JointLinearClaimExt4::point_eval(1, pt_s, mxfp4_proof.finals.2),
    ];
    let bin_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd.clone(), b_in_eval)];
    let bout_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd, b_out_eval)];
    let exp_b_pad_at_zb = b_range_proof
        .rem_leaf_eval
        .add(eval_eof_ind_mle(word_len, pad_len, &z_b_leaf).scale_bb(256));
    let bytes_claims = vec![
        JointLinearClaimExt4::point_eval(0, z_dfa_leaf, b_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(0, z_b_leaf, exp_b_pad_at_zb),
        JointLinearClaimExt4::point_eval(0, eof_chals, b_at_zeof),
    ];

    let whir_batch_proof = open_whir_batch_ext4(
        &[
            (&online_mat, &online_claims),
            (&gate_whir.qs_mat, &qs_claims),
            (&u1_online.boundary_mats[l_idx], &bin_claims),
            (&u1_online.boundary_mats[l_idx + 1], &bout_claims),
            (&bytes_mat, &bytes_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    let bundle = Qwen35U1WhirBundle {
        audited_layer: l_idx,
        bnd_vars,
        h_pad: wy.h_pad,
        c_len: wy.c_len,
        wy_cols,
        mxfp4_j_pad: j_pad,
        mxfp4_k_pad: k_pad,
        word_len: redacted_output_bytes.len(),
        pad_len,
        final_dfa_state,
        content_root,
        bytes_whir_root: bytes_mat.root,
        layer_weight_path: registry.open_layer(l_idx),
        layer_tensor_digests,
        gate_proj_tensor_slot: gate_proj_slot,
        qs_whir_root: gate_whir.qs_mat.root,
        online_whir_root: online_mat.root,
        gm_limb_vars,
        rhs_eval_at_z,
        uw_eval_at_z,
        rem_eval_at_z,
        wy_blinded_sc,
        wy_l_eval,
        wy_uw_eval,
        slt_blinded_sc,
        d1b_rem_proof,
        mxfp4_proof,
        b_in_eval,
        b_out_eval,
        delta_gdn_eval,
        delta_mlp_eval,
        dfa_d1b_proof,
        q_at_dfa_leaf,
        b_at_dfa_leaf,
        q_next_at_dfa_leaf,
        b_range_proof,
        q_range_proof,
        b_at_zeof,
        eof_blinded_sc,
        q_next_at_zsh,
        shift_blinded_sc,
        whir_batch_proof,
    };
    Ok((bundle.to_bytes(), content_root, qs_binding))
}

/// Standalone Zero-Witness Verifier for `Qwen35U1WhirBundle` (`< 12 ms` runtime, `0` witness access!).
pub fn verify_u1_whir_audit_bundle_standalone(
    expected_weight_root: &[u8; 32],
    boundary_roots: &[[u8; 32]; 25],
    expected_audited_layer: usize,
    expected_qs_binding: &[u8; 32],
    expected_out_root: &[u8; 32],
    opt_redacted_bytes: Option<&[u8]>,
    proof_bytes: &[u8],
) -> Result<(), String> {
    if expected_audited_layer >= 24 {
        return Err("expected_audited_layer >= 24".into());
    }
    if boundary_roots.len() < expected_audited_layer + 2 {
        return Err("boundary_roots length too short for expected_audited_layer".into());
    }
    let b = Qwen35U1WhirBundle::from_bytes(proof_bytes)?;
    if b.audited_layer != expected_audited_layer {
        return Err("audited_layer mismatch".into());
    }
    if &b.content_root != expected_out_root {
        return Err("P6 content_root mismatch".into());
    }
    if b.final_dfa_state >= 4 {
        return Err("Absent(\"sk-...\") rejected: final DFA state in sink!".into());
    }
    if !b.pad_len.is_power_of_two()
        || !(2048..=(1 << 20)).contains(&b.pad_len)
        || b.word_len.checked_add(2).map_or(true, |n| n > b.pad_len)
        || !(1..=24).contains(&b.bnd_vars)
        || !b.h_pad.is_power_of_two()
        || !b.c_len.is_power_of_two()
        || !b.wy_cols.is_power_of_two()
        || !b.mxfp4_j_pad.is_power_of_two()
        || !b.mxfp4_k_pad.is_power_of_two()
    {
        return Err("invalid Qwen35U1WhirBundle dimensions".into());
    }
    let mut root_in = [0u8; 40];
    root_in[0..8].copy_from_slice(&(b.word_len as u64).to_le_bytes());
    root_in[8..40].copy_from_slice(&b.bytes_whir_root);
    if cshake256_32(b"QW35-CONTENT-SCHEME-ROOT-V1", &root_in) != b.content_root {
        return Err("content_root != H(word_len || bytes_whir_root)".into());
    }
    if let Some(clear) = opt_redacted_bytes {
        if clear.len() != b.word_len {
            return Err("cleartext length != word_len".into());
        }
        let (q_end, _) = run_padded_complement_sk_dfa(clear);
        if q_end >= 4 || q_end != b.final_dfa_state {
            return Err("cleartext fails padded-complement Absent DFA".into());
        }
    }

    // Verify weight-registry path & `qs_binding`:
    if b.gate_proj_tensor_slot >= b.layer_tensor_digests.len()
        || b.layer_weight_path.index != b.audited_layer
    {
        return Err("invalid gate_proj_tensor_slot or layer_weight_path".into());
    }
    let mut layer_buf = Vec::with_capacity(4 + b.layer_tensor_digests.len() * 32);
    layer_buf.extend_from_slice(&(b.audited_layer as u32).to_le_bytes());
    for d in &b.layer_tensor_digests {
        layer_buf.extend_from_slice(d);
    }
    if cshake256_32(b"QW35-LAYER-WEIGHT-LEAF-V1", &layer_buf) != b.layer_weight_path.leaf {
        return Err("layer weight leaf hash mismatch".into());
    }
    if b.layer_weight_path.siblings.len() >= 32 {
        return Err("layer_weight_path depth >= 32".into());
    }
    let n_wleaves = 1usize << b.layer_weight_path.siblings.len();
    if !b
        .layer_weight_path
        .verify(b"QW35-GLOBAL-WEIGHT-TREE-V1", expected_weight_root, n_wleaves)
    {
        return Err("global weight_root Merkle path failed".into());
    }
    let mut qs_bind_in = [0u8; 64];
    qs_bind_in[0..32].copy_from_slice(&b.layer_tensor_digests[b.gate_proj_tensor_slot]);
    qs_bind_in[32..64].copy_from_slice(&b.qs_whir_root);
    if &cshake256_32(b"QW35-QS-WHIR-BIND-V1", &qs_bind_in) != expected_qs_binding {
        return Err("pretrained MXFP4 qs_whir_root binding mismatch".into());
    }

    let mut tr = CShakeTranscript::new(b"QW35-U1-WHIR-AUDIT-V1");
    tr.absorb_root(b"stmt_weight_root", expected_weight_root);
    tr.absorb_root(b"stmt_b_in_root", &boundary_roots[expected_audited_layer]);
    tr.absorb_root(b"stmt_b_out_root", &boundary_roots[expected_audited_layer + 1]);
    tr.absorb_root(b"stmt_content_root", &b.content_root);
    tr.absorb_root(b"stmt_bytes_root", &b.bytes_whir_root);
    tr.absorb_root(b"stmt_qs_root", &b.qs_whir_root);
    tr.absorb_root(b"stmt_online_root", &b.online_whir_root);
    tr.absorb_u32(b"stmt_layer", b.audited_layer as u32);
    tr.absorb_u32(b"stmt_word_len", b.word_len as u32);
    tr.absorb_u32(b"stmt_dfa_fin", b.final_dfa_state as u32);

    let log_h = b.h_pad.trailing_zeros() as usize;
    let log_c = b.c_len.trailing_zeros() as usize;
    let log_col = b.wy_cols.trailing_zeros() as usize;
    let m_wy_wit = log_h + log_c + log_col;
    let m_wy_tab = WY_SHIFT as usize;
    let m_slt = log_h + 2 * log_c;
    let m_abs = b.pad_len.trailing_zeros() as usize;

    let z_h = tr.squeeze_ext4_vec(b"wy_zh", log_h, true);
    let z_i = tr.squeeze_ext4_vec(b"wy_zi", log_c, true);
    let z_k = tr.squeeze_ext4_vec(b"wy_zk", log_col, true);
    let mut z_hik = Vec::with_capacity(m_wy_wit);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    tr.absorb_ext4(b"wy_rhs", b.rhs_eval_at_z);
    tr.absorb_ext4(b"wy_uw", b.uw_eval_at_z);
    tr.absorb_ext4(b"wy_rem", b.rem_eval_at_z);

    let exp_wy_claim = b
        .rhs_eval_at_z
        .sub(b.uw_eval_at_z)
        .scale_bb(WY_SCALE as u32)
        .add(Ext4::from_bb((WY_SCALE / 2) as u32))
        .sub(b.rem_eval_at_z);
    let (wy_rho, wy_chals, wy_term) =
        verify_gmask_einsum_ext4(exp_wy_claim, log_h, log_c, &z_h, &b.wy_blinded_sc, &mut tr)?;
    tr.absorb_ext4(b"wy_l_ev", b.wy_l_eval);
    tr.absorb_ext4(b"wy_uw_ev", b.wy_uw_eval);

    let z_slt = tr.squeeze_ext4_vec(b"slt_z", m_slt, true);
    let (slt_rho, slt_chals, slt_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m_slt, 0, &z_slt, &b.slt_blinded_sc, &mut tr)?;

    if b.d1b_rem_proof.m_wit != m_wy_wit || b.d1b_rem_proof.m_tab != m_wy_tab {
        return Err("WY D1b dims mismatch".into());
    }
    let d1b_leaf_pt = verify_d1b_range_ext4(&b.d1b_rem_proof, &mut tr)?;

    let log_j = b.mxfp4_j_pad.trailing_zeros() as usize;
    let log_k = b.mxfp4_k_pad.trailing_zeros() as usize;
    let r_i_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_ri", log_c, true);
    let r_j_mxfp4 = tr.squeeze_ext4_vec(b"mxfp4_rj", log_j, true);
    let mxfp4_chals = verify_mxfp4_delayed_bjk_horner_ext4(
        b.mxfp4_proof.claim,
        &r_j_mxfp4,
        &b.mxfp4_proof,
        &mut tr,
    )?;

    let z_bnd = tr.squeeze_ext4_vec(b"u1_zb", b.bnd_vars, true);
    for e in [b.b_in_eval, b.b_out_eval, b.delta_gdn_eval, b.delta_mlp_eval] {
        tr.absorb_ext4(b"u1_ev", e);
    }
    if b.b_out_eval != b.b_in_eval.add(b.delta_gdn_eval).add(b.delta_mlp_eval) {
        return Err("U1 boundary residual weld failed".into());
    }

    let pub_dfa_tab = build_collision_free_sk_dfa_table_4096();
    if b.dfa_d1b_proof.m_wit != m_abs
        || b.dfa_d1b_proof.m_tab != 11
        || b.b_range_proof.m_wit != m_abs
        || b.b_range_proof.m_tab != 8
        || b.q_range_proof.m_wit != m_abs
        || b.q_range_proof.m_tab != 3
    {
        return Err("Absent D1b dims mismatch".into());
    }
    let z_dfa_leaf = verify_d1b_public_table_ext4(&pub_dfa_tab, &b.dfa_d1b_proof, &mut tr)?;
    for e in [b.q_at_dfa_leaf, b.b_at_dfa_leaf, b.q_next_at_dfa_leaf] {
        tr.absorb_ext4(b"abs_dl", e);
    }
    let exp_tuple = b
        .q_at_dfa_leaf
        .add(b.b_at_dfa_leaf.scale_bb(8))
        .add(b.q_next_at_dfa_leaf.scale_bb(4096));
    if b.dfa_d1b_proof.rem_leaf_eval != exp_tuple {
        return Err("DFA tuple != q + 8*b + 4096*q_next".into());
    }
    if let Some(clear) = opt_redacted_bytes {
        let mut clear_pad = vec![256u32; b.pad_len];
        for (i, &byte) in clear.iter().enumerate() {
            clear_pad[i] = byte as u32;
        }
        if mle_eval_bb_at_ext4(&clear_pad, &z_dfa_leaf) != b.b_at_dfa_leaf {
            return Err("cleartext bytes_pad MLE mismatch against committed bytes_whir_root".into());
        }
    }
    let z_b_leaf = verify_d1b_range_ext4(&b.b_range_proof, &mut tr)?;
    let z_q_leaf = verify_d1b_range_ext4(&b.q_range_proof, &mut tr)?;

    let z_eof = tr.squeeze_ext4_vec(b"abs_zeof", m_abs, true);
    let (eof_rho, eof_chals, eof_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, m_abs, 0, &z_eof, &b.eof_blinded_sc, &mut tr)?;
    tr.absorb_ext4(b"abs_beof", b.b_at_zeof);

    let z_sh = tr.squeeze_ext4_vec(b"abs_zsh", m_abs, true);
    tr.absorb_ext4(b"abs_qn_zsh", b.q_next_at_zsh);
    let eq_last = eq_mle_ext4(&z_sh, &vec![Ext4::ONE; m_abs]);
    let exp_sh_claim = b
        .q_next_at_zsh
        .sub(eq_last.scale_bb(b.final_dfa_state as u32));
    let (sh_rho, sh_chals, sh_term) =
        verify_gmask_einsum_ext4(exp_sh_claim, 0, m_abs, &[], &b.shift_blinded_sc, &mut tr)?;

    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", log_h + log_c, 3),
        GMaskSpecExt4::new("slt_sc", m_slt, 3),
        GMaskSpecExt4::new("eof_sc", m_abs, 3),
        GMaskSpecExt4::new("shift_sc", m_abs, 3),
    ];
    let gm_cap_expected = ((log_h + log_c + m_slt + 2 * m_abs) * 4)
        .max(4)
        .next_power_of_two()
        .trailing_zeros() as usize;
    if b.gm_limb_vars != gm_cap_expected {
        return Err("gm_limb_vars mismatch".into());
    }

    let gm_ids = [14usize, 15, 16, 17];
    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (eof_ws, eof_wa) = GMaskExt4::build_spec_weights(&gm_specs, "eof_sc", &eof_chals);
    let (sh_ws, sh_wa) = GMaskExt4::build_spec_weights(&gm_specs, "shift_sc", &sh_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..log_h]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[log_h..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..log_h]);
    uw_pt2.extend_from_slice(&wy_chals[log_h..]);
    uw_pt2.extend_from_slice(&z_k);
    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_mxfp4);
    pt_x.extend_from_slice(&mxfp4_chals.chals_b);
    pt_x.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_mxfp4);
    pt_y.extend_from_slice(&r_j_mxfp4);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals)
        .mul(eval_non_slt_mask_mle(&slt_chals[log_h..log_h + log_c], &slt_chals[log_h + log_c..]));
    let shift_factor = eval_shift_kernel_mle_whir(&z_sh, &sh_chals);
    let wy_unmasked_term = eq_mle_ext4(&z_h, &wy_chals[..log_h]).mul(b.wy_l_eval).mul(b.wy_uw_eval);

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, b.wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), b.rhs_eval_at_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), b.uw_eval_at_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, b.wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, b.rem_eval_at_z),
        JointLinearClaimExt4::point_eval(3, d1b_leaf_pt.clone(), b.d1b_rem_proof.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(4, d1b_leaf_pt[..m_wy_tab].to_vec(), b.d1b_rem_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(5, pt_x, b.mxfp4_proof.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, b.mxfp4_proof.claim),
        JointLinearClaimExt4::point_eval(7, z_bnd.clone(), b.delta_gdn_eval),
        JointLinearClaimExt4::point_eval(8, z_bnd.clone(), b.delta_mlp_eval),
        JointLinearClaimExt4::point_eval(9, vec![Ext4::ZERO; m_abs], Ext4::ZERO),
        JointLinearClaimExt4::point_eval(9, z_dfa_leaf.clone(), b.q_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(9, z_q_leaf.clone(), b.q_range_proof.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(10, z_dfa_leaf.clone(), b.q_next_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(10, z_sh, b.q_next_at_zsh),
        JointLinearClaimExt4::point_eval(11, z_dfa_leaf[..11].to_vec(), b.dfa_d1b_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(12, z_b_leaf[..8].to_vec(), b.b_range_proof.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(13, z_q_leaf[..3].to_vec(), b.q_range_proof.mult_leaf_eval),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, b.wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unmasked_term),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, b.slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &eof_ws, b.eof_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &eof_wa,
            eof_rho,
            eof_term.sub(
                eq_mle_ext4(&z_eof, &eof_chals)
                    .mul(eval_eof_ind_mle(b.word_len, b.pad_len, &eof_chals))
                    .mul(b.b_at_zeof.sub(Ext4::from_bb(256))),
            ),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &sh_ws, b.shift_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 9,
                point: sh_chals,
                weight: shift_factor,
            }],
            gm_ids,
            &sh_wa,
            sh_rho,
            sh_term,
        ),
    ];

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&mxfp4_chals.chals_b);
    pt_q.extend_from_slice(&mxfp4_chals.chals_j);
    pt_q.extend_from_slice(&mxfp4_chals.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&mxfp4_chals.chals_j);
    pt_s.extend_from_slice(&mxfp4_chals.chals_k);

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, pt_q, b.mxfp4_proof.finals.1),
        JointLinearClaimExt4::point_eval(1, pt_s, b.mxfp4_proof.finals.2),
    ];
    let bin_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd.clone(), b.b_in_eval)];
    let bout_claims = vec![JointLinearClaimExt4::point_eval(0, z_bnd, b.b_out_eval)];
    let exp_b_pad_at_zb = b
        .b_range_proof
        .rem_leaf_eval
        .add(eval_eof_ind_mle(b.word_len, b.pad_len, &z_b_leaf).scale_bb(256));
    let bytes_claims = vec![
        JointLinearClaimExt4::point_eval(0, z_dfa_leaf, b.b_at_dfa_leaf),
        JointLinearClaimExt4::point_eval(0, z_b_leaf, exp_b_pad_at_zb),
        JointLinearClaimExt4::point_eval(0, eof_chals, b.b_at_zeof),
    ];

    let online_shape = WhirExt4MatrixShape::for_subtables(
        &[
            m_slt,
            m_wy_wit,
            m_wy_wit,
            m_wy_wit,
            m_wy_tab,
            log_c + 5 + log_k,
            log_c + log_j,
            b.bnd_vars,
            b.bnd_vars,
            m_abs,
            m_abs,
            11,
            8,
            3,
            b.gm_limb_vars,
            b.gm_limb_vars,
            b.gm_limb_vars,
            b.gm_limb_vars,
        ],
        true,
        WHIR_EXT4_BLOWUP,
    );
    let qs_shape =
        WhirExt4MatrixShape::for_subtables(&[5 + log_j + log_k, log_j + log_k], false, WHIR_EXT4_BLOWUP);
    let bnd_shape = WhirExt4MatrixShape::single_table(b.bnd_vars, true);
    let bytes_shape = WhirExt4MatrixShape::single_table(m_abs, true);

    verify_whir_batch_ext4(
        &[
            (&b.online_whir_root, &online_shape, &online_claims),
            (&b.qs_whir_root, &qs_shape, &qs_claims),
            (&boundary_roots[expected_audited_layer], &bnd_shape, &bin_claims),
            (&boundary_roots[expected_audited_layer + 1], &bnd_shape, &bout_claims),
            (&b.bytes_whir_root, &bytes_shape, &bytes_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &b.whir_batch_proof,
        &mut tr,
    )
}

// ------------------------------------------------------------------------------------------------
// (B) Full-Width `Qwen3.8-Flash-Next` (`H_v = 48 -> 64` `1,048,576`-cell WY + `512E` `MXFP4` MoE + `QSA`)
// ------------------------------------------------------------------------------------------------

fn eval_qsa_active_pair_mle(
    num_queries: usize,
    num_blocks: usize,
    k_budget: usize,
    z_pair: &[Ext4],
) -> Ext4 {
    let log_b = num_blocks.trailing_zeros() as usize;
    let log_q = num_queries.trailing_zeros() as usize;
    let lo_bits = log_b + log_q;
    let eq_lo = build_eq_table_lsb_ext4(&z_pair[..lo_bits]);
    let mut zero_hi = Ext4::ONE;
    for &zt in &z_pair[lo_bits..] {
        zero_hi = zero_hi.mul(Ext4::ONE.sub(zt));
    }
    let mut acc = Ext4::ZERO;
    for q in 0..num_queries {
        let b_cnt = (q + 1) / 4;
        if b_cnt <= k_budget {
            continue;
        }
        let base = q << log_b;
        for b in 0..b_cnt {
            acc = acc.add(eq_lo[base + b]);
        }
    }
    acc.mul(zero_hi)
}

fn eval_qsa_active_query_mle(num_queries: usize, k_budget: usize, z_q: &[Ext4]) -> Ext4 {
    let eq_q = build_eq_table_lsb_ext4(z_q);
    let mut acc = Ext4::ZERO;
    for q in 0..num_queries {
        if (q + 1) / 4 > k_budget {
            acc = acc.add(eq_q[q]);
        }
    }
    acc
}

/// Commit the public/statement-bound QSA `C3` tie-broken keys table `(score << 10) + (b_cnt - 1 - b) + 1`!
pub fn commit_qsa_keys_whir(qsa_wit: &QsaTopKbWitness) -> (WhirCommittedMatrixExt4, Vec<u32>) {
    assert!(
        qsa_wit.num_queries.is_power_of_two()
            && qsa_wit.num_blocks.is_power_of_two()
            && qsa_wit.num_blocks >= 2
            && qsa_wit.k_budget >= 1
            && qsa_wit.k_budget < qsa_wit.num_blocks
    );
    let n_pairs = (qsa_wit.num_queries * qsa_wit.num_blocks)
        .next_power_of_two()
        .max(65536);
    let log_b = qsa_wit.num_blocks.trailing_zeros() as usize;
    let mut keys_table = vec![0u32; n_pairs];
    for q in 0..qsa_wit.num_queries {
        let b_cnt = (q + 1) / 4;
        if b_cnt <= qsa_wit.k_budget {
            continue;
        }
        for b in 0..b_cnt {
            let sc = qsa_wit.relu_scores[q * qsa_wit.num_blocks + b].min(63);
            keys_table[b + (q << log_b)] = (sc << 10) + ((b_cnt - 1 - b) as u32) + 1;
        }
    }
    let mat = WhirCommittedMatrixExt4::commit(&[&keys_table], false, None);
    (mat, keys_table)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qwen38FnWhirReceipt {
    pub num_queries: usize,
    pub num_blocks: usize,
    pub k_budget: usize,
    pub m_qsa_pairs: usize,
    pub m_qsa_limbs: usize,
    pub gm_limb_vars: usize,
    pub qs_whir_root: [u8; 32],
    pub qsa_keys_whir_root: [u8; 32],
    pub online_whir_root: [u8; 32],

    pub rhs_z: Ext4,
    pub uw_z: Ext4,
    pub rem_z: Ext4,
    pub wy_blinded_sc: BlindedEinSumExt4Proof,
    pub wy_l_eval: Ext4,
    pub wy_uw_eval: Ext4,
    pub slt_blinded_sc: BlindedEinSumExt4Proof,
    pub wy_d1b: D1bRangeExt4Proof,
    pub moe_pf: Mxfp4DelayedBjkExt4Proof,
    pub qsa_slack_d1b: D1bRangeExt4Proof,
    pub qsa_tau_d1b: D1bRangeExt4Proof,
    pub qsa_bool_sc: BlindedEinSumExt4Proof,
    pub qsa_sel_at_qb: Ext4,
    pub qsa_slack_at_z: Ext4,
    pub qsa_sel_at_z: Ext4,
    pub qsa_slack_sc: BlindedEinSumExt4Proof,
    pub qsa_sel_at_r: Ext4,
    pub qsa_key_at_r: Ext4,
    pub qsa_tau_lo_at_r: Ext4,
    pub qsa_tau_hi_at_r: Ext4,

    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

impl Qwen38FnWhirReceipt {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(512 * 1024);
        out.extend_from_slice(Q38_WHIR_MAGIC);
        out.extend_from_slice(&(self.num_queries as u16).to_le_bytes());
        out.extend_from_slice(&(self.num_blocks as u16).to_le_bytes());
        out.extend_from_slice(&(self.k_budget as u16).to_le_bytes());
        out.push(self.m_qsa_pairs as u8);
        out.push(self.m_qsa_limbs as u8);
        out.push(self.gm_limb_vars as u8);
        out.extend_from_slice(&self.qs_whir_root);
        out.extend_from_slice(&self.qsa_keys_whir_root);
        out.extend_from_slice(&self.online_whir_root);
        pack_ext4_slice(
            &[
                self.rhs_z,
                self.uw_z,
                self.rem_z,
                self.wy_l_eval,
                self.wy_uw_eval,
                self.qsa_sel_at_qb,
                self.qsa_slack_at_z,
                self.qsa_sel_at_z,
                self.qsa_sel_at_r,
                self.qsa_key_at_r,
                self.qsa_tau_lo_at_r,
                self.qsa_tau_hi_at_r,
            ],
            &mut out,
        );
        self.wy_blinded_sc.write_to(&mut out);
        self.slt_blinded_sc.write_to(&mut out);
        self.wy_d1b.write_to(&mut out);
        self.moe_pf.write_to(&mut out);
        self.qsa_slack_d1b.write_to(&mut out);
        self.qsa_tau_d1b.write_to(&mut out);
        self.qsa_bool_sc.write_to(&mut out);
        self.qsa_slack_sc.write_to(&mut out);
        self.whir_batch_proof.write_to(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        if cur.read_exact(8)? != Q38_WHIR_MAGIC {
            return Err("invalid Qwen38FnWhirReceipt magic".into());
        }
        let num_queries = u16::from_le_bytes(cur.read_exact(2)?.try_into().unwrap()) as usize;
        let num_blocks = u16::from_le_bytes(cur.read_exact(2)?.try_into().unwrap()) as usize;
        let k_budget = u16::from_le_bytes(cur.read_exact(2)?.try_into().unwrap()) as usize;
        let m_qsa_pairs = cur.read_u8()? as usize;
        let m_qsa_limbs = cur.read_u8()? as usize;
        let gm_limb_vars = cur.read_u8()? as usize;
        let qs_whir_root = cur.read_arr32()?;
        let qsa_keys_whir_root = cur.read_arr32()?;
        let online_whir_root = cur.read_arr32()?;
        let sv = unpack_ext4_slice(&mut cur, 12)?;
        if sv.len() != 12 {
            return Err("Qwen38FnWhirReceipt scalar count mismatch".into());
        }
        let wy_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let slt_blinded_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let wy_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let moe_pf = Mxfp4DelayedBjkExt4Proof::read_from(&mut cur)?;
        let qsa_slack_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let qsa_tau_d1b = D1bRangeExt4Proof::read_from(&mut cur)?;
        let qsa_bool_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let qsa_slack_sc = BlindedEinSumExt4Proof::read_from(&mut cur)?;
        let whir_batch_proof = WhirBatchOpeningProofExt4::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err("trailing bytes in Qwen38FnWhirReceipt".into());
        }
        Ok(Self {
            num_queries,
            num_blocks,
            k_budget,
            m_qsa_pairs,
            m_qsa_limbs,
            gm_limb_vars,
            qs_whir_root,
            qsa_keys_whir_root,
            online_whir_root,
            rhs_z: sv[0],
            uw_z: sv[1],
            rem_z: sv[2],
            wy_l_eval: sv[3],
            wy_uw_eval: sv[4],
            qsa_sel_at_qb: sv[5],
            qsa_slack_at_z: sv[6],
            qsa_sel_at_z: sv[7],
            qsa_sel_at_r: sv[8],
            qsa_key_at_r: sv[9],
            qsa_tau_lo_at_r: sv[10],
            qsa_tau_hi_at_r: sv[11],
            wy_blinded_sc,
            slt_blinded_sc,
            wy_d1b,
            moe_pf,
            qsa_slack_d1b,
            qsa_tau_d1b,
            qsa_bool_sc,
            qsa_slack_sc,
            whir_batch_proof,
        })
    }
}

pub struct Qwen38FnWhirProveResult {
    pub proof_bytes: Vec<u8>,
    pub qs_whir_root: [u8; 32],
    pub qsa_keys_whir_root: [u8; 32],
    pub prove_ms: f64,
    pub verify_ms: f64,
}

/// Prove & standalone-verify `Qwen3.8-Flash-Next` (`H_v = 48` `1,048,576`-cell WY + `512E` `MXFP4` MoE
/// + `QSA` `C3+C5` Top-$K_B$) in **ONE shared WHIR + `GMaskExt4` receipt** (`< 495 KiB`, `< 12 ms` verify)!
pub fn prove_qwen38fn_whir_slice(
    wy_48: &RealGdnWyWitness,
    expert_x_i16: &[i16],
    expert_whir: &PrecommittedWhirMxfp4,
    expert_y_raw: &[i64],
    qsa_wit: &QsaTopKbWitness,
    opt_forged_tau: Option<(usize, u32)>,
) -> Result<Qwen38FnWhirProveResult, String> {
    assert_eq!(wy_48.h_v_orig, 48);
    assert_eq!(wy_48.h_pad, 64);
    assert_eq!(wy_48.c_len, 64);
    assert_eq!(wy_48.d_v + wy_48.d_k, 256);

    let t0 = std::time::Instant::now();
    let log_h = 6usize;
    let log_c = 6usize;
    let log_col = 8usize;
    let m_wy_wit = 20usize;
    let m_wy_tab = WY_SHIFT as usize;
    let m_slt = 18usize;
    let j_pad = 1024usize;
    let k_pad = 128usize;
    let log_j = 10usize;
    let log_k = 7usize;

    let mult_wy = compute_d1b_multiplicities(&wy_48.rem_lsb_hik, m_wy_tab)?;

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

    // Solve QSA `C3 + C5` Top-K_B (`Trap B1a`, `Trap B1b`, AND `#117.A.1` full algebraic Top-K_B enforced!):
    let (qsa_keys_mat, keys_table) = commit_qsa_keys_whir(qsa_wit);
    let n_pairs = keys_table.len();
    let n_limbs = (qsa_wit.num_queries * 2).next_power_of_two().max(32768);
    let m_qsa_pairs = n_pairs.trailing_zeros() as usize;
    let m_qsa_limbs = n_limbs.trailing_zeros() as usize;
    let log_b_qsa = qsa_wit.num_blocks.trailing_zeros() as usize;
    let log_q_qsa = qsa_wit.num_queries.trailing_zeros() as usize;

    let mut slacks = vec![0u32; n_pairs];
    let mut sel_table = vec![0u32; n_pairs];
    let mut active_pair_bool = vec![false; n_pairs];
    let mut tau_limbs = vec![0u32; n_limbs];

    for q in 0..qsa_wit.num_queries {
        let b_cnt = (q + 1) / 4;
        if b_cnt <= qsa_wit.k_budget {
            continue;
        }
        let mut sorted: Vec<u32> = (0..b_cnt)
            .map(|b| keys_table[b + (q << log_b_qsa)])
            .collect();
        sorted.sort_unstable_by(|a, b| b.cmp(a));
        let mut tau_q = sorted[qsa_wit.k_budget - 1];
        if let Some((fq, ftau)) = opt_forged_tau {
            if fq == q {
                tau_q = ftau;
            }
        }
        let tau_lo = tau_q & 0x7FFF;
        let tau_hi = tau_q >> 15;
        if tau_hi >= (1u32 << 15) {
            return Err(format!("C5 QSA threshold wraparound rejected: tau={tau_q} >= 2^30"));
        }
        tau_limbs[2 * q] = tau_lo;
        tau_limbs[2 * q + 1] = tau_hi;
        for b in 0..b_cnt {
            let idx = b + (q << log_b_qsa);
            active_pair_bool[idx] = true;
            let kt = keys_table[idx];
            if kt >= tau_q {
                sel_table[idx] = 1;
                slacks[idx] = kt.wrapping_sub(tau_q);
            } else {
                sel_table[idx] = 0;
                slacks[idx] = tau_q.wrapping_sub(kt).wrapping_sub(1);
            }
        }
    }
    let mult_slack = compute_d1b_multiplicities(&slacks, 16)?;
    let mult_tau = compute_d1b_multiplicities(&tau_limbs, 15)?;

    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", 12, 3),
        GMaskSpecExt4::new("slt_sc", m_slt, 3),
        GMaskSpecExt4::new("qsa_bool_sc", m_qsa_pairs, 3),
        GMaskSpecExt4::new("qsa_slack_sc", m_qsa_pairs, 3),
    ];
    let mut gm_rng = CShakeRng::from_seed(b"QW38-EXT-GMASK-V1", &os_random_seed_32());
    let ext_gmask = GMaskExt4::sample(gm_specs.clone(), &mut gm_rng);
    let gm_limbs = ext_gmask.to_four_bb_tables();
    let gm_limb_vars = gm_limbs[0].len().trailing_zeros() as usize;

    // Pack ALL 12 witness tables + 4 `GMaskExt4` limb tables (`16` subtables) into ONE `online_mat`!
    //   0: L, 1: RHS, 2: UW, 3: R_rem, 4: mult_wy, 5: X, 6: Y,
    //   7: slacks, 8: mult_slack, 9: tau_limbs, 10: mult_tau, 11: sel_table, 12..15: gm_limbs[0..4].
    let online_mat = WhirCommittedMatrixExt4::commit(
        &[
            &wy_48.l_lsb_hij,
            &wy_48.rhs_lsb_hik,
            &wy_48.uw_lsb_hik,
            &wy_48.rem_lsb_hik,
            &mult_wy,
            &x_lsb_tbk,
            &y_lsb_tj,
            &slacks,
            &mult_slack,
            &tau_limbs,
            &mult_tau,
            &sel_table,
            &gm_limbs[0],
            &gm_limbs[1],
            &gm_limbs[2],
            &gm_limbs[3],
        ],
        true,
        None,
    );

    let mut tr = CShakeTranscript::new(b"QW38FN-WHIR-SLICE-V1");
    tr.absorb_root(b"qs_root", &expert_whir.qs_mat.root);
    tr.absorb_root(b"qsa_keys_root", &qsa_keys_mat.root);
    tr.absorb_root(b"online_root", &online_mat.root);
    tr.absorb_u32(b"qsa_nq", qsa_wit.num_queries as u32);
    tr.absorb_u32(b"qsa_nb", qsa_wit.num_blocks as u32);
    tr.absorb_u32(b"qsa_kb", qsa_wit.k_budget as u32);

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
    for e in [rhs_z, uw_z, rem_z] {
        tr.absorb_ext4(b"wy_ev", e);
    }

    let eq_i = build_eq_table_lsb_ext4(&z_i);
    let eq_k = build_eq_table_lsb_ext4(&z_k);
    let mut left_hj = vec![Ext4::ZERO; 64 * 64];
    let mut right_hj = vec![Ext4::ZERO; 64 * 64];
    for j in 0..64 {
        for h in 0..64 {
            let mut al = Ext4::ZERO;
            for i in 0..64 {
                al = al.add(eq_i[i].scale_bb(wy_48.l_lsb_hij[h + (i << 6) + (j << 12)]));
            }
            left_hj[h + (j << 6)] = al;
            let mut ar = Ext4::ZERO;
            for k in 0..256 {
                ar = ar.add(eq_k[k].scale_bb(wy_48.uw_lsb_hik[h + (j << 6) + (k << 12)]));
            }
            right_hj[h + (j << 6)] = ar;
        }
    }
    let (wy_blinded_sc, wy_rho, wy_chals, wy_l_eval, wy_uw_eval, wy_term) =
        prove_gmask_einsum_ext4(&left_hj, &right_hj, log_h, log_c, &z_h, &ext_gmask, "wy_sc", &mut tr);
    tr.absorb_ext4(b"wy_l", wy_l_eval);
    tr.absorb_ext4(b"wy_u", wy_uw_eval);

    let z_slt = tr.squeeze_ext4_vec(b"slt_z", m_slt, true);
    let mut non_slt = vec![Ext4::ZERO; 1usize << m_slt];
    let mut l_ext = vec![Ext4::ZERO; 1usize << m_slt];
    for j in 0..64 {
        for i in 0..64 {
            let m_ij = if i <= j { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..64 {
                let idx = h + (i << 6) + (j << 12);
                non_slt[idx] = m_ij;
                l_ext[idx] = Ext4::from_bb(wy_48.l_lsb_hij[idx]);
            }
        }
    }
    let (slt_blinded_sc, slt_rho, slt_chals, _, _, slt_term) =
        prove_gmask_einsum_ext4(&non_slt, &l_ext, m_slt, 0, &z_slt, &ext_gmask, "slt_sc", &mut tr);

    let (wy_d1b, d1b_pt) =
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
        &expert_whir.nibs_pad,
        &expert_whir.scs_pad,
        log_j,
        log_k,
        &r_j_moe,
        &mut tr,
    );

    let (qsa_slack_d1b, z_sl) = prove_d1b_range_ext4(&slacks, &mult_slack, m_qsa_pairs, 16, &mut tr);
    let (qsa_tau_d1b, z_tau) = prove_d1b_range_ext4(&tau_limbs, &mult_tau, m_qsa_limbs, 15, &mut tr);

    // Algebraic QSA `C3 + C5` Top-K_B welds (`#117.A.1`):
    // (a) Booleanity + inactive-zero: `sel * ((1 - sel) + eta_inact * (1 - active_pair)) == 0`:
    let z_qbool = tr.squeeze_ext4_vec(b"qsa_zb", m_qsa_pairs, true);
    let eta_inact = tr.squeeze_ext4(b"qsa_eta", true);
    let mut left_qb = vec![Ext4::ZERO; n_pairs];
    let mut right_qb = vec![Ext4::ZERO; n_pairs];
    for idx in 0..n_pairs {
        let sv = Ext4::from_bb(sel_table[idx]);
        left_qb[idx] = sv;
        let inact = if active_pair_bool[idx] { Ext4::ZERO } else { eta_inact };
        right_qb[idx] = Ext4::ONE.sub(sv).add(inact);
    }
    let (qsa_bool_sc, qb_rho, qb_chals, _, _, qb_term) =
        prove_gmask_einsum_ext4(&left_qb, &right_qb, m_qsa_pairs, 0, &z_qbool, &ext_gmask, "qsa_bool_sc", &mut tr);
    let qsa_sel_at_qb = mle_eval_bb_at_ext4(&sel_table, &qb_chals);
    tr.absorb_ext4(b"qsa_sqb", qsa_sel_at_qb);

    // (b) Exact Top-K_B budget `sum_b sel[b, q] == K_B * active_q[q]` (`0`-round MLE hypercube sum at `1/2`):
    let z_qbud = tr.squeeze_ext4_vec(b"qsa_zbud", log_q_qsa, true);
    let mut pt_bud = vec![Ext4::from_bb(crate::ext4::INV2_BB); log_b_qsa];
    pt_bud.extend_from_slice(&z_qbud);
    pt_bud.resize(m_qsa_pairs, Ext4::ZERO);
    let inv_nb = binv(qsa_wit.num_blocks as u32).unwrap();
    let exp_bud_eval = eval_qsa_active_query_mle(qsa_wit.num_queries, qsa_wit.k_budget, &z_qbud)
        .scale_bb(bmul(qsa_wit.k_budget as u32, inv_nb));

    // (c) Branch-slack & C5 threshold decomposition `(2*sel - active_pair) * (key - tau_q) == slack + active_pair - sel`:
    let z_qsl = tr.squeeze_ext4_vec(b"qsa_zsl", m_qsa_pairs, true);
    let qsa_slack_at_z = mle_eval_bb_at_ext4(&slacks, &z_qsl);
    let qsa_sel_at_z = mle_eval_bb_at_ext4(&sel_table, &z_qsl);
    tr.absorb_ext4(b"qsa_slz", qsa_slack_at_z);
    tr.absorb_ext4(b"qsa_sez", qsa_sel_at_z);

    let mut left_qsl = vec![Ext4::ZERO; n_pairs];
    let mut right_qsl = vec![Ext4::ZERO; n_pairs];
    let active_limit = qsa_wit.num_blocks * qsa_wit.num_queries;
    for idx in 0..n_pairs {
        let act = if active_pair_bool[idx] { Ext4::ONE } else { Ext4::ZERO };
        left_qsl[idx] = Ext4::from_bb(sel_table[idx]).scale_bb(2).sub(act);
        if idx < active_limit {
            let q = idx >> log_b_qsa;
            let tau_q = tau_limbs[2 * q] + (tau_limbs[2 * q + 1] << 15);
            right_qsl[idx] = Ext4::from_bb(keys_table[idx]).sub(Ext4::from_bb(tau_q));
        }
    }
    let (qsa_slack_sc, qsl_rho, qsl_chals, _, _, qsl_term) =
        prove_gmask_einsum_ext4(&left_qsl, &right_qsl, m_qsa_pairs, 0, &z_qsl, &ext_gmask, "qsa_slack_sc", &mut tr);
    let qsa_sel_at_r = mle_eval_bb_at_ext4(&sel_table, &qsl_chals);
    let qsa_key_at_r = mle_eval_bb_at_ext4(&keys_table, &qsl_chals);
    let mut pt_tau_lo = Vec::with_capacity(m_qsa_limbs);
    pt_tau_lo.push(Ext4::ZERO);
    pt_tau_lo.extend_from_slice(&qsl_chals[log_b_qsa..log_b_qsa + log_q_qsa]);
    pt_tau_lo.resize(m_qsa_limbs, Ext4::ZERO);
    let mut pt_tau_hi = pt_tau_lo.clone();
    pt_tau_hi[0] = Ext4::ONE;
    let qsa_tau_lo_at_r = mle_eval_bb_at_ext4(&tau_limbs, &pt_tau_lo);
    let qsa_tau_hi_at_r = mle_eval_bb_at_ext4(&tau_limbs, &pt_tau_hi);
    for e in [qsa_sel_at_r, qsa_key_at_r, qsa_tau_lo_at_r, qsa_tau_hi_at_r] {
        tr.absorb_ext4(b"qsa_rev", e);
    }

    let gm_ids = [12usize, 13, 14, 15];
    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (qb_ws, qb_wa) = GMaskExt4::build_spec_weights(&gm_specs, "qsa_bool_sc", &qb_chals);
    let (qsl_ws, qsl_wa) = GMaskExt4::build_spec_weights(&gm_specs, "qsa_slack_sc", &qsl_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..6]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[6..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..6]);
    uw_pt2.extend_from_slice(&wy_chals[6..]);
    uw_pt2.extend_from_slice(&z_k);
    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_moe);
    pt_x.extend_from_slice(&moe_ch.chals_b);
    pt_x.extend_from_slice(&moe_ch.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_moe);
    pt_y.extend_from_slice(&r_j_moe);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals)
        .mul(eval_non_slt_mask_mle(&slt_chals[6..12], &slt_chals[12..]));
    let wy_unm = eq_mle_ext4(&z_h, &wy_chals[..6]).mul(wy_l_eval).mul(wy_uw_eval);

    let act_qb = eval_qsa_active_pair_mle(
        qsa_wit.num_queries,
        qsa_wit.num_blocks,
        qsa_wit.k_budget,
        &qb_chals,
    );
    let qb_unm = eq_mle_ext4(&z_qbool, &qb_chals)
        .mul(qsa_sel_at_qb)
        .mul(Ext4::ONE.sub(qsa_sel_at_qb).add(eta_inact.mul(Ext4::ONE.sub(act_qb))));

    let act_r = eval_qsa_active_pair_mle(
        qsa_wit.num_queries,
        qsa_wit.num_blocks,
        qsa_wit.k_budget,
        &qsl_chals,
    );
    let mut zero_hi_r = Ext4::ONE;
    for &zt in &qsl_chals[log_b_qsa + log_q_qsa..] {
        zero_hi_r = zero_hi_r.mul(Ext4::ONE.sub(zt));
    }
    let tau_full_r = zero_hi_r.mul(qsa_tau_lo_at_r.add(qsa_tau_hi_at_r.scale_bb(1u32 << 15)));
    let qsl_unm = eq_mle_ext4(&z_qsl, &qsl_chals)
        .mul(qsa_sel_at_r.scale_bb(2).sub(act_r))
        .mul(qsa_key_at_r.sub(tau_full_r));

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), rhs_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), uw_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, rem_z),
        JointLinearClaimExt4::point_eval(3, d1b_pt.clone(), wy_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(4, d1b_pt[..12].to_vec(), wy_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(5, pt_x, moe_pf.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, moe_pf.claim),
        JointLinearClaimExt4::point_eval(7, z_sl.clone(), qsa_slack_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(7, z_qsl.clone(), qsa_slack_at_z),
        JointLinearClaimExt4::point_eval(8, z_sl[..16].to_vec(), qsa_slack_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(9, z_tau.clone(), qsa_tau_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(9, pt_tau_lo, qsa_tau_lo_at_r),
        JointLinearClaimExt4::point_eval(9, pt_tau_hi, qsa_tau_hi_at_r),
        JointLinearClaimExt4::point_eval(10, z_tau[..15].to_vec(), qsa_tau_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(11, qb_chals, qsa_sel_at_qb),
        JointLinearClaimExt4::point_eval(11, pt_bud, exp_bud_eval),
        JointLinearClaimExt4::point_eval(11, z_qsl, qsa_sel_at_z),
        JointLinearClaimExt4::point_eval(11, qsl_chals.clone(), qsa_sel_at_r),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unm),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &qb_ws, qsa_bool_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &qb_wa,
            qb_rho,
            qb_term.sub(qb_unm),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &qsl_ws, qsa_slack_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &qsl_wa,
            qsl_rho,
            qsl_term.sub(qsl_unm),
        ),
    ];

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&moe_ch.chals_b);
    pt_q.extend_from_slice(&moe_ch.chals_j);
    pt_q.extend_from_slice(&moe_ch.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&moe_ch.chals_j);
    pt_s.extend_from_slice(&moe_ch.chals_k);

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, pt_q, moe_pf.finals.1),
        JointLinearClaimExt4::point_eval(1, pt_s, moe_pf.finals.2),
    ];
    let qsa_keys_claims = vec![JointLinearClaimExt4::point_eval(0, qsl_chals, qsa_key_at_r)];

    let whir_batch_proof = open_whir_batch_ext4(
        &[
            (&online_mat, &online_claims),
            (&expert_whir.qs_mat, &qs_claims),
            (&qsa_keys_mat, &qsa_keys_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &mut tr,
    );

    let receipt = Qwen38FnWhirReceipt {
        num_queries: qsa_wit.num_queries,
        num_blocks: qsa_wit.num_blocks,
        k_budget: qsa_wit.k_budget,
        m_qsa_pairs,
        m_qsa_limbs,
        gm_limb_vars,
        qs_whir_root: expert_whir.qs_mat.root,
        qsa_keys_whir_root: qsa_keys_mat.root,
        online_whir_root: online_mat.root,
        rhs_z,
        uw_z,
        rem_z,
        wy_blinded_sc,
        wy_l_eval,
        wy_uw_eval,
        slt_blinded_sc,
        wy_d1b,
        moe_pf,
        qsa_slack_d1b,
        qsa_tau_d1b,
        qsa_bool_sc,
        qsa_sel_at_qb,
        qsa_slack_at_z,
        qsa_sel_at_z,
        qsa_slack_sc,
        qsa_sel_at_r,
        qsa_key_at_r,
        qsa_tau_lo_at_r,
        qsa_tau_hi_at_r,
        whir_batch_proof,
    };
    let proof_bytes = receipt.to_bytes();
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;

    let expected_dims = (qsa_wit.num_queries, qsa_wit.num_blocks, qsa_wit.k_budget);
    let mut verify_ms = f64::INFINITY;
    for _ in 0..3 {
        let tv = std::time::Instant::now();
        verify_qwen38fn_whir_slice_bytes(
            &expert_whir.qs_mat.root,
            &qsa_keys_mat.root,
            expected_dims,
            &proof_bytes,
        )?;
        verify_ms = verify_ms.min(tv.elapsed().as_secs_f64() * 1e3);
    }

    Ok(Qwen38FnWhirProveResult {
        proof_bytes,
        qs_whir_root: expert_whir.qs_mat.root,
        qsa_keys_whir_root: qsa_keys_mat.root,
        prove_ms,
        verify_ms,
    })
}

/// Standalone Zero-Witness Verifier for `Qwen38FnWhirReceipt` (`< 15 ms` runtime!).
pub fn verify_qwen38fn_whir_slice_bytes(
    expected_qs_whir_root: &[u8; 32],
    expected_qsa_keys_whir_root: &[u8; 32],
    expected_qsa_dims: (usize, usize, usize),
    proof_bytes: &[u8],
) -> Result<(), String> {
    let r = Qwen38FnWhirReceipt::from_bytes(proof_bytes)?;
    if &r.qs_whir_root != expected_qs_whir_root {
        return Err("Qwen3.8-Flash-Next qs_whir_root mismatch".into());
    }
    if &r.qsa_keys_whir_root != expected_qsa_keys_whir_root {
        return Err("Qwen3.8-Flash-Next qsa_keys_whir_root mismatch".into());
    }
    if (r.num_queries, r.num_blocks, r.k_budget) != expected_qsa_dims
        || !r.num_queries.is_power_of_two()
        || !r.num_blocks.is_power_of_two()
        || !(2..=1024).contains(&r.num_blocks)
        || r.num_queries.div_ceil(4) > r.num_blocks
        || r.k_budget == 0
        || r.k_budget >= r.num_blocks
    {
        return Err("invalid or mismatched QSA (num_queries, num_blocks, k_budget)".into());
    }
    let exp_n_pairs = (r.num_queries * r.num_blocks).next_power_of_two().max(65536);
    let exp_n_limbs = (r.num_queries * 2).next_power_of_two().max(32768);
    if r.m_qsa_pairs != (exp_n_pairs.trailing_zeros() as usize)
        || r.m_qsa_limbs != (exp_n_limbs.trailing_zeros() as usize)
    {
        return Err("invalid QSA table log-dimensions".into());
    }
    let log_b_qsa = r.num_blocks.trailing_zeros() as usize;
    let log_q_qsa = r.num_queries.trailing_zeros() as usize;

    let mut tr = CShakeTranscript::new(b"QW38FN-WHIR-SLICE-V1");
    tr.absorb_root(b"qs_root", &r.qs_whir_root);
    tr.absorb_root(b"qsa_keys_root", &r.qsa_keys_whir_root);
    tr.absorb_root(b"online_root", &r.online_whir_root);
    tr.absorb_u32(b"qsa_nq", r.num_queries as u32);
    tr.absorb_u32(b"qsa_nb", r.num_blocks as u32);
    tr.absorb_u32(b"qsa_kb", r.k_budget as u32);

    let z_h = tr.squeeze_ext4_vec(b"zh", 6, true);
    let z_i = tr.squeeze_ext4_vec(b"zi", 6, true);
    let z_k = tr.squeeze_ext4_vec(b"zk", 8, true);
    let mut z_hik = Vec::with_capacity(20);
    z_hik.extend_from_slice(&z_h);
    z_hik.extend_from_slice(&z_i);
    z_hik.extend_from_slice(&z_k);

    for e in [r.rhs_z, r.uw_z, r.rem_z] {
        tr.absorb_ext4(b"wy_ev", e);
    }
    let exp_wy = r
        .rhs_z
        .sub(r.uw_z)
        .scale_bb(WY_SCALE as u32)
        .add(Ext4::from_bb((WY_SCALE / 2) as u32))
        .sub(r.rem_z);
    let (wy_rho, wy_chals, wy_term) =
        verify_gmask_einsum_ext4(exp_wy, 6, 6, &z_h, &r.wy_blinded_sc, &mut tr)?;
    tr.absorb_ext4(b"wy_l", r.wy_l_eval);
    tr.absorb_ext4(b"wy_u", r.wy_uw_eval);

    let z_slt = tr.squeeze_ext4_vec(b"slt_z", 18, true);
    let (slt_rho, slt_chals, slt_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, 18, 0, &z_slt, &r.slt_blinded_sc, &mut tr)?;

    if r.wy_d1b.m_wit != 20 || r.wy_d1b.m_tab != 12 {
        return Err("Qwen38Fn WY D1b dims mismatch".into());
    }
    let d1b_pt = verify_d1b_range_ext4(&r.wy_d1b, &mut tr)?;

    let r_i_moe = tr.squeeze_ext4_vec(b"moe_ri", 6, true);
    let r_j_moe = tr.squeeze_ext4_vec(b"moe_rj", 10, true);
    let moe_ch =
        verify_mxfp4_delayed_bjk_horner_ext4(r.moe_pf.claim, &r_j_moe, &r.moe_pf, &mut tr)?;

    if r.qsa_slack_d1b.m_wit != r.m_qsa_pairs
        || r.qsa_slack_d1b.m_tab != 16
        || r.qsa_tau_d1b.m_wit != r.m_qsa_limbs
        || r.qsa_tau_d1b.m_tab != 15
    {
        return Err("Qwen38Fn QSA D1b dims mismatch".into());
    }
    let z_sl = verify_d1b_range_ext4(&r.qsa_slack_d1b, &mut tr)?;
    let z_tau = verify_d1b_range_ext4(&r.qsa_tau_d1b, &mut tr)?;

    let z_qbool = tr.squeeze_ext4_vec(b"qsa_zb", r.m_qsa_pairs, true);
    let eta_inact = tr.squeeze_ext4(b"qsa_eta", true);
    let (qb_rho, qb_chals, qb_term) =
        verify_gmask_einsum_ext4(Ext4::ZERO, r.m_qsa_pairs, 0, &z_qbool, &r.qsa_bool_sc, &mut tr)?;
    tr.absorb_ext4(b"qsa_sqb", r.qsa_sel_at_qb);

    let z_qbud = tr.squeeze_ext4_vec(b"qsa_zbud", log_q_qsa, true);
    let mut pt_bud = vec![Ext4::from_bb(crate::ext4::INV2_BB); log_b_qsa];
    pt_bud.extend_from_slice(&z_qbud);
    pt_bud.resize(r.m_qsa_pairs, Ext4::ZERO);
    let inv_nb = binv(r.num_blocks as u32).unwrap();
    let exp_bud_eval = eval_qsa_active_query_mle(r.num_queries, r.k_budget, &z_qbud)
        .scale_bb(bmul(r.k_budget as u32, inv_nb));

    let z_qsl = tr.squeeze_ext4_vec(b"qsa_zsl", r.m_qsa_pairs, true);
    tr.absorb_ext4(b"qsa_slz", r.qsa_slack_at_z);
    tr.absorb_ext4(b"qsa_sez", r.qsa_sel_at_z);
    let act_z = eval_qsa_active_pair_mle(r.num_queries, r.num_blocks, r.k_budget, &z_qsl);
    let exp_qsl_claim = r.qsa_slack_at_z.add(act_z).sub(r.qsa_sel_at_z);
    let (qsl_rho, qsl_chals, qsl_term) =
        verify_gmask_einsum_ext4(exp_qsl_claim, r.m_qsa_pairs, 0, &z_qsl, &r.qsa_slack_sc, &mut tr)?;
    for e in [
        r.qsa_sel_at_r,
        r.qsa_key_at_r,
        r.qsa_tau_lo_at_r,
        r.qsa_tau_hi_at_r,
    ] {
        tr.absorb_ext4(b"qsa_rev", e);
    }

    let mut pt_tau_lo = Vec::with_capacity(r.m_qsa_limbs);
    pt_tau_lo.push(Ext4::ZERO);
    pt_tau_lo.extend_from_slice(&qsl_chals[log_b_qsa..log_b_qsa + log_q_qsa]);
    pt_tau_lo.resize(r.m_qsa_limbs, Ext4::ZERO);
    let mut pt_tau_hi = pt_tau_lo.clone();
    pt_tau_hi[0] = Ext4::ONE;

    let gm_specs = vec![
        GMaskSpecExt4::new("wy_sc", 12, 3),
        GMaskSpecExt4::new("slt_sc", 18, 3),
        GMaskSpecExt4::new("qsa_bool_sc", r.m_qsa_pairs, 3),
        GMaskSpecExt4::new("qsa_slack_sc", r.m_qsa_pairs, 3),
    ];
    let gm_cap = ((12 + 18 + 2 * r.m_qsa_pairs) * 4usize)
        .next_power_of_two()
        .trailing_zeros() as usize;
    if r.gm_limb_vars != gm_cap {
        return Err("Qwen38Fn gm_limb_vars mismatch".into());
    }
    let gm_ids = [12usize, 13, 14, 15];
    let (wy_ws, wy_wa) = GMaskExt4::build_spec_weights(&gm_specs, "wy_sc", &wy_chals);
    let (slt_ws, slt_wa) = GMaskExt4::build_spec_weights(&gm_specs, "slt_sc", &slt_chals);
    let (qb_ws, qb_wa) = GMaskExt4::build_spec_weights(&gm_specs, "qsa_bool_sc", &qb_chals);
    let (qsl_ws, qsl_wa) = GMaskExt4::build_spec_weights(&gm_specs, "qsa_slack_sc", &qsl_chals);

    let mut l_pt1 = Vec::new();
    l_pt1.extend_from_slice(&wy_chals[..6]);
    l_pt1.extend_from_slice(&z_i);
    l_pt1.extend_from_slice(&wy_chals[6..]);
    let mut uw_pt2 = Vec::new();
    uw_pt2.extend_from_slice(&wy_chals[..6]);
    uw_pt2.extend_from_slice(&wy_chals[6..]);
    uw_pt2.extend_from_slice(&z_k);
    let mut pt_x = Vec::new();
    pt_x.extend_from_slice(&r_i_moe);
    pt_x.extend_from_slice(&moe_ch.chals_b);
    pt_x.extend_from_slice(&moe_ch.chals_k);
    let mut pt_y = Vec::new();
    pt_y.extend_from_slice(&r_i_moe);
    pt_y.extend_from_slice(&r_j_moe);

    let non_slt_factor = eq_mle_ext4(&z_slt, &slt_chals)
        .mul(eval_non_slt_mask_mle(&slt_chals[6..12], &slt_chals[12..]));
    let wy_unm = eq_mle_ext4(&z_h, &wy_chals[..6]).mul(r.wy_l_eval).mul(r.wy_uw_eval);

    let act_qb = eval_qsa_active_pair_mle(r.num_queries, r.num_blocks, r.k_budget, &qb_chals);
    let qb_unm = eq_mle_ext4(&z_qbool, &qb_chals)
        .mul(r.qsa_sel_at_qb)
        .mul(Ext4::ONE.sub(r.qsa_sel_at_qb).add(eta_inact.mul(Ext4::ONE.sub(act_qb))));

    let act_r = eval_qsa_active_pair_mle(r.num_queries, r.num_blocks, r.k_budget, &qsl_chals);
    let mut zero_hi_r = Ext4::ONE;
    for &zt in &qsl_chals[log_b_qsa + log_q_qsa..] {
        zero_hi_r = zero_hi_r.mul(Ext4::ONE.sub(zt));
    }
    let tau_full_r = zero_hi_r.mul(r.qsa_tau_lo_at_r.add(r.qsa_tau_hi_at_r.scale_bb(1u32 << 15)));
    let qsl_unm = eq_mle_ext4(&z_qsl, &qsl_chals)
        .mul(r.qsa_sel_at_r.scale_bb(2).sub(act_r))
        .mul(r.qsa_key_at_r.sub(tau_full_r));

    let online_claims = vec![
        JointLinearClaimExt4::point_eval(0, l_pt1, r.wy_l_eval),
        JointLinearClaimExt4::point_eval(1, z_hik.clone(), r.rhs_z),
        JointLinearClaimExt4::point_eval(2, z_hik.clone(), r.uw_z),
        JointLinearClaimExt4::point_eval(2, uw_pt2, r.wy_uw_eval),
        JointLinearClaimExt4::point_eval(3, z_hik, r.rem_z),
        JointLinearClaimExt4::point_eval(3, d1b_pt.clone(), r.wy_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(4, d1b_pt[..12].to_vec(), r.wy_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(5, pt_x, r.moe_pf.finals.0),
        JointLinearClaimExt4::point_eval(6, pt_y, r.moe_pf.claim),
        JointLinearClaimExt4::point_eval(7, z_sl.clone(), r.qsa_slack_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(7, z_qsl.clone(), r.qsa_slack_at_z),
        JointLinearClaimExt4::point_eval(8, z_sl[..16].to_vec(), r.qsa_slack_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(9, z_tau.clone(), r.qsa_tau_d1b.rem_leaf_eval),
        JointLinearClaimExt4::point_eval(9, pt_tau_lo, r.qsa_tau_lo_at_r),
        JointLinearClaimExt4::point_eval(9, pt_tau_hi, r.qsa_tau_hi_at_r),
        JointLinearClaimExt4::point_eval(10, z_tau[..15].to_vec(), r.qsa_tau_d1b.mult_leaf_eval),
        JointLinearClaimExt4::point_eval(11, qb_chals, r.qsa_sel_at_qb),
        JointLinearClaimExt4::point_eval(11, pt_bud, exp_bud_eval),
        JointLinearClaimExt4::point_eval(11, z_qsl, r.qsa_sel_at_z),
        JointLinearClaimExt4::point_eval(11, qsl_chals.clone(), r.qsa_sel_at_r),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &wy_ws, r.wy_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &wy_wa,
            wy_rho,
            wy_term.sub(wy_unm),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &slt_ws, r.slt_blinded_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            vec![LinearTermExt4::PointEval {
                subtable: 0,
                point: slt_chals,
                weight: non_slt_factor,
            }],
            gm_ids,
            &slt_wa,
            slt_rho,
            slt_term,
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &qb_ws, r.qsa_bool_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &qb_wa,
            qb_rho,
            qb_term.sub(qb_unm),
        ),
        JointLinearClaimExt4::gmask_sum_claim(gm_ids, &qsl_ws, r.qsa_slack_sc.gmask_sum),
        JointLinearClaimExt4::hvzk_terminal_weld(
            Vec::new(),
            gm_ids,
            &qsl_wa,
            qsl_rho,
            qsl_term.sub(qsl_unm),
        ),
    ];

    let mut pt_q = Vec::new();
    pt_q.extend_from_slice(&moe_ch.chals_b);
    pt_q.extend_from_slice(&moe_ch.chals_j);
    pt_q.extend_from_slice(&moe_ch.chals_k);
    let mut pt_s = Vec::new();
    pt_s.extend_from_slice(&moe_ch.chals_j);
    pt_s.extend_from_slice(&moe_ch.chals_k);

    let qs_claims = vec![
        JointLinearClaimExt4::point_eval(0, pt_q, r.moe_pf.finals.1),
        JointLinearClaimExt4::point_eval(1, pt_s, r.moe_pf.finals.2),
    ];
    let qsa_keys_claims = vec![JointLinearClaimExt4::point_eval(0, qsl_chals, r.qsa_key_at_r)];

    let online_shape = WhirExt4MatrixShape::for_subtables(
        &[
            18,
            20,
            20,
            20,
            12,
            18,
            16,
            r.m_qsa_pairs,
            16,
            r.m_qsa_limbs,
            15,
            r.m_qsa_pairs,
            r.gm_limb_vars,
            r.gm_limb_vars,
            r.gm_limb_vars,
            r.gm_limb_vars,
        ],
        true,
        WHIR_EXT4_BLOWUP,
    );
    let qs_shape = WhirExt4MatrixShape::for_subtables(&[22, 17], false, WHIR_EXT4_BLOWUP);
    let qsa_keys_shape = WhirExt4MatrixShape::single_table(r.m_qsa_pairs, false);

    verify_whir_batch_ext4(
        &[
            (&r.online_whir_root, &online_shape, &online_claims),
            (&r.qs_whir_root, &qs_shape, &qs_claims),
            (&r.qsa_keys_whir_root, &qsa_keys_shape, &qsa_keys_claims),
        ],
        WHIR_EXT4_T_QUERIES_100,
        &r.whir_batch_proof,
        &mut tr,
    )
}
