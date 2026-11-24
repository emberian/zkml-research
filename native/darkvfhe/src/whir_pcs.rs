//! Multi-round `WHIR` / BaseFold $2^k$-ary Coset-NTT PCS (`WhirPcs61` over $\mathbb{F}_{p_0^3}$,
//! $|\mathbb{F}_{p_0^3}| > 2^{182.99}$) + `GMask61` Full-Transcript Univariate Sumcheck HVZK +
//! Self-Contained `HoistedWhirBundle` Prover & Verifier for `HoistedB61` + `D1b` LogUp-GKR.
//!
//! ### Key Upgrades Over 1-Step `succinct_pcs`
//! 1. **`GMask61` Full-Transcript Sumcheck HVZK (`darkproof::gmask` lifted to 61-bit `Ext3`)**:
//!    - Packs separable degree-$d$ masking polynomials $g(x) = \sum_{j=0}^{\ell-1} g_j(x_j)$ (`g_j` over
//!      $\mathbb{F}_{p_0^3}$) into blinded slots/rows of the committed witness PCS;
//!    - Sends masked hypercube sum $M = S + \rho G$ ($G = 2^{\ell-1} \sum_j (g_j(0) + g_j(1))$) and
//!      masked round polynomials $\tilde{s}_i(t) = s_i(t) + \rho g_{\text{round}, i}(t)$, achieving
//!      exact $\mathrm{TVD} = 0$ witness-independent uniform round messages;
//!    - Supports both external `SlotLinearClaim` discharge (`GMask61::append_slot_claims`) and built-in
//!      internal sumcheck blinding inside `WhirCommittedPcs61` (using a dedicated `Z_gm` rank-preserving
//!      one-time pad so the inner-product reduction reveals zero extra constraints on $g$'s coefficients).
//! 2. **Multi-Round $2^k$-ary `WHIR` / BaseFold Coset Folding (`k_fold in {2, 3}`, `blow = 4`, OOD DEEP Shift)**:
//!    - Eliminates transmitting raw length-$W$ (`16,384`–`2,097,152`) `Ext3` vectors `u_eval` / `u_prox`
//!      in the clear (`3–22 MiB`!), folding down to degree $< W_{\text{final}} \le 64..256$ (`1.5–6 KiB`);
//!    - Enforces out-of-domain (`OOD`) evaluation shifts via inversion-free Ruffini quotient folding
//!      $\hat{f}^{(r)}(X) = f^{(r)}(X) + \beta_{\text{deep}, r} \frac{f^{(r)}(X) - y_{\text{ood}, r}}{X - z_{\text{ood}, r}}$
//!      paired with trajectory-chained, deduplicated coset-fiber SHA-256 Merkle multiproofs calibrated for
//!      **$\ge 128$-bit provable `[BCIKS20]` Unique-Decoding (`130.1b`) & `[DKT26]` Thm 5.12 MCA (`185.3b`)**
//!      soundness (`t_queries = 192` at $\rho = 1/4$, or `t_queries = 312` for `129.5b` `[AHIV17]` $d/3$ UD);
//!    - Supports **Joint Two-Matrix Cascade Merging** (`witness_pcs` + persistent `a_pcs`) when shapes
//!      share column geometry `mc`, paying the multi-round WHIR cascade only **once** per proof!

use crate::cert::{compute_statement_digest, ct2_handle, ct3_handle, derive_fs_point};
use crate::digits::{DigitCols, DirectDigitSpec, ExactGarnerSpec, LiftMode};
use crate::logup_gkr::{
    count_multiplicities_parallel, prove_logup_gkr_with_mults, verify_logup_gkr, FractionTreeProof,
    GkrLayerProof, LogUpConfig, LogUpGkrProof, TABLE_LOG2, TABLE_SIZE,
};
use crate::rns_hoist::{Ct3, HoistedEngine, PrecomputedCt};
use crate::succinct_pcs::{
    bitlen_usize, multiproof_needed, radix2_ntt_natural, ByteReader, CosetDomain, Ext3, Ext3Field,
    PcsRng, PcsTranscript, SlotLinearClaim,
};
use crate::{FastPrime61, HoistedParams};
use darkstep::arith::invmod;
use darkstep::bfv::Ct;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

/// Default trajectory query count at `blow = 4` (`rate = 1/4`):
/// - `[BCIKS20]` Unique Decoding (`theta = 3/8 - 2^-12`): `192 * 0.67751 = 130.08 bits > 128 bits`!
/// - `[DKT26]` Thm 5.12 Zeroth-Order Johnson MCA (`a = 0.5 + 0.5/41`): `192 * 0.96523 = 185.32 bits`
///   (`E_0 / |Ext3| < 2^{-140} << 2^{-128}`)!
pub const WHIR_T_QUERIES_128: usize = 192;
/// Classical `[AHIV17]` `d/3` (`delta = 1/4`) trajectory query count (`312 * 0.41504 = 129.49 bits`).
pub const WHIR_T_QUERIES_AHIV_128: usize = 312;
pub const WHIR_BLOWUP: usize = 4;
pub const WHIR_NUM_ZK_DATA_ROWS: usize = 4;
/// `3` rows for internal `GMask61` + `3` rows for `Z_gm` rank-preserving pad + `3` rows for `P_prox` WHIR mask.
pub const WHIR_EXTRA_EXT3_MASK_ROWS: usize = 9;

pub const HOISTED_WHIR_MAGIC: &[u8; 8] = b"DVFHEWH1";
pub const HOISTED_WHIR_VERSION: u32 = 1;

// ================================================================================================
// §1. Compact Bit-Stream Packing & Canonical Unpacking (`61`-bit & `58`-bit Field/Subsum Arrays)
// ================================================================================================

pub fn pack_u64_bits_le(vals: &[u64], bits: usize, out: &mut Vec<u8>) {
    assert!((1..=64).contains(&bits));
    out.extend_from_slice(&(vals.len() as u32).to_le_bytes());
    out.push(bits as u8);
    let total_bits = vals.len() * bits;
    let byte_len = total_bits.div_ceil(8);
    let start = out.len();
    out.resize(start + byte_len, 0u8);
    let dst = &mut out[start..];
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let mut bit_pos = 0usize;
    for &raw in vals {
        let v = raw & mask;
        debug_assert_eq!(v, raw, "value overflows {bits}-bit packing bound");
        let byte_idx = bit_pos >> 3;
        let bit_off = bit_pos & 7;
        let cur: u128 = (v as u128) << bit_off;
        let bytes = cur.to_le_bytes();
        let write_n = ((bits + bit_off + 7) >> 3).min(16);
        for k in 0..write_n {
            dst[byte_idx + k] |= bytes[k];
        }
        bit_pos += bits;
    }
}

pub fn unpack_u64_bits_le(
    cur: &mut ByteReader<'_>,
    expected_bits: usize,
    max_len: usize,
    modulus_excl: u64,
) -> Result<Vec<u64>, String> {
    let len = cur.read_u32()? as usize;
    let bits = cur.read_u8()? as usize;
    if bits != expected_bits || len > max_len {
        return Err(format!(
            "packed array header mismatch (bits={bits}, expected={expected_bits}, len={len})"
        ));
    }
    let total_bits = len
        .checked_mul(bits)
        .ok_or_else(|| "bit length overflow".to_string())?;
    let byte_len = total_bits.div_ceil(8);
    let raw = cur.take(byte_len)?;

    let mask: u128 = if bits == 64 {
        u64::MAX as u128
    } else {
        (1u128 << bits) - 1
    };
    let mut out = Vec::with_capacity(len);
    let mut bit_pos = 0usize;
    for _ in 0..len {
        let byte_idx = bit_pos >> 3;
        let bit_off = bit_pos & 7;
        let read_n = (byte_len - byte_idx).min(16);
        let mut buf = [0u8; 16];
        buf[..read_n].copy_from_slice(&raw[byte_idx..byte_idx + read_n]);
        let val = ((u128::from_le_bytes(buf) >> bit_off) & mask) as u64;
        if val >= modulus_excl {
            return Err(format!(
                "non-canonical packed integer {val} >= {modulus_excl}"
            ));
        }
        out.push(val);
        bit_pos += bits;
    }
    // Check unused trailing bits in final byte are zero (canonical encoding):
    let rem_bits = total_bits & 7;
    if rem_bits != 0 && !raw.is_empty() {
        let last = raw[byte_len - 1];
        if (last >> rem_bits) != 0 {
            return Err("non-zero trailing padding bits in packed stream".into());
        }
    }
    Ok(out)
}

pub fn pack_ext3_slice(ef_p: u64, xs: &[Ext3], out: &mut Vec<u8>) {
    let _ = ef_p;
    let mut flat = Vec::with_capacity(xs.len() * 3);
    for e in xs {
        flat.push(e[0]);
        flat.push(e[1]);
        flat.push(e[2]);
    }
    pack_u64_bits_le(&flat, 61, out);
}

pub fn unpack_ext3_slice(
    cur: &mut ByteReader<'_>,
    max_ext_len: usize,
    p: u64,
) -> Result<Vec<Ext3>, String> {
    let flat = unpack_u64_bits_le(cur, 61, max_ext_len * 3, p)?;
    if flat.len() % 3 != 0 {
        return Err("packed Ext3 slice length not divisible by 3".into());
    }
    Ok(flat.chunks_exact(3).map(|c| [c[0], c[1], c[2]]).collect())
}

// ================================================================================================
// §2. `GMask61`: Separable Degree-$d$ Univariate Sumcheck Blinding over `Ext3` (`TVD == 0` HVZK)
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GMaskSpec61 {
    pub name: String,
    pub num_rounds: usize,
    pub deg: usize,
}

impl GMaskSpec61 {
    pub fn new(name: impl Into<String>, num_rounds: usize, deg: usize) -> Self {
        assert!(num_rounds >= 1 && deg >= 1);
        GMaskSpec61 {
            name: name.into(),
            num_rounds,
            deg,
        }
    }
}

/// Separable masking polynomial family $g_{\text{name}}(x_0, \dots, x_{\ell-1}) = \sum_{j=0}^{\ell-1} g_j(x_j)$,
/// where $g_j(t) = \sum_{k=0}^{d} c_{j, k} t^k \in \mathbb{F}_{p^3}[t]_{\le d}$.
///
/// ### Algebraic HVZK Theorem
/// For any $\ell \ge 1$ and $d \ge 2$, the linear map sending $\{c_{j,0..d}\}_{j=0}^{\ell-1} \in (\mathbb{F}_{p^3})^{\ell(d+1)}$
/// to $\big(G,\; (\tilde{s}_i(0), [t^2]\tilde{s}_i, \dots, [t^d]\tilde{s}_i)_{i=0}^{\ell-1}\big) \in (\mathbb{F}_{p^3})^{1 + d\ell}$
/// has full row rank $1 + d\ell \le (d + 1)\ell$ (leaving $\ell - 1 \ge 0$ spare degrees of freedom),
/// while $\tilde{s}_i(0) + \tilde{s}_i(1) = \tilde{s}_{i-1}(r_{i-1})$ and $\tilde{s}_{\ell-1}(r_{\ell-1}) = F(r) + \rho g(r)$
/// hold by exact telescoping.
#[derive(Clone, Debug)]
pub struct GMask61 {
    pub ef: Ext3Field,
    pub specs: Vec<GMaskSpec61>,
    offsets: BTreeMap<String, (usize, usize, usize)>, // name -> (ext_offset, num_rounds, deg)
    pub coeffs: Vec<Ext3>,
}

impl GMask61 {
    pub fn sample(ef: Ext3Field, specs: Vec<GMaskSpec61>, rng: &mut PcsRng) -> Self {
        let mut offsets = BTreeMap::new();
        let mut total_ext = 0usize;
        for sp in &specs {
            assert!(
                !offsets.contains_key(&sp.name),
                "duplicate GMaskSpec61 name {}",
                sp.name
            );
            offsets.insert(sp.name.clone(), (total_ext, sp.num_rounds, sp.deg));
            total_ext += sp.num_rounds * (sp.deg + 1);
        }
        let mut raw_fp = vec![0u64; total_ext * 3];
        rng.fill_fp_row(&ef.fp, 0x474D_4153_4B36_3100, &mut raw_fp);
        let coeffs: Vec<Ext3> = raw_fp.chunks_exact(3).map(|c| [c[0], c[1], c[2]]).collect();
        GMask61 {
            ef,
            specs,
            offsets,
            coeffs,
        }
    }

    #[inline]
    pub fn num_fp_cells(&self) -> usize {
        self.coeffs.len() * 3
    }

    /// Required number of $N$-sized slots (`N = 2^log_n`) to pack all `GMask61` basefield cells into a witness PCS.
    #[inline]
    pub fn num_slots(&self, n_slot: usize) -> usize {
        self.num_fp_cells().div_ceil(n_slot)
    }

    /// Pack all `GMask61` basefield cells into `dst[0 .. num_slots * n_slot]` (zero-padded in the tail of the last slot).
    pub fn write_to_slots(&self, dst: &mut [u64], n_slot: usize) {
        let need = self.num_slots(n_slot) * n_slot;
        assert!(dst.len() >= need);
        dst[..need].fill(0);
        for (i, c) in self.coeffs.iter().enumerate() {
            dst[3 * i] = c[0];
            dst[3 * i + 1] = c[1];
            dst[3 * i + 2] = c[2];
        }
    }

    #[inline]
    fn poly_slice(&self, name: &str, j: usize) -> &[Ext3] {
        let &(off, l, deg) = self.offsets.get(name).expect("unknown GMask61 spec");
        assert!(j < l);
        let st = off + j * (deg + 1);
        &self.coeffs[st..st + deg + 1]
    }

    /// Compute $G = \sum_{x \in \{0,1\}^\ell} g(x) = 2^{\ell - 1} \sum_{j=0}^{\ell - 1} (g_j(0) + g_j(1))$.
    pub fn hypercube_sum(&self, name: &str) -> Ext3 {
        let &(_, l, _) = self.offsets.get(name).expect("unknown GMask61 spec");
        let scale = self.ef.fp.pow(2, (l - 1) as u64);
        let mut sum_01 = self.ef.zero();
        for j in 0..l {
            let c = self.poly_slice(name, j);
            // g_j(0) = c[0]; g_j(1) = sum_{k=0}^deg c[k]
            let mut gj1 = self.ef.zero();
            for &ck in c {
                gj1 = self.ef.add(gj1, ck);
            }
            sum_01 = self.ef.add(sum_01, self.ef.add(c[0], gj1));
        }
        self.ef.scale(sum_01, scale)
    }

    /// Evaluate $g(r_0, \dots, r_{\ell - 1}) = \sum_{j=0}^{\ell - 1} g_j(r_j)$.
    pub fn eval_at(&self, name: &str, r: &[Ext3]) -> Ext3 {
        let &(_, l, _) = self.offsets.get(name).expect("unknown GMask61 spec");
        assert_eq!(r.len(), l);
        let mut total = self.ef.zero();
        for (j, &rj) in r.iter().enumerate() {
            let c = self.poly_slice(name, j);
            total = self.ef.add(total, eval_poly_ext3(&self.ef, c, rj));
        }
        total
    }

    /// Monomial coefficients `[k_0, k_1, ..., k_deg]` of $g_{\text{round}, i}(t)$ at round `i` given `r[0..i]`.
    pub fn round_poly(&self, name: &str, i: usize, r_prefix: &[Ext3]) -> Vec<Ext3> {
        let &(_, l, deg) = self.offsets.get(name).expect("unknown GMask61 spec");
        assert!(i < l && r_prefix.len() == i);
        let ef = &self.ef;
        let a_scale = ef.fp.pow(2, (l - 1 - i) as u64);

        let mut prefix_sum = ef.zero();
        for (j, &rj) in r_prefix.iter().enumerate() {
            prefix_sum = ef.add(prefix_sum, eval_poly_ext3(ef, self.poly_slice(name, j), rj));
        }
        let ci = self.poly_slice(name, i);
        let mut k0 = ef.scale(ef.add(prefix_sum, ci[0]), a_scale);

        if i + 1 < l {
            let b_scale = ef.fp.pow(2, (l - 2 - i) as u64);
            let mut rem_01 = ef.zero();
            for j in (i + 1)..l {
                let cj = self.poly_slice(name, j);
                let mut gj1 = ef.zero();
                for &ck in cj {
                    gj1 = ef.add(gj1, ck);
                }
                rem_01 = ef.add(rem_01, ef.add(cj[0], gj1));
            }
            k0 = ef.add(k0, ef.scale(rem_01, b_scale));
        }

        let mut out = Vec::with_capacity(deg + 1);
        out.push(k0);
        for &ck in &ci[1..] {
            out.push(ef.scale(ck, a_scale));
        }
        out
    }

    /// Blind an unmasked round polynomial `s_i(t)` (in monomial basis `[c_0..c_deg]`) into
    /// $\tilde{s}_i(t) = s_i(t) + \rho \cdot g_{\text{round}, i}(t)$.
    pub fn blind_round_poly(
        &self,
        name: &str,
        i: usize,
        r_prefix: &[Ext3],
        rho: Ext3,
        unmasked: &[Ext3],
    ) -> Vec<Ext3> {
        let gp = self.round_poly(name, i, r_prefix);
        assert_eq!(unmasked.len(), gp.len());
        unmasked
            .iter()
            .zip(gp.iter())
            .map(|(&s, &g)| self.ef.add(s, self.ef.mul(rho, g)))
            .collect()
    }

    /// Emit `SlotLinearClaim`s (3 basefield claims for $G$ and 3 basefield claims for $g(r)$) so that a
    /// `GMask61` packed into `base_slot .. base_slot + num_slots(N)` of a witness PCS is verified inside
    /// the **exact same** `WhirCommittedPcs61::open_slot_claims` call with zero extra commitments!
    #[allow(clippy::too_many_arguments)]
    pub fn append_slot_claims_for_spec(
        ef: &Ext3Field,
        specs: &[GMaskSpec61],
        spec_name: &str,
        base_slot: usize,
        n_slot: usize,
        claimed_g_sum: Ext3,
        r_challenges: &[Ext3],
        claimed_g_at_r: Ext3,
        v_families: &mut Vec<Vec<u64>>,
        claims: &mut Vec<SlotLinearClaim>,
    ) {
        let mut ext_off = 0usize;
        let mut target: Option<(usize, usize, usize)> = None;
        for sp in specs {
            if sp.name == spec_name {
                target = Some((ext_off, sp.num_rounds, sp.deg));
                break;
            }
            ext_off += sp.num_rounds * (sp.deg + 1);
        }
        let (off, l, deg) = target.expect("spec_name not found in GMaskSpec61 list");
        assert_eq!(r_challenges.len(), l);

        // 1. Weights `w_sum[u] in Ext3` for G = 2^{l-1} * sum_{j=0}^{l-1} (2*c_{j,0} + c_{j,1} + ... + c_{j,deg}):
        let n_u = l * (deg + 1);
        let scale_g = ef.fp.pow(2, (l - 1) as u64);
        let two_scale_g = ef.fp.mul(2, scale_g);
        let mut w_sum = vec![ef.zero(); n_u];
        for j in 0..l {
            w_sum[j * (deg + 1)] = [two_scale_g, 0, 0];
            for k in 1..=deg {
                w_sum[j * (deg + 1) + k] = [scale_g, 0, 0];
            }
        }

        // 2. Weights `w_at[u] in Ext3` for g(r) = sum_{j=0}^{l-1} sum_{k=0}^{deg} r_j^k * c_{j, k}:
        let mut w_at = vec![ef.zero(); n_u];
        for (j, &rj) in r_challenges.iter().enumerate() {
            let mut r_pw = ef.one();
            for k in 0..=deg {
                w_at[j * (deg + 1) + k] = r_pw;
                r_pw = ef.mul(r_pw, rj);
            }
        }

        emit_ext3_linear_form_as_slot_claims(
            ef,
            base_slot,
            n_slot,
            off,
            &w_sum,
            claimed_g_sum,
            v_families,
            claims,
        );
        emit_ext3_linear_form_as_slot_claims(
            ef,
            base_slot,
            n_slot,
            off,
            &w_at,
            claimed_g_at_r,
            v_families,
            claims,
        );
    }

    /// HVZK-safe (`TVD == 0` Guard 1) external sumcheck weld: emits 3 basefield claims for `G == claimed_g_sum`
    /// and 3 welded basefield claims for `f_wit(r) + rho * g(r) == terminal_masked` so **neither `f(r)` nor `g(r)`
    /// is ever revealed in the clear**!
    #[allow(clippy::too_many_arguments)]
    pub fn append_hvzk_terminal_weld_for_spec(
        ef: &Ext3Field,
        specs: &[GMaskSpec61],
        spec_name: &str,
        wit_slot: usize,
        gm_base_slot: usize,
        n_slot: usize,
        claimed_g_sum: Ext3,
        rho: Ext3,
        r_challenges: &[Ext3],
        terminal_masked: Ext3,
        v_families: &mut Vec<Vec<u64>>,
        claims: &mut Vec<SlotLinearClaim>,
    ) {
        let mut ext_off = 0usize;
        let mut target: Option<(usize, usize, usize)> = None;
        for sp in specs {
            if sp.name == spec_name {
                target = Some((ext_off, sp.num_rounds, sp.deg));
                break;
            }
            ext_off += sp.num_rounds * (sp.deg + 1);
        }
        let (off, l, deg) = target.expect("spec_name not found in GMaskSpec61 list");
        assert_eq!(r_challenges.len(), l);

        let n_u = l * (deg + 1);
        let scale_g = ef.fp.pow(2, (l - 1) as u64);
        let two_scale_g = ef.fp.mul(2, scale_g);
        let mut w_sum = vec![ef.zero(); n_u];
        for j in 0..l {
            w_sum[j * (deg + 1)] = [two_scale_g, 0, 0];
            for k in 1..=deg {
                w_sum[j * (deg + 1) + k] = [scale_g, 0, 0];
            }
        }
        emit_ext3_linear_form_as_slot_claims(
            ef,
            gm_base_slot,
            n_slot,
            off,
            &w_sum,
            claimed_g_sum,
            v_families,
            claims,
        );

        // Build `rho * w_at` for `rho * g(r)` and weld with `eq(r)` on `wit_slot`:
        let mut rho_w_at = vec![ef.zero(); n_u];
        for (j, &rj) in r_challenges.iter().enumerate() {
            let mut r_pw = rho;
            for k in 0..=deg {
                rho_w_at[j * (deg + 1) + k] = r_pw;
                r_pw = ef.mul(r_pw, rj);
            }
        }
        let prev_len = claims.len();
        emit_ext3_linear_form_as_slot_claims(
            ef,
            gm_base_slot,
            n_slot,
            off,
            &rho_w_at,
            terminal_masked,
            v_families,
            claims,
        );
        let eq_r = ef.build_eq_le(r_challenges);
        assert_eq!(eq_r.len(), n_slot);
        for coord in 0..3 {
            let vf_c: Vec<u64> = eq_r.iter().map(|e| e[coord]).collect();
            let vf_idx = v_families.len();
            v_families.push(vf_c);
            claims[prev_len + coord]
                .terms
                .push((vf_idx, vec![(wit_slot, 1u64)]));
        }
    }
}

/// Convert an `Ext3`-linear form $\sum_{u=0}^{n_u - 1} w[u] \cdot c[\text{ext\_off} + u] == \text{rhs} \in \mathrm{Ext3}$
/// into 3 exact $\mathbb{F}_p$ `SlotLinearClaim`s (`coord = 0, 1, 2`).
#[allow(clippy::too_many_arguments)]
fn emit_ext3_linear_form_as_slot_claims(
    ef: &Ext3Field,
    base_slot: usize,
    n_slot: usize,
    ext_off: usize,
    weights: &[Ext3],
    rhs: Ext3,
    v_families: &mut Vec<Vec<u64>>,
    claims: &mut Vec<SlotLinearClaim>,
) {
    let e0: Ext3 = [1, 0, 0];
    let e1: Ext3 = [0, 1, 0];
    let e2: Ext3 = [0, 0, 1];

    for (out_coord, &rhs_coord) in rhs.iter().enumerate() {
        let mut per_slot: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
        for (u, &wu) in weights.iter().enumerate() {
            let m0 = ef.mul(wu, e0)[out_coord];
            let m1 = ef.mul(wu, e1)[out_coord];
            let m2 = ef.mul(wu, e2)[out_coord];
            for (limb, coef) in [(0usize, m0), (1usize, m1), (2usize, m2)] {
                if coef == 0 {
                    continue;
                }
                let fp_idx = 3 * (ext_off + u) + limb;
                let slot = base_slot + (fp_idx / n_slot);
                let pos = fp_idx % n_slot;
                let vec = per_slot.entry(slot).or_insert_with(|| vec![0u64; n_slot]);
                vec[pos] = ef.fp.add(vec[pos], coef);
            }
        }
        let mut terms = Vec::with_capacity(per_slot.len());
        for (slot, vf) in per_slot {
            let vf_idx = v_families.len();
            v_families.push(vf);
            terms.push((vf_idx, vec![(slot, 1u64)]));
        }
        claims.push(SlotLinearClaim {
            terms,
            rhs: rhs_coord,
        });
    }
}

/// Verify masked degree-`deg` univariate sumcheck round polynomials (`\tilde{s}_0(0)+\tilde{s}_0(1) == S + \rho G`,
/// `\tilde{s}_i(0)+\tilde{s}_i(1) == \tilde{s}_{i-1}(r_{i-1})`), returning `(challenges, terminal_masked_val)`.
pub fn verify_gmask61_rounds(
    ef: &Ext3Field,
    tr: &mut PcsTranscript,
    unmasked_sum: Ext3,
    g_sum: Ext3,
    rounds: &[Vec<Ext3>],
    deg: usize,
    chal_base_tag: u64,
) -> Result<(Ext3, Vec<Ext3>, Ext3), String> {
    if rounds.is_empty() || rounds.iter().any(|p| p.len() != deg + 1) {
        return Err("GMask61 sumcheck round polynomial shape mismatch".into());
    }
    tr.absorb_ext3(&g_sum);
    let mut rho = tr.squeeze_ext3(ef, chal_base_tag);
    if rho == [0, 0, 0] {
        rho = [1, 0, 0];
    }
    let mut running = ef.add(unmasked_sum, ef.mul(rho, g_sum));
    let mut rs = Vec::with_capacity(rounds.len());

    for (i, poly) in rounds.iter().enumerate() {
        let s0 = poly[0];
        let mut s1 = ef.zero();
        for &ck in poly {
            s1 = ef.add(s1, ck);
        }
        if ef.add(s0, s1) != running {
            return Err(format!(
                "GMask61 sumcheck round {i} failed s_tilde(0)+s_tilde(1) == claim"
            ));
        }
        for ck in poly {
            tr.absorb_ext3(ck);
        }
        let r_i = tr.squeeze_ext3(ef, chal_base_tag + 1 + i as u64);
        rs.push(r_i);
        running = eval_poly_ext3(ef, poly, r_i);
    }
    Ok((rho, rs, running))
}

#[inline]
pub fn eval_poly_ext3(ef: &Ext3Field, coeffs: &[Ext3], x: Ext3) -> Ext3 {
    let mut acc = ef.zero();
    for &c in coeffs.iter().rev() {
        acc = ef.add(ef.mul(acc, x), c);
    }
    acc
}

// ================================================================================================
// §3. Multi-Round $2^k$-ary Coset-Folding `WHIR` / BaseFold Engine (`WhirPcs61`)
// ================================================================================================

/// Domain geometry at WHIR folding level `r`: `t` disjoint cosets `z^tt * <omega>` (`|H| = 2^{k_sub}`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CosetLevel61 {
    pub p: u64,
    pub t: usize,
    pub k_sub: u32,
    pub omega: u64,
    pub z: u64,
    pub npts: usize,
}

impl CosetLevel61 {
    pub fn initial(fp: &FastPrime61, n0: usize) -> Self {
        assert!(n0.is_power_of_two() && n0 >= 16);
        let p = fp.p;
        let s = (p - 1).trailing_zeros();
        let lg_n = n0.trailing_zeros();
        let k_sub = s.min(lg_n);
        let t = n0 >> k_sub;
        let mut h = 2u64;
        while fp.pow(h, (p - 1) / 2) != p - 1 {
            h += 1;
        }
        let omega = fp.pow(h, (p - 1) >> k_sub);
        let mut z = 2u64;
        while (1..t).any(|tt| fp.pow(z, (tt as u64) << k_sub) == 1) {
            z += 1;
        }
        CosetLevel61 {
            p,
            t,
            k_sub,
            omega,
            z,
            npts: n0,
        }
    }

    /// Fold domain by $B = 2^{k_r}$ (`x -> x^B`): preserves `t` pairwise-disjoint cosets of size $2^{k_{\text{sub}} - k_r}$!
    pub fn fold(&self, fp: &FastPrime61, kr: usize) -> Self {
        assert!((kr as u32) <= self.k_sub);
        let b = 1u64 << kr;
        CosetLevel61 {
            p: self.p,
            t: self.t,
            k_sub: self.k_sub - (kr as u32),
            omega: fp.pow(self.omega, b),
            z: fp.pow(self.z, b),
            npts: self.npts >> kr,
        }
    }

    #[inline]
    pub fn point(&self, fp: &FastPrime61, j: usize) -> u64 {
        let mask = (1usize << self.k_sub) - 1;
        fp.mul(
            fp.pow(self.z, (j >> self.k_sub) as u64),
            fp.pow(self.omega, (j & mask) as u64),
        )
    }

    /// Base point $x_0$ of fiber `f_idx in 0..(npts >> kr)` and primitive $2^{kr}$-th root $\zeta_r$.
    #[inline]
    pub fn fiber_base_and_zeta(&self, fp: &FastPrime61, kr: usize, f_idx: usize) -> (u64, u64) {
        let k_next = self.k_sub - (kr as u32);
        let stride = 1usize << k_next;
        let tt = f_idx >> k_next;
        let i_base = f_idx & (stride - 1);
        let x0 = fp.mul(fp.pow(self.z, tt as u64), fp.pow(self.omega, i_base as u64));
        let zeta = fp.pow(self.omega, 1u64 << k_next);
        (x0, zeta)
    }

    /// Point indices `j_0 .. j_{2^{kr} - 1}` in `0..self.npts` belonging to fiber `f_idx`.
    #[inline]
    pub fn fiber_point_indices(&self, kr: usize, f_idx: usize) -> Vec<usize> {
        let k_next = self.k_sub - (kr as u32);
        let stride = 1usize << k_next;
        let tt = f_idx >> k_next;
        let i_base = f_idx & (stride - 1);
        let b = 1usize << kr;
        let base_coset = tt << self.k_sub;
        (0..b).map(|m| base_coset + i_base + m * stride).collect()
    }

    /// Map a point index `p_idx in 0..self.npts` into `(fiber_idx, sub_pos_in_fiber)` under folding arity `kr`.
    #[inline]
    pub fn locate_in_fiber(&self, kr: usize, p_idx: usize) -> (usize, usize) {
        let k_next = self.k_sub - (kr as u32);
        let mask_sub = (1usize << self.k_sub) - 1;
        let tt = p_idx >> self.k_sub;
        let i_in = p_idx & mask_sub;
        let i_base = i_in & ((1usize << k_next) - 1);
        let sub_pos = i_in >> k_next;
        ((tt << k_next) + i_base, sub_pos)
    }
}

/// Public WHIR commitment & folding schedule shape for `WhirPcs61`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirShape61 {
    pub p: u64,
    pub mr: usize,
    pub mc: usize,
    pub rd: usize,
    pub usable_rows: usize,
    pub c: usize,
    pub w0: usize,
    pub hide: usize,
    pub r_total: usize,
    pub blow: usize,
    pub n0: usize,
    pub t_queries: usize,
    pub k_schedule: Vec<usize>,
    pub w_final: usize,
    pub level0: CosetLevel61,
}

fn build_whir_k_schedule(k_max: usize, w0: usize, k0: usize) -> (Vec<usize>, usize) {
    let mut k_schedule = vec![k0];
    let mut used_k = k0;
    let mut w_cur = w0 >> k0;
    while (w_cur > 256 || (k_schedule.len() == 1 && w_cur > 128)) && used_k + 2 <= k_max {
        let rem_bits = (w_cur.trailing_zeros() as usize).saturating_sub(8);
        let kr = if rem_bits >= 4 && (rem_bits % 3 == 1) && used_k + 4 <= k_max {
            4usize
        } else if w_cur >= 1024 && used_k + 3 <= k_max {
            3usize
        } else {
            2usize
        };
        k_schedule.push(kr);
        used_k += kr;
        w_cur >>= kr;
    }
    if w_cur > 256 && used_k < k_max {
        k_schedule.push(1);
        w_cur >>= 1;
    }
    (k_schedule, w_cur)
}

impl WhirShape61 {
    /// Choose optimal `(mr, mc, k_schedule)` for `num_elems` field elements minimizing WHIR proof bytes!
    pub fn for_len(
        fp: &FastPrime61,
        num_elems: usize,
        min_mc: usize,
        t_queries: usize,
        blow: usize,
    ) -> Self {
        let min_mc = min_mc.max(9); // C >= 512
        let hide_floor = t_queries.saturating_mul(16).next_power_of_two();
        let max_c_cap = (num_elems.max(1 << min_mc) / 6)
            .next_power_of_two()
            .max(1usize << min_mc)
            .max(hide_floor);
        let max_mc = (max_c_cap.trailing_zeros() as usize).clamp(min_mc, 20);
        let mut best: Option<(usize, usize, usize)> = None;
        for mc in min_mc..=max_mc {
            let c = 1usize << mc;
            let needed_data_rows = num_elems.max(1).div_ceil(c);
            let min_rd = (needed_data_rows + WHIR_NUM_ZK_DATA_ROWS)
                .max(8)
                .next_power_of_two();
            let mr = min_rd.trailing_zeros() as usize;
            if mr + mc > 31 {
                continue;
            }
            let cand = Self::from_mr_mc(fp, mr, mc, t_queries, blow);
            if cand.hide < cand.t_queries * (1usize << cand.k_schedule[0]) {
                continue;
            }
            let est_bytes = cand.estimated_proof_bytes();
            if best.is_none_or(|b| est_bytes < b.0) {
                best = Some((est_bytes, mr, mc));
            }
        }
        let (_, mr, mc) = best.expect("valid WhirShape61");
        Self::from_mr_mc(fp, mr, mc, t_queries, blow)
    }

    pub fn from_mr_mc(
        fp: &FastPrime61,
        mr: usize,
        mc: usize,
        t_queries: usize,
        blow: usize,
    ) -> Self {
        assert!(mr >= 3 && mc >= 8 && blow.is_power_of_two() && blow >= 4);
        let rd = 1usize << mr;
        let usable_rows = rd - WHIR_NUM_ZK_DATA_ROWS;
        let c = 1usize << mc;
        let w0 = 2 * c;
        let hide = c;
        let r_total = rd + WHIR_EXTRA_EXT3_MASK_ROWS;
        let n0 = blow * w0;
        let level0 = CosetLevel61::initial(fp, n0);

        // Use `k0 = 0` (`CommitF0`, single-column Stage-0 opening) whenever `r_total >= 45` so tall
        // matrices never pay `2x..4x` Stage-0 column bloat; use `k0 = 1` on short matrices to skip `F^(0)` tree!
        let k_max = level0.k_sub as usize;
        let k0 = if r_total >= 45 && w0 >= 2048 && k_max >= 4 {
            0usize
        } else {
            1usize
        };
        let (k_schedule, w_final) = build_whir_k_schedule(k_max, w0, k0);
        let n_leaves_0 = n0 >> k_schedule[0];
        let eff_t = t_queries.min(n_leaves_0);

        WhirShape61 {
            p: fp.p,
            mr,
            mc,
            rd,
            usable_rows,
            c,
            w0,
            hide,
            r_total,
            blow,
            n0,
            t_queries: eff_t,
            k_schedule,
            w_final,
            level0,
        }
    }

    pub fn estimated_proof_bytes(&self) -> usize {
        let k0 = self.k_schedule[0];
        let leaves0 = self.n0 >> k0;
        let lg0 = bitlen_usize(leaves0.saturating_sub(1));
        let s0_cols = (self.t_queries * (1usize << k0) * self.r_total * 61).div_ceil(8);
        let s0_mp = self.t_queries * 16 + self.t_queries * lg0.saturating_sub(6) * 32;
        let mut folds = 0usize;
        let mut l_cur = leaves0;
        for &kr in &self.k_schedule[1..] {
            l_cur >>= kr;
            let lg = bitlen_usize(l_cur.saturating_sub(1));
            let tq = self.t_queries.min(l_cur);
            folds += 64 + (tq * (1usize << kr) * 183).div_ceil(8) + tq * lg.saturating_sub(5) * 32;
        }
        s0_cols + s0_mp + folds + self.w_final * 24 + (self.mr + self.mc * 2) * 72
    }

    /// Exact provable soundness bits `(bciks20_ud_bits, dkt26_jbr_bits, ahiv17_ud_bits, alg_bits)`!
    pub fn soundness_bits(&self) -> (f64, f64, f64, f64) {
        let rho = 1.0 / (self.blow as f64); // 0.25 at blow = 4
        let log_ext3 = 3.0 * (self.p as f64).log2(); // 182.9994 bits

        // 1. `[BCIKS20]` Unique Decoding (`theta = (1 - rho)/2 - eta` with `eta = 2^-12`):
        let eta_ud = 2.0f64.powi(-12);
        let theta_ud = 0.5 * (1.0 - rho) - eta_ud;
        let q_ud_bits = -(self.t_queries as f64) * (1.0 - theta_ud).log2();

        // 2. `[DKT26]` Thm 5.12 (`ePrint 2026/2056`) Zeroth-Order Johnson MCA (`m = 20`):
        let m_jbr = 20.0f64;
        let eta_jbr = rho.sqrt() / (2.0 * m_jbr + 1.0);
        let agree_jbr = rho.sqrt() + eta_jbr;
        let q_dkt_bits = -(self.t_queries as f64) * agree_jbr.log2();
        let max_aff = (1usize << (*self.k_schedule.iter().max().unwrap_or(&3))) as f64;
        let e0_dkt = max_aff * 8.0 * (self.n0 as f64) * (m_jbr + 0.5).powi(3) / (3.0 * rho);
        let alg_dkt_bits = log_ext3 - e0_dkt.log2();

        // 3. `[AHIV17]` Classical `d/3` Elementary Unique Decoding (`delta = (1 - rho)/3`):
        let delta_ahiv = (1.0 - rho) / 3.0;
        let q_ahiv_bits = -(self.t_queries as f64) * (1.0 - delta_ahiv).log2();

        // 4. Worst-case algebraic union bound across sumcheck + GMask + DEEP OOD + CA:
        let alg_ud_err = (self.k_schedule.len() as f64) * max_aff * (self.n0 as f64) / eta_ud;
        let alg_bits = (log_ext3 - alg_ud_err.log2()).min(alg_dkt_bits);

        (
            q_ud_bits.min(alg_bits),
            q_dkt_bits.min(alg_dkt_bits),
            q_ahiv_bits.min(alg_bits),
            alg_bits,
        )
    }
}

#[inline]
fn hash_whir_s0_fiber(f_idx: usize, salt: &[u8; 16], fiber_cols: &[u64]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_WHIR61_S0_LEAF_V1|");
    h.update((f_idx as u32).to_le_bytes());
    h.update(salt);
    let mut raw = Vec::with_capacity(fiber_cols.len() * 8);
    for &v in fiber_cols {
        raw.extend_from_slice(&v.to_le_bytes());
    }
    h.update(&raw);
    h.finalize().into()
}

#[inline]
fn hash_whir_fold_fiber(round: usize, f_idx: usize, fiber_vals: &[Ext3]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_WHIR61_FOLD_LEAF_V1|");
    h.update((round as u8).to_le_bytes());
    h.update((f_idx as u32).to_le_bytes());
    for e in fiber_vals {
        h.update(e[0].to_le_bytes());
        h.update(e[1].to_le_bytes());
        h.update(e[2].to_le_bytes());
    }
    h.finalize().into()
}

#[inline]
fn hash_whir_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_WHIR61_NODE_V1|");
    h.update(left);
    h.update(right);
    h.finalize().into()
}

#[inline]
fn hash_whir_pad(j: usize) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_WHIR61_PAD_V1|");
    h.update((j as u32).to_le_bytes());
    h.finalize().into()
}

fn build_whir_tree(mut leaves: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    let levels = bitlen_usize(leaves.len().saturating_sub(1)).max(1);
    let full = 1usize << levels;
    for j in leaves.len()..full {
        leaves.push(hash_whir_pad(j));
    }
    let mut tree = vec![leaves];
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = if prev.len() >= 512 {
            prev.par_chunks(2)
                .map(|c| hash_whir_node(&c[0], &c[1]))
                .collect()
        } else {
            prev.chunks(2)
                .map(|c| hash_whir_node(&c[0], &c[1]))
                .collect()
        };
        tree.push(next);
    }
    tree
}

fn extract_siblings(tree: &[Vec<[u8; 32]>], indices: &[usize]) -> Vec<[u8; 32]> {
    let levels = tree.len() - 1;
    multiproof_needed(indices, levels)
        .into_iter()
        .map(|(l, x)| tree[l][x ^ 1])
        .collect()
}

fn verify_whir_tree_multiproof(
    expected_root: &[u8; 32],
    num_leaves: usize,
    indices: &[usize],
    leaf_hashes: &[[u8; 32]],
    siblings: &[[u8; 32]],
) -> Result<(), String> {
    if indices.is_empty() || indices.len() != leaf_hashes.len() {
        return Err("WHIR Merkle multiproof count mismatch".into());
    }
    let mut seen = BTreeSet::new();
    for &idx in indices {
        if idx >= num_leaves || !seen.insert(idx) {
            return Err("WHIR Merkle multiproof invalid or duplicate fiber index".into());
        }
    }
    let levels = bitlen_usize(num_leaves.saturating_sub(1)).max(1);
    let needed = multiproof_needed(indices, levels);
    if siblings.len() != needed.len() {
        return Err("WHIR Merkle multiproof sibling count mismatch".into());
    }
    let mut known: BTreeMap<usize, [u8; 32]> = indices
        .iter()
        .copied()
        .zip(leaf_hashes.iter().copied())
        .collect();
    let mut sib_it = siblings.iter();
    for _l in 0..levels {
        let mut next = BTreeMap::new();
        for (&x, hx) in &known {
            if (x & 1) == 1 && known.contains_key(&(x ^ 1)) {
                continue;
            }
            let sb = match known.get(&(x ^ 1)) {
                Some(h) => h,
                None => sib_it
                    .next()
                    .ok_or_else(|| "WHIR multiproof sibling underflow".to_string())?,
            };
            let parent = if (x & 1) == 0 {
                hash_whir_node(hx, sb)
            } else {
                hash_whir_node(sb, hx)
            };
            next.insert(x >> 1, parent);
        }
        known = next;
    }
    if sib_it.next().is_some()
        || known.len() != 1
        || known.values().next().unwrap() != expected_root
    {
        return Err("WHIR Merkle multiproof root mismatch (tampered fiber or path)".into());
    }
    Ok(())
}

/// Prover-side committed WHIR Matrix PCS state.
#[derive(Clone)]
pub struct WhirCommittedPcs61 {
    pub ef: Ext3Field,
    pub shape: WhirShape61,
    /// `r_total x w0` monomial coefficient matrix.
    pub ext: Vec<u64>,
    /// Internal `GMask61` instance (`name = "pcs_sc"`, `mr + mc` quadratic rounds) stored in rows `rd .. rd + 3`.
    internal_gmask: GMask61,
    pub fiber_salts: Vec<[u8; 16]>,
    pub tree0: Vec<Vec<[u8; 32]>>,
    pub root: [u8; 32],
    /// Cached column-major Stage-0 codeword (`n0 * r_total` `u64`s) when `<= 768 MiB`, else streamed on open.
    cw0: Vec<u64>,
}

/// Per-matrix `GMask61`-blinded sumcheck + coefficient-reduction header (before the WHIR folding cascade).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirMatrixHeader61 {
    pub gmask_sum: Ext3,
    pub sumcheck_rounds: Vec<[Ext3; 3]>,
    pub m_eval: Ext3,
    /// Rank-preserving `Z_gm` scalar masks `(s_G, s_at)` blinding `P_gmask` during the `w0`-round coeff sumcheck.
    pub z_gm_masks: [Ext3; 2],
    /// Unmasked `w0`-round quadratic sumcheck reducing `<V_eval, u_eval> + <V_gm, P_gmask_hat>` to `zeta in Ext3^{w0}`.
    pub coeff_sumcheck_rounds: Vec<[Ext3; 3]>,
    pub u_eval_at_zeta: Ext3,
    pub p_gmask_hat_at_zeta: Ext3,
    pub u_prox_at_zeta: Ext3,
}

/// One folded intermediate WHIR oracle (`r = 1 .. R - 1`) + OOD DEEP evaluation + deduplicated fiber multiproof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirFoldRoundProof61 {
    pub ood_eval_prev: Ext3,
    pub root: [u8; 32],
    /// Opened fibers in `D_r / 2^{k_r}` at the canonical deduplicated trajectory fiber indices (`B_r` `Ext3`s per fiber).
    pub opened_fibers: Vec<Ext3>,
    pub siblings: Vec<[u8; 32]>,
}

/// Standalone `WhirPcs61` opening proof (`~180–420 KiB` vs `2.5–16 MiB` in 1-step Ligero!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirOpeningProof61 {
    pub header: WhirMatrixHeader61,
    /// Initial Stage-0 opened fibers (`t_queries * 2^{k_0} * r_total` 61-bit field elements).
    pub s0_fiber_vals: Vec<u64>,
    pub s0_salts: Vec<[u8; 16]>,
    pub s0_siblings: Vec<[u8; 32]>,
    pub fold_rounds: Vec<WhirFoldRoundProof61>,
    pub final_ood_eval: Ext3,
    pub final_poly: Vec<Ext3>,
}

impl WhirMatrixHeader61 {
    pub fn to_bytes(&self, p: u64, out: &mut Vec<u8>) {
        let mut flat = Vec::with_capacity(
            (1 + self.sumcheck_rounds.len() * 3 + 3 + self.coeff_sumcheck_rounds.len() * 3 + 3) * 3,
        );
        let push_e = |dst: &mut Vec<u64>, e: &Ext3| {
            dst.push(e[0]);
            dst.push(e[1]);
            dst.push(e[2]);
        };
        out.push(self.sumcheck_rounds.len() as u8);
        out.push(self.coeff_sumcheck_rounds.len() as u8);
        push_e(&mut flat, &self.gmask_sum);
        for r in &self.sumcheck_rounds {
            for e in r {
                push_e(&mut flat, e);
            }
        }
        push_e(&mut flat, &self.m_eval);
        push_e(&mut flat, &self.z_gm_masks[0]);
        push_e(&mut flat, &self.z_gm_masks[1]);
        for r in &self.coeff_sumcheck_rounds {
            for e in r {
                push_e(&mut flat, e);
            }
        }
        push_e(&mut flat, &self.u_eval_at_zeta);
        push_e(&mut flat, &self.p_gmask_hat_at_zeta);
        push_e(&mut flat, &self.u_prox_at_zeta);
        let _ = p;
        pack_u64_bits_le(&flat, 61, out);
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>, p: u64) -> Result<Self, String> {
        let n_sc = cur.read_u8()? as usize;
        let n_csc = cur.read_u8()? as usize;
        if n_sc == 0 || n_sc > 32 || n_csc == 0 || n_csc > 32 {
            return Err("invalid WhirMatrixHeader61 round counts".into());
        }
        let expected_ext = 1 + n_sc * 3 + 3 + n_csc * 3 + 3;
        let ext_vec = unpack_ext3_slice(cur, expected_ext, p)?;
        if ext_vec.len() != expected_ext {
            return Err("WhirMatrixHeader61 unpacked Ext3 count mismatch".into());
        }
        let mut idx = 0usize;
        let gmask_sum = ext_vec[idx];
        idx += 1;
        let mut sumcheck_rounds = Vec::with_capacity(n_sc);
        for _ in 0..n_sc {
            sumcheck_rounds.push([ext_vec[idx], ext_vec[idx + 1], ext_vec[idx + 2]]);
            idx += 3;
        }
        let m_eval = ext_vec[idx];
        let z_gm_masks = [ext_vec[idx + 1], ext_vec[idx + 2]];
        idx += 3;
        let mut coeff_sumcheck_rounds = Vec::with_capacity(n_csc);
        for _ in 0..n_csc {
            coeff_sumcheck_rounds.push([ext_vec[idx], ext_vec[idx + 1], ext_vec[idx + 2]]);
            idx += 3;
        }
        let u_eval_at_zeta = ext_vec[idx];
        let p_gmask_hat_at_zeta = ext_vec[idx + 1];
        let u_prox_at_zeta = ext_vec[idx + 2];
        Ok(WhirMatrixHeader61 {
            gmask_sum,
            sumcheck_rounds,
            m_eval,
            z_gm_masks,
            coeff_sumcheck_rounds,
            u_eval_at_zeta,
            p_gmask_hat_at_zeta,
            u_prox_at_zeta,
        })
    }
}

fn write_fold_rounds_61(
    p: u64,
    fold_rounds: &[WhirFoldRoundProof61],
    final_ood_eval: &Ext3,
    final_poly: &[Ext3],
    out: &mut Vec<u8>,
) {
    out.push(fold_rounds.len() as u8);
    for fr in fold_rounds {
        pack_ext3_slice(p, &[fr.ood_eval_prev], out);
        out.extend_from_slice(&fr.root);
        pack_ext3_slice(p, &fr.opened_fibers, out);
        out.extend_from_slice(&(fr.siblings.len() as u32).to_le_bytes());
        for s in &fr.siblings {
            out.extend_from_slice(s);
        }
    }
    pack_ext3_slice(p, &[*final_ood_eval], out);
    pack_ext3_slice(p, final_poly, out);
}

fn read_fold_rounds_61(
    cur: &mut ByteReader<'_>,
    p: u64,
) -> Result<(Vec<WhirFoldRoundProof61>, Ext3, Vec<Ext3>), String> {
    let n_fr = cur.read_u8()? as usize;
    if n_fr > 16 {
        return Err("excessive WHIR fold round count".into());
    }
    let mut fold_rounds = Vec::with_capacity(n_fr);
    for _ in 0..n_fr {
        let ood_v = unpack_ext3_slice(cur, 1, p)?;
        if ood_v.len() != 1 {
            return Err("missing ood_eval_prev".into());
        }
        let root = cur.read_hash()?;
        let opened_fibers = unpack_ext3_slice(cur, 1 << 16, p)?;
        let n_sibs = cur.read_u32()? as usize;
        if n_sibs > (1 << 16) {
            return Err("WHIR fold round sibling overflow".into());
        }
        let mut siblings = Vec::with_capacity(n_sibs);
        for _ in 0..n_sibs {
            siblings.push(cur.read_hash()?);
        }
        fold_rounds.push(WhirFoldRoundProof61 {
            ood_eval_prev: ood_v[0],
            root,
            opened_fibers,
            siblings,
        });
    }
    let fin_ood = unpack_ext3_slice(cur, 1, p)?;
    if fin_ood.len() != 1 {
        return Err("missing final_ood_eval".into());
    }
    let final_poly = unpack_ext3_slice(cur, 4096, p)?;
    Ok((fold_rounds, fin_ood[0], final_poly))
}

impl WhirOpeningProof61 {
    pub fn to_bytes(&self, p: u64, out: &mut Vec<u8>) {
        self.header.to_bytes(p, out);
        pack_u64_bits_le(&self.s0_fiber_vals, 61, out);
        out.extend_from_slice(&(self.s0_salts.len() as u32).to_le_bytes());
        for s in &self.s0_salts {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.s0_siblings.len() as u32).to_le_bytes());
        for s in &self.s0_siblings {
            out.extend_from_slice(s);
        }
        write_fold_rounds_61(
            p,
            &self.fold_rounds,
            &self.final_ood_eval,
            &self.final_poly,
            out,
        );
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>, p: u64) -> Result<Self, String> {
        let header = WhirMatrixHeader61::from_bytes(cur, p)?;
        let s0_fiber_vals = unpack_u64_bits_le(cur, 61, 1 << 23, p)?;
        let n_salts = cur.read_u32()? as usize;
        if n_salts > 4096 {
            return Err("s0_salts count overflow".into());
        }
        let mut s0_salts = Vec::with_capacity(n_salts);
        for _ in 0..n_salts {
            s0_salts.push(cur.take(16)?.try_into().unwrap());
        }
        let n_sibs = cur.read_u32()? as usize;
        if n_sibs > 65536 {
            return Err("s0_siblings count overflow".into());
        }
        let mut s0_siblings = Vec::with_capacity(n_sibs);
        for _ in 0..n_sibs {
            s0_siblings.push(cur.read_hash()?);
        }
        let (fold_rounds, final_ood_eval, final_poly) = read_fold_rounds_61(cur, p)?;
        Ok(WhirOpeningProof61 {
            header,
            s0_fiber_vals,
            s0_salts,
            s0_siblings,
            fold_rounds,
            final_ood_eval,
            final_poly,
        })
    }
}

impl WhirCommittedPcs61 {
    pub fn commit(fp: FastPrime61, data: &[u64], min_mc: usize) -> Self {
        Self::commit_with_rng(
            fp,
            data,
            min_mc,
            WHIR_T_QUERIES_128,
            WHIR_BLOWUP,
            PcsRng::from_os(),
        )
    }

    pub fn commit_with_shape(
        fp: FastPrime61,
        shape: WhirShape61,
        data: &[u64],
        mut rng: PcsRng,
    ) -> Self {
        assert_eq!(fp.p, shape.p);
        assert!(
            data.len() <= shape.usable_rows * shape.c,
            "data len {} exceeds usable_rows*C = {}",
            data.len(),
            shape.usable_rows * shape.c
        );
        let ef = Ext3Field::new(fp);
        let (c, w0, rd, r_total, usable) = (
            shape.c,
            shape.w0,
            shape.rd,
            shape.r_total,
            shape.usable_rows,
        );

        let m_bits = shape.mc + shape.mr;
        let internal_gmask =
            GMask61::sample(ef, vec![GMaskSpec61::new("pcs_sc", m_bits, 2)], &mut rng);
        let n_gm_ext = internal_gmask.coeffs.len();
        assert!(n_gm_ext < c, "internal GMask61 fits inside C");

        let mut ext = vec![0u64; r_total * w0];
        let root_seed = {
            let mut rng_key = rng.clone();
            rng_key.next_block()
        };
        // 1. Data rows `0..usable` (`[0..c)` witness, `[c..w0)` exact-uniform `< p` column-hiding tail):
        ext[..usable * w0]
            .par_chunks_mut(w0)
            .enumerate()
            .for_each(|(r, row_dst)| {
                let start = r * c;
                if start < data.len() {
                    let end = (start + c).min(data.len());
                    for (i, &val) in data[start..end].iter().enumerate() {
                        row_dst[i] = if val >= fp.p { val % fp.p } else { val };
                    }
                }
                fill_whir_mask_slice_61(&fp, &root_seed, r as u64, &mut row_dst[c..w0]);
            });

        // 2..4. All `4 + 3 + 6 = 13` blinding/GMask/Z_gm/P_prox rows filled in `rayon` parallel:
        ext[usable * w0..r_total * w0]
            .par_chunks_mut(w0)
            .enumerate()
            .for_each(|(idx, row_dst)| {
                let r = usable + idx;
                if r < rd {
                    fill_whir_mask_slice_61(&fp, &root_seed, (1u64 << 32) + r as u64, row_dst);
                } else if r < rd + 3 {
                    let limb = r - rd;
                    fill_whir_mask_slice_61(
                        &fp,
                        &root_seed,
                        (2u64 << 32) + limb as u64,
                        &mut row_dst[n_gm_ext..w0],
                    );
                    for (u, coeff) in internal_gmask.coeffs.iter().enumerate() {
                        row_dst[u] = coeff[limb];
                    }
                } else {
                    fill_whir_mask_slice_61(&fp, &root_seed, (3u64 << 32) + r as u64, row_dst);
                }
            });

        let k0 = shape.k_schedule[0];
        let n_leaves_0 = shape.n0 >> k0;
        let mut salt_mid = Sha256::new();
        salt_mid.update(b"WHIR61_FIBER_SALT_V1|");
        salt_mid.update(root_seed);
        let mut fiber_salts = vec![[0u8; 16]; n_leaves_0];
        fiber_salts
            .par_chunks_mut(2)
            .enumerate()
            .for_each(|(pair_idx, pair_dst)| {
                let mut h = salt_mid.clone();
                h.update((pair_idx as u64).to_le_bytes());
                let d: [u8; 32] = h.finalize().into();
                pair_dst[0].copy_from_slice(&d[0..16]);
                if pair_dst.len() > 1 {
                    pair_dst[1].copy_from_slice(&d[16..32]);
                }
            });

        let hold_cw = shape.r_total * shape.n0 * 8 <= (768usize << 20);
        let (cw0, leaves) = if hold_cw {
            let cw = encode_level0_column_major(&fp, &shape, &ext);
            let b0 = 1usize << k0;
            let leaves: Vec<[u8; 32]> = (0..n_leaves_0)
                .into_par_iter()
                .map(|f_idx| {
                    let js = shape.level0.fiber_point_indices(k0, f_idx);
                    let mut fiber_buf = Vec::with_capacity(b0 * r_total);
                    for j in js {
                        fiber_buf.extend_from_slice(&cw[j * r_total..(j + 1) * r_total]);
                    }
                    hash_whir_s0_fiber(f_idx, &fiber_salts[f_idx], &fiber_buf)
                })
                .collect();
            (cw, leaves)
        } else {
            let leaves = stream_level0_fiber_leaves(&fp, &shape, &ext, &fiber_salts);
            (Vec::new(), leaves)
        };

        let tree0 = build_whir_tree(leaves);
        let root = tree0.last().unwrap()[0];

        WhirCommittedPcs61 {
            ef,
            shape,
            ext,
            internal_gmask,
            fiber_salts,
            tree0,
            root,
            cw0,
        }
    }

    pub fn commit_with_rng(
        fp: FastPrime61,
        data: &[u64],
        min_mc: usize,
        t_queries: usize,
        blow: usize,
        rng: PcsRng,
    ) -> Self {
        let shape = WhirShape61::for_len(&fp, data.len(), min_mc, t_queries, blow);
        Self::commit_with_shape(fp, shape, data, rng)
    }

    fn open_stage0_fibers(
        &self,
        fiber_indices: &[usize],
    ) -> (Vec<u64>, Vec<[u8; 16]>, Vec<[u8; 32]>) {
        let sh = &self.shape;
        let k0 = sh.k_schedule[0];
        let b0 = 1usize << k0;
        let mut all_js = Vec::with_capacity(fiber_indices.len() * b0);
        for &f_idx in fiber_indices {
            all_js.extend(sh.level0.fiber_point_indices(k0, f_idx));
        }
        let cols: Vec<Vec<u64>> = if !self.cw0.is_empty() {
            all_js
                .par_iter()
                .map(|&j| self.cw0[j * sh.r_total..(j + 1) * sh.r_total].to_vec())
                .collect()
        } else {
            stream_level0_selected_columns(&self.ef.fp, sh, &self.ext, &all_js)
        };
        let mut flat_vals = Vec::with_capacity(all_js.len() * sh.r_total);
        for col in cols {
            flat_vals.extend_from_slice(&col);
        }
        let salts = fiber_indices.iter().map(|&f| self.fiber_salts[f]).collect();
        let siblings = extract_siblings(&self.tree0, fiber_indices);
        (flat_vals, salts, siblings)
    }
}

#[inline]
fn eval_slot_u64_61(
    fp: &FastPrime61,
    sw: &[(usize, Ext3)],
    v_families: &[Vec<u64>],
    j: usize,
) -> Ext3 {
    let (mut a0, mut a1, mut a2) = (0u64, 0u64, 0u64);
    let (mut s0, mut s1, mut s2) = (0u128, 0u128, 0u128);
    for (k, &(vi, w_ext)) in sw.iter().enumerate() {
        let vj = v_families[vi][j] as u128;
        if vj != 0 {
            s0 += (w_ext[0] as u128) * vj;
            s1 += (w_ext[1] as u128) * vj;
            s2 += (w_ext[2] as u128) * vj;
        }
        if (k & 15) == 15 {
            a0 = fp.add(a0, fp.red128(s0));
            a1 = fp.add(a1, fp.red128(s1));
            a2 = fp.add(a2, fp.red128(s2));
            s0 = 0;
            s1 = 0;
            s2 = 0;
        }
    }
    [
        fp.add(a0, fp.red128(s0)),
        fp.add(a1, fp.red128(s1)),
        fp.add(a2, fp.red128(s2)),
    ]
}

#[inline]
fn eval_slot_ext3_61(ef: &Ext3Field, sw: &[(usize, Ext3)], vf_ext: &[Vec<Ext3>], j: usize) -> Ext3 {
    let mut acc = ef.zero();
    for &(vi, w_ext) in sw {
        let vj = vf_ext[vi][j];
        if vj != [0, 0, 0] {
            acc = ef.add(acc, ef.mul(w_ext, vj));
        }
    }
    acc
}

#[inline]
fn comb_base_ext3_61(fp: &FastPrime61, eq_w: &[Ext3], xs: &[u64]) -> Ext3 {
    let (mut s0, mut s1, mut s2) = (0u128, 0u128, 0u128);
    for (w, &x) in eq_w.iter().zip(xs.iter()) {
        let xu = x as u128;
        if xu != 0 {
            s0 += (w[0] as u128) * xu;
            s1 += (w[1] as u128) * xu;
            s2 += (w[2] as u128) * xu;
        }
    }
    [fp.red128(s0), fp.red128(s1), fp.red128(s2)]
}

impl WhirCommittedPcs61 {
    /// Shared `(mc + mr)`-round `GMask61`-blinded `SlotLinearClaim` sumcheck engine with a zero-swap
    /// 3-round streaming prefix (`k_pre = 3`, cutting temporary table RAM by `8x`, e.g. `19.3 GiB -> 3.2 GiB` at `d = 4096`).
    fn run_slot_row_sumcheck_61(
        &self,
        log_n: usize,
        v_families: &[Vec<u64>],
        claims: &[SlotLinearClaim],
        tr: &mut PcsTranscript,
    ) -> (Ext3, Vec<[Ext3; 3]>, Vec<Ext3>, Ext3) {
        let fp = &self.ef.fp;
        let ef = &self.ef;
        let sh = &self.shape;
        let n_poly = 1usize << log_n;
        assert!(log_n <= sh.mc && sh.c.is_multiple_of(n_poly));
        let polys_per_row = sh.c / n_poly;
        let usable_slots = sh.usable_rows * polys_per_row;

        tr.absorb_bytes(&sh.root_shape_tag());
        tr.absorb_bytes(&(claims.len() as u64).to_le_bytes());
        for cl in claims {
            tr.absorb_bytes(&cl.rhs.to_le_bytes());
        }

        let beta = tr.squeeze_ext3(ef, 1);
        let mut slot_sparse: Vec<Vec<(usize, Ext3)>> = vec![Vec::new(); usable_slots];
        let mut beta_pw = ef.one();
        for cl in claims {
            for (vf_idx, slot_terms) in &cl.terms {
                for &(slot, w_u64) in slot_terms {
                    assert!(slot < usable_slots, "claim touches ZK blinding rows!");
                    let contrib = ef.scale(beta_pw, w_u64);
                    let list = &mut slot_sparse[slot];
                    if let Some(entry) = list.iter_mut().find(|x| x.0 == *vf_idx) {
                        entry.1 = ef.add(entry.1, contrib);
                    } else {
                        list.push((*vf_idx, contrib));
                    }
                }
            }
            beta_pw = ef.mul(beta_pw, beta);
        }
        for sw in &mut slot_sparse {
            sw.retain(|&(_, w_ext)| w_ext != [0, 0, 0]);
        }

        let gmask_sum = self.internal_gmask.hypercube_sum("pcs_sc");
        tr.absorb_ext3(&gmask_sum);
        let mut rho = tr.squeeze_ext3(ef, 50);
        if rho == [0, 0, 0] {
            rho = [1, 0, 0];
        }

        let total_cells = sh.rd * sh.c;
        let m_bits = sh.mc + sh.mr;
        let mut sumcheck_rounds = Vec::with_capacity(m_bits);
        let mut z_challenges = Vec::with_capacity(m_bits);

        let (mut a_tbl, mut m_tbl, mut cur_len, start_round) = if n_poly >= 8
            && m_bits >= 4
            && total_cells >= (1usize << 20)
        {
            // Streaming Round 0 directly over `v_families` (`u64`) and `self.ext` (`u64`) with 0 GiB table RAM:
            let unmasked0 = (0..usable_slots)
                .into_par_iter()
                .map(|slot| {
                    let sw = &slot_sparse[slot];
                    if sw.is_empty() {
                        return [ef.zero(), ef.zero(), ef.zero()];
                    }
                    let base_idx = slot * n_poly;
                    let r = base_idx >> sh.mc;
                    let c_base = base_idx & (sh.c - 1);
                    let ext_slice = &self.ext[r * sh.w0 + c_base..r * sh.w0 + c_base + n_poly];
                    let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                    for u_loc in 0..(n_poly / 2) {
                        let a0 = eval_slot_u64_61(fp, sw, v_families, 2 * u_loc);
                        let a1 = eval_slot_u64_61(fp, sw, v_families, 2 * u_loc + 1);
                        let m0 = ext_slice[2 * u_loc];
                        let m1 = ext_slice[2 * u_loc + 1];
                        let dm = fp.sub(m1, m0);
                        let da = ef.sub(a1, a0);
                        acc[0] = ef.add(acc[0], ef.scale(a0, m0));
                        acc[1] = ef.add(acc[1], ef.add(ef.scale(a0, dm), ef.scale(da, m0)));
                        acc[2] = ef.add(acc[2], ef.scale(da, dm));
                    }
                    acc
                })
                .reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |a, b| [ef.add(a[0], b[0]), ef.add(a[1], b[1]), ef.add(a[2], b[2])],
                );
            let m0_v = self
                .internal_gmask
                .blind_round_poly("pcs_sc", 0, &[], rho, &unmasked0);
            let m0_arr = [m0_v[0], m0_v[1], m0_v[2]];
            for ck in &m0_arr {
                tr.absorb_ext3(ck);
            }
            let r_0 = tr.squeeze_ext3(ef, 51);
            sumcheck_rounds.push(m0_arr);
            z_challenges.push(r_0);

            let mut vf_ext: Vec<Vec<Ext3>> = v_families
                .par_iter()
                .map(|vf| {
                    (0..(n_poly / 2))
                        .map(|u| {
                            let (v0, v1) = (vf[2 * u], vf[2 * u + 1]);
                            ef.add([v0, 0, 0], ef.scale(r_0, fp.sub(v1, v0)))
                        })
                        .collect()
                })
                .collect();
            let eq2 = [ef.sub(ef.one(), r_0), r_0];

            // Streaming Round 1 (`n_poly / 2 -> n_poly / 4`, still 0 GiB table RAM):
            let unmasked1 = (0..usable_slots)
                .into_par_iter()
                .map(|slot| {
                    let sw = &slot_sparse[slot];
                    if sw.is_empty() {
                        return [ef.zero(), ef.zero(), ef.zero()];
                    }
                    let base_idx = slot * n_poly;
                    let r = base_idx >> sh.mc;
                    let c_base = base_idx & (sh.c - 1);
                    let ext_slice = &self.ext[r * sh.w0 + c_base..r * sh.w0 + c_base + n_poly];
                    let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                    for q in 0..(n_poly / 4) {
                        let a0 = eval_slot_ext3_61(ef, sw, &vf_ext, 2 * q);
                        let a1 = eval_slot_ext3_61(ef, sw, &vf_ext, 2 * q + 1);
                        let m0 = comb_base_ext3_61(fp, &eq2, &ext_slice[4 * q..4 * q + 2]);
                        let m1 = comb_base_ext3_61(fp, &eq2, &ext_slice[4 * q + 2..4 * q + 4]);
                        let da = ef.sub(a1, a0);
                        let dm = ef.sub(m1, m0);
                        acc[0] = ef.add(acc[0], ef.mul(a0, m0));
                        acc[1] = ef.add(acc[1], ef.add(ef.mul(a0, dm), ef.mul(da, m0)));
                        acc[2] = ef.add(acc[2], ef.mul(da, dm));
                    }
                    acc
                })
                .reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |a, b| [ef.add(a[0], b[0]), ef.add(a[1], b[1]), ef.add(a[2], b[2])],
                );
            let m1_v =
                self.internal_gmask
                    .blind_round_poly("pcs_sc", 1, &z_challenges, rho, &unmasked1);
            let m1_arr = [m1_v[0], m1_v[1], m1_v[2]];
            for ck in &m1_arr {
                tr.absorb_ext3(ck);
            }
            let r_1 = tr.squeeze_ext3(ef, 52);
            sumcheck_rounds.push(m1_arr);
            z_challenges.push(r_1);

            vf_ext.par_iter_mut().for_each(|vf| {
                let h = vf.len() / 2;
                for u in 0..h {
                    let (x0, x1) = (vf[2 * u], vf[2 * u + 1]);
                    vf[u] = ef.add(x0, ef.mul(r_1, ef.sub(x1, x0)));
                }
                vf.truncate(h);
            });
            let eq4 = ef.build_eq_le(&[r_0, r_1]);

            // Streaming Round 2 (`n_poly / 4 -> n_poly / 8`, still 0 GiB table RAM):
            let unmasked2 = (0..usable_slots)
                .into_par_iter()
                .map(|slot| {
                    let sw = &slot_sparse[slot];
                    if sw.is_empty() {
                        return [ef.zero(), ef.zero(), ef.zero()];
                    }
                    let base_idx = slot * n_poly;
                    let r = base_idx >> sh.mc;
                    let c_base = base_idx & (sh.c - 1);
                    let ext_slice = &self.ext[r * sh.w0 + c_base..r * sh.w0 + c_base + n_poly];
                    let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                    for o in 0..(n_poly / 8) {
                        let a0 = eval_slot_ext3_61(ef, sw, &vf_ext, 2 * o);
                        let a1 = eval_slot_ext3_61(ef, sw, &vf_ext, 2 * o + 1);
                        let m0 = comb_base_ext3_61(fp, &eq4, &ext_slice[8 * o..8 * o + 4]);
                        let m1 = comb_base_ext3_61(fp, &eq4, &ext_slice[8 * o + 4..8 * o + 8]);
                        let da = ef.sub(a1, a0);
                        let dm = ef.sub(m1, m0);
                        acc[0] = ef.add(acc[0], ef.mul(a0, m0));
                        acc[1] = ef.add(acc[1], ef.add(ef.mul(a0, dm), ef.mul(da, m0)));
                        acc[2] = ef.add(acc[2], ef.mul(da, dm));
                    }
                    acc
                })
                .reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |a, b| [ef.add(a[0], b[0]), ef.add(a[1], b[1]), ef.add(a[2], b[2])],
                );
            let m2_v =
                self.internal_gmask
                    .blind_round_poly("pcs_sc", 2, &z_challenges, rho, &unmasked2);
            let m2_arr = [m2_v[0], m2_v[1], m2_v[2]];
            for ck in &m2_arr {
                tr.absorb_ext3(ck);
            }
            let r_2 = tr.squeeze_ext3(ef, 53);
            sumcheck_rounds.push(m2_arr);
            z_challenges.push(r_2);

            let n_3 = n_poly / 8;
            vf_ext.par_iter_mut().for_each(|vf| {
                for u in 0..n_3 {
                    let (x0, x1) = (vf[2 * u], vf[2 * u + 1]);
                    vf[u] = ef.add(x0, ef.mul(r_2, ef.sub(x1, x0)));
                }
                vf.truncate(n_3);
            });
            let eq8 = ef.build_eq_le(&[r_0, r_1, r_2]);

            let len3 = total_cells / 8;
            let m_tbl3: Vec<Ext3> = (0..len3)
                .into_par_iter()
                .map(|o| {
                    let idx0 = 8 * o;
                    let r = idx0 >> sh.mc;
                    let c0 = idx0 & (sh.c - 1);
                    comb_base_ext3_61(fp, &eq8, &self.ext[r * sh.w0 + c0..r * sh.w0 + c0 + 8])
                })
                .collect();
            let mut a_tbl3 = vec![ef.zero(); len3];
            a_tbl3[..usable_slots * n_3]
                .par_chunks_mut(n_3)
                .enumerate()
                .for_each(|(slot, dst)| {
                    let sw = &slot_sparse[slot];
                    if sw.is_empty() {
                        return;
                    }
                    for (j, slot) in dst.iter_mut().enumerate() {
                        *slot = eval_slot_ext3_61(ef, sw, &vf_ext, j);
                    }
                });
            (a_tbl3, m_tbl3, len3, 3usize)
        } else {
            let mut a_tbl0 = vec![ef.zero(); total_cells];
            a_tbl0[..usable_slots * n_poly]
                .par_chunks_mut(n_poly)
                .enumerate()
                .for_each(|(slot, dst)| {
                    let sw = &slot_sparse[slot];
                    if sw.is_empty() {
                        return;
                    }
                    for (j, slot) in dst.iter_mut().enumerate() {
                        *slot = eval_slot_u64_61(fp, sw, v_families, j);
                    }
                });

            let half0 = total_cells / 2;
            let eval_r0 = |u: usize| -> [Ext3; 3] {
                let idx0 = 2 * u;
                let r = idx0 >> sh.mc;
                let c0_idx = idx0 & (sh.c - 1);
                let m0 = self.ext[r * sh.w0 + c0_idx];
                let m1 = self.ext[r * sh.w0 + c0_idx + 1];
                let dm = fp.sub(m1, m0);
                let a0 = a_tbl0[idx0];
                let a1 = a_tbl0[idx0 + 1];
                let da = ef.sub(a1, a0);
                [
                    ef.scale(a0, m0),
                    ef.add(ef.scale(a0, dm), ef.scale(da, m0)),
                    ef.scale(da, dm),
                ]
            };
            let unmasked0 = if half0 >= 2048 {
                (0..half0).into_par_iter().map(eval_r0).reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |acc, x| {
                        [
                            ef.add(acc[0], x[0]),
                            ef.add(acc[1], x[1]),
                            ef.add(acc[2], x[2]),
                        ]
                    },
                )
            } else {
                let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                for u in 0..half0 {
                    let x = eval_r0(u);
                    for k in 0..3 {
                        acc[k] = ef.add(acc[k], x[k]);
                    }
                }
                acc
            };
            let masked0_v = self
                .internal_gmask
                .blind_round_poly("pcs_sc", 0, &[], rho, &unmasked0);
            let masked0 = [masked0_v[0], masked0_v[1], masked0_v[2]];
            for ck in &masked0 {
                tr.absorb_ext3(ck);
            }
            let r_0 = tr.squeeze_ext3(ef, 51);
            sumcheck_rounds.push(masked0);
            z_challenges.push(r_0);

            let m_tbl1: Vec<Ext3> = (0..half0)
                .into_par_iter()
                .map(|u| {
                    let idx0 = 2 * u;
                    let r = idx0 >> sh.mc;
                    let c0_idx = idx0 & (sh.c - 1);
                    let m0 = self.ext[r * sh.w0 + c0_idx];
                    let m1 = self.ext[r * sh.w0 + c0_idx + 1];
                    ef.add([m0, 0, 0], ef.scale(r_0, fp.sub(m1, m0)))
                })
                .collect();
            let a_tbl1: Vec<Ext3> = (0..half0)
                .into_par_iter()
                .map(|u| {
                    let (x0, x1) = (a_tbl0[2 * u], a_tbl0[2 * u + 1]);
                    ef.add(x0, ef.mul(r_0, ef.sub(x1, x0)))
                })
                .collect();
            drop(a_tbl0);
            (a_tbl1, m_tbl1, half0, 1usize)
        };

        let mut scratch = Vec::with_capacity(cur_len / 2);
        for round in start_round..m_bits {
            let half = cur_len / 2;
            let eval_pair = |u: usize| -> [Ext3; 3] {
                let (a0, a1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                let (m0, m1) = (m_tbl[2 * u], m_tbl[2 * u + 1]);
                let da = ef.sub(a1, a0);
                let dm = ef.sub(m1, m0);
                [
                    ef.mul(a0, m0),
                    ef.add(ef.mul(a0, dm), ef.mul(da, m0)),
                    ef.mul(da, dm),
                ]
            };
            let unmasked = if half >= 2048 {
                (0..half).into_par_iter().map(eval_pair).reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |acc, x| {
                        [
                            ef.add(acc[0], x[0]),
                            ef.add(acc[1], x[1]),
                            ef.add(acc[2], x[2]),
                        ]
                    },
                )
            } else {
                let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                for u in 0..half {
                    let x = eval_pair(u);
                    for k in 0..3 {
                        acc[k] = ef.add(acc[k], x[k]);
                    }
                }
                acc
            };
            let masked_v = self.internal_gmask.blind_round_poly(
                "pcs_sc",
                round,
                &z_challenges,
                rho,
                &unmasked,
            );
            let masked = [masked_v[0], masked_v[1], masked_v[2]];
            for ck in &masked {
                tr.absorb_ext3(ck);
            }
            let r_i = tr.squeeze_ext3(ef, 51 + round as u64);
            sumcheck_rounds.push(masked);
            z_challenges.push(r_i);

            if half >= 4096 {
                scratch.clear();
                (0..half)
                    .into_par_iter()
                    .map(|u| {
                        let (x0, x1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                        ef.add(x0, ef.mul(r_i, ef.sub(x1, x0)))
                    })
                    .collect_into_vec(&mut scratch);
                std::mem::swap(&mut a_tbl, &mut scratch);

                scratch.clear();
                (0..half)
                    .into_par_iter()
                    .map(|u| {
                        let (x0, x1) = (m_tbl[2 * u], m_tbl[2 * u + 1]);
                        ef.add(x0, ef.mul(r_i, ef.sub(x1, x0)))
                    })
                    .collect_into_vec(&mut scratch);
                std::mem::swap(&mut m_tbl, &mut scratch);
            } else {
                for u in 0..half {
                    let (a0, a1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                    a_tbl[u] = ef.add(a0, ef.mul(r_i, ef.sub(a1, a0)));
                    let (m0, m1) = (m_tbl[2 * u], m_tbl[2 * u + 1]);
                    m_tbl[u] = ef.add(m0, ef.mul(r_i, ef.sub(m1, m0)));
                }
                a_tbl.truncate(half);
                m_tbl.truncate(half);
            }
            cur_len = half;
        }
        drop(scratch);

        // `m_eval = M~(z_col, z_row)` is already uniform on Ext3 thanks to the 4 ZK data-blinding rows!
        let m_eval = m_tbl[0];
        let y_g = self.internal_gmask.eval_at("pcs_sc", &z_challenges);
        debug_assert_eq!(
            ef.add(ef.mul(a_tbl[0], m_eval), ef.mul(rho, y_g)),
            eval_poly_ext3(
                ef,
                sumcheck_rounds.last().unwrap(),
                *z_challenges.last().unwrap()
            )
        );
        tr.absorb_ext3(&m_eval);

        (gmask_sum, sumcheck_rounds, z_challenges, m_eval)
    }

    /// Run `GMask61`-blinded `(mc + mr)`-round `SlotLinearClaim` sumcheck + rank-preserved `w0`-round
    /// coefficient sumcheck, returning `(header, F^{(0)}(X))` ready for WHIR coset folding!
    fn prove_matrix_to_f0(
        &self,
        log_n: usize,
        v_families: &[Vec<u64>],
        claims: &[SlotLinearClaim],
        tr: &mut PcsTranscript,
    ) -> (WhirMatrixHeader61, Vec<Ext3>) {
        let fp = &self.ef.fp;
        let ef = &self.ef;
        let sh = &self.shape;
        let m_bits = sh.mc + sh.mr;

        let (gmask_sum, sumcheck_rounds, z_challenges, m_eval) =
            self.run_slot_row_sumcheck_61(log_n, v_families, claims, tr);

        // 3. Build `u_eval(X)`, `P_gmask(X)`, `Z_gm(X)`, and `u_prox(X)` of degree `< w0`:
        let z_col = &z_challenges[..sh.mc];
        let z_row = &z_challenges[sh.mc..];
        let eq_row = ef.build_eq_le(z_row);
        let u_eval = combine_rows_ext3_whir(fp, &self.ext, sh.w0, &eq_row);

        let p_gmask = pack_3_rows_ext3(&self.ext, sh.w0, sh.rd);
        let z_gm = pack_3_rows_ext3(&self.ext, sh.w0, sh.rd + 3);

        let (v_g, v_at) = build_internal_gmask_weight_vecs(ef, m_bits, &z_challenges);
        let mut s_g = ef.zero();
        let mut s_at = ef.zero();
        for u in 0..v_g.len() {
            s_g = ef.add(s_g, ef.mul(v_g[u], z_gm[u]));
            s_at = ef.add(s_at, ef.mul(v_at[u], z_gm[u]));
        }
        tr.absorb_ext3(&s_g);
        tr.absorb_ext3(&s_at);
        let mut beta_gm = tr.squeeze_ext3(ef, 300);
        if beta_gm == [0, 0, 0] {
            beta_gm = [1, 0, 0];
        }
        let p_gmask_hat: Vec<Ext3> = p_gmask
            .par_iter()
            .zip(z_gm.par_iter())
            .map(|(&p, &z)| ef.add(p, ef.mul(beta_gm, z)))
            .collect();

        // 4. `w0`-round coefficient sumcheck reducing `<V_eval, u_eval> + <V_gm, P_gmask_hat>` to `zeta in Ext3^{w0}`:
        let lam1 = tr.squeeze_ext3(ef, 301);
        let lam2 = tr.squeeze_ext3(ef, 302);

        let eq_col = ef.build_eq_le(z_col);
        let mut v_eval_pad = vec![ef.zero(); sh.w0];
        v_eval_pad[..sh.c].copy_from_slice(&eq_col);

        let mut v_gm_pad = vec![ef.zero(); sh.w0];
        for u in 0..v_g.len() {
            v_gm_pad[u] = ef.add(ef.mul(lam1, v_g[u]), ef.mul(lam2, v_at[u]));
        }

        let lg_w0 = sh.mc + 1;
        let mut u_ev_cur = u_eval.clone();
        let mut p_gm_cur = p_gmask_hat.clone();
        let mut coeff_sumcheck_rounds = Vec::with_capacity(lg_w0);
        let mut zeta = Vec::with_capacity(lg_w0);
        let mut len_c = sh.w0;

        for r_idx in 0..lg_w0 {
            let half = len_c / 2;
            let eval_c = |u: usize| -> [Ext3; 3] {
                let (ve0, ve1) = (v_eval_pad[2 * u], v_eval_pad[2 * u + 1]);
                let (ue0, ue1) = (u_ev_cur[2 * u], u_ev_cur[2 * u + 1]);
                let dve = ef.sub(ve1, ve0);
                let due = ef.sub(ue1, ue0);

                let (vg0, vg1) = (v_gm_pad[2 * u], v_gm_pad[2 * u + 1]);
                let (pg0, pg1) = (p_gm_cur[2 * u], p_gm_cur[2 * u + 1]);
                let dvg = ef.sub(vg1, vg0);
                let dpg = ef.sub(pg1, pg0);

                let c0 = ef.add(ef.mul(ve0, ue0), ef.mul(vg0, pg0));
                let c1 = ef.add(
                    ef.add(ef.mul(ve0, due), ef.mul(dve, ue0)),
                    ef.add(ef.mul(vg0, dpg), ef.mul(dvg, pg0)),
                );
                let c2 = ef.add(ef.mul(dve, due), ef.mul(dvg, dpg));
                [c0, c1, c2]
            };
            let poly = if half >= 2048 {
                (0..half).into_par_iter().map(eval_c).reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |acc, x| {
                        [
                            ef.add(acc[0], x[0]),
                            ef.add(acc[1], x[1]),
                            ef.add(acc[2], x[2]),
                        ]
                    },
                )
            } else {
                let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                for u in 0..half {
                    let x = eval_c(u);
                    for k in 0..3 {
                        acc[k] = ef.add(acc[k], x[k]);
                    }
                }
                acc
            };
            for ck in &poly {
                tr.absorb_ext3(ck);
            }
            let z_i = tr.squeeze_ext3(ef, 400 + r_idx as u64);
            coeff_sumcheck_rounds.push(poly);
            zeta.push(z_i);

            let fold_in = |v: &mut Vec<Ext3>| {
                if half >= 4096 {
                    *v = (0..half)
                        .into_par_iter()
                        .map(|u| ef.add(v[2 * u], ef.mul(z_i, ef.sub(v[2 * u + 1], v[2 * u]))))
                        .collect();
                } else {
                    for u in 0..half {
                        let (x0, x1) = (v[2 * u], v[2 * u + 1]);
                        v[u] = ef.add(x0, ef.mul(z_i, ef.sub(x1, x0)));
                    }
                    v.truncate(half);
                }
            };
            fold_in(&mut v_eval_pad);
            fold_in(&mut u_ev_cur);
            fold_in(&mut v_gm_pad);
            fold_in(&mut p_gm_cur);
            len_c = half;
        }

        let u_eval_at_zeta = u_ev_cur[0];
        let p_gmask_hat_at_zeta = p_gm_cur[0];
        tr.absorb_ext3(&u_eval_at_zeta);
        tr.absorb_ext3(&p_gmask_hat_at_zeta);

        // 5. Proximity RLC over ALL non-prox rows `0 .. rd + 6` + `P_prox` (`rd + 6 .. rd + 9`):
        let gamma = tr.squeeze_ext3(ef, 500);
        let non_prox = sh.rd + 6;
        let mut prox_weights = Vec::with_capacity(sh.r_total);
        let mut g_pw = ef.one();
        for _ in 0..non_prox {
            prox_weights.push(g_pw);
            g_pw = ef.mul(g_pw, gamma);
        }
        prox_weights.push([1, 0, 0]);
        prox_weights.push([0, 1, 0]);
        prox_weights.push([0, 0, 1]);
        let u_prox = combine_rows_ext3_whir(fp, &self.ext, sh.w0, &prox_weights);
        let u_prox_at_zeta = eval_mle_ext3(ef, &u_prox, &zeta);
        tr.absorb_ext3(&u_prox_at_zeta);

        // 6. Combine `F^{(0)}(X) = u_prox(X) + theta_1 * u_eval(X) + theta_2 * P_gmask_hat(X)`:
        let theta1 = tr.squeeze_ext3(ef, 501);
        let theta2 = tr.squeeze_ext3(ef, 502);
        let f0_poly: Vec<Ext3> = (0..sh.w0)
            .into_par_iter()
            .map(|k| {
                ef.add(
                    u_prox[k],
                    ef.add(ef.mul(theta1, u_eval[k]), ef.mul(theta2, p_gmask_hat[k])),
                )
            })
            .collect();

        (
            WhirMatrixHeader61 {
                gmask_sum,
                sumcheck_rounds,
                m_eval,
                z_gm_masks: [s_g, s_at],
                coeff_sumcheck_rounds,
                u_eval_at_zeta,
                p_gmask_hat_at_zeta,
                u_prox_at_zeta,
            },
            f0_poly,
        )
    }
}

impl WhirShape61 {
    fn root_shape_tag(&self) -> [u8; 24] {
        let mut b = [0u8; 24];
        b[0..8].copy_from_slice(&self.p.to_le_bytes());
        b[8] = self.mr as u8;
        b[9] = self.mc as u8;
        b[10..12].copy_from_slice(&(self.t_queries as u16).to_le_bytes());
        b[12] = self.blow as u8;
        b[13] = self.k_schedule.len() as u8;
        for (i, &k) in self.k_schedule.iter().take(10).enumerate() {
            b[14 + i] = k as u8;
        }
        b
    }
}

type WhirMatrixHeaderEval = (Vec<Ext3>, Ext3, Ext3, Ext3, Ext3, Vec<Ext3>, Ext3);
type WhirCascadeProof = (
    Vec<WhirFoldRoundProof61>,
    Vec<Vec<[Ext3; 3]>>,
    Ext3,
    Vec<Ext3>,
    Vec<usize>,
);
type WhirRowSumcheckOutput = (
    WhirRowSumcheckPart61,
    Vec<Ext3>,
    Ext3,
    Vec<Ext3>,
    Vec<Ext3>,
    Vec<Ext3>,
    Vec<Ext3>,
);
type WhirHoistedEvalVFamilies = (
    Vec<Vec<u64>>,
    [[[usize; 3]; 15]; 7],
    [[[usize; 3]; 14]; 7],
    [[[usize; 3]; 4]; 7],
);

/// Replay `WhirMatrixHeader61` on the verifier (`0` `O(w0)` allocations! Evaluates `V_eval(zeta)` in `O(mc)` muls
/// and `V_gm(zeta)` in `O(mr + mc)` muls!).
/// Returns `(z_row, beta_gm, gamma, theta1, theta2, zeta, f0_at_zeta)`.
#[allow(clippy::too_many_arguments)]
fn verify_matrix_header_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    log_n: usize,
    v_families: &[Vec<u64>],
    claims: &[SlotLinearClaim],
    hdr: &WhirMatrixHeader61,
    tr: &mut PcsTranscript,
) -> Result<WhirMatrixHeaderEval, String> {
    let fp = &ef.fp;
    let n_poly = 1usize << log_n;
    if log_n > shape.mc || !shape.c.is_multiple_of(n_poly) {
        return Err("invalid log_n vs shape.mc".into());
    }
    let m_bits = shape.mc + shape.mr;
    let lg_w0 = shape.mc + 1;
    if hdr.sumcheck_rounds.len() != m_bits || hdr.coeff_sumcheck_rounds.len() != lg_w0 {
        return Err("WhirMatrixHeader61 sumcheck length mismatch".into());
    }
    let polys_per_row = shape.c / n_poly;
    let usable_slots = shape.usable_rows * polys_per_row;

    tr.absorb_bytes(&shape.root_shape_tag());
    tr.absorb_bytes(&(claims.len() as u64).to_le_bytes());
    for cl in claims {
        tr.absorb_bytes(&cl.rhs.to_le_bytes());
    }

    let beta = tr.squeeze_ext3(ef, 1);
    let mut y_batch = ef.zero();
    let mut beta_pows = Vec::with_capacity(claims.len());
    let mut b_pw = ef.one();
    for cl in claims {
        y_batch = ef.add(y_batch, ef.scale(b_pw, cl.rhs % fp.p));
        beta_pows.push(b_pw);
        b_pw = ef.mul(b_pw, beta);
    }

    // 1. Verify `GMask61`-blinded `(mc + mr)`-round sumcheck:
    let (rho, z_challenges, masked_term) = verify_gmask61_rounds(
        ef,
        tr,
        y_batch,
        hdr.gmask_sum,
        &hdr.sumcheck_rounds
            .iter()
            .map(|r| r.to_vec())
            .collect::<Vec<_>>(),
        2,
        50,
    )?;

    // Evaluate public `A~(z_challenges)` in `O(|claims| + N + usable_slots)`:
    let z_j = &z_challenges[..log_n];
    let z_slot = &z_challenges[log_n..];
    let eq_j = ef.build_eq_le(z_j);
    let eq_slot = ef.build_eq_le(z_slot);
    let vf_evals: Vec<Ext3> = v_families
        .par_iter()
        .map(|vf| {
            let mut acc = ef.zero();
            for (j, &vj) in vf.iter().enumerate() {
                if vj != 0 {
                    acc = ef.add(acc, ef.scale(eq_j[j], vj));
                }
            }
            acc
        })
        .collect();

    let mut a_eval = ef.zero();
    for (q_idx, cl) in claims.iter().enumerate() {
        let mut cl_ev = ef.zero();
        for (vf_idx, slot_terms) in &cl.terms {
            let mut slot_ev = ef.zero();
            for &(slot, w_u64) in slot_terms {
                if slot >= usable_slots {
                    return Err("claim references ZK blinding slot".into());
                }
                slot_ev = ef.add(slot_ev, ef.scale(eq_slot[slot], w_u64));
            }
            cl_ev = ef.add(cl_ev, ef.mul(slot_ev, vf_evals[*vf_idx]));
        }
        a_eval = ef.add(a_eval, ef.mul(beta_pows[q_idx], cl_ev));
    }

    // Solve `y_g` uniquely from `a_eval * m_eval + rho * y_g == masked_term`:
    let rho_inv = ef.inv(rho);
    let y_g = ef.mul(rho_inv, ef.sub(masked_term, ef.mul(a_eval, hdr.m_eval)));

    tr.absorb_ext3(&hdr.m_eval);
    tr.absorb_ext3(&hdr.z_gm_masks[0]);
    tr.absorb_ext3(&hdr.z_gm_masks[1]);
    let mut beta_gm = tr.squeeze_ext3(ef, 300);
    if beta_gm == [0, 0, 0] {
        beta_gm = [1, 0, 0];
    }
    let lam1 = tr.squeeze_ext3(ef, 301);
    let lam2 = tr.squeeze_ext3(ef, 302);

    // 2. Verify `w0`-round coefficient sumcheck:
    let g_hat = ef.add(hdr.gmask_sum, ef.mul(beta_gm, hdr.z_gm_masks[0]));
    let y_g_hat = ef.add(y_g, ef.mul(beta_gm, hdr.z_gm_masks[1]));
    let mut running = ef.add(
        hdr.m_eval,
        ef.add(ef.mul(lam1, g_hat), ef.mul(lam2, y_g_hat)),
    );
    let mut zeta = Vec::with_capacity(lg_w0);
    for (r_idx, poly) in hdr.coeff_sumcheck_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = ef.add(poly[0], ef.add(poly[1], poly[2]));
        if ef.add(p0, p1) != running {
            return Err(format!("WHIR coeff sumcheck round {r_idx} failed"));
        }
        for ck in poly {
            tr.absorb_ext3(ck);
        }
        let z_i = tr.squeeze_ext3(ef, 400 + r_idx as u64);
        zeta.push(z_i);
        running = eval_poly_ext3(ef, poly, z_i);
    }

    // Evaluate `V_eval(zeta) = eq(z_col, zeta[..mc]) * (1 - zeta[mc])` in `O(mc)` muls!
    let z_col = &z_challenges[..shape.mc];
    let mut v_eval_zeta = ef.sub(ef.one(), zeta[shape.mc]);
    for (&zc, &zt) in z_col.iter().zip(zeta[..shape.mc].iter()) {
        let eq_i = ef.add(
            ef.mul(ef.sub(ef.one(), zc), ef.sub(ef.one(), zt)),
            ef.mul(zc, zt),
        );
        v_eval_zeta = ef.mul(v_eval_zeta, eq_i);
    }

    // Evaluate `V_gm(zeta)` over its `3 * m_bits <= 96` non-zero prefix entries in `< 300` muls!
    let (v_g, v_at) = build_internal_gmask_weight_vecs(ef, m_bits, &z_challenges);
    let n_gm = v_g.len();
    let k_gm = bitlen_usize(n_gm.saturating_sub(1)).max(1);
    let eq_zeta_lo = ef.build_eq_le(&zeta[..k_gm]);
    let mut zero_hi = ef.one();
    for &zt in &zeta[k_gm..] {
        zero_hi = ef.mul(zero_hi, ef.sub(ef.one(), zt));
    }
    let mut v_gm_lo = ef.zero();
    for u in 0..n_gm {
        let comb = ef.add(ef.mul(lam1, v_g[u]), ef.mul(lam2, v_at[u]));
        v_gm_lo = ef.add(v_gm_lo, ef.mul(comb, eq_zeta_lo[u]));
    }
    let v_gm_zeta = ef.mul(v_gm_lo, zero_hi);

    let want_term = ef.add(
        ef.mul(v_eval_zeta, hdr.u_eval_at_zeta),
        ef.mul(v_gm_zeta, hdr.p_gmask_hat_at_zeta),
    );
    if running != want_term {
        return Err("WHIR coeff sumcheck terminal check failed (GMask or u_eval forgery!)".into());
    }

    tr.absorb_ext3(&hdr.u_eval_at_zeta);
    tr.absorb_ext3(&hdr.p_gmask_hat_at_zeta);
    let gamma = tr.squeeze_ext3(ef, 500);
    tr.absorb_ext3(&hdr.u_prox_at_zeta);
    let theta1 = tr.squeeze_ext3(ef, 501);
    let theta2 = tr.squeeze_ext3(ef, 502);

    let f0_at_zeta = ef.add(
        hdr.u_prox_at_zeta,
        ef.add(
            ef.mul(theta1, hdr.u_eval_at_zeta),
            ef.mul(theta2, hdr.p_gmask_hat_at_zeta),
        ),
    );
    let z_row = z_challenges[shape.mc..].to_vec();
    Ok((z_row, beta_gm, gamma, theta1, theta2, zeta, f0_at_zeta))
}

fn build_internal_gmask_weight_vecs(
    ef: &Ext3Field,
    m_bits: usize,
    r: &[Ext3],
) -> (Vec<Ext3>, Vec<Ext3>) {
    let n_u = m_bits * 3;
    let scale_g = ef.fp.pow(2, (m_bits - 1) as u64);
    let two_scale_g = ef.fp.mul(2, scale_g);
    let mut v_g = vec![ef.zero(); n_u];
    let mut v_at = vec![ef.zero(); n_u];
    for (j, &rj) in r.iter().enumerate() {
        v_g[3 * j] = [two_scale_g, 0, 0];
        v_g[3 * j + 1] = [scale_g, 0, 0];
        v_g[3 * j + 2] = [scale_g, 0, 0];
        v_at[3 * j] = ef.one();
        v_at[3 * j + 1] = rj;
        v_at[3 * j + 2] = ef.mul(rj, rj);
    }
    (v_g, v_at)
}

/// Squeeze an `Ext3` OOD point strictly outside `F_p` (`z[1] != 0 || z[2] != 0`) so `x - z != 0` for all `x in F_p`.
fn squeeze_non_base_ood_61(ef: &Ext3Field, tr: &mut PcsTranscript, tag: u64) -> Ext3 {
    let mut z = tr.squeeze_ext3(ef, tag);
    if z[1] == 0 && z[2] == 0 {
        z[1] = 1;
    }
    z
}

/// Core BaseFold + WHIR OOD-Shifted Multi-Round Coset-Folding Cascade:
/// Verifies BOTH any initial multilinear point claims `(pt_i, val_i)` on `f0_poly` AND per-round OOD
/// univariate shift claims `f^{(r)}(z_ood_r) == y_ood_r` via lockstep sumcheck + trajectory-chained
/// $2^{k_r}$-ary coset-fiber Merkle multiproofs!
fn prove_whir_cascade_core_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    mut cur_poly: Vec<Ext3>,
    init_mle_pts: &[Vec<Ext3>],
    tr: &mut PcsTranscript,
) -> WhirCascadeProof {
    let fp = &ef.fp;
    let num_rounds = shape.k_schedule.len();
    let mut cur_level = shape.level0;

    // Maintain active folded weight table `w_acc` of length `cur_poly.len()` combining `init_mle_pts`:
    let mut w_acc = vec![ef.zero(); cur_poly.len()];
    for (idx, pt) in init_mle_pts.iter().enumerate() {
        let gamma_m = tr.squeeze_ext3(ef, 600 + idx as u64);
        let eq_pt = ef.build_eq_le(pt);
        for (dst, &e) in w_acc.iter_mut().zip(eq_pt.iter()) {
            *dst = ef.add(*dst, ef.mul(gamma_m, e));
        }
    }

    struct PendingFoldTree {
        ood_prev: Ext3,
        level: CosetLevel61,
        kr_next: usize,
        cw_ext3: Vec<Ext3>,
        tree: Vec<Vec<[u8; 32]>>,
        root: [u8; 32],
    }

    let mut pending_trees: Vec<PendingFoldTree> = Vec::with_capacity(num_rounds.saturating_sub(1));
    let mut round_lockstep_scs: Vec<Vec<[Ext3; 3]>> = Vec::with_capacity(num_rounds);

    for r in 0..num_rounds {
        let kr = shape.k_schedule[r];
        let w_len = cur_poly.len();
        let z_ood = squeeze_non_base_ood_61(ef, tr, 700 + (r as u64) * 10);
        let ood_eval = eval_poly_ext3(ef, &cur_poly, z_ood);
        tr.absorb_ext3(&ood_eval);

        let tau_ood = tr.squeeze_ext3(ef, 701 + (r as u64) * 10);
        // Add `tau_ood * [1, z_ood, z_ood^2, ..., z_ood^{w_len - 1}]` into `w_acc` via tensor expansion!
        let ood_tensor = build_monomial_tensor_ext3(ef, z_ood, w_len.trailing_zeros() as usize);
        w_acc
            .par_iter_mut()
            .zip(ood_tensor.par_iter())
            .for_each(|(dst, &ot)| {
                *dst = ef.add(*dst, ef.mul(tau_ood, ot));
            });

        // Run `kr` lockstep quadratic sumcheck rounds (`alpha_{r, 0..kr}` ARE the $2^{kr}$-ary coset fold challenges!):
        let mut sc_rounds = Vec::with_capacity(kr);
        let mut cur_w_len = w_len;
        for step in 0..kr {
            let half = cur_w_len / 2;
            let eval_p = |u: usize| -> [Ext3; 3] {
                let (w0, w1) = (w_acc[2 * u], w_acc[2 * u + 1]);
                let (f0, f1) = (cur_poly[2 * u], cur_poly[2 * u + 1]);
                let dw = ef.sub(w1, w0);
                let df = ef.sub(f1, f0);
                [
                    ef.mul(w0, f0),
                    ef.add(ef.mul(w0, df), ef.mul(dw, f0)),
                    ef.mul(dw, df),
                ]
            };
            let poly = if half >= 2048 {
                (0..half).into_par_iter().map(eval_p).reduce(
                    || [ef.zero(), ef.zero(), ef.zero()],
                    |a, b| [ef.add(a[0], b[0]), ef.add(a[1], b[1]), ef.add(a[2], b[2])],
                )
            } else {
                let mut acc = [ef.zero(), ef.zero(), ef.zero()];
                for u in 0..half {
                    let x = eval_p(u);
                    for k in 0..3 {
                        acc[k] = ef.add(acc[k], x[k]);
                    }
                }
                acc
            };
            for ck in &poly {
                tr.absorb_ext3(ck);
            }
            let alpha = tr.squeeze_ext3(ef, 702 + (r as u64) * 10 + step as u64);
            sc_rounds.push(poly);

            if half >= 4096 {
                w_acc = (0..half)
                    .into_par_iter()
                    .map(|u| {
                        ef.add(
                            w_acc[2 * u],
                            ef.mul(alpha, ef.sub(w_acc[2 * u + 1], w_acc[2 * u])),
                        )
                    })
                    .collect();
                cur_poly = (0..half)
                    .into_par_iter()
                    .map(|u| {
                        ef.add(
                            cur_poly[2 * u],
                            ef.mul(alpha, ef.sub(cur_poly[2 * u + 1], cur_poly[2 * u])),
                        )
                    })
                    .collect();
            } else {
                for u in 0..half {
                    let (w0, w1) = (w_acc[2 * u], w_acc[2 * u + 1]);
                    w_acc[u] = ef.add(w0, ef.mul(alpha, ef.sub(w1, w0)));
                    let (f0, f1) = (cur_poly[2 * u], cur_poly[2 * u + 1]);
                    cur_poly[u] = ef.add(f0, ef.mul(alpha, ef.sub(f1, f0)));
                }
                w_acc.truncate(half);
                cur_poly.truncate(half);
            }
            cur_w_len = half;
        }
        round_lockstep_scs.push(sc_rounds);
        cur_level = cur_level.fold(fp, kr);

        if r + 1 < num_rounds {
            let kr_next = shape.k_schedule[r + 1];
            let cw_ext3 = encode_ext3_poly_on_level(fp, &cur_level, &cur_poly);
            let n_fibers = cur_level.npts >> kr_next;
            let b_next = 1usize << kr_next;
            let leaves: Vec<[u8; 32]> = (0..n_fibers)
                .into_par_iter()
                .map(|f_idx| {
                    let js = cur_level.fiber_point_indices(kr_next, f_idx);
                    let mut fv = Vec::with_capacity(b_next);
                    for j in js {
                        fv.push(cw_ext3[j]);
                    }
                    hash_whir_fold_fiber(r + 1, f_idx, &fv)
                })
                .collect();
            let tree = build_whir_tree(leaves);
            let root = tree.last().unwrap()[0];
            tr.absorb_bytes(&root);
            pending_trees.push(PendingFoldTree {
                ood_prev: ood_eval,
                level: cur_level,
                kr_next,
                cw_ext3,
                tree,
                root,
            });
        } else {
            // Final round (`r == num_rounds - 1`): absorb `ood_eval` & `final_poly`!
            tr.absorb_poly3("WHIR61_FINAL_POLY", &cur_poly);
            // Squeeze `t_queries` distinct sorted Stage-0 fiber indices!
            let n_leaves_0 = shape.n0 >> shape.k_schedule[0];
            let mut s0_fibers = tr.squeeze_distinct_cols(shape.t_queries, n_leaves_0);
            s0_fibers.sort_unstable();

            // Trace trajectory indices across `r = 1 .. num_rounds - 1` and extract deduplicated fibers:
            let mut cur_pts = s0_fibers.clone(); // point indices in D_1!
            let mut fold_proofs = Vec::with_capacity(pending_trees.len());
            for pt in &pending_trees {
                let mut uniq_set = BTreeSet::new();
                for &p_idx in &cur_pts {
                    let (f_next, _) = pt.level.locate_in_fiber(pt.kr_next, p_idx);
                    uniq_set.insert(f_next);
                }
                let uniq_fibers: Vec<usize> = uniq_set.into_iter().collect();
                let mut opened_fibers =
                    Vec::with_capacity(uniq_fibers.len() * (1usize << pt.kr_next));
                for &f_idx in &uniq_fibers {
                    for j in pt.level.fiber_point_indices(pt.kr_next, f_idx) {
                        opened_fibers.push(pt.cw_ext3[j]);
                    }
                }
                let siblings = extract_siblings(&pt.tree, &uniq_fibers);
                fold_proofs.push(WhirFoldRoundProof61 {
                    ood_eval_prev: pt.ood_prev,
                    root: pt.root,
                    opened_fibers,
                    siblings,
                });
                cur_pts = uniq_fibers;
            }
            return (
                fold_proofs,
                round_lockstep_scs,
                ood_eval,
                cur_poly,
                s0_fibers,
            );
        }
    }
    unreachable!()
}

/// Pack `round_lockstep_scs` cleanly inside `final_poly`? No, let's include `lockstep_sc` directly on
/// `WhirFoldRoundProof61` + final round so every byte is explicit and structured!
/// Wait: let's add `lockstep_scs: Vec<[Ext3; 3]>` right into a small helper or `WhirOpeningProof61`!
/// Even cleaner: notice `round_lockstep_scs` flattened has `sum(k_schedule)` triples `[Ext3; 3]` (`<= 14 * 72 B = 1 KiB`)!
/// Let's store `lockstep_scs: Vec<[Ext3; 3]>` in `WhirCascadeTail61` used by both `WhirOpeningProof61` and `WhirJointOpeningProof61`!
fn build_monomial_tensor_ext3(ef: &Ext3Field, z: Ext3, log_w: usize) -> Vec<Ext3> {
    // Entry `idx` = `z^idx = prod_{b=0}^{log_w - 1} (z^{2^b})^{idx_b}` (LSB-first contiguous doubling):
    let mut v = Vec::with_capacity(1usize << log_w);
    v.push(ef.one());
    let mut z_pow = z;
    for _ in 0..log_w {
        let cur_len = v.len();
        for i in 0..cur_len {
            let prod = ef.mul(v[i], z_pow);
            v.push(prod);
        }
        z_pow = ef.mul(z_pow, z_pow);
    }
    v
}

fn eval_mle_ext3(ef: &Ext3Field, table: &[Ext3], pt: &[Ext3]) -> Ext3 {
    let eq = ef.build_eq_le(pt);
    assert_eq!(table.len(), eq.len());
    let mut acc = ef.zero();
    for (&t, &e) in table.iter().zip(eq.iter()) {
        acc = ef.add(acc, ef.mul(t, e));
    }
    acc
}

/// Invert `B = 2^{kr}` fiber evaluations `[P(x_0 * zeta^0), ..., P(x_0 * zeta^{B-1})]` and fold at `eq_alpha`:
/// Returns `P_fold(x_0^B) = sum_{b=0}^{B-1} eq_alpha[b] * P_b(x_0^B)` (`0` runtime inversions; uses pre-inverted `x0_inv`).
fn fold_fiber_evals_ext3(
    ef: &Ext3Field,
    vals: &[Ext3],
    kr: usize,
    x0_inv: u64,
    zeta_inv_pows: &[u64],
    b_inv: u64,
    eq_alpha: &[Ext3],
) -> Ext3 {
    let b_len = 1usize << kr;
    debug_assert_eq!(vals.len(), b_len);
    let fp = &ef.fp;
    let mut buf = vals.to_vec();

    // Radix-2 inverse butterfly over `Ext3` with basefield `u64` twiddles:
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
                    let v = ef.scale(buf[st + j + half], zeta_inv_pows[j * step]);
                    buf[st + j] = ef.add(u, v);
                    buf[st + j + half] = ef.sub(u, v);
                }
            }
            len <<= 1;
        }
    }

    let mut acc = ef.zero();
    let mut scale_cur = b_inv; // B^{-1} * x0^{-b} mod p
    for b in 0..b_len {
        let pb_y = ef.scale(buf[b], scale_cur);
        acc = ef.add(acc, ef.mul(eq_alpha[b], pb_y));
        scale_cur = fp.mul(scale_cur, x0_inv);
    }
    acc
}

fn batch_invert_fp(fp: &FastPrime61, xs: &[u64]) -> Vec<u64> {
    let n = xs.len();
    if n == 0 {
        return Vec::new();
    }
    let mut pref = Vec::with_capacity(n);
    let mut cur = 1u64;
    for &x in xs {
        assert!(x != 0);
        pref.push(cur);
        cur = fp.mul(cur, x);
    }
    let mut inv_all = fp.inv(cur);
    let mut out = vec![0u64; n];
    for i in (0..n).rev() {
        out[i] = fp.mul(inv_all, pref[i]);
        inv_all = fp.mul(inv_all, xs[i]);
    }
    out
}

impl WhirCommittedPcs61 {
    /// Open a batch of `SlotLinearClaim`s against `self.root` using `GMask61` + multi-round $2^k$-ary WHIR!
    pub fn open_whir_slot_claims(
        &self,
        log_n: usize,
        v_families: &[Vec<u64>],
        claims: &[SlotLinearClaim],
        context: &[u8; 32],
    ) -> WhirOpeningBundle61 {
        let mut tr = PcsTranscript::new("WHIR61_OPEN", self.ef.fp.p, &self.root, context);
        let (header, f0_poly) = self.prove_matrix_to_f0(log_n, v_families, claims, &mut tr);
        // Extract `zeta` by replaying the deterministic transcript? Even simpler: return `zeta` from `prove_matrix_to_f0`!
        // Let's recover `zeta` directly by replaying `verify_matrix_header_61` on a cloned initial transcript!
        let mut tr_check = PcsTranscript::new("WHIR61_OPEN", self.ef.fp.p, &self.root, context);
        let (_, _, _, _, _, zeta, _) = verify_matrix_header_61(
            &self.ef,
            &self.shape,
            log_n,
            v_families,
            claims,
            &header,
            &mut tr_check,
        )
        .expect("honest matrix header must self-verify");

        let (fold_rounds, lockstep_scs, final_ood_eval, final_poly, s0_fibers) =
            prove_whir_cascade_core_61(&self.ef, &self.shape, f0_poly, &[zeta], &mut tr);
        let (s0_fiber_vals, s0_salts, s0_siblings) = self.open_stage0_fibers(&s0_fibers);

        WhirOpeningBundle61 {
            proof: WhirOpeningProof61 {
                header,
                s0_fiber_vals,
                s0_salts,
                s0_siblings,
                fold_rounds,
                final_ood_eval,
                final_poly,
            },
            lockstep_scs,
        }
    }
}

/// Self-contained serialized `WhirPcs61` opening bundle (`WhirOpeningProof61` + lockstep sumcheck rounds).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirOpeningBundle61 {
    pub proof: WhirOpeningProof61,
    pub lockstep_scs: Vec<Vec<[Ext3; 3]>>,
}

impl WhirOpeningBundle61 {
    pub fn to_bytes(&self, p: u64, out: &mut Vec<u8>) {
        self.proof.to_bytes(p, out);
        out.push(self.lockstep_scs.len() as u8);
        let mut flat = Vec::new();
        for rd in &self.lockstep_scs {
            out.push(rd.len() as u8);
            for poly in rd {
                for e in poly {
                    flat.extend_from_slice(e);
                }
            }
        }
        pack_u64_bits_le(&flat, 61, out);
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>, p: u64) -> Result<Self, String> {
        let proof = WhirOpeningProof61::from_bytes(cur, p)?;
        let n_r = cur.read_u8()? as usize;
        if n_r == 0 || n_r > 16 {
            return Err("invalid lockstep_scs round count".into());
        }
        let mut lens = Vec::with_capacity(n_r);
        let mut tot_triples = 0usize;
        for _ in 0..n_r {
            let l = cur.read_u8()? as usize;
            if l > 8 {
                return Err("invalid lockstep_scs inner len".into());
            }
            lens.push(l);
            tot_triples += l;
        }
        let ext_vec = unpack_ext3_slice(cur, tot_triples * 3, p)?;
        if ext_vec.len() != tot_triples * 3 {
            return Err("lockstep_scs unpacked Ext3 count mismatch".into());
        }
        let mut idx = 0usize;
        let mut lockstep_scs = Vec::with_capacity(n_r);
        for l in lens {
            let mut v = Vec::with_capacity(l);
            for _ in 0..l {
                v.push([ext_vec[idx], ext_vec[idx + 1], ext_vec[idx + 2]]);
                idx += 3;
            }
            lockstep_scs.push(v);
        }
        Ok(WhirOpeningBundle61 {
            proof,
            lockstep_scs,
        })
    }
}

/// Replay WHIR lockstep sumcheck + OOD challenges on the verifier, returning `(s0_fibers, round_alphas)`!
#[allow(clippy::too_many_arguments)]
fn verify_whir_cascade_replay_and_trajectories_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    init_claims: &[(Vec<Ext3>, Ext3)],
    fold_rounds: &[WhirFoldRoundProof61],
    lockstep_scs: &[Vec<[Ext3; 3]>],
    final_ood_eval: Ext3,
    final_poly: &[Ext3],
    tr: &mut PcsTranscript,
) -> Result<(Vec<usize>, Vec<Vec<Ext3>>), String> {
    let num_rounds = shape.k_schedule.len();
    if fold_rounds.len() + 1 != num_rounds
        || lockstep_scs.len() != num_rounds
        || final_poly.len() != shape.w_final
    {
        return Err("WHIR cascade round/final_poly shape mismatch".into());
    }

    let mut running = ef.zero();
    let mut init_gammas = Vec::with_capacity(init_claims.len());
    for (idx, (_, val)) in init_claims.iter().enumerate() {
        let gm = tr.squeeze_ext3(ef, 600 + idx as u64);
        init_gammas.push(gm);
        running = ef.add(running, ef.mul(gm, *val));
    }

    let mut ood_challenges = Vec::with_capacity(num_rounds);
    let mut ood_taus = Vec::with_capacity(num_rounds);
    let mut round_alphas = Vec::with_capacity(num_rounds);
    let mut all_alphas = Vec::new();

    for r in 0..num_rounds {
        let kr = shape.k_schedule[r];
        if lockstep_scs[r].len() != kr {
            return Err("WHIR lockstep sumcheck inner count mismatch".into());
        }
        let ood_ev = if r + 1 < num_rounds {
            fold_rounds[r].ood_eval_prev
        } else {
            final_ood_eval
        };
        let z_ood = squeeze_non_base_ood_61(ef, tr, 700 + (r as u64) * 10);
        tr.absorb_ext3(&ood_ev);
        let tau_ood = tr.squeeze_ext3(ef, 701 + (r as u64) * 10);
        running = ef.add(running, ef.mul(tau_ood, ood_ev));
        ood_challenges.push(z_ood);
        ood_taus.push(tau_ood);

        let mut alphas_r = Vec::with_capacity(kr);
        for (step, poly) in lockstep_scs[r].iter().enumerate() {
            let p0 = poly[0];
            let p1 = ef.add(poly[0], ef.add(poly[1], poly[2]));
            if ef.add(p0, p1) != running {
                return Err(format!(
                    "WHIR lockstep sumcheck failed at round {r} step {step}"
                ));
            }
            for ck in poly {
                tr.absorb_ext3(ck);
            }
            let alpha = tr.squeeze_ext3(ef, 702 + (r as u64) * 10 + step as u64);
            alphas_r.push(alpha);
            all_alphas.push(alpha);
            running = eval_poly_ext3(ef, poly, alpha);
        }
        round_alphas.push(alphas_r);

        if r + 1 < num_rounds {
            tr.absorb_bytes(&fold_rounds[r].root);
        } else {
            tr.absorb_poly3("WHIR61_FINAL_POLY", final_poly);
        }
    }

    // Verify terminal lockstep equation directly against `final_poly` (`len == w_final <= 128`)!
    // At the end of `all_alphas` (`tot_k` variables folded), each remaining index `q in 0..w_final`
    // has weight:
    //   `sum_m gamma_m * eq(pt_m[..tot_k], all_alphas) * eq(pt_m[tot_k..], q)`
    // + `sum_r tau_r * prod_{b=0}^{kr_rem - 1} (1 - alpha_b + alpha_b * z_ood_r^{2^b}) * (z_ood_r^{2^{rem_k}})^q`!
    let tot_k = all_alphas.len();
    let mut final_weights = vec![ef.zero(); shape.w_final];

    for ((pt, _), &gm) in init_claims.iter().zip(init_gammas.iter()) {
        let mut eq_prefix = gm;
        for (&p_b, &a_b) in pt[..tot_k].iter().zip(all_alphas.iter()) {
            let term = ef.add(
                ef.mul(ef.sub(ef.one(), p_b), ef.sub(ef.one(), a_b)),
                ef.mul(p_b, a_b),
            );
            eq_prefix = ef.mul(eq_prefix, term);
        }
        let eq_rem = ef.build_eq_le(&pt[tot_k..]);
        for q in 0..shape.w_final {
            final_weights[q] = ef.add(final_weights[q], ef.mul(eq_prefix, eq_rem[q]));
        }
    }

    let mut alpha_offset = 0usize;
    for r in 0..num_rounds {
        let z_ood = ood_challenges[r];
        let mut z_pow = z_ood;
        let mut prefix_prod = ood_taus[r];
        for &a_b in &all_alphas[alpha_offset..] {
            // (1 - a_b) + a_b * z_pow
            let factor = ef.add(ef.sub(ef.one(), a_b), ef.mul(a_b, z_pow));
            prefix_prod = ef.mul(prefix_prod, factor);
            z_pow = ef.mul(z_pow, z_pow);
        }
        // Now `z_pow == z_ood^{2^{tot_k - alpha_offset}}`! Remaining `q in 0..w_final` has factor `z_pow^q`:
        let mut cur_z = prefix_prod;
        for fw in &mut final_weights {
            *fw = ef.add(*fw, cur_z);
            cur_z = ef.mul(cur_z, z_pow);
        }
        alpha_offset += shape.k_schedule[r];
    }

    let mut expected_running = ef.zero();
    for q in 0..shape.w_final {
        expected_running = ef.add(expected_running, ef.mul(final_weights[q], final_poly[q]));
    }
    if running != expected_running {
        return Err("WHIR terminal lockstep OOD/MLE check against final_poly failed".into());
    }

    let n_leaves_0 = shape.n0 >> shape.k_schedule[0];
    let mut s0_fibers = tr.squeeze_distinct_cols(shape.t_queries, n_leaves_0);
    s0_fibers.sort_unstable();
    Ok((s0_fibers, round_alphas))
}

/// Verify Stage-0 Merkle multiproof on `s0_fibers` and project each opened column to `F^{(0)}(x_{q, m})`.
#[allow(clippy::too_many_arguments)]
fn verify_stage0_matrix_fibers_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    expected_root: &[u8; 32],
    z_row: &[Ext3],
    beta_gm: Ext3,
    gamma: Ext3,
    theta1: Ext3,
    theta2: Ext3,
    s0_fibers: &[usize],
    s0_fiber_vals: &[u64],
    s0_salts: &[[u8; 16]],
    s0_siblings: &[[u8; 32]],
) -> Result<Vec<Ext3>, String> {
    let fp = &ef.fp;
    let k0 = shape.k_schedule[0];
    let b0 = 1usize << k0;
    let n_q = s0_fibers.len();
    let fiber_stride = b0 * shape.r_total;
    if s0_salts.len() != n_q || s0_fiber_vals.len() != n_q * fiber_stride {
        return Err("WHIR Stage-0 fiber array length mismatch".into());
    }
    let n_leaves_0 = shape.n0 >> k0;
    let leaf_hashes: Vec<[u8; 32]> = (0..n_q)
        .into_par_iter()
        .map(|qi| {
            let slice = &s0_fiber_vals[qi * fiber_stride..(qi + 1) * fiber_stride];
            hash_whir_s0_fiber(s0_fibers[qi], &s0_salts[qi], slice)
        })
        .collect();
    verify_whir_tree_multiproof(
        expected_root,
        n_leaves_0,
        s0_fibers,
        &leaf_hashes,
        s0_siblings,
    )?;

    // Build combined row weight `w_row[0..r_total]` so `F^{(0)}(x) == <w_row, col(x)>` in ONE dot product!
    let eq_row = ef.build_eq_le(z_row);
    let mut w_row = vec![ef.zero(); shape.r_total];
    let mut g_pw = ef.one();
    for w_slot in w_row.iter_mut().take(shape.rd + 6) {
        *w_slot = g_pw;
        g_pw = ef.mul(g_pw, gamma);
    }
    w_row[shape.rd + 6] = [1, 0, 0];
    w_row[shape.rd + 7] = [0, 1, 0];
    w_row[shape.rd + 8] = [0, 0, 1];

    // Add `theta1 * u_eval` (`0..rd`):
    for r in 0..shape.rd {
        w_row[r] = ef.add(w_row[r], ef.mul(theta1, eq_row[r]));
    }
    // Add `theta2 * (P_gmask + beta_gm * Z_gm)`:
    let e_basis: [Ext3; 3] = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    for limb in 0..3 {
        let gm_w = ef.mul(theta2, e_basis[limb]);
        w_row[shape.rd + limb] = ef.add(w_row[shape.rd + limb], gm_w);
        let zgm_w = ef.mul(gm_w, beta_gm);
        w_row[shape.rd + 3 + limb] = ef.add(w_row[shape.rd + 3 + limb], zgm_w);
    }

    let total_pts = n_q * b0;
    let f0_evals: Vec<Ext3> = (0..total_pts)
        .into_par_iter()
        .map(|idx| {
            let col = &s0_fiber_vals[idx * shape.r_total..(idx + 1) * shape.r_total];
            dot_ext3_base_whir(fp, &w_row, col)
        })
        .collect();
    Ok(f0_evals)
}

/// Verify trajectory-chained coset-fiber folding consistency from Stage 0 through all intermediate
/// WHIR trees down to `final_poly`!
fn verify_whir_trajectories_full_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    s0_fibers: &[usize],
    s0_f0_evals: &[Ext3],
    fold_rounds: &[WhirFoldRoundProof61],
    round_alphas: &[Vec<Ext3>],
    final_poly: &[Ext3],
) -> Result<(), String> {
    let fp = &ef.fp;
    let num_rounds = shape.k_schedule.len();

    let mut cur_level = shape.level0;
    let mut cur_fibers = s0_fibers.to_vec();
    let mut cur_fiber_evals = s0_f0_evals.to_vec();

    for r in 0..num_rounds {
        let kr = shape.k_schedule[r];
        let b_len = 1usize << kr;
        let b_inv = fp.inv(b_len as u64);
        let eq_alpha = ef.build_eq_le(&round_alphas[r]);

        // Precompute `zeta_inv_pows` for this level & batch-invert `x0` across `cur_fibers`:
        let (_, zeta) = cur_level.fiber_base_and_zeta(fp, kr, 0);
        let zeta_inv = fp.pow(zeta, (b_len - 1) as u64); // zeta^{B-1} == zeta^{-1}!
        let mut zeta_inv_pows = Vec::with_capacity((b_len / 2).max(1));
        let mut cur_z = 1u64;
        for _ in 0..(b_len / 2).max(1) {
            zeta_inv_pows.push(cur_z);
            cur_z = fp.mul(cur_z, zeta_inv);
        }

        let x0s: Vec<u64> = cur_fibers
            .iter()
            .map(|&f_idx| cur_level.fiber_base_and_zeta(fp, kr, f_idx).0)
            .collect();
        let x0_invs = batch_invert_fp(fp, &x0s);

        let folded_vals: Vec<Ext3> = (0..cur_fibers.len())
            .into_par_iter()
            .map(|i| {
                let slice = &cur_fiber_evals[i * b_len..(i + 1) * b_len];
                fold_fiber_evals_ext3(ef, slice, kr, x0_invs[i], &zeta_inv_pows, b_inv, &eq_alpha)
            })
            .collect();

        let next_level = cur_level.fold(fp, kr);

        if r + 1 < num_rounds {
            let fr = &fold_rounds[r];
            let kr_next = shape.k_schedule[r + 1];
            let b_next = 1usize << kr_next;
            let n_leaves_next = next_level.npts >> kr_next;

            // Deduplicate next-round fibers & map each `p_idx = cur_fibers[i]` into `(pos_in_uniq, sub_pos)`:
            let mut uniq_set = BTreeSet::new();
            let mut locs = Vec::with_capacity(cur_fibers.len());
            for &p_idx in &cur_fibers {
                let (f_next, sub_pos) = next_level.locate_in_fiber(kr_next, p_idx);
                uniq_set.insert(f_next);
                locs.push((f_next, sub_pos));
            }
            let uniq_fibers: Vec<usize> = uniq_set.into_iter().collect();
            if fr.opened_fibers.len() != uniq_fibers.len() * b_next {
                return Err(format!(
                    "WHIR round {} opened_fibers length mismatch",
                    r + 1
                ));
            }

            let leaf_hashes: Vec<[u8; 32]> = (0..uniq_fibers.len())
                .into_par_iter()
                .map(|ui| {
                    let fv = &fr.opened_fibers[ui * b_next..(ui + 1) * b_next];
                    hash_whir_fold_fiber(r + 1, uniq_fibers[ui], fv)
                })
                .collect();
            verify_whir_tree_multiproof(
                &fr.root,
                n_leaves_next,
                &uniq_fibers,
                &leaf_hashes,
                &fr.siblings,
            )?;

            let fiber_pos_map: BTreeMap<usize, usize> = uniq_fibers
                .iter()
                .copied()
                .enumerate()
                .map(|(pos, f)| (f, pos))
                .collect();

            for (i, &(f_next, sub_pos)) in locs.iter().enumerate() {
                let ui = fiber_pos_map[&f_next];
                let got = fr.opened_fibers[ui * b_next + sub_pos];
                if folded_vals[i] != got {
                    return Err(format!(
                        "WHIR round {} folding consistency failed at point {}",
                        r + 1,
                        cur_fibers[i]
                    ));
                }
            }

            cur_level = next_level;
            cur_fibers = uniq_fibers;
            cur_fiber_evals = fr.opened_fibers.clone();
        } else {
            // Final round (`r == num_rounds - 1`): check `folded_vals[i] == final_poly(next_level.point(p_idx))`!
            let fin_err = (0..cur_fibers.len()).into_par_iter().find_map_any(|i| {
                let p_idx = cur_fibers[i];
                let y = next_level.point(fp, p_idx);
                let want = eval_poly_ext3_at_base_whir(fp, final_poly, y);
                if folded_vals[i] != want {
                    Some(format!(
                        "WHIR final_poly consistency failed at point {p_idx}"
                    ))
                } else {
                    None
                }
            });
            if let Some(e) = fin_err {
                return Err(e);
            }
        }
    }
    Ok(())
}

/// Public entry point: standalone zero-witness verification of `WhirOpeningBundle61`!
#[allow(clippy::too_many_arguments)]
pub fn verify_whir_pcs61(
    fp: &FastPrime61,
    shape: &WhirShape61,
    root: &[u8; 32],
    log_n: usize,
    v_families: &[Vec<u64>],
    claims: &[SlotLinearClaim],
    context: &[u8; 32],
    bundle: &WhirOpeningBundle61,
) -> Result<(), String> {
    let ef = Ext3Field::new(*fp);
    let mut tr = PcsTranscript::new("WHIR61_OPEN", fp.p, root, context);
    let (z_row, beta_gm, gamma, theta1, theta2, zeta, f0_at_zeta) = verify_matrix_header_61(
        &ef,
        shape,
        log_n,
        v_families,
        claims,
        &bundle.proof.header,
        &mut tr,
    )?;

    let (s0_fibers, round_alphas) = verify_whir_cascade_replay_and_trajectories_61(
        &ef,
        shape,
        &[(zeta, f0_at_zeta)],
        &bundle.proof.fold_rounds,
        &bundle.lockstep_scs,
        bundle.proof.final_ood_eval,
        &bundle.proof.final_poly,
        &mut tr,
    )?;

    let f0_evals = verify_stage0_matrix_fibers_61(
        &ef,
        shape,
        root,
        &z_row,
        beta_gm,
        gamma,
        theta1,
        theta2,
        &s0_fibers,
        &bundle.proof.s0_fiber_vals,
        &bundle.proof.s0_salts,
        &bundle.proof.s0_siblings,
    )?;

    verify_whir_trajectories_full_61(
        &ef,
        shape,
        &s0_fibers,
        &f0_evals,
        &bundle.proof.fold_rounds,
        &round_alphas,
        &bundle.proof.final_poly,
    )
}

// ================================================================================================
// §3b. Shared-`zeta` Joint Two-Matrix Opening (`witness_pcs` + `a_pcs` -> ONE `zeta` & ONE WHIR Cascade!)
// ================================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirRowSumcheckPart61 {
    pub gmask_sum: Ext3,
    pub sumcheck_rounds: Vec<[Ext3; 3]>,
    pub m_eval: Ext3,
    pub z_gm_masks: [Ext3; 2],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhirSharedTwoMatrixProof61 {
    pub wit_sc: WhirRowSumcheckPart61,
    pub a_sc: WhirRowSumcheckPart61,
    pub shared_coeff_rounds: Vec<[Ext3; 3]>,
    pub evals_at_zeta: [Ext3; 6], // [u_ev_w, p_gm_w, u_pr_w, u_ev_a, p_gm_a, u_pr_a]
    pub wit_s0_fiber_vals: Vec<u64>,
    pub wit_s0_salts: Vec<[u8; 16]>,
    pub wit_s0_siblings: Vec<[u8; 32]>,
    pub a_s0_fiber_vals: Vec<u64>,
    pub a_s0_salts: Vec<[u8; 16]>,
    pub a_s0_siblings: Vec<[u8; 32]>,
    pub fold_rounds: Vec<WhirFoldRoundProof61>,
    pub lockstep_scs: Vec<Vec<[Ext3; 3]>>,
    pub final_ood_eval: Ext3,
    pub final_poly: Vec<Ext3>,
}

impl WhirSharedTwoMatrixProof61 {
    pub fn to_bytes(&self, p: u64, out: &mut Vec<u8>) {
        out.push(self.wit_sc.sumcheck_rounds.len() as u8);
        out.push(self.a_sc.sumcheck_rounds.len() as u8);
        out.push(self.shared_coeff_rounds.len() as u8);
        let mut flat = Vec::new();
        let mut push_part = |pt: &WhirRowSumcheckPart61| {
            flat.extend_from_slice(&pt.gmask_sum);
            for r in &pt.sumcheck_rounds {
                for e in r {
                    flat.extend_from_slice(e);
                }
            }
            flat.extend_from_slice(&pt.m_eval);
            flat.extend_from_slice(&pt.z_gm_masks[0]);
            flat.extend_from_slice(&pt.z_gm_masks[1]);
        };
        push_part(&self.wit_sc);
        push_part(&self.a_sc);
        for r in &self.shared_coeff_rounds {
            for e in r {
                flat.extend_from_slice(e);
            }
        }
        for e in &self.evals_at_zeta {
            flat.extend_from_slice(e);
        }
        pack_u64_bits_le(&flat, 61, out);

        pack_u64_bits_le(&self.wit_s0_fiber_vals, 61, out);
        out.extend_from_slice(&(self.wit_s0_salts.len() as u32).to_le_bytes());
        for s in &self.wit_s0_salts {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.wit_s0_siblings.len() as u32).to_le_bytes());
        for s in &self.wit_s0_siblings {
            out.extend_from_slice(s);
        }

        pack_u64_bits_le(&self.a_s0_fiber_vals, 61, out);
        out.extend_from_slice(&(self.a_s0_salts.len() as u32).to_le_bytes());
        for s in &self.a_s0_salts {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.a_s0_siblings.len() as u32).to_le_bytes());
        for s in &self.a_s0_siblings {
            out.extend_from_slice(s);
        }

        write_fold_rounds_61(
            p,
            &self.fold_rounds,
            &self.final_ood_eval,
            &self.final_poly,
            out,
        );
        out.push(self.lockstep_scs.len() as u8);
        let mut lflat = Vec::new();
        for rd in &self.lockstep_scs {
            out.push(rd.len() as u8);
            for poly in rd {
                for e in poly {
                    lflat.extend_from_slice(e);
                }
            }
        }
        pack_u64_bits_le(&lflat, 61, out);
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>, p: u64) -> Result<Self, String> {
        let nw = cur.read_u8()? as usize;
        let na = cur.read_u8()? as usize;
        let nc = cur.read_u8()? as usize;
        if nw == 0 || nw > 32 || na == 0 || na > 32 || nc == 0 || nc > 32 {
            return Err("invalid WhirSharedTwoMatrixProof61 round counts".into());
        }
        let exp_ext = (1 + nw * 3 + 3) + (1 + na * 3 + 3) + nc * 3 + 6;
        let ev = unpack_ext3_slice(cur, exp_ext, p)?;
        if ev.len() != exp_ext {
            return Err("WhirSharedTwoMatrixProof61 header Ext3 count mismatch".into());
        }
        let mut i = 0usize;
        let read_part = |n: usize, i: &mut usize| -> WhirRowSumcheckPart61 {
            let gmask_sum = ev[*i];
            *i += 1;
            let mut sumcheck_rounds = Vec::with_capacity(n);
            for _ in 0..n {
                sumcheck_rounds.push([ev[*i], ev[*i + 1], ev[*i + 2]]);
                *i += 3;
            }
            let m_eval = ev[*i];
            let z_gm_masks = [ev[*i + 1], ev[*i + 2]];
            *i += 3;
            WhirRowSumcheckPart61 {
                gmask_sum,
                sumcheck_rounds,
                m_eval,
                z_gm_masks,
            }
        };
        let wit_sc = read_part(nw, &mut i);
        let a_sc = read_part(na, &mut i);
        let mut shared_coeff_rounds = Vec::with_capacity(nc);
        for _ in 0..nc {
            shared_coeff_rounds.push([ev[i], ev[i + 1], ev[i + 2]]);
            i += 3;
        }
        let evals_at_zeta: [Ext3; 6] = std::array::from_fn(|k| ev[i + k]);

        let wit_s0_fiber_vals = unpack_u64_bits_le(cur, 61, 1 << 23, p)?;
        let nws = cur.read_u32()? as usize;
        if nws > 4096 {
            return Err("wit_s0_salts overflow".into());
        }
        let mut wit_s0_salts = Vec::with_capacity(nws);
        for _ in 0..nws {
            wit_s0_salts.push(cur.take(16)?.try_into().unwrap());
        }
        let nw_sib = cur.read_u32()? as usize;
        if nw_sib > 65536 {
            return Err("wit_s0_siblings overflow".into());
        }
        let mut wit_s0_siblings = Vec::with_capacity(nw_sib);
        for _ in 0..nw_sib {
            wit_s0_siblings.push(cur.read_hash()?);
        }

        let a_s0_fiber_vals = unpack_u64_bits_le(cur, 61, 1 << 24, p)?;
        let nas = cur.read_u32()? as usize;
        if nas > 4096 {
            return Err("a_s0_salts overflow".into());
        }
        let mut a_s0_salts = Vec::with_capacity(nas);
        for _ in 0..nas {
            a_s0_salts.push(cur.take(16)?.try_into().unwrap());
        }
        let na_sib = cur.read_u32()? as usize;
        if na_sib > 65536 {
            return Err("a_s0_siblings overflow".into());
        }
        let mut a_s0_siblings = Vec::with_capacity(na_sib);
        for _ in 0..na_sib {
            a_s0_siblings.push(cur.read_hash()?);
        }

        let (fold_rounds, final_ood_eval, final_poly) = read_fold_rounds_61(cur, p)?;
        let n_lr = cur.read_u8()? as usize;
        if n_lr == 0 || n_lr > 16 {
            return Err("invalid lockstep_scs count".into());
        }
        let mut lens = Vec::with_capacity(n_lr);
        let mut tot = 0usize;
        for _ in 0..n_lr {
            let l = cur.read_u8()? as usize;
            if l > 8 {
                return Err("invalid lockstep_scs inner len".into());
            }
            lens.push(l);
            tot += l;
        }
        let lev = unpack_ext3_slice(cur, tot * 3, p)?;
        let mut li = 0usize;
        let mut lockstep_scs = Vec::with_capacity(n_lr);
        for l in lens {
            let mut v = Vec::with_capacity(l);
            for _ in 0..l {
                v.push([lev[li], lev[li + 1], lev[li + 2]]);
                li += 3;
            }
            lockstep_scs.push(v);
        }

        Ok(WhirSharedTwoMatrixProof61 {
            wit_sc,
            a_sc,
            shared_coeff_rounds,
            evals_at_zeta,
            wit_s0_fiber_vals,
            wit_s0_salts,
            wit_s0_siblings,
            a_s0_fiber_vals,
            a_s0_salts,
            a_s0_siblings,
            fold_rounds,
            lockstep_scs,
            final_ood_eval,
            final_poly,
        })
    }
}

impl WhirCommittedPcs61 {
    /// Run ONLY the `(mc + mr)`-round `GMask61`-blinded `SlotLinearClaim` sumcheck and build `(u_eval, P_gmask_hat, v_g, v_at)`.
    fn prove_row_sumcheck_part(
        &self,
        log_n: usize,
        v_families: &[Vec<u64>],
        claims: &[SlotLinearClaim],
        tr: &mut PcsTranscript,
    ) -> WhirRowSumcheckOutput {
        let fp = &self.ef.fp;
        let ef = &self.ef;
        let sh = &self.shape;
        let m_bits = sh.mc + sh.mr;

        let (gmask_sum, sumcheck_rounds, z_challenges, m_eval) =
            self.run_slot_row_sumcheck_61(log_n, v_families, claims, tr);

        let eq_row = ef.build_eq_le(&z_challenges[sh.mc..]);
        let u_eval = combine_rows_ext3_whir(fp, &self.ext, sh.w0, &eq_row);
        let p_gmask = pack_3_rows_ext3(&self.ext, sh.w0, sh.rd);
        let z_gm = pack_3_rows_ext3(&self.ext, sh.w0, sh.rd + 3);

        let (v_g, v_at) = build_internal_gmask_weight_vecs(ef, m_bits, &z_challenges);
        let (mut s_g, mut s_at) = (ef.zero(), ef.zero());
        for u in 0..v_g.len() {
            s_g = ef.add(s_g, ef.mul(v_g[u], z_gm[u]));
            s_at = ef.add(s_at, ef.mul(v_at[u], z_gm[u]));
        }
        tr.absorb_ext3(&s_g);
        tr.absorb_ext3(&s_at);
        let mut beta_gm = tr.squeeze_ext3(ef, 300);
        if beta_gm == [0, 0, 0] {
            beta_gm = [1, 0, 0];
        }
        let p_gmask_hat: Vec<Ext3> = p_gmask
            .par_iter()
            .zip(z_gm.par_iter())
            .map(|(&p, &z)| ef.add(p, ef.mul(beta_gm, z)))
            .collect();

        (
            WhirRowSumcheckPart61 {
                gmask_sum,
                sumcheck_rounds,
                m_eval,
                z_gm_masks: [s_g, s_at],
            },
            z_challenges,
            beta_gm,
            u_eval,
            p_gmask_hat,
            v_g,
            v_at,
        )
    }
}

#[allow(clippy::too_many_arguments)]
pub fn open_shared_two_matrix_whir61(
    wit_pcs: &WhirCommittedPcs61,
    a_pcs: &WhirCommittedPcs61,
    log_n: usize,
    wit_vf: &[Vec<u64>],
    wit_claims: &[SlotLinearClaim],
    a_vf: &[Vec<u64>],
    a_claims: &[SlotLinearClaim],
    context: &[u8; 32],
) -> WhirSharedTwoMatrixProof61 {
    assert_eq!(wit_pcs.shape.mc, a_pcs.shape.mc);
    assert_eq!(wit_pcs.shape.k_schedule, a_pcs.shape.k_schedule);
    let ef = &wit_pcs.ef;
    let fp = &ef.fp;
    let w0 = wit_pcs.shape.w0;
    let c = wit_pcs.shape.c;

    let mut bh = Sha256::new();
    bh.update(wit_pcs.root);
    bh.update(a_pcs.root);
    let joint_root: [u8; 32] = bh.finalize().into();

    let mut tr = PcsTranscript::new("WHIR61_SHARED2", fp.p, &joint_root, context);
    let (wit_sc, z_w, _bgm_w, u_ev_w, p_gm_w, vg_w, vat_w) =
        wit_pcs.prove_row_sumcheck_part(log_n, wit_vf, wit_claims, &mut tr);
    let (a_sc, z_a, _bgm_a, u_ev_a, p_gm_a, vg_a, vat_a) =
        a_pcs.prove_row_sumcheck_part(log_n, a_vf, a_claims, &mut tr);

    let lams: [Ext3; 5] = std::array::from_fn(|k| tr.squeeze_ext3(ef, 350 + k as u64));

    let mut ve_w = vec![ef.zero(); w0];
    ve_w[..c].copy_from_slice(&ef.build_eq_le(&z_w[..wit_pcs.shape.mc]));
    let mut vgm_w = vec![ef.zero(); w0];
    for u in 0..vg_w.len() {
        vgm_w[u] = ef.add(ef.mul(lams[0], vg_w[u]), ef.mul(lams[1], vat_w[u]));
    }

    let eq_col_a = ef.build_eq_le(&z_a[..a_pcs.shape.mc]);
    let mut ve_a = vec![ef.zero(); w0];
    for u in 0..c {
        ve_a[u] = ef.mul(lams[2], eq_col_a[u]);
    }
    let mut vgm_a = vec![ef.zero(); w0];
    for u in 0..vg_a.len() {
        vgm_a[u] = ef.add(ef.mul(lams[3], vg_a[u]), ef.mul(lams[4], vat_a[u]));
    }

    let lg_w0 = wit_pcs.shape.mc + 1;
    let mut uew_c = u_ev_w.clone();
    let mut pgw_c = p_gm_w.clone();
    let mut uea_c = u_ev_a.clone();
    let mut pga_c = p_gm_a.clone();
    let mut shared_coeff_rounds = Vec::with_capacity(lg_w0);
    let mut zeta = Vec::with_capacity(lg_w0);
    let mut len_c = w0;

    for r_idx in 0..lg_w0 {
        let half = len_c / 2;
        let eval_quad = |u: usize| -> [Ext3; 3] {
            let mut c0 = ef.zero();
            let mut c1 = ef.zero();
            let mut c2 = ef.zero();
            for (v_arr, p_arr) in [
                (&ve_w, &uew_c),
                (&vgm_w, &pgw_c),
                (&ve_a, &uea_c),
                (&vgm_a, &pga_c),
            ] {
                let (v0, v1) = (v_arr[2 * u], v_arr[2 * u + 1]);
                let (p0, p1) = (p_arr[2 * u], p_arr[2 * u + 1]);
                let dv = ef.sub(v1, v0);
                let dp = ef.sub(p1, p0);
                c0 = ef.add(c0, ef.mul(v0, p0));
                c1 = ef.add(c1, ef.add(ef.mul(v0, dp), ef.mul(dv, p0)));
                c2 = ef.add(c2, ef.mul(dv, dp));
            }
            [c0, c1, c2]
        };
        let poly = if half >= 2048 {
            (0..half).into_par_iter().map(eval_quad).reduce(
                || [ef.zero(), ef.zero(), ef.zero()],
                |a, b| [ef.add(a[0], b[0]), ef.add(a[1], b[1]), ef.add(a[2], b[2])],
            )
        } else {
            let mut acc = [ef.zero(), ef.zero(), ef.zero()];
            for u in 0..half {
                let x = eval_quad(u);
                for k in 0..3 {
                    acc[k] = ef.add(acc[k], x[k]);
                }
            }
            acc
        };
        for ck in &poly {
            tr.absorb_ext3(ck);
        }
        let z_i = tr.squeeze_ext3(ef, 400 + r_idx as u64);
        shared_coeff_rounds.push(poly);
        zeta.push(z_i);

        let fold_v = |v: &mut Vec<Ext3>| {
            if half >= 4096 {
                *v = (0..half)
                    .into_par_iter()
                    .map(|u| ef.add(v[2 * u], ef.mul(z_i, ef.sub(v[2 * u + 1], v[2 * u]))))
                    .collect();
            } else {
                for u in 0..half {
                    let (x0, x1) = (v[2 * u], v[2 * u + 1]);
                    v[u] = ef.add(x0, ef.mul(z_i, ef.sub(x1, x0)));
                }
                v.truncate(half);
            }
        };
        fold_v(&mut ve_w);
        fold_v(&mut uew_c);
        fold_v(&mut vgm_w);
        fold_v(&mut pgw_c);
        fold_v(&mut ve_a);
        fold_v(&mut uea_c);
        fold_v(&mut vgm_a);
        fold_v(&mut pga_c);
        len_c = half;
    }

    let u_ev_w_z = uew_c[0];
    let p_gm_w_z = pgw_c[0];
    let u_ev_a_z = uea_c[0];
    let p_gm_a_z = pga_c[0];
    for e in [u_ev_w_z, p_gm_w_z, u_ev_a_z, p_gm_a_z] {
        tr.absorb_ext3(&e);
    }

    let build_prox = |pcs: &WhirCommittedPcs61, gamma: Ext3| -> Vec<Ext3> {
        let non_prox = pcs.shape.rd + 6;
        let mut pw = Vec::with_capacity(pcs.shape.r_total);
        let mut cur = ef.one();
        for _ in 0..non_prox {
            pw.push(cur);
            cur = ef.mul(cur, gamma);
        }
        pw.push([1, 0, 0]);
        pw.push([0, 1, 0]);
        pw.push([0, 0, 1]);
        combine_rows_ext3_whir(fp, &pcs.ext, w0, &pw)
    };

    let gamma_w = tr.squeeze_ext3(ef, 500);
    let gamma_a = tr.squeeze_ext3(ef, 501);
    let u_pr_w = build_prox(wit_pcs, gamma_w);
    let u_pr_a = build_prox(a_pcs, gamma_a);
    let u_pr_w_z = eval_mle_ext3(ef, &u_pr_w, &zeta);
    let u_pr_a_z = eval_mle_ext3(ef, &u_pr_a, &zeta);
    tr.absorb_ext3(&u_pr_w_z);
    tr.absorb_ext3(&u_pr_a_z);

    let th: [Ext3; 5] = std::array::from_fn(|k| tr.squeeze_ext3(ef, 510 + k as u64));
    let f0_joint: Vec<Ext3> = (0..w0)
        .into_par_iter()
        .map(|k| {
            let mut acc = u_pr_w[k];
            acc = ef.add(acc, ef.mul(th[0], u_ev_w[k]));
            acc = ef.add(acc, ef.mul(th[1], p_gm_w[k]));
            acc = ef.add(acc, ef.mul(th[2], u_pr_a[k]));
            acc = ef.add(acc, ef.mul(th[3], u_ev_a[k]));
            acc = ef.add(acc, ef.mul(th[4], p_gm_a[k]));
            acc
        })
        .collect();

    let (fold_rounds, lockstep_scs, final_ood_eval, final_poly, s0_fibers) =
        prove_whir_cascade_core_61(ef, &wit_pcs.shape, f0_joint, &[zeta], &mut tr);

    let (wit_s0_fiber_vals, wit_s0_salts, wit_s0_siblings) = wit_pcs.open_stage0_fibers(&s0_fibers);
    let (a_s0_fiber_vals, a_s0_salts, a_s0_siblings) = a_pcs.open_stage0_fibers(&s0_fibers);

    WhirSharedTwoMatrixProof61 {
        wit_sc,
        a_sc,
        shared_coeff_rounds,
        evals_at_zeta: [u_ev_w_z, p_gm_w_z, u_pr_w_z, u_ev_a_z, p_gm_a_z, u_pr_a_z],
        wit_s0_fiber_vals,
        wit_s0_salts,
        wit_s0_siblings,
        a_s0_fiber_vals,
        a_s0_salts,
        a_s0_siblings,
        fold_rounds,
        lockstep_scs,
        final_ood_eval,
        final_poly,
    }
}

fn verify_row_sumcheck_part_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    log_n: usize,
    v_families: &[Vec<u64>],
    claims: &[SlotLinearClaim],
    part: &WhirRowSumcheckPart61,
    tr: &mut PcsTranscript,
) -> Result<(Vec<Ext3>, Ext3, Ext3, Ext3), String> {
    let fp = &ef.fp;
    let n_poly = 1usize << log_n;
    if log_n > shape.mc || !shape.c.is_multiple_of(n_poly) {
        return Err("invalid log_n vs shape.mc".into());
    }
    let m_bits = shape.mc + shape.mr;
    if part.sumcheck_rounds.len() != m_bits {
        return Err("WhirRowSumcheckPart61 length mismatch".into());
    }
    let polys_per_row = shape.c / n_poly;
    let usable_slots = shape.usable_rows * polys_per_row;

    tr.absorb_bytes(&shape.root_shape_tag());
    tr.absorb_bytes(&(claims.len() as u64).to_le_bytes());
    for cl in claims {
        tr.absorb_bytes(&cl.rhs.to_le_bytes());
    }
    let beta = tr.squeeze_ext3(ef, 1);
    let mut y_batch = ef.zero();
    let mut beta_pows = Vec::with_capacity(claims.len());
    let mut b_pw = ef.one();
    for cl in claims {
        y_batch = ef.add(y_batch, ef.scale(b_pw, cl.rhs % fp.p));
        beta_pows.push(b_pw);
        b_pw = ef.mul(b_pw, beta);
    }

    let (rho, z_challenges, masked_term) = verify_gmask61_rounds(
        ef,
        tr,
        y_batch,
        part.gmask_sum,
        &part
            .sumcheck_rounds
            .iter()
            .map(|r| r.to_vec())
            .collect::<Vec<_>>(),
        2,
        50,
    )?;

    let eq_j = ef.build_eq_le(&z_challenges[..log_n]);
    let eq_slot = ef.build_eq_le(&z_challenges[log_n..]);
    let vf_evals: Vec<Ext3> = v_families
        .par_iter()
        .map(|vf| {
            let mut acc = ef.zero();
            for (j, &vj) in vf.iter().enumerate() {
                if vj != 0 {
                    acc = ef.add(acc, ef.scale(eq_j[j], vj));
                }
            }
            acc
        })
        .collect();
    let mut a_eval = ef.zero();
    for (q_idx, cl) in claims.iter().enumerate() {
        let mut cl_ev = ef.zero();
        for (vf_idx, slot_terms) in &cl.terms {
            let mut slot_ev = ef.zero();
            for &(slot, w_u64) in slot_terms {
                if slot >= usable_slots {
                    return Err("claim references ZK blinding slot".into());
                }
                slot_ev = ef.add(slot_ev, ef.scale(eq_slot[slot], w_u64));
            }
            cl_ev = ef.add(cl_ev, ef.mul(slot_ev, vf_evals[*vf_idx]));
        }
        a_eval = ef.add(a_eval, ef.mul(beta_pows[q_idx], cl_ev));
    }
    let y_g = ef.mul(
        ef.inv(rho),
        ef.sub(masked_term, ef.mul(a_eval, part.m_eval)),
    );

    tr.absorb_ext3(&part.m_eval);
    tr.absorb_ext3(&part.z_gm_masks[0]);
    tr.absorb_ext3(&part.z_gm_masks[1]);
    let mut beta_gm = tr.squeeze_ext3(ef, 300);
    if beta_gm == [0, 0, 0] {
        beta_gm = [1, 0, 0];
    }
    let g_hat = ef.add(part.gmask_sum, ef.mul(beta_gm, part.z_gm_masks[0]));
    let y_g_hat = ef.add(y_g, ef.mul(beta_gm, part.z_gm_masks[1]));
    Ok((z_challenges, beta_gm, g_hat, y_g_hat))
}

#[allow(clippy::too_many_arguments)]
pub fn verify_shared_two_matrix_whir61(
    fp: &FastPrime61,
    wit_shape: &WhirShape61,
    wit_root: &[u8; 32],
    a_shape: &WhirShape61,
    a_root: &[u8; 32],
    log_n: usize,
    wit_vf: &[Vec<u64>],
    wit_claims: &[SlotLinearClaim],
    a_vf: &[Vec<u64>],
    a_claims: &[SlotLinearClaim],
    context: &[u8; 32],
    prf: &WhirSharedTwoMatrixProof61,
) -> Result<(), String> {
    if wit_shape.mc != a_shape.mc || wit_shape.k_schedule != a_shape.k_schedule {
        return Err("shared two-matrix WHIR requires matching mc & k_schedule".into());
    }
    let ef = Ext3Field::new(*fp);
    let mut bh = Sha256::new();
    bh.update(wit_root);
    bh.update(a_root);
    let joint_root: [u8; 32] = bh.finalize().into();

    let mut tr = PcsTranscript::new("WHIR61_SHARED2", fp.p, &joint_root, context);
    let (z_w, bgm_w, gh_w, ygh_w) = verify_row_sumcheck_part_61(
        &ef,
        wit_shape,
        log_n,
        wit_vf,
        wit_claims,
        &prf.wit_sc,
        &mut tr,
    )?;
    let (z_a, bgm_a, gh_a, ygh_a) =
        verify_row_sumcheck_part_61(&ef, a_shape, log_n, a_vf, a_claims, &prf.a_sc, &mut tr)?;

    let lams: [Ext3; 5] = std::array::from_fn(|k| tr.squeeze_ext3(&ef, 350 + k as u64));
    let lg_w0 = wit_shape.mc + 1;
    if prf.shared_coeff_rounds.len() != lg_w0 {
        return Err("shared_coeff_rounds length mismatch".into());
    }

    let mut running = prf.wit_sc.m_eval;
    running = ef.add(running, ef.mul(lams[0], gh_w));
    running = ef.add(running, ef.mul(lams[1], ygh_w));
    running = ef.add(running, ef.mul(lams[2], prf.a_sc.m_eval));
    running = ef.add(running, ef.mul(lams[3], gh_a));
    running = ef.add(running, ef.mul(lams[4], ygh_a));

    let mut zeta = Vec::with_capacity(lg_w0);
    for (r_idx, poly) in prf.shared_coeff_rounds.iter().enumerate() {
        let p0 = poly[0];
        let p1 = ef.add(poly[0], ef.add(poly[1], poly[2]));
        if ef.add(p0, p1) != running {
            return Err(format!("shared coeff sumcheck failed at round {r_idx}"));
        }
        for ck in poly {
            tr.absorb_ext3(ck);
        }
        let z_i = tr.squeeze_ext3(&ef, 400 + r_idx as u64);
        zeta.push(z_i);
        running = eval_poly_ext3(&ef, poly, z_i);
    }

    let eval_ve_zeta = |z_col: &[Ext3]| -> Ext3 {
        let mut v = ef.sub(ef.one(), zeta[wit_shape.mc]);
        for (&zc, &zt) in z_col.iter().zip(zeta[..wit_shape.mc].iter()) {
            let eq_i = ef.add(
                ef.mul(ef.sub(ef.one(), zc), ef.sub(ef.one(), zt)),
                ef.mul(zc, zt),
            );
            v = ef.mul(v, eq_i);
        }
        v
    };
    let eval_vgm_zeta = |m_bits: usize, z_ch: &[Ext3], l0: Ext3, l1: Ext3| -> Ext3 {
        let (vg, vat) = build_internal_gmask_weight_vecs(&ef, m_bits, z_ch);
        let n_gm = vg.len();
        let k_gm = bitlen_usize(n_gm.saturating_sub(1)).max(1);
        let eq_lo = ef.build_eq_le(&zeta[..k_gm]);
        let mut zero_hi = ef.one();
        for &zt in &zeta[k_gm..] {
            zero_hi = ef.mul(zero_hi, ef.sub(ef.one(), zt));
        }
        let mut acc = ef.zero();
        for u in 0..n_gm {
            let comb = ef.add(ef.mul(l0, vg[u]), ef.mul(l1, vat[u]));
            acc = ef.add(acc, ef.mul(comb, eq_lo[u]));
        }
        ef.mul(acc, zero_hi)
    };

    let [u_ev_w_z, p_gm_w_z, u_pr_w_z, u_ev_a_z, p_gm_a_z, u_pr_a_z] = prf.evals_at_zeta;
    let ve_w_z = eval_ve_zeta(&z_w[..wit_shape.mc]);
    let vgm_w_z = eval_vgm_zeta(wit_shape.mc + wit_shape.mr, &z_w, lams[0], lams[1]);
    let ve_a_z = ef.mul(lams[2], eval_ve_zeta(&z_a[..a_shape.mc]));
    let vgm_a_z = eval_vgm_zeta(a_shape.mc + a_shape.mr, &z_a, lams[3], lams[4]);

    let mut want = ef.mul(ve_w_z, u_ev_w_z);
    want = ef.add(want, ef.mul(vgm_w_z, p_gm_w_z));
    want = ef.add(want, ef.mul(ve_a_z, u_ev_a_z));
    want = ef.add(want, ef.mul(vgm_a_z, p_gm_a_z));
    if running != want {
        return Err("shared two-matrix coeff sumcheck terminal check failed".into());
    }

    for e in [u_ev_w_z, p_gm_w_z, u_ev_a_z, p_gm_a_z] {
        tr.absorb_ext3(&e);
    }
    let gamma_w = tr.squeeze_ext3(&ef, 500);
    let gamma_a = tr.squeeze_ext3(&ef, 501);
    tr.absorb_ext3(&u_pr_w_z);
    tr.absorb_ext3(&u_pr_a_z);
    let th: [Ext3; 5] = std::array::from_fn(|k| tr.squeeze_ext3(&ef, 510 + k as u64));

    let mut f0_joint_z = u_pr_w_z;
    f0_joint_z = ef.add(f0_joint_z, ef.mul(th[0], u_ev_w_z));
    f0_joint_z = ef.add(f0_joint_z, ef.mul(th[1], p_gm_w_z));
    f0_joint_z = ef.add(f0_joint_z, ef.mul(th[2], u_pr_a_z));
    f0_joint_z = ef.add(f0_joint_z, ef.mul(th[3], u_ev_a_z));
    f0_joint_z = ef.add(f0_joint_z, ef.mul(th[4], p_gm_a_z));

    let (s0_fibers, round_alphas) = verify_whir_cascade_replay_and_trajectories_61(
        &ef,
        wit_shape,
        &[(zeta, f0_joint_z)],
        &prf.fold_rounds,
        &prf.lockstep_scs,
        prf.final_ood_eval,
        &prf.final_poly,
        &mut tr,
    )?;

    let f0_w_evals = verify_stage0_matrix_fibers_61(
        &ef,
        wit_shape,
        wit_root,
        &z_w[wit_shape.mc..],
        bgm_w,
        gamma_w,
        th[0],
        th[1],
        &s0_fibers,
        &prf.wit_s0_fiber_vals,
        &prf.wit_s0_salts,
        &prf.wit_s0_siblings,
    )?;

    // For `a_pcs`, note `th[2]` scales `u_prox_a`, `th[3]` scales `u_eval_a`, `th[4]` scales `P_gmask_hat_a`!
    let f0_a_unscaled_prox = verify_stage0_matrix_fibers_scaled_61(
        &ef,
        a_shape,
        a_root,
        &z_a[a_shape.mc..],
        bgm_a,
        gamma_a,
        th[2],
        th[3],
        th[4],
        &s0_fibers,
        &prf.a_s0_fiber_vals,
        &prf.a_s0_salts,
        &prf.a_s0_siblings,
    )?;

    let joint_s0_evals: Vec<Ext3> = f0_w_evals
        .iter()
        .zip(f0_a_unscaled_prox.iter())
        .map(|(&fw, &fa)| ef.add(fw, fa))
        .collect();

    verify_whir_trajectories_full_61(
        &ef,
        wit_shape,
        &s0_fibers,
        &joint_s0_evals,
        &prf.fold_rounds,
        &round_alphas,
        &prf.final_poly,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_stage0_matrix_fibers_scaled_61(
    ef: &Ext3Field,
    shape: &WhirShape61,
    expected_root: &[u8; 32],
    z_row: &[Ext3],
    beta_gm: Ext3,
    gamma: Ext3,
    prox_scale: Ext3,
    theta_ev: Ext3,
    theta_gm: Ext3,
    s0_fibers: &[usize],
    s0_fiber_vals: &[u64],
    s0_salts: &[[u8; 16]],
    s0_siblings: &[[u8; 32]],
) -> Result<Vec<Ext3>, String> {
    let fp = &ef.fp;
    let k0 = shape.k_schedule[0];
    let b0 = 1usize << k0;
    let n_q = s0_fibers.len();
    let fiber_stride = b0 * shape.r_total;
    if s0_salts.len() != n_q || s0_fiber_vals.len() != n_q * fiber_stride {
        return Err("WHIR Stage-0 scaled fiber array length mismatch".into());
    }
    let n_leaves_0 = shape.n0 >> k0;
    let leaf_hashes: Vec<[u8; 32]> = (0..n_q)
        .into_par_iter()
        .map(|qi| {
            let slice = &s0_fiber_vals[qi * fiber_stride..(qi + 1) * fiber_stride];
            hash_whir_s0_fiber(s0_fibers[qi], &s0_salts[qi], slice)
        })
        .collect();
    verify_whir_tree_multiproof(
        expected_root,
        n_leaves_0,
        s0_fibers,
        &leaf_hashes,
        s0_siblings,
    )?;

    let eq_row = ef.build_eq_le(z_row);
    let mut w_row = vec![ef.zero(); shape.r_total];
    let mut g_pw = prox_scale;
    for w_slot in w_row.iter_mut().take(shape.rd + 6) {
        *w_slot = g_pw;
        g_pw = ef.mul(g_pw, gamma);
    }
    let e_basis: [Ext3; 3] = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    for limb in 0..3 {
        w_row[shape.rd + 6 + limb] = ef.mul(prox_scale, e_basis[limb]);
    }
    for r in 0..shape.rd {
        w_row[r] = ef.add(w_row[r], ef.mul(theta_ev, eq_row[r]));
    }
    for limb in 0..3 {
        let gm_w = ef.mul(theta_gm, e_basis[limb]);
        w_row[shape.rd + limb] = ef.add(w_row[shape.rd + limb], gm_w);
        w_row[shape.rd + 3 + limb] = ef.add(w_row[shape.rd + 3 + limb], ef.mul(gm_w, beta_gm));
    }

    let total_pts = n_q * b0;
    Ok((0..total_pts)
        .into_par_iter()
        .map(|idx| {
            let col = &s0_fiber_vals[idx * shape.r_total..(idx + 1) * shape.r_total];
            dot_ext3_base_whir(fp, &w_row, col)
        })
        .collect())
}

// ================================================================================================
// §4. End-to-End `HoistedWhirBundle` (`prove_hoisted_whir` / `verify_hoisted_whir_bytes`)
// ================================================================================================

/// Persistent WHIR commitment for an `R_blk x K_blk` encrypted matrix `A_grid` (`Enc(W)`), aligned
/// to the canonical joint `mc` so online turns share **1 single WHIR cascade** across `wit` + `A`!
#[derive(Clone)]
pub struct WhirPersistentGridPcs {
    pub mode: LiftMode,
    pub r_blk: usize,
    pub k_blk: usize,
    pub n: usize,
    pub pcs: WhirCommittedPcs61,
    pub poly_lifts: Vec<DigitCols>,
    pub offline_range_proof: WhirOfflineGridRangeProof,
}

#[derive(Clone, Debug)]
pub struct WhirOfflineGridRangeProof {
    pub mr: u8,
    pub mc: u8,
    pub t_queries: u16,
    pub blow: u8,
    pub root: [u8; 32],
    pub logup_proof: LogUpGkrProof,
    pub pcs_opening: WhirOpeningBundle61,
}

#[derive(Clone, Debug)]
pub enum HoistedWhirPcsPayload {
    Single(WhirOpeningBundle61),
    SharedTwo(WhirSharedTwoMatrixProof61),
    SeparateTwo {
        wit_open: WhirOpeningBundle61,
        a_open: WhirOpeningBundle61,
    },
}

/// Complete self-contained WHIR + `GMask61` succinct proof bundle for `HoistedB61` + `D1b` LogUp-GKR!
#[derive(Clone, Debug)]
pub struct HoistedWhirBundle {
    pub mode: LiftMode,
    pub max_y_bits: u32,
    pub r_blk: usize,
    pub k_blk: usize,
    pub persistent_a: bool,
    pub wit_mr: u8,
    pub wit_mc: u8,
    pub t_queries: u16,
    pub blow: u8,
    pub witness_pcs_root: [u8; 32],
    pub a_pcs_meta: Option<(u8, u8, u16, u8, [u8; 32])>,
    pub p0_poly_evals: Vec<u64>,
    pub p0_k_evals: Vec<u64>,
    pub p17_poly_subsums: Vec<[u64; 3]>,
    pub p17_k_subsums: Vec<[u64; 3]>,
    pub persistent_a_evals: Option<(Vec<u64>, Vec<[u64; 3]>)>,
    pub logup_proof: LogUpGkrProof,
    pub pcs_payload: HoistedWhirPcsPayload,
}

/// Compute canonical shared `mc` for `(r_blk, k_blk, n, mode)` so `witness_pcs` and `a_pcs` share `D_0`!
pub fn canonical_joint_whir_shapes(
    fp0: &FastPrime61,
    n: usize,
    r_blk: usize,
    k_blk: usize,
    mode: LiftMode,
    t_queries: usize,
    blow: usize,
) -> (WhirShape61, WhirShape61) {
    let log_n = n.trailing_zeros() as usize;
    let lq = mode.q_cols();
    let mult_slots = TABLE_SIZE / n;
    let wit_slots =
        (2 * k_blk) * lq + (3 * r_blk) * 14 + (3 * r_blk) * lq + (3 * r_blk * 8) * 4 + mult_slots;
    let a_slots = (2 * r_blk * k_blk) * lq + mult_slots;
    let wit_elems = wit_slots * n;
    let a_elems = a_slots * n;
    let min_mc = log_n.max(9);
    // When `a_elems > 4 * wit_elems` (e.g. `d = 4096`, `503.6M` vs `64.0M`), keep each matrix on its
    // own size-optimal WHIR geometry (`SeparateTwo`) rather than inflating online `witness_pcs` to `mc_a = 20`:
    if a_elems > 4 * wit_elems {
        return (
            WhirShape61::for_len(fp0, wit_elems, min_mc, t_queries, blow),
            WhirShape61::for_len(fp0, a_elems, min_mc, t_queries, blow),
        );
    }
    let max_elems = wit_elems.max(a_elems);
    let max_c_cap = (max_elems.max(1 << min_mc) / 48)
        .next_power_of_two()
        .max(1usize << min_mc.max(16));
    let max_mc = (max_c_cap.trailing_zeros() as usize).clamp(min_mc, 20);
    let mut best: Option<(usize, usize, usize, usize)> = None;
    for mc in min_mc..=max_mc {
        let c = 1usize << mc;
        let mr_w = (wit_elems.div_ceil(c) + WHIR_NUM_ZK_DATA_ROWS)
            .max(8)
            .next_power_of_two()
            .trailing_zeros() as usize;
        let mr_a = (a_elems.div_ceil(c) + WHIR_NUM_ZK_DATA_ROWS)
            .max(8)
            .next_power_of_two()
            .trailing_zeros() as usize;
        if mr_w.max(mr_a) + mc > 31 {
            continue;
        }
        let mut sh_w = WhirShape61::from_mr_mc(fp0, mr_w, mc, t_queries, blow);
        let mut sh_a = WhirShape61::from_mr_mc(fp0, mr_a, mc, t_queries, blow);
        // Align `k0` to `min(sh_w.k_schedule[0], sh_a.k_schedule[0])` (`0` if either matrix is tall):
        if sh_w.k_schedule != sh_a.k_schedule {
            let k0 = sh_w.k_schedule[0].min(sh_a.k_schedule[0]);
            sh_w = force_k0_schedule(fp0, mr_w, mc, t_queries, blow, k0);
            sh_a = force_k0_schedule(fp0, mr_a, mc, t_queries, blow, k0);
        }
        // Joint proof pays `s0` on both + `folds` ONLY ONCE!
        let k0 = sh_w.k_schedule[0];
        let lg0_a = bitlen_usize((sh_a.n0 >> k0).saturating_sub(1));
        let s0_a = (sh_a.t_queries * (1usize << k0) * sh_a.r_total * 61).div_ceil(8)
            + sh_a.t_queries * 16
            + sh_a.t_queries * lg0_a.saturating_sub(6) * 32;
        let joint_est = sh_w.estimated_proof_bytes() + s0_a;
        if best.is_none_or(|b| joint_est < b.0) {
            best = Some((joint_est, mc, mr_w, mr_a));
        }
    }
    let (_, mc, mr_w, mr_a) = best.expect("valid joint WHIR shapes");
    let sh_w0 = WhirShape61::from_mr_mc(fp0, mr_w, mc, t_queries, blow);
    let sh_a0 = WhirShape61::from_mr_mc(fp0, mr_a, mc, t_queries, blow);
    let k0 = sh_w0.k_schedule[0].min(sh_a0.k_schedule[0]);
    (
        force_k0_schedule(fp0, mr_w, mc, t_queries, blow, k0),
        force_k0_schedule(fp0, mr_a, mc, t_queries, blow, k0),
    )
}

fn force_k0_schedule(
    fp: &FastPrime61,
    mr: usize,
    mc: usize,
    t_queries: usize,
    blow: usize,
    k0: usize,
) -> WhirShape61 {
    let mut sh = WhirShape61::from_mr_mc(fp, mr, mc, t_queries, blow);
    if sh.k_schedule[0] == k0 {
        return sh;
    }
    let k_max = sh.level0.k_sub as usize;
    let (k_schedule, w_final) = build_whir_k_schedule(k_max, sh.w0, k0);
    sh.k_schedule = k_schedule;
    sh.w_final = w_final;
    sh.t_queries = t_queries.min(sh.n0 >> k0);
    sh
}

#[derive(Clone)]
struct AffineLookupCol61 {
    const_offset: u64,
    terms: Vec<(usize, u64)>,
}

fn append_direct_lookup_descs_61(
    base_slot: usize,
    num_limbs: usize,
    top_bits: u32,
    p0: u64,
    out: &mut Vec<AffineLookupCol61>,
) {
    for m in 0..num_limbs {
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(base_slot + m, 1)],
        });
    }
    if top_bits < 20 {
        let shift_off = ((1u64 << 20) - (1u64 << top_bits)) % p0;
        out.push(AffineLookupCol61 {
            const_offset: shift_off,
            terms: vec![(base_slot + num_limbs - 1, 1)],
        });
    }
}

fn append_garner_lookup_descs_61(
    gspec: &ExactGarnerSpec,
    fp0: &FastPrime61,
    base_slot: usize,
    out: &mut Vec<AffineLookupCol61>,
) {
    let p0 = fp0.p;
    let inv2_20 = invmod(1u64 << 20, p0);
    let neg_inv2_20 = fp0.neg(inv2_20);
    let neg_one = fp0.neg(1);
    let pos_sum = (((1u64 << 19) - 1) + ((1u64 << 18) - 1) + 15) % p0;

    for idx in 0..3 {
        let g = base_slot + 5 * idx;
        let delta = gspec.deltas[idx] % p0;
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(g, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(g + 1, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 1u64 << 19,
            terms: vec![(g + 1, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(g + 2, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 3 * (1u64 << 18),
            terms: vec![(g + 2, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(g + 3, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: (1u64 << 20) - 16,
            terms: vec![(g + 3, 1)],
        });
        out.push(AffineLookupCol61 {
            const_offset: 0,
            terms: vec![(g + 4, 1)],
        });
        let ti_const = fp0.sub(pos_sum, fp0.mul(delta, inv2_20));
        out.push(AffineLookupCol61 {
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

fn materialize_lookup_entries_61(
    fp0: &FastPrime61,
    flat_slots: &[u64],
    n: usize,
    descs: &[AffineLookupCol61],
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

fn extract_logup_terminal_points_61(
    fp: &FastPrime61,
    proof: &LogUpGkrProof,
    context_digest: &[u8; 32],
) -> Result<(Vec<Vec<u64>>, Vec<u64>), String> {
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

fn build_eq_le_fp_61(fp: &FastPrime61, z: &[u64]) -> Vec<u64> {
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

fn q_limb_weights_mod_p_61(params: &HoistedParams, mode: LiftMode, l: usize) -> Vec<u64> {
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
                out.push(0);
            }
            out
        }
    }
}

fn y_limb_weights_mod_p_61(params: &HoistedParams, l: usize) -> [u64; 14] {
    let fp = &params.fp[l];
    std::array::from_fn(|m| fp.pow(2, (20 * m) as u64))
}

fn k_limb_weights_mod_p_61(params: &HoistedParams, l: usize) -> [u64; 4] {
    let fp = &params.fp[l];
    std::array::from_fn(|m| fp.pow(2, (20 * m) as u64))
}

#[inline]
fn split_u61_chunks21_61(v: u64) -> [u64; 3] {
    const M21: u64 = (1u64 << 21) - 1;
    [v & M21, (v >> 21) & M21, v >> 42]
}

#[inline]
fn combine_chunks21_mod_p_61(fp: &FastPrime61, s: &[u64; 3]) -> u64 {
    let two21 = (1u64 << 21) % fp.p;
    let two42 = (1u64 << 42) % fp.p;
    let s0 = s[0] % fp.p;
    let s1 = fp.mul(s[1] % fp.p, two21);
    let s2 = fp.mul(s[2] % fp.p, two42);
    fp.add(s0, fp.add(s1, s2))
}

fn build_hoisted_eval_v_families_61(
    params: &HoistedParams,
    mode: LiftMode,
    r_fs: &[u64; 8],
) -> WhirHoistedEvalVFamilies {
    let n = params.n;
    let mut v_fams = Vec::new();
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

        let qw = q_limb_weights_mod_p_61(params, mode, l);
        for m in 0..lq {
            let gm = qw[m];
            let (mut b0, mut b1, mut b2) = (vec![0u64; n], vec![0u64; n], vec![0u64; n]);
            if gm != 0 {
                for j in 0..n {
                    let ch = split_u61_chunks21_61(fpl.mul(gm, rl_pows[j]));
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

        let yw = y_limb_weights_mod_p_61(params, l);
        for m in 0..14 {
            let gm = yw[m];
            let (mut b0, mut b1, mut b2) = (vec![0u64; n], vec![0u64; n], vec![0u64; n]);
            for j in 0..n {
                let ch = split_u61_chunks21_61(fpl.mul(gm, rl_pows[j]));
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

        let kw = k_limb_weights_mod_p_61(params, l);
        for m in 0..4 {
            let gm = kw[m];
            let (mut b0, mut b1, mut b2) = (vec![0u64; n], vec![0u64; n], vec![0u64; n]);
            for j in 0..(n - 1) {
                let ch = split_u61_chunks21_61(fpl.mul(gm, rl_pows[j]));
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

#[allow(clippy::too_many_arguments)]
fn append_folded_p17_claims_61(
    fp0: &FastPrime61,
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
    let total_p = poly_specs.len() + num_rk;
    let mut tau_pows = Vec::with_capacity(total_p);
    let mut cur = 1u64;
    for _ in 0..total_p {
        tau_pows.push(cur);
        cur = fp0.mul(cur, tau_sub);
    }

    let mut q_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); lq];
    let mut y_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); 14];
    for (p_idx, &(base_slot, is_y)) in poly_specs.iter().enumerate() {
        let tw = tau_pows[p_idx];
        if !is_y {
            for (m, q_slot) in q_limb_slots.iter_mut().enumerate() {
                q_slot.push((base_slot + m, tw));
            }
        } else {
            for (m, y_slot) in y_limb_slots.iter_mut().enumerate() {
                y_slot.push((base_slot + m, tw));
            }
        }
    }

    for li in 0..7 {
        let l = li + 1;
        let mut k_limb_slots: Vec<Vec<(usize, u64)>> = vec![Vec::new(); 4];
        for rk in 0..num_rk {
            let tw = tau_pows[poly_specs.len() + rk];
            let k_idx = rk * 8 + l;
            let base_slot = off_k + k_idx * 4;
            for (m, k_slot) in k_limb_slots.iter_mut().enumerate() {
                k_slot.push((base_slot + m, tw));
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

fn compute_whir_fs_witness_root(witness_root: &[u8; 32], a_root: Option<&[u8; 32]>) -> [u8; 32] {
    match a_root {
        None => *witness_root,
        Some(ar) => {
            let mut h = Sha256::new();
            h.update(b"HOISTED_WHIR_BIND_V1|");
            h.update(witness_root);
            h.update(ar);
            h.finalize().into()
        }
    }
}

fn derive_whir_subsum_tau(
    fp0: &FastPrime61,
    stmt_h: &[u8; 32],
    pcs_root: &[u8; 32],
    p0_poly: &[u64],
    p0_k: &[u64],
    p17_poly: &[[u64; 3]],
    p17_k: &[[u64; 3]],
) -> u64 {
    let mut h = Sha256::new();
    h.update(b"HOISTED_WHIR_P17_TAU|");
    h.update(stmt_h);
    h.update(pcs_root);
    for &v in p0_poly.iter().chain(p0_k.iter()) {
        h.update(v.to_le_bytes());
    }
    for s in p17_poly.iter().chain(p17_k.iter()) {
        h.update(s[0].to_le_bytes());
        h.update(s[1].to_le_bytes());
        h.update(s[2].to_le_bytes());
    }
    let out: [u8; 32] = h.finalize().into();
    fp0.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
}

fn derive_whir_open_ctx(stmt_h: &[u8; 32], fs_wroot: &[u8; 32], tau1: u64, tau2: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"HOISTED_WHIR_OPEN_CTX_V1|");
    h.update(stmt_h);
    h.update(fs_wroot);
    h.update(tau1.to_le_bytes());
    h.update(tau2.to_le_bytes());
    h.finalize().into()
}

/// Offline persistent WHIR grid commitment (`Enc(W)` / `Enc(E)` / `Enc(S)`), automatically aligned to
/// `canonical_joint_whir_shapes` so online turns merge `witness_pcs + a_pcs` into 1 WHIR cascade!
pub fn commit_persistent_whir_grid(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    mode: LiftMode,
) -> Result<(Vec<Vec<PrecomputedCt>>, WhirPersistentGridPcs), String> {
    let (a_pre, shared) = crate::cert::precompute_shared_grid(engine, a_grid, mode);
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
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }

    let lookup_entries = materialize_lookup_entries_61(&fp0, &flat_data, n, &descs);
    let mults = count_multiplicities_parallel(&lookup_entries)?;
    for s in 0..mult_slots {
        flat_data[(num_poly_slots + s) * n..(num_poly_slots + s + 1) * n]
            .copy_from_slice(&mults[s * n..(s + 1) * n]);
    }

    let (_, shape_a) =
        canonical_joint_whir_shapes(&fp0, n, r_blk, k_blk, mode, WHIR_T_QUERIES_128, WHIR_BLOWUP);
    let pcs = WhirCommittedPcs61::commit_with_shape(fp0, shape_a, &flat_data, PcsRng::from_os());

    let chunk_log2 = (log_n + 5).max(18);
    let lu_cfg = LogUpConfig::BatchedC3 { chunk_log2 };
    let logup_proof = prove_logup_gkr_with_mults(&fp0, &lookup_entries, &mults, lu_cfg, &pcs.root);

    let (wit_zs, z_tab) = extract_logup_terminal_points_61(&fp0, &logup_proof, &pcs.root)?;
    let mut v_families = Vec::new();
    let mut claims = Vec::new();
    let cols_per_chunk = (1usize << chunk_log2) / n;

    for (b_idx, w_prf) in logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_families.len();
        v_families.push(build_eq_le_fp_61(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp_61(&fp0, &zw[log_n..]);
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
    v_families.push(build_eq_le_fp_61(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp_61(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (num_poly_slots + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    let pcs_opening = pcs.open_whir_slot_claims(log_n, &v_families, &claims, &pcs.root);
    let offline_range_proof = WhirOfflineGridRangeProof {
        mr: pcs.shape.mr as u8,
        mc: pcs.shape.mc as u8,
        t_queries: pcs.shape.t_queries as u16,
        blow: pcs.shape.blow as u8,
        root: pcs.root,
        logup_proof,
        pcs_opening,
    };

    Ok((
        a_pre,
        WhirPersistentGridPcs {
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

/// Complete multithreaded 128-bit `WHIR` + `GMask61` Prover for `HoistedB61` + `D1b` LogUp-GKR!
/// Returns `(out_cts, bundle, commit_ms, open_ms)`.
pub fn prove_hoisted_whir(
    engine: &HoistedEngine,
    a_grid: &[Vec<Ct>],
    b_vec: &[Ct],
    persistent_a: Option<(&[Vec<PrecomputedCt>], &WhirPersistentGridPcs)>,
    mode: LiftMode,
    logup_cfg: LogUpConfig,
) -> Result<(Vec<Ct3>, HoistedWhirBundle, f64, f64), String> {
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
                return Err("WhirPersistentGridPcs metadata mismatch".into());
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
                    LiftMode::ExactGarner15 => {
                        (gspec.encode_u_exact(&aux.u0), gspec.encode_u_exact(&aux.u1))
                    }
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

    for r in 0..r_blk {
        for k_comp in 0..3 {
            for l in 0..8 {
                let k_idx = (3 * r + k_comp) * 8 + l;
                let base_slot = off_k + k_idx * 4;
                let src = &raw.k_res[r][k_comp][l];
                for j in 0..(n - 1) {
                    let v = src[j];
                    flat_data[base_slot * n + j] = v & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 1) * n + j] = (v >> 20) & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 2) * n + j] = (v >> 40) & ((1u64 << 20) - 1);
                    flat_data[(base_slot + 3) * n + j] = v >> 60;
                }
            }
        }
    }

    let mut descs = Vec::new();
    for i in 0..n_a {
        let base = off_a + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_b {
        let base = off_b + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_y {
        let base = off_y + i * 14;
        append_direct_lookup_descs_61(base, 14, dspec.top_y_bits, fp0.p, &mut descs);
    }
    for i in 0..n_s {
        let base = off_s + i * lq;
        match mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_k {
        let base = off_k + i * 4;
        for m in 0..4 {
            descs.push(AffineLookupCol61 {
                const_offset: 0,
                terms: vec![(base + m, 1)],
            });
        }
    }

    let lookup_entries = materialize_lookup_entries_61(&fp0, &flat_data, n, &descs);
    let mults = count_multiplicities_parallel(&lookup_entries)?;
    for s in 0..mult_slots {
        flat_data[(off_mult + s) * n..(off_mult + s + 1) * n]
            .copy_from_slice(&mults[s * n..(s + 1) * n]);
    }

    let t_commit = Instant::now();
    let witness_pcs = if persistent_a.is_some() {
        let (sh_w, _) = canonical_joint_whir_shapes(
            &fp0,
            n,
            r_blk,
            k_blk,
            mode,
            WHIR_T_QUERIES_128,
            WHIR_BLOWUP,
        );
        WhirCommittedPcs61::commit_with_shape(fp0, sh_w, &flat_data, PcsRng::from_os())
    } else {
        WhirCommittedPcs61::commit(fp0, &flat_data, log_n)
    };
    let commit_ms = t_commit.elapsed().as_secs_f64() * 1e3;

    let t_open = Instant::now();
    let ha_grid: Vec<Vec<[u8; 32]>> = a_grid
        .par_iter()
        .map(|r| r.iter().map(ct2_handle).collect())
        .collect();
    let hb_vec: Vec<[u8; 32]> = b_vec.par_iter().map(ct2_handle).collect();
    let hout_vec: Vec<[u8; 32]> = raw.out_cts.par_iter().map(ct3_handle).collect();
    let stmt_h = compute_statement_digest(params, &ha_grid, &hb_vec, &hout_vec);

    let a_root_opt = persistent_a.map(|(_, pg)| &pg.pcs.root);
    let fs_witness_root = compute_whir_fs_witness_root(&witness_pcs.root, a_root_opt);
    let r_fs: [u64; 8] = std::array::from_fn(|l| {
        derive_fs_point(&stmt_h, &fs_witness_root, params.all_primes[l], false)
    });

    let logup_proof =
        prove_logup_gkr_with_mults(&fp0, &lookup_entries, &mults, logup_cfg, &fs_witness_root);

    let (mut v_fams, q_map, y_map, k_map) = build_hoisted_eval_v_families_61(params, mode, &r_fs);
    let base_vf_len = v_fams.len();
    let qw0 = q_limb_weights_mod_p_61(params, mode, 0);
    let yw0 = y_limb_weights_mod_p_61(params, 0);
    let kw0 = k_limb_weights_mod_p_61(params, 0);

    let eval_slot_dot = |slot: usize, vf_idx: usize, src_flat: &[u64]| -> u64 {
        fp0.dot(&src_flat[slot * n..(slot + 1) * n], &v_fams[vf_idx])
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
                    ev0 = fp0.add(
                        ev0,
                        fp0.mul(w0, eval_slot_dot(base_slot + m, 0, &flat_data)),
                    );
                }
            }
            let mut subs = [[0u64; 3]; 7];
            for li in 0..7 {
                for b in 0..3 {
                    let mut sum_int = 0u64;
                    for m in 0..limbs {
                        let vf_idx = if is_y {
                            y_map[li][m][b]
                        } else {
                            q_map[li][m][b]
                        };
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
        p17_poly_subsums.extend_from_slice(&subs);
    }

    let mut p0_k_evals = Vec::with_capacity(3 * r_blk);
    for rk in 0..(3 * r_blk) {
        let base_slot = off_k + (rk * 8) * 4;
        let mut ev0 = 0u64;
        let mut terms0 = Vec::with_capacity(4);
        for (m, &kw) in kw0.iter().enumerate() {
            let dm_ev = eval_slot_dot(base_slot + m, 1, &flat_data);
            ev0 = fp0.add(ev0, fp0.mul(kw, dm_ev));
            terms0.push((base_slot + m, kw));
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
            let base_slot = off_k + (rk * 8 + l) * 4;
            let mut subs = [0u64; 3];
            for (b, sub_slot) in subs.iter_mut().enumerate() {
                let mut s_int = 0u64;
                for (m, km) in k_map[li].iter().enumerate() {
                    s_int += eval_slot_dot(base_slot + m, km[b], &flat_data);
                }
                *sub_slot = s_int;
            }
            subs
        })
        .collect();

    let tau_sub = derive_whir_subsum_tau(
        &fp0,
        &stmt_h,
        &fs_witness_root,
        &p0_poly_evals,
        &p0_k_evals,
        &p17_poly_subsums,
        &p17_k_subsums,
    );
    append_folded_p17_claims_61(
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

    let chunk_cap = match logup_proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => logup_proof.total_lookups.max(2).next_power_of_two(),
    };
    let cols_per_chunk = chunk_cap / n;
    let (wit_zs, z_tab) = extract_logup_terminal_points_61(&fp0, &logup_proof, &fs_witness_root)?;

    for (b_idx, w_prf) in logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_fams.len();
        v_fams.push(build_eq_le_fp_61(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp_61(&fp0, &zw[log_n..]);
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
    v_fams.push(build_eq_le_fp_61(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp_61(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (off_mult + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        logup_proof.table_tree.leaf_payload_eval,
    ));

    let (a_pcs_meta, persistent_a_evals, pcs_payload) = if let Some((_, pg)) = persistent_a {
        let num_a = pg.poly_lifts.len();
        let a_specs: Vec<(usize, bool)> = (0..num_a).map(|i| (i * lq, false)).collect();
        let a_res: Vec<(u64, [[u64; 3]; 7])> = a_specs
            .par_iter()
            .map(|&(base_slot, _)| {
                let mut ev0 = 0u64;
                for (m, &w0) in qw0.iter().enumerate().take(lq) {
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
                .filter_map(|m| {
                    if qw0[m] != 0 {
                        Some((base_slot + m, qw0[m]))
                    } else {
                        None
                    }
                })
                .collect();
            a_claims.push(SlotLinearClaim::single_vec(0, terms0, ev0));
            a_p17.extend_from_slice(&subs);
        }
        let tau_a = derive_whir_subsum_tau(&fp0, &stmt_h, &pg.pcs.root, &a_p0, &[], &a_p17, &[]);
        append_folded_p17_claims_61(
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

        let ctx = derive_whir_open_ctx(&stmt_h, &fs_witness_root, tau_sub, tau_a);
        let payload = if witness_pcs.shape.mc == pg.pcs.shape.mc
            && witness_pcs.shape.k_schedule == pg.pcs.shape.k_schedule
        {
            HoistedWhirPcsPayload::SharedTwo(open_shared_two_matrix_whir61(
                &witness_pcs,
                &pg.pcs,
                log_n,
                &v_fams,
                &claims,
                &v_fams[..base_vf_len],
                &a_claims,
                &ctx,
            ))
        } else {
            HoistedWhirPcsPayload::SeparateTwo {
                wit_open: witness_pcs.open_whir_slot_claims(log_n, &v_fams, &claims, &ctx),
                a_open: pg.pcs.open_whir_slot_claims(
                    log_n,
                    &v_fams[..base_vf_len],
                    &a_claims,
                    &ctx,
                ),
            }
        };
        (
            Some((
                pg.pcs.shape.mr as u8,
                pg.pcs.shape.mc as u8,
                pg.pcs.shape.t_queries as u16,
                pg.pcs.shape.blow as u8,
                pg.pcs.root,
            )),
            Some((a_p0, a_p17)),
            payload,
        )
    } else {
        let ctx = derive_whir_open_ctx(&stmt_h, &fs_witness_root, tau_sub, 0);
        let wit_open = witness_pcs.open_whir_slot_claims(log_n, &v_fams, &claims, &ctx);
        (None, None, HoistedWhirPcsPayload::Single(wit_open))
    };

    let open_ms = t_open.elapsed().as_secs_f64() * 1e3;

    Ok((
        raw.out_cts,
        HoistedWhirBundle {
            mode,
            max_y_bits,
            r_blk,
            k_blk,
            persistent_a: persistent_a.is_some(),
            wit_mr: witness_pcs.shape.mr as u8,
            wit_mc: witness_pcs.shape.mc as u8,
            t_queries: witness_pcs.shape.t_queries as u16,
            blow: witness_pcs.shape.blow as u8,
            witness_pcs_root: witness_pcs.root,
            a_pcs_meta,
            p0_poly_evals,
            p0_k_evals,
            p17_poly_subsums,
            p17_k_subsums,
            persistent_a_evals,
            logup_proof,
            pcs_payload,
        },
        commit_ms,
        open_ms,
    ))
}

/// Standalone Zero-Witness Verifier from raw serialized `proof_bytes: &[u8]`!
/// When `bundle.persistent_a == true` and `opened_a == None`, `expected_persistent_a_root` MUST be
/// `Some(&expected_root)` pinning the custodian/verifier's committed `Enc(W)` WHIR root (`#117.A.2`).
#[allow(clippy::too_many_arguments)]
pub fn verify_hoisted_whir_bytes(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
    opened_a: Option<&[Vec<Ct>]>,
    expected_persistent_a_root: Option<&[u8; 32]>,
    opened_b: &[Ct],
    out_cts: &[Ct3],
    proof_bytes: &[u8],
) -> Result<(), String> {
    let bundle = HoistedWhirBundle::from_bytes(proof_bytes, params)?;
    verify_hoisted_whir_bundle(
        params,
        ha_grid,
        hb_vec,
        hout_vec,
        opened_a,
        expected_persistent_a_root,
        opened_b,
        out_cts,
        &bundle,
    )
}

fn validate_whir_shape_meta_61(
    log_n: usize,
    mr: usize,
    mc: usize,
    t_queries: usize,
    blow: usize,
) -> Result<(), String> {
    if !(WHIR_T_QUERIES_128..=512).contains(&t_queries)
        || !blow.is_power_of_two()
        || !(4..=16).contains(&blow)
    {
        return Err("WHIR security/blowup parameters out of valid 128-bit range".into());
    }
    let min_mc = log_n.max(9);
    if !(3..=20).contains(&mr) || !(min_mc..=21).contains(&mc) || mr + mc > 31 {
        return Err("WHIR (mr, mc) matrix dimensions out of valid range".into());
    }
    let r_total = (1usize << mr) + WHIR_EXTRA_EXT3_MASK_ROWS;
    let w0 = 2usize << mc;
    let k0 = if r_total >= 45 && w0 >= 2048 {
        0usize
    } else {
        1usize
    };
    let n_leaves_0 = (blow * w0) >> k0;
    let req_hide = t_queries.saturating_mul(1usize << k0);
    if req_hide > (1usize << mc) || t_queries > n_leaves_0 {
        return Err("WHIR t_queries * 2^k0 exceeds column hiding or Stage-0 leaf capacity".into());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn verify_hoisted_whir_bundle(
    params: &HoistedParams,
    ha_grid: &[Vec<[u8; 32]>],
    hb_vec: &[[u8; 32]],
    hout_vec: &[[u8; 32]],
    opened_a: Option<&[Vec<Ct>]>,
    expected_persistent_a_root: Option<&[u8; 32]>,
    opened_b: &[Ct],
    out_cts: &[Ct3],
    bundle: &HoistedWhirBundle,
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
    if !bundle.persistent_a {
        if opened_a.is_none() {
            return Err("non-persistent WHIR bundle requires opened_a".into());
        }
        if expected_persistent_a_root.is_some() {
            return Err("expected persistent_a WHIR bundle, got non-persistent".into());
        }
    }
    if let Some(oa) = opened_a {
        if oa.len() != r_blk || oa.iter().any(|r| r.len() != k_blk) {
            return Err("opened_a dimension mismatch".into());
        }
    }
    validate_whir_shape_meta_61(
        log_n,
        bundle.wit_mr as usize,
        bundle.wit_mc as usize,
        bundle.t_queries as usize,
        bundle.blow as usize,
    )?;
    if !params.check_crt_nowrap(k_blk, bundle.max_y_bits) {
        return Err("CRT Q*B no-wrap parameter bound failure".into());
    }

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
                Some(format!("input A handle mismatch at ({r},{c})"))
            } else {
                None
            }
        }) {
            return Err(e);
        }
    }

    let lq = bundle.mode.q_cols();
    let n_a = if bundle.persistent_a {
        0
    } else {
        2 * r_blk * k_blk
    };
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
        || bundle.persistent_a != bundle.persistent_a_evals.is_some()
    {
        return Err("WHIR bundle evaluation array length mismatch".into());
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

    let stmt_h = compute_statement_digest(params, ha_grid, hb_vec, hout_vec);
    let a_root_opt = bundle.a_pcs_meta.as_ref().map(|m| &m.4);
    let fs_witness_root = compute_whir_fs_witness_root(&bundle.witness_pcs_root, a_root_opt);
    let r_fs: [u64; 8] = std::array::from_fn(|l| {
        derive_fs_point(&stmt_h, &fs_witness_root, params.all_primes[l], false)
    });

    verify_logup_gkr(&fp0, &bundle.logup_proof, &fs_witness_root, None)?;

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
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_b {
        let base = off_b + i * lq;
        match bundle.mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_y {
        let base = off_y + i * 14;
        append_direct_lookup_descs_61(base, 14, dspec.top_y_bits, fp0.p, &mut descs);
    }
    for i in 0..n_s {
        let base = off_s + i * lq;
        match bundle.mode {
            LiftMode::Direct20 => {
                append_direct_lookup_descs_61(base, lq, dspec.top_x_bits, fp0.p, &mut descs)
            }
            LiftMode::ExactGarner15 => {
                append_garner_lookup_descs_61(&gspec, &fp0, base, &mut descs)
            }
        }
    }
    for i in 0..n_k {
        let base = off_k + i * 4;
        for m in 0..4 {
            descs.push(AffineLookupCol61 {
                const_offset: 0,
                terms: vec![(base + m, 1)],
            });
        }
    }
    if bundle.logup_proof.total_lookups != descs.len() * n {
        return Err("LogUp total_lookups != expected online digit lookup count".into());
    }

    let (mut v_fams, q_map, y_map, k_map) =
        build_hoisted_eval_v_families_61(params, bundle.mode, &r_fs);
    let base_vf_len = v_fams.len();
    let qw0 = q_limb_weights_mod_p_61(params, bundle.mode, 0);
    let yw0 = y_limb_weights_mod_p_61(params, 0);
    let kw0 = k_limb_weights_mod_p_61(params, 0);

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
        claims.push(SlotLinearClaim::single_vec(
            0,
            terms0,
            bundle.p0_poly_evals[idx],
        ));
    }
    for rk in 0..(3 * r_blk) {
        let base_slot = off_k + (rk * 8) * 4;
        let terms0: Vec<(usize, u64)> = (0..4).map(|m| (base_slot + m, kw0[m])).collect();
        claims.push(SlotLinearClaim::single_vec(
            1,
            terms0,
            bundle.p0_k_evals[rk],
        ));
    }

    let tau_sub = derive_whir_subsum_tau(
        &fp0,
        &stmt_h,
        &fs_witness_root,
        &bundle.p0_poly_evals,
        &bundle.p0_k_evals,
        &bundle.p17_poly_subsums,
        &bundle.p17_k_subsums,
    );
    append_folded_p17_claims_61(
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
    let (wit_zs, z_tab) =
        extract_logup_terminal_points_61(&fp0, &bundle.logup_proof, &fs_witness_root)?;

    for (b_idx, w_prf) in bundle.logup_proof.witness_trees.iter().enumerate() {
        let zw = &wit_zs[b_idx];
        let v_idx = v_fams.len();
        v_fams.push(build_eq_le_fp_61(&fp0, &zw[..log_n]));
        let eq_hi = build_eq_le_fp_61(&fp0, &zw[log_n..]);
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
    v_fams.push(build_eq_le_fp_61(&fp0, &z_tab[..log_n]));
    let eq_tab_hi = build_eq_le_fp_61(&fp0, &z_tab[log_n..TABLE_LOG2]);
    let tab_terms: Vec<(usize, u64)> = (0..mult_slots)
        .map(|s| (off_mult + s, eq_tab_hi[s]))
        .collect();
    claims.push(SlotLinearClaim::single_vec(
        v_tab_idx,
        tab_terms,
        bundle.logup_proof.table_tree.leaf_payload_eval,
    ));

    // Verify WHIR PCS opening payload (`Single`, `SharedTwo`, or `SeparateTwo`):
    match (
        &bundle.a_pcs_meta,
        &bundle.persistent_a_evals,
        &bundle.pcs_payload,
    ) {
        (None, None, HoistedWhirPcsPayload::Single(wit_open)) => {
            let wit_shape = WhirShape61::from_mr_mc(
                &fp0,
                bundle.wit_mr as usize,
                bundle.wit_mc as usize,
                bundle.t_queries as usize,
                bundle.blow as usize,
            );
            let ctx = derive_whir_open_ctx(&stmt_h, &fs_witness_root, tau_sub, 0);
            verify_whir_pcs61(
                &fp0,
                &wit_shape,
                &bundle.witness_pcs_root,
                log_n,
                &v_fams,
                &claims,
                &ctx,
                wit_open,
            )?;
        }
        (Some((amr, amc, atq, abl, aroot)), Some((a_p0, a_p17)), payload) => {
            let (amr, amc, atq, abl) = (*amr, *amc, *atq, *abl);
            validate_whir_shape_meta_61(
                log_n,
                amr as usize,
                amc as usize,
                atq as usize,
                abl as usize,
            )?;
            if expected_persistent_a_root != Some(aroot) {
                return Err(
                    "persistent_a bundle requires matching expected_persistent_a_root".into(),
                );
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
                    .filter_map(|m| {
                        if qw0[m] != 0 {
                            Some((base_slot + m, qw0[m]))
                        } else {
                            None
                        }
                    })
                    .collect();
                a_claims.push(SlotLinearClaim::single_vec(0, terms0, a_p0[idx]));
            }
            let tau_a = derive_whir_subsum_tau(&fp0, &stmt_h, aroot, a_p0, &[], a_p17, &[]);
            append_folded_p17_claims_61(
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
            let ctx = derive_whir_open_ctx(&stmt_h, &fs_witness_root, tau_sub, tau_a);

            let mut wit_shape = WhirShape61::from_mr_mc(
                &fp0,
                bundle.wit_mr as usize,
                bundle.wit_mc as usize,
                bundle.t_queries as usize,
                bundle.blow as usize,
            );
            let mut a_shape = WhirShape61::from_mr_mc(
                &fp0,
                amr as usize,
                amc as usize,
                atq as usize,
                abl as usize,
            );

            match payload {
                HoistedWhirPcsPayload::SharedTwo(joint_prf) => {
                    let k0 = wit_shape.k_schedule[0].min(a_shape.k_schedule[0]);
                    wit_shape = force_k0_schedule(
                        &fp0,
                        bundle.wit_mr as usize,
                        bundle.wit_mc as usize,
                        bundle.t_queries as usize,
                        bundle.blow as usize,
                        k0,
                    );
                    a_shape = force_k0_schedule(
                        &fp0,
                        amr as usize,
                        amc as usize,
                        atq as usize,
                        abl as usize,
                        k0,
                    );
                    verify_shared_two_matrix_whir61(
                        &fp0,
                        &wit_shape,
                        &bundle.witness_pcs_root,
                        &a_shape,
                        aroot,
                        log_n,
                        &v_fams,
                        &claims,
                        &v_fams[..base_vf_len],
                        &a_claims,
                        &ctx,
                        joint_prf,
                    )?;
                }
                HoistedWhirPcsPayload::SeparateTwo { wit_open, a_open } => {
                    verify_whir_pcs61(
                        &fp0,
                        &wit_shape,
                        &bundle.witness_pcs_root,
                        log_n,
                        &v_fams,
                        &claims,
                        &ctx,
                        wit_open,
                    )?;
                    verify_whir_pcs61(
                        &fp0,
                        &a_shape,
                        aroot,
                        log_n,
                        &v_fams[..base_vf_len],
                        &a_claims,
                        &ctx,
                        a_open,
                    )?;
                }
                HoistedWhirPcsPayload::Single(_) => {
                    return Err("persistent_a bundle cannot carry Single PCS payload".into())
                }
            }
        }
        _ => return Err("inconsistent persistent_a metadata vs PCS payload".into()),
    }

    // 5. Verify 8-prime `R_blk x K_blk` scalar matvec, `Qp` limb openings, and BEHZ rescale identity!
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
                combine_chunks21_mod_p_61(fp, &bundle.p17_poly_subsums[poly_idx * 7 + (l - 1)])
            }
        };

        let mut m0 = vec![0u64; r_blk * k_blk];
        let mut m1 = vec![0u64; r_blk * k_blk];
        for idx in 0..(r_blk * k_blk) {
            let (raw0, raw1) = if let Some((ref a_p0, ref a_p17)) = bundle.persistent_a_evals {
                if l == 0 {
                    (a_p0[2 * idx], a_p0[2 * idx + 1])
                } else {
                    (
                        combine_chunks21_mod_p_61(fp, &a_p17[(2 * idx) * 7 + (l - 1)]),
                        combine_chunks21_mod_p_61(fp, &a_p17[(2 * idx + 1) * 7 + (l - 1)]),
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
                        return Some(format!(
                            "A WHIR opening != ciphertext limb mod {p} at ({r},{c})"
                        ));
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
                    return Some(format!(
                        "B WHIR opening != ciphertext limb mod {p} at ({c})"
                    ));
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
                        "output limb mismatch vs WHIR y_eval at row {r}, comp {k_comp}, prime {p}"
                    ));
                }
                let s_ev = get_online_raw(s_base + rk);
                let k_ev = if l == 0 {
                    bundle.p0_k_evals[rk]
                } else {
                    combine_chunks21_mod_p_61(fp, &bundle.p17_k_subsums[(l - 1) * (3 * r_blk) + rk])
                };

                let lhs = fp.add(fp.mul(t_mod_p, pk), hq_shift);
                let rhs = fp.red128(
                    (q_mod_p as u128) * (y_ev as u128)
                        + (s_ev as u128)
                        + (fp.mul(t_mod_p, xn_plus_1) as u128) * (k_ev as u128),
                );
                if lhs != rhs {
                    return Some(format!(
                        "WHIR hoisted rescale identity fails in F_p (row {r}, comp {k_comp}, p={p})"
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

// ================================================================================================
// §5. `HoistedWhirBundle` Canonical Binary Wire Serialization (`58`-bit Subsum + `61`-bit Field Packing)
// ================================================================================================

fn write_fraction_tree_whir(t: &FractionTreeProof, out: &mut Vec<u8>) {
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

fn read_fraction_tree_whir(cur: &mut ByteReader<'_>, p0: u64) -> Result<FractionTreeProof, String> {
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
        return Err("FractionTreeProof packed length mismatch".into());
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

fn write_logup_whir(prf: &LogUpGkrProof, out: &mut Vec<u8>) {
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
        write_fraction_tree_whir(wt, out);
    }
    write_fraction_tree_whir(&prf.table_tree, out);
}

fn read_logup_whir(cur: &mut ByteReader<'_>, p0: u64) -> Result<LogUpGkrProof, String> {
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
        witness_trees.push(read_fraction_tree_whir(cur, p0)?);
    }
    let table_tree = read_fraction_tree_whir(cur, p0)?;
    Ok(LogUpGkrProof {
        config,
        total_lookups,
        mult_commitment,
        witness_trees,
        table_tree,
    })
}

fn pack_subsums_58b(subs: &[[u64; 3]], out: &mut Vec<u8>) {
    let mut flat = Vec::with_capacity(subs.len() * 3);
    for s in subs {
        flat.push(s[0]);
        flat.push(s[1]);
        flat.push(s[2]);
    }
    pack_u64_bits_le(&flat, 58, out);
}

fn unpack_subsums_58b(
    cur: &mut ByteReader<'_>,
    max_triples: usize,
    max_subsum_incl: u64,
) -> Result<Vec<[u64; 3]>, String> {
    let flat = unpack_u64_bits_le(cur, 58, max_triples * 3, max_subsum_incl + 1)?;
    if flat.len() % 3 != 0 {
        return Err("58b subsum length not divisible by 3".into());
    }
    Ok(flat.chunks_exact(3).map(|c| [c[0], c[1], c[2]]).collect())
}

impl HoistedWhirBundle {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(1 << 18);
        out.extend_from_slice(HOISTED_WHIR_MAGIC);
        out.extend_from_slice(&HOISTED_WHIR_VERSION.to_le_bytes());
        out.push(match self.mode {
            LiftMode::Direct20 => 0,
            LiftMode::ExactGarner15 => 1,
        });
        out.push(if self.persistent_a { 1 } else { 0 });
        out.push(self.wit_mr);
        out.push(self.wit_mc);
        out.extend_from_slice(&self.t_queries.to_le_bytes());
        out.push(self.blow);
        out.extend_from_slice(&self.max_y_bits.to_le_bytes());
        out.extend_from_slice(&(self.r_blk as u32).to_le_bytes());
        out.extend_from_slice(&(self.k_blk as u32).to_le_bytes());
        out.extend_from_slice(&self.witness_pcs_root);

        if let Some((amr, amc, atq, abl, ref aroot)) = self.a_pcs_meta {
            out.push(1);
            out.push(amr);
            out.push(amc);
            out.extend_from_slice(&atq.to_le_bytes());
            out.push(abl);
            out.extend_from_slice(aroot);
        } else {
            out.push(0);
        }

        pack_u64_bits_le(&self.p0_poly_evals, 61, &mut out);
        pack_u64_bits_le(&self.p0_k_evals, 61, &mut out);
        pack_subsums_58b(&self.p17_poly_subsums, &mut out);
        pack_subsums_58b(&self.p17_k_subsums, &mut out);

        if let Some((ref a_p0, ref a_p17)) = self.persistent_a_evals {
            out.push(1);
            pack_u64_bits_le(a_p0, 61, &mut out);
            pack_subsums_58b(a_p17, &mut out);
        } else {
            out.push(0);
        }

        write_logup_whir(&self.logup_proof, &mut out);

        match &self.pcs_payload {
            HoistedWhirPcsPayload::Single(b) => {
                out.push(0);
                b.to_bytes(0, &mut out);
            }
            HoistedWhirPcsPayload::SharedTwo(b) => {
                out.push(1);
                b.to_bytes(0, &mut out);
            }
            HoistedWhirPcsPayload::SeparateTwo { wit_open, a_open } => {
                out.push(2);
                wit_open.to_bytes(0, &mut out);
                a_open.to_bytes(0, &mut out);
            }
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], params: &HoistedParams) -> Result<Self, String> {
        let p0 = params.all_primes[0];
        let max_subsum = 15u64 * (params.n as u64) * (1u64 << 41);
        let mut cur = ByteReader::new(bytes);
        if cur.take(8)? != HOISTED_WHIR_MAGIC {
            return Err("bad HoistedWhirBundle magic".into());
        }
        if cur.read_u32()? != HOISTED_WHIR_VERSION {
            return Err("unsupported HoistedWhirBundle version".into());
        }
        let mode = match cur.read_u8()? {
            0 => LiftMode::Direct20,
            1 => LiftMode::ExactGarner15,
            _ => return Err("invalid LiftMode byte".into()),
        };
        let persistent_a = match cur.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err("invalid persistent_a byte".into()),
        };
        let wit_mr = cur.read_u8()?;
        let wit_mc = cur.read_u8()?;
        let t_queries = cur.read_u16()?;
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
                let atq = cur.read_u16()?;
                let abl = cur.read_u8()?;
                let aroot = cur.read_hash()?;
                Some((amr, amc, atq, abl, aroot))
            }
            _ => return Err("invalid a_pcs_meta flag".into()),
        };

        let p0_poly_evals = unpack_u64_bits_le(&mut cur, 61, 1 << 20, p0)?;
        let p0_k_evals = unpack_u64_bits_le(&mut cur, 61, 1 << 16, p0)?;
        let p17_poly_subsums = unpack_subsums_58b(&mut cur, 1 << 22, max_subsum)?;
        let p17_k_subsums = unpack_subsums_58b(&mut cur, 1 << 19, max_subsum)?;

        let persistent_a_evals = match cur.read_u8()? {
            0 => None,
            1 => {
                let a_p0 = unpack_u64_bits_le(&mut cur, 61, 1 << 20, p0)?;
                let a_p17 = unpack_subsums_58b(&mut cur, 1 << 22, max_subsum)?;
                Some((a_p0, a_p17))
            }
            _ => return Err("invalid persistent_a_evals flag".into()),
        };

        let logup_proof = read_logup_whir(&mut cur, p0)?;
        let pcs_payload = match cur.read_u8()? {
            0 => HoistedWhirPcsPayload::Single(WhirOpeningBundle61::from_bytes(&mut cur, p0)?),
            1 => HoistedWhirPcsPayload::SharedTwo(WhirSharedTwoMatrixProof61::from_bytes(
                &mut cur, p0,
            )?),
            2 => {
                let wit_open = WhirOpeningBundle61::from_bytes(&mut cur, p0)?;
                let a_open = WhirOpeningBundle61::from_bytes(&mut cur, p0)?;
                HoistedWhirPcsPayload::SeparateTwo { wit_open, a_open }
            }
            _ => return Err("unknown HoistedWhirPcsPayload tag".into()),
        };

        if !cur.is_eof() {
            return Err("trailing bytes after HoistedWhirBundle".into());
        }

        Ok(HoistedWhirBundle {
            mode,
            max_y_bits,
            r_blk,
            k_blk,
            persistent_a,
            wit_mr,
            wit_mc,
            t_queries,
            blow,
            witness_pcs_root,
            a_pcs_meta,
            p0_poly_evals,
            p0_k_evals,
            p17_poly_subsums,
            p17_k_subsums,
            persistent_a_evals,
            logup_proof,
            pcs_payload,
        })
    }
}

// ================================================================================================
// §6. Parallel & Streaming Coset-NTT Encoding Helpers (`<= 768 MiB` RAM Guard!)
// ================================================================================================

#[inline]
fn pack_3_rows_ext3(ext: &[u64], w0: usize, r_start: usize) -> Vec<Ext3> {
    (0..w0)
        .map(|c| {
            [
                ext[r_start * w0 + c],
                ext[(r_start + 1) * w0 + c],
                ext[(r_start + 2) * w0 + c],
            ]
        })
        .collect()
}

#[inline]
fn dot_ext3_base_whir(fp: &FastPrime61, weights: &[Ext3], col: &[u64]) -> Ext3 {
    debug_assert_eq!(weights.len(), col.len());
    let (mut a0, mut a1, mut a2) = (0u64, 0u64, 0u64);
    for (cw, cc) in weights.chunks(32).zip(col.chunks(32)) {
        let (mut s0, mut s1, mut s2) = (0u128, 0u128, 0u128);
        for (&w, &v) in cw.iter().zip(cc.iter()) {
            let v128 = v as u128;
            s0 += (w[0] as u128) * v128;
            s1 += (w[1] as u128) * v128;
            s2 += (w[2] as u128) * v128;
        }
        a0 = fp.add(a0, fp.red128(s0));
        a1 = fp.add(a1, fp.red128(s1));
        a2 = fp.add(a2, fp.red128(s2));
    }
    [a0, a1, a2]
}

#[inline]
fn eval_poly_ext3_at_base_whir(fp: &FastPrime61, coeffs: &[Ext3], x: u64) -> Ext3 {
    let (mut a0, mut a1, mut a2) = (0u64, 0u64, 0u64);
    for c in coeffs.iter().rev() {
        a0 = fp.add(fp.mul(a0, x), c[0]);
        a1 = fp.add(fp.mul(a1, x), c[1]);
        a2 = fp.add(fp.mul(a2, x), c[2]);
    }
    [a0, a1, a2]
}

fn combine_rows_ext3_whir(
    fp: &FastPrime61,
    ext: &[u64],
    w0: usize,
    row_weights: &[Ext3],
) -> Vec<Ext3> {
    let r_cnt = row_weights.len();
    let mut out = vec![[0u64; 3]; w0];
    out.par_chunks_mut(512).enumerate().for_each(|(blk, dst)| {
        let base_c = blk * 512;
        for (dc, slot) in dst.iter_mut().enumerate() {
            let c = base_c + dc;
            let (mut a0, mut a1, mut a2) = (0u64, 0u64, 0u64);
            let (mut s0, mut s1, mut s2) = (0u128, 0u128, 0u128);
            for r in 0..r_cnt {
                let v = ext[r * w0 + c] as u128;
                let rw = row_weights[r];
                s0 += (rw[0] as u128) * v;
                s1 += (rw[1] as u128) * v;
                s2 += (rw[2] as u128) * v;
                if (r & 31) == 31 {
                    a0 = fp.add(a0, fp.red128(s0));
                    a1 = fp.add(a1, fp.red128(s1));
                    a2 = fp.add(a2, fp.red128(s2));
                    s0 = 0;
                    s1 = 0;
                    s2 = 0;
                }
            }
            *slot = [
                fp.add(a0, fp.red128(s0)),
                fp.add(a1, fp.red128(s1)),
                fp.add(a2, fp.red128(s2)),
            ];
        }
    });
    out
}

fn fill_whir_mask_slice_61(fp: &FastPrime61, root_seed: &[u8; 32], row_tag: u64, dst: &mut [u64]) {
    let mut mid = Sha256::new();
    mid.update(b"WHIR61_MASK_PRF_V1|");
    mid.update(root_seed);
    mid.update(row_tag.to_le_bytes());
    let mask61 = (1u128 << 61) - 1;
    let p = fp.p;
    let mut ctr = 0u64;
    for chunk in dst.chunks_mut(4) {
        let mut h = mid.clone();
        h.update(ctr.to_le_bytes());
        ctr += 1;
        let d: [u8; 32] = h.finalize().into();
        let lo = u128::from_le_bytes(d[0..16].try_into().unwrap());
        let hi = u128::from_le_bytes(d[16..32].try_into().unwrap());
        let cands = [
            (lo & mask61) as u64,
            ((lo >> 61) | ((hi & ((1u128 << 54) - 1)) << 67) & mask61) as u64,
            ((hi >> 5) & mask61) as u64,
            ((hi >> 66) & mask61) as u64,
        ];
        for (k, out_slot) in chunk.iter_mut().enumerate() {
            let mut v = cands[k];
            while v >= p {
                let mut h_fb = mid.clone();
                h_fb.update((u64::MAX - ctr).to_le_bytes());
                ctr += 1;
                let dfb: [u8; 32] = h_fb.finalize().into();
                v = (u64::from_le_bytes(dfb[0..8].try_into().unwrap())) & ((1u64 << 61) - 1);
            }
            *out_slot = v;
        }
    }
}

fn precompute_twiddles_61(fp: &FastPrime61, lvl: &CosetLevel61) -> Vec<u64> {
    let n = 1usize << lvl.k_sub;
    let mut tw = Vec::with_capacity((n / 2).max(1));
    let mut cur = 1u64;
    for _ in 0..(n / 2) {
        tw.push(cur);
        cur = fp.mul(cur, lvl.omega);
    }
    tw
}

#[inline]
fn build_coset_z_pows_61(
    fp: &FastPrime61,
    z_t: u64,
    n_sub: usize,
    max_w: usize,
) -> (Vec<u64>, Vec<u64>) {
    let mut z_i_pows = Vec::with_capacity(n_sub);
    let mut cur = 1u64;
    for _ in 0..n_sub {
        z_i_pows.push(cur);
        cur = fp.mul(cur, z_t);
    }
    let z_n = cur; // z_t^{n_sub}
    let q_cnt = max_w.max(1).div_ceil(n_sub);
    let mut z_qn_pows = Vec::with_capacity(q_cnt);
    let mut q_cur = 1u64;
    for _ in 0..q_cnt {
        z_qn_pows.push(q_cur);
        q_cur = fp.mul(q_cur, z_n);
    }
    (z_i_pows, z_qn_pows)
}

/// Zero-DRAM-table L1-cache `u128` coset row folder + radix-2 NTT (`16x` fewer `red128` reductions!).
#[inline]
fn encode_row_on_coset_61(
    fp: &FastPrime61,
    row: &[u64],
    n_sub: usize,
    z_i_pows: &[u64],
    z_qn_pows: &[u64],
    tw: &[u64],
    buf: &mut [u64],
) {
    let w = row.len();
    if w <= n_sub {
        for i in 0..w {
            buf[i] = fp.mul(row[i], z_i_pows[i]);
        }
        buf[w..n_sub].fill(0);
    } else {
        let q_full = w / n_sub;
        let rem = w % n_sub;
        for i in 0..n_sub {
            let mut acc_mod = 0u64;
            let mut s128 = 0u128;
            let q_lim = q_full + usize::from(i < rem);
            for q in 0..q_lim {
                let a = row[q * n_sub + i];
                if a != 0 {
                    s128 += (a as u128) * (z_qn_pows[q] as u128);
                }
                if (q & 15) == 15 {
                    acc_mod = fp.add(acc_mod, fp.red128(s128));
                    s128 = 0;
                }
            }
            let sum_i = fp.add(acc_mod, fp.red128(s128));
            buf[i] = fp.mul(sum_i, z_i_pows[i]);
        }
    }
    if n_sub >= 2 {
        radix2_ntt_natural(fp, buf, tw);
    }
}

/// Evaluate an `Ext3` polynomial `poly` (`deg < W_r`) on `lvl` using 3 parallel basefield coset NTTs!
fn encode_ext3_poly_on_level(fp: &FastPrime61, lvl: &CosetLevel61, poly: &[Ext3]) -> Vec<Ext3> {
    let w = poly.len();
    let n = 1usize << lvl.k_sub;
    let tw = precompute_twiddles_61(fp, lvl);

    let limbs: [Vec<u64>; 3] = std::array::from_fn(|limb| {
        let coeffs: Vec<u64> = poly.iter().map(|e| e[limb]).collect();
        let coset_chunks: Vec<Vec<u64>> = (0..lvl.t)
            .into_par_iter()
            .map(|tt| {
                let z_t = fp.pow(lvl.z, tt as u64);
                let (z_i_pows, z_qn_pows) = build_coset_z_pows_61(fp, z_t, n, w);
                let mut buf = vec![0u64; n];
                encode_row_on_coset_61(fp, &coeffs, n, &z_i_pows, &z_qn_pows, &tw, &mut buf);
                buf
            })
            .collect();
        let mut flat = Vec::with_capacity(lvl.npts);
        for ch in coset_chunks {
            flat.extend_from_slice(&ch);
        }
        flat
    });

    (0..lvl.npts)
        .into_par_iter()
        .map(|j| [limbs[0][j], limbs[1][j], limbs[2][j]])
        .collect()
}

fn encode_level0_column_major(fp: &FastPrime61, shape: &WhirShape61, ext: &[u64]) -> Vec<u64> {
    let lvl = &shape.level0;
    let n_sub = 1usize << lvl.k_sub;
    let tw = precompute_twiddles_61(fp, lvl);
    let (r_total, w0, n0) = (shape.r_total, shape.w0, shape.n0);

    let mut cw = vec![0u64; n0 * r_total];
    cw.par_chunks_mut(n_sub * r_total)
        .enumerate()
        .for_each(|(tt, dst_coset)| {
            let z_t = fp.pow(lvl.z, tt as u64);
            let (z_i_pows, z_qn_pows) = build_coset_z_pows_61(fp, z_t, n_sub, w0);
            let mut buf = vec![0u64; n_sub];
            for r in 0..r_total {
                let row = &ext[r * w0..(r + 1) * w0];
                encode_row_on_coset_61(fp, row, n_sub, &z_i_pows, &z_qn_pows, &tw, &mut buf);
                for i in 0..n_sub {
                    dst_coset[i * r_total + r] = buf[i];
                }
            }
        });
    cw
}

fn stream_level0_fiber_leaves(
    fp: &FastPrime61,
    shape: &WhirShape61,
    ext: &[u64],
    fiber_salts: &[[u8; 16]],
) -> Vec<[u8; 32]> {
    let _ = CosetDomain::new;
    let lvl = &shape.level0;
    let k0 = shape.k_schedule[0];
    let b0 = 1usize << k0;
    let n_sub = 1usize << lvl.k_sub;
    let fibers_per_coset = n_sub >> k0;
    let (r_total, w0) = (shape.r_total, shape.w0);
    let tw = precompute_twiddles_61(fp, lvl);

    let coset_leaf_chunks: Vec<Vec<[u8; 32]>> = (0..lvl.t)
        .into_par_iter()
        .map(|tt| {
            let z_t = fp.pow(lvl.z, tt as u64);
            let (z_i_pows, z_qn_pows) = build_coset_z_pows_61(fp, z_t, n_sub, w0);
            let mut coset_rows = vec![0u64; r_total * n_sub];
            let mut buf = vec![0u64; n_sub];
            for r in 0..r_total {
                let row = &ext[r * w0..(r + 1) * w0];
                encode_row_on_coset_61(fp, row, n_sub, &z_i_pows, &z_qn_pows, &tw, &mut buf);
                coset_rows[r * n_sub..(r + 1) * n_sub].copy_from_slice(&buf);
            }

            let stride = 1usize << (lvl.k_sub - (k0 as u32));
            let mut leaves_tt = Vec::with_capacity(fibers_per_coset);
            let mut fiber_buf = vec![0u64; b0 * r_total];
            for i_base in 0..fibers_per_coset {
                let f_idx = tt * fibers_per_coset + i_base;
                for m in 0..b0 {
                    let col_in_coset = i_base + m * stride;
                    let dst_col = &mut fiber_buf[m * r_total..(m + 1) * r_total];
                    for r in 0..r_total {
                        dst_col[r] = coset_rows[r * n_sub + col_in_coset];
                    }
                }
                leaves_tt.push(hash_whir_s0_fiber(f_idx, &fiber_salts[f_idx], &fiber_buf));
            }
            leaves_tt
        })
        .collect();

    let mut all_leaves = Vec::with_capacity(lvl.t * fibers_per_coset);
    for ch in coset_leaf_chunks {
        all_leaves.extend(ch);
    }
    all_leaves
}

fn stream_level0_selected_columns(
    fp: &FastPrime61,
    shape: &WhirShape61,
    ext: &[u64],
    js: &[usize],
) -> Vec<Vec<u64>> {
    let lvl = &shape.level0;
    let n_sub = 1usize << lvl.k_sub;
    let mask_sub = n_sub - 1;
    let (r_total, w0) = (shape.r_total, shape.w0);

    let mut needed_cosets: BTreeMap<usize, Vec<(usize, usize)>> = BTreeMap::new();
    for (out_idx, &j) in js.iter().enumerate() {
        let tt = j >> lvl.k_sub;
        let i_in = j & mask_sub;
        needed_cosets.entry(tt).or_default().push((out_idx, i_in));
    }

    let tw = precompute_twiddles_61(fp, lvl);
    let needed_vec: Vec<(usize, Vec<(usize, usize)>)> = needed_cosets.into_iter().collect();
    let per_coset_cols: Vec<Vec<(usize, Vec<u64>)>> = needed_vec
        .into_par_iter()
        .map(|(tt, reqs)| {
            let z_t = fp.pow(lvl.z, tt as u64);
            let (z_i_pows, z_qn_pows) = build_coset_z_pows_61(fp, z_t, n_sub, w0);
            let mut cols_local: Vec<Vec<u64>> = vec![Vec::with_capacity(r_total); reqs.len()];
            let mut buf = vec![0u64; n_sub];
            for r in 0..r_total {
                let row = &ext[r * w0..(r + 1) * w0];
                encode_row_on_coset_61(fp, row, n_sub, &z_i_pows, &z_qn_pows, &tw, &mut buf);
                for (ri, &(_, i_in)) in reqs.iter().enumerate() {
                    cols_local[ri].push(buf[i_in]);
                }
            }
            reqs.into_iter()
                .map(|(out_idx, _)| out_idx)
                .zip(cols_local)
                .collect()
        })
        .collect();

    let mut out = vec![Vec::new(); js.len()];
    for group in per_coset_cols {
        for (out_idx, col) in group {
            out[out_idx] = col;
        }
    }
    out
}
