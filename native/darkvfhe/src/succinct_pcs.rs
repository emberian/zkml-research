//! Standalone Multithreaded (`rayon`) 128-Bit Succinct Coset-NTT Reed–Solomon / Ligero Matrix PCS
//! over 61-Bit Crandall Primes (`FastPrime61` + Cubic Extension `Ext3`, `|F_{p^3}| > 2^{182.99}`).
//!
//! Closes `[OPEN]` Boundary #1 of `notes/native-hoisted-b61-rust-benchmarks.md`:
//! - **Radix-2 `Coset` LDE at blowup `4`** (`rate = 1/4`, relative distance `Delta = 3/4`, Unique
//!   Decoding radius `delta_UD = 3/8`).
//! - **Balanced `mr x mc` row/column split** minimizing total serialized proof bytes.
//! - **True Statistical / Perfect HVZK Blinding** (`opened columns leak zero witness information`):
//!   1. Every row appends `hide = t_cols` uniform random tail coefficients `xi_{r,0..hide-1}`; since
//!      all `npts` coset evaluation points are non-zero and distinct, the `t_cols x t_cols` shifted
//!      Vandermonde block `(x_{j_a}^{C + k})` is invertible, so any `t_cols` opened column values of
//!      any data row are uniformly distributed on `F_p^{t_cols}` and independent of the witness!
//!   2. Three uniform random proximity-mask rows (`rd .. rd + 3`) mask the `Ext3` proximity linear
//!      combination `u_prox(X)` (`deg < W`).
//!   3. Four uniform random data-blinding rows (`rd - 4 .. rd`, zero-weighted on `{0, 1}^m` in all
//!      linear claims) blind the `Ext3` evaluation linear combination `u_eval(X)` (`deg < W`) at the
//!      non-boolean sumcheck terminal point `z_row in (F_{p^3})^{mr}`.
//! - **Salted SHA-256 Merkle Multiproofs** of `t_cols = 312` distinct queried columns (`(5/8)^312 =
//!   2^{-211.56}` Unique-Decoding soundness; `(3/4)^312 = 2^{-129.49} < 2^{-128}` classical Ligero
//!   `T_LEDGER+` soundness; `< 2^{-164}` `Ext3` RLC / sumcheck soundness).

use crate::FastPrime61;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Default ledger column count: `t_cols = 312` (`> T_LEDGER = 309`), giving:
/// - Unique Decoding (`delta_UD = (1 - 1/4)/2 = 3/8`): `(5/8)^312 = 2^{-211.56}`
/// - Classical Ligero (`delta = 1/4`): `(3/4)^312 = 2^{-129.49} < 2^{-128}`.
pub const T_COLS_128: usize = 312;
pub const DEFAULT_BLOWUP: usize = 4;
pub const NUM_ZK_DATA_ROWS: usize = 4;
pub const NUM_PROX_MASK_ROWS: usize = 3;

/// Element of cubic extension field `F_{p^3} = F_p[u] / (u^3 - c1 * u - c0)` (`> 182.99` bits).
pub type Ext3 = [u64; 3];

/// Deterministic cubic extension arithmetic `F_p[u] / (u^3 - c1 * u - c0)` for any 61-bit prime `p`.
#[derive(Clone, Copy, Debug)]
pub struct Ext3Field {
    pub fp: FastPrime61,
    pub c0: u64,
    pub c1: u64,
}

impl Ext3Field {
    /// Deterministically select the lexicographically first `(c1, c0)` with `c1 in 0..p`, `c0 in 1..p`
    /// such that `P(X) = X^3 - c1 * X - c0` is provably irreducible over `F_p` (`gcd(X^p - X, P) = 1`).
    pub fn new(fp: FastPrime61) -> Self {
        for c1 in 0..16u64 {
            for c0 in 1..256u64 {
                let cand = Ext3Field { fp, c0, c1 };
                if cand.is_irreducible() {
                    return cand;
                }
            }
        }
        panic!("failed to find irreducible cubic over F_{}", fp.p);
    }

    fn is_irreducible(&self) -> bool {
        // A degree-3 polynomial P(X) over F_p is irreducible iff it has no root in F_p,
        // which holds iff gcd(X^p - X mod P(X), P(X)) == 1 AND X^{p^3} == X mod P(X).
        let u: Ext3 = [0, 1, 0];
        let u_pow_p = self.pow(u, self.fp.p);
        let diff = self.sub(u_pow_p, u); // R(X) = X^p - X mod P(X), degree <= 2
        if diff == [0, 0, 0] {
            return false; // splits into 3 distinct linear factors in F_p
        }
        // Polynomial GCD of P(X) = -c0 - c1*X + 0*X^2 + 1*X^3 and diff(X) over F_p:
        let p_poly = vec![self.fp.neg(self.c0), self.fp.neg(self.c1), 0, 1];
        let r_poly = vec![diff[0], diff[1], diff[2]];
        if Self::poly_gcd_deg(&self.fp, p_poly, r_poly) != 0 {
            return false;
        }
        // Verify Frobenius order 3: (u^p)^{p^2} == u:
        let u_pow_p2 = self.pow_big_p(u_pow_p);
        let u_pow_p3 = self.pow_big_p(u_pow_p2);
        u_pow_p3 == u
    }

    fn pow_big_p(&self, base: Ext3) -> Ext3 {
        self.pow(base, self.fp.p)
    }

    fn poly_trim(v: &mut Vec<u64>) {
        while v.len() > 1 && *v.last().unwrap() == 0 {
            v.pop();
        }
    }

    fn poly_gcd_deg(fp: &FastPrime61, mut a: Vec<u64>, mut b: Vec<u64>) -> usize {
        Self::poly_trim(&mut a);
        Self::poly_trim(&mut b);
        while !(b.len() == 1 && b[0] == 0) {
            let db = b.len() - 1;
            let inv_lb = fp.inv(b[db]);
            while a.len() > db && !(a.len() == 1 && a[0] == 0) {
                let da = a.len() - 1;
                let coef = fp.mul(a[da], inv_lb);
                let shift = da - db;
                for i in 0..=db {
                    let term = fp.mul(coef, b[i]);
                    a[i + shift] = fp.sub(a[i + shift], term);
                }
                Self::poly_trim(&mut a);
            }
            std::mem::swap(&mut a, &mut b);
        }
        a.len() - 1
    }

    #[inline(always)]
    pub fn zero(&self) -> Ext3 {
        [0, 0, 0]
    }

    #[inline(always)]
    pub fn one(&self) -> Ext3 {
        [1, 0, 0]
    }

    #[inline(always)]
    pub fn from_base(&self, x: u64) -> Ext3 {
        [if x >= self.fp.p { x % self.fp.p } else { x }, 0, 0]
    }

    #[inline(always)]
    pub fn add(&self, a: Ext3, b: Ext3) -> Ext3 {
        [
            self.fp.add(a[0], b[0]),
            self.fp.add(a[1], b[1]),
            self.fp.add(a[2], b[2]),
        ]
    }

    #[inline(always)]
    pub fn sub(&self, a: Ext3, b: Ext3) -> Ext3 {
        [
            self.fp.sub(a[0], b[0]),
            self.fp.sub(a[1], b[1]),
            self.fp.sub(a[2], b[2]),
        ]
    }

    #[inline(always)]
    pub fn neg(&self, a: Ext3) -> Ext3 {
        [self.fp.neg(a[0]), self.fp.neg(a[1]), self.fp.neg(a[2])]
    }

    #[inline(always)]
    pub fn scale(&self, a: Ext3, s: u64) -> Ext3 {
        [
            self.fp.mul(a[0], s),
            self.fp.mul(a[1], s),
            self.fp.mul(a[2], s),
        ]
    }

    #[inline(always)]
    pub fn mul(&self, a: Ext3, b: Ext3) -> Ext3 {
        let fp = &self.fp;
        // Degree <= 4 product: d0 + d1*u + d2*u^2 + d3*u^3 + d4*u^4
        let d0 = fp.mul(a[0], b[0]);
        let d1 = fp.red128(a[0] as u128 * b[1] as u128 + a[1] as u128 * b[0] as u128);
        let d2 = fp.red128(
            a[0] as u128 * b[2] as u128 + a[1] as u128 * b[1] as u128 + a[2] as u128 * b[0] as u128,
        );
        let d3 = fp.red128(a[1] as u128 * b[2] as u128 + a[2] as u128 * b[1] as u128);
        let d4 = fp.mul(a[2], b[2]);

        // Reduce u^4 = c0*u + c1*u^2, then u^3 = c0 + c1*u:
        let d3_eff = d3;
        let r2 = fp.add(d2, fp.mul(d4, self.c1));
        let r1 =
            fp.red128(d1 as u128 + d4 as u128 * self.c0 as u128 + d3_eff as u128 * self.c1 as u128);
        let r0 = fp.add(d0, fp.mul(d3_eff, self.c0));
        [r0, r1, r2]
    }

    pub fn pow(&self, mut base: Ext3, mut exp: u64) -> Ext3 {
        let mut acc = self.one();
        while exp > 0 {
            if exp & 1 == 1 {
                acc = self.mul(acc, base);
            }
            base = self.mul(base, base);
            exp >>= 1;
        }
        acc
    }

    ///Multiplicative inverse in `F_{p^3}^*` via Norm `x^{-1} = x^{p^2 + p} / (x * x^p * x^{p^2})` (`x^{p^2+p} in F_{p^3}`, norm in `F_p^*`!).
    pub fn inv(&self, x: Ext3) -> Ext3 {
        assert!(x != [0, 0, 0], "Ext3 division by zero");
        let xp = self.pow(x, self.fp.p);
        let xp2 = self.pow(xp, self.fp.p);
        let conj = self.mul(xp, xp2);
        let norm_ext = self.mul(x, conj);
        debug_assert_eq!(norm_ext[1], 0);
        debug_assert_eq!(norm_ext[2], 0);
        let inv_norm = self.fp.inv(norm_ext[0]);
        self.scale(conj, inv_norm)
    }

    /// Evaluate `eq_le(z, x)` table over `{0, 1}^k` in little-endian bit order (`idx = sum_{b=0}^{k-1} 2^b x_b`).
    pub fn build_eq_le(&self, z: &[Ext3]) -> Vec<Ext3> {
        let mut v = vec![self.one()];
        let one = self.one();
        for &zk in z.iter().rev() {
            let om = self.sub(one, zk);
            let mut next = Vec::with_capacity(v.len() * 2);
            for &val in &v {
                next.push(self.mul(val, om));
                next.push(self.mul(val, zk));
            }
            v = next;
        }
        v
    }
}

/// Radix-2 Coset evaluation domain: `T` disjoint cosets `z^t * {1, omega, ..., omega^{2^k - 1}}`
/// of the order-`2^k` multiplicative subgroup of `F_p^*`, in natural order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CosetDomain {
    pub p: u64,
    pub k: u32,
    pub t: usize,
    pub omega: u64,
    pub z: u64,
    pub npts: usize,
}

impl CosetDomain {
    pub fn new(fp: &FastPrime61, npts: usize, w: usize) -> Self {
        let p = fp.p;
        let s = (p - 1).trailing_zeros();
        assert!(s >= 1, "prime must be odd");
        let mut best: Option<(usize, u32, usize)> = None;
        for k in 1..=s {
            let t = npts.div_ceil(1usize << k);
            let cost = t * ((1usize << (k - 1)) * k as usize + w);
            if best.is_none_or(|b| cost <= b.0) {
                best = Some((cost, k, t));
            }
        }
        let (_, k, t) = best.unwrap();
        let mut h = 2u64;
        while fp.pow(h, (p - 1) / 2) != p - 1 {
            h += 1;
        }
        let omega = fp.pow(h, (p - 1) >> k);
        let mut z = 2u64;
        while (1..t).any(|tt| fp.pow(z, (tt as u64) << k) == 1) {
            z += 1;
        }
        CosetDomain {
            p,
            k,
            t,
            omega,
            z,
            npts,
        }
    }

    #[inline]
    pub fn point(&self, fp: &FastPrime61, j: usize) -> u64 {
        let mask = (1usize << self.k) - 1;
        fp.mul(
            fp.pow(self.z, (j >> self.k) as u64),
            fp.pow(self.omega, (j & mask) as u64),
        )
    }
}

/// In-place natural-order radix-2 NTT over `FastPrime61`: `a[i] <- sum_c a[c] * omega^{c * i}`.
pub fn radix2_ntt_natural(fp: &FastPrime61, a: &mut [u64], tw: &[u64]) {
    let n = a.len();
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = if lg == 0 {
            0
        } else {
            i.reverse_bits() >> (usize::BITS - lg)
        };
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            let (lo, hi) = a[st..st + len].split_at_mut(half);
            for j in 0..half {
                let u = lo[j];
                let v = fp.mul(hi[j], tw[j * step]);
                lo[j] = fp.add(u, v);
                hi[j] = fp.sub(u, v);
            }
        }
        len <<= 1;
    }
}

#[inline]
pub fn bitlen_usize(x: usize) -> usize {
    if x == 0 {
        0
    } else {
        (usize::BITS - x.leading_zeros()) as usize
    }
}

/// Public matrix commitment shape (`mr` row bits, `mc` column bits, `blow` LDE blowup, `t_cols` queries).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PcsShape {
    pub p: u64,
    pub mr: usize,
    pub mc: usize,
    pub rd: usize,
    pub usable_rows: usize,
    pub c: usize,
    pub t_cols: usize,
    pub hide: usize,
    pub r_total: usize,
    pub w: usize,
    pub blow: usize,
    pub npts: usize,
    pub tree_levels: usize,
    pub domain: CosetDomain,
}

impl PcsShape {
    /// Choose balanced `(mr, mc)` for `num_elems` field elements (`mc >= min_mc`, `mr >= 3`)
    /// minimizing serialized proof bytes: `6 * (2^mc + t_cols) + t_cols * (2^mr + 3)`.
    pub fn for_len(
        fp: &FastPrime61,
        num_elems: usize,
        min_mc: usize,
        t_cols: usize,
        blow: usize,
    ) -> Self {
        let min_mc = min_mc.max(4);
        let mut best: Option<(usize, usize, usize)> = None;
        for mc in min_mc..=20 {
            let c = 1usize << mc;
            let needed_data_rows = num_elems.max(1).div_ceil(c);
            let min_rd = (needed_data_rows + NUM_ZK_DATA_ROWS)
                .max(8)
                .next_power_of_two();
            let mr = min_rd.trailing_zeros() as usize;
            if mr + mc > 30 {
                continue;
            }
            let rd = 1usize << mr;
            let r_total = rd + NUM_PROX_MASK_ROWS;
            let w = c + t_cols;
            let npts = blow * w;
            if t_cols > npts {
                continue;
            }
            // Approximate proof words: 6 * w (u_prox + u_eval) + t_cols * r_total (columns) + 2 * (mr + mc) * 9 (sumcheck)
            let cost_words = 6 * w + t_cols * r_total + 9 * (mr + mc);
            if best.is_none_or(|b| cost_words < b.0) {
                best = Some((cost_words, mr, mc));
            }
        }
        let (_, mr, mc) = best.expect("valid PCS shape");
        Self::from_mr_mc(fp, mr, mc, t_cols, blow)
    }

    pub fn from_mr_mc(fp: &FastPrime61, mr: usize, mc: usize, t_cols: usize, blow: usize) -> Self {
        assert!(mr >= 3 && mc >= 4 && blow >= 2);
        let rd = 1usize << mr;
        let usable_rows = rd - NUM_ZK_DATA_ROWS;
        let c = 1usize << mc;
        let hide = t_cols;
        let r_total = rd + NUM_PROX_MASK_ROWS;
        let w = c + hide;
        let npts = blow * w;
        assert!(t_cols < npts);
        let tree_levels = bitlen_usize(npts - 1);
        let domain = CosetDomain::new(fp, npts, w);
        PcsShape {
            p: fp.p,
            mr,
            mc,
            rd,
            usable_rows,
            c,
            t_cols,
            hide,
            r_total,
            w,
            blow,
            npts,
            tree_levels,
            domain,
        }
    }

    /// Exact interactive/UD soundness bits `(ud_col_bits, ligero_col_bits, ext3_alg_bits)`.
    pub fn soundness_bits(&self) -> (f64, f64, f64) {
        let rate = (self.w as f64) / (self.npts as f64); // 0.25 at blow=4
        let delta_ud = (1.0 - rate) / 2.0; // 0.375 at blow=4 ([BCIKS20] correlated agreement / UD)
        let ud_bits = -(self.t_cols as f64) * (1.0 - delta_ud).log2();
        let delta_lig = (1.0 - rate) / 3.0; // 0.25 at blow=4 (classical [AHIV17] Ligero third-distance)
        let lig_bits = -(self.t_cols as f64) * (1.0 - delta_lig).log2();
        let p3_bits = 3.0 * (self.p as f64).log2();
        let alg_err_log2 = ((self.npts + 4 * (self.mr + self.mc)) as f64).log2() - p3_bits;
        (ud_bits, lig_bits, -alg_err_log2)
    }
}

// ---------------------------------------------------------------------------------------
// Deterministic CSPRNG / Seeded Blinding Stream & Salted SHA-256 Merkle Multiproofs
// ---------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct PcsRng {
    seed: [u8; 32],
    ctr: u64,
}

impl PcsRng {
    pub fn from_os() -> Self {
        let mut seed = [0u8; 32];
        #[cfg(unix)]
        {
            use std::io::Read;
            if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                let _ = f.read_exact(&mut seed);
            }
        }
        // Mix monotonic timestamp + address jitter as defense-in-depth:
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_PCS_OS_RNG|");
        h.update(seed);
        h.update(
            (std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0))
            .to_le_bytes(),
        );
        PcsRng {
            seed: h.finalize().into(),
            ctr: 0,
        }
    }

    pub fn from_seed(seed: [u8; 32]) -> Self {
        PcsRng { seed, ctr: 0 }
    }

    #[inline]
    pub fn next_block(&mut self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.seed);
        h.update(self.ctr.to_le_bytes());
        self.ctr += 1;
        h.finalize().into()
    }

    pub fn fill_fp_row(&mut self, fp: &FastPrime61, row_tag: u64, dst: &mut [u64]) {
        for (sub_ctr, chunk) in dst.chunks_mut(2).enumerate() {
            let mut h = Sha256::new();
            h.update(b"PCS_MASK_ROW|");
            h.update(self.seed);
            h.update(row_tag.to_le_bytes());
            h.update((sub_ctr as u64).to_le_bytes());
            let d: [u8; 32] = h.finalize().into();
            let lo = u128::from_le_bytes(d[0..16].try_into().unwrap());
            chunk[0] = fp.red128(lo);
            if chunk.len() > 1 {
                let hi = u128::from_le_bytes(d[16..32].try_into().unwrap());
                chunk[1] = fp.red128(hi);
            }
        }
    }

    pub fn salt_for_col(&self, j: usize) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"PCS_COL_SALT|");
        h.update(self.seed);
        h.update((j as u64).to_le_bytes());
        h.finalize().into()
    }
}

#[inline]
pub fn hash_pcs_leaf(j: usize, salt: &[u8; 32], col: &[u64]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_PCS_LEAF_V1|");
    h.update((j as u32).to_le_bytes());
    h.update(salt);
    let mut raw = Vec::with_capacity(col.len() * 8);
    for &v in col {
        raw.extend_from_slice(&v.to_le_bytes());
    }
    h.update(&raw);
    h.finalize().into()
}

#[inline]
pub fn hash_pcs_pad(j: usize) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_PCS_PAD_V1|");
    h.update((j as u32).to_le_bytes());
    h.finalize().into()
}

#[inline]
pub fn hash_pcs_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"DARKVFHE_PCS_NODE_V1|");
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// Canonical `(level, node_whose_sibling_is_needed)` schedule for a deduplicated Merkle multiproof.
pub fn multiproof_needed(js: &[usize], levels: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for l in 0..levels {
        let known: BTreeSet<usize> = js.iter().map(|&j| j >> l).collect();
        for &x in &known {
            if !known.contains(&(x ^ 1)) {
                out.push((l, x));
            }
        }
    }
    out
}

/// Deduplicated salted SHA-256 Merkle multiproof for `t_cols` distinct column openings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleMultiproof {
    pub salts: Vec<[u8; 32]>,
    pub siblings: Vec<[u8; 32]>,
}

pub fn build_merkle_tree(mut leaves: Vec<[u8; 32]>, tree_levels: usize) -> Vec<Vec<[u8; 32]>> {
    let full = 1usize << tree_levels;
    let cur_len = leaves.len();
    for j in cur_len..full {
        leaves.push(hash_pcs_pad(j));
    }
    let mut tree = vec![leaves];
    while tree.last().unwrap().len() > 1 {
        let prev = tree.last().unwrap();
        let next: Vec<[u8; 32]> = if prev.len() >= 512 {
            prev.par_chunks(2)
                .map(|c| hash_pcs_node(&c[0], &c[1]))
                .collect()
        } else {
            prev.chunks(2)
                .map(|c| hash_pcs_node(&c[0], &c[1]))
                .collect()
        };
        tree.push(next);
    }
    tree
}

pub fn prove_multiproof(
    tree: &[Vec<[u8; 32]>],
    salts: &[[u8; 32]],
    js: &[usize],
) -> MerkleMultiproof {
    let levels = tree.len() - 1;
    let chosen_salts: Vec<[u8; 32]> = js.iter().map(|&j| salts[j]).collect();
    let needed = multiproof_needed(js, levels);
    let siblings: Vec<[u8; 32]> = needed.into_iter().map(|(l, x)| tree[l][x ^ 1]).collect();
    MerkleMultiproof {
        salts: chosen_salts,
        siblings,
    }
}

pub fn verify_multiproof(
    expected_root: &[u8; 32],
    npts: usize,
    tree_levels: usize,
    js: &[usize],
    cols: &[Vec<u64>],
    mp: &MerkleMultiproof,
) -> Result<(), String> {
    if js.is_empty() || js.len() != cols.len() || js.len() != mp.salts.len() {
        return Err("Merkle multiproof count mismatch".into());
    }
    let mut seen = BTreeSet::new();
    for &j in js {
        if j >= npts || !seen.insert(j) {
            return Err("Merkle multiproof invalid or duplicate column index".into());
        }
    }
    let needed = multiproof_needed(js, tree_levels);
    if mp.siblings.len() != needed.len() {
        return Err("Merkle multiproof sibling count mismatch".into());
    }
    let leaf_hashes: Vec<[u8; 32]> = (0..js.len())
        .into_par_iter()
        .map(|i| hash_pcs_leaf(js[i], &mp.salts[i], &cols[i]))
        .collect();

    let mut known: BTreeMap<usize, [u8; 32]> = js.iter().copied().zip(leaf_hashes).collect();
    let mut sib_iter = mp.siblings.iter();
    for _l in 0..tree_levels {
        let mut next = BTreeMap::new();
        for (&x, hx) in &known {
            if x & 1 == 1 && known.contains_key(&(x ^ 1)) {
                continue; // already combined when processing even partner `x ^ 1`
            }
            let sb = match known.get(&(x ^ 1)) {
                Some(h) => h,
                None => sib_iter
                    .next()
                    .ok_or_else(|| "Merkle multiproof sibling underflow".to_string())?,
            };
            let parent = if x & 1 == 0 {
                hash_pcs_node(hx, sb)
            } else {
                hash_pcs_node(sb, hx)
            };
            next.insert(x >> 1, parent);
        }
        known = next;
    }
    if sib_iter.next().is_some() || known.len() != 1 {
        return Err("Merkle multiproof trailing siblings".into());
    }
    let computed_root = known.values().next().unwrap();
    if computed_root != expected_root {
        return Err("Merkle multiproof root mismatch (forged column or path)".into());
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Fiat–Shamir Transcript for SuccinctPcs
// ---------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct PcsTranscript {
    state: [u8; 32],
}

impl PcsTranscript {
    pub fn new(domain_tag: &str, p: u64, root: &[u8; 32], context: &[u8; 32]) -> Self {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_SUCCINCT_PCS_V1|");
        h.update(domain_tag.as_bytes());
        h.update(p.to_le_bytes());
        h.update(root);
        h.update(context);
        PcsTranscript {
            state: h.finalize().into(),
        }
    }

    pub fn absorb_bytes(&mut self, data: &[u8]) {
        let mut h = Sha256::new();
        h.update(self.state);
        h.update((data.len() as u64).to_le_bytes());
        h.update(data);
        self.state = h.finalize().into();
    }

    pub fn absorb_ext3(&mut self, x: &Ext3) {
        let mut buf = [0u8; 24];
        buf[0..8].copy_from_slice(&x[0].to_le_bytes());
        buf[8..16].copy_from_slice(&x[1].to_le_bytes());
        buf[16..24].copy_from_slice(&x[2].to_le_bytes());
        let mut h = Sha256::new();
        h.update(self.state);
        h.update(buf);
        self.state = h.finalize().into();
    }

    pub fn absorb_poly3(&mut self, tag: &str, poly: &[Ext3]) {
        let mut h = Sha256::new();
        h.update(self.state);
        h.update(tag.as_bytes());
        h.update((poly.len() as u64).to_le_bytes());
        for c in poly {
            h.update(c[0].to_le_bytes());
            h.update(c[1].to_le_bytes());
            h.update(c[2].to_le_bytes());
        }
        self.state = h.finalize().into();
    }

    pub fn squeeze_fp(&mut self, fp: &FastPrime61, tag: u64) -> u64 {
        let mut h = Sha256::new();
        h.update(self.state);
        h.update(b"FP|");
        h.update(tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        self.state = out;
        fp.red128(u128::from_le_bytes(out[0..16].try_into().unwrap()))
    }

    pub fn squeeze_ext3(&mut self, ef: &Ext3Field, tag: u64) -> Ext3 {
        [
            self.squeeze_fp(&ef.fp, tag * 3),
            self.squeeze_fp(&ef.fp, tag * 3 + 1),
            self.squeeze_fp(&ef.fp, tag * 3 + 2),
        ]
    }

    /// Sample `t_cols` distinct column indices in `[0, npts)` without replacement.
    pub fn squeeze_distinct_cols(&mut self, t_cols: usize, npts: usize) -> Vec<usize> {
        assert!(t_cols <= npts);
        let mut out = Vec::with_capacity(t_cols);
        let mut seen = HashMap::with_capacity(t_cols * 2);
        let mut ctr = 0u64;
        while out.len() < t_cols {
            let mut h = Sha256::new();
            h.update(self.state);
            h.update(b"COLS|");
            h.update(ctr.to_le_bytes());
            ctr += 1;
            let digest: [u8; 32] = h.finalize().into();
            for chunk in digest.chunks_exact(8) {
                if out.len() == t_cols {
                    break;
                }
                let idx = (u64::from_le_bytes(chunk.try_into().unwrap()) as usize) % npts;
                if seen.insert(idx, ()).is_none() {
                    out.push(idx);
                }
            }
        }
        self.absorb_bytes(b"COLS_DONE");
        out
    }
}

// ---------------------------------------------------------------------------------------
// Prover Commitment & Structured Batched Linear Evaluation Opening
// ---------------------------------------------------------------------------------------

/// A structured linear claim on `N`-aligned slots of a `SuccinctMatrixPcs` (`N = 2^log_n` divides `C = 2^mc`):
/// Claims that `sum_{(vec_idx, slot_terms)} sum_{(slot, w_slot)} w_slot * <M_slot[0..N], v_family[vec_idx]> == rhs`.
#[derive(Clone, Debug)]
pub struct SlotLinearClaim {
    pub terms: Vec<(usize, Vec<(usize, u64)>)>,
    pub rhs: u64,
}

impl SlotLinearClaim {
    pub fn single_vec(vec_idx: usize, slot_terms: Vec<(usize, u64)>, rhs: u64) -> Self {
        SlotLinearClaim {
            terms: vec![(vec_idx, slot_terms)],
            rhs,
        }
    }
}

/// Self-contained succinct opening proof for `SuccinctMatrixPcs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctPcsOpeningProof {
    /// `(mr + mc)` quadratic sumcheck round polynomials `[c0, c1, c2]` over `Ext3` (`g(X) = c0 + c1*X + c2*X^2`).
    pub sumcheck_rounds: Vec<[Ext3; 3]>,
    /// Masked `Ext3` proximity linear combination polynomial `u_prox(X)` of degree `< W` (`len == W`).
    pub u_prox: Vec<Ext3>,
    /// ZK-row-blinded `Ext3` evaluation linear combination polynomial `u_eval(X)` of degree `< W` (`len == W`).
    pub u_eval: Vec<Ext3>,
    /// Distinct queried column indices (`len == t_cols`).
    pub col_indices: Vec<usize>,
    /// Opened column vectors at `col_indices` (`t_cols` vectors, each length `r_total`).
    pub opened_cols: Vec<Vec<u64>>,
    /// Deduplicated salted SHA-256 Merkle multiproof for `opened_cols`.
    pub multiproof: MerkleMultiproof,
}

impl SuccinctPcsOpeningProof {
    pub fn to_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.sumcheck_rounds.len() as u32).to_le_bytes());
        for r in &self.sumcheck_rounds {
            for e in r {
                for &v in e {
                    out.extend_from_slice(&v.to_le_bytes());
                }
            }
        }
        out.extend_from_slice(&(self.u_prox.len() as u32).to_le_bytes());
        for e in &self.u_prox {
            for &v in e {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.u_eval.len() as u32).to_le_bytes());
        for e in &self.u_eval {
            for &v in e {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.col_indices.len() as u32).to_le_bytes());
        for &j in &self.col_indices {
            out.extend_from_slice(&(j as u32).to_le_bytes());
        }
        let col_h = self.opened_cols.first().map_or(0, Vec::len);
        out.extend_from_slice(&(col_h as u32).to_le_bytes());
        for col in &self.opened_cols {
            debug_assert_eq!(col.len(), col_h);
            for &v in col {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        out.extend_from_slice(&(self.multiproof.salts.len() as u32).to_le_bytes());
        for s in &self.multiproof.salts {
            out.extend_from_slice(s);
        }
        out.extend_from_slice(&(self.multiproof.siblings.len() as u32).to_le_bytes());
        for s in &self.multiproof.siblings {
            out.extend_from_slice(s);
        }
    }

    pub fn from_bytes(cur: &mut ByteReader<'_>, p: u64) -> Result<Self, String> {
        let n_sc = cur.read_u32()? as usize;
        if n_sc > 32 {
            return Err("sumcheck round count out of bounds".into());
        }
        let mut sumcheck_rounds = Vec::with_capacity(n_sc);
        for _ in 0..n_sc {
            sumcheck_rounds.push([cur.read_ext3(p)?, cur.read_ext3(p)?, cur.read_ext3(p)?]);
        }
        let w_prox = cur.read_u32()? as usize;
        if w_prox > (1 << 22) {
            return Err("u_prox length out of bounds".into());
        }
        let mut u_prox = Vec::with_capacity(w_prox);
        for _ in 0..w_prox {
            u_prox.push(cur.read_ext3(p)?);
        }
        let w_eval = cur.read_u32()? as usize;
        if w_eval != w_prox {
            return Err("u_eval length != u_prox length".into());
        }
        let mut u_eval = Vec::with_capacity(w_eval);
        for _ in 0..w_eval {
            u_eval.push(cur.read_ext3(p)?);
        }
        let t_cols = cur.read_u32()? as usize;
        if t_cols == 0 || t_cols > 4096 {
            return Err("t_cols out of bounds".into());
        }
        let mut col_indices = Vec::with_capacity(t_cols);
        for _ in 0..t_cols {
            col_indices.push(cur.read_u32()? as usize);
        }
        let col_h = cur.read_u32()? as usize;
        if col_h == 0 || col_h > (1 << 20) {
            return Err("column height out of bounds".into());
        }
        let mut opened_cols = Vec::with_capacity(t_cols);
        for _ in 0..t_cols {
            let mut col = Vec::with_capacity(col_h);
            for _ in 0..col_h {
                col.push(cur.read_fp(p)?);
            }
            opened_cols.push(col);
        }
        let n_salts = cur.read_u32()? as usize;
        if n_salts != t_cols {
            return Err("multiproof salt count != t_cols".into());
        }
        let mut salts = Vec::with_capacity(n_salts);
        for _ in 0..n_salts {
            salts.push(cur.read_hash()?);
        }
        let n_sibs = cur.read_u32()? as usize;
        if n_sibs > t_cols * 32 {
            return Err("multiproof sibling count out of bounds".into());
        }
        let mut siblings = Vec::with_capacity(n_sibs);
        for _ in 0..n_sibs {
            siblings.push(cur.read_hash()?);
        }
        Ok(SuccinctPcsOpeningProof {
            sumcheck_rounds,
            u_prox,
            u_eval,
            col_indices,
            opened_cols,
            multiproof: MerkleMultiproof { salts, siblings },
        })
    }
}

/// Prover-side committed matrix state (`ext` rows, per-column salts, Merkle tree, and cached/streamed codeword).
#[derive(Clone)]
pub struct CommittedMatrixPcs {
    pub ef: Ext3Field,
    pub shape: PcsShape,
    /// `r_total x w` extended polynomial coefficient matrix (row-major).
    pub ext: Vec<u64>,
    pub salts: Vec<[u8; 32]>,
    pub tree: Vec<Vec<[u8; 32]>>,
    pub root: [u8; 32],
    /// Column-major codeword `npts x r_total` when held in RAM (`<= 768 MiB`), else empty (streamed on open).
    cw: Vec<u64>,
}

impl CommittedMatrixPcs {
    /// Commit a flat witness slice `data` (length `<= shape.usable_rows * shape.c`) with fresh OS randomness.
    pub fn commit(fp: FastPrime61, data: &[u64], min_mc: usize) -> Self {
        Self::commit_with_rng(
            fp,
            data,
            min_mc,
            T_COLS_128,
            DEFAULT_BLOWUP,
            PcsRng::from_os(),
        )
    }

    /// Commit with explicit `t_cols`, `blow`, and `PcsRng` (supports deterministic testing & custom profiles).
    pub fn commit_with_rng(
        fp: FastPrime61,
        data: &[u64],
        min_mc: usize,
        t_cols: usize,
        blow: usize,
        mut rng: PcsRng,
    ) -> Self {
        let shape = PcsShape::for_len(&fp, data.len(), min_mc, t_cols, blow);
        assert!(
            data.len() <= shape.usable_rows * shape.c,
            "data exceeds usable_rows * C capacity"
        );
        let ef = Ext3Field::new(fp);
        let (c, w, _rd, r_total, usable) =
            (shape.c, shape.w, shape.rd, shape.r_total, shape.usable_rows);

        let mut ext = vec![0u64; r_total * w];
        // Fill data rows 0..usable + random tail masks [c..w) in parallel using per-row keyed PRF:
        let rng_snapshot = rng.clone();
        ext[..usable * w]
            .par_chunks_mut(w)
            .enumerate()
            .for_each(|(r, row_dst)| {
                let start = r * c;
                if start < data.len() {
                    let end = (start + c).min(data.len());
                    for (i, &val) in data[start..end].iter().enumerate() {
                        row_dst[i] = if val >= fp.p { val % fp.p } else { val };
                    }
                }
                let mut row_rng = rng_snapshot.clone();
                row_rng.fill_fp_row(&fp, r as u64, &mut row_dst[c..w]);
            });

        // Fill 4 ZK data-blinding rows (`usable .. rd`) + 3 ZK proximity-mask rows (`rd .. r_total`):
        for r in usable..r_total {
            rng.fill_fp_row(&fp, (1u64 << 32) + r as u64, &mut ext[r * w..(r + 1) * w]);
        }

        let salts: Vec<[u8; 32]> = (0..shape.npts)
            .into_par_iter()
            .map(|j| rng_snapshot.salt_for_col(j))
            .collect();

        let hold_cw = shape.r_total * shape.npts * 8 <= (768usize << 20);
        let (cw, leaves) = if hold_cw {
            let cw = encode_coset_column_major(&fp, &shape, &ext);
            let leaves: Vec<[u8; 32]> = (0..shape.npts)
                .into_par_iter()
                .map(|j| {
                    let col = &cw[j * r_total..(j + 1) * r_total];
                    hash_pcs_leaf(j, &salts[j], col)
                })
                .collect();
            (cw, leaves)
        } else {
            let leaves = stream_coset_leaves(&fp, &shape, &ext, &salts);
            (Vec::new(), leaves)
        };

        let tree = build_merkle_tree(leaves, shape.tree_levels);
        let root = tree.last().unwrap()[0];

        CommittedMatrixPcs {
            ef,
            shape,
            ext,
            salts,
            tree,
            root,
            cw,
        }
    }

    /// Open a batch of `SlotLinearClaim`s (`N = 2^log_n` divides `C = 2^mc`) against `self.root`.
    pub fn open_slot_claims(
        &self,
        log_n: usize,
        v_families: &[Vec<u64>],
        claims: &[SlotLinearClaim],
        context: &[u8; 32],
    ) -> SuccinctPcsOpeningProof {
        let fp = &self.ef.fp;
        let ef = &self.ef;
        let sh = &self.shape;
        let n_poly = 1usize << log_n;
        assert!(log_n <= sh.mc && sh.c.is_multiple_of(n_poly));
        let polys_per_row = sh.c / n_poly;
        let _total_slots = sh.rd * polys_per_row;
        let usable_slots = sh.usable_rows * polys_per_row;

        let mut tr = PcsTranscript::new("SLOT_OPEN", fp.p, &self.root, context);
        tr.absorb_bytes(&(claims.len() as u64).to_le_bytes());
        for cl in claims {
            tr.absorb_bytes(&cl.rhs.to_le_bytes());
        }

        // 1. Batch all claims with powers `1, beta, beta^2, ...` in `Ext3` using sparse per-slot lists:
        let beta = tr.squeeze_ext3(ef, 1);
        let mut slot_sparse: Vec<Vec<(usize, Ext3)>> = vec![Vec::new(); usable_slots];
        let mut y_batch = ef.zero();
        let mut beta_pw = ef.one();

        for cl in claims {
            y_batch = ef.add(y_batch, ef.scale(beta_pw, cl.rhs % fp.p));
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

        // Materialize `a_tbl` (`rd * c` Ext3 entries; `0` on ZK blinding rows `usable_slots..total_slots`!)
        // using lazy `u128` inner products (`<= 16` 122-bit products per `red128`), and fold Round 0 directly
        // against base-field `self.ext` (`u64`) without allocating a full-size `rd * c` `Ext3` `m_tbl`!
        let total_cells = sh.rd * sh.c;
        let mut a_tbl = vec![ef.zero(); total_cells];
        a_tbl[..usable_slots * n_poly]
            .par_chunks_mut(n_poly)
            .enumerate()
            .for_each(|(slot, dst)| {
                let sw = &slot_sparse[slot];
                if sw.is_empty() {
                    return;
                }
                let slices: Vec<(&[u64], Ext3)> = sw
                    .iter()
                    .filter(|&&(_, w_ext)| w_ext != [0, 0, 0])
                    .map(|&(vi, w_ext)| (v_families[vi].as_slice(), w_ext))
                    .collect();
                if slices.is_empty() {
                    return;
                }
                for j in 0..n_poly {
                    let mut a0 = 0u64;
                    let mut a1 = 0u64;
                    let mut a2 = 0u64;
                    let mut s0 = 0u128;
                    let mut s1 = 0u128;
                    let mut s2 = 0u128;
                    for (k, &(vf, w_ext)) in slices.iter().enumerate() {
                        let vj = vf[j] as u128;
                        if vj != 0 {
                            s0 += (w_ext[0] as u128) * vj;
                            s1 += (w_ext[1] as u128) * vj;
                            s2 += (w_ext[2] as u128) * vj;
                        }
                        if k & 15 == 15 {
                            a0 = fp.add(a0, fp.red128(s0));
                            a1 = fp.add(a1, fp.red128(s1));
                            a2 = fp.add(a2, fp.red128(s2));
                            s0 = 0;
                            s1 = 0;
                            s2 = 0;
                        }
                    }
                    dst[j] = [
                        fp.add(a0, fp.red128(s0)),
                        fp.add(a1, fp.red128(s1)),
                        fp.add(a2, fp.red128(s2)),
                    ];
                }
            });

        // 2. Run `m = mc + mr` quadratic sumcheck rounds in `Ext3` (`idx` little-endian: bit 0 folded first):
        let m_bits = sh.mc + sh.mr;
        let mut sumcheck_rounds = Vec::with_capacity(m_bits);
        let mut z_challenges = Vec::with_capacity(m_bits);

        // Round 0 (`total_cells -> total_cells / 2`) directly against `self.ext` (`u64`):
        let half0 = total_cells / 2;
        let eval_pair_r0 = |u: usize| -> [Ext3; 3] {
            let idx0 = 2 * u;
            let r = idx0 >> sh.mc;
            let c0_idx = idx0 & (sh.c - 1);
            let m0 = self.ext[r * sh.w + c0_idx];
            let m1 = self.ext[r * sh.w + c0_idx + 1];
            let dm = fp.sub(m1, m0);
            let a0 = a_tbl[idx0];
            let a1 = a_tbl[idx0 + 1];
            let da = ef.sub(a1, a0);
            let c0 = ef.scale(a0, m0);
            let c1 = ef.add(ef.scale(a0, dm), ef.scale(da, m0));
            let c2 = ef.scale(da, dm);
            [c0, c1, c2]
        };
        let poly0 = if half0 >= 2048 {
            (0..half0).into_par_iter().map(eval_pair_r0).reduce(
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
                let x = eval_pair_r0(u);
                acc[0] = ef.add(acc[0], x[0]);
                acc[1] = ef.add(acc[1], x[1]);
                acc[2] = ef.add(acc[2], x[2]);
            }
            acc
        };
        tr.absorb_ext3(&poly0[0]);
        tr.absorb_ext3(&poly0[1]);
        tr.absorb_ext3(&poly0[2]);
        let r_0 = tr.squeeze_ext3(ef, 100);
        sumcheck_rounds.push(poly0);
        z_challenges.push(r_0);

        let mut m_tbl: Vec<Ext3> = (0..half0)
            .into_par_iter()
            .map(|u| {
                let idx0 = 2 * u;
                let r = idx0 >> sh.mc;
                let c0_idx = idx0 & (sh.c - 1);
                let m0 = self.ext[r * sh.w + c0_idx];
                let m1 = self.ext[r * sh.w + c0_idx + 1];
                ef.add([m0, 0, 0], ef.scale(r_0, fp.sub(m1, m0)))
            })
            .collect();
        let next_a0: Vec<Ext3> = (0..half0)
            .into_par_iter()
            .map(|u| {
                let (x0, x1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                ef.add(x0, ef.mul(r_0, ef.sub(x1, x0)))
            })
            .collect();
        a_tbl = next_a0;
        let mut cur_len = half0;

        for round in 1..m_bits {
            let half = cur_len / 2;
            let eval_pair = |u: usize| -> [Ext3; 3] {
                let a0 = a_tbl[2 * u];
                let a1 = a_tbl[2 * u + 1];
                let m0 = m_tbl[2 * u];
                let m1 = m_tbl[2 * u + 1];
                let da = ef.sub(a1, a0);
                let dm = ef.sub(m1, m0);
                // (a0 + da * X)(m0 + dm * X) = a0*m0 + (a0*dm + da*m0)*X + (da*dm)*X^2
                let c0 = ef.mul(a0, m0);
                let c1 = ef.add(ef.mul(a0, dm), ef.mul(da, m0));
                let c2 = ef.mul(da, dm);
                [c0, c1, c2]
            };

            let poly = if half >= 2048 {
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
                    acc[0] = ef.add(acc[0], x[0]);
                    acc[1] = ef.add(acc[1], x[1]);
                    acc[2] = ef.add(acc[2], x[2]);
                }
                acc
            };

            tr.absorb_ext3(&poly[0]);
            tr.absorb_ext3(&poly[1]);
            tr.absorb_ext3(&poly[2]);
            let r_i = tr.squeeze_ext3(ef, 100 + round as u64);
            sumcheck_rounds.push(poly);
            z_challenges.push(r_i);

            if half >= 4096 {
                let next_a: Vec<Ext3> = (0..half)
                    .into_par_iter()
                    .map(|u| {
                        let (x0, x1) = (a_tbl[2 * u], a_tbl[2 * u + 1]);
                        ef.add(x0, ef.mul(r_i, ef.sub(x1, x0)))
                    })
                    .collect();
                let next_m: Vec<Ext3> = (0..half)
                    .into_par_iter()
                    .map(|u| {
                        let (x0, x1) = (m_tbl[2 * u], m_tbl[2 * u + 1]);
                        ef.add(x0, ef.mul(r_i, ef.sub(x1, x0)))
                    })
                    .collect();
                a_tbl = next_a;
                m_tbl = next_m;
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
        let _ = y_batch;

        // 3. Compute ZK-row-blinded `u_eval(X) = sum_{r=0}^{rd-1} eq(z_row)[r] * ext_row[r]` (`len == w`):
        let z_row = &z_challenges[sh.mc..];
        let eq_row = ef.build_eq_le(z_row);
        let u_eval = combine_rows_ext3(fp, &self.ext, sh.w, &eq_row);
        tr.absorb_poly3("U_EVAL", &u_eval);

        // 4. Sample `Ext3` proximity challenge `gamma` and compute `u_prox(X)` (`len == w`):
        //    `u_prox(X) = sum_{r=0}^{rd-1} gamma^r * ext_row[r] + ext_row[rd]*1 + ext_row[rd+1]*u + ext_row[rd+2]*u^2`
        let gamma = tr.squeeze_ext3(ef, 500);
        let mut prox_weights = Vec::with_capacity(sh.r_total);
        let mut g_pw = ef.one();
        for _ in 0..sh.rd {
            prox_weights.push(g_pw);
            g_pw = ef.mul(g_pw, gamma);
        }
        prox_weights.push([1, 0, 0]);
        prox_weights.push([0, 1, 0]);
        prox_weights.push([0, 0, 1]);
        let u_prox = combine_rows_ext3(fp, &self.ext, sh.w, &prox_weights);
        tr.absorb_poly3("U_PROX", &u_prox);

        // 5. Sample `t_cols` distinct columns and build deduplicated salted Merkle multiproof:
        let col_indices = tr.squeeze_distinct_cols(sh.t_cols, sh.npts);
        let opened_cols = if !self.cw.is_empty() {
            col_indices
                .par_iter()
                .map(|&j| self.cw[j * sh.r_total..(j + 1) * sh.r_total].to_vec())
                .collect()
        } else {
            stream_selected_columns(fp, sh, &self.ext, &col_indices)
        };
        let multiproof = prove_multiproof(&self.tree, &self.salts, &col_indices);

        SuccinctPcsOpeningProof {
            sumcheck_rounds,
            u_prox,
            u_eval,
            col_indices,
            opened_cols,
            multiproof,
        }
    }
}

/// Statement inputs for [`verify_slot_claims`].
pub struct SlotClaimsQuery<'a> {
    pub shape: &'a PcsShape,
    pub root: &'a [u8; 32],
    pub log_n: usize,
    pub v_families: &'a [Vec<u64>],
    pub claims: &'a [SlotLinearClaim],
    pub context: &'a [u8; 32],
}

/// Standalone Succinct Verifier for `SuccinctPcsOpeningProof` (`0` access to secret witness!).
pub fn verify_slot_claims(
    fp: &FastPrime61,
    query: &SlotClaimsQuery<'_>,
    proof: &SuccinctPcsOpeningProof,
) -> Result<(), String> {
    let SlotClaimsQuery {
        shape,
        root,
        log_n,
        v_families,
        claims,
        context,
    } = *query;
    let ef = Ext3Field::new(*fp);
    let n_poly = 1usize << log_n;
    if log_n > shape.mc || !shape.c.is_multiple_of(n_poly) {
        return Err("invalid log_n vs shape.mc".into());
    }
    let m_bits = shape.mc + shape.mr;
    if proof.sumcheck_rounds.len() != m_bits
        || proof.u_prox.len() != shape.w
        || proof.u_eval.len() != shape.w
        || proof.col_indices.len() != shape.t_cols
        || proof.opened_cols.len() != shape.t_cols
        || proof.opened_cols.iter().any(|c| c.len() != shape.r_total)
    {
        return Err("PCS opening proof shape mismatch".into());
    }

    let polys_per_row = shape.c / n_poly;
    let usable_slots = shape.usable_rows * polys_per_row;

    let mut tr = PcsTranscript::new("SLOT_OPEN", fp.p, root, context);
    tr.absorb_bytes(&(claims.len() as u64).to_le_bytes());
    for cl in claims {
        tr.absorb_bytes(&cl.rhs.to_le_bytes());
    }

    // 1. Replay `beta` and compute initial sumcheck claim `Y_batch`:
    let beta = tr.squeeze_ext3(&ef, 1);
    let mut running_claim = ef.zero();
    let mut beta_pows = Vec::with_capacity(claims.len());
    let mut b_pw = ef.one();
    for cl in claims {
        running_claim = ef.add(running_claim, ef.scale(b_pw, cl.rhs % fp.p));
        beta_pows.push(b_pw);
        b_pw = ef.mul(b_pw, beta);
    }

    // 2. Verify all `mc + mr` quadratic sumcheck rounds over `Ext3`:
    let mut z_challenges = Vec::with_capacity(m_bits);
    for (round, poly) in proof.sumcheck_rounds.iter().enumerate() {
        let g0 = poly[0];
        let g1 = ef.add(poly[0], ef.add(poly[1], poly[2]));
        if ef.add(g0, g1) != running_claim {
            return Err(format!(
                "PCS sumcheck round {round} failed g(0)+g(1)==claim"
            ));
        }
        tr.absorb_ext3(&poly[0]);
        tr.absorb_ext3(&poly[1]);
        tr.absorb_ext3(&poly[2]);
        let r_i = tr.squeeze_ext3(&ef, 100 + round as u64);
        z_challenges.push(r_i);
        // Horner: poly[0] + r_i * (poly[1] + r_i * poly[2])
        running_claim = ef.add(poly[0], ef.mul(r_i, ef.add(poly[1], ef.mul(r_i, poly[2]))));
    }

    // 3. Evaluate `A~(z_challenges)` directly in `O(|claims| + N + rd*polys_per_row)` (no `rd * c` alloc!)
    //    and verify terminal sumcheck identity `running_claim == A~(z) * M~(z)` where
    //    `M~(z) == <u_eval[0..C], eq_le(z_col)>`:
    let z_j = &z_challenges[..log_n];
    let z_slot = &z_challenges[log_n..]; // (mc - log_n) + mr bits
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

    let z_col = &z_challenges[..shape.mc];
    let eq_col = ef.build_eq_le(z_col);
    let m_eval = proof.u_eval[..shape.c]
        .iter()
        .zip(&eq_col)
        .fold(ef.zero(), |acc, (&u, &eq)| ef.add(acc, ef.mul(u, eq)));

    if running_claim != ef.mul(a_eval, m_eval) {
        return Err("PCS terminal sumcheck check A~(z)*M~(z) == claim failed".into());
    }

    // 4. Replay transcript for `u_eval`, `gamma`, `u_prox`, and `col_indices`:
    tr.absorb_poly3("U_EVAL", &proof.u_eval);
    let gamma = tr.squeeze_ext3(&ef, 500);
    tr.absorb_poly3("U_PROX", &proof.u_prox);
    let expected_cols = tr.squeeze_distinct_cols(shape.t_cols, shape.npts);
    if proof.col_indices != expected_cols {
        return Err("PCS queried column challenge mismatch".into());
    }

    // 5. Verify salted SHA-256 Merkle multiproof against `root`:
    verify_multiproof(
        root,
        shape.npts,
        shape.tree_levels,
        &proof.col_indices,
        &proof.opened_cols,
        &proof.multiproof,
    )?;

    // 6. Verify BOTH `u_prox(x_j)` AND `u_eval(x_j)` against every opened column `j` in `rayon` parallel!
    let z_row = &z_challenges[shape.mc..];
    let eq_row = ef.build_eq_le(z_row);

    let mut prox_weights = Vec::with_capacity(shape.r_total);
    let mut g_pw = ef.one();
    for _ in 0..shape.rd {
        prox_weights.push(g_pw);
        g_pw = ef.mul(g_pw, gamma);
    }
    prox_weights.push([1, 0, 0]);
    prox_weights.push([0, 1, 0]);
    prox_weights.push([0, 0, 1]);

    let col_err = (0..shape.t_cols).into_par_iter().find_map_any(|t_idx| {
        let j = proof.col_indices[t_idx];
        let x_j = shape.domain.point(fp, j);
        let col = &proof.opened_cols[t_idx];

        let lhs_eval = dot_ext3_base(fp, &eq_row, &col[..shape.rd]);
        let rhs_eval = eval_poly_ext3_at_base(fp, &proof.u_eval, x_j);
        if lhs_eval != rhs_eval {
            return Some(format!("PCS u_eval column consistency failed at col {j}"));
        }

        let lhs_prox = dot_ext3_base(fp, &prox_weights, col);
        let rhs_prox = eval_poly_ext3_at_base(fp, &proof.u_prox, x_j);
        if lhs_prox != rhs_prox {
            return Some(format!("PCS u_prox proximity test failed at col {j}"));
        }
        None
    });

    if let Some(e) = col_err {
        return Err(e);
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Low-level Parallel Coset-NTT & Linear Algebra Helpers
// ---------------------------------------------------------------------------------------

#[inline]
fn dot_ext3_base(fp: &FastPrime61, weights: &[Ext3], col: &[u64]) -> Ext3 {
    debug_assert_eq!(weights.len(), col.len());
    let mut acc0 = 0u64;
    let mut acc1 = 0u64;
    let mut acc2 = 0u64;
    for (cw, cc) in weights.chunks(32).zip(col.chunks(32)) {
        let mut s0 = 0u128;
        let mut s1 = 0u128;
        let mut s2 = 0u128;
        for (&w, &v) in cw.iter().zip(cc.iter()) {
            let v128 = v as u128;
            s0 += w[0] as u128 * v128;
            s1 += w[1] as u128 * v128;
            s2 += w[2] as u128 * v128;
        }
        acc0 = fp.add(acc0, fp.red128(s0));
        acc1 = fp.add(acc1, fp.red128(s1));
        acc2 = fp.add(acc2, fp.red128(s2));
    }
    [acc0, acc1, acc2]
}

#[inline]
fn eval_poly_ext3_at_base(fp: &FastPrime61, coeffs: &[Ext3], x: u64) -> Ext3 {
    let mut a0 = 0u64;
    let mut a1 = 0u64;
    let mut a2 = 0u64;
    for c in coeffs.iter().rev() {
        a0 = fp.add(fp.mul(a0, x), c[0]);
        a1 = fp.add(fp.mul(a1, x), c[1]);
        a2 = fp.add(fp.mul(a2, x), c[2]);
    }
    [a0, a1, a2]
}

fn combine_rows_ext3(fp: &FastPrime61, ext: &[u64], w: usize, row_weights: &[Ext3]) -> Vec<Ext3> {
    let r_cnt = row_weights.len();
    let mut out = vec![[0u64; 3]; w];
    out.par_chunks_mut(512).enumerate().for_each(|(blk, dst)| {
        let base_c = blk * 512;
        for (dc, slot) in dst.iter_mut().enumerate() {
            let c = base_c + dc;
            let mut a0 = 0u64;
            let mut a1 = 0u64;
            let mut a2 = 0u64;
            let mut s0 = 0u128;
            let mut s1 = 0u128;
            let mut s2 = 0u128;
            for r in 0..r_cnt {
                let v = ext[r * w + c] as u128;
                let rw = row_weights[r];
                s0 += rw[0] as u128 * v;
                s1 += rw[1] as u128 * v;
                s2 += rw[2] as u128 * v;
                if r & 31 == 31 {
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

fn precompute_coset_tables(
    fp: &FastPrime61,
    dom: &CosetDomain,
    w: usize,
) -> (Vec<u64>, Vec<Vec<u64>>) {
    let n = 1usize << dom.k;
    let mut tw = Vec::with_capacity(n / 2);
    let mut cur = 1u64;
    for _ in 0..(n / 2) {
        tw.push(cur);
        cur = fp.mul(cur, dom.omega);
    }
    let scale: Vec<Vec<u64>> = (0..dom.t)
        .map(|tt| {
            let z_t = fp.pow(dom.z, tt as u64);
            let mut pw = Vec::with_capacity(w);
            let mut c = 1u64;
            for _ in 0..w {
                pw.push(c);
                c = fp.mul(c, z_t);
            }
            pw
        })
        .collect();
    (tw, scale)
}

fn encode_coset_column_major(fp: &FastPrime61, shape: &PcsShape, ext: &[u64]) -> Vec<u64> {
    let dom = &shape.domain;
    let n = 1usize << dom.k;
    let (tw, scale) = precompute_coset_tables(fp, dom, shape.w);
    let (r_total, w, npts) = (shape.r_total, shape.w, shape.npts);

    const B: usize = 64;
    let mut cw = vec![0u64; npts * r_total];
    struct SyncPtr(*mut u64);
    unsafe impl Send for SyncPtr {}
    unsafe impl Sync for SyncPtr {}
    let ptr = SyncPtr(cw.as_mut_ptr());
    let ptr_ref = &ptr;

    (0..r_total.div_ceil(B)).into_par_iter().for_each(|blk| {
        let r0 = blk * B;
        let nb = B.min(r_total - r0);
        let mut rows_buf = vec![0u64; nb * npts];
        let mut buf = vec![0u64; n];
        for (dr, dst) in rows_buf.chunks_mut(npts).enumerate() {
            let row = &ext[(r0 + dr) * w..(r0 + dr + 1) * w];
            for (tt, sc) in scale.iter().enumerate() {
                buf.fill(0);
                for (c, (&a, &f)) in row.iter().zip(sc).enumerate() {
                    let slot = &mut buf[c & (n - 1)];
                    *slot = fp.add(*slot, fp.mul(a, f));
                }
                radix2_ntt_natural(fp, &mut buf, &tw);
                let lo = tt * n;
                if lo < npts {
                    let hi = (lo + n).min(npts);
                    dst[lo..hi].copy_from_slice(&buf[..hi - lo]);
                }
            }
        }
        for j in 0..npts {
            for dr in 0..nb {
                // SAFETY: each `blk` writes exclusively to row indices `r0..r0+nb` across all columns `j`.
                unsafe {
                    *ptr_ref.0.add(j * r_total + r0 + dr) = rows_buf[dr * npts + j];
                }
            }
        }
    });
    cw
}

fn encode_rows_chunk(
    fp: &FastPrime61,
    shape: &PcsShape,
    ext: &[u64],
    r0: usize,
    nb: usize,
    tw: &[u64],
    scale: &[Vec<u64>],
) -> Vec<u64> {
    let n = 1usize << shape.domain.k;
    let (w, npts) = (shape.w, shape.npts);
    let mut rows = vec![0u64; nb * npts];
    rows.par_chunks_mut(npts).enumerate().for_each(|(dr, dst)| {
        let row = &ext[(r0 + dr) * w..(r0 + dr + 1) * w];
        let mut buf = vec![0u64; n];
        for (tt, sc) in scale.iter().enumerate() {
            buf.fill(0);
            for (c, (&a, &f)) in row.iter().zip(sc).enumerate() {
                let slot = &mut buf[c & (n - 1)];
                *slot = fp.add(*slot, fp.mul(a, f));
            }
            radix2_ntt_natural(fp, &mut buf, tw);
            let lo = tt * n;
            if lo < npts {
                let hi = (lo + n).min(npts);
                dst[lo..hi].copy_from_slice(&buf[..hi - lo]);
            }
        }
    });
    rows
}

fn stream_coset_leaves(
    fp: &FastPrime61,
    shape: &PcsShape,
    ext: &[u64],
    salts: &[[u8; 32]],
) -> Vec<[u8; 32]> {
    let (r_total, npts) = (shape.r_total, shape.npts);
    let (tw, scale) = precompute_coset_tables(fp, &shape.domain, shape.w);
    let blk_rows = ((256usize << 20) / (8 * npts)).max(1);

    let mut hashers: Vec<Sha256> = (0..npts)
        .map(|j| {
            let mut h = Sha256::new();
            h.update(b"DARKVFHE_PCS_LEAF_V1|");
            h.update((j as u32).to_le_bytes());
            h.update(salts[j]);
            h
        })
        .collect();

    for r0 in (0..r_total).step_by(blk_rows) {
        let nb = blk_rows.min(r_total - r0);
        let rows = encode_rows_chunk(fp, shape, ext, r0, nb, &tw, &scale);
        hashers.par_iter_mut().enumerate().for_each(|(j, h)| {
            for dr in 0..nb {
                h.update(rows[dr * npts + j].to_le_bytes());
            }
        });
    }
    hashers
        .into_par_iter()
        .map(|h| h.finalize().into())
        .collect()
}

fn stream_selected_columns(
    fp: &FastPrime61,
    shape: &PcsShape,
    ext: &[u64],
    js: &[usize],
) -> Vec<Vec<u64>> {
    let (r_total, npts) = (shape.r_total, shape.npts);
    let (tw, scale) = precompute_coset_tables(fp, &shape.domain, shape.w);
    let blk_rows = ((256usize << 20) / (8 * npts)).max(1);
    let mut cols = vec![Vec::with_capacity(r_total); js.len()];
    for r0 in (0..r_total).step_by(blk_rows) {
        let nb = blk_rows.min(r_total - r0);
        let rows = encode_rows_chunk(fp, shape, ext, r0, nb, &tw, &scale);
        cols.par_iter_mut().zip(js.par_iter()).for_each(|(c, &j)| {
            for dr in 0..nb {
                c.push(rows[dr * npts + j]);
            }
        });
    }
    cols
}

// ---------------------------------------------------------------------------------------
// Compact Untrusted-Input Binary Deserializer (`ByteReader`)
// ---------------------------------------------------------------------------------------

pub struct ByteReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> ByteReader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        ByteReader { data, pos: 0 }
    }

    pub fn is_eof(&self) -> bool {
        self.pos == self.data.len()
    }

    pub fn take(&mut self, len: usize) -> Result<&'a [u8], String> {
        if self.pos + len > self.data.len() {
            return Err("unexpected EOF while decoding proof bundle".into());
        }
        let s = &self.data[self.pos..self.pos + len];
        self.pos += len;
        Ok(s)
    }

    pub fn read_u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    pub fn read_u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    pub fn read_u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    pub fn read_fp(&mut self, p: u64) -> Result<u64, String> {
        let v = self.read_u64()?;
        if v >= p {
            return Err(format!("non-canonical field element {v} >= {p}"));
        }
        Ok(v)
    }

    pub fn read_ext3(&mut self, p: u64) -> Result<Ext3, String> {
        Ok([self.read_fp(p)?, self.read_fp(p)?, self.read_fp(p)?])
    }

    pub fn read_hash(&mut self) -> Result<[u8; 32], String> {
        Ok(self.take(32)?.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HoistedParams;

    #[test]
    fn ext3_irreducibility_and_inverses_across_all_primes() {
        for &n in &[64usize, 128, 8192] {
            let params = HoistedParams::for_ring(n);
            for l in 0..8 {
                let ef = Ext3Field::new(params.fp[l]);
                let a: Ext3 = [1234567, 89101112, 13141516];
                let b: Ext3 = [9999991, 7777773, 5555551];
                let inv_a = ef.inv(a);
                assert_eq!(ef.mul(a, inv_a), ef.one());
                // Distributivity:
                let c: Ext3 = [42, 43, 44];
                assert_eq!(ef.mul(a, ef.add(b, c)), ef.add(ef.mul(a, b), ef.mul(a, c)));
            }
            let ef_t = Ext3Field::new(params.fp_t);
            let x: Ext3 = [7, 11, 13];
            assert_eq!(ef_t.mul(x, ef_t.inv(x)), ef_t.one());
        }
    }

    #[test]
    fn succinct_pcs_commit_open_verify_roundtrip_and_falsifiers() {
        let params = HoistedParams::for_ring(64);
        let fp = params.fp[0];
        let log_n = 6usize;
        let n = 1usize << log_n; // 64
        let num_polys = 20usize;
        let data: Vec<u64> = (0..num_polys * n)
            .map(|i| ((i * 1337 + 19) as u64) % fp.p)
            .collect();

        let pcs = CommittedMatrixPcs::commit_with_rng(
            fp,
            &data,
            log_n,
            T_COLS_128,
            DEFAULT_BLOWUP,
            PcsRng::from_seed([7u8; 32]),
        );
        let (ud_bits, lig_bits, alg_bits) = pcs.shape.soundness_bits();
        assert!(ud_bits >= 200.0 && lig_bits >= 128.0 && alg_bits >= 160.0);

        let v0: Vec<u64> = (0..n).map(|j| ((j * 7 + 3) as u64) % fp.p).collect();
        let v1: Vec<u64> = (0..n).map(|j| fp.pow(5, j as u64)).collect();
        let v_fams = vec![v0.clone(), v1.clone()];

        let dot_slot =
            |slot: usize, vf: &[u64]| -> u64 { fp.dot(&data[slot * n..(slot + 1) * n], vf) };
        let rhs0 = fp.add(fp.mul(3, dot_slot(0, &v0)), fp.mul(11, dot_slot(5, &v0)));
        let rhs1 = dot_slot(19, &v1);

        let claims = vec![
            SlotLinearClaim::single_vec(0, vec![(0, 3), (5, 11)], rhs0),
            SlotLinearClaim::single_vec(1, vec![(19, 1)], rhs1),
        ];
        let ctx = [0xABu8; 32];
        let prf = pcs.open_slot_claims(log_n, &v_fams, &claims, &ctx);

        let mut bytes = Vec::new();
        prf.to_bytes(&mut bytes);
        let mut rdr = ByteReader::new(&bytes);
        let decoded = SuccinctPcsOpeningProof::from_bytes(&mut rdr, fp.p).expect("decode proof");
        assert!(rdr.is_eof());

        verify_slot_claims(
            &fp,
            &SlotClaimsQuery {
                shape: &pcs.shape,
                root: &pcs.root,
                log_n,
                v_families: &v_fams,
                claims: &claims,
                context: &ctx,
            },
            &decoded,
        )
        .expect("honest PCS proof must verify");

        // Falsifier 1: Mutate claimed evaluation by +1
        let mut bad_claims = claims.clone();
        bad_claims[1].rhs = fp.add(bad_claims[1].rhs, 1);
        assert!(verify_slot_claims(
            &fp,
            &SlotClaimsQuery {
                shape: &pcs.shape,
                root: &pcs.root,
                log_n,
                v_families: &v_fams,
                claims: &bad_claims,
                context: &ctx,
            },
            &decoded,
        )
        .is_err());

        // Falsifier 2: Forge 1 cell in opened column
        let mut bad_col = decoded.clone();
        bad_col.opened_cols[0][0] = fp.add(bad_col.opened_cols[0][0], 1);
        assert!(verify_slot_claims(
            &fp,
            &SlotClaimsQuery {
                shape: &pcs.shape,
                root: &pcs.root,
                log_n,
                v_families: &v_fams,
                claims: &claims,
                context: &ctx,
            },
            &bad_col,
        )
        .is_err());

        // Falsifier 3: Forge 1 Merkle sibling hash
        let mut bad_mp = decoded.clone();
        bad_mp.multiproof.siblings[0][0] ^= 1;
        assert!(verify_slot_claims(
            &fp,
            &SlotClaimsQuery {
                shape: &pcs.shape,
                root: &pcs.root,
                log_n,
                v_families: &v_fams,
                claims: &claims,
                context: &ctx,
            },
            &bad_mp,
        )
        .is_err());
    }
}
