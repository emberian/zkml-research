//! `BabyBear` (`p = 2013265921 = 15·2^27 + 1`), quartic extension `Ext4 = F_p[X]/(X^4 - 11)`
//! (`Minidregg.Selvage.BabyBearExt4`, 123.7-bit challenge space), `cSHAKE256` XOF/hash/Merkle
//! primitives, and domain-separated `CShakeTranscript` Fiat–Shamir challenger.

use serde::{Deserialize, Serialize};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake256, CShake256Core};
use std::fs::File;

/// BabyBear prime `p = 15 * 2^27 + 1 = 2013265921` (`two_adicity = 27`).
pub const P: u64 = 2013265921;
pub const P_U32: u32 = 2013265921;
/// Primitive multiplicative generator `g = 31` of `F_p^*`.
pub const G_PRIM: u32 = 31;
/// `2^{-1} mod p = (p + 1) / 2`.
pub const INV2_BB: u32 = 1006632961;
/// Non-residue `W = 11` for irreducible quartic `X^4 - 11` (`BabyBearExt4.lean`).
pub const W_EXT4: u32 = 11;

#[inline(always)]
pub fn badd(a: u32, b: u32) -> u32 {
    let s = (a as u64) + (b as u64);
    if s >= P {
        (s - P) as u32
    } else {
        s as u32
    }
}

#[inline(always)]
pub fn bsub(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b
    } else {
        (P_U32 - b) + a
    }
}

#[inline(always)]
pub fn bneg(a: u32) -> u32 {
    if a == 0 {
        0
    } else {
        P_U32 - a
    }
}

#[inline(always)]
pub fn bmul(a: u32, b: u32) -> u32 {
    (((a as u64) * (b as u64)) % P) as u32
}

#[inline]
pub fn bpow(mut base: u32, mut exp: u64) -> u32 {
    let mut acc = 1u32;
    base = ((base as u64) % P) as u32;
    while exp > 0 {
        if (exp & 1) != 0 {
            acc = bmul(acc, base);
        }
        base = bmul(base, base);
        exp >>= 1;
    }
    acc
}

/// BabyBear multiplicative inverse (`None` iff `a % P == 0`).
#[inline]
pub fn binv(a: u32) -> Option<u32> {
    let c = ((a as u64) % P) as u32;
    if c == 0 {
        None
    } else {
        Some(bpow(c, P - 2))
    }
}

/// Canonical projection of signed 64-bit integer into `[0, P)`.
#[inline(always)]
pub fn bb_from_i64(v: i64) -> u32 {
    let r = v.rem_euclid(P as i64);
    r as u32
}

/// Principal `n`-th root of unity in BabyBear (`n` a power of two `<= 2^27`).
pub fn root_of_unity_bb(n: usize) -> u32 {
    assert!(n.is_power_of_two());
    let lg = n.trailing_zeros();
    assert!(lg <= 27, "BabyBear two-adicity is 27, got log2(n)={lg}");
    bpow(G_PRIM, (P - 1) >> lg)
}

/// Element `c_0 + c_1 X + c_2 X^2 + c_3 X^3` in `BabyBear[X] / (X^4 - 11)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Ext4(pub [u32; 4]);

impl Ext4 {
    pub const ZERO: Self = Self([0, 0, 0, 0]);
    pub const ONE: Self = Self([1, 0, 0, 0]);

    #[inline(always)]
    pub const fn from_bb(x: u32) -> Self {
        Self([x, 0, 0, 0])
    }

    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.0 == [0, 0, 0, 0]
    }

    #[inline(always)]
    pub fn is_canonical(&self) -> bool {
        self.0[0] < P_U32 && self.0[1] < P_U32 && self.0[2] < P_U32 && self.0[3] < P_U32
    }

    #[inline(always)]
    pub fn add(self, rhs: Self) -> Self {
        Self([
            badd(self.0[0], rhs.0[0]),
            badd(self.0[1], rhs.0[1]),
            badd(self.0[2], rhs.0[2]),
            badd(self.0[3], rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub fn sub(self, rhs: Self) -> Self {
        Self([
            bsub(self.0[0], rhs.0[0]),
            bsub(self.0[1], rhs.0[1]),
            bsub(self.0[2], rhs.0[2]),
            bsub(self.0[3], rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub fn neg(self) -> Self {
        Self([
            bneg(self.0[0]),
            bneg(self.0[1]),
            bneg(self.0[2]),
            bneg(self.0[3]),
        ])
    }

    /// Basefield scalar times `Ext4` (`4` BabyBear multiplications).
    #[inline(always)]
    pub fn scale_bb(self, c: u32) -> Self {
        Self([
            bmul(self.0[0], c),
            bmul(self.0[1], c),
            bmul(self.0[2], c),
            bmul(self.0[3], c),
        ])
    }

    /// Quadratic-over-quadratic Karatsuba multiplication (`9` BabyBear multiplications):
    /// `K_2 = F_p[u]/(u^2 - 11)`, `Ext4 = K_2[X]/(X^2 - u)` with `A_0 = (a0, a2), A_1 = (a1, a3)`.
    #[inline]
    pub fn mul(self, rhs: Self) -> Self {
        #[inline(always)]
        fn k2_mul(x: [u32; 2], y: [u32; 2]) -> [u32; 2] {
            let m0 = bmul(x[0], y[0]);
            let m1 = bmul(x[1], y[1]);
            let m2 = bmul(badd(x[0], x[1]), badd(y[0], y[1]));
            let c0 = badd(m0, bmul(W_EXT4, m1));
            let c1 = bsub(m2, badd(m0, m1));
            [c0, c1]
        }

        let a0 = [self.0[0], self.0[2]];
        let a1 = [self.0[1], self.0[3]];
        let b0 = [rhs.0[0], rhs.0[2]];
        let b1 = [rhs.0[1], rhs.0[3]];

        let p0 = k2_mul(a0, b0);
        let p1 = k2_mul(a1, b1);
        let a_sum = [badd(a0[0], a1[0]), badd(a0[1], a1[1])];
        let b_sum = [badd(b0[0], b1[0]), badd(b0[1], b1[1])];
        let p_sum = k2_mul(a_sum, b_sum);
        let odd = [
            bsub(p_sum[0], badd(p0[0], p1[0])),
            bsub(p_sum[1], badd(p0[1], p1[1])),
        ];
        // `u * p1 = (11 * p1[1], p1[0])`
        let even = [badd(p0[0], bmul(W_EXT4, p1[1])), badd(p0[1], p1[0])];
        Self([even[0], odd[0], even[1], odd[1]])
    }

    #[inline]
    pub fn sq(self) -> Self {
        self.mul(self)
    }

    ///Kum-norm tower inversion in `F_p[X]/(X^4 - 11)` using **1 single BabyBear inversion**.
    /// Note: all provers in `qwen35audit` use **zero** inversions; only verifiers call `inv()`.
    pub fn inv(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let a0 = [self.0[0], self.0[2]];
        let a1 = [self.0[1], self.0[3]];

        // In K_2: sq(x0 + x1 u) = (x0^2 + 11 x1^2) + 2 x0 x1 u
        let a0_sq = [
            badd(bmul(a0[0], a0[0]), bmul(W_EXT4, bmul(a0[1], a0[1]))),
            bmul(2, bmul(a0[0], a0[1])),
        ];
        let a1_sq = [
            badd(bmul(a1[0], a1[0]), bmul(W_EXT4, bmul(a1[1], a1[1]))),
            bmul(2, bmul(a1[0], a1[1])),
        ];
        // N = A_0^2 - u * A_1^2 where u * A_1^2 = (11 * a1_sq[1], a1_sq[0])
        let n0 = bsub(a0_sq[0], bmul(W_EXT4, a1_sq[1]));
        let n1 = bsub(a0_sq[1], a1_sq[0]);

        // Norm to F_p: n_bb = n0^2 - 11 * n1^2
        let n_bb = bsub(bmul(n0, n0), bmul(W_EXT4, bmul(n1, n1)));
        let inv_n_bb = binv(n_bb)?;
        let n_inv = [bmul(n0, inv_n_bb), bmul(bneg(n1), inv_n_bb)];

        // (A_0 - A_1 X) * N^{-1}
        let even = [
            badd(bmul(a0[0], n_inv[0]), bmul(W_EXT4, bmul(a0[1], n_inv[1]))),
            badd(bmul(a0[0], n_inv[1]), bmul(a0[1], n_inv[0])),
        ];
        let odd = [
            bneg(badd(
                bmul(a1[0], n_inv[0]),
                bmul(W_EXT4, bmul(a1[1], n_inv[1])),
            )),
            bneg(badd(bmul(a1[0], n_inv[1]), bmul(a1[1], n_inv[0]))),
        ];
        Some(Self([even[0], odd[0], even[1], odd[1]]))
    }

    #[inline(always)]
    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        for i in 0..4 {
            out[4 * i..4 * (i + 1)].copy_from_slice(&self.0[i].to_le_bytes());
        }
        out
    }

    #[inline]
    pub fn from_bytes(bytes: &[u8; 16]) -> Result<Self, String> {
        let mut c = [0u32; 4];
        for i in 0..4 {
            let v = u32::from_le_bytes(bytes[4 * i..4 * (i + 1)].try_into().unwrap());
            if v >= P_U32 {
                return Err(format!("non-canonical Ext4 limb {v} >= {P_U32}"));
            }
            c[i] = v;
        }
        Ok(Self(c))
    }
}

// ===========================================================================
// Radix-2 NTT & INTT over BabyBear (`u32`) and `Ext4` (`scale_bb` twiddles!)
// ===========================================================================

/// Precompute forward twiddles `[1, omega, omega^2, ..., omega^{n/2 - 1}]` for power-of-two `n`.
pub fn precompute_twiddles_bb(n: usize, inverse: bool) -> Vec<u32> {
    assert!(n.is_power_of_two());
    if n <= 1 {
        return Vec::new();
    }
    let omega = root_of_unity_bb(n);
    let root = if inverse { binv(omega).unwrap() } else { omega };
    let half = n / 2;
    let mut tw = Vec::with_capacity(half);
    let mut cur = 1u32;
    for _ in 0..half {
        tw.push(cur);
        cur = bmul(cur, root);
    }
    tw
}

/// In-place radix-2 BabyBear NTT (`tw` from `precompute_twiddles_bb(n, false)`).
pub fn ntt_bb_in_place(a: &mut [u32], tw: &[u32]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = i.reverse_bits() >> (usize::BITS - lg);
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            for j in 0..half {
                let u = a[st + j];
                let v = bmul(a[st + j + half], tw[j * step]);
                a[st + j] = badd(u, v);
                a[st + j + half] = bsub(u, v);
            }
        }
        len <<= 1;
    }
}

/// In-place radix-2 BabyBear INTT (`inv_tw` from `precompute_twiddles_bb(n, true)`).
pub fn intt_bb_in_place(a: &mut [u32], inv_tw: &[u32]) {
    ntt_bb_in_place(a, inv_tw);
    let n_inv = binv(a.len() as u32).unwrap();
    for x in a.iter_mut() {
        *x = bmul(*x, n_inv);
    }
}

/// In-place radix-2 `Ext4` NTT using basefield `u32` twiddles (`4` base muls per butterfly!).
pub fn ntt_ext4_in_place(a: &mut [Ext4], tw: &[u32]) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = i.reverse_bits() >> (usize::BITS - lg);
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            for j in 0..half {
                let u = a[st + j];
                let v = a[st + j + half].scale_bb(tw[j * step]);
                a[st + j] = u.add(v);
                a[st + j + half] = u.sub(v);
            }
        }
        len <<= 1;
    }
}

// ===========================================================================
// Multilinear `eq`, Folding, & Univariate Quotient Helpers over `Ext4`
// ===========================================================================

#[inline]
pub fn eq_lin_ext4(r: Ext4, x: Ext4) -> Ext4 {
    let one_m_r = Ext4::ONE.sub(r);
    let one_m_x = Ext4::ONE.sub(x);
    one_m_r.mul(one_m_x).add(r.mul(x))
}

pub fn eq_mle_ext4(z: &[Ext4], x: &[Ext4]) -> Ext4 {
    assert_eq!(z.len(), x.len());
    z.iter()
        .zip(x.iter())
        .fold(Ext4::ONE, |acc, (&zj, &xj)| acc.mul(eq_lin_ext4(zj, xj)))
}

/// Build LSB-first `eq(r, ·)` hypercube table of length `2^k` in `max(0, 2^k - 1)` `Ext4` muls.
pub fn build_eq_table_lsb_ext4(r: &[Ext4]) -> Vec<Ext4> {
    let k = r.len();
    if k == 0 {
        return vec![Ext4::ONE];
    }
    let mut tbl = Vec::with_capacity(1usize << k);
    tbl.push(Ext4::ONE.sub(r[0]));
    tbl.push(r[0]);
    for &ri in &r[1..] {
        let cur_len = tbl.len();
        for idx in 0..cur_len {
            let base = tbl[idx];
            let hi = base.mul(ri);
            let lo = base.sub(hi);
            tbl[idx] = lo;
            tbl.push(hi);
        }
    }
    tbl
}

/// Build MSB-to-LSB suffix equality tables for LSB-first Gruen `F_{>=2}` elimination (`2025/1117` §5.1).
pub fn build_eq_suffix_tables_ext4(z_s: &[Ext4]) -> Vec<Vec<Ext4>> {
    let ell = z_s.len();
    if ell == 0 {
        return Vec::new();
    }
    let mut suf = Vec::with_capacity(ell);
    suf.push(vec![Ext4::ONE]);
    if ell >= 2 {
        let z_last = z_s[ell - 1];
        suf.push(vec![Ext4::ONE.sub(z_last), z_last]);
        for m in 2..ell {
            let prev = &suf[m - 1];
            let z_cur = z_s[ell - m];
            let mut next = Vec::with_capacity(1usize << m);
            for &v in prev.iter() {
                let hi = v.mul(z_cur);
                let lo = v.sub(hi);
                next.push(lo);
                next.push(hi);
            }
            suf.push(next);
        }
    }
    suf
}

/// Evaluate `q(x) = q0 + (q1 - q0 - q_inf)·x + q_inf·x^2` over `Ext4`.
#[inline]
pub fn eval_quad_zero_one_inf_ext4(q0: Ext4, q1: Ext4, q_inf: Ext4, x: Ext4) -> Ext4 {
    let c1 = q1.sub(q0).sub(q_inf);
    let x2 = x.sq();
    q0.add(c1.mul(x)).add(q_inf.mul(x2))
}

/// Evaluate degree-`<= 3` polynomial reconstructed from `{p(0), p(1), p(2), p(∞)}` at `x ∈ Ext4` (`0` inversions!).
#[inline]
pub fn eval_cubic_zero_one_two_inf_ext4(
    p0: Ext4,
    p1: Ext4,
    p2: Ext4,
    p_inf: Ext4,
    x: Ext4,
) -> Ext4 {
    let six_c3 = p_inf.scale_bb(6);
    let two_p1 = p1.add(p1);
    let two_c2 = p2.sub(two_p1).add(p0).sub(six_c3);
    let c2 = two_c2.scale_bb(INV2_BB);
    let c1 = p1.sub(p0).sub(c2).sub(p_inf);
    let x2 = x.sq();
    let x3 = x2.mul(x);
    p0.add(c1.mul(x)).add(c2.mul(x2)).add(p_inf.mul(x3))
}

/// Fold a basefield `Bb` table by its first `Ext4` challenge (`4` base muls per pair!).
pub fn fold_bb_to_ext4(f: &[u32], r: Ext4) -> Vec<Ext4> {
    assert!(f.len() >= 2 && f.len().is_power_of_two());
    f.chunks_exact(2)
        .map(|pair| {
            let diff = bsub(pair[1], pair[0]);
            Ext4::from_bb(pair[0]).add(r.scale_bb(diff))
        })
        .collect()
}

/// Fold an `Ext4` table along LSB stride 1 by challenge `r`.
pub fn fold_ext4(f: &[Ext4], r: Ext4) -> Vec<Ext4> {
    assert!(f.len() >= 2 && f.len().is_power_of_two());
    f.chunks_exact(2)
        .map(|pair| pair[0].add(r.mul(pair[1].sub(pair[0]))))
        .collect()
}

/// Evaluate the multilinear extension of a basefield `Bb` table (`length = 2^m`) at `pt ∈ Ext4^m` (LSB-first).
pub fn mle_eval_bb_at_ext4(tab: &[u32], pt: &[Ext4]) -> Ext4 {
    assert_eq!(tab.len(), 1usize << pt.len());
    if pt.is_empty() {
        return Ext4::from_bb(tab[0] % P_U32);
    }
    let eq = build_eq_table_lsb_ext4(pt);
    let mut acc = [0u128; 4];
    for (i, (&v, &w)) in tab.iter().zip(eq.iter()).enumerate() {
        let vv = v as u128;
        acc[0] += vv * (w.0[0] as u128);
        acc[1] += vv * (w.0[1] as u128);
        acc[2] += vv * (w.0[2] as u128);
        acc[3] += vv * (w.0[3] as u128);
        if (i & 15) == 15 {
            acc[0] %= P as u128;
            acc[1] %= P as u128;
            acc[2] %= P as u128;
            acc[3] %= P as u128;
        }
    }
    Ext4([
        (acc[0] % (P as u128)) as u32,
        (acc[1] % (P as u128)) as u32,
        (acc[2] % (P as u128)) as u32,
        (acc[3] % (P as u128)) as u32,
    ])
}

// ===========================================================================
// NIST SP 800-185 `cSHAKE256` Hash, XOF CSPRNG, Merkle Paths, & Transcript
// ===========================================================================

/// Compute 32-byte NIST SP 800-185 `cSHAKE256(data, 256, "", customization)`.
#[inline]
pub fn cshake256_32(customization: &[u8], data: &[u8]) -> [u8; 32] {
    let mut h = CShake256::from_core(CShake256Core::new(customization));
    h.update(data);
    let mut reader = h.finalize_xof();
    let mut out = [0u8; 32];
    XofReader::read(&mut reader, &mut out);
    out
}

/// Expand `seed` into arbitrary-length XOF output via `cSHAKE256`.
pub fn cshake256_xof(customization: &[u8], seed: &[u8], out: &mut [u8]) {
    let mut h = CShake256::from_core(CShake256Core::new(customization));
    h.update(seed);
    let mut reader = h.finalize_xof();
    XofReader::read(&mut reader, out);
}

/// Read 32 bytes of OS entropy from `/dev/urandom` for ZK masking randomness.
pub fn os_random_seed_32() -> [u8; 32] {
    let mut f = File::open("/dev/urandom").expect("failed to open /dev/urandom");
    let mut seed = [0u8; 32];
    std::io::Read::read_exact(&mut f, &mut seed)
        .expect("failed reading 32 bytes from /dev/urandom");
    seed
}

/// Deterministic/OS-seeded `cSHAKE256` XOF stream for sampling unbiased BabyBear elements & salts.
pub struct CShakeRng {
    reader: sha3::CShake256Reader,
}

impl CShakeRng {
    pub fn from_seed(customization: &[u8], seed: &[u8]) -> Self {
        let mut h = CShake256::from_core(CShake256Core::new(customization));
        h.update(seed);
        Self {
            reader: h.finalize_xof(),
        }
    }

    pub fn fill_bytes(&mut self, dst: &mut [u8]) {
        XofReader::read(&mut self.reader, dst);
    }

    /// Rejection-sample a uniform element in `[0, P)` (`< 2^{-31}` bias = `0`, exact uniform!).
    pub fn next_bb(&mut self) -> u32 {
        let mut buf = [0u8; 4];
        loop {
            XofReader::read(&mut self.reader, &mut buf);
            let cand = u32::from_le_bytes(buf) & 0x7FFF_FFFF;
            if cand < P_U32 {
                return cand;
            }
        }
    }
}

/// Single-leaf `cSHAKE256` Merkle authentication path (used for opening 1 of 24 layer weight roots).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleSinglePath {
    pub index: usize,
    pub leaf: [u8; 32],
    pub siblings: Vec<[u8; 32]>,
}

pub fn merkle_node_cshake(domain: &[u8], level: u8, idx: u32, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 1 + 4 + 64];
    buf[0] = level;
    buf[1..5].copy_from_slice(&idx.to_le_bytes());
    buf[5..37].copy_from_slice(left);
    buf[37..69].copy_from_slice(right);
    cshake256_32(domain, &buf)
}

pub fn merkle_root_cshake(domain: &[u8], leaves: &[[u8; 32]]) -> [u8; 32] {
    assert!(!leaves.is_empty() && leaves.len().is_power_of_two());
    let mut cur = leaves.to_vec();
    let mut level = 0u8;
    while cur.len() > 1 {
        let mut next = Vec::with_capacity(cur.len() / 2);
        for (idx, pair) in cur.chunks_exact(2).enumerate() {
            next.push(merkle_node_cshake(domain, level, idx as u32, &pair[0], &pair[1]));
        }
        cur = next;
        level += 1;
    }
    cur[0]
}

pub fn merkle_open_single_cshake(domain: &[u8], leaves: &[[u8; 32]], index: usize) -> MerkleSinglePath {
    assert!(!leaves.is_empty() && leaves.len().is_power_of_two() && index < leaves.len());
    let leaf = leaves[index];
    let mut cur = leaves.to_vec();
    let mut idx = index;
    let mut level = 0u8;
    let mut siblings = Vec::new();
    while cur.len() > 1 {
        siblings.push(cur[idx ^ 1]);
        let mut next = Vec::with_capacity(cur.len() / 2);
        for (p_idx, pair) in cur.chunks_exact(2).enumerate() {
            next.push(merkle_node_cshake(domain, level, p_idx as u32, &pair[0], &pair[1]));
        }
        cur = next;
        idx >>= 1;
        level += 1;
    }
    MerkleSinglePath {
        index,
        leaf,
        siblings,
    }
}

impl MerkleSinglePath {
    pub fn verify(&self, domain: &[u8], expected_root: &[u8; 32], num_leaves: usize) -> bool {
        if !num_leaves.is_power_of_two()
            || self.index >= num_leaves
            || (1usize << self.siblings.len()) != num_leaves
        {
            return false;
        }
        let mut cur = self.leaf;
        let mut idx = self.index;
        for (level, sib) in self.siblings.iter().enumerate() {
            let p_idx = (idx >> 1) as u32;
            cur = if (idx & 1) == 0 {
                merkle_node_cshake(domain, level as u8, p_idx, &cur, sib)
            } else {
                merkle_node_cshake(domain, level as u8, p_idx, sib, &cur)
            };
            idx >>= 1;
        }
        &cur == expected_root
    }
}

/// Domain-separated `cSHAKE256` Fiat–Shamir transcript (`0` shared prover/verifier state).
#[derive(Clone, Debug)]
pub struct CShakeTranscript {
    state: [u8; 32],
    squeeze_ctr: u64,
}

impl CShakeTranscript {
    pub fn new(protocol_label: &[u8]) -> Self {
        Self {
            state: cshake256_32(b"QW35-FS-INIT-V1", protocol_label),
            squeeze_ctr: 0,
        }
    }

    pub fn absorb_bytes(&mut self, label: &[u8], payload: &[u8]) {
        let mut h = CShake256::from_core(CShake256Core::new(b"QW35-FS-ABSORB-V1"));
        h.update(&self.state);
        h.update(&(label.len() as u32).to_le_bytes());
        h.update(label);
        h.update(&(payload.len() as u64).to_le_bytes());
        h.update(payload);
        let mut reader = h.finalize_xof();
        XofReader::read(&mut reader, &mut self.state);
        self.squeeze_ctr = 0;
    }

    #[inline]
    pub fn absorb_u32(&mut self, label: &[u8], v: u32) {
        self.absorb_bytes(label, &v.to_le_bytes());
    }

    #[inline]
    pub fn absorb_root(&mut self, label: &[u8], root: &[u8; 32]) {
        self.absorb_bytes(label, root);
    }

    #[inline]
    pub fn absorb_ext4(&mut self, label: &[u8], x: Ext4) {
        self.absorb_bytes(label, &x.to_bytes());
    }

    pub fn absorb_ext4_slice(&mut self, label: &[u8], xs: &[Ext4]) {
        let mut buf = Vec::with_capacity(xs.len() * 16);
        for &x in xs {
            buf.extend_from_slice(&x.to_bytes());
        }
        self.absorb_bytes(label, &buf);
    }

    fn xof_reader(&mut self, label: &[u8]) -> sha3::CShake256Reader {
        let mut h = CShake256::from_core(CShake256Core::new(b"QW35-FS-SQUEEZE-V1"));
        h.update(&self.state);
        h.update(&self.squeeze_ctr.to_le_bytes());
        h.update(&(label.len() as u32).to_le_bytes());
        h.update(label);
        self.squeeze_ctr += 1;
        h.finalize_xof()
    }

    /// Squeeze an unbiased BabyBear element in `[0, P)`.
    pub fn squeeze_bb(&mut self, label: &[u8]) -> u32 {
        let mut reader = self.xof_reader(label);
        let mut buf = [0u8; 4];
        loop {
            XofReader::read(&mut reader, &mut buf);
            let cand = u32::from_le_bytes(buf) & 0x7FFF_FFFF;
            if cand < P_U32 {
                return cand;
            }
        }
    }

    /// Squeeze a 123.7-bit challenge in `Ext4` (`nonzero = true` rejects `0`).
    pub fn squeeze_ext4(&mut self, label: &[u8], nonzero: bool) -> Ext4 {
        let mut reader = self.xof_reader(label);
        let mut buf = [0u8; 4];
        loop {
            let mut limbs = [0u32; 4];
            for item in &mut limbs {
                loop {
                    XofReader::read(&mut reader, &mut buf);
                    let cand = u32::from_le_bytes(buf) & 0x7FFF_FFFF;
                    if cand < P_U32 {
                        *item = cand;
                        break;
                    }
                }
            }
            let elem = Ext4(limbs);
            if !nonzero || !elem.is_zero() {
                return elem;
            }
        }
    }

    pub fn squeeze_ext4_vec(&mut self, label: &[u8], len: usize, nonzero: bool) -> Vec<Ext4> {
        (0..len)
            .map(|i| {
                let mut l = Vec::with_capacity(label.len() + 8);
                l.extend_from_slice(label);
                l.extend_from_slice(&(i as u32).to_le_bytes());
                self.squeeze_ext4(&l, nonzero)
            })
            .collect()
    }

    /// Squeeze `count` distinct sorted indices in `[0, domain_size)` (`domain_size` a power of two).
    pub fn squeeze_distinct_indices(&mut self, label: &[u8], domain_size: usize, count: usize) -> Vec<usize> {
        assert!(domain_size.is_power_of_two() && count <= domain_size);
        let mask = domain_size - 1;
        let mut reader = self.xof_reader(label);
        let mut chosen = Vec::with_capacity(count);
        let mut seen = vec![false; domain_size];
        let mut buf = [0u8; 4];
        while chosen.len() < count {
            XofReader::read(&mut reader, &mut buf);
            let idx = (u32::from_le_bytes(buf) as usize) & mask;
            if !seen[idx] {
                seen[idx] = true;
                chosen.push(idx);
            }
        }
        chosen.sort_unstable();
        chosen
    }
}

/// Safe bounds-checked reader for standalone proof deserialization.
pub struct ByteCursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ByteCursor<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    pub fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    pub fn read_exact(&mut self, n: usize) -> Result<&'a [u8], String> {
        let end = self
            .pos
            .checked_add(n)
            .ok_or_else(|| "cursor overflow".to_string())?;
        if end > self.bytes.len() {
            return Err(format!(
                "unexpected EOF: needed {n} bytes at {}, len {}",
                self.pos,
                self.bytes.len()
            ));
        }
        let s = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    pub fn read_u8(&mut self) -> Result<u8, String> {
        Ok(self.read_exact(1)?[0])
    }

    pub fn read_u32(&mut self) -> Result<u32, String> {
        let b = self.read_exact(4)?;
        Ok(u32::from_le_bytes(b.try_into().unwrap()))
    }

    pub fn read_bb(&mut self) -> Result<u32, String> {
        let v = self.read_u32()?;
        if v >= P_U32 {
            return Err(format!("non-canonical BabyBear felt {v} >= {P_U32}"));
        }
        Ok(v)
    }

    pub fn read_arr32(&mut self) -> Result<[u8; 32], String> {
        let b = self.read_exact(32)?;
        Ok(b.try_into().unwrap())
    }

    pub fn read_arr16(&mut self) -> Result<[u8; 16], String> {
        let b = self.read_exact(16)?;
        Ok(b.try_into().unwrap())
    }

    pub fn read_ext4(&mut self) -> Result<Ext4, String> {
        let b = self.read_arr16()?;
        Ext4::from_bytes(&b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ext4_mul_schoolbook(a: Ext4, b: Ext4) -> Ext4 {
        let mut prod = [0u32; 7];
        for i in 0..4 {
            for j in 0..4 {
                prod[i + j] = badd(prod[i + j], bmul(a.0[i], b.0[j]));
            }
        }
        for deg in (4..7).rev() {
            prod[deg - 4] = badd(prod[deg - 4], bmul(W_EXT4, prod[deg]));
        }
        Ext4([prod[0], prod[1], prod[2], prod[3]])
    }

    #[test]
    fn test_ext4_field_axioms_and_ntt() {
        assert_eq!(bpow(G_PRIM, (P - 1) / 2), P_U32 - 1);
        assert_ne!(bpow(G_PRIM, (P - 1) / 3), 1);
        assert_ne!(bpow(G_PRIM, (P - 1) / 5), 1);

        let mut tr = CShakeTranscript::new(b"test-ext4");
        for i in 0..256u32 {
            tr.absorb_u32(b"i", i);
            let a = tr.squeeze_ext4(b"a", true);
            let b = tr.squeeze_ext4(b"b", true);
            assert_eq!(a.mul(b), ext4_mul_schoolbook(a, b));
            let a_inv = a.inv().expect("Ext4 X^4 - 11 is irreducible");
            assert_eq!(a.mul(a_inv), Ext4::ONE);
        }

        let n = 64usize;
        let tw = precompute_twiddles_bb(n, false);
        let inv_tw = precompute_twiddles_bb(n, true);
        let orig: Vec<u32> = (0..n).map(|i| bmul((i as u32) + 7, 1234567)).collect();
        let mut buf = orig.clone();
        ntt_bb_in_place(&mut buf, &tw);
        intt_bb_in_place(&mut buf, &inv_tw);
        assert_eq!(buf, orig);
    }
}
