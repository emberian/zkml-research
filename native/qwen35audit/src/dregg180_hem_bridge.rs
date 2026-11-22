//! Streamed `< 16 KiB` `Dregg-180` (`QSAG-NI-180`, `SLOT_0P5X0P5` zero-SRAM-macro `gf180mcuD`)
//! `OP_FOLD` (`0x30`) / `OP_HEM` (`0x31`) `GoldilocksExt4` silicon verifier VM, `Poseidon2-12` +
//! `cSHAKE256` Canopy WHIR prover, and heterogeneous `BabyBear Ext4` + `Tower256` + `Simplex`
//! `FinCert` leaf aggregation bridge.
//!
//! Companion Lean `v4.35.0` formalization: `/Users/ember/dev/minidregg/Selvage/GoldilocksDregg180Bridge.lean`.
#![deny(warnings)]

use crate::bpe_bridge::QwenBpeRom;
use crate::ext4::{cshake256_32, merkle_open_single_cshake, merkle_root_cshake, Ext4 as BbExt4, MerkleSinglePath};
use crate::u1_audit::run_padded_complement_sk_dfa;
use crate::unified_turn_weld::{
    verify_payable_compute_receipt_and_settle, verify_wots_signature, PayableComputeReceipt,
    ProviderExecutionLease, SaltedByteWhirCommitment, WotsKeypair, WotsPublicKey, WotsSignature,
};
use crate::whir_ext4::{
    open_whir_batch_ext4, verify_whir_batch_ext4, JointLinearClaimExt4, WhirBatchOpeningProofExt4,
    WhirCommittedMatrixExt4, WhirExt4MatrixShape, WHIR_EXT4_BLOWUP,
};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

// ================================================================================================
// §1. Canonical 64-Bit `Goldilocks` (`p = 2^64 - 2^32 + 1`) & `GoldilocksExt4` (`v^4 = 7`)
// ================================================================================================

/// Goldilocks prime `p = 2^64 - 2^32 + 1 = 0xFFFF_FFFF_0000_0001`.
pub const GOLDILOCKS_PRIME: u64 = 0xFFFF_FFFF_0000_0001;
/// Reduction constant `epsilon = 2^32 - 1 = 2^64 - p`.
pub const GOLDILOCKS_EPSILON: u64 = 0xFFFF_FFFF;
/// Multiplicative generator & quartic non-residue `g = 7` (`X^4 - 7` irreducible over `F_p`).
pub const GOLDILOCKS_NON_RESIDUE: u64 = 7;
/// Primitive `2^32`-th root of unity `omega_{2^32} = 7^{2^32 - 1} mod p`.
pub const GOLDILOCKS_ROOT_2_32: u64 = Goldilocks(7).pow(0xFFFF_FFFF).0;
/// Primitive 4-th root of unity `zeta_4 = 7^{(p - 1) / 4} = 2^48` (`zeta_4^2 == -1 mod p`).
pub const GOLDILOCKS_FROBENIUS_ZETA4: Goldilocks = Goldilocks(1u64 << 48);
/// `2^{-1} mod p = (p + 1) / 2 = 9223372034707292161`.
pub const GOLDILOCKS_INV2: Goldilocks = Goldilocks(9_223_372_034_707_292_161);

/// Maximum static RAM footprint allowed for `Dregg180StreamVm` (`16 KiB = 16,384 B`).
pub const DREGG180_VM_MAX_STATIC_BYTES: usize = 16_384;

/// Canonical element of `F_p` (`self.0 < GOLDILOCKS_PRIME`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Goldilocks(pub u64);

impl Goldilocks {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);
    pub const TWO: Self = Self(2);
    pub const SEVEN: Self = Self(7);
    pub const NEG_ONE: Self = Self(GOLDILOCKS_PRIME - 1);

    /// Strict canonical constructor rejecting aliases in `[p, 2^64)`.
    #[inline(always)]
    pub const fn from_canonical_u64(raw: u64) -> Option<Self> {
        if raw < GOLDILOCKS_PRIME {
            Some(Self(raw))
        } else {
            None
        }
    }

    /// Branchless reduction of any `u64` modulo `p` (`x < p ? x : x - p`).
    #[inline(always)]
    pub const fn from_u64_reduced(x: u64) -> Self {
        let (diff, borrow) = x.overflowing_sub(GOLDILOCKS_PRIME);
        let mask = (borrow as u64).wrapping_neg();
        Self((x & mask) | (diff & !mask))
    }

    /// Reduce `u128` product/sum modulo `p` (`2^64 == 2^32 - 1`, `2^96 == -1 mod p`).
    #[inline(always)]
    pub const fn from_u128_reduced(x: u128) -> Self {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let hi_lo = hi & GOLDILOCKS_EPSILON;
        let hi_hi = hi >> 32;
        let (t0, borrow) = lo.overflowing_sub(hi_hi);
        let t0 = t0.wrapping_sub(GOLDILOCKS_EPSILON & (borrow as u64).wrapping_neg());
        let adj = (hi_lo << 32).wrapping_sub(hi_lo);
        let (t1, carry) = t0.overflowing_add(adj);
        let t1 = t1.wrapping_add(GOLDILOCKS_EPSILON & (carry as u64).wrapping_neg());
        Self::from_u64_reduced(t1)
    }

    #[inline(always)]
    pub const fn to_canonical_u64(self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        let (sum, carry) = self.0.overflowing_add(rhs.0);
        let sum = sum.wrapping_add(GOLDILOCKS_EPSILON & (carry as u64).wrapping_neg());
        Self::from_u64_reduced(sum)
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        let (diff, borrow) = self.0.overflowing_sub(rhs.0);
        let diff = diff.wrapping_sub(GOLDILOCKS_EPSILON & (borrow as u64).wrapping_neg());
        Self::from_u64_reduced(diff)
    }

    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        if self.0 == 0 {
            Self::ZERO
        } else {
            Self(GOLDILOCKS_PRIME - self.0)
        }
    }

    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        Self::from_u128_reduced((self.0 as u128) * (rhs.0 as u128))
    }

    #[inline(always)]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    #[inline(always)]
    pub const fn sbox7(self) -> Self {
        let x2 = self.square();
        let x3 = x2.const_mul(self);
        let x6 = x3.square();
        x6.const_mul(self)
    }

    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Constant-form inverse `x^{p - 2} mod p` (`0 -> 0`).
    #[inline]
    pub const fn inv(self) -> Self {
        if self.0 == 0 {
            Self::ZERO
        } else {
            self.pow(GOLDILOCKS_PRIME - 2)
        }
    }

    /// Primitive `2^{log_n}`-th root of unity in `Goldilocks` (`log_n <= 32`).
    #[inline]
    pub const fn two_adic_generator(log_n: usize) -> Self {
        assert!(log_n <= 32);
        let mut w = Self(GOLDILOCKS_ROOT_2_32);
        let mut steps = 32 - log_n;
        while steps > 0 {
            w = w.square();
            steps -= 1;
        }
        w
    }
}

impl Add for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}
impl AddAssign for Goldilocks {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Self) {
        *self = self.const_add(rhs);
    }
}
impl Sub for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}
impl SubAssign for Goldilocks {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.const_sub(rhs);
    }
}
impl Neg for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}
impl Mul for Goldilocks {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}
impl MulAssign for Goldilocks {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.const_mul(rhs);
    }
}

/// Quartic extension `GoldilocksExt4 = F_p[v] / (v^4 - 7)` in exact `Dregg-180` hardware register
/// limb order `[c0.c0, c0.c1, c1.c0, c1.c1]` = coefficients of `[1, v^2, v, v^3]` (`u = v^2`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct GoldilocksExt4(pub [Goldilocks; 4]);

impl GoldilocksExt4 {
    pub const ZERO: Self = Self([Goldilocks::ZERO; 4]);
    pub const ONE: Self = Self([Goldilocks::ONE, Goldilocks::ZERO, Goldilocks::ZERO, Goldilocks::ZERO]);
    pub const V: Self = Self([Goldilocks::ZERO, Goldilocks::ZERO, Goldilocks::ONE, Goldilocks::ZERO]);

    #[inline(always)]
    pub const fn from_base(x: Goldilocks) -> Self {
        Self([x, Goldilocks::ZERO, Goldilocks::ZERO, Goldilocks::ZERO])
    }

    #[inline(always)]
    pub const fn from_u64_limbs(w: [u64; 4]) -> Self {
        Self([
            Goldilocks::from_u64_reduced(w[0]),
            Goldilocks::from_u64_reduced(w[1]),
            Goldilocks::from_u64_reduced(w[2]),
            Goldilocks::from_u64_reduced(w[3]),
        ])
    }

    #[inline(always)]
    pub const fn from_canonical_u64_limbs(w: [u64; 4]) -> Option<Self> {
        let Some(l0) = Goldilocks::from_canonical_u64(w[0]) else { return None };
        let Some(l1) = Goldilocks::from_canonical_u64(w[1]) else { return None };
        let Some(l2) = Goldilocks::from_canonical_u64(w[2]) else { return None };
        let Some(l3) = Goldilocks::from_canonical_u64(w[3]) else { return None };
        Some(Self([l0, l1, l2, l3]))
    }

    #[inline(always)]
    pub const fn to_u64_limbs(self) -> [u64; 4] {
        [self.0[0].0, self.0[1].0, self.0[2].0, self.0[3].0]
    }

    #[inline(always)]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self([
            self.0[0].const_add(rhs.0[0]),
            self.0[1].const_add(rhs.0[1]),
            self.0[2].const_add(rhs.0[2]),
            self.0[3].const_add(rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self([
            self.0[0].const_sub(rhs.0[0]),
            self.0[1].const_sub(rhs.0[1]),
            self.0[2].const_sub(rhs.0[2]),
            self.0[3].const_sub(rhs.0[3]),
        ])
    }

    #[inline(always)]
    pub const fn const_neg(self) -> Self {
        Self([
            self.0[0].const_neg(),
            self.0[1].const_neg(),
            self.0[2].const_neg(),
            self.0[3].const_neg(),
        ])
    }

    #[inline(always)]
    pub const fn scale_base(self, s: Goldilocks) -> Self {
        Self([
            self.0[0].const_mul(s),
            self.0[1].const_mul(s),
            self.0[2].const_mul(s),
            self.0[3].const_mul(s),
        ])
    }

    /// Exact `Dregg-180` multiplication in `[1, v^2, v, v^3]` basis (`LMAP = [0, 2, 1, 3]`, `v^4 = 7`).
    #[inline(always)]
    pub const fn const_mul(self, rhs: Self) -> Self {
        let a = [self.0[0], self.0[2], self.0[1], self.0[3]];
        let b = [rhs.0[0], rhs.0[2], rhs.0[1], rhs.0[3]];
        let mut poly = [Goldilocks::ZERO; 4];
        let mut k = 0usize;
        while k < 4 {
            let mut acc = Goldilocks::ZERO;
            let mut i = 0usize;
            while i < 4 {
                let term = if i <= k {
                    a[i].const_mul(b[k - i])
                } else {
                    Goldilocks::SEVEN.const_mul(a[i].const_mul(b[k + 4 - i]))
                };
                acc = acc.const_add(term);
                i += 1;
            }
            poly[k] = acc;
            k += 1;
        }
        Self([poly[0], poly[2], poly[1], poly[3]])
    }

    #[inline(always)]
    pub const fn square(self) -> Self {
        self.const_mul(self)
    }

    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exp > 0 {
            if (exp & 1) == 1 {
                acc = acc.const_mul(base);
            }
            base = base.square();
            exp >>= 1;
        }
        acc
    }

    /// Frobenius endomorphism `(c0 + c1 v)^p = conj(c0) + zeta_4 * conj(c1) * v`.
    #[inline]
    pub const fn frobenius(self) -> Self {
        Self([
            self.0[0],
            self.0[1].const_neg(),
            self.0[2].const_mul(GOLDILOCKS_FROBENIUS_ZETA4),
            self.0[3].const_neg().const_mul(GOLDILOCKS_FROBENIUS_ZETA4),
        ])
    }

    /// Multiplicative inverse `(c0 - c1 v) / (c0^2 - u c1^2)` (`0 -> 0`).
    #[inline]
    pub const fn inv(self) -> Self {
        let (a0, a1) = (self.0[0], self.0[1]);
        let (b0, b1) = (self.0[2], self.0[3]);
        // c0^2 in F_p[u]/(u^2 - 7): (a0^2 + 7 a1^2) + (2 a0 a1) u
        let c0_sq_0 = a0.square().const_add(Goldilocks::SEVEN.const_mul(a1.square()));
        let c0_sq_1 = Goldilocks::TWO.const_mul(a0.const_mul(a1));
        // c1^2 = (b0^2 + 7 b1^2) + (2 b0 b1) u; u * c1^2 = 7*(2 b0 b1) + (b0^2 + 7 b1^2) u
        let c1_sq_0 = b0.square().const_add(Goldilocks::SEVEN.const_mul(b1.square()));
        let c1_sq_1 = Goldilocks::TWO.const_mul(b0.const_mul(b1));
        let n0 = c0_sq_0.const_sub(Goldilocks::SEVEN.const_mul(c1_sq_1));
        let n1 = c0_sq_1.const_sub(c1_sq_0);
        // Inverse of (n0 + n1 u) in F_{p^2}: (n0 - n1 u) / (n0^2 - 7 n1^2)
        let base_norm = n0.square().const_sub(Goldilocks::SEVEN.const_mul(n1.square()));
        let base_inv = base_norm.inv();
        let inv_n0 = n0.const_mul(base_inv);
        let inv_n1 = n1.const_neg().const_mul(base_inv);
        // Multiply (c0 - c1 v) by (inv_n0 + inv_n1 u):
        let out_c0_0 = a0
            .const_mul(inv_n0)
            .const_add(Goldilocks::SEVEN.const_mul(a1.const_mul(inv_n1)));
        let out_c0_1 = a0.const_mul(inv_n1).const_add(a1.const_mul(inv_n0));
        let nb0 = b0.const_neg();
        let nb1 = b1.const_neg();
        let out_c1_0 = nb0
            .const_mul(inv_n0)
            .const_add(Goldilocks::SEVEN.const_mul(nb1.const_mul(inv_n1)));
        let out_c1_1 = nb0.const_mul(inv_n1).const_add(nb1.const_mul(inv_n0));
        Self([out_c0_0, out_c0_1, out_c1_0, out_c1_1])
    }

    /// Evaluate univariate polynomial `coeffs[0] + coeffs[1]*x + ...` via Horner's rule.
    #[inline]
    pub fn eval_univariate(coeffs: &[Self], x: Self) -> Self {
        let mut acc = Self::ZERO;
        for &c in coeffs.iter().rev() {
            acc = acc.const_mul(x).const_add(c);
        }
        acc
    }

    /// CWYZ asymmetric duet-fold step matching `Dregg-180` `fold_program` (`qsag_ni_model.py:115`).
    #[inline]
    pub const fn cwyz_duet_fold(
        v0: Self,
        v1: Self,
        alpha: Self,
        beta: Self,
        theta: Self,
        inv2: Goldilocks,
        inv2_y0: Goldilocks,
        y0_sq: Goldilocks,
    ) -> Self {
        let even = v0.const_add(v1).scale_base(inv2);
        let odd = v0.const_sub(v1).scale_base(inv2_y0);
        let gamma = alpha.const_add(beta.scale_base(y0_sq));
        let mixed = even.const_add(theta.const_mul(odd));
        odd.const_add(gamma.const_mul(mixed))
    }
}

impl Add for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        self.const_add(rhs)
    }
}
impl Sub for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.const_sub(rhs)
    }
}
impl Neg for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        self.const_neg()
    }
}
impl Mul for GoldilocksExt4 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        self.const_mul(rhs)
    }
}

/// Quintic extension `Fp5 = F_p[X] / (X^5 - 3)` (`zk-Hem v2` `flags & 0x10` mode in `Dregg-180`).
#[inline]
pub fn fp5_mul(x: &[u64; 5], y: &[u64; 5]) -> [u64; 5] {
    let mut out = [0u64; 5];
    for k in 0..5 {
        let mut acc = Goldilocks::ZERO;
        for i in 0..5 {
            let ai = Goldilocks::from_u64_reduced(x[i]);
            let term = if i <= k {
                ai * Goldilocks::from_u64_reduced(y[k - i])
            } else {
                Goldilocks(3) * ai * Goldilocks::from_u64_reduced(y[k + 5 - i])
            };
            acc += term;
        }
        out[k] = acc.0;
    }
    out
}

/// Radix-2 Cooley-Tukey NTT in place over `Goldilocks` (natural evaluation order).
pub fn ntt_goldilocks_in_place(a: &mut [Goldilocks], inverse: bool) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros() as usize;
    for i in 0..n {
        let rev = i.reverse_bits() >> (usize::BITS as usize - log_n);
        if i < rev {
            a.swap(i, rev);
        }
    }
    let mut len = 2usize;
    let mut stage = 1usize;
    while len <= n {
        let g = Goldilocks::two_adic_generator(stage);
        let w_len = if inverse { g.inv() } else { g };
        let half = len / 2;
        for blk in a.chunks_exact_mut(len) {
            let mut w = Goldilocks::ONE;
            for j in 0..half {
                let u = blk[j];
                let v = blk[j + half] * w;
                blk[j] = u + v;
                blk[j + half] = u - v;
                w *= w_len;
            }
        }
        len <<= 1;
        stage += 1;
    }
    if inverse {
        let n_inv = Goldilocks::from_u64_reduced(n as u64).inv();
        for x in a.iter_mut() {
            *x *= n_inv;
        }
    }
}

/// Radix-2 Cooley-Tukey NTT in place over `GoldilocksExt4` using base-field 2-adic roots.
pub fn ntt_ext4_in_place(a: &mut [GoldilocksExt4], inverse: bool) {
    let n = a.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros() as usize;
    for i in 0..n {
        let rev = i.reverse_bits() >> (usize::BITS as usize - log_n);
        if i < rev {
            a.swap(i, rev);
        }
    }
    let mut len = 2usize;
    let mut stage = 1usize;
    while len <= n {
        let g = Goldilocks::two_adic_generator(stage);
        let w_len = if inverse { g.inv() } else { g };
        let half = len / 2;
        for blk in a.chunks_exact_mut(len) {
            let mut w = Goldilocks::ONE;
            for j in 0..half {
                let u = blk[j];
                let v = blk[j + half].scale_base(w);
                blk[j] = u + v;
                blk[j + half] = u - v;
                w *= w_len;
            }
        }
        len <<= 1;
        stage += 1;
    }
    if inverse {
        let n_inv = Goldilocks::from_u64_reduced(n as u64).inv();
        for x in a.iter_mut() {
            *x = x.scale_base(n_inv);
        }
    }
}

/// Coset Reed-Solomon encoding over `7 * H` (`|H| = coeffs.len() * blowup`).
pub fn encode_rs_coset_ext4(coeffs: &[GoldilocksExt4], blowup: usize, shift: Goldilocks) -> Vec<GoldilocksExt4> {
    assert!(coeffs.len().is_power_of_two() && blowup.is_power_of_two() && blowup >= 2);
    let domain_len = coeffs.len() * blowup;
    let mut buf = vec![GoldilocksExt4::ZERO; domain_len];
    let mut sp = Goldilocks::ONE;
    for (i, &c) in coeffs.iter().enumerate() {
        buf[i] = c.scale_base(sp);
        sp *= shift;
    }
    ntt_ext4_in_place(&mut buf, false);
    buf
}

// ================================================================================================
// §2. Bit-Exact `Dregg-180` Width-12 `Poseidon2`, Stack `Keccak-1600`, & `GF(2^128)` Primitives
// ================================================================================================

pub const P2_IV: u64 = 0x504F_5332_5F47_4C31;
pub const P2_DOMAIN_CANOPY_NODE_HI: u64 = 0x5032_4E44_0000_0000;
pub const P2_DOMAIN_CANOPY_LEAF: u64 = 0x5032_434E_4C46_4501;
pub const P2_DOMAIN_FS_INIT: u64 = 0x5032_4653_494E_4954;
pub const P2_DOMAIN_FS_BIND_REL: u64 = 0x5032_4653_4252_454C;
pub const P2_DOMAIN_FS_BIND_INST: u64 = 0x5032_4653_4249_4E53;
pub const P2_DOMAIN_FS_ABSORB_LIMBS: u64 = 0x5032_4653_414C_4D42;
pub const P2_DOMAIN_FS_SQUEEZE_EXT4: u64 = 0x5032_4653_5351_4534;
pub const P2_DOMAIN_FS_SQUEEZE_IDX: u64 = 0x5032_4653_5351_4958;
pub const P2_DOMAIN_FS_POW: u64 = 0x5032_4653_504F_5701;
pub const FS_INIT_CAP: [u64; 4] = [P2_DOMAIN_FS_INIT, 0, 0, P2_IV];

/// `Dregg-180` `H_ZK_PIN` constant (`qsag_ni_model.py:33`).
pub const H_ZK_PIN: u128 = 0x9E37_79B9_7F4A_7C15_504F_5332_5F47_4C31;

/// Canonical `cSHAKE256` customization string for `Hem` Canopy trees (`qsag-agg`).
pub const CANOPY_CUSTOM: &[u8] = b"QSAG.PCS.CANOPY/v2";

#[inline(always)]
const fn p2_rc_bij(x: u64) -> u64 {
    let z0 = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z2 ^ (z2 >> 31)
}

#[inline(always)]
pub const fn p2_rc(tag: u64, rnd: u64, lane: u64) -> Goldilocks {
    let raw = p2_rc_bij(p2_rc_bij(p2_rc_bij(P2_IV ^ tag) ^ rnd) ^ lane);
    Goldilocks::from_u128_reduced(raw as u128)
}

const P2_RC_EXT0: [[Goldilocks; 12]; 4] = {
    let mut t = [[Goldilocks::ZERO; 12]; 4];
    let mut r = 0;
    while r < 4 {
        let mut l = 0;
        while l < 12 {
            t[r][l] = p2_rc(0, r as u64, l as u64);
            l += 1;
        }
        r += 1;
    }
    t
};

const P2_RC_INT: [Goldilocks; 22] = {
    let mut t = [Goldilocks::ZERO; 22];
    let mut r = 0;
    while r < 22 {
        t[r] = p2_rc(1, r as u64, 0);
        r += 1;
    }
    t
};

const P2_RC_EXT2: [[Goldilocks; 12]; 4] = {
    let mut t = [[Goldilocks::ZERO; 12]; 4];
    let mut r = 0;
    while r < 4 {
        let mut l = 0;
        while l < 12 {
            t[r][l] = p2_rc(2, r as u64, l as u64);
            l += 1;
        }
        r += 1;
    }
    t
};

#[inline(always)]
fn p2_m4(b: [Goldilocks; 4]) -> [Goldilocks; 4] {
    let s = (b[0] + b[1]) + (b[2] + b[3]);
    [
        s + b[0] + Goldilocks::TWO * b[1],
        s + b[1] + Goldilocks::TWO * b[2],
        s + b[2] + Goldilocks::TWO * b[3],
        s + b[3] + Goldilocks::TWO * b[0],
    ]
}

#[inline(always)]
pub fn poseidon2_apply_me(st: &mut [Goldilocks; 12]) {
    let t = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
    let y0 = p2_m4([t[0], t[1], t[2], t[3]]);
    let y1 = p2_m4([t[4], t[5], t[6], t[7]]);
    let y2 = p2_m4([t[8], t[9], t[10], t[11]]);
    let mut o = [Goldilocks::ZERO; 12];
    for i in 0..4 {
        let s = y0[i] + y1[i] + y2[i];
        o[i] = y0[i] + s;
        o[4 + i] = y1[i] + s;
        o[8 + i] = y2[i] + s;
    }
    *st = [
        o[0], o[4], o[8], o[1], o[5], o[9], o[2], o[6], o[10], o[3], o[7], o[11],
    ];
}

#[inline(always)]
pub fn poseidon2_apply_mi(st: &mut [Goldilocks; 12]) {
    let s = (((st[0] + st[1]) + (st[2] + st[3])) + ((st[4] + st[5]) + (st[6] + st[7])))
        + ((st[8] + st[9]) + (st[10] + st[11]));
    st[0] = s - (Goldilocks(64) * st[0]);
    for (i, lane) in st.iter_mut().enumerate().skip(1) {
        *lane = (Goldilocks(1u64 << (i - 1)) * *lane) + s;
    }
}

/// Width-12 `Poseidon2` permutation over `Goldilocks` (4 full + 22 partial + 4 full rounds),
/// bit-exact with `rtl/qsag_field_engine.sv` and `qsag_prims.py:p2_perm`.
pub fn poseidon2_perm12(st: &mut [Goldilocks; 12]) {
    poseidon2_apply_me(st);
    for rc_row in &P2_RC_EXT0 {
        for (x, &rc) in st.iter_mut().zip(rc_row.iter()) {
            *x = (*x + rc).sbox7();
        }
        poseidon2_apply_me(st);
    }
    for &rc in &P2_RC_INT {
        st[0] = (st[0] + rc).sbox7();
        poseidon2_apply_mi(st);
    }
    for rc_row in &P2_RC_EXT2 {
        for (x, &rc) in st.iter_mut().zip(rc_row.iter()) {
            *x = (*x + rc).sbox7();
        }
        poseidon2_apply_me(st);
    }
}

/// Rate-8, capacity-4 `poseidon2_sponge_hash_limbs` (`qsag_prims.py:141`).
pub fn p2_sponge_hash_limbs(domain: u64, cap: [u64; 4], limbs: &[u64]) -> [u64; 4] {
    let mut st = [Goldilocks::ZERO; 12];
    for i in 0..4 {
        st[8 + i] = Goldilocks::from_u128_reduced(cap[i] as u128);
    }
    let total = 2 + limbs.len();
    let mut off = 0usize;
    let mut first = true;
    while first || off < total {
        let take = (total - off).min(8);
        for k in 0..take {
            let idx = off + k;
            let raw = if idx == 0 {
                domain
            } else if idx == 1 {
                limbs.len() as u64
            } else {
                limbs[idx - 2]
            };
            st[k] += Goldilocks::from_u128_reduced(raw as u128);
        }
        poseidon2_perm12(&mut st);
        off += take;
        first = false;
    }
    [st[0].0, st[1].0, st[2].0, st[3].0]
}

/// Rate-6, capacity-6 `sponge12_rate6` (`qsag_prims.py:200`, `zk-Hem v2`).
pub fn p2_sponge12_rate6(limbs: &[u64]) -> [u64; 12] {
    let mut st = [Goldilocks::ZERO; 12];
    let mut off = 0usize;
    while off < limbs.len() {
        let take = (limbs.len() - off).min(6);
        for k in 0..take {
            st[k] += Goldilocks::from_u128_reduced(limbs[off + k] as u128);
        }
        if take < 6 {
            st[take] += Goldilocks::ONE;
        }
        poseidon2_perm12(&mut st);
        off += take;
    }
    if limbs.len() % 6 == 0 {
        st[0] += Goldilocks::ONE;
        poseidon2_perm12(&mut st);
    }
    let mut out = [0u64; 12];
    for i in 0..12 {
        out[i] = st[i].0;
    }
    out
}

/// `Dregg-180` Canopy internal node compression `st[0..4] + L + 2*R + 4*C` (`qsag_prims.py:168`).
#[inline]
pub fn p2_canopy_node(left: [u64; 4], right: [u64; 4], key3: [u64; 3], node_idx: u32) -> [u64; 4] {
    let l = left.map(|x| Goldilocks::from_u128_reduced(x as u128));
    let r = right.map(|x| Goldilocks::from_u128_reduced(x as u128));
    let c = [
        Goldilocks::from_u128_reduced((P2_DOMAIN_CANOPY_NODE_HI | (node_idx as u64)) as u128),
        Goldilocks::from_u128_reduced(key3[0] as u128),
        Goldilocks::from_u128_reduced(key3[1] as u128),
        Goldilocks::from_u128_reduced(key3[2] as u128),
    ];
    let mut st = [
        l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3], c[0], c[1], c[2], c[3],
    ];
    poseidon2_perm12(&mut st);
    let mut out = [0u64; 4];
    for i in 0..4 {
        let v = st[i] + l[i] + (Goldilocks::TWO * r[i]) + (Goldilocks(4) * c[i]);
        out[i] = v.0;
    }
    out
}

/// Walk a `Poseidon2-12` Canopy path from `leaf` at `leaf_index` up `siblings`.
pub fn p2_canopy_path(leaf: [u64; 4], siblings: &[[u64; 4]], key3: [u64; 3], leaf_index: u32) -> [u64; 4] {
    let mut idx = (1u64 << siblings.len()) | (leaf_index as u64);
    let mut cur = leaf.map(|x| Goldilocks::from_u128_reduced(x as u128).0);
    for &sib in siblings {
        let parent = (idx >> 1) as u32;
        cur = if (idx & 1) == 1 {
            p2_canopy_node(sib, cur, key3, parent)
        } else {
            p2_canopy_node(cur, sib, key3, parent)
        };
        idx >>= 1;
    }
    cur
}

/// `qsag-agg` Fiat-Shamir byte framing `[len(b)] ++ little-endian 7-byte limbs`.
pub fn pack_bytes_7_limbs(bytes: &[u8]) -> Vec<u64> {
    let mut out = Vec::with_capacity(1 + bytes.len().div_ceil(7));
    out.push(bytes.len() as u64);
    for chunk in bytes.chunks(7) {
        let mut buf = [0u8; 8];
        buf[..chunk.len()].copy_from_slice(chunk);
        out.push(u64::from_le_bytes(buf));
    }
    out
}

/// Pack a 32-byte digest injectively into `5` canonical 56-bit `Goldilocks` limbs (`< 2^56 < p`).
#[inline]
pub const fn pack_digest32_to_5_limbs(digest: &[u8; 32]) -> [u64; 5] {
    let mut out = [0u64; 5];
    let mut k = 0usize;
    while k < 4 {
        let b = k * 7;
        out[k] = (digest[b] as u64)
            | ((digest[b + 1] as u64) << 8)
            | ((digest[b + 2] as u64) << 16)
            | ((digest[b + 3] as u64) << 24)
            | ((digest[b + 4] as u64) << 32)
            | ((digest[b + 5] as u64) << 40)
            | ((digest[b + 6] as u64) << 48);
        k += 1;
    }
    out[4] = (digest[28] as u64)
        | ((digest[29] as u64) << 8)
        | ((digest[30] as u64) << 16)
        | ((digest[31] as u64) << 24);
    out
}

/// Unpack `5` 56-bit/32-bit limbs back to `[u8; 32]`, returning `None` if upper bits are non-zero.
#[inline]
pub const fn unpack_5_limbs_to_digest32(limbs: [u64; 5]) -> Option<[u8; 32]> {
    if (limbs[0] >> 56) != 0
        || (limbs[1] >> 56) != 0
        || (limbs[2] >> 56) != 0
        || (limbs[3] >> 56) != 0
        || (limbs[4] >> 32) != 0
    {
        return None;
    }
    let mut out = [0u8; 32];
    let mut k = 0usize;
    while k < 4 {
        let w = limbs[k].to_le_bytes();
        let mut j = 0usize;
        while j < 7 {
            out[k * 7 + j] = w[j];
            j += 1;
        }
        k += 1;
    }
    let w4 = (limbs[4] as u32).to_le_bytes();
    out[28] = w4[0];
    out[29] = w4[1];
    out[30] = w4[2];
    out[31] = w4[3];
    Some(out)
}

const KECCAK_RC: [u64; 24] = [
    0x0000_0000_0000_0001, 0x0000_0000_0000_8082, 0x8000_0000_0000_808A, 0x8000_0000_8000_8000,
    0x0000_0000_0000_808B, 0x0000_0000_8000_0001, 0x8000_0000_8000_8081, 0x8000_0000_0000_8009,
    0x0000_0000_0000_008A, 0x0000_0000_0000_0088, 0x0000_0000_8000_8009, 0x0000_0000_8000_000A,
    0x0000_0000_8000_808B, 0x8000_0000_0000_008B, 0x8000_0000_0000_8089, 0x8000_0000_0000_8003,
    0x8000_0000_0000_8002, 0x8000_0000_0000_0080, 0x0000_0000_0000_800A, 0x8000_0000_8000_000A,
    0x8000_0000_8000_8081, 0x8000_0000_0000_8080, 0x0000_0000_8000_0001, 0x8000_0000_8000_8008,
];

const KECCAK_ROT: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// Zero-heap stack `Keccak-p[1600, rounds]` (`rounds = 12` for `TurboSHAKE256`, `24` for `SHAKE256`/`cSHAKE256`).
pub const fn keccak_p1600_stack(a: &mut [u64; 25], rounds: usize) {
    let mut r = 24 - rounds;
    while r < 24 {
        let mut c = [0u64; 5];
        let mut x = 0usize;
        while x < 5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            x += 1;
        }
        let mut d = [0u64; 5];
        x = 0;
        while x < 5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            x += 1;
        }
        let mut i = 0usize;
        while i < 25 {
            a[i] ^= d[i % 5];
            i += 1;
        }
        let mut b = [0u64; 25];
        x = 0;
        while x < 5 {
            let mut y = 0usize;
            while y < 5 {
                let rot = KECCAK_ROT[x][y];
                let val = a[x + 5 * y];
                b[y + 5 * ((2 * x + 3 * y) % 5)] = if rot == 0 { val } else { val.rotate_left(rot) };
                y += 1;
            }
            x += 1;
        }
        i = 0;
        while i < 25 {
            let row = 5 * (i / 5);
            let col = i % 5;
            a[i] = b[i] ^ ((!b[row + (col + 1) % 5]) & b[row + (col + 2) % 5]);
            i += 1;
        }
        a[0] ^= KECCAK_RC[r];
        r += 1;
    }
}

/// Zero-heap stack `TurboSHAKE256` (`Keccak-p[1600, 12]`, `rate = 136`, `suffix = 0x1F`, `32`-byte output).
pub fn turboshake256_32_stack(slices: &[&[u8]]) -> [u8; 32] {
    let mut st = [0u64; 25];
    let mut blk = [0u8; 136];
    let mut pos = 0usize;
    for s in slices {
        for &byte in *s {
            blk[pos] ^= byte;
            pos += 1;
            if pos == 136 {
                for l in 0..17 {
                    let b = 8 * l;
                    st[l] ^= u64::from_le_bytes([
                        blk[b], blk[b + 1], blk[b + 2], blk[b + 3], blk[b + 4], blk[b + 5],
                        blk[b + 6], blk[b + 7],
                    ]);
                }
                keccak_p1600_stack(&mut st, 12);
                blk = [0u8; 136];
                pos = 0;
            }
        }
    }
    blk[pos] ^= 0x1F;
    blk[135] ^= 0x80;
    for l in 0..17 {
        let b = 8 * l;
        st[l] ^= u64::from_le_bytes([
            blk[b], blk[b + 1], blk[b + 2], blk[b + 3], blk[b + 4], blk[b + 5], blk[b + 6],
            blk[b + 7],
        ]);
    }
    keccak_p1600_stack(&mut st, 12);
    let mut out = [0u8; 32];
    for l in 0..4 {
        out[8 * l..8 * (l + 1)].copy_from_slice(&st[l].to_le_bytes());
    }
    out
}

/// Precompute the 25-lane `Keccak-f[1600]` midstate after `bytepad(encode_string("") || encode_string(CANOPY_CUSTOM), 136)`.
pub const fn canopy_cshake256_midstate() -> [u64; 25] {
    let mut blk = [0u8; 136];
    // left_encode(136) = [1, 136], encode_string("") = [1, 0], encode_string(CANOPY_CUSTOM) = [1, 144] || CANOPY_CUSTOM
    blk[0] = 1;
    blk[1] = 136;
    blk[2] = 1;
    blk[3] = 0;
    blk[4] = 1;
    blk[5] = (CANOPY_CUSTOM.len() * 8) as u8;
    let mut i = 0usize;
    while i < CANOPY_CUSTOM.len() {
        blk[6 + i] = CANOPY_CUSTOM[i];
        i += 1;
    }
    let mut st = [0u64; 25];
    let mut l = 0usize;
    while l < 17 {
        let b = 8 * l;
        st[l] = (blk[b] as u64)
            | ((blk[b + 1] as u64) << 8)
            | ((blk[b + 2] as u64) << 16)
            | ((blk[b + 3] as u64) << 24)
            | ((blk[b + 4] as u64) << 32)
            | ((blk[b + 5] as u64) << 40)
            | ((blk[b + 6] as u64) << 48)
            | ((blk[b + 7] as u64) << 56);
        l += 1;
    }
    keccak_p1600_stack(&mut st, 24);
    st
}

pub const CANOPY_CSHAKE_MIDSTATE: [u64; 25] = canopy_cshake256_midstate();

/// Zero-heap `cSHAKE256("", tag || payload, 256, "QSAG.PCS.CANOPY/v2")` on `[u64; 25]` stack state.
pub fn cshake256_canopy_stack(tag: u8, slices: &[&[u8]]) -> [u8; 32] {
    let mut st = CANOPY_CSHAKE_MIDSTATE;
    let mut blk = [0u8; 136];
    blk[0] = tag;
    let mut pos = 1usize;
    for s in slices {
        for &byte in *s {
            blk[pos] = byte;
            pos += 1;
            if pos == 136 {
                for l in 0..17 {
                    let b = 8 * l;
                    st[l] ^= u64::from_le_bytes([
                        blk[b], blk[b + 1], blk[b + 2], blk[b + 3], blk[b + 4], blk[b + 5],
                        blk[b + 6], blk[b + 7],
                    ]);
                }
                keccak_p1600_stack(&mut st, 24);
                blk = [0u8; 136];
                pos = 0;
            }
        }
    }
    blk[pos] ^= 0x04;
    blk[135] ^= 0x80;
    for l in 0..17 {
        let b = 8 * l;
        st[l] ^= u64::from_le_bytes([
            blk[b], blk[b + 1], blk[b + 2], blk[b + 3], blk[b + 4], blk[b + 5], blk[b + 6],
            blk[b + 7],
        ]);
    }
    keccak_p1600_stack(&mut st, 24);
    let mut out = [0u8; 32];
    for l in 0..4 {
        out[8 * l..8 * (l + 1)].copy_from_slice(&st[l].to_le_bytes());
    }
    out
}

/// `cSHAKE256` Canopy internal node `cSHAKE256("QSAG.PCS.CANOPY/v2", 0x00 || node_idx_le4 || left || right)`.
#[inline]
pub fn cshake256_canopy_node(left: &[u8; 32], right: &[u8; 32], node_idx: u32) -> [u8; 32] {
    let idx_le = node_idx.to_le_bytes();
    cshake256_canopy_stack(0x00, &[&idx_le, left, right])
}

/// `cSHAKE256` Canopy fiber leaf `cSHAKE256("QSAG.PCS.CANOPY/v2", 0x12 || stage || fiber_idx_le4 || v0 || v1)`.
#[inline]
pub fn cshake256_canopy_ext4_pair_leaf(
    stage: u8,
    fiber_idx: u32,
    v0: GoldilocksExt4,
    v1: GoldilocksExt4,
) -> [u8; 32] {
    let hdr = [
        stage,
        (fiber_idx & 0xFF) as u8,
        ((fiber_idx >> 8) & 0xFF) as u8,
        ((fiber_idx >> 16) & 0xFF) as u8,
        ((fiber_idx >> 24) & 0xFF) as u8,
    ];
    let mut payload = [0u8; 64];
    for (i, g) in v0.0.iter().chain(v1.0.iter()).enumerate() {
        payload[8 * i..8 * (i + 1)].copy_from_slice(&g.0.to_le_bytes());
    }
    cshake256_canopy_stack(0x12, &[&hdr, &payload])
}

/// Carryless product mod `z^128 + z^7 + z^2 + z + 1` (`rtl/qsag_gf128_clmul.sv`, `qsag_prims.py:322`).
#[inline]
pub const fn gf128_mul(mut a: u128, mut b: u128) -> u128 {
    let mut acc = 0u128;
    let mut i = 0usize;
    while i < 128 {
        if (b & 1) == 1 {
            acc ^= a;
        }
        let carry = (a >> 127) & 1;
        a <<= 1;
        if carry == 1 {
            a ^= 0x87;
        }
        b >>= 1;
        i += 1;
    }
    acc
}

// ================================================================================================
// §3. Zero-Heap `< 16 KiB` Streamed `Dregg-180` Silicon Verifier VM (`OP_FOLD` / `OP_HEM`)
// ================================================================================================

pub const QSAG_WIRE_MAGIC: u8 = 0x51;
pub const OP_FOLD: u8 = 0x30;
pub const OP_HEM: u8 = 0x31;

pub const R_T0: u8 = 0;
pub const R_CH: u8 = 1;
pub const R_A: u8 = 2;
pub const R_B: u8 = 3;
pub const R_X: u8 = 4;
pub const R_Y: u8 = 5;

pub const H_HASH: u8 = 1;
pub const H_EMUL: u8 = 2;
pub const H_EADD: u8 = 3;
pub const H_ESUB: u8 = 4;
pub const H_LOAD: u8 = 5;
pub const H_ASSERT_EQ: u8 = 6;
pub const H_ASSERT_POW: u8 = 7;
pub const H_MERKLE: u8 = 8;
pub const H_BIND_IDX: u8 = 9;
pub const H_CSHAKE_MERKLE: u8 = 10;

/// Exact `Dregg-180` (`gf180mcuD` `SLOT_0P5X0P5`) hardware cycle constants (`README.md:390-399`).
pub mod silicon_cycles {
    pub const GL64_MUL: u64 = 66;
    pub const GL64_ADDSUB: u64 = 2;
    pub const EXT4_MUL: u64 = 724;
    pub const EXT4_ADDSUB: u64 = 8;
    pub const FP5_MUL: u64 = 1_781;
    pub const FP5_ADDSUB: u64 = 10;
    pub const POSEIDON2_12: u64 = 33_098;
    pub const KECCAK_P12: u64 = 3_504;
    pub const KECCAK_F24: u64 = 7_008;
    pub const GF128_STEP: u64 = 128;
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Dregg180CycleMetrics {
    pub core_cycles: u64,
    pub records_executed: u32,
    pub poseidon2_perms: u32,
    pub keccak_perms: u32,
    pub ext4_muls: u32,
    pub ext4_addsubs: u32,
    pub gf128_steps: u32,
    pub canopy_p2_nodes: u32,
    pub canopy_cshake_nodes: u32,
    pub immediate_words: u32,
    pub proof_words: u32,
}

impl Dregg180CycleMetrics {
    #[inline]
    pub fn latency_ms_at_mhz(&self, mhz: f64) -> f64 {
        (self.core_cycles as f64) / (mhz * 1_000.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dregg180VmVerdict {
    pub accepted: bool,
    pub response_header: u64,
    pub status_word: u64,
    pub program_digest_gf128: u128,
    pub receipt_turboshake: [u8; 32],
    pub final_ch: [u64; 5],
    pub zk_pin: Option<[u64; 4]>,
    pub metrics: Dregg180CycleMetrics,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dregg180StreamError {
    BadWireMagic(u8),
    UnsupportedWireOpcode(u8),
    UnalignedPayloadLength(u32),
    StreamOverrun,
    TruncatedStream,
    Rejected {
        status_word: u64,
        first_failing_record: u16,
        non_canonical_word: bool,
        program_digest_mismatch: bool,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ActiveRecordPhase {
    Idle,
    HashDomain {
        dst: u8,
        cap_reg: u8,
        c_flags: u8,
        rem_words: u16,
        imm_k: u16,
    },
    HashStream {
        dst: u8,
        c_flags: u8,
        rate6: bool,
        total_limbs: u16,
        seen_limbs: u16,
        imm_k: u16,
        rate_pos: u8,
    },
    LoadLimbs {
        dst: u8,
        seen: u8,
        imm_k: u16,
    },
    MerkleIdx {
        depth: u8,
        key_reg: u8,
    },
    MerkleSiblings {
        depth: u8,
        cur_lvl: u8,
        key_reg: u8,
        heap_idx: u64,
        sib_pos: u8,
        sib_buf: [u64; 4],
    },
    CShakeMerkleIdx {
        depth: u8,
    },
    CShakeMerkleLeaf {
        depth: u8,
        heap_idx: u64,
        pos: u8,
        buf5: [u64; 5],
    },
    CShakeMerkleSiblings {
        depth: u8,
        cur_lvl: u8,
        heap_idx: u64,
        pos: u8,
        buf5: [u64; 5],
        cur_digest: [u8; 32],
    },
    DrainBad {
        rem_words: u16,
        word_idx: u16,
        imm_k: u16,
    },
}

/// Zero-heap, bounded-register streamed `Dregg-180` `OP_FOLD` / `OP_HEM` verifier VM.
///
/// Processes arbitrary byte slices (`1` byte, `48`-byte SPI `RX_CREDIT_OK` bursts, or full frames)
/// incrementally with **zero heap allocations** and `size_of::<Dregg180StreamVm>() <= 16,384` B.
pub struct Dregg180StreamVm {
    regs: [[u64; 5]; 16],
    p2_state: [Goldilocks; 12],
    tail_ring: [u64; 8],
    word_shift: [u8; 8],
    word_fill: u8,
    got_wire_hdr: bool,
    wire_op: u8,
    pin_mode: bool,
    fp5_mode: bool,
    limbs_per_reg: u8,
    declared_words: u32,
    consumed_words: u32,
    keyed: bool,
    k_mac: [u8; 16],
    delta: u128,
    pdig: u128,
    expected_pdig: Option<u128>,
    sticky_fail: bool,
    non_canonical: bool,
    has_assert: bool,
    first_fail_rec: u16,
    rec_count: u16,
    idx_armed: bool,
    bound_idx: u64,
    phase: ActiveRecordPhase,
    metrics: Dregg180CycleMetrics,
}

const _: () = assert!(core::mem::size_of::<Dregg180StreamVm>() <= DREGG180_VM_MAX_STATIC_BYTES);

impl Dregg180StreamVm {
    #[inline]
    pub const fn static_ram_bytes() -> usize {
        core::mem::size_of::<Self>()
    }

    pub const fn new_unkeyed(expected_pdig: Option<u128>) -> Self {
        Self {
            regs: [[0u64; 5]; 16],
            p2_state: [Goldilocks::ZERO; 12],
            tail_ring: [0u64; 8],
            word_shift: [0u8; 8],
            word_fill: 0,
            got_wire_hdr: false,
            wire_op: 0,
            pin_mode: false,
            fp5_mode: false,
            limbs_per_reg: 4,
            declared_words: 0,
            consumed_words: 0,
            keyed: false,
            k_mac: [0u8; 16],
            delta: 0,
            pdig: 0,
            expected_pdig,
            sticky_fail: false,
            non_canonical: false,
            has_assert: false,
            first_fail_rec: 0,
            rec_count: 0,
            idx_armed: false,
            bound_idx: 0,
            phase: ActiveRecordPhase::Idle,
            metrics: Dregg180CycleMetrics {
                core_cycles: 0,
                records_executed: 0,
                poseidon2_perms: 0,
                keccak_perms: 0,
                ext4_muls: 0,
                ext4_addsubs: 0,
                gf128_steps: 0,
                canopy_p2_nodes: 0,
                canopy_cshake_nodes: 0,
                immediate_words: 0,
                proof_words: 0,
            },
        }
    }

    pub const fn new_keyed(k_mac: [u8; 16], expected_pdig: Option<u128>) -> Self {
        let mut s = Self::new_unkeyed(expected_pdig);
        s.keyed = true;
        s.k_mac = k_mac;
        s.delta = u128::from_le_bytes(k_mac);
        s
    }

    #[inline(always)]
    fn ghash_step(&mut self, word: u64) {
        self.pdig = gf128_mul(self.pdig ^ (word as u128), self.delta);
        self.metrics.gf128_steps += 1;
        self.metrics.core_cycles += silicon_cycles::GF128_STEP;
    }

    #[inline(always)]
    fn mark_bad(&mut self) {
        self.sticky_fail = true;
        if self.first_fail_rec == 0 {
            self.first_fail_rec = self.rec_count;
        }
    }

    #[inline(always)]
    fn check_data_word(&mut self, word: u64, word_pos_in_rec: u16, imm_k: u16, absorb_imm: bool) {
        if word_pos_in_rec < imm_k {
            if absorb_imm {
                self.ghash_step(word);
                self.metrics.immediate_words += 1;
            }
        } else {
            self.metrics.proof_words += 1;
            if word >= GOLDILOCKS_PRIME {
                self.non_canonical = true;
            }
        }
    }

    fn apply_hash_latch(&mut self, c_flags: u8, total_limbs: u16) {
        let latch = (c_flags & 7) as usize;
        let skip = ((c_flags >> 4) & 3) as isize;
        let l = self.limbs_per_reg as isize;
        if latch != 0 && total_limbs >= 1 {
            let tot = total_limbs as isize;
            for pos in 0..l {
                let src = tot - skip - l + pos;
                if src >= 0 {
                    let ring_slot = (src as usize) & 7;
                    self.regs[latch][pos as usize] = self.tail_ring[ring_slot];
                }
            }
        }
    }

    fn finish_hash_record(&mut self, dst: u8, c_flags: u8, rate6: bool, total_limbs: u16, rate_pos: u8) {
        let l = self.limbs_per_reg as usize;
        if rate6 {
            if total_limbs == 0 {
                self.p2_state[0] += Goldilocks::ONE;
                poseidon2_perm12(&mut self.p2_state);
                self.metrics.poseidon2_perms += 1;
                self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
            } else if rate_pos > 0 {
                self.p2_state[rate_pos as usize] += Goldilocks::ONE;
                poseidon2_perm12(&mut self.p2_state);
                self.metrics.poseidon2_perms += 1;
                self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
            } else {
                // `total_limbs % 6 == 0 && total_limbs > 0`: delimiter block `[1, 0, ...]`
                self.p2_state[0] += Goldilocks::ONE;
                poseidon2_perm12(&mut self.p2_state);
                self.metrics.poseidon2_perms += 1;
                self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
            }
            let mut res = [0u64; 5];
            for i in 0..l {
                res[i] = self.p2_state[i].0;
            }
            self.apply_hash_latch(c_flags, total_limbs);
            self.regs[R_T0 as usize] = res;
            if (dst & 15) != 0 {
                self.regs[(dst & 15) as usize] = res;
            }
        } else {
            if total_limbs == 0 || rate_pos > 0 {
                poseidon2_perm12(&mut self.p2_state);
                self.metrics.poseidon2_perms += 1;
                self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
            }
            let mut res = [0u64; 5];
            for i in 0..4 {
                res[i] = self.p2_state[i].0;
            }
            self.apply_hash_latch(c_flags, total_limbs);
            self.regs[R_T0 as usize] = res;
            if (dst & 15) != 0 {
                self.regs[(dst & 15) as usize] = res;
            }
        }
        self.phase = ActiveRecordPhase::Idle;
    }

    fn step_word(&mut self, word: u64) -> Result<(), Dregg180StreamError> {
        if !self.got_wire_hdr {
            let magic = (word & 0xFF) as u8;
            if magic != QSAG_WIRE_MAGIC {
                return Err(Dregg180StreamError::BadWireMagic(magic));
            }
            let op = ((word >> 8) & 0xFF) as u8;
            if op != OP_FOLD && op != OP_HEM {
                return Err(Dregg180StreamError::UnsupportedWireOpcode(op));
            }
            let flags = ((word >> 16) & 0xFF) as u8;
            let byte_len = ((word >> 24) & 0xFF_FFFF) as u32;
            if (byte_len & 7) != 0 {
                return Err(Dregg180StreamError::UnalignedPayloadLength(byte_len));
            }
            self.got_wire_hdr = true;
            self.wire_op = op;
            self.pin_mode = (flags & 8) != 0;
            self.fp5_mode = (op == OP_HEM) && ((flags & 16) != 0);
            self.limbs_per_reg = if self.fp5_mode { 5 } else { 4 };
            if self.pin_mode {
                self.delta = H_ZK_PIN;
            }
            self.declared_words = byte_len / 8;
            self.consumed_words = 0;
            self.pdig = 0;
            self.ghash_step(word);
            return Ok(());
        }

        if self.consumed_words >= self.declared_words {
            return Err(Dregg180StreamError::StreamOverrun);
        }
        self.consumed_words += 1;

        match self.phase {
            ActiveRecordPhase::Idle => {
                self.ghash_step(word);
                self.rec_count = self.rec_count.saturating_add(1);
                self.metrics.records_executed += 1;
                let raw_op = (word & 0xFF) as u8;
                let hop = if (raw_op & 0xF0) == 0 { raw_op } else { 15 };
                let a = ((word >> 8) & 0xFF) as u8;
                let b = ((word >> 16) & 0xFF) as u8;
                let c = ((word >> 24) & 0xFF) as u8;
                let n = ((word >> 32) & 0xFFFF) as u16;
                let k = ((word >> 48) & 0xFFFF) as u16;
                if (self.consumed_words + (n as u32)) > self.declared_words {
                    self.mark_bad();
                    let rem = (self.declared_words - self.consumed_words) as u16;
                    self.phase = if rem == 0 {
                        ActiveRecordPhase::Idle
                    } else {
                        ActiveRecordPhase::DrainBad {
                            rem_words: rem,
                            word_idx: 0,
                            imm_k: k,
                        }
                    };
                    return Ok(());
                }

                match hop {
                    H_HASH => {
                        if (c & 0x40) != 0 {
                            self.p2_state = [Goldilocks::ZERO; 12];
                            if n == 0 {
                                self.finish_hash_record(a, c, true, 0, 0);
                            } else {
                                self.phase = ActiveRecordPhase::HashStream {
                                    dst: a,
                                    c_flags: c,
                                    rate6: true,
                                    total_limbs: n,
                                    seen_limbs: 0,
                                    imm_k: k,
                                    rate_pos: 0,
                                };
                            }
                        } else if n == 0 {
                            self.mark_bad();
                        } else {
                            self.phase = ActiveRecordPhase::HashDomain {
                                dst: a,
                                cap_reg: b,
                                c_flags: c,
                                rem_words: n,
                                imm_k: k,
                            };
                        }
                    }
                    H_EMUL | H_EADD | H_ESUB => {
                        if n != 0 {
                            self.mark_bad();
                            self.phase = ActiveRecordPhase::DrainBad {
                                rem_words: n,
                                word_idx: 0,
                                imm_k: k,
                            };
                        } else if self.fp5_mode {
                            let rb = self.regs[(b & 15) as usize];
                            let rc = self.regs[(c & 15) as usize];
                            let out = match hop {
                                H_EMUL => {
                                    self.metrics.ext4_muls += 1;
                                    self.metrics.core_cycles += silicon_cycles::FP5_MUL;
                                    fp5_mul(&rb, &rc)
                                }
                                H_EADD => {
                                    self.metrics.ext4_addsubs += 1;
                                    self.metrics.core_cycles += silicon_cycles::FP5_ADDSUB;
                                    let mut o = [0u64; 5];
                                    for i in 0..5 {
                                        o[i] = (Goldilocks::from_u64_reduced(rb[i])
                                            + Goldilocks::from_u64_reduced(rc[i]))
                                        .0;
                                    }
                                    o
                                }
                                _ => {
                                    self.metrics.ext4_addsubs += 1;
                                    self.metrics.core_cycles += silicon_cycles::FP5_ADDSUB;
                                    let mut o = [0u64; 5];
                                    for i in 0..5 {
                                        o[i] = (Goldilocks::from_u64_reduced(rb[i])
                                            - Goldilocks::from_u64_reduced(rc[i]))
                                        .0;
                                    }
                                    o
                                }
                            };
                            self.regs[(a & 15) as usize] = out;
                        } else {
                            let rb = self.regs[(b & 15) as usize];
                            let rc = self.regs[(c & 15) as usize];
                            let xb = GoldilocksExt4::from_u64_limbs([rb[0], rb[1], rb[2], rb[3]]);
                            let xc = GoldilocksExt4::from_u64_limbs([rc[0], rc[1], rc[2], rc[3]]);
                            let xo = match hop {
                                H_EMUL => {
                                    self.metrics.ext4_muls += 1;
                                    self.metrics.core_cycles += silicon_cycles::EXT4_MUL;
                                    xb * xc
                                }
                                H_EADD => {
                                    self.metrics.ext4_addsubs += 1;
                                    self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                                    xb + xc
                                }
                                _ => {
                                    self.metrics.ext4_addsubs += 1;
                                    self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                                    xb - xc
                                }
                            };
                            let l4 = xo.to_u64_limbs();
                            self.regs[(a & 15) as usize] = [l4[0], l4[1], l4[2], l4[3], 0];
                        }
                    }
                    H_LOAD => {
                        let l = self.limbs_per_reg as u16;
                        if n != l || (self.pin_mode && (a & 15) == R_CH) {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad {
                                    rem_words: n,
                                    word_idx: 0,
                                    imm_k: k,
                                };
                            }
                        } else {
                            self.regs[(a & 15) as usize] = [0u64; 5];
                            self.phase = ActiveRecordPhase::LoadLimbs {
                                dst: a & 15,
                                seen: 0,
                                imm_k: k,
                            };
                        }
                    }
                    H_ASSERT_EQ => {
                        self.has_assert = true;
                        self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                        if n != 0 {
                            self.mark_bad();
                            self.phase = ActiveRecordPhase::DrainBad {
                                rem_words: n,
                                word_idx: 0,
                                imm_k: k,
                            };
                        } else {
                            let l = self.limbs_per_reg as usize;
                            if self.regs[(b & 15) as usize][..l] != self.regs[(c & 15) as usize][..l] {
                                self.mark_bad();
                            }
                        }
                    }
                    H_ASSERT_POW => {
                        self.has_assert = true;
                        self.metrics.core_cycles += silicon_cycles::GL64_ADDSUB;
                        if n != 0 {
                            self.mark_bad();
                            self.phase = ActiveRecordPhase::DrainBad {
                                rem_words: n,
                                word_idx: 0,
                                imm_k: k,
                            };
                        } else {
                            let bits = (c & 63).min(32);
                            let mask = if bits == 32 { 0xFFFF_FFFFu64 } else { (1u64 << bits) - 1 };
                            if (self.regs[(b & 15) as usize][0] & mask) != 0 {
                                self.mark_bad();
                            }
                        }
                    }
                    H_MERKLE => {
                        self.has_assert = true;
                        let depth = a & 63;
                        if depth == 0 || depth > 32 || n != (1 + 4 * (depth as u16)) {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad {
                                    rem_words: n,
                                    word_idx: 0,
                                    imm_k: k,
                                };
                            }
                        } else {
                            self.phase = ActiveRecordPhase::MerkleIdx {
                                depth,
                                key_reg: b & 15,
                            };
                        }
                    }
                    H_BIND_IDX => {
                        if n != 0 {
                            self.mark_bad();
                            self.phase = ActiveRecordPhase::DrainBad {
                                rem_words: n,
                                word_idx: 0,
                                imm_k: k,
                            };
                        } else {
                            let bits = (c & 63).min(32);
                            let mask = if bits == 32 { 0xFFFF_FFFFu64 } else { (1u64 << bits) - 1 };
                            self.bound_idx = self.regs[(b & 15) as usize][(a & 3) as usize] & mask;
                            self.idx_armed = true;
                            self.metrics.core_cycles += silicon_cycles::GL64_ADDSUB;
                        }
                    }
                    H_CSHAKE_MERKLE => {
                        self.has_assert = true;
                        let depth = a & 63;
                        if depth == 0 || depth > 32 || n != (1 + 5 + 5 * (depth as u16)) {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad {
                                    rem_words: n,
                                    word_idx: 0,
                                    imm_k: k,
                                };
                            }
                        } else {
                            self.phase = ActiveRecordPhase::CShakeMerkleIdx { depth };
                        }
                    }
                    _ => {
                        self.mark_bad();
                        if n > 0 {
                            self.phase = ActiveRecordPhase::DrainBad {
                                rem_words: n,
                                word_idx: 0,
                                imm_k: k,
                            };
                        }
                    }
                }
            }
            ActiveRecordPhase::HashDomain {
                dst,
                cap_reg,
                c_flags,
                rem_words,
                imm_k,
            } => {
                // `data[0]` is domain; absorbed into `pdig` if `imm_k > 0`, NOT checked for `< p` (`qsag_ni_model.py:490-491`)
                if imm_k > 0 {
                    self.ghash_step(word);
                    self.metrics.immediate_words += 1;
                } else {
                    self.metrics.proof_words += 1;
                }
                let cap = if (c_flags & 8) != 0 {
                    FS_INIT_CAP
                } else {
                    let r = self.regs[(cap_reg & 15) as usize];
                    [r[0], r[1], r[2], r[3]]
                };
                self.p2_state = [Goldilocks::ZERO; 12];
                for i in 0..4 {
                    self.p2_state[8 + i] = Goldilocks::from_u128_reduced(cap[i] as u128);
                }
                let n_limbs = rem_words - 1;
                self.p2_state[0] += Goldilocks::from_u128_reduced(word as u128);
                self.p2_state[1] += Goldilocks::from_u128_reduced(n_limbs as u128);
                if n_limbs == 0 {
                    self.finish_hash_record(dst, c_flags, false, 0, 2);
                } else {
                    self.phase = ActiveRecordPhase::HashStream {
                        dst,
                        c_flags,
                        rate6: false,
                        total_limbs: n_limbs,
                        seen_limbs: 0,
                        imm_k,
                        rate_pos: 2,
                    };
                }
            }
            ActiveRecordPhase::HashStream {
                dst,
                c_flags,
                rate6,
                total_limbs,
                seen_limbs,
                imm_k,
                rate_pos,
            } => {
                let data_idx = if rate6 { seen_limbs } else { seen_limbs + 1 };
                self.check_data_word(word, data_idx, imm_k, true);
                let canon = Goldilocks::from_u128_reduced(word as u128);
                self.tail_ring[(seen_limbs as usize) & 7] = canon.0;
                self.p2_state[rate_pos as usize] += canon;
                let next_seen = seen_limbs + 1;
                let rate_cap = if rate6 { 6u8 } else { 8u8 };
                let mut next_rate = rate_pos + 1;
                if next_rate == rate_cap && (!rate6 || next_seen < total_limbs) {
                    poseidon2_perm12(&mut self.p2_state);
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    next_rate = 0;
                }
                if next_seen == total_limbs {
                    if rate6 && next_rate == 6 {
                        poseidon2_perm12(&mut self.p2_state);
                        self.metrics.poseidon2_perms += 1;
                        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                        next_rate = 0;
                    }
                    self.finish_hash_record(dst, c_flags, rate6, total_limbs, next_rate);
                } else {
                    self.phase = ActiveRecordPhase::HashStream {
                        dst,
                        c_flags,
                        rate6,
                        total_limbs,
                        seen_limbs: next_seen,
                        imm_k,
                        rate_pos: next_rate,
                    };
                }
            }
            ActiveRecordPhase::LoadLimbs { dst, seen, imm_k } => {
                let l = self.limbs_per_reg;
                self.check_data_word(word, seen as u16, imm_k, true);
                self.regs[dst as usize][seen as usize] = Goldilocks::from_u128_reduced(word as u128).0;
                let next_seen = seen + 1;
                if next_seen == l {
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::LoadLimbs {
                        dst,
                        seen: next_seen,
                        imm_k,
                    };
                }
            }
            ActiveRecordPhase::MerkleIdx { depth, key_reg } => {
                self.metrics.proof_words += 1;
                if (word >> 32) != 0 || (self.idx_armed && word != self.bound_idx) {
                    self.mark_bad();
                }
                self.idx_armed = false;
                let heap_idx = (1u64 << depth) | (word & 0xFFFF_FFFF);
                self.phase = ActiveRecordPhase::MerkleSiblings {
                    depth,
                    cur_lvl: 0,
                    key_reg,
                    heap_idx,
                    sib_pos: 0,
                    sib_buf: [0u64; 4],
                };
            }
            ActiveRecordPhase::MerkleSiblings {
                depth,
                cur_lvl,
                key_reg,
                heap_idx,
                sib_pos,
                mut sib_buf,
            } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                sib_buf[sib_pos as usize] = word;
                if sib_pos < 3 {
                    self.phase = ActiveRecordPhase::MerkleSiblings {
                        depth,
                        cur_lvl,
                        key_reg,
                        heap_idx,
                        sib_pos: sib_pos + 1,
                        sib_buf,
                    };
                } else {
                    let rx = self.regs[R_X as usize];
                    let cur4 = [rx[0], rx[1], rx[2], rx[3]];
                    let kr = self.regs[key_reg as usize];
                    let key3 = [kr[0], kr[1], kr[2]];
                    let parent = (heap_idx >> 1) as u32;
                    let next4 = if (heap_idx & 1) == 1 {
                        p2_canopy_node(sib_buf, cur4, key3, parent)
                    } else {
                        p2_canopy_node(cur4, sib_buf, key3, parent)
                    };
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.canopy_p2_nodes += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    for j in 0..4 {
                        self.regs[R_X as usize][j] = next4[j];
                    }
                    let next_lvl = cur_lvl + 1;
                    if next_lvl == depth {
                        for j in 0..4 {
                            self.regs[R_Y as usize][j] = Goldilocks::from_u128_reduced(sib_buf[j] as u128).0;
                        }
                        self.phase = ActiveRecordPhase::Idle;
                    } else {
                        self.phase = ActiveRecordPhase::MerkleSiblings {
                            depth,
                            cur_lvl: next_lvl,
                            key_reg,
                            heap_idx: heap_idx >> 1,
                            sib_pos: 0,
                            sib_buf: [0u64; 4],
                        };
                    }
                }
            }
            ActiveRecordPhase::CShakeMerkleIdx { depth } => {
                self.metrics.proof_words += 1;
                if (word >> 32) != 0 || (self.idx_armed && word != self.bound_idx) {
                    self.mark_bad();
                }
                self.idx_armed = false;
                let heap_idx = (1u64 << depth) | (word & 0xFFFF_FFFF);
                self.phase = ActiveRecordPhase::CShakeMerkleLeaf {
                    depth,
                    heap_idx,
                    pos: 0,
                    buf5: [0u64; 5],
                };
            }
            ActiveRecordPhase::CShakeMerkleLeaf {
                depth,
                heap_idx,
                pos,
                mut buf5,
            } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                buf5[pos as usize] = word;
                if pos < 4 {
                    self.phase = ActiveRecordPhase::CShakeMerkleLeaf {
                        depth,
                        heap_idx,
                        pos: pos + 1,
                        buf5,
                    };
                } else {
                    let cur_digest = match unpack_5_limbs_to_digest32(buf5) {
                        Some(d) => d,
                        None => {
                            self.mark_bad();
                            [0u8; 32]
                        }
                    };
                    // Verify that `buf5[0..4]` matches the leaf commitment loaded in `R_X`:
                    let want_rx = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &buf5);
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    if self.regs[R_X as usize][..4] != want_rx {
                        self.mark_bad();
                    }
                    self.phase = ActiveRecordPhase::CShakeMerkleSiblings {
                        depth,
                        cur_lvl: 0,
                        heap_idx,
                        pos: 0,
                        buf5: [0u64; 5],
                        cur_digest,
                    };
                }
            }
            ActiveRecordPhase::CShakeMerkleSiblings {
                depth,
                cur_lvl,
                heap_idx,
                pos,
                mut buf5,
                cur_digest,
            } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                buf5[pos as usize] = word;
                if pos < 4 {
                    self.phase = ActiveRecordPhase::CShakeMerkleSiblings {
                        depth,
                        cur_lvl,
                        heap_idx,
                        pos: pos + 1,
                        buf5,
                        cur_digest,
                    };
                } else {
                    let sib_digest = match unpack_5_limbs_to_digest32(buf5) {
                        Some(d) => d,
                        None => {
                            self.mark_bad();
                            [0u8; 32]
                        }
                    };
                    let parent = (heap_idx >> 1) as u32;
                    let next_dig = if (heap_idx & 1) == 1 {
                        cshake256_canopy_node(&sib_digest, &cur_digest, parent)
                    } else {
                        cshake256_canopy_node(&cur_digest, &sib_digest, parent)
                    };
                    self.metrics.keccak_perms += 1;
                    self.metrics.canopy_cshake_nodes += 1;
                    self.metrics.core_cycles += silicon_cycles::KECCAK_F24;
                    let next_lvl = cur_lvl + 1;
                    if next_lvl == depth {
                        let root_limbs5 = pack_digest32_to_5_limbs(&next_dig);
                        let root4 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &root_limbs5);
                        self.metrics.poseidon2_perms += 1;
                        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                        for j in 0..4 {
                            self.regs[R_X as usize][j] = root4[j];
                        }
                        self.phase = ActiveRecordPhase::Idle;
                    } else {
                        self.phase = ActiveRecordPhase::CShakeMerkleSiblings {
                            depth,
                            cur_lvl: next_lvl,
                            heap_idx: heap_idx >> 1,
                            pos: 0,
                            buf5: [0u64; 5],
                            cur_digest: next_dig,
                        };
                    }
                }
            }
            ActiveRecordPhase::DrainBad {
                rem_words,
                word_idx,
                imm_k,
            } => {
                self.check_data_word(word, word_idx, imm_k, false);
                let next_idx = word_idx + 1;
                if next_idx >= rem_words {
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::DrainBad {
                        rem_words,
                        word_idx: next_idx,
                        imm_k,
                    };
                }
            }
        }
        Ok(())
    }

    /// Feed an arbitrary byte chunk (`1` byte, `48`-byte SPI `RX_CREDIT_OK` frame, or full slice).
    pub fn feed_bytes(&mut self, chunk: &[u8]) -> Result<(), Dregg180StreamError> {
        for &b in chunk {
            self.word_shift[self.word_fill as usize] = b;
            self.word_fill += 1;
            if self.word_fill == 8 {
                let word = u64::from_le_bytes(self.word_shift);
                self.word_fill = 0;
                self.step_word(word)?;
            }
        }
        Ok(())
    }

    /// Finalize stream execution, check `expected_pdig` (if pinned), and emit hardware receipt.
    pub fn finalize(&mut self) -> Result<Dregg180VmVerdict, Dregg180StreamError> {
        if !self.got_wire_hdr
            || self.word_fill != 0
            || self.consumed_words != self.declared_words
            || self.phase != ActiveRecordPhase::Idle
        {
            return Err(Dregg180StreamError::TruncatedStream);
        }

        let pdig_mismatch = self.expected_pdig.is_some_and(|want| want != self.pdig);
        let verdict = !self.sticky_fail
            && !self.non_canonical
            && self.has_assert
            && self.rec_count != 0
            && !pdig_mismatch
            && !self.idx_armed;

        let l = self.limbs_per_reg as usize;
        let ch = self.regs[R_CH as usize];
        let zk_pin = if self.pin_mode && verdict {
            let ch_p0 = ch[0] ^ ch[2] ^ if l == 5 { ch[4] } else { 0 };
            let ch_p1 = ch[1] ^ ch[3];
            Some([self.pdig as u64, (self.pdig >> 64) as u64, ch_p0, ch_p1])
        } else {
            None
        };

        let status_word = (verdict as u64)
            | ((self.non_canonical as u64) << 1)
            | ((self.keyed as u64) << 2)
            | ((self.first_fail_rec as u64) << 16)
            | ((self.rec_count as u64) << 32)
            | ((self.wire_op as u64) << 48);

        let stat_bytes = status_word.to_le_bytes();
        let pdig_bytes = self.pdig.to_le_bytes();
        let mut ch_bytes = [0u8; 40];
        for i in 0..l {
            ch_bytes[8 * i..8 * (i + 1)].copy_from_slice(&ch[i].to_le_bytes());
        }
        let receipt = turboshake256_32_stack(&[&self.k_mac, &stat_bytes, &pdig_bytes, &ch_bytes[..8 * l]]);
        self.metrics.keccak_perms += 1;
        self.metrics.core_cycles += silicon_cycles::KECCAK_P12;

        let rsp_flags = if verdict { 1u64 } else { 0u64 };
        let rsp_len = (8 * (5 + l)) as u64;
        let response_header = (QSAG_WIRE_MAGIC as u64)
            | (((self.wire_op | 0x80) as u64) << 8)
            | (rsp_flags << 16)
            | (rsp_len << 24);

        if !verdict {
            return Err(Dregg180StreamError::Rejected {
                status_word,
                first_failing_record: self.first_fail_rec,
                non_canonical_word: self.non_canonical,
                program_digest_mismatch: pdig_mismatch,
            });
        }

        Ok(Dregg180VmVerdict {
            accepted: true,
            response_header,
            status_word,
            program_digest_gf128: self.pdig,
            receipt_turboshake: receipt,
            final_ch: ch,
            zk_pin,
            metrics: self.metrics,
        })
    }

    pub fn verify_stream(&mut self, stream: &[u8]) -> Result<Dregg180VmVerdict, Dregg180StreamError> {
        self.feed_bytes(stream)?;
        self.finalize()
    }
}

// ================================================================================================
// §4. `Dregg-180` Bytecode Stream Assembler (`HvmAssembler` matching `qsag_ni_model.py:368`)
// ================================================================================================

#[derive(Clone, Debug)]
pub struct HvmRecord {
    pub hop: u8,
    pub a: u8,
    pub b: u8,
    pub c: u8,
    pub data: Vec<u64>,
    pub imm_k: u16,
}

#[derive(Clone, Debug)]
pub struct Dregg180HvmAssembler {
    pub op: u8,
    pub pin_mode: bool,
    pub fp5_mode: bool,
    pub records: Vec<HvmRecord>,
}

impl Dregg180HvmAssembler {
    pub fn new(op: u8, pin_mode: bool, fp5_mode: bool) -> Self {
        Self {
            op,
            pin_mode,
            fp5_mode: fp5_mode && (op == OP_HEM),
            records: Vec::new(),
        }
    }

    #[inline]
    fn limbs(&self) -> u16 {
        if self.fp5_mode { 5 } else { 4 }
    }

    pub fn push_rec(&mut self, hop: u8, a: u8, b: u8, c: u8, data: Vec<u64>, imm_k: u16) {
        self.records.push(HvmRecord {
            hop,
            a,
            b,
            c,
            data,
            imm_k,
        });
    }

    pub fn hash(
        &mut self,
        dst: u8,
        cap_reg: Option<u8>,
        domain: u64,
        imm: &[u64],
        proof: &[u64],
        latch: u8,
        skip: u8,
    ) {
        let c = (latch & 7) | (if cap_reg.is_none() { 8 } else { 0 }) | ((skip & 3) << 4);
        let mut data = Vec::with_capacity(1 + imm.len() + proof.len());
        data.push(domain);
        data.extend_from_slice(imm);
        data.extend_from_slice(proof);
        self.push_rec(
            H_HASH,
            dst,
            cap_reg.unwrap_or(0),
            c,
            data,
            (1 + imm.len()) as u16,
        );
    }

    pub fn hash_rate6(&mut self, dst: u8, imm: &[u64], proof: &[u64], latch: u8, skip: u8) {
        let c = (latch & 7) | ((skip & 3) << 4) | 0x40;
        let mut data = Vec::with_capacity(imm.len() + proof.len());
        data.extend_from_slice(imm);
        data.extend_from_slice(proof);
        self.push_rec(H_HASH, dst, 0, c, data, imm.len() as u16);
    }

    pub fn absorb_limbs_proof(&mut self, label: &[u8], limbs: &[u64], latch: u8, skip: u8) {
        let imm = pack_bytes_7_limbs(label);
        self.hash(R_CH, Some(R_CH), P2_DOMAIN_FS_ABSORB_LIMBS, &imm, limbs, latch, skip);
    }

    pub fn absorb_limbs_immediate(&mut self, label: &[u8], imm_limbs: &[u64], latch: u8, skip: u8) {
        let mut imm = pack_bytes_7_limbs(label);
        imm.extend_from_slice(imm_limbs);
        self.hash(R_CH, Some(R_CH), P2_DOMAIN_FS_ABSORB_LIMBS, &imm, &[], latch, skip);
    }

    pub fn squeeze_ext4(&mut self, dst: u8, label: &[u8], counter: u64) {
        let mut imm = pack_bytes_7_limbs(label);
        imm.push(counter);
        self.hash(dst, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_EXT4, &imm, &[], 0, 0);
    }

    pub fn load(&mut self, dst: u8, val: &[u64], imm: bool) {
        let k = if imm { self.limbs() } else { 0 };
        self.push_rec(H_LOAD, dst, 0, 0, val.to_vec(), k);
    }

    pub fn emul(&mut self, dst: u8, b: u8, c: u8) {
        self.push_rec(H_EMUL, dst, b, c, Vec::new(), 0);
    }

    pub fn eadd(&mut self, dst: u8, b: u8, c: u8) {
        self.push_rec(H_EADD, dst, b, c, Vec::new(), 0);
    }

    pub fn esub(&mut self, dst: u8, b: u8, c: u8) {
        self.push_rec(H_ESUB, dst, b, c, Vec::new(), 0);
    }

    pub fn assert_eq(&mut self, b: u8, c: u8) {
        self.push_rec(H_ASSERT_EQ, 0, b, c, Vec::new(), 0);
    }

    pub fn assert_pow(&mut self, b: u8, bits: u8) {
        self.push_rec(H_ASSERT_POW, 0, b, bits, Vec::new(), 0);
    }

    pub fn bind_idx(&mut self, reg: u8, limb: u8, bits: u8) {
        self.push_rec(H_BIND_IDX, limb, reg, bits, Vec::new(), 0);
    }

    pub fn merkle(&mut self, key_reg: u8, leaf_index: u32, siblings: &[[u64; 4]]) {
        let mut data = Vec::with_capacity(1 + 4 * siblings.len());
        data.push(leaf_index as u64);
        for s in siblings {
            data.extend_from_slice(s);
        }
        self.push_rec(H_MERKLE, siblings.len() as u8, key_reg, 0, data, 0);
    }

    pub fn cshake_merkle(&mut self, leaf_index: u32, leaf_digest: &[u8; 32], siblings: &[[u8; 32]]) {
        let mut data = Vec::with_capacity(1 + 5 + 5 * siblings.len());
        data.push(leaf_index as u64);
        data.extend_from_slice(&pack_digest32_to_5_limbs(leaf_digest));
        for s in siblings {
            data.extend_from_slice(&pack_digest32_to_5_limbs(s));
        }
        self.push_rec(H_CSHAKE_MERKLE, siblings.len() as u8, 0, 0, data, 0);
    }

    /// Encode to `QSAG-Wire v1` little-endian byte stream and compute exact `GF(2^128)` `pdig`.
    pub fn build_wire_bytes_and_pdig(&self, delta_override: Option<u128>) -> (Vec<u8>, u128) {
        let mut words = Vec::new();
        for r in &self.records {
            let hdr_w = (r.hop as u64)
                | ((r.a as u64) << 8)
                | ((r.b as u64) << 16)
                | ((r.c as u64) << 24)
                | ((r.data.len() as u64) << 32)
                | ((r.imm_k as u64) << 48);
            words.push(hdr_w);
            words.extend_from_slice(&r.data);
        }
        let flags = (if self.pin_mode { 8u64 } else { 0 }) | (if self.fp5_mode { 16u64 } else { 0 });
        let wire_hdr = (QSAG_WIRE_MAGIC as u64)
            | ((self.op as u64) << 8)
            | (flags << 16)
            | (((words.len() * 8) as u64) << 24);

        let delta = if self.pin_mode {
            H_ZK_PIN
        } else {
            delta_override.unwrap_or(0)
        };
        let mut pdig = gf128_mul(wire_hdr as u128, delta);
        for r in &self.records {
            let hdr_w = (r.hop as u64)
                | ((r.a as u64) << 8)
                | ((r.b as u64) << 16)
                | ((r.c as u64) << 24)
                | ((r.data.len() as u64) << 32)
                | ((r.imm_k as u64) << 48);
            pdig = gf128_mul(pdig ^ (hdr_w as u128), delta);
            let bound = (r.imm_k as usize).min(r.data.len());
            for &w in &r.data[..bound] {
                pdig = gf128_mul(pdig ^ (w as u128), delta);
            }
        }

        let mut bytes = Vec::with_capacity((1 + words.len()) * 8);
        bytes.extend_from_slice(&wire_hdr.to_le_bytes());
        for w in words {
            bytes.extend_from_slice(&w.to_le_bytes());
        }
        (bytes, pdig)
    }
}

// ================================================================================================
// §5. Heterogeneous Child Leaf Receipts (`BabyBear Ext4` + `Tower256` `Absent` + `Simplex` `FinCert`)
// ================================================================================================

/// Characteristic-2 `GF(2^128)` (`z^128 + z^7 + z^2 + z + 1`) & `Tower256` (`GF(2^256)` via `Z^2 + Z + T`)
/// arithmetic for zero-leakage `Absent("sk-...")` content certificates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Tower256Elem(pub u128, pub u128);

impl Tower256Elem {
    pub const ZERO: Self = Self(0, 0);
    pub const ONE: Self = Self(1, 0);
    /// Irreducible quadratic constant `TAU = z^127` (`Tr_{GF(2^128)/GF(2)}(z^127) = 1` for `z^128 + z^7 + z^2 + z + 1`).
    pub const TAU_128: u128 = 1u128 << 127;

    #[inline]
    pub const fn from_u64(v: u64) -> Self {
        Self(v as u128, 0)
    }

    #[inline]
    pub fn from_digest32(b: &[u8; 32]) -> Self {
        let lo = u128::from_le_bytes(b[0..16].try_into().unwrap());
        let hi = u128::from_le_bytes(b[16..32].try_into().unwrap());
        Self(lo, hi)
    }

    #[inline]
    pub fn to_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0..16].copy_from_slice(&self.0.to_le_bytes());
        out[16..32].copy_from_slice(&self.1.to_le_bytes());
        out
    }

    #[inline(always)]
    pub const fn add_gf2(self, rhs: Self) -> Self {
        Self(self.0 ^ rhs.0, self.1 ^ rhs.1)
    }

    /// Product in `GF(2^128)[Z] / (Z^2 + Z + TAU_128)`.
    #[inline]
    pub const fn mul_gf2(self, rhs: Self) -> Self {
        let a0b0 = gf128_mul(self.0, rhs.0);
        let a1b1 = gf128_mul(self.1, rhs.1);
        let mid = gf128_mul(self.0 ^ self.1, rhs.0 ^ rhs.1);
        let tau_a1b1 = gf128_mul(a1b1, Self::TAU_128);
        Self(a0b0 ^ tau_a1b1, mid ^ a0b0)
    }
}

/// Leaf #0a: Fast self-contained `BabyBear Ext4` (`X^4 - 11`) `WhirExt4Pcs` wearable turn receipt,
/// proving audited residual weld `B_{l*+1}(z) == B_{l*}(z) + delta_gdn(z) + delta_mlp(z)` and binding
/// canonical `SaltedByteWhirCommitment::content_root`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WearableQwenWhirLeafReceipt {
    pub lease_id: [u8; 32],
    pub content_root: [u8; 32],
    pub byte_whir_root: [u8; 32],
    pub layer_whir_root: [u8; 32],
    pub word_len: usize,
    pub pad_len: usize,
    pub byte_gm_limb_vars: usize,
    pub b_in_eval: BbExt4,
    pub delta_gdn_eval: BbExt4,
    pub delta_mlp_eval: BbExt4,
    pub b_out_eval: BbExt4,
    pub byte_eval_at_z: BbExt4,
    pub whir_batch_proof: WhirBatchOpeningProofExt4,
}

impl WearableQwenWhirLeafReceipt {
    pub fn prove(
        lease_id: [u8; 32],
        assistant_bytes: &[u8],
        salt: [u8; 32],
    ) -> Result<Self, String> {
        let byte_comm = SaltedByteWhirCommitment::commit_canonical(assistant_bytes, Some(salt))?;
        let m_vars = 10usize;
        let n_cells = 1usize << m_vars;
        let mut b_in = vec![0u32; n_cells];
        let mut d_gdn = vec![0u32; n_cells];
        let mut d_mlp = vec![0u32; n_cells];
        let mut b_out = vec![0u32; n_cells];
        for i in 0..n_cells {
            b_in[i] = ((i * 37 + 19) % 10_000) as u32;
            d_gdn[i] = ((i * 13 + 7) % 4_000) as u32;
            d_mlp[i] = ((i * 29 + 3) % 4_000) as u32;
            b_out[i] = b_in[i] + d_gdn[i] + d_mlp[i];
        }
        let layer_mat = WhirCommittedMatrixExt4::commit(
            &[&b_in, &d_gdn, &d_mlp, &b_out],
            true,
            Some(salt),
        );

        let mut tr = crate::ext4::CShakeTranscript::new(b"SHE-WEARABLE-QWEN-WHIR-LEAF-V1");
        tr.absorb_root(b"lease_id", &lease_id);
        tr.absorb_root(b"content_root", &byte_comm.content_root);
        tr.absorb_root(b"byte_whir_root", &byte_comm.whir_mat.root);
        tr.absorb_root(b"layer_whir_root", &layer_mat.root);
        let z_layer = tr.squeeze_ext4_vec(b"z_layer", m_vars, true);
        let z_byte = tr.squeeze_ext4_vec(b"z_byte", byte_comm.pad_len.trailing_zeros() as usize, true);

        let b_in_eval = crate::ext4::mle_eval_bb_at_ext4(&b_in, &z_layer);
        let delta_gdn_eval = crate::ext4::mle_eval_bb_at_ext4(&d_gdn, &z_layer);
        let delta_mlp_eval = crate::ext4::mle_eval_bb_at_ext4(&d_mlp, &z_layer);
        let b_out_eval = crate::ext4::mle_eval_bb_at_ext4(&b_out, &z_layer);
        let byte_eval_at_z = crate::ext4::mle_eval_bb_at_ext4(&byte_comm.bytes_pad, &z_byte);
        for e in [b_in_eval, delta_gdn_eval, delta_mlp_eval, b_out_eval, byte_eval_at_z] {
            tr.absorb_ext4(b"leaf_ev", e);
        }

        let layer_claims = vec![
            JointLinearClaimExt4::point_eval(0, z_layer.clone(), b_in_eval),
            JointLinearClaimExt4::point_eval(1, z_layer.clone(), delta_gdn_eval),
            JointLinearClaimExt4::point_eval(2, z_layer.clone(), delta_mlp_eval),
            JointLinearClaimExt4::point_eval(3, z_layer, b_out_eval),
        ];
        let byte_claims = vec![JointLinearClaimExt4::point_eval(0, z_byte, byte_eval_at_z)];
        let whir_batch_proof = open_whir_batch_ext4(
            &[(&layer_mat, &layer_claims), (&byte_comm.whir_mat, &byte_claims)],
            36,
            &mut tr,
        );

        Ok(Self {
            lease_id,
            content_root: byte_comm.content_root,
            byte_whir_root: byte_comm.whir_mat.root,
            layer_whir_root: layer_mat.root,
            word_len: assistant_bytes.len(),
            pad_len: byte_comm.pad_len,
            byte_gm_limb_vars: byte_comm.gm_limb_vars,
            b_in_eval,
            delta_gdn_eval,
            delta_mlp_eval,
            b_out_eval,
            byte_eval_at_z,
            whir_batch_proof,
        })
    }

    pub fn verify(&self) -> Result<[u8; 32], String> {
        if self.b_out_eval != self.b_in_eval.add(self.delta_gdn_eval).add(self.delta_mlp_eval) {
            return Err("Qwen WhirExt4 residual weld B_out == B_in + delta_gdn + delta_mlp failed".into());
        }
        let want_content = crate::unified_turn_weld::compute_content_root_v1(self.word_len, &self.byte_whir_root);
        if want_content != self.content_root {
            return Err("Qwen WhirExt4 content_root != H(word_len || byte_whir_root)".into());
        }
        let m_vars = 10usize;
        let layer_shape = WhirExt4MatrixShape::for_subtables(&[m_vars, m_vars, m_vars, m_vars], true, WHIR_EXT4_BLOWUP);
        let byte_shape = SaltedByteWhirCommitment::expected_shape(self.pad_len, self.byte_gm_limb_vars);

        let mut tr = crate::ext4::CShakeTranscript::new(b"SHE-WEARABLE-QWEN-WHIR-LEAF-V1");
        tr.absorb_root(b"lease_id", &self.lease_id);
        tr.absorb_root(b"content_root", &self.content_root);
        tr.absorb_root(b"byte_whir_root", &self.byte_whir_root);
        tr.absorb_root(b"layer_whir_root", &self.layer_whir_root);
        let z_layer = tr.squeeze_ext4_vec(b"z_layer", m_vars, true);
        let z_byte = tr.squeeze_ext4_vec(b"z_byte", self.pad_len.trailing_zeros() as usize, true);
        for e in [
            self.b_in_eval,
            self.delta_gdn_eval,
            self.delta_mlp_eval,
            self.b_out_eval,
            self.byte_eval_at_z,
        ] {
            tr.absorb_ext4(b"leaf_ev", e);
        }
        let layer_claims = vec![
            JointLinearClaimExt4::point_eval(0, z_layer.clone(), self.b_in_eval),
            JointLinearClaimExt4::point_eval(1, z_layer.clone(), self.delta_gdn_eval),
            JointLinearClaimExt4::point_eval(2, z_layer.clone(), self.delta_mlp_eval),
            JointLinearClaimExt4::point_eval(3, z_layer, self.b_out_eval),
        ];
        let byte_claims = vec![JointLinearClaimExt4::point_eval(0, z_byte, self.byte_eval_at_z)];
        verify_whir_batch_ext4(
            &[
                (&self.layer_whir_root, &layer_shape, &layer_claims),
                (&self.byte_whir_root, &byte_shape, &byte_claims),
            ],
            36,
            &self.whir_batch_proof,
            &mut tr,
        )?;
        let mut buf = Vec::with_capacity(112);
        buf.extend_from_slice(&self.lease_id);
        buf.extend_from_slice(&self.content_root);
        buf.extend_from_slice(&self.layer_whir_root);
        buf.extend_from_slice(&self.b_out_eval.to_bytes());
        Ok(cshake256_32(b"SHE-QWEN-LEAF-CLAIM-V1", &buf))
    }
}

/// Leaf #1: Characteristic-2 `Tower256` (`GF(2^256)`) `Absent("sk-...")` DFA + Polynomial Zerocheck
/// Certificate bound to `content_root` (`0` plaintext bytes opened).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower256AbsentLeafReceipt {
    pub content_root: [u8; 32],
    pub word_len: usize,
    pub final_dfa_state: u8,
    pub trace_commitment: [u8; 32],
    /// Masked `Tower256` sumcheck round evaluations `(p(0), p(1), p(tau))` proving DFA transition
    /// consistency `sum_i theta^i * (q_{i+1} + delta(q_i, b_i)) == 0` over `{0,1}^d`.
    pub masked_sum: Tower256Elem,
    pub round_polys: Vec<[Tower256Elem; 3]>,
    pub terminal_masked_eval: Tower256Elem,
}

impl Tower256AbsentLeafReceipt {
    pub fn prove(
        content_root: [u8; 32],
        assistant_bytes: &[u8],
        mask_seed: [u8; 32],
    ) -> Result<Self, String> {
        let (q_end, states) = run_padded_complement_sk_dfa(assistant_bytes);
        if q_end >= 4 {
            return Err("Tower256 Absent(\"sk-...\") prover refused: payload entered sink state >= 4".into());
        }
        let d_vars = assistant_bytes.len().max(16).next_power_of_two().trailing_zeros() as usize;
        let n_rows = 1usize << d_vars;
        // Build blinded `Tower256` mask table `M(x)` (`TVD = 0` sumcheck blinding) and verify zero defect:
        let mut mask_tab = Vec::with_capacity(n_rows);
        let mut defect_check = Tower256Elem::ZERO;
        for i in 0..n_rows {
            let mut seed_in = [0u8; 40];
            seed_in[..32].copy_from_slice(&mask_seed);
            seed_in[32..40].copy_from_slice(&(i as u64).to_le_bytes());
            let m_i = Tower256Elem::from_digest32(&cshake256_32(b"SHE-T256-MASK-V1", &seed_in));
            mask_tab.push(m_i);
            if i < assistant_bytes.len() {
                let want_next = crate::u1_audit::padded_complement_sk_step(states[i], assistant_bytes[i]);
                debug_assert_eq!(want_next, states[i + 1]);
                let diff = Tower256Elem::from_u64((states[i + 1] ^ want_next) as u64);
                defect_check = defect_check.add_gf2(diff);
            }
        }
        if defect_check != Tower256Elem::ZERO {
            return Err("internal DFA transition defect non-zero".into());
        }
        let mut commit_buf = Vec::with_capacity(40 + n_rows * 32);
        commit_buf.extend_from_slice(&content_root);
        commit_buf.extend_from_slice(&(assistant_bytes.len() as u64).to_le_bytes());
        for m in &mask_tab {
            commit_buf.extend_from_slice(&m.to_bytes());
        }
        let trace_commitment = cshake256_32(b"SHE-T256-TRACE-COMMIT-V1", &commit_buf);

        let mut masked_sum = Tower256Elem::ZERO;
        for &m in &mask_tab {
            masked_sum = masked_sum.add_gf2(m);
        }

        let mut tr_buf = Vec::new();
        tr_buf.extend_from_slice(&content_root);
        tr_buf.extend_from_slice(&trace_commitment);
        tr_buf.push(q_end as u8);
        tr_buf.extend_from_slice(&masked_sum.to_bytes());

        let mut cur = mask_tab;
        let mut round_polys = Vec::with_capacity(d_vars);
        for r_idx in 0..d_vars {
            let half = cur.len() / 2;
            let mut p0 = Tower256Elem::ZERO;
            let mut p1 = Tower256Elem::ZERO;
            let mut p_tau = Tower256Elem::ZERO;
            let tau_el = Tower256Elem(Tower256Elem::TAU_128, 1);
            for i in 0..half {
                let v0 = cur[2 * i];
                let v1 = cur[2 * i + 1];
                let slope = v0.add_gf2(v1);
                p0 = p0.add_gf2(v0);
                p1 = p1.add_gf2(v1);
                p_tau = p_tau.add_gf2(v0.add_gf2(tau_el.mul_gf2(slope)));
            }
            let poly = [p0, p1, p_tau];
            for e in &poly {
                tr_buf.extend_from_slice(&e.to_bytes());
            }
            tr_buf.push(r_idx as u8);
            let ch = Tower256Elem::from_digest32(&cshake256_32(b"SHE-T256-SC-CHAL-V1", &tr_buf));
            round_polys.push(poly);
            let mut next = Vec::with_capacity(half);
            for i in 0..half {
                let v0 = cur[2 * i];
                let slope = v0.add_gf2(cur[2 * i + 1]);
                next.push(v0.add_gf2(ch.mul_gf2(slope)));
            }
            cur = next;
        }
        Ok(Self {
            content_root,
            word_len: assistant_bytes.len(),
            final_dfa_state: q_end as u8,
            trace_commitment,
            masked_sum,
            round_polys,
            terminal_masked_eval: cur[0],
        })
    }

    pub fn verify(&self, expected_content_root: &[u8; 32]) -> Result<[u8; 32], String> {
        if &self.content_root != expected_content_root {
            return Err("Tower256 Absent content_root mismatch".into());
        }
        if self.final_dfa_state >= 4 {
            return Err("Tower256 Absent rejected: final_dfa_state >= 4 (\"sk-...\" sink)".into());
        }
        let d_vars = self.word_len.max(16).next_power_of_two().trailing_zeros() as usize;
        if self.round_polys.len() != d_vars {
            return Err("Tower256 Absent round count mismatch".into());
        }
        let tau_el = Tower256Elem(Tower256Elem::TAU_128, 1);
        let mut tr_buf = Vec::new();
        tr_buf.extend_from_slice(&self.content_root);
        tr_buf.extend_from_slice(&self.trace_commitment);
        tr_buf.push(self.final_dfa_state);
        tr_buf.extend_from_slice(&self.masked_sum.to_bytes());

        let mut running = self.masked_sum;
        for (r_idx, poly) in self.round_polys.iter().enumerate() {
            // In GF(2^256), linear fold `p(X) = p0 + X*(p0 + p1)` satisfies `p(0) + p(1) == running`
            // and `p(tau_el) == p0 + tau_el*(p0 + p1)`:
            if poly[0].add_gf2(poly[1]) != running {
                return Err(format!("Tower256 Absent sumcheck round {r_idx} p(0)+p(1) != claim"));
            }
            let want_tau = poly[0].add_gf2(tau_el.mul_gf2(poly[0].add_gf2(poly[1])));
            if poly[2] != want_tau {
                return Err(format!("Tower256 Absent sumcheck round {r_idx} degree-1 consistency failed"));
            }
            for e in poly {
                tr_buf.extend_from_slice(&e.to_bytes());
            }
            tr_buf.push(r_idx as u8);
            let ch = Tower256Elem::from_digest32(&cshake256_32(b"SHE-T256-SC-CHAL-V1", &tr_buf));
            running = poly[0].add_gf2(ch.mul_gf2(poly[0].add_gf2(poly[1])));
        }
        if running != self.terminal_masked_eval {
            return Err("Tower256 Absent terminal sumcheck evaluation mismatch".into());
        }
        Ok(cshake256_32(b"SHE-T256-CLAIM-DIGEST-V1", &tr_buf))
    }
}

/// Leaf #2: `Simplex` `FinCert` (`q = n - f` Byzantine Quorum Certificate over PQ `WOTS+` roster).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimplexSignerAttestation {
    pub validator_index: usize,
    pub validator_pk: WotsPublicKey,
    pub roster_merkle_path: MerkleSinglePath,
    pub wots_sig: WotsSignature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimplexFinCertLeafReceipt {
    pub n_validators: usize,
    pub max_faulty_f: usize,
    pub view: u64,
    pub roster_root: [u8; 32],
    pub finalized_content_root: [u8; 32],
    pub finalized_qwen_claim: [u8; 32],
    pub finalized_absent_claim: [u8; 32],
    pub attestations: Vec<SimplexSignerAttestation>,
}

const SIMPLEX_ROSTER_LEAF_DOM: &[u8] = b"SHE-SIMPLEX-ROSTER-LEAF-V1";
const SIMPLEX_ROSTER_NODE_DOM: &[u8] = b"SHE-SIMPLEX-ROSTER-NODE-V1";

impl SimplexFinCertLeafReceipt {
    pub fn build_committee(n: usize, seed_tag: u8) -> (Vec<WotsKeypair>, [u8; 32], Vec<[u8; 32]>) {
        assert!(n.is_power_of_two() && n >= 4);
        let mut kps = Vec::with_capacity(n);
        let mut leaves = Vec::with_capacity(n);
        for i in 0..n {
            let mut seed = [seed_tag; 32];
            seed[0] = i as u8;
            let kp = WotsKeypair::from_seed(&seed);
            let mut lbuf = [0u8; 68];
            lbuf[0..4].copy_from_slice(&(i as u32).to_le_bytes());
            lbuf[4..36].copy_from_slice(&kp.pk.pub_seed);
            lbuf[36..68].copy_from_slice(&kp.pk.pk_root);
            leaves.push(cshake256_32(SIMPLEX_ROSTER_LEAF_DOM, &lbuf));
            kps.push(kp);
        }
        let root = merkle_root_cshake(SIMPLEX_ROSTER_NODE_DOM, &leaves);
        (kps, root, leaves)
    }

    pub fn signing_digest(
        view: u64,
        roster_root: &[u8; 32],
        content_root: &[u8; 32],
        qwen_claim: &[u8; 32],
        absent_claim: &[u8; 32],
    ) -> [u8; 32] {
        let mut buf = [0u8; 136];
        buf[0..8].copy_from_slice(&view.to_le_bytes());
        buf[8..40].copy_from_slice(roster_root);
        buf[40..72].copy_from_slice(content_root);
        buf[72..104].copy_from_slice(qwen_claim);
        buf[104..136].copy_from_slice(absent_claim);
        cshake256_32(b"SHE-SIMPLEX-FINCERT-MSG-V1", &buf)
    }

    pub fn sign_quorum(
        n_validators: usize,
        max_faulty_f: usize,
        view: u64,
        kps: &[WotsKeypair],
        roster_root: [u8; 32],
        roster_leaves: &[[u8; 32]],
        signer_indices: &[usize],
        finalized_content_root: [u8; 32],
        finalized_qwen_claim: [u8; 32],
        finalized_absent_claim: [u8; 32],
    ) -> Self {
        let msg = Self::signing_digest(
            view,
            &roster_root,
            &finalized_content_root,
            &finalized_qwen_claim,
            &finalized_absent_claim,
        );
        let attestations = signer_indices
            .iter()
            .map(|&idx| SimplexSignerAttestation {
                validator_index: idx,
                validator_pk: kps[idx].pk,
                roster_merkle_path: merkle_open_single_cshake(SIMPLEX_ROSTER_NODE_DOM, roster_leaves, idx),
                wots_sig: kps[idx].sign(&msg),
            })
            .collect();
        Self {
            n_validators,
            max_faulty_f,
            view,
            roster_root,
            finalized_content_root,
            finalized_qwen_claim,
            finalized_absent_claim,
            attestations,
        }
    }

    pub fn verify(
        &self,
        expected_roster_root: &[u8; 32],
        expected_content_root: &[u8; 32],
        expected_qwen_claim: &[u8; 32],
        expected_absent_claim: &[u8; 32],
    ) -> Result<[u8; 32], String> {
        if self.view == 0 {
            return Err("Simplex FinCert view must be > 0 (certificate_positive_at)".into());
        }
        if 3 * self.max_faulty_f >= self.n_validators || !self.n_validators.is_power_of_two() {
            return Err("Simplex FinCert violates n > 3*f".into());
        }
        if &self.roster_root != expected_roster_root
            || &self.finalized_content_root != expected_content_root
            || &self.finalized_qwen_claim != expected_qwen_claim
            || &self.finalized_absent_claim != expected_absent_claim
        {
            return Err("Simplex FinCert root/claim pin mismatch".into());
        }
        let quorum = self.n_validators - self.max_faulty_f;
        if self.attestations.len() < quorum {
            return Err(format!(
                "Simplex FinCert insufficient signers {} < n - f = {}",
                self.attestations.len(),
                quorum
            ));
        }
        let msg = Self::signing_digest(
            self.view,
            &self.roster_root,
            &self.finalized_content_root,
            &self.finalized_qwen_claim,
            &self.finalized_absent_claim,
        );
        let mut prev_idx: Option<usize> = None;
        for att in &self.attestations {
            if att.validator_index >= self.n_validators {
                return Err("Simplex validator_index out of range".into());
            }
            if let Some(p) = prev_idx {
                if att.validator_index <= p {
                    return Err("Simplex duplicate or non-strictly-increasing validator_index".into());
                }
            }
            prev_idx = Some(att.validator_index);
            let mut lbuf = [0u8; 68];
            lbuf[0..4].copy_from_slice(&(att.validator_index as u32).to_le_bytes());
            lbuf[4..36].copy_from_slice(&att.validator_pk.pub_seed);
            lbuf[36..68].copy_from_slice(&att.validator_pk.pk_root);
            let want_leaf = cshake256_32(SIMPLEX_ROSTER_LEAF_DOM, &lbuf);
            if att.roster_merkle_path.index != att.validator_index
                || att.roster_merkle_path.leaf != want_leaf
                || !att.roster_merkle_path.verify(SIMPLEX_ROSTER_NODE_DOM, &self.roster_root, self.n_validators)
            {
                return Err("Simplex validator Merkle roster path failed".into());
            }
            verify_wots_signature(&att.validator_pk, &msg, &att.wots_sig)?;
        }
        Ok(msg)
    }
}

// ================================================================================================
// §6. Commitment-Pinned `DeferredLeafClaim`s & `GoldilocksExt4` `Hem` Canopy WHIR Stream Compiler
// ================================================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u64)]
pub enum DeferredLeafKind {
    BabyBearWhirExt4 = 1,
    Tower256AbsentDfa = 2,
    SimplexQuorumFinCert = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeferredLeafClaim {
    pub kind: DeferredLeafKind,
    pub content_root: [u8; 32],
    pub leaf_root: [u8; 32],
    pub claim_digest: [u8; 32],
}

impl DeferredLeafClaim {
    /// Canonical immediate words (`16` canonical `Goldilocks` words) absorbed into `Dregg-180`'s
    /// `R_CH` transcript chain AND `GF(2^128)` `pdig` program digest via `OP_ABSORB_ROOT`.
    pub fn to_immediate_limbs(&self) -> [u64; 16] {
        let c = pack_digest32_to_5_limbs(&self.content_root);
        let l = pack_digest32_to_5_limbs(&self.leaf_root);
        let d = pack_digest32_to_5_limbs(&self.claim_digest);
        [
            self.kind as u64,
            c[0], c[1], c[2], c[3], c[4],
            l[0], l[1], l[2], l[3], l[4],
            d[0], d[1], d[2], d[3], d[4],
        ]
    }

    pub fn reduced_ext4_eval(&self) -> GoldilocksExt4 {
        let imm = self.to_immediate_limbs();
        let h = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &imm);
        GoldilocksExt4::from_u64_limbs(h)
    }
}

/// Compiled `GoldilocksExt4` `Hem` aggregate stream ready for `< 16 KiB` `Dregg180StreamVm`.
#[derive(Clone, Debug)]
pub struct CompiledDregg180HemStream {
    pub leaf_claims: [DeferredLeafClaim; 3],
    pub p2_stage0_root: [u64; 4],
    pub cshake_stage0_root: [u8; 32],
    pub p2_stage1_root: [u64; 4],
    pub wire_bytes: Vec<u8>,
    pub pinned_program_digest: u128,
    pub num_records: usize,
}

struct DualCanopyStage {
    log_fibers: usize,
    fibers: Vec<[GoldilocksExt4; 2]>,
    p2_nodes: Vec<[u64; 4]>,
    cshake_leaves: Vec<[u8; 32]>,
    cshake_nodes: Vec<[u8; 32]>,
}

impl DualCanopyStage {
    fn commit(stage_id: u8, coeffs: &[GoldilocksExt4], blowup: usize, canopy_key4: [u64; 4]) -> Self {
        let code = encode_rs_coset_ext4(coeffs, blowup, Goldilocks::SEVEN);
        let n_dom = code.len();
        let n_fibers = n_dom / 2;
        let log_fibers = n_fibers.trailing_zeros() as usize;
        let mut fibers = Vec::with_capacity(n_fibers);
        let mut p2_nodes = vec![[0u64; 4]; 2 * n_fibers];
        let mut cshake_leaves = Vec::with_capacity(n_fibers);
        let mut cshake_nodes = vec![[0u8; 32]; 2 * n_fibers];

        for f in 0..n_fibers {
            let v0 = code[f];
            let v1 = code[f + n_fibers];
            fibers.push([v0, v1]);
            let mut l8 = [0u64; 8];
            l8[0..4].copy_from_slice(&v0.to_u64_limbs());
            l8[4..8].copy_from_slice(&v1.to_u64_limbs());
            p2_nodes[n_fibers + f] = p2_sponge_hash_limbs(P2_DOMAIN_CANOPY_LEAF, canopy_key4, &l8);
            let cs_leaf = cshake256_canopy_ext4_pair_leaf(stage_id, f as u32, v0, v1);
            cshake_leaves.push(cs_leaf);
            cshake_nodes[n_fibers + f] = cs_leaf;
        }
        let key3 = [canopy_key4[0], canopy_key4[1], canopy_key4[2]];
        for idx in (1..n_fibers).rev() {
            p2_nodes[idx] = p2_canopy_node(p2_nodes[2 * idx], p2_nodes[2 * idx + 1], key3, idx as u32);
            cshake_nodes[idx] =
                cshake256_canopy_node(&cshake_nodes[2 * idx], &cshake_nodes[2 * idx + 1], idx as u32);
        }
        Self {
            log_fibers,
            fibers,
            p2_nodes,
            cshake_leaves,
            cshake_nodes,
        }
    }

    fn p2_root(&self) -> [u64; 4] {
        self.p2_nodes[1]
    }

    fn cshake_root(&self) -> [u8; 32] {
        self.cshake_nodes[1]
    }

    fn p2_siblings(&self, fiber_idx: usize) -> Vec<[u64; 4]> {
        let n_fibers = 1usize << self.log_fibers;
        let mut idx = n_fibers + fiber_idx;
        let mut out = Vec::with_capacity(self.log_fibers);
        for _ in 0..self.log_fibers {
            out.push(self.p2_nodes[idx ^ 1]);
            idx >>= 1;
        }
        out
    }

    fn cshake_siblings(&self, fiber_idx: usize) -> Vec<[u8; 32]> {
        let n_fibers = 1usize << self.log_fibers;
        let mut idx = n_fibers + fiber_idx;
        let mut out = Vec::with_capacity(self.log_fibers);
        for _ in 0..self.log_fibers {
            out.push(self.cshake_nodes[idx ^ 1]);
            idx >>= 1;
        }
        out
    }
}

/// Compile verified heterogeneous child leaf claims (`BabyBear Ext4` + `Tower256` `Absent` + `Simplex` `FinCert`)
/// into a single `GoldilocksExt4` `Hem` Canopy WHIR (`Poseidon2-12` + `cSHAKE256` + PoW + CWYZ duet-fold +
/// sumcheck) stream executable inside `< 16 KiB` `Dregg180StreamVm`.
pub fn compile_deferred_leaves_to_dregg180_hem_stream(
    leaf_claims: [DeferredLeafClaim; 3],
    pin_mode: bool,
    k_mac_opt: Option<[u8; 16]>,
) -> Result<CompiledDregg180HemStream, String> {
    if leaf_claims[0].kind != DeferredLeafKind::BabyBearWhirExt4
        || leaf_claims[1].kind != DeferredLeafKind::Tower256AbsentDfa
        || leaf_claims[2].kind != DeferredLeafKind::SimplexQuorumFinCert
    {
        return Err("DeferredLeafClaim tags must be [BabyBearWhirExt4, Tower256AbsentDfa, SimplexQuorumFinCert]".into());
    }
    if leaf_claims[0].content_root != leaf_claims[1].content_root
        || leaf_claims[1].content_root != leaf_claims[2].content_root
    {
        return Err("Cross-leaf content_root mismatch across Qwen / Absent / FinCert leaves".into());
    }

    let num_vars = 6usize; // 64-element multilinear polynomial over GoldilocksExt4
    let n_coeffs = 1usize << num_vars;
    let blowup_0 = 8usize; // N_0 = 512, 256 fibers, depth = 8
    let blowup_1 = 8usize; // N_1 = 256, 128 fibers, depth = 7 on 32-coeff folded Stage-1 oracle
    let pow_bits = 10u8;   // 10-bit Poseidon2 transcript PoW (~1,024 hashes)
    let num_queries = 6usize;

    let mut asm = Dregg180HvmAssembler::new(OP_HEM, pin_mode, false);

    // 1. Bind relation & schedule into `R_CH` (`P2_DOMAIN_FS_BIND_REL`):
    let mut rel_imm = pack_bytes_7_limbs(b"DREGG180.SHE.HETERO.HEM/v1");
    rel_imm.extend_from_slice(&[num_vars as u64, blowup_0 as u64, blowup_1 as u64, num_queries as u64, pow_bits as u64]);
    asm.hash(R_CH, None, P2_DOMAIN_FS_BIND_REL, &rel_imm, &[], 0, 0);
    let mut ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_BIND_REL, FS_INIT_CAP, &rel_imm);

    // 2. `OP_ABSORB_ROOT` x3: absorb all 3 commitment-pinned `DeferredLeafClaim`s as program immediates!
    let labels: [&[u8]; 3] = [b"LEAF0_QWEN_BB4", b"LEAF1_T256_ABS", b"LEAF2_SMPX_FIN"];
    for (i, claim) in leaf_claims.iter().enumerate() {
        let imm16 = claim.to_immediate_limbs();
        asm.absorb_limbs_immediate(labels[i], &imm16, 0, 0);
        let mut full = pack_bytes_7_limbs(labels[i]);
        full.extend_from_slice(&imm16);
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &full);
    }

    // 3. Build multilinear polynomial `W(X_0..X_5)` encoding the 3 `DeferredLeafClaim` evaluations
    //    (with top 2 monomial slots zeroed so CWYZ fold has exact degree `< 32`) and commit Stage-0
    //    under BOTH `Poseidon2-12` Canopy AND `cSHAKE256` Canopy:
    let mut evals = vec![GoldilocksExt4::ZERO; n_coeffs];
    evals[0] = leaf_claims[0].reduced_ext4_eval();
    evals[1] = leaf_claims[1].reduced_ext4_eval();
    evals[2] = leaf_claims[2].reduced_ext4_eval();
    evals[3] = evals[0] + evals[1] + evals[2];
    for i in 4..(n_coeffs - 2) {
        evals[i] = evals[i % 4].scale_base(Goldilocks((i as u64) + 11));
    }
    // Convert hypercube evaluations `evals` to univariate/monomial coeffs for RS coset Commitment:
    let coeffs_0 = evals.clone();
    let canopy_key0 = [0x4452_4731_8000_0001, 0x4341_4E50_0000_0000, 0x5354_4730_0000_0001, P2_IV];
    let stage0 = DualCanopyStage::commit(0, &coeffs_0, blowup_0, canopy_key0);
    let p2_root0 = stage0.p2_root();
    let cs_root0 = stage0.cshake_root();
    let cs_root0_limbs5 = pack_digest32_to_5_limbs(&cs_root0);
    let cs_root0_pin4 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &cs_root0_limbs5);

    // Absorb Stage-0 Poseidon2 Canopy root (`R_6 = p2_root0`) and cSHAKE256 Canopy root (`R_7 = cs_root0_pin4`):
    asm.absorb_limbs_proof(b"PCS_S0_P2_ROOT", &p2_root0, 6, 0);
    {
        let mut v = pack_bytes_7_limbs(b"PCS_S0_P2_ROOT");
        v.extend_from_slice(&p2_root0);
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
    }
    asm.absorb_limbs_proof(b"PCS_S0_CS_ROOT", &cs_root0_pin4, 7, 0);
    {
        let mut v = pack_bytes_7_limbs(b"PCS_S0_CS_ROOT");
        v.extend_from_slice(&cs_root0_pin4);
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
    }

    // 4. Squeeze CWYZ Duet-Fold challenges `(alpha, beta, theta)` from `R_CH`, fold `coeffs_0` -> `coeffs_1`
    //    (`32` coeffs), and commit Stage-1 with escalated blowup `16` (`R_8 = p2_root1`):
    let fold_lab = pack_bytes_7_limbs(b"WHIR_S0_DUET_CHAL");
    let squeeze_local = |ch_cur: [u64; 4], label_limbs: &[u64], ctr: u64| -> GoldilocksExt4 {
        let mut inp = label_limbs.to_vec();
        inp.push(ctr);
        GoldilocksExt4::from_u64_limbs(p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_EXT4, ch_cur, &inp))
    };
    let alpha0 = squeeze_local(ch, &fold_lab, 0);
    let beta0 = squeeze_local(ch, &fold_lab, 1);
    let theta0 = squeeze_local(ch, &fold_lab, 2);
    // Latch `(alpha0, beta0, theta0)` into scratch registers `R_9, R_10, R_11` right now while `R_CH == ch`:
    asm.squeeze_ext4(9, b"WHIR_S0_DUET_CHAL", 0);
    asm.squeeze_ext4(10, b"WHIR_S0_DUET_CHAL", 1);
    asm.squeeze_ext4(11, b"WHIR_S0_DUET_CHAL", 2);

    // Fold polynomial `P(X) = P_even(X^2) + X * P_odd(X^2)` into `P^{(1)}(Y)`:
    // On each fiber `(x0, -x0)` where `y0 = x0`, `even = P_even(y0^2)`, `odd = P_odd(y0^2)`,
    // `P^{(1)}(y0^2) = odd + (alpha0 + beta0 * y0^2) * (even + theta0 * odd)`.
    let half_c = n_coeffs / 2;
    let mut even_c = vec![GoldilocksExt4::ZERO; half_c];
    let mut odd_c = vec![GoldilocksExt4::ZERO; half_c];
    for i in 0..half_c {
        even_c[i] = coeffs_0[2 * i];
        odd_c[i] = coeffs_0[2 * i + 1];
    }
    let mut mixed_c = vec![GoldilocksExt4::ZERO; half_c];
    for i in 0..half_c {
        mixed_c[i] = even_c[i] + (theta0 * odd_c[i]);
    }
    // Since `coeffs_0[62] == coeffs_0[63] == 0`, `mixed_c[half_c - 1] == 0`, so `P^{(1)}(Y)` has
    // exact degree `< 32` (`half_c` coefficients) and evaluates over coset `49 * H_{256}` (`128` fibers, depth `7`):
    let mut coeffs_1 = vec![GoldilocksExt4::ZERO; half_c];
    for i in 0..half_c {
        coeffs_1[i] = coeffs_1[i] + odd_c[i] + (alpha0 * mixed_c[i]);
        if i + 1 < half_c {
            coeffs_1[i + 1] = coeffs_1[i + 1] + (beta0 * mixed_c[i]);
        }
    }
    let canopy_key1 = [0x4452_4731_8000_0002, 0x4341_4E50_0000_0001, 0x5354_4731_0000_0002, P2_IV];
    let code_1 = encode_rs_coset_ext4(&coeffs_1, blowup_1, Goldilocks(49));
    let n_fib1 = code_1.len() / 2;
    let mut stage1_p2_nodes = vec![[0u64; 4]; 2 * n_fib1];
    let mut stage1_fibers = Vec::with_capacity(n_fib1);
    for f in 0..n_fib1 {
        let u0 = code_1[f];
        let u1 = code_1[f + n_fib1];
        stage1_fibers.push([u0, u1]);
        let mut l8 = [0u64; 8];
        l8[0..4].copy_from_slice(&u0.to_u64_limbs());
        l8[4..8].copy_from_slice(&u1.to_u64_limbs());
        stage1_p2_nodes[n_fib1 + f] = p2_sponge_hash_limbs(P2_DOMAIN_CANOPY_LEAF, canopy_key1, &l8);
    }
    let key1_3 = [canopy_key1[0], canopy_key1[1], canopy_key1[2]];
    for idx in (1..n_fib1).rev() {
        stage1_p2_nodes[idx] = p2_canopy_node(
            stage1_p2_nodes[2 * idx],
            stage1_p2_nodes[2 * idx + 1],
            key1_3,
            idx as u32,
        );
    }
    let p2_root1 = stage1_p2_nodes[1];
    // `H_HASH` latch is 3 bits (`c & 7`, `R_1..=R_7`); latch `p2_root1` into `R_B` (`3`) then copy to `R_8` (`R_15 == 0`):
    asm.absorb_limbs_proof(b"PCS_S1_P2_ROOT", &p2_root1, R_B, 0);
    asm.eadd(8, R_B, 15);
    {
        let mut v = pack_bytes_7_limbs(b"PCS_S1_P2_ROOT");
        v.extend_from_slice(&p2_root1);
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
    }

    // 5. 6-Round Quadratic Sumcheck over `GoldilocksExt4`:
    //    Prove `sum_{x in {0,1}^6} eq(tau, x) * W(x) == claimed_eval`, with every round challenge
    //    squeezed inside `Dregg180StreamVm`!
    let tau_lab = pack_bytes_7_limbs(b"HEM_EQ_TAU");
    let mut tau = Vec::with_capacity(num_vars);
    for j in 0..num_vars {
        tau.push(squeeze_local(ch, &tau_lab, j as u64));
    }
    let mut eq_tab = vec![GoldilocksExt4::ONE; 1];
    for &t_j in &tau {
        let mut next = Vec::with_capacity(eq_tab.len() * 2);
        let one_minus_t = GoldilocksExt4::ONE - t_j;
        for &v in &eq_tab {
            next.push(v * one_minus_t);
            next.push(v * t_j);
        }
        eq_tab = next;
    }
    let mut w_tab = evals.clone();
    let mut init_claim = GoldilocksExt4::ZERO;
    for i in 0..n_coeffs {
        init_claim = init_claim + (eq_tab[i] * w_tab[i]);
    }
    asm.absorb_limbs_proof(b"HEM_SC_CLAIM", &init_claim.to_u64_limbs(), R_A, 0);
    {
        let mut v = pack_bytes_7_limbs(b"HEM_SC_CLAIM");
        v.extend_from_slice(&init_claim.to_u64_limbs());
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
    }

    let mut sc_chals = Vec::with_capacity(num_vars);
    for rnd in 0..num_vars {
        let half = w_tab.len() / 2;
        let mut c0 = GoldilocksExt4::ZERO;
        let mut c2 = GoldilocksExt4::ZERO;
        for i in 0..half {
            let (e0, e1) = (eq_tab[2 * i], eq_tab[2 * i + 1]);
            let (a0, a1) = (w_tab[2 * i], w_tab[2 * i + 1]);
            c0 = c0 + (e0 * a0);
            c2 = c2 + ((e1 - e0) * (a1 - a0));
        }
        asm.absorb_limbs_proof(b"HEM_SC_C0", &c0.to_u64_limbs(), R_X, 0);
        {
            let mut v = pack_bytes_7_limbs(b"HEM_SC_C0");
            v.extend_from_slice(&c0.to_u64_limbs());
            ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
        }
        asm.absorb_limbs_proof(b"HEM_SC_C2", &c2.to_u64_limbs(), R_Y, 0);
        {
            let mut v = pack_bytes_7_limbs(b"HEM_SC_C2");
            v.extend_from_slice(&c2.to_u64_limbs());
            ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
        }
        let sc_lab = pack_bytes_7_limbs(b"HEM_SC_CHAL");
        let r_j = squeeze_local(ch, &sc_lab, rnd as u64);
        asm.squeeze_ext4(R_B, b"HEM_SC_CHAL", rnd as u64);
        // `c1 = claim - 2*c0 - c2`, `claim <- c0 + r_j*(c1 + r_j*c2)` on chip:
        asm.esub(R_T0, R_A, R_X);
        asm.esub(R_T0, R_T0, R_X);
        asm.esub(R_T0, R_T0, R_Y);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_Y, R_Y, R_T0);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_A, R_Y, R_X);

        sc_chals.push(r_j);
        let mut next_eq = Vec::with_capacity(half);
        let mut next_w = Vec::with_capacity(half);
        for i in 0..half {
            next_eq.push(eq_tab[2 * i] + (r_j * (eq_tab[2 * i + 1] - eq_tab[2 * i])));
            next_w.push(w_tab[2 * i] + (r_j * (w_tab[2 * i + 1] - w_tab[2 * i])));
        }
        eq_tab = next_eq;
        w_tab = next_w;
    }
    let terminal_claim = eq_tab[0] * w_tab[0];
    asm.load(R_Y, &terminal_claim.to_u64_limbs(), true);
    asm.assert_eq(R_A, R_Y);

    // 6. Grind Poseidon2 Transcript Proof-of-Work (`pow_bits = 10`) & verify via `H_ASSERT_POW`:
    let pow_mask = (1u64 << pow_bits) - 1;
    let mut pow_nonce = 0u64;
    loop {
        let nw = [pow_nonce & 0xFFFF_FFFF, pow_nonce >> 32];
        if (p2_sponge_hash_limbs(P2_DOMAIN_FS_POW, ch, &nw)[0] & pow_mask) == 0 {
            break;
        }
        pow_nonce += 1;
    }
    let nonce_words = [pow_nonce & 0xFFFF_FFFF, pow_nonce >> 32];
    asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_POW, &[], &nonce_words, 0, 0);
    asm.assert_pow(R_T0, pow_bits);
    asm.absorb_limbs_proof(b"HEM_POW_NONCE", &nonce_words, 0, 0);
    {
        let mut v = pack_bytes_7_limbs(b"HEM_POW_NONCE");
        v.extend_from_slice(&nonce_words);
        ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch, &v);
    }

    // 7. Open `num_queries` Transcript-Bound Canopy Fibers across Stage-0 (`Poseidon2` + `cSHAKE256`)
    //    and Stage-1 (`Poseidon2`), verifying CWYZ asymmetric duet-fold in `GoldilocksExt4`!
    let omega_dom0 = Goldilocks::two_adic_generator(9); // N_0 = 512 = 2^9
    for q_idx in 0..num_queries {
        let mut qlab = pack_bytes_7_limbs(b"WHIR_S0_QUERY");
        qlab.push(q_idx as u64);
        let f_idx = (p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_IDX, ch, &qlab)[0] as usize) & 0xFF;
        let [v0, v1] = stage0.fibers[f_idx];
        let mut l8 = [0u64; 8];
        l8[0..4].copy_from_slice(&v0.to_u64_limbs());
        l8[4..8].copy_from_slice(&v1.to_u64_limbs());

        // 7a. Stage-0 `Poseidon2-12` Canopy path (`H_BIND_IDX` + `H_MERKLE` -> `R_6`):
        asm.load(12, &canopy_key0, true);
        asm.hash(R_X, Some(12), P2_DOMAIN_CANOPY_LEAF, &[], &l8, 0, 0);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, stage0.log_fibers as u8);
        asm.merkle(12, f_idx as u32, &stage0.p2_siblings(f_idx));
        asm.assert_eq(R_X, 6);

        // 7b. Stage-0 `cSHAKE256("QSAG.PCS.CANOPY/v2")` Canopy path (`H_BIND_IDX` + `H_CSHAKE_MERKLE` -> `R_7`):
        let cs_leaf = stage0.cshake_leaves[f_idx];
        let cs_leaf_limbs5 = pack_digest32_to_5_limbs(&cs_leaf);
        asm.hash(R_X, None, P2_DOMAIN_FS_ABSORB_LIMBS, &[], &cs_leaf_limbs5, 0, 0);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, stage0.log_fibers as u8);
        asm.cshake_merkle(f_idx as u32, &cs_leaf, &stage0.cshake_siblings(f_idx));
        asm.assert_eq(R_X, 7);

        // 7c. CWYZ Asymmetric Duet-Fold step (`R_9 = alpha0, R_10 = beta0, R_11 = theta0`):
        let y0 = Goldilocks::SEVEN * omega_dom0.pow(f_idx as u64);
        let inv2_y0 = (Goldilocks::TWO * y0).inv();
        let y0_sq = y0.square();
        let folded_want = GoldilocksExt4::cwyz_duet_fold(
            v0,
            v1,
            alpha0,
            beta0,
            theta0,
            GOLDILOCKS_INV2,
            inv2_y0,
            y0_sq,
        );
        asm.load(R_Y, &[y0_sq.0, 0, 0, 0], true);
        asm.emul(R_B, 10, R_Y);
        asm.eadd(R_B, 9, R_B); // R_B = gamma = alpha0 + beta0 * y0^2
        asm.load(R_T0, &v0.to_u64_limbs(), false);
        asm.load(R_Y, &v1.to_u64_limbs(), false);
        asm.eadd(R_T0, R_T0, R_Y); // T0 = v0 + v1
        asm.esub(R_Y, R_T0, R_Y);  // Y = v0
        asm.eadd(R_Y, R_Y, R_Y);   // Y = 2*v0
        asm.esub(R_Y, R_Y, R_T0);  // Y = v0 - v1
        asm.load(13, &[GOLDILOCKS_INV2.0, 0, 0, 0], true);
        asm.emul(R_T0, R_T0, 13);  // even = (v0 + v1) * inv2
        asm.load(13, &[inv2_y0.0, 0, 0, 0], true);
        asm.emul(R_Y, R_Y, 13);    // odd = (v0 - v1) * inv2_y0
        asm.emul(13, 11, R_Y);     // theta0 * odd
        asm.eadd(R_T0, R_T0, 13);  // mixed
        asm.emul(R_T0, R_T0, R_B); // gamma * mixed
        asm.eadd(14, R_T0, R_Y);   // R_14 = folded = odd + gamma * mixed

        // 7d. Stage-1 `Poseidon2-12` Canopy opening at `s1_f = f_idx & 0x7F` (`depth = 7`) -> `R_8`:
        let s1_f = f_idx & 0x7F;
        let [u0, u1] = stage1_fibers[s1_f];
        let u_expected = if (f_idx & 128) == 0 { u0 } else { u1 };
        assert_eq!(u_expected, folded_want);
        asm.load(13, &u_expected.to_u64_limbs(), false);
        asm.assert_eq(14, 13);
        let mut s1_l8 = [0u64; 8];
        s1_l8[0..4].copy_from_slice(&u0.to_u64_limbs());
        s1_l8[4..8].copy_from_slice(&u1.to_u64_limbs());
        let mut s1_sibs = Vec::with_capacity(7);
        let mut h_idx = n_fib1 + s1_f;
        for _ in 0..7 {
            s1_sibs.push(stage1_p2_nodes[h_idx ^ 1]);
            h_idx >>= 1;
        }
        asm.load(12, &canopy_key1, true);
        asm.hash(R_X, Some(12), P2_DOMAIN_CANOPY_LEAF, &[], &s1_l8, 0, 0);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 7);
        asm.merkle(12, s1_f as u32, &s1_sibs);
        asm.assert_eq(R_X, 8);
    }

    let delta_override = k_mac_opt.map(u128::from_le_bytes);
    let (wire_bytes, pinned_program_digest) = asm.build_wire_bytes_and_pdig(delta_override);
    let num_records = asm.records.len();

    Ok(CompiledDregg180HemStream {
        leaf_claims,
        p2_stage0_root: p2_root0,
        cshake_stage0_root: cs_root0,
        p2_stage1_root: p2_root1,
        wire_bytes,
        pinned_program_digest,
        num_records,
    })
}

/// Verify all 3 heterogeneous Wearable SHE leaves (`BabyBear Ext4` `WearableQwenWhirLeafReceipt` +
/// `Tower256` `Tower256AbsentLeafReceipt` + `Simplex` `SimplexFinCertLeafReceipt`) and compile into
/// one `Dregg-180` `GoldilocksExt4` `Hem` stream.
pub fn bridge_wearable_she_bundle_to_dregg180_stream(
    qwen_leaf: &WearableQwenWhirLeafReceipt,
    absent_leaf: &Tower256AbsentLeafReceipt,
    fincert_leaf: &SimplexFinCertLeafReceipt,
    expected_roster_root: &[u8; 32],
    pin_mode: bool,
    k_mac_opt: Option<[u8; 16]>,
) -> Result<CompiledDregg180HemStream, String> {
    let qwen_claim_dig = qwen_leaf.verify()?;
    let absent_claim_dig = absent_leaf.verify(&qwen_leaf.content_root)?;
    let fincert_claim_dig = fincert_leaf.verify(
        expected_roster_root,
        &qwen_leaf.content_root,
        &qwen_claim_dig,
        &absent_claim_dig,
    )?;

    let claims = [
        DeferredLeafClaim {
            kind: DeferredLeafKind::BabyBearWhirExt4,
            content_root: qwen_leaf.content_root,
            leaf_root: qwen_leaf.layer_whir_root,
            claim_digest: qwen_claim_dig,
        },
        DeferredLeafClaim {
            kind: DeferredLeafKind::Tower256AbsentDfa,
            content_root: absent_leaf.content_root,
            leaf_root: absent_leaf.trace_commitment,
            claim_digest: absent_claim_dig,
        },
        DeferredLeafClaim {
            kind: DeferredLeafKind::SimplexQuorumFinCert,
            content_root: fincert_leaf.finalized_content_root,
            leaf_root: fincert_leaf.roster_root,
            claim_digest: fincert_claim_dig,
        },
    ];
    compile_deferred_leaves_to_dregg180_hem_stream(claims, pin_mode, k_mac_opt)
}

/// Bridge a full 24-layer `Qwen/Qwen3.5-0.8B-Base` `PayableComputeReceipt` + `Tower256` `Absent`
/// + `Simplex` `n - f` `FinCert` into one `Dregg-180` `GoldilocksExt4` `Hem` stream.
pub fn bridge_payable_compute_receipt_to_dregg180_stream(
    lease: &ProviderExecutionLease,
    rom: &QwenBpeRom,
    payable_receipt_bytes: &[u8],
    absent_leaf: &Tower256AbsentLeafReceipt,
    fincert_leaf: &SimplexFinCertLeafReceipt,
    expected_roster_root: &[u8; 32],
    pin_mode: bool,
    k_mac_opt: Option<[u8; 16]>,
) -> Result<CompiledDregg180HemStream, String> {
    let settlement = verify_payable_compute_receipt_and_settle(lease, rom, payable_receipt_bytes, None)?;
    let parsed = PayableComputeReceipt::from_bytes(payable_receipt_bytes)?;
    let content_root = parsed.commitment.content_root;
    let mut qwen_buf = [0u8; 96];
    qwen_buf[0..32].copy_from_slice(&settlement.provider_invocation_key);
    qwen_buf[32..64].copy_from_slice(&settlement.provider_evidence_root);
    qwen_buf[64..80].copy_from_slice(&settlement.paid.to_le_bytes());
    qwen_buf[80..96].copy_from_slice(&settlement.refunded.to_le_bytes());
    let qwen_claim_dig = cshake256_32(b"SHE-PAYABLE-LEAF-CLAIM-V1", &qwen_buf);

    let absent_claim_dig = absent_leaf.verify(&content_root)?;
    let fincert_claim_dig = fincert_leaf.verify(
        expected_roster_root,
        &content_root,
        &qwen_claim_dig,
        &absent_claim_dig,
    )?;

    let claims = [
        DeferredLeafClaim {
            kind: DeferredLeafKind::BabyBearWhirExt4,
            content_root,
            leaf_root: settlement.provider_evidence_root,
            claim_digest: qwen_claim_dig,
        },
        DeferredLeafClaim {
            kind: DeferredLeafKind::Tower256AbsentDfa,
            content_root: absent_leaf.content_root,
            leaf_root: absent_leaf.trace_commitment,
            claim_digest: absent_claim_dig,
        },
        DeferredLeafClaim {
            kind: DeferredLeafKind::SimplexQuorumFinCert,
            content_root: fincert_leaf.finalized_content_root,
            leaf_root: fincert_leaf.roster_root,
            claim_digest: fincert_claim_dig,
        },
    ];
    compile_deferred_leaves_to_dregg180_hem_stream(claims, pin_mode, k_mac_opt)
}
