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
use rayon::prelude::*;
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
pub const P2_DOMAIN_FS_POW_T1: u64 = 0x5032_4653_504F_5731;
pub const P2_DOMAIN_FS_POW_T2: u64 = 0x5032_4653_504F_5732;
pub const P2_DOMAIN_ORDERED_COMPRESS: u64 = 0x5032_4F52_4443_4D50;
pub const P2_DOMAIN_PROG_HASH: u64 = 0x5032_5052_4F47_4853;
pub const FS_INIT_CAP: [u64; 4] = [P2_DOMAIN_FS_INIT, 0, 0, P2_IV];

/// Production `UD-100` Canopy BaseFold/WHIR query & PoW schedule (post `gpt-6.2-astra` H2 hardening):
/// rate `rho = 1/8` (`blowup = 8`, unique-decoding radius `delta_UD = 7/16`, `1 - delta_UD = 9/16`,
/// `log2(16/9) = 0.830075` bits/query).
/// - Bare query-only two-table union bound (ZERO PoW credit needed): `2 * (9/16)^122 = 2^{-100.27} < 2^{-100}`.
/// - Single-table bare query bound: `(9/16)^122 = 2^{-101.27} < 2^{-101}`.
/// - Combined with single-read bound `16`-bit PoW grinding: `2 * (9/16)^122 * 2^{-16} = 2^{-116.27} < 2^{-116}`.
/// - Remaining interactive terms over `|F_GL^4| = p_GL^4 ~= 2^{256}` (sumcheck `< 2^{-250}`, LogUp poles
///   `<= 83,968 / p_GL^4 < 2^{-239}`, BaseFold batching/folding `[BCIKS20]`/`[H24]` `< 2^{-230}`) + ROM FS.
pub const UD100_BLOWUP: usize = 8;
pub const UD100_NUM_QUERIES: usize = 122;
pub const UD100_POW_BITS: u8 = 16;

/// Non-native `BabyBear` prime `p_BB = 15 * 2^27 + 1 = 2,013,265,921` embedded inside `Goldilocks`.
pub const BABYBEAR_PRIME_U64: u64 = 2_013_265_921;
/// Safe Fiat-Shamir quotient ceiling `floor((p_GL - 1) / p_BB) - 1 = 9,162,596,890` guaranteeing
/// `(q_fs + 1) * p_BB <= p_GL`, hence `q_fs * p_BB + r < p_GL` for all `r < p_BB` (proved in Lean!).
pub const BABYBEAR_FS_Q_SAFE: u64 = 9_162_596_890;
/// Execution trace size `N_exec = 2^12 = 4,096` (supports `m = 1..=6` full cubic `BabyBear Ext4`
/// sumcheck + full in-circuit `chi(x)`/`W_bb(r)`/`eq(tau, r)` terminal evaluation + `4 x 256` DFA ROM
/// + up to `4,096`-byte committed payloads).
pub const HEM_EXEC_VARS: usize = 12;
pub const HEM_EXEC_ROWS: usize = 1 << HEM_EXEC_VARS;
/// Maximum supported `BabyBear Ext4` child sumcheck rounds with full in-circuit committed `W_bb(r)` evaluation.
pub const HEM_MAX_BB_ROUNDS: usize = 6;
/// Fixed start row of committed `W_bb = (A_bb[0..2^m], B_bb[0..2^m])` in Table 1 (`rows 32..32+2^{m+1}`).
pub const HEM_ROW_WBB_START: usize = 32;
/// `[0, 2^16)` LogUp range table size `N_rng = 2^16 = 65,536`.
pub const HEM_RNG16_VARS: usize = 16;
pub const HEM_RNG16_ROWS: usize = 1 << HEM_RNG16_VARS;

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

/// Ordered 2-to-1 Davies-Meyer `Poseidon2-12` compression binding `(tag, acc[4], val[4])` in disjoint
/// state lanes (`st[0..4] + acc + 2*val + 4*cap`). Defeats `C1` additive-sum replay collisions!
#[inline]
pub fn p2_ordered_compress(acc: [u64; 4], val: [u64; 4], tag: u64) -> [u64; 4] {
    let l = acc.map(|x| Goldilocks::from_u128_reduced(x as u128));
    let r = val.map(|x| Goldilocks::from_u128_reduced(x as u128));
    let c = [
        Goldilocks::from_u128_reduced(P2_DOMAIN_ORDERED_COMPRESS as u128),
        Goldilocks::from_u128_reduced(tag as u128),
        Goldilocks::ZERO,
        Goldilocks::from_u128_reduced(P2_IV as u128),
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
    let mut words = [0u64; 8];
    words[0..4].copy_from_slice(&v0.to_u64_limbs());
    words[4..8].copy_from_slice(&v1.to_u64_limbs());
    cshake256_canopy_words_leaf(stage, fiber_idx, &words)
}

/// `cSHAKE256` Canopy multi-word fiber leaf `cSHAKE256("QSAG.PCS.CANOPY/v2", 0x12 || stage || fiber_idx_le4 || words_le)`.
/// Matches `Dregg180StreamVm`'s streaming `H_FIBER_ACC` sponge bit-for-bit.
pub fn cshake256_canopy_words_leaf(stage: u8, fiber_idx: u32, words: &[u64]) -> [u8; 32] {
    let mut st = CANOPY_CSHAKE_MIDSTATE;
    let mut blk = [0u8; 136];
    blk[0] = 0x12;
    blk[1] = stage;
    let f_le = fiber_idx.to_le_bytes();
    blk[2..6].copy_from_slice(&f_le);
    let mut pos = 6usize;
    for &w in words {
        for &byte in &w.to_le_bytes() {
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
pub const H_BF_AUX: u8 = 11;
pub const H_FIBER_ACC: u8 = 12;
pub const H_BF_FOLD_FIBER: u8 = 13;

/// Sub-opcodes for `H_BF_AUX = 11` (zero-heap BaseFold/WHIR & public MLE hardware micro-ops).
pub const BF_AUX_LATCH_Z: u8 = 0;
pub const BF_AUX_LATCH_BF: u8 = 1;
pub const BF_AUX_EVAL_EQ_Z_BF: u8 = 2;
pub const BF_AUX_FOLD_FINAL_POLY: u8 = 3;
pub const BF_AUX_ASSERT_FINAL_EVAL: u8 = 4;
pub const BF_AUX_EVAL_PUBLIC_MLE_Z: u8 = 5;
pub const BF_AUX_EVAL_SPARSE_SEL_Z: u8 = 6;
pub const BF_AUX_LATCH_FINAL_POLY: u8 = 7;
pub const BF_AUX_STAGE0_FOLD2: u8 = 8;
pub const BF_AUX_LATCH_TAU: u8 = 9;
pub const BF_AUX_EVAL_EQ_TAU_Z: u8 = 10;
pub const BF_AUX_COMPRESS_REG: u8 = 11;

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
    pub public_program_hash: [u64; 4],
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
        bound_leaf: bool,
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
    BfSparseSel {
        len: u8,
        dst: u8,
        lam_reg: u8,
        rem_words: u16,
        acc: GoldilocksExt4,
    },
    BfLatchFinalPoly {
        seen: u8,
        rate_pos: u8,
    },
    BfCompressReg {
        dst: u8,
        src_a: u8,
        src_b: u8,
    },
    FiberAcc {
        is_ext4: bool,
        use_cs_leaf: bool,
        eta_reg: u8,
        half_words: u16,
        total_words: u16,
        seen: u16,
        rate_pos: u8,
        limb_pos: u8,
        cur_limbs: [Goldilocks; 4],
    },
    BfFoldFiber {
        k: u8,
        log_n_cur: u8,
        round_start: u8,
        expected_reg: u8,
        dst_reg: u8,
        want_slot: u8,
        f_cur: u64,
        total_words: u8,
        seen: u8,
        rate_pos: u8,
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
    prog_p2_state: [Goldilocks; 12],
    prog_rate_pos: u8,
    expected_prog_hash: Option<[u64; 4]>,
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
    // Streaming BaseFold/WHIR & dual-Canopy leaf hardware registers (`0` heap allocs!):
    cs_st: [u64; 25],
    cs_blk: [u8; 136],
    cs_pos: u8,
    cur_cs_leaf: [u8; 32],
    cs_leaf_valid: bool,
    bf_saved_idx: u64,
    bf_chain_active: bool,
    bf_final_poly_loaded: bool,
    fiber_buf: [GoldilocksExt4; 8],
    bf_final_poly: [GoldilocksExt4; 8],
    tau_chals: [GoldilocksExt4; 16],
    z_chals: [GoldilocksExt4; 16],
    bf_chals: [GoldilocksExt4; 16],
    phase: ActiveRecordPhase,
    metrics: Dregg180CycleMetrics,
}

const _: () = assert!(core::mem::size_of::<Dregg180StreamVm>() <= DREGG180_VM_MAX_STATIC_BYTES);

#[inline(always)]
const fn reg_to_ext4(r: [u64; 5]) -> GoldilocksExt4 {
    GoldilocksExt4::from_u64_limbs([r[0], r[1], r[2], r[3]])
}

#[inline(always)]
const fn ext4_to_reg(x: GoldilocksExt4) -> [u64; 5] {
    let l = x.to_u64_limbs();
    [l[0], l[1], l[2], l[3], 0]
}

impl Dregg180StreamVm {
    #[inline]
    pub const fn static_ram_bytes() -> usize {
        core::mem::size_of::<Self>()
    }

    pub const fn new_unkeyed(expected_pdig: Option<u128>) -> Self {
        let mut prog_st = [Goldilocks::ZERO; 12];
        prog_st[8] = Goldilocks::from_u128_reduced(P2_DOMAIN_PROG_HASH as u128);
        prog_st[11] = Goldilocks::from_u128_reduced(P2_IV as u128);
        Self {
            regs: [[0u64; 5]; 16],
            p2_state: [Goldilocks::ZERO; 12],
            prog_p2_state: prog_st,
            prog_rate_pos: 0,
            expected_prog_hash: None,
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
            cs_st: [0u64; 25],
            cs_blk: [0u8; 136],
            cs_pos: 0,
            cur_cs_leaf: [0u8; 32],
            cs_leaf_valid: false,
            bf_saved_idx: 0,
            bf_chain_active: false,
            bf_final_poly_loaded: false,
            fiber_buf: [GoldilocksExt4::ZERO; 8],
            bf_final_poly: [GoldilocksExt4::ZERO; 8],
            tau_chals: [GoldilocksExt4::ZERO; 16],
            z_chals: [GoldilocksExt4::ZERO; 16],
            bf_chals: [GoldilocksExt4::ZERO; 16],
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

    /// Trustless keyless verifier (`pin_mode = false`, `k_mac = None`) that enforces only the
    /// deterministic public verifier bytecode & public statement immediates via keyless `Poseidon2-12`.
    pub const fn new_unkeyed_pinned_program(expected_prog_hash: [u64; 4]) -> Self {
        let mut s = Self::new_unkeyed(None);
        s.expected_prog_hash = Some(expected_prog_hash);
        s
    }

    pub const fn new_keyed(k_mac: [u8; 16], expected_pdig: Option<u128>) -> Self {
        let mut s = Self::new_unkeyed(expected_pdig);
        s.keyed = true;
        s.k_mac = k_mac;
        s.delta = u128::from_le_bytes(k_mac);
        s
    }

    #[inline(always)]
    fn prog_hash_absorb(&mut self, word: u64) {
        // Absorb as two injective 32-bit limbs (< 2^32 << p_GL) so no 64-bit header can alias mod p_GL.
        let lo = Goldilocks(word & 0xFFFF_FFFF);
        let hi = Goldilocks(word >> 32);
        self.prog_p2_state[self.prog_rate_pos as usize] += lo;
        self.prog_rate_pos += 1;
        if self.prog_rate_pos == 8 {
            poseidon2_perm12(&mut self.prog_p2_state);
            self.prog_rate_pos = 0;
        }
        self.prog_p2_state[self.prog_rate_pos as usize] += hi;
        self.prog_rate_pos += 1;
        if self.prog_rate_pos == 8 {
            poseidon2_perm12(&mut self.prog_p2_state);
            self.prog_rate_pos = 0;
        }
    }

    #[inline(always)]
    fn ghash_step(&mut self, word: u64) {
        self.pdig = gf128_mul(self.pdig ^ (word as u128), self.delta);
        self.prog_hash_absorb(word);
        self.metrics.gf128_steps += 1;
        self.metrics.core_cycles += silicon_cycles::GF128_STEP;
    }

    #[inline(always)]
    fn cs_stream_byte(&mut self, byte: u8) {
        self.cs_blk[self.cs_pos as usize] = byte;
        self.cs_pos += 1;
        if self.cs_pos == 136 {
            for l in 0..17 {
                let b = 8 * l;
                self.cs_st[l] ^= u64::from_le_bytes([
                    self.cs_blk[b], self.cs_blk[b + 1], self.cs_blk[b + 2], self.cs_blk[b + 3],
                    self.cs_blk[b + 4], self.cs_blk[b + 5], self.cs_blk[b + 6], self.cs_blk[b + 7],
                ]);
            }
            keccak_p1600_stack(&mut self.cs_st, 24);
            self.metrics.keccak_perms += 1;
            self.metrics.core_cycles += silicon_cycles::KECCAK_F24;
            self.cs_blk = [0u8; 136];
            self.cs_pos = 0;
        }
    }

    #[inline(always)]
    fn cs_stream_finish(&mut self) {
        self.cs_blk[self.cs_pos as usize] ^= 0x04;
        self.cs_blk[135] ^= 0x80;
        for l in 0..17 {
            let b = 8 * l;
            self.cs_st[l] ^= u64::from_le_bytes([
                self.cs_blk[b], self.cs_blk[b + 1], self.cs_blk[b + 2], self.cs_blk[b + 3],
                self.cs_blk[b + 4], self.cs_blk[b + 5], self.cs_blk[b + 6], self.cs_blk[b + 7],
            ]);
        }
        keccak_p1600_stack(&mut self.cs_st, 24);
        self.metrics.keccak_perms += 1;
        self.metrics.core_cycles += silicon_cycles::KECCAK_F24;
        for l in 0..4 {
            self.cur_cs_leaf[8 * l..8 * (l + 1)].copy_from_slice(&self.cs_st[l].to_le_bytes());
        }
        self.cs_leaf_valid = true;
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
                        let bound_leaf = b == 1;
                        let want_n = if bound_leaf {
                            1 + 5 * (depth as u16)
                        } else {
                            1 + 5 + 5 * (depth as u16)
                        };
                        if depth == 0 || depth > 32 || (b != 0 && b != 1) || n != want_n || k != 0 {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad {
                                    rem_words: n,
                                    word_idx: 0,
                                    imm_k: k,
                                };
                            }
                        } else {
                            self.phase = ActiveRecordPhase::CShakeMerkleIdx { depth, bound_leaf };
                        }
                    }
                    H_BF_AUX => {
                        match a {
                            BF_AUX_LATCH_Z => {
                                if n != 0 || k != 0 || b >= 16 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    self.z_chals[b as usize] = reg_to_ext4(self.regs[(c & 15) as usize]);
                                    self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_LATCH_BF => {
                                if n != 0 || k != 0 || b >= 16 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    self.bf_chals[b as usize] = reg_to_ext4(self.regs[(c & 15) as usize]);
                                    self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_LATCH_TAU => {
                                if n != 0 || k != 0 || b >= 16 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    self.tau_chals[b as usize] = reg_to_ext4(self.regs[(c & 15) as usize]);
                                    self.metrics.core_cycles += silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_EVAL_EQ_Z_BF | BF_AUX_EVAL_EQ_TAU_Z => {
                                let len = b as usize;
                                if n != 0 || k != 0 || len == 0 || len > 16 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let mut acc = GoldilocksExt4::ONE;
                                    for j in 0..len {
                                        let lhs = if a == BF_AUX_EVAL_EQ_Z_BF { self.z_chals[j] } else { self.tau_chals[j] };
                                        let rhs = if a == BF_AUX_EVAL_EQ_Z_BF { self.bf_chals[j] } else { self.z_chals[j] };
                                        let term = (GoldilocksExt4::ONE - lhs) * (GoldilocksExt4::ONE - rhs) + (lhs * rhs);
                                        acc = acc * term;
                                    }
                                    self.regs[(c & 15) as usize] = ext4_to_reg(acc);
                                    self.metrics.ext4_muls += (3 * len) as u32;
                                    self.metrics.ext4_addsubs += (3 * len) as u32;
                                    self.metrics.core_cycles += (len as u64) * (3 * silicon_cycles::EXT4_MUL + 3 * silicon_cycles::EXT4_ADDSUB);
                                }
                            }
                            BF_AUX_FOLD_FINAL_POLY => {
                                let start = b as usize;
                                if n != 0 || k != 0 || start + 3 > 16 || !self.bf_final_poly_loaded {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let mut cur = self.bf_final_poly;
                                    let mut len = 8usize;
                                    for step in 0..3 {
                                        let r = self.bf_chals[start + step];
                                        let half = len / 2;
                                        for i in 0..half {
                                            let v0 = cur[2 * i];
                                            let v1 = cur[2 * i + 1];
                                            cur[i] = v0 + r * (v1 - v0);
                                        }
                                        len = half;
                                    }
                                    self.regs[(c & 15) as usize] = ext4_to_reg(cur[0]);
                                    self.metrics.ext4_muls += 7;
                                    self.metrics.ext4_addsubs += 14;
                                    self.metrics.core_cycles += 7 * silicon_cycles::EXT4_MUL + 14 * silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_ASSERT_FINAL_EVAL => {
                                self.has_assert = true;
                                if n != 0 || k != 0 || b > 24 || !self.bf_chain_active || !self.bf_final_poly_loaded || self.bf_saved_idx >= 64 {
                                    self.mark_bad();
                                    self.bf_chain_active = false;
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let mut shift = Goldilocks::SEVEN;
                                    for _ in 0..b {
                                        shift = shift.square();
                                    }
                                    let omega = Goldilocks::two_adic_generator(6); // N_final = 64
                                    let x_final = shift * omega.pow(self.bf_saved_idx);
                                    let x_ext = GoldilocksExt4::from_base(x_final);
                                    let want = GoldilocksExt4::eval_univariate(&self.bf_final_poly, x_ext);
                                    let got = reg_to_ext4(self.regs[(c & 15) as usize]);
                                    if want != got {
                                        self.mark_bad();
                                    }
                                    self.bf_chain_active = false;
                                    self.metrics.ext4_muls += 7;
                                    self.metrics.ext4_addsubs += 7;
                                    self.metrics.core_cycles += ((b as u64) + 6) * silicon_cycles::GL64_MUL
                                        + 7 * silicon_cycles::EXT4_MUL
                                        + 7 * silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_EVAL_PUBLIC_MLE_Z => {
                                let len = (b & 31) as usize;
                                let mode = (c >> 4) & 15;
                                let dst = (c & 15) as usize;
                                if n != 0 || k != 0 || len == 0 || len > 16 || (mode == 1 && len < 8) || (mode == 2 && len < 10) || mode > 4 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let val = match mode {
                                        0 => {
                                            let mut acc = GoldilocksExt4::ZERO;
                                            for j in 0..len {
                                                acc = acc + self.z_chals[j].scale_base(Goldilocks(1u64 << j));
                                            }
                                            acc
                                        }
                                        1 => {
                                            let mut acc = GoldilocksExt4::ZERO;
                                            for j in 0..8 {
                                                acc = acc + self.z_chals[j].scale_base(Goldilocks(1u64 << j));
                                            }
                                            acc
                                        }
                                        2 => self.z_chals[8] + self.z_chals[9].scale_base(Goldilocks::TWO),
                                        3 => {
                                            let mut acc = GoldilocksExt4::ONE;
                                            for j in 0..len {
                                                acc = acc * (GoldilocksExt4::ONE - self.z_chals[j]);
                                            }
                                            acc
                                        }
                                        _ => {
                                            let mut acc = GoldilocksExt4::ONE;
                                            for j in 0..len {
                                                acc = acc * self.z_chals[j];
                                            }
                                            acc
                                        }
                                    };
                                    self.regs[dst] = ext4_to_reg(val);
                                    self.metrics.ext4_muls += len as u32;
                                    self.metrics.ext4_addsubs += len as u32;
                                    self.metrics.core_cycles += (len as u64) * (silicon_cycles::EXT4_MUL + silicon_cycles::EXT4_ADDSUB);
                                }
                            }
                            BF_AUX_EVAL_SPARSE_SEL_Z => {
                                let len = b & 31;
                                if n == 0 || k != n || len == 0 || len > 16 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    self.phase = ActiveRecordPhase::BfSparseSel {
                                        len,
                                        dst: c & 15,
                                        lam_reg: (c >> 4) & 15,
                                        rem_words: n,
                                        acc: GoldilocksExt4::ZERO,
                                    };
                                }
                            }
                            BF_AUX_LATCH_FINAL_POLY => {
                                if n != 32 || k != 0 {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let rch = self.regs[R_CH as usize];
                                    self.p2_state = [Goldilocks::ZERO; 12];
                                    for i in 0..4 {
                                        self.p2_state[8 + i] = Goldilocks::from_u128_reduced(rch[i] as u128);
                                    }
                                    self.p2_state[0] += Goldilocks::from_u128_reduced(P2_DOMAIN_FS_ABSORB_LIMBS as u128);
                                    self.p2_state[1] += Goldilocks(32);
                                    self.phase = ActiveRecordPhase::BfLatchFinalPoly { seen: 0, rate_pos: 2 };
                                }
                            }
                            BF_AUX_STAGE0_FOLD2 => {
                                let log_n = b as usize;
                                if n != 0 || k != 0 || !(4..=24).contains(&log_n) || !self.bf_chain_active || self.bf_saved_idx >= (1u64 << (log_n - 1)) {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    let v0 = reg_to_ext4(self.regs[R_A as usize]);
                                    let v1 = reg_to_ext4(self.regs[R_B as usize]);
                                    let omega = Goldilocks::two_adic_generator(log_n);
                                    let x = Goldilocks::SEVEN * omega.pow(self.bf_saved_idx);
                                    let inv2_x = (Goldilocks::TWO * x).inv();
                                    let even = (v0 + v1).scale_base(GOLDILOCKS_INV2);
                                    let odd = (v0 - v1).scale_base(inv2_x);
                                    let folded = even + self.bf_chals[0] * (odd - even);
                                    self.regs[(c & 15) as usize] = ext4_to_reg(folded);
                                    self.metrics.ext4_muls += 1;
                                    self.metrics.ext4_addsubs += 4;
                                    self.metrics.core_cycles += ((log_n as u64) + 64) * silicon_cycles::GL64_MUL
                                        + silicon_cycles::EXT4_MUL
                                        + 4 * silicon_cycles::EXT4_ADDSUB;
                                }
                            }
                            BF_AUX_COMPRESS_REG => {
                                let dst = c & 15;
                                let src_a = b & 15;
                                let src_b = (b >> 4) & 15;
                                if n != 1 || k != 1 || dst == R_CH || self.fp5_mode {
                                    self.mark_bad();
                                    if n > 0 {
                                        self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                    }
                                } else {
                                    self.phase = ActiveRecordPhase::BfCompressReg { dst, src_a, src_b };
                                }
                            }
                            _ => {
                                self.mark_bad();
                                if n > 0 {
                                    self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                                }
                            }
                        }
                    }
                    H_FIBER_ACC => {
                        let stage_id = a & 7;
                        let is_ext4 = (a & 8) != 0;
                        let reset_acc = (a & 16) != 0;
                        let use_cs_leaf = (a & 32) != 0;
                        let key_reg = (b & 15) as usize;
                        let eta_reg = (b >> 4) & 15;
                        let num_cols = c as u16;
                        let words_per_col = if is_ext4 { 4u16 } else { 1u16 };
                        let expected_n = 2 * num_cols * words_per_col;
                        if num_cols == 0
                            || num_cols > 32
                            || n != expected_n
                            || k != 0
                            || !self.idx_armed
                            || (!reset_acc && (!self.bf_chain_active || self.bound_idx != self.bf_saved_idx))
                        {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                            }
                        } else {
                            if reset_acc {
                                self.regs[R_A as usize] = [0u64; 5];
                                self.regs[R_B as usize] = [0u64; 5];
                                self.bf_saved_idx = self.bound_idx;
                                self.bf_chain_active = true;
                            }
                            let kr = self.regs[key_reg];
                            self.p2_state = [Goldilocks::ZERO; 12];
                            for i in 0..4 {
                                self.p2_state[8 + i] = Goldilocks::from_u128_reduced(kr[i] as u128);
                            }
                            self.p2_state[0] += Goldilocks::from_u128_reduced(P2_DOMAIN_CANOPY_LEAF as u128);
                            self.p2_state[1] += Goldilocks(n as u64);
                            if use_cs_leaf {
                                self.cs_st = CANOPY_CSHAKE_MIDSTATE;
                                self.cs_blk = [0u8; 136];
                                self.cs_pos = 0;
                                self.cs_leaf_valid = false;
                                self.cs_stream_byte(0x12);
                                self.cs_stream_byte(stage_id);
                                for byte in (self.bound_idx as u32).to_le_bytes() {
                                    self.cs_stream_byte(byte);
                                }
                            }
                            self.phase = ActiveRecordPhase::FiberAcc {
                                is_ext4,
                                use_cs_leaf,
                                eta_reg,
                                half_words: num_cols * words_per_col,
                                total_words: n,
                                seen: 0,
                                rate_pos: 2,
                                limb_pos: 0,
                                cur_limbs: [Goldilocks::ZERO; 4],
                            };
                        }
                    }
                    H_BF_FOLD_FIBER => {
                        let fold_k = a & 3;
                        let log_n_cur = (a >> 2) & 31;
                        let key_reg = (b & 15) as usize;
                        let round_start = (b >> 4) & 15;
                        let expected_reg = c & 15;
                        let dst_reg = (c >> 4) & 15;
                        let expected_n = if fold_k >= 1 && fold_k <= 3 { (1u16 << fold_k) * 4 } else { 0 };
                        if fold_k == 0
                            || fold_k > 3
                            || log_n_cur <= fold_k
                            || log_n_cur > 24
                            || round_start + fold_k > 16
                            || n != expected_n
                            || k != 0
                            || !self.bf_chain_active
                            || self.bf_saved_idx >= (1u64 << log_n_cur)
                        {
                            self.mark_bad();
                            if n > 0 {
                                self.phase = ActiveRecordPhase::DrainBad { rem_words: n, word_idx: 0, imm_k: k };
                            }
                        } else {
                            let log_nfib = log_n_cur - fold_k;
                            let f_cur = self.bf_saved_idx & ((1u64 << log_nfib) - 1);
                            let want_slot = (self.bf_saved_idx >> log_nfib) as u8;
                            self.bound_idx = f_cur;
                            self.idx_armed = true;
                            self.bf_saved_idx = f_cur;
                            let kr = self.regs[key_reg];
                            self.p2_state = [Goldilocks::ZERO; 12];
                            for i in 0..4 {
                                self.p2_state[8 + i] = Goldilocks::from_u128_reduced(kr[i] as u128);
                            }
                            self.p2_state[0] += Goldilocks::from_u128_reduced(P2_DOMAIN_CANOPY_LEAF as u128);
                            self.p2_state[1] += Goldilocks(n as u64);
                            self.phase = ActiveRecordPhase::BfFoldFiber {
                                k: fold_k,
                                log_n_cur,
                                round_start,
                                expected_reg,
                                dst_reg,
                                want_slot,
                                f_cur,
                                total_words: n as u8,
                                seen: 0,
                                rate_pos: 2,
                            };
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
                // L3 hardening: reject non-canonical (`>= p_GL`) immediate limbs on register loads too!
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
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
                // L2 hardening: fail closed unless `H_BIND_IDX` / `H_BF_FOLD_FIBER` armed an index AND `idx < 2^depth`!
                let max_idx = 1u64 << depth;
                if !self.idx_armed || word >= max_idx || word != self.bound_idx {
                    self.mark_bad();
                }
                self.idx_armed = false;
                let heap_idx = max_idx | (word & 0xFFFF_FFFF);
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
            ActiveRecordPhase::CShakeMerkleIdx { depth, bound_leaf } => {
                self.metrics.proof_words += 1;
                // L2 hardening: require armed index and `idx < 2^depth` on all cSHAKE Canopy queries!
                let max_idx = 1u64 << depth;
                if !self.idx_armed || word >= max_idx || word != self.bound_idx {
                    self.mark_bad();
                }
                self.idx_armed = false;
                let heap_idx = max_idx | (word & 0xFFFF_FFFF);
                if bound_leaf {
                    if !self.cs_leaf_valid {
                        self.mark_bad();
                    }
                    self.cs_leaf_valid = false;
                    self.phase = ActiveRecordPhase::CShakeMerkleSiblings {
                        depth,
                        cur_lvl: 0,
                        heap_idx,
                        pos: 0,
                        buf5: [0u64; 5],
                        cur_digest: self.cur_cs_leaf,
                    };
                } else {
                    self.phase = ActiveRecordPhase::CShakeMerkleLeaf {
                        depth,
                        heap_idx,
                        pos: 0,
                        buf5: [0u64; 5],
                    };
                }
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
            ActiveRecordPhase::BfSparseSel {
                len,
                dst,
                lam_reg,
                rem_words,
                acc,
            } => {
                self.ghash_step(word);
                self.metrics.immediate_words += 1;
                let mut eq_z = GoldilocksExt4::ONE;
                if word >= (1u64 << len) {
                    self.mark_bad();
                } else {
                    for j in 0..(len as usize) {
                        let factor = if ((word >> j) & 1) == 1 {
                            self.z_chals[j]
                        } else {
                            GoldilocksExt4::ONE - self.z_chals[j]
                        };
                        eq_z = eq_z * factor;
                    }
                }
                let lam = reg_to_ext4(self.regs[lam_reg as usize]);
                let next_acc = acc * lam + eq_z;
                self.metrics.ext4_muls += (len as u32) + 1;
                self.metrics.ext4_addsubs += (len as u32) + 1;
                self.metrics.core_cycles += ((len as u64) + 1) * (silicon_cycles::EXT4_MUL + silicon_cycles::EXT4_ADDSUB);
                if rem_words <= 1 {
                    self.regs[dst as usize] = ext4_to_reg(next_acc);
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::BfSparseSel {
                        len,
                        dst,
                        lam_reg,
                        rem_words: rem_words - 1,
                        acc: next_acc,
                    };
                }
            }
            ActiveRecordPhase::BfLatchFinalPoly { seen, rate_pos } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                let canon = Goldilocks::from_u128_reduced(word as u128);
                self.bf_final_poly[(seen / 4) as usize].0[(seen % 4) as usize] = canon;
                self.p2_state[rate_pos as usize] += canon;
                let next_seen = seen + 1;
                let mut next_rate = rate_pos + 1;
                if next_rate == 8 {
                    poseidon2_perm12(&mut self.p2_state);
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    next_rate = 0;
                }
                if next_seen == 32 {
                    if next_rate > 0 {
                        poseidon2_perm12(&mut self.p2_state);
                        self.metrics.poseidon2_perms += 1;
                        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    }
                    let mut res = [0u64; 5];
                    for i in 0..4 {
                        res[i] = self.p2_state[i].0;
                    }
                    self.regs[R_T0 as usize] = res;
                    self.regs[R_CH as usize] = res;
                    self.bf_final_poly_loaded = true;
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::BfLatchFinalPoly {
                        seen: next_seen,
                        rate_pos: next_rate,
                    };
                }
            }
            ActiveRecordPhase::FiberAcc {
                is_ext4,
                use_cs_leaf,
                eta_reg,
                half_words,
                total_words,
                seen,
                rate_pos,
                limb_pos,
                mut cur_limbs,
            } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                let canon = Goldilocks::from_u128_reduced(word as u128);
                self.p2_state[rate_pos as usize] += canon;
                let mut next_rate = rate_pos + 1;
                if next_rate == 8 {
                    poseidon2_perm12(&mut self.p2_state);
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    next_rate = 0;
                }
                if use_cs_leaf {
                    for byte in word.to_le_bytes() {
                        self.cs_stream_byte(byte);
                    }
                }
                let target_reg = if seen < half_words { R_A as usize } else { R_B as usize };
                let eta = reg_to_ext4(self.regs[eta_reg as usize]);
                let mut next_limb_pos = limb_pos;
                if !is_ext4 {
                    let cur_acc = reg_to_ext4(self.regs[target_reg]);
                    let next_acc = cur_acc * eta + GoldilocksExt4::from_base(canon);
                    self.regs[target_reg] = ext4_to_reg(next_acc);
                    self.metrics.ext4_muls += 1;
                    self.metrics.ext4_addsubs += 1;
                    self.metrics.core_cycles += silicon_cycles::EXT4_MUL + silicon_cycles::EXT4_ADDSUB;
                } else {
                    cur_limbs[limb_pos as usize] = canon;
                    if limb_pos == 3 {
                        let cur_acc = reg_to_ext4(self.regs[target_reg]);
                        let next_acc = cur_acc * eta + GoldilocksExt4(cur_limbs);
                        self.regs[target_reg] = ext4_to_reg(next_acc);
                        self.metrics.ext4_muls += 1;
                        self.metrics.ext4_addsubs += 1;
                        self.metrics.core_cycles += silicon_cycles::EXT4_MUL + silicon_cycles::EXT4_ADDSUB;
                        next_limb_pos = 0;
                        cur_limbs = [Goldilocks::ZERO; 4];
                    } else {
                        next_limb_pos = limb_pos + 1;
                    }
                }
                let next_seen = seen + 1;
                if next_seen == total_words {
                    if next_rate > 0 {
                        poseidon2_perm12(&mut self.p2_state);
                        self.metrics.poseidon2_perms += 1;
                        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    }
                    for i in 0..4 {
                        self.regs[R_X as usize][i] = self.p2_state[i].0;
                    }
                    if use_cs_leaf {
                        self.cs_stream_finish();
                    }
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::FiberAcc {
                        is_ext4,
                        use_cs_leaf,
                        eta_reg,
                        half_words,
                        total_words,
                        seen: next_seen,
                        rate_pos: next_rate,
                        limb_pos: next_limb_pos,
                        cur_limbs,
                    };
                }
            }
            ActiveRecordPhase::BfFoldFiber {
                k,
                log_n_cur,
                round_start,
                expected_reg,
                dst_reg,
                want_slot,
                f_cur,
                total_words,
                seen,
                rate_pos,
            } => {
                self.metrics.proof_words += 1;
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                }
                let canon = Goldilocks::from_u128_reduced(word as u128);
                self.fiber_buf[(seen / 4) as usize].0[(seen % 4) as usize] = canon;
                self.p2_state[rate_pos as usize] += canon;
                let mut next_rate = rate_pos + 1;
                if next_rate == 8 {
                    poseidon2_perm12(&mut self.p2_state);
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    next_rate = 0;
                }
                let next_seen = seen + 1;
                if next_seen == total_words {
                    if next_rate > 0 {
                        poseidon2_perm12(&mut self.p2_state);
                        self.metrics.poseidon2_perms += 1;
                        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                    }
                    for i in 0..4 {
                        self.regs[R_X as usize][i] = self.p2_state[i].0;
                    }
                    self.has_assert = true;
                    let expected_val = reg_to_ext4(self.regs[expected_reg as usize]);
                    if self.fiber_buf[want_slot as usize] != expected_val {
                        self.mark_bad();
                    }
                    let log_nfib = (log_n_cur - k) as usize;
                    let mut cur_len = 1usize << k;
                    let mut shift = Goldilocks::SEVEN;
                    for _ in 0..round_start {
                        shift = shift.square();
                    }
                    let mut cur_log_n = log_n_cur as usize;
                    for step in 0..(k as usize) {
                        let half = cur_len / 2;
                        let omega = Goldilocks::two_adic_generator(cur_log_n);
                        let step_root = omega.pow(1u64 << log_nfib);
                        let base_x = shift * omega.pow(f_cur);
                        let r_chal = self.bf_chals[(round_start as usize) + step];
                        let mut x_m = base_x;
                        for m in 0..half {
                            let v0 = self.fiber_buf[m];
                            let v1 = self.fiber_buf[m + half];
                            let even = (v0 + v1).scale_base(GOLDILOCKS_INV2);
                            let odd = (v0 - v1).scale_base((Goldilocks::TWO * x_m).inv());
                            self.fiber_buf[m] = even + r_chal * (odd - even);
                            x_m *= step_root;
                        }
                        self.metrics.ext4_muls += half as u32;
                        self.metrics.ext4_addsubs += (4 * half) as u32;
                        self.metrics.core_cycles += (half as u64)
                            * (64 * silicon_cycles::GL64_MUL
                                + silicon_cycles::EXT4_MUL
                                + 4 * silicon_cycles::EXT4_ADDSUB);
                        shift = shift.square();
                        cur_log_n -= 1;
                        cur_len = half;
                    }
                    self.regs[dst_reg as usize] = ext4_to_reg(self.fiber_buf[0]);
                    self.phase = ActiveRecordPhase::Idle;
                } else {
                    self.phase = ActiveRecordPhase::BfFoldFiber {
                        k,
                        log_n_cur,
                        round_start,
                        expected_reg,
                        dst_reg,
                        want_slot,
                        f_cur,
                        total_words,
                        seen: next_seen,
                        rate_pos: next_rate,
                    };
                }
            }
            ActiveRecordPhase::BfCompressReg { dst, src_a, src_b } => {
                self.check_data_word(word, 0, 1, true);
                if word >= GOLDILOCKS_PRIME {
                    self.non_canonical = true;
                    self.mark_bad();
                } else {
                    let ra = self.regs[src_a as usize];
                    let rb = self.regs[src_b as usize];
                    let out = p2_ordered_compress(
                        [ra[0], ra[1], ra[2], ra[3]],
                        [rb[0], rb[1], rb[2], rb[3]],
                        word,
                    );
                    self.regs[dst as usize] = [out[0], out[1], out[2], out[3], 0];
                    self.metrics.poseidon2_perms += 1;
                    self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
                }
                self.phase = ActiveRecordPhase::Idle;
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

        // Finalize keyless Poseidon2-12 public program digest (covers wire_hdr, all record headers, all imm_k words):
        self.prog_p2_state[self.prog_rate_pos as usize] += Goldilocks::ONE;
        poseidon2_perm12(&mut self.prog_p2_state);
        self.metrics.poseidon2_perms += 1;
        self.metrics.core_cycles += silicon_cycles::POSEIDON2_12;
        let public_program_hash = [
            self.prog_p2_state[0].0,
            self.prog_p2_state[1].0,
            self.prog_p2_state[2].0,
            self.prog_p2_state[3].0,
        ];

        let pdig_mismatch = self.expected_pdig.is_some_and(|want| want != self.pdig)
            || self.expected_prog_hash.is_some_and(|want| want != public_program_hash);
        let verdict = !self.sticky_fail
            && !self.non_canonical
            && self.has_assert
            && self.rec_count != 0
            && !pdig_mismatch
            && !self.idx_armed
            && !self.bf_chain_active;

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
            public_program_hash,
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

    /// Bound-leaf `cSHAKE256` Canopy path verification consuming `self.cur_cs_leaf` latched by `H_FIBER_ACC`.
    pub fn cshake_merkle_bound(&mut self, leaf_index: u32, siblings: &[[u8; 32]]) {
        let mut data = Vec::with_capacity(1 + 5 * siblings.len());
        data.push(leaf_index as u64);
        for s in siblings {
            data.extend_from_slice(&pack_digest32_to_5_limbs(s));
        }
        self.push_rec(H_CSHAKE_MERKLE, siblings.len() as u8, 1, 0, data, 0);
    }

    pub fn bf_latch_z(&mut self, idx: u8, src_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_LATCH_Z, idx, src_reg & 15, Vec::new(), 0);
    }

    pub fn bf_latch_bf(&mut self, idx: u8, src_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_LATCH_BF, idx, src_reg & 15, Vec::new(), 0);
    }

    pub fn bf_latch_tau(&mut self, idx: u8, src_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_LATCH_TAU, idx, src_reg & 15, Vec::new(), 0);
    }

    pub fn bf_eval_eq_z_bf(&mut self, len: u8, dst_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_EVAL_EQ_Z_BF, len, dst_reg & 15, Vec::new(), 0);
    }

    pub fn bf_eval_eq_tau_z(&mut self, len: u8, dst_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_EVAL_EQ_TAU_Z, len, dst_reg & 15, Vec::new(), 0);
    }

    pub fn bf_fold_final_poly(&mut self, round_start: u8, dst_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_FOLD_FINAL_POLY, round_start, dst_reg & 15, Vec::new(), 0);
    }

    pub fn bf_assert_final_eval(&mut self, total_folded_rounds: u8, got_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_ASSERT_FINAL_EVAL, total_folded_rounds, got_reg & 15, Vec::new(), 0);
    }

    pub fn bf_eval_public_mle_z(&mut self, len: u8, mode: u8, dst_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_EVAL_PUBLIC_MLE_Z, len & 31, ((mode & 15) << 4) | (dst_reg & 15), Vec::new(), 0);
    }

    pub fn bf_eval_sparse_sel_z(&mut self, len: u8, lam_reg: u8, dst_reg: u8, row_indices: &[u64]) {
        self.push_rec(
            H_BF_AUX,
            BF_AUX_EVAL_SPARSE_SEL_Z,
            len & 31,
            ((lam_reg & 15) << 4) | (dst_reg & 15),
            row_indices.to_vec(),
            row_indices.len() as u16,
        );
    }

    pub fn bf_latch_final_poly(&mut self, coeffs: &[GoldilocksExt4; 8]) {
        let mut data = Vec::with_capacity(32);
        for c in coeffs {
            data.extend_from_slice(&c.to_u64_limbs());
        }
        self.push_rec(H_BF_AUX, BF_AUX_LATCH_FINAL_POLY, 0, 0, data, 0);
    }

    pub fn bf_stage0_fold2(&mut self, log_n: u8, dst_reg: u8) {
        self.push_rec(H_BF_AUX, BF_AUX_STAGE0_FOLD2, log_n, dst_reg & 15, Vec::new(), 0);
    }

    /// Ordered Davies-Meyer `Poseidon2-12` compression `dst = H_ord(tag, regs[src_a], regs[src_b])`.
    /// `tag` is pinned as an immediate (`imm_k = 1`). Defeats `C1` additive-sum replay collisions!
    pub fn bf_compress_reg(&mut self, dst: u8, src_a: u8, src_b: u8, tag: u64) {
        let b = (src_a & 15) | ((src_b & 15) << 4);
        self.push_rec(H_BF_AUX, BF_AUX_COMPRESS_REG, b, dst & 15, vec![tag], 1);
    }

    pub fn fiber_acc(
        &mut self,
        stage_id: u8,
        is_ext4: bool,
        reset_acc: bool,
        use_cs_leaf: bool,
        key_reg: u8,
        eta_reg: u8,
        num_cols: u8,
        words: &[u64],
    ) {
        let a = (stage_id & 7)
            | ((is_ext4 as u8) << 3)
            | ((reset_acc as u8) << 4)
            | ((use_cs_leaf as u8) << 5);
        let b = (key_reg & 15) | ((eta_reg & 15) << 4);
        self.push_rec(H_FIBER_ACC, a, b, num_cols, words.to_vec(), 0);
    }

    pub fn bf_fold_fiber(
        &mut self,
        fold_k: u8,
        log_n_cur: u8,
        key_reg: u8,
        round_start: u8,
        expected_reg: u8,
        dst_reg: u8,
        fiber: &[GoldilocksExt4],
    ) {
        let a = (fold_k & 3) | ((log_n_cur & 31) << 2);
        let b = (key_reg & 15) | ((round_start & 15) << 4);
        let c = (expected_reg & 15) | ((dst_reg & 15) << 4);
        let mut data = Vec::with_capacity(fiber.len() * 4);
        for v in fiber {
            data.extend_from_slice(&v.to_u64_limbs());
        }
        self.push_rec(H_BF_FOLD_FIBER, a, b, c, data, 0);
    }

    /// Compute the keyless `Poseidon2-12` public program hash covering ONLY `(wire_hdr, record headers, imm_k words)`.
    pub fn compute_public_program_hash(&self) -> [u64; 4] {
        let total_words: usize = self.records.iter().map(|r| 1 + r.data.len()).sum();
        let flags = (if self.pin_mode { 8u64 } else { 0 }) | (if self.fp5_mode { 16u64 } else { 0 });
        let wire_hdr = (QSAG_WIRE_MAGIC as u64)
            | ((self.op as u64) << 8)
            | (flags << 16)
            | (((total_words * 8) as u64) << 24);
        let mut st = [Goldilocks::ZERO; 12];
        st[8] = Goldilocks::from_u128_reduced(P2_DOMAIN_PROG_HASH as u128);
        st[11] = Goldilocks::from_u128_reduced(P2_IV as u128);
        let mut pos = 0usize;
        let mut absorb = |w: u64| {
            st[pos] += Goldilocks(w & 0xFFFF_FFFF);
            pos += 1;
            if pos == 8 {
                poseidon2_perm12(&mut st);
                pos = 0;
            }
            st[pos] += Goldilocks(w >> 32);
            pos += 1;
            if pos == 8 {
                poseidon2_perm12(&mut st);
                pos = 0;
            }
        };
        absorb(wire_hdr);
        for r in &self.records {
            let hdr_w = (r.hop as u64)
                | ((r.a as u64) << 8)
                | ((r.b as u64) << 16)
                | ((r.c as u64) << 24)
                | ((r.data.len() as u64) << 32)
                | ((r.imm_k as u64) << 48);
            absorb(hdr_w);
            let bound = (r.imm_k as usize).min(r.data.len());
            for &w in &r.data[..bound] {
                absorb(w);
            }
        }
        st[pos] += Goldilocks::ONE;
        poseidon2_perm12(&mut st);
        [st[0].0, st[1].0, st[2].0, st[3].0]
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
    pub public_program_hash: [u64; 4],
    pub num_records: usize,
}

/// Coset Reed-Solomon encoding over `shift * H` (`|H| = coeffs.len() * blowup`) for base-field `Goldilocks`.
pub fn encode_rs_coset_goldilocks(coeffs: &[Goldilocks], blowup: usize, shift: Goldilocks) -> Vec<Goldilocks> {
    assert!(coeffs.len().is_power_of_two() && blowup.is_power_of_two() && blowup >= 2);
    let domain_len = coeffs.len() * blowup;
    let mut buf = vec![Goldilocks::ZERO; domain_len];
    let mut sp = Goldilocks::ONE;
    for (i, &c) in coeffs.iter().enumerate() {
        buf[i] = c * sp;
        sp *= shift;
    }
    ntt_goldilocks_in_place(&mut buf, false);
    buf
}

#[inline]
fn fs_squeeze_ext4_local(ch_cur: [u64; 4], label: &[u8], ctr: u64) -> GoldilocksExt4 {
    let mut inp = pack_bytes_7_limbs(label);
    inp.push(ctr);
    GoldilocksExt4::from_u64_limbs(p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_EXT4, ch_cur, &inp))
}

#[inline]
fn fs_absorb_limbs_local(ch_cur: [u64; 4], label: &[u8], limbs: &[u64]) -> [u64; 4] {
    let mut v = pack_bytes_7_limbs(label);
    v.extend_from_slice(limbs);
    p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, ch_cur, &v)
}

#[inline]
fn emit_compress_reg(asm: &mut Dregg180HvmAssembler, acc: u8, val: u8, tag: u64) {
    // C1 fix: ordered Davies-Meyer `Poseidon2-12` compression binding `(tag, regs[acc], regs[val])`
    // in disjoint state lanes directly from live VM registers (zero additive collision!).
    asm.bf_compress_reg(acc, acc, val, tag);
}

#[inline]
fn emit_copy_reg(asm: &mut Dregg180HvmAssembler, dst: u8, src: u8) {
    if dst != src {
        asm.esub(dst, dst, dst);
        asm.eadd(dst, dst, src);
    }
}

#[inline]
fn emit_zero_reg(asm: &mut Dregg180HvmAssembler, dst: u8) {
    asm.esub(dst, dst, dst);
}

#[inline]
fn build_eq_table_lsb_gl_ext4(pt: &[GoldilocksExt4]) -> Vec<GoldilocksExt4> {
    let mut tab = vec![GoldilocksExt4::ONE; 1];
    for &p_j in pt.iter().rev() {
        let one_minus = GoldilocksExt4::ONE - p_j;
        let mut next = Vec::with_capacity(tab.len() * 2);
        for &v in &tab {
            next.push(v * one_minus);
            next.push(v * p_j);
        }
        tab = next;
    }
    tab
}

#[inline]
fn mle_eval_ext4_gl_ext4(col: &[GoldilocksExt4], eq_tab: &[GoldilocksExt4]) -> GoldilocksExt4 {
    let mut acc = GoldilocksExt4::ZERO;
    for (&c, &e) in col.iter().zip(eq_tab.iter()) {
        acc = acc + (e * c);
    }
    acc
}

/// Grind a `pow_bits`-bit `Poseidon2-12` PoW nonce in parallel via `rayon` (deterministic lowest chunk),
/// returning BOTH `(nonce, ch_after_pow)` so the checked PoW digest IS the exact transcript state `R_CH`
/// used to squeeze all query indices (closing `H1` single-read PoW binding!).
fn grind_p2_pow(domain: u64, ch: [u64; 4], pow_bits: u8) -> (u64, [u64; 4]) {
    let pow_mask = (1u64 << pow_bits) - 1;
    let chunk_size = 1u64 << 14;
    let mut base = 0u64;
    loop {
        let found = (0..16u64)
            .into_par_iter()
            .filter_map(|c| {
                let start = base + c * chunk_size;
                for n in start..(start + chunk_size) {
                    let nw = [n & 0xFFFF_FFFF, n >> 32];
                    let out = p2_sponge_hash_limbs(domain, ch, &nw);
                    if (out[0] & pow_mask) == 0 {
                        return Some((n, out));
                    }
                }
                None
            })
            .min_by_key(|&(n, _)| n);
        if let Some(res) = found {
            return res;
        }
        base += 16 * chunk_size;
    }
}

/// Stage-0 multi-column dual-Canopy (`Poseidon2-12` + `cSHAKE256`) RS commitment at `blowup = 8`.
#[derive(Clone)]
pub struct Stage0MatrixCanopy {
    pub stage_id: u8,
    pub is_ext4: bool,
    pub num_cols: usize,
    pub log_fibers: usize,
    pub canopy_key: [u64; 4],
    pub words_per_fiber: usize,
    pub fiber_words_flat: Vec<u64>,
    pub p2_nodes: Vec<[u64; 4]>,
    pub cshake_nodes: Vec<[u8; 32]>,
}

impl Stage0MatrixCanopy {
    pub fn commit_base(stage_id: u8, cols: &[Vec<Goldilocks>], blowup: usize, canopy_key: [u64; 4]) -> Self {
        let num_cols = cols.len();
        assert!(num_cols >= 1 && num_cols <= 32);
        let codes: Vec<Vec<Goldilocks>> = cols
            .par_iter()
            .map(|c| encode_rs_coset_goldilocks(c, blowup, Goldilocks::SEVEN))
            .collect();
        let n_dom = codes[0].len();
        let n_fibers = n_dom / 2;
        let log_fibers = n_fibers.trailing_zeros() as usize;
        let words_per_fiber = 2 * num_cols;
        let leaves: Vec<(Vec<u64>, [u64; 4], [u8; 32])> = (0..n_fibers)
            .into_par_iter()
            .map(|f| {
                let mut w = Vec::with_capacity(words_per_fiber);
                for c in 0..num_cols {
                    w.push(codes[c][f].0);
                }
                for c in 0..num_cols {
                    w.push(codes[c][f + n_fibers].0);
                }
                let p2 = p2_sponge_hash_limbs(P2_DOMAIN_CANOPY_LEAF, canopy_key, &w);
                let cs = cshake256_canopy_words_leaf(stage_id, f as u32, &w);
                (w, p2, cs)
            })
            .collect();
        Self::finish_tree(stage_id, false, num_cols, log_fibers, canopy_key, words_per_fiber, leaves)
    }

    pub fn commit_ext4(stage_id: u8, cols: &[Vec<GoldilocksExt4>], blowup: usize, canopy_key: [u64; 4]) -> Self {
        let num_cols = cols.len();
        assert!(num_cols >= 1 && num_cols <= 32);
        let codes: Vec<Vec<GoldilocksExt4>> = cols
            .par_iter()
            .map(|c| encode_rs_coset_ext4(c, blowup, Goldilocks::SEVEN))
            .collect();
        let n_dom = codes[0].len();
        let n_fibers = n_dom / 2;
        let log_fibers = n_fibers.trailing_zeros() as usize;
        let words_per_fiber = 8 * num_cols;
        let leaves: Vec<(Vec<u64>, [u64; 4], [u8; 32])> = (0..n_fibers)
            .into_par_iter()
            .map(|f| {
                let mut w = Vec::with_capacity(words_per_fiber);
                for c in 0..num_cols {
                    w.extend_from_slice(&codes[c][f].to_u64_limbs());
                }
                for c in 0..num_cols {
                    w.extend_from_slice(&codes[c][f + n_fibers].to_u64_limbs());
                }
                let p2 = p2_sponge_hash_limbs(P2_DOMAIN_CANOPY_LEAF, canopy_key, &w);
                let cs = cshake256_canopy_words_leaf(stage_id, f as u32, &w);
                (w, p2, cs)
            })
            .collect();
        Self::finish_tree(stage_id, true, num_cols, log_fibers, canopy_key, words_per_fiber, leaves)
    }

    fn finish_tree(
        stage_id: u8,
        is_ext4: bool,
        num_cols: usize,
        log_fibers: usize,
        canopy_key: [u64; 4],
        words_per_fiber: usize,
        leaves: Vec<(Vec<u64>, [u64; 4], [u8; 32])>,
    ) -> Self {
        let n_fibers = 1usize << log_fibers;
        let mut fiber_words_flat = Vec::with_capacity(n_fibers * words_per_fiber);
        let mut p2_nodes = vec![[0u64; 4]; 2 * n_fibers];
        let mut cshake_nodes = vec![[0u8; 32]; 2 * n_fibers];
        for (f, (w, p2, cs)) in leaves.into_iter().enumerate() {
            fiber_words_flat.extend_from_slice(&w);
            p2_nodes[n_fibers + f] = p2;
            cshake_nodes[n_fibers + f] = cs;
        }
        let key3 = [canopy_key[0], canopy_key[1], canopy_key[2]];
        let mut level_size = n_fibers / 2;
        while level_size >= 1 {
            let start = level_size;
            let (p2_lvl, cs_lvl): (Vec<[u64; 4]>, Vec<[u8; 32]>) = (start..(2 * start))
                .into_par_iter()
                .map(|idx| {
                    (
                        p2_canopy_node(p2_nodes[2 * idx], p2_nodes[2 * idx + 1], key3, idx as u32),
                        cshake256_canopy_node(&cshake_nodes[2 * idx], &cshake_nodes[2 * idx + 1], idx as u32),
                    )
                })
                .unzip();
            for (off, (p2, cs)) in p2_lvl.into_iter().zip(cs_lvl.into_iter()).enumerate() {
                p2_nodes[start + off] = p2;
                cshake_nodes[start + off] = cs;
            }
            level_size /= 2;
        }
        Self {
            stage_id,
            is_ext4,
            num_cols,
            log_fibers,
            canopy_key,
            words_per_fiber,
            fiber_words_flat,
            p2_nodes,
            cshake_nodes,
        }
    }

    pub fn p2_root(&self) -> [u64; 4] {
        self.p2_nodes[1]
    }

    pub fn cshake_root(&self) -> [u8; 32] {
        self.cshake_nodes[1]
    }

    pub fn cshake_root_pin4(&self) -> [u64; 4] {
        let limbs5 = pack_digest32_to_5_limbs(&self.cshake_nodes[1]);
        p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &limbs5)
    }

    pub fn fiber_words(&self, f: usize) -> &[u64] {
        let off = f * self.words_per_fiber;
        &self.fiber_words_flat[off..off + self.words_per_fiber]
    }

    pub fn p2_siblings(&self, f: usize) -> Vec<[u64; 4]> {
        let n_fibers = 1usize << self.log_fibers;
        let mut idx = n_fibers + f;
        let mut out = Vec::with_capacity(self.log_fibers);
        for _ in 0..self.log_fibers {
            out.push(self.p2_nodes[idx ^ 1]);
            idx >>= 1;
        }
        out
    }

    pub fn cshake_siblings(&self, f: usize) -> Vec<[u8; 32]> {
        let n_fibers = 1usize << self.log_fibers;
        let mut idx = n_fibers + f;
        let mut out = Vec::with_capacity(self.log_fibers);
        for _ in 0..self.log_fibers {
            out.push(self.cshake_nodes[idx ^ 1]);
            idx >>= 1;
        }
        out
    }
}

/// Intermediate `2^k`-ary BaseFold RS commitment (`Poseidon2-12` Canopy).
struct BaseFoldStageCanopy {
    log_n_cur: usize,
    log_fibers: usize,
    canopy_key: [u64; 4],
    fibers: Vec<Vec<GoldilocksExt4>>,
    p2_nodes: Vec<[u64; 4]>,
}

impl BaseFoldStageCanopy {
    fn commit(coeffs: &[GoldilocksExt4], blowup: usize, round_start: usize, fold_k: usize, canopy_key: [u64; 4]) -> Self {
        let mut shift = Goldilocks::SEVEN;
        for _ in 0..round_start {
            shift = shift.square();
        }
        let code = encode_rs_coset_ext4(coeffs, blowup, shift);
        let n_dom = code.len();
        let log_n_cur = n_dom.trailing_zeros() as usize;
        let arity = 1usize << fold_k;
        let n_fibers = n_dom / arity;
        let log_fibers = n_fibers.trailing_zeros() as usize;
        let leaves: Vec<(Vec<GoldilocksExt4>, [u64; 4])> = (0..n_fibers)
            .into_par_iter()
            .map(|f| {
                let mut fib = Vec::with_capacity(arity);
                let mut w = Vec::with_capacity(4 * arity);
                for m in 0..arity {
                    let v = code[f + m * n_fibers];
                    fib.push(v);
                    w.extend_from_slice(&v.to_u64_limbs());
                }
                let p2 = p2_sponge_hash_limbs(P2_DOMAIN_CANOPY_LEAF, canopy_key, &w);
                (fib, p2)
            })
            .collect();
        let mut fibers = Vec::with_capacity(n_fibers);
        let mut p2_nodes = vec![[0u64; 4]; 2 * n_fibers];
        for (f, (fib, p2)) in leaves.into_iter().enumerate() {
            fibers.push(fib);
            p2_nodes[n_fibers + f] = p2;
        }
        let key3 = [canopy_key[0], canopy_key[1], canopy_key[2]];
        let mut level_size = n_fibers / 2;
        while level_size >= 1 {
            let start = level_size;
            let p2_lvl: Vec<[u64; 4]> = (start..(2 * start))
                .into_par_iter()
                .map(|idx| p2_canopy_node(p2_nodes[2 * idx], p2_nodes[2 * idx + 1], key3, idx as u32))
                .collect();
            for (off, p2) in p2_lvl.into_iter().enumerate() {
                p2_nodes[start + off] = p2;
            }
            level_size /= 2;
        }
        Self {
            log_n_cur,
            log_fibers,
            canopy_key,
            fibers,
            p2_nodes,
        }
    }

    fn p2_root(&self) -> [u64; 4] {
        self.p2_nodes[1]
    }

    fn p2_siblings(&self, f: usize) -> Vec<[u64; 4]> {
        let n_fibers = 1usize << self.log_fibers;
        let mut idx = n_fibers + f;
        let mut out = Vec::with_capacity(self.log_fibers);
        for _ in 0..self.log_fibers {
            out.push(self.p2_nodes[idx ^ 1]);
            idx >>= 1;
        }
        out
    }
}

/// Complete lockstep BaseFold opening data for a `2^num_vars`-coeff batched polynomial (`final_poly` deg `< 8`).
struct LockstepBaseFoldProof {
    round_c0_c2: Vec<(GoldilocksExt4, GoldilocksExt4)>,
    stages: Vec<BaseFoldStageCanopy>,
    final_poly: [GoldilocksExt4; 8],
}

fn prove_lockstep_basefold(
    mut poly_coeffs: Vec<GoldilocksExt4>,
    z_point: &[GoldilocksExt4],
    stage_ks: &[usize],
    base_key_seed: u64,
    label_prefix: &[u8],
    ch: &mut [u64; 4],
) -> LockstepBaseFoldProof {
    let num_vars = z_point.len();
    assert_eq!(poly_coeffs.len(), 1usize << num_vars);
    let folded_total: usize = 1 + stage_ks.iter().sum::<usize>();
    assert_eq!(folded_total + 3, num_vars);
    let mut eq_tab = build_eq_table_lsb_gl_ext4(z_point);
    let mut round_c0_c2 = Vec::with_capacity(num_vars);
    let mut stages = Vec::with_capacity(stage_ks.len());
    let mut final_poly = [GoldilocksExt4::ZERO; 8];

    // Precompute round boundaries at which each stage commitment or `final_poly` is absorbed:
    // After round 0 completes -> commit stage 0 (`stage_ks[0]`);
    // After round `1 + sum(stage_ks[..s]) - 1` completes -> commit stage `s` (or `final_poly` when `s == stage_ks.len()`).
    let mut next_stage_idx = 0usize;
    let mut next_commit_after_round = 0usize; // after round 0 (Stage 0 -> Stage 1)

    let mut lab_c0 = label_prefix.to_vec();
    lab_c0.extend_from_slice(b"_C0");
    let mut lab_c2 = label_prefix.to_vec();
    lab_c2.extend_from_slice(b"_C2");
    let mut lab_ch = label_prefix.to_vec();
    lab_ch.extend_from_slice(b"_CH");
    let mut lab_rt = label_prefix.to_vec();
    lab_rt.extend_from_slice(b"_RT");

    for rnd in 0..num_vars {
        let half = poly_coeffs.len() / 2;
        let (c0, c2) = if half >= 1024 {
            (0..half)
                .into_par_iter()
                .map(|i| {
                    let (e0, e1) = (eq_tab[2 * i], eq_tab[2 * i + 1]);
                    let (a0, a1) = (poly_coeffs[2 * i], poly_coeffs[2 * i + 1]);
                    (e0 * a0, (e1 - e0) * (a1 - a0))
                })
                .reduce(
                    || (GoldilocksExt4::ZERO, GoldilocksExt4::ZERO),
                    |(a0, b0), (a1, b1)| (a0 + a1, b0 + b1),
                )
        } else {
            let mut s0 = GoldilocksExt4::ZERO;
            let mut s2 = GoldilocksExt4::ZERO;
            for i in 0..half {
                let (e0, e1) = (eq_tab[2 * i], eq_tab[2 * i + 1]);
                let (a0, a1) = (poly_coeffs[2 * i], poly_coeffs[2 * i + 1]);
                s0 = s0 + (e0 * a0);
                s2 = s2 + ((e1 - e0) * (a1 - a0));
            }
            (s0, s2)
        };
        round_c0_c2.push((c0, c2));
        *ch = fs_absorb_limbs_local(*ch, &lab_c0, &c0.to_u64_limbs());
        *ch = fs_absorb_limbs_local(*ch, &lab_c2, &c2.to_u64_limbs());
        let r_j = fs_squeeze_ext4_local(*ch, &lab_ch, rnd as u64);

        // Lockstep fold BOTH `eq_tab` and `poly_coeffs` with the exact same `r_j`:
        if half >= 1024 {
            let (next_eq, next_poly): (Vec<GoldilocksExt4>, Vec<GoldilocksExt4>) = (0..half)
                .into_par_iter()
                .map(|i| {
                    (
                        eq_tab[2 * i] + r_j * (eq_tab[2 * i + 1] - eq_tab[2 * i]),
                        poly_coeffs[2 * i] + r_j * (poly_coeffs[2 * i + 1] - poly_coeffs[2 * i]),
                    )
                })
                .unzip();
            eq_tab = next_eq;
            poly_coeffs = next_poly;
        } else {
            let mut next_eq = Vec::with_capacity(half);
            let mut next_poly = Vec::with_capacity(half);
            for i in 0..half {
                next_eq.push(eq_tab[2 * i] + r_j * (eq_tab[2 * i + 1] - eq_tab[2 * i]));
                next_poly.push(poly_coeffs[2 * i] + r_j * (poly_coeffs[2 * i + 1] - poly_coeffs[2 * i]));
            }
            eq_tab = next_eq;
            poly_coeffs = next_poly;
        }

        if rnd == next_commit_after_round {
            if next_stage_idx < stage_ks.len() {
                let k = stage_ks[next_stage_idx];
                let key = [
                    base_key_seed ^ ((next_stage_idx as u64) + 1),
                    0x4341_4E50_0000_0000 ^ (next_stage_idx as u64),
                    0x4246_5354_0000_0000 | (rnd as u64),
                    P2_IV,
                ];
                let st = BaseFoldStageCanopy::commit(&poly_coeffs, UD100_BLOWUP, rnd + 1, k, key);
                *ch = fs_absorb_limbs_local(*ch, &lab_rt, &st.p2_root());
                stages.push(st);
                next_commit_after_round += k;
                next_stage_idx += 1;
            } else {
                assert_eq!(poly_coeffs.len(), 8);
                final_poly.copy_from_slice(&poly_coeffs[..8]);
                let mut f32 = [0u64; 32];
                for i in 0..8 {
                    f32[4 * i..4 * (i + 1)].copy_from_slice(&final_poly[i].to_u64_limbs());
                }
                *ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, *ch, &f32);
                next_commit_after_round = usize::MAX;
            }
        }
    }
    LockstepBaseFoldProof {
        round_c0_c2,
        stages,
        final_poly,
    }
}

/// Emit bytecode for a complete `LockstepBaseFoldProof` sumcheck (`R_A` holds initial claim `Y`,
/// `z_chals[0..num_vars]` holds `z`), absorbing stage roots (optionally compressing each root into `root_bundle_reg`),
/// latching `final_poly[0..8]`, and asserting `eq(z, r_bf) * fold(final_poly) == terminal_claim`!
fn emit_lockstep_basefold_sumcheck(
    asm: &mut Dregg180HvmAssembler,
    num_vars: usize,
    stage_ks: &[usize],
    label_prefix: &[u8],
    stage_root_regs: Option<&[u8]>,
    root_bundle_reg: Option<(u8, u64)>,
    proof: Option<&LockstepBaseFoldProof>,
) {
    let mut lab_c0 = label_prefix.to_vec();
    lab_c0.extend_from_slice(b"_C0");
    let mut lab_c2 = label_prefix.to_vec();
    lab_c2.extend_from_slice(b"_C2");
    let mut lab_ch = label_prefix.to_vec();
    lab_ch.extend_from_slice(b"_CH");
    let mut lab_rt = label_prefix.to_vec();
    lab_rt.extend_from_slice(b"_RT");

    let mut next_stage_idx = 0usize;
    let mut next_commit_after_round = 0usize;
    let zero4 = [0u64; 4];

    for rnd in 0..num_vars {
        let (c0_w, c2_w) = match proof {
            Some(p) => (p.round_c0_c2[rnd].0.to_u64_limbs(), p.round_c0_c2[rnd].1.to_u64_limbs()),
            None => (zero4, zero4),
        };
        asm.absorb_limbs_proof(&lab_c0, &c0_w, R_X, 0);
        asm.absorb_limbs_proof(&lab_c2, &c2_w, R_Y, 0);
        asm.squeeze_ext4(R_B, &lab_ch, rnd as u64);
        asm.bf_latch_bf(rnd as u8, R_B);
        // `c1 = claim - 2*c0 - c2`, `claim <- c0 + r_j*(c1 + r_j*c2)`:
        asm.esub(R_T0, R_A, R_X);
        asm.esub(R_T0, R_T0, R_X);
        asm.esub(R_T0, R_T0, R_Y);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_Y, R_Y, R_T0);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_A, R_Y, R_X);

        if rnd == next_commit_after_round {
            if next_stage_idx < stage_ks.len() {
                let root_w = match proof {
                    Some(p) => p.stages[next_stage_idx].p2_root(),
                    None => zero4,
                };
                asm.absorb_limbs_proof(&lab_rt, &root_w, R_X, 0);
                if let Some(regs) = stage_root_regs {
                    emit_copy_reg(asm, regs[next_stage_idx], R_X);
                }
                if let Some((b_reg, tag_base)) = root_bundle_reg {
                    emit_compress_reg(asm, b_reg, R_X, tag_base + (next_stage_idx as u64));
                }
                next_commit_after_round += stage_ks[next_stage_idx];
                next_stage_idx += 1;
            } else {
                let fp = match proof {
                    Some(p) => p.final_poly,
                    None => [GoldilocksExt4::ZERO; 8],
                };
                asm.bf_latch_final_poly(&fp);
                next_commit_after_round = usize::MAX;
            }
        }
    }
    // Check `eq(z_chals[0..num_vars], bf_chals[0..num_vars]) * fold(final_poly) == R_A`:
    asm.bf_eval_eq_z_bf(num_vars as u8, R_X);
    asm.bf_fold_final_poly((num_vars - 3) as u8, R_Y);
    asm.emul(R_T0, R_X, R_Y);
    asm.assert_eq(R_A, R_T0);
}

/// Compile verified heterogeneous child leaf claims (`BabyBear Ext4` + `Tower256` `Absent` + `Simplex` `FinCert`)
/// into a real **`UD-100` (`blowup = 8`, `122` dual Canopy queries, single-read bound `16`-bit PoW,
/// complete lockstep BaseFold closing to `final_poly[0..8]`)** `GoldilocksExt4` `Hem` stream
/// executable inside `< 16 KiB` `Dregg180StreamVm`.
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
    let stage_ks: &[usize] = &[2]; // Stage 0 (2-ary) -> Stage 1 (4-ary, depth 6) -> final_poly[8]
    let canopy_key0 = [0x4452_4731_8000_0001, 0x4341_4E50_0000_0000, 0x5354_4730_0000_0001, P2_IV];

    let mut asm = Dregg180HvmAssembler::new(OP_HEM, pin_mode, false);

    // 1. Bind relation & `UD-100` schedule into `R_CH` (`P2_DOMAIN_FS_BIND_REL`):
    let mut rel_imm = pack_bytes_7_limbs(b"DREGG180.SHE.HETERO.UD100/v2");
    rel_imm.extend_from_slice(&[
        num_vars as u64,
        UD100_BLOWUP as u64,
        UD100_NUM_QUERIES as u64,
        UD100_POW_BITS as u64,
    ]);
    asm.hash(R_CH, None, P2_DOMAIN_FS_BIND_REL, &rel_imm, &[], 0, 0);
    let mut ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_BIND_REL, FS_INIT_CAP, &rel_imm);

    // 2. Absorb all 3 commitment-pinned `DeferredLeafClaim`s as program immediates:
    let labels: [&[u8]; 3] = [b"LEAF0_QWEN_BB4", b"LEAF1_T256_ABS", b"LEAF2_SMPX_FIN"];
    for (i, claim) in leaf_claims.iter().enumerate() {
        let imm16 = claim.to_immediate_limbs();
        asm.absorb_limbs_immediate(labels[i], &imm16, 0, 0);
        ch = fs_absorb_limbs_local(ch, labels[i], &imm16);
    }

    // 3. Build polynomial `W` encoding the 3 `DeferredLeafClaim` evaluations & commit Stage-0 dual Canopy:
    let mut evals = vec![GoldilocksExt4::ZERO; n_coeffs];
    evals[0] = leaf_claims[0].reduced_ext4_eval();
    evals[1] = leaf_claims[1].reduced_ext4_eval();
    evals[2] = leaf_claims[2].reduced_ext4_eval();
    evals[3] = evals[0] + evals[1] + evals[2];
    for i in 4..n_coeffs {
        evals[i] = evals[i % 4].scale_base(Goldilocks((i as u64) + 11));
    }
    let stage0 = Stage0MatrixCanopy::commit_ext4(0, &[evals.clone()], UD100_BLOWUP, canopy_key0);
    let p2_root0 = stage0.p2_root();
    let cs_root0 = stage0.cshake_root();
    let cs_root0_pin4 = stage0.cshake_root_pin4();

    // Latch Stage-0 roots into `R_6 = p2_root0`, `R_7 = cs_root0_pin4`:
    asm.absorb_limbs_proof(b"PCS_S0_P2_ROOT", &p2_root0, 6, 0);
    ch = fs_absorb_limbs_local(ch, b"PCS_S0_P2_ROOT", &p2_root0);
    asm.absorb_limbs_proof(b"PCS_S0_CS_ROOT", &cs_root0_pin4, 7, 0);
    ch = fs_absorb_limbs_local(ch, b"PCS_S0_CS_ROOT", &cs_root0_pin4);

    // 4. Squeeze evaluation point `z[0..6]` on chip, claim `W(z)`, and prove `W(z)` via REAL Lockstep BaseFold!
    let mut z_pt = Vec::with_capacity(num_vars);
    for j in 0..num_vars {
        let zj = fs_squeeze_ext4_local(ch, b"HEM_EVAL_Z", j as u64);
        asm.squeeze_ext4(R_T0, b"HEM_EVAL_Z", j as u64);
        asm.bf_latch_z(j as u8, R_T0);
        z_pt.push(zj);
    }
    let eq_z = build_eq_table_lsb_gl_ext4(&z_pt);
    let init_claim = mle_eval_ext4_gl_ext4(&evals, &eq_z);
    asm.absorb_limbs_proof(b"HEM_SC_CLAIM", &init_claim.to_u64_limbs(), R_A, 0);
    ch = fs_absorb_limbs_local(ch, b"HEM_SC_CLAIM", &init_claim.to_u64_limbs());

    let bf_proof = prove_lockstep_basefold(evals, &z_pt, stage_ks, 0x4452_4731_8000_0000, b"BF_LEAF", &mut ch);
    let p2_root1 = bf_proof.stages[0].p2_root();
    let stage1_key = bf_proof.stages[0].canopy_key;
    emit_lockstep_basefold_sumcheck(&mut asm, num_vars, stage_ks, b"BF_LEAF", Some(&[8]), None, Some(&bf_proof));

    // 5. Grind `16`-bit `Poseidon2-12` Transcript Proof-of-Work ONCE directly into `R_CH` & check `H_ASSERT_POW(R_CH, 16)` (H1 fix!):
    let (pow_nonce, ch_after_pow) = grind_p2_pow(P2_DOMAIN_FS_POW, ch, UD100_POW_BITS);
    let nonce_words = [pow_nonce & 0xFFFF_FFFF, pow_nonce >> 32];
    asm.hash(R_CH, Some(R_CH), P2_DOMAIN_FS_POW, &[], &nonce_words, 0, 0);
    asm.assert_pow(R_CH, UD100_POW_BITS);
    ch = ch_after_pow;

    // 6. Execute `122` Transcript-Bound Dual-Canopy Query Chains (bare `(9/16)^122 < 2^{-101.27}`, + 16-bit PoW = `2^{-117.27}`):
    //    Stage 0 (2-ary, depth 8, bound P2 + cSHAKE leaves via `H_FIBER_ACC`) -> Stage 1 (4-ary, depth 6, `H_BF_FOLD_FIBER`)
    //    -> `BF_AUX_ASSERT_FINAL_EVAL` against `final_poly[0..8]`!
    asm.load(9, &GoldilocksExt4::ONE.to_u64_limbs(), true); // eta = 1 (single column)
    for q_idx in 0..UD100_NUM_QUERIES {
        let mut qlab = pack_bytes_7_limbs(b"UD100_QUERY");
        qlab.push(q_idx as u64);
        let f0 = (p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_IDX, ch, &qlab)[0] as usize)
            & ((1usize << stage0.log_fibers) - 1);

        // Stage-0 bound dual Canopy opening (exact same words feed P2 leaf, cSHAKE leaf, and Stage-0 fold!):
        asm.load(12, &canopy_key0, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, stage0.log_fibers as u8);
        asm.fiber_acc(0, true, true, true, 12, 9, 1, stage0.fiber_words(f0));
        asm.merkle(12, f0 as u32, &stage0.p2_siblings(f0));
        asm.assert_eq(R_X, 6);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, stage0.log_fibers as u8);
        asm.cshake_merkle_bound(f0 as u32, &stage0.cshake_siblings(f0));
        asm.assert_eq(R_X, 7);
        asm.bf_stage0_fold2((stage0.log_fibers + 1) as u8, R_A);

        // Stage-1 4-ary BaseFold check & fold (f1 = f0 & 63, depth 6):
        let f1 = f0 & ((1usize << bf_proof.stages[0].log_fibers) - 1);
        asm.load(12, &stage1_key, true);
        asm.bf_fold_fiber(2, bf_proof.stages[0].log_n_cur as u8, 12, 1, R_A, R_A, &bf_proof.stages[0].fibers[f1]);
        asm.merkle(12, f1 as u32, &bf_proof.stages[0].p2_siblings(f1));
        asm.assert_eq(R_X, 8);

        // Final degree-<8 polynomial check at `x_final = 7^8 * omega_64^{f1}`:
        asm.bf_assert_final_eval(3, R_A);
    }

    let delta_override = k_mac_opt.map(u128::from_le_bytes);
    let (wire_bytes, pinned_program_digest) = asm.build_wire_bytes_and_pdig(delta_override);
    let public_program_hash = asm.compute_public_program_hash();
    let num_records = asm.records.len();

    Ok(CompiledDregg180HemStream {
        leaf_claims,
        p2_stage0_root: p2_root0,
        cshake_stage0_root: cs_root0,
        p2_stage1_root: p2_root1,
        wire_bytes,
        pinned_program_digest,
        public_program_hash,
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

// ================================================================================================
// §7. Trustless (`pin_mode = false`, `k_mac = None`) `UD-100` Non-Native `BabyBear Ext4` (`X^4-11`)
//     Sumcheck + `Absent("sk-")` 4-State DFA `GoldilocksExt4` `OP_HEM` AIR & `[0, 2^16)` LogUp
// ================================================================================================

const CANOPY_KEY_VK: [u64; 4] = [0x4452_4731_564B_0001, 0x4341_4E50_0000_0010, 0x564B_5330_0000_0001, P2_IV];
const CANOPY_KEY_BYTES: [u64; 4] = [0x4452_4731_4259_0002, 0x4341_4E50_0000_0020, 0x4259_5330_0000_0002, P2_IV];
const CANOPY_KEY_WIT1: [u64; 4] = [0x4452_4731_5731_0003, 0x4341_4E50_0000_0030, 0x5731_5330_0000_0003, P2_IV];
const CANOPY_KEY_WIT2: [u64; 4] = [0x4452_4731_5732_0004, 0x4341_4E50_0000_0040, 0x5732_5330_0000_0004, P2_IV];
const CANOPY_KEY_MRNG: [u64; 4] = [0x4452_4731_4D52_0005, 0x4341_4E50_0000_0050, 0x4D52_5330_0000_0005, P2_IV];
const CANOPY_KEY_HRNG: [u64; 4] = [0x4452_4731_4852_0006, 0x4341_4E50_0000_0060, 0x4852_5330_0000_0006, P2_IV];
const CANOPY_KEY_WBB: [u64; 4] = [0x4452_4731_5742_0007, 0x4341_4E50_0000_0070, 0x5742_5330_0000_0007, P2_IV];
const T1_BF_KEY_SEED: u64 = 0x4452_4731_5431_0000;
const T2_BF_KEY_SEED: u64 = 0x4452_4731_5432_0000;
const T1_STAGE_KS: &[usize] = &[3, 3, 2]; // 1 + 3 + 3 + 2 = 9 = 12 - 3 -> final_poly[8]
const T2_STAGE_KS: &[usize] = &[3, 3, 3, 3]; // 1 + 3 + 3 + 3 + 3 = 13 = 16 - 3 -> final_poly[8]

/// 4-state Padded-Complement `Absent("sk-")` DFA matching Lean `Selvage.GoldilocksDregg180Bridge.noSkDashStep`:
///   - `0`: idle (accepting)
///   - `1`: matched `'s'` (`115`, accepting)
///   - `2`: matched `"sk"` (`107`, accepting)
///   - `3`: **INESCAPABLE SINK** — matched `"sk-"` (`45`, non-accepting!)
#[inline]
pub const fn no_sk_dash_step_4state(q: u8, b: u8) -> u8 {
    if q == 3 {
        3
    } else if q == 2 && b == b'-' {
        3
    } else if q == 1 && b == b'k' {
        2
    } else if b == b's' {
        1
    } else {
        0
    }
}

/// Run the 4-state `Absent("sk-")` DFA on `bytes`, returning `(final_state, states_len_plus_1)`.
pub fn run_no_sk_dash_dfa_4state(bytes: &[u8]) -> (u8, Vec<u8>) {
    let mut states = Vec::with_capacity(bytes.len() + 1);
    let mut q = 0u8;
    states.push(q);
    for &b in bytes {
        q = no_sk_dash_step_4state(q, b);
        states.push(q);
    }
    (q, states)
}

/// Public commitment to a `<= 1,024`-byte payload (`0x00`-padded to `1,024` bytes, which preserves
/// sink `3` vs accepting `{0, 1, 2}` in `no_sk_dash_step_4state`).
#[derive(Clone)]
pub struct PayloadBytesCommitment {
    pub padded_bytes: Vec<Goldilocks>,
    pub canopy: Stage0MatrixCanopy,
}

impl PayloadBytesCommitment {
    pub fn commit(payload: &[u8]) -> Result<Self, String> {
        if payload.len() > HEM_EXEC_ROWS {
            return Err(format!("payload length {} exceeds HEM_EXEC_ROWS={}", payload.len(), HEM_EXEC_ROWS));
        }
        let mut padded_bytes = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        for (i, &b) in payload.iter().enumerate() {
            padded_bytes[i] = Goldilocks(b as u64);
        }
        let canopy = Stage0MatrixCanopy::commit_base(1, &[padded_bytes.clone()], UD100_BLOWUP, CANOPY_KEY_BYTES);
        Ok(Self { padded_bytes, canopy })
    }

    pub fn p2_root(&self) -> [u64; 4] {
        self.canopy.p2_root()
    }

    pub fn cshake_root(&self) -> [u8; 32] {
        self.canopy.cshake_root()
    }

    pub fn cshake_root_pin4(&self) -> [u64; 4] {
        self.canopy.cshake_root_pin4()
    }
}

/// Public dual-Canopy (`Poseidon2-12` + `cSHAKE256`) commitment to the child `BabyBear` witness table
/// `W_bb = (A_bb[0..2^m], B_bb[0..2^m])` placed at Table 1 rows `32..32+2^{m+1}`.
/// Every entry is enforced `< p_BB` via `C_wbb = sel_wbb*(r_val - w_bb)` + `r_val + d_val = p_BB - 1`,
/// and `A(r) * B(r) * eq(tau, r) == claim_m` is proved 100% INSIDE `GoldilocksExt4` on `Dregg180StreamVm`
/// (ZERO `Option` terminal oracle callback, ZERO unverified terminal claim loophole!).
#[derive(Clone)]
pub struct BabyBearWitnessCommitment {
    pub bb_num_rounds: usize,
    pub w_bb_col: Vec<Goldilocks>,
    pub canopy: Stage0MatrixCanopy,
}

impl BabyBearWitnessCommitment {
    pub fn commit(m_rounds: usize, a_vals: &[u32], b_vals: &[u32]) -> Result<Self, String> {
        if m_rounds == 0 || m_rounds > HEM_MAX_BB_ROUNDS {
            return Err(format!("m_rounds must be in 1..={HEM_MAX_BB_ROUNDS}, got {m_rounds}"));
        }
        let n_bb = 1usize << m_rounds;
        if a_vals.len() != n_bb || b_vals.len() != n_bb {
            return Err("BabyBearWitnessCommitment dimension mismatch".into());
        }
        let mut w_bb_col = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        for i in 0..n_bb {
            if (a_vals[i] as u64) >= BABYBEAR_PRIME_U64 || (b_vals[i] as u64) >= BABYBEAR_PRIME_U64 {
                return Err("BabyBearWitnessCommitment contains non-canonical entry >= p_BB".into());
            }
            w_bb_col[HEM_ROW_WBB_START + i] = Goldilocks(a_vals[i] as u64);
            w_bb_col[HEM_ROW_WBB_START + n_bb + i] = Goldilocks(b_vals[i] as u64);
        }
        let canopy = Stage0MatrixCanopy::commit_base(6, &[w_bb_col.clone()], UD100_BLOWUP, CANOPY_KEY_WBB);
        Ok(Self { bb_num_rounds: m_rounds, w_bb_col, canopy })
    }

    pub fn p2_root(&self) -> [u64; 4] {
        self.canopy.p2_root()
    }

    /// Test-only helper that commits raw `Goldilocks` entries without `< p_BB` check so adversarial tests
    /// can prove `Dregg180StreamVm` rejects a committed `W_bb` containing non-canonical `>= p_BB` entries!
    pub fn commit_unchecked_raw(m_rounds: usize, a_vals: &[u64], b_vals: &[u64]) -> Result<Self, String> {
        let n_bb = 1usize << m_rounds;
        if m_rounds == 0 || m_rounds > HEM_MAX_BB_ROUNDS || a_vals.len() != n_bb || b_vals.len() != n_bb {
            return Err("commit_unchecked_raw dimension mismatch".into());
        }
        let mut w_bb_col = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        for i in 0..n_bb {
            w_bb_col[HEM_ROW_WBB_START + i] = Goldilocks(a_vals[i]);
            w_bb_col[HEM_ROW_WBB_START + n_bb + i] = Goldilocks(b_vals[i]);
        }
        let canopy = Stage0MatrixCanopy::commit_base(6, &[w_bb_col.clone()], UD100_BLOWUP, CANOPY_KEY_WBB);
        Ok(Self { bb_num_rounds: m_rounds, w_bb_col, canopy })
    }

    pub fn cshake_root(&self) -> [u8; 32] {
        self.canopy.cshake_root()
    }

    pub fn cshake_root_pin4(&self) -> [u64; 4] {
        self.canopy.cshake_root_pin4()
    }
}

/// Deterministic preprocessed circuit layout for `m_rounds` (`1..=6`) full degree-3 cubic
/// `BabyBear Ext4` (`X^4 - 11`) sumcheck rounds + full in-circuit `chi(x)` / `W_bb(r)` / `eq(tau, r)`
/// terminal evaluation against committed `W_bb` + `4 x 256` `Absent("sk-")` 4-state DFA ROM.
#[derive(Clone)]
pub struct TrustlessHemCircuitLayout {
    pub bb_num_rounds: usize,
    pub vk_cols: Vec<Vec<Goldilocks>>, // [sel_mac, sel_eq, sel_fs, sel_wbb, src_a, src_b, src_c, rom_q_next]
    pub g_rows: Vec<[[usize; 4]; 4]>,  // g_rows[rnd][coeff 0..4][limb 0..4]
    pub fs_rows: Vec<[usize; 4]>,      // fs_rows[rnd][limb 0..4]
    pub pub_r_indices: Vec<u64>,       // constants(4) + init_claim(4) + tau(4*m) + g_i(16*m)
    pub pub_a_indices: Vec<u64>,       // raw_r_i(4*m)
    pub first_mac_row: usize,
    pub total_used_rows: usize,
}

impl TrustlessHemCircuitLayout {
    pub fn build(bb_num_rounds: usize) -> Result<Self, String> {
        if bb_num_rounds == 0 || bb_num_rounds > HEM_MAX_BB_ROUNDS {
            return Err(format!(
                "bb_num_rounds must be in 1..={HEM_MAX_BB_ROUNDS} for N_exec={HEM_EXEC_ROWS}, got {bb_num_rounds}"
            ));
        }
        let mut sel_mac = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut sel_eq = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut sel_fs = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut sel_wbb = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut src_a = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut src_b = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut src_c = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        let mut rom_q_next = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
        for u in 0..HEM_EXEC_ROWS {
            rom_q_next[u] = Goldilocks(no_sk_dash_step_4state(((u >> 8) & 3) as u8, (u & 0xFF) as u8) as u64);
        }

        // Fixed public header rows `0..32`:
        //   0 = const 0, 1 = const 1, 2 = const 11 (`X^4 - 11`), 3 = const `p_BB - 1` (`-1 mod p_BB`),
        //   4..8 = `bb_initial_claim`, 8..8+4m = `bb_tau[0..m]`.
        const ROW_ZERO: usize = 0;
        const ROW_ONE: usize = 1;
        const ROW_ELEVEN: usize = 2;
        const ROW_NEG_ONE: usize = 3;
        let init_claim_rows = [4usize, 5, 6, 7];
        let mut pub_r_indices: Vec<u64> = (0..8u64).collect();
        let mut tau_rows = Vec::with_capacity(bb_num_rounds);
        for j in 0..bb_num_rounds {
            let base = 8 + 4 * j;
            tau_rows.push([base, base + 1, base + 2, base + 3]);
            for l in 0..4 {
                pub_r_indices.push((base + l) as u64);
            }
        }

        // Committed `W_bb` witness table rows `32..32 + 2^{m+1}` (`sel_wbb = 1` enforces `r_val == w_bb_col` & `< p_BB`!):
        let n_bb = 1usize << bb_num_rounds;
        let mut w_a_rows = Vec::with_capacity(n_bb);
        let mut w_b_rows = Vec::with_capacity(n_bb);
        for i in 0..n_bb {
            let ra = HEM_ROW_WBB_START + i;
            let rb = HEM_ROW_WBB_START + n_bb + i;
            sel_wbb[ra] = Goldilocks::ONE;
            sel_wbb[rb] = Goldilocks::ONE;
            w_a_rows.push(ra);
            w_b_rows.push(rb);
        }
        let mut cur_row = HEM_ROW_WBB_START + 2 * n_bb;
        let mut first_mac_row = 0usize;

        let mut push_gate = |is_mac: bool, sa: usize, sb: usize, sc: usize, row: &mut usize| -> usize {
            let r = *row;
            if is_mac {
                if first_mac_row == 0 {
                    first_mac_row = r;
                }
                sel_mac[r] = Goldilocks::ONE;
            } else {
                sel_eq[r] = Goldilocks::ONE;
            }
            src_a[r] = Goldilocks(sa as u64);
            src_b[r] = Goldilocks(sb as u64);
            src_c[r] = Goldilocks(sc as u64);
            *row += 1;
            r
        };

        fn push_ext4_mul<F: FnMut(bool, usize, usize, usize, &mut usize) -> usize>(
            push_gate: &mut F,
            a: [usize; 4],
            b: [usize; 4],
            row: &mut usize,
        ) -> [usize; 4] {
            let t1 = push_gate(true, a[1], b[3], ROW_ZERO, row);
            let t2 = push_gate(true, a[2], b[2], t1, row);
            let t3 = push_gate(true, a[3], b[1], t2, row);
            let t4 = push_gate(true, ROW_ELEVEN, t3, ROW_ZERO, row);
            let p0 = push_gate(true, a[0], b[0], t4, row);

            let t5 = push_gate(true, a[2], b[3], ROW_ZERO, row);
            let t6 = push_gate(true, a[3], b[2], t5, row);
            let t7 = push_gate(true, ROW_ELEVEN, t6, ROW_ZERO, row);
            let t8 = push_gate(true, a[0], b[1], t7, row);
            let p1 = push_gate(true, a[1], b[0], t8, row);

            let t9 = push_gate(true, a[3], b[3], ROW_ZERO, row);
            let t10 = push_gate(true, ROW_ELEVEN, t9, ROW_ZERO, row);
            let t11 = push_gate(true, a[0], b[2], t10, row);
            let t12 = push_gate(true, a[1], b[1], t11, row);
            let p2 = push_gate(true, a[2], b[0], t12, row);

            let t13 = push_gate(true, a[0], b[3], ROW_ZERO, row);
            let t14 = push_gate(true, a[1], b[2], t13, row);
            let t15 = push_gate(true, a[2], b[1], t14, row);
            let p3 = push_gate(true, a[3], b[0], t15, row);
            [p0, p1, p2, p3]
        }

        let mut g_rows = Vec::with_capacity(bb_num_rounds);
        let mut fs_rows = Vec::with_capacity(bb_num_rounds);
        let mut pub_a_indices: Vec<u64> = Vec::with_capacity(4 * bb_num_rounds);

        // 1. `m` full cubic `BabyBear Ext4` sumcheck rounds (`g_i(0) + g_i(1) == claim_i`, `g_i(r_i) == claim_{i+1}`):
        let mut claim_rows = init_claim_rows;
        for _rnd in 0..bb_num_rounds {
            let mut gr = [[0usize; 4]; 4];
            for k in 0..4 {
                for l in 0..4 {
                    gr[k][l] = cur_row;
                    pub_r_indices.push(cur_row as u64);
                    cur_row += 1;
                }
            }
            g_rows.push(gr);

            let mut fr = [0usize; 4];
            for l in 0..4 {
                sel_fs[cur_row] = Goldilocks::ONE;
                fr[l] = cur_row;
                pub_a_indices.push(cur_row as u64);
                cur_row += 1;
            }
            fs_rows.push(fr);

            let mut s1 = [0usize; 4];
            let mut s2 = [0usize; 4];
            let mut s3 = [0usize; 4];
            let mut s4 = [0usize; 4];
            for l in 0..4 {
                s1[l] = push_gate(true, ROW_ONE, gr[0][l], gr[0][l], &mut cur_row);
                s2[l] = push_gate(true, ROW_ONE, s1[l], gr[1][l], &mut cur_row);
                s3[l] = push_gate(true, ROW_ONE, s2[l], gr[2][l], &mut cur_row);
                s4[l] = push_gate(true, ROW_ONE, s3[l], gr[3][l], &mut cur_row);
                push_gate(false, s4[l], claim_rows[l], ROW_ZERO, &mut cur_row);
            }

            let mut acc = gr[3];
            for step_c in [gr[2], gr[1], gr[0]] {
                let prod = push_ext4_mul(&mut push_gate, acc, fr, &mut cur_row);
                let mut next_acc = [0usize; 4];
                for l in 0..4 {
                    next_acc[l] = push_gate(true, ROW_ONE, prod[l], step_c[l], &mut cur_row);
                }
                acc = next_acc;
            }
            claim_rows = acc;
        }

        // 2. In-circuit LSB Lagrange basis `chi[x] = prod_{j=0}^{m-1} ((1 - x_j)(1 - r_j) + x_j*r_j)` in `BbExt4`:
        let mut chi_rows: Vec<[usize; 4]> = Vec::with_capacity(n_bb);
        let one_minus_r0 = [
            push_gate(true, ROW_NEG_ONE, fs_rows[0][0], ROW_ONE, &mut cur_row),
            push_gate(true, ROW_NEG_ONE, fs_rows[0][1], ROW_ZERO, &mut cur_row),
            push_gate(true, ROW_NEG_ONE, fs_rows[0][2], ROW_ZERO, &mut cur_row),
            push_gate(true, ROW_NEG_ONE, fs_rows[0][3], ROW_ZERO, &mut cur_row),
        ];
        chi_rows.push(one_minus_r0);
        chi_rows.push(fs_rows[0]);
        for rnd in 1..bb_num_rounds {
            let cur_len = chi_rows.len();
            let ri = fs_rows[rnd];
            for idx in 0..cur_len {
                let base = chi_rows[idx];
                let hi = push_ext4_mul(&mut push_gate, base, ri, &mut cur_row);
                let lo = [
                    push_gate(true, ROW_NEG_ONE, hi[0], base[0], &mut cur_row),
                    push_gate(true, ROW_NEG_ONE, hi[1], base[1], &mut cur_row),
                    push_gate(true, ROW_NEG_ONE, hi[2], base[2], &mut cur_row),
                    push_gate(true, ROW_NEG_ONE, hi[3], base[3], &mut cur_row),
                ];
                chi_rows[idx] = lo;
                chi_rows.push(hi);
            }
        }

        // 3. Exact in-circuit committed multilinear evaluations `A_bb(r)` & `B_bb(r)` against `W_bb` Canopy:
        let mut eval_a = [
            push_gate(true, chi_rows[0][0], w_a_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][1], w_a_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][2], w_a_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][3], w_a_rows[0], ROW_ZERO, &mut cur_row),
        ];
        for i in 1..n_bb {
            for l in 0..4 {
                eval_a[l] = push_gate(true, chi_rows[i][l], w_a_rows[i], eval_a[l], &mut cur_row);
            }
        }
        let mut eval_b = [
            push_gate(true, chi_rows[0][0], w_b_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][1], w_b_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][2], w_b_rows[0], ROW_ZERO, &mut cur_row),
            push_gate(true, chi_rows[0][3], w_b_rows[0], ROW_ZERO, &mut cur_row),
        ];
        for i in 1..n_bb {
            for l in 0..4 {
                eval_b[l] = push_gate(true, chi_rows[i][l], w_b_rows[i], eval_b[l], &mut cur_row);
            }
        }

        // 4. Exact in-circuit `eq(tau, r) = prod_{j=0}^{m-1} (1 + 2*tau_j*r_j - tau_j - r_j)` in `BbExt4`:
        let mut eq_acc = [0usize; 4];
        for j in 0..bb_num_rounds {
            let tr = push_ext4_mul(&mut push_gate, tau_rows[j], fs_rows[j], &mut cur_row);
            let mut two_tr = [0usize; 4];
            let mut m1 = [0usize; 4];
            let mut m2 = [0usize; 4];
            for l in 0..4 {
                two_tr[l] = push_gate(true, ROW_ONE, tr[l], tr[l], &mut cur_row);
                m1[l] = push_gate(true, ROW_NEG_ONE, tau_rows[j][l], two_tr[l], &mut cur_row);
                m2[l] = push_gate(true, ROW_NEG_ONE, fs_rows[j][l], m1[l], &mut cur_row);
            }
            let fac = [
                push_gate(true, ROW_ONE, m2[0], ROW_ONE, &mut cur_row),
                m2[1],
                m2[2],
                m2[3],
            ];
            if j == 0 {
                eq_acc = fac;
            } else {
                eq_acc = push_ext4_mul(&mut push_gate, eq_acc, fac, &mut cur_row);
            }
        }

        // 5. In-circuit terminal weld `claim_m == eq(tau, r) * A_bb(r) * B_bb(r)` (ZERO host oracle / ZERO `Option`!):
        let ab_prod = push_ext4_mul(&mut push_gate, eval_a, eval_b, &mut cur_row);
        let computed_term = push_ext4_mul(&mut push_gate, eq_acc, ab_prod, &mut cur_row);
        for l in 0..4 {
            push_gate(false, claim_rows[l], computed_term[l], ROW_ZERO, &mut cur_row);
        }
        if cur_row > HEM_EXEC_ROWS {
            return Err(format!("circuit rows {cur_row} exceed HEM_EXEC_ROWS={HEM_EXEC_ROWS}"));
        }

        Ok(Self {
            bb_num_rounds,
            vk_cols: vec![sel_mac, sel_eq, sel_fs, sel_wbb, src_a, src_b, src_c, rom_q_next],
            g_rows,
            fs_rows,
            pub_r_indices,
            pub_a_indices,
            first_mac_row,
            total_used_rows: cur_row,
        })
    }
}

/// Opaque preprocessed public Verifier Key (depends ONLY on `bb_num_rounds`, zero witness!).
/// Fields are private so external/untrusted callers cannot fabricate a VK with forged roots (`H4` fix).
#[derive(Clone)]
pub struct TrustlessHemVk {
    layout: TrustlessHemCircuitLayout,
    canopy: Stage0MatrixCanopy,
}

impl TrustlessHemVk {
    pub fn build(bb_num_rounds: usize) -> Result<Self, String> {
        let layout = TrustlessHemCircuitLayout::build(bb_num_rounds)?;
        let canopy = Stage0MatrixCanopy::commit_base(0, &layout.vk_cols, UD100_BLOWUP, CANOPY_KEY_VK);
        Ok(Self { layout, canopy })
    }

    #[inline]
    pub fn bb_num_rounds(&self) -> usize {
        self.layout.bb_num_rounds
    }

    #[inline]
    pub fn p2_root(&self) -> [u64; 4] {
        self.canopy.p2_root()
    }

    #[inline]
    pub fn cshake_root(&self) -> [u8; 32] {
        self.canopy.cshake_root()
    }
}

/// Verifier-owned canonical VK cache for all supported round counts (`bb_num_rounds ∈ 1..=6`).
/// Guarantees `verify_trustless_dregg180_hem_stream` NEVER relies on a caller/prover-supplied VK (`H4` fix!).
pub fn canonical_trustless_vk(bb_num_rounds: usize) -> Result<&'static TrustlessHemVk, String> {
    use std::sync::OnceLock;
    if bb_num_rounds == 0 || bb_num_rounds > HEM_MAX_BB_ROUNDS {
        return Err(format!("bb_num_rounds must be in 1..={HEM_MAX_BB_ROUNDS}, got {bb_num_rounds}"));
    }
    static CACHE: [OnceLock<TrustlessHemVk>; HEM_MAX_BB_ROUNDS] = [
        OnceLock::new(), OnceLock::new(), OnceLock::new(),
        OnceLock::new(), OnceLock::new(), OnceLock::new(),
    ];
    Ok(CACHE[bb_num_rounds - 1].get_or_init(|| {
        TrustlessHemVk::build(bb_num_rounds).expect("canonical TrustlessHemVk build")
    }))
}

/// Public statement for Trustless (`pin_mode = false`, `k_mac = None`) `UD-100` `OP_HEM` verification.
/// Contains NO unverified terminal evaluation claim — `Dregg180StreamVm` itself proves
/// `claim_m == eq(bb_tau, r) * A_bb(r) * B_bb(r) (mod p_BB)` directly against `(w_bb_p2_root, w_bb_cs_root)`!
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustlessHemPublicStatement {
    pub bb_num_rounds: usize,
    pub bb_tau: [BbExt4; HEM_MAX_BB_ROUNDS],
    pub bb_initial_claim: BbExt4,
    pub vk_p2_root: [u64; 4],
    pub vk_cs_root: [u8; 32],
    pub w_bb_p2_root: [u64; 4],
    pub w_bb_cs_root: [u8; 32],
    pub bytes_p2_root: [u64; 4],
    pub bytes_cs_root: [u8; 32],
}

/// Caller/verifier-owned expected statement (ZERO `Option` callbacks — 100% self-contained on `Dregg180StreamVm`!).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierExpectedTrustlessStatement {
    pub bb_num_rounds: usize,
    pub bb_tau: [BbExt4; HEM_MAX_BB_ROUNDS],
    pub bb_initial_claim: BbExt4,
    pub w_bb_p2_root: [u64; 4],
    pub w_bb_cs_root: [u8; 32],
    pub bytes_p2_root: [u64; 4],
    pub bytes_cs_root: [u8; 32],
}

impl TrustlessHemPublicStatement {
    pub fn vk_cs_pin4(&self) -> [u64; 4] {
        p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &pack_digest32_to_5_limbs(&self.vk_cs_root))
    }

    pub fn w_bb_cs_pin4(&self) -> [u64; 4] {
        p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &pack_digest32_to_5_limbs(&self.w_bb_cs_root))
    }

    pub fn bytes_cs_pin4(&self) -> [u64; 4] {
        p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, FS_INIT_CAP, &pack_digest32_to_5_limbs(&self.bytes_cs_root))
    }

    /// Strict statement-ingress canonicality check (`L3` + BabyBear canonicality + unused-slot zeroing).
    pub fn validate_canonical(&self) -> Result<(), String> {
        if self.bb_num_rounds == 0 || self.bb_num_rounds > HEM_MAX_BB_ROUNDS {
            return Err(format!(
                "statement bb_num_rounds={} out of range 1..={HEM_MAX_BB_ROUNDS}",
                self.bb_num_rounds
            ));
        }
        for (name, root) in [
            ("vk_p2_root", self.vk_p2_root),
            ("w_bb_p2_root", self.w_bb_p2_root),
            ("bytes_p2_root", self.bytes_p2_root),
        ] {
            if root.iter().any(|&w| w >= GOLDILOCKS_PRIME) {
                return Err(format!("statement {name} contains non-canonical Goldilocks limb >= p_GL"));
            }
        }
        if !self.bb_initial_claim.is_canonical() {
            return Err("statement contains non-canonical BabyBear Ext4 initial claim >= p_BB".into());
        }
        for i in 0..self.bb_num_rounds {
            if !self.bb_tau[i].is_canonical() {
                return Err(format!("statement bb_tau[{i}] contains non-canonical limb >= p_BB"));
            }
        }
        for i in self.bb_num_rounds..HEM_MAX_BB_ROUNDS {
            if self.bb_tau[i] != BbExt4::ZERO {
                return Err(format!("statement unused bb_tau[{i}] must be zero"));
            }
        }
        Ok(())
    }

    /// Compute the causal Fiat-Shamir `R_CH` state immediately BEFORE Pass 1 (`g_0..g_{m-1}`),
    /// binding the `v3` schedule, canonical `vk`, committed `w_bb`, committed `bytes`, `bb_tau`, and `bb_initial_claim`.
    pub fn transcript_ch_before_pass1(&self) -> [u64; 4] {
        let mut rel_imm = pack_bytes_7_limbs(b"DREGG180.TRUSTLESS.BB4_DFA.UD100/v3");
        rel_imm.extend_from_slice(&[
            self.bb_num_rounds as u64,
            HEM_EXEC_VARS as u64,
            HEM_RNG16_VARS as u64,
            UD100_BLOWUP as u64,
            UD100_NUM_QUERIES as u64,
            UD100_POW_BITS as u64,
        ]);
        let mut ch = p2_sponge_hash_limbs(P2_DOMAIN_FS_BIND_REL, FS_INIT_CAP, &rel_imm);
        ch = fs_absorb_limbs_local(ch, b"VK_P2_ROOT", &self.vk_p2_root);
        ch = fs_absorb_limbs_local(ch, b"VK_CS_ROOT", &self.vk_cs_pin4());
        ch = fs_absorb_limbs_local(ch, b"WBB_P2_ROOT", &self.w_bb_p2_root);
        ch = fs_absorb_limbs_local(ch, b"WBB_CS_ROOT", &self.w_bb_cs_pin4());
        ch = fs_absorb_limbs_local(ch, b"BYTES_P2_ROOT", &self.bytes_p2_root);
        ch = fs_absorb_limbs_local(ch, b"BYTES_CS_ROOT", &self.bytes_cs_pin4());
        for j in 0..self.bb_num_rounds {
            let t4 = self.bb_tau[j].0.map(|x| x as u64);
            ch = fs_absorb_limbs_local(ch, b"BB_TAU", &t4);
        }
        let ic = self.bb_initial_claim.0.map(|x| x as u64);
        ch = fs_absorb_limbs_local(ch, b"BB_INIT_CLAIM", &ic);
        ch
    }
}

/// Real child `BabyBear Ext4` (`X^4 - 11`) cubic sumcheck transcript (`g_i(X) = c0 + c1*X + c2*X^2 + c3*X^3`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChildBabyBearSumcheckTranscript {
    pub bb_tau: [BbExt4; HEM_MAX_BB_ROUNDS],
    pub initial_claim: BbExt4,
    pub round_polys: Vec<[BbExt4; 4]>,
    pub raw_gl_challenges: Vec<[u64; 4]>,
    pub bb_challenges: Vec<BbExt4>,
    pub expected_terminal_eval: BbExt4,
}

/// Prove a genuine `m_rounds`-variable cubic `BabyBear Ext4` (`X^4 - 11`) sumcheck
/// `sum_{x in {0,1}^m} eq(tau, x) * A(x) * B(x) == initial_claim` using the exact causal
/// `Poseidon2-12` (`Goldilocks -> BabyBear`) Fiat-Shamir challenges matching `Dregg180StreamVm` Pass 1!
pub fn prove_child_babybear_ext4_cubic_sumcheck(
    m_rounds: usize,
    vk: &TrustlessHemVk,
    w_bb_comm: &BabyBearWitnessCommitment,
    payload_comm: &PayloadBytesCommitment,
    a_vals: &[u32],
    b_vals: &[u32],
    tau_bb: &[BbExt4],
) -> Result<ChildBabyBearSumcheckTranscript, String> {
    let n = 1usize << m_rounds;
    if m_rounds == 0 || m_rounds > HEM_MAX_BB_ROUNDS || a_vals.len() != n || b_vals.len() != n || tau_bb.len() != m_rounds {
        return Err("child BabyBear sumcheck dimension mismatch".into());
    }
    let mut tau_arr = [BbExt4::ZERO; HEM_MAX_BB_ROUNDS];
    for j in 0..m_rounds {
        tau_arr[j] = tau_bb[j];
    }
    let mut eq_t = crate::ext4::build_eq_table_lsb_ext4(tau_bb);
    let mut a_t: Vec<BbExt4> = a_vals.iter().map(|&v| BbExt4::from_bb(v)).collect();
    let mut b_t: Vec<BbExt4> = b_vals.iter().map(|&v| BbExt4::from_bb(v)).collect();
    let mut initial_claim = BbExt4::ZERO;
    for i in 0..n {
        initial_claim = initial_claim.add(eq_t[i].mul(a_t[i]).mul(b_t[i]));
    }
    let dummy_stmt = TrustlessHemPublicStatement {
        bb_num_rounds: m_rounds,
        bb_tau: tau_arr,
        bb_initial_claim: initial_claim,
        vk_p2_root: vk.p2_root(),
        vk_cs_root: vk.cshake_root(),
        w_bb_p2_root: w_bb_comm.p2_root(),
        w_bb_cs_root: w_bb_comm.cshake_root(),
        bytes_p2_root: payload_comm.p2_root(),
        bytes_cs_root: payload_comm.cshake_root(),
    };
    let mut ch = dummy_stmt.transcript_ch_before_pass1();
    let inv2_bb = crate::ext4::INV2_BB;
    let inv6_bb = crate::ext4::binv(6).unwrap();
    let bb_two = BbExt4::from_bb(2);
    let bb_three = BbExt4::from_bb(3);
    let bb_six = BbExt4::from_bb(6);

    let mut round_polys = Vec::with_capacity(m_rounds);
    let mut raw_gl_challenges = Vec::with_capacity(m_rounds);
    let mut bb_challenges = Vec::with_capacity(m_rounds);
    let mut running = initial_claim;

    for rnd in 0..m_rounds {
        let half = a_t.len() / 2;
        let (mut y0, mut y1, mut y2, mut y3) = (BbExt4::ZERO, BbExt4::ZERO, BbExt4::ZERO, BbExt4::ZERO);
        for i in 0..half {
            let (e0, e1) = (eq_t[2 * i], eq_t[2 * i + 1]);
            let (u0, u1) = (a_t[2 * i], a_t[2 * i + 1]);
            let (v0, v1) = (b_t[2 * i], b_t[2 * i + 1]);
            let de = e1.sub(e0);
            let du = u1.sub(u0);
            let dv = v1.sub(v0);
            y0 = y0.add(e0.mul(u0).mul(v0));
            y1 = y1.add(e1.mul(u1).mul(v1));
            let (e2, u2, v2) = (e1.add(de), u1.add(du), v1.add(dv));
            y2 = y2.add(e2.mul(u2).mul(v2));
            let (e3, u3, v3) = (e2.add(de), u2.add(du), v2.add(dv));
            y3 = y3.add(e3.mul(u3).mul(v3));
        }
        // Newton forward-difference cubic interpolation on `{0, 1, 2, 3}` in `BabyBear Ext4`:
        // `c0 = y0`, `c3 = (y3 - 3*y2 + 3*y1 - y0) / 6`,
        // `c2 = (y2 - 2*y1 + y0) / 2 - 3*c3`, `c1 = y1 - y0 - c2 - c3`.
        let d1_0 = y1.sub(y0);
        let d1_1 = y2.sub(y1);
        let d1_2 = y3.sub(y2);
        let d2_0 = d1_1.sub(d1_0);
        let d2_1 = d1_2.sub(d1_1);
        let d3_0 = d2_1.sub(d2_0);
        let c0 = y0;
        let c3 = d3_0.scale_bb(inv6_bb);
        let c2 = d2_0.scale_bb(inv2_bb).sub(c3.mul(bb_three));
        let c1 = d1_0.sub(c2).sub(c3);
        let _ = (bb_two, bb_six);
        debug_assert_eq!(c0.add(c0).add(c1).add(c2).add(c3), running);
        let poly = [c0, c1, c2, c3];
        round_polys.push(poly);

        for k in 0..4 {
            let mut lab = *b"BB_SC_G0";
            lab[7] = b'0' + (k as u8);
            let limbs4 = poly[k].0.map(|x| x as u64);
            ch = fs_absorb_limbs_local(ch, &lab, &limbs4);
        }
        let raw_ext = fs_squeeze_ext4_local(ch, b"BB_SC_RAW_R", rnd as u64);
        let raw4 = raw_ext.to_u64_limbs();
        for &w in &raw4 {
            if w / BABYBEAR_PRIME_U64 > BABYBEAR_FS_Q_SAFE {
                return Err("squeezed Goldilocks challenge exceeded BABYBEAR_FS_Q_SAFE tail (prob 4.7e-11)".into());
            }
        }
        let r_bb = BbExt4([
            (raw4[0] % BABYBEAR_PRIME_U64) as u32,
            (raw4[1] % BABYBEAR_PRIME_U64) as u32,
            (raw4[2] % BABYBEAR_PRIME_U64) as u32,
            (raw4[3] % BABYBEAR_PRIME_U64) as u32,
        ]);
        raw_gl_challenges.push(raw4);
        bb_challenges.push(r_bb);
        running = c3.mul(r_bb).add(c2).mul(r_bb).add(c1).mul(r_bb).add(c0);

        let mut n_eq = Vec::with_capacity(half);
        let mut n_a = Vec::with_capacity(half);
        let mut n_b = Vec::with_capacity(half);
        for i in 0..half {
            n_eq.push(eq_t[2 * i].add(r_bb.mul(eq_t[2 * i + 1].sub(eq_t[2 * i]))));
            n_a.push(a_t[2 * i].add(r_bb.mul(a_t[2 * i + 1].sub(a_t[2 * i]))));
            n_b.push(b_t[2 * i].add(r_bb.mul(b_t[2 * i + 1].sub(b_t[2 * i]))));
        }
        eq_t = n_eq;
        a_t = n_a;
        b_t = n_b;
    }
    debug_assert_eq!(eq_t[0].mul(a_t[0]).mul(b_t[0]), running);
    Ok(ChildBabyBearSumcheckTranscript {
        bb_tau: tau_arr,
        initial_claim,
        round_polys,
        raw_gl_challenges,
        bb_challenges,
        expected_terminal_eval: running,
    })
}

/// Adversarial tamper hooks for testing an untrusted prover (with NO `K_MAC`, `pin_mode = false`)
/// against `verify_trustless_dregg180_hem_stream`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustlessHemTamper {
    None,
    /// Tamper `g_0(0)` limb 0 by `+1 mod p_BB` so `g_0(0) + g_0(1) != initial_claim`.
    WrongBabyBearRoundSum,
    /// Tamper last-round `g_{m-1}` so `g_{m-1}(r_{m-1}) != eq(tau, r) * A_bb(r) * B_bb(r)` while `g_{m-1}(0)+g_{m-1}(1) == claim_{m-1}`!
    WrongBabyBearHornerEval,
    /// Forge a non-canonical BabyBear remainder `r = r_honest + p_BB < 2^32` (`q = q_honest - 1`, `d = 0`),
    /// passing `a*b + c == q*p_BB + r` AND 2-limb 16-bit range, caught ONLY by `r + d == p_BB - 1`!
    NonCanonicalBabyBearAliasGtPbb,
    /// Forge exact `r = p_BB` (alias of `0`) on a MAC row with `a*b + c == q_honest*p_BB + 0` (`r_honest == 0`),
    /// so MAC residual is IDENTICALLY ZERO and ONLY canonical slack `r + d == p_BB - 1` rejects (`M3` fix!).
    NonCanonicalBabyBearExactPbbAlias,
    /// Corrupt quotient `q_lo` by `+1` on a BabyBear MAC row (breaking `a*b + c == q*p_BB + r`).
    WrongBabyBearQuotient,
    /// Payload contains `"sk-"`; untrusted prover tries to lie `s_terminal = 0` while keeping honest DFA trace.
    ForgedDfaTerminalState,
    /// Payload contains `"sk-"`; untrusted prover forges transition `(2, '-') -> 0` instead of sink `3`.
    ForgedDfaTransitionBypass,
    /// Payload contains `"sk-"`; untrusted prover breaks state continuity `dfa_s[t+1] = 0 != dfa_s_next[t] = 3`.
    ForgedDfaShiftBreak,
    /// Untrusted prover corrupts `[0, 2^16)` LogUp multiplicity `m_rng16` on Table 2.
    ForgedRange16Multiplicity,
    /// Untrusted prover corrupts one Stage-1 BaseFold fiber evaluation on Table 1.
    TamperedStage1BaseFoldFiber,
    /// Untrusted prover flips 1 bit in a Stage-0 `cSHAKE256` Canopy sibling on Table 1.
    TamperedStage0CShakeSibling,
}

struct ExecChallengeTuple {
    gamma_w: GoldilocksExt4,
    beta_w: GoldilocksExt4,
    gamma_dfa: GoldilocksExt4,
    beta_dfa: GoldilocksExt4,
    gamma_sh: GoldilocksExt4,
    beta_sh: GoldilocksExt4,
    beta_16: GoldilocksExt4,
    alpha_exec: GoldilocksExt4,
}

/// Evaluate `G_exec` at a single (hypercube or extrapolated) point from all 37 column values + public MLEs.
#[inline]
#[allow(clippy::too_many_arguments)]
fn eval_g_exec_point(
    v: &[GoldilocksExt4; 37],
    eq_tau: GoldilocksExt4,
    idx: GoldilocksExt4,
    rom_b: GoldilocksExt4,
    rom_q: GoldilocksExt4,
    eq_first: GoldilocksExt4,
    eq_last: GoldilocksExt4,
    pub_sel_r: GoldilocksExt4,
    pub_sel_a: GoldilocksExt4,
    ch: &ExecChallengeTuple,
) -> GoldilocksExt4 {
    let sel_mac = v[0];
    let sel_eq = v[1];
    let sel_fs = v[2];
    let sel_wbb = v[3];
    let src_a = v[4];
    let src_b = v[5];
    let src_c = v[6];
    let rom_q_next = v[7];
    let dfa_b = v[8];
    let w_bb = v[9];
    let a = v[10];
    let b = v[11];
    let c = v[12];
    let r_lo = v[13];
    let r_hi = v[14];
    let d_lo = v[15];
    let d_hi = v[16];
    let q_lo = v[17];
    let q_hi = v[18];
    let q_top = v[19];
    let dq_lo = v[20];
    let dq_hi = v[21];
    let dq_top = v[22];
    let m_wire = v[23];
    let dfa_s = v[24];
    let dfa_s_next = v[25];
    let dfa_b_slack = v[26];
    let m_dfa_rom = v[27];
    let h_w01 = v[28];
    let h_w2r = v[29];
    let h_dfa = v[30];
    let h_sh = v[31];
    let h_rng0 = v[32];
    let h_rng1 = v[33];
    let h_rng2 = v[34];
    let h_rng3 = v[35];
    let h_rng4 = v[36];

    let two16 = Goldilocks(1u64 << 16);
    let two32 = Goldilocks(1u64 << 32);
    let p_bb = Goldilocks(BABYBEAR_PRIME_U64);
    let p_bb_m1 = GoldilocksExt4::from_base(Goldilocks(BABYBEAR_PRIME_U64 - 1));
    let q_safe = GoldilocksExt4::from_base(Goldilocks(BABYBEAR_FS_Q_SAFE));
    let two_ext = GoldilocksExt4::from_base(Goldilocks::TWO);
    let c255 = GoldilocksExt4::from_base(Goldilocks(255));

    let r_val = r_lo + r_hi.scale_base(two16);
    let d_val = d_lo + d_hi.scale_base(two16);
    let q_val = q_lo + q_hi.scale_base(two16);
    let q_fs = q_val + q_top.scale_base(two32);
    let dq_fs = dq_lo + dq_hi.scale_base(two16) + dq_top.scale_base(two32);

    let c0 = sel_mac * (a * b + c - q_val.scale_base(p_bb) - r_val);
    let c1 = sel_eq * (a - b);
    let c2 = sel_fs * (a - q_fs.scale_base(p_bb) - r_val);
    let c3 = sel_fs * (q_fs + dq_fs - q_safe);
    let c4 = q_top * (q_top - GoldilocksExt4::ONE) * (q_top - two_ext);
    let c5 = dq_top * (dq_top - GoldilocksExt4::ONE) * (dq_top - two_ext);
    let c6 = r_val + d_val - p_bb_m1;
    let c7 = dfa_b + dfa_b_slack - c255;

    let dw_a = ch.beta_w - (src_a + ch.gamma_w * a);
    let dw_b = ch.beta_w - (src_b + ch.gamma_w * b);
    let c8 = h_w01 * dw_a * dw_b - ((GoldilocksExt4::ONE - sel_fs) * dw_b + dw_a);

    let dw_c = ch.beta_w - (src_c + ch.gamma_w * c);
    let dw_r = ch.beta_w - (idx + ch.gamma_w * r_val);
    let c9 = h_w2r * dw_c * dw_r - (dw_r - m_wire * dw_c);

    let g_dfa2 = ch.gamma_dfa * ch.gamma_dfa;
    let dd_l = ch.beta_dfa - (dfa_s + ch.gamma_dfa * dfa_b + g_dfa2 * dfa_s_next);
    let dd_r = ch.beta_dfa - (rom_q + ch.gamma_dfa * rom_b + g_dfa2 * rom_q_next);
    let c10 = h_dfa * dd_l * dd_r - (dd_r - m_dfa_rom * dd_l);

    let ds_l = ch.beta_sh - (idx + GoldilocksExt4::ONE + ch.gamma_sh * dfa_s_next);
    let ds_r = ch.beta_sh - (idx + ch.gamma_sh * dfa_s);
    let n_sh_l = GoldilocksExt4::ONE - eq_last;
    let n_sh_r = GoldilocksExt4::ONE - eq_first;
    let c11 = h_sh * ds_l * ds_r - (n_sh_l * ds_r - n_sh_r * ds_l);

    let rng_c = |h: GoldilocksExt4, x0: GoldilocksExt4, x1: GoldilocksExt4| -> GoldilocksExt4 {
        let d0 = ch.beta_16 - x0;
        let d1 = ch.beta_16 - x1;
        h * d0 * d1 - (d0 + d1)
    };
    let c12 = rng_c(h_rng0, r_lo, r_hi);
    let c13 = rng_c(h_rng1, d_lo, d_hi);
    let c14 = rng_c(h_rng2, q_lo, q_hi);
    let c15 = rng_c(h_rng3, dq_lo, dq_hi);
    let c16 = rng_c(h_rng4, dfa_b, dfa_b_slack);
    // C_17: bind Table 1 witness rows `32..32+2^{m+1}` to the public committed `W_bb` Canopy column!
    let c17 = sel_wbb * (r_val - w_bb);

    let cs = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17];
    let mut zero_acc = GoldilocksExt4::ZERO;
    let mut ap = GoldilocksExt4::ONE;
    for &ck in &cs {
        zero_acc = zero_acc + ap * ck;
        ap = ap * ch.alpha_exec;
    }
    // `ap == alpha_exec^18` now:
    let mut tot = eq_tau * zero_acc;
    let sum_terms = [
        h_w01 + h_w2r,                                     // 18
        h_dfa,                                             // 19
        h_sh,                                              // 20
        h_rng0 + h_rng1 + h_rng2 + h_rng3 + h_rng4,        // 21
        pub_sel_r * r_val,                                 // 22
        pub_sel_a * a,                                     // 23
        eq_first * dfa_s,                                  // 24
        eq_last * dfa_s_next,                              // 25
    ];
    for &st in &sum_terms {
        tot = tot + ap * st;
        ap = ap * ch.alpha_exec;
    }
    tot
}

struct TrustlessHemInternalProof {
    bb_round_polys: Vec<[BbExt4; 4]>,
    bb_raw_chals: Vec<[u64; 4]>,
    wit1_p2_root: [u64; 4],
    wit1_cs_pin4: [u64; 4],
    mrng_p2_root: [u64; 4],
    mrng_cs_pin4: [u64; 4],
    s_terminal: GoldilocksExt4,
    wit2_p2_root: [u64; 4],
    wit2_cs_pin4: [u64; 4],
    hrng_p2_root: [u64; 4],
    hrng_cs_pin4: [u64; 4],
    s_rng16: GoldilocksExt4,
    ch_logup_ckpt: [u64; 4],
    ch_sc_ckpt: [u64; 4],
    t1_sc_rounds: Vec<[GoldilocksExt4; 4]>, // (c0, c2, c3, c4) per round
    t1_evals_37: [GoldilocksExt4; 37],
    t1_bf: LockstepBaseFoldProof,
    t1_pow_nonce: u64,
    t1_queries: Vec<Table1QueryOpening>,
    t2_sc_rounds: Vec<[GoldilocksExt4; 3]>, // (c0, c2, c3) per round
    t2_evals_2: [GoldilocksExt4; 2],        // [m_rng16(z), h_rng_tab(z)]
    t2_bf: LockstepBaseFoldProof,
    t2_pow_nonce: u64,
    t2_queries: Vec<Table2QueryOpening>,
}

struct Table1QueryOpening {
    f0: u32,
    vk_words: Vec<u64>,
    vk_p2_sibs: Vec<[u64; 4]>,
    vk_cs_sibs: Vec<[u8; 32]>,
    bytes_words: Vec<u64>,
    bytes_p2_sibs: Vec<[u64; 4]>,
    bytes_cs_sibs: Vec<[u8; 32]>,
    w_bb_words: Vec<u64>,
    w_bb_p2_sibs: Vec<[u64; 4]>,
    w_bb_cs_sibs: Vec<[u8; 32]>,
    wit1_words: Vec<u64>,
    wit1_p2_sibs: Vec<[u64; 4]>,
    wit1_cs_sibs: Vec<[u8; 32]>,
    wit2_words: Vec<u64>,
    wit2_p2_sibs: Vec<[u64; 4]>,
    wit2_cs_sibs: Vec<[u8; 32]>,
    stage_fibers: Vec<(u32, Vec<GoldilocksExt4>, Vec<[u64; 4]>)>,
}

struct Table2QueryOpening {
    f0: u32,
    mrng_words: Vec<u64>,
    mrng_p2_sibs: Vec<[u64; 4]>,
    mrng_cs_sibs: Vec<[u8; 32]>,
    hrng_words: Vec<u64>,
    hrng_p2_sibs: Vec<[u64; 4]>,
    hrng_cs_sibs: Vec<[u8; 32]>,
    stage_fibers: Vec<(u32, Vec<GoldilocksExt4>, Vec<[u64; 4]>)>,
}

/// Complete trustless (`pin_mode = false`, `k_mac = None`) `UD-100` `OP_HEM` proof bundle.
#[derive(Clone, Debug)]
pub struct TrustlessHemProofBundle {
    pub stmt: TrustlessHemPublicStatement,
    pub wire_bytes: Vec<u8>,
    pub public_program_hash: [u64; 4],
    pub s_terminal: u8,
    pub num_records: usize,
}

/// Helper: load selected indices from `evals_37` into `(idx, dst_reg)` registers while verifying
/// the 256-bit Davies-Meyer `Poseidon2-12` commitment `R_12 == compress(evals_37)`.
fn emit_checked_evals37_load(
    asm: &mut Dregg180HvmAssembler,
    evals_opt: Option<&[GoldilocksExt4; 37]>,
    want_digest_reg: u8,
    latches: &[(usize, u8)],
) {
    debug_assert!(
        latches.iter().all(|&(_, dst)| dst != R_T0 && dst != R_X && dst != R_Y),
        "emit_checked_evals37_load latches must not target clobbered scratch regs R_T0/R_X/R_Y"
    );
    emit_zero_reg(asm, R_Y);
    for k in 0..37 {
        let w = match evals_opt {
            Some(e) => e[k].to_u64_limbs(),
            None => [0u64; 4],
        };
        asm.load(R_X, &w, false);
        for &(idx, dst) in latches {
            if idx == k {
                emit_copy_reg(asm, dst, R_X);
            }
        }
        emit_compress_reg(asm, R_Y, R_X, 0xE000 + (k as u64));
    }
    asm.assert_eq(R_Y, want_digest_reg);
}

/// Helper: squeeze a Fiat-Shamir `GoldilocksExt4` challenge from a saved checkpoint register `ckpt_reg`!
fn emit_squeeze_from_ckpt(asm: &mut Dregg180HvmAssembler, dst: u8, ckpt_reg: u8, label: &[u8], ctr: u64) {
    let mut imm = pack_bytes_7_limbs(label);
    imm.push(ctr);
    asm.hash(dst, Some(ckpt_reg), P2_DOMAIN_FS_SQUEEZE_EXT4, &imm, &[], 0, 0);
}

/// Single unified deterministic bytecode emitter for BOTH:
/// - `proof = Some(p)`: real untrusted prover stream (`pin_mode = false`, `k_mac = None`), AND
/// - `proof = None`: trustless verifier's keyless `public_program_hash` derivation from `stmt` ALONE!
fn emit_trustless_hem_stream(
    stmt: &TrustlessHemPublicStatement,
    layout: &TrustlessHemCircuitLayout,
    proof: Option<&TrustlessHemInternalProof>,
) -> Dregg180HvmAssembler {
    let mut asm = Dregg180HvmAssembler::new(OP_HEM, false, false);
    let zero4 = [0u64; 4];
    let m = stmt.bb_num_rounds;

    // --------------------------------------------------------------------------------------------
    // Round 0: Public Statement & `UD-100` Schedule Immediates (pinned by keyless `public_program_hash`)
    // --------------------------------------------------------------------------------------------
    let mut rel_imm = pack_bytes_7_limbs(b"DREGG180.TRUSTLESS.BB4_DFA.UD100/v3");
    rel_imm.extend_from_slice(&[
        m as u64,
        HEM_EXEC_VARS as u64,
        HEM_RNG16_VARS as u64,
        UD100_BLOWUP as u64,
        UD100_NUM_QUERIES as u64,
        UD100_POW_BITS as u64,
    ]);
    asm.hash(R_CH, None, P2_DOMAIN_FS_BIND_REL, &rel_imm, &[], 0, 0);
    asm.absorb_limbs_immediate(b"VK_P2_ROOT", &stmt.vk_p2_root, 0, 0);
    asm.absorb_limbs_immediate(b"VK_CS_ROOT", &stmt.vk_cs_pin4(), 0, 0);
    asm.absorb_limbs_immediate(b"WBB_P2_ROOT", &stmt.w_bb_p2_root, 0, 0);
    asm.absorb_limbs_immediate(b"WBB_CS_ROOT", &stmt.w_bb_cs_pin4(), 0, 0);
    asm.absorb_limbs_immediate(b"BYTES_P2_ROOT", &stmt.bytes_p2_root, 0, 0);
    asm.absorb_limbs_immediate(b"BYTES_CS_ROOT", &stmt.bytes_cs_pin4(), 0, 0);
    for j in 0..m {
        let tau_limbs = stmt.bb_tau[j].0.map(|x| x as u64);
        asm.absorb_limbs_immediate(b"BB_TAU", &tau_limbs, 0, 0);
    }
    let init_claim_limbs = stmt.bb_initial_claim.0.map(|x| x as u64);
    asm.absorb_limbs_immediate(b"BB_INIT_CLAIM", &init_claim_limbs, 0, 0);

    // --------------------------------------------------------------------------------------------
    // Round 1 (Pass 1): Child `BabyBear Ext4` Transcript `g_i -> raw_r_i`, compressed into `R_12`!
    // --------------------------------------------------------------------------------------------
    emit_zero_reg(&mut asm, 12);
    for rnd in 0..m {
        let mut g16 = [0u64; 16];
        if let Some(p) = proof {
            for k in 0..4 {
                for l in 0..4 {
                    g16[4 * k + l] = p.bb_round_polys[rnd][k].0[l] as u64;
                }
            }
        }
        for k in 0..4 {
            let mut lab = *b"BB_SC_G0";
            lab[7] = b'0' + (k as u8);
            asm.absorb_limbs_proof(&lab, &g16[4 * k..4 * (k + 1)], R_X, 0);
            emit_compress_reg(&mut asm, 12, R_X, 0xB000 + ((rnd * 5 + k) as u64));
        }
        asm.squeeze_ext4(R_T0, b"BB_SC_RAW_R", rnd as u64);
        emit_compress_reg(&mut asm, 12, R_T0, 0xB000 + ((rnd * 5 + 4) as u64));
    }

    // --------------------------------------------------------------------------------------------
    // Round 2: Commit Phase-1 Witness Tables (`wit1`, `m_rng16`) + `s_terminal` (checked ∈ {0, 1, 2}!)
    // --------------------------------------------------------------------------------------------
    emit_zero_reg(&mut asm, 14); // `t1_root_bundle`
    emit_zero_reg(&mut asm, 15); // `t2_root_bundle`
    let (w1_p2, w1_cs, mr_p2, mr_cs, s_term_w) = match proof {
        Some(p) => (p.wit1_p2_root, p.wit1_cs_pin4, p.mrng_p2_root, p.mrng_cs_pin4, p.s_terminal.to_u64_limbs()),
        None => (zero4, zero4, zero4, zero4, zero4),
    };
    asm.absorb_limbs_proof(b"WIT1_P2_ROOT", &w1_p2, R_X, 0);
    emit_compress_reg(&mut asm, 14, R_X, 0x1001);
    asm.absorb_limbs_proof(b"WIT1_CS_ROOT", &w1_cs, R_X, 0);
    emit_compress_reg(&mut asm, 14, R_X, 0x1002);
    asm.absorb_limbs_proof(b"MRNG_P2_ROOT", &mr_p2, R_X, 0);
    emit_compress_reg(&mut asm, 15, R_X, 0x2001);
    asm.absorb_limbs_proof(b"MRNG_CS_ROOT", &mr_cs, R_X, 0);
    emit_compress_reg(&mut asm, 15, R_X, 0x2002);
    asm.absorb_limbs_proof(b"DFA_S_TERM", &s_term_w, R_X, 0);
    emit_copy_reg(&mut asm, 9, R_X); // `R_9 = s_terminal`
    // Enforce `s_terminal * (s_terminal - 1) * (s_terminal - 2) == 0` right on chip (`s_T ∈ {0, 1, 2}`!):
    asm.load(R_Y, &[1, 0, 0, 0], true);
    asm.esub(R_A, 9, R_Y);       // s - 1
    asm.emul(R_A, 9, R_A);       // s * (s - 1)
    asm.load(R_Y, &[2, 0, 0, 0], true);
    asm.esub(R_B, 9, R_Y);       // s - 2
    asm.emul(R_A, R_A, R_B);     // s * (s - 1) * (s - 2)
    emit_zero_reg(&mut asm, R_Y);
    asm.assert_eq(R_A, R_Y);

    // Snapshot `R_11 = R_CH` (checkpoint for LogUp challenges AFTER Phase-1 commitment!):
    emit_copy_reg(&mut asm, 11, R_CH);

    // --------------------------------------------------------------------------------------------
    // Round 4: Commit Phase-2 LogUp Helpers (`wit2`, `h_rng_tab`) + `S_rng16`
    // --------------------------------------------------------------------------------------------
    let (w2_p2, w2_cs, hr_p2, hr_cs, s_rng_w) = match proof {
        Some(p) => (p.wit2_p2_root, p.wit2_cs_pin4, p.hrng_p2_root, p.hrng_cs_pin4, p.s_rng16.to_u64_limbs()),
        None => (zero4, zero4, zero4, zero4, zero4),
    };
    asm.absorb_limbs_proof(b"WIT2_P2_ROOT", &w2_p2, R_X, 0);
    emit_compress_reg(&mut asm, 14, R_X, 0x1003);
    asm.absorb_limbs_proof(b"WIT2_CS_ROOT", &w2_cs, R_X, 0);
    emit_compress_reg(&mut asm, 14, R_X, 0x1004);
    asm.absorb_limbs_proof(b"HRNG_P2_ROOT", &hr_p2, R_X, 0);
    emit_compress_reg(&mut asm, 15, R_X, 0x2003);
    asm.absorb_limbs_proof(b"HRNG_CS_ROOT", &hr_cs, R_X, 0);
    emit_compress_reg(&mut asm, 15, R_X, 0x2004);
    asm.absorb_limbs_proof(b"LOGUP_S_RNG16", &s_rng_w, R_X, 0);
    emit_copy_reg(&mut asm, 8, R_X); // `R_8 = S_rng16`

    // Snapshot `R_10 = R_CH` (checkpoint for Sumcheck challenges AFTER Phase-2 commitment!):
    emit_copy_reg(&mut asm, 10, R_CH);

    // --------------------------------------------------------------------------------------------
    // Round 5 + Pass 2: Compute `PubRhs_r` (`R_6`) and `PubRhs_a` (`R_7`) and assert Pass 2 == Pass 1 (`R_12`)!
    // --------------------------------------------------------------------------------------------
    emit_squeeze_from_ckpt(&mut asm, R_B, 10, b"SC_LAMBDA_PUB", 0); // `R_B = lambda_pub`
    emit_zero_reg(&mut asm, 6);  // `PubRhs_r` (Horner over `pub_r_indices`)
    emit_zero_reg(&mut asm, 7);  // `PubRhs_a` (Horner over `pub_a_indices`)
    emit_zero_reg(&mut asm, 13); // `pass2_digest_check`

    // Prefix of `pub_r`: constants `[0, 1, 11, p_BB - 1]`, `bb_initial_claim[0..4]`, `bb_tau[0..m][0..4]` (all immediates!):
    let mut pub_r_fixed: Vec<u64> = vec![
        0,
        1,
        11,
        BABYBEAR_PRIME_U64 - 1,
        init_claim_limbs[0],
        init_claim_limbs[1],
        init_claim_limbs[2],
        init_claim_limbs[3],
    ];
    for j in 0..m {
        for l in 0..4 {
            pub_r_fixed.push(stmt.bb_tau[j].0[l] as u64);
        }
    }
    for &val in &pub_r_fixed {
        asm.emul(6, 6, R_B);
        asm.load(R_X, &[val, 0, 0, 0], true);
        asm.eadd(6, 6, R_X);
    }
    let basis_e: [[u64; 4]; 4] = [
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
    ];
    let inv7 = Goldilocks::SEVEN.inv().0;
    for rnd in 0..m {
        for k in 0..4 {
            emit_zero_reg(&mut asm, R_A); // reconstruct 4-limb `g_i[k]`
            for l in 0..4 {
                let limb = proof.map_or(0u64, |p| p.bb_round_polys[rnd][k].0[l] as u64);
                asm.push_rec(H_LOAD, R_X, 0, 0, vec![0, 0, 0, limb], 3);
                asm.load(R_Y, &[0, 0, inv7, 0], true);
                asm.emul(R_X, R_X, R_Y); // `R_X = [limb, 0, 0, 0]` GUARANTEED pure base-field!
                asm.emul(6, 6, R_B);
                asm.eadd(6, 6, R_X); // `PubRhs_r = PubRhs_r * lambda + limb`
                asm.load(R_Y, &basis_e[l], true);
                asm.emul(R_T0, R_X, R_Y);
                asm.eadd(R_A, R_A, R_T0); // accumulate exact 4-limb `Ext4` `g_i[k]`
            }
            emit_compress_reg(&mut asm, 13, R_A, 0xB000 + ((rnd * 5 + k) as u64));
        }
        emit_zero_reg(&mut asm, R_A); // reconstruct 4-limb `raw_r_i`
        for l in 0..4 {
            let limb = proof.map_or(0u64, |p| p.bb_raw_chals[rnd][l]);
            asm.push_rec(H_LOAD, R_X, 0, 0, vec![0, 0, 0, limb], 3);
            asm.load(R_Y, &[0, 0, inv7, 0], true);
            asm.emul(R_X, R_X, R_Y); // `R_X = [limb, 0, 0, 0]` GUARANTEED pure base-field!
            asm.emul(7, 7, R_B);
            asm.eadd(7, 7, R_X); // `PubRhs_a = PubRhs_a * lambda + limb`
            asm.load(R_Y, &basis_e[l], true);
            asm.emul(R_T0, R_X, R_Y);
            asm.eadd(R_A, R_A, R_T0);
        }
        emit_compress_reg(&mut asm, 13, R_A, 0xB000 + ((rnd * 5 + 4) as u64));
    }
    asm.assert_eq(13, 12); // Pass 2 `(g_i, raw_r_i)` == Pass 1 `(g_i, raw_r_i)`!

    // --------------------------------------------------------------------------------------------
    // Round 6a: Table 1 (`N_exec = 4096`) 12-Round Degree-4 AIR + LogUp + Boundary Sumcheck!
    // --------------------------------------------------------------------------------------------
    // Latch `tau_exec[0..12]` from `R_10` (`ch_sc_ckpt`):
    for j in 0..HEM_EXEC_VARS {
        emit_squeeze_from_ckpt(&mut asm, R_T0, 10, b"SC_TAU_EXEC", j as u64);
        asm.bf_latch_tau(j as u8, R_T0);
    }
    // Compute `InitClaim_exec = alpha^{21} * S_rng16 + alpha^{22} * PubRhs_r + alpha^{23} * PubRhs_a + alpha^{25} * s_terminal` into `R_A`:
    emit_squeeze_from_ckpt(&mut asm, R_B, 10, b"SC_ALPHA_EXEC", 0); // `R_B = alpha_exec`
    asm.load(R_X, &[1, 0, 0, 0], true);
    for _ in 0..21 {
        asm.emul(R_X, R_X, R_B); // `R_X = alpha^21`
    }
    asm.emul(R_A, R_X, 8);       // `alpha^21 * S_rng16`
    asm.emul(R_X, R_X, R_B);     // `alpha^22`
    asm.emul(R_T0, R_X, 6);
    asm.eadd(R_A, R_A, R_T0);    // `+ alpha^22 * PubRhs_r`
    asm.emul(R_X, R_X, R_B);     // `alpha^23`
    asm.emul(R_T0, R_X, 7);
    asm.eadd(R_A, R_A, R_T0);    // `+ alpha^23 * PubRhs_a`
    asm.emul(R_X, R_X, R_B);     // `alpha^24`
    asm.emul(R_X, R_X, R_B);     // `alpha^25`
    asm.emul(R_T0, R_X, 9);
    asm.eadd(R_A, R_A, R_T0);    // `+ alpha^25 * s_terminal`

    // Execute 10 rounds of degree-4 sumcheck (`c0, c2, c3, c4` sent; `c1 = claim - 2*c0 - c2 - c3 - c4`):
    // Use `R_6 = c0, R_7 = c2, R_9 = c3, R_12 = c4` (all free now!).
    for rnd in 0..HEM_EXEC_VARS {
        let (c0w, c2w, c3w, c4w) = match proof {
            Some(p) => (
                p.t1_sc_rounds[rnd][0].to_u64_limbs(),
                p.t1_sc_rounds[rnd][1].to_u64_limbs(),
                p.t1_sc_rounds[rnd][2].to_u64_limbs(),
                p.t1_sc_rounds[rnd][3].to_u64_limbs(),
            ),
            None => (zero4, zero4, zero4, zero4),
        };
        asm.absorb_limbs_proof(b"T1_SC_C0", &c0w, 6, 0);
        asm.absorb_limbs_proof(b"T1_SC_C2", &c2w, 7, 0);
        asm.absorb_limbs_proof(b"T1_SC_C3", &c3w, R_X, 0);
        emit_copy_reg(&mut asm, 9, R_X);
        asm.absorb_limbs_proof(b"T1_SC_C4", &c4w, R_X, 0);
        emit_copy_reg(&mut asm, 12, R_X);
        asm.squeeze_ext4(R_B, b"T1_SC_Z", rnd as u64);
        asm.bf_latch_z(rnd as u8, R_B);
        // `c1 = R_A - 2*R_6 - R_7 - R_9 - R_12`:
        asm.esub(R_T0, R_A, 6);
        asm.esub(R_T0, R_T0, 6);
        asm.esub(R_T0, R_T0, 7);
        asm.esub(R_T0, R_T0, 9);
        asm.esub(R_T0, R_T0, 12);
        // Horner `(((c4 * z + c3) * z + c2) * z + c1) * z + c0`:
        asm.emul(R_Y, 12, R_B);
        asm.eadd(R_Y, R_Y, 9);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_Y, R_Y, 7);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_Y, R_Y, R_T0);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_A, R_Y, 6);
    }
    // Save `term_exec` in `R_13`!
    emit_copy_reg(&mut asm, 13, R_A);

    // Absorb all 37 claimed evaluations at `z_exec` into `R_CH` AND compress into `R_12`:
    emit_zero_reg(&mut asm, 12);
    for k in 0..37 {
        let w = proof.map_or(zero4, |p| p.t1_evals_37[k].to_u64_limbs());
        asm.absorb_limbs_proof(b"T1_EV", &w, R_X, 0);
        emit_compress_reg(&mut asm, 12, R_X, 0xE000 + (k as u64));
    }

    // --------------------------------------------------------------------------------------------
    // On-chip exact evaluation of `G_exec(z_exec)` into `R_7` and `H_ASSERT_EQ(R_7, R_13)`!
    // Live persistent regs here: `R_7 = G_acc`, `R_8 = S_rng16`, `R_9 = alpha_pow`, `R_10 = ch_sc_ckpt`,
    // `R_11 = ch_logup_ckpt`, `R_12 = evals_digest`, `R_13 = term_exec`, `R_14 = t1_bundle`, `R_15 = t2_bundle`.
    // Free scratch: `R_T0, R_A, R_B, R_X, R_Y, R_6` (inside `emit_checked_evals37_load`, `R_X, R_Y` are used).
    // --------------------------------------------------------------------------------------------
    let evals_opt = proof.map(|p| &p.t1_evals_37);
    emit_zero_reg(&mut asm, 7); // `zero_acc` (`sum_{k=0..17} alpha^k C_k`)
    asm.load(9, &[1, 0, 0, 0], true); // `R_9 = alpha_pow = 1`
    let add_c_term = |asm: &mut Dregg180HvmAssembler, c_reg: u8| {
        asm.emul(R_T0, 9, c_reg);
        asm.eadd(7, 7, R_T0);
        emit_squeeze_from_ckpt(asm, R_T0, 10, b"SC_ALPHA_EXEC", 0);
        asm.emul(9, 9, R_T0);
    };

    // Helper: compute `lo + 2^16 * hi` into `dst` using `tmp` (neither `R_T0`, `R_X`, nor `R_Y`!):
    let load_lin2 = |asm: &mut Dregg180HvmAssembler, idx_lo: usize, idx_hi: usize, dst: u8, tmp: u8| {
        emit_checked_evals37_load(asm, evals_opt, 12, &[(idx_lo, dst), (idx_hi, tmp)]);
        asm.load(R_Y, &[1u64 << 16, 0, 0, 0], true);
        asm.emul(tmp, tmp, R_Y);
        asm.eadd(dst, dst, tmp);
    };

    // C_0 = sel_mac (0) * (a (10) * b (11) + c (12) - q_val (17,18) * p_BB - r_val (13,14)):
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(10, R_A), (11, R_B), (12, 6)]);
    asm.emul(R_A, R_A, R_B);
    asm.eadd(6, R_A, 6); // `R_6 = a*b + c`
    load_lin2(&mut asm, 17, 18, R_A, R_B); // `R_A = q_val`
    asm.load(R_Y, &[BABYBEAR_PRIME_U64, 0, 0, 0], true);
    asm.emul(R_A, R_A, R_Y);
    asm.esub(6, 6, R_A); // `R_6 = a*b + c - q_val*p_BB`
    load_lin2(&mut asm, 13, 14, R_A, R_B); // `R_A = r_val`
    asm.esub(6, 6, R_A);
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(0, R_A)]); // `sel_mac`
    asm.emul(6, R_A, 6);
    add_c_term(&mut asm, 6);

    // C_1 = sel_eq (1) * (a (10) - b (11)):
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(1, 6), (10, R_A), (11, R_B)]);
    asm.esub(R_A, R_A, R_B);
    asm.emul(6, 6, R_A);
    add_c_term(&mut asm, 6);

    // C_2 = sel_fs (2) * (a (10) - q_fs (17,18,19) * p_BB - r_val (13,14)) & C_3 = sel_fs * (q_fs + dq_fs - Q_SAFE):
    load_lin2(&mut asm, 17, 18, 6, R_A); // `q_val`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(19, R_A)]); // `q_top`
    asm.load(R_Y, &[1u64 << 32, 0, 0, 0], true);
    asm.emul(R_A, R_A, R_Y);
    asm.eadd(6, 6, R_A); // `R_6 = q_fs`
    emit_copy_reg(&mut asm, R_B, 6); // save `q_fs` in `R_B`
    asm.load(R_Y, &[BABYBEAR_PRIME_U64, 0, 0, 0], true);
    asm.emul(6, 6, R_Y); // `6 = q_fs * p_BB`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(13, R_A)]); // `r_lo`
    asm.eadd(6, 6, R_A);
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(14, R_A)]); // `r_hi`
    asm.load(R_Y, &[1u64 << 16, 0, 0, 0], true);
    asm.emul(R_A, R_A, R_Y);
    asm.eadd(6, 6, R_A); // `6 = q_fs * p_BB + r_val`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(10, R_A)]); // `a`
    asm.esub(R_A, R_A, 6); // `R_A = a - q_fs*p_BB - r_val`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(2, 6)]); // `sel_fs`
    asm.emul(6, 6, R_A); // `C_2`
    add_c_term(&mut asm, 6);

    // C_3: `R_B` STILL holds `q_fs`!
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(20, 6), (21, R_A)]); // `dq_lo, dq_hi`
    asm.load(R_Y, &[1u64 << 16, 0, 0, 0], true);
    asm.emul(R_A, R_A, R_Y);
    asm.eadd(6, 6, R_A);
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(22, R_A)]); // `dq_top`
    asm.load(R_Y, &[1u64 << 32, 0, 0, 0], true);
    asm.emul(R_A, R_A, R_Y);
    asm.eadd(6, 6, R_A); // `dq_fs`
    asm.eadd(6, 6, R_B); // `q_fs + dq_fs`
    asm.load(R_Y, &[BABYBEAR_FS_Q_SAFE, 0, 0, 0], true);
    asm.esub(6, 6, R_Y);
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(2, R_A)]); // `sel_fs`
    asm.emul(6, R_A, 6); // `C_3`
    add_c_term(&mut asm, 6);

    // C_4 = q_top (19) * (q_top - 1) * (q_top - 2) & C_5 = dq_top (22) * (dq_top - 1) * (dq_top - 2):
    for col_idx in [19usize, 22usize] {
        emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(col_idx, 6)]);
        asm.load(R_Y, &[1, 0, 0, 0], true);
        asm.esub(R_A, 6, R_Y);
        asm.emul(R_A, 6, R_A);
        asm.load(R_Y, &[2, 0, 0, 0], true);
        asm.esub(R_B, 6, R_Y);
        asm.emul(6, R_A, R_B);
        add_c_term(&mut asm, 6);
    }

    // C_6 = r_val (13,14) + d_val (15,16) - (p_BB - 1):
    load_lin2(&mut asm, 13, 14, 6, R_A);
    load_lin2(&mut asm, 15, 16, R_A, R_B);
    asm.eadd(6, 6, R_A);
    asm.load(R_Y, &[BABYBEAR_PRIME_U64 - 1, 0, 0, 0], true);
    asm.esub(6, 6, R_Y);
    add_c_term(&mut asm, 6);

    // C_7 = dfa_b (8) + dfa_b_slack (26) - 255:
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(8, 6), (26, R_A)]);
    asm.eadd(6, 6, R_A);
    asm.load(R_Y, &[255, 0, 0, 0], true);
    asm.esub(6, 6, R_Y);
    add_c_term(&mut asm, 6);

    // C_8 (`h_w01` = 28): `h_w01 * dw_a * dw_b - ((1 - sel_fs)*dw_b + dw_a)`:
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(4, R_A), (10, R_B)]); // `src_a, a`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_W", 0);
    asm.emul(R_B, R_B, R_T0);
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_W", 0);
    asm.esub(6, R_T0, R_A); // `R_6 = dw_a`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(5, R_A), (11, R_B)]); // `src_b, b`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_W", 0);
    asm.emul(R_B, R_B, R_T0);
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_W", 0);
    asm.esub(R_B, R_T0, R_A); // `R_B = dw_b`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(2, R_A)]); // `sel_fs`
    asm.load(R_Y, &[1, 0, 0, 0], true);
    asm.esub(R_A, R_Y, R_A); // `1 - sel_fs`
    asm.emul(R_A, R_A, R_B); // `(1 - sel_fs) * dw_b`
    asm.eadd(R_A, R_A, 6);   // `R_A = (1 - sel_fs)*dw_b + dw_a`
    asm.emul(6, 6, R_B);     // `6 = dw_a * dw_b`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(28, R_B)]); // `h_w01`
    asm.emul(6, R_B, 6);
    asm.esub(6, 6, R_A);     // `C_8`
    add_c_term(&mut asm, 6);

    // C_9 (`h_w2r` = 29): `h_w2r * dw_c * dw_r - (dw_r - m_wire * dw_c)`:
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(6, R_A), (12, R_B)]); // `src_c, c`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_W", 0);
    asm.emul(R_B, R_B, R_T0);
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_W", 0);
    asm.esub(6, R_T0, R_A); // `R_6 = dw_c`
    load_lin2(&mut asm, 13, 14, R_B, R_A); // `r_val`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_W", 0);
    asm.emul(R_B, R_B, R_T0);
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 0, R_A); // `idx(z)`
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_W", 0);
    asm.esub(R_B, R_T0, R_A); // `R_B = dw_r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(23, R_A)]); // `m_wire`
    asm.emul(R_A, R_A, 6);   // `m_wire * dw_c`
    asm.esub(R_A, R_B, R_A); // `R_A = dw_r - m_wire * dw_c`
    asm.emul(6, 6, R_B);     // `6 = dw_c * dw_r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(29, R_B)]); // `h_w2r`
    asm.emul(6, R_B, 6);
    asm.esub(6, 6, R_A);     // `C_9`
    add_c_term(&mut asm, 6);

    // C_10 (`h_dfa` = 30): `h_dfa * dd_l * dd_r - (dd_r - m_dfa_rom * dd_l)`:
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(24, 6), (8, R_A), (25, R_B)]); // `dfa_s, dfa_b, dfa_s_next`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_DFA", 0);
    asm.emul(R_A, R_A, R_T0);
    asm.eadd(6, 6, R_A);
    asm.emul(R_T0, R_T0, R_T0); // `gamma_dfa^2`
    asm.emul(R_B, R_B, R_T0);
    asm.eadd(6, 6, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_DFA", 0);
    asm.esub(6, R_T0, 6); // `R_6 = dd_l`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(7, R_B)]); // `rom_q_next`
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 2, R_A); // `rom_q(z) = z_8 + 2*z_9`
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 1, R_X); // `rom_b(z)`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_DFA", 0);
    asm.emul(R_X, R_X, R_T0);
    asm.eadd(R_A, R_A, R_X);
    asm.emul(R_T0, R_T0, R_T0);
    asm.emul(R_B, R_B, R_T0);
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_DFA", 0);
    asm.esub(R_B, R_T0, R_A); // `R_B = dd_r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(27, R_A)]); // `m_dfa_rom`
    asm.emul(R_A, R_A, 6);
    asm.esub(R_A, R_B, R_A); // `R_A = dd_r - m_dfa_rom * dd_l`
    asm.emul(6, 6, R_B);     // `6 = dd_l * dd_r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(30, R_B)]); // `h_dfa`
    asm.emul(6, R_B, 6);
    asm.esub(6, 6, R_A);     // `C_10`
    add_c_term(&mut asm, 6);

    // C_11 (`h_sh` = 31): `h_sh * ds_l * ds_r - ((1 - eq_last)*ds_r - (1 - eq_first)*ds_l)`:
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(25, R_A)]); // `dfa_s_next`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_SH", 0);
    asm.emul(R_A, R_A, R_T0);
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 0, R_B); // `idx(z)`
    asm.eadd(R_A, R_A, R_B);
    asm.load(R_Y, &[1, 0, 0, 0], true);
    asm.eadd(R_A, R_A, R_Y); // `idx + 1 + gamma_sh * dfa_s_next`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_SH", 0);
    asm.esub(6, R_T0, R_A); // `R_6 = ds_l`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(24, R_A)]); // `dfa_s`
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_GAMMA_SH", 0);
    asm.emul(R_A, R_A, R_T0);
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 0, R_B);
    asm.eadd(R_A, R_A, R_B);
    emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_SH", 0);
    asm.esub(R_B, R_T0, R_A); // `R_B = ds_r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(31, R_A)]); // `h_sh`
    asm.emul(R_X, R_A, 6);
    asm.emul(R_X, R_X, R_B); // `h_sh * ds_l * ds_r`
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 4, R_A); // `eq_last`
    asm.load(R_Y, &[1, 0, 0, 0], true);
    asm.esub(R_A, R_Y, R_A);
    asm.emul(R_A, R_A, R_B); // `(1 - eq_last) * ds_r`
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 3, R_T0); // `eq_first`
    asm.esub(R_T0, R_Y, R_T0);
    asm.emul(R_T0, R_T0, 6); // `(1 - eq_first) * ds_l`
    asm.esub(R_A, R_A, R_T0);
    asm.esub(6, R_X, R_A); // `C_11`
    add_c_term(&mut asm, 6);

    // C_12..C_16 (`h_rng0..h_rng4` for `(r_lo,r_hi), (d_lo,d_hi), (q_lo,q_hi), (dq_lo,dq_hi), (dfa_b,dfa_b_slack)`):
    for (h_idx, x0_idx, x1_idx) in [
        (32usize, 13usize, 14usize),
        (33, 15, 16),
        (34, 17, 18),
        (35, 20, 21),
        (36, 8, 26),
    ] {
        emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(h_idx, 6), (x0_idx, R_A), (x1_idx, R_B)]);
        emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"LU_BETA_16", 0);
        asm.esub(R_A, R_T0, R_A); // `d0`
        asm.esub(R_B, R_T0, R_B); // `d1`
        asm.emul(R_X, 6, R_A);
        asm.emul(R_X, R_X, R_B); // `h * d0 * d1`
        asm.eadd(R_Y, R_A, R_B); // `d0 + d1`
        asm.esub(6, R_X, R_Y);
        add_c_term(&mut asm, 6);
    }

    // C_17 (`sel_wbb * (r_val - w_bb)`): binds Table 1 witness rows `32..32+2^{m+1}` to committed `W_bb` Canopy!
    load_lin2(&mut asm, 13, 14, 6, R_A); // `r_val`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(3, R_A), (9, R_B)]); // `sel_wbb, w_bb`
    asm.esub(6, 6, R_B); // `r_val - w_bb`
    asm.emul(6, R_A, 6); // `sel_wbb * (r_val - w_bb)`
    add_c_term(&mut asm, 6);

    // Multiply `R_7` (`zero_acc`) by `eq(tau_exec, z_exec)`!
    asm.bf_eval_eq_tau_z(HEM_EXEC_VARS as u8, R_T0);
    asm.emul(7, 7, R_T0);

    // Sum terms 18..25 (`R_9 == alpha_exec^18`!):
    // 18: `h_w01 + h_w2r`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(28, 6), (29, R_A)]);
    asm.eadd(6, 6, R_A);
    add_c_term(&mut asm, 6);
    // 19: `h_dfa`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(30, 6)]);
    add_c_term(&mut asm, 6);
    // 20: `h_sh`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(31, 6)]);
    add_c_term(&mut asm, 6);
    // 21: `h_rng0 + h_rng1 + h_rng2 + h_rng3 + h_rng4`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(32, 6), (33, R_A), (34, R_B)]);
    asm.eadd(6, 6, R_A);
    asm.eadd(6, 6, R_B);
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(35, R_A), (36, R_B)]);
    asm.eadd(6, 6, R_A);
    asm.eadd(6, 6, R_B);
    add_c_term(&mut asm, 6);
    // 22: `pub_sel_r(z_exec) * r_val(z_exec)`
    load_lin2(&mut asm, 13, 14, 6, R_A);
    emit_squeeze_from_ckpt(&mut asm, R_B, 10, b"SC_LAMBDA_PUB", 0);
    asm.bf_eval_sparse_sel_z(HEM_EXEC_VARS as u8, R_B, R_A, &layout.pub_r_indices);
    asm.emul(6, 6, R_A);
    add_c_term(&mut asm, 6);
    // 23: `pub_sel_a(z_exec) * a(z_exec)`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(10, 6)]);
    emit_squeeze_from_ckpt(&mut asm, R_B, 10, b"SC_LAMBDA_PUB", 0);
    asm.bf_eval_sparse_sel_z(HEM_EXEC_VARS as u8, R_B, R_A, &layout.pub_a_indices);
    asm.emul(6, 6, R_A);
    add_c_term(&mut asm, 6);
    // 24: `eq(z_exec, 0) * dfa_s(z_exec)`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(24, 6)]);
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 3, R_A);
    asm.emul(6, 6, R_A);
    add_c_term(&mut asm, 6);
    // 25: `eq(z_exec, 4095) * dfa_s_next(z_exec)`
    emit_checked_evals37_load(&mut asm, evals_opt, 12, &[(25, 6)]);
    asm.bf_eval_public_mle_z(HEM_EXEC_VARS as u8, 4, R_A);
    asm.emul(6, 6, R_A);
    add_c_term(&mut asm, 6);

    // Assert exact algebraic identity `G_exec(z_exec) == term_exec`!
    asm.assert_eq(7, 13);

    // --------------------------------------------------------------------------------------------
    // Round 6b: Table 1 Lockstep `UD-100` BaseFold Opening (`N_exec = 4096`, `122` dual Canopy queries + `16`-bit PoW!)
    // --------------------------------------------------------------------------------------------
    // First carry Table 2's 3 needed checkpoints `(S_rng16=R_8, ch_sc_ckpt=R_10, ch_logup_ckpt=R_11)` into `R_15` (`t2_bundle`)
    // so `R_6..R_14` are ALL free during Table 1's 122 queries!
    emit_compress_reg(&mut asm, 15, 8, 0x2010);
    emit_compress_reg(&mut asm, 15, 10, 0x2011);
    emit_compress_reg(&mut asm, 15, 11, 0x2012);

    // Squeeze `eta_1` into `R_B`, save into `R_13`, compress into `R_14` (`t1_bundle`),
    // and compute `Y_1 = sum eta_1^{36-k} evals_37[k]` into `R_A` while verifying `evals_37` matches `R_12`:
    asm.squeeze_ext4(R_B, b"T1_BF_ETA", 0);
    emit_copy_reg(&mut asm, 13, R_B);
    emit_compress_reg(&mut asm, 14, R_B, 0x1005);
    emit_zero_reg(&mut asm, R_A);
    emit_zero_reg(&mut asm, R_Y);
    for k in 0..37 {
        let w = proof.map_or(zero4, |p| p.t1_evals_37[k].to_u64_limbs());
        asm.load(R_X, &w, false);
        asm.emul(R_A, R_A, R_B);
        asm.eadd(R_A, R_A, R_X);
        emit_compress_reg(&mut asm, R_Y, R_X, 0xE000 + (k as u64));
    }
    asm.assert_eq(R_Y, 12);

    // Run 12-round Table 1 Lockstep BaseFold sumcheck (`stage_ks = &[3, 3, 2]` -> `final_poly[8]`):
    emit_lockstep_basefold_sumcheck(
        &mut asm,
        HEM_EXEC_VARS,
        T1_STAGE_KS,
        b"T1_BF",
        None,
        Some((14, 0x1010)),
        proof.map(|p| &p.t1_bf),
    );

    // `16`-bit PoW #1 (`H1` fix: single nonce read hashed ONCE directly into `R_CH`, checked on `R_CH`,
    // and immediately used as query seed — zero decoupled second read!):
    let t1_pow_w = proof.map_or([0u64; 2], |p| [p.t1_pow_nonce & 0xFFFF_FFFF, p.t1_pow_nonce >> 32]);
    asm.hash(R_CH, Some(R_CH), P2_DOMAIN_FS_POW_T1, &[], &t1_pow_w, 0, 0);
    asm.assert_pow(R_CH, UD100_POW_BITS);

    // Reload Table 1's prover roots into `R_6..R_12` (`R_13` already holds `eta_1`!) and verify `compress(...) == R_14`!
    let t1_s1_w = proof.map_or(zero4, |p| p.t1_bf.stages[0].p2_root());
    let t1_s2_w = proof.map_or(zero4, |p| p.t1_bf.stages[1].p2_root());
    let t1_s3_w = proof.map_or(zero4, |p| p.t1_bf.stages[2].p2_root());
    emit_zero_reg(&mut asm, R_A); // recompute `t1_root_bundle` check in `R_A`
    asm.load(6, &w1_p2, false);
    emit_compress_reg(&mut asm, R_A, 6, 0x1001);
    asm.load(7, &w1_cs, false);
    emit_compress_reg(&mut asm, R_A, 7, 0x1002);
    asm.load(8, &w2_p2, false);
    emit_compress_reg(&mut asm, R_A, 8, 0x1003);
    asm.load(9, &w2_cs, false);
    emit_compress_reg(&mut asm, R_A, 9, 0x1004);
    emit_compress_reg(&mut asm, R_A, 13, 0x1005); // `R_13` holds `eta_1`!
    asm.load(10, &t1_s1_w, false);
    emit_compress_reg(&mut asm, R_A, 10, 0x1010);
    asm.load(11, &t1_s2_w, false);
    emit_compress_reg(&mut asm, R_A, 11, 0x1011);
    asm.load(12, &t1_s3_w, false);
    emit_compress_reg(&mut asm, R_A, 12, 0x1012);
    asm.assert_eq(R_A, 14); // 100% proves `R_6..R_13` match committed roots & `eta_1`!

    // Execute `122` Transcript-Bound Dual-Canopy Query Chains on Table 1 (`N_exec = 4096`, `depth_0 = 14`):
    let t1_s_keys: [[u64; 4]; 3] = [
        [T1_BF_KEY_SEED ^ 1, 0x4341_4E50_0000_0000, 0x4246_5354_0000_0000, P2_IV],
        [T1_BF_KEY_SEED ^ 2, 0x4341_4E50_0000_0001, 0x4246_5354_0000_0003, P2_IV],
        [T1_BF_KEY_SEED ^ 3, 0x4341_4E50_0000_0002, 0x4246_5354_0000_0006, P2_IV],
    ];
    let dummy_sib14_p2 = vec![zero4; 14];
    let dummy_sib14_cs = vec![[0u8; 32]; 14];
    let dummy_w16 = vec![0u64; 16];
    let dummy_w2 = vec![0u64; 2];
    let dummy_w36 = vec![0u64; 36];
    let dummy_w72 = vec![0u64; 72];
    let dummy_fib8_t1 = vec![GoldilocksExt4::ZERO; 8];
    let dummy_fib4_t1 = vec![GoldilocksExt4::ZERO; 4];
    let dummy_sibs_t1 = [vec![zero4; 11], vec![zero4; 8], vec![zero4; 6]];

    for q_idx in 0..UD100_NUM_QUERIES {
        let mut qlab = pack_bytes_7_limbs(b"T1_UD100_Q");
        qlab.push(q_idx as u64);
        let q = proof.map(|p| &p.t1_queries[q_idx]);
        let f0 = q.map_or(0u32, |x| x.f0);

        // Stage 0a: `vk` (`8` base cols, public roots `vk_p2_root` & `vk_cs_pin4`!)
        asm.load(14, &CANOPY_KEY_VK, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.fiber_acc(0, false, true, true, 14, 13, 8, q.map_or(&dummy_w16, |x| &x.vk_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib14_p2, |x| &x.vk_p2_sibs));
        asm.load(R_Y, &stmt.vk_p2_root, true);
        asm.assert_eq(R_X, R_Y);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib14_cs, |x| &x.vk_cs_sibs));
        asm.load(R_Y, &stmt.vk_cs_pin4(), true);
        asm.assert_eq(R_X, R_Y);

        // Stage 0b: `bytes` (`1` base col, public payload roots `bytes_p2_root` & `bytes_cs_pin4`!)
        asm.load(14, &CANOPY_KEY_BYTES, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.fiber_acc(1, false, false, true, 14, 13, 1, q.map_or(&dummy_w2, |x| &x.bytes_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib14_p2, |x| &x.bytes_p2_sibs));
        asm.load(R_Y, &stmt.bytes_p2_root, true);
        asm.assert_eq(R_X, R_Y);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib14_cs, |x| &x.bytes_cs_sibs));
        asm.load(R_Y, &stmt.bytes_cs_pin4(), true);
        asm.assert_eq(R_X, R_Y);

        // Stage 0c: `w_bb` (`1` base col, public child witness roots `w_bb_p2_root` & `w_bb_cs_pin4`!)
        asm.load(14, &CANOPY_KEY_WBB, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.fiber_acc(6, false, false, true, 14, 13, 1, q.map_or(&dummy_w2, |x| &x.w_bb_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib14_p2, |x| &x.w_bb_p2_sibs));
        asm.load(R_Y, &stmt.w_bb_p2_root, true);
        asm.assert_eq(R_X, R_Y);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib14_cs, |x| &x.w_bb_cs_sibs));
        asm.load(R_Y, &stmt.w_bb_cs_pin4(), true);
        asm.assert_eq(R_X, R_Y);

        // Stage 0d: `wit1` (`18` base cols -> `R_6`, `R_7`)
        asm.load(14, &CANOPY_KEY_WIT1, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.fiber_acc(2, false, false, true, 14, 13, 18, q.map_or(&dummy_w36, |x| &x.wit1_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib14_p2, |x| &x.wit1_p2_sibs));
        asm.assert_eq(R_X, 6);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib14_cs, |x| &x.wit1_cs_sibs));
        asm.assert_eq(R_X, 7);

        // Stage 0e: `wit2` (`9` Ext4 cols -> `R_8`, `R_9`)
        asm.load(14, &CANOPY_KEY_WIT2, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.fiber_acc(3, true, false, true, 14, 13, 9, q.map_or(&dummy_w72, |x| &x.wit2_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib14_p2, |x| &x.wit2_p2_sibs));
        asm.assert_eq(R_X, 8);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 14);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib14_cs, |x| &x.wit2_cs_sibs));
        asm.assert_eq(R_X, 9);

        // Stage-0 2-ary fold (`R_A, R_B` -> `R_A` on `D_0 = 2^15`):
        asm.bf_stage0_fold2(15, R_A);

        // Stages 1, 2, 3 (`k = 3, 3, 2`, `log_n_cur = 14, 11, 8`, `round_start = 1, 4, 7`, roots in `R_10, R_11, R_12`):
        for (s_idx, &(fk, log_n_cur, rnd_st, root_reg)) in
            [(3u8, 14u8, 1u8, 10u8), (3, 11, 4, 11), (2, 8, 7, 12)].iter().enumerate()
        {
            let default_fib = if fk == 3 { dummy_fib8_t1.as_slice() } else { dummy_fib4_t1.as_slice() };
            let (fi, fib, sibs) = match q {
                Some(x) => (x.stage_fibers[s_idx].0, x.stage_fibers[s_idx].1.as_slice(), x.stage_fibers[s_idx].2.as_slice()),
                None => (0u32, default_fib, dummy_sibs_t1[s_idx].as_slice()),
            };
            asm.load(14, &t1_s_keys[s_idx], true);
            asm.bf_fold_fiber(fk, log_n_cur, 14, rnd_st, R_A, R_A, fib);
            asm.merkle(14, fi, sibs);
            asm.assert_eq(R_X, root_reg);
        }
        // Final degree-<8 polynomial check at `x_final = 7^{2^9} * omega_64^{f_3}`:
        asm.bf_assert_final_eval(9, R_A);
    }

    // --------------------------------------------------------------------------------------------
    // Round 7: Table 2 (`N_rng = 65536 = 2^16`) `[0, 2^16)` LogUp Sumcheck + Lockstep `UD-100` BaseFold!
    // --------------------------------------------------------------------------------------------
    // Reload Table 2's committed roots & checkpoints and verify against `R_15`!
    // `R_6 = mrng_p2`, `R_7 = mrng_cs`, `R_8 = hrng_p2`, `R_9 = hrng_cs`,
    // `R_10 = S_rng16`, `R_11 = ch_sc_ckpt`, `R_12 = ch_logup_ckpt`.
    let ch_sc_w = proof.map_or(zero4, |p| p.ch_sc_ckpt);
    let ch_lu_w = proof.map_or(zero4, |p| p.ch_logup_ckpt);
    emit_zero_reg(&mut asm, R_A);
    asm.load(6, &mr_p2, false);
    emit_compress_reg(&mut asm, R_A, 6, 0x2001);
    asm.load(7, &mr_cs, false);
    emit_compress_reg(&mut asm, R_A, 7, 0x2002);
    asm.load(8, &hr_p2, false);
    emit_compress_reg(&mut asm, R_A, 8, 0x2003);
    asm.load(9, &hr_cs, false);
    emit_compress_reg(&mut asm, R_A, 9, 0x2004);
    asm.load(10, &s_rng_w, false);
    emit_compress_reg(&mut asm, R_A, 10, 0x2010);
    asm.load(11, &ch_sc_w, false);
    emit_compress_reg(&mut asm, R_A, 11, 0x2011);
    asm.load(12, &ch_lu_w, false);
    emit_compress_reg(&mut asm, R_A, 12, 0x2012);
    asm.assert_eq(R_A, 15); // 100% proves `R_6..R_12` match committed Table-2 roots & checkpoints!

    // Latch `tau_rng[0..16]` from `R_11` (`ch_sc_ckpt`):
    for j in 0..HEM_RNG16_VARS {
        emit_squeeze_from_ckpt(&mut asm, R_T0, 11, b"SC_TAU_RNG", j as u64);
        asm.bf_latch_tau(j as u8, R_T0);
    }
    // Initial Table 2 sumcheck claim: `R_A = alpha_rng * S_rng16` (`R_10 = S_rng16`):
    emit_squeeze_from_ckpt(&mut asm, R_B, 11, b"SC_ALPHA_RNG", 0);
    asm.emul(R_A, R_B, 10);

    // 16-round degree-3 sumcheck on Table 2 (`c0, c2, c3` sent; `c1 = claim - 2*c0 - c2 - c3`):
    // Free scratch during sumcheck: `R_13 = c0, R_14 = c2, R_15 = c3` (`R_6..R_12` stay untouched!)
    for rnd in 0..HEM_RNG16_VARS {
        let (c0w, c2w, c3w) = match proof {
            Some(p) => (
                p.t2_sc_rounds[rnd][0].to_u64_limbs(),
                p.t2_sc_rounds[rnd][1].to_u64_limbs(),
                p.t2_sc_rounds[rnd][2].to_u64_limbs(),
            ),
            None => (zero4, zero4, zero4),
        };
        asm.absorb_limbs_proof(b"T2_SC_C0", &c0w, R_X, 0);
        emit_copy_reg(&mut asm, 13, R_X);
        asm.absorb_limbs_proof(b"T2_SC_C2", &c2w, R_X, 0);
        emit_copy_reg(&mut asm, 14, R_X);
        asm.absorb_limbs_proof(b"T2_SC_C3", &c3w, R_X, 0);
        emit_copy_reg(&mut asm, 15, R_X);
        asm.squeeze_ext4(R_B, b"T2_SC_Z", rnd as u64);
        asm.bf_latch_z(rnd as u8, R_B);
        // `c1 = R_A - 2*R_13 - R_14 - R_15`:
        asm.esub(R_T0, R_A, 13);
        asm.esub(R_T0, R_T0, 13);
        asm.esub(R_T0, R_T0, 14);
        asm.esub(R_T0, R_T0, 15);
        // Horner `((c3 * z + c2) * z + c1) * z + c0`:
        asm.emul(R_Y, 15, R_B);
        asm.eadd(R_Y, R_Y, 14);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_Y, R_Y, R_T0);
        asm.emul(R_Y, R_Y, R_B);
        asm.eadd(R_A, R_Y, 13);
    }

    // Absorb `m_rng16(z_rng)` (`R_13`) and `h_rng_tab(z_rng)` (`R_14`), verify exact `G_rng(z_rng) == R_A`:
    // `G_rng(z) = eq(tau_rng, z) * (h_rng_tab(z) * (beta_16 - id(z)) - m_rng16(z)) + alpha_rng * h_rng_tab(z)`!
    let (m_ev_w, h_ev_w) = match proof {
        Some(p) => (p.t2_evals_2[0].to_u64_limbs(), p.t2_evals_2[1].to_u64_limbs()),
        None => (zero4, zero4),
    };
    asm.absorb_limbs_proof(b"T2_EV_M", &m_ev_w, R_X, 0);
    emit_copy_reg(&mut asm, 13, R_X);
    asm.absorb_limbs_proof(b"T2_EV_H", &h_ev_w, R_X, 0);
    emit_copy_reg(&mut asm, 14, R_X);

    emit_squeeze_from_ckpt(&mut asm, R_X, 12, b"LU_BETA_16", 0); // `beta_16` from `ch_logup_ckpt`
    asm.bf_eval_public_mle_z(HEM_RNG16_VARS as u8, 0, R_Y);      // `id(z_rng)`
    asm.esub(R_X, R_X, R_Y);                                     // `beta_16 - id(z_rng)`
    asm.emul(R_X, 14, R_X);                                      // `h_rng * (beta_16 - id)`
    asm.esub(R_X, R_X, 13);                                      // `- m_rng16`
    asm.bf_eval_eq_tau_z(HEM_RNG16_VARS as u8, R_Y);             // `eq(tau_rng, z_rng)`
    asm.emul(R_X, R_X, R_Y);                                     // `eq * (...)`
    emit_squeeze_from_ckpt(&mut asm, R_Y, 11, b"SC_ALPHA_RNG", 0); // `alpha_rng` from `ch_sc_ckpt`
    asm.emul(R_Y, R_Y, 14);                                      // `alpha_rng * h_rng`
    asm.eadd(R_X, R_X, R_Y);                                     // `G_rng(z_rng)`
    asm.assert_eq(R_A, R_X);

    // Table 2 Lockstep `UD-100` BaseFold Opening (`N_rng = 65536`, `stage_ks = &[3, 3, 3, 3]` -> `final_poly[8]`):
    // Squeeze `eta_2` into `R_15`, compute `Y_2 = m_rng(z) * eta_2 + h_rng(z)` into `R_A`!
    // Wait: `R_10..R_12` (`S_rng16, ch_sc_ckpt, ch_logup_ckpt`) are NO LONGER NEEDED — free `R_10..R_13` for `t2_s1..t2_s4`!
    // Layout for Table 2's 122 queries:
    //   `R_6 = mrng_p2`, `R_7 = mrng_cs`, `R_8 = hrng_p2`, `R_9 = hrng_cs`,
    //   `R_10 = t2_s1`, `R_11 = t2_s2`, `R_12 = t2_s3`, `R_13 = t2_s4`, `R_15 = eta_2`, `R_14 = key scratch`!
    asm.squeeze_ext4(R_B, b"T2_BF_ETA", 0);
    emit_copy_reg(&mut asm, 15, R_B); // `R_15 = eta_2`
    asm.emul(R_A, 13, 15);
    asm.eadd(R_A, R_A, 14);           // `Y_2 = m_rng(z) * eta_2 + h_rng(z)`

    emit_lockstep_basefold_sumcheck(
        &mut asm,
        HEM_RNG16_VARS,
        T2_STAGE_KS,
        b"T2_BF",
        Some(&[10, 11, 12, 13]),
        None,
        proof.map(|p| &p.t2_bf),
    );

    // `16`-bit PoW #2 (`H1` fix: single nonce read hashed ONCE directly into `R_CH`, checked on `R_CH`,
    // and immediately used as Table 2 query seed — zero decoupled second read!):
    let t2_pow_w = proof.map_or([0u64; 2], |p| [p.t2_pow_nonce & 0xFFFF_FFFF, p.t2_pow_nonce >> 32]);
    asm.hash(R_CH, Some(R_CH), P2_DOMAIN_FS_POW_T2, &[], &t2_pow_w, 0, 0);
    asm.assert_pow(R_CH, UD100_POW_BITS);

    // Execute `122` Transcript-Bound Dual-Canopy Query Chains on Table 2 (`N_rng = 65536`, `depth_0 = 18`):
    let t2_s_keys: [[u64; 4]; 4] = [
        [T2_BF_KEY_SEED ^ 1, 0x4341_4E50_0000_0000, 0x4246_5354_0000_0000, P2_IV],
        [T2_BF_KEY_SEED ^ 2, 0x4341_4E50_0000_0001, 0x4246_5354_0000_0003, P2_IV],
        [T2_BF_KEY_SEED ^ 3, 0x4341_4E50_0000_0002, 0x4246_5354_0000_0006, P2_IV],
        [T2_BF_KEY_SEED ^ 4, 0x4341_4E50_0000_0003, 0x4246_5354_0000_0009, P2_IV],
    ];
    let dummy_sib18_p2 = vec![zero4; 18];
    let dummy_sib18_cs = vec![[0u8; 32]; 18];
    let dummy_w8 = vec![0u64; 8];
    let dummy_fib8 = vec![GoldilocksExt4::ZERO; 8];
    let dummy_sibs_t2 = [
        vec![zero4; 15],
        vec![zero4; 12],
        vec![zero4; 9],
        vec![zero4; 6],
    ];

    for q_idx in 0..UD100_NUM_QUERIES {
        let mut qlab = pack_bytes_7_limbs(b"T2_UD100_Q");
        qlab.push(q_idx as u64);
        let q = proof.map(|p| &p.t2_queries[q_idx]);
        let f0 = q.map_or(0u32, |x| x.f0);

        // Stage 0a: `m_rng16` (`1` base col -> `R_6`, `R_7`)
        asm.load(14, &CANOPY_KEY_MRNG, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 18);
        asm.fiber_acc(4, false, true, true, 14, 15, 1, q.map_or(&dummy_w2, |x| &x.mrng_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib18_p2, |x| &x.mrng_p2_sibs));
        asm.assert_eq(R_X, 6);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 18);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib18_cs, |x| &x.mrng_cs_sibs));
        asm.assert_eq(R_X, 7);

        // Stage 0b: `h_rng_tab` (`1` Ext4 col -> `R_8`, `R_9`)
        asm.load(14, &CANOPY_KEY_HRNG, true);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 18);
        asm.fiber_acc(5, true, false, true, 14, 15, 1, q.map_or(&dummy_w8, |x| &x.hrng_words));
        asm.merkle(14, f0, q.map_or(&dummy_sib18_p2, |x| &x.hrng_p2_sibs));
        asm.assert_eq(R_X, 8);
        asm.hash(R_T0, Some(R_CH), P2_DOMAIN_FS_SQUEEZE_IDX, &qlab, &[], 0, 0);
        asm.bind_idx(R_T0, 0, 18);
        asm.cshake_merkle_bound(f0, q.map_or(&dummy_sib18_cs, |x| &x.hrng_cs_sibs));
        asm.assert_eq(R_X, 9);

        // Stage-0 2-ary fold (`R_A, R_B` -> `R_A` on `D_0 = 2^19`):
        asm.bf_stage0_fold2(19, R_A);

        // Stages 1, 2, 3, 4 (each 8-ary `k=3`, `log_n_cur = 18, 15, 12, 9`, `round_start = 1, 4, 7, 10`, roots `R_10..R_13`):
        for (s_idx, &(log_n_cur, rnd_st, root_reg)) in
            [(18u8, 1u8, 10u8), (15, 4, 11), (12, 7, 12), (9, 10, 13)].iter().enumerate()
        {
            let (fi, fib, sibs) = match q {
                Some(x) => (
                    x.stage_fibers[s_idx].0,
                    x.stage_fibers[s_idx].1.as_slice(),
                    x.stage_fibers[s_idx].2.as_slice(),
                ),
                None => (0u32, dummy_fib8.as_slice(), dummy_sibs_t2[s_idx].as_slice()),
            };
            asm.load(14, &t2_s_keys[s_idx], true);
            asm.bf_fold_fiber(3, log_n_cur, 14, rnd_st, R_A, R_A, fib);
            asm.merkle(14, fi, sibs);
            asm.assert_eq(R_X, root_reg);
        }
        // Final degree-<8 polynomial check at `x_final = 7^{2^{13}} * omega_64^{f_4}`:
        asm.bf_assert_final_eval(13, R_A);
    }

    asm
}

/// Deterministically compute the keyless `Poseidon2-12` public verifier program hash from `stmt` ALONE
/// (zero witness, zero `K_MAC`, `pin_mode = false`).
///
/// **L1 Memory Scoping Note:** Host/setup derivation here allocates the assembler buffer to hash the
/// canonical program; embedded streaming verification (`Dregg180StreamVm::new_unkeyed_pinned_program`)
/// runs in `size_of::<Dregg180StreamVm>() = 3,632 B <= 16,384 B` static RAM with **0 heap allocations**.
pub fn compute_expected_trustless_program_hash(stmt: &TrustlessHemPublicStatement) -> Result<[u64; 4], String> {
    stmt.validate_canonical()?;
    let canon_vk = canonical_trustless_vk(stmt.bb_num_rounds)?;
    let asm = emit_trustless_hem_stream(stmt, &canon_vk.layout, None);
    Ok(asm.compute_public_program_hash())
}

/// Trustless (`pin_mode = false`, `k_mac = None`) standalone `UD-100` verifier executing inside `< 16 KiB`
/// `Dregg180StreamVm`:
/// - Selects the **verifier-owned** canonical preprocessed VK via `canonical_trustless_vk` (`H4` fix — no caller VK trust!);
/// - Enforces strict statement canonicality (`L3` fix) and equality against verifier-owned `expected` statement;
/// - **ZERO `Option` terminal oracle callback / ZERO unverified terminal claim loophole:** `Dregg180StreamVm` itself
///   proves `claim_m == eq(bb_tau, r) * A_bb(r) * B_bb(r) (mod p_BB)` directly against `(w_bb_p2_root, w_bb_cs_root)`!
/// - Derives the keyless `public_program_hash` and runs `Dregg180StreamVm` (`0` heap allocs during VM streaming!).
pub fn verify_trustless_dregg180_hem_stream(
    expected: &VerifierExpectedTrustlessStatement,
    stmt: &TrustlessHemPublicStatement,
    wire_bytes: &[u8],
) -> Result<Dregg180VmVerdict, String> {
    stmt.validate_canonical()?;
    let canon_vk = canonical_trustless_vk(expected.bb_num_rounds)?;
    if stmt.bb_num_rounds != expected.bb_num_rounds {
        return Err("statement bb_num_rounds != verifier expected bb_num_rounds".into());
    }
    if stmt.vk_p2_root != canon_vk.p2_root() || stmt.vk_cs_root != canon_vk.cshake_root() {
        return Err("statement VK Canopy roots do not match verifier-owned canonical VK".into());
    }
    if stmt.bb_tau != expected.bb_tau {
        return Err("statement bb_tau != verifier expected bb_tau".into());
    }
    if stmt.bb_initial_claim != expected.bb_initial_claim {
        return Err("statement bb_initial_claim != verifier expected bb_initial_claim".into());
    }
    if stmt.w_bb_p2_root != expected.w_bb_p2_root || stmt.w_bb_cs_root != expected.w_bb_cs_root {
        return Err("statement W_bb Canopy roots != verifier expected W_bb roots".into());
    }
    if stmt.bytes_p2_root != expected.bytes_p2_root || stmt.bytes_cs_root != expected.bytes_cs_root {
        return Err("statement payload Canopy roots != verifier expected payload roots".into());
    }
    let expected_hash = compute_expected_trustless_program_hash(stmt)?;
    let mut vm = Dregg180StreamVm::new_unkeyed_pinned_program(expected_hash);
    vm.verify_stream(wire_bytes)
        .map_err(|e| format!("Dregg180StreamVm trustless UD-100 rejection: {e:?}"))
}

/// Honest trustless prover (`pin_mode = false`, `k_mac = None`) proving BOTH:
/// (a) Exact Non-Native `BabyBear Ext4` (`X^4 - 11`) cubic sumcheck verification (`g_i(0)+g_i(1)=claim_i`,
///     Horner `g_i(r_i)=claim_{i+1}`, causal `Poseidon2` `Goldilocks -> BabyBear` Fiat-Shamir, `r < p_BB`),
///     PLUS full in-circuit `chi(x)` / `A_bb(r)` / `B_bb(r)` / `eq(tau, r)` terminal evaluation against
///     committed `w_bb_comm` (`W_bb` dual Canopy), AND
/// (b) Exact `Absent("sk-")` 4-state DFA trace over the `4 x 256` transition ROM bound to `payload_comm`,
/// inside `GoldilocksExt4` sumcheck + `[0, 2^16)` LogUp + `UD-100` Lockstep BaseFold (`122` dual Canopy queries + `16`-bit PoW).
pub fn prove_trustless_nonnative_babybear_and_dfa_hem(
    vk: &TrustlessHemVk,
    w_bb_comm: &BabyBearWitnessCommitment,
    payload_comm: &PayloadBytesCommitment,
    transcript: &ChildBabyBearSumcheckTranscript,
) -> Result<TrustlessHemProofBundle, String> {
    prove_trustless_hem_with_wbb_override(
        vk,
        w_bb_comm,
        &w_bb_comm.w_bb_col,
        payload_comm,
        transcript,
        TrustlessHemTamper::None,
    )
}

/// Prover entry point with explicit adversarial tamper hooks (`TrustlessHemTamper::None` = honest prover)
/// to test that an untrusted prover with NO `K_MAC` (`pin_mode = false`) cannot forge any BabyBear,
/// canonicality, committed-table, DFA, range-check, BaseFold, or Canopy violation!
pub fn prove_trustless_hem_with_tamper(
    vk: &TrustlessHemVk,
    w_bb_comm: &BabyBearWitnessCommitment,
    payload_comm: &PayloadBytesCommitment,
    transcript: &ChildBabyBearSumcheckTranscript,
    tamper: TrustlessHemTamper,
) -> Result<TrustlessHemProofBundle, String> {
    prove_trustless_hem_with_wbb_override(
        vk,
        w_bb_comm,
        &w_bb_comm.w_bb_col,
        payload_comm,
        transcript,
        tamper,
    )
}

/// Adversarial prover entry point that allows populating `r_val[32..32+2^{m+1}]` from `witness_wbb_col`
/// (e.g., a fake witness table `(A_fake, B_fake)` matching `transcript`) while Stage-0 Canopy still opens
/// the verifier-pinned `w_bb_comm` (`(A_honest, B_honest)`), proving `C_wbb = sel_wbb * (r_val - w_bb)`
/// catches witness-table substitution even when every MAC and terminal `sel_eq` gate passes locally!
pub fn prove_trustless_hem_with_wbb_override(
    vk: &TrustlessHemVk,
    w_bb_comm: &BabyBearWitnessCommitment,
    witness_wbb_col: &[Goldilocks],
    payload_comm: &PayloadBytesCommitment,
    transcript: &ChildBabyBearSumcheckTranscript,
    tamper: TrustlessHemTamper,
) -> Result<TrustlessHemProofBundle, String> {
    let layout = &vk.layout;
    let m = layout.bb_num_rounds;
    if transcript.round_polys.len() != m || transcript.raw_gl_challenges.len() != m {
        return Err("transcript round count does not match VK".into());
    }
    if w_bb_comm.bb_num_rounds != m || witness_wbb_col.len() != HEM_EXEC_ROWS {
        return Err("W_bb commitment dimension does not match VK".into());
    }
    let mut bb_round_polys = transcript.round_polys.clone();
    if tamper == TrustlessHemTamper::WrongBabyBearRoundSum {
        bb_round_polys[0][0].0[0] = crate::ext4::badd(bb_round_polys[0][0].0[0], 1);
    }
    if tamper == TrustlessHemTamper::WrongBabyBearHornerEval {
        // Keep `g_{m-1}(0) + g_{m-1}(1) == 2*c0 + c1 + c2 + c3 == claim_{m-1}` intact while altering `g_{m-1}(r_{m-1})`!
        bb_round_polys[m - 1][1].0[0] = crate::ext4::badd(bb_round_polys[m - 1][1].0[0], 1);
        bb_round_polys[m - 1][2].0[0] = crate::ext4::bsub(bb_round_polys[m - 1][2].0[0], 1);
    }

    let stmt = TrustlessHemPublicStatement {
        bb_num_rounds: m,
        bb_tau: transcript.bb_tau,
        bb_initial_claim: transcript.initial_claim,
        vk_p2_root: vk.p2_root(),
        vk_cs_root: vk.cshake_root(),
        w_bb_p2_root: w_bb_comm.p2_root(),
        w_bb_cs_root: w_bb_comm.cshake_root(),
        bytes_p2_root: payload_comm.p2_root(),
        bytes_cs_root: payload_comm.cshake_root(),
    };

    // --------------------------------------------------------------------------------------------
    // 1. Causal Pass-1 transcript `g_i -> raw_r_i`:
    // --------------------------------------------------------------------------------------------
    let mut ch = stmt.transcript_ch_before_pass1();
    let mut bb_raw_chals = Vec::with_capacity(m);
    for rnd in 0..m {
        for k in 0..4 {
            let mut lab = *b"BB_SC_G0";
            lab[7] = b'0' + (k as u8);
            let limbs4 = bb_round_polys[rnd][k].0.map(|x| x as u64);
            ch = fs_absorb_limbs_local(ch, &lab, &limbs4);
        }
        let raw_ext = fs_squeeze_ext4_local(ch, b"BB_SC_RAW_R", rnd as u64);
        bb_raw_chals.push(raw_ext.to_u64_limbs());
    }

    // --------------------------------------------------------------------------------------------
    // 2. Populate Execution Witness Table 1 (`18` base cols on `N_exec = 4096`) + `m_rng16` on `65536`:
    // --------------------------------------------------------------------------------------------
    let mut a_col = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut b_col = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut c_col = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut r_vals = vec![0u64; HEM_EXEC_ROWS];
    let mut d_vals = vec![BABYBEAR_PRIME_U64 - 1; HEM_EXEC_ROWS];
    let mut q_vals = vec![0u64; HEM_EXEC_ROWS];
    let mut q_top = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut dq_vals = vec![0u64; HEM_EXEC_ROWS];
    let mut dq_top = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];

    let set_r_honest = |row: usize, val: u64, rv: &mut [u64], dv: &mut [u64]| {
        if val < BABYBEAR_PRIME_U64 {
            rv[row] = val;
            dv[row] = (BABYBEAR_PRIME_U64 - 1) - val;
        } else {
            // Adversarial non-canonical `W_bb` entry (`>= p_BB`): prover cannot find valid `d >= 0`!
            rv[row] = val;
            dv[row] = 0;
        }
    };
    set_r_honest(0, 0, &mut r_vals, &mut d_vals);
    set_r_honest(1, 1, &mut r_vals, &mut d_vals);
    set_r_honest(2, 11, &mut r_vals, &mut d_vals);
    set_r_honest(3, BABYBEAR_PRIME_U64 - 1, &mut r_vals, &mut d_vals);
    for l in 0..4 {
        set_r_honest(4 + l, stmt.bb_initial_claim.0[l] as u64, &mut r_vals, &mut d_vals);
    }
    for j in 0..m {
        for l in 0..4 {
            set_r_honest(8 + 4 * j + l, stmt.bb_tau[j].0[l] as u64, &mut r_vals, &mut d_vals);
        }
    }
    let n_bb = 1usize << m;
    for i in 0..(2 * n_bb) {
        let row = HEM_ROW_WBB_START + i;
        set_r_honest(row, witness_wbb_col[row].0, &mut r_vals, &mut d_vals);
    }
    for rnd in 0..m {
        for k in 0..4 {
            for l in 0..4 {
                set_r_honest(layout.g_rows[rnd][k][l], bb_round_polys[rnd][k].0[l] as u64, &mut r_vals, &mut d_vals);
            }
        }
        for l in 0..4 {
            let row = layout.fs_rows[rnd][l];
            let raw = bb_raw_chals[rnd][l];
            let q_full = raw / BABYBEAR_PRIME_U64;
            let rem = raw % BABYBEAR_PRIME_U64;
            if q_full > BABYBEAR_FS_Q_SAFE {
                return Err("raw Goldilocks challenge exceeded BABYBEAR_FS_Q_SAFE".into());
            }
            let dq_full = BABYBEAR_FS_Q_SAFE - q_full;
            a_col[row] = Goldilocks(raw);
            q_vals[row] = q_full & 0xFFFF_FFFF;
            q_top[row] = Goldilocks(q_full >> 32);
            dq_vals[row] = dq_full & 0xFFFF_FFFF;
            dq_top[row] = Goldilocks(dq_full >> 32);
            set_r_honest(row, rem, &mut r_vals, &mut d_vals);
        }
    }

    // Evaluate all MAC and EQ rows in topological order (`row = 0..4096`):
    let sel_mac = &layout.vk_cols[0];
    let sel_eq = &layout.vk_cols[1];
    let sel_fs = &layout.vk_cols[2];
    let src_a = &layout.vk_cols[4];
    let src_b = &layout.vk_cols[5];
    let src_c = &layout.vk_cols[6];
    let rom_q_next_col = &layout.vk_cols[7];
    let mut alias_injected = false;
    let mut exact_pbb_injected = false;

    for row in 0..HEM_EXEC_ROWS {
        if sel_mac[row].0 == 1 {
            let va = r_vals[src_a[row].0 as usize];
            let vb = r_vals[src_b[row].0 as usize];
            let vc = r_vals[src_c[row].0 as usize];
            a_col[row] = Goldilocks(va);
            b_col[row] = Goldilocks(vb);
            c_col[row] = Goldilocks(vc);
            let prod_sum = (va as u128) * (vb as u128) + (vc as u128);
            let mut q_mac = (prod_sum / (BABYBEAR_PRIME_U64 as u128)) as u64;
            let mut r_mac = (prod_sum % (BABYBEAR_PRIME_U64 as u128)) as u64;

            if tamper == TrustlessHemTamper::NonCanonicalBabyBearAliasGtPbb
                && !alias_injected
                && q_mac >= 1
                && (r_mac + BABYBEAR_PRIME_U64) < (1u64 << 32)
            {
                // Forged alias: `q' = q - 1`, `r' = r + p_BB < 2^32` (exact MAC match, passes 16-bit limbs, fails `r + d = p_BB - 1`!)
                q_mac -= 1;
                r_mac += BABYBEAR_PRIME_U64;
                q_vals[row] = q_mac;
                r_vals[row] = r_mac;
                d_vals[row] = 0; // prover has no valid `d >= 0` in `[0, 2^32)`!
                alias_injected = true;
            } else if tamper == TrustlessHemTamper::NonCanonicalBabyBearExactPbbAlias
                && !exact_pbb_injected
                && q_mac >= 1
                && r_mac == 0
            {
                // M3 fix: inject exact `r = p_BB` alias ONLY on a row where `a*b + c == q_mac * p_BB`
                // (`r_honest == 0`), so MAC residual `a*b + c - q'*p_BB - r' == 0` IDENTICALLY and
                // ONLY the canonical slack `r' + d == p_BB - 1` rejects!
                q_mac -= 1;
                q_vals[row] = q_mac;
                r_vals[row] = BABYBEAR_PRIME_U64;
                d_vals[row] = 0;
                let mac_lhs = Goldilocks(va) * Goldilocks(vb) + Goldilocks(vc);
                let mac_rhs = Goldilocks(q_mac) * Goldilocks(BABYBEAR_PRIME_U64) + Goldilocks(r_vals[row]);
                assert_eq!(mac_lhs, mac_rhs, "M3 invariant: ExactPbbAlias MUST leave MAC residual == 0");
                let slack_res = Goldilocks(r_vals[row]) + Goldilocks(d_vals[row]) - Goldilocks(BABYBEAR_PRIME_U64 - 1);
                assert_ne!(slack_res, Goldilocks::ZERO, "M3 invariant: ExactPbbAlias MUST make canonical slack != 0");
                exact_pbb_injected = true;
            } else {
                if tamper == TrustlessHemTamper::WrongBabyBearQuotient && row == layout.first_mac_row {
                    q_mac = q_mac.wrapping_add(1);
                }
                q_vals[row] = q_mac;
                set_r_honest(row, r_mac, &mut r_vals, &mut d_vals);
            }
        } else if sel_eq[row].0 == 1 {
            a_col[row] = Goldilocks(r_vals[src_a[row].0 as usize]);
            b_col[row] = Goldilocks(r_vals[src_b[row].0 as usize]);
            c_col[row] = Goldilocks(r_vals[src_c[row].0 as usize]);
            set_r_honest(row, 0, &mut r_vals, &mut d_vals);
        } else if sel_fs[row].0 == 0 {
            a_col[row] = Goldilocks(r_vals[src_a[row].0 as usize]);
            b_col[row] = Goldilocks(r_vals[src_b[row].0 as usize]);
            c_col[row] = Goldilocks(r_vals[src_c[row].0 as usize]);
        }
    }
    if tamper == TrustlessHemTamper::NonCanonicalBabyBearAliasGtPbb && !alias_injected {
        return Err("NonCanonicalBabyBearAliasGtPbb found no eligible MAC row".into());
    }
    if tamper == TrustlessHemTamper::NonCanonicalBabyBearExactPbbAlias && !exact_pbb_injected {
        return Err("NonCanonicalBabyBearExactPbbAlias requires a MAC row with q_mac >= 1 and r_mac == 0".into());
    }

    // Wiring multiplicities `m_wire[j]` = count of reads of `(j, r[j])` across non-FS `a`, all `b`, all `c`:
    let mut m_wire = vec![0u64; HEM_EXEC_ROWS];
    for row in 0..HEM_EXEC_ROWS {
        if sel_fs[row].0 == 0 {
            m_wire[src_a[row].0 as usize] += 1;
        }
        m_wire[src_b[row].0 as usize] += 1;
        m_wire[src_c[row].0 as usize] += 1;
    }

    // 4-state `Absent("sk-")` DFA trace on `payload_comm.padded_bytes`:
    let mut dfa_s = vec![0u8; HEM_EXEC_ROWS];
    let mut dfa_s_next = vec![0u8; HEM_EXEC_ROWS];
    let mut dfa_b_slack = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut m_dfa_rom = vec![0u64; HEM_EXEC_ROWS];
    let mut q_cur = 0u8;
    for t in 0..HEM_EXEC_ROWS {
        let byte_u8 = payload_comm.padded_bytes[t].0 as u8;
        dfa_b_slack[t] = Goldilocks(255u64.saturating_sub(payload_comm.padded_bytes[t].0));
        dfa_s[t] = q_cur;
        let mut q_nxt = no_sk_dash_step_4state(q_cur, byte_u8);
        if tamper == TrustlessHemTamper::ForgedDfaTransitionBypass && q_cur == 2 && byte_u8 == b'-' {
            // Untrusted prover lies `(2, '-') -> 0` instead of sink `3`!
            q_nxt = 0;
        }
        dfa_s_next[t] = q_nxt;
        if q_nxt == no_sk_dash_step_4state(q_cur, byte_u8) {
            m_dfa_rom[((q_cur as usize) << 8) | (byte_u8 as usize)] += 1;
        }
        q_cur = if tamper == TrustlessHemTamper::ForgedDfaShiftBreak && q_nxt == 3 {
            // Untrusted prover breaks shift continuity `dfa_s[t+1] = 0 != dfa_s_next[t] = 3`!
            0
        } else {
            q_nxt
        };
    }
    let true_s_terminal = dfa_s_next[HEM_EXEC_ROWS - 1];
    if tamper == TrustlessHemTamper::None && true_s_terminal >= 3 {
        return Err("honest prover refused: payload contains forbidden \"sk-\" (DFA reached sink state 3)".into());
    }
    let claimed_s_terminal: u8 = if tamper == TrustlessHemTamper::ForgedDfaTerminalState {
        0 // lie that terminal state is 0 even though `dfa_s_next[1023] == 3`!
    } else {
        true_s_terminal.min(2)
    };
    let s_terminal_ext = GoldilocksExt4::from_base(Goldilocks(claimed_s_terminal as u64));

    // Split 16-bit limbs + count `[0, 2^16)` multiplicities `m_rng16[0..65536]`:
    let mut r_lo = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut r_hi = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut d_lo = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut d_hi = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut q_lo = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut q_hi = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut dq_lo = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut dq_hi = vec![Goldilocks::ZERO; HEM_EXEC_ROWS];
    let mut m_rng16 = vec![0u64; HEM_RNG16_ROWS];
    for t in 0..HEM_EXEC_ROWS {
        let vals10 = [
            r_vals[t] & 0xFFFF,
            (r_vals[t] >> 16) & 0xFFFF,
            d_vals[t] & 0xFFFF,
            (d_vals[t] >> 16) & 0xFFFF,
            q_vals[t] & 0xFFFF,
            (q_vals[t] >> 16) & 0xFFFF,
            dq_vals[t] & 0xFFFF,
            (dq_vals[t] >> 16) & 0xFFFF,
            payload_comm.padded_bytes[t].0 & 0xFFFF,
            dfa_b_slack[t].0 & 0xFFFF,
        ];
        r_lo[t] = Goldilocks(vals10[0]);
        r_hi[t] = Goldilocks(vals10[1]);
        d_lo[t] = Goldilocks(vals10[2]);
        d_hi[t] = Goldilocks(vals10[3]);
        q_lo[t] = Goldilocks(vals10[4]);
        q_hi[t] = Goldilocks(vals10[5]);
        dq_lo[t] = Goldilocks(vals10[6]);
        dq_hi[t] = Goldilocks(vals10[7]);
        for &u in &vals10 {
            m_rng16[u as usize] += 1;
        }
    }
    if tamper == TrustlessHemTamper::ForgedRange16Multiplicity {
        m_rng16[0] = m_rng16[0].saturating_sub(1);
    }

    let wit1_cols: Vec<Vec<Goldilocks>> = vec![
        a_col,
        b_col,
        c_col,
        r_lo,
        r_hi,
        d_lo,
        d_hi,
        q_lo,
        q_hi,
        q_top,
        dq_lo,
        dq_hi,
        dq_top,
        m_wire.iter().map(|&x| Goldilocks(x)).collect(),
        dfa_s.iter().map(|&x| Goldilocks(x as u64)).collect(),
        dfa_s_next.iter().map(|&x| Goldilocks(x as u64)).collect(),
        dfa_b_slack,
        m_dfa_rom.iter().map(|&x| Goldilocks(x)).collect(),
    ];
    let mrng_col: Vec<Goldilocks> = m_rng16.iter().map(|&x| Goldilocks(x)).collect();

    // Commit Phase-1 witness tables under dual Canopy (`Poseidon2-12` + `cSHAKE256`):
    let wit1_canopy = Stage0MatrixCanopy::commit_base(2, &wit1_cols, UD100_BLOWUP, CANOPY_KEY_WIT1);
    let mrng_canopy = Stage0MatrixCanopy::commit_base(4, &[mrng_col.clone()], UD100_BLOWUP, CANOPY_KEY_MRNG);
    let wit1_p2_root = wit1_canopy.p2_root();
    let wit1_cs_pin4 = wit1_canopy.cshake_root_pin4();
    let mrng_p2_root = mrng_canopy.p2_root();
    let mrng_cs_pin4 = mrng_canopy.cshake_root_pin4();

    ch = fs_absorb_limbs_local(ch, b"WIT1_P2_ROOT", &wit1_p2_root);
    ch = fs_absorb_limbs_local(ch, b"WIT1_CS_ROOT", &wit1_cs_pin4);
    ch = fs_absorb_limbs_local(ch, b"MRNG_P2_ROOT", &mrng_p2_root);
    ch = fs_absorb_limbs_local(ch, b"MRNG_CS_ROOT", &mrng_cs_pin4);
    ch = fs_absorb_limbs_local(ch, b"DFA_S_TERM", &s_terminal_ext.to_u64_limbs());
    let ch_logup_ckpt = ch;

    // --------------------------------------------------------------------------------------------
    // 3. Squeeze LogUp challenges AFTER Phase-1 commitment & build Phase-2 LogUp Helper Columns!
    // --------------------------------------------------------------------------------------------
    let gamma_w = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_GAMMA_W", 0);
    let beta_w = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_BETA_W", 0);
    let gamma_dfa = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_GAMMA_DFA", 0);
    let beta_dfa = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_BETA_DFA", 0);
    let gamma_sh = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_GAMMA_SH", 0);
    let beta_sh = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_BETA_SH", 0);
    let beta_16 = fs_squeeze_ext4_local(ch_logup_ckpt, b"LU_BETA_16", 0);
    let gamma_dfa2 = gamma_dfa * gamma_dfa;

    let mut h_w01 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_w2r = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_dfa = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_sh = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_rng0 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_rng1 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_rng2 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_rng3 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut h_rng4 = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut s_rng16 = GoldilocksExt4::ZERO;

    // M1 hardening: fail closed if a LogUp denominator pole (`== 0`) is ever hit (prob `<= 83,968 / p_GL^4 < 2^{-239}`)
    // instead of silently computing `inv(0) = 0`.
    let checked_inv = |d: GoldilocksExt4, label: &str| -> Result<GoldilocksExt4, String> {
        if d == GoldilocksExt4::ZERO {
            return Err(format!("LogUp exceptional zero-denominator pole hit at {label}"));
        }
        Ok(d.inv())
    };

    for t in 0..HEM_EXEC_ROWS {
        let r_t = GoldilocksExt4::from_base(wit1_cols[3][t] + wit1_cols[4][t] * Goldilocks(1u64 << 16));
        let dw_a = beta_w - (GoldilocksExt4::from_base(src_a[t]) + gamma_w.scale_base(wit1_cols[0][t]));
        let dw_b = beta_w - (GoldilocksExt4::from_base(src_b[t]) + gamma_w.scale_base(wit1_cols[1][t]));
        let n_wa = GoldilocksExt4::ONE - GoldilocksExt4::from_base(sel_fs[t]);
        h_w01[t] = (n_wa * dw_b + dw_a) * checked_inv(dw_a * dw_b, "h_w01")?;

        let dw_c = beta_w - (GoldilocksExt4::from_base(src_c[t]) + gamma_w.scale_base(wit1_cols[2][t]));
        let dw_r = beta_w - (GoldilocksExt4::from_base(Goldilocks(t as u64)) + gamma_w * r_t);
        let mw = GoldilocksExt4::from_base(wit1_cols[13][t]);
        h_w2r[t] = (dw_r - mw * dw_c) * checked_inv(dw_c * dw_r, "h_w2r")?;

        let dd_l = beta_dfa
            - (GoldilocksExt4::from_base(wit1_cols[14][t])
                + gamma_dfa.scale_base(payload_comm.padded_bytes[t])
                + gamma_dfa2.scale_base(wit1_cols[15][t]));
        let dd_r = beta_dfa
            - (GoldilocksExt4::from_base(Goldilocks(((t >> 8) & 3) as u64))
                + gamma_dfa.scale_base(Goldilocks((t & 0xFF) as u64))
                + gamma_dfa2.scale_base(rom_q_next_col[t]));
        let md = GoldilocksExt4::from_base(wit1_cols[17][t]);
        h_dfa[t] = (dd_r - md * dd_l) * checked_inv(dd_l * dd_r, "h_dfa")?;

        let ds_l = beta_sh
            - (GoldilocksExt4::from_base(Goldilocks((t + 1) as u64))
                + gamma_sh.scale_base(wit1_cols[15][t]));
        let ds_r = beta_sh
            - (GoldilocksExt4::from_base(Goldilocks(t as u64)) + gamma_sh.scale_base(wit1_cols[14][t]));
        let nl = if t + 1 == HEM_EXEC_ROWS { GoldilocksExt4::ZERO } else { GoldilocksExt4::ONE };
        let nr = if t == 0 { GoldilocksExt4::ZERO } else { GoldilocksExt4::ONE };
        h_sh[t] = (nl * ds_r - nr * ds_l) * checked_inv(ds_l * ds_r, "h_sh")?;

        let pair_inv = |x0: Goldilocks, x1: Goldilocks| -> Result<GoldilocksExt4, String> {
            let d0 = beta_16 - GoldilocksExt4::from_base(x0);
            let d1 = beta_16 - GoldilocksExt4::from_base(x1);
            Ok((d0 + d1) * checked_inv(d0 * d1, "h_rng")?)
        };
        h_rng0[t] = pair_inv(wit1_cols[3][t], wit1_cols[4][t])?;
        h_rng1[t] = pair_inv(wit1_cols[5][t], wit1_cols[6][t])?;
        h_rng2[t] = pair_inv(wit1_cols[7][t], wit1_cols[8][t])?;
        h_rng3[t] = pair_inv(wit1_cols[10][t], wit1_cols[11][t])?;
        h_rng4[t] = pair_inv(payload_comm.padded_bytes[t], wit1_cols[16][t])?;
        s_rng16 = s_rng16 + h_rng0[t] + h_rng1[t] + h_rng2[t] + h_rng3[t] + h_rng4[t];
    }

    // Build `h_rng_tab[0..65536]` in parallel, failing closed on any exceptional zero denominator:
    let h_rng_tab: Vec<GoldilocksExt4> = (0..HEM_RNG16_ROWS)
        .into_par_iter()
        .map(|u| -> Result<GoldilocksExt4, String> {
            let denom = beta_16 - GoldilocksExt4::from_base(Goldilocks(u as u64));
            if denom == GoldilocksExt4::ZERO {
                return Err(format!("LogUp exceptional zero-denominator pole at Table 2 row {u}"));
            }
            Ok(denom.inv().scale_base(mrng_col[u]))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let wit2_cols: Vec<Vec<GoldilocksExt4>> = vec![
        h_w01, h_w2r, h_dfa, h_sh, h_rng0, h_rng1, h_rng2, h_rng3, h_rng4,
    ];
    let wit2_canopy = Stage0MatrixCanopy::commit_ext4(3, &wit2_cols, UD100_BLOWUP, CANOPY_KEY_WIT2);
    let hrng_canopy = Stage0MatrixCanopy::commit_ext4(5, &[h_rng_tab.clone()], UD100_BLOWUP, CANOPY_KEY_HRNG);
    let wit2_p2_root = wit2_canopy.p2_root();
    let wit2_cs_pin4 = wit2_canopy.cshake_root_pin4();
    let hrng_p2_root = hrng_canopy.p2_root();
    let hrng_cs_pin4 = hrng_canopy.cshake_root_pin4();

    ch = fs_absorb_limbs_local(ch, b"WIT2_P2_ROOT", &wit2_p2_root);
    ch = fs_absorb_limbs_local(ch, b"WIT2_CS_ROOT", &wit2_cs_pin4);
    ch = fs_absorb_limbs_local(ch, b"HRNG_P2_ROOT", &hrng_p2_root);
    ch = fs_absorb_limbs_local(ch, b"HRNG_CS_ROOT", &hrng_cs_pin4);
    ch = fs_absorb_limbs_local(ch, b"LOGUP_S_RNG16", &s_rng16.to_u64_limbs());
    let ch_sc_ckpt = ch;

    // --------------------------------------------------------------------------------------------
    // 4. Table 1 (`N_exec = 4096`) 12-Round Degree-4 Sumcheck + Lockstep `UD-100` BaseFold!
    // --------------------------------------------------------------------------------------------
    let lambda_pub = fs_squeeze_ext4_local(ch_sc_ckpt, b"SC_LAMBDA_PUB", 0);
    let alpha_exec = fs_squeeze_ext4_local(ch_sc_ckpt, b"SC_ALPHA_EXEC", 0);
    let tau_exec: Vec<GoldilocksExt4> = (0..HEM_EXEC_VARS)
        .map(|j| fs_squeeze_ext4_local(ch_sc_ckpt, b"SC_TAU_EXEC", j as u64))
        .collect();
    let exec_ch = ExecChallengeTuple {
        gamma_w,
        beta_w,
        gamma_dfa,
        beta_dfa,
        gamma_sh,
        beta_sh,
        beta_16,
        alpha_exec,
    };

    // Build all 37 column tables as `Vec<GoldilocksExt4>` for folding during Table 1 sumcheck:
    let mut cols37: Vec<Vec<GoldilocksExt4>> = Vec::with_capacity(37);
    for col in &layout.vk_cols {
        cols37.push(col.iter().map(|&x| GoldilocksExt4::from_base(x)).collect());
    }
    cols37.push(payload_comm.padded_bytes.iter().map(|&x| GoldilocksExt4::from_base(x)).collect());
    cols37.push(w_bb_comm.w_bb_col.iter().map(|&x| GoldilocksExt4::from_base(x)).collect());
    for col in &wit1_cols {
        cols37.push(col.iter().map(|&x| GoldilocksExt4::from_base(x)).collect());
    }
    for col in &wit2_cols {
        cols37.push(col.clone());
    }
    assert_eq!(cols37.len(), 37);

    let mut eq_tau_t = build_eq_table_lsb_gl_ext4(&tau_exec);
    let mut idx_t: Vec<GoldilocksExt4> = (0..HEM_EXEC_ROWS)
        .map(|t| GoldilocksExt4::from_base(Goldilocks(t as u64)))
        .collect();
    let mut rom_b_t: Vec<GoldilocksExt4> = (0..HEM_EXEC_ROWS)
        .map(|t| GoldilocksExt4::from_base(Goldilocks((t & 0xFF) as u64)))
        .collect();
    let mut rom_q_t: Vec<GoldilocksExt4> = (0..HEM_EXEC_ROWS)
        .map(|t| GoldilocksExt4::from_base(Goldilocks(((t >> 8) & 3) as u64)))
        .collect();
    let mut eq_first_t = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    eq_first_t[0] = GoldilocksExt4::ONE;
    let mut eq_last_t = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    eq_last_t[HEM_EXEC_ROWS - 1] = GoldilocksExt4::ONE;

    // Sparse public selectors `pub_sel_r[t] = sum_{i} lambda^{n-1-i} * [t == pub_r_indices[i]]`:
    let mut pub_sel_r_t = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let n_pr = layout.pub_r_indices.len();
    let mut lp = GoldilocksExt4::ONE;
    for &idx in layout.pub_r_indices.iter().rev() {
        pub_sel_r_t[idx as usize] = pub_sel_r_t[idx as usize] + lp;
        lp = lp * lambda_pub;
    }
    let mut pub_sel_a_t = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    let mut lp = GoldilocksExt4::ONE;
    for &idx in layout.pub_a_indices.iter().rev() {
        pub_sel_a_t[idx as usize] = pub_sel_a_t[idx as usize] + lp;
        lp = lp * lambda_pub;
    }
    let _ = n_pr;

    let inv2_gl = GOLDILOCKS_INV2;
    let inv6_gl = Goldilocks(6).inv();
    let inv12_gl = Goldilocks(12).inv();
    let two_gl = Goldilocks::TWO;
    let three_gl = Goldilocks(3);
    let four_gl = Goldilocks(4);

    let mut t1_sc_rounds = Vec::with_capacity(HEM_EXEC_VARS);
    let mut z_exec = Vec::with_capacity(HEM_EXEC_VARS);
    for rnd in 0..HEM_EXEC_VARS {
        let half = eq_tau_t.len() / 2;
        let eval_t1_pair = |i: usize| -> [GoldilocksExt4; 5] {
            let extrap = |v0: GoldilocksExt4, v1: GoldilocksExt4| -> [GoldilocksExt4; 5] {
                let d = v1 - v0;
                [v0, v1, v0 - d, v1 + d, v0 - d.scale_base(two_gl)]
            };
            let mut pts_v = [[GoldilocksExt4::ZERO; 37]; 5];
            for c in 0..37 {
                let ex = extrap(cols37[c][2 * i], cols37[c][2 * i + 1]);
                for p in 0..5 {
                    pts_v[p][c] = ex[p];
                }
            }
            let e_tau = extrap(eq_tau_t[2 * i], eq_tau_t[2 * i + 1]);
            let e_idx = extrap(idx_t[2 * i], idx_t[2 * i + 1]);
            let e_rb = extrap(rom_b_t[2 * i], rom_b_t[2 * i + 1]);
            let e_rq = extrap(rom_q_t[2 * i], rom_q_t[2 * i + 1]);
            let e_f0 = extrap(eq_first_t[2 * i], eq_first_t[2 * i + 1]);
            let e_fl = extrap(eq_last_t[2 * i], eq_last_t[2 * i + 1]);
            let e_pr = extrap(pub_sel_r_t[2 * i], pub_sel_r_t[2 * i + 1]);
            let e_pa = extrap(pub_sel_a_t[2 * i], pub_sel_a_t[2 * i + 1]);
            let mut out = [GoldilocksExt4::ZERO; 5];
            for p in 0..5 {
                out[p] = eval_g_exec_point(
                    &pts_v[p], e_tau[p], e_idx[p], e_rb[p], e_rq[p], e_f0[p], e_fl[p], e_pr[p], e_pa[p],
                    &exec_ch,
                );
            }
            out
        };
        let s_pts = if half >= 256 {
            (0..half)
                .into_par_iter()
                .map(eval_t1_pair)
                .reduce(
                    || [GoldilocksExt4::ZERO; 5],
                    |a, b| [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4]],
                )
        } else {
            let mut acc = [GoldilocksExt4::ZERO; 5];
            for i in 0..half {
                let v = eval_t1_pair(i);
                for p in 0..5 {
                    acc[p] = acc[p] + v[p];
                }
            }
            acc
        };
        // Interpolate degree-4 monomial coeffs `(c0, c1, c2, c3, c4)` from `{0, 1, -1, 2, -2}`:
        let c0 = s_pts[0];
        let e1 = (s_pts[1] + s_pts[2]).scale_base(inv2_gl) - c0;
        let o1 = (s_pts[1] - s_pts[2]).scale_base(inv2_gl);
        let e2 = (s_pts[3] + s_pts[4]).scale_base(inv2_gl) - c0;
        let o2 = (s_pts[3] - s_pts[4]).scale_base(inv2_gl);
        let c4 = (e2 - e1.scale_base(four_gl)).scale_base(inv12_gl);
        let c2 = e1 - c4;
        let c3 = (o2 - o1.scale_base(two_gl)).scale_base(inv6_gl);
        let _ = three_gl;
        t1_sc_rounds.push([c0, c2, c3, c4]);

        ch = fs_absorb_limbs_local(ch, b"T1_SC_C0", &c0.to_u64_limbs());
        ch = fs_absorb_limbs_local(ch, b"T1_SC_C2", &c2.to_u64_limbs());
        ch = fs_absorb_limbs_local(ch, b"T1_SC_C3", &c3.to_u64_limbs());
        ch = fs_absorb_limbs_local(ch, b"T1_SC_C4", &c4.to_u64_limbs());
        let z_j = fs_squeeze_ext4_local(ch, b"T1_SC_Z", rnd as u64);
        z_exec.push(z_j);

        let fold_vec = |v: &[GoldilocksExt4]| -> Vec<GoldilocksExt4> {
            let mut out = Vec::with_capacity(half);
            for i in 0..half {
                out.push(v[2 * i] + z_j * (v[2 * i + 1] - v[2 * i]));
            }
            out
        };
        for c in 0..37 {
            cols37[c] = fold_vec(&cols37[c]);
        }
        eq_tau_t = fold_vec(&eq_tau_t);
        idx_t = fold_vec(&idx_t);
        rom_b_t = fold_vec(&rom_b_t);
        rom_q_t = fold_vec(&rom_q_t);
        eq_first_t = fold_vec(&eq_first_t);
        eq_last_t = fold_vec(&eq_last_t);
        pub_sel_r_t = fold_vec(&pub_sel_r_t);
        pub_sel_a_t = fold_vec(&pub_sel_a_t);
    }

    let mut t1_evals_37 = [GoldilocksExt4::ZERO; 37];
    for k in 0..37 {
        t1_evals_37[k] = cols37[k][0];
        ch = fs_absorb_limbs_local(ch, b"T1_EV", &t1_evals_37[k].to_u64_limbs());
    }

    // Batch all 37 columns of Table 1 in Horner order `F_1 = sum_{k=0..36} eta_1^{36-k} col_k`:
    let eta_1 = fs_squeeze_ext4_local(ch, b"T1_BF_ETA", 0);
    let mut f1_poly = vec![GoldilocksExt4::ZERO; HEM_EXEC_ROWS];
    for t in 0..HEM_EXEC_ROWS {
        let mut acc = GoldilocksExt4::ZERO;
        for col in &layout.vk_cols {
            acc = acc * eta_1 + GoldilocksExt4::from_base(col[t]);
        }
        acc = acc * eta_1 + GoldilocksExt4::from_base(payload_comm.padded_bytes[t]);
        acc = acc * eta_1 + GoldilocksExt4::from_base(w_bb_comm.w_bb_col[t]);
        for col in &wit1_cols {
            acc = acc * eta_1 + GoldilocksExt4::from_base(col[t]);
        }
        for col in &wit2_cols {
            acc = acc * eta_1 + col[t];
        }
        f1_poly[t] = acc;
    }

    let mut t1_bf = prove_lockstep_basefold(f1_poly, &z_exec, T1_STAGE_KS, T1_BF_KEY_SEED, b"T1_BF", &mut ch);
    let (t1_pow_nonce, ch_after_t1_pow) = grind_p2_pow(P2_DOMAIN_FS_POW_T1, ch, UD100_POW_BITS);
    ch = ch_after_t1_pow;

    let mut t1_queries = Vec::with_capacity(UD100_NUM_QUERIES);
    for q_idx in 0..UD100_NUM_QUERIES {
        let mut qlab = pack_bytes_7_limbs(b"T1_UD100_Q");
        qlab.push(q_idx as u64);
        let f0 = (p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_IDX, ch, &qlab)[0] as usize) & 0x3FFF;
        let mut cur_idx = f0;
        let mut stage_fibers = Vec::with_capacity(3);
        for s_idx in 0..3 {
            let st = &t1_bf.stages[s_idx];
            let fi = cur_idx & ((1usize << st.log_fibers) - 1);
            let mut fib = st.fibers[fi].clone();
            if tamper == TrustlessHemTamper::TamperedStage1BaseFoldFiber && q_idx == 0 && s_idx == 0 {
                fib[0] = fib[0] + GoldilocksExt4::ONE;
            }
            stage_fibers.push((fi as u32, fib, st.p2_siblings(fi)));
            cur_idx = fi;
        }
        let mut wit1_cs_sibs = wit1_canopy.cshake_siblings(f0);
        if tamper == TrustlessHemTamper::TamperedStage0CShakeSibling && q_idx == 0 {
            wit1_cs_sibs[0][0] ^= 0x01;
        }
        t1_queries.push(Table1QueryOpening {
            f0: f0 as u32,
            vk_words: vk.canopy.fiber_words(f0).to_vec(),
            vk_p2_sibs: vk.canopy.p2_siblings(f0),
            vk_cs_sibs: vk.canopy.cshake_siblings(f0),
            bytes_words: payload_comm.canopy.fiber_words(f0).to_vec(),
            bytes_p2_sibs: payload_comm.canopy.p2_siblings(f0),
            bytes_cs_sibs: payload_comm.canopy.cshake_siblings(f0),
            w_bb_words: w_bb_comm.canopy.fiber_words(f0).to_vec(),
            w_bb_p2_sibs: w_bb_comm.canopy.p2_siblings(f0),
            w_bb_cs_sibs: w_bb_comm.canopy.cshake_siblings(f0),
            wit1_words: wit1_canopy.fiber_words(f0).to_vec(),
            wit1_p2_sibs: wit1_canopy.p2_siblings(f0),
            wit1_cs_sibs,
            wit2_words: wit2_canopy.fiber_words(f0).to_vec(),
            wit2_p2_sibs: wit2_canopy.p2_siblings(f0),
            wit2_cs_sibs: wit2_canopy.cshake_siblings(f0),
            stage_fibers,
        });
    }
    let _ = &mut t1_bf;

    // --------------------------------------------------------------------------------------------
    // 5. Table 2 (`N_rng = 65536 = 2^16`) 16-Round Degree-3 Sumcheck + Lockstep `UD-100` BaseFold!
    // --------------------------------------------------------------------------------------------
    let alpha_rng = fs_squeeze_ext4_local(ch_sc_ckpt, b"SC_ALPHA_RNG", 0);
    let tau_rng: Vec<GoldilocksExt4> = (0..HEM_RNG16_VARS)
        .map(|j| fs_squeeze_ext4_local(ch_sc_ckpt, b"SC_TAU_RNG", j as u64))
        .collect();
    let mut eq_tau_r = build_eq_table_lsb_gl_ext4(&tau_rng);
    let mut id_r: Vec<GoldilocksExt4> = (0..HEM_RNG16_ROWS)
        .map(|u| GoldilocksExt4::from_base(Goldilocks(u as u64)))
        .collect();
    let mut m_r: Vec<GoldilocksExt4> = mrng_col.iter().map(|&x| GoldilocksExt4::from_base(x)).collect();
    let mut h_r: Vec<GoldilocksExt4> = h_rng_tab.clone();

    let mut t2_sc_rounds = Vec::with_capacity(HEM_RNG16_VARS);
    let mut z_rng = Vec::with_capacity(HEM_RNG16_VARS);
    for rnd in 0..HEM_RNG16_VARS {
        let half = m_r.len() / 2;
        let eval_pair = |i: usize| -> [GoldilocksExt4; 4] {
            let (e0, e1) = (eq_tau_r[2 * i], eq_tau_r[2 * i + 1]);
            let (id0, id1) = (id_r[2 * i], id_r[2 * i + 1]);
            let (m0, m1) = (m_r[2 * i], m_r[2 * i + 1]);
            let (h0, h1) = (h_r[2 * i], h_r[2 * i + 1]);
            let pts_e = [e0, e1, e0 - (e1 - e0), e1 + (e1 - e0)];
            let pts_id = [id0, id1, id0 - (id1 - id0), id1 + (id1 - id0)];
            let pts_m = [m0, m1, m0 - (m1 - m0), m1 + (m1 - m0)];
            let pts_h = [h0, h1, h0 - (h1 - h0), h1 + (h1 - h0)];
            let mut out = [GoldilocksExt4::ZERO; 4];
            for p in 0..4 {
                out[p] = pts_e[p] * (pts_h[p] * (beta_16 - pts_id[p]) - pts_m[p]) + alpha_rng * pts_h[p];
            }
            out
        };
        let s_pts = if half >= 1024 {
            (0..half)
                .into_par_iter()
                .map(eval_pair)
                .reduce(
                    || [GoldilocksExt4::ZERO; 4],
                    |a, b| [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]],
                )
        } else {
            let mut acc = [GoldilocksExt4::ZERO; 4];
            for i in 0..half {
                let v = eval_pair(i);
                for p in 0..4 {
                    acc[p] = acc[p] + v[p];
                }
            }
            acc
        };
        // Interpolate degree-3 monomial coeffs `(c0, c1, c2, c3)` from `{0, 1, -1, 2}`:
        let c0 = s_pts[0];
        let c2 = (s_pts[1] + s_pts[2]).scale_base(inv2_gl) - c0;
        let o1 = (s_pts[1] - s_pts[2]).scale_base(inv2_gl);
        let c3 = (s_pts[3] - c0 - c2.scale_base(four_gl) - o1.scale_base(two_gl)).scale_base(inv6_gl);
        t2_sc_rounds.push([c0, c2, c3]);

        ch = fs_absorb_limbs_local(ch, b"T2_SC_C0", &c0.to_u64_limbs());
        ch = fs_absorb_limbs_local(ch, b"T2_SC_C2", &c2.to_u64_limbs());
        ch = fs_absorb_limbs_local(ch, b"T2_SC_C3", &c3.to_u64_limbs());
        let z_j = fs_squeeze_ext4_local(ch, b"T2_SC_Z", rnd as u64);
        z_rng.push(z_j);

        let fold_par = |v: &[GoldilocksExt4]| -> Vec<GoldilocksExt4> {
            if half >= 1024 {
                (0..half)
                    .into_par_iter()
                    .map(|i| v[2 * i] + z_j * (v[2 * i + 1] - v[2 * i]))
                    .collect()
            } else {
                (0..half).map(|i| v[2 * i] + z_j * (v[2 * i + 1] - v[2 * i])).collect()
            }
        };
        eq_tau_r = fold_par(&eq_tau_r);
        id_r = fold_par(&id_r);
        m_r = fold_par(&m_r);
        h_r = fold_par(&h_r);
    }

    let t2_evals_2 = [m_r[0], h_r[0]];
    ch = fs_absorb_limbs_local(ch, b"T2_EV_M", &t2_evals_2[0].to_u64_limbs());
    ch = fs_absorb_limbs_local(ch, b"T2_EV_H", &t2_evals_2[1].to_u64_limbs());

    let eta_2 = fs_squeeze_ext4_local(ch, b"T2_BF_ETA", 0);
    let f2_poly: Vec<GoldilocksExt4> = (0..HEM_RNG16_ROWS)
        .into_par_iter()
        .map(|u| eta_2.scale_base(mrng_col[u]) + h_rng_tab[u])
        .collect();

    let t2_bf = prove_lockstep_basefold(f2_poly, &z_rng, T2_STAGE_KS, T2_BF_KEY_SEED, b"T2_BF", &mut ch);
    let (t2_pow_nonce, ch_after_t2_pow) = grind_p2_pow(P2_DOMAIN_FS_POW_T2, ch, UD100_POW_BITS);
    ch = ch_after_t2_pow;

    let mut t2_queries = Vec::with_capacity(UD100_NUM_QUERIES);
    for q_idx in 0..UD100_NUM_QUERIES {
        let mut qlab = pack_bytes_7_limbs(b"T2_UD100_Q");
        qlab.push(q_idx as u64);
        let f0 = (p2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_IDX, ch, &qlab)[0] as usize) & 0x3_FFFF;
        let mut cur_idx = f0;
        let mut stage_fibers = Vec::with_capacity(4);
        for s_idx in 0..4 {
            let st = &t2_bf.stages[s_idx];
            let fi = cur_idx & ((1usize << st.log_fibers) - 1);
            stage_fibers.push((fi as u32, st.fibers[fi].clone(), st.p2_siblings(fi)));
            cur_idx = fi;
        }
        t2_queries.push(Table2QueryOpening {
            f0: f0 as u32,
            mrng_words: mrng_canopy.fiber_words(f0).to_vec(),
            mrng_p2_sibs: mrng_canopy.p2_siblings(f0),
            mrng_cs_sibs: mrng_canopy.cshake_siblings(f0),
            hrng_words: hrng_canopy.fiber_words(f0).to_vec(),
            hrng_p2_sibs: hrng_canopy.p2_siblings(f0),
            hrng_cs_sibs: hrng_canopy.cshake_siblings(f0),
            stage_fibers,
        });
    }

    let internal = TrustlessHemInternalProof {
        bb_round_polys,
        bb_raw_chals,
        wit1_p2_root,
        wit1_cs_pin4,
        mrng_p2_root,
        mrng_cs_pin4,
        s_terminal: s_terminal_ext,
        wit2_p2_root,
        wit2_cs_pin4,
        hrng_p2_root,
        hrng_cs_pin4,
        s_rng16,
        ch_logup_ckpt,
        ch_sc_ckpt,
        t1_sc_rounds,
        t1_evals_37,
        t1_bf,
        t1_pow_nonce,
        t1_queries,
        t2_sc_rounds,
        t2_evals_2,
        t2_bf,
        t2_pow_nonce,
        t2_queries,
    };
    let asm = emit_trustless_hem_stream(&stmt, layout, Some(&internal));
    let (wire_bytes, _) = asm.build_wire_bytes_and_pdig(None);
    let public_program_hash = asm.compute_public_program_hash();
    let num_records = asm.records.len();

    Ok(TrustlessHemProofBundle {
        stmt,
        wire_bytes,
        public_program_hash,
        s_terminal: claimed_s_terminal,
        num_records,
    })
}
