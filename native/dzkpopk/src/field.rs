//! The 255-bit NTT prime field of zkpopk_ligero.py: P = 2^255 - 2^39 + 1 (= c 2^32 + 1, the largest such prime
//! below 2^255), Montgomery form with R = 2^256, four little-endian u64 limbs.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::Zero;

/// P, little-endian limbs.
pub const P: [u64; 4] = [0xffff_ff80_0000_0001, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff];
pub const TWO_ADIC: u32 = 32;
/// zkpopk_ligero.SHIFT (coset off every 2-power subgroup).
pub const SHIFT: u64 = 3;
/// zkpopk_ligero.ROOT, canonical, big-endian hex.
pub const ROOT_HEX: &str = "4daabe0bbeae714f40c2c13d533ca18809a16d8cb3e6c859d8399c63bd297928";

const fn neg_inv64(p0: u64) -> u64 {
    // inverse of p0 mod 2^64 by Newton, then negate
    let mut x: u64 = 1;
    let mut i = 0;
    while i < 7 {
        x = x.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(x)));
        i += 1;
    }
    x.wrapping_neg()
}
const PINV: u64 = neg_inv64(P[0]);

#[inline(always)]
fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + c as u128;
    (t as u64, (t >> 64) as u64)
}
#[inline(always)]
fn sbb(a: u64, b: u64, br: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub(b as u128).wrapping_sub(br as u128);
    (t as u64, (t >> 127) as u64)
}
#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = acc as u128 + (a as u128) * (b as u128) + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn geq_p(a: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != P[i] {
            return a[i] > P[i];
        }
    }
    true
}
#[inline(always)]
fn sub_p(a: &mut [u64; 4]) {
    let mut br = 0;
    for i in 0..4 {
        let (v, b) = sbb(a[i], P[i], br);
        a[i] = v;
        br = b;
    }
}

/// A field element in Montgomery form.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct Fe(pub [u64; 4]);

impl Fe {
    pub const ZERO: Fe = Fe([0; 4]);

    #[inline(always)]
    pub fn add(self, b: Fe) -> Fe {
        let (a, b) = (self.0, b.0);
        let mut r = [0u64; 4];
        let mut c = 0;
        for i in 0..4 {
            let (v, cc) = adc(a[i], b[i], c);
            r[i] = v;
            c = cc;
        }
        // P < 2^255 so no carry out
        if geq_p(&r) {
            sub_p(&mut r);
        }
        Fe(r)
    }

    #[inline(always)]
    pub fn sub(self, b: Fe) -> Fe {
        let (a, b) = (self.0, b.0);
        let mut r = [0u64; 4];
        let mut br = 0;
        for i in 0..4 {
            let (v, bb) = sbb(a[i], b[i], br);
            r[i] = v;
            br = bb;
        }
        if br != 0 {
            let mut c = 0;
            for i in 0..4 {
                let (v, cc) = adc(r[i], P[i], c);
                r[i] = v;
                c = cc;
            }
        }
        Fe(r)
    }

    #[inline(always)]
    pub fn neg(self) -> Fe {
        Fe::ZERO.sub(self)
    }

    /// Montgomery product (CIOS).
    #[inline(always)]
    pub fn mul(self, b: Fe) -> Fe {
        let (a, b) = (self.0, b.0);
        let mut t = [0u64; 6];
        for i in 0..4 {
            let mut c = 0;
            for j in 0..4 {
                let (v, cc) = mac(t[j], a[j], b[i], c);
                t[j] = v;
                c = cc;
            }
            let (v, cc) = adc(t[4], c, 0);
            t[4] = v;
            t[5] = cc;
            let m = t[0].wrapping_mul(PINV);
            let (_, mut c) = mac(t[0], m, P[0], 0);
            for j in 1..4 {
                let (v, cc) = mac(t[j], m, P[j], c);
                t[j - 1] = v;
                c = cc;
            }
            let (v, cc) = adc(t[4], c, 0);
            t[3] = v;
            t[4] = t[5] + cc;
        }
        let mut r = [t[0], t[1], t[2], t[3]];
        if t[4] != 0 || geq_p(&r) {
            sub_p(&mut r);
        }
        Fe(r)
    }

    #[inline(always)]
    pub fn sq(self) -> Fe {
        self.mul(self)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [0; 4]
    }

    /// From canonical limbs (< P required).
    pub fn from_canonical(x: [u64; 4]) -> Fe {
        debug_assert!(!geq_p(&x));
        Fe(x).mul(R2)
    }

    /// Canonical limbs.
    pub fn to_canonical(self) -> [u64; 4] {
        self.mul(Fe([1, 0, 0, 0])).0
    }

    pub fn from_u64(x: u64) -> Fe {
        Fe::from_canonical([x, 0, 0, 0])
    }

    pub fn from_i64(x: i64) -> Fe {
        if x >= 0 {
            Fe::from_u64(x as u64)
        } else {
            Fe::from_u64(x.unsigned_abs()).neg()
        }
    }

    pub fn from_u128(x: u128) -> Fe {
        Fe::from_canonical([x as u64, (x >> 64) as u64, 0, 0])
    }

    pub fn from_i128(x: i128) -> Fe {
        if x >= 0 {
            Fe::from_u128(x as u128)
        } else {
            Fe::from_u128(x.unsigned_abs()).neg()
        }
    }

    pub fn from_biguint(x: &BigUint) -> Fe {
        let r = x % p_big();
        let mut l = [0u64; 4];
        for (i, d) in r.to_u64_digits().iter().enumerate() {
            l[i] = *d;
        }
        Fe::from_canonical(l)
    }

    pub fn from_bigint(x: &BigInt) -> Fe {
        let f = Fe::from_biguint(x.magnitude());
        if x.sign() == Sign::Minus {
            f.neg()
        } else {
            f
        }
    }

    pub fn to_biguint(self) -> BigUint {
        let c = self.to_canonical();
        let mut u = Vec::with_capacity(8);
        for x in c {
            u.push(x as u32);
            u.push((x >> 32) as u32);
        }
        BigUint::from_slice(&u)
    }

    /// The centered lift in (-P/2, P/2) if it fits an i128.
    pub fn to_i128_centered(self) -> Option<i128> {
        let c = self.to_canonical();
        if c[2] == 0 && c[3] == 0 && c[1] >> 63 == 0 {
            return Some(((c[1] as u128) << 64 | c[0] as u128) as i128);
        }
        let n = Fe::from_canonical(c).neg().to_canonical();
        if n[2] == 0 && n[3] == 0 && n[1] >> 63 == 0 {
            return Some(-(((n[1] as u128) << 64 | n[0] as u128) as i128));
        }
        None
    }

    /// 32-byte big-endian canonical encoding (zkpopk_ligero.fe).
    pub fn to_be32(self) -> [u8; 32] {
        let c = self.to_canonical();
        let mut out = [0u8; 32];
        for i in 0..4 {
            out[(3 - i) * 8..(4 - i) * 8].copy_from_slice(&c[i].to_be_bytes());
        }
        out
    }

    /// Parse 32 big-endian bytes; None if the integer is >= P (noncanonical).
    pub fn from_be32(b: &[u8]) -> Option<Fe> {
        let mut l = [0u64; 4];
        for i in 0..4 {
            l[i] = u64::from_be_bytes(b[(3 - i) * 8..(4 - i) * 8].try_into().unwrap());
        }
        if geq_p(&l) {
            None
        } else {
            Some(Fe::from_canonical(l))
        }
    }

    pub fn pow_u64(self, mut e: u64) -> Fe {
        let mut r = ONE;
        let mut b = self;
        while e > 0 {
            if e & 1 == 1 {
                r = r.mul(b);
            }
            b = b.sq();
            e >>= 1;
        }
        r
    }

    pub fn pow_limbs(self, e: &[u64]) -> Fe {
        let mut r = ONE;
        for i in (0..e.len()).rev() {
            for bit in (0..64).rev() {
                r = r.sq();
                if (e[i] >> bit) & 1 == 1 {
                    r = r.mul(self);
                }
            }
        }
        r
    }

    pub fn inv(self) -> Fe {
        let mut e = P;
        e[0] -= 2;
        self.pow_limbs(&e)
    }
}

/// R^2 mod P (R = 2^256), computed by doubling R mod P 256 times.
const R2: Fe = {
    // R mod P = 2^256 - 2P (since 2P < 2^256 < 3P)
    let mut r = [0u64; 4];
    // compute 2^256 - 2P = -(2P) mod 2^256
    let p2 = [P[0] << 1, (P[1] << 1) | (P[0] >> 63), (P[2] << 1) | (P[1] >> 63), (P[3] << 1) | (P[2] >> 63)];
    let mut br = 0u64;
    let mut i = 0;
    while i < 4 {
        let t = (0u128).wrapping_sub(p2[i] as u128).wrapping_sub(br as u128);
        r[i] = t as u64;
        br = (t >> 127) as u64;
        i += 1;
    }
    // r = R mod P; double 256 times mod P to get R^2 mod P
    let mut k = 0;
    while k < 256 {
        let mut s = [0u64; 4];
        let mut c = 0u64;
        let mut j = 0;
        while j < 4 {
            let t = (r[j] as u128) + (r[j] as u128) + c as u128;
            s[j] = t as u64;
            c = (t >> 64) as u64;
            j += 1;
        }
        // s < 2P < 2^256: subtract P if s >= P
        let mut ge = true;
        let mut j = 4;
        while j > 0 {
            j -= 1;
            if s[j] != P[j] {
                ge = s[j] > P[j];
                break;
            }
        }
        if ge {
            let mut br = 0u64;
            let mut j = 0;
            while j < 4 {
                let t = (s[j] as u128).wrapping_sub(P[j] as u128).wrapping_sub(br as u128);
                s[j] = t as u64;
                br = (t >> 127) as u64;
                j += 1;
            }
        }
        r = s;
        k += 1;
    }
    Fe(r)
};

/// 1 in Montgomery form (R mod P).
pub const ONE: Fe = {
    let p2 = [P[0] << 1, (P[1] << 1) | (P[0] >> 63), (P[2] << 1) | (P[1] >> 63), (P[3] << 1) | (P[2] >> 63)];
    let mut r = [0u64; 4];
    let mut br = 0u64;
    let mut i = 0;
    while i < 4 {
        let t = (0u128).wrapping_sub(p2[i] as u128).wrapping_sub(br as u128);
        r[i] = t as u64;
        br = (t >> 127) as u64;
        i += 1;
    }
    Fe(r)
};

pub fn p_big() -> &'static BigUint {
    use std::sync::OnceLock;
    static PB: OnceLock<BigUint> = OnceLock::new();
    PB.get_or_init(|| BigUint::from_slice(&[0x0000_0001, 0xffff_ff80, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, 0x7fff_ffff]))
}

pub fn root() -> Fe {
    use std::sync::OnceLock;
    static R: OnceLock<Fe> = OnceLock::new();
    *R.get_or_init(|| Fe::from_biguint(&BigUint::parse_bytes(ROOT_HEX.as_bytes(), 16).unwrap()))
}

/// zkpopk_ligero.root_of(n): a primitive n-th root of unity, n a power of two <= 2^32.
pub fn root_of(n: usize) -> Fe {
    assert!(n.is_power_of_two() && n as u64 <= 1u64 << TWO_ADIC);
    root().pow_u64((1u64 << TWO_ADIC) / n as u64)
}

pub fn batch_inv(xs: &[Fe]) -> Vec<Fe> {
    let mut pre = Vec::with_capacity(xs.len());
    let mut acc = ONE;
    for x in xs {
        pre.push(acc);
        acc = acc.mul(*x);
    }
    let mut inv = acc.inv();
    let mut out = vec![Fe::ZERO; xs.len()];
    for i in (0..xs.len()).rev() {
        out[i] = pre[i].mul(inv);
        inv = inv.mul(xs[i]);
    }
    out
}

/// Horner evaluation of coefficients c at x (zkpopk_ligero.peval).
pub fn peval(c: &[Fe], x: Fe) -> Fe {
    let mut acc = Fe::ZERO;
    for a in c.iter().rev() {
        acc = acc.mul(x).add(*a);
    }
    acc
}

pub fn is_zero_big(x: &BigInt) -> bool {
    x.is_zero()
}
