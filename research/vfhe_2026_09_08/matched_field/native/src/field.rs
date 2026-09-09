//! Scalar research adapter for the four exact BFV RNS primes.
//!
//! [SOURCE] Trait contracts: local Plonky3 82cfad73, `field/src/field.rs`,
//! `field/src/integers.rs`, and `field/src/extension/mod.rs`.
//! [DERIVED] Canonical representatives and u128 multiplication implement Z/qZ.
//! [EXECUTED] The tests below check complete factorizations and generator orders,
//! prime certificates, and quartic irreducibility with polynomial arithmetic.
//! They are executable checks, not a formal proof or a security estimate.

use core::array;
use core::fmt::{self, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use core::str::FromStr;

use num_bigint::BigUint;
use p3_challenger::UniformSamplingField;
use p3_field::extension::{
    BinomialExtensionField, BinomiallyExtendable, BinomiallyExtendableAlgebra,
    HasTwoAdicBinomialExtension,
};
use p3_field::integers::QuotientMap;
use p3_field::{
    Field, Packable, PrimeCharacteristicRing, PrimeField, PrimeField64, RawDataSerializable,
    TwoAdicField,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Deserializer, Serialize};

pub const BFV_PRIMES: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];

/// A canonical residue, with field traits available only for the four listed q.
/// Scalar packing is intentional; this is a correctness-first research backend.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct BfvField<const Q: u64>(u64);

pub type BfvQ0 = BfvField<1125899906826241>;
pub type BfvQ1 = BfvField<1125899906629633>;
pub type BfvQ2 = BfvField<1125899905744897>;
pub type BfvQ3 = BfvField<1125899905351681>;
pub type BfvExtension<const Q: u64> = BinomialExtensionField<BfvField<Q>, 4>;

mod sealed {
    pub trait Sealed {}
}

/// Add `where BfvField<Q>: BfvParameters` to functions generic over q.
/// Sealing prevents downstream code from granting field status to a composite q.
pub trait BfvParameters: sealed::Sealed {
    const PRIMITIVE_ROOT: u64;
    const EXT_GENERATOR_CONSTANT: u64;
}

macro_rules! parameters {
    ($q:literal, $g:literal, $e:literal) => {
        impl sealed::Sealed for BfvField<$q> {}
        impl BfvParameters for BfvField<$q> {
            const PRIMITIVE_ROOT: u64 = $g;
            const EXT_GENERATOR_CONSTANT: u64 = $e;
        }
    };
}

// [EXECUTED] Parameters found by ascending integer search; the complete-order
// tests below independently validate the selected candidates, including q^4-1.
parameters!(1125899906826241, 22, 8);
parameters!(1125899906629633, 10, 4);
parameters!(1125899905744897, 7, 7);
parameters!(1125899905351681, 13, 6);

const fn pow_mod(mut a: u64, mut e: u64, q: u64) -> u64 {
    let mut result = 1;
    while e != 0 {
        if e & 1 != 0 {
            result = (result as u128 * a as u128 % q as u128) as u64;
        }
        a = (a as u128 * a as u128 % q as u128) as u64;
        e >>= 1;
    }
    result
}

impl<const Q: u64> BfvField<Q>
where
    Self: BfvParameters,
{
    /// Quotient-map construction; use `from_canonical` for untrusted residues.
    #[inline]
    pub const fn new(value: u64) -> Self {
        Self(value % Q)
    }

    #[inline]
    pub const fn from_canonical(value: u64) -> Option<Self> {
        if value < Q { Some(Self(value)) } else { None }
    }

    #[inline]
    pub const fn as_u64(self) -> u64 {
        self.0
    }

    /// Reject noncanonical wire encodings rather than reducing modulo q.
    pub fn from_canonical_le_bytes(bytes: [u8; 8]) -> Option<Self> {
        Self::from_canonical(u64::from_le_bytes(bytes))
    }
}

impl<const Q: u64> Display for BfvField<Q> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NonCanonicalFieldElement;

impl Display for NonCanonicalFieldElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("expected a canonical unsigned decimal field element less than q")
    }
}
impl std::error::Error for NonCanonicalFieldElement {}

impl<const Q: u64> FromStr for BfvField<Q>
where
    Self: BfvParameters,
{
    type Err = NonCanonicalFieldElement;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty()
            || !s.bytes().all(|b| b.is_ascii_digit())
            || (s.len() > 1 && s.starts_with('0'))
        {
            return Err(NonCanonicalFieldElement);
        }
        s.parse::<u64>()
            .ok()
            .and_then(Self::from_canonical)
            .ok_or(NonCanonicalFieldElement)
    }
}

impl<'de, const Q: u64> Deserialize<'de> for BfvField<Q>
where
    Self: BfvParameters,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = u64::deserialize(deserializer)?;
        Self::from_canonical(value)
            .ok_or_else(|| serde::de::Error::custom("noncanonical BFV field residue"))
    }
}

impl<const Q: u64> Packable for BfvField<Q> where Self: BfvParameters {}

impl<const Q: u64> PrimeCharacteristicRing for BfvField<Q>
where
    Self: BfvParameters,
{
    type PrimeSubfield = Self;
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);
    const TWO: Self = Self(2);
    const NEG_ONE: Self = Self(Q - 1);

    #[inline]
    fn from_prime_subfield(f: Self) -> Self {
        f
    }

    #[inline]
    fn halve(&self) -> Self {
        Self((self.0 + if self.0 & 1 != 0 { Q } else { 0 }) >> 1)
    }
}

impl<const Q: u64> Field for BfvField<Q>
where
    Self: BfvParameters,
{
    type Packing = Self;
    const GENERATOR: Self = Self(Self::PRIMITIVE_ROOT);

    #[inline]
    fn try_inverse(&self) -> Option<Self> {
        if self.0 == 0 {
            None
        } else {
            Some(Self(pow_mod(self.0, Q - 2, Q)))
        }
    }

    fn order() -> BigUint {
        BigUint::from(Q)
    }
}

impl<const Q: u64> PrimeField for BfvField<Q>
where
    Self: BfvParameters,
{
    fn as_canonical_biguint(&self) -> BigUint {
        BigUint::from(self.0)
    }
}

impl<const Q: u64> PrimeField64 for BfvField<Q>
where
    Self: BfvParameters,
{
    const ORDER_U64: u64 = Q;
    #[inline]
    fn as_canonical_u64(&self) -> u64 {
        self.0
    }
}

impl<const Q: u64> RawDataSerializable for BfvField<Q>
where
    Self: BfvParameters,
{
    p3_field::impl_raw_serializable_primefield64!();
}

impl<const Q: u64> TwoAdicField for BfvField<Q>
where
    Self: BfvParameters,
{
    const TWO_ADICITY: usize = 14;

    fn two_adic_generator(bits: usize) -> Self {
        assert!(bits <= Self::TWO_ADICITY, "BFV field has two-adicity 14");
        Self(pow_mod(Self::PRIMITIVE_ROOT, (Q - 1) >> bits, Q))
    }
}

impl<const Q: u64> UniformSamplingField for BfvField<Q>
where
    Self: BfvParameters,
{
    // q = 1 (mod 2^14), so rejection probability is exactly 1/q for 1..=14.
    const MAX_SINGLE_SAMPLE_BITS: usize = 14;
    const SAMPLING_BITS_M: [u64; 64] = {
        let mut result = [0; 64];
        let mut k = 0;
        while k < 64 {
            result[k] = Q & (u64::MAX << k);
            k += 1;
        }
        result
    };
}

impl<const Q: u64> Distribution<BfvField<Q>> for StandardUniform
where
    BfvField<Q>: BfvParameters,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BfvField<Q> {
        loop {
            let candidate = rng.next_u64() & ((1_u64 << 50) - 1);
            if let Some(value) = BfvField::from_canonical(candidate) {
                return value;
            }
        }
    }
}

macro_rules! unsigned_quotient {
    ($($t:ty),+) => {$(
        impl<const Q: u64> QuotientMap<$t> for BfvField<Q>
        where Self: BfvParameters {
            #[inline]
            fn from_int(value: $t) -> Self { Self((value as u128 % Q as u128) as u64) }
            #[inline]
            fn from_canonical_checked(value: $t) -> Option<Self> {
                if (value as u128) < Q as u128 { Some(Self(value as u64)) } else { None }
            }
            #[inline]
            unsafe fn from_canonical_unchecked(value: $t) -> Self {
                debug_assert!((value as u128) < Q as u128);
                Self(value as u64)
            }
        }
    )+};
}
unsigned_quotient!(u8, u16, u32, u64, u128);

macro_rules! signed_quotient {
    ($($t:ty),+) => {$(
        impl<const Q: u64> QuotientMap<$t> for BfvField<Q>
        where Self: BfvParameters {
            #[inline]
            fn from_int(value: $t) -> Self {
                // rem_euclid handles i128::MIN without overflowing a negation.
                Self((value as i128).rem_euclid(Q as i128) as u64)
            }
            #[inline]
            fn from_canonical_checked(value: $t) -> Option<Self> {
                let value = value as i128;
                let half = ((Q - 1) / 2) as i128;
                if (-half..=half).contains(&value) {
                    Some(Self(value.rem_euclid(Q as i128) as u64))
                } else { None }
            }
            #[inline]
            unsafe fn from_canonical_unchecked(value: $t) -> Self {
                debug_assert!(<Self as QuotientMap<$t>>::from_canonical_checked(value).is_some());
                Self((value as i128).rem_euclid(Q as i128) as u64)
            }
        }
    )+};
}
signed_quotient!(i8, i16, i32, i64, i128);

impl<const Q: u64> Add for BfvField<Q>
where
    Self: BfvParameters,
{
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let sum = self.0 + rhs.0;
        Self(if sum >= Q { sum - Q } else { sum })
    }
}
impl<const Q: u64> Sub for BfvField<Q>
where
    Self: BfvParameters,
{
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(if self.0 >= rhs.0 {
            self.0 - rhs.0
        } else {
            self.0 + Q - rhs.0
        })
    }
}
impl<const Q: u64> Neg for BfvField<Q>
where
    Self: BfvParameters,
{
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self(if self.0 == 0 { 0 } else { Q - self.0 })
    }
}
impl<const Q: u64> Mul for BfvField<Q>
where
    Self: BfvParameters,
{
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self((self.0 as u128 * rhs.0 as u128 % Q as u128) as u64)
    }
}
impl<const Q: u64> Div for BfvField<Q>
where
    Self: BfvParameters,
{
    type Output = Self;
    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inverse()
    }
}

macro_rules! assign {
    ($trait:ident, $method:ident, $op:tt) => {
        impl<const Q: u64> $trait for BfvField<Q>
        where Self: BfvParameters {
            #[inline]
            fn $method(&mut self, rhs: Self) { *self = *self $op rhs; }
        }
    };
}
assign!(AddAssign, add_assign, +);
assign!(SubAssign, sub_assign, -);
assign!(MulAssign, mul_assign, *);
assign!(DivAssign, div_assign, /);

impl<const Q: u64> Sum for BfvField<Q>
where
    Self: BfvParameters,
{
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}
impl<const Q: u64> Product for BfvField<Q>
where
    Self: BfvParameters,
{
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |a, b| a * b)
    }
}

impl<const Q: u64> BinomiallyExtendableAlgebra<Self, 4> for BfvField<Q> where Self: BfvParameters {}

impl<const Q: u64> BinomiallyExtendable<4> for BfvField<Q>
where
    Self: BfvParameters,
{
    const W: Self = Self(Self::PRIMITIVE_ROOT);
    const DTH_ROOT: Self = Self(pow_mod(Self::PRIMITIVE_ROOT, (Q - 1) / 4, Q));
    const EXT_GENERATOR: [Self; 4] = [
        Self(Self::EXT_GENERATOR_CONSTANT),
        Self(1),
        Self(0),
        Self(0),
    ];
}

impl<const Q: u64> HasTwoAdicBinomialExtension<4> for BfvField<Q>
where
    Self: BfvParameters,
{
    const EXT_TWO_ADICITY: usize = 16;

    fn ext_two_adic_generator(bits: usize) -> [Self; 4] {
        assert!(bits <= 16, "quartic BFV extension has two-adicity 16");
        if bits <= 14 {
            return [
                Self::two_adic_generator(bits),
                Self::ZERO,
                Self::ZERO,
                Self::ZERO,
            ];
        }
        // [DERIVED] X^4 = W, ord(W) = q-1, hence ord(X) = 4(q-1).
        // X^((q-1)/2^(bits-2)) has order 2^bits and agrees with base roots.
        let exponent = (Q - 1) >> (bits - 2);
        let mut result = [Self::ZERO; 4];
        result[(exponent % 4) as usize] = Self(pow_mod(Self::PRIMITIVE_ROOT, exponent / 4, Q));
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::extension::HasFrobenius;
    use p3_field::{BasedVectorSpace, PackedValue};

    const BASE_FACTORS: [&[(u64, u32)]; 4] = [
        &[
            (2, 14),
            (3, 3),
            (5, 1),
            (7, 1),
            (13, 1),
            (19, 1),
            (37, 1),
            (73, 1),
            (109, 1),
        ],
        &[(2, 14), (3, 1), (15473, 1), (1480417, 1)],
        &[(2, 14), (3, 1), (17, 1), (1347440719, 1)],
        &[(2, 14), (3, 2), (5, 1), (359, 1), (4253759, 1)],
    ];
    const EXT_FACTORS: [&[(u128, u32)]; 4] = [
        &[
            (2, 16),
            (3, 3),
            (5, 1),
            (7, 1),
            (13, 1),
            (19, 1),
            (37, 1),
            (73, 1),
            (109, 1),
            (87317, 1),
            (12776801, 1),
            (44060321, 1),
            (694333636637, 1),
            (10454482976929, 1),
        ],
        &[
            (2, 16),
            (3, 1),
            (5, 1),
            (13, 2),
            (181, 1),
            (641, 1),
            (6599, 1),
            (15473, 1),
            (1480417, 1),
            (1810937, 1),
            (7482961, 1),
            (477089033, 1),
            (85308372983, 1),
        ],
        &[
            (2, 16),
            (3, 1),
            (5, 1),
            (17, 1),
            (4253, 1),
            (5437, 1),
            (852278741, 1),
            (1347440719, 1),
            (6432254125361, 1),
            (562949952872449, 1),
        ],
        &[
            (2, 16),
            (3, 2),
            (5, 1),
            (13, 1),
            (359, 1),
            (1949, 1),
            (4253759, 1),
            (11017049, 1),
            (288840406709, 1),
            (4425485643872804756813, 1),
        ],
    ];

    fn trial_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n % 2 == 0 {
            return n == 2;
        }
        let mut d = 3;
        while d <= n / d {
            if n % d == 0 {
                return false;
            }
            d += 2;
        }
        true
    }

    fn certify_factor(n: u128) {
        if let Ok(n) = u64::try_from(n) {
            assert!(trial_prime(n), "composite factor {n}");
            return;
        }
        assert_eq!(n, 4425485643872804756813);
        // Complete factorization of n-1 and a Lucas certificate with witness 2.
        let factors = [
            (2_u64, 2_u32),
            (7, 1),
            (1187, 1),
            (3265817, 1),
            (40771842751, 1),
        ];
        let mut product = 1_u128;
        for (r, e) in factors {
            assert!(trial_prime(r));
            product *= (r as u128).pow(e);
        }
        assert_eq!(product, n - 1);
        let modulus = BigUint::from(n);
        let order = BigUint::from(n - 1);
        let witness = BigUint::from(2_u8);
        assert_eq!(witness.modpow(&order, &modulus), BigUint::from(1_u8));
        for (r, _) in factors {
            assert_ne!(witness.modpow(&(&order / r), &modulus), BigUint::from(1_u8));
        }
    }

    fn certify_base<const Q: u64>(index: usize)
    where
        BfvField<Q>: BfvParameters,
    {
        let mut product = 1_u64;
        let g = BfvField::<Q>::PRIMITIVE_ROOT;
        for &(r, e) in BASE_FACTORS[index] {
            assert!(trial_prime(r));
            product *= r.pow(e);
            assert_ne!(pow_mod(g, (Q - 1) / r, Q), 1);
        }
        assert_eq!(product, Q - 1);
        assert_eq!(pow_mod(g, Q - 1, Q), 1);
        assert_eq!((Q - 1).trailing_zeros(), 14);
        println!(
            "q={Q}: complete-factor Lucas primality and primitive-root certificate passed, g={g}"
        );
    }

    fn exp_big<F: Field>(mut value: F, exponent: &BigUint) -> F {
        let mut result = F::ONE;
        for i in 0..exponent.bits() {
            if exponent.bit(i) {
                result *= value;
            }
            value = value.square();
        }
        result
    }

    fn certify_extension<const Q: u64>(index: usize)
    where
        BfvField<Q>: BfvParameters,
    {
        let order = BigUint::from(Q).pow(4) - 1_u8;
        let mut product = BigUint::from(1_u8);
        for &(r, e) in EXT_FACTORS[index] {
            certify_factor(r);
            product *= BigUint::from(r).pow(e);
        }
        assert_eq!(product, order, "incomplete extension-order factorization");
        let generator = BfvExtension::<Q>::GENERATOR;
        assert_eq!(exp_big(generator, &order), BfvExtension::<Q>::ONE);
        for &(r, _) in EXT_FACTORS[index] {
            assert_ne!(
                exp_big(generator, &(&order / BigUint::from(r))),
                BfvExtension::<Q>::ONE
            );
        }
        println!("q={Q}: quartic generator complete-order certificate passed: {generator}");
    }

    #[test]
    fn prime_and_full_generator_certificates() {
        certify_base::<1125899906826241>(0);
        certify_base::<1125899906629633>(1);
        certify_base::<1125899905744897>(2);
        certify_base::<1125899905351681>(3);
        certify_extension::<1125899906826241>(0);
        certify_extension::<1125899906629633>(1);
        certify_extension::<1125899905744897>(2);
        certify_extension::<1125899905351681>(3);
    }

    // Independent polynomial oracle over integer residues: no BfvField or p3
    // multiplication/Frobenius implementation is used for the Rabin check.
    fn trim(p: &mut Vec<u64>) {
        while p.last() == Some(&0) {
            p.pop();
        }
    }

    fn poly_rem(mut a: Vec<u64>, b: &[u64], q: u64) -> Vec<u64> {
        assert!(!b.is_empty());
        let inverse = pow_mod(*b.last().unwrap(), q - 2, q);
        trim(&mut a);
        while a.len() >= b.len() {
            let offset = a.len() - b.len();
            let scale = (*a.last().unwrap() as u128 * inverse as u128 % q as u128) as u64;
            for (i, &v) in b.iter().enumerate() {
                let sub = (scale as u128 * v as u128 % q as u128) as u64;
                a[i + offset] = (a[i + offset] + q - sub) % q;
            }
            trim(&mut a);
        }
        a
    }

    fn poly_mul(a: &[u64], b: &[u64], f: &[u64], q: u64) -> Vec<u64> {
        if a.is_empty() || b.is_empty() {
            return vec![];
        }
        let mut result = vec![0_u64; a.len() + b.len() - 1];
        for (i, &av) in a.iter().enumerate() {
            for (j, &bv) in b.iter().enumerate() {
                result[i + j] =
                    ((result[i + j] as u128 + av as u128 * bv as u128) % q as u128) as u64;
            }
        }
        poly_rem(result, f, q)
    }

    fn poly_pow(mut a: Vec<u64>, mut n: u64, f: &[u64], q: u64) -> Vec<u64> {
        let mut result = vec![1];
        while n != 0 {
            if n & 1 != 0 {
                result = poly_mul(&result, &a, f, q);
            }
            a = poly_mul(&a, &a, f, q);
            n >>= 1;
        }
        result
    }

    fn poly_gcd(mut a: Vec<u64>, mut b: Vec<u64>, q: u64) -> Vec<u64> {
        trim(&mut a);
        trim(&mut b);
        while !b.is_empty() {
            let r = poly_rem(a, &b, q);
            a = b;
            b = r;
        }
        let inverse = pow_mod(*a.last().unwrap(), q - 2, q);
        a.iter_mut()
            .for_each(|v| *v = (*v as u128 * inverse as u128 % q as u128) as u64);
        a
    }

    fn irreducible<const Q: u64>()
    where
        BfvField<Q>: BfvParameters,
    {
        let w = BfvField::<Q>::PRIMITIVE_ROOT;
        let f = vec![Q - w, 0, 0, 0, 1];
        let x = vec![0, 1];
        let mut xqn = x.clone();
        for k in 1..=4 {
            xqn = poly_pow(xqn, Q, &f, Q);
            if k == 2 {
                let mut difference = xqn.clone();
                difference.resize(difference.len().max(2), 0);
                difference[1] = (difference[1] + Q - 1) % Q;
                assert_eq!(poly_gcd(f.clone(), difference, Q), vec![1]);
            }
        }
        assert_eq!(xqn, x);
        // Falsifier for the same oracle: X^4-1 splits over these base fields.
        let split = vec![Q - 1, 0, 0, 0, 1];
        let mut split_xq2 = poly_pow(poly_pow(x.clone(), Q, &split, Q), Q, &split, Q);
        split_xq2.resize(split_xq2.len().max(2), 0);
        split_xq2[1] = (split_xq2[1] + Q - 1) % Q;
        assert_ne!(poly_gcd(split, split_xq2, Q), vec![1]);
        // For degree 4, the Rabin conditions above are x^(q^4)=x mod f
        // and gcd(f, x^(q^2)-x)=1; 2 is the only prime divisor of 4.
        println!("q={Q}: X^4-{w} Rabin irreducibility check passed");
    }

    #[test]
    fn quartics_pass_independent_rabin_irreducibility_check() {
        irreducible::<1125899906826241>();
        irreducible::<1125899906629633>();
        irreducible::<1125899905744897>();
        irreducible::<1125899905351681>();
    }

    fn arithmetic<const Q: u64>()
    where
        BfvField<Q>: BfvParameters,
    {
        type F<const P: u64> = BfvField<P>;
        assert_eq!(<F<Q> as PackedValue>::WIDTH, 1);
        assert_eq!(F::<Q>::ZERO.try_inverse(), None);
        let boundaries = [0, 1, 2, Q / 2, Q / 2 + 1, Q - 2, Q - 1];
        for a in boundaries {
            let fa = F::<Q>::new(a);
            assert_eq!(fa.halve().double(), fa);
            assert_eq!(fa + -fa, F::<Q>::ZERO);
            if a != 0 {
                assert_eq!(fa * fa.inverse(), F::<Q>::ONE);
            }
            for b in boundaries {
                let fb = F::<Q>::new(b);
                let bigq = BigUint::from(Q);
                assert_eq!(
                    (fa * fb).as_canonical_biguint(),
                    BigUint::from(a) * BigUint::from(b) % &bigq
                );
                assert_eq!(
                    (fa + fb).as_canonical_biguint(),
                    (BigUint::from(a) + BigUint::from(b)) % &bigq
                );
                assert_eq!(
                    (fa - fb).as_canonical_biguint(),
                    (BigUint::from(a) + &bigq - BigUint::from(b)) % &bigq
                );
                if b != 0 {
                    assert_eq!((fa / fb) * fb, fa);
                }
            }
        }
        let mut state = 0x7654_3210_fedc_ba98_u64;
        for _ in 0..512 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let a = F::<Q>::new(state);
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let b = F::<Q>::new(state);
            let expected = BigUint::from(a.0) * BigUint::from(b.0) % BigUint::from(Q);
            assert_eq!((a * b).as_canonical_biguint(), expected);
            if !a.is_zero() {
                assert_eq!(a * a.inverse(), F::<Q>::ONE);
            }
        }
        for bits in 0..=14 {
            let root = F::<Q>::two_adic_generator(bits);
            assert_eq!(root.exp_power_of_2(bits), F::<Q>::ONE);
            if bits > 0 {
                assert_eq!(root.exp_power_of_2(bits - 1), F::<Q>::NEG_ONE);
                assert_eq!(root.square(), F::<Q>::two_adic_generator(bits - 1));
            }
            if bits > 0 {
                assert_eq!(F::<Q>::SAMPLING_BITS_M[bits], Q - 1);
            }
        }
        let dth = <F<Q> as BinomiallyExtendable<4>>::DTH_ROOT;
        assert_eq!(dth, F::<Q>::GENERATOR.exp_u64((Q - 1) / 4));
        assert_eq!(dth.square(), F::<Q>::NEG_ONE);
        let x = BfvExtension::<Q>::new([F::<Q>::ZERO, F::<Q>::ONE, F::<Q>::ZERO, F::<Q>::ZERO]);
        assert_eq!(x.exp_u64(4), BfvExtension::<Q>::from(F::<Q>::GENERATOR));
        for bits in 0..=16 {
            let root = BfvExtension::<Q>::two_adic_generator(bits);
            assert_eq!(root.exp_power_of_2(bits), BfvExtension::<Q>::ONE);
            if bits > 0 {
                assert_eq!(root.exp_power_of_2(bits - 1), BfvExtension::<Q>::NEG_ONE);
                assert_eq!(
                    root.square(),
                    BfvExtension::<Q>::two_adic_generator(bits - 1)
                );
            }
        }
        for a in 0..16_u64 {
            let value = BfvExtension::<Q>::new([
                F::<Q>::new(a),
                F::<Q>::ONE,
                F::<Q>::new(2 * a + 1),
                F::<Q>::new(7),
            ]);
            assert_eq!(value * value.inverse(), BfvExtension::<Q>::ONE);
            assert_eq!(value.frobenius(), value.exp_u64(Q));
            assert_eq!(value.repeated_frobenius(4), value);
            // Compare multiplication with the independent polynomial oracle.
            let coeffs: Vec<_> = value
                .as_basis_coefficients_slice()
                .iter()
                .map(|v: &BfvField<Q>| v.0)
                .collect();
            let modulus = [Q - F::<Q>::PRIMITIVE_ROOT, 0, 0, 0, 1];
            let mut expected = poly_mul(&coeffs, &coeffs, &modulus, Q);
            expected.resize(4, 0);
            let actual: Vec<_> = value
                .square()
                .as_basis_coefficients_slice()
                .iter()
                .map(|v: &BfvField<Q>| v.0)
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn arithmetic_roots_frobenius_and_extension_inverse() {
        arithmetic::<1125899906826241>();
        arithmetic::<1125899906629633>();
        arithmetic::<1125899905744897>();
        arithmetic::<1125899905351681>();
    }

    fn decoding<const Q: u64>()
    where
        BfvField<Q>: BfvParameters,
    {
        for value in [0, 1, Q - 1] {
            let field = BfvField::<Q>::from_canonical(value).unwrap();
            assert_eq!(value.to_string().parse::<BfvField<Q>>().unwrap(), field);
            assert_eq!(
                serde_json::from_str::<BfvField<Q>>(&value.to_string()).unwrap(),
                field
            );
            assert_eq!(serde_json::to_string(&field).unwrap(), value.to_string());
            assert_eq!(
                BfvField::<Q>::from_canonical_le_bytes(value.to_le_bytes()),
                Some(field)
            );
            assert_eq!(field.into_bytes(), value.to_le_bytes());
        }
        for value in [Q, Q + 1, u64::MAX] {
            assert!(BfvField::<Q>::from_canonical(value).is_none());
            assert!(BfvField::<Q>::from_canonical_le_bytes(value.to_le_bytes()).is_none());
            assert!(value.to_string().parse::<BfvField<Q>>().is_err());
            assert!(serde_json::from_str::<BfvField<Q>>(&value.to_string()).is_err());
        }
        for invalid in ["", "00", "01", "+1", "-1", " 1", "1 ", "1.0", "1e0"] {
            assert!(
                invalid.parse::<BfvField<Q>>().is_err(),
                "accepted {invalid:?}"
            );
        }
        for invalid in ["-1", "1.0", "1e0", "\"1\"", "null"] {
            assert!(serde_json::from_str::<BfvField<Q>>(invalid).is_err());
        }
        let half = ((Q - 1) / 2) as i128;
        for value in [-half, 0, half] {
            assert!(<BfvField<Q> as QuotientMap<i128>>::from_canonical_checked(value).is_some());
        }
        for value in [-half - 1, half + 1, i128::MIN, i128::MAX] {
            assert!(<BfvField<Q> as QuotientMap<i128>>::from_canonical_checked(value).is_none());
            assert_eq!(
                BfvField::<Q>::from_i128(value).0,
                value.rem_euclid(Q as i128) as u64
            );
        }
        assert_eq!(
            BfvField::<Q>::from_u128(u128::MAX).0,
            (u128::MAX % Q as u128) as u64
        );
        assert!(<BfvField<Q> as QuotientMap<u128>>::from_canonical_checked(u128::MAX).is_none());
    }

    #[test]
    fn canonical_decoders_and_signed_quotient_extremes() {
        decoding::<1125899906826241>();
        decoding::<1125899906629633>();
        decoding::<1125899905744897>();
        decoding::<1125899905351681>();
    }

    #[test]
    #[should_panic(expected = "two-adicity 14")]
    fn oversized_base_domain_is_rejected() {
        let _ = BfvQ0::two_adic_generator(15);
    }

    #[test]
    #[should_panic(expected = "two-adicity 16")]
    fn oversized_extension_domain_is_rejected() {
        let _ = BfvExtension::<1125899906826241>::two_adic_generator(17);
    }
}
