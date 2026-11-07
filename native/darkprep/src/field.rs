//! Arithmetic mod a prime p < 2^63.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp {
    pub p: u64,
}

impl Fp {
    pub fn new(p: u64) -> Self {
        assert!(p > 2 && p < (1 << 63));
        Fp { p }
    }
    #[inline]
    pub fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p { s - self.p } else { s }
    }
    #[inline]
    pub fn sub(&self, a: u64, b: u64) -> u64 {
        if a >= b { a - b } else { a + self.p - b }
    }
    #[inline]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % self.p as u128) as u64
    }
    pub fn pow(&self, mut a: u64, mut e: u64) -> u64 {
        let mut r = 1u64;
        a %= self.p;
        while e > 0 {
            if e & 1 == 1 {
                r = self.mul(r, a);
            }
            a = self.mul(a, a);
            e >>= 1;
        }
        r
    }
    pub fn inv(&self, a: u64) -> u64 {
        self.pow(a, self.p - 2)
    }
    /// 2^k mod p.
    pub fn two_pow(&self, k: u32) -> u64 {
        self.pow(2, k as u64)
    }
}
