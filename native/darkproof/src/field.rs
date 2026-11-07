//! F_p for the step's 61-bit prime, the BFV plaintext modulus t of the HE profile (bfv.ntt_primes(61, L + 1, 2N)[L]):
//!   P_DEMO   = 2^61 - 1294335, N = 8192 / L = 3 (also the harness's shared prime, the default);
//!   P_LEDGER = 2^61 - 3178495, N = 16384 / L = 4 (the deployed ledger profile).
//! The modulus is process-wide: `set_p` once before any field arithmetic (the ledger's genesis pins it).
use std::sync::atomic::{AtomicU64, Ordering};

pub const P_DEMO: u64 = 2305843009212399617;
pub const P_LEDGER: u64 = 2305843009210515457;
const M61: u128 = (1u128 << 61) - 1;
static PV: AtomicU64 = AtomicU64::new(P_DEMO);
static CV: AtomicU64 = AtomicU64::new((1u64 << 61) - P_DEMO);

/// The field modulus.
#[inline(always)]
pub fn p() -> u64 {
    PV.load(Ordering::Relaxed)
}

#[inline(always)]
fn c() -> u64 {
    CV.load(Ordering::Relaxed)
}

/// Select the modulus (one of the two profile primes). Panics if a different one was already selected after use
/// began elsewhere; tests that need both run in separate processes.
pub fn set_p(q: u64) {
    assert!(q == P_DEMO || q == P_LEDGER, "unsupported field modulus {q}");
    PV.store(q, Ordering::SeqCst);
    CV.store((1u64 << 61) - q, Ordering::SeqCst);
}

#[inline(always)]
pub fn red(x: u128) -> u64 {
    // x < 2^128: fold twice at 2^61, then one conditional subtraction
    let (pp, cc) = (p(), c() as u128);
    let t = (x & M61) + (x >> 61) * cc;
    let t = (t & M61) + (t >> 61) * cc;
    let t = t as u64;
    if t >= pp { t - pp } else { t }
}

#[inline(always)]
pub fn add(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= p() { s - p() } else { s }
}

#[inline(always)]
pub fn sub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a + p() - b }
}

#[inline(always)]
pub fn neg(a: u64) -> u64 {
    if a == 0 { 0 } else { p() - a }
}

#[inline(always)]
pub fn mul(a: u64, b: u64) -> u64 {
    red(a as u128 * b as u128)
}

/// Python's `c % p` for a signed int coefficient.
#[inline(always)]
pub fn from_i64(c: i64) -> u64 {
    let r = c.rem_euclid(p() as i64);
    r as u64
}

#[inline(always)]
pub fn from_i128(c: i128) -> u64 {
    c.rem_euclid(p() as i128) as u64
}

pub fn pow(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, b);
        }
        b = mul(b, b);
        e >>= 1;
    }
    r
}

pub fn inv(a: u64) -> u64 {
    assert!(a % p() != 0, "inverse of 0");
    pow(a, p() - 2)
}

/// 1 - r (mod p).
#[inline(always)]
pub fn one_minus(r: u64) -> u64 {
    sub(1, r)
}

/// Dot product with lazy reduction (u128 accumulator, reduced every 32 terms).
#[inline]
pub fn dot(a: &[u64], b: &[u64]) -> u64 {
    debug_assert_eq!(a.len(), b.len());
    let mut acc: u64 = 0;
    for (ca, cb) in a.chunks(32).zip(b.chunks(32)) {
        let mut s: u128 = 0;
        for (&x, &y) in ca.iter().zip(cb) {
            s += x as u128 * y as u128;
        }
        acc = add(acc, red(s));
    }
    acc
}

/// int(hex digest, 16) % p for a 32-byte big-endian digest.
pub fn from_digest(d: &[u8; 32]) -> u64 {
    let mut acc: u64 = 0;
    for chunk in d.chunks(8) {
        let limb = u64::from_be_bytes(chunk.try_into().unwrap());
        acc = (((acc as u128) << 64 | limb as u128) % p() as u128) as u64;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn red_matches_u128_mod() {
        for q in [P_DEMO, P_LEDGER] {
            set_p(q);
            red_case(q);
        }
        set_p(P_DEMO);
    }
    fn red_case(P: u64) {
        let xs = [0u128, 1, P as u128, P as u128 * 2 + 5, u128::MAX, (P as u128 - 1) * (P as u128 - 1), 1u128 << 127];
        for &x in &xs {
            assert_eq!(red(x) as u128, x % P as u128, "{x}");
        }
        let mut s = 12345u64;
        for _ in 0..100000 {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let a = s % P;
            let b = s.rotate_left(17) % P;
            assert_eq!(mul(a, b) as u128, (a as u128 * b as u128) % P as u128);
        }
    }
}
