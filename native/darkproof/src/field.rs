//! F_p for p = bfv.ntt_primes(61, 4, 16384)[3] = 2^61 - 1294335 (the harness's shared 61-bit prime).
pub const P: u64 = 2305843009212399617;
const C: u64 = (1u64 << 61) - P; // 2^61 = C mod p
const M61: u128 = (1u128 << 61) - 1;

#[inline(always)]
pub fn red(x: u128) -> u64 {
    // x < 2^128: fold twice at 2^61, then one conditional subtraction
    let t = (x & M61) + (x >> 61) * C as u128;
    let t = (t & M61) + (t >> 61) * C as u128;
    let t = t as u64;
    if t >= P { t - P } else { t }
}

#[inline(always)]
pub fn add(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= P { s - P } else { s }
}

#[inline(always)]
pub fn sub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a + P - b }
}

#[inline(always)]
pub fn neg(a: u64) -> u64 {
    if a == 0 { 0 } else { P - a }
}

#[inline(always)]
pub fn mul(a: u64, b: u64) -> u64 {
    red(a as u128 * b as u128)
}

/// Python's `c % p` for a signed int coefficient.
#[inline(always)]
pub fn from_i64(c: i64) -> u64 {
    let r = c.rem_euclid(P as i64);
    r as u64
}

#[inline(always)]
pub fn from_i128(c: i128) -> u64 {
    c.rem_euclid(P as i128) as u64
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
    assert!(a % P != 0, "inverse of 0");
    pow(a, P - 2)
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
        acc = (((acc as u128) << 64 | limb as u128) % P as u128) as u64;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn red_matches_u128_mod() {
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
