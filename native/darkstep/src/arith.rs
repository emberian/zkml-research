//! Word-size modular arithmetic for the 61-bit NTT primes, and the primes themselves (bfv_ref.ntt_primes).

#[inline(always)]
pub fn mulmod(a: u64, b: u64, q: u64) -> u64 {
    ((a as u128 * b as u128) % q as u128) as u64
}

#[inline(always)]
pub fn addmod(a: u64, b: u64, q: u64) -> u64 {
    let s = a + b;
    if s >= q { s - q } else { s }
}

#[inline(always)]
pub fn submod(a: u64, b: u64, q: u64) -> u64 {
    if a >= b { a - b } else { a + q - b }
}

pub fn powmod(mut b: u64, mut e: u64, q: u64) -> u64 {
    let mut r = 1u64 % q;
    b %= q;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, b, q);
        }
        b = mulmod(b, b, q);
        e >>= 1;
    }
    r
}

pub fn invmod(a: u64, q: u64) -> u64 {
    // q prime
    powmod(a, q - 2, q)
}

/// Signed integer to its residue in [0, q).
#[inline(always)]
pub fn from_i64(x: i64, q: u64) -> u64 {
    if x >= 0 {
        if (x as u64) < q { x as u64 } else { (x as u64) % q }
    } else {
        let m = x.unsigned_abs();
        if m < q { q - m } else { (x as i128).rem_euclid(q as i128) as u64 }
    }
}

#[inline(always)]
pub fn from_i128(x: i128, q: u64) -> u64 {
    x.rem_euclid(q as i128) as u64
}

/// Little-endian limbs mod q.
pub fn limbs_mod(l: &[u64], q: u64) -> u64 {
    let mut r: u128 = 0;
    for &x in l.iter().rev() {
        r = ((r << 64) | x as u128) % q as u128;
    }
    r as u64
}

/// Shoup precomputation floor(w 2^64 / q).
#[inline(always)]
pub fn shoup(w: u64, q: u64) -> u64 {
    (((w as u128) << 64) / q as u128) as u64
}

#[inline(always)]
pub fn mulmod_shoup(a: u64, w: u64, wp: u64, q: u64) -> u64 {
    let hi = ((a as u128 * wp as u128) >> 64) as u64;
    let r = a.wrapping_mul(w).wrapping_sub(hi.wrapping_mul(q));
    if r >= q { r - q } else { r }
}

fn mr_witness(n: u64, a: u64, d: u64, s: u32) -> bool {
    let mut x = powmod(a, d, n);
    if x == 1 || x == n - 1 {
        return true;
    }
    for _ in 1..s {
        x = mulmod(x, x, n);
        if x == n - 1 {
            return true;
        }
    }
    false
}

/// Deterministic Miller-Rabin for n < 2^64 (bases 2..37 suffice). Agrees with bfv_ref.is_probable_prime on primes,
/// and on composites up to its 2^-80 error.
pub fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let (mut d, mut s) = (n - 1, 0u32);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37].iter().all(|&a| mr_witness(n, a, d, s))
}

/// bfv_ref.ntt_primes(bits, count, two_n): the largest primes below 2^bits with p = 1 mod 2N, descending.
pub fn ntt_primes(bits: u32, count: usize, two_n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut p = ((1u64 << bits) - 1) / two_n * two_n + 1;
    while out.len() < count {
        if is_prime(p) {
            out.push(p);
        }
        p -= two_n;
    }
    out
}

/// Barrett reduction for a modulus below 2^61 (all our primes): x = a b < 2^122.
#[derive(Clone, Copy, Debug)]
pub struct Modulus {
    pub q: u64,
    mu: u64,       // floor(2^122 / q)
    pw: [u64; 5],  // 2^(64 k) mod q
}

impl Modulus {
    pub fn new(q: u64) -> Self {
        assert!(q < (1u64 << 61) && q > (1u64 << 32));
        let mut m = Modulus { q, mu: ((1u128 << 122) / q as u128) as u64, pw: [0; 5] };
        m.pw[0] = 1;
        let two64 = ((1u128 << 64) % q as u128) as u64;
        for k in 1..5 {
            m.pw[k] = m.mul(m.pw[k - 1], two64);
        }
        m
    }

    /// Up to five little-endian limbs mod q: sum (x_k mod q) (2^64k mod q).
    #[inline(always)]
    pub fn limbs5(&self, l: &[u64]) -> u64 {
        let mut acc: u128 = 0;
        for (k, &x) in l.iter().enumerate() {
            if x != 0 {
                let xr = if x >= self.q { x % self.q } else { x };
                acc += if k == 0 { xr as u128 } else { self.mul(xr, self.pw[k]) as u128 };
            }
        }
        self.reduce(acc)
    }

    /// x mod q for x < 2^122 (callers keep to that bound: then r < 3q before the corrections).
    #[inline(always)]
    pub fn reduce(&self, x: u128) -> u64 {
        let qhat = (((x >> 60) * self.mu as u128) >> 62) as u64;
        let mut r = (x - qhat as u128 * self.q as u128) as u64;
        while r >= self.q {
            r -= self.q;
        }
        r
    }

    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        self.reduce(a as u128 * b as u128)
    }

    /// A u64 (any value) mod q.
    #[inline(always)]
    pub fn reduce_u64(&self, x: u64) -> u64 {
        self.reduce(x as u128)
    }

    /// Little-endian limbs mod q (Horner over 2^64).
    #[inline]
    pub fn limbs(&self, l: &[u64]) -> u64 {
        let mut r = 0u64;
        for &x in l.iter().rev() {
            // r 2^64 + x = ((r 2^32 + x_hi) 2^32 + x_lo): two steps, each under 2^93
            let a = self.reduce(((r as u128) << 32) | (x >> 32) as u128);
            r = self.reduce(((a as u128) << 32) | (x & 0xffff_ffff) as u128);
        }
        r
    }
}
