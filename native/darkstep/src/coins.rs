//! Secret coins for BFV: the return masks M, u, e0, e1 and the 2^F flood of every HE return, and a key's encryption
//! coins. Two sources:
//! - `Coins::Py`: the harness's random.Random streams, seeded from PUBLIC labels ("hm|11|...", random.Random(100 + j)).
//!   The in-process reference harness (`run_local`) and the bit-exact tests use them; a party process never does
//!   unless built with `test-det`.
//! - `Coins::Prf`: SHA-256 in counter mode under a 32-byte key from the OS, one stream per label. Uniform samplers by
//!   rejection, the same distributions as the Python draws.
use pycompat::PyRandom;
use sha2::{Digest, Sha256};

/// A fresh 32-byte key from the OS.
pub fn os_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    getrandom::getrandom(&mut k).expect("os rng");
    k
}

pub struct Prf {
    base: Sha256,
    ctr: u64,
    buf: [u8; 32],
    pos: usize,
}

impl Prf {
    /// The stream SHA-256(key | len(label) | label | ctr), ctr = 0, 1, ...
    pub fn new(key: &[u8; 32], label: &str) -> Prf {
        let mut base = Sha256::new();
        base.update(b"darkstep-coins-v1");
        base.update(key);
        base.update((label.len() as u64).to_le_bytes());
        base.update(label.as_bytes());
        Prf { base, ctr: 0, buf: [0; 32], pos: 32 }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        if self.pos == 32 {
            let mut h = self.base.clone();
            h.update(self.ctr.to_le_bytes());
            self.buf.copy_from_slice(&h.finalize());
            self.ctr += 1;
            self.pos = 0;
        }
        let v = u64::from_le_bytes(self.buf[self.pos..self.pos + 8].try_into().unwrap());
        self.pos += 8;
        v
    }

    /// Uniform in [0, n), n >= 1.
    #[inline]
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let mask = if n == 1 { 0 } else { u64::MAX >> (n - 1).leading_zeros() };
        loop {
            let v = self.next_u64() & mask;
            if v < n {
                return v;
            }
        }
    }

    /// Uniform in [0, n) for a W-limb n > 0.
    pub fn below_arr<const W: usize>(&mut self, n: &[u64; W]) -> [u64; W] {
        let top = (0..W).rev().find(|&i| n[i] != 0).expect("empty range");
        let mask = u64::MAX >> n[top].leading_zeros();
        loop {
            let mut r = [0u64; W];
            for (i, x) in r.iter_mut().enumerate().take(top + 1) {
                *x = self.next_u64();
                if i == top {
                    *x &= mask;
                }
            }
            if lt(&r, n) {
                return r;
            }
        }
    }
}

fn lt<const W: usize>(a: &[u64; W], b: &[u64; W]) -> bool {
    for i in (0..W).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

fn sub<const W: usize>(a: &[u64; W], b: &[u64; W]) -> [u64; W] {
    let mut o = [0u64; W];
    let mut br = 0u64;
    for i in 0..W {
        let (x, b1) = a[i].overflowing_sub(b[i]);
        let (y, b2) = x.overflowing_sub(br);
        o[i] = y;
        br = (b1 || b2) as u64;
    }
    o
}

pub enum Coins {
    Py(PyRandom),
    Prf(Prf),
}

impl Coins {
    /// The source for `label`: the public reference stream random.Random(label) when `key` is None, else the PRF.
    pub fn for_label(key: Option<&[u8; 32]>, label: &str) -> Coins {
        match key {
            None => Coins::Py(PyRandom::from_str_seed(label)),
            Some(k) => Coins::Prf(Prf::new(k, label)),
        }
    }

    pub fn is_reference(&self) -> bool {
        matches!(self, Coins::Py(_))
    }

    /// randrange(n)
    #[inline]
    pub fn randrange_u64(&mut self, n: u64) -> u64 {
        match self {
            Coins::Py(r) => r.randrange_u64(n),
            Coins::Prf(r) => r.below(n),
        }
    }

    /// choice((-1, 0, 1))
    #[inline]
    pub fn ternary(&mut self) -> i64 {
        match self {
            Coins::Py(r) => r.ternary(),
            Coins::Prf(r) => r.below(3) as i64 - 1,
        }
    }

    /// randint(a, b)
    #[inline]
    pub fn randint_i64(&mut self, a: i64, b: i64) -> i64 {
        match self {
            Coins::Py(r) => r.randint_i64(a, b),
            Coins::Prf(r) => a + r.below((b - a + 1) as u64) as i64,
        }
    }

    /// randrange(n) for a W-limb n.
    #[inline]
    pub fn randbelow_arr<const W: usize>(&mut self, n: &[u64; W]) -> [u64; W] {
        match self {
            Coins::Py(r) => r.randbelow_arr(n),
            Coins::Prf(r) => r.below_arr(n),
        }
    }

    /// randint(-2^f, 2^f) as (negative?, magnitude).
    #[inline]
    pub fn randint_sym_pow2_arr<const W: usize>(&mut self, fbits: u32) -> (bool, [u64; W]) {
        match self {
            Coins::Py(r) => r.randint_sym_pow2_arr(fbits),
            Coins::Prf(r) => {
                let mut width = [0u64; W];
                width[(fbits as usize + 1) / 64] |= 1u64 << ((fbits + 1) % 64);
                width[0] += 1;
                let v = r.below_arr(&width);
                let mut f = [0u64; W];
                f[fbits as usize / 64] |= 1u64 << (fbits % 64);
                if lt(&v, &f) {
                    (true, sub(&f, &v))
                } else {
                    (false, sub(&v, &f))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prf_samplers_in_range_and_spread() {
        let k = [7u8; 32];
        let mut c = Coins::Prf(Prf::new(&k, "t"));
        let mut hist = [0usize; 17];
        for _ in 0..170_000 {
            let v = c.randint_i64(-8, 8);
            assert!((-8..=8).contains(&v));
            hist[(v + 8) as usize] += 1;
        }
        assert!(hist.iter().all(|&h| (9_000..11_000).contains(&h)), "{hist:?}");
        let mut neg = 0;
        for _ in 0..10_000 {
            let (n, m) = c.randint_sym_pow2_arr::<5>(175);
            neg += n as usize;
            let lim = [0, 0, 1u64 << (175 - 128), 0, 0];
            assert!(!lt(&lim, &m), "magnitude <= 2^175");
        }
        assert!((4_500..5_500).contains(&neg));
        // distinct labels, distinct streams; same key and label, same stream
        let a: Vec<u64> = (0..4).map(|_| Prf::new(&k, "a").next_u64()).collect();
        assert!(a.windows(2).all(|w| w[0] == w[1]));
        assert_ne!(Prf::new(&k, "a").next_u64(), Prf::new(&k, "b").next_u64());
        assert_ne!(Prf::new(&k, "a").next_u64(), Prf::new(&[8u8; 32], "a").next_u64());
    }
}
