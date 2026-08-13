//! u64-lane modular arithmetic + Harvey lazy negacyclic NTT.
//! Structurally the same algorithm fhe-math 0.1.1 `ntt/native.rs` uses
//! (Shoup-multiplied Cooley-Tukey forward / Gentleman-Sande backward with
//! deferred reduction, values kept < 4p). Requires 4p < 2^64, i.e. p < 2^62.

#[derive(Clone)]
pub struct Mod64 {
    pub p: u64,
    pub p2: u64, // 2p
    pub p4: u64, // 4p
    barrett: u128,
}

impl Mod64 {
    pub fn new(p: u64) -> Self {
        assert!(p >= 2 && p < (1u64 << 62), "p must be < 2^62");
        let barrett = (u128::MAX / (p as u128)) + if u128::MAX % (p as u128) == (p as u128) - 1 { 1 } else { 0 };
        // floor(2^128 / p): u128::MAX/p == floor((2^128-1)/p); equal to floor(2^128/p)
        // unless p divides 2^128, impossible for odd p>2.
        Self { p, p2: 2 * p, p4: 4 * p, barrett }
    }

    #[inline(always)]
    pub fn reduce_u128(&self, a: u128) -> u64 {
        // Barrett: q = floor(a * barrett / 2^128); r = a - q*p
        let q = mul_hi_u128(a, self.barrett);
        let r = (a.wrapping_sub(q.wrapping_mul(self.p as u128))) as u64;
        if r >= self.p { r - self.p } else { r }
    }

    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        self.reduce_u128((a as u128) * (b as u128))
    }

    #[inline(always)]
    pub fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p { s - self.p } else { s }
    }

    pub fn shoup(&self, w: u64) -> u64 {
        (((w as u128) << 64) / (self.p as u128)) as u64
    }

    /// Shoup product, lazy: for a < 2^64, w < p, returns r < 2p with r = a*w mod p (mod 2p).
    #[inline(always)]
    pub fn lazy_mul_shoup(&self, a: u64, w: u64, w_shoup: u64) -> u64 {
        let q = ((a as u128) * (w_shoup as u128)) >> 64;
        (a.wrapping_mul(w)).wrapping_sub((q as u64).wrapping_mul(self.p))
    }

    #[inline(always)]
    pub fn mul_shoup(&self, a: u64, w: u64, w_shoup: u64) -> u64 {
        let r = self.lazy_mul_shoup(a, w, w_shoup);
        if r >= self.p { r - self.p } else { r }
    }

    pub fn pow(&self, mut b: u64, mut e: u64) -> u64 {
        let mut r = 1u64;
        b %= self.p;
        while e > 0 {
            if e & 1 == 1 { r = self.mul(r, b); }
            b = self.mul(b, b);
            e >>= 1;
        }
        r
    }

    pub fn inv(&self, a: u64) -> u64 { self.pow(a, self.p - 2) }
}

#[inline(always)]
pub fn mul_hi_u128(a: u128, b: u128) -> u128 {
    const M: u128 = u64::MAX as u128;
    let (a0, a1) = (a & M, a >> 64);
    let (b0, b1) = (b & M, b >> 64);
    let a0b0 = a0 * b0;
    let a1b0 = a1 * b0;
    let a0b1 = a0 * b1;
    let a1b1 = a1 * b1;
    let mid = (a0b0 >> 64) + (a1b0 & M) + (a0b1 & M);
    a1b1 + (a1b0 >> 64) + (a0b1 >> 64) + (mid >> 64)
}

/// Negacyclic NTT of size `n` over `Mod64`, Harvey lazy butterflies.
pub struct Ntt64 {
    pub m: Mod64,
    pub n: usize,
    omegas: Vec<u64>,
    omegas_shoup: Vec<u64>,
    zetas_inv: Vec<u64>,
    zetas_inv_shoup: Vec<u64>,
    n_inv: u64,
    n_inv_shoup: u64,
}

fn bitrev_index(i: usize, n: usize) -> usize {
    i.reverse_bits() >> (n.leading_zeros() + 1)
}

impl Ntt64 {
    pub fn new(p: u64, n: usize) -> Self {
        let m = Mod64::new(p);
        assert!(n.is_power_of_two());
        // primitive 2n-th root of unity
        let psi = primitive_root_2n(&m, n);
        let psi_inv = m.inv(psi);
        let mut powers = Vec::with_capacity(n);
        let mut powers_inv = Vec::with_capacity(n);
        let mut c = 1u64;
        let mut ci = psi_inv;
        for _ in 0..n {
            powers.push(c);
            powers_inv.push(ci);
            c = m.mul(c, psi);
            ci = m.mul(ci, psi_inv);
        }
        let mut omegas = Vec::with_capacity(n);
        let mut zetas_inv = Vec::with_capacity(n);
        for i in 0..n {
            let j = bitrev_index(i, n);
            omegas.push(powers[j]);
            zetas_inv.push(powers_inv[j]);
        }
        let omegas_shoup = omegas.iter().map(|w| m.shoup(*w)).collect();
        let zetas_inv_shoup = zetas_inv.iter().map(|w| m.shoup(*w)).collect();
        let n_inv = m.inv(n as u64);
        let n_inv_shoup = m.shoup(n_inv);
        Self { m, n, omegas, omegas_shoup, zetas_inv, zetas_inv_shoup, n_inv, n_inv_shoup }
    }

    #[inline(always)]
    fn butterfly(&self, x: &mut u64, y: &mut u64, w: u64, ws: u64) {
        // x,y < 4p on entry, < 4p on exit
        if *x >= self.m.p2 { *x -= self.m.p2; }
        let t = self.m.lazy_mul_shoup(*y, w, ws); // < 2p
        *y = *x + self.m.p2 - t;
        *x += t;
    }

    #[inline(always)]
    fn inv_butterfly(&self, x: &mut u64, y: &mut u64, w: u64, ws: u64) {
        let mut t = *x + *y;
        if t >= self.m.p2 { t -= self.m.p2; }
        let u = *x + self.m.p2 - *y;
        *x = t;
        *y = self.m.lazy_mul_shoup(u, w, ws);
    }

    #[inline(always)]
    fn reduce3(&self, a: u64) -> u64 {
        let mut a = a;
        if a >= self.m.p2 { a -= self.m.p2; }
        if a >= self.m.p { a -= self.m.p; }
        a
    }

    pub fn forward(&self, a: &mut [u64]) {
        let mut l = self.n >> 1;
        let mut k = 1usize;
        while l > 0 {
            for chunk in a.chunks_exact_mut(2 * l) {
                let w = self.omegas[k];
                let ws = self.omegas_shoup[k];
                k += 1;
                let (left, right) = chunk.split_at_mut(l);
                if l == 1 {
                    self.butterfly(&mut left[0], &mut right[0], w, ws);
                    left[0] = self.reduce3(left[0]);
                    right[0] = self.reduce3(right[0]);
                } else {
                    for (x, y) in left.iter_mut().zip(right.iter_mut()) {
                        self.butterfly(x, y, w, ws);
                    }
                }
            }
            l >>= 1;
        }
    }

    pub fn backward(&self, a: &mut [u64]) {
        let mut k = 0usize;
        let mut l = 1usize;
        while l < self.n {
            for chunk in a.chunks_exact_mut(2 * l) {
                let w = self.zetas_inv[k];
                let ws = self.zetas_inv_shoup[k];
                k += 1;
                let (left, right) = chunk.split_at_mut(l);
                for (x, y) in left.iter_mut().zip(right.iter_mut()) {
                    self.inv_butterfly(x, y, w, ws);
                }
            }
            l <<= 1;
        }
        for ai in a.iter_mut() {
            *ai = self.m.mul_shoup(*ai, self.n_inv, self.n_inv_shoup);
        }
    }

    /// pointwise product in NTT domain
    pub fn pointwise(&self, a: &mut [u64], b: &[u64]) {
        for (x, y) in a.iter_mut().zip(b.iter()) {
            *x = self.m.mul(*x, *y);
        }
    }
}

fn primitive_root_2n(m: &Mod64, n: usize) -> u64 {
    // find g of order exactly 2n
    let two_n = 2 * n as u64;
    assert!((m.p - 1) % two_n == 0, "p-1 not divisible by 2n");
    let e = (m.p - 1) / two_n;
    let mut cand = 2u64;
    loop {
        let g = m.pow(cand, e);
        // check order exactly 2n: g^n != 1 and g^(2n)==1
        if g != 1 && m.pow(g, n as u64) != 1 && m.pow(g, two_n) == 1 {
            // additionally check g^(2n/q) != 1 for prime q | 2n; 2n is a power of two so
            // g^n != 1 suffices
            return g;
        }
        cand += 1;
        assert!(cand < 1000);
    }
}
