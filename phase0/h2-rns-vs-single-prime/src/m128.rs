//! 2-limb (u128) modular arithmetic + the SAME Harvey lazy negacyclic NTT,
//! for a single ~109-bit modulus. Requires 4p < 2^128, i.e. p < 2^126.
//!
//! Two multiplier back-ends so the single-prime side gets its best shot:
//!   * Shoup (precomputed constant, lazy, no conditional subtraction) — used in
//!     the NTT butterflies, exactly like the u64 side.
//!   * Montgomery CIOS (general two-operand) — used for pointwise products,
//!     where neither operand is a fixed precomputed constant.

use crate::m64::mul_hi_u128;

#[derive(Clone)]
pub struct Mod128 {
    pub p: u128,
    pub p2: u128,
    pub p4: u128,
    // Montgomery
    pub n0inv: u64, // -p^{-1} mod 2^64
    pub r2: u128,   // 2^256 mod p
}

/// floor((w << 128) / p), for w < p < 2^126.
pub fn shoup_const(w: u128, p: u128) -> u128 {
    assert!(w < p && p < (1u128 << 126));
    let mut rem = w;
    let mut q: u128 = 0;
    for _ in 0..128 {
        rem <<= 1;
        q <<= 1;
        if rem >= p {
            rem -= p;
            q |= 1;
        }
    }
    q
}

#[inline(always)]
pub fn mont_mul(a: u128, b: u128, n: u128, n0inv: u64) -> u128 {
    let av = [a as u64, (a >> 64) as u64];
    let bv = [b as u64, (b >> 64) as u64];
    let nv = [n as u64, (n >> 64) as u64];
    let mut t = [0u64; 4];
    for i in 0..2 {
        let mut c: u64 = 0;
        for j in 0..2 {
            let s = (t[j] as u128) + (av[j] as u128) * (bv[i] as u128) + (c as u128);
            t[j] = s as u64;
            c = (s >> 64) as u64;
        }
        let s = (t[2] as u128) + (c as u128);
        t[2] = s as u64;
        t[3] = (s >> 64) as u64;

        let m = t[0].wrapping_mul(n0inv);
        let s = (t[0] as u128) + (m as u128) * (nv[0] as u128);
        let mut c = (s >> 64) as u64;
        for j in 1..2 {
            let s = (t[j] as u128) + (m as u128) * (nv[j] as u128) + (c as u128);
            t[j - 1] = s as u64;
            c = (s >> 64) as u64;
        }
        let s = (t[2] as u128) + (c as u128);
        t[1] = s as u64;
        t[2] = t[3].wrapping_add((s >> 64) as u64);
    }
    let mut r = (t[0] as u128) | ((t[1] as u128) << 64);
    if t[2] != 0 || r >= n {
        r = r.wrapping_sub(n);
    }
    r
}

impl Mod128 {
    pub fn new(p: u128) -> Self {
        assert!(p < (1u128 << 126) && p >= 3 && p & 1 == 1);
        // -p^{-1} mod 2^64 by Newton
        let p0 = p as u64;
        let mut inv: u64 = 1;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
        }
        let n0inv = inv.wrapping_neg();
        // r2 = 2^256 mod p, by repeated doubling from 1
        let mut acc: u128 = 1 % p;
        for _ in 0..256 {
            acc <<= 1;
            // careful: acc may overflow if p near 2^126; p < 2^126 so acc < 2^126 -> acc<<1 < 2^127
            if acc >= p {
                acc -= p;
            }
        }
        Self { p, p2: 2 * p, p4: 4 * p, n0inv, r2: acc }
    }

    #[inline(always)]
    pub fn to_mont(&self, a: u128) -> u128 { mont_mul(a, self.r2, self.p, self.n0inv) }
    #[inline(always)]
    pub fn from_mont(&self, a: u128) -> u128 { mont_mul(a, 1, self.p, self.n0inv) }
    #[inline(always)]
    pub fn mmul(&self, a: u128, b: u128) -> u128 { mont_mul(a, b, self.p, self.n0inv) }

    /// General (non-Montgomery-domain) modular multiply, via Montgomery round trip
    /// amortised: a*b mod p = from_mont(mmul(mmul(a,b), r2))... we instead expose the
    /// natural pattern: keep data in Montgomery form, one mmul per product.
    #[inline(always)]
    pub fn mul_plain(&self, a: u128, b: u128) -> u128 {
        // one extra mmul to undo the R^-1; this is what you pay if you refuse to
        // keep a Montgomery representation.
        self.mmul(self.mmul(a, b), self.r2)
    }

    #[inline(always)]
    pub fn shoup(&self, w: u128) -> u128 { shoup_const(w, self.p) }

    /// Lazy Shoup product: a < 2^128, w < p, result < 2p, congruent to a*w mod p.
    #[inline(always)]
    pub fn lazy_mul_shoup(&self, a: u128, w: u128, ws: u128) -> u128 {
        let q = mul_hi_u128(a, ws);
        a.wrapping_mul(w).wrapping_sub(q.wrapping_mul(self.p))
    }

    #[inline(always)]
    pub fn mul_shoup(&self, a: u128, w: u128, ws: u128) -> u128 {
        let r = self.lazy_mul_shoup(a, w, ws);
        if r >= self.p { r - self.p } else { r }
    }

    pub fn pow(&self, b: u128, e: u128) -> u128 {
        let mut r = self.to_mont(1);
        let mut bb = self.to_mont(b % self.p);
        let mut e = e;
        while e > 0 {
            if e & 1 == 1 { r = self.mmul(r, bb); }
            bb = self.mmul(bb, bb);
            e >>= 1;
        }
        self.from_mont(r)
    }

    pub fn inv(&self, a: u128) -> u128 { self.pow(a, self.p - 2) }
    pub fn mul(&self, a: u128, b: u128) -> u128 {
        self.from_mont(self.mmul(self.to_mont(a), self.to_mont(b)))
    }
}

pub struct Ntt128 {
    pub m: Mod128,
    pub n: usize,
    omegas: Vec<u128>,
    omegas_shoup: Vec<u128>,
    zetas_inv: Vec<u128>,
    zetas_inv_shoup: Vec<u128>,
    n_inv: u128,
    n_inv_shoup: u128,
}

fn bitrev_index(i: usize, n: usize) -> usize {
    i.reverse_bits() >> (n.leading_zeros() + 1)
}

impl Ntt128 {
    pub fn new(p: u128, n: usize) -> Self {
        let m = Mod128::new(p);
        assert!(n.is_power_of_two());
        let two_n = 2 * n as u128;
        assert!((p - 1) % two_n == 0);
        let e = (p - 1) / two_n;
        let mut psi = 0u128;
        let mut cand = 2u128;
        loop {
            let g = m.pow(cand, e);
            if g != 1 && m.pow(g, n as u128) != 1 {
                psi = g;
                break;
            }
            cand += 1;
            assert!(cand < 1000);
        }
        let psi_inv = m.inv(psi);
        let mut powers = Vec::with_capacity(n);
        let mut powers_inv = Vec::with_capacity(n);
        let mut c = 1u128;
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
        let n_inv = m.inv(n as u128);
        let n_inv_shoup = m.shoup(n_inv);
        Self { m, n, omegas, omegas_shoup, zetas_inv, zetas_inv_shoup, n_inv, n_inv_shoup }
    }

    #[inline(always)]
    fn butterfly(&self, x: &mut u128, y: &mut u128, w: u128, ws: u128) {
        if *x >= self.m.p2 { *x -= self.m.p2; }
        let t = self.m.lazy_mul_shoup(*y, w, ws);
        *y = *x + self.m.p2 - t;
        *x += t;
    }

    #[inline(always)]
    fn inv_butterfly(&self, x: &mut u128, y: &mut u128, w: u128, ws: u128) {
        let mut t = *x + *y;
        if t >= self.m.p2 { t -= self.m.p2; }
        let u = *x + self.m.p2 - *y;
        *x = t;
        *y = self.m.lazy_mul_shoup(u, w, ws);
    }

    #[inline(always)]
    fn reduce3(&self, a: u128) -> u128 {
        let mut a = a;
        if a >= self.m.p2 { a -= self.m.p2; }
        if a >= self.m.p { a -= self.m.p; }
        a
    }

    pub fn forward(&self, a: &mut [u128]) {
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

    pub fn backward(&self, a: &mut [u128]) {
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
}
