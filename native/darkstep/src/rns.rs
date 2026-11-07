//! RNS context for BFV over Q = prod q_k with plaintext modulus t (the SPDZ prime): exact encoding round(Q m / t) mod
//! q_k and exact decryption round(t x / Q) mod t, both equal to bfv_ref's big-integer formulas.
use crate::arith::*;
use crate::ntt::Ntt;
use num_bigint::BigUint;

pub struct Rns {
    pub n: usize,
    pub qs: Vec<u64>,
    pub md: Vec<Modulus>,
    pub md_t: Modulus,
    t_shoup: Vec<u64>,
    recip: Vec<u128>,
    pub ntts: Vec<Ntt>,
    pub t: u64,
    pub q_big: BigUint,
    inv_k: Vec<u64>,
    q_mod_t: u64,
    inv2t: Vec<u64>,
    qhat: Vec<BigUint>,
}

impl Rns {
    pub fn new(n: usize, qs: &[u64], t: u64) -> Self {
        let q_big: BigUint = qs.iter().map(|&q| BigUint::from(q)).product();
        let qhat: Vec<BigUint> = qs.iter().map(|&q| &q_big / BigUint::from(q)).collect();
        let inv_k = qs
            .iter()
            .zip(&qhat)
            .map(|(&q, qh)| invmod(limbs_mod(&qh.to_u64_digits(), q), q))
            .collect();
        let q_mod_t = limbs_mod(&q_big.to_u64_digits(), t);
        let inv2t = qs.iter().map(|&q| invmod(mulmod(2, t % q, q), q)).collect();
        let md = qs.iter().map(|&q| Modulus::new(q)).collect();
        let t_shoup = qs.iter().map(|&q| shoup(t % q, q)).collect();
        // floor(2^125 / q): f 2^64 / q ~ (f R) >> 61, error under 2 ulps of 2^-64
        let recip = qs.iter().map(|&q| (1u128 << 125) / q as u128).collect();
        Rns { n, qs: qs.to_vec(), md, md_t: Modulus::new(t), t_shoup, recip, ntts: qs.iter().map(|&q| Ntt::new(q, n)).collect(), t, q_big, inv_k, q_mod_t, inv2t, qhat }
    }

    pub fn l(&self) -> usize {
        self.qs.len()
    }

    pub fn zero(&self) -> Vec<u64> {
        vec![0; self.l() * self.n]
    }

    /// Residues of round(Q m / t) (bfv_ref: (2 Q centered(m) + t) // (2 t)) for m in [0, t), into out[k] per prime.
    #[inline]
    pub fn encode_round(&self, m: u64, out: &mut [u64]) {
        let t = self.t;
        let qm = self.md_t.mul(self.q_mod_t, m);
        let mut rem = 2 * qm + t; // < 3t < 2^63
        if rem >= 2 * t {
            rem -= 2 * t;
        }
        // (2 Q m + t - rem) = t - rem (mod q_k), since q_k | Q; t - rem in (-t, t]
        for (k, &q) in self.qs.iter().enumerate() {
            let num = if rem <= t { t - rem } else { q - (rem - t) };
            out[k] = self.md[k].mul(num, self.inv2t[k]);
        }
    }

    /// floor(t x / Q + 1/2) mod t for x given by its residues (bfv_ref.decrypt's per-coefficient rounding).
    pub fn decrypt_round(&self, res: &[u64]) -> u64 {
        let t = self.t;
        let mut int_part: u128 = 0;
        let mut frac_fp: u128 = 0;
        let mut f = [0u64; 8];
        for k in 0..self.l() {
            let q = self.qs[k];
            let a = self.md[k].mul(res[k], self.inv_k[k]);
            // a t = quo q + f, via Shoup on the constant t (t < q)
            let est = ((a as u128 * self.t_shoup[k] as u128) >> 64) as u64;
            let mut r = (a as u128 * t as u128 - est as u128 * q as u128) as u64;
            let mut quo = est;
            if r >= q {
                r -= q;
                quo += 1;
            }
            int_part += quo as u128;
            f[k] = r;
            frac_fp += (r as u128 * self.recip[k]) >> 61;
        }
        let slack = 4 * self.l() as u128;
        let lo = (frac_fp + (1u128 << 63)).saturating_sub(slack);
        let hi = frac_fp + (1u128 << 63) + slack;
        let carry = if (lo >> 64) == (hi >> 64) {
            (lo >> 64) as u64
        } else {
            // exact: floor(sum f_k / q_k + 1/2) = floor((2 sum f_k Qhat_k + Q) / (2 Q))
            let mut s = BigUint::from(0u32);
            for k in 0..self.l() {
                s += BigUint::from(f[k]) * &self.qhat[k];
            }
            let v: BigUint = (s * 2u32 + &self.q_big) / (&self.q_big * 2u32);
            v.to_u64_digits().first().copied().unwrap_or(0)
        };
        ((int_part % t as u128 + carry as u128) % t as u128) as u64
    }

    pub fn fwd(&self, p: &mut [u64]) {
        for (k, nt) in self.ntts.iter().enumerate() {
            nt.forward(&mut p[k * self.n..(k + 1) * self.n]);
        }
    }

    pub fn inv(&self, p: &mut [u64]) {
        for (k, nt) in self.ntts.iter().enumerate() {
            nt.inverse(&mut p[k * self.n..(k + 1) * self.n]);
        }
    }

    /// acc += a * b (pointwise, NTT domain).
    pub fn mul_acc(&self, acc: &mut [u64], a: &[u64], b: &[u64]) {
        let n = self.n;
        for (k, &q) in self.qs.iter().enumerate() {
            let r = k * n..(k + 1) * n;
            let md = self.md[k];
            for ((x, &y), &z) in acc[r.clone()].iter_mut().zip(&a[r.clone()]).zip(&b[r]) {
                *x = addmod(*x, md.mul(y, z), q);
            }
        }
    }

    pub fn mul_pw(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut out = self.zero();
        self.mul_acc(&mut out, a, b);
        out
    }

    pub fn add_assign(&self, a: &mut [u64], b: &[u64]) {
        let n = self.n;
        for (k, &q) in self.qs.iter().enumerate() {
            for (x, &y) in a[k * n..(k + 1) * n].iter_mut().zip(&b[k * n..(k + 1) * n]) {
                *x = addmod(*x, y, q);
            }
        }
    }

    /// Signed small/medium coefficients to residues.
    pub fn from_signed(&self, c: &[i64]) -> Vec<u64> {
        let n = self.n;
        let mut out = self.zero();
        for (k, &q) in self.qs.iter().enumerate() {
            for i in 0..n {
                out[k * n + i] = from_i64(c[i], q);
            }
        }
        out
    }
}

impl Rns {
    /// The coefficient as an integer in [0, Q) (tests and dumps).
    pub fn crt_big(&self, res: &[u64]) -> BigUint {
        let mut s = BigUint::from(0u32);
        for k in 0..self.l() {
            s += BigUint::from(mulmod(res[k], self.inv_k[k], self.qs[k])) * &self.qhat[k];
        }
        s % &self.q_big
    }

    pub fn poly_big(&self, p: &[u64]) -> Vec<BigUint> {
        let (n, l) = (self.n, self.l());
        (0..n).map(|i| self.crt_big(&(0..l).map(|k| p[k * n + i]).collect::<Vec<_>>())).collect()
    }
}
