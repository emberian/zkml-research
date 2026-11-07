//! Negacyclic NTT over Z_q[X]/(X^N + 1) (Cooley-Tukey forward, Gentleman-Sande inverse, Shoup twiddles).
use crate::arith::*;

pub struct Ntt {
    pub q: u64,
    pub n: usize,
    psi: Vec<u64>,
    psi_s: Vec<u64>,
    ipsi: Vec<u64>,
    ipsi_s: Vec<u64>,
    ninv: u64,
    ninv_s: u64,
}

fn bitrev(x: usize, bits: u32) -> usize {
    if bits == 0 { 0 } else { x.reverse_bits() >> (usize::BITS - bits) }
}

impl Ntt {
    pub fn new(q: u64, n: usize) -> Self {
        assert!(n.is_power_of_two() && (q - 1) % (2 * n as u64) == 0);
        let mut psi0 = 0;
        for g in 2u64.. {
            let c = powmod(g, (q - 1) / (2 * n as u64), q);
            if powmod(c, n as u64, q) == q - 1 {
                psi0 = c;
                break;
            }
        }
        let ipsi0 = invmod(psi0, q);
        let bits = n.trailing_zeros();
        let mut psi = vec![0u64; n];
        let mut ipsi = vec![0u64; n];
        for k in 0..n {
            let e = bitrev(k, bits) as u64;
            psi[k] = powmod(psi0, e, q);
            ipsi[k] = powmod(ipsi0, e, q);
        }
        let psi_s = psi.iter().map(|&w| shoup(w, q)).collect();
        let ipsi_s = ipsi.iter().map(|&w| shoup(w, q)).collect();
        let ninv = invmod(n as u64, q);
        Ntt { q, n, psi, psi_s, ipsi, ipsi_s, ninv, ninv_s: shoup(ninv, q) }
    }

    pub fn forward(&self, a: &mut [u64]) {
        let (q, n) = (self.q, self.n);
        let mut t = n;
        let mut m = 1;
        while m < n {
            t >>= 1;
            for i in 0..m {
                let j1 = 2 * i * t;
                let (w, ws) = (self.psi[m + i], self.psi_s[m + i]);
                let (lo, hi) = a[j1..j1 + 2 * t].split_at_mut(t);
                for (u, v) in lo.iter_mut().zip(hi.iter_mut()) {
                    let x = *u;
                    let y = mulmod_shoup(*v, w, ws, q);
                    *u = addmod(x, y, q);
                    *v = submod(x, y, q);
                }
            }
            m <<= 1;
        }
    }

    pub fn inverse(&self, a: &mut [u64]) {
        let (q, n) = (self.q, self.n);
        let mut t = 1;
        let mut m = n;
        while m > 1 {
            let h = m >> 1;
            let mut j1 = 0;
            for i in 0..h {
                let (w, ws) = (self.ipsi[h + i], self.ipsi_s[h + i]);
                let (lo, hi) = a[j1..j1 + 2 * t].split_at_mut(t);
                for (u, v) in lo.iter_mut().zip(hi.iter_mut()) {
                    let x = *u;
                    let y = *v;
                    *u = addmod(x, y, q);
                    *v = mulmod_shoup(submod(x, y, q), w, ws, q);
                }
                j1 += 2 * t;
            }
            t <<= 1;
            m = h;
        }
        for x in a.iter_mut() {
            *x = mulmod_shoup(*x, self.ninv, self.ninv_s, q);
        }
    }
}
