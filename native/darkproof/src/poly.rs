//! cozk.py's polynomial helpers over F_p (coefficient vectors, lowest degree first). Lengths follow Python exactly:
//! no trimming of leading zeros anywhere, because message lengths are part of the wire schema.
use crate::field::{self, P};

pub fn pmul(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let n = a.len() + b.len() - 1;
    let mut acc = vec![0u128; n];
    let mut out = vec![0u64; n];
    // lazy reduction: accumulate up to 32 products per slot between folds
    for (blk, ca) in a.chunks(32).enumerate() {
        for (ii, &x) in ca.iter().enumerate() {
            if x == 0 {
                continue;
            }
            let i = blk * 32 + ii;
            for (j, &y) in b.iter().enumerate() {
                acc[i + j] += x as u128 * y as u128;
            }
        }
        for k in 0..n {
            if acc[k] != 0 {
                out[k] = field::add(out[k], field::red(acc[k]));
                acc[k] = 0;
            }
        }
    }
    out
}

pub fn padd(a: &[u64], b: &[u64]) -> Vec<u64> {
    let n = a.len().max(b.len());
    (0..n).map(|i| field::add(*a.get(i).unwrap_or(&0), *b.get(i).unwrap_or(&0))).collect()
}

pub fn padd_into(acc: &mut Vec<u64>, b: &[u64]) {
    if acc.len() < b.len() {
        acc.resize(b.len(), 0);
    }
    for (x, &y) in acc.iter_mut().zip(b) {
        *x = field::add(*x, y);
    }
}

/// acc += c * b (lengths extend like padd).
pub fn paxpy(acc: &mut Vec<u64>, c: u64, b: &[u64]) {
    if acc.len() < b.len() {
        acc.resize(b.len(), 0);
    }
    for (x, &y) in acc.iter_mut().zip(b) {
        *x = field::add(*x, field::mul(c, y));
    }
}

pub fn pscale(c: u64, a: &[u64]) -> Vec<u64> {
    a.iter().map(|&x| field::mul(c, x)).collect()
}

pub fn peval(a: &[u64], x: u64) -> u64 {
    let mut acc = 0u64;
    for &c in a.iter().rev() {
        acc = field::add(field::mul(acc, x), c);
    }
    acc
}

/// Coefficient vectors of the Lagrange basis polynomials on `nodes`.
pub fn lagrange_basis(nodes: &[u64]) -> Vec<Vec<u64>> {
    let mut m = vec![1u64];
    for &z in nodes {
        m = pmul(&m, &[field::neg(z), 1]);
    }
    nodes
        .iter()
        .map(|&z| {
            let mut q = vec![0u64; m.len() - 1];
            let mut carry = 0u64;
            for i in (1..m.len()).rev() {
                carry = field::add(m[i], field::mul(carry, z));
                q[i - 1] = carry;
            }
            let den = peval(&q, z);
            pscale(field::inv(den), &q)
        })
        .collect()
}

/// Powers x^0..x^(n-1).
pub fn powers(x: u64, n: usize) -> Vec<u64> {
    let mut out = Vec::with_capacity(n);
    let mut v = 1u64;
    for _ in 0..n {
        out.push(v);
        v = field::mul(v, x);
    }
    out
}

/// sum_i vals[i] * basis[i] (coefficient vectors of equal length).
pub fn combine(vals: &[u64], basis: &[Vec<u64>], len: usize) -> Vec<u64> {
    let mut acc = vec![0u128; len];
    let mut out = vec![0u64; len];
    for (blk, (cv, cb)) in vals.chunks(32).zip(basis.chunks(32)).enumerate() {
        let _ = blk;
        for (&v, l) in cv.iter().zip(cb) {
            if v == 0 {
                continue;
            }
            for (a, &c) in acc.iter_mut().zip(l) {
                *a += v as u128 * c as u128;
            }
        }
        for k in 0..len {
            out[k] = field::add(out[k], field::red(acc[k]));
            acc[k] = 0;
        }
    }
    out
}

pub const fn p() -> u64 {
    P
}
