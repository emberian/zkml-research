//! cosnark_ext.py: challenges in F_{p^E}, E = profile EXT in {1, 2}. E = 2 is F_p[u] / (u^2 - NR), NR the least
//! quadratic non-residue >= 2 of p (3 for P_DEMO, 5 for P_LEDGER).
//!
//! Natively an element is `[u64; E]` (const generic E, so E = 1 compiles to the base-field code). Python's tuples carry
//! a STRUCTURAL length (1: known to be in F_p, E: challenge-born); natively a value of length 1 is stored with zero
//! upper components, which gives the same field values everywhere, and the structural length survives only where it
//! changes the protocol: the Beaver triple count of a shared product (`Tab::base`, `push_mul` / `take_mul`: 1, 2 or 3
//! triples in the harness's order).
use crate::field;
use crate::spdz::{lin2, shadd, shsub, Sh};
use crate::transcript::Transcript;
use rayon::prelude::*;

/// cosnark_ext.nr: the least quadratic non-residue >= 2 of the field modulus.
pub fn nr() -> u64 {
    match field::p() {
        field::P_DEMO => 3,
        field::P_LEDGER => 5,
        p => {
            let mut n = 2u64;
            while field::pow(n, (p - 1) / 2) != p - 1 {
                n += 1;
            }
            n
        }
    }
}

#[inline(always)]
pub fn zero<const E: usize>() -> [u64; E] {
    [0; E]
}

#[inline(always)]
pub fn lift<const E: usize>(x: u64) -> [u64; E] {
    let mut o = [0; E];
    o[0] = x;
    o
}

#[inline(always)]
pub fn one<const E: usize>() -> [u64; E] {
    lift(1)
}

#[inline(always)]
pub fn add<const E: usize>(a: [u64; E], b: [u64; E]) -> [u64; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = field::add(a[k], b[k]);
    }
    o
}

#[inline(always)]
pub fn sub<const E: usize>(a: [u64; E], b: [u64; E]) -> [u64; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = field::sub(a[k], b[k]);
    }
    o
}

#[inline(always)]
pub fn neg<const E: usize>(a: [u64; E]) -> [u64; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = field::neg(a[k]);
    }
    o
}

/// c (in F_p) times a.
#[inline(always)]
pub fn scal<const E: usize>(c: u64, a: [u64; E]) -> [u64; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = field::mul(c, a[k]);
    }
    o
}

#[inline(always)]
pub fn mul<const E: usize>(a: [u64; E], b: [u64; E]) -> [u64; E] {
    let mut o = [0; E];
    if E == 1 {
        o[0] = field::mul(a[0], b[0]);
    } else {
        o[0] = field::add(field::mul(a[0], b[0]), field::mul(nr(), field::mul(a[1], b[1])));
        o[1] = field::add(field::mul(a[0], b[1]), field::mul(a[1], b[0]));
    }
    o
}

pub fn inv<const E: usize>(a: [u64; E]) -> [u64; E] {
    let mut o = [0; E];
    if E == 1 {
        o[0] = field::inv(a[0]);
    } else {
        let nrm = field::sub(field::mul(a[0], a[0]), field::mul(nr(), field::mul(a[1], a[1])));
        let ni = field::inv(nrm);
        o[0] = field::mul(a[0], ni);
        o[1] = field::mul(field::neg(a[1]), ni);
    }
    o
}

#[inline(always)]
pub fn one_minus<const E: usize>(r: [u64; E]) -> [u64; E] {
    sub(one(), r)
}

/// sum x_i y_i (zip semantics: the shorter length).
pub fn dot<const E: usize>(a: &[[u64; E]], b: &[[u64; E]]) -> [u64; E] {
    a.iter().zip(b).fold(zero(), |acc, (&x, &y)| add(acc, mul(x, y)))
}

/// sum a_i b_i with a in F_p (zip semantics).
pub fn dot_base<const E: usize>(a: &[u64], b: &[[u64; E]]) -> [u64; E] {
    let mut o = [0; E];
    for k in 0..E {
        let bk: Vec<u64> = b.iter().take(a.len()).map(|v| v[k]).collect();
        let n = bk.len();
        o[k] = field::dot(&a[..n], &bk);
    }
    o
}

/// k challenges: ONE transcript call of E k draws, grouped consecutively.
pub fn chal<const E: usize>(tr: &mut Transcript, k: usize) -> Vec<[u64; E]> {
    let v = tr.chal(E * k);
    v.chunks(E).map(|c| c.try_into().unwrap()).collect()
}

/// chal::<E>(tr, k) one element at a time, the same values in the same order (no k-element table: at M = 52 the
/// middle's gamma is 70M elements, 1.1 GB at EXT = 2, and chal built a second, flat copy of it).
pub struct ChalStream<'a, const E: usize> {
    tr: &'a mut Transcript,
    i: u64,
    k: usize,
}

impl<'a, const E: usize> ChalStream<'a, E> {
    pub fn new(tr: &'a mut Transcript, k: usize) -> Self {
        ChalStream { tr, i: 0, k }
    }
    pub fn next(&mut self) -> [u64; E] {
        assert!((self.i as usize) < E * self.k, "the challenge stream is exhausted");
        std::array::from_fn(|_| {
            let v = self.tr.chal1_i(self.i);
            self.i += 1;
            v
        })
    }
    /// every element drawn (the transcript then stands where chal would leave it)
    pub fn done(&self) -> bool {
        self.i as usize == E * self.k
    }
}

pub fn chal1<const E: usize>(tr: &mut Transcript) -> [u64; E] {
    chal::<E>(tr, 1)[0]
}

/// eq(r, idx) over [0, 2^len(r)); bit k of idx pairs with r[k].
pub fn eqv<const E: usize>(r: &[[u64; E]]) -> Vec<[u64; E]> {
    let mut v = vec![one::<E>()];
    for &rk in r {
        let om = one_minus(rk);
        let mut nv = Vec::with_capacity(v.len() * 2);
        nv.par_extend(v.par_iter().map(|&x| mul(x, om)));
        nv.par_extend(v.par_iter().map(|&x| mul(x, rk)));
        v = nv;
    }
    v
}

pub fn mle<const E: usize>(vec: &[[u64; E]], r: &[[u64; E]]) -> [u64; E] {
    dot(vec, &eqv(r))
}

pub fn mle_base<const E: usize>(vec: &[u64], r: &[[u64; E]]) -> [u64; E] {
    dot_base(vec, &eqv(r))
}

/// Lagrange coefficients of the nodes 0..deg at r.
pub fn lagc<const E: usize>(deg: usize, r: [u64; E]) -> Vec<[u64; E]> {
    (0..=deg)
        .map(|i| {
            let mut num = one::<E>();
            let mut den = 1u64;
            for j in 0..=deg {
                if j != i {
                    num = mul(num, sub(r, lift(j as u64)));
                    den = field::mul(den, field::from_i64(i as i64 - j as i64));
                }
            }
            scal(field::inv(den), num)
        })
        .collect()
}

/// The polynomial through (j, vals[j]) at r.
pub fn interp_at<const E: usize>(vals: &[[u64; E]], r: [u64; E]) -> [u64; E] {
    dot(&lagc(vals.len() - 1, r), vals)
}

// ------------------------------------------------------------------------------- shared values (SPDZ shares)
pub const SZ: Sh = (0, 0);

#[inline(always)]
pub fn szero<const E: usize>() -> [Sh; E] {
    [SZ; E]
}

#[inline(always)]
pub fn slift<const E: usize>(x: Sh) -> [Sh; E] {
    let mut o = [SZ; E];
    o[0] = x;
    o
}

#[inline(always)]
pub fn sadd<const E: usize>(a: [Sh; E], b: [Sh; E]) -> [Sh; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = shadd(a[k], b[k]);
    }
    o
}

#[inline(always)]
pub fn ssub<const E: usize>(a: [Sh; E], b: [Sh; E]) -> [Sh; E] {
    let mut o = a;
    for k in 0..E {
        o[k] = shsub(a[k], b[k]);
    }
    o
}

/// c0 x + c1 y for base constants c0, c1 (componentwise).
#[inline(always)]
pub fn slin2b<const E: usize>(c0: u64, x: [Sh; E], c1: u64, y: [Sh; E]) -> [Sh; E] {
    let mut o = x;
    for k in 0..E {
        o[k] = lin2(c0, x[k], c1, y[k]);
    }
    o
}

#[inline(always)]
fn cm(c: u64, x: Sh) -> Sh {
    (field::mul(c, x.0), field::mul(c, x.1))
}

/// The public element c times the shared element x (local: shares and MAC shares are linear).
#[inline(always)]
pub fn scmul<const E: usize>(c: [u64; E], x: [Sh; E], nr: u64) -> [Sh; E] {
    let mut o = [SZ; E];
    if E == 1 {
        o[0] = cm(c[0], x[0]);
    } else {
        o[0] = shadd(cm(c[0], x[0]), cm(field::mul(nr, c[1]), x[1]));
        o[1] = shadd(cm(c[0], x[1]), cm(c[1], x[0]));
    }
    o
}

/// The same for share values alone (no MAC: the linear sumchecks' tables).
#[inline(always)]
pub fn ucmul<const E: usize>(c: [u64; E], x: [u64; E], nr: u64) -> [u64; E] {
    let mut o = [0; E];
    if E == 1 {
        o[0] = field::mul(c[0], x[0]);
    } else {
        o[0] = field::add(field::mul(c[0], x[0]), field::mul(field::mul(nr, c[1]), x[1]));
        o[1] = field::add(field::mul(c[0], x[1]), field::mul(c[1], x[0]));
    }
    o
}

/// Beaver triples of one shared product x y by the operands' structural lengths (xb, yb: base): 1, 2 or 3.
#[inline(always)]
pub fn mul_triples<const E: usize>(xb: bool, yb: bool) -> usize {
    if E == 1 {
        return 1;
    }
    match (xb, yb) {
        (true, true) => 1,
        (false, false) => 3,
        _ => 2,
    }
}

/// Queue the products' operand pairs of x y in the harness's triple order (cosnark_ext.smul): (1, 1) x0 y0;
/// (E, 1) x0 y0, x1 y0; (1, E) x0 y0, x0 y1; (E, E) x0 y0, x1 y1, (x0 + x1)(y0 + y1).
#[inline(always)]
pub fn push_mul<const E: usize>(x: [Sh; E], xb: bool, y: [Sh; E], yb: bool, xs: &mut Vec<Sh>, ys: &mut Vec<Sh>) {
    if E == 1 || (xb && yb) {
        xs.push(x[0]);
        ys.push(y[0]);
        return;
    }
    match (xb, yb) {
        (false, true) => {
            xs.extend([x[0], x[1]]);
            ys.extend([y[0], y[0]]);
        }
        (true, false) => {
            xs.extend([x[0], x[0]]);
            ys.extend([y[0], y[1]]);
        }
        _ => {
            xs.extend([x[0], x[1], shadd(x[0], x[1])]);
            ys.extend([y[0], y[1], shadd(y[0], y[1])]);
        }
    }
}

/// The product from its triples' results (push_mul's order); z = (P1 + NR P2, P3 - P1 - P2) for (E, E).
#[inline(always)]
pub fn take_mul<const E: usize>(xb: bool, yb: bool, p: &[Sh], nr: u64) -> [Sh; E] {
    let mut o = [SZ; E];
    if E == 1 || (xb && yb) {
        o[0] = p[0];
    } else if xb != yb {
        o[0] = p[0];
        o[1] = p[1];
    } else {
        o[0] = shadd(p[0], cm(nr, p[1]));
        o[1] = shsub(shsub(p[2], p[0]), p[1]);
    }
    o
}

/// A table of shared elements with its structural length: base (committed data) or E (folded by a challenge).
pub enum Tab<const E: usize> {
    B(Vec<Sh>),
    X(Vec<[Sh; E]>),
}

impl<const E: usize> Tab<E> {
    pub fn len(&self) -> usize {
        match self {
            Tab::B(v) => v.len(),
            Tab::X(v) => v.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Structurally in F_p (E = 1: always).
    pub fn base(&self) -> bool {
        E == 1 || matches!(self, Tab::B(_))
    }
    #[inline(always)]
    pub fn get(&self, k: usize) -> [Sh; E] {
        match self {
            Tab::B(v) => slift(v[k]),
            Tab::X(v) => v[k],
        }
    }
    /// (1 - r) T[2k] + r T[2k + 1].
    pub fn fold(&self, r: [u64; E]) -> Tab<E> {
        let om = one_minus(r);
        let nr = nr();
        match self {
            Tab::B(v) if E == 1 => Tab::B(v.par_chunks(2).map(|c| lin2(om[0], c[0], r[0], c[1])).collect()),
            Tab::B(v) => Tab::X(
                v.par_chunks(2)
                    .map(|c| {
                        let mut o = [SZ; E];
                        for k in 0..E {
                            o[k] = lin2(om[k], c[0], r[k], c[1]);
                        }
                        o
                    })
                    .collect(),
            ),
            Tab::X(v) => Tab::X(v.par_chunks(2).map(|c| sadd(scmul(om, c[0], nr), scmul(r, c[1], nr))).collect()),
        }
    }
}

/// This party's share values of an element: E ints.
#[inline(always)]
pub fn shares<const E: usize>(x: &[Sh; E]) -> [u64; E] {
    let mut o = [0; E];
    for k in 0..E {
        o[k] = x[k].0;
    }
    o
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nr_is_the_least_non_residue() {
        for q in [field::P_DEMO, field::P_LEDGER] {
            field::set_p(q);
            let mut n = 2u64;
            while field::pow(n, (q - 1) / 2) != q - 1 {
                n += 1;
            }
            assert_eq!(nr(), n);
            let a: [u64; 2] = [12345, 678910];
            assert_eq!(mul(a, inv(a)), one());
        }
        field::set_p(field::P_DEMO);
    }
}
