//! A single-process ideal execution of mpc_fork.run_step (plain SPDZ matvec and outer, as proofwire's verifier
//! replays it) that records what the proof consumes: every party's wires, the middle's preprocessing atoms (with
//! RecEngine's proof-only trh bits from random.Random(1)), the public transcript and the dealer's state after the
//! step. It mirrors the harness's draw order exactly, so at d = 4/16 its witness equals darkproof_vectors.py's,
//! and at d = 4096 (where Python never ran) it supplies the timing runs. It is a witness generator, not the
//! custodians' protocol (that is native/darkstep).
use crate::field;
use crate::spdz::{Dealer, Sh};
use crate::step::{StepParams, KAPPA};
use crate::witness::Witness;
use pycompat::PyRandom;
use std::collections::BTreeMap;

const N: usize = 3;
type V = [Sh; N];

struct Eng {
    dealer: Dealer,
    prng: PyRandom,
    /// "RS": K + 1 - s proof bits per truncation (cosnark_gates RecEngine.prep "trh")
    rs: bool,
    /// exact truncation (xtrunc.md): masks uniform in [0, p)
    xt: bool,
    public: Vec<u64>,
    atoms: Vec<V>,
}

fn lin(terms: &[(u64, &V)]) -> V {
    let mut o = [(0u64, 0u64); N];
    for &(c, x) in terms {
        if c == 0 {
            continue;
        }
        for i in 0..N {
            o[i].0 = field::add(o[i].0, field::mul(c, x[i].0));
            o[i].1 = field::add(o[i].1, field::mul(c, x[i].1));
        }
    }
    o
}

impl Eng {
    fn cadd(&self, c: u64, x: &V) -> V {
        let mut o = *x;
        o[0].0 = field::add(o[0].0, c);
        for i in 0..N {
            o[i].1 = field::add(o[i].1, field::mul(self.dealer.alpha_sh[i], c));
        }
        o
    }
    fn auth(&mut self, v: u64) -> V {
        let a = self.dealer.auth_all(v);
        [a[0], a[1], a[2]]
    }
    fn rec(&mut self, x: V) -> V {
        self.atoms.push(x);
        x
    }
    fn open(&mut self, x: &V) -> u64 {
        let v = x.iter().fold(0, |a, s| field::add(a, s.0));
        self.public.push(v);
        v
    }
    fn sub(x: &V, y: &V) -> V {
        let mut o = *x;
        for i in 0..N {
            o[i] = (field::sub(x[i].0, y[i].0), field::sub(x[i].1, y[i].1));
        }
        o
    }
    fn mul(&mut self, x: &V, y: &V) -> V {
        let av = self.dealer.rng.randrange_u64(field::p());
        let bv = self.dealer.rng.randrange_u64(field::p());
        let a = self.auth(av);
        let a = self.rec(a);
        let b = self.auth(bv);
        let b = self.rec(b);
        let c = self.auth(field::mul(av, bv));
        let c = self.rec(c);
        let e = self.open(&Self::sub(x, &a));
        let f = self.open(&Self::sub(y, &b));
        let s = lin(&[(1, &c), (e, &b), (f, &a)]);
        let ef = field::mul(e, f);
        if ef != 0 { self.cadd(ef, &s) } else { s }
    }
    fn input(&mut self, vals: &[u64], orng: &mut PyRandom) -> Vec<V> {
        vals.iter()
            .map(|&v| {
                let rv = orng.randrange_u64(field::p());
                let r = self.auth(rv);
                let c = field::sub(v, rv);
                self.public.push(c);
                self.cadd(c, &r)
            })
            .collect()
    }
    fn matvec(&mut self, w: &[V], v: &[V], d: usize, tp: bool) -> Vec<V> {
        let av: Vec<u64> = (0..d * d).map(|_| self.dealer.rng.randrange_u64(field::p())).collect();
        let bv: Vec<u64> = (0..d).map(|_| self.dealer.rng.randrange_u64(field::p())).collect();
        let a: Vec<V> = av.iter().map(|&x| self.auth(x)).collect();
        let b: Vec<V> = bv.iter().map(|&x| self.auth(x)).collect();
        let cvals: Vec<u64> = (0..d)
            .map(|i| (0..d).fold(0, |acc, r| field::add(acc, field::mul(if tp { av[r * d + i] } else { av[i * d + r] }, bv[r]))))
            .collect();
        let c: Vec<V> = cvals.iter().map(|&x| self.auth(x)).collect();
        let e: Vec<u64> = (0..d * d).map(|k| self.open(&Self::sub(&w[k], &a[k]))).collect();
        let f: Vec<u64> = (0..d).map(|r| self.open(&Self::sub(&v[r], &b[r]))).collect();
        use rayon::prelude::*;
        let alpha = self.dealer.alpha_sh.clone();
        (0..d)
            .into_par_iter()
            .map(|i| {
                let mut o = c[i];
                let mut cst = 0u64;
                for r in 0..d {
                    let (eir, air) = if tp { (e[r * d + i], &a[r * d + i]) } else { (e[i * d + r], &a[i * d + r]) };
                    for p in 0..N {
                        o[p].0 = field::add(o[p].0, field::add(field::mul(eir, b[r][p].0), field::mul(f[r], air[p].0)));
                        o[p].1 = field::add(o[p].1, field::add(field::mul(eir, b[r][p].1), field::mul(f[r], air[p].1)));
                    }
                    cst = field::add(cst, field::mul(eir, f[r]));
                }
                if cst != 0 {
                    o[0].0 = field::add(o[0].0, cst);
                    for p in 0..N {
                        o[p].1 = field::add(o[p].1, field::mul(alpha[p], cst));
                    }
                }
                o
            })
            .collect()
    }
    fn outer(&mut self, a: &[V], x: &[V]) -> Vec<V> {
        let (d1, d2) = (a.len(), x.len());
        let uv: Vec<u64> = (0..d1).map(|_| self.dealer.rng.randrange_u64(field::p())).collect();
        let wv: Vec<u64> = (0..d2).map(|_| self.dealer.rng.randrange_u64(field::p())).collect();
        let u: Vec<V> = uv.iter().map(|&x| self.auth(x)).collect();
        let w: Vec<V> = wv.iter().map(|&x| self.auth(x)).collect();
        let mut uw = Vec::with_capacity(d1 * d2);
        for i in 0..d1 {
            for j in 0..d2 {
                uw.push(self.auth(field::mul(uv[i], wv[j])));
            }
        }
        let e: Vec<u64> = (0..d1).map(|i| self.open(&Self::sub(&a[i], &u[i]))).collect();
        let f: Vec<u64> = (0..d2).map(|j| self.open(&Self::sub(&x[j], &w[j]))).collect();
        let mut out = Vec::with_capacity(d1 * d2);
        for i in 0..d1 {
            for j in 0..d2 {
                let s = lin(&[(1, &uw[i * d2 + j]), (e[i], &w[j]), (f[j], &u[i])]);
                let ef = field::mul(e[i], f[j]);
                out.push(if ef != 0 { self.cadd(ef, &s) } else { s });
            }
        }
        out
    }
    fn trunc(&mut self, x: &V, s: u32, k: u32) -> V {
        let rv = if self.xt { self.dealer.rng.randbelow_u64(field::p()) } else { self.dealer.rng.randbelow_u64(1u64 << (k + KAPPA)) };
        let r = self.auth(rv);
        let r = self.rec(r);
        let mut bits = Vec::with_capacity(s as usize);
        for i in 0..s {
            let b = self.auth((rv >> i) & 1);
            bits.push(self.rec(b));
        }
        let rhi = self.auth(rv >> s);
        let rhi = self.rec(rhi);
        let val = rv >> s;
        for j in 0..if self.rs { k + 1 - s } else { k + KAPPA - s } {
            let v = (val >> j) & 1;
            let xs: Vec<u64> = (0..N - 1).map(|_| self.prng.randrange_u64(field::p())).collect();
            let ms: Vec<u64> = (0..N - 1).map(|_| self.prng.randrange_u64(field::p())).collect();
            let lx = field::sub(v, xs.iter().fold(0, |a, &b| field::add(a, b)));
            let lm = field::sub(field::mul(self.dealer.alpha, v), ms.iter().fold(0, |a, &b| field::add(a, b)));
            self.atoms.push([(xs[0], ms[0]), (xs[1], ms[1]), (lx, lm)]);
        }
        let c = self.open(&self.cadd(1u64 << k, &lin(&[(1, x), (1, &r)])));
        let clow = c & ((1u64 << s) - 1);
        let a: Vec<u64> = (0..s).map(|i| (clow >> i) & 1).collect();
        let eq: Vec<V> = (0..s as usize)
            .map(|j| {
                let e = lin(&[(field::from_i64(1 - 2 * a[j] as i64), &bits[j])]);
                let e = if a[j] != 0 { self.cadd(a[j], &e) } else { e };
                let e2 = lin(&[(field::p() - 1, &e)]);
                self.cadd(1, &e2)
            })
            .collect();
        let mut borrow: Option<V> = None;
        let mut prefix: Option<V> = None;
        for i in (0..s as usize).rev() {
            let mut term = lin(&[(1 - a[i], &bits[i])]);
            if let Some(pf) = prefix {
                term = self.mul(&term, &pf);
            }
            borrow = Some(match borrow {
                None => term,
                Some(b) => lin(&[(1, &b), (1, &term)]),
            });
            prefix = Some(match prefix {
                None => eq[i],
                Some(pf) => self.mul(&pf, &eq[i]),
            });
        }
        let q = field::from_i64((c >> s) as i64 - (1i64 << (k - s)));
        let o = lin(&[(field::p() - 1, &rhi), (field::p() - 1, &borrow.unwrap())]);
        if q != 0 { self.cadd(q, &o) } else { o }
    }
    fn lookup2(&mut self, u: &V, offset: u64, tables: &(Vec<u64>, Vec<u64>)) -> (V, V) {
        let rv = self.dealer.rng.randrange_u64(field::p());
        let mut pw = Vec::with_capacity(255);
        for j in 1..=255u64 {
            let a = self.auth(field::pow(rv, j));
            pw.push(self.rec(a));
        }
        let c = self.open(&Self::sub(&self.cadd(offset, u), &pw[0]));
        let mk = |me: &Self, coeffs: &[u64]| -> V {
            let tay = crate::step::taylor_shift(coeffs, c);
            let terms: Vec<(u64, &V)> = (1..tay.len()).map(|j| (tay[j], &pw[j - 1])).collect();
            let o = lin(&terms);
            if tay[0] != 0 { me.cadd(tay[0], &o) } else { o }
        };
        (mk(self, &tables.0), mk(self, &tables.1))
    }
}

/// The harness's inputs for width d: random.Random(d), randint(-7, 7) for W1, W2, x, y.
pub fn harness_inputs(d: usize) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>) {
    let mut r = PyRandom::from_u64(d as u64);
    let mut m = |k: usize| -> Vec<u64> { (0..k).map(|_| field::from_i64(r.randint_i64(-7, 7))).collect() };
    let w1 = m(d * d);
    let w2 = m(d * d);
    let x = m(d);
    let y = m(d);
    (w1, w2, x, y)
}

/// mpc_fork.run_step under spdz.Dealer(p, 3, 5), owner seed 9, RecEngine seed 1.
pub fn run_step(w1: &[u64], w2: &[u64], x: &[u64], y: &[u64], d: usize, prm: StepParams, tables: &(Vec<u64>, Vec<u64>)) -> Witness {
    let mut e = Eng { dealer: Dealer::from_seed(5, N), prng: PyRandom::from_u64(1), rs: prm.rs, xt: prm.xt, public: Vec::new(), atoms: Vec::new() };
    let mut orng = PyRandom::from_u64(9);
    let sw1 = e.input(w1, &mut orng);
    let sw2 = e.input(w2, &mut orng);
    let sx = e.input(x, &mut orng);
    let sy = e.input(y, &mut orng);
    let z1 = e.matvec(&sw1, &sx, d, false);
    let u1: Vec<V> = z1.iter().map(|z| e.trunc(z, prm.s1, prm.k1)).collect();
    let hg: Vec<(V, V)> = u1.iter().map(|u| e.lookup2(u, 128, tables)).collect();
    let h: Vec<V> = hg.iter().map(|t| t.0).collect();
    let g1: Vec<V> = hg.iter().map(|t| t.1).collect();
    let z2 = e.matvec(&sw2, &h, d, false);
    let ev: Vec<V> = z2.iter().zip(&sy).map(|(z, yy)| {
        let t = e.trunc(z, prm.s1, prm.k1);
        Eng::sub(&t, yy)
    }).collect();
    let d2: Vec<V> = ev.iter().map(|v| e.trunc(v, prm.s2, prm.k2)).collect();
    let b = e.matvec(&sw2, &d2, d, true);
    let bg: Vec<V> = b.iter().zip(&g1).map(|(bb, g)| e.mul(bb, g)).collect();
    let d1: Vec<V> = bg.iter().map(|v| e.trunc(v, prm.s3, prm.k3)).collect();
    let mut wires: Vec<BTreeMap<String, Vec<Sh>>> = vec![BTreeMap::new(); N];
    let put = |wires: &mut Vec<BTreeMap<String, Vec<Sh>>>, k: &str, v: Vec<V>| {
        for (i, m) in wires.iter_mut().enumerate() {
            m.insert(k.to_string(), v.iter().map(|x| x[i]).collect());
        }
    };
    let g2 = e.outer(&d2, &h);
    let w2n: Vec<V> = sw2.iter().zip(&g2).map(|(a, b)| Eng::sub(a, b)).collect();
    drop(g2);
    put(&mut wires, "W2n", w2n);
    let g1o = e.outer(&d1, &sx);
    let w1n: Vec<V> = sw1.iter().zip(&g1o).map(|(a, b)| Eng::sub(a, b)).collect();
    drop(g1o);
    put(&mut wires, "W1n", w1n);
    put(&mut wires, "W1", sw1);
    put(&mut wires, "W2", sw2);
    for (k, v) in [("x", sx), ("y", sy), ("z1", z1), ("h", h), ("z2", z2), ("d2", d2), ("b", b), ("g1", g1), ("bg", bg), ("d1", d1)] {
        put(&mut wires, k, v);
    }
    Witness {
        d,
        n: N,
        alpha_sh: e.dealer.alpha_sh.clone(),
        dealer_state: e.dealer.rng.state(),
        wires,
        public: e.public,
        atoms: (0..N).map(|i| e.atoms.iter().map(|x| x[i]).collect()).collect(),
    }
}
