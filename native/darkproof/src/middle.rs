//! cosnark_gates_zk.py: the middle (SPDZ execution integrity of the nonlinear gates) with ZK layers 2-3.
//! `prove` is ONE custodian's prover; `verify` the public verifier. The constraint system comes from the
//! verifier's own symbolic replay of the step (`step::replay`). Generic over the challenges' field F_{p^E} (cosnark_ext).
use crate::ext::{self, Tab};
use crate::field;
use crate::h::Hash;
use crate::ligero::{self, LigParams, LigParty, LigProof, LinSink, LinSystem};
use crate::net::{gather_hashes, Net};
use crate::pcs::{self, colsums, PcsCols, PcsParty, Shape};
use crate::rng::Det;
use crate::spdz::{Sh, Spdz};
use crate::spine::{self, operands, prod_forms, public_digest, rc, y_form, EEm, EvalsE, Sc};
use crate::step::{Atom, Io, Rec, NAMES};
use crate::transcript::Transcript;
use crate::{Ctx, Profile};
use rayon::prelude::*;
use std::collections::BTreeMap;

pub const SPINE: [&str; 8] = ["z1", "z2", "b", "h", "g1", "d2", "bg", "d1"];

#[derive(Clone, Debug, PartialEq)]
pub struct MiddleProof {
    pub roots: BTreeMap<String, Vec<Hash>>,
    pub zc_roots: Vec<Vec<Hash>>,
    pub claims_root: Vec<Hash>,
    pub lsc_roots: Vec<Vec<Hash>>,
    pub eval_roots: Vec<Hash>,
    pub mask_roots: Vec<Hash>,
    pub prox: BTreeMap<String, Vec<Vec<u64>>>,
    pub pcs_cols: BTreeMap<String, PcsCols>,
    pub ligero: LigProof,
}

pub fn plen(x: usize) -> usize {
    x.max(1).next_power_of_two()
}

fn lg(x: usize) -> usize {
    pcs::bitlen(x - 1)
}

/// public_shapes: the batch vectors' lengths and every commitment's shape (with the owner's "yo" when bound).
pub fn public_shapes(
    pr: &Profile,
    n_prep: usize,
    n_had: usize,
    d: usize,
    bind: bool,
) -> (BTreeMap<String, usize>, BTreeMap<String, Shape>) {
    public_shapes_io(pr, n_prep, n_had, d, bind, None)
}

/// public_shapes for a program's external vectors (io; None: the step's NAMES, SPINE carried).
pub fn public_shapes_io(
    pr: &Profile,
    n_prep: usize,
    n_had: usize,
    d: usize,
    bind: bool,
    io: Option<&Io>,
) -> (BTreeMap<String, usize>, BTreeMap<String, Shape>) {
    let mut lens = BTreeMap::new();
    lens.insert("P".to_string(), plen(n_prep));
    for k in ["A", "B", "C"] {
        lens.insert(k.to_string(), plen(n_had));
    }
    match io {
        None => {
            for nm in NAMES {
                lens.insert(nm.to_string(), plen(d));
            }
        }
        Some(io) => {
            for (nm, l) in &io.lens {
                lens.insert(nm.to_string(), *l);
            }
        }
    }
    let carried: Vec<&str> = io.map(|io| io.carried.clone()).unwrap_or_else(|| SPINE.to_vec());
    let block = if pr.nmask > 0 { pr.nmask / pr.lives } else { 0 };
    let mut sh: BTreeMap<String, Shape> = lens
        .iter()
        .map(|(k, &l)| (k.clone(), Shape::new(pr, lg(l), if carried.contains(&k.as_str()) { block } else { 0 })))
        .collect();
    if bind {
        sh.insert("yo".into(), Shape::new(pr, lg(plen(d)), 0));
    }
    (lens, sh)
}

/// build_q: the batched linear functional per vector, and its constant, for F_{p^E} gammas (an untouched entry
/// stays zero).
#[allow(clippy::type_complexity)]
pub fn build_q<const E: usize>(
    rec: &Rec,
    lens: &BTreeMap<String, usize>,
    gam: &[[u64; E]],
) -> (BTreeMap<String, Vec<[u64; E]>>, [u64; E]) {
    let mut q: BTreeMap<String, Vec<[u64; E]>> = lens.iter().map(|(k, &l)| (k.clone(), vec![[0u64; E]; l])).collect();
    let mut cst = ext::zero::<E>();
    let nc = rec.cons.len();
    {
        let mut qn: Vec<Vec<[u64; E]>> = rec.names.iter().map(|nm| std::mem::take(q.get_mut(*nm).unwrap())).collect();
        let qp = q.get_mut("P").unwrap();
        for (g, con) in gam.iter().zip(&rec.cons) {
            for &(a, co) in &con.form.terms {
                let v = ext::scal(co, *g);
                match a {
                    Atom::Ext(nm, k) => {
                        let s = &mut qn[nm as usize][k as usize];
                        *s = ext::add(*s, v);
                    }
                    Atom::Prep(pos) => {
                        let s = &mut qp[pos as usize];
                        *s = ext::add(*s, v);
                    }
                }
            }
            cst = ext::add(cst, ext::scal(field::sub(con.form.c, con.value), *g));
        }
        if let Some(pm) = &rec.pubmat {
            // z1[j M + t] - sum_k X[k][t] W1[j d + k], with gamma at start + j M + t
            let (d, m) = (pm.d, pm.m);
            let g = &gam[pm.start..pm.start + d * m];
            let qz = &mut qn[pm.z1 as usize];
            for (k, gv) in g.iter().enumerate() {
                qz[k] = ext::add(qz[k], *gv);
            }
            let qw = &mut qn[pm.w1 as usize];
            qw[..d * d].par_chunks_mut(d).enumerate().for_each(|(j, row)| {
                let gj = &g[j * m..(j + 1) * m];
                for (k, s) in row.iter_mut().enumerate() {
                    let v = ext::dot_base(&pm.x[k * m..(k + 1) * m], gj);
                    *s = ext::sub(*s, v);
                }
            });
        }
        for (nm, v) in rec.names.iter().zip(qn) {
            *q.get_mut(*nm).unwrap() = v;
        }
    }
    let g3 = &gam[nc..];
    for (k, &(a, b, c)) in rec.had.iter().enumerate() {
        for (j, (vn, at)) in [("A", a), ("B", b), ("C", c)].iter().enumerate() {
            let g = g3[3 * k + j];
            let s = &mut q.get_mut(*vn).unwrap()[k];
            *s = ext::add(*s, g);
            let s = &mut q.get_mut("P").unwrap()[*at as usize];
            *s = ext::sub(*s, g);
        }
    }
    (q, cst)
}

pub fn evaluations<const E: usize>(
    lens: &BTreeMap<String, usize>,
    zrs: &[[u64; E]],
    rr: &[[u64; E]],
    rb: Option<&[[u64; E]]>,
) -> EvalsE<E> {
    let mut ev: EvalsE<E> = vec![("A".into(), zrs.to_vec()), ("B".into(), zrs.to_vec()), ("C".into(), zrs.to_vec())];
    for (k, &l) in lens {
        ev.push((k.clone(), rr[..lg(l)].to_vec()));
    }
    if let Some(rb) = rb {
        ev.push(("yo".into(), rb.to_vec()));
        ev.push(("y".into(), rb.to_vec()));
    }
    ev
}

pub struct MLayout {
    pub zrows: Vec<usize>,
    pub crow: usize,
    pub lrows: Vec<usize>,
    pub urows: Vec<Vec<usize>>,
    pub prod: (usize, usize, usize),
    pub nrows: usize,
}

/// Row numbering: zerocheck rounds, the claims row, the linear rounds (a value j, component k at j E + k), every
/// evaluation's u rows (E component blocks), the product rows.
pub fn row_layout<T>(sh: &BTreeMap<String, Shape>, ev: &[(String, T)], lh: usize, lmax: usize, kl: usize, e: usize) -> MLayout {
    let mut nxt = 0;
    let zrows = (nxt..nxt + lh).collect();
    nxt += lh;
    let crow = nxt;
    nxt += 1;
    let lrows = (nxt..nxt + lmax).collect();
    nxt += lmax;
    let mut urows = Vec::new();
    for (k, _) in ev {
        let nr = sh[k].w.div_ceil(kl);
        urows.push((nxt..nxt + e * nr).collect());
        nxt += e * nr;
    }
    MLayout { zrows, crow, lrows, urows, prod: (nxt, nxt + 1, nxt + 2), nrows: nxt + 3 }
}

pub struct MiddleSys<const E: usize> {
    pub kl: usize,
    pub ev: EvalsE<E>,
    pub shapes: Vec<Shape>,
    pub cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    pub lay: MLayout,
    pub tau: Vec<[u64; E]>,
    pub zrs: Vec<[u64; E]>,
    pub rr: Vec<[u64; E]>,
    pub ks: Vec<String>,
    /// per k in ks: the final coefficient mle(q_pad)(rr) * prod_{j >= m} (1 - r_j)
    pub coef: Vec<[u64; E]>,
    pub cst: [u64; E],
}

impl<const E: usize> MiddleSys<E> {
    fn y(&self, em: &mut EEm<E>, e: usize, coef: [u64; E]) {
        y_form(em, &self.ev, &self.shapes, &self.lay.urows, self.kl, e, coef);
    }
}

impl<const E: usize> LinSystem for MiddleSys<E> {
    fn emit(&self, sink: &mut dyn LinSink) {
        spine::pcs_consistency_e(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.lay.urows);
        let mut em = EEm::<E>::new(sink);
        let one = ext::one::<E>();
        let m1 = ext::neg(one);
        let zero = ext::zero::<E>();
        let pf = prod_forms::<E>(self.lay.prod, 0);
        let z = &self.lay.zrows;
        rc(&mut em, z[0], 0, one);
        rc(&mut em, z[0], 1, one);
        em.done("Hadamard zerocheck: round sums", zero);
        for i in 1..z.len() {
            let lc = ext::lagc(3, self.zrs[i - 1]);
            rc(&mut em, z[i], 0, one);
            rc(&mut em, z[i], 1, one);
            for j in 0..4 {
                rc(&mut em, z[i - 1], j, ext::neg(lc[j]));
            }
            em.done("Hadamard zerocheck: round sums", zero);
        }
        let lc = ext::lagc(3, *self.zrs.last().unwrap());
        let eq = ext::mle(&ext::eqv(&self.tau), &self.zrs);
        for j in 0..4 {
            rc(&mut em, *z.last().unwrap(), j, lc[j]);
        }
        em.form(&pf.z, ext::neg(eq));
        self.y(&mut em, 2, eq);
        em.done("Hadamard zerocheck: final = eq (A B - C)", zero);
        operands(&mut em, &pf, "product operands", "product operand sums", &|em| self.y(em, 0, m1), &|em| self.y(em, 1, m1));
        for i in 0..self.ks.len() {
            rc(&mut em, self.lay.crow, i, one);
        }
        em.done("linear batch: openings/IO/copy constraints", ext::neg(self.cst));
        let l = &self.lay.lrows;
        for (i, k) in self.ks.iter().enumerate() {
            let lab = format!("linear sumcheck {k}");
            rc(&mut em, l[0], 3 * i, one);
            rc(&mut em, l[0], 3 * i + 1, one);
            rc(&mut em, self.lay.crow, i, m1);
            em.done(&lab, zero);
            for r in 1..l.len() {
                let lc = ext::lagc(2, self.rr[r - 1]);
                rc(&mut em, l[r], 3 * i, one);
                rc(&mut em, l[r], 3 * i + 1, one);
                for j in 0..3 {
                    rc(&mut em, l[r - 1], 3 * i + j, ext::neg(lc[j]));
                }
                em.done(&lab, zero);
            }
            let lc = ext::lagc(2, *self.rr.last().unwrap());
            for j in 0..3 {
                rc(&mut em, *l.last().unwrap(), 3 * i + j, lc[j]);
            }
            self.y(&mut em, 3 + i, ext::neg(self.coef[i]));
            em.done(&format!("linear sumcheck {k}: final"), zero);
        }
        if self.ev.len() == 3 + self.ks.len() + 2 {
            let e = self.ev.len();
            self.y(&mut em, e - 2, one);
            self.y(&mut em, e - 1, m1);
            em.done("signed input binding: the custodians' y = the owner's signed y", zero);
        }
    }
}

/// The final coefficients of the lockstep linear sumchecks.
fn final_coefs<const E: usize>(q: &BTreeMap<String, Vec<[u64; E]>>, lens: &BTreeMap<String, usize>, rr: &[[u64; E]]) -> Vec<[u64; E]> {
    let e = ext::eqv(rr);
    lens.iter()
        .map(|(k, &l)| {
            let mut c = ext::dot(&q[k], &e[..l]);
            for &rj in &rr[lg(l)..] {
                c = ext::mul(c, ext::one_minus(rj));
            }
            c
        })
        .collect()
}

pub struct MiddleIn<'a> {
    pub pr: &'a Profile,
    pub lp: &'a LigParams,
    pub i: usize,
    pub n: usize,
    pub d: usize,
    /// this party's shares of the middle's preprocessing atoms, in the replay's order
    pub atoms: &'a [Sh],
    /// this party's shares of the spine vectors (NAMES)
    pub wires: &'a BTreeMap<String, Vec<Sh>>,
    pub rec: &'a Rec<'a>,
    pub public: &'a [u64],
    pub ctx: &'a Ctx,
    pub det: &'a Det,
    /// the ideal dealer's stream for the Ligero's triples (real runs; identical for every party)
    pub lig_dealer: Option<pycompat::PyRandom>,
    /// the deployed run: this party's tape triples for the Ligero's products (overrides lig_dealer)
    pub lig_tape: Option<Vec<(u64, u64, u64)>>,
    /// TEST ONLY: prove even when a truncation input is outside its proved bound (the forced-bundle refusal rows)
    pub ignore_range: bool,
    /// ATTACK HOOK (fs_public_falsifier; EXT = 1 only): colluders rewrite the batch constant after seeing gamma
    pub cst_patch: Option<&'a (dyn Fn(&BTreeMap<String, Vec<u64>>, u64, &[u64]) -> u64 + Sync)>,
}

/// Plain (unauthenticated) products in the middle's Ligero at EXT = 1: the zerocheck's final product.
pub const LIG_SCALARS: usize = 1;

/// The middle Ligero's plain products under EXT = e (three at e = 2: P1, P2, P3).
pub fn lig_scalars(e: usize) -> usize {
    LIG_SCALARS * if e == 1 { 1 } else { 3 }
}

pub struct MiddleOut {
    pub proof: MiddleProof,
    pub lig_rows: Vec<Vec<u64>>,
    pub sys: Box<dyn LinSystem + Send>,
    pub quad: Vec<(usize, usize, usize)>,
    pub stats: BTreeMap<String, u64>,
}

fn padv(v: &[Sh], l: usize) -> Vec<Sh> {
    let mut o = v.to_vec();
    o.resize(l, (0, 0));
    o
}

/// One zerocheck round with one product per live pair (1 or 3 Beaver triples: round 0's tables are base, later
/// rounds' are folded by F_{p^E} challenges): the round's values at X = 0..3 and every pair's products at X = 0, 1, 2.
#[allow(clippy::type_complexity)]
fn zc_round<const E: usize>(
    sp: &mut Spdz,
    net: &mut dyn Net,
    st: &Sc<E>,
    prev: &Tab<E>,
    live: usize,
) -> (Vec<[Sh; E]>, Vec<[[Sh; E]; 3]>) {
    let half = st.f.len() / 2;
    let na = live.div_ceil(2).min(half);
    let m1 = field::p() - 1;
    let nr = ext::nr();
    let (fb, gb) = (st.f.base(), st.g.base());
    let per = ext::mul_triples::<E>(fb, gb);
    let ops: Vec<([Sh; E], [Sh; E])> = (0..na)
        .into_par_iter()
        .map(|k| (ext::slin2b(m1, st.f.get(2 * k), 2, st.f.get(2 * k + 1)), ext::slin2b(m1, st.g.get(2 * k), 2, st.g.get(2 * k + 1))))
        .collect();
    let (mut xs, mut ys) = (Vec::with_capacity(na * per), Vec::with_capacity(na * per));
    for (x, y) in ops {
        ext::push_mul(x, fb, y, gb, &mut xs, &mut ys);
    }
    let p2 = sp.mul_batch(net, &xs, &ys);
    drop(xs);
    drop(ys);
    let pp: Vec<[[Sh; E]; 3]> = (0..half)
        .into_par_iter()
        .map(|k| {
            let c = if k < na { ext::take_mul::<E>(fb, gb, &p2[k * per..(k + 1) * per], nr) } else { ext::szero() };
            [prev.get(2 * k), prev.get(2 * k + 1), c]
        })
        .collect();
    drop(p2);
    let sub = st.sub.as_ref().unwrap();
    let eq = st.eq.as_ref().unwrap();
    let vals = (0..4u64)
        .map(|xv| {
            let om = field::one_minus(xv);
            (0..half)
                .into_par_iter()
                .map(|k| {
                    let [a, b, c] = pp[k];
                    let prod = match xv {
                        0 => a,
                        1 => b,
                        2 => c,
                        _ => ext::sadd(ext::slin2b(1, a, m1 - 2, b), ext::slin2b(3, c, 0, c)),
                    };
                    let term = ext::ssub(prod, ext::slin2b(om, sub.get(2 * k), xv, sub.get(2 * k + 1)));
                    let e = ext::add(ext::scal(om, eq[2 * k]), ext::scal(xv, eq[2 * k + 1]));
                    ext::scmul(e, term, nr)
                })
                .reduce(ext::szero::<E>, ext::sadd)
        })
        .collect();
    (vals, pp)
}

/// A share-only table of the linear sumchecks (never multiplied: no MACs): base, or folded by F_{p^E} challenges.
enum UT<const E: usize> {
    B(Vec<u64>),
    X(Vec<[u64; E]>),
}

impl<const E: usize> UT<E> {
    #[inline(always)]
    fn get(&self, k: usize) -> [u64; E] {
        match self {
            UT::B(v) => v.get(k).map_or([0; E], |&x| ext::lift(x)),
            UT::X(v) => v.get(k).copied().unwrap_or([0; E]),
        }
    }
    fn len(&self) -> usize {
        match self {
            UT::B(v) => v.len(),
            UT::X(v) => v.len(),
        }
    }
    fn fold(&self, r: [u64; E], nr: u64) -> UT<E> {
        let om = ext::one_minus(r);
        let n = self.len().div_ceil(2);
        match self {
            UT::B(v) if E == 1 => UT::B(
                v.par_chunks(2).map(|c| field::add(field::mul(c[0], om[0]), field::mul(*c.get(1).unwrap_or(&0), r[0]))).collect(),
            ),
            _ => UT::X(
                (0..n).into_par_iter().map(|j| ext::add(ext::ucmul(om, self.get(2 * j), nr), ext::ucmul(r, self.get(2 * j + 1), nr))).collect(),
            ),
        }
    }
}

/// cosnark_gates.fill_range: this party's shares of the range rows' atoms (Beaver products round by round over every
/// checked truncation), then every truncation's violation indicator opened; returns the violated ones.
fn fill_range(rec: &Rec, a: &mut [Sh], net: &mut dyn Net, sp: &mut Spdz) -> Vec<(&'static str, usize)> {
    let rows = &rec.range_rows;
    let maxl = rows.iter().map(|r| r.l).max().unwrap_or(0);
    let mut beta: Vec<Option<Sh>> = vec![None; rows.len()];
    let add = |x: Sh, y: Sh| (field::add(x.0, y.0), field::add(x.1, y.1));
    let sub = |x: Sh, y: Sh| (field::sub(x.0, y.0), field::sub(x.1, y.1));
    for i in 0..maxl {
        let idx: Vec<usize> = (0..rows.len()).filter(|&k| i < rows[k].l && rows[k].t[i].is_some()).collect();
        let xs: Vec<Sh> = idx.iter().map(|&k| a[rows[k].d.bits[i] as usize]).collect();
        let ys: Vec<Sh> = idx.iter().map(|&k| beta[k].unwrap()).collect();
        let prods = sp.mul_batch(net, &xs, &ys);
        for (&k, t) in idx.iter().zip(prods) {
            a[rows[k].t[i].unwrap() as usize] = t;
        }
        for (k, row) in rows.iter().enumerate() {
            if i >= row.l {
                continue;
            }
            let ri = row.d.bits.get(i).map(|&x| a[x as usize]);
            let t = row.t[i].map(|x| a[x as usize]);
            let nb = if row.cb[i] == 1 {
                t.unwrap_or((0, 0))
            } else {
                let mut v = (0, 0);
                if let Some(r) = ri {
                    v = add(v, r);
                }
                if let Some(b) = beta[k] {
                    v = add(v, b);
                }
                if let Some(t) = t {
                    v = sub(v, t);
                }
                v
            };
            a[row.bb[i] as usize] = nb;
            beta[k] = Some(nb);
        }
    }
    let ind: Vec<Sh> = rows
        .iter()
        .map(|row| {
            let mut v = a[row.bb[row.l - 1] as usize];
            let mut cst = 0u64;
            for i in row.d.b as usize..row.l {
                let nb = a[row.bb[i] as usize];
                v = add(v, add(nb, nb));
                if let Some(&r) = row.d.bits.get(i) {
                    v = sub(v, a[r as usize]);
                }
                if i > 0 {
                    v = sub(v, a[row.bb[i - 1] as usize]);
                }
                cst = field::add(cst, row.cb[i]);
            }
            if cst != 0 { sp.cadd(cst, v) } else { v }
        })
        .collect();
    let vals = sp.open_batch(net, &ind, "range-check");
    rows.iter().zip(vals).filter(|(_, v)| *v != 0).map(|(r, _)| (r.d.name, r.d.k)).collect()
}

/// cosnark_gates.fill_lookup: this party's shares of the lookups' bit-circuit atoms. Level by level: the linear atoms
/// of that level (lookup by lookup, creation order), then the next level's products as one batch.
fn fill_lookup(rec: &Rec, a: &mut [Sh], net: &mut dyn Net, sp: &mut Spdz) {
    use crate::step::LbOp;
    let mut lvl = vec![0u32; a.len()];
    let mut top = 0;
    for ops in &rec.lb_rows {
        for op in ops {
            let (x, l) = match op {
                LbOp::Lin(x, f, _) => (*x, f.iter().map(|&(y, _)| lvl[y as usize]).max().unwrap_or(0)),
                LbOp::Mul(x, b, y) => (*x, lvl[*b as usize].max(lvl[*y as usize]) + 1),
            };
            lvl[x as usize] = l;
            top = top.max(l);
        }
    }
    for l in 0..=top {
        for ops in &rec.lb_rows {
            for op in ops {
                if let LbOp::Lin(x, f, c) = op {
                    if lvl[*x as usize] == l {
                        let mut v = (0u64, 0u64);
                        for &(y, co) in f {
                            let s = a[y as usize];
                            v = (field::add(v.0, field::mul(co, s.0)), field::add(v.1, field::mul(co, s.1)));
                        }
                        a[*x as usize] = if *c != 0 { sp.cadd(*c, v) } else { v };
                    }
                }
            }
        }
        let batch: Vec<(u32, u32, u32)> = rec
            .lb_rows
            .iter()
            .flatten()
            .filter_map(|op| match op {
                LbOp::Mul(x, b, y) if lvl[*x as usize] == l + 1 => Some((*x, *b, *y)),
                _ => None,
            })
            .collect();
        if batch.is_empty() {
            continue;
        }
        let xs: Vec<Sh> = batch.iter().map(|t| a[t.1 as usize]).collect();
        let ys: Vec<Sh> = batch.iter().map(|t| a[t.2 as usize]).collect();
        for (t, pr) in batch.iter().zip(sp.mul_batch(net, &xs, &ys)) {
            a[t.0 as usize] = pr;
        }
    }
}


/// prove_middle_zk for custodian `inp.i`. spine_coms: the spine's commitments of SPINE (carried, second life).
pub fn prove(
    inp: &MiddleIn,
    net: &mut dyn Net,
    sp: &mut Spdz,
    spine_coms: BTreeMap<String, PcsParty>,
    owner_y: Option<PcsParty>,
) -> Result<MiddleOut, String> {
    if inp.lp.ext != inp.pr.ext {
        return Err("the Ligero's EXT is not the profile's".into());
    }
    match inp.pr.ext {
        1 => prove_g::<1>(inp, net, sp, spine_coms, owner_y),
        2 => prove_g::<2>(inp, net, sp, spine_coms, owner_y),
        e => Err(format!("unsupported EXT {e}")),
    }
}

fn prove_g<const E: usize>(
    inp: &MiddleIn,
    net: &mut dyn Net,
    sp: &mut Spdz,
    mut spine_coms: BTreeMap<String, PcsParty>,
    owner_y: Option<PcsParty>,
) -> Result<MiddleOut, String> {
    let (pr, lp, i, n, d) = (inp.pr, inp.lp, inp.i, inp.n, inp.d);
    let rec = inp.rec;
    let kl = pr.k_l;
    let nr = ext::nr();
    let mut tt = crate::Trace::new("middle", i);
    let (lens, _) = public_shapes_io(pr, rec.n_prep(), rec.had.len(), d, false, rec.io.as_ref());
    let mut atoms_v: Vec<Sh> = rec.witness_atoms(inp.atoms)?;
    tt.lap(&format!("witness atoms ({} cons, {} hadamard rows, {} atoms)", rec.cons.len(), rec.had.len(), atoms_v.len()));
    if !rec.range_rows.is_empty() {
        atoms_v.resize(rec.n_prep(), (0, 0));
        let bad = fill_range(rec, &mut atoms_v, net, sp);
        if !bad.is_empty() && !inp.ignore_range {
            let names: Vec<String> = bad.iter().take(4).map(|(nm, k)| format!("{nm}[{k}]")).collect();
            return Err(format!(
                "proving refused: truncation input outside its proved bound: {}{}",
                names.join(", "),
                if bad.len() > 4 { " ..." } else { "" }
            ));
        }
    }
    tt.lap("range rows filled");
    if !rec.lb_rows.is_empty() {
        fill_lookup(rec, &mut atoms_v, net, sp);
    }
    tt.lap("lookup circuit filled");
    let mut pv = atoms_v;
    pv.resize(lens["P"], (0, 0));
    let gather = |sel: fn(&(u32, u32, u32)) -> u32| -> Vec<Sh> {
        padv(&rec.had.iter().map(|t| pv[sel(t) as usize]).collect::<Vec<_>>(), lens["A"])
    };
    let mut vecs: BTreeMap<String, Vec<Sh>> = BTreeMap::new();
    vecs.insert("A".into(), gather(|t| t.0));
    vecs.insert("B".into(), gather(|t| t.1));
    vecs.insert("C".into(), gather(|t| t.2));
    vecs.insert("P".into(), pv);
    for nm in &rec.names {
        vecs.insert(nm.to_string(), padv(&inp.wires[*nm], lens[*nm]));
    }
    // from here on only the shares are read (claims, linear sumchecks), except A, B, C, whose MACs the
    // zerocheck's Beaver products need: keep shares alone (memory: half of every vector, the large P above all)
    let mut abc: BTreeMap<String, Vec<Sh>> = BTreeMap::new();
    let mut xs: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for (k, v) in std::mem::take(&mut vecs) {
        xs.insert(k.clone(), v.iter().map(|x| x.0).collect());
        if ["A", "B", "C"].contains(&k.as_str()) {
            abc.insert(k, v);
        }
    }
    let carried: Vec<&str> = rec.io.as_ref().map(|io| io.carried.clone()).unwrap_or_else(|| SPINE.to_vec());
    let mut com: BTreeMap<String, PcsParty> = BTreeMap::new();
    for (k, v) in &xs {
        if carried.contains(&k.as_str()) {
            let mut c = spine_coms.remove(k).expect("spine commitment");
            c.shape.base = c.shape.block;
            com.insert(k.clone(), c);
        } else {
            com.insert(k.clone(), PcsParty::commit(pr, v, k, i, inp.det));
        }
    }
    tt.lap("vectors and commitments");
    let bind = owner_y.is_some();
    if let Some(oy) = owner_y {
        com.insert("yo".into(), oy);
    }
    let keys: Vec<String> = com.keys().cloned().collect();
    let my: Vec<Hash> = keys.iter().map(|k| com[k].root).collect();
    let all = gather_hashes(net, &my);
    let roots: BTreeMap<String, Vec<Hash>> =
        keys.iter().enumerate().map(|(ki, k)| (k.clone(), (0..n).map(|p| all[p][ki]).collect())).collect();
    let mut lg_ = LigParty::new(lp, i, n, &format!("(2, {})", inp.ctx.repr()), inp.det);
    if let Some(dl) = &inp.lig_dealer {
        lg_ = lg_.with_dealer(dl.clone());
    }
    if let Some(t) = &inp.lig_tape {
        lg_ = lg_.with_tape(t.clone());
    }
    let mut tr = Transcript::new(rec.io.as_ref().map(|io| io.label).unwrap_or("middle-zk"));
    tr.absorb(|h| {
        h.s("ctx").ctx(inp.ctx);
    });
    let pd = public_digest(inp.public);
    tr.absorb(|h| {
        h.s("public").hx(&pd);
    });
    for k in &keys {
        tr.absorb(|h| {
            h.s(k).list_hx(&roots[k]);
        });
    }
    // zerocheck A * B - C = 0
    let lh = lg(lens["A"]);
    let tau = ext::chal::<E>(&mut tr, lh);
    let mut zrs: Vec<[u64; E]> = Vec::new();
    let mut zc_roots = Vec::new();
    let mut prev: Tab<E> = Tab::B(abc["C"].clone());
    let mut st = Sc::<E> {
        f: Tab::B(abc.remove("A").unwrap()),
        g: Tab::B(abc.remove("B").unwrap()),
        sub: Some(Tab::B(abc.remove("C").unwrap())),
        eq: Some(ext::eqv(&tau)),
        deg: 3,
        claim: None,
        last: vec![],
    };
    // one Beaver product per live pair per round (cosnark_gates_zk.zround): f g is quadratic in X, its X = 0, 1 values
    // are known (round 0: the C atoms; later: the previous round's pair products at r), X = 3 by interpolation
    let mut live = rec.had.len();
    let mut pp: Vec<[[Sh; E]; 3]> = Vec::new();
    let inv2 = field::inv(2);
    for rnd in 0..lh {
        if rnd > 0 {
            let r = *zrs.last().unwrap();
            st.f = st.f.fold(r);
            st.g = st.g.fold(r);
            st.sub = Some(st.sub.as_ref().unwrap().fold(r));
            st.eq = Some(spine::fold_pub(st.eq.as_ref().unwrap(), r));
            let r1 = ext::sub(r, ext::one());
            let r2 = ext::sub(r, ext::lift(2));
            let l0 = ext::scal(inv2, ext::mul(r1, r2));
            let l1 = ext::neg(ext::mul(r, r2));
            let l2 = ext::scal(inv2, ext::mul(r, r1));
            let pv: Vec<[Sh; E]> = pp
                .par_iter()
                .map(|&[a, b, c]| ext::sadd(ext::sadd(ext::scmul(l0, a, nr), ext::scmul(l1, b, nr)), ext::scmul(l2, c, nr)))
                .collect();
            prev = if E == 1 { Tab::B(pv.into_iter().map(|x| x[0]).collect()) } else { Tab::X(pv) };
            live = (live + 1) / 2;
        }
        let (vals, p_) = zc_round(sp, net, &st, &prev, live);
        pp = p_;
        lg_.add_row(&vals.iter().flat_map(|v| ext::shares(v)).collect::<Vec<_>>());
        let rts = lg_.commit(net);
        tr.absorb(|h| {
            h.s("zc").list_hx(&rts);
        });
        zc_roots.push(rts);
        zrs.push(ext::chal1::<E>(&mut tr));
    }
    drop(st);
    drop(prev);
    drop(pp);
    tt.lap("zerocheck");
    let gam = ext::chal::<E>(&mut tr, rec.cons.len() + 3 * rec.had.len());
    let (q, mut cst) = build_q::<E>(rec, &lens, &gam);
    if let Some(f) = inp.cst_patch {
        if E != 1 {
            return Err("the fs_public attack hook is EXT = 1 only".into());
        }
        let q1: BTreeMap<String, Vec<u64>> = q.iter().map(|(k, v)| (k.clone(), v.iter().map(|x| x[0]).collect())).collect();
        let g1: Vec<u64> = gam.iter().map(|x| x[0]).collect();
        cst[0] = f(&q1, cst[0], &g1);
    }
    drop(gam);
    tt.lap("gamma and build_q");
    let ks: Vec<String> = lens.keys().cloned().collect();
    // claims <q_X, X> (shares only: they are never opened)
    let claims: Vec<[u64; E]> = ks
        .iter()
        .map(|k| {
            let (qq, xx) = (&q[k], &xs[k]);
            (0..qq.len())
                .into_par_iter()
                .with_min_len(4096)
                .map(|j| ext::scal(xx[j], qq[j]))
                .reduce(ext::zero::<E>, ext::add)
        })
        .collect();
    lg_.add_row(&claims.iter().flat_map(|c| c.iter().copied()).collect::<Vec<_>>());
    let croot = lg_.commit(net);
    tr.absorb(|h| {
        h.s("claims").list_hx(&croot);
    });
    let lmax = lens.values().map(|&l| lg(l)).max().unwrap();
    // lockstep linear sumchecks; a vector's zero padding is never materialized (folds of zeros stay zero)
    let mut tabs: Vec<(Vec<[u64; E]>, UT<E>)> = ks.iter().map(|k| (q[k].clone(), UT::B(xs.remove(k).unwrap()))).collect();
    let mut rr: Vec<[u64; E]> = Vec::new();
    let mut lsc_roots = Vec::new();
    for rnd in 0..lmax {
        if rnd > 0 {
            let r = *rr.last().unwrap();
            let om = ext::one_minus(r);
            for (qq, xx) in tabs.iter_mut() {
                *qq = qq
                    .par_chunks(2)
                    .map(|c| ext::add(ext::mul(c[0], om), ext::mul(*c.get(1).unwrap_or(&[0; E]), r)))
                    .collect();
                *xx = xx.fold(r, nr);
            }
        }
        let mut row = Vec::with_capacity(3 * E * ks.len());
        for (qq, xx) in &tabs {
            for t in 0..3u64 {
                let omt = field::one_minus(t);
                let v = (0..qq.len().div_ceil(2))
                    .into_par_iter()
                    .with_min_len(2048)
                    .map(|j| {
                        let q0 = qq[2 * j];
                        let q1 = *qq.get(2 * j + 1).unwrap_or(&[0; E]);
                        let qa = ext::add(ext::scal(omt, q0), ext::scal(t, q1));
                        ext::add(ext::ucmul(ext::scal(omt, qa), xx.get(2 * j), nr), ext::ucmul(ext::scal(t, qa), xx.get(2 * j + 1), nr))
                    })
                    .reduce(ext::zero::<E>, ext::add);
                row.extend(v);
            }
        }
        lg_.add_row(&row);
        let rts = lg_.commit(net);
        tr.absorb(|h| {
            h.s("lsc").list_hx(&rts);
        });
        lsc_roots.push(rts);
        rr.push(ext::chal1::<E>(&mut tr));
    }
    drop(tabs);
    tt.lap("claims and linear sumchecks");
    let rb = if bind { Some(ext::chal::<E>(&mut tr, lg(plen(d)))) } else { None };
    let ev = evaluations(&lens, &zrs, &rr, rb.as_deref());
    let shp: BTreeMap<String, Shape> = com.iter().map(|(k, c)| (k.clone(), c.shape.clone())).collect();
    let lay = row_layout(&shp, &ev, lh, lmax, kl, E);
    let mut ys = Vec::new();
    for (k, pt) in &ev {
        let c = &com[k];
        let (u, y) = c.eval_share_e(pt);
        ys.push(y);
        for uk in &u {
            for s0 in (0..c.shape.w).step_by(kl) {
                lg_.add_row(&uk[s0..(s0 + kl).min(c.shape.w)]);
            }
        }
    }
    tt.lap("evaluation rows");
    let (rx, ry, rz) = spine::prod_shares::<E>(&mut lg_, net, &ys[0..1], &ys[1..2]);
    for v in [rx, ry, rz] {
        lg_.add_row(&v);
    }
    let eval_roots = lg_.commit(net);
    let mask_roots = lg_.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    tt.lap("ligero commits");
    let (prox, pcs_cols) = spine::pcs_prove_e::<E>(pr, &mut com, &mut tr, net, n)?;
    tt.lap("pcs openings");
    let cols = pcs_cols.iter().map(|(k, c)| (k.clone(), (c.j.clone(), colsums(c, com[k].shape.r)))).collect();
    let coef = final_coefs(&q, &lens, &rr);
    let sys = MiddleSys::<E> {
        kl,
        shapes: ev.iter().map(|(k, _)| shp[k].clone()).collect(),
        ev,
        cols,
        lay,
        tau,
        zrs,
        rr,
        ks,
        coef,
        cst,
    };
    let quad = vec![sys.lay.prod];
    let lig = lg_.prove(net, &mut tr, &sys, &quad);
    tt.lap("ligero prove");
    sp.mac_check(net, "middle-zk")?;
    tt.lap("mac check");
    let mut stats = BTreeMap::new();
    stats.insert("hidden_rows".into(), sys.lay.nrows as u64);
    stats.insert("ligero_wire".into(), lg_.wire);
    stats.insert("atoms".into(), rec.n_prep() as u64);
    stats.insert("hadamard".into(), rec.had.len() as u64);
    let proof = MiddleProof {
        roots,
        zc_roots,
        claims_root: croot,
        lsc_roots,
        eval_roots,
        mask_roots,
        prox,
        pcs_cols,
        ligero: lig,
    };
    Ok(MiddleOut { proof, lig_rows: lg_.rows.clone(), sys: Box::new(sys), quad, stats })
}

/// verify_middle_zk: public data only (rec is the verifier's own replay).
#[allow(clippy::too_many_arguments)]
pub fn verify(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    rec: &Rec,
    d: usize,
    spine_roots: &BTreeMap<String, Vec<Hash>>,
    ctx: &Ctx,
    proof: &MiddleProof,
    bind: bool,
    public: &[u64],
) -> Result<(), String> {
    if lp.ext != pr.ext {
        return Err("the Ligero's EXT is not the profile's".into());
    }
    match pr.ext {
        1 => verify_g::<1>(pr, lp, n, rec, d, spine_roots, ctx, proof, bind, public),
        2 => verify_g::<2>(pr, lp, n, rec, d, spine_roots, ctx, proof, bind, public),
        e => Err(format!("unsupported EXT {e}")),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_g<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    rec: &Rec,
    d: usize,
    spine_roots: &BTreeMap<String, Vec<Hash>>,
    ctx: &Ctx,
    proof: &MiddleProof,
    bind: bool,
    public: &[u64],
) -> Result<(), String> {
    let (lens, sh) = public_shapes_io(pr, rec.n_prep(), rec.had.len(), d, bind, rec.io.as_ref());
    let roots = &proof.roots;
    if roots.keys().ne(sh.keys()) {
        return Err("proof names the wrong commitments".into());
    }
    match &rec.io {
        None => {
            for nm in SPINE {
                if let Some(sr) = spine_roots.get(nm) {
                    if &roots[nm] != sr {
                        return Err(format!("middle's {nm} is not the spine's committed {nm}"));
                    }
                }
            }
        }
        Some(io) => {
            for nm in &io.carried {
                if spine_roots.get(*nm) != Some(&roots[*nm]) {
                    return Err(format!("the {nm} commitment is not the ledger head's"));
                }
            }
        }
    }
    let mut tr = Transcript::new(rec.io.as_ref().map(|io| io.label).unwrap_or("middle-zk"));
    tr.absorb(|h| {
        h.s("ctx").ctx(ctx);
    });
    let pd = public_digest(public);
    tr.absorb(|h| {
        h.s("public").hx(&pd);
    });
    for (k, r) in roots {
        tr.absorb(|h| {
            h.s(k).list_hx(r);
        });
    }
    let lh = lg(lens["A"]);
    if proof.zc_roots.len() != lh {
        return Err("wrong number of zerocheck rounds".into());
    }
    let tau = ext::chal::<E>(&mut tr, lh);
    let mut zrs = Vec::new();
    for rnd in 0..lh {
        tr.absorb(|h| {
            h.s("zc").list_hx(&proof.zc_roots[rnd]);
        });
        zrs.push(ext::chal1::<E>(&mut tr));
    }
    let gam = ext::chal::<E>(&mut tr, rec.cons.len() + 3 * rec.had.len());
    let (q, cst) = build_q::<E>(rec, &lens, &gam);
    drop(gam);
    let lmax = lens.values().map(|&l| lg(l)).max().unwrap();
    if proof.lsc_roots.len() != lmax {
        return Err("wrong number of linear sumcheck rounds".into());
    }
    tr.absorb(|h| {
        h.s("claims").list_hx(&proof.claims_root);
    });
    let mut rr = Vec::new();
    for rnd in 0..lmax {
        tr.absorb(|h| {
            h.s("lsc").list_hx(&proof.lsc_roots[rnd]);
        });
        rr.push(ext::chal1::<E>(&mut tr));
    }
    let rb = if bind { Some(ext::chal::<E>(&mut tr, lg(plen(d)))) } else { None };
    let ev = evaluations(&lens, &zrs, &rr, rb.as_deref());
    let lay = row_layout(&sh, &ev, lh, lmax, pr.k_l, E);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    let keys: Vec<String> = sh.keys().cloned().collect();
    let shv: Vec<Shape> = sh.values().cloned().collect();
    let rootv: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
    let proxv: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| proof.prox[k].clone()).collect();
    let colv: Vec<PcsCols> = keys.iter().map(|k| proof.pcs_cols[k].clone()).collect();
    pcs::verify_e::<E>(pr, &keys, &shv, &rootv, &proxv, &colv, &mut tr, n)?;
    let cols = keys
        .iter()
        .map(|k| (k.clone(), (proof.pcs_cols[k].j.clone(), colsums(&proof.pcs_cols[k], sh[k].r))))
        .collect();
    let coef = final_coefs(&q, &lens, &rr);
    drop(q);
    let ks: Vec<String> = lens.keys().cloned().collect();
    let nrows = lay.nrows;
    let sys = MiddleSys::<E> {
        kl: pr.k_l,
        shapes: ev.iter().map(|(k, _)| sh[k].clone()).collect(),
        ev,
        cols,
        lay,
        tau,
        zrs,
        rr,
        ks,
        coef,
        cst,
    };
    let mut groups: Vec<Vec<Hash>> = proof.zc_roots.clone();
    groups.push(proof.claims_root.clone());
    groups.extend(proof.lsc_roots.iter().cloned());
    groups.push(proof.eval_roots.clone());
    let mut sizes = vec![1usize; lh + 1 + lmax];
    sizes.push(nrows - lh - 1 - lmax);
    let quad = vec![sys.lay.prod];
    ligero::verify(lp, n, &groups, &sizes, &proof.mask_roots, &sys, &quad, &proof.ligero, &mut tr)
}

/// Beaver triples the middle's degree-3 zerocheck consumes at EXT = 1: one per live pair per round, sum over the
/// lg(plen(n_had)) rounds of ceil(n_i / 2), n_0 = n_had, n_(i+1) = ceil(n_i / 2) (about n_had + log2 n_had; gen 5
/// drew 4 (plen - 1)).
pub fn beaver_count(n_had: usize) -> usize {
    beaver_count_e(n_had, 1)
}

/// The same under EXT = e: round 0 multiplies base tables (1 triple per pair), later rounds tables folded by
/// F_{p^e} challenges (3 at e = 2).
pub fn beaver_count_e(n_had: usize, e: usize) -> usize {
    let mut live = n_had;
    let mut tot = 0;
    for rnd in 0..lg(plen(n_had)) {
        let na = live.div_ceil(2);
        tot += na * if rnd == 0 || e == 1 { 1 } else { 3 };
        live = na;
    }
    tot
}
