//! cosnark_zk.py: the spine with ZK layers 2-3. `prove` is ONE custodian's prover (all exchanges through `Net`);
//! `verify` is the public verifier. Every challenge is an F_{p^E} element (E = the profile's EXT; cosnark_ext): the
//! code is generic over E and dispatched once at the top, so E = 1 is the base-field protocol byte for byte.
use crate::ext::{self, Tab};
use crate::field;
use crate::gmask::{self, GMask, MaskZ};
use crate::h::{Hash, Py};
use crate::ligero::{self, LigParams, LigParty, LigProof, LinSink, LinSystem};
use crate::net::{gather_hashes, Net};
use crate::pcs::{self, colsums, PcsCols, PcsParty, Shape};
use crate::rng::Det;
use crate::spdz::{lin2, Sh, Spdz};
use crate::transcript::{lagc, Transcript};
use crate::{Ctx, Profile};
use rayon::prelude::*;
use std::collections::BTreeMap;

pub const VEC: [&str; 9] = ["x", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1"];
pub const MAT: [&str; 4] = ["W1", "W2", "W1n", "W2n"];
pub const NPROD: usize = 6;

#[derive(Clone, Debug, PartialEq)]
pub struct SpineProof {
    pub roots: BTreeMap<String, Vec<Hash>>,
    /// ZKSC "rows": every round's Ligero roots by sumcheck (empty under "mask")
    pub round_roots: BTreeMap<String, Vec<Vec<Hash>>>,
    pub eval_roots: Vec<Hash>,
    pub mask_roots: Vec<Hash>,
    pub prox: BTreeMap<String, Vec<Vec<u64>>>,
    pub pcs_cols: BTreeMap<String, PcsCols>,
    pub ligero: LigProof,
    /// ZKSC "mask" (cut D; all empty under "rows"): the g group's roots, the opened G values (spec order, flat), the
    /// opened round messages by sumcheck (each flat: (deg + 1) E values)
    pub g_roots: Vec<Hash>,
    pub g_open: Vec<u64>,
    pub rounds: BTreeMap<String, Vec<Vec<u64>>>,
}

pub fn log2(d: usize) -> usize {
    assert!(d.is_power_of_two());
    d.trailing_zeros() as usize
}

/// cosnark_zk.shapes.
pub fn shapes(pr: &Profile, d: usize, chained: bool, bind: bool) -> BTreeMap<String, Shape> {
    let ld = log2(d);
    let mut out = BTreeMap::new();
    let block = if pr.nmask > 0 { pr.nmask / pr.lives } else { 0 };
    for k in VEC.iter().chain(MAT.iter()).chain(if bind { ["xo"].iter() } else { [].iter() }) {
        let m = if MAT.contains(k) { 2 * ld } else { ld };
        let base = if chained && (*k == "W1" || *k == "W2") { block } else { 0 };
        out.insert(k.to_string(), Shape::new(pr, m, base));
    }
    out
}

/// H("public-transcript", len(public), tuple(public)).
pub fn public_digest(public: &[u64]) -> Hash {
    let mut h = Py::new();
    h.s("public-transcript").int(public.len() as u64).tuple(public);
    h.done()
}

pub type Evals = Vec<(String, Vec<u64>)>;


/// The evaluation list with F_{p^E} points.
pub type EvalsE<const E: usize> = Vec<(String, Vec<[u64; E]>)>;

fn cat<T: Copy>(a: &[T], b: &[T]) -> Vec<T> {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    v
}

/// The schedule's challenges: (tau, rs) per sumcheck in order z1, z2, b, bg; (rc, rr) per rank-1; rb.
#[derive(Clone, Debug, Default)]
pub struct Sched<const E: usize> {
    pub scs: BTreeMap<String, (Vec<[u64; E]>, Vec<[u64; E]>)>,
    pub r1: Vec<(Vec<[u64; E]>, Vec<[u64; E]>)>,
    pub rb: Option<Vec<[u64; E]>>,
}

pub fn evals_of<const E: usize>(s: &Sched<E>) -> EvalsE<E> {
    let mut ev: EvalsE<E> = Vec::new();
    for (name, wk, vk, zk, tp) in
        [("z1", "W1", "x", "z1", false), ("z2", "W2", "h", "z2", false), ("b", "W2", "d2", "b", true)]
    {
        let (tau, rs) = &s.scs[name];
        ev.push((zk.into(), tau.clone()));
        ev.push((vk.into(), rs.clone()));
        ev.push((wk.into(), if !tp { cat(rs, tau) } else { cat(tau, rs) }));
    }
    let (_, rs) = &s.scs["bg"];
    for k in ["b", "g1", "bg"] {
        ev.push((k.into(), rs.clone()));
    }
    for (q, (wn, wo, dv, vv)) in [("W1n", "W1", "d1", "x"), ("W2n", "W2", "d2", "h")].iter().enumerate() {
        let (rc, rr) = &s.r1[q];
        let rcr = cat(rc, rr);
        ev.push((wn.to_string(), rcr.clone()));
        ev.push((wo.to_string(), rcr));
        ev.push((dv.to_string(), rr.clone()));
        ev.push((vv.to_string(), rc.clone()));
    }
    if let Some(rb) = &s.rb {
        ev.push(("xo".into(), rb.clone()));
        ev.push(("x".into(), rb.clone()));
    }
    ev
}

pub struct Layout {
    /// ZKSC "rows": the round rows by sumcheck (empty under "mask")
    pub rows: BTreeMap<String, Vec<usize>>,
    /// ZKSC "mask": the g group's rows, first (0 under "rows")
    pub ng: usize,
    pub urows: Vec<Vec<usize>>,
    pub prod: (usize, usize, usize),
    pub nrows: usize,
}

/// Hidden-row numbering in commit order: rounds (z1, z2, b, bg; ld each; a round's value j, component k at position
/// j E + k), then each evaluation's u rows (component-major: E blocks of ceil(W / K_L) rows), then the product rows.
pub fn row_layout<T>(ld: usize, sh: &BTreeMap<String, Shape>, ev: &[(String, T)], kl: usize, e: usize) -> Layout {
    row_layout_g(ld, sh, ev, kl, e, None)
}

/// The same with ZKSC "mask": ng = Some(the g group's rows), which come first in place of the round rows.
pub fn row_layout_g<T>(ld: usize, sh: &BTreeMap<String, Shape>, ev: &[(String, T)], kl: usize, e: usize, ng: Option<usize>) -> Layout {
    let mut rows = BTreeMap::new();
    let mut nxt = 0;
    if let Some(g) = ng {
        nxt = g;
    } else {
        for name in ["z1", "z2", "b", "bg"] {
            rows.insert(name.to_string(), (nxt..nxt + ld).collect());
            nxt += ld;
        }
    }
    let mut urows = Vec::new();
    for (k, _) in ev {
        let nr = sh[k].w.div_ceil(kl);
        urows.push((nxt..nxt + e * nr).collect());
        nxt += e * nr;
    }
    Layout { rows, ng: ng.unwrap_or(0), urows, prod: (nxt, nxt + 1, nxt + 2), nrows: nxt + 3 }
}

// ---------------------------------------------------------------------- linear forms over F_{p^E} values
type Cells = Vec<(u32, u32, u64)>;

/// Emits identities over F_{p^E} as E consecutive F_p constraints, component 0 first (cosnark_zk.eadder).
pub(crate) struct EEm<'a, const E: usize> {
    pub sink: &'a mut dyn LinSink,
    pub b: [Cells; E],
    pub nr: u64,
}

impl<'a, const E: usize> EEm<'a, E> {
    pub fn new(sink: &'a mut dyn LinSink) -> Self {
        EEm { sink, b: std::array::from_fn(|_| Vec::new()), nr: ext::nr() }
    }
    #[inline(always)]
    fn put(&mut self, k: usize, cell: (usize, usize), c: u64) {
        if c != 0 {
            self.b[k].push((cell.0 as u32, cell.1 as u32, c));
        }
    }
    /// coef V, V a hidden value whose component k is the single cell cells[k] (cosnark_zk.evar).
    #[inline(always)]
    pub fn var(&mut self, cells: [(usize, usize); E], c: [u64; E]) {
        if E == 1 {
            self.put(0, cells[0], c[0]);
        } else {
            self.put(0, cells[0], c[0]);
            self.put(0, cells[1], field::mul(self.nr, c[1]));
            self.put(1, cells[1], c[0]);
            self.put(1, cells[0], c[1]);
        }
    }
    /// coef V for V's components given as linear forms.
    pub fn form(&mut self, comps: &[Cells; E], c: [u64; E]) {
        let mut add = |k: usize, f: &Cells, s: u64| {
            if s != 0 {
                for &(r, pos, v) in f {
                    self.b[k].push((r, pos, field::mul(s, v)));
                }
            }
        };
        if E == 1 {
            add(0, &comps[0], c[0]);
        } else {
            let nr = self.nr;
            add(0, &comps[0], c[0]);
            add(0, &comps[1], field::mul(nr, c[1]));
            add(1, &comps[1], c[0]);
            add(1, &comps[0], c[1]);
        }
    }
    pub fn done(&mut self, label: &str, rhs: [u64; E]) {
        for k in 0..E {
            self.sink.con(label, &self.b[k], rhs[k]);
            self.b[k].clear();
        }
    }
}

/// cosnark_zk.prod_forms: product gate q's operand and result forms and the aux constraints (E = 2: three cells per
/// gate, x2 = x0 + x1 and y2 = y0 + y1; z = (P1 + NR P2, P3 - P1 - P2)).
pub(crate) struct ProdForms<const E: usize> {
    pub x: [(usize, usize); E],
    pub y: [(usize, usize); E],
    pub z: [Cells; E],
    pub aux: Vec<Cells>,
}

pub(crate) fn prod_forms<const E: usize>(prod: (usize, usize, usize), q: usize) -> ProdForms<E> {
    let (xr, yr, zr) = prod;
    let c = |r: usize, p: usize, v: u64| (r as u32, p as u32, v);
    if E == 1 {
        return ProdForms {
            x: std::array::from_fn(|_| (xr, q)),
            y: std::array::from_fn(|_| (yr, q)),
            z: std::array::from_fn(|_| vec![c(zr, q, 1)]),
            aux: vec![],
        };
    }
    let b = 3 * q;
    let m1 = field::p() - 1;
    let nr = ext::nr();
    let mut z: [Cells; E] = std::array::from_fn(|_| Vec::new());
    z[0] = vec![c(zr, b, 1), c(zr, b + 1, nr)];
    z[1] = vec![c(zr, b + 2, 1), c(zr, b, m1), c(zr, b + 1, m1)];
    ProdForms {
        x: std::array::from_fn(|k| (xr, b + k)),
        y: std::array::from_fn(|k| (yr, b + k)),
        z,
        aux: vec![vec![c(xr, b + 2, 1), c(xr, b, m1), c(xr, b + 1, m1)], vec![c(yr, b + 2, 1), c(yr, b, m1), c(yr, b + 1, m1)]],
    }
}

/// The cells of evaluation e's u row component k, column c.
#[inline(always)]
fn ucells<const E: usize>(urows: &[Vec<usize>], e: usize, w: usize, kl: usize, c: usize) -> [(usize, usize); E] {
    let nr = w.div_ceil(kl);
    std::array::from_fn(|k| (urows[e][k * nr + c / kl], c % kl))
}

/// Y_e: coef <u_e[:C], eq(pt[:mc])> over F_{p^E}.
pub(crate) fn y_form<const E: usize>(em: &mut EEm<E>, ev: &EvalsE<E>, shapes: &[Shape], urows: &[Vec<usize>], kl: usize, e: usize, coef: [u64; E]) {
    let s = &shapes[e];
    let b = ext::eqv(&ev[e].1[..s.mc]);
    for c in 0..s.c {
        em.var(ucells::<E>(urows, e, s.w, kl, c), ext::mul(coef, b[c]));
    }
}

/// coef times the round row r's value j.
#[inline(always)]
pub(crate) fn rc<const E: usize>(em: &mut EEm<E>, r: usize, j: usize, coef: [u64; E]) {
    em.var(std::array::from_fn(|k| (r, j * E + k)), coef);
}

/// product q's two operand identities and (E = 2) its aux constraints.
pub(crate) fn operands<const E: usize>(
    em: &mut EEm<E>,
    pf: &ProdForms<E>,
    label: &str,
    aux_label: &str,
    yx: &dyn Fn(&mut EEm<E>),
    yy: &dyn Fn(&mut EEm<E>),
) {
    em.var(pf.x, ext::one());
    yx(em);
    em.done(label, ext::zero());
    em.var(pf.y, ext::one());
    yy(em);
    em.done(label, ext::zero());
    for f in &pf.aux {
        em.sink.con(aux_label, f, 0);
    }
}

/// The verifier's checks as Ligero constraints (cosnark_zk.constraints).
pub struct SpineSys<const E: usize> {
    pub kl: usize,
    pub ev: EvalsE<E>,
    pub shapes: Vec<Shape>,
    /// per evaluation's commitment: (opened columns, column sums)
    pub cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    pub lay: Layout,
    pub sched: Sched<E>,
    /// ZKSC "mask": the opened masking data (None: hidden round rows)
    pub mz: Option<MaskZ<E>>,
}

impl<const E: usize> SpineSys<E> {
    fn y(&self, em: &mut EEm<E>, e: usize, coef: [u64; E]) {
        y_form(em, &self.ev, &self.shapes, &self.lay.urows, self.kl, e, coef);
    }
    fn sumcheck(&self, em: &mut EEm<E>, name: &str, deg: usize, first: Option<usize>, fin: &dyn Fn(&mut EEm<E>)) {
        let (_, rs) = &self.sched.scs[name];
        let r = &self.lay.rows[name];
        let one = ext::one::<E>();
        rc(em, r[0], 0, one);
        rc(em, r[0], 1, one);
        if let Some(e) = first {
            self.y(em, e, ext::neg(one));
        }
        em.done(&format!("sumcheck {name}: first round sum = claim"), ext::zero());
        let lab = format!("sumcheck {name}: round sums");
        for i in 1..r.len() {
            let lc = ext::lagc(deg, rs[i - 1]);
            rc(em, r[i], 0, one);
            rc(em, r[i], 1, one);
            for j in 0..=deg {
                rc(em, r[i - 1], j, ext::neg(lc[j]));
            }
            em.done(&lab, ext::zero());
        }
        let lc = ext::lagc(deg, *rs.last().unwrap());
        for j in 0..=deg {
            rc(em, *r.last().unwrap(), j, lc[j]);
        }
        fin(em);
        em.done(&format!("sumcheck {name}: final claim = product gate"), ext::zero());
    }
}

/// PCS evaluation consistency at the opened columns (base points: the handover's).
pub fn pcs_consistency(
    em_sink: &mut dyn LinSink,
    kl: usize,
    ev: &Evals,
    shapes: &[Shape],
    cols: &BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: &[Vec<usize>],
) {
    let ev1: EvalsE<1> = ev.iter().map(|(k, pt)| (k.clone(), pt.iter().map(|&x| [x]).collect())).collect();
    pcs_consistency_e::<1>(em_sink, kl, &ev1, shapes, cols, urows)
}

/// PCS evaluation consistency at the opened columns: component k of u_e against component k of the weights a_e.
pub fn pcs_consistency_e<const E: usize>(
    em_sink: &mut dyn LinSink,
    kl: usize,
    ev: &EvalsE<E>,
    shapes: &[Shape],
    cols: &BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: &[Vec<usize>],
) {
    let mut bufs: [Cells; E] = std::array::from_fn(|_| Vec::new());
    for (e, (k, pt)) in ev.iter().enumerate() {
        let s = &shapes[e];
        let a = s.eval_weights_e(pt);
        let (jj, csum) = &cols[k];
        let label = format!("PCS evaluation consistency ({k})");
        let nr = s.w.div_ceil(kl);
        for (t, &j) in jj.iter().enumerate() {
            let x = s.dom.point(j);
            let mut xs = 1u64;
            for b in bufs.iter_mut() {
                b.clear();
            }
            for c in 0..s.w {
                for (kk, b) in bufs.iter_mut().enumerate() {
                    b.push((urows[e][kk * nr + c / kl] as u32, (c % kl) as u32, xs));
                }
                xs = field::mul(xs, x);
            }
            let n = a.len().min(csum[t].len());
            let rhs = ext::dot_base(&csum[t][..n], &a[..n]);
            for kk in 0..E {
                em_sink.con(&label, &bufs[kk], rhs[kk]);
            }
        }
    }
}

impl<const E: usize> LinSystem for SpineSys<E> {
    fn emit(&self, sink: &mut dyn LinSink) {
        pcs_consistency_e(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.lay.urows);
        let mut em = EEm::<E>::new(sink);
        let one = ext::one::<E>();
        let m1 = ext::neg(one);
        let pf: Vec<ProdForms<E>> = (0..NPROD).map(|q| prod_forms::<E>(self.lay.prod, q)).collect();
        let (tau, rs) = &self.sched.scs["bg"];
        let eq = ext::mle(&ext::eqv(tau), rs);
        for (q, name, idx) in [(0usize, "z1", 0usize), (1, "z2", 3), (2, "b", 6)] {
            if let Some(mz) = &self.mz {
                let first = |em: &mut EEm<E>| self.y(em, idx, one);
                mz.sumcheck(&mut em, name, &self.sched.scs[name].1, Some(&first), &|em: &mut EEm<E>| em.form(&pf[q].z, one));
            } else {
                self.sumcheck(&mut em, name, 2, Some(idx), &|em: &mut EEm<E>| em.form(&pf[q].z, m1));
            }
            operands(
                &mut em,
                &pf[q],
                &format!("product {q} operands"),
                &format!("product {q} operand sums"),
                &|em| self.y(em, idx + 2, m1),
                &|em| self.y(em, idx + 1, m1),
            );
        }
        if let Some(mz) = &self.mz {
            mz.sumcheck(&mut em, "bg", rs, None, &|em: &mut EEm<E>| {
                em.form(&pf[3].z, eq);
                self.y(em, 11, ext::neg(eq));
            });
        } else {
            self.sumcheck(&mut em, "bg", 3, None, &|em: &mut EEm<E>| {
                em.form(&pf[3].z, ext::neg(eq));
                self.y(em, 11, eq);
            });
        }
        operands(&mut em, &pf[3], "product 3 operands", "product 3 operand sums", &|em| self.y(em, 9, m1), &|em| self.y(em, 10, m1));
        for (q, base) in [(4usize, 12usize), (5, 16)] {
            let wn = if q == 4 { "W1n" } else { "W2n" };
            self.y(&mut em, base, one);
            self.y(&mut em, base + 1, m1);
            em.form(&pf[q].z, one);
            em.done(&format!("rank-1 update {wn}: W'(r) = W(r) - d(r_row) v(r_col)"), ext::zero());
            operands(
                &mut em,
                &pf[q],
                &format!("product {q} operands"),
                &format!("product {q} operand sums"),
                &|em| self.y(em, base + 2, m1),
                &|em| self.y(em, base + 3, m1),
            );
        }
        if self.ev.len() == 22 {
            self.y(&mut em, 20, one);
            self.y(&mut em, 21, m1);
            em.done("signed input binding: the custodians' x = the owner's signed x", ext::zero());
        }
    }
}

// ------------------------------------------------------------------------------------------------ prover
/// A sumcheck's per-party state (cb in prove_zk): tables of shared elements with their structural lengths.
pub struct Sc<const E: usize> {
    pub f: Tab<E>,
    pub g: Tab<E>,
    pub sub: Option<Tab<E>>,
    pub eq: Option<Vec<[u64; E]>>,
    pub deg: usize,
    pub claim: Option<[u64; E]>,
    pub last: Vec<[u64; E]>,
}

pub fn fold_sh(t: &[Sh], r: u64) -> Vec<Sh> {
    let om = field::one_minus(r);
    t.par_chunks(2).map(|c| lin2(om, c[0], r, c[1])).collect()
}

/// eq folded by r: eq[2k] (1 - r) + eq[2k + 1] r.
pub fn fold_pub<const E: usize>(t: &[[u64; E]], r: [u64; E]) -> Vec<[u64; E]> {
    let om = ext::one_minus(r);
    t.par_chunks(2).map(|c| ext::add(ext::mul(c[0], om), ext::mul(c[1], r))).collect()
}

/// One round: every value of the round polynomial at X = 0..deg, as this party's SPDZ shares of F_{p^E} elements.
/// The products f(X) g(X) take 1, 2 or 3 Beaver triples each by the tables' structural lengths, in the harness's
/// order (X-major, then pair, then the product's triples).
pub fn round_vals<const E: usize>(sp: &mut Spdz, net: &mut dyn Net, st: &Sc<E>) -> Vec<[Sh; E]> {
    let half = st.f.len() / 2;
    let deg = st.deg;
    let (fb, gb) = (st.f.base(), st.g.base());
    let per = ext::mul_triples::<E>(fb, gb);
    let nr = ext::nr();
    let mut xs = Vec::with_capacity((deg + 1) * half * per);
    let mut ys = Vec::with_capacity((deg + 1) * half * per);
    for xv in 0..=deg as u64 {
        let om = field::one_minus(xv);
        let ops: Vec<([Sh; E], [Sh; E])> = (0..half)
            .into_par_iter()
            .map(|k| {
                (
                    ext::slin2b(om, st.f.get(2 * k), xv, st.f.get(2 * k + 1)),
                    ext::slin2b(om, st.g.get(2 * k), xv, st.g.get(2 * k + 1)),
                )
            })
            .collect();
        for (fx, gx) in ops {
            ext::push_mul(fx, fb, gx, gb, &mut xs, &mut ys);
        }
    }
    let prods = sp.mul_batch(net, &xs, &ys);
    (0..=deg)
        .map(|xv| {
            let xv64 = xv as u64;
            let om = field::one_minus(xv64);
            (0..half)
                .into_par_iter()
                .map(|k| {
                    let o = (xv * half + k) * per;
                    let mut term = ext::take_mul::<E>(fb, gb, &prods[o..o + per], nr);
                    if let Some(sub) = &st.sub {
                        term = ext::ssub(term, ext::slin2b(om, sub.get(2 * k), xv64, sub.get(2 * k + 1)));
                    }
                    if let Some(eq) = &st.eq {
                        let e = ext::add(ext::scal(om, eq[2 * k]), ext::scal(xv64, eq[2 * k + 1]));
                        term = ext::scmul(e, term, nr);
                    }
                    term
                })
                .reduce(ext::szero::<E>, ext::sadd)
        })
        .collect()
}

pub struct SpineIn<'a> {
    pub pr: &'a Profile,
    pub lp: &'a LigParams,
    pub i: usize,
    pub n: usize,
    pub d: usize,
    /// this party's SPDZ shares: VEC names (length d) and MAT names (d*d, row-major)
    pub wires: &'a BTreeMap<String, Vec<Sh>>,
    pub ctx: &'a Ctx,
    pub public: &'a [u64],
    pub det: &'a Det,
    pub attack: Option<&'a str>,
    /// the ideal dealer's stream for the Ligero's triples (real runs; identical for every party)
    pub lig_dealer: Option<pycompat::PyRandom>,
    /// the deployed run: this party's tape triples for the Ligero's products (overrides lig_dealer)
    pub lig_tape: Option<Vec<(u64, u64, u64)>>,
}

/// Plain (unauthenticated) products in the spine's Ligero at EXT = 1: the six evaluation-pair products.
pub const LIG_SCALARS: usize = 6;

/// The spine Ligero's plain products under EXT = e: six gates, three products each at e = 2 (P1, P2, P3).
pub fn lig_scalars(e: usize) -> usize {
    LIG_SCALARS * if e == 1 { 1 } else { 3 }
}

pub struct SpineOut {
    pub proof: SpineProof,
    pub coms: BTreeMap<String, PcsParty>,
    pub lig_rows: Vec<Vec<u64>>,
    pub sys: Box<dyn LinSystem + Send>,
    pub quad: Vec<(usize, usize, usize)>,
    pub stats: BTreeMap<String, u64>,
}

/// The product rows' shares from the operands' (cosnark_zk.prod_shares): one plain product per gate at E = 1;
/// at E = 2 three cells per gate (x0, x1, x0 + x1) and three products, gate by gate.
pub(crate) fn prod_shares<const E: usize>(
    lg: &mut LigParty,
    net: &mut dyn Net,
    xs: &[[u64; E]],
    ys: &[[u64; E]],
) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
    let cells = |v: &[[u64; E]]| -> Vec<u64> {
        v.iter().flat_map(|x| if E == 1 { vec![x[0]] } else { vec![x[0], x[1], field::add(x[0], x[1])] }).collect()
    };
    let (rx, ry) = (cells(xs), cells(ys));
    let rz = lg.mul_plain_batch(net, &rx, &ry);
    (rx, ry, rz)
}

/// cosnark_zk.prove_zk for custodian `inp.i`. carry: the previous step's child commitments (W1, W2), carried with
/// their openings; owner_x: this party's part of the owner's x commitment.
pub fn prove(
    inp: &SpineIn,
    net: &mut dyn Net,
    sp: &mut Spdz,
    carry: BTreeMap<String, PcsParty>,
    owner_x: Option<PcsParty>,
) -> Result<SpineOut, String> {
    if inp.lp.ext != inp.pr.ext {
        return Err("the Ligero's EXT is not the profile's".into());
    }
    match inp.pr.ext {
        1 => prove_g::<1>(inp, net, sp, carry, owner_x),
        2 => prove_g::<2>(inp, net, sp, carry, owner_x),
        e => Err(format!("unsupported EXT {e}")),
    }
}

fn prove_g<const E: usize>(
    inp: &SpineIn,
    net: &mut dyn Net,
    sp: &mut Spdz,
    mut carry: BTreeMap<String, PcsParty>,
    owner_x: Option<PcsParty>,
) -> Result<SpineOut, String> {
    let (pr, lp, i, n, d) = (inp.pr, inp.lp, inp.i, inp.n, inp.d);
    let ld = log2(d);
    let kl = pr.k_l;
    let attack = inp.attack.unwrap_or("");
    let w = inp.wires;
    let nr = ext::nr();
    let mut tt = crate::Trace::new("spine", i);
    let mut com: BTreeMap<String, PcsParty> = BTreeMap::new();
    let mut honest_w1n: Option<Vec<u64>> = None;
    for k in VEC.iter().chain(MAT.iter()) {
        let mut sh: Vec<u64> = w[*k].iter().map(|x| x.0).collect();
        if (attack == "forge_W1n" || attack == "lie_in_u") && *k == "W1n" {
            honest_w1n = Some(sh.clone());
            if i == 0 {
                sh[5] = field::add(sh[5], 1);
            }
        }
        if (attack == "forge_z1" || attack == "forge_sumcheck") && *k == "z1" && i == 0 {
            sh[3] = field::add(sh[3], 1);
        }
        if let Some(mut c) = carry.remove(*k) {
            c.shape.base = c.shape.block;
            com.insert(k.to_string(), c);
            continue;
        }
        com.insert(k.to_string(), PcsParty::commit(pr, &sh, k, i, inp.det));
    }
    tt.lap("commitments");
    let bind = owner_x.is_some();
    if let Some(ox) = owner_x {
        com.insert("xo".into(), ox);
    }
    let keys: Vec<String> = com.keys().cloned().collect();
    let my_roots: Vec<Hash> = keys.iter().map(|k| com[k].root).collect();
    let all = gather_hashes(net, &my_roots);
    let roots: BTreeMap<String, Vec<Hash>> =
        keys.iter().enumerate().map(|(ki, k)| (k.clone(), (0..n).map(|p| all[p][ki]).collect())).collect();

    let seed_label = format!("(1, {})", inp.ctx.repr());
    let mut lg = LigParty::new(lp, i, n, &seed_label, inp.det);
    if let Some(dl) = &inp.lig_dealer {
        lg = lg.with_dealer(dl.clone());
    }
    if let Some(t) = &inp.lig_tape {
        lg = lg.with_tape(t.clone());
    }
    let mut tr = Transcript::new("step-zk");
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
    let mut sched = Sched::<E>::default();
    let mut round_roots: BTreeMap<String, Vec<Vec<Hash>>> = BTreeMap::new();
    // cut D: every g of the spine committed as one group, the G values opened, rho drawn (before the first tau)
    let mut gmz: Option<(MaskZ<E>, Vec<u64>, Vec<Hash>)> = None;
    if pr.mask {
        let gm = GMask::new(gmask::spine_specs(ld), 0, kl, E);
        gmz = Some(gmask::commit::<E>(gm, &mut lg, net, &mut tr, if attack == "forge_G" && i == 0 { Some("z2") } else { None }));
    }
    let tables = [("z1", "W1", "x", false), ("z2", "W2", "h", false), ("b", "W2", "d2", true)];
    let nsc = tables.len() + 1;
    for sci in 0..nsc {
        let name = if sci < 3 { tables[sci].0 } else { "bg" };
        let tau = ext::chal::<E>(&mut tr, ld);
        let mut rs: Vec<[u64; E]> = Vec::new();
        let mut st: Sc<E>;
        if name == "bg" {
            // The harness starts this claim at 0 and re-centres every round on it, a no-op whenever bg = b * g1
            // holds (every honest step and every attack row). Natively it is not run: it would open the hidden
            // round sums.
            st = Sc {
                f: Tab::B(w["b"].clone()),
                g: Tab::B(w["g1"].clone()),
                sub: Some(Tab::B(w["bg"].clone())),
                eq: Some(ext::eqv(&tau)),
                deg: 3,
                // the harness's claim 0 (a no-op when bg = b g1); under "mask" the round is opened anyway
                claim: if pr.mask { Some(ext::zero()) } else { None },
                last: vec![],
            };
        } else {
            let (_, wk, vk, tp) = tables[sci];
            let wm = &w[wk];
            let et = ext::eqv(&tau);
            // f = sum_i eq(tau)_i W[i][.] (or its transpose): F_{p^E} weights on base shares
            let fv: Vec<[Sh; E]> = (0..d)
                .into_par_iter()
                .map(|j| {
                    let mut acc = ext::szero::<E>();
                    for ii in 0..d {
                        let wv = if !tp { wm[ii * d + j] } else { wm[j * d + ii] };
                        for k in 0..E {
                            acc[k] = crate::spdz::shadd(acc[k], crate::spdz::cmul(et[ii][k], wv));
                        }
                    }
                    acc
                })
                .collect();
            let f = if E == 1 { Tab::B(fv.into_iter().map(|a| a[0]).collect()) } else { Tab::X(fv) };
            let mut claim = None;
            if attack == "forge_sumcheck" && name == "z1" {
                // colluders broadcast their committed z1 shares to target the forged z1's MLE
                let z1 = com["z1"].ext.clone();
                let s = &com["z1"].shape;
                let mine: Vec<u64> = (0..s.rd).flat_map(|r| z1[r * s.w..r * s.w + s.c].to_vec()).collect();
                let all = net.all_gather(mine);
                let zsum: Vec<u64> =
                    (0..all[0].len()).map(|k| all.iter().fold(0, |a, v| field::add(a, v[k]))).collect();
                claim = Some(ext::mle_base(&zsum, &tau));
            }
            st = Sc { f, g: Tab::B(w[vk].clone()), sub: None, eq: None, deg: 2, claim, last: vec![] };
        }
        for rnd in 0..ld {
            if rnd > 0 {
                let r = *rs.last().unwrap();
                st.f = st.f.fold(r);
                st.g = st.g.fold(r);
                if let Some(s) = &st.sub {
                    st.sub = Some(s.fold(r));
                }
                if let Some(e) = &st.eq {
                    st.eq = Some(fold_pub(e, r));
                }
                if st.claim.is_some() {
                    st.claim = Some(ext::interp_at(&st.last, r));
                }
            }
            let vals = round_vals(sp, net, &st);
            if let Some((mz, gsh, _)) = &mut gmz {
                // cut D: the opened message s_rnd = f part + rho g part
                if rnd == 0 {
                    if let Some(c) = st.claim {
                        st.claim = Some(ext::add(c, ext::mul(mz.rho, mz.g[name])));
                    }
                }
                let fv: Vec<[u64; E]> = vals.iter().map(|v| ext::shares(v)).collect();
                let bump = if attack == "bad_share" && name == "b" && rnd == 0 && i == 0 { Some(("b", 0)) } else { None };
                let mut plain = gmask::open_round::<E>(mz, gsh, net, &[name], rnd, &rs, &[fv], bump).remove(0);
                if let Some(claim) = st.claim {
                    // colluders: shift the opened message so its sum matches the (forged) claim
                    let fix = ext::scal(field::inv(2), ext::sub(claim, ext::add(plain[0], plain[1])));
                    plain = plain.iter().map(|&v| ext::add(v, fix)).collect();
                }
                if attack == "forge_round" && name == "z2" && rnd == 1 {
                    // a forged message whose own sum is kept: +5 at X = 0, -5 at X = 1; later rounds follow it at r
                    plain[0] = ext::add(plain[0], ext::lift(5));
                    plain[1] = ext::sub(plain[1], ext::lift(5));
                    st.claim = Some(ext::zero());
                }
                let fl = gmask::flat(&plain);
                st.last = plain.clone();
                mz.msgs.entry(name.to_string()).or_default().push(plain);
                tr.absorb(|h| {
                    h.s("scr").list(&fl);
                });
                rs.push(ext::chal1::<E>(&mut tr));
                continue;
            }
            let mut shares: Vec<u64> = vals.iter().flat_map(|v| ext::shares(v)).collect();
            if let Some(claim) = st.claim {
                // colluders: make the hidden round sum match the (forged) claim
                let all = net.all_gather(shares.clone());
                let plain: Vec<[u64; E]> = (0..=st.deg)
                    .map(|x| std::array::from_fn(|k| all.iter().fold(0, |a, v| field::add(a, v[x * E + k]))))
                    .collect();
                let fix = ext::scal(field::inv(2), ext::sub(claim, ext::add(plain[0], plain[1])));
                if i == 0 {
                    shares = shares.iter().enumerate().map(|(pos, &v)| field::add(v, fix[pos % E])).collect();
                }
                st.last = plain.iter().map(|&v| ext::add(v, fix)).collect();
            }
            lg.add_row(&shares);
            let rts = lg.commit(net);
            tr.absorb(|h| {
                h.s("scr").list_hx(&rts);
            });
            round_roots.entry(name.to_string()).or_default().push(rts);
            rs.push(ext::chal1::<E>(&mut tr));
        }
        sched.scs.insert(name.to_string(), (tau, rs));
    }
    tt.lap("sumchecks");
    for _ in 0..2 {
        let rc = ext::chal::<E>(&mut tr, ld);
        let rr = ext::chal::<E>(&mut tr, ld);
        sched.r1.push((rc, rr));
    }
    if bind {
        sched.rb = Some(ext::chal::<E>(&mut tr, ld));
    }
    let ev = evals_of(&sched);
    let shp: BTreeMap<String, Shape> = com.iter().map(|(k, c)| (k.clone(), c.shape.clone())).collect();
    let lay = row_layout_g(ld, &shp, &ev, kl, E, gmz.as_ref().map(|g| g.0.gm.nrows));
    let mut ys: Vec<[u64; E]> = Vec::with_capacity(ev.len());
    for (k, pt) in &ev {
        let c = &com[k];
        let (mut u, mut y) = c.eval_share_e(pt);
        if attack == "lie_in_u" && k == "W1n" && i == 0 {
            let s = &c.shape;
            let hon = honest_w1n.as_ref().unwrap();
            let mut ext_ = c.ext.clone();
            for r in 0..s.rd {
                ext_[r * s.w..r * s.w + s.c].copy_from_slice(&hon[r * s.c..(r + 1) * s.c]);
            }
            let tmp = PcsParty { ext: ext_, ..shallow(c) };
            let (u2, y2) = tmp.eval_share_e(pt);
            u = u2;
            y = y2;
        }
        ys.push(y);
        for uk in &u {
            for s0 in (0..c.shape.w).step_by(kl) {
                lg.add_row(&uk[s0..(s0 + kl).min(c.shape.w)]);
            }
        }
    }
    tt.lap("evaluation rows");
    let pairs = [(2usize, 1usize), (5, 4), (8, 7), (9, 10), (14, 15), (18, 19)];
    let xs: Vec<[u64; E]> = pairs.iter().map(|&(a, _)| ys[a]).collect();
    let yv: Vec<[u64; E]> = pairs.iter().map(|&(_, b)| ys[b]).collect();
    let (rx, ry, rz) = prod_shares::<E>(&mut lg, net, &xs, &yv);
    lg.add_row(&rx);
    lg.add_row(&ry);
    lg.add_row(&rz);
    let eval_roots = lg.commit(net);
    let mask_roots = lg.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    tt.lap("ligero commits");
    let (prox, pcs_cols) = pcs_prove_e::<E>(pr, &mut com, &mut tr, net, n)?;
    tt.lap("pcs openings");
    let cols = pcs_cols.iter().map(|(k, c)| (k.clone(), (c.j.clone(), colsums(c, com[k].shape.r)))).collect();
    let (mz, g_roots) = match gmz {
        Some((mz, _, gr)) => (Some(mz), gr),
        None => (None, Vec::new()),
    };
    let (g_open, rounds) = match &mz {
        Some(m) => (m.g_flat(), m.msgs.iter().map(|(k, v)| (k.clone(), v.iter().map(|x| gmask::flat(x)).collect())).collect()),
        None => (Vec::new(), BTreeMap::new()),
    };
    let sys = SpineSys::<E> { kl, shapes: ev.iter().map(|(k, _)| shp[k].clone()).collect(), ev, cols, lay, sched, mz };
    let quad = vec![sys.lay.prod];
    let lig = lg.prove(net, &mut tr, &sys, &quad);
    tt.lap("ligero prove");
    sp.mac_check(net, "cosnark-zk")?;
    tt.lap("mac check");
    let _ = nr;
    let mut stats = BTreeMap::new();
    stats.insert("hidden_rows".into(), sys.lay.nrows as u64);
    stats.insert("ligero_wire".into(), lg.wire);
    stats.insert("ligero_beaver_scalar".into(), lg.scalar_triples);
    stats.insert("ligero_poly_triples".into(), lg.poly_triples);
    let proof = SpineProof {
        roots,
        round_roots,
        eval_roots,
        mask_roots,
        prox,
        pcs_cols,
        ligero: lig,
        g_roots,
        g_open,
        rounds,
    };
    Ok(SpineOut { proof, coms: com, lig_rows: lg.rows.clone(), sys: Box::new(sys), quad, stats })
}

fn shallow(c: &PcsParty) -> PcsParty {
    PcsParty {
        label: c.label.clone(),
        shape: c.shape.clone(),
        ext: Vec::new(),
        salts: Vec::new(),
        tree: Vec::new(),
        root: c.root,
        opened_lives: 0,
        max_lives: c.max_lives,
        cw: Vec::new(),
    }
}

/// cosnark.lag3: interpolate through (0..k-1, vals), evaluate at x.
pub fn lag3(vals: &[u64], x: u64) -> u64 {
    let lc = lagc(vals.len() - 1, x);
    field::dot(vals, &lc)
}

/// pcs_prove(com, [], tr): every party's proximity combination per commitment, then the opened columns.
pub fn pcs_prove(
    pr: &Profile,
    com: &mut BTreeMap<String, PcsParty>,
    tr: &mut Transcript,
    net: &mut dyn Net,
    n: usize,
) -> Result<(BTreeMap<String, Vec<Vec<u64>>>, BTreeMap<String, PcsCols>), String> {
    pcs_prove_e::<1>(pr, com, tr, net, n)
}

/// pcs_prove with F_{p^E} proximity weights: one row per custodian, the E components of its combination
/// concatenated (each masked by its own proximity mask row).
#[allow(clippy::type_complexity)]
pub fn pcs_prove_e<const E: usize>(
    pr: &Profile,
    com: &mut BTreeMap<String, PcsParty>,
    tr: &mut Transcript,
    net: &mut dyn Net,
    n: usize,
) -> Result<(BTreeMap<String, Vec<Vec<u64>>>, BTreeMap<String, PcsCols>), String> {
    let mut prox = BTreeMap::new();
    for (k, c) in com.iter() {
        let s = &c.shape;
        let gam = s.prox_weights_e::<E>(ext::chal::<E>(tr, s.prox_len_e(E)));
        let mine: Vec<u64> = c.row_combo_e(&gam).concat();
        let all = net.all_gather(mine);
        tr.absorb(|h| {
            h.s("g").s(k).list2(&all);
        });
        prox.insert(k.clone(), all);
    }
    let mut cols = BTreeMap::new();
    for (k, c) in com.iter_mut() {
        c.take_life(k, pr.lives).map_err(|e| format!("LifeExhausted: {}", e.0))?;
        let jj = tr.distinct_cols(pr.t_cols, c.shape.npts);
        let mine: Vec<pcs::Opening> = c.open_batch(&jj);
        let all = ligero::gather_openings(net, vec![mine]);
        let _ = n;
        cols.insert(k.clone(), PcsCols { j: jj, open: all.into_iter().next().unwrap() });
    }
    Ok((prox, cols))
}

// ------------------------------------------------------------------------------------------------ verifier
/// cosnark_zk.verify_zk: public data only.
#[allow(clippy::too_many_arguments)]
pub fn verify(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    d: usize,
    ctx: &Ctx,
    parent_roots: Option<&BTreeMap<String, Vec<Hash>>>,
    chained: bool,
    proof: &SpineProof,
    bind: bool,
    public: &[u64],
) -> Result<(), String> {
    if lp.ext != pr.ext {
        return Err("the Ligero's EXT is not the profile's".into());
    }
    match pr.ext {
        1 => verify_g::<1>(pr, lp, n, d, ctx, parent_roots, chained, proof, bind, public),
        2 => verify_g::<2>(pr, lp, n, d, ctx, parent_roots, chained, proof, bind, public),
        e => Err(format!("unsupported EXT {e}")),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_g<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    d: usize,
    ctx: &Ctx,
    parent_roots: Option<&BTreeMap<String, Vec<Hash>>>,
    chained: bool,
    proof: &SpineProof,
    bind: bool,
    public: &[u64],
) -> Result<(), String> {
    let ld = log2(d);
    let sh = shapes(pr, d, chained, bind);
    let roots = &proof.roots;
    if roots.keys().ne(sh.keys()) {
        return Err("proof names the wrong commitments".into());
    }
    if let Some(par) = parent_roots {
        if roots["W1"] != par["W1"] || roots["W2"] != par["W2"] {
            return Err("parent commitment is not the previous step's child commitment".into());
        }
    }
    let mut tr = Transcript::new("step-zk");
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
    let rr = &proof.round_roots;
    let mut mz: Option<MaskZ<E>> = None;
    if pr.mask {
        let rd = &proof.rounds;
        let sp = gmask::spine_specs(ld);
        if rd.keys().map(|s| s.as_str()).ne(["b", "bg", "z1", "z2"])
            || rd.values().any(|v| v.len() != ld)
            || proof.g_open.len() != E * sp.len()
            || proof.g_roots.len() != n
        {
            return Err("wrong number of sumcheck rounds".into());
        }
        if sp.iter().any(|(nm, _, dg)| rd[nm].iter().any(|v| v.len() != E * (dg + 1))) {
            return Err("sumcheck round messages of the wrong shape".into());
        }
        let gm = GMask::new(sp, 0, pr.k_l, E);
        let mut m = MaskZ::<E>::from_wire(gm, &proof.g_roots, &proof.g_open, &mut tr);
        m.msgs = rd.iter().map(|(k, v)| (k.clone(), v.iter().map(|x| gmask::unflat::<E>(x)).collect())).collect();
        mz = Some(m);
    } else if rr.keys().map(|s| s.as_str()).ne(["b", "bg", "z1", "z2"]) || rr.values().any(|v| v.len() != ld) {
        return Err("wrong number of sumcheck rounds".into());
    }
    let mut sched = Sched::<E>::default();
    for name in ["z1", "z2", "b", "bg"] {
        let tau = ext::chal::<E>(&mut tr, ld);
        let mut rs = Vec::new();
        for rnd in 0..ld {
            if mz.is_some() {
                tr.absorb(|h| {
                    h.s("scr").list(&proof.rounds[name][rnd]);
                });
            } else {
                tr.absorb(|h| {
                    h.s("scr").list_hx(&rr[name][rnd]);
                });
            }
            rs.push(ext::chal1::<E>(&mut tr));
        }
        sched.scs.insert(name.into(), (tau, rs));
    }
    if let Some(m) = &mz {
        // cut D: the round sums in the clear (bg's claim is public: rho G)
        for (nm, _, dg) in &m.gm.specs {
            let c0 = if nm == "bg" { Some(ext::mul(m.rho, m.g[nm])) } else { None };
            gmask::check_rounds::<E>(nm, &m.msgs[nm], &sched.scs[nm].1, *dg, c0)?;
        }
    }
    for _ in 0..2 {
        let rc = ext::chal::<E>(&mut tr, ld);
        let r2 = ext::chal::<E>(&mut tr, ld);
        sched.r1.push((rc, r2));
    }
    if bind {
        sched.rb = Some(ext::chal::<E>(&mut tr, ld));
    }
    let ev = evals_of(&sched);
    let lay = row_layout_g(ld, &sh, &ev, pr.k_l, E, mz.as_ref().map(|m| m.gm.nrows));
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
    let nrows = lay.nrows;
    let ng = lay.ng;
    let masked = mz.is_some();
    let sys = SpineSys::<E> { kl: pr.k_l, shapes: ev.iter().map(|(k, _)| sh[k].clone()).collect(), ev, cols, lay, sched, mz };
    let mut groups: Vec<Vec<Hash>> = Vec::new();
    let mut sizes;
    if masked {
        groups.push(proof.g_roots.clone());
        sizes = vec![ng];
        sizes.push(nrows - ng);
    } else {
        for nm in ["z1", "z2", "b", "bg"] {
            for i in 0..ld {
                groups.push(rr[nm][i].clone());
            }
        }
        sizes = vec![1usize; 4 * ld];
        sizes.push(nrows - 4 * ld);
    }
    groups.push(proof.eval_roots.clone());
    let quad = vec![sys.lay.prod];
    ligero::verify(lp, n, &groups, &sizes, &proof.mask_roots, &sys, &quad, &proof.ligero, &mut tr)
}

/// Beaver triples the spine's sumcheck rounds consume at EXT = 1 (three degree-2 matvec sumchecks and the degree-3
/// Hadamard zerocheck over d entries): sum over rounds of (deg + 1) * half = 9 (d - 1) + 4 (d - 1).
pub fn beaver_count(d: usize) -> usize {
    13 * (d - 1)
}

/// The same under EXT = e, by the tables' structural lengths: round 0 of a matvec sumcheck multiplies an F_{p^e}
/// table by a base vector (2 triples per product at e = 2), round 0 of bg two base vectors (1), every later round
/// two F_{p^e} tables (3).
pub fn beaver_count_e(d: usize, e: usize) -> usize {
    if e == 1 {
        return beaver_count(d);
    }
    let ld = log2(d);
    let mut tot = 0;
    for (deg, first) in [(2usize, 2usize), (2, 2), (2, 2), (3, 1)] {
        for rnd in 0..ld {
            let half = d >> (rnd + 1);
            tot += (deg + 1) * half * if rnd == 0 { first } else { 3 };
        }
    }
    tot
}
