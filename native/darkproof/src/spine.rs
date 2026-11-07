//! cosnark_zk.py: the spine with ZK layers 2-3. `prove` is ONE custodian's prover (all exchanges through `Net`);
//! `verify` is the public verifier.
use crate::field;
use crate::h::{Hash, Py};
use crate::ligero::{self, LigParams, LigParty, LigProof, LinSink, LinSystem};
use crate::net::{gather_hashes, Net};
use crate::pcs::{self, colsums, PcsCols, PcsParty, Shape};
use crate::rng::Det;
use crate::spdz::{cmul, lin2, shadd, shsub, Sh, Spdz};
use crate::transcript::{eqv, lagc, mle, Transcript};
use crate::{Ctx, Profile};
use rayon::prelude::*;
use std::collections::BTreeMap;

pub const VEC: [&str; 9] = ["x", "z1", "h", "z2", "d2", "b", "g1", "bg", "d1"];
pub const MAT: [&str; 4] = ["W1", "W2", "W1n", "W2n"];
pub const NPROD: usize = 6;

#[derive(Clone, Debug, PartialEq)]
pub struct SpineProof {
    pub roots: BTreeMap<String, Vec<Hash>>,
    pub round_roots: BTreeMap<String, Vec<Vec<Hash>>>,
    pub eval_roots: Vec<Hash>,
    pub mask_roots: Vec<Hash>,
    pub prox: BTreeMap<String, Vec<Vec<u64>>>,
    pub pcs_cols: BTreeMap<String, PcsCols>,
    pub ligero: LigProof,
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

fn cat(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    v
}

/// The schedule's challenges: (tau, rs) per sumcheck in order z1, z2, b, bg; (rc, rr) per rank-1; rb.
#[derive(Clone, Debug, Default)]
pub struct Sched {
    pub scs: BTreeMap<String, (Vec<u64>, Vec<u64>)>,
    pub r1: Vec<(Vec<u64>, Vec<u64>)>,
    pub rb: Option<Vec<u64>>,
}

pub fn evals_of(s: &Sched) -> Evals {
    let mut ev: Evals = Vec::new();
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
    pub rows: BTreeMap<String, Vec<usize>>,
    pub urows: Vec<Vec<usize>>,
    pub prod: (usize, usize, usize),
    pub nrows: usize,
}

pub fn row_layout(ld: usize, sh: &BTreeMap<String, Shape>, ev: &Evals, kl: usize) -> Layout {
    let mut rows = BTreeMap::new();
    let mut nxt = 0;
    for name in ["z1", "z2", "b", "bg"] {
        rows.insert(name.to_string(), (nxt..nxt + ld).collect());
        nxt += ld;
    }
    let mut urows = Vec::new();
    for (k, _) in ev {
        let nr = sh[k].w.div_ceil(kl);
        urows.push((nxt..nxt + nr).collect());
        nxt += nr;
    }
    Layout { rows, urows, prod: (nxt, nxt + 1, nxt + 2), nrows: nxt + 3 }
}

/// The verifier's checks as Ligero constraints (cosnark_zk.constraints).
pub struct SpineSys {
    pub kl: usize,
    pub ev: Evals,
    pub shapes: Vec<Shape>,
    /// per evaluation's commitment: (opened columns, column sums)
    pub cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    pub lay: Layout,
    pub sched: Sched,
}

struct Em<'a> {
    sink: &'a mut dyn LinSink,
    buf: Vec<(u32, u32, u64)>,
}
impl Em<'_> {
    fn cell(&mut self, r: usize, pos: usize, c: u64) {
        self.buf.push((r as u32, pos as u32, c));
    }
    fn done(&mut self, label: &str, rhs: u64) {
        self.sink.con(label, &self.buf, rhs);
        self.buf.clear();
    }
}

impl SpineSys {
    fn y(&self, em: &mut Em, e: usize, coef: u64) {
        let (k, pt) = &self.ev[e];
        let s = &self.shapes[e];
        let _ = k;
        let b = eqv(&pt[..s.mc]);
        for c in 0..s.c {
            em.cell(self.lay.urows[e][c / self.kl], c % self.kl, field::mul(coef, b[c]));
        }
    }
    fn sumcheck(&self, em: &mut Em, name: &str, deg: usize, first: Option<usize>, fin: &dyn Fn(&mut Em)) {
        let (_, rs) = &self.sched.scs[name];
        let r = &self.lay.rows[name];
        em.cell(r[0], 0, 1);
        em.cell(r[0], 1, 1);
        if let Some(e) = first {
            self.y(em, e, field::p() - 1);
        }
        em.done(&format!("sumcheck {name}: first round sum = claim"), 0);
        for i in 1..r.len() {
            let lc = lagc(deg, rs[i - 1]);
            em.cell(r[i], 0, 1);
            em.cell(r[i], 1, 1);
            for j in 0..=deg {
                em.cell(r[i - 1], j, field::neg(lc[j]));
            }
            em.done(&format!("sumcheck {name}: round sums"), 0);
        }
        let lc = lagc(deg, *rs.last().unwrap());
        for j in 0..=deg {
            em.cell(*r.last().unwrap(), j, lc[j]);
        }
        fin(em);
        em.done(&format!("sumcheck {name}: final claim = product gate"), 0);
    }
}

pub fn pcs_consistency(
    em_sink: &mut dyn LinSink,
    kl: usize,
    ev: &Evals,
    shapes: &[Shape],
    cols: &BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: &[Vec<usize>],
) {
    let mut buf: Vec<(u32, u32, u64)> = Vec::new();
    for (e, (k, pt)) in ev.iter().enumerate() {
        let s = &shapes[e];
        let a = s.eval_weights(pt);
        let (jj, csum) = &cols[k];
        let label = format!("PCS evaluation consistency ({k})");
        for (t, &j) in jj.iter().enumerate() {
            let x = s.dom.point(j);
            let mut xs = 1u64;
            buf.clear();
            for c in 0..s.w {
                buf.push((urows[e][c / kl] as u32, (c % kl) as u32, xs));
                xs = field::mul(xs, x);
            }
            let n = a.len().min(csum[t].len());
            em_sink.con(&label, &buf, field::dot(&a[..n], &csum[t][..n]));
        }
    }
}

impl LinSystem for SpineSys {
    fn emit(&self, sink: &mut dyn LinSink) {
        pcs_consistency(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.lay.urows);
        let mut em = Em { sink, buf: Vec::new() };
        let (x, yr, zr) = self.lay.prod;
        for (q, name, idx) in [(0usize, "z1", 0usize), (1, "z2", 3), (2, "b", 6)] {
            self.sumcheck(&mut em, name, 2, Some(idx), &|em: &mut Em| em.cell(zr, q, field::p() - 1));
            em.cell(x, q, 1);
            self.y(&mut em, idx + 2, field::p() - 1);
            em.done(&format!("product {q} operands"), 0);
            em.cell(yr, q, 1);
            self.y(&mut em, idx + 1, field::p() - 1);
            em.done(&format!("product {q} operands"), 0);
        }
        let (tau, rs) = &self.sched.scs["bg"];
        let eq = mle(&eqv(tau), rs);
        self.sumcheck(&mut em, "bg", 3, None, &|em: &mut Em| {
            em.cell(zr, 3, field::neg(eq));
            self.y(em, 11, eq);
        });
        em.cell(x, 3, 1);
        self.y(&mut em, 9, field::p() - 1);
        em.done("product 3 operands", 0);
        em.cell(yr, 3, 1);
        self.y(&mut em, 10, field::p() - 1);
        em.done("product 3 operands", 0);
        for (q, base) in [(4usize, 12usize), (5, 16)] {
            let wn = if q == 4 { "W1n" } else { "W2n" };
            self.y(&mut em, base, 1);
            self.y(&mut em, base + 1, field::p() - 1);
            em.cell(zr, q, 1);
            em.done(&format!("rank-1 update {wn}: W'(r) = W(r) - d(r_row) v(r_col)"), 0);
            em.cell(x, q, 1);
            self.y(&mut em, base + 2, field::p() - 1);
            em.done(&format!("product {q} operands"), 0);
            em.cell(yr, q, 1);
            self.y(&mut em, base + 3, field::p() - 1);
            em.done(&format!("product {q} operands"), 0);
        }
        if self.ev.len() == 22 {
            self.y(&mut em, 20, 1);
            self.y(&mut em, 21, field::p() - 1);
            em.done("signed input binding: the custodians' x = the owner's signed x", 0);
        }
    }
}

// ------------------------------------------------------------------------------------------------ prover
/// A sumcheck's per-party state (cb in prove_zk).
pub struct Sc {
    pub f: Vec<Sh>,
    pub g: Vec<Sh>,
    pub sub: Option<Vec<Sh>>,
    pub eq: Option<Vec<u64>>,
    pub deg: usize,
    pub claim: Option<u64>,
    pub last: Vec<u64>,
}

pub fn fold_sh(t: &[Sh], r: u64) -> Vec<Sh> {
    let om = field::one_minus(r);
    t.par_chunks(2).map(|c| lin2(om, c[0], r, c[1])).collect()
}

/// One round: every value of the round polynomial at X = 0..deg, as this party's SPDZ shares.
pub fn round_vals(sp: &mut Spdz, net: &mut dyn Net, st: &Sc) -> Vec<Sh> {
    let half = st.f.len() / 2;
    let deg = st.deg;
    let mut xs = Vec::with_capacity((deg + 1) * half);
    let mut ys = Vec::with_capacity((deg + 1) * half);
    for xv in 0..=deg as u64 {
        let om = field::one_minus(xv);
        let (fx, gx): (Vec<Sh>, Vec<Sh>) = (0..half)
            .into_par_iter()
            .map(|k| (lin2(om, st.f[2 * k], xv, st.f[2 * k + 1]), lin2(om, st.g[2 * k], xv, st.g[2 * k + 1])))
            .unzip();
        xs.extend(fx);
        ys.extend(gx);
    }
    let prods = sp.mul_batch(net, &xs, &ys);
    (0..=deg)
        .map(|xv| {
            let om = field::one_minus(xv as u64);
            let xv64 = xv as u64;
            (0..half)
                .into_par_iter()
                .map(|k| {
                    let mut term = prods[xv * half + k];
                    if let Some(sub) = &st.sub {
                        term = shsub(term, lin2(om, sub[2 * k], xv64, sub[2 * k + 1]));
                    }
                    if let Some(eq) = &st.eq {
                        let e = field::add(field::mul(eq[2 * k], om), field::mul(eq[2 * k + 1], xv64));
                        term = cmul(e, term);
                    }
                    term
                })
                .reduce(|| (0, 0), shadd)
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

/// Plain (unauthenticated) products in the spine's Ligero: the six evaluation-pair products.
pub const LIG_SCALARS: usize = 6;

pub struct SpineOut {
    pub proof: SpineProof,
    pub coms: BTreeMap<String, PcsParty>,
    pub lig_rows: Vec<Vec<u64>>,
    pub sys: SpineSys,
    pub quad: Vec<(usize, usize, usize)>,
    pub stats: BTreeMap<String, u64>,
}

/// cosnark_zk.prove_zk for custodian `inp.i`. carry: the previous step's child commitments (W1, W2), carried with
/// their openings; owner_x: this party's part of the owner's x commitment.
pub fn prove(
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
    let mut sched = Sched::default();
    let mut round_roots: BTreeMap<String, Vec<Vec<Hash>>> = BTreeMap::new();
    let tables = [("z1", "W1", "x", false), ("z2", "W2", "h", false), ("b", "W2", "d2", true)];
    let nsc = tables.len() + 1;
    for sci in 0..nsc {
        let name = if sci < 3 { tables[sci].0 } else { "bg" };
        let tau = tr.chal(ld);
        let mut rs: Vec<u64> = Vec::new();
        let mut st: Sc;
        if name == "bg" {
            // The harness starts this claim at 0 and re-centres every round on it, a no-op whenever bg = b * g1
            // holds (every honest step and every attack row). Natively it is not run: it would open the hidden
            // round sums.
            st = Sc {
                f: w["b"].clone(),
                g: w["g1"].clone(),
                sub: Some(w["bg"].clone()),
                eq: Some(eqv(&tau)),
                deg: 3,
                claim: None,
                last: vec![],
            };
        } else {
            let (_, wk, vk, tp) = tables[sci];
            let wm = &w[wk];
            let et = eqv(&tau);
            let f: Vec<Sh> = (0..d)
                .into_par_iter()
                .map(|j| {
                    let mut acc: Sh = (0, 0);
                    for ii in 0..d {
                        let wv = if !tp { wm[ii * d + j] } else { wm[j * d + ii] };
                        acc = shadd(acc, cmul(et[ii], wv));
                    }
                    acc
                })
                .collect();
            let mut claim = None;
            if attack == "forge_sumcheck" && name == "z1" {
                // colluders broadcast their committed z1 shares to target the forged z1's MLE
                let z1 = com["z1"].ext.clone();
                let s = &com["z1"].shape;
                let mine: Vec<u64> = (0..s.rd).flat_map(|r| z1[r * s.w..r * s.w + s.c].to_vec()).collect();
                let all = net.all_gather(mine);
                let zsum: Vec<u64> =
                    (0..all[0].len()).map(|k| all.iter().fold(0, |a, v| field::add(a, v[k]))).collect();
                claim = Some(mle(&zsum, &tau));
            }
            st = Sc { f, g: w[vk].clone(), sub: None, eq: None, deg: 2, claim, last: vec![] };
        }
        for rnd in 0..ld {
            if rnd > 0 {
                let r = *rs.last().unwrap();
                st.f = fold_sh(&st.f, r);
                st.g = fold_sh(&st.g, r);
                if let Some(s) = &st.sub {
                    st.sub = Some(fold_sh(s, r));
                }
                if let Some(e) = &st.eq {
                    let om = field::one_minus(r);
                    st.eq = Some(e.chunks(2).map(|c| field::add(field::mul(c[0], om), field::mul(c[1], r))).collect());
                }
                if st.claim.is_some() {
                    st.claim = Some(lag3(&st.last, r));
                }
            }
            let vals = round_vals(sp, net, &st);
            let mut shares: Vec<u64> = vals.iter().map(|v| v.0).collect();
            if let Some(claim) = st.claim {
                let all = net.all_gather(shares.clone());
                let plain: Vec<u64> =
                    (0..=st.deg).map(|x| all.iter().fold(0, |a, v| field::add(a, v[x]))).collect();
                let fix = field::mul(field::sub(field::sub(claim, plain[0]), plain[1]), field::inv(2));
                if i == 0 {
                    shares = shares.iter().map(|&v| field::add(v, fix)).collect();
                }
                st.last = plain.iter().map(|&v| field::add(v, fix)).collect();
            }
            lg.add_row(&shares);
            let rts = lg.commit(net);
            tr.absorb(|h| {
                h.s("scr").list_hx(&rts);
            });
            round_roots.entry(name.to_string()).or_default().push(rts);
            rs.push(tr.chal1());
        }
        sched.scs.insert(name.to_string(), (tau, rs));
    }
    tt.lap("sumchecks");
    for _ in 0..2 {
        let rc = tr.chal(ld);
        let rr = tr.chal(ld);
        sched.r1.push((rc, rr));
    }
    if bind {
        sched.rb = Some(tr.chal(ld));
    }
    let ev = evals_of(&sched);
    let shp: BTreeMap<String, Shape> = com.iter().map(|(k, c)| (k.clone(), c.shape.clone())).collect();
    let lay = row_layout(ld, &shp, &ev, kl);
    let mut ys: Vec<u64> = Vec::with_capacity(ev.len());
    for (k, pt) in &ev {
        let c = &com[k];
        let (mut u, mut y) = c.eval_share(pt);
        if attack == "lie_in_u" && k == "W1n" && i == 0 {
            let s = &c.shape;
            let hon = honest_w1n.as_ref().unwrap();
            let mut ext = c.ext.clone();
            for r in 0..s.rd {
                ext[r * s.w..r * s.w + s.c].copy_from_slice(&hon[r * s.c..(r + 1) * s.c]);
            }
            let tmp = PcsParty { ext, ..shallow(c) };
            let (u2, y2) = tmp.eval_share(pt);
            u = u2;
            y = y2;
        }
        ys.push(y);
        for s0 in (0..c.shape.w).step_by(kl) {
            lg.add_row(&u[s0..(s0 + kl).min(c.shape.w)]);
        }
    }
    tt.lap("evaluation rows");
    let pairs = [(2usize, 1usize), (5, 4), (8, 7), (9, 10), (14, 15), (18, 19)];
    let xs: Vec<u64> = pairs.iter().map(|&(a, _)| ys[a]).collect();
    let yv: Vec<u64> = pairs.iter().map(|&(_, b)| ys[b]).collect();
    let zs = lg.mul_plain_batch(net, &xs, &yv);
    lg.add_row(&xs);
    lg.add_row(&yv);
    lg.add_row(&zs);
    let eval_roots = lg.commit(net);
    let mask_roots = lg.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    tt.lap("ligero commits");
    let (prox, pcs_cols) = pcs_prove(pr, &mut com, &mut tr, net, n)?;
    tt.lap("pcs openings");
    let cols = pcs_cols.iter().map(|(k, c)| (k.clone(), (c.j.clone(), colsums(c, com[k].shape.r)))).collect();
    let sys = SpineSys { kl, shapes: ev.iter().map(|(k, _)| shp[k].clone()).collect(), ev, cols, lay, sched };
    let quad = vec![sys.lay.prod];
    let lig = lg.prove(net, &mut tr, &sys, &quad);
    tt.lap("ligero prove");
    sp.mac_check(net, "cosnark-zk")?;
    tt.lap("mac check");
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
    };
    Ok(SpineOut { proof, coms: com, lig_rows: lg.rows.clone(), sys, quad, stats })
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
    let mut prox = BTreeMap::new();
    for (k, c) in com.iter() {
        let s = &c.shape;
        let gam = s.prox_weights(tr.chal(s.prox_len()));
        let mine = c.row_combo(&gam);
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
        let mine: Vec<pcs::Opening> = jj.par_iter().map(|&j| c.open(j)).collect();
        let all = ligero::gather_openings(net, vec![mine]);
        let _ = n;
        cols.insert(k.clone(), PcsCols { j: jj, open: all.into_iter().next().unwrap() });
    }
    Ok((prox, cols))
}

// ------------------------------------------------------------------------------------------------ verifier
/// cosnark_zk.verify_zk: public data only.
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
    if rr.keys().map(|s| s.as_str()).ne(["b", "bg", "z1", "z2"]) || rr.values().any(|v| v.len() != ld) {
        return Err("wrong number of sumcheck rounds".into());
    }
    let mut sched = Sched::default();
    for name in ["z1", "z2", "b", "bg"] {
        let tau = tr.chal(ld);
        let mut rs = Vec::new();
        for rnd in 0..ld {
            tr.absorb(|h| {
                h.s("scr").list_hx(&rr[name][rnd]);
            });
            rs.push(tr.chal1());
        }
        sched.scs.insert(name.into(), (tau, rs));
    }
    for _ in 0..2 {
        let rc = tr.chal(ld);
        let r2 = tr.chal(ld);
        sched.r1.push((rc, r2));
    }
    if bind {
        sched.rb = Some(tr.chal(ld));
    }
    let ev = evals_of(&sched);
    let lay = row_layout(ld, &sh, &ev, pr.k_l);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    let keys: Vec<String> = sh.keys().cloned().collect();
    let shv: Vec<Shape> = sh.values().cloned().collect();
    let rootv: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
    let proxv: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| proof.prox[k].clone()).collect();
    let colv: Vec<PcsCols> = keys.iter().map(|k| proof.pcs_cols[k].clone()).collect();
    pcs::verify(pr, &keys, &shv, &rootv, &proxv, &colv, &mut tr, n)?;
    let cols = keys
        .iter()
        .map(|k| (k.clone(), (proof.pcs_cols[k].j.clone(), colsums(&proof.pcs_cols[k], sh[k].r))))
        .collect();
    let nrows = lay.nrows;
    let sys = SpineSys { kl: pr.k_l, shapes: ev.iter().map(|(k, _)| sh[k].clone()).collect(), ev, cols, lay, sched };
    let mut groups: Vec<Vec<Hash>> = Vec::new();
    for nm in ["z1", "z2", "b", "bg"] {
        for i in 0..ld {
            groups.push(rr[nm][i].clone());
        }
    }
    groups.push(proof.eval_roots.clone());
    let mut sizes = vec![1usize; 4 * ld];
    sizes.push(nrows - 4 * ld);
    let quad = vec![sys.lay.prod];
    ligero::verify(lp, n, &groups, &sizes, &proof.mask_roots, &sys, &quad, &proof.ligero, &mut tr)
}

/// Beaver triples the spine's sumcheck rounds consume (three degree-2 matvec sumchecks and the degree-3 Hadamard
/// zerocheck over d entries): sum over rounds of (deg + 1) * half = 9 (d - 1) + 4 (d - 1).
pub fn beaver_count(d: usize) -> usize {
    13 * (d - 1)
}
