//! cozk.py: collaborative zero-knowledge Ligero over additive shares, split per custodian (`LigParty` is one
//! custodian's state; openings go through `Net`), and the public verifier.
use crate::field;
use crate::h::{h_leaf, h_pad, Hash};
use crate::net::{gather_hashes, Net};
use crate::pcs::{auth_path, bitlen, merkle_levels, verify_path, Opening};
use crate::poly::{self, lagrange_basis, padd, peval, pmul, pscale};
use crate::rng::{salt, Coins, Det};
use crate::transcript::Transcript;
use pycompat::PyRandom;
use rayon::prelude::*;

pub struct LigParams {
    pub k: usize,
    pub t: usize,
    pub tt: usize,
    pub npts: usize,
    pub zeta: Vec<u64>,
    pub l: Vec<Vec<u64>>,
    pub lz: Vec<Vec<u64>>,
    pub vz: Vec<u64>,
    /// pw[j] = powers of (j + 1), length 2(k + t) - 1
    pub pw: Vec<Vec<u64>>,
}

impl LigParams {
    pub fn new(k: usize, t: usize, tt: usize, blow: usize) -> Self {
        assert!(tt <= t);
        let zeta: Vec<u64> = (0..k).map(|i| field::p() - 1 - i as u64).collect();
        let eta: Vec<u64> = (0..t).map(|l| field::p() - 1 - k as u64 - l as u64).collect();
        let mut nodes = zeta.clone();
        nodes.extend(&eta);
        let l = lagrange_basis(&nodes);
        let lz = lagrange_basis(&zeta);
        let mut vz = vec![1u64];
        for &z in &zeta {
            vz = pmul(&vz, &[field::neg(z), 1]);
        }
        let npts = blow * (k + t);
        let maxlen = 2 * (k + t) - 1;
        let pw = (0..npts).map(|j| poly::powers((j + 1) as u64, maxlen)).collect();
        LigParams { k, t, tt, npts, zeta, l, lz, vz, pw }
    }
    pub fn interp(&self, vals: &[u64]) -> Vec<u64> {
        poly::combine(vals, &self.l, self.k + self.t)
    }
    pub fn interp_z(&self, alpha: &[u64]) -> Vec<u64> {
        poly::combine(alpha, &self.lz, self.k)
    }
    pub fn code(&self, f: &[u64]) -> Vec<u64> {
        (0..self.npts).map(|j| field::dot(f, &self.pw[j][..f.len()])).collect()
    }
    pub fn path_len(&self) -> usize {
        bitlen(self.npts - 1) + 1
    }
}

/// One linear constraint: terms (row, pos, coef) (repeated cells add up) and its right-hand side.
pub trait LinSink {
    fn con(&mut self, label: &str, terms: &[(u32, u32, u64)], rhs: u64);
}

/// Something that emits the linear constraints in order (called more than once: count, then accumulate).
pub trait LinSystem: Sync {
    fn emit(&self, sink: &mut dyn LinSink);
}

pub struct Counter {
    pub n: usize,
    pub rhs: Vec<u64>,
}
impl LinSink for Counter {
    fn con(&mut self, _l: &str, _t: &[(u32, u32, u64)], rhs: u64) {
        self.n += 1;
        self.rhs.push(rhs);
    }
}

struct Alpha<'a> {
    rr: &'a [u64],
    idx: usize,
    alpha: Vec<Vec<u64>>,
}
impl LinSink for Alpha<'_> {
    fn con(&mut self, _l: &str, terms: &[(u32, u32, u64)], _rhs: u64) {
        let c = self.rr[self.idx];
        self.idx += 1;
        for &(r, pos, a) in terms {
            let s = &mut self.alpha[r as usize][pos as usize];
            *s = field::add(*s, field::mul(c, a));
        }
    }
}

/// DIAGNOSTIC (prover side, plaintext): cosnark_zk.first_violated.
pub struct FirstViolated<'a> {
    pub rows: &'a [Vec<u64>],
    pub found: Option<String>,
}
impl LinSink for FirstViolated<'_> {
    fn con(&mut self, label: &str, terms: &[(u32, u32, u64)], rhs: u64) {
        if self.found.is_some() {
            return;
        }
        let v = terms.iter().fold(0u64, |acc, &(r, pos, c)| {
            field::add(acc, field::mul(c, self.rows[r as usize][pos as usize]))
        });
        if v != rhs {
            self.found = Some(label.to_string());
        }
    }
}

pub fn first_violated(rows: &[Vec<u64>], sys: &dyn LinSystem, quad: &[(usize, usize, usize)]) -> Option<String> {
    let mut fv = FirstViolated { rows, found: None };
    sys.emit(&mut fv);
    if fv.found.is_some() {
        return fv.found;
    }
    for &(x, y, z) in quad {
        for pos in 0..rows[x].len() {
            if field::mul(rows[x][pos], rows[y][pos]) != rows[z][pos] {
                return Some(format!("product gate {pos}"));
            }
        }
    }
    None
}

fn alpha_of(sys: &dyn LinSystem, rr: &[u64], nrows: usize, k: usize) -> Vec<Vec<u64>> {
    let mut a = Alpha { rr, idx: 0, alpha: vec![vec![0u64; k]; nrows] };
    sys.emit(&mut a);
    a.alpha
}

pub struct Group {
    pub rows: Vec<usize>,
    pub codes: Vec<Vec<u64>>,
    pub tree: Vec<Vec<Hash>>,
    pub salts: Vec<Hash>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LigProof {
    pub w: Vec<u64>,
    pub q: Vec<u64>,
    pub pq: Vec<u64>,
    /// group (commit order, then the mask group) -> party -> opened column
    pub cols: Vec<Vec<Vec<Opening>>>,
    /// the opened column indices (on the wire only under multiproofs; the verifier checks them against its own draw)
    pub j: Vec<usize>,
}

/// One custodian's Ligero prover state.
pub struct LigParty<'p> {
    pub pp: &'p LigParams,
    pub i: usize,
    pub n: usize,
    det: bool,
    rng: Coins,
    /// the ideal dealer's stream (the harness: cozk's dealer under the hook, or one stream the in-process harness
    /// gives every party through with_dealer); None in the deployed run, which takes its triples from the tape
    dealer: Option<PyRandom>,
    /// this party's tape triples (value shares of authenticated triples; the MAC shares are unused: the quadratic
    /// test checks z = x y). None: the ideal dealer stream.
    tape: Option<(Vec<(u64, u64, u64)>, usize)>,
    /// this party's shares of every row's k message values (row-major, commit order)
    pub rows: Vec<Vec<u64>>,
    pub polys: Vec<Vec<u64>>,
    pub groups: Vec<Group>,
    pending: Vec<usize>,
    masks: Vec<Vec<u64>>,
    mask_group: Option<Group>,
    pub wire: u64,
    pub scalar_triples: u64,
    pub poly_triples: u64,
}

/// _share(v, n, p, rng) from the ideal dealer: every party's share; party i keeps share i.
fn deal(dealer: &mut PyRandom, v: &[u64], n: usize, i: usize) -> Vec<u64> {
    let mut xs: Vec<Vec<u64>> = Vec::with_capacity(n);
    for _ in 0..n - 1 {
        xs.push(v.iter().map(|_| dealer.randrange_u64(field::p())).collect());
    }
    if i < n - 1 {
        return xs.swap_remove(i);
    }
    v.iter()
        .enumerate()
        .map(|(c, &x)| xs.iter().fold(x, |acc, s| field::sub(acc, s[c])))
        .collect()
}

impl<'p> LigParty<'p> {
    /// seed_label = str((seed, context)) as cozk.Prover receives it.
    pub fn new(pp: &'p LigParams, i: usize, n: usize, seed_label: &str, det: &Det) -> Self {
        let (rng, dealer, on) = match det.on() {
            true => (
                det.coins(&["cozk", seed_label, "party", &i.to_string()]),
                det.rng(&["cozk", seed_label, "dealer"]),
                true,
            ),
            // real runs: OS coins; triples from the tape (with_tape), or from an ideal dealer stream the in-process
            // harness gives every party identically through `with_dealer`
            false => (crate::rng::secret_coins(), None, false),
        };
        LigParty {
            pp,
            i,
            n,
            det: on,
            rng,
            dealer,
            tape: None,
            rows: Vec::new(),
            polys: Vec::new(),
            groups: Vec::new(),
            pending: Vec::new(),
            masks: Vec::new(),
            mask_group: None,
            wire: 0,
            scalar_triples: 0,
            poly_triples: 0,
        }
    }

    /// Take the products' triples from this party's tape instead of a dealer (the deployed run).
    pub fn with_tape(mut self, t: Vec<(u64, u64, u64)>) -> Self {
        self.tape = Some((t, 0));
        self
    }

    /// Triples a tape must hold for one cozk proof with `scalars` plain products and `quads` row triples:
    /// one per plain product, 2 (k + t) - 1 per polynomial triple (tape mode builds it pointwise).
    pub fn tape_triples(pp: &LigParams, scalars: usize, quads: usize) -> usize {
        scalars + quads * (2 * (pp.k + pp.t) - 1)
    }

    fn scalar_triple(&mut self) -> (u64, u64, u64) {
        let (n, i) = (self.n, self.i);
        if let Some((t, pos)) = &mut self.tape {
            let x = *t.get(*pos).expect("the tape's Ligero triples are exhausted");
            *pos += 1;
            return x;
        }
        let dl = self.dealer.as_mut().expect("no tape and no ideal dealer for the Ligero's triples");
        let a = dl.randrange_u64(field::p());
        let b = dl.randrange_u64(field::p());
        let ai = deal(dl, &[a], n, i)[0];
        let bi = deal(dl, &[b], n, i)[0];
        let ci = deal(dl, &[field::mul(a, b)], n, i)[0];
        (ai, bi, ci)
    }

    /// One polynomial triple (a, b, a b) of degree < deg, this party's shares. Dealer mode: cozk's ideal dealer.
    /// Tape mode: each party picks its own random share polynomials of a and b, the shares of a(x), b(x) at the 2 deg - 1
    /// points x = 0 .. 2 deg - 2 are multiplied with tape triples, and c is interpolated locally.
    fn poly_triple(&mut self, net: &mut dyn Net, deg: usize) -> (Vec<u64>, Vec<u64>, Vec<u64>) {
        let (n, i) = (self.n, self.i);
        if self.tape.is_none() {
            let dl = self.dealer.as_mut().expect("no tape and no ideal dealer for the Ligero's triples");
            let a: Vec<u64> = (0..deg).map(|_| dl.randrange_u64(field::p())).collect();
            let b: Vec<u64> = (0..deg).map(|_| dl.randrange_u64(field::p())).collect();
            let cpoly = pmul(&a, &b);
            let as_ = deal(dl, &a, n, i);
            let bs_ = deal(dl, &b, n, i);
            let cs_ = deal(dl, &cpoly, n, i);
            return (as_, bs_, cs_);
        }
        let a: Vec<u64> = (0..deg).map(|_| self.rng.randrange_u64(field::p())).collect();
        let b: Vec<u64> = (0..deg).map(|_| self.rng.randrange_u64(field::p())).collect();
        let m = 2 * deg - 1;
        let ev = |f: &[u64], x: u64| f.iter().rev().fold(0u64, |acc, &c| field::add(field::mul(acc, x), c));
        let ea: Vec<u64> = (0..m as u64).map(|x| ev(&a, x)).collect();
        let eb: Vec<u64> = (0..m as u64).map(|x| ev(&b, x)).collect();
        let ec = self.mul_plain_batch(net, &ea, &eb);
        self.scalar_triples -= m as u64;
        let c = crate::step::interpolate(&ec);
        (a, b, c)
    }

    /// Replace the dealer stream (all parties must hold the same one: the ideal dealer).
    pub fn with_dealer(mut self, d: PyRandom) -> Self {
        self.dealer = Some(d);
        self
    }

    pub fn add_row(&mut self, share: &[u64]) -> usize {
        let pp = self.pp;
        assert!(share.len() <= pp.k);
        let mut vals = share.to_vec();
        vals.resize(pp.k, 0);
        self.rows.push(vals.clone());
        for _ in 0..pp.t {
            vals.push(self.rng.randrange_u64(field::p()));
        }
        self.polys.push(pp.interp(&vals));
        self.pending.push(self.rows.len() - 1);
        self.rows.len() - 1
    }

    fn commit_polys(&mut self, polys: &[&Vec<u64>]) -> (Vec<Vec<u64>>, Vec<Vec<Hash>>, Vec<Hash>) {
        let pp = self.pp;
        let codes: Vec<Vec<u64>> = polys.par_iter().map(|f| pp.code(f)).collect();
        let salts: Vec<Hash> = (0..pp.npts).map(|_| salt(&mut self.rng)).collect();
        let mut level: Vec<Hash> = (0..pp.npts)
            .into_par_iter()
            .map(|j| {
                let col: Vec<u64> = codes.iter().map(|c| c[j]).collect();
                h_leaf(&salts[j], &col)
            })
            .collect();
        let full = 1usize << bitlen(pp.npts - 1);
        for j in 0..full - pp.npts {
            level.push(h_pad(j as u64));
        }
        let tree = merkle_levels(level);
        (codes, tree, salts)
    }

    /// Commit the rows added since the last commit as one group; returns every party's root.
    pub fn commit(&mut self, net: &mut dyn Net) -> Vec<Hash> {
        let idx = std::mem::take(&mut self.pending);
        let polys: Vec<&Vec<u64>> = idx.iter().map(|&r| &self.polys[r]).collect();
        let polys: Vec<Vec<u64>> = polys.into_iter().cloned().collect();
        let refs: Vec<&Vec<u64>> = polys.iter().collect();
        let (codes, tree, salts) = self.commit_polys(&refs);
        let root = tree.last().unwrap()[0];
        self.groups.push(Group { rows: idx, codes, tree, salts });
        gather_hashes(net, &[root]).into_iter().map(|v| v[0]).collect()
    }

    pub fn commit_masks(&mut self, net: &mut dyn Net) -> Vec<Hash> {
        let pp = self.pp;
        let (k, t) = (pp.k, pp.t);
        let mp: Vec<u64> = (0..k + t).map(|_| self.rng.randrange_u64(field::p())).collect();
        let mut ml: Vec<u64> = (0..2 * k + t - 1).map(|_| self.rng.randrange_u64(field::p())).collect();
        let s = pp.zeta.iter().fold(0u64, |a, &z| field::add(a, peval(&ml, z)));
        ml[0] = field::sub(ml[0], field::mul(s, field::inv(k as u64)));
        let r: Vec<u64> = (0..k + 2 * t - 1).map(|_| self.rng.randrange_u64(field::p())).collect();
        let mq = pmul(&pp.vz, &r);
        self.masks = vec![mp, ml, mq];
        let masks = self.masks.clone();
        let refs: Vec<&Vec<u64>> = masks.iter().collect();
        let (codes, tree, salts) = self.commit_polys(&refs);
        let root = tree.last().unwrap()[0];
        self.mask_group = Some(Group { rows: vec![], codes, tree, salts });
        gather_hashes(net, &[root]).into_iter().map(|v| v[0]).collect()
    }

    /// open_poly: every party sends its share vector; returns the sum.
    fn open_poly(&mut self, net: &mut dyn Net, mine: Vec<u64>) -> Vec<u64> {
        let n = self.n as u64;
        self.wire += mine.len() as u64 * n * (n - 1);
        let all = net.all_gather(mine);
        let mut out = vec![0u64; all.iter().map(|v| v.len()).max().unwrap_or(0)];
        for v in &all {
            for (a, &b) in out.iter_mut().zip(v) {
                *a = field::add(*a, b);
            }
        }
        out
    }

    /// Shares of x_m * y_m for every pair, each with a scalar Beaver triple from the dealer (cozk mul_plain); all
    /// openings in one exchange. No MAC: the quadratic test checks z = x y.
    pub fn mul_plain_batch(&mut self, net: &mut dyn Net, xs: &[u64], ys: &[u64]) -> Vec<u64> {
        let i = self.i;
        let mut trip = Vec::with_capacity(xs.len());
        for _ in 0..xs.len() {
            trip.push(self.scalar_triple());
            self.scalar_triples += 1;
        }
        // Python opens e then f per product; the opened values and wire counts are the same in one batch
        let mut mine = Vec::with_capacity(2 * xs.len());
        for (m, &(a, b, _)) in trip.iter().enumerate() {
            mine.push(field::sub(xs[m], a));
            mine.push(field::sub(ys[m], b));
        }
        let nn = self.n as u64;
        self.wire += mine.len() as u64 * nn * (nn - 1);
        let all = net.all_gather(mine);
        trip.iter()
            .enumerate()
            .map(|(m, &(a, b, c))| {
                let e = all.iter().fold(0, |s, v| field::add(s, v[2 * m]));
                let f = all.iter().fold(0, |s, v| field::add(s, v[2 * m + 1]));
                let mut z = field::add(c, field::add(field::mul(e, b), field::mul(f, a)));
                if i == 0 {
                    z = field::add(z, field::mul(e, f));
                }
                z
            })
            .collect()
    }

    /// cozk.Prover.prove. `quad`: row triples (x, y, z).
    pub fn prove(
        &mut self,
        net: &mut dyn Net,
        tr: &mut Transcript,
        sys: &dyn LinSystem,
        quad: &[(usize, usize, usize)],
    ) -> LigProof {
        let pp = self.pp;
        let i = self.i;
        let nrows = self.rows.len();
        // proximity
        let gam = tr.chal(nrows);
        let mut wv = vec![0u64];
        for (r, &g) in gam.iter().enumerate() {
            poly::paxpy(&mut wv, g, &self.polys[r]);
        }
        poly::padd_into(&mut wv, &self.masks[0]);
        let w = self.open_poly(net, wv);
        tr.absorb(|h| {
            h.s("lig-w").list(&w);
        });
        // linear
        let mut cnt = Counter { n: 0, rhs: Vec::new() };
        sys.emit(&mut cnt);
        let rr = tr.chal(cnt.n);
        let alpha = alpha_of(sys, &rr, nrows, pp.k);
        let rp: Vec<Option<Vec<u64>>> =
            alpha.par_iter().map(|a| if a.iter().any(|&x| x != 0) { Some(pp.interp_z(a)) } else { None }).collect();
        let prods: Vec<Vec<u64>> = rp
            .par_iter()
            .zip(self.polys.par_iter())
            .filter_map(|(r, f)| r.as_ref().map(|r| pmul(r, f)))
            .collect();
        let mut qv = vec![0u64];
        for pr in &prods {
            poly::padd_into(&mut qv, pr);
        }
        poly::padd_into(&mut qv, &self.masks[1]);
        let q = self.open_poly(net, qv);
        tr.absorb(|h| {
            h.s("lig-q").list(&q);
        });
        // quadratic, one polynomial Beaver triple per row triple
        let rho = tr.chal(quad.len());
        let mut acc = self.masks[2].clone();
        for (&(rx, ry, rz), &c) in quad.iter().zip(&rho) {
            let (as_, bs_, cs_) = self.poly_triple(net, pp.k + pp.t);
            self.poly_triples += 1;
            let e = self.open_poly(net, padd(&self.polys[rx], &pscale(field::p() - 1, &as_)));
            let f = self.open_poly(net, padd(&self.polys[ry], &pscale(field::p() - 1, &bs_)));
            let ef = pmul(&e, &f);
            let mut prod = vec![0u64];
            poly::padd_into(&mut prod, &cs_);
            poly::padd_into(&mut prod, &pmul(&e, &bs_));
            poly::padd_into(&mut prod, &pmul(&f, &as_));
            if i == 0 {
                poly::padd_into(&mut prod, &ef);
            }
            let mut nacc = vec![0u64];
            poly::padd_into(&mut nacc, &acc);
            poly::paxpy(&mut nacc, c, &prod);
            poly::paxpy(&mut nacc, field::p() - c, &self.polys[rz]);
            acc = nacc;
        }
        let pq = self.open_poly(net, acc);
        tr.absorb(|h| {
            h.s("lig-p").list(&pq);
        });
        // columns
        let jj = tr.distinct_cols(pp.tt, pp.npts);
        let mine: Vec<Vec<Opening>> = self
            .groups
            .iter()
            .chain(std::iter::once(self.mask_group.as_ref().unwrap()))
            .map(|g| {
                jj.iter()
                    .map(|&j| (g.codes.iter().map(|c| c[j]).collect(), auth_path(&g.tree, &g.salts[j], j)))
                    .collect()
            })
            .collect();
        let cols = gather_openings(net, mine);
        LigProof { w, q, pq, cols, j: jj }
    }
}

/// Exchange per-group column openings so every party holds the full proof: returns group -> party -> openings.
pub fn gather_openings(net: &mut dyn Net, mine: Vec<Vec<Opening>>) -> Vec<Vec<Vec<Opening>>> {
    let enc = encode_openings(&mine);
    let all = net.all_gather(enc);
    let per_party: Vec<Vec<Vec<Opening>>> = all.iter().map(|v| decode_openings(v)).collect();
    let ng = mine.len();
    (0..ng).map(|g| per_party.iter().map(|pp| pp[g].clone()).collect()).collect()
}

pub fn encode_openings(groups: &[Vec<Opening>]) -> Vec<u64> {
    let mut out = vec![groups.len() as u64];
    for g in groups {
        out.push(g.len() as u64);
        for (col, path) in g {
            out.push(col.len() as u64);
            out.extend(col);
            out.push(path.len() as u64);
            for h in path {
                out.extend(crate::net::h2w(h));
            }
        }
    }
    out
}

pub fn decode_openings(v: &[u64]) -> Vec<Vec<Opening>> {
    let mut o = 0usize;
    let mut take = |k: usize| {
        let s = &v[o..o + k];
        o += k;
        s.to_vec()
    };
    let ng = take(1)[0] as usize;
    let mut out = Vec::with_capacity(ng);
    for _ in 0..ng {
        let nc = take(1)[0] as usize;
        let mut g = Vec::with_capacity(nc);
        for _ in 0..nc {
            let cl = take(1)[0] as usize;
            let col = take(cl);
            let pl = take(1)[0] as usize;
            let path = (0..pl).map(|_| crate::net::w2h(&take(4))).collect();
            g.push((col, path));
        }
        out.push(g);
    }
    out
}

/// cozk.verify: group_roots[g] = every party's root of group g (commit order); group_sizes[g] its row count.
pub fn verify(
    pp: &LigParams,
    n: usize,
    group_roots: &[Vec<Hash>],
    group_sizes: &[usize],
    mask_roots: &[Hash],
    sys: &dyn LinSystem,
    quad: &[(usize, usize, usize)],
    msg: &LigProof,
    tr: &mut Transcript,
) -> Result<(), String> {
    let (k, t) = (pp.k, pp.t);
    let nrows: usize = group_sizes.iter().sum();
    let (w, q, pq) = (&msg.w, &msg.q, &msg.pq);
    if w.len() > k + t || q.len() > 2 * k + t - 1 || pq.len() > 2 * (k + t) - 1 {
        return Err("Ligero: a message exceeds its degree bound".into());
    }
    let gam = tr.chal(nrows);
    tr.absorb(|h| {
        h.s("lig-w").list(w);
    });
    let mut cnt = Counter { n: 0, rhs: Vec::new() };
    sys.emit(&mut cnt);
    let rr = tr.chal(cnt.n);
    let lhs = pp.zeta.iter().fold(0u64, |a, &z| field::add(a, peval(q, z)));
    let rhs = field::dot(&rr, &cnt.rhs);
    if lhs != rhs {
        return Err("Ligero linear test: the constraints do not hold".into());
    }
    let alpha = alpha_of(sys, &rr, nrows, k);
    let rp: Vec<Option<Vec<u64>>> =
        alpha.par_iter().map(|a| if a.iter().any(|&x| x != 0) { Some(pp.interp_z(a)) } else { None }).collect();
    tr.absorb(|h| {
        h.s("lig-q").list(q);
    });
    let rho = tr.chal(quad.len());
    if pp.zeta.iter().any(|&z| peval(pq, z) != 0) {
        return Err("Ligero quadratic test: a product gate does not hold".into());
    }
    tr.absorb(|h| {
        h.s("lig-p").list(pq);
    });
    let jj = tr.distinct_cols(pp.tt, pp.npts);
    if !msg.j.is_empty() && msg.j != jj {
        return Err("Ligero column challenge mismatch".into());
    }
    if msg.cols.len() != group_roots.len() + 1 {
        return Err("Ligero: wrong number of column groups".into());
    }
    let mut sizes = group_sizes.to_vec();
    sizes.push(3);
    let fails: Vec<Option<String>> = jj
        .par_iter()
        .enumerate()
        .map(|(t_, &j)| {
            let x = (j + 1) as u64;
            let mut colsum: Vec<u64> = Vec::with_capacity(nrows);
            let mut msum = vec![0u64; 3];
            for g in 0..sizes.len() {
                let rts = if g < group_roots.len() { &group_roots[g] } else { &mask_roots.to_vec() };
                let mut s = vec![0u64; sizes[g]];
                for i in 0..n {
                    let (col, pth) = &msg.cols[g][i][t_];
                    if col.len() != sizes[g] || !verify_path(&rts[i], col, j, pth) {
                        return Some(format!("Ligero: Merkle opening fails (group {g}, custodian {i})"));
                    }
                    for (a, &b) in s.iter_mut().zip(col) {
                        *a = field::add(*a, b);
                    }
                }
                if g < group_roots.len() {
                    colsum.extend(s);
                } else {
                    msum = s;
                }
            }
            let prox = field::add(field::dot(&gam, &colsum), msum[0]);
            if peval(w, x) != prox {
                return Some("Ligero proximity test fails at an opened column".into());
            }
            let mut lin = msum[1];
            for (r, rpr) in rp.iter().enumerate() {
                if let Some(rpr) = rpr {
                    lin = field::add(lin, field::mul(peval(rpr, x), colsum[r]));
                }
            }
            if peval(q, x) != lin {
                return Some("Ligero linear test fails at an opened column".into());
            }
            let mut qd = msum[2];
            for (&(a, b, z), &c) in quad.iter().zip(&rho) {
                qd = field::add(qd, field::mul(c, field::sub(field::mul(colsum[a], colsum[b]), colsum[z])));
            }
            if peval(pq, x) != qd {
                return Some("Ligero quadratic test fails at an opened column".into());
            }
            None
        })
        .collect();
    if let Some(Some(e)) = fails.into_iter().find(|f| f.is_some()) {
        return Err(e);
    }
    Ok(())
}
