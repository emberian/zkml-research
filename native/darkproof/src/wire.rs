//! proofwire.py: the step bundle's bytes (schema-driven: every length is a function of d, n, the pinned profile and
//! the verifier's own replay of the step against the public transcript) and the untrusted-input verifier.
use crate::field;
use crate::h::{py_str_repr, Hash};
use crate::ligero::LigProof;
use crate::middle::{self, MiddleProof};
use crate::owner;
use crate::pcs::{Opening, PcsCols, Shape};
use crate::spine::{self, log2, SpineProof};
use crate::step::{self, StepParams};
use crate::{Ctx, Profile};
use std::collections::BTreeMap;

pub const MAGIC: &[u8; 8] = b"DLSTEP01";

pub struct W {
    pub b: Vec<u8>,
}
impl W {
    fn fe(&mut self, x: u64) {
        assert!(x < field::p(), "non-canonical field element");
        self.b.extend_from_slice(&x.to_be_bytes());
    }
    fn h(&mut self, x: &Hash) {
        self.b.extend_from_slice(x);
    }
    fn idx(&mut self, x: usize, bound: usize) {
        assert!(x < bound);
        self.b.extend_from_slice(&(x as u32).to_be_bytes());
    }
    fn fes(&mut self, xs: &[u64], n: usize) {
        assert_eq!(xs.len(), n, "list length differs from schema");
        for &x in xs {
            self.fe(x);
        }
    }
    pub(crate) fn hs(&mut self, xs: &[Hash], n: usize) {
        assert_eq!(xs.len(), n, "list length differs from schema");
        for x in xs {
            self.h(x);
        }
    }
}

pub struct R<'a> {
    pub(crate) d: &'a [u8],
    pub(crate) o: usize,
}
impl<'a> R<'a> {
    pub fn new(d: &'a [u8]) -> Self {
        R { d, o: 0 }
    }
}
pub(crate) type PR<T> = Result<T, String>;
impl<'a> R<'a> {
    pub(crate) fn take(&mut self, k: usize) -> PR<&'a [u8]> {
        if self.o + k > self.d.len() {
            return Err("truncated".into());
        }
        let s = &self.d[self.o..self.o + k];
        self.o += k;
        Ok(s)
    }
    pub(crate) fn fe(&mut self) -> PR<u64> {
        let x = u64::from_be_bytes(self.take(8)?.try_into().unwrap());
        if x >= field::p() {
            return Err("non-canonical field element".into());
        }
        Ok(x)
    }
    fn h(&mut self) -> PR<Hash> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    fn idx(&mut self, bound: usize) -> PR<usize> {
        let x = u32::from_be_bytes(self.take(4)?.try_into().unwrap()) as usize;
        if x >= bound {
            return Err("column index out of range".into());
        }
        Ok(x)
    }
    fn fes(&mut self, n: usize) -> PR<Vec<u64>> {
        (0..n).map(|_| self.fe()).collect()
    }
    pub(crate) fn hs(&mut self, n: usize) -> PR<Vec<Hash>> {
        (0..n).map(|_| self.h()).collect()
    }
}

// ---------------------------------------------------------------------------------- shared pieces of the schema
fn w_openings(w: &mut W, ops: &[Opening], t: usize, sz: usize, lg: usize) {
    assert_eq!(ops.len(), t);
    for (col, path) in ops {
        w.fes(col, sz);
        w.hs(path, lg);
    }
}
fn r_openings(r: &mut R, t: usize, sz: usize, lg: usize) -> PR<Vec<Opening>> {
    (0..t).map(|_| Ok((r.fes(sz)?, r.hs(lg)?))).collect()
}

pub(crate) fn w_ligero(w: &mut W, pr: &Profile, n: usize, sizes: &[usize], l: &LigProof) {
    let (k, t, tt) = (pr.k_l, pr.t_hide, pr.t_open);
    let lg = crate::pcs::bitlen(pr.blow * (k + t) - 1) + 1;
    w.fes(&l.w, k + t);
    w.fes(&l.q, 2 * k + t - 1);
    w.fes(&l.pq, 2 * (k + t) - 1);
    let mut sz = sizes.to_vec();
    sz.push(3);
    assert_eq!(l.cols.len(), sz.len());
    for (g, s) in l.cols.iter().zip(&sz) {
        assert_eq!(g.len(), n);
        for party in g {
            w_openings(w, party, tt, *s, lg);
        }
    }
}
pub(crate) fn r_ligero(r: &mut R, pr: &Profile, n: usize, sizes: &[usize]) -> PR<LigProof> {
    let (k, t, tt) = (pr.k_l, pr.t_hide, pr.t_open);
    let lg = crate::pcs::bitlen(pr.blow * (k + t) - 1) + 1;
    let wv = r.fes(k + t)?;
    let q = r.fes(2 * k + t - 1)?;
    let pq = r.fes(2 * (k + t) - 1)?;
    let mut cols = Vec::new();
    for &s in sizes.iter().chain(std::iter::once(&3)) {
        cols.push((0..n).map(|_| r_openings(r, tt, s, lg)).collect::<PR<Vec<_>>>()?);
    }
    Ok(LigProof { w: wv, q, pq, cols })
}

pub(crate) type PcsParts = (BTreeMap<String, Vec<Hash>>, BTreeMap<String, Vec<Vec<u64>>>, BTreeMap<String, PcsCols>);

pub(crate) fn w_roots(w: &mut W, n: usize, sh: &BTreeMap<String, Shape>, roots: &BTreeMap<String, Vec<Hash>>) {
    assert!(roots.keys().eq(sh.keys()), "dict keys differ from schema");
    for k in sh.keys() {
        w.hs(&roots[k], n);
    }
}
pub(crate) fn w_prox_cols(
    w: &mut W,
    pr: &Profile,
    n: usize,
    sh: &BTreeMap<String, Shape>,
    prox: &BTreeMap<String, Vec<Vec<u64>>>,
    cols: &BTreeMap<String, PcsCols>,
) {
    assert!(prox.keys().eq(sh.keys()) && cols.keys().eq(sh.keys()), "dict keys differ from schema");
    for (k, s) in sh {
        assert_eq!(prox[k].len(), n);
        for v in &prox[k] {
            w.fes(v, s.w);
        }
    }
    for (k, s) in sh {
        let c = &cols[k];
        assert_eq!(c.j.len(), pr.t_cols);
        for &j in &c.j {
            w.idx(j, s.npts);
        }
        for party in &c.open {
            w_openings(w, party, pr.t_cols, s.r, s.path_len());
        }
    }
}
pub(crate) fn r_pcs(r: &mut R, pr: &Profile, n: usize, sh: &BTreeMap<String, Shape>) -> PR<PcsParts> {
    let mut roots = BTreeMap::new();
    for k in sh.keys() {
        roots.insert(k.clone(), r.hs(n)?);
    }
    Ok((roots, BTreeMap::new(), BTreeMap::new()))
}
pub(crate) fn r_prox_cols(r: &mut R, pr: &Profile, n: usize, sh: &BTreeMap<String, Shape>, parts: &mut PcsParts) -> PR<()> {
    for (k, s) in sh {
        parts.1.insert(k.clone(), (0..n).map(|_| r.fes(s.w)).collect::<PR<Vec<_>>>()?);
    }
    for (k, s) in sh {
        let j = (0..pr.t_cols).map(|_| r.idx(s.npts)).collect::<PR<Vec<_>>>()?;
        let open = (0..n).map(|_| r_openings(r, pr.t_cols, s.r, s.path_len())).collect::<PR<Vec<_>>>()?;
        parts.2.insert(k.clone(), PcsCols { j, open });
    }
    Ok(())
}

pub const RNAMES: [&str; 4] = ["z1", "z2", "b", "bg"];

fn spine_sizes(pr: &Profile, d: usize, sh: &BTreeMap<String, Shape>, bind: bool) -> Vec<usize> {
    let ld = log2(d);
    let mut s = spine::Sched::default();
    for nm in RNAMES {
        s.scs.insert(nm.into(), (vec![0; ld], vec![0; ld]));
    }
    s.r1 = vec![(vec![0; ld], vec![0; ld]); 2];
    if bind {
        s.rb = Some(vec![0; ld]);
    }
    let ev = spine::evals_of(&s);
    let nrows = spine::row_layout(ld, sh, &ev, pr.k_l).nrows;
    let mut sizes = vec![1usize; 4 * ld];
    sizes.push(nrows - 4 * ld);
    sizes
}

pub fn write_spine(w: &mut W, pr: &Profile, n: usize, d: usize, chained: bool, bind: bool, p: &SpineProof) {
    let sh = spine::shapes(pr, d, chained, bind);
    let ld = log2(d);
    w_roots(w, n, &sh, &p.roots);
    for nm in RNAMES {
        assert_eq!(p.round_roots[nm].len(), ld);
        for rr in &p.round_roots[nm] {
            w.hs(rr, n);
        }
    }
    w.hs(&p.eval_roots, n);
    w.hs(&p.mask_roots, n);
    w_prox_cols(w, pr, n, &sh, &p.prox, &p.pcs_cols);
    w_ligero(w, pr, n, &spine_sizes(pr, d, &sh, bind), &p.ligero);
}

pub fn read_spine(r: &mut R, pr: &Profile, n: usize, d: usize, chained: bool, bind: bool) -> PR<SpineProof> {
    let sh = spine::shapes(pr, d, chained, bind);
    let ld = log2(d);
    let mut parts = r_pcs(r, pr, n, &sh)?;
    let mut round_roots = BTreeMap::new();
    for nm in RNAMES {
        round_roots.insert(nm.to_string(), (0..ld).map(|_| r.hs(n)).collect::<PR<Vec<_>>>()?);
    }
    let eval_roots = r.hs(n)?;
    let mask_roots = r.hs(n)?;
    r_prox_cols(r, pr, n, &sh, &mut parts)?;
    let ligero = r_ligero(r, pr, n, &spine_sizes(pr, d, &sh, bind))?;
    Ok(SpineProof { roots: parts.0, round_roots, eval_roots, mask_roots, prox: parts.1, pcs_cols: parts.2, ligero })
}

struct MShape {
    sh: BTreeMap<String, Shape>,
    lh: usize,
    lmax: usize,
    sizes: Vec<usize>,
}

fn middle_shape(pr: &Profile, n_prep: usize, n_had: usize, d: usize, bind: bool) -> MShape {
    let (lens, sh) = middle::public_shapes(pr, n_prep, n_had, d, bind);
    let lg = |x: usize| crate::pcs::bitlen(x - 1);
    let lh = lg(lens["A"]);
    let lmax = lens.values().map(|&l| lg(l)).max().unwrap();
    let rb = vec![0u64; log2(d)];
    let ev = middle::evaluations(&lens, &vec![0; lh], &vec![0; lmax], if bind { Some(&rb) } else { None });
    let nrows = middle::row_layout(&sh, &ev, lh, lmax, pr.k_l).nrows;
    let mut sizes = vec![1usize; lh + 1 + lmax];
    sizes.push(nrows - lh - 1 - lmax);
    MShape { sh, lh, lmax, sizes }
}

pub fn write_middle(w: &mut W, pr: &Profile, n: usize, d: usize, n_prep: usize, n_had: usize, bind: bool, p: &MiddleProof) {
    let ms = middle_shape(pr, n_prep, n_had, d, bind);
    w_roots(w, n, &ms.sh, &p.roots);
    assert_eq!(p.zc_roots.len(), ms.lh);
    for r in &p.zc_roots {
        w.hs(r, n);
    }
    w.hs(&p.claims_root, n);
    assert_eq!(p.lsc_roots.len(), ms.lmax);
    for r in &p.lsc_roots {
        w.hs(r, n);
    }
    w.hs(&p.eval_roots, n);
    w.hs(&p.mask_roots, n);
    w_prox_cols(w, pr, n, &ms.sh, &p.prox, &p.pcs_cols);
    w_ligero(w, pr, n, &ms.sizes, &p.ligero);
}

pub fn read_middle(r: &mut R, pr: &Profile, n: usize, d: usize, n_prep: usize, n_had: usize, bind: bool) -> PR<MiddleProof> {
    let ms = middle_shape(pr, n_prep, n_had, d, bind);
    let mut parts = r_pcs(r, pr, n, &ms.sh)?;
    let zc_roots = (0..ms.lh).map(|_| r.hs(n)).collect::<PR<Vec<_>>>()?;
    let claims_root = r.hs(n)?;
    let lsc_roots = (0..ms.lmax).map(|_| r.hs(n)).collect::<PR<Vec<_>>>()?;
    let eval_roots = r.hs(n)?;
    let mask_roots = r.hs(n)?;
    r_prox_cols(r, pr, n, &ms.sh, &mut parts)?;
    let ligero = r_ligero(r, pr, n, &ms.sizes)?;
    Ok(MiddleProof {
        roots: parts.0,
        zc_roots,
        claims_root,
        lsc_roots,
        eval_roots,
        mask_roots,
        prox: parts.1,
        pcs_cols: parts.2,
        ligero,
    })
}

/// proofwire.encode_step.
#[allow(clippy::too_many_arguments)]
pub fn encode_step(
    pr: &Profile,
    ctx: &Ctx,
    d: usize,
    n: usize,
    chained: bool,
    spine: &SpineProof,
    public: &[u64],
    middle: &MiddleProof,
    n_prep: usize,
    n_had: usize,
    owner_sig: Option<&[u8]>,
) -> Vec<u8> {
    let mut w = W { b: Vec::new() };
    let mb = ctx.model.as_bytes();
    assert!((1..=64).contains(&mb.len()));
    w.b.extend_from_slice(MAGIC);
    w.b.extend_from_slice(&(mb.len() as u16).to_be_bytes());
    w.b.extend_from_slice(mb);
    w.b.extend_from_slice(&(ctx.epoch as u32).to_be_bytes());
    w.b.extend_from_slice(&ctx.step.to_be_bytes());
    w.b.extend_from_slice(&(d as u16).to_be_bytes());
    w.b.push(n as u8);
    w.b.push(chained as u8);
    let bind = owner_sig.is_some();
    write_spine(&mut w, pr, n, d, chained, bind, spine);
    w.b.extend_from_slice(&(public.len() as u32).to_be_bytes());
    for &v in public {
        w.fe(v);
    }
    write_middle(&mut w, pr, n, d, n_prep, n_had, bind, middle);
    if let Some(s) = owner_sig {
        assert_eq!(s.len(), owner::sig_len(pr.owner_h));
        w.b.extend_from_slice(s);
    }
    w.b
}

/// The step program's public transcript length (data-independent).
pub fn transcript_len(d: usize, prm: StepParams, carried: bool) -> usize {
    prm.transcript_len(d, carried)
}

/// The deployed program's field: the HE profile's plaintext modulus (bfv.ntt_primes(61, L + 1, 2N)[L]).
pub fn he_field(pr: &Profile) -> Option<u64> {
    match (pr.he.0, pr.he.1) {
        (8192, 3) => Some(field::P_DEMO),
        (16384, 4) => Some(field::P_LEDGER),
        _ => None,
    }
}

pub struct Accepted {
    pub child: BTreeMap<String, Vec<Hash>>,
    pub leaf: Option<u64>,
}

fn tuple_repr(model: &str, epoch: u64, step: u64) -> String {
    format!("({}, {}, {})", py_str_repr(model), epoch, step)
}

/// proofwire.verify_step: expect_ctx, parent_roots, d_pinned, owner_pk and min_leaf come from the ledger.
#[allow(clippy::too_many_arguments)]
pub fn verify_step(
    pr: &Profile,
    lp: &crate::ligero::LigParams,
    blob: &[u8],
    expect: &Ctx,
    parent_roots: &BTreeMap<String, Vec<Hash>>,
    tables: &(Vec<u64>, Vec<u64>),
    d_pinned: usize,
    prm: StepParams,
    owner_pk: Option<&Hash>,
    min_leaf: u64,
) -> Result<Accepted, String> {
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_inner(pr, lp, blob, expect, parent_roots, tables, d_pinned, prm, owner_pk, min_leaf)
    }));
    match res {
        Ok(r) => r,
        Err(_) => Err("parse: panic".into()),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_inner(
    pr: &Profile,
    lp: &crate::ligero::LigParams,
    blob: &[u8],
    expect: &Ctx,
    parent_roots: &BTreeMap<String, Vec<Hash>>,
    tables: &(Vec<u64>, Vec<u64>),
    d_pinned: usize,
    prm: StepParams,
    owner_pk: Option<&Hash>,
    min_leaf: u64,
) -> Result<Accepted, String> {
    let bind = owner_pk.is_some();
    // the lookup tables are the program's (its domain [t_lo, t_lo + 256)), never the caller's
    let own_tables;
    let tables = if prm.t_lo == -128 {
        tables
    } else {
        own_tables = step::tables_for(prm.t_lo);
        &own_tables
    };
    let mut r = R { d: blob, o: 0 };
    let parsed = (|| -> PR<_> {
        if r.take(8)? != MAGIC {
            return Err("bad magic".into());
        }
        let ml = u16::from_be_bytes(r.take(2)?.try_into().unwrap()) as usize;
        if !(1..=64).contains(&ml) {
            return Err("bad model id length".into());
        }
        let model_b = r.take(ml)?.to_vec();
        let hdr = r.take(16)?;
        let epoch = u32::from_be_bytes(hdr[0..4].try_into().unwrap()) as u64;
        let step = u64::from_be_bytes(hdr[4..12].try_into().unwrap());
        let d = u16::from_be_bytes(hdr[12..14].try_into().unwrap()) as usize;
        let (n, chained) = (hdr[14], hdr[15]);
        if (model_b.as_slice(), epoch, step) != (expect.model.as_bytes(), expect.epoch, expect.step) {
            let shown = String::from_utf8_lossy(&model_b).to_string();
            return Ok(Err(format!(
                "binding mismatch: proof is for {}, expected {}",
                tuple_repr(&shown, epoch, step),
                expect.repr()
            )));
        }
        if d != d_pinned || n != 3 || chained != 1 {
            return Err("shape or chaining differs from the ledger's genesis record".into());
        }
        let n = n as usize;
        if prm.he && he_field(pr) != Some(field::p()) {
            return Err("the deployed program's field is the HE profile's plaintext modulus".into());
        }
        let spine = read_spine(&mut r, pr, n, d, true, bind)?;
        let cnt = u32::from_be_bytes(r.take(4)?.try_into().unwrap()) as usize;
        // the step program's transcript length is a function of d and the pinned program alone: anything else is
        // refused before a single value is read (Python caps at 2^24, which d = 4096's 84.5M values exceed)
        let want = transcript_len(d, prm, prm.carried(expect.step));
        if cnt > want {
            return Err(if cnt > 1 << 24 { "public transcript too long" } else { "public transcript longer than the step program" }.into());
        }
        if cnt < want {
            return Err("public transcript shorter than the step program".into());
        }
        let public = r.fes(cnt)?;
        Ok(Ok((spine, public, n, d)))
    })();
    let (spine, public, n, d) = match parsed {
        Err(e) => return Err(format!("parse: {e}")),
        Ok(Err(e)) => return Err(e),
        Ok(Ok(x)) => x,
    };
    let rec = match step::replay(&public, d, prm, tables, prm.carried(expect.step)) {
        Ok(rec) => rec,
        Err(step::Short::Commit) => return Err("parse: he_outer_commit entry is not 0".into()),
        Err(step::Short::Short) => return Err("parse: public transcript shorter than the step program".into()),
    };
    if rec.tpos != public.len() {
        return Err("parse: public transcript longer than the step program".into());
    }
    let tail = (|| -> PR<_> {
        let middle = read_middle(&mut r, pr, n, d, rec.n_prep(), rec.had.len(), bind)?;
        let sig = if bind { Some(r.take(owner::sig_len(pr.owner_h))?.to_vec()) } else { None };
        if r.o != r.d.len() {
            return Err("trailing bytes".into());
        }
        Ok((middle, sig))
    })();
    let (middle, sig) = tail.map_err(|e| format!("parse: {e}"))?;
    let mut leaf = None;
    if let Some(pk) = owner_pk {
        let sig = sig.unwrap();
        let msg = owner::batch_message(expect, &spine.roots["xo"], &middle.roots["yo"]);
        if !owner::verify(pk, pr.owner_h, min_leaf, &msg, &sig) {
            return Err(
                "owner signature does not verify over (context, x and y commitments), or its leaf was used".into()
            );
        }
        leaf = Some(owner::sig_leaf(&sig));
    }
    spine::verify(pr, lp, n, d, expect, Some(parent_roots), true, &spine, bind, &public)
        .map_err(|e| format!("spine: {e}"))?;
    middle::verify(pr, lp, n, &rec, d, &spine.roots, expect, &middle, bind, &public)
        .map_err(|e| format!("middle: {e}"))?;
    let mut child = BTreeMap::new();
    child.insert("W1".to_string(), spine.roots["W1n"].clone());
    child.insert("W2".to_string(), spine.roots["W2n"].clone());
    Ok(Accepted { child, leaf })
}
