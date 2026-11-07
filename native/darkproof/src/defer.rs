//! Cut E (proofwire DEFER; proof.md sections 21-22): a step does not open its children W1n, W2n. It commits carries
//! c1, c2 = W(r) - d(r_row) v(r_col) (two lives) after its last schedule challenge, and the child's next opening
//! (the next step, the release, or a closing proof) discharges W_(k+1)(r_k) = c_k at the ledger's r_k.
use crate::h::Hash;
use crate::pcs::{bitlen, PcsParty, Shape};
use crate::Profile;
use std::collections::BTreeMap;

pub const CARRY: [&str; 2] = ["c1", "c2"];
pub const CARRY_IN: [&str; 2] = ["c1p", "c2p"];

/// cosnark_zk.carry_m: a carry holds the E components of one element, 2^m >= E entries.
pub fn carry_m(e: usize) -> usize {
    bitlen(e - 1)
}

/// cosnark_zk.carry_shape: the profile's vector parameters (two lives), m = carry_m; `second`: its second life.
pub fn carry_shape(pr: &Profile, second: bool) -> Shape {
    let s = Shape::new(pr, carry_m(pr.ext), 0);
    let b = s.block;
    Shape { base: if second { b } else { 0 }, ..s }
}

/// A step's pending claims as the ledger and the verifier hold them (proofwire.deferred_of / pending_json): the
/// points (W1, W2: flat, E components per coordinate) and the carry roots (c1p, c2p: one root per custodian).
#[derive(Clone, Debug, PartialEq)]
pub struct Pending {
    pub points: BTreeMap<String, Vec<u64>>,
    pub carry_roots: BTreeMap<String, Vec<Hash>>,
}

impl Pending {
    pub fn points_e<const E: usize>(&self, k: &str) -> Vec<[u64; E]> {
        self.points[k].chunks(E).map(|c| std::array::from_fn(|i| c[i])).collect()
    }
}

/// One custodian's side of the claims a step leaves for its discharge (the prover's stats["deferred"]): the points
/// and this party's carry commitments (c1p, c2p), carried into the discharging proof for their second life.
#[derive(Clone)]
pub struct DeferIn {
    pub points: BTreeMap<String, Vec<u64>>,
    pub carries: BTreeMap<String, PcsParty>,
}

impl DeferIn {
    pub fn points_e<const E: usize>(&self, k: &str) -> Vec<[u64; E]> {
        self.points[k].chunks(E).map(|c| std::array::from_fn(|i| c[i])).collect()
    }
}

/// The ledger's view of the custodians' DeferIns (every party's carry roots, in party order).
pub fn pending_of(parts: &[DeferIn]) -> Pending {
    let carry_roots = CARRY_IN.iter().map(|k| (k.to_string(), parts.iter().map(|d| d.carries[*k].root).collect())).collect();
    Pending { points: parts[0].points.clone(), carry_roots }
}

// ------------------------------------------------------------------------------------------------- closing proof
use crate::ext;
use crate::h::Py;
use crate::ligero::{self, LigParams, LigParty, LigProof, LinSink, LinSystem};
use crate::net::{gather_hashes, Net};
use crate::pcs::{colsums, PcsCols};
use crate::rng::Det;
use crate::spine::{self, EEm, EvalsE};
use crate::transcript::Transcript;
use crate::Ctx;

/// cosnark_zk.prove_close's proof: the head's W1, W2 (single life) and the carries c1p, c2p (second life) opened at
/// the last step's points; W(r_k) = c_k in a Ligero without products.
#[derive(Clone, Debug, PartialEq)]
pub struct CloseProof {
    pub roots: BTreeMap<String, Vec<Hash>>,
    pub eval_roots: Vec<Hash>,
    pub mask_roots: Vec<Hash>,
    pub prox: BTreeMap<String, Vec<Vec<u64>>>,
    pub pcs_cols: BTreeMap<String, PcsCols>,
    pub ligero: LigProof,
}

/// cosnark_zk.close_shapes.
pub fn close_shapes(pr: &Profile, d: usize) -> BTreeMap<String, Shape> {
    let ld = spine::log2(d);
    let mut sh = BTreeMap::new();
    for k in ["W1", "W2"] {
        sh.insert(k.to_string(), Shape::new(&pr.w_life(), 2 * ld, 0));
    }
    for k in CARRY_IN {
        sh.insert(k.to_string(), carry_shape(pr, true));
    }
    sh
}

/// cosnark_zk.close_evals: W1, W2 at the last step's points, then the carries (their single row).
fn close_evals<const E: usize>(w1: Vec<[u64; E]>, w2: Vec<[u64; E]>) -> EvalsE<E> {
    let cpt = vec![ext::zero::<E>(); carry_m(E)];
    vec![("W1".into(), w1), ("W2".into(), w2), ("c1p".into(), cpt.clone()), ("c2p".into(), cpt)]
}

/// The u rows of the close evaluations, in order (E component blocks of ceil(W / K_L) rows each).
pub fn close_rows(sh: &BTreeMap<String, Shape>, kl: usize, e: usize) -> (Vec<Vec<usize>>, usize) {
    let (mut urows, mut nxt) = (Vec::new(), 0);
    for k in ["W1", "W2", "c1p", "c2p"] {
        let nr = sh[k].w.div_ceil(kl);
        urows.push((nxt..nxt + e * nr).collect());
        nxt += e * nr;
    }
    (urows, nxt)
}

struct CloseSys<const E: usize> {
    kl: usize,
    ev: EvalsE<E>,
    shapes: Vec<Shape>,
    cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: Vec<Vec<usize>>,
}

impl<const E: usize> LinSystem for CloseSys<E> {
    fn emit(&self, sink: &mut dyn LinSink) {
        spine::pcs_consistency_e(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.urows);
        let mut em = EEm::<E>::new(sink);
        for i in 0..2 {
            spine::y_form(&mut em, &self.ev, &self.shapes, &self.urows, self.kl, i, ext::one());
            let r0 = self.urows[2 + i][0];
            em.var(std::array::from_fn(|k| (r0, k)), ext::neg(ext::one()));
            em.done(&format!("closing: W{}(r_k) = c_k", i + 1), ext::zero());
        }
    }
}

/// The context tuple (model, epoch, step, "close") as the transcript absorbs it.
fn close_ctx(h: &mut Py, c: &Ctx) {
    h.raw(b"(").str_any(&c.model).raw(b", ").int(c.epoch).raw(b", ").int(c.step).raw(b", ").s("close").raw(b")");
}

/// cosnark_zk.prove_close for custodian i: head = this party's head W1, W2 commitments (the last step's children),
/// dfr = this party's side of the head's pending claims. ctx = (model, epoch, head step). No MPC product is needed.
#[allow(clippy::too_many_arguments)]
pub fn prove_close(
    pr: &Profile,
    lp: &LigParams,
    i: usize,
    n: usize,
    net: &mut dyn Net,
    ctx: &Ctx,
    head: &BTreeMap<String, PcsParty>,
    dfr: &DeferIn,
    det: &Det,
) -> Result<CloseProof, String> {
    match pr.ext {
        1 => prove_close_g::<1>(pr, lp, i, n, net, ctx, head, dfr, det),
        2 => prove_close_g::<2>(pr, lp, i, n, net, ctx, head, dfr, det),
        e => Err(format!("unsupported EXT {e}")),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_close_g<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    i: usize,
    n: usize,
    net: &mut dyn Net,
    ctx: &Ctx,
    head: &BTreeMap<String, PcsParty>,
    dfr: &DeferIn,
    det: &Det,
) -> Result<CloseProof, String> {
    let mut com: BTreeMap<String, PcsParty> = BTreeMap::new();
    for k in ["W1", "W2"] {
        com.insert(k.to_string(), head[k].clone());
    }
    for k in CARRY_IN {
        let mut c = dfr.carries[k].clone();
        c.shape.base = c.shape.block; // the carry's second life
        com.insert(k.to_string(), c);
    }
    let keys: Vec<String> = com.keys().cloned().collect();
    let my: Vec<Hash> = keys.iter().map(|k| com[k].root).collect();
    let all = gather_hashes(net, &my);
    let roots: BTreeMap<String, Vec<Hash>> = keys.iter().enumerate().map(|(ki, k)| (k.clone(), (0..n).map(|p| all[p][ki]).collect())).collect();
    let seed = format!("(3, ({}, {}, {}, 'close'))", crate::h::py_str_repr(&ctx.model), ctx.epoch, ctx.step);
    let mut lg = LigParty::new(lp, i, n, &seed, det);
    let mut tr = Transcript::new("close-zk");
    tr.absorb(|h| {
        h.s("ctx");
        close_ctx(h, ctx);
    });
    for k in &keys {
        tr.absorb(|h| {
            h.s(k).list_hx(&roots[k]);
        });
    }
    let ev = close_evals::<E>(dfr.points_e::<E>("W1"), dfr.points_e::<E>("W2"));
    let shp: BTreeMap<String, Shape> = com.iter().map(|(k, c)| (k.clone(), c.shape.clone())).collect();
    let (urows, _) = close_rows(&shp, pr.k_l, E);
    for (k, pt) in &ev {
        let c = &com[k];
        let (u, _) = c.eval_share_e(pt);
        for uk in &u {
            for s0 in (0..c.shape.w).step_by(pr.k_l) {
                lg.add_row(&uk[s0..(s0 + pr.k_l).min(c.shape.w)]);
            }
        }
    }
    let eval_roots = lg.commit(net);
    let mask_roots = lg.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    let (prox, pcs_cols) = spine::pcs_prove_e::<E>(pr, &mut com, &mut tr, net, n)?;
    let cols = pcs_cols.iter().map(|(k, c)| (k.clone(), (c.j.clone(), colsums(c, com[k].shape.r)))).collect();
    let sys = CloseSys::<E> { kl: pr.k_l, shapes: ev.iter().map(|(k, _)| shp[k].clone()).collect(), ev, cols, urows };
    let ligero = lg.prove(net, &mut tr, &sys, &[]);
    Ok(CloseProof { roots, eval_roots, mask_roots, prox, pcs_cols, ligero })
}

/// cosnark_zk.verify_close: public data only; head_roots (the head's W1, W2 roots) and the pending claims come from
/// the ledger.
#[allow(clippy::too_many_arguments)]
pub fn verify_close(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    d: usize,
    ctx: &Ctx,
    head_roots: &BTreeMap<String, Vec<Hash>>,
    pend: &Pending,
    proof: &CloseProof,
) -> Result<(), String> {
    match pr.ext {
        1 => verify_close_g::<1>(pr, lp, n, d, ctx, head_roots, pend, proof),
        2 => verify_close_g::<2>(pr, lp, n, d, ctx, head_roots, pend, proof),
        e => Err(format!("unsupported EXT {e}")),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_close_g<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    n: usize,
    d: usize,
    ctx: &Ctx,
    head_roots: &BTreeMap<String, Vec<Hash>>,
    pend: &Pending,
    proof: &CloseProof,
) -> Result<(), String> {
    let sh = close_shapes(pr, d);
    let roots = &proof.roots;
    if roots.keys().ne(sh.keys()) {
        return Err("closing proof names the wrong commitments".into());
    }
    if ["W1", "W2"].iter().any(|k| head_roots.get(*k) != Some(&roots[*k])) || CARRY_IN.iter().any(|k| pend.carry_roots.get(*k) != Some(&roots[*k])) {
        return Err("closing proof is not over the head's commitments and carries".into());
    }
    let mut tr = Transcript::new("close-zk");
    tr.absorb(|h| {
        h.s("ctx");
        close_ctx(h, ctx);
    });
    for (k, r) in roots {
        tr.absorb(|h| {
            h.s(k).list_hx(r);
        });
    }
    let ev = close_evals::<E>(pend.points_e::<E>("W1"), pend.points_e::<E>("W2"));
    let (urows, nrows) = close_rows(&sh, pr.k_l, E);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    let keys: Vec<String> = sh.keys().cloned().collect();
    let shv: Vec<Shape> = sh.values().cloned().collect();
    let rootv: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
    let proxv: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| proof.prox[k].clone()).collect();
    let colv: Vec<PcsCols> = keys.iter().map(|k| proof.pcs_cols[k].clone()).collect();
    crate::pcs::verify_e::<E>(pr, &keys, &shv, &rootv, &proxv, &colv, &mut tr, n)?;
    let cols = keys.iter().map(|k| (k.clone(), (proof.pcs_cols[k].j.clone(), colsums(&proof.pcs_cols[k], sh[k].r)))).collect();
    let sys = CloseSys::<E> { kl: pr.k_l, shapes: ev.iter().map(|(k, _)| sh[k].clone()).collect(), ev, cols, urows };
    ligero::verify(lp, n, &[proof.eval_roots.clone()], &[nrows], &proof.mask_roots, &sys, &[], &proof.ligero, &mut tr)
}
