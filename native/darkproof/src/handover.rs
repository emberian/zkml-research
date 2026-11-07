//! handover.py: the custody-handover proof's bytes (schema-driven, every length a function of (d, n_old, n_new, the
//! pinned profile)) and its untrusted-input verifier. The old committee's commitment of W (the ledger head's roots,
//! carried in its second life: mask block 1) and the new committee's fresh commitment (first life) are evaluated at
//! one Fiat-Shamir point per matrix; a collaborative ZK Ligero among all n_old + n_new custodians proves, on hidden
//! rows, evaluation consistency at both commitments' opened columns and W_old(r) = W_new(r).
use crate::field;
use crate::h::{py_str_repr, Hash};
use crate::ligero::{self, decode_openings, encode_openings, LigParams, LigParty, LigProof, LinSink, LinSystem};
use crate::net::{gather_hashes, Net};
use crate::pcs::{self, colsums, Opening, PcsCols, PcsParty, Shape};
use crate::rng::Det;
use rayon::prelude::*;
use crate::ext;
use crate::spine::{log2, pcs_consistency_e, EvalsE};
use crate::transcript::Transcript;
use crate::wire::{r_ligero, r_pcs, r_prox_cols_e, R, PR};
use crate::Profile;
use std::collections::BTreeMap;

pub const MAGIC: &[u8; 8] = b"DLHAND01";
pub const KINDS: [&str; 2] = ["W1", "W2"];
pub type Roots = BTreeMap<String, Vec<Hash>>;

/// handover.context_digest: ("handover", model, epoch_old, epoch_new, after_step, tuple(old_set), tuple(new_set)).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandoverCtx {
    pub model: String,
    pub epoch_old: u64,
    pub epoch_new: u64,
    pub after_step: u64,
    pub old_set: Vec<String>,
    pub new_set: Vec<String>,
}

fn tuple_of_str(xs: &[String]) -> String {
    let items: Vec<String> = xs.iter().map(|s| py_str_repr(s)).collect();
    if items.len() == 1 {
        format!("({},)", items[0])
    } else {
        format!("({})", items.join(", "))
    }
}

impl HandoverCtx {
    /// repr() of the context tuple.
    pub fn repr(&self) -> String {
        format!(
            "('handover', {}, {}, {}, {}, {}, {})",
            py_str_repr(&self.model),
            self.epoch_old,
            self.epoch_new,
            self.after_step,
            tuple_of_str(&self.old_set),
            tuple_of_str(&self.new_set)
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct HandoverProof {
    pub old_roots: Roots,
    pub new_roots: Roots,
    pub eval_roots: Vec<Hash>,
    pub mask_roots: Vec<Hash>,
    pub prox_old: BTreeMap<String, Vec<Vec<u64>>>,
    pub cols_old: BTreeMap<String, PcsCols>,
    pub prox_new: BTreeMap<String, Vec<Vec<u64>>>,
    pub cols_new: BTreeMap<String, PcsCols>,
    pub ligero: LigProof,
    /// cut E (DEFER): the new committee's carries cN1, cN2 (keys c1, c2; empty outside DEFER). Under DEFER old_roots
    /// also holds the old carries c1p, c2p of a pending head, prox_old / cols_old cover W1, W2 (and c1p, c2p), and
    /// prox_new / cols_new cover c1, c2 only: the new W is not opened in the handover.
    pub carry_roots: Roots,
}

/// The public shapes (cosnark_zk.PubShape) of the old (second life) and new (first life) matrix commitments.
pub fn shapes(pr: &Profile, d: usize) -> (BTreeMap<String, Shape>, BTreeMap<String, Shape>) {
    let m = 2 * log2(d);
    let old_base = if pr.lives > 0 { pr.nmask / pr.lives } else { 0 };
    let mk = |base| KINDS.iter().map(|k| (k.to_string(), Shape::new(pr, m, base))).collect();
    (mk(old_base), mk(0))
}

/// Hidden Ligero rows: one u row combination per evaluation (old W1, new W1, old W2, new W2), EXT components of
/// ceil(W / K_L) rows each.
pub fn nrows(pr: &Profile, d: usize) -> usize {
    4 * pr.ext * shapes(pr, d).0["W1"].w.div_ceil(pr.k_l)
}

fn sizes_ok(d: usize, n_old: usize, n_new: usize) -> bool {
    d >= 2 && d.is_power_of_two() && d < 1 << 16 && (1..=255).contains(&n_old) && (1..=255).contains(&n_new)
}

/// The byte length the schema fixes for this proof (handover.encode's output length). Under multiproofs it depends
/// on the drawn columns (wire::mp_needed), so it takes the proof; it is derived from the schema, not the encoder.
pub fn byte_len(pr: &Profile, d: usize, p: &HandoverProof) -> usize {
    if pr.defer {
        return byte_len_defer(pr, d, p);
    }
    let (n_old, n_new) = (p.old_roots["W1"].len(), p.new_roots["W1"].len());
    let n = n_old + n_new;
    let (so, sn) = shapes(pr, d);
    // one tree's openings of `sz`-element columns at js: one path per column, or a multiproof (columns, salts, the
    // siblings mp_needed names); the multiproof's length depends on the drawn js
    let tree = |js: &[usize], sz: usize, path_len: usize| -> usize {
        if pr.multiproof {
            js.len() * (8 * sz + 32) + 32 * crate::wire::mp_needed(js, path_len - 1).len()
        } else {
            js.len() * (8 * sz + 32 * path_len)
        }
    };
    let pcs_side = |nn: usize, sh: &BTreeMap<String, Shape>, cols: &BTreeMap<String, PcsCols>| -> usize {
        sh.iter().map(|(k, s)| 32 * nn + 8 * nn * pr.ext * s.w + 4 * pr.t_cols + nn * tree(&cols[k].j, s.r, s.path_len())).sum::<usize>()
    };
    let (k, t) = (pr.k_l, pr.t_hide);
    let lg = crate::pcs::bitlen(pr.blow * (k + t) - 1) + 1;
    let lj: Vec<usize> = if pr.multiproof { p.ligero.j.clone() } else { (0..pr.t_open).collect() };
    // the tests' messages w, q, pq once per component; the mask group has 3 EXT rows
    let lig = 8 * pr.ext * ((k + t) + (2 * k + t - 1) + (2 * (k + t) - 1))
        + if pr.multiproof { 4 * pr.t_open } else { 0 }
        + n * (tree(&lj, nrows(pr, d), lg) + tree(&lj, 3 * pr.ext, lg));
    12 + pcs_side(n_old, &so, &p.cols_old) + pcs_side(n_new, &sn, &p.cols_new) + 2 * 32 * n + lig
}

/// handover.decode: d, n_old and n_new come from the ledger; any deviation from the schema is a parse error.
pub fn decode(pr: &Profile, blob: &[u8], d: usize, n_old: usize, n_new: usize) -> PR<HandoverProof> {
    if pr.defer {
        return decode_defer(pr, blob, d, n_old, n_new, false);
    }
    if !sizes_ok(d, n_old, n_new) {
        return Err("committee sizes or width out of range".into());
    }
    let (so, sn) = shapes(pr, d);
    let mut r = R::new(blob);
    if r.take(8)? != MAGIC {
        return Err("bad magic".into());
    }
    let hdr = r.take(4)?;
    if (u16::from_be_bytes([hdr[0], hdr[1]]) as usize, hdr[2] as usize, hdr[3] as usize) != (d, n_old, n_new) {
        return Err("width or committee sizes differ from the ledger's".into());
    }
    let n = n_old + n_new;
    let mut po = r_pcs(&mut r, pr, n_old, &so)?;
    let mut pn = r_pcs(&mut r, pr, n_new, &sn)?;
    let eval_roots = r.hs(n)?;
    let mask_roots = r.hs(n)?;
    r_prox_cols_e(&mut r, pr, n_old, &so, &mut po, pr.ext)?;
    r_prox_cols_e(&mut r, pr, n_new, &sn, &mut pn, pr.ext)?;
    let ligero = r_ligero(&mut r, pr, n, &[nrows(pr, d)])?;
    if r.o != r.d.len() {
        return Err("trailing bytes".into());
    }
    Ok(HandoverProof {
        old_roots: po.0,
        new_roots: pn.0,
        eval_roots,
        mask_roots,
        prox_old: po.1,
        cols_old: po.2,
        prox_new: pn.1,
        cols_new: pn.2,
        ligero,
        carry_roots: Roots::new(),
    })
}

/// handover._constraints: evaluation consistency at each commitment's opened columns, then old W(r) = new W(r). Every
/// check is an identity over F_{p^E}, emitted as E F_p constraints, component 0 first (cosnark_zk.evar / eadder).
struct HandoverSys<const E: usize> {
    kl: usize,
    ev: EvalsE<E>,
    shapes: Vec<Shape>,
    cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: Vec<Vec<usize>>,
}

impl<const E: usize> LinSystem for HandoverSys<E> {
    fn emit(&self, sink: &mut dyn LinSink) {
        pcs_consistency_e::<E>(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.urows);
        let nrr = ext::nr();
        let mut bufs: [Vec<(u32, u32, u64)>; E] = std::array::from_fn(|_| Vec::new());
        for (q, k) in KINDS.iter().enumerate() {
            let (eo, en) = (2 * q, 2 * q + 1);
            let s = &self.shapes[eo];
            let nr = s.w.div_ceil(self.kl);
            let b = ext::eqv::<E>(&self.ev[eo].1[..s.mc]);
            for bb in bufs.iter_mut() {
                bb.clear();
            }
            // evar(U(e, c), coef): component 0 = coef_0 V_0 + NR coef_1 V_1, component 1 = coef_0 V_1 + coef_1 V_0
            let mut put = |bufs: &mut [Vec<(u32, u32, u64)>; E], e: usize, c: usize, coef: [u64; E]| {
                let cell = |kk: usize| (self.urows[e][kk * nr + c / self.kl] as u32, (c % self.kl) as u32);
                let mut push = |k: usize, kk: usize, v: u64| {
                    if v != 0 {
                        let (r, cc) = cell(kk);
                        bufs[k].push((r, cc, v));
                    }
                };
                if E == 1 {
                    push(0, 0, coef[0]);
                } else {
                    push(0, 0, coef[0]);
                    push(0, 1, field::mul(nrr, coef[1]));
                    push(1, 1, coef[0]);
                    push(1, 0, coef[1]);
                }
            };
            for c in 0..s.c {
                put(&mut bufs, eo, c, b[c]);
                put(&mut bufs, en, c, ext::neg(b[c]));
            }
            let label = format!("handover: old {k}(r) = new {k}(r)");
            for bb in bufs.iter() {
                sink.con(&label, bb, 0);
            }
        }
    }
}

/// The transcript up to the evaluation points: ctx, then every commitment's root tuple (handover._keys order).
fn transcript(ctx: &HandoverCtx, old_roots: &Roots, new_roots: &Roots) -> Transcript {
    let mut tr = Transcript::new("handover");
    let cr = ctx.repr();
    tr.absorb(|h| {
        h.s("ctx").raw(cr.as_bytes());
    });
    for side in ["old", "new"] {
        let roots = if side == "old" { old_roots } else { new_roots };
        for k in KINDS {
            let key = format!("('{side}', '{k}')");
            tr.absorb(|h| {
                h.str_any(&key).list_hx(&roots[k]);
            });
        }
    }
    tr
}

/// handover._schedule and _rows: one point per matrix in F_{p^E} (one transcript call of E 2 log2 d draws), the
/// evaluation list (old k, r), (new k, r) per k, its shapes, the hidden rows of each evaluation (component-major: E
/// blocks of ceil(W / K_L) rows) and the row count.
fn schedule<const E: usize>(
    tr: &mut Transcript,
    pr: &Profile,
    d: usize,
    so: &BTreeMap<String, Shape>,
    sn: &BTreeMap<String, Shape>,
) -> (EvalsE<E>, Vec<Shape>, Vec<Vec<usize>>, usize) {
    let ld = log2(d);
    let mut ev: EvalsE<E> = Vec::new();
    let mut shv = Vec::new();
    for k in KINDS {
        let r = ext::chal::<E>(tr, 2 * ld);
        ev.push((format!("old {k}"), r.clone()));
        ev.push((format!("new {k}"), r));
        shv.push(so[k].clone());
        shv.push(sn[k].clone());
    }
    let mut urows = Vec::new();
    let mut nxt = 0;
    for s in &shv {
        let nr = E * s.w.div_ceil(pr.k_l);
        urows.push((nxt..nxt + nr).collect::<Vec<usize>>());
        nxt += nr;
    }
    (ev, shv, urows, nxt)
}

fn colsum_map(
    so: &BTreeMap<String, Shape>,
    sn: &BTreeMap<String, Shape>,
    cols_old: &BTreeMap<String, PcsCols>,
    cols_new: &BTreeMap<String, PcsCols>,
) -> BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)> {
    let mut cols = BTreeMap::new();
    for (side, sh, pc) in [("old", so, cols_old), ("new", sn, cols_new)] {
        for k in KINDS {
            cols.insert(format!("{side} {k}"), (pc[k].j.clone(), colsums(&pc[k], sh[k].r)));
        }
    }
    cols
}

/// handover.verify on a parsed proof: public data only (ctx and old_roots come from the ledger).
#[allow(clippy::too_many_arguments)]
pub fn verify_proof(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    old_roots: &Roots,
    proof: &HandoverProof,
) -> Result<(), String> {
    if &proof.old_roots != old_roots {
        return Err("handover: old roots are not the ledger head's".into());
    }
    let (so, sn) = shapes(pr, d);
    if KINDS.iter().any(|k| proof.old_roots[*k].len() != n_old || proof.new_roots[*k].len() != n_new) {
        return Err("handover: wrong committee sizes".into());
    }
    if lp.ext != pr.ext {
        return Err("handover: the Ligero's extension degree differs from the profile's".into());
    }
    match pr.ext {
        1 => verify_proof_e::<1>(pr, lp, d, n_old, n_new, ctx, proof, &so, &sn),
        2 => verify_proof_e::<2>(pr, lp, d, n_old, n_new, ctx, proof, &so, &sn),
        e => Err(format!("handover: extension degree {e} is not supported")),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_proof_e<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    proof: &HandoverProof,
    so: &BTreeMap<String, Shape>,
    sn: &BTreeMap<String, Shape>,
) -> Result<(), String> {
    let mut tr = transcript(ctx, &proof.old_roots, &proof.new_roots);
    let (ev, shv, urows, nxt) = schedule::<E>(&mut tr, pr, d, so, sn);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    let keys: Vec<String> = KINDS.iter().map(|k| k.to_string()).collect();
    for (side, nn, sh, roots, prox, pc) in [
        ("old", n_old, so, &proof.old_roots, &proof.prox_old, &proof.cols_old),
        ("new", n_new, sn, &proof.new_roots, &proof.prox_new, &proof.cols_new),
    ] {
        let shs: Vec<Shape> = keys.iter().map(|k| sh[k].clone()).collect();
        let rts: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
        let pxs: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| prox[k].clone()).collect();
        let cls: Vec<PcsCols> = keys.iter().map(|k| pc[k].clone()).collect();
        pcs::verify_e::<E>(pr, &keys, &shs, &rts, &pxs, &cls, &mut tr, nn)
            .map_err(|e| format!("handover ({side} committee): {e}"))?;
    }
    let cols = colsum_map(so, sn, &proof.cols_old, &proof.cols_new);
    let sys = HandoverSys::<E> { kl: pr.k_l, ev, shapes: shv, cols, urows };
    ligero::verify(lp, n_old + n_new, &[proof.eval_roots.clone()], &[nxt], &proof.mask_roots, &sys, &[], &proof.ligero, &mut tr)
}

/// The untrusted-input verifier (handover.verify_bytes): bytes in; the new committee's roots out when it accepts.
/// d, n_old, n_new, ctx and old_roots come from the ledger, never from the bytes.
#[allow(clippy::too_many_arguments)]
pub fn verify(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    old_roots: &Roots,
    blob: &[u8],
) -> Result<Roots, String> {
    if pr.defer {
        return verify_defer(pr, lp, d, n_old, n_new, ctx, old_roots, None, blob).map(|(r, _)| r);
    }
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = decode(pr, blob, d, n_old, n_new).map_err(|e| format!("parse: {e}"))?;
        verify_proof(pr, lp, d, n_old, n_new, ctx, old_roots, &proof)?;
        Ok(proof.new_roots)
    }));
    match res {
        Ok(r) => r,
        Err(_) => Err("malformed handover proof (panic)".into()),
    }
}

// ------------------------------------------------------------------------------------------------ encoder
/// handover.encode.
pub fn encode(pr: &Profile, d: usize, p: &HandoverProof) -> Vec<u8> {
    if pr.defer {
        return encode_defer(pr, d, p);
    }
    let (n_old, n_new) = (p.old_roots["W1"].len(), p.new_roots["W1"].len());
    assert!(sizes_ok(d, n_old, n_new));
    let (so, sn) = shapes(pr, d);
    let mut w = crate::wire::W { b: Vec::new() };
    w.b.extend_from_slice(MAGIC);
    w.b.extend_from_slice(&(d as u16).to_be_bytes());
    w.b.push(n_old as u8);
    w.b.push(n_new as u8);
    let n = n_old + n_new;
    crate::wire::w_roots(&mut w, n_old, &so, &p.old_roots);
    crate::wire::w_roots(&mut w, n_new, &sn, &p.new_roots);
    w.hs(&p.eval_roots, n);
    w.hs(&p.mask_roots, n);
    crate::wire::w_prox_cols_e(&mut w, pr, n_old, &so, &p.prox_old, &p.cols_old, pr.ext);
    crate::wire::w_prox_cols_e(&mut w, pr, n_new, &sn, &p.prox_new, &p.cols_new, pr.ext);
    crate::wire::w_ligero(&mut w, pr, n, &[nrows(pr, d)], &p.ligero);
    w.b
}

// ------------------------------------------------------------------------------------------------ prover
/// One custodian's part of handover.prove. Parties 0..n_old are the old committee (in its order), n_old..n_old +
/// n_new the new one; `net` connects all n_old + n_new of them. `mine` is this party's own commitment part of W1 and
/// W2: the old committee's carried child (its first life spent in the step) or the new committee's fresh
/// commitment. Every party returns the same proof. The old parts' second life is counted (LifeExhausted refuses a
/// third opening).
#[allow(clippy::too_many_arguments)]
pub fn prove(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    mine: &mut BTreeMap<String, PcsParty>,
    net: &mut dyn Net,
    det: &Det,
) -> Result<HandoverProof, String> {
    if pr.defer {
        return prove_defer(pr, lp, d, n_old, n_new, ctx, mine, None, None, net, det).map(|(p, _)| p);
    }
    let n = n_old + n_new;
    let g = net.me();
    assert_eq!(net.n(), n);
    let old = g < n_old;
    let (so, sn) = shapes(pr, d);
    for k in KINDS {
        let c = mine.get_mut(k).ok_or("handover: missing own commitment part")?;
        let want = if old { &so[k] } else { &sn[k] };
        c.shape.base = want.base;
        if &c.shape != want {
            return Err("handover: own commitment part has the wrong shape".into());
        }
        // refuse a further opening before sending anything (pcs_side counts the life itself)
        if c.shape.hide > 0 && c.opened_lives + 1 > c.max_lives {
            return Err(format!(
                "LifeExhausted: commitment {k} already opened in {} proofs; a further opening reveals it",
                pr.lives
            ));
        }
    }
    // roots of every party's parts; the old committee's are the first n_old
    let all = gather_hashes(net, &[mine["W1"].root, mine["W2"].root]);
    let side_roots = |r: std::ops::Range<usize>| -> Roots {
        KINDS.iter().enumerate().map(|(ki, k)| (k.to_string(), r.clone().map(|p| all[p][ki]).collect())).collect()
    };
    let (old_roots, new_roots) = (side_roots(0..n_old), side_roots(n_old..n));
    if lp.ext != pr.ext {
        return Err("handover: the Ligero's extension degree differs from the profile's".into());
    }
    match pr.ext {
        1 => prove_e::<1>(pr, lp, d, n_old, n_new, ctx, mine, net, det, old_roots, new_roots, &so, &sn),
        2 => prove_e::<2>(pr, lp, d, n_old, n_new, ctx, mine, net, det, old_roots, new_roots, &so, &sn),
        e => Err(format!("handover: extension degree {e} is not supported")),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_e<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    mine: &mut BTreeMap<String, PcsParty>,
    net: &mut dyn Net,
    det: &Det,
    old_roots: Roots,
    new_roots: Roots,
    so: &BTreeMap<String, Shape>,
    sn: &BTreeMap<String, Shape>,
) -> Result<HandoverProof, String> {
    let n = n_old + n_new;
    let g = net.me();
    let old = g < n_old;
    let mut tr = transcript(ctx, &old_roots, &new_roots);
    let (ev, shv, urows, nr) = schedule::<E>(&mut tr, pr, d, so, sn);
    let seed_label = format!("(('handover',), {})", ctx.repr());
    let mut lg = LigParty::new(lp, g, n, &seed_label, det);
    for (e, (key, pt)) in ev.iter().enumerate() {
        let s = &shv[e];
        // E component rows (cosnark.row_combo_e), component-major; the other committee's parties hold zeros
        let u: Vec<Vec<u64>> = if key.starts_with("old") == old {
            mine[&key[4..]].row_combo_e::<E>(&s.eval_weights_e::<E>(pt))
        } else {
            vec![vec![0u64; s.w]; E]
        };
        for uk in &u {
            for s0 in (0..s.w).step_by(pr.k_l) {
                lg.add_row(&uk[s0..(s0 + pr.k_l).min(s.w)]);
            }
        }
    }
    debug_assert_eq!(lg.rows.len(), nr);
    let eval_roots = lg.commit(net);
    let mask_roots = lg.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    let (prox_old, cols_old) = pcs_side::<E>(pr, mine, old, 0..n_old, &mut tr, net)?;
    let (prox_new, cols_new) = pcs_side::<E>(pr, mine, !old, n_old..n, &mut tr, net)?;
    let cols = colsum_map(so, sn, &cols_old, &cols_new);
    let sys = HandoverSys::<E> { kl: pr.k_l, ev, shapes: shv, cols, urows };
    let ligero = lg.prove(net, &mut tr, &sys, &[]);
    Ok(HandoverProof { old_roots, new_roots, eval_roots, mask_roots, prox_old, cols_old, prox_new, cols_new, ligero, carry_roots: Roots::new() })
}

/// cosnark.pcs_prove(part, [], tr, n_side) for one committee, run over the joint net: the committee's parties
/// contribute, the others send nothing and follow the transcript.
fn pcs_side<const E: usize>(
    pr: &Profile,
    mine: &mut BTreeMap<String, PcsParty>,
    member: bool,
    side: std::ops::Range<usize>,
    tr: &mut Transcript,
    net: &mut dyn Net,
) -> Result<(BTreeMap<String, Vec<Vec<u64>>>, BTreeMap<String, PcsCols>), String> {
    let mut prox = BTreeMap::new();
    for k in KINDS {
        let s = mine[k].shape.clone();
        // F_{p^E} proximity weights: one row per custodian, its E components concatenated (cosnark.pcs_prove)
        let gam = s.prox_weights_e::<E>(ext::chal::<E>(tr, s.prox_len_e(E)));
        let v = if member { mine[k].row_combo_e::<E>(&gam).concat() } else { Vec::new() };
        let all: Vec<Vec<u64>> = net.all_gather(v)[side.clone()].to_vec();
        tr.absorb(|h| {
            h.s("g").s(k).list2(&all);
        });
        prox.insert(k.to_string(), all);
    }
    let mut cols = BTreeMap::new();
    for k in KINDS {
        let npts = mine[k].shape.npts;
        if member {
            mine.get_mut(k).unwrap().take_life(k, pr.lives).map_err(|e| format!("LifeExhausted: {}", e.0))?;
        }
        let jj = tr.distinct_cols(pr.t_cols, npts);
        let ops: Vec<Opening> = if member { jj.par_iter().map(|&j| mine[k].open(j)).collect() } else { Vec::new() };
        let all = net.all_gather(encode_openings(&[ops]));
        let open = all[side.clone()].iter().map(|v| decode_openings(v).remove(0)).collect();
        cols.insert(k.to_string(), PcsCols { j: jj, open });
    }
    Ok((prox, cols))
}

// ------------------------------------------------------------------------------------------------ resharing
/// TEST ONLY (the Python reference's draw order, for the vs-Python check): handover.reshare with Mersenne Twister
/// streams. MT19937 is not a CSPRNG: a new custodian that sees enough of an old custodian's subshares could
/// recover the stream and predict the subshares sent to the others. Production resharing is `reshare_os`.
/// old_shares[i] = custodian i's share vector; returns (sub[i][j], new_shares[j]); with one stream for all
/// (`rng.len() == 1`) the draws are in Python's order (random.Random(seed)).
pub fn reshare(old_shares: &[Vec<u64>], n_new: usize, rng: &mut [pycompat::PyRandom]) -> (Vec<Vec<Vec<u64>>>, Vec<Vec<u64>>) {
    let len = old_shares[0].len();
    let mut sub = Vec::with_capacity(old_shares.len());
    for (i, s) in old_shares.iter().enumerate() {
        let r = if rng.len() == 1 { &mut rng[0] } else { &mut rng[i] };
        let mut parts: Vec<Vec<u64>> = (0..n_new - 1).map(|_| (0..len).map(|_| r.randrange_u64(field::p())).collect()).collect();
        let last = (0..len).map(|c| parts.iter().fold(s[c], |a, p| field::sub(a, p[c]))).collect();
        parts.push(last);
        sub.push(parts);
    }
    let new = (0..n_new).map(|j| combine(&sub.iter().map(|p| p[j].as_slice()).collect::<Vec<_>>())).collect();
    (sub, new)
}

/// Production resharing of one old custodian's share: n_new - 1 uniform subshares from the OS CSPRNG (getrandom,
/// rejection sampling on 61 bits) and the remainder, so they sum to the share.
pub fn reshare_os(share: &[u64], n_new: usize) -> Vec<Vec<u64>> {
    let p = field::p();
    let mut parts: Vec<Vec<u64>> = (0..n_new - 1).map(|_| os_field(share.len(), p)).collect();
    let last = (0..share.len()).map(|c| parts.iter().fold(share[c], |a, q| field::sub(a, q[c]))).collect();
    parts.push(last);
    parts
}

/// Uniform elements of F_p from the OS CSPRNG.
pub fn os_field(n: usize, p: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(n);
    let mut buf = vec![0u8; 8 * 4096];
    while out.len() < n {
        getrandom::getrandom(&mut buf).expect("OS randomness");
        for c in buf.chunks_exact(8) {
            let x = u64::from_le_bytes(c.try_into().unwrap()) & ((1u64 << 61) - 1);
            if x < p && out.len() < n {
                out.push(x);
            }
        }
    }
    buf.iter_mut().for_each(|b| unsafe { std::ptr::write_volatile(b, 0) });
    out
}

/// New custodian j's share: the sum of the subshares it received.
pub fn combine(received: &[&[u64]]) -> Vec<u64> {
    let len = received[0].len();
    (0..len).map(|c| received.iter().fold(0u64, |a, s| field::add(a, s[c]))).collect()
}

// ------------------------------------------------------------------------------------------------ cut E (DEFER)
// handover.py's cut E section (prove_defer / verify_defer / schema_defer, magic DLHAND02). The pending head's W1, W2
// (one life) are opened once and evaluated at the handover's r and at the head's r_k (the discharge against the old
// carries c1p, c2p, second life); the new committee's W is absorbed before r and not opened; its carries cN1, cN2 =
// new W(r) (each new custodian its own share's evaluation) are committed after r ("carry") and proved equal to old
// W(r). The new head is pending: points {W1, W2} = r, carry_roots {c1p: cN1, c2p: cN2}.
use crate::defer::{carry_m, carry_shape, DeferIn, Pending, CARRY, CARRY_IN};

pub const MAGIC_E: &[u8; 8] = b"DLHAND02";

/// The cut E shapes: (old: W1, W2 [single life] and, for a pending head, c1p, c2p [second life]; new W1, W2 [single
/// life, roots only]; new carries c1, c2 [first life]).
pub fn shapes_defer(pr: &Profile, d: usize, pending: bool) -> (BTreeMap<String, Shape>, BTreeMap<String, Shape>, BTreeMap<String, Shape>) {
    let m = 2 * log2(d);
    let w = Shape::new(&pr.w_life(), m, 0);
    let mut so: BTreeMap<String, Shape> = KINDS.iter().map(|k| (k.to_string(), w.clone())).collect();
    if pending {
        for k in CARRY_IN {
            so.insert(k.to_string(), carry_shape(pr, true));
        }
    }
    let sn = KINDS.iter().map(|k| (k.to_string(), w.clone())).collect();
    let sc = CARRY.iter().map(|k| (k.to_string(), carry_shape(pr, false))).collect();
    (so, sn, sc)
}

/// handover._devals: pairs (W evaluation, carry evaluation); keys "old W1", "new c1", ... (the cols map's keys).
fn devals<const E: usize>(r: &[Vec<[u64; E]>; 2], dpts: Option<&[Vec<[u64; E]>; 2]>) -> EvalsE<E> {
    let cpt = vec![ext::zero::<E>(); carry_m(E)];
    let mut ev: EvalsE<E> = Vec::new();
    for (q, k) in KINDS.iter().enumerate() {
        ev.push((format!("old {k}"), r[q].clone()));
        ev.push((format!("new {}", CARRY[q]), cpt.clone()));
    }
    if let Some(dp) = dpts {
        for (q, k) in KINDS.iter().enumerate() {
            ev.push((format!("old {k}"), dp[q].clone()));
            ev.push((format!("old {}", CARRY_IN[q]), cpt.clone()));
        }
    }
    ev
}

fn dshape<'a>(key: &str, so: &'a BTreeMap<String, Shape>, sc: &'a BTreeMap<String, Shape>) -> &'a Shape {
    let (side, k) = key.split_once(' ').unwrap();
    if side == "old" {
        &so[k]
    } else {
        &sc[k]
    }
}

fn drows(pr: &Profile, ev_shapes: &[Shape], e: usize) -> (Vec<Vec<usize>>, usize) {
    let (mut urows, mut nxt) = (Vec::new(), 0);
    for s in ev_shapes {
        let nr = e * s.w.div_ceil(pr.k_l);
        urows.push((nxt..nxt + nr).collect::<Vec<usize>>());
        nxt += nr;
    }
    (urows, nxt)
}

pub fn nrows_defer(pr: &Profile, d: usize, pending: bool) -> usize {
    let (so, _, sc) = shapes_defer(pr, d, pending);
    let per = pr.ext * (so["W1"].w.div_ceil(pr.k_l) + sc["c1"].w.div_ceil(pr.k_l));
    if pending {
        4 * per
    } else {
        2 * per
    }
}

/// handover._dconstraints: PCS consistency of every evaluation, then per pair W(pt) = carry (close_constraints' form).
struct DeferSys<const E: usize> {
    kl: usize,
    ev: EvalsE<E>,
    shapes: Vec<Shape>,
    cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: Vec<Vec<usize>>,
}

impl<const E: usize> LinSystem for DeferSys<E> {
    fn emit(&self, sink: &mut dyn LinSink) {
        pcs_consistency_e::<E>(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.urows);
        let mut em = crate::spine::EEm::<E>::new(sink);
        for i in 0..self.ev.len() / 2 {
            let (ew, ec) = (2 * i, 2 * i + 1);
            crate::spine::y_form(&mut em, &self.ev, &self.shapes, &self.urows, self.kl, ew, ext::one());
            let r0 = self.urows[ec][0];
            em.var(std::array::from_fn(|k| (r0, k)), ext::neg(ext::one()));
            let (wk, ck) = (&self.ev[ew].0[4..], &self.ev[ec].0);
            let label = if ck.starts_with("new") {
                format!("handover: old {wk}(r) = new carry {}", &ck[4..])
            } else {
                format!("handover discharge: old {wk}(r_k) = {}", &ck[4..])
            };
            em.done(&label, ext::zero());
        }
    }
}

/// The transcript up to r: ctx, old W, the old carries (pending head), new W (handover._dkeys).
fn transcript_defer(ctx: &HandoverCtx, old_roots: &Roots, new_roots: &Roots, pending: bool) -> Transcript {
    let mut tr = Transcript::new("handover");
    let cr = ctx.repr();
    tr.absorb(|h| {
        h.s("ctx").raw(cr.as_bytes());
    });
    let mut keys: Vec<(&str, &str)> = KINDS.iter().map(|k| ("old", *k)).collect();
    if pending {
        keys.extend(CARRY_IN.iter().map(|k| ("old", *k)));
    }
    keys.extend(KINDS.iter().map(|k| ("new", *k)));
    for (side, k) in keys {
        let roots = if side == "old" { old_roots } else { new_roots };
        let key = format!("('{side}', '{k}')");
        tr.absorb(|h| {
            h.str_any(&key).list_hx(&roots[k]);
        });
    }
    tr
}

fn dpoints<const E: usize>(tr: &mut Transcript, d: usize) -> [Vec<[u64; E]>; 2] {
    let ld = log2(d);
    let r1 = ext::chal::<E>(tr, 2 * ld);
    let r2 = ext::chal::<E>(tr, 2 * ld);
    [r1, r2]
}

fn pend_points<const E: usize>(p: &Pending) -> [Vec<[u64; E]>; 2] {
    [p.points_e::<E>("W1"), p.points_e::<E>("W2")]
}

fn flat<const E: usize>(v: &[[u64; E]]) -> Vec<u64> {
    v.iter().flat_map(|x| x.iter().copied()).collect()
}

/// The PCS part of one committee over the joint net (cosnark.pcs_prove(part, [], tr, n_side)): keys in sorted order;
/// members contribute their parts (and spend a life), the others follow the transcript.
fn pcs_side_defer<const E: usize>(
    pr: &Profile,
    sh: &BTreeMap<String, Shape>,
    mut own: Option<&mut BTreeMap<String, PcsParty>>,
    side: std::ops::Range<usize>,
    tr: &mut Transcript,
    net: &mut dyn Net,
) -> Result<(BTreeMap<String, Vec<Vec<u64>>>, BTreeMap<String, PcsCols>), String> {
    let mut prox = BTreeMap::new();
    for (k, s) in sh {
        let gam = s.prox_weights_e::<E>(ext::chal::<E>(tr, s.prox_len_e(E)));
        let v = match own.as_ref() {
            Some(m) => m[k].row_combo_e::<E>(&gam).concat(),
            None => Vec::new(),
        };
        let all: Vec<Vec<u64>> = net.all_gather(v)[side.clone()].to_vec();
        tr.absorb(|h| {
            h.s("g").s(k).list2(&all);
        });
        prox.insert(k.clone(), all);
    }
    let mut cols = BTreeMap::new();
    for (k, s) in sh {
        if let Some(m) = own.as_mut() {
            let c = m.get_mut(k).unwrap();
            let ml = c.max_lives;
            c.take_life(k, ml).map_err(|e| format!("LifeExhausted: {}", e.0))?;
        }
        let jj = tr.distinct_cols(pr.t_cols, s.npts);
        let ops: Vec<Opening> = match own.as_ref() {
            Some(m) => jj.par_iter().map(|&j| m[k].open(j)).collect(),
            None => Vec::new(),
        };
        let all = net.all_gather(encode_openings(&[ops]));
        let open = all[side.clone()].iter().map(|v| decode_openings(v).remove(0)).collect();
        cols.insert(k.clone(), PcsCols { j: jj, open });
    }
    Ok((prox, cols))
}

/// One custodian's part of handover.prove_defer. `mine`: this party's W1, W2 parts (an old party: the pending head's
/// children, single life, unopened; a new party: its fresh commitment, `pr.w_life()`). `pend`: the head's pending
/// claims (public, from the ledger; None for a final head). `old_carries`: an old party's own c1p, c2p (their
/// first life spent in step k). Returns the proof and, for a new party, its side of the new head's pending claims
/// (points r, carries {c1p: cN1, c2p: cN2}), which the next step's prover takes as its DeferIn.
#[allow(clippy::too_many_arguments)]
pub fn prove_defer(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    mine: &mut BTreeMap<String, PcsParty>,
    pend: Option<&Pending>,
    old_carries: Option<&mut BTreeMap<String, PcsParty>>,
    net: &mut dyn Net,
    det: &Det,
) -> Result<(HandoverProof, Option<DeferIn>), String> {
    if lp.ext != pr.ext {
        return Err("handover: the Ligero's extension degree differs from the profile's".into());
    }
    match pr.ext {
        1 => prove_defer_e::<1>(pr, lp, d, n_old, n_new, ctx, mine, pend, old_carries, net, det),
        2 => prove_defer_e::<2>(pr, lp, d, n_old, n_new, ctx, mine, pend, old_carries, net, det),
        e => Err(format!("handover: extension degree {e} is not supported")),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_defer_e<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    mine: &mut BTreeMap<String, PcsParty>,
    pend: Option<&Pending>,
    mut old_carries: Option<&mut BTreeMap<String, PcsParty>>,
    net: &mut dyn Net,
    det: &Det,
) -> Result<(HandoverProof, Option<DeferIn>), String> {
    let n = n_old + n_new;
    let g = net.me();
    assert_eq!(net.n(), n);
    let old = g < n_old;
    let pending = pend.is_some();
    let (so, sn, sc) = shapes_defer(pr, d, pending);
    for k in KINDS {
        let c = mine.get_mut(k).ok_or("handover: missing own commitment part")?;
        c.shape.base = 0;
        if c.shape != so[k] {
            return Err("handover: own commitment part has the wrong shape".into());
        }
        if old && c.shape.hide > 0 && c.opened_lives + 1 > c.max_lives {
            return Err(format!("LifeExhausted: commitment {k} already opened in {} proofs; a further opening reveals it", c.max_lives));
        }
    }
    if old && pending {
        let oc = old_carries.as_mut().ok_or("handover: an old custodian of a pending head needs its carries")?;
        for k in CARRY_IN {
            let c = oc.get_mut(k).ok_or("handover: missing own carry")?;
            c.shape.base = c.shape.block; // the carry's second life
            if c.shape != so[k] || pend.unwrap().carry_roots[k].get(g) != Some(&c.root) {
                return Err(format!("handover: own carry {k} is not the head's pending carry"));
            }
        }
    }
    let all = gather_hashes(net, &[mine["W1"].root, mine["W2"].root]);
    let side_roots = |r: std::ops::Range<usize>| -> Roots {
        KINDS.iter().enumerate().map(|(ki, k)| (k.to_string(), r.clone().map(|p| all[p][ki]).collect())).collect()
    };
    let (mut old_roots, new_roots) = (side_roots(0..n_old), side_roots(n_old..n));
    if let Some(p) = pend {
        for k in CARRY_IN {
            old_roots.insert(k.to_string(), p.carry_roots[k].clone());
        }
    }
    let mut tr = transcript_defer(ctx, &old_roots, &new_roots, pending);
    let r = dpoints::<E>(&mut tr, d);
    // the new committee's carries cN = new W(r)
    let mut my_carries: BTreeMap<String, PcsParty> = BTreeMap::new();
    if !old {
        for (q, k) in KINDS.iter().enumerate() {
            let (_, y) = mine[*k].eval_share_e::<E>(&r[q]);
            let mut v = y.to_vec();
            v.resize(1 << carry_m(E), 0);
            my_carries.insert(CARRY[q].to_string(), PcsParty::commit(pr, &v, CARRY[q], g - n_old, det));
        }
    }
    let mc: Vec<Hash> = if old { vec![[0u8; 32]; 2] } else { CARRY.iter().map(|k| my_carries[*k].root).collect() };
    let allc = gather_hashes(net, &mc);
    let carry_roots: Roots = CARRY.iter().enumerate().map(|(ci, k)| (k.to_string(), (n_old..n).map(|p| allc[p][ci]).collect())).collect();
    tr.absorb(|h| {
        h.s("carry").list_hx(&carry_roots["c1"]).list_hx(&carry_roots["c2"]);
    });
    let dp = pend.map(pend_points::<E>);
    let ev = devals::<E>(&r, dp.as_ref());
    let shv: Vec<Shape> = ev.iter().map(|(k, _)| dshape(k, &so, &sc).clone()).collect();
    let (urows, nr) = drows(pr, &shv, E);
    let seed_label = format!("(('handover',), {})", ctx.repr());
    let mut lg = LigParty::new(lp, g, n, &seed_label, det);
    for (e, (key, pt)) in ev.iter().enumerate() {
        let s = &shv[e];
        let (side, k) = key.split_once(' ').unwrap();
        let u: Vec<Vec<u64>> = if (side == "old") == old {
            let c = if side == "new" {
                &my_carries[k]
            } else if k.starts_with('W') {
                &mine[k]
            } else {
                &old_carries.as_ref().unwrap()[k]
            };
            c.row_combo_e::<E>(&s.eval_weights_e::<E>(pt))
        } else {
            vec![vec![0u64; s.w]; E]
        };
        for uk in &u {
            for s0 in (0..s.w).step_by(pr.k_l) {
                lg.add_row(&uk[s0..(s0 + pr.k_l).min(s.w)]);
            }
        }
    }
    debug_assert_eq!(lg.rows.len(), nr);
    let eval_roots = lg.commit(net);
    let mask_roots = lg.commit_masks(net);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&eval_roots).list_hx(&mask_roots);
    });
    // the old side: its W and (pending) its carries, in one map (sorted keys: W1, W2, c1p, c2p)
    let mut old_own: Option<BTreeMap<String, PcsParty>> = None;
    if old {
        let mut m: BTreeMap<String, PcsParty> = KINDS.iter().map(|k| (k.to_string(), mine.remove(*k).unwrap())).collect();
        if pending {
            let oc = old_carries.as_mut().unwrap();
            for k in CARRY_IN {
                m.insert(k.to_string(), oc.remove(k).unwrap());
            }
        }
        old_own = Some(m);
    }
    let res = pcs_side_defer::<E>(pr, &so, old_own.as_mut(), 0..n_old, &mut tr, net);
    // give the parts back (their life counters spent) before any error returns
    if let Some(m) = old_own {
        for (k, c) in m {
            if k.starts_with('W') {
                mine.insert(k, c);
            } else {
                old_carries.as_mut().unwrap().insert(k, c);
            }
        }
    }
    let (prox_old, cols_old) = res?;
    let (prox_new, cols_new) = pcs_side_defer::<E>(pr, &sc, if old { None } else { Some(&mut my_carries) }, n_old..n, &mut tr, net)?;
    let mut cols = BTreeMap::new();
    for (k, s) in &so {
        cols.insert(format!("old {k}"), (cols_old[k].j.clone(), colsums(&cols_old[k], s.r)));
    }
    for (k, s) in &sc {
        cols.insert(format!("new {k}"), (cols_new[k].j.clone(), colsums(&cols_new[k], s.r)));
    }
    let sys = DeferSys::<E> { kl: pr.k_l, ev, shapes: shv, cols, urows };
    let ligero = lg.prove(net, &mut tr, &sys, &[]);
    let out = (!old).then(|| DeferIn {
        points: [("W1".to_string(), flat(&r[0])), ("W2".to_string(), flat(&r[1]))].into_iter().collect(),
        carries: [("c1p".to_string(), my_carries.remove("c1").unwrap()), ("c2p".to_string(), my_carries.remove("c2").unwrap())].into_iter().collect(),
    });
    Ok((HandoverProof { old_roots, new_roots, eval_roots, mask_roots, prox_old, cols_old, prox_new, cols_new, ligero, carry_roots }, out))
}

/// handover.verify_defer on a parsed proof. Returns the new head's pending claims.
#[allow(clippy::too_many_arguments)]
pub fn verify_proof_defer(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    old_roots: &Roots,
    pend: Option<&Pending>,
    proof: &HandoverProof,
) -> Result<Pending, String> {
    let pending = pend.is_some();
    let (so, sn, sc) = shapes_defer(pr, d, pending);
    if !proof.old_roots.keys().eq(so.keys()) {
        return Err("handover: the proof names the wrong old commitments for this head".into());
    }
    if KINDS.iter().any(|k| old_roots.get(*k) != Some(&proof.old_roots[*k])) {
        return Err("handover: old roots are not the ledger head's".into());
    }
    if let Some(p) = pend {
        if CARRY_IN.iter().any(|k| p.carry_roots.get(*k) != Some(&proof.old_roots[*k])) {
            return Err("handover: the old carries are not the head's pending carries".into());
        }
    }
    if proof.old_roots.values().any(|v| v.len() != n_old)
        || proof.new_roots.values().any(|v| v.len() != n_new)
        || proof.carry_roots.values().any(|v| v.len() != n_new)
    {
        return Err("handover: wrong committee sizes".into());
    }
    if lp.ext != pr.ext {
        return Err("handover: the Ligero's extension degree differs from the profile's".into());
    }
    match pr.ext {
        1 => verify_defer_e::<1>(pr, lp, d, n_old, n_new, ctx, pend, proof, &so, &sn, &sc),
        2 => verify_defer_e::<2>(pr, lp, d, n_old, n_new, ctx, pend, proof, &so, &sn, &sc),
        e => Err(format!("handover: extension degree {e} is not supported")),
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_defer_e<const E: usize>(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    pend: Option<&Pending>,
    proof: &HandoverProof,
    so: &BTreeMap<String, Shape>,
    _sn: &BTreeMap<String, Shape>,
    sc: &BTreeMap<String, Shape>,
) -> Result<Pending, String> {
    let mut tr = transcript_defer(ctx, &proof.old_roots, &proof.new_roots, pend.is_some());
    let r = dpoints::<E>(&mut tr, d);
    tr.absorb(|h| {
        h.s("carry").list_hx(&proof.carry_roots["c1"]).list_hx(&proof.carry_roots["c2"]);
    });
    let dp = pend.map(pend_points::<E>);
    let ev = devals::<E>(&r, dp.as_ref());
    let shv: Vec<Shape> = ev.iter().map(|(k, _)| dshape(k, so, sc).clone()).collect();
    let (urows, nxt) = drows(pr, &shv, E);
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    for (side, nn, sh, roots, prox, pc) in [
        ("old", n_old, so, &proof.old_roots, &proof.prox_old, &proof.cols_old),
        ("new", n_new, sc, &proof.carry_roots, &proof.prox_new, &proof.cols_new),
    ] {
        let keys: Vec<String> = sh.keys().cloned().collect();
        let shs: Vec<Shape> = keys.iter().map(|k| sh[k].clone()).collect();
        let rts: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
        let pxs: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| prox[k].clone()).collect();
        let cls: Vec<PcsCols> = keys.iter().map(|k| pc[k].clone()).collect();
        pcs::verify_e::<E>(pr, &keys, &shs, &rts, &pxs, &cls, &mut tr, nn).map_err(|e| format!("handover ({side} committee): {e}"))?;
    }
    let mut cols = BTreeMap::new();
    for (k, s) in so {
        cols.insert(format!("old {k}"), (proof.cols_old[k].j.clone(), colsums(&proof.cols_old[k], s.r)));
    }
    for (k, s) in sc {
        cols.insert(format!("new {k}"), (proof.cols_new[k].j.clone(), colsums(&proof.cols_new[k], s.r)));
    }
    let sys = DeferSys::<E> { kl: pr.k_l, ev, shapes: shv, cols, urows };
    ligero::verify(lp, n_old + n_new, &[proof.eval_roots.clone()], &[nxt], &proof.mask_roots, &sys, &[], &proof.ligero, &mut tr)?;
    Ok(Pending {
        points: [("W1".to_string(), flat(&r[0])), ("W2".to_string(), flat(&r[1]))].into_iter().collect(),
        carry_roots: [("c1p".to_string(), proof.carry_roots["c1"].clone()), ("c2p".to_string(), proof.carry_roots["c2"].clone())].into_iter().collect(),
    })
}

/// The untrusted-input verifier under cut E: (the new roots, the new head's pending claims). `pend`: the head's
/// pending claims from the ledger (None: a final head).
#[allow(clippy::too_many_arguments)]
pub fn verify_defer(
    pr: &Profile,
    lp: &LigParams,
    d: usize,
    n_old: usize,
    n_new: usize,
    ctx: &HandoverCtx,
    old_roots: &Roots,
    pend: Option<&Pending>,
    blob: &[u8],
) -> Result<(Roots, Pending), String> {
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = decode_defer(pr, blob, d, n_old, n_new, pend.is_some()).map_err(|e| format!("parse: {e}"))?;
        let p = verify_proof_defer(pr, lp, d, n_old, n_new, ctx, old_roots, pend, &proof)?;
        Ok((proof.new_roots, p))
    }));
    match res {
        Ok(r) => r,
        Err(_) => Err("malformed handover proof (panic)".into()),
    }
}

/// handover.decode under cut E (schema_defer). `pending` comes from the ledger.
pub fn decode_defer(pr: &Profile, blob: &[u8], d: usize, n_old: usize, n_new: usize, pending: bool) -> PR<HandoverProof> {
    if !sizes_ok(d, n_old, n_new) {
        return Err("committee sizes or width out of range".into());
    }
    let (so, sn, sc) = shapes_defer(pr, d, pending);
    let mut r = R::new(blob);
    if r.take(8)? != MAGIC_E {
        return Err("bad magic".into());
    }
    let hdr = r.take(4)?;
    if (u16::from_be_bytes([hdr[0], hdr[1]]) as usize, hdr[2] as usize, hdr[3] as usize) != (d, n_old, n_new) {
        return Err("width or committee sizes differ from the ledger's".into());
    }
    let n = n_old + n_new;
    let mut po = r_pcs(&mut r, pr, n_old, &so)?;
    let pn = r_pcs(&mut r, pr, n_new, &sn)?;
    let mut pc = r_pcs(&mut r, pr, n_new, &sc)?;
    let eval_roots = r.hs(n)?;
    let mask_roots = r.hs(n)?;
    r_prox_cols_e(&mut r, pr, n_old, &so, &mut po, pr.ext)?;
    r_prox_cols_e(&mut r, pr, n_new, &sc, &mut pc, pr.ext)?;
    let ligero = r_ligero(&mut r, pr, n, &[nrows_defer(pr, d, pending)])?;
    if r.o != r.d.len() {
        return Err("trailing bytes".into());
    }
    Ok(HandoverProof {
        old_roots: po.0,
        new_roots: pn.0,
        eval_roots,
        mask_roots,
        prox_old: po.1,
        cols_old: po.2,
        prox_new: pc.1,
        cols_new: pc.2,
        ligero,
        carry_roots: pc.0,
    })
}

fn encode_defer(pr: &Profile, d: usize, p: &HandoverProof) -> Vec<u8> {
    let (n_old, n_new) = (p.old_roots["W1"].len(), p.new_roots["W1"].len());
    assert!(sizes_ok(d, n_old, n_new));
    let pending = p.old_roots.contains_key("c1p");
    let (so, sn, sc) = shapes_defer(pr, d, pending);
    let mut w = crate::wire::W { b: Vec::new() };
    w.b.extend_from_slice(MAGIC_E);
    w.b.extend_from_slice(&(d as u16).to_be_bytes());
    w.b.push(n_old as u8);
    w.b.push(n_new as u8);
    let n = n_old + n_new;
    crate::wire::w_roots(&mut w, n_old, &so, &p.old_roots);
    crate::wire::w_roots(&mut w, n_new, &sn, &p.new_roots);
    crate::wire::w_roots(&mut w, n_new, &sc, &p.carry_roots);
    w.hs(&p.eval_roots, n);
    w.hs(&p.mask_roots, n);
    crate::wire::w_prox_cols_e(&mut w, pr, n_old, &so, &p.prox_old, &p.cols_old, pr.ext);
    crate::wire::w_prox_cols_e(&mut w, pr, n_new, &sc, &p.prox_new, &p.cols_new, pr.ext);
    crate::wire::w_ligero(&mut w, pr, n, &[nrows_defer(pr, d, pending)], &p.ligero);
    w.b
}

fn byte_len_defer(pr: &Profile, d: usize, p: &HandoverProof) -> usize {
    let (n_old, n_new) = (p.old_roots["W1"].len(), p.new_roots["W1"].len());
    let n = n_old + n_new;
    let pending = p.old_roots.contains_key("c1p");
    let (so, _, sc) = shapes_defer(pr, d, pending);
    let tree = |js: &[usize], sz: usize, path_len: usize| -> usize {
        if pr.multiproof {
            js.len() * (8 * sz + 32) + 32 * crate::wire::mp_needed(js, path_len - 1).len()
        } else {
            js.len() * (8 * sz + 32 * path_len)
        }
    };
    let side = |nn: usize, sh: &BTreeMap<String, Shape>, cols: &BTreeMap<String, PcsCols>| -> usize {
        sh.iter().map(|(k, s)| 32 * nn + 8 * nn * pr.ext * s.w + 4 * pr.t_cols + nn * tree(&cols[k].j, s.r, s.path_len())).sum::<usize>()
    };
    let (k, t) = (pr.k_l, pr.t_hide);
    let lg = crate::pcs::bitlen(pr.blow * (k + t) - 1) + 1;
    let lj: Vec<usize> = if pr.multiproof { p.ligero.j.clone() } else { (0..pr.t_open).collect() };
    let lig = 8 * pr.ext * ((k + t) + (2 * k + t - 1) + (2 * (k + t) - 1))
        + if pr.multiproof { 4 * pr.t_open } else { 0 }
        + n * (tree(&lj, nrows_defer(pr, d, pending), lg) + tree(&lj, 3 * pr.ext, lg));
    12 + side(n_old, &so, &p.cols_old) + 32 * n_new * KINDS.len() + side(n_new, &sc, &p.cols_new) + 2 * 32 * n + lig
}
