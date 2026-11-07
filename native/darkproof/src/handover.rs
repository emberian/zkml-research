//! handover.py: the custody-handover proof's bytes (schema-driven, every length a function of (d, n_old, n_new, the
//! pinned profile)) and its untrusted-input verifier. The old committee's commitment of W (the ledger head's roots,
//! carried in its second life: mask block 1) and the new committee's fresh commitment (first life) are evaluated at
//! one Fiat-Shamir point per matrix; a collaborative ZK Ligero among all n_old + n_new custodians proves, on hidden
//! rows, evaluation consistency at both commitments' opened columns and W_old(r) = W_new(r).
use crate::field;
use crate::h::{py_str_repr, Hash};
use crate::ligero::{self, LigParams, LigProof, LinSink, LinSystem};
use crate::pcs::{self, colsums, PcsCols, Shape};
use crate::spine::{log2, pcs_consistency, Evals};
use crate::transcript::{eqv, Transcript};
use crate::wire::{r_ligero, r_pcs, r_prox_cols, R, PR};
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
}

/// The public shapes (cosnark_zk.PubShape) of the old (second life) and new (first life) matrix commitments.
pub fn shapes(pr: &Profile, d: usize) -> (BTreeMap<String, Shape>, BTreeMap<String, Shape>) {
    let m = 2 * log2(d);
    let old_base = if pr.lives > 0 { pr.nmask / pr.lives } else { 0 };
    let mk = |base| KINDS.iter().map(|k| (k.to_string(), Shape::new(pr, m, base))).collect();
    (mk(old_base), mk(0))
}

/// Hidden Ligero rows: one u row combination per evaluation (old W1, new W1, old W2, new W2), ceil(W / K_L) rows each.
pub fn nrows(pr: &Profile, d: usize) -> usize {
    4 * shapes(pr, d).0["W1"].w.div_ceil(pr.k_l)
}

fn sizes_ok(d: usize, n_old: usize, n_new: usize) -> bool {
    d >= 2 && d.is_power_of_two() && d < 1 << 16 && (1..=255).contains(&n_old) && (1..=255).contains(&n_new)
}

/// The byte length the schema fixes (handover.encode's output length).
pub fn byte_len(pr: &Profile, d: usize, n_old: usize, n_new: usize) -> usize {
    let (so, _) = shapes(pr, d);
    let s = &so["W1"];
    let n = n_old + n_new;
    let pcs_side = |nn: usize| 2 * (32 * nn + 8 * nn * s.w + 4 * pr.t_cols + nn * pr.t_cols * (8 * s.r + 32 * s.path_len()));
    let lp_len = crate::pcs::bitlen(pr.blow * (pr.k_l + pr.t_hide) - 1) + 1;
    let lig = 8 * ((pr.k_l + pr.t_hide) + (2 * pr.k_l + pr.t_hide - 1) + (2 * (pr.k_l + pr.t_hide) - 1))
        + n * pr.t_open * ((8 * nrows(pr, d) + 32 * lp_len) + (8 * 3 + 32 * lp_len));
    12 + pcs_side(n_old) + pcs_side(n_new) + 2 * 32 * n + lig
}

/// handover.decode: d, n_old and n_new come from the ledger; any deviation from the schema is a parse error.
pub fn decode(pr: &Profile, blob: &[u8], d: usize, n_old: usize, n_new: usize) -> PR<HandoverProof> {
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
    r_prox_cols(&mut r, pr, n_old, &so, &mut po)?;
    r_prox_cols(&mut r, pr, n_new, &sn, &mut pn)?;
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
    })
}

/// handover._constraints: evaluation consistency at each commitment's opened columns, then old W(r) = new W(r).
struct HandoverSys {
    kl: usize,
    ev: Evals,
    shapes: Vec<Shape>,
    cols: BTreeMap<String, (Vec<usize>, Vec<Vec<u64>>)>,
    urows: Vec<Vec<usize>>,
}

impl LinSystem for HandoverSys {
    fn emit(&self, sink: &mut dyn LinSink) {
        pcs_consistency(sink, self.kl, &self.ev, &self.shapes, &self.cols, &self.urows);
        let mut buf: Vec<(u32, u32, u64)> = Vec::new();
        for (q, k) in KINDS.iter().enumerate() {
            let (eo, en) = (2 * q, 2 * q + 1);
            let s = &self.shapes[eo];
            let b = eqv(&self.ev[eo].1[..s.mc]);
            buf.clear();
            for c in 0..s.c {
                buf.push((self.urows[eo][c / self.kl] as u32, (c % self.kl) as u32, b[c]));
                buf.push((self.urows[en][c / self.kl] as u32, (c % self.kl) as u32, field::neg(b[c])));
            }
            sink.con(&format!("handover: old {k}(r) = new {k}(r)"), &buf, 0);
        }
    }
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
    let ld = log2(d);
    let (so, sn) = shapes(pr, d);
    if KINDS.iter().any(|k| proof.old_roots[*k].len() != n_old || proof.new_roots[*k].len() != n_new) {
        return Err("handover: wrong committee sizes".into());
    }
    let mut tr = Transcript::new("handover");
    let cr = ctx.repr();
    tr.absorb(|h| {
        h.s("ctx").raw(cr.as_bytes());
    });
    for side in ["old", "new"] {
        let roots = if side == "old" { &proof.old_roots } else { &proof.new_roots };
        for k in KINDS {
            let key = format!("('{side}', '{k}')");
            tr.absorb(|h| {
                h.str_any(&key).list_hx(&roots[k]);
            });
        }
    }
    let mut ev: Evals = Vec::new();
    let mut shv = Vec::new();
    for k in KINDS {
        let r = tr.chal(2 * ld);
        ev.push((format!("old {k}"), r.clone()));
        ev.push((format!("new {k}"), r));
        shv.push(so[k].clone());
        shv.push(sn[k].clone());
    }
    let mut urows = Vec::new();
    let mut nxt = 0;
    for s in &shv {
        let nr = s.w.div_ceil(pr.k_l);
        urows.push((nxt..nxt + nr).collect::<Vec<usize>>());
        nxt += nr;
    }
    tr.absorb(|h| {
        h.s("lig-evals").list_hx(&proof.eval_roots).list_hx(&proof.mask_roots);
    });
    let keys: Vec<String> = KINDS.iter().map(|k| k.to_string()).collect();
    let mut cols = BTreeMap::new();
    for (side, nn, sh, roots, prox, pc) in [
        ("old", n_old, &so, &proof.old_roots, &proof.prox_old, &proof.cols_old),
        ("new", n_new, &sn, &proof.new_roots, &proof.prox_new, &proof.cols_new),
    ] {
        let shs: Vec<Shape> = keys.iter().map(|k| sh[k].clone()).collect();
        let rts: Vec<Vec<Hash>> = keys.iter().map(|k| roots[k].clone()).collect();
        let pxs: Vec<Vec<Vec<u64>>> = keys.iter().map(|k| prox[k].clone()).collect();
        let cls: Vec<PcsCols> = keys.iter().map(|k| pc[k].clone()).collect();
        pcs::verify(pr, &keys, &shs, &rts, &pxs, &cls, &mut tr, nn)
            .map_err(|e| format!("handover ({side} committee): {e}"))?;
        for k in &keys {
            cols.insert(format!("{side} {k}"), (pc[k].j.clone(), colsums(&pc[k], sh[k].r)));
        }
    }
    let sys = HandoverSys { kl: pr.k_l, ev, shapes: shv, cols, urows };
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
