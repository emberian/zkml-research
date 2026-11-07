//! Per-step proofs in the deployed run: ONE custodian's share of the collaborative proof of one step, over that
//! custodian's own transport. Every party ends with the same bundle bytes (every proof message is broadcast), so each
//! custodian can hand the bundle to the ledger.
//!
//! Inputs come from the custodian's own step (darkstep::step::ProofRecord plus W1n, W2n) and its own preprocessing
//! tape: the proof section holds `tape_triples(..)` authenticated Beaver triples, consumed in this order:
//!   [spine Beaver products: spine::beaver_count(d)] [middle Beaver products: middle::beaver_count(n_had)]
//!   [spine Ligero: LigParty::tape_triples(lp, spine::LIG_SCALARS, 1)] [middle Ligero: (.., middle::LIG_SCALARS, 1)]
//! No dealer stream is consulted. PCS tails, masks, salts and Ligero randomness are each party's own secret stream.
use crate::h::Hash;
use crate::ligero::{LigParams, LigParty};
use crate::middle;
use crate::net::{gather_hashes, Net};
use crate::pcs::PcsParty;
use crate::rng::Det;
use crate::spdz::{Sh, Spdz, Triple};
use crate::spine;
use crate::step::{self, StepParams};
use crate::wire;
use crate::{Ctx, Profile};
use std::collections::BTreeMap;

/// One custodian's inputs for the proof of one step.
pub struct PartyStep {
    pub i: usize,
    pub n: usize,
    pub d: usize,
    pub alpha_i: u64,
    /// this party's shares: x y z1 h z2 d2 b g1 bg d1 (length d) and W1 W2 W1n W2n (d * d, row-major)
    pub wires: BTreeMap<String, Vec<Sh>>,
    /// the step's public transcript values, in order
    pub public: Vec<u64>,
    /// the middle's preprocessing atoms (truncation masks and bits, range bits, lookup powers, the b * g1 triples),
    /// in creation order
    pub atoms: Vec<Sh>,
    /// the tape's proof section (tape_triples(..) triples)
    pub triples: Vec<Triple>,
    /// TEST ONLY: the deterministic hook (bit-exact with the harness). PCS and Ligero randomness come from it and the
    /// Ligeros' triples from cozk's dealer stream, so the tape holds only the Beaver section.
    pub det: Det,
    /// TEST ONLY: prove even with a truncation input outside its proved bound (a forced bundle)
    pub ignore_range: bool,
}

pub struct StepProof {
    pub blob: Vec<u8>,
    /// this party's child commitments W1n, W2n: the next step's carry
    pub child: BTreeMap<String, PcsParty>,
    /// at genesis: every party's roots of its W1, W2 commitments (the ledger's genesis record)
    pub genesis_roots: Option<BTreeMap<String, Vec<Hash>>>,
    pub secs: f64,
    /// field elements this party sent during the proof
    pub sent: u64,
}

/// Hadamard rows of the middle for width d under program prm (data-independent: a replay on a zero transcript).
pub fn n_had(d: usize, prm: StepParams, carried: bool, tables: &(Vec<u64>, Vec<u64>)) -> usize {
    let zeros = vec![0u64; prm.transcript_len(d, carried)];
    step::replay(&zeros, d, prm, tables, carried).expect("replay of the program's own length").had.len()
}

/// The proof section of one step's tape: tape_triples plus the proved bounds' products (prm.rc).
pub fn step_section(lp: &LigParams, d: usize, prm: StepParams, carried: bool, tables: &(Vec<u64>, Vec<u64>)) -> usize {
    let zeros = vec![0u64; prm.transcript_len(d, carried)];
    let rec = step::replay(&zeros, d, prm, tables, carried).expect("replay of the program's own length");
    tape_triples(lp, d, rec.had.len()) + rec.range_products()
}

/// Triples one custodian's tape must hold in its proof section for one step (without proved bounds; with them use
/// step_section).
pub fn tape_triples(lp: &LigParams, d: usize, n_had: usize) -> usize {
    spine::beaver_count(d)
        + middle::beaver_count(n_had)
        + LigParty::tape_triples(lp, spine::LIG_SCALARS, 1)
        + LigParty::tape_triples(lp, middle::LIG_SCALARS, 1)
}

/// The proof of step ctx by custodian st.i. carry: this party's previous child commitments (None at genesis: W1, W2
/// are committed here and the genesis roots returned).
#[allow(clippy::too_many_arguments)]
pub fn prove_step(
    pr: &Profile,
    lp: &LigParams,
    tables: &(Vec<u64>, Vec<u64>),
    prm: StepParams,
    net: &mut dyn Net,
    ctx: &Ctx,
    st: PartyStep,
    carry: Option<BTreeMap<String, PcsParty>>,
) -> Result<StepProof, String> {
    let t0 = std::time::Instant::now();
    let sent0 = net.sent();
    let (i, n, d) = (st.i, st.n, st.d);
    if net.me() != i || net.n() != n {
        return Err("transport is for another party or committee size".into());
    }
    let own_tables;
    let tables = if prm.t_lo == -128 {
        tables
    } else {
        own_tables = step::tables_for(prm.t_lo);
        &own_tables
    };
    let det = st.det;
    let carried = prm.carried(ctx.step);
    let rec = step::replay(&st.public, d, prm, tables, carried).map_err(|e| format!("own transcript: {e:?}"))?;
    if rec.tpos != st.public.len() {
        return Err("own transcript is longer than the step program".into());
    }
    if st.atoms.len() != rec.n_program_atoms() {
        return Err(format!("{} middle atoms, the program has {}", st.atoms.len(), rec.n_program_atoms()));
    }
    let nb = spine::beaver_count(d) + rec.range_products() + middle::beaver_count(rec.had.len());
    let (ls, lm) = if det.on() {
        (0, 0)
    } else {
        (LigParty::tape_triples(lp, spine::LIG_SCALARS, 1), LigParty::tape_triples(lp, middle::LIG_SCALARS, 1))
    };
    if st.triples.len() != nb + ls + lm {
        return Err(format!("the tape's proof section has {} triples, the proof needs {}", st.triples.len(), nb + ls + lm));
    }
    let mut tri = st.triples;
    let lig_m: Vec<(u64, u64, u64)> = tri.split_off(nb + ls).into_iter().map(|(a, b, c)| (a.0, b.0, c.0)).collect();
    let lig_s: Vec<(u64, u64, u64)> = tri.split_off(nb).into_iter().map(|(a, b, c)| (a.0, b.0, c.0)).collect();
    let mut sp = Spdz::from_tape(i, n, st.alpha_i, tri);
    let mut wires = st.wires;
    let mut genesis_roots = None;
    let carry = match carry {
        Some(c) => c,
        None => {
            let g: BTreeMap<String, PcsParty> = ["W1", "W2"]
                .iter()
                .map(|k| {
                    let s: Vec<u64> = wires[*k].iter().map(|x| x.0).collect();
                    (k.to_string(), PcsParty::commit(pr, &s, k, i, &det))
                })
                .collect();
            let all = gather_hashes(net, &[g["W1"].root, g["W2"].root]);
            genesis_roots = Some(
                [("W1", 0), ("W2", 1)].iter().map(|(k, j)| (k.to_string(), (0..n).map(|p| all[p][*j]).collect())).collect(),
            );
            g
        }
    };
    let si = spine::SpineIn {
        pr,
        lp,
        i,
        n,
        d,
        wires: &wires,
        ctx,
        public: &st.public,
        det: &det,
        attack: None,
        lig_dealer: None,
        lig_tape: if det.on() { None } else { Some(lig_s) },
    };
    let mut so = spine::prove(&si, net, &mut sp, carry, None)?;
    for k in spine::MAT {
        wires.remove(k);
    }
    let child: BTreeMap<String, PcsParty> =
        [("W1", "W1n"), ("W2", "W2n")].iter().map(|(c, k)| (c.to_string(), so.coms.remove(*k).unwrap())).collect();
    let spine_coms: BTreeMap<String, PcsParty> =
        middle::SPINE.iter().map(|k| (k.to_string(), so.coms.remove(*k).unwrap())).collect();
    let mi = middle::MiddleIn {
        pr,
        lp,
        i,
        n,
        d,
        atoms: &st.atoms,
        wires: &wires,
        rec: &rec,
        public: &st.public,
        ctx,
        det: &det,
        lig_dealer: None,
        lig_tape: if det.on() { None } else { Some(lig_m) },
        ignore_range: st.ignore_range,
        cst_patch: None,
    };
    let mo = middle::prove(&mi, net, &mut sp, spine_coms, None)?;
    let blob = wire::encode_step(pr, ctx, d, n, true, &so.proof, &st.public, &mo.proof, rec.n_prep(), rec.had.len(), None);
    Ok(StepProof { blob, child, genesis_roots, secs: t0.elapsed().as_secs_f64(), sent: net.sent() - sent0 })
}

/// The (Ta, Tb, Tc) triples of a tape section: `count` triples from entry `from` (None: to the tape's end).
#[cfg(feature = "tcp")]
pub fn tape_triples_at(tape: &darkstep::tape::Tape, from: usize, count: Option<usize>) -> Result<Vec<Triple>, String> {
    use darkstep::tape::Tag;
    let end = match count {
        Some(c) => from + 3 * c,
        None => tape.len(),
    };
    if end > tape.len() {
        return Err("the tape's proof section is shorter than the proof needs".into());
    }
    let mut triples = Vec::with_capacity((end - from) / 3);
    let mut k = from;
    while k < end {
        if k + 3 > end {
            return Err("the tape's proof section ends inside a triple".into());
        }
        let tg = |j: usize| tape.tags[j];
        if (tg(k), tg(k + 1), tg(k + 2)) != (Tag::Ta as u8, Tag::Tb as u8, Tag::Tc as u8) {
            return Err(format!("the tape's proof section is not (Ta, Tb, Tc) triples at entry {k}"));
        }
        let e = |j: usize| (tape.sh[j], tape.mac[j]);
        triples.push((e(k), e(k + 1), e(k + 2)));
        k += 3;
    }
    Ok(triples)
}

/// One custodian's PartyStep from its darkstep step: the ProofRecord, W1n, W2n and the tape's proof section (the
/// (Ta, Tb, Tc) entries after the step's cursor, to the tape's end).
#[cfg(feature = "tcp")]
pub fn from_darkstep(
    i: usize,
    d: usize,
    rec: &darkstep::step::ProofRecord,
    w1n: &[Vec<darkstep::party::Sh>],
    w2n: &[Vec<darkstep::party::Sh>],
    tape: &darkstep::tape::Tape,
    det: Det,
) -> Result<PartyStep, String> {
    from_darkstep_n(i, d, rec, w1n, w2n, tape, None, det)
}

/// from_darkstep with a proof section of exactly `count` triples (a run's tape continues with the next step after
/// it: advance the party's cursor by 3 count).
#[cfg(feature = "tcp")]
#[allow(clippy::too_many_arguments)]
pub fn from_darkstep_n(
    i: usize,
    d: usize,
    rec: &darkstep::step::ProofRecord,
    w1n: &[Vec<darkstep::party::Sh>],
    w2n: &[Vec<darkstep::party::Sh>],
    tape: &darkstep::tape::Tape,
    count: Option<usize>,
    det: Det,
) -> Result<PartyStep, String> {
    let sh = |x: &darkstep::party::Sh| (x.s, x.m);
    let mut wires: BTreeMap<String, Vec<Sh>> = rec.wires.iter().map(|(k, v)| (k.to_string(), v.iter().map(sh).collect())).collect();
    wires.insert("W1n".into(), w1n.iter().flatten().map(sh).collect());
    wires.insert("W2n".into(), w2n.iter().flatten().map(sh).collect());
    let triples = tape_triples_at(tape, rec.tape_cursor, count)?;
    Ok(PartyStep {
        i,
        n: 3,
        d,
        alpha_i: rec.alpha_i,
        wires,
        public: rec.public.clone(),
        atoms: rec.middle_atoms.iter().map(sh).collect(),
        triples,
        det,
        ignore_range: false,
    })
}

/// darkstep's custodian sockets by reference (the step's other tags keep running beside the proof's).
#[cfg(feature = "tcp")]
pub struct TcpRef<'a>(pub &'a darkstep::net::Net);

#[cfg(feature = "tcp")]
impl Net for TcpRef<'_> {
    fn me(&self) -> usize {
        self.0.me
    }
    fn n(&self) -> usize {
        self.0.n
    }
    fn all_gather(&mut self, mine: Vec<u64>) -> Vec<Vec<u64>> {
        self.0.exchange(darkstep::net::PROOF, &mine)
    }
    fn sent(&self) -> u64 {
        self.0.total_sent()[darkstep::net::PROOF as usize] / 8
    }
}

/// One custodian's inputs for the release proof (cosnark_release): its shares of the head's W1, W2 (d * d,
/// row-major), of the release's external vectors z1, h (d M), the public transcript, the release's atoms in creation
/// order, and its tape's release proof section (`release_triples(..)` triples).
pub struct PartyRelease {
    pub i: usize,
    pub n: usize,
    pub d: usize,
    pub alpha_i: u64,
    pub wires: BTreeMap<String, Vec<Sh>>,
    pub public: Vec<u64>,
    pub atoms: Vec<Sh>,
    pub triples: Vec<Triple>,
    /// TEST ONLY (feature test-det), as PartyStep.det
    pub det: Det,
}

/// The release's public policy: X[k][t] at k M + t (mod p), labels, classes, the comparison shift.
pub struct Policy {
    pub x: Vec<u64>,
    pub labels: Vec<usize>,
    pub ncls: usize,
    pub kc: u32,
    /// TEST ONLY: prove even with a truncation input outside its proved bound (a forced bundle)
    pub ignore_range: bool,
}

/// Triples one custodian's tape must hold for the release proof.
pub fn release_triples(lp: &LigParams, n_had: usize) -> usize {
    middle::beaver_count(n_had) + LigParty::tape_triples(lp, middle::LIG_SCALARS, 1)
}

/// The release proof by custodian st.i: ctx = (model, epoch, head step); head: this party's carried commitments of
/// the head's W1, W2 (the last step's StepProof.child). Every party returns the same bytes.
#[allow(clippy::too_many_arguments)]
pub fn prove_release(
    pr: &Profile,
    lp: &LigParams,
    prm: StepParams,
    net: &mut dyn Net,
    ctx: &Ctx,
    pol: &Policy,
    st: PartyRelease,
    head: BTreeMap<String, PcsParty>,
) -> Result<(Vec<u8>, f64), String> {
    let t0 = std::time::Instant::now();
    let (i, n, d) = (st.i, st.n, st.d);
    let m = pol.labels.len();
    if net.me() != i || net.n() != n {
        return Err("transport is for another party or committee size".into());
    }
    let rec = step::replay_release(&st.public, d, m, prm, &pol.x, &pol.labels, pol.ncls, pol.kc)
        .map_err(|e| format!("own transcript: {e:?}"))?;
    if rec.tpos != st.public.len() {
        return Err("own transcript is longer than the release program".into());
    }
    if st.atoms.len() != rec.n_program_atoms() {
        return Err(format!("{} release atoms, the program has {}", st.atoms.len(), rec.n_program_atoms()));
    }
    let det = st.det;
    let nb = rec.range_products() + middle::beaver_count(rec.had.len());
    let lm = if det.on() { 0 } else { LigParty::tape_triples(lp, middle::LIG_SCALARS, 1) };
    if st.triples.len() != nb + lm {
        return Err(format!("the tape's release section has {} triples, the proof needs {}", st.triples.len(), nb + lm));
    }
    let mut tri = st.triples;
    let lig_m: Vec<(u64, u64, u64)> = tri.split_off(nb).into_iter().map(|(a, b, c)| (a.0, b.0, c.0)).collect();
    let mut sp = Spdz::from_tape(i, n, st.alpha_i, tri);
    let mi = middle::MiddleIn {
        pr,
        lp,
        i,
        n,
        d,
        atoms: &st.atoms,
        wires: &st.wires,
        rec: &rec,
        public: &st.public,
        ctx,
        det: &det,
        lig_dealer: None,
        lig_tape: if det.on() { None } else { Some(lig_m) },
        ignore_range: pol.ignore_range,
        cst_patch: None,
    };
    let mo = middle::prove(&mi, net, &mut sp, head, None)?;
    let blob = wire::encode_release(pr, ctx, d, n, m, pol.ncls, &st.public, &mo.proof, &rec);
    Ok((blob, t0.elapsed().as_secs_f64()))
}

/// The release program (cosnark_release.run_release, its batch-friendly order) run by one custodian on darkstep's
/// party, over the release section of its tape: w1, w2 = its shares of the head's weights (d x d). Returns the opened
/// count C and the PartyRelease record (without triples; take them from the tape after the party's cursor:
/// release_triples(lp, n_had)). The MAC check runs before returning.
#[cfg(feature = "tcp")]
pub fn release_mpc(
    pt: &mut darkstep::party::Party,
    w1: &[Vec<darkstep::party::Sh>],
    w2: &[Vec<darkstep::party::Sh>],
    pol: &Policy,
    prm: StepParams,
) -> Result<(u64, PartyRelease), String> {
    use darkstep::party::Sh as DSh;
    use rayon::prelude::*;
    let d = w1.len();
    let m = pol.labels.len();
    let p = pt.p;
    assert_eq!(p, crate::field::p(), "darkstep's field is not darkproof's");
    let (a0, t0) = (pt.atom_log.len(), pt.tr.v.len());
    // z1 = W1 X, local: row j of W1 against column t of X
    let xt: Vec<Vec<u64>> = (0..m).map(|t| (0..d).map(|k| pol.x[k * m + t]).collect()).collect();
    let z1: Vec<DSh> = (0..d)
        .into_par_iter()
        .flat_map_iter(|j| {
            let ws: Vec<u64> = w1[j].iter().map(|x| x.s).collect();
            let wm: Vec<u64> = w1[j].iter().map(|x| x.m).collect();
            let xt = &xt;
            (0..m).map(move |t| DSh { s: crate::field::dot(&ws, &xt[t]), m: crate::field::dot(&wm, &xt[t]) })
        })
        .collect();
    let u1 = pt.trunc_vec(&z1, prm.s1, prm.k1);
    let sig = vec![step::tables_for(prm.t_lo).0];
    let h: Vec<DSh> = pt.lookup_vec(&u1, crate::field::from_i64(-prm.t_lo), &sig, 255).into_iter().map(|v| v[0]).collect();
    drop(u1);
    pt.middle_mul = true;
    let mut xs = Vec::with_capacity(pol.ncls * m * d);
    let mut ys = Vec::with_capacity(pol.ncls * m * d);
    for c in 0..pol.ncls {
        for t in 0..m {
            for k in 0..d {
                xs.push(w2[c][k]);
                ys.push(h[k * m + t]);
            }
        }
    }
    let prods = pt.mul_vec(&xs, &ys);
    drop((xs, ys));
    let sums: Vec<DSh> = prods.chunks(d).map(|ch| ch.iter().fold(DSh { s: 0, m: 0 }, |a, x| pt.add(a, *x))).collect();
    drop(prods);
    let o = pt.trunc_vec(&sums, prm.s1, prm.k1);
    let mut diffs = Vec::with_capacity(m * (pol.ncls - 1));
    for t in 0..m {
        let l = pol.labels[t];
        for k in 0..pol.ncls {
            if k != l {
                diffs.push(pt.lin(&[(1, o[l * m + t]), (p - 1, o[k * m + t])], p - 1));
            }
        }
    }
    let q = pt.trunc_vec(&diffs, pol.kc, pol.kc);
    let f: Vec<DSh> = q.iter().map(|x| pt.cadd(1, *x)).collect();
    let nf = pol.ncls - 1;
    let mut acc: Vec<DSh> = (0..m).map(|t| f[t * nf]).collect();
    for j in 1..nf {
        let ys: Vec<DSh> = (0..m).map(|t| f[t * nf + j]).collect();
        acc = pt.mul_vec(&acc, &ys);
    }
    pt.middle_mul = false;
    let total = acc.iter().fold(DSh { s: 0, m: 0 }, |a, x| pt.add(a, *x));
    let c = pt.open_vec(&[total], darkstep::party::PH_MUL)[0];
    pt.mac_check("release")?;
    let sh = |x: &DSh| (x.s, x.m);
    let mut wires = BTreeMap::new();
    wires.insert("W1".to_string(), w1.iter().flatten().map(sh).collect());
    wires.insert("W2".to_string(), w2.iter().flatten().map(sh).collect());
    wires.insert("z1".to_string(), z1.iter().map(sh).collect());
    wires.insert("h".to_string(), h.iter().map(sh).collect());
    let atoms: Vec<Sh> = pt.atom_log[a0..]
        .iter()
        .flat_map(|r| r.clone().map(|k| (pt.tape.sh[k], pt.tape.mac[k])))
        .collect();
    let st = PartyRelease {
        i: pt.i,
        n: 3,
        d,
        alpha_i: pt.alpha(),
        wires,
        public: pt.tr.v[t0..].to_vec(),
        atoms,
        triples: Vec::new(),
        det: Det::off(),
    };
    Ok((c, st))
}

/// The release section of a TEST dealer's tapes (cosnark_release's order), then its proof section; the run's tapes
/// come from MASCOT in this order.
#[cfg(feature = "tcp")]
pub fn deal_release(dl: &mut darkstep::tape::Dealer, d: usize, m: usize, ncls: usize, prm: StepParams, kc: u32, lp: &LigParams, tables: &(Vec<u64>, Vec<u64>), pol: &Policy) {
    for _ in 0..d * m {
        dl.trunc(prm.s1, prm.k1);
    }
    for _ in 0..d * m {
        dl.lookup(255);
    }
    for _ in 0..ncls * m * d {
        dl.mul();
    }
    for _ in 0..ncls * m {
        dl.trunc(prm.s1, prm.k1);
    }
    for _ in 0..m * (ncls - 1) {
        dl.trunc(kc, kc);
    }
    for _ in 0..m * (ncls - 2) {
        dl.mul();
    }
    let _ = tables;
    for _ in 0..release_section(lp, d, m, prm, pol) {
        dl.mul();
    }
}

/// The release's proof section: release_triples plus the proved bounds' products (prm.rc).
pub fn release_section(lp: &LigParams, d: usize, m: usize, prm: StepParams, pol: &Policy) -> usize {
    let zeros = vec![0u64; wire::release_len(d, m, prm, pol.ncls, pol.kc)];
    let rec = step::replay_release(&zeros, d, m, prm, &pol.x, &pol.labels, pol.ncls, pol.kc).expect("release replay");
    release_triples(lp, rec.had.len()) + rec.range_products()
}

/// Hadamard rows of the release proof (data-independent: a replay on a zero transcript).
pub fn release_n_had(d: usize, m: usize, prm: StepParams, pol: &Policy) -> usize {
    let zeros = vec![0u64; wire::release_len(d, m, prm, pol.ncls, pol.kc)];
    step::replay_release(&zeros, d, m, prm, &pol.x, &pol.labels, pol.ncls, pol.kc).expect("release replay").had.len()
}

/// The plaintext twin of the release (cosnark_release.plain_count): the count over the integers.
pub fn plain_count(w1: &[Vec<i64>], w2: &[Vec<i64>], x: &[Vec<i64>], labels: &[usize], prm: StepParams, ncls: usize, kc: u32) -> u64 {
    let d = w1.len();
    let m = labels.len();
    let sig = |u: i64| (u.div_euclid(4)).clamp(-7, 7);
    let mut c = 0;
    for t in 0..m {
        let h: Vec<i64> = (0..d).map(|j| sig((0..d).map(|k| w1[j][k] * x[k][t]).sum::<i64>() >> prm.s1)).collect();
        let o: Vec<i64> = (0..ncls).map(|cl| (0..d).map(|k| w2[cl][k] * h[k]).sum::<i64>() >> prm.s1).collect();
        let l = labels[t];
        if (0..ncls).filter(|&k| k != l).all(|k| (o[l] - o[k] - 1) >> kc == 0) {
            c += 1;
        }
    }
    c
}
