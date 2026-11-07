//! Per-step proofs in the deployed run: ONE custodian's share of the collaborative proof of one step, over that
//! custodian's own transport. Every party ends with the same bundle bytes (every proof message is broadcast), so each
//! custodian can hand the bundle to the ledger.
//!
//! Inputs come from the custodian's own step (darkstep::step::ProofRecord plus W1n, W2n) and its own preprocessing
//! tape: the proof section holds `tape_triples(..)` authenticated Beaver triples, consumed in this order:
//!   [spine Beaver products: spine::beaver_count_e(d, ext)] [middle Beaver products: middle::beaver_count_e(n_had, ext)]
//!   [spine Ligero: LigParty::tape_triples(lp, spine::lig_scalars(ext), 1)] [middle Ligero: (.., middle::lig_scalars(ext), 1)]
//! with ext = lp.ext, the challenges' field (cosnark_ext; the products' structural lengths set the counts).
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
use crate::{field, Ctx, Profile};
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
    /// DEFER: this step's pending claims (this party's side), for the discharging proof
    pub deferred: Option<crate::defer::DeferIn>,
}

/// Public genesis (StepParams.pg): the public initial weights W1, W2 (d x d, row-major, integers) enter custody as a
/// public constant (custodian 0's share W, the others' 0), committed with PUBLIC coins (PcsParty::commit_public), so
/// every custodian and every verifier computes the same commitments. Returns custodian `i`'s carry (its W1, W2
/// commitments: step 1's parent, at their second life like any carried step's) and every custodian's roots (the
/// genesis record's). Equal shares commit equally, so this is two d^2 commitments whatever n.
pub fn public_genesis(pr: &Profile, d: usize, i: usize, w1: &[i64], w2: &[i64], n: usize) -> (BTreeMap<String, PcsParty>, BTreeMap<String, Vec<Hash>>) {
    let (coms, roots) = public_commit(pr, d, w1, w2, n, Some(i));
    (coms.unwrap(), roots)
}

/// The roots of public_genesis alone (the verifier's side).
pub fn public_genesis_roots(pr: &Profile, d: usize, w1: &[i64], w2: &[i64], n: usize) -> BTreeMap<String, Vec<Hash>> {
    public_commit(pr, d, w1, w2, n, None).1
}

fn public_commit(
    pr: &Profile,
    d: usize,
    w1: &[i64],
    w2: &[i64],
    n: usize,
    me: Option<usize>,
) -> (Option<BTreeMap<String, PcsParty>>, BTreeMap<String, Vec<Hash>>) {
    assert!(w1.len() == d * d && w2.len() == d * d, "public genesis: W must be d x d");
    // DEFER: a W has one life (cosnark_zk.w_pcs)
    let pw = pr.w_life();
    let pr = &pw;
    let zero = PcsParty::commit_public(pr, &vec![0u64; d * d], "zero");
    let mut coms = BTreeMap::new();
    let mut roots = BTreeMap::new();
    for (k, w) in [("W1", w1), ("W2", w2)] {
        let share: Vec<u64> = w.iter().map(|&v| field::from_i64(v)).collect();
        let c0 = if w.iter().all(|&v| v == 0) { zero.clone() } else { PcsParty::commit_public(pr, &share, k) };
        roots.insert(k.to_string(), (0..n).map(|p| if p == 0 { c0.root } else { zero.root }).collect());
        if let Some(i) = me {
            let mut c = if i == 0 { c0 } else { zero.clone() };
            c.label = k.to_string();
            coms.insert(k.to_string(), c);
        }
    }
    (me.map(|_| coms), roots)
}

/// The public initial weights pinned by a darktrain cfg json: (d, W1, W2) = darktrain::init(cfg).
#[cfg(feature = "tcp")]
pub fn public_weights(cfg_json: &[u8]) -> Result<(usize, Vec<i64>, Vec<i64>), String> {
    let c: darktrain::Cfg = serde_json::from_slice(cfg_json).map_err(|e| format!("public genesis cfg: {e}"))?;
    let (w1, w2) = darktrain::init(&c);
    Ok((c.d, w1, w2))
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
    tape_triples(lp, d, rec.had.len()) + rec.proof_products()
}

/// Triples one custodian's tape must hold in its proof section for one step (without proved bounds; with them use
/// step_section).
/// Counts follow the challenges' field (lp.ext): the products' structural lengths (spine::beaver_count_e,
/// middle::beaver_count_e) and the Ligeros' plain products (lig_scalars).
pub fn tape_triples(lp: &LigParams, d: usize, n_had: usize) -> usize {
    spine::beaver_count_e(d, lp.ext)
        + middle::beaver_count_e(n_had, lp.ext)
        + LigParty::tape_triples(lp, spine::lig_scalars(lp.ext), 1)
        + LigParty::tape_triples(lp, middle::lig_scalars(lp.ext), 1)
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
    prove_step_d(pr, lp, tables, prm, net, ctx, st, carry, None)
}

/// DEFER in the deployed run: the discharging proof's input from a carry (StepProof.child, or the carry checkpoint,
/// which holds this party's carries c1p, c2p beside W1, W2) and the ledger replica's pending claims (Ledger.pending:
/// their points). Takes c1p, c2p out of the carry. None when the head is final (pend None); refused when the two
/// disagree (a carry without the ledger's pending claims, or the reverse).
pub fn carry_in(carry: &mut BTreeMap<String, PcsParty>, pend: Option<&crate::defer::Pending>) -> Result<Option<crate::defer::DeferIn>, String> {
    let held = crate::defer::CARRY_IN.iter().filter(|k| carry.contains_key(**k)).count();
    match pend {
        None if held == 0 => Ok(None),
        None => Err("the carry holds a step's carries, but the ledger's head is final (nothing pending)".into()),
        Some(_) if held != 2 => Err("the ledger's head is pending, but the carry does not hold its carries (c1p, c2p)".into()),
        Some(p) => {
            let carries = crate::defer::CARRY_IN.iter().map(|k| (k.to_string(), carry.remove(*k).unwrap())).collect();
            Ok(Some(crate::defer::DeferIn { points: p.points.clone(), carries }))
        }
    }
}

/// prove_step for the deployed run under DEFER: the parent's pending claims from the ledger replica (pend: its
/// Ledger.pending), this party's carries from the carry (carry_in). Without DEFER (pend None) it is prove_step.
#[allow(clippy::too_many_arguments)]
pub fn prove_step_l(
    pr: &Profile,
    lp: &LigParams,
    tables: &(Vec<u64>, Vec<u64>),
    prm: StepParams,
    net: &mut dyn Net,
    ctx: &Ctx,
    st: PartyStep,
    carry: Option<BTreeMap<String, PcsParty>>,
    pend: Option<&crate::defer::Pending>,
) -> Result<StepProof, String> {
    let mut carry = carry;
    let dfr = match carry.as_mut() {
        Some(c) => carry_in(c, pend)?,
        None if pend.is_some() => return Err("the ledger's head is pending, but there is no carry".into()),
        None => None,
    };
    prove_step_d(pr, lp, tables, prm, net, ctx, st, carry, dfr)
}

/// prove_step with DEFER's input: this party's side of the parent's pending claims (StepProof.deferred).
#[allow(clippy::too_many_arguments)]
pub fn prove_step_d(
    pr: &Profile,
    lp: &LigParams,
    tables: &(Vec<u64>, Vec<u64>),
    prm: StepParams,
    net: &mut dyn Net,
    ctx: &Ctx,
    mut st: PartyStep,
    carry: Option<BTreeMap<String, PcsParty>>,
    dfr: Option<crate::defer::DeferIn>,
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
    rec.xt_refusal().map_err(|e| format!("custodians refuse: {e}"))?;
    st.atoms = rec.witness_atoms(&st.atoms).map_err(|e| format!("middle: {e}"))?;
    let nb = spine::beaver_count_e(d, lp.ext) + rec.proof_products() + middle::beaver_count_e(rec.had.len(), lp.ext);
    let (ls, lm) = if det.on() {
        (0, 0)
    } else {
        (LigParty::tape_triples(lp, spine::lig_scalars(lp.ext), 1), LigParty::tape_triples(lp, middle::lig_scalars(lp.ext), 1))
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
        None if prm.pg.is_some() => return Err("public genesis: step 1 takes run::public_genesis's carry".into()),
        None => {
            let g: BTreeMap<String, PcsParty> = ["W1", "W2"]
                .iter()
                .map(|k| {
                    let s: Vec<u64> = wires[*k].iter().map(|x| x.0).collect();
                    // DEFER: a W has one life (cosnark_zk.w_pcs)
                    (k.to_string(), PcsParty::commit(&pr.w_life(), &s, k, i, &det))
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
    let mut so = spine::prove_d(&si, net, &mut sp, carry, None, dfr)?;
    let deferred = so.deferred.take();
    for k in spine::MAT {
        wires.remove(k);
    }
    let mut child: BTreeMap<String, PcsParty> =
        [("W1", "W1n"), ("W2", "W2n")].iter().map(|(c, k)| (c.to_string(), so.coms.remove(*k).unwrap())).collect();
    if let Some(df) = &deferred {
        // DEFER: the carry also holds this step's carries (c1p, c2p), for the discharging proof (carry_in); the
        // points of the pending claims are the ledger's (Ledger.pending)
        for (k, c) in &df.carries {
            child.insert(k.clone(), c.clone());
        }
    }
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
        spent: None,
    };
    let mo = middle::prove(&mi, net, &mut sp, spine_coms, None)?;
    let blob = wire::encode_step(pr, ctx, d, n, true, &so.proof, &st.public, &mo.proof, rec.n_prep(), rec.had.len(), None);
    Ok(StepProof { deferred, blob, child, genesis_roots, secs: t0.elapsed().as_secs_f64(), sent: net.sent() - sent0 })
}

/// tape_triples_at(tape, from, None) for a terminal section: the tape is cut to `from` as the triples are read (from
/// its end, its buffers shrinking every 2^20 triples), so the section and the tape are never both held.
#[cfg(feature = "tcp")]
pub fn take_tape_triples(tape: &mut darkstep::tape::Tape, from: usize) -> Result<Vec<Triple>, String> {
    use darkstep::tape::Tag;
    let end = tape.len();
    if from > end || (end - from) % 3 != 0 {
        return Err("the tape's proof section is not whole triples".into());
    }
    let count = (end - from) / 3;
    let cut = |tape: &mut darkstep::tape::Tape, k: usize| {
        tape.tags.truncate(k);
        tape.sh.truncate(k);
        tape.mac.truncate(k);
        tape.tags.shrink_to_fit();
        tape.sh.shrink_to_fit();
        tape.mac.shrink_to_fit();
    };
    let mut triples = Vec::with_capacity(count);
    let mut k = end;
    while k > from {
        let j = k - 3;
        if (tape.tags[j], tape.tags[j + 1], tape.tags[j + 2]) != (Tag::Ta as u8, Tag::Tb as u8, Tag::Tc as u8) {
            return Err(format!("the tape's proof section is not (Ta, Tb, Tc) triples at entry {j}"));
        }
        let e = |j: usize| (tape.sh[j], tape.mac[j]);
        triples.push((e(j), e(j + 1), e(j + 2)));
        k = j;
        if triples.len() % (1 << 20) == 0 {
            cut(tape, k);
        }
    }
    cut(tape, from);
    triples.reverse();
    Ok(triples)
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
    /// the deployed release: the proof section read from the tape file (then `triples` is empty)
    pub tape_file: Option<ReleaseTape>,
}

/// A release tape file's proof section (darkstep's DLTAPE01: a 24-byte header, n tags, n shares, n MACs), read in
/// order from disk: the release loads only the MPC part of its tape (load_release_tape), and the prover draws the
/// section's triples from here, never holding them (at M = 52: 38.7M triples, 1.9 GB; the tape itself 2.7 GB).
#[derive(Clone, Debug)]
pub struct ReleaseTape {
    path: std::path::PathBuf,
    n: usize,
    from: usize,
    count: usize,
    /// Some: the file is sealed (DLVAULT2) under this key and role; the readers open it block by block
    sealed: Option<(std::sync::Arc<dlvault::Key>, String)>,
}

/// A reader of a release tape file's plaintext at `at`: the file itself, or its DLVAULT2 blocks opened in place.
fn tape_reader(path: &std::path::Path, sealed: &Option<(std::sync::Arc<dlvault::Key>, String)>, at: u64) -> Result<Box<dyn std::io::Read + Send>, String> {
    use std::io::{Seek, SeekFrom};
    let ioe = |e: std::io::Error| format!("{}: {e}", path.display());
    match sealed {
        None => {
            let mut f = std::fs::File::open(path).map_err(ioe)?;
            f.seek(SeekFrom::Start(at)).map_err(ioe)?;
            Ok(Box::new(std::io::BufReader::with_capacity(1 << 20, f)))
        }
        Some((k, role)) => {
            let mut r = dlvault::Reader::open(path, k.clone(), role).map_err(ioe)?;
            r.seek(SeekFrom::Start(at)).map_err(ioe)?;
            Ok(Box::new(std::io::BufReader::with_capacity(1 << 16, r)))
        }
    }
}

impl ReleaseTape {
    pub fn count(&self) -> usize {
        self.count
    }
    /// triples j0 .. j0 + cnt of the section, in order
    pub fn triples(&self, j0: usize, cnt: usize) -> Result<TapeTriples, String> {
        if j0 + cnt > self.count {
            return Err("the release tape's proof section is shorter than asked".into());
        }
        let k = (self.from + 3 * j0) as u64;
        let open = |base: u64| tape_reader(&self.path, &self.sealed, base + 8 * k);
        let n = self.n as u64;
        Ok(TapeTriples { sh: open(24 + n)?, mac: open(24 + 9 * n)?, left: cnt, path: self.path.clone(), read: 0 })
    }
}

/// The reader of ReleaseTape::triples.
pub struct TapeTriples {
    sh: Box<dyn std::io::Read + Send>,
    mac: Box<dyn std::io::Read + Send>,
    left: usize,
    path: std::path::PathBuf,
    read: usize,
}

impl TapeTriples {
    /// the file's pages out of the page cache (it is read once; under a cgroup cap the cache counts as the seat's)
    fn drop_cache(&self) {
        #[cfg(feature = "tcp")]
        darkstep::serve::drop_cache(&self.path);
    }
}

impl Iterator for TapeTriples {
    type Item = Triple;
    fn next(&mut self) -> Option<Triple> {
        use std::io::Read;
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        self.read += 1;
        if self.read % (1 << 20) == 0 || self.left == 0 {
            self.drop_cache();
        }
        let (mut a, mut b) = ([0u8; 24], [0u8; 24]);
        self.sh.read_exact(&mut a).expect("release tape: shares");
        self.mac.read_exact(&mut b).expect("release tape: MACs");
        let w = |x: &[u8; 24], j: usize| u64::from_le_bytes(x[8 * j..8 * j + 8].try_into().unwrap());
        Some(((w(&a, 0), w(&b, 0)), (w(&a, 1), w(&b, 1)), (w(&a, 2), w(&b, 2))))
    }
}

trait ReadSeek: std::io::Read + std::io::Seek + Send {}
impl<T: std::io::Read + std::io::Seek + Send> ReadSeek for T {}

/// Load a release tape file's MPC part (the tape but its last 3 nrt entries; nrt = release_section) and the handle
/// of its proof section, whose tags are checked to be (Ta, Tb, Tc) triples. Reads the file once, sequentially.
/// A plain DLTAPE01 file (tests); the deployment's tape is sealed: load_release_tape_sealed.
#[cfg(feature = "tcp")]
pub fn load_release_tape(path: &std::path::Path, nrt: usize) -> Result<(darkstep::tape::Tape, ReleaseTape), String> {
    if dlvault::is_sealed(path) {
        return Err(format!("{}: a sealed tape (DLVAULT2); it needs its file key (load_release_tape_sealed)", path.display()));
    }
    load_release_tape_src(path, nrt, None)
}

/// load_release_tape for a sealed release tape (DLVAULT2 under the seat's epoch file key `key`, role `role`): the
/// MPC part is decrypted block by block as it is read, the proof section's readers open their own blocks. A plain
/// file is refused (tapes at rest are sealed).
#[cfg(feature = "tcp")]
pub fn load_release_tape_sealed(path: &std::path::Path, nrt: usize, key: std::sync::Arc<dlvault::Key>, role: &str) -> Result<(darkstep::tape::Tape, ReleaseTape), String> {
    if !dlvault::is_sealed(path) {
        return Err(format!("{}: not sealed (DLVAULT2); tapes at rest must be sealed", path.display()));
    }
    load_release_tape_src(path, nrt, Some((key, role.to_string())))
}

#[cfg(feature = "tcp")]
fn load_release_tape_src(path: &std::path::Path, nrt: usize, sealed: Option<(std::sync::Arc<dlvault::Key>, String)>) -> Result<(darkstep::tape::Tape, ReleaseTape), String> {
    use darkstep::tape::Tag;
    use std::io::{Read, Seek, SeekFrom};
    let ioe = |e: std::io::Error| format!("{}: {e}", path.display());
    let (mut f, len): (Box<dyn ReadSeek>, u64) = match &sealed {
        None => {
            let file = std::fs::File::open(path).map_err(ioe)?;
            let len = file.metadata().map_err(ioe)?.len();
            (Box::new(std::io::BufReader::with_capacity(1 << 20, file)), len)
        }
        Some((k, role)) => {
            let r = dlvault::Reader::open(path, k.clone(), role).map_err(ioe)?;
            let len = r.len();
            (Box::new(std::io::BufReader::with_capacity(1 << 20, r)), len)
        }
    };
    let mut hdr = [0u8; 24];
    f.read_exact(&mut hdr).map_err(ioe)?;
    if &hdr[..8] != b"DLTAPE01" {
        return Err(format!("{}: not a tape", path.display()));
    }
    let alpha_i = u64::from_le_bytes(hdr[8..16].try_into().unwrap());
    let n = u64::from_le_bytes(hdr[16..24].try_into().unwrap()) as usize;
    if len != (24 + 17 * n) as u64 {
        return Err(format!("{}: {len} bytes, a tape of {n} entries has {}", path.display(), 24 + 17 * n));
    }
    if 3 * nrt > n {
        return Err(format!("{}: the tape has {n} entries, the release's proof section alone {}", path.display(), 3 * nrt));
    }
    let k = n - 3 * nrt;
    let mut tags = vec![0u8; n];
    f.read_exact(&mut tags).map_err(ioe)?;
    if let Some(j) = (k..n).step_by(3).find(|&j| (tags[j], tags[j + 1], tags[j + 2]) != (Tag::Ta as u8, Tag::Tb as u8, Tag::Tc as u8)) {
        return Err(format!("{}: the release's proof section is not (Ta, Tb, Tc) triples at entry {j}", path.display()));
    }
    tags.truncate(k);
    tags.shrink_to_fit();
    let mut words = |f: &mut Box<dyn ReadSeek>| -> Result<Vec<u64>, String> {
        let mut b = vec![0u8; 8 * k];
        f.read_exact(&mut b).map_err(ioe)?;
        Ok(b.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect())
    };
    let sh = words(&mut f)?;
    f.seek(SeekFrom::Start((24 + 9 * n) as u64)).map_err(ioe)?;
    let mac = words(&mut f)?;
    drop(f);
    darkstep::serve::drop_cache(path);
    Ok((darkstep::tape::Tape { alpha_i, tags, sh, mac }, ReleaseTape { path: path.to_path_buf(), n, from: k, count: nrt, sealed }))
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
    middle::beaver_count_e(n_had, lp.ext) + LigParty::tape_triples(lp, middle::lig_scalars(lp.ext), 1)
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
    prove_release_d(pr, lp, prm, net, ctx, pol, st, head, None)
}

/// prove_release with DEFER: dfr = this party's side of the head step's pending claims, discharged by the release.
#[allow(clippy::too_many_arguments)]
pub fn prove_release_d(
    pr: &Profile,
    lp: &LigParams,
    prm: StepParams,
    net: &mut dyn Net,
    ctx: &Ctx,
    pol: &Policy,
    mut st: PartyRelease,
    head: BTreeMap<String, PcsParty>,
    dfr: Option<crate::defer::DeferIn>,
) -> Result<(Vec<u8>, f64), String> {
    let t0 = std::time::Instant::now();
    let (i, n, d) = (st.i, st.n, st.d);
    let m = pol.labels.len();
    if net.me() != i || net.n() != n {
        return Err("transport is for another party or committee size".into());
    }
    let mut tt = crate::Trace::new("release", i);
    let mut rec = step::replay_release(&st.public, d, m, prm, &pol.x, &pol.labels, pol.ncls, pol.kc)
        .map_err(|e| format!("own transcript: {e:?}"))?;
    rec.xt_refusal().map_err(|e| format!("custodians refuse: {e}"))?;
    tt.lap("replay of the release program");
    if rec.tpos != st.public.len() {
        return Err("own transcript is longer than the release program".into());
    }
    st.atoms = rec.witness_atoms(&st.atoms).map_err(|e| format!("release: {e}"))?;
    let det = st.det;
    let nb = rec.proof_products() + middle::beaver_count_e(rec.had.len(), lp.ext);
    let lm = if det.on() { 0 } else { LigParty::tape_triples(lp, middle::lig_scalars(lp.ext), 1) };
    let have = st.tape_file.as_ref().map_or(st.triples.len(), |t| t.count());
    if have != nb + lm {
        return Err(format!("the tape's release section has {have} triples, the proof needs {}", nb + lm));
    }
    let shares = |t: Vec<Triple>| -> Vec<(u64, u64, u64)> { t.into_iter().map(|(a, b, c)| (a.0, b.0, c.0)).collect() };
    let (lig_m, mut sp) = match st.tape_file.take() {
        Some(tf) => (shares(tf.triples(nb, lm)?.collect()), Spdz::from_iter(i, n, st.alpha_i, Box::new(tf.triples(0, nb)?))),
        None => {
            let mut tri = std::mem::take(&mut st.triples);
            (shares(tri.split_off(nb)), Spdz::from_tape(i, n, st.alpha_i, tri))
        }
    };
    // the constraint list and the atoms go to the middle by value, which frees them once spent
    let spent = middle::Spent {
        cons: std::sync::Mutex::new(Some(std::mem::take(&mut rec.cons))),
        atoms: std::sync::Mutex::new(Some(std::mem::take(&mut st.atoms))),
        range_rows: std::sync::Mutex::new(Some(std::mem::take(&mut rec.range_rows))),
        lb_rows: std::sync::Mutex::new(Some(std::mem::take(&mut rec.lb_rows))),
    };
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
        spent: Some(&spent),
    };
    let mo = middle::prove_d(&mi, net, &mut sp, head, None, dfr)?;
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
    let (tb, tv) = (pt.cur, pt.tr.v.len());
    let u1 = pt.trunc_vec(&z1, prm.s1, prm.k1);
    let h: Vec<DSh> = if prm.rs && prm.lb {
        lookup_bits(pt, tb, tv, d * m, prm)
    } else {
        let sig = vec![step::tables_for(prm.t_lo).0];
        pt.lookup_vec(&u1, crate::field::from_i64(-prm.t_lo), &sig, 255).into_iter().map(|v| v[0]).collect()
    };
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
        tape_file: None,
    };
    Ok((c, st))
}

/// One custodian's release, as the run's party binary calls it after its last step: what it opened, the bundle, and
/// what it cost.
pub struct ReleaseOut {
    /// the opened count C (the only value that leaves custody)
    pub c: u64,
    /// the release bundle (wire::encode_release); every custodian holds the same bytes
    pub blob: Vec<u8>,
    /// proof-section triples consumed from the tape (release_section)
    pub triples: usize,
    pub mpc_secs: f64,
    pub prove_secs: f64,
    /// this custodian's own check of the bundle against the head roots (0 when no roots were given)
    pub verify_secs: f64,
    /// field elements this custodian sent on tag PROOF during the release proof
    pub sent: u64,
}

/// The release hook of a custodian process: release_mpc over the party's tape from its cursor (the release
/// program's preprocessing, then its proof section of release_section(..) triples), prove_release over the party's
/// own Net (tag PROOF), the cursor moved past both, and, with `head_roots` (the head's W1, W2 roots: the last
/// accepted step's child roots), the bundle checked as the ledger checks it. ctx = (model, epoch, head step);
/// head = this party's carried commitments of the head's weights (the last StepProof.child); w1, w2 = its shares of
/// the head's weights (d x d). Every custodian must call it with the same policy.
#[cfg(feature = "tcp")]
#[allow(clippy::too_many_arguments)]
pub fn release_custodian(
    pr: &Profile,
    lp: &LigParams,
    prm: StepParams,
    pt: &mut darkstep::party::Party,
    w1: &[Vec<darkstep::party::Sh>],
    w2: &[Vec<darkstep::party::Sh>],
    pol: &Policy,
    ctx: &Ctx,
    head: BTreeMap<String, PcsParty>,
    head_roots: Option<&BTreeMap<String, Vec<Hash>>>,
) -> Result<ReleaseOut, String> {
    release_custodian_l(pr, lp, prm, pt, w1, w2, pol, ctx, head, head_roots, None)
}

/// release_custodian under DEFER: pend = the ledger replica's pending claims of the head (Ledger.pending), discharged
/// by the release; head = the carry (W1, W2 and, when pending, this party's carries c1p, c2p).
#[cfg(feature = "tcp")]
#[allow(clippy::too_many_arguments)]
pub fn release_custodian_l(
    pr: &Profile,
    lp: &LigParams,
    prm: StepParams,
    pt: &mut darkstep::party::Party,
    w1: &[Vec<darkstep::party::Sh>],
    w2: &[Vec<darkstep::party::Sh>],
    pol: &Policy,
    ctx: &Ctx,
    head: BTreeMap<String, PcsParty>,
    head_roots: Option<&BTreeMap<String, Vec<Hash>>>,
    pend: Option<&crate::defer::Pending>,
) -> Result<ReleaseOut, String> {
    release_custodian_src(pr, lp, prm, pt, w1, w2, pol, ctx, head, head_roots, pend, None)
}

/// release_custodian_l with the proof section streamed from the tape file: pt.tape holds only the MPC part
/// (load_release_tape), which the MPC must consume exactly.
#[cfg(feature = "tcp")]
#[allow(clippy::too_many_arguments)]
pub fn release_custodian_src(
    pr: &Profile,
    lp: &LigParams,
    prm: StepParams,
    pt: &mut darkstep::party::Party,
    w1: &[Vec<darkstep::party::Sh>],
    w2: &[Vec<darkstep::party::Sh>],
    pol: &Policy,
    ctx: &Ctx,
    mut head: BTreeMap<String, PcsParty>,
    head_roots: Option<&BTreeMap<String, Vec<Hash>>>,
    pend: Option<&crate::defer::Pending>,
    tape_file: Option<ReleaseTape>,
) -> Result<ReleaseOut, String> {
    let dfr = carry_in(&mut head, pend)?;
    let d = w1.len();
    let m = pol.labels.len();
    if pol.x.len() != d * m || w2.len() != d || pol.ncls > d {
        return Err("release: the policy's shape is not the weights'".into());
    }
    let mut tt = crate::Trace::new("release", pt.i);
    tt.lap("start");
    let t0 = std::time::Instant::now();
    let (c, mut st) = release_mpc(pt, w1, w2, pol, prm)?;
    let mpc_secs = t0.elapsed().as_secs_f64();
    // the party's MAC log (every opening of its life; release_mpc's MAC check covered it) is not read again: the
    // release is terminal
    let olog = pt.open_log.capacity() * std::mem::size_of::<(u64, u64)>();
    pt.open_log = Vec::new();
    tt.lap(&format!("MPC (its MAC log freed: {:.2} GB; the party transcript kept: {:.2} GB)", olog as f64 / 1e9, (pt.tr.v.capacity() * 8) as f64 / 1e9));
    // the release is terminal: its proof section is the rest of the tape (prove_release refuses a count that is not
    // the proof's), taken from the tape's end as the tape shrinks, and the rest of the tape freed before proving. The
    // count is not recomputed here: release_section replays the program (at M = 52 a transient Rec of about 7 GB).
    let nrt = match tape_file {
        Some(tf) => {
            if pt.cur != pt.tape.len() {
                return Err(format!("the release tape's MPC part has {} entries, the MPC used {}", pt.tape.len(), pt.cur));
            }
            let c = tf.count();
            st.tape_file = Some(tf);
            c
        }
        None => {
            st.triples = take_tape_triples(&mut pt.tape, pt.cur)?;
            st.triples.len()
        }
    };
    let cur_after = pt.cur + 3 * nrt;
    pt.tape = darkstep::tape::Tape { alpha_i: pt.tape.alpha_i, ..Default::default() };
    pt.atom_log = Vec::new();
    tt.lap("proof section taken, tape freed");
    let mut net = TcpRef(&pt.net);
    let sent0 = net.sent();
    let (blob, prove_secs) = prove_release_d(pr, lp, prm, &mut net, ctx, pol, st, head, dfr)?;
    let sent = net.sent() - sent0;
    pt.cur = cur_after;
    let mut verify_secs = 0.0;
    if let Some(roots) = head_roots {
        let tv = std::time::Instant::now();
        let (_, cv) = wire::verify_release_d(pr, lp, &blob, ctx, roots, &pol.x, &pol.labels, prm, pol.ncls, d, pol.kc, pend)?;
        verify_secs = tv.elapsed().as_secs_f64();
        if cv != c {
            return Err(format!("release: the bundle's count {cv} is not the opened {c}"));
        }
    }
    Ok(ReleaseOut { c, blob, triples: nrt, mpc_secs, prove_secs, verify_secs, sent })
}

/// A halted run's closing proof (cut E), one custodian's side.
pub struct CloseOut {
    /// wire::encode_close: every custodian holds the same bytes; Ledger::close accepts them
    pub blob: Vec<u8>,
    pub secs: f64,
    /// field elements this party sent during the proof
    pub sent: u64,
}

/// The closing proof of the ledger head over any transport: ctx = (model, epoch, head step), head = this party's
/// carry (W1, W2 and its carries c1p, c2p), pend = the ledger replica's pending claims (Ledger.pending). No MPC
/// product and no tape: the head's W are opened at the last step's points against the carries.
#[allow(clippy::too_many_arguments)]
pub fn close_party(
    pr: &Profile,
    lp: &LigParams,
    i: usize,
    n: usize,
    net: &mut dyn Net,
    ctx: &Ctx,
    mut head: BTreeMap<String, PcsParty>,
    pend: &crate::defer::Pending,
    d: usize,
    det: &Det,
) -> Result<CloseOut, String> {
    if !pr.defer {
        return Err("a closing proof exists only under DEFER".into());
    }
    if net.me() != i || net.n() != n {
        return Err("transport is for another party or committee size".into());
    }
    let t0 = std::time::Instant::now();
    let sent0 = net.sent();
    let dfr = carry_in(&mut head, Some(pend))?.unwrap();
    let p = crate::defer::prove_close(pr, lp, i, n, net, ctx, &head, &dfr, det)?;
    let blob = wire::encode_close(pr, ctx, d, n, &p);
    Ok(CloseOut { blob, secs: t0.elapsed().as_secs_f64(), sent: net.sent() - sent0 })
}

/// close_party for the deployed run: darkstep's net (tag PROOF), secret coins. The caller then calls
/// Ledger::close(lp, &out.blob) on its replica (every custodian accepts the same bytes).
#[cfg(feature = "tcp")]
#[allow(clippy::too_many_arguments)]
pub fn close_custodian(
    pr: &Profile,
    lp: &LigParams,
    net: &darkstep::net::Net,
    i: usize,
    n: usize,
    ctx: &Ctx,
    head: BTreeMap<String, PcsParty>,
    pend: &crate::defer::Pending,
    d: usize,
) -> Result<CloseOut, String> {
    close_party(pr, lp, i, n, &mut TcpRef(net), ctx, head, pend, d, &Det::off())
}

/// The gen 6 release policy (train lane, train_eval.py): the first `m` official test images (t10k 0..m-1, public, with
/// their labels), encoded by the run's own encoder (the cfg's, with the training split's means), 10 classes (one W2
/// row each: reps = 1), comparison shift kc = 10.
#[cfg(feature = "tcp")]
pub fn mnist_policy(cfg_json: &[u8], mnist_dir: &std::path::Path, m: usize) -> Result<Policy, String> {
    let c: darktrain::Cfg = serde_json::from_slice(cfg_json).map_err(|e| format!("release policy cfg: {e}"))?;
    c.validate()?;
    if c.nout() != 10 {
        return Err("release policy: one W2 row per class (reps = 1)".into());
    }
    let mn = darktrain::data::load(mnist_dir)?;
    if m == 0 || m > mn.test.n {
        return Err(format!("release policy: M = {m} test images, the split has {}", mn.test.n));
    }
    let c = c.with_means(&mn);
    let xs: Vec<Vec<i64>> = (0..m).map(|t| darktrain::encode(&c, mn.test.image(t), mn.test.lab[t]).0).collect();
    let x = (0..c.d).flat_map(|k| xs.iter().map(move |xt| crate::field::from_i64(xt[k]))).collect();
    let labels = (0..m).map(|t| mn.test.lab[t] as usize).collect();
    Ok(Policy { x, labels, ncls: 10, kc: 10, ignore_range: false })
}

#[cfg(feature = "tcp")]
/// L (proof.md 23; cosnark_gates.RecEngine.lookup_bits): h = SIG[u1] for the n z1 truncations just run (their tape
/// block at `tb`, their transcript at `tv`), by z1's borrow chain to bit B = s1 + 8 and the LB circuit on shares, every
/// product a Beaver product outside the proof (not logged as middle atoms). Opens only Beaver differences.
fn lookup_bits(pt: &mut darkstep::party::Party, tb: usize, tv: usize, n: usize, prm: StepParams) -> Vec<darkstep::party::Sh> {
    use darkstep::party::Sh as DSh;
    let p = pt.p;
    let (s, kk) = (prm.s1 as usize, prm.k1);
    let b = s + 8;
    let trhb = darkstep::tape::Tag::Trhb as u8;
    let mut nb = 0;
    while pt.tape.tags.get(tb + 2 + s + nb) == Some(&trhb) {
        nb += 1;
    }
    assert!(s + nb >= b, "L: the tape carries {nb} rhi bits, fewer than B - s");
    let per = 2 + s + nb + 6 * (s - 1);
    let ent = 1 + 4 * (s - 1);
    let l = (kk + darkstep::tape::KAPPA + 1) as u32;
    let lo = (1i128 << kk) + ((prm.t_lo as i128) << s);
    let sh = |pt: &darkstep::party::Party, x: usize| DSh { s: pt.tape.sh[x], m: pt.tape.mac[x] };
    let r: Vec<Vec<DSh>> = (0..n)
        .map(|k| (0..b).map(|i| sh(pt, tb + k * per + if i < s { 1 + i } else { 2 + i })).collect())
        .collect();
    let cb: Vec<Vec<u64>> = (0..n)
        .map(|k| {
            let cp = (pt.tr.v[tv + k * ent] as i128 - lo).rem_euclid(1i128 << l);
            (0..b).map(|i| ((cp >> i) & 1) as u64).collect()
        })
        .collect();
    let zero = DSh { s: 0, m: 0 };
    let mut beta: Vec<Vec<DSh>> = vec![vec![zero]; n];
    for i in 0..b {
        let t = if i > 0 {
            let xs: Vec<DSh> = (0..n).map(|k| r[k][i]).collect();
            let ys: Vec<DSh> = (0..n).map(|k| beta[k][i]).collect();
            pt.mul_vec(&xs, &ys)
        } else {
            Vec::new()
        };
        for k in 0..n {
            let nbv = match (cb[k][i], i) {
                (1, 0) => zero,
                (1, _) => t[k],
                (_, 0) => pt.lin(&[(1, r[k][i])], 0),
                _ => pt.lin(&[(1, r[k][i]), (1, beta[k][i]), (p - 1, t[k])], 0),
            };
            beta[k].push(nbv);
        }
    }
    let (ops, vph, (hf, hc)) = step::lookup_bits_ops(prm.t_lo);
    let na = ops.iter().map(|o| match o {
        step::LbOp::Lin(a, ..) | step::LbOp::Mul(a, ..) => *a as usize + 1,
    }).max().unwrap_or(0).max(vph.len());
    let mut lvl = vec![0u32; na];
    for op in &ops {
        match op {
            step::LbOp::Lin(a, f, _) => lvl[*a as usize] = f.iter().map(|&(y, _)| lvl[y as usize]).max().unwrap_or(0),
            step::LbOp::Mul(a, x, y) => lvl[*a as usize] = lvl[*x as usize].max(lvl[*y as usize]) + 1,
        }
    }
    let top = lvl.iter().copied().max().unwrap_or(0);
    let mut val: Vec<Vec<DSh>> = (0..n)
        .map(|k| {
            let mut v = vec![zero; na];
            for (j, &ph) in vph.iter().enumerate() {
                let i = s + j;
                v[ph as usize] = pt.lin(&[(p - 1, r[k][i]), (p - 1, beta[k][i]), (2, beta[k][i + 1])], cb[k][i]);
            }
            v
        })
        .collect();
    for lv in 0..=top {
        for vk in val.iter_mut() {
            for op in &ops {
                if let step::LbOp::Lin(a, f, c) = op {
                    if lvl[*a as usize] == lv {
                        let terms: Vec<(u64, DSh)> = f.iter().map(|&(y, co)| (co, vk[y as usize])).collect();
                        vk[*a as usize] = pt.lin(&terms, *c);
                    }
                }
            }
        }
        let mut xs = Vec::new();
        let mut ys = Vec::new();
        let mut at = Vec::new();
        for (k, vk) in val.iter().enumerate() {
            for op in &ops {
                if let step::LbOp::Mul(a, x, y) = op {
                    if lvl[*a as usize] == lv + 1 {
                        xs.push(vk[*x as usize]);
                        ys.push(vk[*y as usize]);
                        at.push((k, *a as usize));
                    }
                }
            }
        }
        if !xs.is_empty() {
            for ((k, a), pr) in at.into_iter().zip(pt.mul_vec(&xs, &ys)) {
                val[k][a] = pr;
            }
        }
    }
    val.iter()
        .map(|vk| {
            let terms: Vec<(u64, DSh)> = hf.iter().map(|&(y, co)| (co, vk[y as usize])).collect();
            pt.lin(&terms, hc)
        })
        .collect()
}

/// The release section of a TEST dealer's tapes (cosnark_release's order), then its proof section; the run's tapes
/// come from MASCOT in this order.
#[cfg(feature = "tcp")]
pub fn deal_release(dl: &mut darkstep::tape::Dealer, d: usize, m: usize, ncls: usize, prm: StepParams, kc: u32, lp: &LigParams, tables: &(Vec<u64>, Vec<u64>), pol: &Policy) {
    for _ in 0..d * m {
        dl.trunc(prm.s1, prm.k1);
    }
    if prm.rs && prm.lb {
        // L: Beaver triples for the lookups by bits (their order on the tape is the products' order; all alike)
        for _ in 0..d * m * step::lookup_bits_products(prm) {
            dl.mul();
        }
    } else {
        for _ in 0..d * m {
            dl.lookup(255);
        }
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
    release_triples(lp, rec.had.len()) + rec.proof_products()
}

/// Hadamard rows of the release proof (data-independent: a replay on a zero transcript).
pub fn release_n_had(d: usize, m: usize, prm: StepParams, pol: &Policy) -> usize {
    let zeros = vec![0u64; wire::release_len(d, m, prm, pol.ncls, pol.kc)];
    step::replay_release(&zeros, d, m, prm, &pol.x, &pol.labels, pol.ncls, pol.kc).expect("release replay").had.len()
}

/// The release's truncation inputs over the integers (the plaintext twin, as plain_count) against the program's proved
/// intervals (StepParams::bound): per truncation (z1 = W1 x, score = W2 h, compare = o_l - o_k - 1), its name,
/// the least and greatest input, the interval [a, a + 2^B) and how many inputs fall outside it.
pub fn plain_bounds(w1: &[Vec<i64>], w2: &[Vec<i64>], x: &[Vec<i64>], labels: &[usize], prm: StepParams, ncls: usize, kc: u32) -> Vec<(&'static str, i64, i64, i64, u32, usize)> {
    let d = w1.len();
    let m = labels.len();
    let sig = |u: i64| (u.div_euclid(4)).clamp(-7, 7);
    let mut acc: Vec<(&'static str, Vec<i64>)> = vec![("z1", vec![]), ("score", vec![]), ("compare", vec![])];
    for t in 0..m {
        let z: Vec<i64> = (0..d).map(|j| (0..d).map(|k| w1[j][k] * x[k][t]).sum::<i64>()).collect();
        let h: Vec<i64> = z.iter().map(|&v| sig(v >> prm.s1)).collect();
        let sc: Vec<i64> = (0..ncls).map(|cl| (0..d).map(|k| w2[cl][k] * h[k]).sum::<i64>()).collect();
        let o: Vec<i64> = sc.iter().map(|&v| v >> prm.s1).collect();
        let l = labels[t];
        acc[0].1.extend(z);
        acc[1].1.extend(sc);
        acc[2].1.extend((0..ncls).filter(|&k| k != l).map(|k| o[l] - o[k] - 1));
    }
    acc.into_iter()
        .map(|(nm, v)| {
            let (a, b) = prm.bound(nm, kc);
            let out = v.iter().filter(|&&u| u < a || u >= a + (1i64 << b)).count();
            (nm, *v.iter().min().unwrap(), *v.iter().max().unwrap(), a, b, out)
        })
        .collect()
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
