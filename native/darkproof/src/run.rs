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

/// Triples one custodian's tape must hold in its proof section for one step.
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
    let det = Det(None);
    let carried = prm.carried(ctx.step);
    let rec = step::replay(&st.public, d, prm, tables, carried).map_err(|e| format!("own transcript: {e:?}"))?;
    if rec.tpos != st.public.len() {
        return Err("own transcript is longer than the step program".into());
    }
    if st.atoms.len() != rec.n_prep() {
        return Err(format!("{} middle atoms, the program has {}", st.atoms.len(), rec.n_prep()));
    }
    let nb = spine::beaver_count(d) + middle::beaver_count(rec.had.len());
    let ls = LigParty::tape_triples(lp, spine::LIG_SCALARS, 1);
    let lm = LigParty::tape_triples(lp, middle::LIG_SCALARS, 1);
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
        lig_tape: Some(lig_s),
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
        lig_tape: Some(lig_m),
        cst_patch: None,
    };
    let mo = middle::prove(&mi, net, &mut sp, spine_coms, None)?;
    let blob = wire::encode_step(pr, ctx, d, n, true, &so.proof, &st.public, &mo.proof, rec.n_prep(), rec.had.len(), None);
    Ok(StepProof { blob, child, genesis_roots, secs: t0.elapsed().as_secs_f64(), sent: net.sent() - sent0 })
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
