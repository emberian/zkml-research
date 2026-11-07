//! The recipient's ZKPoPK gate (decision doc §20.2, §21.1) for the HE helpers: keys from the ceremony
//! (a_j = public_a(seed/j), registered with key proofs), one batched Ligero proof per (sender, HE call) sent with the
//! ciphertexts on HE_CT, and every recipient verifying before any ptxct. A refusal anywhere aborts the step for all
//! three custodians with the same reason (the verdicts are exchanged on CTRL). Reference: native_ref_gated.py.
use crate::bfv::Ct;
use crate::net::{self, Net};
use crate::rns::Rns;
use dzkpopk::ceremony::{Ceremony, Custodian};
use dzkpopk::{BigPoly, Json, KeyRegistry, Kind, ProveOpts, SkCt, Statement, Witness};
use std::sync::Arc;
use std::time::Instant;

pub const EPOCH: i64 = 1;

/// Custodians that share one process (`darkstep local`) take turns proving and verifying: three 64-ciphertext
/// provers at once need about 3 x 3 GB next to the step's own memory, more than a 12 GB job may use. Each custodian
/// of a deployment is its own process, where this lock is uncontended. The time spent waiting is reported apart.
static ZK_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

pub struct Gate {
    /// every custodian's registered key (from this custodian's own view of the ceremony)
    pub regs: Vec<Arc<KeyRegistry>>,
    pub s: Vec<i64>,
    pub e_pk: Vec<i64>,
    pub tcols: usize,
    pub det_seed: Option<String>,
    pub ceremony_s: f64,
    pub prove_s: f64,
    pub verify_s: f64,
    /// waiting for the in-process ZK lock (co-located custodians only)
    pub wait_s: f64,
    /// the low-memory prover (re-encodes rows instead of keeping them): for custodians sharing one machine
    pub low_memory: bool,
    pub proof_bytes_sent: u64,
    /// (label, sha256 of my proof) per call, and (label, sender, statement digest) per verified batch
    pub proofs: Vec<(String, String)>,
}

/// The batch label the statement's context binds: the HE call (kind, number, transpose) and its sender.
pub fn context(kind: &str, call: u64, transpose: bool, sender: usize) -> Json {
    Json::list(vec![
        Json::s("dl-he-batch"),
        Json::s("model"),
        Json::i(0),
        Json::i(0),
        Json::s(kind),
        Json::i(call as i64),
        Json::i(transpose as i64),
        Json::i(sender as i64),
    ])
}

pub fn label(kind: &str, call: u64, transpose: bool, sender: usize) -> String {
    format!("{kind}-{call}-{}-{sender}", transpose as u8)
}

fn limb_major_to_big(rns: &Rns, v: &[u64]) -> BigPoly {
    let n = rns.n;
    let res: Vec<Vec<u64>> = (0..rns.l()).map(|k| v[k * n..(k + 1) * n].to_vec()).collect();
    BigPoly::from_rns(&res, &rns.qs)
}

pub fn statement(rns: &Rns, reg: &Arc<KeyRegistry>, cts: &[Ct], slots: &[usize], ctx: Json) -> Result<Statement, String> {
    let bc: Vec<(BigPoly, BigPoly)> = cts.iter().map(|c| (limb_major_to_big(rns, &c.c0), limb_major_to_big(rns, &c.c1))).collect();
    Statement::new(reg.clone(), Kind::Sk, bc, vec![slots.to_vec(); cts.len()], ctx)
}

/// r at the slots: the unique r in [-(t-1)/2, (t-1)/2] with r = -Q m (mod t) (= t round(Q m_c / t) - Q m_c).
pub fn witness_r(rns: &Rns, m: &[u64], slots: &[usize]) -> Vec<i64> {
    let t = rns.t;
    let qt = (&rns.q_big % t).to_u64_digits().first().copied().unwrap_or(0);
    slots
        .iter()
        .map(|&k| {
            let x = ((t as u128 - (qt as u128 * m[k] as u128) % t as u128) % t as u128) as u64;
            if x > t / 2 {
                x as i64 - t as i64
            } else {
                x as i64
            }
        })
        .collect()
}

impl Gate {
    /// Prove my batch for this call (`forge`: the falsifier's cheat path, which skips the prover's own checks).
    pub fn prove(&mut self, rns: &Rns, me: usize, cts: &[Ct], ws: Vec<SkCt>, slots: &[usize], ctx: Json, lbl: &str, forge: bool) -> Result<Vec<u8>, String> {
        let tw = Instant::now();
        let _g = ZK_LOCK.lock().unwrap();
        self.wait_s += tw.elapsed().as_secs_f64();
        let t0 = Instant::now();
        let st = statement(rns, &self.regs[me], cts, slots, ctx)?;
        let wit = Witness::Sk { s: self.s.clone(), e_pk: self.e_pk.clone(), cts: ws };
        let mut opts = ProveOpts { low_memory: self.low_memory, ..Default::default() };
        #[cfg(feature = "test-det")]
        {
            opts.det_seed = self.det_seed.clone();
        }
        if forge {
            opts.cheat = Some(dzkpopk::Cheat::default());
        }
        let blob = dzkpopk::prove_with(&st, &wit, self.tcols, &mut opts)?;
        self.prove_s += t0.elapsed().as_secs_f64();
        self.proof_bytes_sent += 2 * blob.len() as u64;
        self.proofs.push((lbl.to_string(), pycompat::repr::sha256_hex(&blob)));
        Ok(blob)
    }

    /// Verify sender j's batch against the statement I build from MY expected context and j's registered key.
    pub fn verify(&mut self, rns: &Rns, j: usize, cts: &[Ct], slots: &[usize], ctx: Json, proof: &[u8]) -> Result<(), String> {
        let tw = Instant::now();
        let _g = ZK_LOCK.lock().unwrap();
        self.wait_s += tw.elapsed().as_secs_f64();
        let t0 = Instant::now();
        let st = statement(rns, &self.regs[j], cts, slots, ctx)?;
        let r = dzkpopk::verify(&st, proof, self.tcols);
        self.verify_s += t0.elapsed().as_secs_f64();
        r
    }
}

/// The verdict exchange: every custodian posts its refusals [(recipient, sender, reason)]; all abort on the first
/// refusal in (sender, recipient) order, so the three report the same reason.
pub fn agree(net: &Net, me: usize, mine: &[(usize, String)], what: &str) -> Result<(), String> {
    let enc = serde_json::to_vec(&mine.iter().map(|(j, r)| serde_json::json!([j, r])).collect::<Vec<_>>()).unwrap();
    let all = net.exchange_bytes(net::CTRL, &enc);
    let mut refusals: Vec<(usize, usize, String)> = vec![];
    for (i, b) in all.iter().enumerate() {
        let v: Vec<(usize, String)> = if i == me {
            mine.to_vec()
        } else {
            serde_json::from_slice::<Vec<(usize, String)>>(b).map_err(|e| format!("ZKPoPK gate: malformed verdict from custodian {i}: {e}"))?
        };
        for (j, r) in v {
            refusals.push((j, i, r));
        }
    }
    refusals.sort();
    match refusals.first() {
        None => Ok(()),
        Some((j, i, r)) => Err(format!("ZKPoPK gate: custodian {i} refused custodian {j}'s batch ({what}): {r}")),
    }
}

// ------------------------------------------------------------------------------------------- the ceremony, networked
fn poly_bytes(p: &BigPoly) -> Vec<u8> {
    let mut v = vec![p.nl() as u64];
    v.extend_from_slice(p.data());
    crate::net::u64s_to_bytes(&v)
}

fn poly_parse(b: &[u8]) -> Result<BigPoly, String> {
    let v = crate::net::bytes_to_u64s(b);
    if v.is_empty() {
        return Err("empty key".into());
    }
    BigPoly::from_limbs(v[0] as usize, v[1..].to_vec())
}

/// keygen_ceremony.run_ceremony over the custodians' mesh: commit, reveal, key + key proof, register every key.
/// Returns (my custodian, the ceremony with all three keys registered).
pub fn ceremony(net: &Net, me: usize, n: usize, primes: &[u64], t: u64, tcols: usize, det_seed: Option<&str>) -> Result<(Custodian, Ceremony), String> {
    #[cfg(feature = "test-det")]
    let mut cust = match det_seed {
        Some(s) => Custodian::new_det(me, s),
        None => Custodian::new(me),
    };
    #[cfg(not(feature = "test-det"))]
    let mut cust = {
        if det_seed.is_some() {
            return Err("a deterministic ceremony needs a build with --features test-det".into());
        }
        Custodian::new(me)
    };
    let np = net.n;
    let mut cer = Ceremony::new(EPOCH, np, n, primes, t, tcols);
    let coms = net.exchange_bytes(net::CTRL, cust.commitment(EPOCH).as_bytes());
    for (i, c) in coms.iter().enumerate() {
        let c = if i == me { cust.commitment(EPOCH) } else { String::from_utf8(c.clone()).map_err(|_| "commitment: not text")? };
        cer.commit(i, &c).map_err(|e| e.0)?;
    }
    let rev = net.exchange_bytes(net::CTRL, format!("{}|{}", cust.r, cust.salt).as_bytes());
    for (i, b) in rev.iter().enumerate() {
        let s = if i == me { format!("{}|{}", cust.r, cust.salt) } else { String::from_utf8(b.clone()).map_err(|_| "reveal: not text")? };
        let (r, salt) = s.split_once('|').ok_or("reveal: shape")?;
        cer.reveal(i, r, salt).map_err(|e| e.0)?;
    }
    let (b, proof) = cust.make_key(&cer)?;
    let mut mine = poly_bytes(&b);
    let blen = mine.len() as u64;
    let mut msg = blen.to_le_bytes().to_vec();
    msg.append(&mut mine);
    msg.extend_from_slice(&proof);
    let keys = net.exchange_bytes(net::CTRL, &msg);
    for (i, m) in keys.iter().enumerate() {
        let m = if i == me { &msg } else { m };
        if m.len() < 8 {
            return Err(format!("custodian {i}'s key message: shape"));
        }
        let bl = u64::from_le_bytes(m[..8].try_into().unwrap()) as usize;
        if m.len() < 8 + bl {
            return Err(format!("custodian {i}'s key message: shape"));
        }
        let bi = poly_parse(&m[8..8 + bl])?;
        cer.register(i, bi, &m[8 + bl..]).map_err(|e| e.0)?;
    }
    Ok((cust, cer))
}
