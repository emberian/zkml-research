//! Custodian processes and the in-process three-party run (dealer + three threads over 127.0.0.1 TCP).
use crate::arith::ntt_primes;
use crate::bfv::OwnKey;
use crate::he::He;
use crate::net::{self, bytes_to_u64s, u64s_to_bytes, Net};
use crate::party::{Party, Sh};
use crate::rns::Rns;
use crate::step::*;
use crate::tape::Tape;
use serde_json::json;
use std::net::{SocketAddr, TcpListener};
use std::sync::Arc;
use std::time::Instant;

pub const DEALER_SEED: u64 = 5;
pub const OWNER_SEED: u64 = 9;
pub const KEY_SEED0: u64 = 100;
pub const MV_SEED: u64 = 11;
pub const OU_SEED: u64 = 13;

#[derive(Clone)]
pub struct Prof {
    pub n: usize,
    pub l: usize,
    pub f_bits: u32,
    pub d: usize,
    pub qs: Vec<u64>,
    pub t: u64,
    /// compute threads per custodian
    pub threads: usize,
    /// Some(T): ceremony keys and the ZKPoPK gate with T opened columns (309 ledger, 97 demo); None: OwnKey, ungated
    pub gate: Option<usize>,
    /// TEST ONLY (feature test-det): DL_DETERMINISTIC seed for the ceremony and the batch proofs
    pub det_seed: Option<String>,
    /// the three custodians share this process and machine (`darkstep local`): low-memory ZK proving
    pub colocated: bool,
    /// HE encryption and return coins from OS randomness (every party process); false = the harness's public
    /// reference streams, which only the in-process test harness (`run_local`) uses
    pub secure_coins: bool,
    /// the step program (step::Program; HARNESS unless set)
    pub program: Program,
}

pub fn prof(a: &[String]) -> Prof {
    let n: usize = a[0].parse().unwrap();
    let l: usize = a[1].parse().unwrap();
    let pr = ntt_primes(61, l + 1, 2 * n as u64);
    let cores = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    let threads = std::env::var("DS_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(cores);
    Prof { n, l, f_bits: a[2].parse().unwrap(), d: a[3].parse().unwrap(), qs: pr[..l].to_vec(), t: pr[l], threads, gate: None, det_seed: None, colocated: false, secure_coins: false, program: Program::HARNESS }
}

pub fn flag(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|x| x == name).and_then(|k| args.get(k + 1).cloned())
}

pub fn attack_of(args: &[String]) -> Option<(String, usize)> {
    flag(args, "--attack").map(|s| {
        let (k, p) = s.split_once(':').expect("KIND:PARTY");
        (k.to_string(), p.parse().unwrap())
    })
}

/// One custodian: keygen, public-key exchange, the step. Returns its result JSON and final shares.
pub fn custodian(i: usize, pf: &Prof, net: Net, tape: Tape, cs: &[u64], attack: Option<(String, usize)>) -> (serde_json::Value, Option<(Vec<Vec<Sh>>, Vec<Vec<Sh>>)>, Option<String>) {
    let t0 = Instant::now();
    let rns = Arc::new(Rns::new(pf.n, &pf.qs, pf.t));
    let (key, pks, gate) = match pf.gate {
        None => {
            let key = if pf.secure_coins { OwnKey::new_secure(rns.clone()) } else { OwnKey::new(rns.clone(), KEY_SEED0 + i as u64) };
            // public keys: exchange (pk0_ntt, pk1_ntt)
            let mut mine = key.pk.pk0_ntt.clone();
            mine.extend_from_slice(&key.pk.pk1_ntt);
            let all = net.exchange_bytes(net::CTRL, &u64s_to_bytes(&mine));
            let ln = rns.l() * rns.n;
            let pks = all
                .iter()
                .map(|b| {
                    let v = bytes_to_u64s(b);
                    crate::bfv::PubKey { pk0_ntt: v[..ln].to_vec(), pk1_ntt: v[ln..].to_vec() }
                })
                .collect();
            (key, pks, None)
        }
        Some(tcols) => {
            // keys from the ceremony: every key registered with its key proof; the public keys ARE the registry
            let tc = Instant::now();
            let (cust, cer) = match crate::gate::ceremony(&net, i, pf.n, &pf.qs, pf.t, tcols, pf.det_seed.as_deref()) {
                Ok(x) => x,
                Err(e) => {
                    net.shutdown();
                    return (json!({"party": i, "verdict": "REFUSED", "by": format!("ceremony: {e}")}), None, None);
                }
            };
            let regs: Vec<Arc<dzkpopk::KeyRegistry>> = (0..3).map(|k| cer.registry(k).unwrap()).collect();
            let key = if pf.secure_coins {
                OwnKey::from_ceremony_secure(rns.clone(), &cust.s, regs[i].b_res(), regs[i].a_res())
            } else {
                OwnKey::from_ceremony(rns.clone(), KEY_SEED0 + i as u64, &cust.s, regs[i].b_res(), regs[i].a_res())
            };
            let pks = regs
                .iter()
                .map(|r| OwnKey::from_ceremony(rns.clone(), 0, &vec![0; pf.n], r.b_res(), r.a_res()).pk)
                .collect();
            let g = crate::gate::Gate {
                regs,
                s: cust.s.clone(),
                e_pk: cust.e.clone(),
                tcols,
                det_seed: pf.det_seed.clone(),
                ceremony_s: tc.elapsed().as_secs_f64(),
                prove_s: 0.0,
                verify_s: 0.0,
                wait_s: 0.0,
                low_memory: std::env::var("DS_ZK_LOWMEM").map(|v| v != "0").unwrap_or(pf.colocated),
                proof_bytes_sent: 0,
                proofs: vec![],
            };
            (key, pks, Some(g))
        }
    };
    let mut he = He {
        rns: rns.clone(),
        key,
        pks,
        f_bits: pf.f_bits,
        mv_seed: MV_SEED,
        ou_seed: OU_SEED,
        mv_calls: 0,
        ou_calls: 0,
        context: ("model".into(), 0, 0),
        he_send: 0,
        he_return: 0,
        ou_send: 0,
        ou_return: 0,
        ou_commit: 0,
        cts_sent: 0,
        cts_returned: 0,
        attack,
        gate,
    };
    let setup = t0.elapsed().as_secs_f64();
    let tab = pf.program.tables(pf.t);
    let mut pt = Party::new(i, pf.t, net, tape);
    let t1 = Instant::now();
    // each custodian computes on its own pool: a pool shared by the three in-process parties lets one party's blocked
    // returner jobs starve the others (they are separate machines in deployment)
    let pool = rayon::ThreadPoolBuilder::new().num_threads(pf.threads).build().unwrap();
    let res = pool.install(|| run_step_prog(&mut pt, &mut he, cs, pf.d, &tab, &pf.program));
    let step_s = t1.elapsed().as_secs_f64();
    let sent = pt.net.total_sent();
    let per_peer = pt.net.sent_per_peer();
    let base = json!({
        "party": i, "setup_seconds": setup, "step_seconds": step_s,
        "transcript_len": pt.tr.len(), "tape_used": pt.cur, "tape_len": pt.tape.len(),
        "middle_atoms": pt.atom_log.iter().map(|r| r.len()).sum::<usize>(),
        "wire": pt.wire, "bytes_sent": {"open": sent[0], "he_ct": sent[1], "he_ret": sent[2], "ctrl": sent[3], "proof": sent[4]},
        "bytes_sent_to": per_peer.iter().enumerate().filter(|(j, _)| *j != i).map(|(j, s)| (j.to_string(), json!({"open": s[0], "he_ct": s[1], "he_ret": s[2], "ctrl": s[3], "proof": s[4], "total": s.iter().sum::<u64>()}))).collect::<serde_json::Map<_, _>>(),
        "he_wire": {"mv": {"he_send": he.he_send, "he_return": he.he_return},
                    "ou": {"he_send": he.ou_send, "he_return": he.ou_return, "commit": he.ou_commit}},
    });
    let mut base = base;
    if let Some(g) = &he.gate {
        base["gate"] = json!({
            "T": g.tcols, "ceremony_seconds": g.ceremony_s, "prove_seconds": g.prove_s, "verify_seconds": g.verify_s, "zk_lock_wait_seconds": g.wait_s, "low_memory": g.low_memory,
            "proof_bytes_sent": g.proof_bytes_sent, "ceremony_seed": g.regs[0].seed.split('/').next(),
            "key_b_sha256": g.regs.iter().map(|r| pycompat::repr::sha256_hex(&dzkpopk::Json::List(r.b.to_big().into_iter().map(|x| dzkpopk::Json::Int(x.into())).collect()).canonical())).collect::<Vec<_>>(),
            "proofs": g.proofs.iter().map(|(l, h)| json!([l, h])).collect::<Vec<_>>(),
        });
    }
    let tdig = transcript_digest(&pt.tr);
    let mut dump = Vec::new();
    if i == 0 && pf.d <= 128 {
        pt.tr.dump(&mut dump).unwrap();
    }
    pt.net.shutdown();
    match res {
        Ok(out) => {
            let mut v = base;
            v["verdict"] = json!("ACCEPT");
            v["transcript"] = json!(tdig);
            v["digest"] = json!(party_digest(&out.w1n, &out.w2n));
            v["sigma"] = json!(out.sigma);
            v["phases"] = json!(out.phases.iter().map(|(k, s)| json!([k, s])).collect::<Vec<_>>());
            (v, Some((out.w1n, out.w2n)), Some(String::from_utf8(dump).unwrap()))
        }
        Err(e) => {
            let mut v = base;
            v["verdict"] = json!("REFUSED");
            v["by"] = json!(e);
            (v, None, None)
        }
    }
}

pub fn reveal_check(pf: &Prof, shares: &[(Vec<Vec<Sh>>, Vec<Vec<Sh>>)]) -> bool {
    let p = pf.t;
    let plain = inputs_for(pf.d, &pf.program);
    let (e1, e2) = match plain.step_prog(&pf.program) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{e}");
            return false;
        }
    };
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let rev = |sel: &dyn Fn(&(Vec<Vec<Sh>>, Vec<Vec<Sh>>)) -> &Vec<Vec<Sh>>, want: &Vec<Vec<i64>>| -> bool {
        (0..pf.d).all(|r| {
            (0..pf.d).all(|c| {
                let s = shares.iter().fold(0u64, |a, x| crate::arith::addmod(a, sel(x)[r][c].s, p));
                cen(s) == want[r][c]
            })
        })
    };
    rev(&|x| &x.0, &e1) && rev(&|x| &x.1, &e2)
}


pub type Shares = (Vec<Vec<Sh>>, Vec<Vec<Sh>>);

/// The whole step in this process: dealer, then three custodian threads over 127.0.0.1 TCP. Returns the summary JSON
/// (what `darkstep local` prints and writes) and party 0's transcript dump (d <= 128).
pub fn run_local(pf: &Prof, attack: Option<(String, usize)>) -> (serde_json::Value, Option<String>) {
    run_local_opts(pf, attack, std::env::var("DS_PROOF_ATOMS").is_ok())
}

/// proof_atoms: deal the collaborative proof's truncation range bits onto the tapes too (the step skips them).
pub fn run_local_opts(pf: &Prof, attack: Option<(String, usize)>, proof_atoms: bool) -> (serde_json::Value, Option<String>) {
    let t0 = Instant::now();
    let plain = inputs_for(pf.d, &pf.program);
    let (cs, dl) =
        crate::tape::deal_step_dealer_prog(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t), proof_atoms, &pf.program);
    let tapes = dl.tapes;
    let deal_s = t0.elapsed().as_secs_f64();
    let listeners: Vec<TcpListener> = (0..3).map(|_| TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<SocketAddr> = listeners.iter().map(|l| l.local_addr().unwrap()).collect();
    let t1 = Instant::now();
    let cs = Arc::new(cs);
    let handles: Vec<_> = listeners
        .into_iter()
        .zip(tapes)
        .enumerate()
        .map(|(i, (l, tape))| {
            let addrs = addrs.clone();
            let cs = cs.clone();
            let attack = attack.clone();
            let mut pf2 = pf.clone();
            pf2.colocated = true;
            std::thread::spawn(move || {
                let net = Net::connect(i, l, &addrs);
                custodian(i, &pf2, net, tape, &cs, attack)
            })
        })
        .collect();
    let outs: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    let wall = t1.elapsed().as_secs_f64();
    let all_ok = outs.iter().all(|o| o.1.is_some());
    let mut outs = outs;
    let refines = all_ok && {
        let sh: Vec<Shares> = outs.iter_mut().map(|o| o.1.take().unwrap()).collect();
        reveal_check(pf, &sh)
    };
    let res = json!({
        "verdict": if all_ok { "ACCEPT" } else { "REFUSED" }, "refines_spec": refines,
        "N": pf.n, "L": pf.l, "F_bits": pf.f_bits, "d": pf.d, "t": pf.t, "Q_primes": pf.qs,
        "deal_seconds": deal_s, "step_wall_seconds": wall,
        "transcript": outs[0].0.get("transcript"),
        "parties": outs.iter().map(|o| o.0.get("digest").cloned().unwrap_or_default()).collect::<Vec<_>>(),
        "sigma": outs.iter().map(|o| o.0.get("sigma").cloned().unwrap_or_default()).collect::<Vec<_>>(),
        "by": outs.iter().filter_map(|o| o.0.get("by").cloned()).collect::<Vec<_>>(),
        "detail": outs.iter().map(|o| o.0.clone()).collect::<Vec<_>>(),
    });
    (res, outs.into_iter().next().and_then(|o| o.2))
}
