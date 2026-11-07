//! Custodian processes and the in-process three-party run (dealer + three threads over 127.0.0.1 TCP).
use crate::arith::ntt_primes;
use crate::bfv::OwnKey;
use crate::he::He;
use crate::net::{self, bytes_to_u64s, u64s_to_bytes, Net};
use crate::party::{Party, Sh};
use crate::rns::Rns;
use crate::step::*;
use crate::tape::{deal_step, Tape};
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
}

pub fn prof(a: &[String]) -> Prof {
    let n: usize = a[0].parse().unwrap();
    let l: usize = a[1].parse().unwrap();
    let pr = ntt_primes(61, l + 1, 2 * n as u64);
    Prof { n, l, f_bits: a[2].parse().unwrap(), d: a[3].parse().unwrap(), qs: pr[..l].to_vec(), t: pr[l] }
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
    let key = OwnKey::new(rns.clone(), KEY_SEED0 + i as u64);
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
    };
    let setup = t0.elapsed().as_secs_f64();
    let tab = tables(pf.t);
    let mut pt = Party::new(i, pf.t, net, tape);
    let t1 = Instant::now();
    let res = run_step(&mut pt, &mut he, cs, pf.d, &tab);
    let step_s = t1.elapsed().as_secs_f64();
    let sent = pt.net.total_sent();
    let base = json!({
        "party": i, "setup_seconds": setup, "step_seconds": step_s,
        "transcript_len": pt.tr.len(), "tape_used": pt.cur, "tape_len": pt.tape.len(),
        "wire": pt.wire, "bytes_sent": {"open": sent[0], "he_ct": sent[1], "he_ret": sent[2], "ctrl": sent[3]},
        "he_wire": {"mv": {"he_send": he.he_send, "he_return": he.he_return},
                    "ou": {"he_send": he.ou_send, "he_return": he.ou_return, "commit": he.ou_commit}},
    });
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
    let plain = inputs(pf.d);
    let (e1, e2) = plain.step();
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
    let t0 = Instant::now();
    let plain = inputs(pf.d);
    let (tapes, cs) = deal_step(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t));
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
            let pf2 = pf.clone();
            std::thread::spawn(move || {
                let net = Net::connect(i, l, &addrs);
                custodian(i, &pf2, net, tape, &cs, attack)
            })
        })
        .collect();
    let outs: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    let wall = t1.elapsed().as_secs_f64();
    let all_ok = outs.iter().all(|o| o.1.is_some());
    let refines = all_ok && reveal_check(pf, &outs.iter().map(|o| o.1.clone().unwrap()).collect::<Vec<_>>());
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
