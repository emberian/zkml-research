//! The custody handover between custodian processes, with enforced erasure (gen 6).
//!
//!   dl-hand local <work> <d> <demo|ledger> <port_base>
//!       everything on 127.0.0.1: the TEST-ONLY setup (an ideal dealer stands in for step k's end state), six
//!       custodian processes (old 0..2, new 0..2; PID files in <work>/pids), the ledger rotation, and a restart of
//!       each old custodian after the handover. Writes <work>/summary.json; exits non-zero unless every check holds.
//!   dl-hand deal <work> <d> <profile>
//!   dl-hand old <work> <i> <d> <profile> <port_base>
//!   dl-hand new <work> <j> <d> <profile> <port_base>       (j = 0 also submits the rotation to the ledger)
//!   dl-hand restart <work> <i> <d> <profile>                (an old custodian started again after the handover)
//!
//! Ports: old mesh base+0..2, new mesh base+3..5, joint mesh base+6..11. Every process uses the zeroizing allocator.
use darkhand::erase::{Wipe, ZeroOnFree};
use darkhand::side::{self, ct_bytes, ct_parse, digest, os_field, Common, OldCustodian, KINDS};
use darkproof::handover::HandoverCtx;
use darkproof::ledger::{Genesis, Ledger};
use darkproof::pcs::PcsParty;
use darkproof::rng::Det;
use darkproof::Profile;
use darkstep::bfv::OwnKey;
use darkstep::net::Net;
use darkstep::party::Sh;
use darkstep::rns::Rns;
use darkstep::tape::{Dealer, Tag, Tape};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::net::{SocketAddr, TcpListener};
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[global_allocator]
static A: ZeroOnFree = ZeroOnFree;

const MODEL: &str = "mind-h";
const CHECK: usize = 8;
const OLD_SET: [&str; 3] = ["c0", "c1", "c2"];
const NEW_SET: [&str; 3] = ["c3", "c4", "c5"];

fn common(d: usize, prof: &str) -> Common {
    let he: [&str; 3] = match prof {
        "demo" => ["8192", "3", "118"],
        "ledger" => ["16384", "4", "175"],
        _ => panic!("profile: demo or ledger"),
    };
    let args: Vec<String> = he.iter().map(|s| s.to_string()).chain(std::iter::once(d.to_string())).collect();
    let pf = darkstep::node::prof(&args);
    darkproof::field::set_p(pf.t);
    let pr = Profile::by_name(prof).unwrap();
    let lp = pr.ligero();
    let ctx = HandoverCtx {
        model: MODEL.into(),
        epoch_old: 0,
        epoch_new: 1,
        after_step: 0,
        old_set: OLD_SET.iter().map(|s| s.to_string()).collect(),
        new_set: NEW_SET.iter().map(|s| s.to_string()).collect(),
    };
    Common { pr, lp, d, n_old: 3, n_new: 3, ctx, rns: Arc::new(Rns::new(pf.n, &pf.qs, pf.t)), t: pf.t }
}

fn mesh(base: u16, off: u16, n: u16, me: usize) -> Net {
    let a: Vec<SocketAddr> = (0..n).map(|k| SocketAddr::from(([127, 0, 0, 1], base + off + k))).collect();
    let l = TcpListener::bind(a[me]).unwrap_or_else(|e| panic!("bind {}: {e}", a[me]));
    Net::connect(me, l, &a)
}

fn read_tape(p: &Path) -> std::io::Result<Tape> {
    let mut f = std::io::BufReader::new(std::fs::File::open(p)?);
    Tape::read_from(&mut f)
}

fn write_tape(p: &Path, t: &Tape) {
    let mut f = std::io::BufWriter::new(std::fs::File::create(p).unwrap());
    t.write_to(&mut f).unwrap();
}

fn write_json(p: &Path, v: &Value) {
    std::fs::write(p, serde_json::to_string_pretty(v).unwrap()).unwrap();
}

fn peak_rss_mb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok()))
        .map(|kb| kb / 1024.0)
        .unwrap_or(-1.0)
}

fn wait_for(p: &Path) {
    while !p.exists() {
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

/// TEST ONLY: an ideal dealer stands in for the state step k leaves behind. Each old custodian gets a tape holding
/// its authenticated W1 then W2 shares (2 d^2 entries) under the old alpha; each new custodian gets its own
/// preprocessing under a different alpha (auth_plain entries for the re-authentication and the check openings).
/// The plaintext W is written to <work>/truth (the test's oracle, read by no custodian).
fn deal(work: &Path, d: usize, prof: &str) {
    let c = common(d, prof);
    let seed = |_: ()| u64::from_le_bytes(os_field(1, c.t)[0].to_le_bytes());
    let mut old = Dealer::new(c.t, 3, seed(()));
    let w = os_field(2 * d * d, c.t);
    for &v in &w {
        old.auth(v, Tag::Ar);
    }
    let mut new = Dealer::new(c.t, 3, seed(()));
    for _ in 0..2 * d * d + 2 * CHECK {
        new.auth_plain();
    }
    for i in 0..3 {
        let od = work.join(format!("old{i}"));
        let nd = work.join(format!("new{i}"));
        std::fs::create_dir_all(&od).unwrap();
        std::fs::create_dir_all(&nd).unwrap();
        write_tape(&od.join("tape.bin"), &old.tapes[i]);
        write_tape(&nd.join("tape.bin"), &new.tapes[i]);
    }
    std::fs::create_dir_all(work.join("pub")).unwrap();
    let truth: Vec<u64> = w.iter().take(CHECK).chain(w[d * d..].iter().take(CHECK)).copied().collect();
    write_json(&work.join("truth.json"), &json!({"W1_head": &truth[..CHECK], "W2_head": &truth[CHECK..],
        "old_alpha_nonzero": old.alpha != 0, "alphas_differ": old.alpha != new.alpha}));
}

fn roots_json(r: &BTreeMap<String, Vec<[u8; 32]>>) -> Value {
    json!(r.iter().map(|(k, v)| (k.clone(), v.iter().map(|h| pycompat::repr::hex(h)).collect::<Vec<_>>())).collect::<BTreeMap<_, _>>())
}

/// One old custodian: its epoch-1 key ceremony with the old committee, a ciphertext under its key (kept public in
/// <work>/pub, as a ciphertext it sent during the run would be), its child commitment, then the handover.
fn old(work: &Path, i: usize, d: usize, prof: &str, base: u16) {
    let c = common(d, prof);
    let dir = work.join(format!("old{i}"));
    let tape = read_tape(&dir.join("tape.bin")).expect("old tape");
    let w: BTreeMap<String, Vec<Sh>> = KINDS
        .iter()
        .enumerate()
        .map(|(q, k)| (k.to_string(), (q * d * d..(q + 1) * d * d).map(|p| Sh { s: tape.sh[p], m: tape.mac[p] }).collect()))
        .collect();
    let net3 = mesh(base, 0, 3, i);
    let (cust, cer) = darkhand::ceremony::run(&net3, i, c.rns.n, &c.rns.qs, c.t, c.pr.t_cols, 1).expect("old ceremony");
    net3.shutdown();
    std::fs::write(dir.join("key.bin"), darkstep::net::u64s_to_bytes(&cust.s.iter().map(|&x| x as u64).collect::<Vec<_>>())).unwrap();
    let reg = cer.registry(i).unwrap();
    let mut key = OwnKey::from_ceremony(c.rns.clone(), u64::from_le_bytes(os_field(1, c.t)[0].to_le_bytes()), &cust.s, reg.b_res(), reg.a_res());
    let mut m = os_field(c.rns.n, c.t);
    let ct = key.encrypt_exact(&m);
    let mdig = digest(&m);
    m.wipe();
    std::fs::write(work.join(format!("pub/old{i}.ct")), ct_bytes(&ct)).unwrap();
    std::fs::write(work.join(format!("pub/old{i}.ct.sha256")), &mdig).unwrap();
    let carry: BTreeMap<String, PcsParty> = KINDS
        .iter()
        .map(|k| {
            let plain: Vec<u64> = w[*k].iter().map(|x| x.s).collect();
            let mut pc = PcsParty::commit(&c.pr, &plain, &format!("{k}n"), i, &Det(None));
            pc.opened_lives = 1;
            let mut plain = plain;
            plain.wipe();
            (k.to_string(), pc)
        })
        .collect();
    let roots: BTreeMap<String, Vec<[u8; 32]>> = carry.iter().map(|(k, p)| (k.clone(), vec![p.root])).collect();
    write_json(&work.join(format!("pub/old{i}.roots.json")), &roots_json(&roots));
    let st = OldCustodian {
        i,
        w,
        tape,
        cust,
        cer,
        key: Some(key),
        carry,
        files: vec![dir.join("tape.bin"), dir.join("key.bin")],
        captured: Some((ct, mdig)),
    };
    let net6 = mesh(base, 6, 6, i);
    let mut rep = side::old_side(&c, st, net6).unwrap_or_else(|e| json!({"role": "old", "party": i, "error": e}));
    rep["peak_rss_mb"] = json!(peak_rss_mb());
    write_json(&work.join(format!("pub/old{i}.json")), &rep);
}

/// One new custodian: the handover (its own ceremony at epoch 2, resharing, the joint proof, re-authentication);
/// custodian 0 submits the proof bytes to the ledger.
fn new(work: &Path, j: usize, d: usize, prof: &str, base: u16) {
    let c = common(d, prof);
    let dir = work.join(format!("new{j}"));
    let tape = read_tape(&dir.join("tape.bin")).expect("new tape");
    let net3 = mesh(base, 3, 3, j);
    let net6 = mesh(base, 6, 6, 3 + j);
    let out = match side::new_side(&c, j, net3, net6, tape, 2, CHECK) {
        Ok(o) => o,
        Err(e) => {
            write_json(&work.join(format!("pub/new{j}.json")), &json!({"role": "new", "party": j, "error": e}));
            return;
        }
    };
    let mut rep = out.report.clone();
    if j == 0 {
        let lpath = work.join("ledger.jsonl");
        wait_for(&lpath);
        let mut lg = Ledger::open(&lpath, MODEL, &c.pr, None).expect("ledger");
        let cust: Vec<String> = NEW_SET.iter().map(|s| s.to_string()).collect();
        rep["rotation"] = json!(match lg.rotate(&cust, &out.new_roots, &out.proof) {
            Ok(()) => "accept".to_string(),
            Err(e) => e,
        });
        rep["ledger_head_is_new_roots"] = json!(lg.head().1 == out.new_roots);
    }
    std::fs::write(work.join(format!("pub/new{j}.ct")), hex_decode(rep["ct_under_new_key"].as_str().unwrap())).unwrap();
    std::fs::write(work.join(format!("pub/new{j}.ct.sha256")), rep["ct_plain_sha256"].as_str().unwrap()).unwrap();
    rep.as_object_mut().unwrap().remove("ct_under_new_key");
    rep["peak_rss_mb"] = json!(peak_rss_mb());
    write_json(&work.join(format!("pub/new{j}.json")), &rep);
    out.party.net.shutdown();
}

fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|k| u8::from_str_radix(&s[2 * k..2 * k + 2], 16).unwrap()).collect()
}

/// An old custodian started again after the handover, from its state directory: it loads whatever key and share
/// material is there (nothing should be), and tries to decrypt its own earlier ciphertext and each new custodian's
/// ciphertext with it. Missing material is filled with zeros, which is all this custodian can still produce.
fn restart(work: &Path, i: usize, d: usize, prof: &str) -> Value {
    let c = common(d, prof);
    let dir = work.join(format!("old{i}"));
    let key_file = std::fs::read(dir.join("key.bin")).ok();
    let tape = read_tape(&dir.join("tape.bin")).ok();
    let mut s: Vec<i64> = key_file.as_ref().map(|b| darkstep::net::bytes_to_u64s(b).iter().map(|&x| x as i64).collect()).unwrap_or_default();
    let had_key = !s.is_empty() && s.iter().any(|&x| x != 0);
    s.resize(c.rns.n, 0);
    // the public part of its old key (b, a) is recomputed from nothing secret: a zero b gives the key s = 0's view
    let zero_b: Vec<Vec<u64>> = c.rns.qs.iter().map(|_| vec![0u64; c.rns.n]).collect();
    let key = OwnKey::from_ceremony(c.rns.clone(), 0, &s, &zero_b, &zero_b);
    let mut tries = Vec::new();
    let mut targets = vec![format!("old{i}")];
    targets.extend((0..3).map(|j| format!("new{j}")));
    for t in targets {
        let ct = std::fs::read(work.join(format!("pub/{t}.ct"))).ok().and_then(|b| ct_parse(&b));
        let want = std::fs::read_to_string(work.join(format!("pub/{t}.ct.sha256"))).unwrap_or_default();
        let ok = ct.map(|ct| digest(&key.decrypt(&ct, None)) == want);
        tries.push(json!({"ciphertext": t, "decrypted": ok}));
    }
    json!({"role": "old-restarted", "party": i, "key_file_present": key_file.is_some(), "key_material_nonzero": had_key,
           "tape_file_present": tape.is_some(), "share_entries_loaded": tape.map(|t| t.len()).unwrap_or(0),
           "decryption_attempts": tries})
}

fn spawn(work: &Path, args: &[String], name: &str) -> std::process::Child {
    let exe = std::env::current_exe().unwrap();
    let log = std::fs::File::create(work.join(format!("logs/{name}.log"))).unwrap();
    let child = std::process::Command::new(exe)
        .args(args)
        .stdout(log.try_clone().unwrap())
        .stderr(log)
        .spawn()
        .unwrap();
    std::fs::write(work.join(format!("pids/{name}.pid")), child.id().to_string()).unwrap();
    child
}

fn read_json(p: &Path) -> Value {
    std::fs::read_to_string(p).ok().and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(Value::Null)
}

fn local(work: &Path, d: usize, prof: &str, base: u16) -> bool {
    for sub in ["logs", "pids", "pub"] {
        std::fs::create_dir_all(work.join(sub)).unwrap();
    }
    let t0 = std::time::Instant::now();
    deal(work, d, prof);
    let ws = work.display().to_string();
    let mut kids = Vec::new();
    for i in 0..3 {
        let a = ["old", &ws, &i.to_string(), &d.to_string(), prof, &base.to_string()].map(String::from).to_vec();
        kids.push((format!("old{i}"), spawn(work, &a, &format!("old{i}"))));
    }
    for j in 0..3 {
        let a = ["new", &ws, &j.to_string(), &d.to_string(), prof, &base.to_string()].map(String::from).to_vec();
        kids.push((format!("new{j}"), spawn(work, &a, &format!("new{j}"))));
    }
    // the ledger: its head is the old committee's commitment (the child of step k)
    let c = common(d, prof);
    let mut roots: BTreeMap<String, Vec<[u8; 32]>> = KINDS.iter().map(|k| (k.to_string(), Vec::new())).collect();
    for i in 0..3 {
        let p = work.join(format!("pub/old{i}.roots.json"));
        wait_for(&p);
        std::thread::sleep(std::time::Duration::from_millis(100));
        let v = read_json(&p);
        for k in KINDS {
            let h = v[k][0].as_str().unwrap();
            roots.get_mut(k).unwrap().push(darkproof::h::unhex32(h).unwrap());
        }
    }
    let g = Genesis { d, program: darkproof::step::StepParams::HARNESS, owner_pk: None, custodians: OLD_SET.iter().map(|s| s.to_string()).collect(), roots: roots.clone() };
    let tmp = work.join("ledger.jsonl.tmp");
    drop(Ledger::open(&tmp, MODEL, &c.pr, Some(g)).expect("genesis"));
    std::fs::rename(&tmp, work.join("ledger.jsonl")).unwrap();
    let mut exits = BTreeMap::new();
    for (name, mut k) in kids {
        let st = k.wait().unwrap();
        exits.insert(name.clone(), st.code());
        let _ = std::fs::remove_file(work.join(format!("pids/{name}.pid")));
    }
    let restarts: Vec<Value> = (0..3).map(|i| restart(work, i, d, prof)).collect();
    let olds: Vec<Value> = (0..3).map(|i| read_json(&work.join(format!("pub/old{i}.json")))).collect();
    let news: Vec<Value> = (0..3).map(|j| read_json(&work.join(format!("pub/new{j}.json")))).collect();
    let truth = read_json(&work.join("truth.json"));
    // ---- the checks
    let mut checks: Vec<(String, bool)> = Vec::new();
    let mut ck = |name: &str, ok: bool| checks.push((name.to_string(), ok));
    ck("all six custodian processes exited 0", exits.values().all(|c| *c == Some(0)));
    let digests: Vec<&str> = olds.iter().chain(&news).map(|v| v["proof_sha256"].as_str().unwrap_or("")).collect();
    ck("all six hold the same handover proof", !digests[0].is_empty() && digests.iter().all(|x| *x == digests[0]));
    ck("the ledger accepts the rotation (native verifier)", news[0]["rotation"] == "accept");
    ck("the ledger head is the new committee's roots", news[0]["ledger_head_is_new_roots"] == true);
    ck("new committee: MAC check of openings under its own key passes", news.iter().all(|v| v["mac_check"] == "ok"));
    ck("new committee: opened W1, W2 entries equal the plaintext W",
       news.iter().all(|v| v["opened"]["W1"] == truth["W1_head"] && v["opened"]["W2"] == truth["W2_head"]));
    ck("the new MAC key differs from the old", truth["alphas_differ"] == true);
    ck("new committee: each decrypts its own ciphertext (control)", news.iter().all(|v| v["decrypts_own_ct"] == true));
    ck("old: before erasure the scan finds the material (control)",
       olds.iter().all(|v| v["scan_before_erasure"]["available"] == false || v["scan_before_erasure"]["hits"].as_u64().unwrap_or(0) > 0));
    ck("old: after erasure the scan finds none of it",
       olds.iter().all(|v| v["scan_after_erasure"]["available"] == false || v["scan_after_erasure"]["hits"] == 0));
    ck("old: the memory scan ran (Linux)", olds.iter().all(|v| v["scan_after_erasure"]["available"] == true));
    ck("old: the zeroizing allocator was active", olds.iter().all(|v| v["allocator_wiped_bytes"].as_u64().unwrap_or(0) > 0));
    ck("old: decrypts its earlier ciphertext before erasure (control)", olds.iter().all(|v| v["decrypts_captured_before_erasure"] == true));
    ck("old: cannot decrypt it after erasure (in the same process)", olds.iter().all(|v| v["decrypts_captured_after_erasure"] == false));
    ck("old: no state files left", olds.iter().all(|v| v["state_files_left"].as_array().map(|a| a.is_empty()).unwrap_or(false)));
    ck("old restarted: no key or share material on disk",
       restarts.iter().all(|v| v["key_file_present"] == false && v["tape_file_present"] == false && v["share_entries_loaded"] == 0));
    ck("old restarted: decrypts neither its old ciphertext nor any new custodian's",
       restarts.iter().all(|v| v["decryption_attempts"].as_array().unwrap().iter().all(|t| t["decrypted"] == false)));
    let all = checks.iter().all(|c| c.1);
    let summary = json!({
        "d": d, "profile": prof, "all_checks": all, "seconds": t0.elapsed().as_secs_f64(),
        "checks": checks.iter().map(|(n, ok)| json!({"check": n, "ok": ok})).collect::<Vec<_>>(),
        "exits": exits, "old": olds, "new": news, "restarted": restarts,
    });
    write_json(&work.join("summary.json"), &summary);
    for (n, ok) in &checks {
        println!("{} {n}", if *ok { "ok  " } else { "FAIL" });
    }
    println!("all checks: {all}");
    all
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let arg = |k: usize| a.get(k).cloned().unwrap_or_else(|| panic!("missing argument {k}; see the header"));
    let work = PathBuf::from(arg(2));
    match a.get(1).map(|s| s.as_str()) {
        Some("local") => {
            let ok = local(&work, arg(3).parse().unwrap(), &arg(4), arg(5).parse().unwrap());
            std::process::exit(if ok { 0 } else { 1 });
        }
        Some("deal") => deal(&work, arg(3).parse().unwrap(), &arg(4)),
        Some("old") => old(&work, arg(3).parse().unwrap(), arg(4).parse().unwrap(), &arg(5), arg(6).parse().unwrap()),
        Some("new") => new(&work, arg(3).parse().unwrap(), arg(4).parse().unwrap(), &arg(5), arg(6).parse().unwrap()),
        Some("restart") => {
            let v = restart(&work, arg(3).parse().unwrap(), arg(4).parse().unwrap(), &arg(5));
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
        }
        _ => {
            eprintln!("usage: see the header of darkhand/src/bin/dl-hand.rs");
            std::process::exit(2);
        }
    }
}
