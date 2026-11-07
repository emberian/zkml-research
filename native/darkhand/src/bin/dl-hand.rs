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
//!   dl-hand local-self <work> <d> <profile> <port_base>
//!       the self-handover after an SPDZ abort: the same three seats (one process each, its old and new roles as two
//!       threads on the joint mesh), the HE keys kept, the W shares reshared and re-authenticated under a NEW MAC key,
//!       the handover proof binding them to the ledger head; the old shares, tape and alpha share erased.
//!   dl-hand seat <work> <i> <d> <profile> <port_base>        (one seat of local-self)
//!
//!   dl-hand restart-seat <out.json> <handover_P<I>.json> [join_P<J>.json ...] -- serve I N L F d D ... (the seat's argv)
//!       a deployed old seat restarted after the handover: what it can load from disk, and its decryption attempts
//!   dl-hand verify-rotation <workdir> <ledger.jsonl> <handover_e<E>.bin> N L F d [profile]
//!       re-verify a replica's rotation natively from the proof bytes; a one-byte-flipped copy must be refused
//! DLH_STRAY_COPY=1 (TEST ONLY): each old seat dir also gets a copy of its tape the erasure does not know about; the
//! disk scan after erasure must find it (the negative control of the disk check).
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
/// the whole local run's deadline
const DEADLINE_S: u64 = 3600;
const OLD_SET: [&str; 3] = ["c0", "c1", "c2"];
const NEW_SET: [&str; 3] = ["c3", "c4", "c5"];

fn common(d: usize, prof: &str) -> Common {
    common_mode(d, prof, false)
}

/// `self_mode`: a self-handover (the same seats, the MAC key retired): the new set is the old set.
fn common_mode(d: usize, prof: &str, self_mode: bool) -> Common {
    // the HE parameters by the profile's family (demo-x2, ledger-x2de, ...: the proof profile varies, the HE does not)
    let he: [&str; 3] = match prof.split('-').next() {
        Some("demo") => ["8192", "3", "118"],
        Some("ledger") => ["16384", "4", "175"],
        _ => panic!("profile: demo* or ledger*"),
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
        new_set: if self_mode { OLD_SET } else { NEW_SET }.iter().map(|s| s.to_string()).collect(),
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
    // re-authentication, one mask per matrix for the masked check, and the TEST-ONLY revealed entries
    for _ in 0..2 * d * d + 2 + 2 * CHECK {
        new.auth_plain();
    }
    for i in 0..3 {
        let od = work.join(format!("old{i}"));
        let nd = work.join(format!("new{i}"));
        std::fs::create_dir_all(&od).unwrap();
        std::fs::create_dir_all(&nd).unwrap();
        write_tape(&od.join("tape.bin"), &old.tapes[i]);
        // TEST ONLY negative control of the disk scan: a stray copy the erasure does not know about
        if std::env::var("DLH_STRAY_COPY").is_ok() {
            write_tape(&od.join("stray-copy.bin"), &old.tapes[i]);
            // MP-SPDZ's forms of the alpha share (Player-MAC-Keys decimal text; a Montgomery word at an odd offset)
            let al = old.tapes[i].alpha_i;
            std::fs::write(od.join("stray-mac-keys.txt"), format!("3\n{al}")).unwrap();
            let r64 = ((1u128 << 64) % c.t as u128) as u64;
            let mont = ((al as u128 * r64 as u128) % c.t as u128) as u64;
            let mut b = b"SPDZ gfp\0".to_vec();
            b.extend_from_slice(&mont.to_le_bytes());
            std::fs::write(od.join("stray-transactions.data"), b).unwrap();
        }
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
    let mut rep = side::old_side(&c, || old_setup(&c, work, i, d, base), || mesh(base, 6, 6, i))
        .unwrap_or_else(|e| json!({"role": "old", "party": i, "error": e}));
    rep["peak_rss_mb"] = json!(peak_rss_mb());
    write_json(&work.join(format!("pub/old{i}.json")), &rep);
}

#[inline(never)]
fn old_setup(c: &Common, work: &Path, i: usize, d: usize, base: u16) -> Box<OldCustodian> {
    let dir = work.join(format!("old{i}"));
    let tape = Box::new(read_tape(&dir.join("tape.bin")).expect("old tape"));
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
    let mut key = OwnKey::from_ceremony_secure(c.rns.clone(), &cust.s, reg.b_res(), reg.a_res());
    let mut m = os_field(c.rns.n, c.t);
    let ct = key.encrypt_exact(&m);
    let mdig = digest(&m);
    m.wipe();
    std::fs::write(work.join(format!("pub/old{i}.ct")), ct_bytes(&ct)).unwrap();
    std::fs::write(work.join(format!("pub/old{i}.ct.sha256")), &mdig).unwrap();
    let carry: BTreeMap<String, PcsParty> = KINDS
        .iter()
        .map(|k| {
            let mut plain: Vec<u64> = w[*k].iter().map(|x| x.s).collect();
            let mut pc = PcsParty::commit(&c.pr, &plain, &format!("{k}n"), i, &Det(None));
            pc.opened_lives = 1;
            plain.wipe();
            (k.to_string(), pc)
        })
        .collect();
    let roots: BTreeMap<String, Vec<[u8; 32]>> = carry.iter().map(|(k, p)| (k.clone(), vec![p.root])).collect();
    write_json(&work.join(format!("pub/old{i}.roots.json")), &roots_json(&roots));
    // the seat's epoch file key (in the kernel's persistent keyring on Linux) and its TLS key sealed under it
    let id = darkstep::tls::generate(i);
    let vname = darkhand::vault::key_name("dlh-local", i, 1, &darkstep::tls::cert_fingerprint(&id.cert_der));
    let vault = darkhand::vault::Vault::create(&vname, cfg!(target_os = "linux")).expect("vault");
    let tls = dir.join(format!("tls_{i}.key"));
    vault.seal_to(&tls, "tls", id.key_der.clone()).expect("sealed TLS key");
    drop(id);
    Box::new(OldCustodian {
        i,
        w,
        tape: *tape,
        keys: Some(side::HeSecret::from_ceremony(cust, &cer)),
        key: Some(key),
        carry,
        files: vec![dir.join("tape.bin"), dir.join("key.bin"), tls],
        scan_paths: vec![dir.clone()],
        captured: Some((ct, mdig)),
        vault: Some(vault),
        old_carries: None,
    })
}

/// One new custodian: the handover (its own ceremony at epoch 2, resharing, the joint proof, re-authentication);
/// custodian 0 submits the proof bytes to the ledger.
fn new(work: &Path, j: usize, d: usize, prof: &str, base: u16) {
    let c = common(d, prof);
    let dir = work.join(format!("new{j}"));
    let mut tape = read_tape(&dir.join("tape.bin")).expect("new tape");
    if j == 0 && std::env::var_os("DLH_CORRUPT_MAC").is_some() {
        // TEST ONLY: a wrong MAC share on new custodian 0's first auth_plain entry; the joint MAC check must fail
        tape.mac[0] = darkstep::arith::addmod(tape.mac[0], 1, c.t);
    }
    let net3 = mesh(base, 3, 3, j);
    let net6 = mesh(base, 6, 6, 3 + j);
    let out = match side::new_side(&c, j, net3, net6, tape, 2, CHECK, None) {
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
        std::fs::write(work.join("pub/handover.bin"), &out.proof).unwrap();
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
    let key = OwnKey::from_ceremony_secure(c.rns.clone(), &s, &zero_b, &zero_b);
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

/// The deployed old seat restarted after the handover (`restart-seat`): from the seat's own command line (dl-custodian
/// serve I N L F d D ... --tls T --tapes P --owner-msgs P --handover-at K), load everything the binary would load
/// from disk: its TLS key (needed to sign any TLS handshake), its checkpoint (its W shares and MAC shares), its
/// carried commitment, its tapes and owner messages of steps 0..=K. dl-custodian never writes the HE key to disk,
/// so the only key it can rebuild is from what these files hold: none of them holds a key, and the attempt uses the
/// zero key. It tries to decrypt the ciphertext it made under its old key just before the handover (from its
/// handover report) and each new seat's ciphertext under the new key (from their join reports).
fn restart_seat(out: &Path, handover_rep: &Path, joins: &[PathBuf], argv: &[String]) -> Value {
    use darkstep::node::flag;
    let i: usize = argv[1].parse().expect("serve I");
    let pf = darkstep::node::prof(&argv[2..6]);
    let dir = PathBuf::from(&argv[6]);
    let tls = PathBuf::from(flag(argv, "--tls").expect("--tls"));
    let k: usize = flag(argv, "--handover-at").expect("--handover-at K").parse().unwrap();
    // step_path reads --chunk-steps / --chunk-first from the args as serve does (the args include "serve")
    let mut a = vec!["dl-custodian".to_string()];
    a.extend_from_slice(argv);
    let k0: usize = flag(argv, "--chunk-first").map(|x| x.parse().unwrap()).unwrap_or(0);
    let mut present = Vec::new();
    let mut probe = |what: String, p: PathBuf| {
        let md = std::fs::metadata(&p).ok();
        present.push(json!({"what": what, "path": p.display().to_string(), "present": md.is_some(), "bytes": md.map(|m| m.len())}));
    };
    probe("TLS private key".into(), tls.join(format!("tls_{i}.key")));
    probe("checkpoint (W shares, MAC shares, alpha share)".into(), dir.join(format!("ckpt_P{i}.bin")));
    probe("checkpoint temp".into(), dir.join(format!("ckpt_P{i}.tmp")));
    probe("carried commitment".into(), dir.join(format!("carry_P{i}.bin")));
    for s in k0..=k {
        for (f, what) in [("--tapes", "tape"), ("--owner-msgs", "owner messages")] {
            if let Some(pat) = flag(argv, f) {
                probe(format!("{what} of step {s}"), PathBuf::from(darkstep::serve::step_path(&a, &pat, s)));
            }
        }
    }
    let ck = darkstep::serve::read_checkpoint(&dir.join(format!("ckpt_P{i}.bin")));
    let shares_loaded = ck.as_ref().map(|c| 2 * c.d * c.d).unwrap_or(0);
    let tls_key = std::fs::read(tls.join(format!("tls_{i}.key"))).ok();
    let tape = darkstep::serve::step_path(&a, &flag(argv, "--tapes").unwrap_or_default(), k);
    let tape_entries = std::fs::File::open(&tape).ok().and_then(|f| darkstep::tape::Tape::read_from(&mut std::io::BufReader::new(f)).ok()).map(|t| t.len()).unwrap_or(0);
    // the decryption attempts with the only key this seat can rebuild from disk
    let rns = Arc::new(Rns::new(pf.n, &pf.qs, pf.t));
    let zero_b: Vec<Vec<u64>> = rns.qs.iter().map(|_| vec![0u64; rns.n]).collect();
    let key = OwnKey::from_ceremony_secure(rns.clone(), &vec![0i64; rns.n], &zero_b, &zero_b);
    let mut tries = Vec::new();
    let h = read_json(handover_rep);
    let mut targets = vec![(format!("old seat {i}'s own ciphertext (before the handover)"), h["captured_ct"].clone(), h["captured_plain_sha256"].clone())];
    for (x, jp) in joins.iter().enumerate() {
        let r = read_json(jp);
        let r = if r.get("report").is_some() { r["report"].clone() } else { r };
        targets.push((format!("new seat {x}'s ciphertext ({})", jp.display()), r["ct_under_new_key"].clone(), r["ct_plain_sha256"].clone()));
    }
    for (name, ct, want) in targets {
        let ct = ct.as_str().map(hex_decode).and_then(|b| ct_parse(&b));
        let ok = ct.as_ref().map(|ct| Some(digest(&key.decrypt(ct, None))) == want.as_str().map(String::from));
        tries.push(json!({"ciphertext": name, "found": ct.is_some(), "decrypted": ok}));
    }
    let v = json!({"role": "old-restarted", "party": i, "files": present, "tls_key_loaded": tls_key.is_some(),
                   "share_entries_loaded": shares_loaded, "tape_entries_loaded": tape_entries,
                   "he_key_sources_on_disk": [], "decryption_attempts": tries});
    write_json(out, &v);
    v
}

/// `verify-rotation`: an independent native check of a ledger replica's rotation. The ledger up to the rotation is
/// replayed into a fresh file, then the rotation record is re-submitted with the handover proof bytes (native
/// verifier, darkproof::handover::verify via Ledger::rotate). Negative control: the same proof with one byte
/// flipped (at the middle) must be refused.
fn verify_rotation(ledger: &Path, proof: &Path, nlfd: &[String], profile: &str, work: &Path) -> Value {
    let pf = darkstep::node::prof(nlfd);
    darkproof::field::set_p(pf.t);
    let pr = Profile::by_name(profile).unwrap_or_else(|| panic!("profile {profile}"));
    let text = std::fs::read_to_string(ledger).expect("ledger");
    let lines: Vec<&str> = text.lines().collect();
    let at = lines.iter().position(|l| serde_json::from_str::<Value>(l).map(|v| v["kind"] == "rotate").unwrap_or(false)).expect("a rotate record");
    let rec: Value = serde_json::from_str(lines[at]).unwrap();
    let model = serde_json::from_str::<Value>(lines[0]).unwrap()["model"].as_str().unwrap().to_string();
    let blob = std::fs::read(proof).expect("handover proof");
    use sha2::Digest;
    let sha = pycompat::repr::hex(&sha2::Sha256::digest(&blob));
    let custodians: Vec<String> = rec["custodians"].as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect();
    let roots: BTreeMap<String, Vec<[u8; 32]>> = rec["roots"].as_object().unwrap().iter()
        .map(|(k, v)| (k.clone(), v.as_array().unwrap().iter().map(|h| darkproof::h::unhex32(h.as_str().unwrap()).unwrap()).collect()))
        .collect();
    let run = |name: &str, b: &[u8]| -> (Result<(), String>, f64) {
        let p = work.join(format!("{name}.jsonl"));
        let _ = std::fs::remove_file(&p);
        std::fs::write(&p, lines[..at].join("\n") + "\n").unwrap();
        let mut lg = Ledger::open(&p, &model, &pr, None).expect("replay up to the rotation");
        let t = std::time::Instant::now();
        let r = lg.rotate(&custodians, &roots, b);
        let r = r.and_then(|_| if lg.epoch == rec["epoch"].as_u64().unwrap() && lg.parent == roots { Ok(()) } else { Err("head after rotation differs".into()) });
        (r, t.elapsed().as_secs_f64())
    };
    let (ok, secs) = run("verify", &blob);
    let mut bad = blob.clone();
    let mid = bad.len() / 2;
    bad[mid] ^= 1;
    let (neg, _) = run("verify-flipped", &bad);
    json!({"ledger": ledger.display().to_string(), "proof": proof.display().to_string(), "proof_bytes": blob.len(),
           "proof_sha256_matches_record": rec["handover_proof"].as_str() == Some(sha.as_str()), "epoch": rec["epoch"],
           "accepted": ok.is_ok(), "error": ok.err(), "verify_seconds": secs,
           "flipped_byte_refused": neg.is_err(), "flipped_error": neg.err()})
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

/// One seat of a self-handover: keys from its (epoch-1) ceremony, kept; its old role reshares and erases its W
/// shares, tape and alpha share; its new role receives, re-authenticates under the new tape, and continues.
fn seat(work: &Path, i: usize, d: usize, prof: &str, base: u16) {
    let c = common_mode(d, prof, true);
    let dir = work.join(format!("old{i}"));
    let net3 = mesh(base, 0, 3, i);
    let (cust, cer) = darkhand::ceremony::run(&net3, i, c.rns.n, &c.rns.qs, c.t, c.pr.t_cols, 1).expect("ceremony");
    net3.shutdown();
    let reg = cer.registry(i).unwrap();
    let key = OwnKey::from_ceremony_secure(c.rns.clone(), &cust.s, reg.b_res(), reg.a_res());
    let new_tape = read_tape(&work.join(format!("new{i}/tape.bin"))).expect("new tape");
    let (rep_old, rep_new) = std::thread::scope(|s| {
        let c = &c;
        let dir = &dir;
        // 64 MiB stacks: the old role scrubs 4 MiB of its stack before its final scan
        let old_t = std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(s, move || {
            side::old_side(c, || old_seat_state(c, work, dir, i, d), || mesh(base, 6, 6, i))
                .unwrap_or_else(|e| json!({"role": "old", "party": i, "error": e}))
        }).unwrap();
        let new_t = std::thread::Builder::new().stack_size(64 << 20).spawn_scoped(s, move || {
            let net3 = mesh(base, 3, 3, i);
            let net6 = mesh(base, 6, 6, 3 + i);
            match side::new_side(c, i, net3, net6, new_tape, 1, CHECK, Some(key)) {
                Ok(out) => {
                    let mut rep = out.report.clone();
                    if i == 0 {
                        let lpath = work.join("ledger.jsonl");
                        wait_for(&lpath);
                        let mut lg = Ledger::open(&lpath, MODEL, &c.pr, None).expect("ledger");
                        let cust: Vec<String> = OLD_SET.iter().map(|s| s.to_string()).collect();
                        std::fs::write(work.join("pub/handover.bin"), &out.proof).unwrap();
                        rep["rotation"] = json!(match lg.rotate(&cust, &out.new_roots, &out.proof) {
                            Ok(()) => "accept".to_string(),
                            Err(e) => e,
                        });
                        rep["ledger_head_is_new_roots"] = json!(lg.head().1 == out.new_roots);
                        rep["ledger_custodians"] = json!(lg.custodians);
                    }
                    rep.as_object_mut().unwrap().remove("ct_under_new_key");
                    out.party.net.shutdown();
                    rep
                }
                Err(e) => json!({"role": "new", "party": i, "error": e}),
            }
        }).unwrap();
        (old_t.join().unwrap(), new_t.join().unwrap())
    });
    let mut rep_old = rep_old;
    rep_old["peak_rss_mb"] = json!(peak_rss_mb());
    write_json(&work.join(format!("pub/old{i}.json")), &rep_old);
    write_json(&work.join(format!("pub/new{i}.json")), &rep_new);
}

#[inline(never)]
fn old_seat_state(c: &Common, work: &Path, dir: &Path, i: usize, d: usize) -> Box<OldCustodian> {
    let tape = Box::new(read_tape(&dir.join("tape.bin")).expect("old tape"));
    let w: BTreeMap<String, Vec<Sh>> = KINDS
        .iter()
        .enumerate()
        .map(|(q, k)| (k.to_string(), (q * d * d..(q + 1) * d * d).map(|p| Sh { s: tape.sh[p], m: tape.mac[p] }).collect()))
        .collect();
    let carry: BTreeMap<String, PcsParty> = KINDS
        .iter()
        .map(|k| {
            let mut plain: Vec<u64> = w[*k].iter().map(|x| x.s).collect();
            let mut pc = PcsParty::commit(&c.pr, &plain, &format!("{k}n"), i, &Det(None));
            pc.opened_lives = 1;
            plain.wipe();
            (k.to_string(), pc)
        })
        .collect();
    let roots: BTreeMap<String, Vec<[u8; 32]>> = carry.iter().map(|(k, p)| (k.clone(), vec![p.root])).collect();
    write_json(&work.join(format!("pub/old{i}.roots.json")), &roots_json(&roots));
    Box::new(OldCustodian { i, w, tape: *tape, keys: None, key: None, carry, files: vec![dir.join("tape.bin")], scan_paths: vec![dir.to_path_buf()], captured: None, vault: None, old_carries: None })
}

fn local_self(work: &Path, d: usize, prof: &str, base: u16) -> bool {
    for sub in ["logs", "pids", "pub"] {
        std::fs::create_dir_all(work.join(sub)).unwrap();
    }
    let t0 = std::time::Instant::now();
    deal(work, d, prof);
    let ws = work.display().to_string();
    let mut kids: Vec<(String, std::process::Child)> = (0..3)
        .map(|i| {
            let a = ["seat", &ws, &i.to_string(), &d.to_string(), prof, &base.to_string()].map(String::from).to_vec();
            (format!("seat{i}"), spawn(work, &a, &format!("seat{i}")))
        })
        .collect();
    let c = common_mode(d, prof, true);
    make_ledger(work, &c, d);
    let exits = wait_all(work, &mut kids);
    let olds: Vec<Value> = (0..3).map(|i| read_json(&work.join(format!("pub/old{i}.json")))).collect();
    let news: Vec<Value> = (0..3).map(|j| read_json(&work.join(format!("pub/new{j}.json")))).collect();
    let truth = read_json(&work.join("truth.json"));
    let mut checks: Vec<(String, bool)> = Vec::new();
    let mut ck = |name: &str, ok: bool| checks.push((name.to_string(), ok));
    ck("all three seat processes exited 0", exits.values().all(|c| *c == Some(0)));
    let digests: Vec<&str> = olds.iter().chain(&news).map(|v| v["proof_sha256"].as_str().unwrap_or("")).collect();
    ck("both roles of every seat hold the same handover proof", !digests[0].is_empty() && digests.iter().all(|x| *x == digests[0]));
    ck("the ledger accepts the self-rotation (same custodians, epoch + 1)", news[0]["rotation"] == "accept");
    ck("the ledger head is the re-committed roots", news[0]["ledger_head_is_new_roots"] == true);
    ck("the ledger's custodian set is unchanged", news[0]["ledger_custodians"] == json!(OLD_SET));
    ck("MAC check under the NEW MAC key passes", news.iter().all(|v| v["mac_check"] == "ok"));
    ck("opened W1, W2 entries equal the plaintext W",
       news.iter().all(|v| v["opened"]["W1"] == truth["W1_head"] && v["opened"]["W2"] == truth["W2_head"]));
    ck("the new MAC key differs from the old", truth["alphas_differ"] == true);
    ck("the kept HE key still decrypts (each seat, own ciphertext)", news.iter().all(|v| v["decrypts_own_ct"] == true));
    ck("before erasure the scan finds the old shares, tape and alpha (control)",
       olds.iter().all(|v| v["scan_before_erasure"]["available"] == false || v["scan_before_erasure"]["hits"].as_u64().unwrap_or(0) > 0));
    ck("after erasure the scan finds none of them (the seat's process still runs its new role)",
       olds.iter().all(|v| v["scan_after_erasure"]["available"] == false || v["scan_after_erasure"]["hits"] == 0));
    ck("the memory scan ran (Linux)", olds.iter().all(|v| v["scan_after_erasure"]["available"] == true));
    ck("before erasure the disk scan finds the tape (and key) material in the state files (control)",
       olds.iter().all(|v| v["disk_scan_before_erasure"]["hits"].as_u64().unwrap_or(0) > 0));
    ck("after erasure the disk scan of the seat's directories finds none of it",
       olds.iter().all(|v| v["disk_scan_after_erasure"]["hits"] == 0 && v["disk_scan_after_erasure"]["unreadable"] == json!([])));
    ck("no old tape file left", olds.iter().all(|v| v["state_files_left"].as_array().map(|a| a.is_empty()).unwrap_or(false)));
    let all = checks.iter().all(|c| c.1);
    let summary = json!({
        "mode": "self-handover", "d": d, "profile": prof, "all_checks": all, "seconds": t0.elapsed().as_secs_f64(),
        "checks": checks.iter().map(|(n, ok)| json!({"check": n, "ok": ok})).collect::<Vec<_>>(),
        "exits": exits, "old": olds, "new": news,
    });
    write_json(&work.join("summary.json"), &summary);
    for (n, ok) in &checks {
        println!("{} {n}", if *ok { "ok  " } else { "FAIL" });
    }
    println!("all checks: {all}");
    all
}

/// The ledger, its head the old committee's commitment (the child of step k), from the roots the old custodians
/// publish.
fn make_ledger(work: &Path, c: &Common, d: usize) {
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
    let g = Genesis { d, program: darkproof::step::StepParams::HARNESS, owner_pk: None,
                      custodians: OLD_SET.iter().map(|s| s.to_string()).collect(), roots };
    let tmp = work.join("ledger.jsonl.tmp");
    drop(Ledger::open(&tmp, MODEL, &c.pr, Some(g)).expect("genesis"));
    std::fs::rename(&tmp, work.join("ledger.jsonl")).unwrap();
}

/// Wait for every child; if one fails or the run passes its deadline, stop the rest (the children this driver
/// started, by the PIDs it recorded for them) so nobody waits forever on a dead peer.
fn wait_all(work: &Path, kids: &mut [(String, std::process::Child)]) -> BTreeMap<String, Option<i32>> {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(DEADLINE_S);
    let mut exits: BTreeMap<String, Option<i32>> = BTreeMap::new();
    while exits.len() < kids.len() {
        let mut failed = false;
        for (name, k) in kids.iter_mut() {
            if exits.contains_key(name) {
                continue;
            }
            if let Some(st) = k.try_wait().unwrap() {
                exits.insert(name.clone(), st.code());
                let _ = std::fs::remove_file(work.join(format!("pids/{name}.pid")));
                failed |= st.code() != Some(0);
            }
        }
        if failed || std::time::Instant::now() > deadline {
            for (name, k) in kids.iter_mut() {
                if !exits.contains_key(name) {
                    let _ = k.kill();
                    let _ = k.wait();
                    exits.insert(name.clone(), None);
                    let _ = std::fs::remove_file(work.join(format!("pids/{name}.pid")));
                }
            }
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    exits
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
    let c = common(d, prof);
    make_ledger(work, &c, d);
    let exits = wait_all(work, &mut kids);
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
    ck("old: before erasure the disk scan finds the tape (and key) material in the state files (control)",
       olds.iter().all(|v| v["disk_scan_before_erasure"]["hits"].as_u64().unwrap_or(0) > 0));
    ck("old: after erasure the disk scan of the seat's directories finds none of it",
       olds.iter().all(|v| v["disk_scan_after_erasure"]["hits"] == 0 && v["disk_scan_after_erasure"]["unreadable"] == json!([])));
    ck("old: the sealed files open under the vault key before erasure (control)",
       olds.iter().all(|v| v["vault_before_erasure"]["sealed_copies_open_before_erasure"].as_array().is_some_and(|a| !a.is_empty() && a.iter().all(|t| t[2] == true))));
    ck("old: the vault key is invalidated and gone from the keyring (Linux) and memory",
       olds.iter().all(|v| v["vault_destroyed"]["invalidate_error"].is_null() && v["vault_destroyed"]["key_in_keyring_after"] == false
           && v["vault_after_erasure"]["key_in_keyring"] == false && v["vault_after_erasure"]["load_error"].is_string()
           && (cfg!(not(target_os = "linux")) || v["vault_destroyed"]["in_keyring"] == true)));
    ck("old: after erasure no key the seat holds opens a copy of its sealed files",
       olds.iter().all(|v| v["vault_after_erasure"]["sealed_copies"].as_array().is_some_and(|a| !a.is_empty()
           && a.iter().all(|t| t["opens_by_keyring"] == false && t["opens_by_zero_key"] == false))));
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
        Some("local-self") => {
            let ok = local_self(&work, arg(3).parse().unwrap(), &arg(4), arg(5).parse().unwrap());
            std::process::exit(if ok { 0 } else { 1 });
        }
        Some("seat") => seat(&work, arg(3).parse().unwrap(), arg(4).parse().unwrap(), &arg(5), arg(6).parse().unwrap()),
        Some("restart") => {
            let v = restart(&work, arg(3).parse().unwrap(), arg(4).parse().unwrap(), &arg(5));
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
        }
        Some("restart-seat") => {
            // dl-hand restart-seat OUT.json HANDOVER_P<I>.json [JOIN_P<J>.json ...] -- serve I N L F d D ...
            let dd = a.iter().position(|x| x == "--").expect("-- then the seat's serve arguments");
            let joins: Vec<PathBuf> = a[4..dd].iter().map(PathBuf::from).collect();
            let v = restart_seat(&work, Path::new(&arg(3)), &joins, &a[dd + 1..]);
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
        }
        Some("vault-present") => {
            // dl-hand vault-present NAME: whether the uid's persistent keyring still holds that file key (exit 0: absent)
            let name = arg(2);
            let present = darkhand::vault::present(&name);
            println!("{}", json!({"name": name, "present": present}));
            std::process::exit(if present { 1 } else { 0 });
        }
        Some("vault-open") => {
            // dl-hand vault-open NAME FILE...: try to open each sealed copy (role from its file name) with every key this uid can still get
            // (the keyring by NAME, the zero key); exit 0 when none opens and each file is a sealed one
            let name = arg(2);
            let role_of = |f: &Path| darkhand::side::vault_role(f);
            let load = darkhand::vault::Vault::load(&name);
            let zero = darkhand::vault::Vault::with_key(&name, [0u8; 32]);
            let mut all_closed = true;
            let mut rows = Vec::new();
            for f in &a[3..] {
                let fp = Path::new(f);
                let b = std::fs::read(fp).unwrap_or_default();
                let sealed = b.starts_with(darkhand::vault::MAGIC);
                let role = role_of(fp);
                let by_key = load.as_ref().map(|v| v.open(&role, b.clone()).is_ok()).unwrap_or(false);
                let by_zero = sealed && zero.open(&role, b.clone()).is_ok();
                all_closed &= sealed && !by_key && !by_zero;
                rows.push(json!({"file": f, "bytes": b.len(), "sealed": sealed, "role": role, "opens_by_keyring": by_key, "opens_by_zero_key": by_zero}));
            }
            println!("{}", json!({"name": name, "key_in_keyring": load.is_ok(), "load_error": load.err(), "files": rows, "none_opens": all_closed}));
            std::process::exit(if all_closed { 0 } else { 1 });
        }
        Some("verify-rotation") => {
            // dl-hand verify-rotation WORKDIR LEDGER.jsonl HANDOVER.bin N L F d [PROFILE]
            let v = verify_rotation(Path::new(&arg(3)), Path::new(&arg(4)), &a[5..9], a.get(9).map(|s| s.as_str()).unwrap_or("ledger"), &work);
            println!("{}", serde_json::to_string_pretty(&v).unwrap());
            std::process::exit(if v["accepted"] == true && v["flipped_byte_refused"] == true && v["proof_sha256_matches_record"] == true { 0 } else { 1 });
        }
        _ => {
            eprintln!("usage: see the header of darkhand/src/bin/dl-hand.rs");
            std::process::exit(2);
        }
    }
}
