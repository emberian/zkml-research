//! Exact truncation in the proved run (`dl-custodian serve --prove --rs --xt`; notes/dark-learning-gen6/xtrunc.md):
//! public genesis, two carried proved steps on one continuing XT tape (masks uniform in [0, p)), step 1's first mask
//! moved (with its MAC shares) so that its truncation opening is 0, in the wrap zone. Every custodian redoes step 1 on
//! its spare one-step tape (same dealer stream: the same MAC key, fresh masks; the owner answers the repeated request
//! with the spare's broadcasts), proves it, and the run continues: both steps are on every ledger replica (whose
//! genesis pins "XT": true) and the revealed weights equal the plaintext twin. Ledger profile, d = 64, gated T = 309.
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::{Plain, Program};
use darkstep::tape::{Tag, Tape};
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

#[test]
fn a_wrap_zone_step_is_redone_proved_and_the_run_continues() {
    let pf = prof(&A.map(String::from));
    let (p, d) = (pf.t, pf.d);
    let base = std::env::temp_dir().join(format!("dl-custodian-xt-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("run");
    std::fs::create_dir_all(&dir).unwrap();
    let cfg = br#"{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3}"#;
    let cfgp = base.join("genesis.json");
    std::fs::write(&cfgp, cfg).unwrap();
    let (_, w1, w2) = darkproof::run::public_weights(cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).arg("proof-triples").args(A).args(["--rs", "--xt"]).output().unwrap();
    let c: usize = String::from_utf8(out.stdout).unwrap().trim().split_once(',').unwrap().1.parse().unwrap();
    let xs: Vec<Vec<i64>> = (0..2)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(2000 + s as u64);
            (0..2 * d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let m = |v: &[i64]| -> Vec<u64> { v.iter().map(|&x| darkstep::arith::from_i64(x, p)).collect() };
    let mut dl = darkstep::tape::Dealer::new(p, 3, DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    dl.rs = true;
    dl.xt = true;
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = Vec::new();
    for x in &xs {
        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &m(x), &Program::HARNESS));
        darkstep::tape::deal_proof_section(&mut dl, c);
    }
    let fresh: Vec<Tape> = dl.alpha_sh.iter().map(|&a| Tape { alpha_i: a, ..Default::default() }).collect();
    let mut tapes = std::mem::replace(&mut dl.tapes, fresh);
    let spare_cs = darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &m(&xs[1]), &Program::HARNESS);
    darkstep::tape::deal_proof_section(&mut dl, c);
    // step 1's first mask: its opening z1[0] + 2^K1 + r, z1 from the twin's weights after step 0, moved to 0
    let rows = |w: &[i64]| -> Vec<Vec<i64>> { w.chunks(d).map(|r| r.to_vec()).collect() };
    let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
    let mut tw = Plain { w1: rows(&w1), w2: rows(&w2), x: xs[0][..d].to_vec(), y: xs[0][d..].to_vec() };
    let (a, b) = tw.step_prog(&pg).unwrap();
    tw.w1 = a;
    tw.w2 = b;
    let tr: Vec<usize> = tapes[0].tags.iter().enumerate().filter(|(_, &t)| t == Tag::Tr as u8).map(|(k, _)| k).collect();
    let at = tr[4 * d];
    let z1_0: i64 = (0..d).map(|j| tw.w1[0][j] * xs[1][j]).sum();
    let r: u64 = (0..3).fold(0u64, |a, i| darkstep::arith::addmod(a, tapes[i].sh[at], p));
    let c0 = darkstep::arith::addmod(darkstep::arith::addmod(darkstep::arith::from_i64(z1_0, p), 1 << Program::HARNESS.k1, p), r, p);
    assert!(c0 >= 1 << (Program::HARNESS.k1 + 1));
    tapes[0].sh[at] = darkstep::arith::submod(tapes[0].sh[at], c0, p);
    for i in 0..3 {
        tapes[i].mac[at] = darkstep::arith::submod(tapes[i].mac[at], darkstep::arith::mulmod(dl.alpha_sh[i], c0, p), p);
    }
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        std::fs::create_dir_all(&own).unwrap();
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &certs[j]).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        tapes[i].write_to(&mut std::io::BufWriter::new(std::fs::File::create(own.join("tape.bin")).unwrap())).unwrap();
        dl.tapes[i].write_to(&mut std::io::BufWriter::new(std::fs::File::create(own.join("spare_0.bin")).unwrap())).unwrap();
    }
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let ocerts = certs.clone();
    let owner = std::thread::spawn(move || {
        let mut asked = [0usize; 2];
        darkstep::serve::owner_serve(l, &oid, &ocerts, move |k, _| {
            asked[k] += 1;
            if k == 1 && asked[1] == 2 { Ok(spare_cs.clone()) } else { cs.get(k).cloned().ok_or("no step".into()) }
        })
    });
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(&dir)
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", "2", "--gate", "309", "--ret-primes", "2"])
                .args(["--tape", own.join("tape.bin").to_str().unwrap(), "--timeout", "120", "--test-keep-shares", "--prove", "--rs", "--xt"])
                .args(["--xt-spare-tapes", own.join("spare_{r}.bin").to_str().unwrap()])
                .args(["--genesis-cfg", cfgp.to_str().unwrap()])
                .env("DS_THREADS", "4")
                .spawn()
                .unwrap()
        })
        .collect();
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    assert_eq!(codes, vec![0, 0, 0], "every custodian completes (on failure the owner thread is left waiting)");
    let log = owner.join().unwrap().unwrap();
    assert_eq!(log.len(), 3, "step 0, step 1 and step 1's redo");
    for i in 0..3 {
        let r1: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join(format!("step_1_P{i}.json"))).unwrap()).unwrap();
        assert_eq!(r1["verdict"], "ACCEPT");
        assert!(r1["xt_redo"]["reason"].as_str().unwrap().starts_with(darkstep::party::XT_REDO), "custodian {i}: {}", r1["xt_redo"]);
        for k in 0..2 {
            let pr: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join(format!("proof_{k}_P{i}.json"))).unwrap()).unwrap();
            assert_eq!(pr["verified"], true, "step {k}, custodian {i}");
        }
        let lg = std::fs::read_to_string(dir.join(format!("ledger_P{i}.jsonl"))).unwrap();
        assert!(lg.lines().next().unwrap().contains("\"XT\": true"), "the genesis pins XT");
        assert_eq!(lg.matches("\"kind\": \"step\"").count(), 2);
    }
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap()).chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect())
        .collect();
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let sum: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    tw.x = xs[1][..d].to_vec();
    tw.y = xs[1][d..].to_vec();
    let (a, b) = tw.step_prog(&pg).unwrap();
    let twin: Vec<i64> = a.iter().chain(b.iter()).flatten().copied().collect();
    assert_eq!(sum, twin, "public genesis + 2 proved XT steps (one redone) = the twin");
    std::fs::remove_dir_all(&base).ok();
}
