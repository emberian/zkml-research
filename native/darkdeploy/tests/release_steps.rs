//! The mind's release inside `dl-custodian` processes (ledger profile, d = 64, gated T = 309, public genesis): one
//! proved step on the test dealer's tapes (`dl-custodian test-deal`, one seat's tape per call), then `--release`:
//! release_custodian over the head's shares, its proof, and each custodian's ledger replica accepting it. Only C is
//! opened; it equals the plaintext count over the (test-only) revealed head, and the ledger records it.
//! Run one at a time (`-- --test-threads=1`).
use darkstep::node::prof;
use darkstep::party::Sh;
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

#[test]
fn release_after_one_proved_step() {
    release_run(false);
}

/// As in a deployment: the release's preprocessing is its own tape (`--release-tape`), read only when the release
/// starts, after the steps' tape is freed.
#[test]
fn release_from_its_own_tape() {
    release_run(true);
}

fn release_run(split: bool) {
    let pf = prof(&A.map(String::from));
    let (d, p) = (pf.d, pf.t);
    let mnist = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../research/dark_learning_2026_11_06/data/mnist");
    let base = std::env::temp_dir().join(format!("dl-release-{}-{split}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(base.join("run")).unwrap();
    let cfg = format!(
        r#"{{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3, "data": "{}", "seed_order": 2, "release": {{"M": 8}}}}"#,
        mnist.display()
    );
    let cfgp = base.join("genesis.json");
    std::fs::write(&cfgp, &cfg).unwrap();
    let exe = env!("CARGO_BIN_EXE_dl-custodian");
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        let mut c = Command::new(exe);
        c.args(["test-deal", cfgp.to_str().unwrap(), "1", &i.to_string(), own.to_str().unwrap(), "--genesis-cfg", cfgp.to_str().unwrap(), "--release"]);
        if i == 1 {
            c.arg("--public");
        }
        if split {
            c.arg("--split-release");
        }
        assert!(c.status().unwrap().success(), "test-deal {i}");
    }
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &certs[j]).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
    }
    let cs = darkstep::net::bytes_to_u64s(&std::fs::read(base.join("seat1").join("public_step0.bin")).unwrap());
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let ocerts = certs.clone();
    let owner = std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &ocerts, |k, _| if k == 0 { Ok(cs.clone()) } else { Err("no step".into()) }));
    let dir = base.join("run");
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            let mut c = Command::new(exe);
            c.args(["serve", &i.to_string()])
                .args(A)
                .arg(&dir)
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", "1", "--gate", "309", "--ret-primes", "2"])
                .args(["--tape", own.join(format!("tape_{i}.bin")).to_str().unwrap(), "--timeout", "120", "--test-keep-shares", "--prove"])
                .args(["--genesis-cfg", cfgp.to_str().unwrap(), "--release", "--release-data", mnist.to_str().unwrap()])
                .env("DS_THREADS", "4");
            if split {
                let r = own.join(format!("release_{i}.bin"));
                assert!(r.exists(), "the release's own tape");
                c.args(["--release-tape", r.to_str().unwrap()]);
            }
            c.spawn().unwrap()
        })
        .collect();
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    assert_eq!(codes, vec![0, 0, 0]);
    owner.join().unwrap().unwrap();
    let reps: Vec<serde_json::Value> =
        (0..3).map(|i| serde_json::from_str(&std::fs::read_to_string(dir.join(format!("release_P{i}.json"))).unwrap()).unwrap()).collect();
    for (i, r) in reps.iter().enumerate() {
        assert_eq!(r["M"], 8, "custodian {i}: the cfg's pinned M");
        assert_eq!(r["C"], reps[0]["C"], "one C");
        assert_eq!(r["proof_sha256"], reps[0]["proof_sha256"], "one release bundle");
        assert_eq!(r["ledger_accepted"], true);
        let lg = std::fs::read_to_string(dir.join(format!("ledger_P{i}.jsonl"))).unwrap();
        assert!(lg.contains("\"kind\": \"release\""), "custodian {i}: the release is on its ledger");
    }
    // the plaintext count over the revealed head (test only)
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| {
            let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
            v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect()
        })
        .collect();
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let w: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    let rows = |w: &[i64]| -> Vec<Vec<i64>> { w.chunks(d).map(|r| r.to_vec()).collect() };
    darkproof::field::set_p(p);
    let pol = darkproof::run::mnist_policy(cfg.as_bytes(), &mnist, 8).unwrap();
    let xi: Vec<Vec<i64>> = (0..d).map(|k| (0..8).map(|t| cen(pol.x[k * 8 + t])).collect()).collect();
    let prm = darkproof::step::StepParams { rc: true, lb: true, ..darkproof::step::StepParams::HARNESS }.deployed();
    let c = darkproof::run::plain_count(&rows(&w[..d * d]), &rows(&w[d * d..]), &xi, &pol.labels, prm, pol.ncls, pol.kc);
    assert_eq!(reps[0]["C"], c, "the released C is the plaintext count over the head");
    std::fs::remove_dir_all(&base).ok();
}
