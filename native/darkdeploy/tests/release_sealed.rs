//! The release from a sealed release tape (prep's DLVAULT2, Linux: the kernel keyring), alone after the last step's
//! checkpoint: one proved step under `--vault` (ledger profile, d = 64, public genesis); each seat's release tape
//! sealed in 1 MiB-block form under its own epoch file key with the role "tape|rel|0" (as prep writes them); then
//! `serve --resume --steps 0 --release`: no step tape is loaded, the release tape is opened under the key, claimed
//! in the box's registry (its sha256 as on disk), used, and wiped (--wipe-spent). C equals the plaintext count over
//! the revealed head. Control: the tapes restored byte for byte are refused by the registry (single use). Run one at a
//! time (`-- --test-threads=1`).
#![cfg(target_os = "linux")]
use darkstep::node::prof;
use darkstep::party::Sh;
use std::path::Path;
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn seal_v2(name: &str, plain: &Path, out: &Path, role: &str) {
    let v = darkhand::vault::Vault::load(name).unwrap();
    let key = dlvault::Key::new(name, v.key_bytes());
    let b = std::fs::read(plain).unwrap();
    // small blocks: many of them from a small tape
    let mut w = dlvault::Writer::create_bs(out, &key, role, b.len() as u64, 1 << 12).unwrap();
    w.write_at(0, &b).unwrap();
    w.finish().unwrap();
}

/// One launch of the three seats; the owner serves `cs` for step 0 only.
fn launch(base: &Path, ids: &[darkstep::tls::Identity], cs: &[u64], extra: &dyn Fn(usize) -> Vec<String>) -> Vec<(i32, String)> {
    let exe = env!("CARGO_BIN_EXE_dl-custodian");
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let cs = cs.to_vec();
    std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &certs, |k, _| if k == 0 { Ok(cs.clone()) } else { Err("no step".into()) }));
    let dir = base.join("run");
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(exe)
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(&dir)
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--gate", "309", "--ret-primes", "2"])
                .args(["--tape", own.join(format!("tape_{i}.bin")).to_str().unwrap(), "--timeout", "120", "--test-keep-shares", "--prove", "--vault"])
                .args(["--genesis-cfg", base.join("genesis.json").to_str().unwrap()])
                .args(["--consumed-log", base.join(format!("consumed_{i}.jsonl")).to_str().unwrap()])
                .args(extra(i))
                .env("DS_THREADS", "4")
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    kids.into_iter()
        .map(|k| {
            let o = k.wait_with_output().unwrap();
            (o.status.code().unwrap_or(-1), String::from_utf8_lossy(&o.stderr).to_string())
        })
        .collect()
}

#[test]
fn the_release_alone_from_a_sealed_tape_after_the_checkpoint() {
    let pf = prof(&A.map(String::from));
    let (d, p) = (pf.d, pf.t);
    // DL_MNIST: the dataset's dir on a box (the workspace there is the native tree alone)
    let mnist = std::env::var("DL_MNIST").map(std::path::PathBuf::from).unwrap_or_else(|_| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../research/dark_learning_2026_11_06/data/mnist"));
    let base = std::env::temp_dir().join(format!("dl-release-sealed-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(base.join("run")).unwrap();
    let cfg = format!(
        r#"{{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3, "data": "{}", "seed_order": 2, "release": {{"M": 8}}}}"#,
        mnist.display()
    );
    let cfgp = base.join("genesis.json");
    std::fs::write(&cfgp, &cfg).unwrap();
    let exe = env!("CARGO_BIN_EXE_dl-custodian");
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    let mut names = vec![];
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        let mut c = Command::new(exe);
        c.args(["test-deal", cfgp.to_str().unwrap(), "1", &i.to_string(), own.to_str().unwrap(), "--genesis-cfg", cfgp.to_str().unwrap(), "--release", "--split-release"]);
        if i == 1 {
            c.arg("--public");
        }
        assert!(c.status().unwrap().success(), "test-deal {i}");
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        let o = Command::new(exe).args(["vault-init", &i.to_string(), own.to_str().unwrap()]).output().unwrap();
        assert!(o.status.success(), "vault-init: {}", String::from_utf8_lossy(&o.stderr));
        let n = std::fs::read_to_string(own.join("vault.name")).unwrap();
        // the release tape as prep seals it: CHUNK/step-0/tape_I.bin, role tape|CHUNK|0; the plain copy removed
        let sd = own.join("rel/step-0");
        std::fs::create_dir_all(&sd).unwrap();
        seal_v2(&n, &own.join(format!("release_{i}.bin")), &sd.join(format!("tape_{i}.bin")), "tape|rel|0");
        assert!(dlvault::is_sealed(&sd.join(format!("tape_{i}.bin"))));
        std::fs::remove_file(own.join(format!("release_{i}.bin"))).unwrap();
        names.push(n);
    }
    let cs = darkstep::net::bytes_to_u64s(&std::fs::read(base.join("seat1").join("public_step0.bin")).unwrap());
    let dir = base.join("run");
    // the step, proved; no release
    let r = launch(&base, &ids, &cs, &|_| vec!["--steps".into(), "1".into()]);
    assert!(r.iter().all(|x| x.0 == 0), "{r:?}");
    let rel = |i: usize| base.join(format!("seat{i}/rel/step-0/tape_{i}.bin")).to_str().unwrap().to_string();
    let release_only = |i: usize| -> Vec<String> {
        ["--resume", "--steps", "0", "--release", "--release-data", mnist.to_str().unwrap(), "--release-tape", &rel(i), "--wipe-spent"].iter().map(|s| s.to_string()).collect()
    };
    // a copy of each sealed release tape, for the control below
    for i in 0..3 {
        std::fs::copy(rel(i), format!("{}.copy", rel(i))).unwrap();
    }
    let r = launch(&base, &ids, &cs, &release_only);
    assert!(r.iter().all(|x| x.0 == 0), "the release alone: {r:?}");
    for i in 0..3 {
        assert!(!Path::new(&rel(i)).exists(), "custodian {i}: --wipe-spent wiped the spent release tape");
    }
    let reps: Vec<serde_json::Value> =
        (0..3).map(|i| serde_json::from_str(&std::fs::read_to_string(dir.join(format!("release_P{i}.json"))).unwrap()).unwrap()).collect();
    for (i, r) in reps.iter().enumerate() {
        assert!(r.get("error").is_none(), "custodian {i}: {r}");
        assert_eq!(r["C"], reps[0]["C"], "one C");
        assert_eq!(r["proof_sha256"], reps[0]["proof_sha256"], "one release bundle");
        assert_eq!(r["ledger_accepted"], true);
        let log = std::fs::read_to_string(base.join(format!("consumed_{i}.jsonl"))).unwrap();
        assert!(log.contains(&rel(i)), "custodian {i}: the sealed release tape is claimed in the registry");
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
    for (i, r) in reps.iter().enumerate() {
        assert_eq!(r["wiped"][0][1], "ok", "custodian {i}: {r}");
    }
    // control: the same release tapes again (restored byte for byte) are refused (single use)
    for i in 0..3 {
        std::fs::rename(format!("{}.copy", rel(i)), rel(i)).unwrap();
    }
    let r = launch(&base, &ids, &cs, &release_only);
    for i in 0..3 {
        let rep: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join(format!("release_P{i}.json"))).unwrap()).unwrap();
        let e = rep["error"].as_str().unwrap_or("");
        assert!(r[i].0 != 0 || e.contains("already consumed"), "custodian {i}: a second release on the same tape: {:?} {rep}", r[i]);
        assert!(e.contains("already consumed") || r[i].1.contains("already consumed"), "custodian {i}: refused as consumed: {} {rep}", r[i].1);
    }
    for n in names {
        darkhand::vault::Vault::load(&n).unwrap().destroy();
    }
    std::fs::remove_dir_all(&base).ok();
}
