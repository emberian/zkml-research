//! Three `dl-custodian serve --prove` processes over pinned TLS, the owner a thread: every step is proved inside
//! the custodians (tag PROOF on the same mesh), all three hold the same bundle, and each verifies it against the
//! chain (genesis roots, then every accepted step's child roots). The revealed weights (test only) equal the
//! plaintext twin. Ledger profile (N = 16384, L = 4, F = 175), d = 64, gated T = 309, 3 steps.
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::{inputs_for, Plain, Program};
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];

// Run these one at a time (`-- --test-threads=1`): each starts three processes on freshly picked free ports.

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

#[test]
fn three_proved_steps_over_tls() {
    let pf = prof(&A.map(String::from));
    let d = pf.d;
    let steps = 3;
    let base = std::env::temp_dir().join(format!("dl-custodian-prove-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("run");
    std::fs::create_dir_all(&dir).unwrap();
    // proof section sizes from the binary itself
    let out = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).arg("proof-triples").args(A).output().unwrap();
    let gc = String::from_utf8(out.stdout).unwrap();
    let (g, c) = gc.trim().split_once(',').unwrap();
    let (g, c): (usize, usize) = (g.parse().unwrap(), c.parse().unwrap());
    let plain = inputs_for(d, &Program::HARNESS);
    let later: Vec<Vec<i64>> = (1..steps)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(1000 + s as u64);
            (0..2 * d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let mut dl = darkstep::tape::Dealer::new(pf.t, 3, DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = vec![darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &plain.flat_mod(pf.t), &Program::HARNESS)];
    darkstep::tape::deal_proof_section(&mut dl, g);
    for xs in &later {
        let xm: Vec<u64> = xs.iter().map(|&x| darkstep::arith::from_i64(x, pf.t)).collect();
        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &xm, &Program::HARNESS));
        darkstep::tape::deal_proof_section(&mut dl, c);
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
        dl.tapes[i].write_to(&mut std::io::BufWriter::new(std::fs::File::create(own.join("tape.bin")).unwrap())).unwrap();
    }
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let ocerts = certs.clone();
    let owner = std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &ocerts, |k, _| cs.get(k).cloned().ok_or("no step".into())));
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(&dir)
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &steps.to_string(), "--gate", "309", "--ret-primes", "2"])
                .args(["--tape", own.join("tape.bin").to_str().unwrap(), "--timeout", "120", "--test-keep-shares", "--prove"])
                .args(if i == 0 { vec!["--proof-archive".to_string(), base.join("archive").to_str().unwrap().to_string()] } else { vec![] })
                .env("DS_THREADS", "4")
                .spawn()
                .unwrap()
        })
        .collect();
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    owner.join().unwrap().unwrap();
    assert_eq!(codes, vec![0, 0, 0]);
    for k in 0..steps {
        let reps: Vec<serde_json::Value> = (0..3)
            .map(|i| serde_json::from_str(&std::fs::read_to_string(dir.join(format!("step_{k}_P{i}.json"))).unwrap()).unwrap())
            .collect();
        for r in &reps {
            assert_eq!(r["verdict"], "ACCEPT", "step {k}");
            assert_eq!(r["after_step"]["verified"], true, "step {k}: the bundle verifies against the chain");
            assert_eq!(r["after_step"]["proof_sha256"], reps[0]["after_step"]["proof_sha256"], "step {k}: one bundle");
        }
        let b0 = std::fs::read(base.join("archive").join(format!("proof_e0_s{}.bin", k + 1))).unwrap();
        // control: a flipped byte in the bundle is refused by the verifier
        if k == 0 {
            let mut bad = b0.clone();
            let m = bad.len() / 2;
            bad[m] ^= 1;
            darkproof::field::set_p(pf.t);
            let pr = darkproof::Profile::ledger();
            let roots_json: std::collections::BTreeMap<String, Vec<String>> =
                serde_json::from_str(&std::fs::read_to_string(dir.join("genesis_roots.json")).unwrap()).unwrap();
            let roots = roots_json
                .into_iter()
                .map(|(k, v)| (k, v.iter().map(|h| { let b = hex(h); let mut a = [0u8; 32]; a.copy_from_slice(&b); a }).collect()))
                .collect();
            let prm = darkproof::step::StepParams { rc: true, lb: true, ..darkproof::step::StepParams::HARNESS }.deployed();
            let ok = darkproof::wire::verify_step(&pr, &pr.ligero(), &b0, &darkproof::Ctx::new("dl-gen6", 0, 1), &roots, &darkproof::step::tables(), d, prm, None, 0);
            assert!(ok.is_ok(), "the stored bundle verifies: {:?}", ok.err());
            let refused = darkproof::wire::verify_step(&pr, &pr.ligero(), &bad, &darkproof::Ctx::new("dl-gen6", 0, 1), &roots, &darkproof::step::tables(), d, prm, None, 0);
            assert!(refused.is_err(), "a flipped byte is refused");
        }
    }
    // test-only reveal against the plaintext twin
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| {
            let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
            v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect()
        })
        .collect();
    let p = pf.t;
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let sum: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    let mut pl = plain;
    let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
    for s in 0..steps {
        if s > 0 {
            pl.x = later[s - 1][..d].to_vec();
            pl.y = later[s - 1][d..].to_vec();
        }
        let (w1, w2) = pl.step_prog(&pg).unwrap();
        pl = Plain { w1, w2, x: pl.x, y: pl.y };
    }
    let twin: Vec<i64> = pl.w1.iter().chain(pl.w2.iter()).flatten().copied().collect();
    assert_eq!(sum, twin, "revealed weights after {steps} proved steps = plaintext twin");
    std::fs::remove_dir_all(&base).ok();
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

/// Public genesis with proofs: W = darktrain::init(cfg) enters custody as the public constant, every custodian
/// commits it itself (the program pins sha256 of the cfg), and two proved carried steps chain from that commitment.
#[test]
fn public_genesis_two_proved_steps() {
    public_genesis_steps(false);
}

/// The same with --pipeline-proofs: the proof of step k on its own mesh beside step k + 1.
#[test]
fn public_genesis_pipelined_proofs() {
    public_genesis_steps(true);
}

/// Pipelined, and the run split in two processes per custodian (the second with --resume).
#[test]
fn public_genesis_pipelined_resume() {
    public_genesis_steps_mode(true, true);
}

fn public_genesis_steps(pipelined: bool) {
    public_genesis_steps_mode(pipelined, false);
}

fn public_genesis_steps_mode(pipelined: bool, split: bool) {
    let pf = prof(&A.map(String::from));
    let d = pf.d;
    let steps = 2;
    let base = std::env::temp_dir().join(format!("dl-custodian-pg{}{}-{}", pipelined as u8, split as u8, std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("run");
    std::fs::create_dir_all(&dir).unwrap();
    let cfg = br#"{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3}"#;
    let cfgp = base.join("genesis.json");
    std::fs::write(&cfgp, cfg).unwrap();
    let (_, w1, w2) = darkproof::run::public_weights(cfg).unwrap();
    assert!(w2.iter().any(|&x| x != 0), "a nontrivial public W");
    let out = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).arg("proof-triples").args(A).output().unwrap();
    let gc = String::from_utf8(out.stdout).unwrap();
    let c: usize = gc.trim().split_once(',').unwrap().1.parse().unwrap();
    let xs: Vec<Vec<i64>> = (0..steps)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(2000 + s as u64);
            (0..2 * d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let mut dl = darkstep::tape::Dealer::new(pf.t, 3, DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = Vec::new();
    for x in &xs {
        let xm: Vec<u64> = x.iter().map(|&v| darkstep::arith::from_i64(v, pf.t)).collect();
        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &xm, &Program::HARNESS));
        darkstep::tape::deal_proof_section(&mut dl, c);
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
        dl.tapes[i].write_to(&mut std::io::BufWriter::new(std::fs::File::create(own.join("tape.bin")).unwrap())).unwrap();
    }
    // split: one step, then a fresh process per custodian with --resume for the second (the carry checkpoint and
    // the ledger replica carry the proof chain across)
    let parts: Vec<(usize, bool)> = if split { vec![(1, false), (steps - 1, true)] } else { vec![(steps, false)] };
    let mut codes = vec![];
    for (n, resume) in parts {
        let ports: Vec<u16> = (0..7).map(|_| free_port()).collect();
        let pmesh: Vec<String> = (4..7).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
        let pmesh = pmesh.join(",");
        let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
        let owner_at = format!("127.0.0.1:{}", ports[3]);
        let l = std::net::TcpListener::bind(&owner_at).unwrap();
        let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
        let ocerts = certs.clone();
        let cs = cs.clone();
        let owner = std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &ocerts, |k, _| cs.get(k).cloned().ok_or("no step".into())));
        let kids: Vec<_> = (0..3)
            .map(|i| {
                let own = base.join(format!("seat{i}"));
                Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                    .args(["serve", &i.to_string()])
                    .args(A)
                    .arg(&dir)
                    .args(&addrs)
                    .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &n.to_string(), "--gate", "309", "--ret-primes", "2"])
                    .args(["--tape", own.join("tape.bin").to_str().unwrap(), "--timeout", "120", "--test-keep-shares", "--prove"])
                    .args(if i == 0 { vec!["--proof-archive".to_string(), base.join("archive").to_str().unwrap().to_string()] } else { vec![] })
                    .args(["--genesis-cfg", cfgp.to_str().unwrap()])
                    .args(if pipelined { vec!["--pipeline-proofs", "--proof-mesh", &pmesh] } else { vec![] })
                    .args(if resume { vec!["--resume"] } else { vec![] })
                    .env("DS_THREADS", "4")
                    .spawn()
                    .unwrap()
            })
            .collect();
        codes = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
        assert_eq!(codes, vec![0, 0, 0], "part of {n} step(s), resume {resume}");
        owner.join().unwrap().unwrap();
    }
    assert_eq!(codes, vec![0, 0, 0]);
    for k in 0..steps {
        let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join(format!("step_{k}_P0.json"))).unwrap()).unwrap();
        assert_eq!(r["verdict"], "ACCEPT");
        for i in 0..3 {
            // every custodian's own proof report (written by the proof, inline or in the worker)
            let p: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join(format!("proof_{k}_P{i}.json"))).unwrap()).unwrap();
            assert_eq!(p["verified"], true, "step {k}, custodian {i}: accepted by its ledger replica (public-genesis chain)");
            assert_eq!(p["ledger_step"], k + 1);
        }
        if pipelined {
            assert_eq!(r["after_step"]["pipelined"], true);
            if k > 0 && !split {
                assert_eq!(r["after_step"]["proof_of_previous_step"]["serve_step"], k - 1, "step {k} reports step {}'s proof", k - 1);
            }
        }
    }
    for i in 0..3 {
        let lg = std::fs::read_to_string(dir.join(format!("ledger_P{i}.jsonl"))).unwrap();
        assert_eq!(lg.matches("\"kind\": \"step\"").count(), steps, "custodian {i}: {steps} steps on its ledger replica");
    }
    // the plaintext twin from the same cfg
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| {
            let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
            v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect()
        })
        .collect();
    let p = pf.t;
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let sum: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    let rows = |w: &[i64]| -> Vec<Vec<i64>> { w.chunks(d).map(|r| r.to_vec()).collect() };
    let mut pl = Plain { w1: rows(&w1), w2: rows(&w2), x: vec![], y: vec![] };
    let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
    for x in &xs {
        pl.x = x[..d].to_vec();
        pl.y = x[d..].to_vec();
        let (a, b) = pl.step_prog(&pg).unwrap();
        pl.w1 = a;
        pl.w2 = b;
    }
    let twin: Vec<i64> = pl.w1.iter().chain(pl.w2.iter()).flatten().copied().collect();
    assert_eq!(sum, twin, "public genesis + 2 proved steps = the twin from the same cfg");
    std::fs::remove_dir_all(&base).ok();
}
