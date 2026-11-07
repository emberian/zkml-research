//! A halted run under cut E (DEFER, profile ledger-x2de with RS): one proved step leaves the ledger's head pending;
//! `dl-custodian close` at each custodian proves the pending claims closed over the mesh and the replica records it
//! (one close bundle at all three). Control: a second close is refused, the head no longer pending.
//! Run one at a time (`-- --test-threads=1`).
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::step::Program;
use darkstep::tape::{Dealer, Tape};
use std::path::{Path, PathBuf};
use std::process::Command;

const A: [&str; 4] = ["16384", "4", "175", "64"];
const CFG: &[u8] = br#"{"d": 64, "hid": 64, "reps": 1, "tile": 0, "bias": false, "seed_init": 1, "a1": 0, "a2": 3}"#;

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn write_tape(t: &Tape, p: &Path) {
    t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(p).unwrap())).unwrap();
}

/// One launch of the three custodians for `steps` steps (and the owner as a thread); returns codes and stderr.
fn launch(base: &Path, ids: &[darkstep::tls::Identity], cs: &[Vec<u64>], steps: usize, extra: &[&str]) -> (Vec<i32>, Vec<String>) {
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let oid = darkstep::tls::Identity { key_der: ids[3].key_der.clone(), cert_der: ids[3].cert_der.clone() };
    let certs: Vec<Vec<u8>> = ids[..3].iter().map(|x| x.cert_der.clone()).collect();
    let cs = cs.to_vec();
    std::thread::spawn(move || darkstep::serve::owner_serve(l, &oid, &certs, |k, _| cs.get(k).cloned().ok_or("no step".into())));
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(own.join("D"))
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &steps.to_string(), "--gate", "309", "--ret-primes", "2"])
                .args(["--tapes", own.join(format!("tape_{i}_{{k}}.bin")).to_str().unwrap(), "--timeout", "60", "--prove", "--profile", "ledger-x2de", "--rs"])
                .args(["--genesis-cfg", base.join("genesis.json").to_str().unwrap()])
                .args(["--consumed-log", base.join(format!("consumed_box{}.jsonl", i.min(1))).to_str().unwrap()])
                .args(extra)
                .env("DS_THREADS", "4")
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    let outs: Vec<std::process::Output> = kids.into_iter().map(|k| k.wait_with_output().unwrap()).collect();
    (outs.iter().map(|o| o.status.code().unwrap_or(-1)).collect(), outs.iter().map(|o| String::from_utf8_lossy(&o.stderr).to_string()).collect())
}


fn close(base: &Path, ids: &[darkstep::tls::Identity]) -> (Vec<i32>, Vec<String>) {
    let ports: Vec<u16> = (0..3).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let _ = ids;
    let kids: Vec<_> = (0..3)
        .map(|i| {
            let own = base.join(format!("seat{i}"));
            Command::new(env!("CARGO_BIN_EXE_dl-custodian"))
                .args(["close", &i.to_string()])
                .args(A)
                .arg(own.join("D"))
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--profile", "ledger-x2de", "--timeout", "60"])
                .env("DS_THREADS", "4")
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    let outs: Vec<std::process::Output> = kids.into_iter().map(|k| k.wait_with_output().unwrap()).collect();
    (outs.iter().map(|o| o.status.code().unwrap_or(-1)).collect(), outs.iter().map(|o| String::from_utf8_lossy(&o.stderr).to_string()).collect())
}

#[test]
fn a_halted_run_closes_its_pending_head() {
    let pf = prof(&A.map(String::from));
    let base: PathBuf = std::env::temp_dir().join(format!("dl-close-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(&base).unwrap();
    std::fs::write(base.join("genesis.json"), CFG).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_dl-custodian")).arg("proof-triples").args(A).args(["--profile", "ledger-x2de", "--rs"]).output().unwrap();
    let c: usize = String::from_utf8(out.stdout).unwrap().trim().split_once(',').unwrap().1.parse().unwrap();
    let mut dl = Dealer::new(pf.t, 3, DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    dl.rs = true;
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut r = pycompat::PyRandom::from_u64(4000);
    let xm: Vec<u64> = (0..2 * pf.d).map(|_| darkstep::arith::from_i64(r.randint_i64(-7, 7), pf.t)).collect();
    let cs = vec![darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, &xm, &Program::HARNESS)];
    darkstep::tape::deal_proof_section(&mut dl, c);
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        std::fs::create_dir_all(own.join("D")).unwrap();
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        write_tape(&dl.tapes[i], &own.join(format!("tape_{i}_0.bin")));
    }
    let (codes, errs) = launch(&base, &ids, &cs, 1, &[]);
    assert_eq!(codes, vec![0, 0, 0], "one proved step under ledger-x2de: {errs:?}");
    let lg = std::fs::read_to_string(base.join("seat0/D/ledger_P0.jsonl")).unwrap();
    assert!(lg.contains("\"EXT\": 2") && lg.contains("\"RS\": true"), "the genesis pins x2 and RS: {}", lg.lines().next().unwrap());
    let (codes, errs) = close(&base, &ids);
    assert_eq!(codes, vec![0, 0, 0], "close: {errs:?}");
    let reps: Vec<serde_json::Value> = (0..3)
        .map(|i| serde_json::from_str(&std::fs::read_to_string(base.join(format!("seat{i}/D/close_P{i}.json"))).unwrap()).unwrap())
        .collect();
    for (i, r) in reps.iter().enumerate() {
        assert_eq!(r["ledger_closed"], true, "seat {i}");
        assert_eq!(r["close_sha256"], reps[0]["close_sha256"], "one close bundle");
        let lg = std::fs::read_to_string(base.join(format!("seat{i}/D/ledger_P{i}.jsonl"))).unwrap();
        assert!(lg.lines().count() >= 3, "seat {i}: genesis, step, close on the replica");
    }
    // control: the head is closed now, so a second close has nothing to close
    let (codes, errs) = close(&base, &ids);
    assert!(codes.iter().all(|&c| c != 0), "{codes:?}");
    assert!(errs.iter().all(|e| e.contains("not pending")), "{errs:?}");
    std::fs::remove_dir_all(&base).ok();
}
