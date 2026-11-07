//! Preprocessing is single-use, enforced: each custodian records every tape it loads in the box's registry
//! (`--consumed-log`); a second start on a consumed tape is refused before any step, while a resume onto the next
//! step's (fresh) tape goes on. Ledger profile, d = 64, gated T = 309, public genesis, per-step tape files.
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
                .args(["--tapes", own.join(format!("tape_{i}_{{k}}.bin")).to_str().unwrap(), "--timeout", "30"])
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

#[test]
fn a_consumed_tape_is_refused_and_a_resume_goes_on() {
    let pf = prof(&A.map(String::from));
    let base: PathBuf = std::env::temp_dir().join(format!("dl-single-use-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    std::fs::create_dir_all(&base).unwrap();
    std::fs::write(base.join("genesis.json"), CFG).unwrap();
    let mut dl = Dealer::new(pf.t, 3, DEALER_SEED);
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = vec![];
    let mut tapes: Vec<Vec<Tape>> = vec![];
    for s in 0..2 {
        let mut r = pycompat::PyRandom::from_u64(4000 + s);
        let xm: Vec<u64> = (0..2 * pf.d).map(|_| darkstep::arith::from_i64(r.randint_i64(-7, 7), pf.t)).collect();
        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, &xm, &Program::HARNESS));
        tapes.push(dl.tapes.clone());
        for t in dl.tapes.iter_mut() {
            *t = Tape { alpha_i: t.alpha_i, ..Default::default() };
        }
    }
    let ids: Vec<darkstep::tls::Identity> = (0..4).map(darkstep::tls::generate).collect();
    for i in 0..3 {
        let own = base.join(format!("seat{i}"));
        std::fs::create_dir_all(&own).unwrap();
        for j in 0..3 {
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        for (s, ts) in tapes.iter().enumerate() {
            write_tape(&ts[i], &own.join(format!("tape_{i}_{s}.bin")));
        }
    }
    // step 0
    let (codes, _) = launch(&base, &ids, &cs, 1, &[]);
    assert_eq!(codes, vec![0, 0, 0], "the first use of step 0's tapes");
    let reg = std::fs::read_to_string(base.join("consumed_box1.jsonl")).unwrap();
    assert_eq!(reg.lines().count(), 2, "seats 1 and 2 share a box registry: two tapes recorded");
    // a fresh start on step 0's tapes again: refused before any step, by every custodian
    let (codes, errs) = launch(&base, &ids, &cs, 1, &[]);
    assert!(codes.iter().all(|&c| c != 0), "a second use is refused: {codes:?}");
    for (i, e) in errs.iter().enumerate() {
        assert!(e.contains("preprocessing already consumed"), "custodian {i}: {e}");
    }
    // control: --resume goes on to step 1, whose tapes are fresh
    let (codes, errs) = launch(&base, &ids, &cs, 1, &["--resume"]);
    assert_eq!(codes, vec![0, 0, 0], "resume onto fresh tapes: {errs:?}");
    let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(base.join("seat0/D/step_1_P0.json")).unwrap()).unwrap();
    assert_eq!(r["verdict"], "ACCEPT");
    std::fs::remove_dir_all(&base).ok();
}
