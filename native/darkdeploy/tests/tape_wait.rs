//! A late chunk: with `--tape-wait S` the three custodians agree on CTRL to wait while any one's next-step chunk is
//! incomplete on its box (no `chunk-P<I>.json` yet, which darkprep writes last), and go on when it is; past S they
//! all stop together. Ledger profile, d = 64, gated T = 309, public genesis, tapes in prep's chunk layout
//! (`ch{c}/step-{j}/tape_I.bin`, one step per chunk). Run one at a time (`-- --test-threads=1`).
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
                .args(["--tapes", own.join(format!("ch{{c}}/step-{{j}}/tape_{i}.bin")).to_str().unwrap(), "--chunk-steps", "1", "--timeout", "30"])
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


/// Seat dirs under `base` with step 0's and step 1's tapes in chunks ch0 and ch1; ch0 complete, ch1 without its marker.
fn prepare(base: &Path) -> (Vec<darkstep::tls::Identity>, Vec<Vec<u64>>) {
    let pf = prof(&A.map(String::from));
    let _ = std::fs::remove_dir_all(base);
    std::fs::create_dir_all(base).unwrap();
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
        for j in 0..3 {
            std::fs::create_dir_all(&own).unwrap();
            std::fs::write(own.join(format!("cert_{j}.der")), &ids[j].cert_der).unwrap();
        }
        std::fs::write(own.join("cert_owner.der"), &ids[3].cert_der).unwrap();
        std::fs::write(own.join(format!("tls_{i}.key")), &ids[i].key_der).unwrap();
        for (s, ts) in tapes.iter().enumerate() {
            let sd = own.join(format!("ch{s}/step-0"));
            std::fs::create_dir_all(&sd).unwrap();
            write_tape(&ts[i], &sd.join(format!("tape_{i}.bin")));
        }
        std::fs::write(own.join(format!("ch0/chunk-P{i}.json")), b"{}").unwrap();
    }
    (ids, cs)
}

fn serve_json(base: &Path, i: usize) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(base.join(format!("seat{i}/D/serve_P{i}.json"))).unwrap()).unwrap()
}

#[test]
fn the_committee_waits_for_a_late_chunk_and_goes_on() {
    let base: PathBuf = std::env::temp_dir().join(format!("dl-tape-wait-{}", std::process::id()));
    let (ids, cs) = prepare(&base);
    // seat 2's chunk 1 completes 30 s in, the others' at once: all three must wait for seat 2's
    for i in 0..2 {
        std::fs::write(base.join(format!("seat{i}/ch1/chunk-P{i}.json")), b"{}").unwrap();
    }
    let late = base.join("seat2/ch1/chunk-P2.json");
    let w = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_secs(30));
        std::fs::write(late, b"{}").unwrap();
    });
    let (codes, errs) = launch(&base, &ids, &cs, 2, &["--tape-wait", "300"]);
    w.join().unwrap();
    assert_eq!(codes, vec![0, 0, 0], "{errs:?}");
    for i in 0..3 {
        let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(base.join(format!("seat{i}/D/step_1_P{i}.json"))).unwrap()).unwrap();
        assert_eq!(r["verdict"], "ACCEPT", "seat {i}");
        let w = serve_json(&base, i)["tape_wait_seconds"].as_f64().unwrap();
        assert!(w >= 20.0, "seat {i} waited {w} s, though seat 2's chunk was late");
    }
    std::fs::remove_dir_all(&base).ok();
}

#[test]
fn past_the_wait_all_three_stop_together() {
    let base: PathBuf = std::env::temp_dir().join(format!("dl-tape-wait-x-{}", std::process::id()));
    let (ids, cs) = prepare(&base);
    // only seat 1's chunk 1 never completes
    for i in [0, 2] {
        std::fs::write(base.join(format!("seat{i}/ch1/chunk-P{i}.json")), b"{}").unwrap();
    }
    let (codes, errs) = launch(&base, &ids, &cs, 2, &["--tape-wait", "20"]);
    assert_eq!(codes, vec![1, 1, 1], "{errs:?}");
    for (i, e) in errs.iter().enumerate() {
        assert!(e.contains("preprocessing not ready at [0, 1, 0]"), "seat {i}: {e}");
        assert_eq!(serve_json(&base, i)["next_step"], 1, "seat {i} ran step 0 only");
    }
    // step 1's tape was never loaded, so it is not in the registry: it stays usable
    let reg = std::fs::read_to_string(base.join("consumed_box1.jsonl")).unwrap();
    assert_eq!(reg.lines().count(), 2, "box 1 recorded step 0's two tapes only");
    std::fs::remove_dir_all(&base).ok();
}
