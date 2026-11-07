//! The multi-step custodians (`darkstep serve`, three processes) over pinned TLS with the owner (owner_serve, a
//! thread here): weights carried as shares across steps, checkpoints, pause and resume. The revealed weights
//! (test-only) must equal the plaintext twin (step_spec iterated over the same inputs).
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::{inputs_for, Plain, Program};
use std::path::{Path, PathBuf};
use std::process::Command;

const A: [&str; 4] = ["4096", "3", "118", "64"];

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

struct Run {
    dir: PathBuf,
    tls: PathBuf,
    cs: Vec<Vec<u64>>,
    later: Vec<Vec<i64>>,
}

fn setup(name: &str, k: usize) -> Run {
    let pf = prof(&A.map(String::from));
    let base = std::env::temp_dir().join(format!("darkstep-serve-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let (dir, tls) = (base.join("run"), base.join("tls"));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::create_dir_all(&tls).unwrap();
    let plain = inputs_for(pf.d, &Program::HARNESS);
    let later: Vec<Vec<i64>> = (1..k)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(1000 + s as u64);
            (0..2 * pf.d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let later_mod: Vec<Vec<u64>> = later.iter().map(|v| v.iter().map(|&x| darkstep::arith::from_i64(x, pf.t)).collect()).collect();
    let (tapes, cs) = darkstep::tape::deal_steps_prog(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t), &later_mod, false, &Program::HARNESS);
    for (i, tp) in tapes.iter().enumerate() {
        tp.write_to(&mut std::io::BufWriter::new(std::fs::File::create(dir.join(format!("tape_{i}.bin"))).unwrap())).unwrap();
    }
    for seat in ["0", "1", "2", "owner"] {
        let st = Command::new(env!("CARGO_BIN_EXE_darkstep")).args(["tls-keygen", seat]).arg(&tls).output().unwrap();
        assert!(st.status.success());
    }
    Run { dir, tls, cs, later }
}

/// Serve `steps` steps from the run's state; returns the three exit codes and the owner's log.
fn serve(r: &Run, steps: usize, first: usize, extra: &[&str]) -> (Vec<i32>, Vec<serde_json::Value>) {
    serve_env(r, steps, first, extra, None)
}

fn serve_env(r: &Run, steps: usize, first: usize, extra: &[&str], env1: Option<(&str, &str)>) -> (Vec<i32>, Vec<serde_json::Value>) {
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let id = darkstep::tls::Identity {
        key_der: std::fs::read(r.tls.join("tls_owner.key")).unwrap(),
        cert_der: std::fs::read(r.tls.join("cert_owner.der")).unwrap(),
    };
    let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(r.tls.join(format!("cert_{j}.der"))).unwrap()).collect();
    let cs = r.cs.clone();
    let owner = std::thread::spawn(move || darkstep::serve::owner_serve(l, &id, &certs, |k, _| cs.get(k).cloned().ok_or("no such step".into())));
    let kids: Vec<_> = (0..3)
        .map(|i| {
            // each custodian sees only its own key; certificates are public
            let own = r.dir.parent().unwrap().join(format!("tls_seat{i}"));
            std::fs::create_dir_all(&own).unwrap();
            for f in ["cert_0.der", "cert_1.der", "cert_2.der", "cert_owner.der"] {
                std::fs::copy(r.tls.join(f), own.join(f)).unwrap();
            }
            std::fs::copy(r.tls.join(format!("tls_{i}.key")), own.join(format!("tls_{i}.key"))).unwrap();
            Command::new(env!("CARGO_BIN_EXE_darkstep"))
                .args(["serve", &i.to_string()])
                .args(A)
                .arg(&r.dir)
                .args(&addrs)
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &steps.to_string(), "--gate", "309"])
                .args(["--tape", r.dir.join(format!("tape_{i}.bin")).to_str().unwrap(), "--timeout", "60", "--test-keep-shares"])
                .args(extra)
                .env("DS_THREADS", "4")
                .envs(env1.filter(|_| i == 1))
                .env("DS_RECONNECT_SECS", "30")
                .spawn()
                .unwrap()
        })
        .collect();
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    let log = owner.join().unwrap().unwrap_or_default();
    let _ = first;
    (codes, log)
}

fn reveal(dir: &Path, d: usize, p: u64) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| {
            let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
            v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect()
        })
        .collect();
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let sum: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    let rows: Vec<Vec<i64>> = sum.chunks(d).map(|r| r.to_vec()).collect();
    (rows[..d].to_vec(), rows[d..].to_vec())
}

fn twin(r: &Run, steps: usize) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let pf = prof(&A.map(String::from));
    let mut pl = inputs_for(pf.d, &Program::HARNESS);
    for s in 0..steps {
        if s > 0 {
            pl.x = r.later[s - 1][..pf.d].to_vec();
            pl.y = r.later[s - 1][pf.d..].to_vec();
        }
        // the HARNESS program with its |W| <= 7 entry assertion lifted (carried weights grow past it); the
        // truncation bounds are then asserted instead, so a step outside the protocol's precondition fails here
        let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
        let (w1, w2) = pl.step_prog(&pg).unwrap();
        pl = Plain { w1, w2, x: pl.x, y: pl.y };
    }
    (pl.w1, pl.w2)
}

fn report(dir: &Path, k: usize, i: usize) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(dir.join(format!("step_{k}_P{i}.json"))).unwrap()).unwrap()
}

#[test]
fn three_steps_carried_as_shares_equal_the_plaintext_twin() {
    let r = setup("straight", 3);
    let pf = prof(&A.map(String::from));
    let (codes, log) = serve(&r, 3, 0, &[]);
    assert_eq!(codes, vec![0, 0, 0]);
    assert_eq!(log.len(), 3);
    for k in 0..3 {
        let reps: Vec<_> = (0..3).map(|i| report(&r.dir, k, i)).collect();
        for v in &reps {
            assert_eq!(v["verdict"], "ACCEPT", "step {k}");
            assert_eq!(v["transcript"], reps[0]["transcript"], "step {k}: the custodians agree");
            assert!(v["gate"]["prove_seconds"].as_f64().unwrap() > 0.0, "gated");
        }
    }
    // genesis opens 2d^2 + 2d inputs, carried steps 2d (the weights are not input again)
    assert!(report(&r.dir, 0, 0)["transcript_len"].as_u64().unwrap() > report(&r.dir, 1, 0)["transcript_len"].as_u64().unwrap() + (2 * 64 * 64 - 10) as u64);
    let got = reveal(&r.dir, pf.d, pf.t);
    assert_eq!(got, twin(&r, 3), "revealed weights after 3 steps = plaintext twin");
    assert_ne!(got, twin(&r, 2), "control: not the 2-step twin");
}

#[test]
fn pause_checkpoint_and_resume_equal_the_straight_run() {
    let r = setup("resume", 3);
    let pf = prof(&A.map(String::from));
    let (codes, _) = serve(&r, 2, 0, &[]);
    assert_eq!(codes, vec![0, 0, 0]);
    // a pause window covering every minute: all three stop at the next boundary with code 3
    let (codes, log) = serve(&r, 1, 2, &["--resume", "--pause-utc", "00:00-23:59"]);
    let now = (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() / 60) % 1440;
    if now < 1439 {
        assert_eq!(codes, vec![3, 3, 3], "paused");
        assert!(log.is_empty());
    }
    let (codes, _) = serve(&r, 1, 2, &["--resume"]);
    assert_eq!(codes, vec![0, 0, 0]);
    assert_eq!(report(&r.dir, 2, 0)["verdict"], "ACCEPT");
    assert_eq!(reveal(&r.dir, pf.d, pf.t), twin(&r, 3), "2 steps + resume 1 = the 3-step twin");
}

/// Custodian 1's link to custodian 0 is cut mid-step (after 1 MB sent, inside the HE matvec): the link resumes under
/// the same pinned identities and the steps still equal the plaintext twin.
#[test]
fn a_link_cut_mid_step_resumes_and_the_steps_equal_the_twin() {
    let r = setup("cut", 2);
    let pf = prof(&A.map(String::from));
    let (codes, _) = serve_env(&r, 2, 0, &[], Some(("DS_TEST_KILL", "0,1000000")));
    assert_eq!(codes, vec![0, 0, 0]);
    let rep = report(&r.dir, 0, 1);
    assert!(rep["reconnects"][0].as_u64().unwrap() >= 1, "the link was resumed: {}", rep["reconnects"]);
    assert_eq!(reveal(&r.dir, pf.d, pf.t), twin(&r, 2));
}

/// The same cut during a check phase (the first Freivalds opening) aborts the step for all three.
#[test]
fn a_link_cut_in_a_check_phase_aborts() {
    let r = setup("cutcheck", 1);
    let (codes, log) = serve_env(&r, 1, 0, &["--timeout", "20"], Some(("DS_TEST_KILL", "0,critical")));
    assert!(codes.iter().all(|&c| c != 0), "every custodian stops: {codes:?}");
    assert!(log.len() <= 1);
    let reps: Vec<String> = (0..3).filter_map(|i| std::fs::read_to_string(r.dir.join(format!("step_0_P{i}.json"))).ok()).collect();
    assert!(reps.iter().all(|t| !t.contains("\"ACCEPT\"")), "no custodian accepted the step");
}
