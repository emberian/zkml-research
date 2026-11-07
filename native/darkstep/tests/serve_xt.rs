//! Exact truncation's redo in the multi-step custodians (`darkstep serve --xt`; notes/dark-learning-gen6/xtrunc.md):
//! step 1's first truncation mask is moved (with its MAC shares) so that its opening lands in the wrap zone. Every
//! custodian then redoes step 1 on a spare one-step tape under the SAME MAC key (fresh masks; the owner sends step 1's
//! inputs again under them), and the run continues on its tape: the three steps equal the plaintext twin. Without a
//! spare the custodians stop with code 5 (REDO, not a refusal; the checkpoint is at step 0) and the key is kept.
use darkstep::node::{prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::{inputs_for, Plain, Program};
use darkstep::tape::{deal_one_step, Dealer, Tag, Tape};
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
    spare_cs: Vec<u64>,
    later: Vec<Vec<i64>>,
}

fn twin(later: &[Vec<i64>], steps: usize) -> Plain {
    let pf = prof(&A.map(String::from));
    let mut pl = inputs_for(pf.d, &Program::HARNESS);
    let pg = Program { wmax: None, check_k: true, ..Program::HARNESS };
    for s in 0..steps {
        if s > 0 {
            pl.x = later[s - 1][..pf.d].to_vec();
            pl.y = later[s - 1][pf.d..].to_vec();
        }
        let (w1, w2) = pl.step_prog(&pg).unwrap();
        pl = Plain { w1, w2, x: pl.x, y: pl.y };
    }
    pl
}

fn setup(name: &str) -> Run {
    let pf = prof(&A.map(String::from));
    let (p, d) = (pf.t, pf.d);
    let base = std::env::temp_dir().join(format!("darkstep-serve-xt-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let (dir, tls) = (base.join("run"), base.join("tls"));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::create_dir_all(&tls).unwrap();
    let plain = inputs_for(d, &Program::HARNESS);
    let later: Vec<Vec<i64>> = (1..3)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(1000 + s as u64);
            (0..2 * d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let m = |v: &[i64]| -> Vec<u64> { v.iter().map(|&x| darkstep::arith::from_i64(x, p)).collect() };
    // one dealer stream (one alpha): steps 0, 1, 2 on the continuing tape, then the spare for step 1
    let mut dl = Dealer::new(p, 3, DEALER_SEED);
    dl.xt = true;
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let mut cs = vec![deal_one_step(&mut dl, &mut owner, d, &plain.flat_mod(p), &Program::HARNESS)];
    for v in &later {
        cs.push(deal_one_step(&mut dl, &mut owner, d, &m(v), &Program::HARNESS));
    }
    let fresh: Vec<Tape> = dl.alpha_sh.iter().map(|&a| Tape { alpha_i: a, ..Default::default() }).collect();
    let mut tapes = std::mem::replace(&mut dl.tapes, fresh);
    let spare_cs = deal_one_step(&mut dl, &mut owner, d, &m(&later[0]), &Program::HARNESS);
    // move step 1's first mask r by -c (c its honest opening z1[0] + 2^K1 + r, no wrap): the opening becomes 0
    let tr: Vec<usize> = tapes[0].tags.iter().enumerate().filter(|(_, &t)| t == Tag::Tr as u8).map(|(k, _)| k).collect();
    let at = tr[4 * d];
    let w0 = twin(&later, 1);
    let z1_0: i64 = (0..d).map(|j| w0.w1[0][j] * later[0][j]).sum();
    let r: u64 = (0..3).fold(0u64, |a, i| darkstep::arith::addmod(a, tapes[i].sh[at], p));
    let c = darkstep::arith::addmod(darkstep::arith::addmod(darkstep::arith::from_i64(z1_0, p), 1 << Program::HARNESS.k1, p), r, p);
    assert!(c >= 1 << (Program::HARNESS.k1 + 1), "the honest opening is outside the zone");
    tapes[0].sh[at] = darkstep::arith::submod(tapes[0].sh[at], c, p);
    for i in 0..3 {
        tapes[i].mac[at] = darkstep::arith::submod(tapes[i].mac[at], darkstep::arith::mulmod(dl.alpha_sh[i], c, p), p);
    }
    let write = |t: &Tape, f: PathBuf| t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(f).unwrap())).unwrap();
    for i in 0..3 {
        write(&tapes[i], dir.join(format!("tape_{i}.bin")));
        write(&dl.tapes[i], dir.join(format!("spare_0_{i}.bin")));
    }
    for seat in ["0", "1", "2", "owner"] {
        let st = Command::new(env!("CARGO_BIN_EXE_darkstep")).args(["tls-keygen", seat]).arg(&tls).output().unwrap();
        assert!(st.status.success());
    }
    Run { dir, tls, cs, spare_cs, later }
}

/// Serve 3 steps; the owner answers a repeated request for step 1 with the spare tape's broadcasts.
fn serve(r: &Run, extra: &[&str]) -> (Vec<i32>, usize) {
    let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
    let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
    let owner_at = format!("127.0.0.1:{}", ports[3]);
    let l = std::net::TcpListener::bind(&owner_at).unwrap();
    let id = darkstep::tls::Identity { key_der: std::fs::read(r.tls.join("tls_owner.key")).unwrap(), cert_der: std::fs::read(r.tls.join("cert_owner.der")).unwrap() };
    let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(r.tls.join(format!("cert_{j}.der"))).unwrap()).collect();
    let (cs, spare) = (r.cs.clone(), r.spare_cs.clone());
    let owner = std::thread::spawn(move || {
        let mut asked = vec![0usize; 3];
        darkstep::serve::owner_serve(l, &id, &certs, move |k, _| {
            asked[k] += 1;
            if k == 1 && asked[k] == 2 { Ok(spare.clone()) } else { cs.get(k).cloned().ok_or("no such step".into()) }
        })
    });
    let kids: Vec<_> = (0..3)
        .map(|i| {
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
                .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", "3", "--xt"])
                .args(["--tape", r.dir.join(format!("tape_{i}.bin")).to_str().unwrap(), "--timeout", "60", "--test-keep-shares"])
                .args(extra)
                .env("DS_THREADS", "4")
                .spawn()
                .unwrap()
        })
        .collect();
    let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
    let log = owner.join().unwrap().unwrap_or_default();
    (codes, log.len())
}

fn report(dir: &Path, k: usize, i: usize) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(dir.join(format!("step_{k}_P{i}.json"))).unwrap()).unwrap()
}

fn reveal(dir: &Path, d: usize, p: u64) -> (Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let shares: Vec<Vec<Sh>> = (0..3)
        .map(|i| darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap()).chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect())
        .collect();
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let sum: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |a, s| darkstep::arith::addmod(a, s[k].s, p)))).collect();
    let rows: Vec<Vec<i64>> = sum.chunks(d).map(|r| r.to_vec()).collect();
    (rows[..d].to_vec(), rows[d..].to_vec())
}

#[test]
fn a_wrap_zone_step_is_redone_on_a_spare_tape_and_the_run_continues() {
    let r = setup("spare");
    let pf = prof(&A.map(String::from));
    let spare = r.dir.join("spare_{r}_{i}.bin");
    let (codes, served) = serve(&r, &["--xt-spare-tapes", spare.to_str().unwrap()]);
    assert_eq!(codes, vec![0, 0, 0]);
    assert_eq!(served, 4, "steps 0, 1 (twice) and 2");
    for k in 0..3 {
        for i in 0..3 {
            assert_eq!(report(&r.dir, k, i)["verdict"], "ACCEPT", "step {k} party {i}");
        }
    }
    for i in 0..3 {
        let x = &report(&r.dir, 1, i)["xt_redo"];
        assert!(x["reason"].as_str().unwrap().starts_with(darkstep::party::XT_REDO), "party {i}: {x}");
        assert!(report(&r.dir, 0, i).get("xt_redo").is_none() && report(&r.dir, 2, i).get("xt_redo").is_none());
    }
    let t = twin(&r.later, 3);
    assert_eq!(reveal(&r.dir, pf.d, pf.t), (t.w1, t.w2), "the redone run equals the 3-step plaintext twin");
}

#[test]
fn without_a_spare_the_custodians_stop_for_a_redo_and_keep_the_key() {
    let r = setup("nospare");
    let (codes, served) = serve(&r, &[]);
    assert_eq!(codes, vec![5, 5, 5], "code 5: a redo, not a refusal (1)");
    assert_eq!(served, 2, "steps 0 and 1");
    for i in 0..3 {
        assert_eq!(report(&r.dir, 0, i)["verdict"], "ACCEPT");
        let v = report(&r.dir, 1, i);
        assert_eq!(v["verdict"], "REDO", "party {i}");
        let s: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(r.dir.join(format!("serve_P{i}.json"))).unwrap()).unwrap();
        assert_eq!(s["next_step"], 1, "the checkpoint is at the step before the redo");
    }
}


/// The run driver's redo (native/deploy/run.py, exit 5): per-step tape files; step 1's is forced into the wrap zone.
/// The custodians stop with code 5 at step 1; `serve --resume --steps 1` on step 1's fresh tape (a pattern keyed by
/// {k}, like rec's chunk paths) redoes it under the same key, and `serve --resume` on the normal pattern runs step 2:
/// the three steps equal the plaintext twin. This is the sequence run.py issues.
#[test]
fn exit_5_then_resume_on_a_fresh_step_tape_equals_the_twin() {
    let pf = prof(&A.map(String::from));
    let (p, d) = (pf.t, pf.d);
    let base = std::env::temp_dir().join(format!("darkstep-serve-xt-{}-resume", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let (dir, tls) = (base.join("run"), base.join("tls"));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::create_dir_all(&tls).unwrap();
    let plain = inputs_for(d, &Program::HARNESS);
    let later: Vec<Vec<i64>> = (1..3)
        .map(|s| {
            let mut r = pycompat::PyRandom::from_u64(1000 + s as u64);
            (0..2 * d).map(|_| r.randint_i64(-7, 7)).collect()
        })
        .collect();
    let m = |v: &[i64]| -> Vec<u64> { v.iter().map(|&x| darkstep::arith::from_i64(x, p)).collect() };
    let mut dl = Dealer::new(p, 3, DEALER_SEED);
    dl.xt = true;
    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
    let fresh = |dl: &Dealer| -> Vec<Tape> { dl.alpha_sh.iter().map(|&a| Tape { alpha_i: a, ..Default::default() }).collect() };
    let mut per_step: Vec<Vec<Tape>> = Vec::new();
    let mut cs = Vec::new();
    for k in 0..3 {
        let inp = if k == 0 { plain.flat_mod(p) } else { m(&later[k - 1]) };
        cs.push(deal_one_step(&mut dl, &mut owner, d, &inp, &Program::HARNESS));
        let f = fresh(&dl);
        per_step.push(std::mem::replace(&mut dl.tapes, f));
    }
    let spare_cs = deal_one_step(&mut dl, &mut owner, d, &m(&later[0]), &Program::HARNESS);
    // step 1's first mask moved so its opening is 0
    let at = per_step[1][0].tags.iter().position(|&t| t == Tag::Tr as u8).unwrap();
    let w0 = twin(&later, 1);
    let z1_0: i64 = (0..d).map(|j| w0.w1[0][j] * later[0][j]).sum();
    let r: u64 = (0..3).fold(0u64, |a, i| darkstep::arith::addmod(a, per_step[1][i].sh[at], p));
    let c = darkstep::arith::addmod(darkstep::arith::addmod(darkstep::arith::from_i64(z1_0, p), 1 << Program::HARNESS.k1, p), r, p);
    per_step[1][0].sh[at] = darkstep::arith::submod(per_step[1][0].sh[at], c, p);
    for i in 0..3 {
        per_step[1][i].mac[at] = darkstep::arith::submod(per_step[1][i].mac[at], darkstep::arith::mulmod(dl.alpha_sh[i], c, p), p);
    }
    let write = |t: &Tape, f: PathBuf| t.write_to(&mut std::io::BufWriter::new(std::fs::File::create(f).unwrap())).unwrap();
    for i in 0..3 {
        for k in 0..3 {
            write(&per_step[k][i], dir.join(format!("step_{k}_{i}.bin")));
        }
        write(&dl.tapes[i], dir.join(format!("xs_1_{i}.bin")));
    }
    for seat in ["0", "1", "2", "owner"] {
        assert!(Command::new(env!("CARGO_BIN_EXE_darkstep")).args(["tls-keygen", seat]).arg(&tls).output().unwrap().status.success());
    }
    let run = |steps: usize, pat: &str, owner_vals: Vec<Option<Vec<u64>>>, resume: bool| -> Vec<i32> {
        let ports: Vec<u16> = (0..4).map(|_| free_port()).collect();
        let addrs: Vec<String> = (0..3).map(|j| format!("127.0.0.1:{}", ports[j])).collect();
        let owner_at = format!("127.0.0.1:{}", ports[3]);
        let l = std::net::TcpListener::bind(&owner_at).unwrap();
        let id = darkstep::tls::Identity { key_der: std::fs::read(tls.join("tls_owner.key")).unwrap(), cert_der: std::fs::read(tls.join("cert_owner.der")).unwrap() };
        let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(tls.join(format!("cert_{j}.der"))).unwrap()).collect();
        let ow = std::thread::spawn(move || darkstep::serve::owner_serve(l, &id, &certs, move |k, _| owner_vals.get(k).cloned().flatten().ok_or("no such step".into())));
        let kids: Vec<_> = (0..3)
            .map(|i| {
                let own = base.join(format!("tls_seat{i}"));
                std::fs::create_dir_all(&own).unwrap();
                for f in ["cert_0.der", "cert_1.der", "cert_2.der", "cert_owner.der"] {
                    std::fs::copy(tls.join(f), own.join(f)).unwrap();
                }
                std::fs::copy(tls.join(format!("tls_{i}.key")), own.join(format!("tls_{i}.key"))).unwrap();
                Command::new(env!("CARGO_BIN_EXE_darkstep"))
                    .args(["serve", &i.to_string()])
                    .args(A)
                    .arg(&dir)
                    .args(&addrs)
                    .args(["--tls", own.to_str().unwrap(), "--owner", &owner_at, "--steps", &steps.to_string(), "--xt"])
                    .args(["--tapes", dir.join(pat.replace("{i}", &i.to_string())).to_str().unwrap(), "--timeout", "60", "--test-keep-shares"])
                    .args(if resume { vec!["--resume"] } else { vec![] })
                    .env("DS_THREADS", "4")
                    .spawn()
                    .unwrap()
            })
            .collect();
        let codes: Vec<i32> = kids.into_iter().map(|mut k| k.wait().unwrap().code().unwrap_or(-1)).collect();
        if codes.iter().all(|&c| c != 2) {
            ow.join().unwrap().unwrap();
        }
        codes
    };
    let normal: Vec<Option<Vec<u64>>> = cs.iter().cloned().map(Some).collect();
    assert_eq!(run(3, "step_{k}_{i}.bin", normal.clone(), false), vec![5, 5, 5], "the wrap at step 1: a redo");
    for i in 0..3 {
        assert_eq!(report(&dir, 1, i)["verdict"], "REDO");
    }
    let redo = vec![None, Some(spare_cs.clone())];
    assert_eq!(run(1, "xs_{k}_{i}.bin", redo, true), vec![0, 0, 0], "step 1 redone on its fresh tape");
    for i in 0..3 {
        assert_eq!(report(&dir, 1, i)["verdict"], "ACCEPT");
    }
    assert_eq!(run(1, "step_{k}_{i}.bin", normal, true), vec![0, 0, 0], "step 2 on the normal pattern");
    let t = twin(&later, 3);
    assert_eq!(reveal(&dir, d, p), (t.w1, t.w2), "exit 5, the redo resume and the next resume = the 3-step twin");
}
