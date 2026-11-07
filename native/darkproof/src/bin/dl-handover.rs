//! dl-handover bench <d> <demo|ledger>: one custody handover at width d with secret randomness: the old committee's
//! carried child (one life spent), resharing to a new committee of three, its fresh commitment, the six-party native
//! prover (in-process mesh, one thread per party), the encoder and the native verifier. Prints one JSON line.
use darkproof::handover::{self, HandoverCtx};
use darkproof::net::mem_mesh;
use darkproof::pcs::PcsParty;
use darkproof::rng::{secret_rng, Det};
use darkproof::{field, Profile};
use std::collections::BTreeMap;
use std::time::Instant;

fn rss_mb() -> f64 {
    let mut u: libc_rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(0, &mut u) };
    // ru_maxrss: KiB on Linux, bytes on macOS
    if cfg!(target_os = "macos") { u.ru_maxrss as f64 / 1048576.0 } else { u.ru_maxrss as f64 / 1024.0 }
}
#[repr(C)]
struct libc_rusage {
    ru_utime: [i64; 2],
    ru_stime: [i64; 2],
    ru_maxrss: i64,
    rest: [i64; 13],
}
extern "C" {
    fn getrusage(who: i32, usage: *mut libc_rusage) -> i32;
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 4 || a[1] != "bench" {
        eprintln!("usage: dl-handover bench <d> <demo|ledger>");
        std::process::exit(2);
    }
    let d: usize = a[2].parse().unwrap();
    let pr = Profile::by_name(&a[3]).expect("profile");
    // the profile's field (the BFV plaintext modulus of its HE parameters), before any LigParams
    field::set_p(if pr.name == "ledger" { field::P_LEDGER } else { field::P_DEMO });
    let lp = pr.ligero();
    let det = Det(None);
    let t0 = Instant::now();
    let mut r = secret_rng();
    let old: BTreeMap<String, Vec<Vec<u64>>> = ["W1", "W2"]
        .iter()
        .map(|k| (k.to_string(), (0..3).map(|_| (0..d * d).map(|_| r.randrange_u64(field::p())).collect()).collect()))
        .collect();
    let mut rs: Vec<_> = (0..3).map(|_| secret_rng()).collect();
    let tr = Instant::now();
    let new: BTreeMap<String, Vec<Vec<u64>>> =
        old.iter().map(|(k, v)| (k.clone(), handover::reshare(v, 3, &mut rs).1)).collect();
    let reshare_s = tr.elapsed().as_secs_f64();
    let ctx = HandoverCtx {
        model: "mind-h".into(),
        epoch_old: 0,
        epoch_new: 1,
        after_step: 1,
        old_set: vec!["c0".into(), "c1".into(), "c2".into()],
        new_set: vec!["c3".into(), "c4".into(), "c5".into()],
    };
    // the old committee's parts (in a run these already exist: the step's child) and the new committee's (the
    // handover's own cost), each three parties in parallel
    let commit = |old_side: bool| -> Vec<BTreeMap<String, PcsParty>> {
        std::thread::scope(|s| {
            let hs: Vec<_> = (0..3)
                .map(|i| {
                    let (pr, old, new, det) = (&pr, &old, &new, &det);
                    s.spawn(move || {
                        ["W1", "W2"]
                            .iter()
                            .map(|k| {
                                let c = if old_side {
                                    let mut c = PcsParty::commit(pr, &old[*k][i], &format!("{k}n"), i, det);
                                    c.opened_lives = 1;
                                    c
                                } else {
                                    PcsParty::commit(pr, &new[*k][i], k, i, det)
                                };
                                (k.to_string(), c)
                            })
                            .collect()
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        })
    };
    let tc = Instant::now();
    let mut parts = commit(true);
    let commit_old_s = tc.elapsed().as_secs_f64();
    let tc = Instant::now();
    parts.extend(commit(false));
    let commit_new_s = tc.elapsed().as_secs_f64();
    let tp = Instant::now();
    let nets = mem_mesh(6);
    let outs: Vec<_> = std::thread::scope(|s| {
        let hs: Vec<_> = nets
            .into_iter()
            .zip(parts)
            .map(|(mut net, mut mine)| {
                let (pr, lp, ctx, det) = (&pr, &lp, &ctx, &det);
                s.spawn(move || {
                    let p = handover::prove(pr, lp, d, 3, 3, ctx, &mut mine, &mut net, det).unwrap();
                    (p, net_sent(&net))
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let prove_s = tp.elapsed().as_secs_f64();
    let te = Instant::now();
    let blob = handover::encode(&pr, d, &outs[0].0);
    let encode_s = te.elapsed().as_secs_f64();
    let tv = Instant::now();
    let nr = handover::verify(&pr, &lp, d, 3, 3, &ctx, &outs[0].0.old_roots, &blob).expect("verifier accepts");
    let verify_s = tv.elapsed().as_secs_f64();
    assert_eq!(nr, outs[0].0.new_roots);
    assert_eq!(blob.len(), handover::byte_len(&pr, d, 3, 3));
    let sent: Vec<u64> = outs.iter().map(|o| o.1).collect();
    println!(
        "{{\"d\": {d}, \"profile\": \"{}\", \"bytes\": {}, \"reshare_s\": {reshare_s:.2}, \"commit_old_s\": {commit_old_s:.2}, \"commit_new_s\": {commit_new_s:.2}, \"prove_s\": {prove_s:.2}, \"encode_s\": {encode_s:.2}, \"verify_s\": {verify_s:.2}, \"elements_sent_per_party\": {:?}, \"peak_rss_mb\": {:.0}, \"total_s\": {:.1}, \"threads\": {}}}",
        pr.name,
        blob.len(),
        sent,
        rss_mb(),
        t0.elapsed().as_secs_f64(),
        rayon::current_num_threads()
    );
}

fn net_sent(n: &darkproof::net::MemNet) -> u64 {
    use darkproof::net::Net;
    n.sent()
}
