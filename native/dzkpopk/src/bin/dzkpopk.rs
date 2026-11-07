//! dzkpopk CLI: bit-exact vectors against the harness, cross-verification, benchmarks.
//!
//!   DL_DETERMINISTIC=<seed> dzkpopk vectors N L M T OUTDIR [kinds]  # the harness's instances; prove; nat_<kind>.bin
//!   dzkpopk verify N L M T KIND PROOF                                # verify a (Python) proof
//!   DL_DETERMINISTIC=<seed> dzkpopk ceremony N L T                   # the 3-custodian ceremony, digests
//!   dzkpopk bench KIND N L M S T [reps]                              # M sk cts with S forward-layout slots each
//!   dzkpopk counts N L T                                             # proof bytes per batch shape (formula)

use dzkpopk::canon::Json;
use dzkpopk::gen::{encrypt_pk, encrypt_sk, keygen};
use dzkpopk::vectors::{ctx, instances, params};
use dzkpopk::*;
use pycompat::PyRandom;
use std::sync::Arc;
use std::time::Instant;

fn sha_hex(b: &[u8]) -> String {
    pycompat::repr::sha256_hex(b)
}

fn arg<T: std::str::FromStr>(a: &[String], i: usize) -> T
where
    T::Err: std::fmt::Debug,
{
    a[i].parse().unwrap()
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    #[cfg(feature = "test-det")]
    let det = std::env::var("DL_DETERMINISTIC").ok();
    #[cfg(not(feature = "test-det"))]
    if std::env::var("DL_DETERMINISTIC").is_ok() {
        eprintln!("DL_DETERMINISTIC needs a build with --features test-det");
        std::process::exit(2);
    }
    match a.get(1).map(|s| s.as_str()) {
        Some("vectors") => {
            let (n, l, m, t): (usize, usize, usize, usize) = (arg(&a, 2), arg(&a, 3), arg(&a, 4), arg(&a, 5));
            let out = &a[6];
            let kinds: Vec<String> = a.get(7).map(|s| s.split(',').map(String::from).collect()).unwrap_or(vec!["sk".into(), "pk".into(), "key".into()]);
            let mut res = vec![];
            for (kind, st, wit) in instances(n, l, m) {
                if !kinds.iter().any(|k| k == kind) {
                    continue;
                }
                let t0 = Instant::now();
                #[cfg(feature = "test-det")]
                let mut opts = ProveOpts { det_seed: det.clone(), ..Default::default() };
                #[cfg(not(feature = "test-det"))]
                let mut opts = ProveOpts::default();
                let blob = prove_with(&st, &wit, t, &mut opts).unwrap();
                let tp = t0.elapsed().as_secs_f64();
                let t0 = Instant::now();
                let v = verify(&st, &blob, t);
                let tv = t0.elapsed().as_secs_f64();
                let sh = shape(&st, t).unwrap();
                std::fs::write(format!("{out}/nat_{kind}.bin"), &blob).unwrap();
                res.push(format!(
                    "\"{kind}\": {{\"digest\": \"{}\", \"sha256\": \"{}\", \"bytes\": {}, \"formula\": {}, \"prove_s\": {:.3}, \"self_verify\": \"{:?}\", \"verify_s\": {:.3}}}",
                    pycompat::repr::hex(&st.digest()),
                    sha_hex(&blob),
                    blob.len(),
                    proof_bytes(sh.k, sh.th, t, sh.m1, sh.m2),
                    tp,
                    v,
                    tv
                ));
            }
            println!("{{\n{}\n}}", res.join(",\n"));
        }
        Some("verify") => {
            let (n, l, m, t): (usize, usize, usize, usize) = (arg(&a, 2), arg(&a, 3), arg(&a, 4), arg(&a, 5));
            let kind = &a[6];
            let blob = std::fs::read(&a[7]).unwrap();
            let (_, st, _) = instances(n, l, m).into_iter().find(|(k, _, _)| k == kind).unwrap();
            let t0 = Instant::now();
            let r = verify(&st, &blob, t);
            println!("{{\"kind\": \"{kind}\", \"result\": \"{:?}\", \"verify_s\": {:.3}}}", r, t0.elapsed().as_secs_f64());
        }
        Some("ceremony") => {
            let (n, l, t): (usize, usize, usize) = (arg(&a, 2), arg(&a, 3), arg(&a, 4));
            let (qp, tt) = params(n, l);
            #[cfg(feature = "test-det")]
            let (cer, _) = match det.as_deref() {
                Some(s) => ceremony::run_ceremony_det(1, 3, n, &qp, tt, t, s).unwrap(),
                None => ceremony::run_ceremony(1, 3, n, &qp, tt, t).unwrap(),
            };
            #[cfg(not(feature = "test-det"))]
            let (cer, _) = ceremony::run_ceremony(1, 3, n, &qp, tt, t).unwrap();
            let bd: Vec<String> = (0..3)
                .map(|i| {
                    let b = &cer.registry(i).unwrap().b;
                    let j = Json::List(b.to_big().into_iter().map(|x| Json::Int(x.into())).collect());
                    format!("\"{}\"", sha_hex(&j.canonical()))
                })
                .collect();
            println!(
                "{{\"seed\": \"{}\", \"transcript\": \"{}\", \"commits\": [{}], \"proofs\": [{}], \"b_digest\": [{}]}}",
                cer.seed.as_ref().unwrap(),
                cer.transcript(),
                (0..3).map(|i| format!("\"{}\"", cer.commits[&i])).collect::<Vec<_>>().join(", "),
                (0..3).map(|i| format!("\"{}\"", cer.keys[&i].proof_digest)).collect::<Vec<_>>().join(", "),
                bd.join(", ")
            );
        }
        Some("bench") => {
            let kind = Kind::parse(&a[2]).unwrap();
            let (n, l, m, s, t): (usize, usize, usize, usize, usize) = (arg(&a, 3), arg(&a, 4), arg(&a, 5), arg(&a, 6), arg(&a, 7));
            let reps: usize = a.get(8).map(|x| x.parse().unwrap()).unwrap_or(1);
            let (qp, tt) = params(n, l);
            let mut rng = PyRandom::from_u64(4096);
            let t0 = Instant::now();
            let (reg, sk, epk) = keygen(n, &qp, tt, "bench-seed", "custodian-1", &mut rng);
            let reg = Arc::new(reg);
            let sl: Vec<usize> = (0..s).collect();
            let (st, wit) = match kind {
                Kind::Pk => {
                    let (mut cts, mut ws) = (vec![], vec![]);
                    for _ in 0..m {
                        let mut pm = vec![0u64; n];
                        for &k in &sl {
                            pm[k] = rng.randrange_u64(tt);
                        }
                        let (ct, w) = encrypt_pk(&reg, &pm, &sl, &mut rng, None);
                        cts.push(ct);
                        ws.push(w);
                    }
                    (Statement::new(reg, kind, cts, vec![sl.clone(); m], ctx()).unwrap(), Witness::Pk { cts: ws })
                }
                _ => {
                    let (mut cts, mut ws) = (vec![], vec![]);
                    for _ in 0..m {
                        let mut pm = vec![0u64; n];
                        for &k in &sl {
                            pm[k] = rng.randrange_u64(tt);
                        }
                        let (ct, w) = encrypt_sk(&reg, &sk, &pm, &sl, &mut rng, None);
                        cts.push(ct);
                        ws.push(w);
                    }
                    let slots = if kind == Kind::Key { vec![] } else { vec![sl.clone(); m] };
                    let cts = if kind == Kind::Key { vec![] } else { cts };
                    let ws = if kind == Kind::Key { vec![] } else { ws };
                    (Statement::new(reg, kind, cts, slots, ctx()).unwrap(), Witness::Sk { s: sk, e_pk: epk, cts: ws })
                }
            };
            let tgen = t0.elapsed().as_secs_f64();
            let sh = shape(&st, t).unwrap();
            for rep in 0..reps {
                let t0 = Instant::now();
                let mut o = ProveOpts { low_memory: std::env::var("DZK_LOW_MEMORY").is_ok_and(|v| v != "0"), ..Default::default() };
                let blob = prove_with(&st, &wit, t, &mut o).unwrap();
                let tp = t0.elapsed().as_secs_f64();
                let t0 = Instant::now();
                let v = verify(&st, &blob, t);
                let tv = t0.elapsed().as_secs_f64();
                let formula = proof_bytes(sh.k, sh.th, t, sh.m1, sh.m2);
                println!(
                    "{{\"kind\": \"{}\", \"N\": {n}, \"L\": {l}, \"M\": {m}, \"S\": {s}, \"T\": {t}, \"rep\": {rep}, \"threads\": {}, \"low_memory\": {}, \"gen_s\": {:.2}, \"prove_s\": {:.3}, \"verify_s\": {:.3}, \"verify\": \"{:?}\", \"bytes\": {}, \"formula\": {}, \"exact\": {}, \"k\": {}, \"rows\": {}, \"digits\": {}}}",
                    kind.name(),
                    rayon::current_num_threads(),
                    o.low_memory,
                    tgen,
                    tp,
                    tv,
                    v,
                    blob.len(),
                    formula,
                    blob.len() == formula,
                    sh.k,
                    sh.m1 + sh.m2,
                    sh.n1 + sh.n2
                );
            }
        }
        Some("counts") => {
            let (n, l, t): (usize, usize, usize) = (arg(&a, 2), arg(&a, 3), arg(&a, 4));
            let (qp, tt) = params(n, l);
            for (m, s) in [(2usize, 64usize), (64, 64), (32, 128), (16, 256)] {
                let (bits, sh) = batch_proof_bits(Kind::Sk, n, &qp, tt, &vec![s; m], t).unwrap();
                println!("sk M={m} S={s}: {bits} bits, k={}, rows={}, digits={}", sh.k, sh.m1 + sh.m2, sh.n1 + sh.n2);
            }
        }
        _ => {
            eprintln!("usage: see the header of src/bin/dzkpopk.rs");
            std::process::exit(2);
        }
    }
}
