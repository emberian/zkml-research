//! darkstep: one MPC-fork step by three custodians.
//!
//!   darkstep local N L F_bits d [--out PREFIX] [--attack KIND:PARTY] [--threads T] [--gate T_COLS]
//!       dealer + three custodian threads in this process, connected over 127.0.0.1 TCP
//!       --gate T: keys from the ceremony and the ZKPoPK gate before every ptxct (T = 309 ledger, 97 demo);
//!       DL_DETERMINISTIC=<seed> (builds with --features test-det only) seeds the ceremony and the proofs
//!   darkstep deal N L F_bits d DIR                       (feature test-harness only)
//!       the ideal dealer + owner from the harness's PUBLIC seeds: DIR/tape_{0,1,2}.bin and DIR/public.bin. A test
//!       stand-in for the preprocessing (darkprep); a deployment never runs it
//!   darkstep party I N L F_bits d DIR HOST:PORT HOST:PORT HOST:PORT [--attack KIND:PARTY]
//!       one custodian process; writes DIR/result_I.json and DIR/shares_I.bin. Its HE coins come from the OS
//!       (Prof::secure_coins), never from the harness's public reference streams
//!   darkstep tls-keygen I DIR
//!       a fresh TLS identity for seat I (custodian 0..2, or "owner"): DIR/tls_I.key (0600, never copied) and
//!       DIR/cert_I.der (public; copy it to every seat)
//!   darkstep serve I N L F_bits d DIR HOST:PORT HOST:PORT HOST:PORT --tls TLSDIR --owner HOST:PORT --steps K
//!       [--gate T] [--program harness|gen6] [--tape FILE | --tapes PATTERN] [--owner-msgs PATTERN] [--resume]
//!       [--listen HOST:PORT] [--pause-utc HH:MM-HH:MM] [--timeout SECS] [--ret-primes K]
//!       one custodian for K steps over mutual TLS (pinned certificates in TLSDIR: tls_I.key, cert_{0,1,2,owner}.der).
//!       Its weight shares stay in this process; each step's inputs come from the owner; after every step it writes
//!       DIR/step_<k>_P<I>.json and its own checkpoint DIR/ckpt_P<I>.bin. PATTERN holds {k} (the step). With
//!       --pause-utc, custodian 0 decides at each step boundary whether the run pauses (all three checkpoint and exit
//!       with code 3); --resume continues from the checkpoint. --ret-primes K (party, serve, local): HE returns
//!       modulus-switched to K primes with c0 only where decrypted (K = 2; every custodian the same)
//!   darkstep deal-steps N L F_bits d K DIR [--program P] [--only I [--public]]   (feature test-harness only)
//!       the public-seed test dealer for K steps: DIR/tape_{0,1,2}.bin (continuous) and DIR/public_step<k>.bin;
//!       --only I writes custodian I's tape alone (and the broadcasts only with --public)
//!   darkstep reveal N L F_bits d DIR                     (feature test-harness only)
//!       sums DIR/shares_*.bin and checks the new weights against step_spec; it reassembles the model, so a
//!       deployed party binary cannot run it
use darkstep::net::{bytes_to_u64s, u64s_to_bytes, Net};
use darkstep::node::*;
#[cfg(feature = "test-harness")]
use darkstep::party::Sh;
#[cfg(feature = "test-harness")]
use darkstep::step::*;
#[cfg(feature = "test-harness")]
use darkstep::tape::deal_step;
use darkstep::tape::Tape;
use serde_json::json;
use std::net::{SocketAddr, TcpListener};
use std::time::Instant;


/// The process's peak resident set (VmHWM), where /proc exists.
fn peak_rss_kb() -> Option<u64> {
    let st = std::fs::read_to_string("/proc/self/status").ok()?;
    st.lines().find_map(|l| l.strip_prefix("VmHWM:")).and_then(|r| r.trim().trim_end_matches("kB").trim().parse().ok())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("");
    if let Some(t) = flag(&args, "--threads") {
        rayon::ThreadPoolBuilder::new().num_threads(t.parse().unwrap()).build_global().unwrap();
    }
    match cmd {
        "serve" => std::process::exit(darkstep::serve::serve_main(&args, &mut darkstep::serve::NoHook)),
        "tls-keygen" => {
            let dir = std::path::PathBuf::from(&args[3]);
            std::fs::create_dir_all(&dir).unwrap();
            let seat = &args[2];
            let id = darkstep::tls::generate(seat.parse::<usize>().unwrap_or(9));
            let mut f = darkstep::serve::open_private(&dir.join(format!("tls_{seat}.key"))).unwrap();
            std::io::Write::write_all(&mut f, &id.key_der).unwrap();
            std::fs::write(dir.join(format!("cert_{seat}.der")), &id.cert_der).unwrap();
            println!("{}", json!({"seat": seat, "cert_sha256": darkstep::tls::cert_fingerprint(&id.cert_der)}));
        }
        #[cfg(feature = "test-harness")]
        "owner-test" => {
            // TEST: the owner serving the test dealer's broadcasts DIR/public_step<k>.bin; owner-test HOST:PORT TLSDIR DIR
            let tls = std::path::PathBuf::from(&args[3]);
            let dir = std::path::PathBuf::from(&args[4]);
            let id = darkstep::tls::Identity {
                key_der: std::fs::read(tls.join("tls_owner.key")).expect("owner key"),
                cert_der: std::fs::read(tls.join("cert_owner.der")).expect("owner cert"),
            };
            let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(tls.join(format!("cert_{j}.der"))).unwrap()).collect();
            let l = TcpListener::bind(&args[2]).unwrap();
            let r = darkstep::serve::owner_serve(l, &id, &certs, |k, _| {
                std::fs::read(dir.join(format!("public_step{k}.bin"))).map(|b| bytes_to_u64s(&b)).map_err(|e| e.to_string())
            });
            if let Err(e) = r {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        #[cfg(feature = "test-harness")]
        "deal-steps" => {
            let mut pf = prof(&args[2..6]);
            pf.program = darkstep::serve::program_of(&args);
            let k: usize = args[6].parse().unwrap();
            let dir = std::path::PathBuf::from(&args[7]);
            std::fs::create_dir_all(&dir).unwrap();
            let plain = darkstep::step::inputs_for(pf.d, &pf.program);
            let later: Vec<Vec<u64>> = (1..k)
                .map(|s| {
                    let mut r = pycompat::PyRandom::from_u64(1000 + s as u64);
                    (0..2 * pf.d).map(|_| darkstep::arith::from_i64(r.randint_i64(-7, 7), pf.t)).collect()
                })
                .collect();
            // --proof-triples G,C: after each step its proof section (G triples at genesis, C after a carried step) on
            // the same dealer stream, with the truncations' range bits (proof atoms); one owner stream throughout
            // --public-genesis: the weights are public (no W inputs); every step is dealt as a carried step, and
            // DIR/genesis_w.bin holds W1, W2 as i64 LE for `serve --genesis-public`
            let pubgen = args.iter().any(|a| a == "--public-genesis");
            let (tapes, cs) = if pubgen {
                let mut dl = darkstep::tape::Dealer::new(pf.t, 3, DEALER_SEED);
                let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
                let xy0: Vec<u64> = plain.x.iter().chain(plain.y.iter()).map(|&v| darkstep::arith::from_i64(v, pf.t)).collect();
                let mut cs = vec![darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, &xy0, &pf.program)];
                for xs in &later {
                    cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, xs, &pf.program));
                }
                let w: Vec<u8> = plain.w1.iter().chain(plain.w2.iter()).flatten().flat_map(|x| x.to_le_bytes()).collect();
                std::fs::write(dir.join("genesis_w.bin"), w).unwrap();
                (dl.tapes, cs)
            } else { match flag(&args, "--proof-triples") {
                None => darkstep::tape::deal_steps_prog(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t), &later, false, &pf.program),
                Some(gc) => {
                    let (g, c) = gc.split_once(',').expect("--proof-triples G,C");
                    let (g, c): (usize, usize) = (g.parse().unwrap(), c.parse().unwrap());
                    let mut dl = darkstep::tape::Dealer::new(pf.t, 3, DEALER_SEED);
                    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
                    let mut owner = pycompat::PyRandom::from_u64(OWNER_SEED);
                    let mut cs = vec![darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, &plain.flat_mod(pf.t), &pf.program)];
                    darkstep::tape::deal_proof_section(&mut dl, g);
                    for xs in &later {
                        cs.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, pf.d, xs, &pf.program));
                        darkstep::tape::deal_proof_section(&mut dl, c);
                    }
                    (dl.tapes, cs)
                }
            } };
            // --only I: write custodian I's tape only (run the dealer on each custodian's own box)
            let only: Option<usize> = flag(&args, "--only").map(|x| x.parse().unwrap());
            for (i, tp) in tapes.iter().enumerate() {
                if only.is_some_and(|o| o != i) {
                    continue;
                }
                let mut f = std::io::BufWriter::new(std::fs::File::create(dir.join(format!("tape_{i}.bin"))).unwrap());
                tp.write_to(&mut f).unwrap();
            }
            for (s, c) in cs.iter().enumerate().filter(|_| only.is_none() || args.iter().any(|a| a == "--public")) {
                std::fs::write(dir.join(format!("public_step{s}.bin")), u64s_to_bytes(c)).unwrap();
            }
            let raw: Vec<Vec<i64>> = later.iter().map(|v| v.iter().map(|&x| if x > pf.t / 2 { x as i64 - pf.t as i64 } else { x as i64 }).collect()).collect();
            std::fs::write(dir.join("later_inputs.json"), serde_json::to_string(&raw).unwrap()).unwrap();
            println!("{}", json!({"steps": k, "tape_len": tapes[0].len()}));
        }
        "local" => {
            let pf = gated(prof(&args[2..6]), &args);
            let prefix = flag(&args, "--out").unwrap_or_else(|| format!("native_N{}_L{}_F{}_d{}", pf.n, pf.l, pf.f_bits, pf.d));
            let (res, dump) = run_local(&pf, attack_of(&args));
            if let Some(d) = dump {
                std::fs::write(format!("{prefix}.transcript.txt"), d).unwrap();
            }
            std::fs::write(format!("{prefix}.json"), serde_json::to_string_pretty(&res).unwrap()).unwrap();
            let mut short = res.clone();
            short.as_object_mut().unwrap().remove("detail");
            println!("{}", serde_json::to_string(&short).unwrap());
        }
        #[cfg(feature = "test-harness")]
        "deal" => {
            let pf = prof(&args[2..6]);
            let dir = std::path::PathBuf::from(&args[6]);
            std::fs::create_dir_all(&dir).unwrap();
            let t0 = Instant::now();
            let plain = inputs(pf.d);
            let (tapes, cs) = deal_step(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t));
            for (i, tp) in tapes.iter().enumerate() {
                let mut f = std::io::BufWriter::new(std::fs::File::create(dir.join(format!("tape_{i}.bin"))).unwrap());
                tp.write_to(&mut f).unwrap();
            }
            std::fs::write(dir.join("public.bin"), u64s_to_bytes(&cs)).unwrap();
            println!("{}", json!({"deal_seconds": t0.elapsed().as_secs_f64(), "tape_len": tapes[0].len(), "inputs": cs.len()}));
        }
        "party" => {
            let t_start = Instant::now();
            let i: usize = args[2].parse().unwrap();
            let mut pf = gated(prof(&args[3..7]), &args);
            pf.secure_coins = true;
            let dir = std::path::PathBuf::from(&args[7]);
            let addrs: Vec<SocketAddr> = args[8..11].iter().map(|a| a.parse().unwrap()).collect();
            let tape = Tape::read_from(&mut std::io::BufReader::new(std::fs::File::open(dir.join(format!("tape_{i}.bin"))).unwrap())).unwrap();
            let cs = bytes_to_u64s(&std::fs::read(dir.join("public.bin")).unwrap());
            let listener = TcpListener::bind(addrs[i]).unwrap();
            let net = Net::connect(i, listener, &addrs);
            let (mut v, shares, dump) = custodian(i, &pf, net, tape, &cs, attack_of(&args));
            v["wall_seconds"] = json!(t_start.elapsed().as_secs_f64());
            if let Some(kb) = peak_rss_kb() {
                v["peak_rss_kb"] = json!(kb);
            }
            std::fs::write(dir.join(format!("result_{i}.json")), serde_json::to_string_pretty(&v).unwrap()).unwrap();
            if let Some((w1, w2)) = shares {
                let flat: Vec<u64> = w1.iter().chain(w2.iter()).flat_map(|r| r.iter().flat_map(|x| [x.s, x.m])).collect();
                std::fs::write(dir.join(format!("shares_{i}.bin")), u64s_to_bytes(&flat)).unwrap();
            }
            if let Some(d) = dump {
                if i == 0 && !d.is_empty() {
                    std::fs::write(dir.join("transcript.txt"), d).unwrap();
                }
            }
            println!("{}", serde_json::to_string(&json!({"party": i, "verdict": v["verdict"], "step_seconds": v["step_seconds"], "by": v.get("by")})).unwrap());
        }
        #[cfg(feature = "test-harness")]
        "reveal" => {
            let mut pf = prof(&args[2..6]);
            pf.program = darkstep::serve::program_of(&args);
            let dir = std::path::PathBuf::from(&args[6]);
            let d = pf.d;
            let shares: Vec<(Vec<Vec<Sh>>, Vec<Vec<Sh>>)> = (0..3)
                .map(|i| {
                    let v = bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
                    let sh: Vec<Sh> = v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect();
                    let rows: Vec<Vec<Sh>> = sh.chunks(d).map(|r| r.to_vec()).collect();
                    (rows[..d].to_vec(), rows[d..].to_vec())
                })
                .collect();
            println!("{}", json!({"refines_spec": reveal_check(&pf, &shares)}));
        }
        _ => {
            eprintln!("usage: see the header of native/darkstep/src/bin/darkstep.rs");
            std::process::exit(2);
        }
    }
}
