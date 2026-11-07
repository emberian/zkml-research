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
//!       [--listen HOST:PORT] [--pause-utc HH:MM-HH:MM] [--timeout SECS]
//!       one custodian for K steps over mutual TLS (pinned certificates in TLSDIR: tls_I.key, cert_{0,1,2,owner}.der).
//!       Its weight shares stay in this process; each step's inputs come from the owner; after every step it writes
//!       DIR/step_<k>_P<I>.json and its own checkpoint DIR/ckpt_P<I>.bin. PATTERN holds {k} (the step). With
//!       --pause-utc, custodian 0 decides at each step boundary whether the run pauses (all three checkpoint and exit
//!       with code 3); --resume continues from the checkpoint
//!   darkstep deal-steps N L F_bits d K DIR                (feature test-harness only)
//!       the public-seed test dealer for K steps: DIR/tape_{0,1,2}.bin (continuous) and DIR/public_step<k>.bin
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
use darkstep::step::Program;
use darkstep::tape::Tape;
use serde_json::json;
use std::net::{SocketAddr, TcpListener};
use std::time::Instant;

fn gated(mut pf: Prof, args: &[String]) -> Prof {
    pf.gate = flag(args, "--gate").map(|t| t.parse().expect("--gate T"));
    pf.det_seed = std::env::var("DL_DETERMINISTIC").ok();
    pf
}

/// The process's peak resident set (VmHWM), where /proc exists.
fn peak_rss_kb() -> Option<u64> {
    let st = std::fs::read_to_string("/proc/self/status").ok()?;
    st.lines().find_map(|l| l.strip_prefix("VmHWM:")).and_then(|r| r.trim().trim_end_matches("kB").trim().parse().ok())
}

fn program_of(args: &[String]) -> Program {
    match flag(args, "--program").as_deref() {
        None | Some("harness") => Program::HARNESS,
        Some("gen6") => Program::GEN6,
        Some(x) => panic!("--program {x}: harness or gen6"),
    }
}

fn utc_minutes() -> u64 {
    (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() / 60) % (24 * 60)
}

/// "HH:MM-HH:MM" contains the current UTC minute.
fn in_window(w: &str) -> bool {
    let m = |x: &str| -> u64 {
        let (h, mi) = x.split_once(':').expect("HH:MM");
        h.parse::<u64>().unwrap() * 60 + mi.parse::<u64>().unwrap()
    };
    let (a, b) = w.split_once('-').expect("HH:MM-HH:MM");
    let (a, b, now) = (m(a), m(b), utc_minutes());
    if a <= b { (a..b).contains(&now) } else { now >= a || now < b }
}

fn read_tape(path: &str) -> Tape {
    Tape::read_from(&mut std::io::BufReader::new(std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}")))).unwrap()
}

fn serve(args: &[String]) -> i32 {
    use darkstep::serve::*;
    let i: usize = args[2].parse().unwrap();
    let mut pf = gated(prof(&args[3..7]), args);
    pf.secure_coins = true;
    pf.program = program_of(args);
    let dir = std::path::PathBuf::from(&args[7]);
    std::fs::create_dir_all(&dir).unwrap();
    let addrs: Vec<SocketAddr> = args[8..11].iter().map(|a| a.parse().unwrap()).collect();
    let tlsdir = std::path::PathBuf::from(flag(args, "--tls").expect("--tls TLSDIR"));
    let owner_addr: SocketAddr = flag(args, "--owner").expect("--owner HOST:PORT").parse().unwrap();
    let steps: usize = flag(args, "--steps").expect("--steps K").parse().unwrap();
    let timeout = std::time::Duration::from_secs(flag(args, "--timeout").map(|t| t.parse().unwrap()).unwrap_or(600));
    let id = darkstep::tls::Identity {
        key_der: std::fs::read(tlsdir.join(format!("tls_{i}.key"))).expect("own TLS key"),
        cert_der: std::fs::read(tlsdir.join(format!("cert_{i}.der"))).expect("own certificate"),
    };
    let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(tlsdir.join(format!("cert_{j}.der"))).expect("peer certificate")).collect();
    let owner_cert = std::fs::read(tlsdir.join("cert_owner.der")).expect("owner certificate");
    let tape_for = |k: usize| -> Option<String> {
        flag(args, "--tapes").map(|p| p.replace("{k}", &k.to_string()))
    };
    let ckpt = dir.join(format!("ckpt_P{i}.bin"));
    let resume = args.iter().any(|a| a == "--resume");
    let ck = if resume { Some(read_checkpoint(&ckpt).unwrap_or_else(|e| panic!("--resume: {e}"))) } else { None };
    let first = ck.as_ref().map(|c| c.step).unwrap_or(0);
    let tape = match (flag(args, "--tape"), tape_for(first)) {
        (Some(f), _) => read_tape(&f),
        (None, Some(f)) => read_tape(&f),
        _ => panic!("--tape FILE or --tapes PATTERN"),
    };
    let t_start = Instant::now();
    let listener = if i + 1 < 3 {
        let at: SocketAddr = flag(args, "--listen").map(|a| a.parse().unwrap()).unwrap_or(addrs[i]);
        Some(TcpListener::bind(at).unwrap_or_else(|e| panic!("bind {at}: {e}")))
    } else {
        None
    };
    let net = match darkstep::net::Net::connect_tls(i, listener, &addrs, &id, &certs, timeout) {
        Ok(n) => n,
        Err(e) => {
            eprintln!("{e}");
            return 2;
        }
    };
    let mut owner = match dial_owner(owner_addr, &id, &owner_cert, timeout) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{e}");
            net.shutdown();
            return 2;
        }
    };
    let connect_s = t_start.elapsed().as_secs_f64();
    let tc = Instant::now();
    let mut st = match CustodianState::new(i, pf.clone(), net, tape, darkstep::node::attack_of(args)) {
        Ok(s) => s,
        Err((e, net)) => {
            eprintln!("setup: {e}");
            net.shutdown();
            return 1;
        }
    };
    let setup_s = tc.elapsed().as_secs_f64();
    if let Some(c) = ck {
        if let Err(e) = st.resume(c) {
            eprintln!("{e}");
            st.pt.net.shutdown();
            return 2;
        }
    }
    let pause = flag(args, "--pause-utc");
    let mut code = 0;
    let mut reports = Vec::new();
    while st.step < first + steps {
        let k = st.step;
        // custodian 0 decides whether to pause here; the three agree on CTRL
        let mine = [if i == 0 { pause.as_deref().map(in_window).unwrap_or(false) as u64 } else { 0 }];
        let votes = st.pt.net.exchange(darkstep::net::CTRL, &mine);
        if votes[0][0] == 1 {
            code = 3;
            break;
        }
        if k > first {
            if let Some(f) = tape_for(k) {
                if let Err(e) = st.load_tape(read_tape(&f)) {
                    eprintln!("{e}");
                    code = 1;
                    break;
                }
            }
        }
        let msg = flag(args, "--owner-msgs").map(|p| std::fs::read(p.replace("{k}", &k.to_string())).expect("owner message")).unwrap_or_default();
        let tw = Instant::now();
        let cs = match owner_inputs(&mut owner, &st.pt.net, k, &msg) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("{e}");
                code = 1;
                break;
            }
        };
        let owner_s = tw.elapsed().as_secs_f64();
        match st.run(&cs) {
            Ok((mut rep, _record)) => {
                rep["owner_wait_seconds"] = json!(owner_s);
                st.checkpoint(&ckpt).expect("checkpoint");
                std::fs::write(dir.join(format!("step_{k}_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).unwrap();
                println!("{}", json!({"party": i, "step": k, "verdict": "ACCEPT", "step_seconds": rep["step_seconds"]}));
                reports.push(rep);
            }
            Err(e) => {
                let rep = json!({"party": i, "step": k, "verdict": "REFUSED", "by": e});
                std::fs::write(dir.join(format!("step_{k}_P{i}.json")), serde_json::to_string_pretty(&rep).unwrap()).unwrap();
                println!("{rep}");
                code = 1;
                break;
            }
        }
    }
    let (cpu, rss) = proc_usage();
    let summary = json!({"party": i, "first_step": first, "next_step": st.step, "exit": code, "paused": code == 3,
        "connect_seconds": connect_s, "setup_seconds": setup_s, "wall_seconds": t_start.elapsed().as_secs_f64(),
        "cpu_seconds": cpu, "peak_rss_kb": rss, "ceremony_seconds": st.he.gate.as_ref().map(|g| g.ceremony_s),
        "cert_sha256": (0..3).map(|j| darkstep::tls::cert_fingerprint(&certs[j])).collect::<Vec<_>>()});
    std::fs::write(dir.join(format!("serve_P{i}.json")), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    #[cfg(feature = "test-harness")]
    if args.iter().any(|a| a == "--test-keep-shares") {
        if let Some((w1, w2)) = &st.w {
            let flat: Vec<u64> = w1.iter().chain(w2.iter()).flat_map(|r| r.iter().flat_map(|x| [x.s, x.m])).collect();
            std::fs::write(dir.join(format!("shares_{i}.bin")), u64s_to_bytes(&flat)).unwrap();
        }
    }
    let _ = write_frame(&mut owner, &u64::MAX.to_le_bytes());
    owner.conn.send_close_notify();
    let _ = owner.conn.complete_io(&mut owner.sock);
    st.pt.net.shutdown();
    code
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("");
    if let Some(t) = flag(&args, "--threads") {
        rayon::ThreadPoolBuilder::new().num_threads(t.parse().unwrap()).build_global().unwrap();
    }
    match cmd {
        "serve" => std::process::exit(serve(&args)),
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
        "deal-steps" => {
            let mut pf = prof(&args[2..6]);
            pf.program = program_of(&args);
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
            let (tapes, cs) = darkstep::tape::deal_steps_prog(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t), &later, false, &pf.program);
            for (i, tp) in tapes.iter().enumerate() {
                let mut f = std::io::BufWriter::new(std::fs::File::create(dir.join(format!("tape_{i}.bin"))).unwrap());
                tp.write_to(&mut f).unwrap();
            }
            for (s, c) in cs.iter().enumerate() {
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
            let pf = prof(&args[2..6]);
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
