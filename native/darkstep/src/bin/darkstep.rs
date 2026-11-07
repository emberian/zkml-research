//! darkstep: one MPC-fork step by three custodians.
//!
//!   darkstep local N L F_bits d [--out PREFIX] [--attack KIND:PARTY] [--threads T]
//!       dealer + three custodian threads in this process, connected over 127.0.0.1 TCP
//!   darkstep deal N L F_bits d DIR
//!       the ideal dealer + owner: DIR/tape_{0,1,2}.bin and DIR/public.bin (the owner's input broadcasts)
//!   darkstep party I N L F_bits d DIR HOST:PORT HOST:PORT HOST:PORT [--attack KIND:PARTY]
//!       one custodian process; writes DIR/result_I.json and DIR/shares_I.bin
//!   darkstep reveal N L F_bits d DIR
//!       sums DIR/shares_*.bin and checks the new weights against step_spec (test only)
use darkstep::net::{bytes_to_u64s, u64s_to_bytes, Net};
use darkstep::node::*;
use darkstep::party::Sh;
use darkstep::step::*;
use darkstep::tape::{deal_step, Tape};
use serde_json::json;
use std::net::{SocketAddr, TcpListener};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("");
    if let Some(t) = flag(&args, "--threads") {
        rayon::ThreadPoolBuilder::new().num_threads(t.parse().unwrap()).build_global().unwrap();
    }
    match cmd {
        "local" => {
            let pf = prof(&args[2..6]);
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
            let i: usize = args[2].parse().unwrap();
            let pf = prof(&args[3..7]);
            let dir = std::path::PathBuf::from(&args[7]);
            let addrs: Vec<SocketAddr> = args[8..11].iter().map(|a| a.parse().unwrap()).collect();
            let tape = Tape::read_from(&mut std::io::BufReader::new(std::fs::File::open(dir.join(format!("tape_{i}.bin"))).unwrap())).unwrap();
            let cs = bytes_to_u64s(&std::fs::read(dir.join("public.bin")).unwrap());
            let listener = TcpListener::bind(addrs[i]).unwrap();
            let net = Net::connect(i, listener, &addrs);
            let (v, shares, dump) = custodian(i, &pf, net, tape, &cs, attack_of(&args));
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
