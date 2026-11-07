//! darkprep CLI.
//!   darkprep plan     --d D --mode harness|steady [--threads T] [--batch B]
//!   darkprep run      --mpspdz DIR --d D --mode M --p P --out DIR [--threads T] [--batch B] [--port N] [--verify] [--no-tapes] [--mpc-src FILE] [--extra a,b]
//!   darkprep assemble --tx DIR --d D --mode M --p P --out DIR [--verify]
//!   darkprep verify   --tapes DIR
//!   darkprep corrupt  --tape FILE --entry K --what share|mac|tag --out FILE      (test-only negative controls)
use darkprep::field::Fp;
use darkprep::mpspdz::{Run, Transactions};
use darkprep::schedule::{Inputs, Plan, StepParams};
use darkprep::tape::{assemble, read_owner, write_owner, Tape};
use darkprep::{owner, verify};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

fn args() -> (String, HashMap<String, String>) {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let cmd = a.first().cloned().unwrap_or_default();
    let mut m = HashMap::new();
    let mut i = 1;
    while i < a.len() {
        let k = a[i].trim_start_matches("--").to_string();
        if i + 1 < a.len() && !a[i + 1].starts_with("--") {
            m.insert(k, a[i + 1].clone());
            i += 2;
        } else {
            m.insert(k, "1".into());
            i += 1;
        }
    }
    (cmd, m)
}

fn step(m: &HashMap<String, String>) -> StepParams {
    let d: usize = m.get("d").expect("--d").parse().unwrap();
    let mode = match m.get("mode").map(|s| s.as_str()).unwrap_or("harness") {
        "harness" => Inputs::Harness,
        "steady" => Inputs::Steady,
        x => panic!("unknown mode {x}"),
    };
    StepParams::at(d, mode)
}

fn get<T: std::str::FromStr>(m: &HashMap<String, String>, k: &str, dflt: T) -> T {
    m.get(k).map(|v| v.parse().ok().expect(k)).unwrap_or(dflt)
}

fn assemble_all(sp: &StepParams, p: u64, txdir: &Path, out: &Path, check: bool) -> Result<String, String> {
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let t0 = std::time::Instant::now();
    let mut tapes = Vec::new();
    let mut msgs = Vec::new();
    for i in 0..3u32 {
        let tx = Transactions::read(&txdir.join(format!("Transactions-P{i}.data")), p)?;
        let tape = assemble(sp, &tx, i)?;
        let mut f = std::io::BufWriter::new(std::fs::File::create(out.join(format!("tape-P{i}.bin"))).map_err(|e| e.to_string())?);
        tape.write_to(&mut f).map_err(|e| e.to_string())?;
        msgs.push(owner::custodian_message(sp, &tx));
        tapes.push(tape);
    }
    let rs = owner::owner_masks(Fp::new(p), &msgs)?;
    let mut f = std::fs::File::create(out.join("owner.bin")).map_err(|e| e.to_string())?;
    write_owner(&mut f, p, &rs).map_err(|e| e.to_string())?;
    let asm_s = t0.elapsed().as_secs_f64();
    let mut s = format!("\"assemble_s\": {asm_s:.3}, \"tape_entries\": {}, \"owner_masks\": {}", tapes[0].entries.len(), rs.len());
    if check {
        let r = verify::verify(&tapes, &rs)?;
        s += &format!(", \"verify\": \"{:?}\"", r);
    }
    Ok(s)
}

fn load_tapes(dir: &Path) -> Result<(Vec<Tape>, Vec<u64>), String> {
    let mut tapes = Vec::new();
    for i in 0..3 {
        let mut f = std::fs::File::open(dir.join(format!("tape-P{i}.bin"))).map_err(|e| e.to_string())?;
        tapes.push(Tape::read_from(&mut f)?);
    }
    let (_, rs) = read_owner(&mut std::fs::File::open(dir.join("owner.bin")).map_err(|e| e.to_string())?)?;
    Ok((tapes, rs))
}

fn main() {
    let (cmd, m) = args();
    let res: Result<(), String> = (|| match cmd.as_str() {
        "plan" => {
            let sp = step(&m);
            let plan = Plan::of(&sp);
            println!("{:?}\n{:?}\nmpc args: {}", sp, plan, plan.mpc_args(get(&m, "threads", 1), get(&m, "batch", 1000)).join(" "));
            Ok(())
        }
        "run" => {
            let sp = step(&m);
            let plan = Plan::of(&sp);
            let p: u64 = get(&m, "p", 0);
            let mpspdz = PathBuf::from(m.get("mpspdz").expect("--mpspdz"));
            let out = PathBuf::from(m.get("out").expect("--out"));
            let margs = plan.mpc_args(get(&m, "threads", 1), get(&m, "batch", 1000));
            if let Some(src) = m.get("mpc-src") {
                std::fs::copy(src, mpspdz.join("Programs/Source/darkprep.mpc")).map_err(|e| e.to_string())?;
            }
            let tc = std::time::Instant::now();
            let prog = Run::compile(&mpspdz, &margs)?;
            let compile_s = tc.elapsed().as_secs_f64();
            let mut extra = vec!["-d".to_string()];
            if let Some(x) = m.get("extra") {
                extra.extend(x.split(',').map(String::from));
            }
            let run = Run { mpspdz: mpspdz.clone(), prog: prog.clone(), p, port_base: get(&m, "port", 14700), extra, workdir: out.clone() };
            let (wall, st) = run.execute()?;
            let total: f64 = st.iter().map(|s| s.sent_bytes).sum();
            let mut j = format!(
                "{{\"d\": {}, \"mode\": \"{:?}\", \"p\": {p}, \"prog\": \"{prog}\", \"plan\": {{\"in\": {}, \"ar\": {}, \"tri\": {}, \"lp\": {}, \"trunc_classes\": [{}]}}, \"compile_s\": {compile_s:.3}, \"wall_s\": {wall:.3}, \"parties\": [{}], \"total_sent_bytes\": {total:.0}, \"total_sent_bits\": {:.0}",
                sp.d, sp.inputs, plan.n_in, plan.n_ar, plan.n_tri, plan.n_lp,
                plan.trunc_classes.iter().map(|(a, b, c)| format!("[{a}, {b}, {c}]")).collect::<Vec<_>>().join(", "),
                st.iter().map(|s| format!("{{\"time_s\": {}, \"sent_bytes\": {:.0}, \"rounds\": {}}}", s.time_s, s.sent_bytes, s.rounds)).collect::<Vec<_>>().join(", "),
                total * 8.0
            );
            if m.contains_key("no-tapes") {
                j += "}";
            } else {
                j += &format!(", {}}}", assemble_all(&sp, p, &mpspdz.join("Persistence"), &out, m.contains_key("verify"))?);
            }
            std::fs::write(out.join("stats.json"), &j).map_err(|e| e.to_string())?;
            println!("{j}");
            Ok(())
        }
        "assemble" => {
            let sp = step(&m);
            let s = assemble_all(&sp, get(&m, "p", 0), Path::new(m.get("tx").expect("--tx")), Path::new(m.get("out").expect("--out")), m.contains_key("verify"))?;
            println!("{{{s}}}");
            Ok(())
        }
        "verify" => {
            let (tapes, rs) = load_tapes(Path::new(m.get("tapes").expect("--tapes")))?;
            let r = verify::verify(&tapes, &rs)?;
            println!("OK {:?}", r);
            Ok(())
        }
        "corrupt" => {
            let path = PathBuf::from(m.get("tape").expect("--tape"));
            let mut t = Tape::read_from(&mut std::fs::File::open(&path).map_err(|e| e.to_string())?)?;
            let k: usize = get(&m, "entry", 0);
            let fp = Fp::new(t.p);
            let e = &mut t.entries[k];
            match m.get("what").map(|s| s.as_str()).unwrap_or("share") {
                "share" => e.1 = fp.add(e.1, 1),
                "mac" => e.2 = fp.add(e.2, 1),
                "tag" => e.0 = darkprep::schedule::Tag::from_code((e.0 as u8 + 1) % 9).unwrap(),
                x => return Err(format!("unknown --what {x}")),
            }
            let mut f = std::fs::File::create(m.get("out").expect("--out")).map_err(|e| e.to_string())?;
            t.write_to(&mut f).map_err(|e| e.to_string())?;
            println!("corrupted entry {k} of {}", path.display());
            Ok(())
        }
        _ => Err("usage: darkprep plan|run|assemble|verify|corrupt ...".into()),
    })();
    if let Err(e) = res {
        eprintln!("darkprep: {e}");
        std::process::exit(1);
    }
}
