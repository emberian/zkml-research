//! darkprep CLI.
//!   darkprep plan     --d D --mode harness|steady [--truncs ..] [--proof|--release M,NCLS,KC --proof-triples N] [--threads T] [--batch B]
//!   darkprep run      --mpspdz DIR --d D --mode M --p P --out DIR [--threads T] [--batch B] [--port N] [--verify] [--no-tapes] [--mpc-src FILE] [--extra a,b]
//!   darkprep assemble --tx DIR --d D --mode M --p P --out DIR [--verify]
//!   darkprep verify   --tapes DIR
//!   darkprep corrupt  --tape FILE --entry K --what share|mac|tag --out FILE      (test-only negative controls)
//!   darkprep party-chunk --party I --mpspdz DIR --ipfile F --p P --d D --mode harness|steady --steps K [--proof]
//!                        [--proof-triples N] --out CHUNKDIR [--threads T] [--batch B] [--plaintext] [--mpc-src FILE]
//!                        [--backend mascot|lowgear|highgear] [--extra a,b,..]  (lowgear: --extra -S,60,-lg2,64)
//!                        [--release M,NCLS,KC --proof-triples N]  (the release chunk instead of K steps)
//!                        [--handover-ar N]  (a new seat's handover tape: N auth_plain entries)  [--new-mac-key]
//!                        [--step-tapes-only]  (no whole-chunk tape_<I>.bin: only step-<j>/tape_<I>.bin)
//!                        [--rs]  (the proof program's "RS": K + 1 - s Trhb bits)  [--lookup-triples T]  (release, L cut)
//!                        --vault NAME | --vault-file TLSDIR/vault.name  (required: every step's tape_<I>.bin and
//!                        owner-msg-P<I>.bin is sealed, DLVAULT1, roles "tape|<chunk>|<j>" / "owner-msg|<chunk>|<j>";
//!                        the release tape as DLVAULT2 blocks under the same key and role; a build with feature
//!                        test-plain-tapes may write plain files with --plain-tapes instead)
//!       ONE custodian's share of a chunk of K steps, run on its own box against the other two (MASCOT, TLS).
//!       Writes CHUNKDIR/step-<j>/tape_<I>.bin (darkstep's tape format) and owner-msg-P<I>.bin (this custodian's
//!       plain input-tuple shares, for the data owner), CHUNKDIR/chunk-P<I>.json (measurements); built in
//!       CHUNKDIR.tmp-P<I> and renamed when complete, so a CHUNKDIR that exists is whole.
//!   darkprep produce --queue QDIR --max-ready N --start C --count M  + party-chunk's options except --out
//!       a continuous producer: chunks QDIR/chunk-<c> while fewer than N unconsumed chunks are ready; the consumer
//!       deletes (or moves away) a chunk when it has used it; a file QDIR/STOP ends the loop after the current chunk.
//!   darkprep owner --msgs F0,F1,F2 --p P --out OWNER.bin [--public-d D --public PUBLIC.bin]
//!       the data owner: checks a b = c per input tuple, writes its masks r; with --public-d, also the broadcasts
//!       c = v - r for darkstep::step::inputs(D) (the harness inputs) in darkstep's public.bin layout
//!   darkprep export-darkstep --tapes DIR --out DIR
//!       native/darkstep's party input: DIR/tape_{0,1,2}.bin (its DLTAPE01 layout) and DIR/public.bin, the data
//!       owner's broadcasts c = v - r for the harness inputs (darkstep::step::inputs(d)) under the owner's masks
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
    let mut sp = StepParams::at(d, mode);
    // --xt: exact truncation (notes/dark-learning-gen6/xtrunc.md): 61-bit masks checked r < p inside the MPC
    if m.contains_key("xt") {
        let p: u64 = get(m, "p", 0);
        assert!(p > 1 << 60 && p < 1 << 61, "--xt needs --p, the 61-bit SPDZ prime");
        sp.xt = Some(p);
    }
    sp
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
        let r = verify::verify_xt(&tapes, &rs, sp.xt)?;
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
            let sp = chunk_step(&m);
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
            let r = verify::verify_xt(&tapes, &rs, if m.contains_key("xt") { Some(get(&m, "p", 0)) } else { None })?;
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
        "export-darkstep" => {
            let (tapes, rs) = load_tapes(Path::new(m.get("tapes").expect("--tapes")))?;
            let out = PathBuf::from(m.get("out").expect("--out"));
            std::fs::create_dir_all(&out).map_err(|e| e.to_string())?;
            let t0 = &tapes[0];
            if t0.inputs != 0 {
                return Err("darkstep runs the harness step (W1, W2, x, y input): export a harness-mode tape".into());
            }
            for t in &tapes {
                let ds = darkstep::tape::Tape {
                    alpha_i: t.alpha_i,
                    tags: t.entries.iter().map(|e| e.0 as u8 + 1).collect(), // darkstep numbers In = 1 .. Ar = 9
                    sh: t.entries.iter().map(|e| e.1).collect(),
                    mac: t.entries.iter().map(|e| e.2).collect(),
                };
                let mut f = std::io::BufWriter::new(std::fs::File::create(out.join(format!("tape_{}.bin", t.party))).map_err(|e| e.to_string())?);
                ds.write_to(&mut f).map_err(|e| e.to_string())?;
            }
            let fp = Fp::new(t0.p);
            let v = darkstep::step::inputs(t0.d as usize).flat_mod(t0.p);
            if v.len() != rs.len() {
                return Err(format!("{} inputs, {} owner masks", v.len(), rs.len()));
            }
            let cs: Vec<u64> = v.iter().zip(&rs).map(|(&x, &r)| fp.sub(x, r)).collect();
            std::fs::write(out.join("public.bin"), darkstep::net::u64s_to_bytes(&cs)).map_err(|e| e.to_string())?;
            println!("exported {} entries per party and {} owner broadcasts to {}", t0.entries.len(), cs.len(), out.display());
            Ok(())
        }
        "party-chunk" => {
            let out = PathBuf::from(m.get("out").expect("--out"));
            party_chunk(&m, &out).map(|j| println!("{j}"))
        }
        "produce" => {
            let q = PathBuf::from(m.get("queue").expect("--queue"));
            std::fs::create_dir_all(&q).map_err(|e| e.to_string())?;
            let max_ready: usize = get(&m, "max-ready", 2);
            let start: usize = get(&m, "start", 0);
            let count: usize = get(&m, "count", 1);
            let party: usize = get(&m, "party", 9);
            let mut log = std::fs::OpenOptions::new().create(true).append(true).open(q.join(format!("producer-P{party}.jsonl"))).map_err(|e| e.to_string())?;
            for c in start..start + count {
                loop {
                    if q.join("STOP").exists() {
                        return Ok(());
                    }
                    let ready = std::fs::read_dir(&q).map_err(|e| e.to_string())?.flatten()
                        .filter(|e| { let n = e.file_name().to_string_lossy().into_owned(); n.starts_with("chunk-") && !n.contains(".tmp") })
                        .count();
                    if ready < max_ready {
                        break;
                    }
                    std::thread::sleep(std::time::Duration::from_secs(2));
                }
                let j = party_chunk(&m, &q.join(format!("chunk-{c:06}")))?;
                use std::io::Write;
                writeln!(log, "{j}").map_err(|e| e.to_string())?;
            }
            Ok(())
        }
        "owner" => {
            let p: u64 = get(&m, "p", 0);
            let fp = Fp::new(p);
            let msgs: Vec<Vec<[u64; 3]>> = m.get("msgs").expect("--msgs").split(',')
                .map(|f| std::fs::read(f).map_err(|e| format!("{f}: {e}")).and_then(|b| owner::read_message(&b)))
                .collect::<Result<_, _>>()?;
            let rs = owner::owner_masks(fp, &msgs)?;
            let mut f = std::fs::File::create(m.get("out").expect("--out")).map_err(|e| e.to_string())?;
            write_owner(&mut f, p, &rs).map_err(|e| e.to_string())?;
            if let Some(d) = m.get("public-d") {
                let v = darkstep::step::inputs(d.parse().unwrap()).flat_mod(p);
                if v.len() != rs.len() {
                    return Err(format!("{} inputs, {} masks", v.len(), rs.len()));
                }
                let cs: Vec<u64> = v.iter().zip(&rs).map(|(&x, &r)| fp.sub(x, r)).collect();
                std::fs::write(m.get("public").expect("--public"), darkstep::net::u64s_to_bytes(&cs)).map_err(|e| e.to_string())?;
            }
            println!("owner: {} masks checked (a b = c)", rs.len());
            Ok(())
        }
        _ => Err("usage: darkprep plan|run|assemble|verify|corrupt|export-darkstep|party-chunk|produce|owner ...".into()),
    })();
    if let Err(e) = res {
        eprintln!("darkprep: {e}");
        std::process::exit(1);
    }
}

fn chunk_step(m: &HashMap<String, String>) -> StepParams {
    let mut sp = step(m);
    if let Some(t) = m.get("truncs") {
        // the step program's (s1, k1, s2, k2, s3, k3): darkstep::step::Program::truncs()
        let v: Vec<u32> = t.split(',').map(|x| x.parse().expect("--truncs s1,k1,s2,k2,s3,k3")).collect();
        assert_eq!(v.len(), 6, "--truncs s1,k1,s2,k2,s3,k3");
        sp.trunc = [(v[0], v[1]), (v[0], v[1]), (v[2], v[3]), (v[4], v[5])];
    }
    // --rs: the proof program's "RS" flag (K + 1 - s Trhb bits per truncation)
    sp.rs = m.contains_key("rs");
    if let Some(r) = m.get("release") {
        // the mind's release (darkproof::run::deal_release): M examples, ncls classes, comparisons (kc, kc); its
        // proof section's count is the proof lane's (darkproof::run::release_section), never a default here
        let v: Vec<usize> = r.split(',').map(|x| x.parse().expect("--release M,NCLS,KC")).collect();
        assert_eq!(v.len(), 3, "--release M,NCLS,KC");
        let n = m.get("proof-triples").expect("--release needs --proof-triples N (darkproof::run::release_section)").parse().expect("--proof-triples");
        // --lookup-triples T: the release's lookups as T Beaver triples each (darkproof's L cut, RS + LB; 27 at GEN6)
        let lt: usize = get(m, "lookup-triples", 0);
        return sp.release(darkprep::schedule::Release { m: v[0], ncls: v[1], kc: v[2] as u32, lookup_triples: lt }, n);
    }
    if let Some(n) = m.get("handover-ar") {
        // a new seat's handover tape: N auth_plain entries (2 d^2 + 16 for darkhand::side::new_side)
        return sp.handover(n.parse().expect("--handover-ar N"));
    }
    if m.contains_key("proof") {
        // the count is the proof lane's (darkproof::run::step_section; `darkproof counts D PROFILE`), which changes
        // with its method; there is no default here so a stale formula can never size a tape
        sp.proof_atoms = true;
        sp.proof_triples = m.get("proof-triples").expect("--proof needs --proof-triples N (darkproof counts)").parse().expect("--proof-triples");
    }
    sp
}


/// The seat's vault (--vault NAME or --vault-file PATH holding NAME), or None for a TEST build's --plain-tapes.
fn load_vault(m: &HashMap<String, String>) -> Result<Option<darkhand::vault::Vault>, String> {
    let name = match (m.get("vault"), m.get("vault-file")) {
        (Some(n), _) => Some(n.trim().to_string()),
        (None, Some(f)) => Some(std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?.trim().to_string()),
        (None, None) => None,
    };
    match name {
        Some(n) => darkhand::vault::Vault::load(&n).map(Some),
        None if cfg!(feature = "test-plain-tapes") && m.contains_key("plain-tapes") => Ok(None),
        None => Err("--vault NAME or --vault-file TLSDIR/vault.name is required: tapes at rest are sealed under the seat's epoch file key (a test build takes --plain-tapes)".into()),
    }
}

/// One custodian's part of one chunk (see the header). Returns the measurement JSON.
fn party_chunk(m: &HashMap<String, String>, out: &Path) -> Result<String, String> {
    let party: usize = m.get("party").expect("--party").parse().unwrap();
    // the seat's epoch file key, loaded (never made) here: dl-custodian vault-init made it; NAME from --vault NAME or
    // the consuming seat's TLSDIR/vault.name (--vault-file). Loaded before the MASCOT run, so a missing key costs no run.
    let vault = load_vault(m)?;
    let chunk_name = out.file_name().map(|s| s.to_string_lossy().into_owned()).ok_or("--out needs a directory name")?;
    let sp = chunk_step(m);
    let steps: usize = get(m, "steps", 1);
    if sp.phase != darkprep::schedule::Phase::Step && (steps != 1 || m.contains_key("genesis")) {
        return Err("a release or handover chunk is one tape: --steps 1, no --genesis".into());
    }
    if !m.contains_key("new-mac-key") && !m.contains_key("plaintext") {
        // MP-SPDZ silently draws a fresh MAC key when it finds none, so a chunk meant for an existing key (whose files
        // a handover just erased, say) would come out under a key no other chunk shares: refuse instead
        let backend = m.get("backend").map(|s| s.as_str()).unwrap_or("mascot");
        let dir = PathBuf::from(m.get("mpspdz").expect("--mpspdz")).join("Player-Data");
        if !darkprep::mpspdz::has_mac_key(&dir, backend, party) {
            return Err(format!("no {backend} MAC key share for party {party} in {}; pass --new-mac-key to draw a fresh one", dir.display()));
        }
    }
    if m.contains_key("new-mac-key") {
        // this custodian's MAC key share is retired first, so MP-SPDZ generates a fresh one for this run (a new
        // committee, or the same seats after an abort); later chunks reuse it
        let retired = darkprep::mpspdz::retire_mac_keys(&PathBuf::from(m.get("mpspdz").expect("--mpspdz")), Some(party));
        eprintln!("darkprep: new MAC key; retired {retired:?}");
    }
    let p: u64 = get(m, "p", 0);
    let mpspdz = PathBuf::from(m.get("mpspdz").expect("--mpspdz"));
    // --genesis: step 0 of this chunk inputs W1, W2, x, y (2 d^2 + 2 d); the others carry the weights (x, y: 2 d)
    let chunk: Vec<StepParams> = (0..steps)
        .map(|j| {
            let mut q = sp;
            if m.contains_key("genesis") {
                q.inputs = if j == 0 { darkprep::schedule::Inputs::Harness } else { darkprep::schedule::Inputs::Steady };
            }
            q
        })
        .collect();
    let plan = darkprep::schedule::plan_of_steps(&chunk);
    if let Some(src) = m.get("mpc-src") {
        std::fs::copy(src, mpspdz.join("Programs/Source/darkprep.mpc")).map_err(|e| e.to_string())?;
    }
    let margs = plan.mpc_args(get(m, "threads", 1), get(m, "batch", 1000));
    let tc = std::time::Instant::now();
    let prog = Run::compile(&mpspdz, &margs)?;
    let compile_s = tc.elapsed().as_secs_f64();
    let tmp = PathBuf::from(format!("{}.tmp-P{party}", out.display()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
    let mut extra = vec!["-d".to_string()];
    if let Some(x) = m.get("extra") {
        extra.extend(x.split(',').map(String::from));
    }
    let run = darkprep::mpspdz::PartyRun {
        backend: m.get("backend").cloned().unwrap_or_else(|| "mascot".into()),
        mpspdz: mpspdz.clone(), prog: prog.clone(), p, party,
        ipfile: PathBuf::from(m.get("ipfile").expect("--ipfile")).canonicalize().map_err(|e| e.to_string())?,
        plaintext: m.contains_key("plaintext"), extra, workdir: tmp.clone(),
    };
    let r = run.execute()?;
    let ta = std::time::Instant::now();
    let txf = mpspdz.join(format!("Persistence/Transactions-P{party}.data"));
    let tx = Transactions::read(&txf, p)?;
    // each step's tape and owner message, assembled in memory and sealed under the seat's epoch file key (vault):
    // no plaintext tape reaches a disk. TEST builds may instead stream plain DLTAPE01 files (--plain-tapes), and then
    // also the whole-chunk file (every step back to back, one alpha; a hard link when there is one step).
    let ns: Vec<usize> = chunk.iter().map(darkprep::schedule::n_entries).collect();
    let all_path = tmp.join(format!("tape_{party}.bin"));
    let whole = vault.is_none() && !m.contains_key("step-tapes-only");
    let mut all = if whole && steps > 1 { Some(darkprep::tape::DarkstepWriter::create(&all_path, tx.alpha_i, ns.iter().sum()).map_err(|e| e.to_string())?) } else { None };
    let mut entries = Vec::new();
    for j in 0..steps {
        let sd = tmp.join(format!("step-{j}"));
        std::fs::create_dir_all(&sd).map_err(|e| e.to_string())?;
        let tpath = sd.join(format!("tape_{party}.bin"));
        let mut n = 0usize;
        if let (Some(v), darkprep::schedule::Phase::Release(_)) = (&vault, chunk[j].phase) {
            // the release tape (gigabytes): DLVAULT2 blocks, written as assembled, never whole in memory
            let key = dlvault::Key::new(&v.name, v.key_bytes());
            let mut w = darkprep::tape::SealedDarkstepWriter::create(&tpath, &key, &darkprep::tape::tape_role(&chunk_name, j), tx.alpha_i, ns[j]).map_err(|e| e.to_string())?;
            let mut err: Option<std::io::Error> = None;
            darkprep::tape::assemble_in_chunk_emit(&chunk, &tx, party as u32, j, &mut |t, sm| {
                n += 1;
                if let Err(e) = w.push(t, sm) {
                    err.get_or_insert(e);
                }
            })?;
            if let Some(e) = err {
                return Err(e.to_string());
            }
            w.finish().map_err(|e| e.to_string())?;
        } else if let Some(v) = &vault {
            let mut buf = darkprep::tape::DarkstepBuf::new(tx.alpha_i, ns[j]);
            let mut err: Option<String> = None;
            darkprep::tape::assemble_in_chunk_emit(&chunk, &tx, party as u32, j, &mut |t, sm| {
                n += 1;
                if let Err(e) = buf.push(t, sm) {
                    err.get_or_insert(e);
                }
            })?;
            if let Some(e) = err {
                return Err(e);
            }
            v.seal_to(&tpath, &darkprep::tape::tape_role(&chunk_name, j), buf.finish()?).map_err(|e| e.to_string())?;
        } else {
            let mut one = darkprep::tape::DarkstepWriter::create(&tpath, tx.alpha_i, ns[j]).map_err(|e| e.to_string())?;
            let mut err: Option<std::io::Error> = None;
            darkprep::tape::assemble_in_chunk_emit(&chunk, &tx, party as u32, j, &mut |t, sm| {
                n += 1;
                let r = one.push(t, sm).and_then(|_| match all.as_mut() { Some(a) => a.push(t, sm), None => Ok(()) });
                if let Err(e) = r {
                    err.get_or_insert(e);
                }
            })?;
            if let Some(e) = err {
                return Err(e.to_string());
            }
            one.finish().map_err(|e| e.to_string())?;
        }
        if n != ns[j] {
            return Err(format!("step {j}: assembled {n} entries, the schedule has {}", ns[j]));
        }
        entries.push(n);
        let msg = owner::custodian_message_in_chunk(&chunk, &tx, j);
        let mpath = sd.join(format!("owner-msg-P{party}.bin"));
        let mut mb: Vec<u8> = Vec::new();
        owner::write_message(&mut mb, &msg).map_err(|e| e.to_string())?;
        match &vault {
            Some(v) => v.seal_to(&mpath, &darkprep::tape::owner_msg_role(&chunk_name, j), mb).map_err(|e| e.to_string())?,
            None => std::fs::write(&mpath, &mb).map_err(|e| e.to_string())?,
        }
    }
    match all {
        Some(a) => a.finish().map_err(|e| e.to_string())?,
        None if !whole => {}
        None => std::fs::hard_link(tmp.join(format!("step-0/tape_{party}.bin")), &all_path).map_err(|e| e.to_string())?,
    }
    drop(tx);
    // the tapes are now the only copy of this party's shares: overwrite, sync and unlink MP-SPDZ's copies (the
    // Transactions file, and its memory dump, which can hold the last batch's sint registers)
    darkprep::mpspdz::wipe_file(&txf).map_err(|e| e.to_string())?;
    let mem = mpspdz.join(format!("Player-Data/Memory-p-P{party}"));
    if mem.exists() {
        darkprep::mpspdz::wipe_file(&mem).map_err(|e| e.to_string())?;
    }
    let asm_s = ta.elapsed().as_secs_f64();
    let links = r.links.iter().map(|(ip, s, rcv)| format!("{{\"peer\": \"{ip}\", \"sent_bytes\": {s}, \"received_bytes\": {rcv}}}")).collect::<Vec<_>>().join(", ");
    let j = format!(
        "{{\"party\": {party}, \"chunk\": \"{}\", \"d\": {}, \"mode\": \"{:?}\", \"phase\": \"{:?}\", \"steps\": {steps}, \"proof_atoms\": {}, \"proof_triples_per_step\": {}, \"tape_entries_per_step\": {entries:?}, \"genesis\": {}, \"plan\": {{\"in\": {}, \"ar\": {}, \"tri\": {}, \"lp\": {}, \"trunc_classes\": [{}]}}, \"prog\": \"{prog}\", \"backend\": \"{}\", \"tls\": {}, \"compile_s\": {compile_s:.3}, \"wall_s\": {:.3}, \"assemble_s\": {asm_s:.3}, \"cpu_user_s\": {:.2}, \"cpu_sys_s\": {:.2}, \"max_rss_kb\": {}, \"mpspdz_sent_bytes\": {:.0}, \"mpspdz_rounds\": {}, \"links\": [{links}]}}",
        out.display(), sp.d, sp.inputs, sp.phase, sp.proof_atoms, sp.proof_triples, m.contains_key("genesis"), plan.n_in, plan.n_ar, plan.n_tri, plan.n_lp,
        plan.trunc_classes.iter().map(|(a, b, c)| format!("[{a}, {b}, {c}]")).collect::<Vec<_>>().join(", "),
        m.get("backend").map(|s| s.as_str()).unwrap_or("mascot"), !m.contains_key("plaintext"), r.wall_s, r.cpu_user_s, r.cpu_sys_s, r.max_rss_kb, r.stats.sent_bytes, r.stats.rounds
    );
    std::fs::write(tmp.join(format!("chunk-P{party}.json")), &j).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_dir_all(out);
    std::fs::rename(&tmp, out).map_err(|e| e.to_string())?;
    Ok(j)
}
