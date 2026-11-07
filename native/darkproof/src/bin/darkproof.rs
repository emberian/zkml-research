//! darkproof CLI: bit-exact checks against the harness's vectors, and timing runs.
//!   darkproof check VECDIR TAG        # TAG e.g. demo_d4: native bundles == Python bundles, cross-verify
use darkproof::h::unhex32;
use darkproof::rng::Det;
use darkproof::witness::{make_bundle, BundleOpts, Witness};
use darkproof::{wire, Ctx, Profile};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::Path;

fn sha(b: &[u8]) -> String {
    darkproof::h::hex(&Sha256::digest(b))
}

fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    (0..a.len().min(b.len())).find(|&i| a[i] != b[i]).or(if a.len() != b.len() { Some(a.len().min(b.len())) } else { None })
}

fn roots_of(v: &Value) -> BTreeMap<String, Vec<[u8; 32]>> {
    v.as_object()
        .unwrap()
        .iter()
        .map(|(k, a)| (k.clone(), a.as_array().unwrap().iter().map(|h| unhex32(h.as_str().unwrap()).unwrap()).collect()))
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if matches!(args.get(1).map(|s| s.as_str()), Some("check" | "rows" | "ds-check" | "rel-check")) && !cfg!(feature = "test-det") {
        eprintln!("bit-exact checks need the deterministic hook: build with --features test-det");
        std::process::exit(2);
    }
    match args.get(1).map(|s| s.as_str()) {
        Some("check") => check(Path::new(&args[2]), &args[3]),
        Some("rows") => rows(Path::new(&args[2]), &args[3]),
        Some("gen-check") => gen_check(Path::new(&args[2]), &args[3]),
        Some("bench") => bench(args[2].parse().unwrap(), &args[3]),
        Some("run-check") => run_check(Path::new(&args[2]), &args[3]),
        Some("rel-check") => rel_check(Path::new(&args[2]), &args[3]),
        Some("counts") => counts(args[2].parse().unwrap(), &args[3]),
        #[cfg(feature = "tcp")]
        Some("ds-check") => ds_check(Path::new(&args[2]), &args[3]),
        #[cfg(feature = "tcp")]
        Some("ds-bench") => ds_bench(args[2].parse().unwrap(), &args[3]),
        #[cfg(feature = "tcp")]
        Some("ds-chain") => ds_chain(args[2].parse().unwrap(), &args[3], args[4].parse().unwrap(), args[5].parse().unwrap()),
        _ => eprintln!("usage: darkproof check VECDIR TAG"),
    }
}

/// The step program a vector set was made with (meta "program"; absent: the harness's).
fn program_of(meta: &Value, d: usize) -> darkproof::step::StepParams {
    match meta.get("program") {
        None => darkproof::step::StepParams::for_width(d),
        Some(p) => {
            let w = darkproof::step::StepParams::for_width(d);
            let f = |k: &str, dflt: u32| p.get(k).and_then(|v| v.as_u64()).map(|v| v as u32).unwrap_or(dflt);
            let g = |k: &str, dflt: i64| p.get(k).and_then(|v| v.as_i64()).unwrap_or(dflt);
            darkproof::step::StepParams { s1: f("S1", w.s1), k1: f("K1", w.k1), s2: f("S2", w.s2), k2: f("K2", w.k2), s3: f("S3", w.s3), k3: f("K3", w.k3), he: p["he"].as_bool().unwrap_or(false), rc: p["RC"].as_bool().unwrap_or(false), r3: g("R3", 0), t_lo: g("T_LO", -128), lb: p["LB"].as_bool().unwrap_or(false), pg: None }
        }
    }
}

/// TAG e.g. demo_d4 (the harness's pw bundles) or demo_d4_he (the deployed step's chain he1, he2, ...).
fn check(dir: &Path, tag: &str) {
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    darkproof::field::set_p(meta["p"].as_u64().unwrap());
    let prm = program_of(&meta, meta["d"].as_u64().unwrap() as usize);
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let det = Det(Some(meta["seed"].as_str().unwrap().to_string()));
    let opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det, spine_attack: None, fs_public_attack: false, diagnose: true, transport: darkproof::net::transport_from_env(), prm: Some(prm) };
    let mut ok_all = true;
    let groots = roots_of(&meta["genesis_roots"]);
    let mut carry = None;
    let mut parent = groots.clone();
    let mut names: Vec<String> =
        meta["bundles"].as_object().unwrap().keys().filter(|k| k.starts_with("pw") || k.starts_with("he")).cloned().collect();
    names.sort();
    for name in names.iter().map(|s| s.as_str()) {
        let b = &meta["bundles"][name];
        let c = b["ctx"].as_array().unwrap();
        let ctx = Ctx::new(c[0].as_str().unwrap(), c[1].as_u64().unwrap(), c[2].as_u64().unwrap());
        let w = Witness::load(&dir.join(b["witness"].as_str().unwrap()));
        let pyb = std::fs::read(dir.join(b["blob"].as_str().unwrap())).unwrap();
        let out = make_bundle(&opts, w.clone(), &ctx, carry.take(), None).expect("prove");
        if let Some(g) = &out.genesis_roots {
            assert_eq!(g, &groots, "genesis roots differ");
        }
        let eq = out.blob == pyb;
        ok_all &= eq;
        println!(
            "{tag} {name}: native {} bytes sha256 {} | python {} bytes sha256 {} | {} | prove {:.2}s | violates {:?} {:?}",
            out.blob.len(),
            &sha(&out.blob)[..16],
            pyb.len(),
            &sha(&pyb)[..16],
            if eq { "EQUAL".to_string() } else { format!("DIFFER at offset {:?}", first_diff(&out.blob, &pyb)) },
            out.prove_secs,
            out.spine_violates,
            out.middle_violates
        );
        let t = std::time::Instant::now();
        let v = wire::verify_step(&pr, &lp, &pyb, &ctx, &parent, &tables, w.d, prm, None, 0);
        println!("  native verify of the python bundle: {:?} ({:.2}s)", v.as_ref().map(|_| "accept"), t.elapsed().as_secs_f64());
        ok_all &= v.is_ok();
        let mut bad = pyb.clone();
        let pos = bad.len() / 2;
        bad[pos] ^= 1;
        let v2 = wire::verify_step(&pr, &lp, &bad, &ctx, &parent, &tables, w.d, prm, None, 0);
        println!("  native verify, one flipped byte at {pos}: {:?}", v2.as_ref().map(|_| "accept"));
        ok_all &= v2.is_err();
        std::fs::write(dir.join(format!("{tag}_{name}.native.bin")), &out.blob).unwrap();
        parent = v.map(|a| a.child).unwrap_or(parent);
        carry = Some(out.child);
    }
    if let Some(b) = meta["bundles"].get("si1") {
        let xy = &meta["si_xy"];
        let v = |k: &str| xy[k].as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect::<Vec<u64>>();
        let mut owner = darkproof::owner::Owner::new(pr.owner_h, Some((0u8..32).collect()), None);
        assert_eq!(darkproof::h::hex(&owner.pk), b["owner_pk"].as_str().unwrap(), "owner public key differs");
        let ctx = Ctx::new("mind-0", 0, 1);
        let w = Witness::load(&dir.join(b["witness"].as_str().unwrap()));
        let pyb = std::fs::read(dir.join(b["blob"].as_str().unwrap())).unwrap();
        let out = make_bundle(&opts, w.clone(), &ctx, None, Some(darkproof::witness::OwnerIn { owner: &mut owner, x: v("x"), y: v("y") })).unwrap();
        let eq = out.blob == pyb;
        ok_all &= eq;
        println!(
            "{tag} si1 (owner-signed): native {} bytes sha256 {} | python {} bytes sha256 {} | {}",
            out.blob.len(), &sha(&out.blob)[..16], pyb.len(), &sha(&pyb)[..16],
            if eq { "EQUAL".to_string() } else { format!("DIFFER at offset {:?}", first_diff(&out.blob, &pyb)) }
        );
        let groots = roots_of(&meta["si_genesis_roots"]);
        let v1 = wire::verify_step(&pr, &lp, &pyb, &ctx, &groots, &tables, w.d, darkproof::step::StepParams::for_width(w.d), Some(&owner.pk), 0);
        println!("  native verify of the python bundle: {:?}", v1.as_ref().map(|_| "accept"));
        ok_all &= v1.is_ok();
        let mut bad = pyb.clone();
        let l = bad.len();
        bad[l - 100] ^= 1;
        let v2 = wire::verify_step(&pr, &lp, &bad, &ctx, &groots, &tables, w.d, darkproof::step::StepParams::for_width(w.d), Some(&owner.pk), 0);
        println!("  native verify, one flipped signature byte: {:?}", v2.as_ref().map(|_| "accept"));
        ok_all &= v2.is_err();
        std::fs::write(dir.join(format!("{tag}_si1.native.bin")), &out.blob).unwrap();
    }
    println!("{}", if ok_all { "CHECK PASS" } else { "CHECK FAIL" });
    std::process::exit(if ok_all { 0 } else { 1 });
}

/// The deployed run's per-party prover (darkproof::run::prove_step) on a vector chain (TAG e.g. demo_d4_he): three
/// custodian threads, each with ONLY its own shares, MAC key share and tape (a seeded stand-in for its MASCOT tape:
/// authenticated triples under the step's MAC key, never a shared dealer stream). Checks: every party ends with the
/// same bundle; the native verifier accepts it chained from the genesis roots; a tape triple off by one at one
/// custodian aborts the proof (MAC check).
fn run_check(dir: &Path, tag: &str) {
    use darkproof::run::{n_had, prove_step, tape_triples, PartyStep};
    use darkproof::spdz::{Dealer, Triple};
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    darkproof::field::set_p(meta["p"].as_u64().unwrap());
    let d = meta["d"].as_u64().unwrap() as usize;
    let prm = program_of(&meta, d);
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let mut names: Vec<String> = meta["bundles"].as_object().unwrap().keys().cloned().collect();
    names.sort();
    let mut parent = roots_of(&meta["genesis_roots"]);
    let mut carry: Vec<Option<BTreeMap<String, darkproof::pcs::PcsParty>>> = vec![None, None, None];
    let mut ok_all = true;
    for (k, name) in names.iter().enumerate() {
        let b = &meta["bundles"][name.as_str()];
        let c = b["ctx"].as_array().unwrap();
        let ctx = Ctx::new(c[0].as_str().unwrap(), c[1].as_u64().unwrap(), c[2].as_u64().unwrap());
        let w = Witness::load(&dir.join(b["witness"].as_str().unwrap()));
        let nt = darkproof::run::step_section(&lp, d, prm, prm.carried(ctx.step), &tables);
        // the custodians' tapes: authenticated triples under the step's alpha (stand-in for MASCOT)
        let mut tdl = Dealer::from_state(&pycompat::PyRandom::from_u64(1000 + k as u64).state(), w.alpha_sh.clone());
        let mut tapes: Vec<Vec<Triple>> = vec![Vec::with_capacity(nt); 3];
        for _ in 0..nt {
            let av = tdl.rng.randrange_u64(darkproof::field::p());
            let bv = tdl.rng.randrange_u64(darkproof::field::p());
            let (a, b2, cc) = (tdl.auth_all(av), tdl.auth_all(bv), tdl.auth_all(darkproof::field::mul(av, bv)));
            for i in 0..3 {
                tapes[i].push((a[i], b2[i], cc[i]));
            }
        }
        let run = |tapes: Vec<Vec<Triple>>, carry: Vec<Option<BTreeMap<String, darkproof::pcs::PcsParty>>>| {
            let nets = darkproof::net::Nets::new(darkproof::net::transport_from_env(), 3);
            let t0 = std::time::Instant::now();
            let outs: Vec<Result<darkproof::run::StepProof, String>> = std::thread::scope(|s| {
                let hs: Vec<_> = tapes
                    .into_iter()
                    .zip(carry)
                    .enumerate()
                    .map(|(i, (tp, cy))| {
                        let (nets, w, pr, lp, tables, ctx) = (&nets, &w, &pr, &lp, &tables, &ctx);
                        s.spawn(move || {
                            let mut net = nets.take(i);
                            let st = PartyStep {
                                i,
                                n: 3,
                                d,
                                alpha_i: w.alpha_sh[i],
                                wires: w.wires[i].clone(),
                                public: w.public.clone(),
                                atoms: w.atoms[i].clone(),
                                triples: tp,
                                det: darkproof::rng::Det(None),
                                ignore_range: false,
                            };
                            prove_step(pr, lp, tables, prm, &mut *net, ctx, st, cy)
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap_or_else(|_| Err("party panicked".into()))).collect()
            });
            (outs, t0.elapsed().as_secs_f64())
        };
        // negative controls first (on clones of the carry), at custodian 1's first middle triple:
        //   c's value share off by one (a wrong product: its MAC is untouched, the proof's constraints catch it)
        //   a's value share off by one (the opened e is not the authenticated one: the MAC check aborts)
        let jb = darkproof::spine::beaver_count(d);
        for (what, slot) in [("c", 2usize), ("a", 0usize)] {
            let mut bad = tapes.clone();
            let t = &mut bad[1][jb];
            let sh = match slot { 0 => &mut t.0, _ => &mut t.2 };
            sh.0 = darkproof::field::add(sh.0, 1);
            let cl = carry.iter().map(|c| c.as_ref().map(|m| m.iter().map(|(k, p)| (k.clone(), darkproof::witness::clone_pcs(p))).collect())).collect();
            let (bo, _) = run(bad, cl);
            let verdict = match &bo[0] {
                Err(e) => format!("REFUSED in proving ({e})"),
                Ok(p) => {
                    let gp = p.genesis_roots.clone().unwrap_or_else(|| parent.clone());
                    match wire::verify_step(&pr, &lp, &p.blob, &ctx, &gp, &tables, d, prm, None, 0) {
                        Err(e) => format!("REFUSED by the verifier ({e})"),
                        Ok(_) => "ACCEPTED".into(),
                    }
                }
            };
            println!("{tag} {name}: tape triple {what} share off by one at custodian 1: {verdict}");
            ok_all &= verdict.starts_with("REFUSED");
        }
        let (outs, secs) = run(tapes.clone(), std::mem::take(&mut carry));
        if k == 0 {
            // production coins: a second proof of the same witness and tape differs in bytes, and verifies too
            let (o2, _) = run(tapes, vec![None, None, None]);
            let p2 = o2.into_iter().next().unwrap().expect("second proof");
            let g2 = p2.genesis_roots.clone().unwrap();
            let v2 = wire::verify_step(&pr, &lp, &p2.blob, &ctx, &g2, &tables, d, prm, None, 0);
            let differ = match &outs[0] { Ok(p1) => p1.blob != p2.blob, Err(_) => false };
            println!("{tag} {name}: a second production proof of the same witness: bytes differ {differ}, verifies {:?}", v2.as_ref().map(|_| "accept"));
            ok_all &= differ && v2.is_ok();
        }
        let mut parts = Vec::new();
        for o in outs {
            match o {
                Ok(p) => parts.push(p),
                Err(e) => {
                    println!("{tag} {name}: prove failed: {e}");
                    std::process::exit(1);
                }
            }
        }
        let same = parts.iter().all(|p| p.blob == parts[0].blob);
        if let Some(g) = &parts[0].genesis_roots {
            parent = g.clone();
        }
        let t = std::time::Instant::now();
        let v = wire::verify_step(&pr, &lp, &parts[0].blob, &ctx, &parent, &tables, d, prm, None, 0);
        println!(
            "{tag} {name}: {} triples per tape; prove {:.2}s; {} bytes; parties agree: {}; sent per party {} elements; verify {:?} ({:.2}s)",
            nt, secs, parts[0].blob.len(), same, parts[0].sent, v.as_ref().map(|_| "accept"), t.elapsed().as_secs_f64()
        );
        ok_all &= same && v.is_ok();
        parent = v.map(|a| a.child).unwrap_or(parent);
        carry = parts.into_iter().map(|p| Some(p.child)).collect();
    }
    println!("{}", if ok_all { "RUN-CHECK PASS" } else { "RUN-CHECK FAIL" });
    std::process::exit(if ok_all { 0 } else { 1 });
}

/// One custodian's HE helper state as darkstep's node builds it (OwnKey from the harness's key seed, public keys
/// exchanged over CTRL; ungated).
#[cfg(feature = "tcp")]
fn ds_he(i: usize, pf: &darkstep::node::Prof, net: &darkstep::net::Net) -> darkstep::he::He {
    use darkstep::net::{bytes_to_u64s, u64s_to_bytes};
    use std::sync::Arc;
    let rns = Arc::new(darkstep::rns::Rns::new(pf.n, &pf.qs, pf.t));
    let key = darkstep::bfv::OwnKey::new(rns.clone(), darkstep::node::KEY_SEED0 + i as u64);
    let mut mine = key.pk.pk0_ntt.clone();
    mine.extend_from_slice(&key.pk.pk1_ntt);
    let all = net.exchange_bytes(darkstep::net::CTRL, &u64s_to_bytes(&mine));
    let ln = rns.l() * rns.n;
    let pks = all
        .iter()
        .map(|b| {
            let v = bytes_to_u64s(b);
            darkstep::bfv::PubKey { pk0_ntt: v[..ln].to_vec(), pk1_ntt: v[ln..].to_vec() }
        })
        .collect();
    darkstep::he::He {
        rns, key, pks, f_bits: pf.f_bits, mv_seed: darkstep::node::MV_SEED, ou_seed: darkstep::node::OU_SEED,
        mv_calls: 0, ou_calls: 0, context: ("model".into(), 0, 0), he_send: 0, he_return: 0, ou_send: 0,
        ou_return: 0, ou_commit: 0, cts_sent: 0, cts_returned: 0, attack: None, gate: None,
    }
}

/// Timing of the deployed step and its proof in one process: darkstep's genesis HE step (ideal-dealer tapes with
/// the proof atoms and the FULL proof section, Ligero triples included) and darkproof::run::prove_step with
/// production coins, three custodian threads over 127.0.0.1 sockets. D = width, PROFILE = demo | ledger; the program
/// is StepParams::for_width(D).deployed() unless DP_PROGRAM='{"S1":..,"R3":..,"T_LO":..}' says otherwise.
#[cfg(feature = "tcp")]
fn ds_bench(d: usize, prof: &str) {
    use darkproof::run::{from_darkstep, n_had, prove_step, tape_triples, TcpRef};
    use std::sync::Arc;
    let pr = Profile::by_name(prof).unwrap();
    let p = wire::he_field(&pr).unwrap();
    darkproof::field::set_p(p);
    let lp = pr.ligero();
    let prm = match std::env::var("DP_PROGRAM") {
        Ok(j) => program_of(&serde_json::json!({ "program": serde_json::from_str::<Value>(&j).unwrap() }), d).deployed(),
        Err(_) => darkproof::step::StepParams::for_width(d).deployed(),
    };
    let tables = darkproof::step::tables_for(prm.t_lo);
    let pf = darkstep::node::prof(&[pr.he.0.to_string(), pr.he.1.to_string(), pr.he.2.to_string(), d.to_string()]);
    assert_eq!(pf.t, p);
    let pg = darkstep::step::Program { s1: prm.s1, k1: prm.k1, s2: prm.s2, k2: prm.k2, s3: prm.s3, k3: prm.k3, r3: prm.r3, t_lo: prm.t_lo, xmax: 7, wmax: None, check_k: false };
    let t0 = std::time::Instant::now();
    let nt = darkproof::run::step_section(&lp, d, prm, false, &tables);
    let plain = darkstep::step::inputs(d);
    let (cs, mut dl) = darkstep::tape::deal_step_dealer_prog(p, d, darkstep::node::DEALER_SEED, darkstep::node::OWNER_SEED, &plain.flat_mod(p), true, &pg);
    darkstep::tape::deal_proof_section(&mut dl, nt);
    let tapes = dl.tapes;
    println!("d={d} profile={prof} program={prm:?} proof-section triples {nt}; dealing {:.1}s", t0.elapsed().as_secs_f64());
    let ls: Vec<std::net::TcpListener> = (0..3).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<std::net::SocketAddr> = ls.iter().map(|l| l.local_addr().unwrap()).collect();
    let cs = Arc::new(cs);
    let threads = std::env::var("DS_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let outs: Vec<(f64, f64, Vec<u8>, u64, BTreeMap<String, Vec<[u8; 32]>>)> = std::thread::scope(|s| {
        let hs: Vec<_> = ls
            .into_iter()
            .zip(tapes)
            .enumerate()
            .map(|(i, (l, tape))| {
                let (addrs, cs, pf, pr, lp, tables, pg) = (&addrs, cs.clone(), &pf, &pr, &lp, &tables, &pg);
                s.spawn(move || {
                    let net = darkstep::net::Net::connect(i, l, addrs);
                    let mut he = ds_he(i, pf, &net);
                    let tab = pg.tables(pf.t);
                    let mut pt = darkstep::party::Party::new(i, pf.t, net, tape);
                    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
                    let t = std::time::Instant::now();
                    let out = pool.install(|| darkstep::step::run_step_prog(&mut pt, &mut he, &cs, d, &tab, pg)).expect("darkstep step");
                    let step_s = t.elapsed().as_secs_f64();
                    let st = from_darkstep(i, d, &out.record, &out.w1n, &out.w2n, &pt.tape, Det::off()).expect("record");
                    drop(out);
                    let mut tn = TcpRef(&pt.net);
                    let ctx = Ctx::new("mind-0", 0, 1);
                    let sp = pool.install(|| prove_step(pr, lp, tables, prm, &mut tn, &ctx, st, None)).expect("prove");
                    (step_s, sp.secs, sp.blob, sp.sent, sp.genesis_roots.unwrap())
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let agree = outs.iter().all(|o| o.2 == outs[0].2);
    for (i, o) in outs.iter().enumerate() {
        println!("party {i}: step {:.1}s, prove {:.1}s, proof sent {} elements ({:.1} MB)", o.0, o.1, o.3, o.3 as f64 * 8.0 / 1e6);
    }
    println!("bundle {} bytes; parties agree {agree}; peak RSS {:.2} GB", outs[0].2.len(), peak_rss_gb());
    let t = std::time::Instant::now();
    let v = wire::verify_step(&pr, &lp, &outs[0].2, &Ctx::new("mind-0", 0, 1), &outs[0].4, &tables, d, prm, None, 0);
    println!("verify {:.1}s {:?}", t.elapsed().as_secs_f64(), v.as_ref().map(|_| "accept"));
    println!("bench rows");
}

/// The run in one process: three custodian threads over 127.0.0.1 sockets run STEPS deployed steps (genesis, then
/// carried) on ONE tape each (a test dealer standing in for MASCOT: step, its proof section, the next step, ..., the
/// release section, the release's proof section), prove every step with run::prove_step (production coins), a
/// native ledger accepts every bundle, then the custodians run the release program on the head's shares, prove it
/// (run::prove_release) and the ledger accepts the release. The released count must equal the plaintext twin's on
/// the revealed head (a test-only reveal). M public examples, X random in [0, 100], half the labels the plain
/// model's strict argmax.
#[cfg(feature = "tcp")]
fn ds_chain(d: usize, prof: &str, steps: usize, m: usize) {
    use darkproof::run::{deal_release, from_darkstep_n, n_had, plain_count, prove_release, prove_step, release_mpc, release_n_had, release_triples, tape_triples, tape_triples_at, Policy, TcpRef};
    use std::sync::Arc;
    let pr = Profile::by_name(prof).unwrap();
    let p = wire::he_field(&pr).unwrap();
    darkproof::field::set_p(p);
    let lp = pr.ligero();
    let prm = match std::env::var("DP_PROGRAM") {
        Ok(j) => program_of(&serde_json::json!({ "program": serde_json::from_str::<Value>(&j).unwrap() }), d).deployed(),
        Err(_) => darkproof::step::StepParams::for_width(d).deployed(),
    };
    // PUBLIC GENESIS (DP_PG_CFG=<darktrain cfg json>): W = darktrain::init(cfg) enters custody as a public constant,
    // committed with public coins; every step is the carried program
    let pg_cfg: Option<Vec<u8>> = std::env::var("DP_PG_CFG").ok().map(|f| std::fs::read(f).expect("DP_PG_CFG"));
    let mut prm = prm;
    if let Some(c) = &pg_cfg {
        use sha2::{Digest, Sha256};
        prm.pg = Some(Sha256::digest(c).into());
    }
    let pgw: Option<(Vec<i64>, Vec<i64>)> = pg_cfg.as_ref().map(|c| {
        let (dd, w1, w2) = darkproof::run::public_weights(c).unwrap();
        assert_eq!(dd, d, "the public genesis cfg's d");
        (w1, w2)
    });
    let tables = darkproof::step::tables_for(prm.t_lo);
    let pf = darkstep::node::prof(&[pr.he.0.to_string(), pr.he.1.to_string(), pr.he.2.to_string(), d.to_string()]);
    let pg = darkstep::step::Program { s1: prm.s1, k1: prm.k1, s2: prm.s2, k2: prm.k2, s3: prm.s3, k3: prm.k3, r3: prm.r3, t_lo: prm.t_lo, xmax: 7, wmax: None, check_k: false };
    let ncls = d.min(10);
    let kc = 10;
    // the public test set
    let mut xr = pycompat::PyRandom::from_u64(77);
    let xi: Vec<Vec<i64>> = (0..d).map(|_| (0..m).map(|_| xr.randrange_u64(101) as i64).collect()).collect();
    let x: Vec<u64> = (0..d).flat_map(|k| (0..m).map(move |t| (k, t))).map(|(k, t)| darkproof::field::from_i64(xi[k][t])).collect();
    // one test dealer for the run
    let t0 = std::time::Instant::now();
    let mut dl = darkstep::tape::Dealer::new(p, 3, darkstep::node::DEALER_SEED);
    dl.proof_rng = Some(pycompat::PyRandom::from_u64(1));
    let mut owner = pycompat::PyRandom::from_u64(darkstep::node::OWNER_SEED);
    let mut plain = darkstep::step::inputs(d);
    // BOUND CONTROL (DP_W2SCALE=s): W2 scaled at genesis so z2 leaves its declared bound 2^K1
    // (DP_W1SCALE=s: W1 scaled, so u1 = z1 >> S1 leaves the table's domain)
    let w2scale: Option<i64> = std::env::var("DP_W2SCALE").ok().map(|v| v.parse().unwrap());
    let w1scale: Option<i64> = std::env::var("DP_W1SCALE").ok().map(|v| v.parse().unwrap());
    for (sc, mtx) in [(w2scale, &mut plain.w2), (w1scale, &mut plain.w1)] {
        if let Some(sc) = sc {
            for r in mtx.iter_mut() {
                for v in r.iter_mut() {
                    *v *= sc;
                }
            }
        }
    }
    let w2scale = w2scale.or(w1scale);
    if let Some((w1, w2)) = &pgw {
        plain.w1 = (0..d).map(|j| w1[j * d..(j + 1) * d].to_vec()).collect();
        plain.w2 = (0..d).map(|j| w2[j * d..(j + 1) * d].to_vec()).collect();
    }
    let genesis = plain.flat_mod(p);
    let xy = genesis[2 * d * d..].to_vec();
    let mut css = Vec::new();
    let mut nts = Vec::new();
    for k in 0..steps {
        let inp = if k == 0 && pgw.is_none() { genesis.clone() } else { xy.clone() };
        css.push(darkstep::tape::deal_one_step(&mut dl, &mut owner, d, &inp, &pg));
        let nt = darkproof::run::step_section(&lp, d, prm, prm.carried(k as u64 + 1), &tables);
        darkstep::tape::deal_proof_section(&mut dl, nt);
        nts.push(nt);
    }
    let pol0 = Policy { x: x.clone(), labels: vec![0; m], ncls, kc, ignore_range: false };
    deal_release(&mut dl, d, m, ncls, prm, kc, &lp, &tables, &pol0);
    let tapes = dl.tapes;
    println!("d={d} profile={prof} steps={steps} M={m} program={prm:?}; dealing {:.1}s, tape {} entries per party", t0.elapsed().as_secs_f64(), tapes[0].len());
    let ls: Vec<std::net::TcpListener> = (0..3).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<std::net::SocketAddr> = ls.iter().map(|l| l.local_addr().unwrap()).collect();
    let css = Arc::new(css);
    let threads = std::env::var("DS_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    type Carry = BTreeMap<String, darkproof::pcs::PcsParty>;
    type DS = Vec<Vec<darkstep::party::Sh>>;
    let model = "mind-0";
    // phase 1: the steps and their proofs
    let mut parts: Vec<(darkstep::party::Party, Carry, DS, DS, Vec<Vec<u8>>, Option<BTreeMap<String, Vec<[u8; 32]>>>)> = std::thread::scope(|s| {
        let hs: Vec<_> = ls
            .into_iter()
            .zip(tapes)
            .enumerate()
            .map(|(i, (l, tape))| {
                let (addrs, css, pf, pr, lp, tables, pg, nts, pgw) = (&addrs, css.clone(), &pf, &pr, &lp, &tables, &pg, &nts, &pgw);
                s.spawn(move || {
                    let net = darkstep::net::Net::connect(i, l, addrs);
                    let mut he = ds_he(i, pf, &net);
                    let tab = pg.tables(pf.t);
                    let mut pt = darkstep::party::Party::new(i, pf.t, net, tape);
                    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
                    let (mut carry, mut head, mut blobs, mut groots): (Option<Carry>, Option<(DS, DS)>, Vec<Vec<u8>>, _) = (None, None, Vec::new(), None);
                    if let Some((w1, w2)) = pgw {
                        let (c, roots) = darkproof::run::public_genesis(pr, d, i, w1, w2, 3);
                        let sh = |w: &[i64]| -> DS {
                            (0..d).map(|j| (0..d).map(|k| pt.cadd(darkproof::field::from_i64(w[j * d + k]), darkstep::party::Sh { s: 0, m: 0 })).collect()).collect()
                        };
                        // CONTROL (DP_PG_TAMPER): custody holds W1 + e_00, not the public W its commitment is of
                        let mut w1c = w1.clone();
                        if std::env::var_os("DP_PG_TAMPER").is_some() {
                            w1c[0] += 1;
                        }
                        head = Some((sh(&w1c), sh(w2)));
                        carry = Some(c);
                        groots = Some(roots);
                    }
                    for k in 0..steps {
                        let ts = std::time::Instant::now();
                        // ProofRecord.public and .middle_atoms are cumulative over the party's life: keep this step's
                        let (t_from, a_from) = (pt.tr.v.len(), pt.atom_log.len());
                        let out = pool.install(|| match head.take() {
                            None => darkstep::step::run_step_prog(&mut pt, &mut he, &css[k], d, &tab, pg),
                            Some((m1, m2)) => {
                                let sx = pt.input_vec(&css[k][..d]);
                                let sy = pt.input_vec(&css[k][d..]);
                                darkstep::step::run_step_shares(&mut pt, &mut he, m1, m2, sx, sy, d, &tab, pg)
                            }
                        }).expect("darkstep step");
                        let step_s = ts.elapsed().as_secs_f64();
                        let mut st = from_darkstep_n(i, d, &out.record, &out.w1n, &out.w2n, &pt.tape, Some(nts[k]), Det::off()).expect("record");
                        st.public = pt.tr.v[t_from..].to_vec();
                        st.ignore_range = std::env::var_os("DP_IGNORE_RANGE").is_some();
                        st.atoms = pt.atom_log[a_from..].iter().flat_map(|r| r.clone().map(|j| (pt.tape.sh[j], pt.tape.mac[j]))).collect();
                        let ctx = Ctx::new(model, 0, k as u64 + 1);
                        let sp = {
                            let mut tn = TcpRef(&pt.net);
                            match pool.install(|| prove_step(pr, lp, tables, prm, &mut tn, &ctx, st, carry.take())) {
                                Ok(sp) => sp,
                                Err(e) => {
                                    println!("step {}: custodian {i}: {e}", k + 1);
                                    std::thread::sleep(std::time::Duration::from_millis(300));
                                    println!("REFUSED IN PROVING");
                                    std::process::exit(3);
                                }
                            }
                        };
                        pt.cur += 3 * nts[k];
                        if i == 0 {
                            println!("step {}: darkstep {:.1}s, proof {:.1}s, bundle {} bytes, proof sent {} elements", k + 1, step_s, sp.secs, sp.blob.len(), sp.sent);
                        }
                        if sp.genesis_roots.is_some() {
                            groots = sp.genesis_roots.clone();
                        }
                        blobs.push(sp.blob);
                        carry = Some(sp.child);
                        head = Some((out.w1n, out.w2n));
                    }
                    let (w1n, w2n) = head.unwrap();
                    (pt, carry.unwrap(), w1n, w2n, blobs, groots)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    // the ledger accepts every step
    let dir = std::env::temp_dir().join(format!("dp-chain-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let lpath = dir.join("mind-0.ledger");
    let cust = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<String>>();
    let mut lg = darkproof::ledger::Ledger::open(&lpath, model, &pr, Some(darkproof::ledger::Genesis { d, program: prm, owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: parts[0].5.clone().unwrap() })).unwrap();
    let mut ok_all = parts.iter().all(|p| p.4 == parts[0].4);
    if let (Some(cfg), Some((w1, _))) = (&pg_cfg, &pgw) {
        // public genesis: refused before the check, with another cfg, and with roots that are not the cfg's W
        let r0 = lg.accept(&lp, &parts[0].4[0], &tables);
        println!("public genesis: step 1 before the cfg check: {r0:?}");
        let mut other = cfg.clone();
        other.push(b'\n');
        let r1 = lg.check_public_genesis(&other);
        println!("public genesis: another cfg: {r1:?}");
        let mut w1b = w1.clone();
        w1b[0] += 1;
        let forged = darkproof::run::public_genesis_roots(&pr, d, &w1b, &vec![0; d * d], 3);
        let fpath = dir.join("forged.ledger");
        let mut fl = darkproof::ledger::Ledger::open(&fpath, model, &pr, Some(darkproof::ledger::Genesis { d, program: prm, owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: forged })).unwrap();
        let r2 = fl.check_public_genesis(cfg);
        println!("public genesis: roots of another W under the pinned cfg: {r2:?}");
        let t = std::time::Instant::now();
        let r3 = lg.check_public_genesis(cfg);
        println!("public genesis: the pinned cfg: {r3:?} ({:.1}s)", t.elapsed().as_secs_f64());
        ok_all &= r0.is_err() && r1.is_err() && r2.is_err() && r3.is_ok();
    }
    for (k, b) in parts[0].4.iter().enumerate() {
        let t = std::time::Instant::now();
        let r = lg.accept(&lp, b, &tables);
        println!("ledger accepts step {}: {:?} ({:.1}s)", k + 1, r, t.elapsed().as_secs_f64());
        ok_all &= r.is_ok();
    }
    if w2scale.is_some() {
        // the integer spec of one step (step_spec, exact floors, SIG/DSIG by their formulas) against the revealed head
        let (w1, w2, xv, yv) = (&plain.w1, &plain.w2, &plain.x, &plain.y);
        let sigf = |u: i64| (u.div_euclid(4)).clamp(-7, 7);
        let dsigf = |u: i64| if (-28..32).contains(&u) { 1 } else { 0 };
        let z1: Vec<i64> = (0..d).map(|j| (0..d).map(|k| w1[j][k] * xv[k]).sum()).collect();
        let u1: Vec<i64> = z1.iter().map(|z| z >> prm.s1).collect();
        let h: Vec<i64> = u1.iter().map(|&u| sigf(u)).collect();
        let g1: Vec<i64> = u1.iter().map(|&u| dsigf(u)).collect();
        let z2: Vec<i64> = (0..d).map(|j| (0..d).map(|k| w2[j][k] * h[k]).sum()).collect();
        let e: Vec<i64> = (0..d).map(|j| (z2[j] >> prm.s1) - yv[j]).collect();
        let d2: Vec<i64> = e.iter().map(|v| v >> prm.s2).collect();
        let b: Vec<i64> = (0..d).map(|k| (0..d).map(|j| w2[j][k] * d2[j]).sum()).collect();
        let d1: Vec<i64> = (0..d).map(|k| (b[k] * g1[k] + prm.r3) >> prm.s3).collect();
        let w2n: Vec<Vec<i64>> = (0..d).map(|j| (0..d).map(|k| w2[j][k] - d2[j] * h[k]).collect()).collect();
        let w1n: Vec<Vec<i64>> = (0..d).map(|j| (0..d).map(|k| w1[j][k] - d1[j] * xv[k]).collect()).collect();
        let mx = |v: &[i64]| v.iter().map(|x| x.abs()).max().unwrap();
        fn rev(ms: [&Vec<Vec<darkstep::party::Sh>>; 3], d: usize, p: u64) -> Vec<Vec<i64>> {
            (0..d).map(|r| (0..d).map(|c| { let v = (0..3).fold(0u64, |a, i| darkproof::field::add(a, ms[i][r][c].s)); if v > p / 2 { v as i64 - p as i64 } else { v as i64 } }).collect()).collect()
        }
        let hw1 = rev([&parts[0].2, &parts[1].2, &parts[2].2], d, p);
        let hw2 = rev([&parts[0].3, &parts[1].3, &parts[2].3], d, p);
        println!(
            "BOUND CONTROL: max |z1| = {} (bound 2^{} = {}), max |z2| = {} (bound 2^{} = {}), max |e| = {} (bound 2^{}), max |b g1 + R3| = {} (bound 2^{}); u1 in the table's domain: {}",
            mx(&z1), prm.k1, 1i64 << prm.k1, mx(&z2), prm.k1, 1i64 << prm.k1, mx(&e), prm.k2,
            (0..d).map(|k| (b[k] * g1[k] + prm.r3).abs()).max().unwrap(), prm.k3,
            u1.iter().all(|&u| u >= prm.t_lo && u < prm.t_lo + 256)
        );
        println!("BOUND CONTROL: the custodians' W1n equals the integer spec's: {}; W2n: {}", hw1 == w1n, hw2 == w2n);
        println!("{}", if ok_all { "BOUND CONTROL: the ledger ACCEPTED the out-of-bound step" } else { "BOUND CONTROL: refused" });
        std::process::exit(0);
    }
    // the plaintext twin on the revealed head (TEST ONLY)
    fn rev(ms: [&Vec<Vec<darkstep::party::Sh>>; 3], d: usize, p: u64) -> Vec<Vec<i64>> {
        (0..d).map(|r| (0..d).map(|c| { let v = (0..3).fold(0u64, |a, i| darkproof::field::add(a, ms[i][r][c].s)); if v > p / 2 { v as i64 - p as i64 } else { v as i64 } }).collect()).collect()
    }
    let hw1 = rev([&parts[0].2, &parts[1].2, &parts[2].2], d, p);
    let hw2 = rev([&parts[0].3, &parts[1].3, &parts[2].3], d, p);
    let sig = |u: i64| (u.div_euclid(4)).clamp(-7, 7);
    let mut lr = pycompat::PyRandom::from_u64(78);
    let labels: Vec<usize> = (0..m)
        .map(|t| {
            let h: Vec<i64> = (0..d).map(|j| sig((0..d).map(|k| hw1[j][k] * xi[k][t]).sum::<i64>() >> prm.s1)).collect();
            let o: Vec<i64> = (0..ncls).map(|c| (0..d).map(|k| hw2[c][k] * h[k]).sum::<i64>() >> prm.s1).collect();
            let r = lr.randrange_u64(ncls as u64) as usize;
            if t % 2 == 0 { (0..ncls).max_by_key(|&c| (o[c], std::cmp::Reverse(c))).unwrap() } else { r }
        })
        .collect();
    let pol = Policy { x, labels, ncls, kc, ignore_range: std::env::var_os("DP_IGNORE_RANGE").is_some() };
    let cp = plain_count(&hw1, &hw2, &xi, &pol.labels, prm, ncls, kc);
    let nrt = darkproof::run::release_section(&lp, d, m, prm, &pol);
    // phase 2: the release
    let ctx = Ctx::new(model, 0, steps as u64);
    let outs: Vec<(u64, Vec<u8>, f64, f64)> = std::thread::scope(|s| {
        let hs: Vec<_> = parts
            .drain(..)
            .map(|(mut pt, carry, w1n, w2n, _, _)| {
                let (pol, pr, lp, ctx) = (&pol, &pr, &lp, &ctx);
                s.spawn(move || {
                    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
                    let tm = std::time::Instant::now();
                    let (c, mut st) = pool.install(|| release_mpc(&mut pt, &w1n, &w2n, pol, prm)).expect("release mpc");
                    let mpc_s = tm.elapsed().as_secs_f64();
                    st.triples = tape_triples_at(&pt.tape, pt.cur, Some(nrt)).expect("release proof section");
                    let mut tn = TcpRef(&pt.net);
                    let (blob, secs) = pool.install(|| prove_release(pr, lp, prm, &mut tn, ctx, pol, st, carry)).expect("release proof");
                    (c, blob, mpc_s, secs)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let agree = outs.iter().all(|o| o.1 == outs[0].1 && o.0 == outs[0].0);
    println!("release: MPC {:.1}s, proof {:.1}s, bundle {} bytes; parties agree {agree}; opened C = {}", outs[0].2, outs[0].3, outs[0].1.len(), outs[0].0);
    let t = std::time::Instant::now();
    let r = lg.release(&lp, &outs[0].1, &pol);
    println!("ledger accepts the release: {:?} ({:.1}s); plaintext twin C = {cp}", r, t.elapsed().as_secs_f64());
    ok_all &= agree && r.as_ref().map(|x| x.1 == cp && x.1 == outs[0].0).unwrap_or(false);
    let r2 = lg.accept(&lp, &parts_blob_dummy(), &tables);
    println!("a step after the release: {:?}", r2);
    ok_all &= r2.is_err();
    println!("ledger file: {}", lpath.display());
    println!("{}", if ok_all { "DS-CHAIN PASS" } else { "DS-CHAIN FAIL" });
    std::process::exit(if ok_all { 0 } else { 1 });
}

#[cfg(feature = "tcp")]
fn parts_blob_dummy() -> Vec<u8> {
    b"DLSTEP01".to_vec()
}

#[cfg(feature = "tcp")]
fn peak_rss_gb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.split_whitespace().nth(1).unwrap().parse::<f64>().unwrap() / 1e6))
        .unwrap_or(f64::NAN)
}

/// darkstep's genesis step (HE matvec + outer, ideal-dealer tapes with the proof atoms and the proof section) feeds
/// darkproof::run::prove_step through its ProofRecord, over darkstep's own sockets: the record must equal the
/// harness's witness (wires, middle atoms vs RecEngine.atom_sh, public transcript, alpha), and in the deterministic
/// mode the bundle must equal the Python bundle byte for byte. TAG e.g. demo_d4_he (its he1).
#[cfg(feature = "tcp")]
fn ds_check(dir: &Path, tag: &str) {
    use darkproof::run::{from_darkstep, n_had, prove_step, TcpRef};
    use std::sync::Arc;
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    let p = meta["p"].as_u64().unwrap();
    darkproof::field::set_p(p);
    let d = meta["d"].as_u64().unwrap() as usize;
    let prm = program_of(&meta, d);
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables_for(prm.t_lo);
    // the darkstep program: GEN6 when the shifts are GEN6's (its inputs_for), else the harness's
    let g6 = darkstep::step::Program::GEN6;
    let pg = if (prm.s1, prm.k1, prm.s2, prm.k2, prm.s3, prm.k3, prm.r3) == (g6.s1, g6.k1, g6.s2, g6.k2, g6.s3, g6.k3, g6.r3) { g6 } else { darkstep::step::Program::HARNESS };
    let he = &meta["he"];
    let pf = darkstep::node::prof(&[he["N"].to_string(), he["L"].to_string(), he["F"].to_string(), d.to_string()]);
    assert_eq!(pf.t, p, "darkstep's plaintext modulus differs");
    let b1 = &meta["bundles"]["he1"];
    let w = Witness::load(&dir.join(b1["witness"].as_str().unwrap()));
    let pyb = std::fs::read(dir.join(b1["blob"].as_str().unwrap())).unwrap();
    let seed = meta["seed"].as_str().unwrap().to_string();
    let ctx = Ctx::new("mind-0", 0, 1);
    let zeros = vec![0u64; prm.transcript_len(d, false)];
    let rec0 = darkproof::step::replay(&zeros, d, prm, &tables, false).unwrap();
    let nb = darkproof::spine::beaver_count(d) + rec0.proof_products() + darkproof::middle::beaver_count(rec0.had.len());
    let plain = if pg == darkstep::step::Program::HARNESS { darkstep::step::inputs(d) } else { darkstep::step::inputs_for(d, &pg) };
    let (cs, mut dl) = darkstep::tape::deal_step_dealer_prog(p, d, darkstep::node::DEALER_SEED, darkstep::node::OWNER_SEED, &plain.flat_mod(p), true, &pg);
    darkstep::tape::deal_proof_section(&mut dl, nb);
    let tapes = dl.tapes;
    let ls: Vec<std::net::TcpListener> = (0..3).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<std::net::SocketAddr> = ls.iter().map(|l| l.local_addr().unwrap()).collect();
    let cs = Arc::new(cs);
    let outs: Vec<(bool, Vec<u8>)> = std::thread::scope(|s| {
        let hs: Vec<_> = ls
            .into_iter()
            .zip(tapes)
            .enumerate()
            .map(|(i, (l, tape))| {
                let (addrs, cs, pf, w, pr, lp, tables, ctx, seed, pg, rec0) = (&addrs, cs.clone(), &pf, &w, &pr, &lp, &tables, &ctx, seed.clone(), &pg, &rec0);
                s.spawn(move || {
                    let net = darkstep::net::Net::connect(i, l, addrs);
                    let mut he = ds_he(i, pf, &net);
                    let tab = pg.tables(pf.t);
                    let mut pt = darkstep::party::Party::new(i, pf.t, net, tape);
                    let pool = rayon::ThreadPoolBuilder::new().num_threads(4).build().unwrap();
                    let out = pool.install(|| darkstep::step::run_step_prog(&mut pt, &mut he, &cs, d, &tab, pg)).expect("darkstep step");
                    let st = from_darkstep(i, d, &out.record, &out.w1n, &out.w2n, &pt.tape, Det(Some(seed))).expect("record");
                    // the record against the harness's witness (its middle atoms as the middle takes them: under LB the
                    // record still carries the MPC's masked powers, which the harness's middle witness leaves out)
                    let mid = rec0.witness_atoms(&st.atoms).unwrap_or_default();
                    let mut same = st.alpha_i == w.alpha_sh[i] && st.public == w.public && mid == w.atoms[i];
                    for (k, v) in &w.wires[i] {
                        if st.wires.get(k) != Some(v) {
                            println!("party {i}: wire {k} differs from the harness's");
                            same = false;
                        }
                    }
                    println!(
                        "party {i}: record vs harness: alpha {}, public {} ({} values), middle atoms {} ({} atoms), wires {}; proof-section triples {}",
                        st.alpha_i == w.alpha_sh[i], st.public == w.public, st.public.len(), mid == w.atoms[i], mid.len(),
                        w.wires[i].iter().all(|(k, v)| st.wires.get(k) == Some(v)), st.triples.len()
                    );
                    let mut tn = TcpRef(&pt.net);
                    let sp = pool.install(|| prove_step(pr, lp, tables, prm, &mut tn, ctx, st, None)).expect("prove");
                    (same, sp.blob)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let rec_ok = outs.iter().all(|o| o.0);
    let blob = &outs[0].1;
    let agree = outs.iter().all(|o| &o.1 == blob);
    let eq = blob == &pyb;
    println!(
        "{tag} he1 via darkstep: native {} bytes sha256 {} | python {} bytes sha256 {} | {} | parties agree {}",
        blob.len(), &sha(blob)[..16], pyb.len(), &sha(&pyb)[..16],
        if eq { "EQUAL".to_string() } else { format!("DIFFER at offset {:?}", first_diff(blob, &pyb)) }, agree
    );
    let ok = rec_ok && agree && eq;
    println!("{}", if ok { "DS-CHECK PASS" } else { "DS-CHECK FAIL" });
    std::process::exit(if ok { 0 } else { 1 });
}

/// The release (cosnark_release) bit-exact against the harness: the native pw chain gives the head's carried
/// commitments, then three custodian threads prove the release from the harness's witness; the bundle must equal
/// Python's, the native verifier must accept it against the head's roots and the published policy, and refuse a
/// flipped byte, a wrong count claim (the count's opening changed) and another label set.
fn rel_check(dir: &Path, tag: &str) {
    use darkproof::run::{prove_release, PartyRelease, Policy};
    use darkproof::spdz::{Dealer, Triple};
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    darkproof::field::set_p(meta["p"].as_u64().unwrap());
    let d = meta["d"].as_u64().unwrap() as usize;
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let det = Det(Some(meta["seed"].as_str().unwrap().to_string()));
    let opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det: det.clone(), spine_attack: None, fs_public_attack: false, diagnose: false, transport: darkproof::net::transport_from_env(), prm: None };
    let mut carry = None;
    for name in ["pw1", "pw2"] {
        let b = &meta["bundles"][name];
        let c = b["ctx"].as_array().unwrap();
        let ctx = Ctx::new(c[0].as_str().unwrap(), c[1].as_u64().unwrap(), c[2].as_u64().unwrap());
        let w = Witness::load(&dir.join(b["witness"].as_str().unwrap()));
        let out = make_bundle(&opts, w, &ctx, carry.take(), None).expect("prove");
        assert_eq!(out.blob, std::fs::read(dir.join(b["blob"].as_str().unwrap())).unwrap(), "{name} differs");
        carry = Some(out.child);
    }
    let rm = &meta["release"];
    let c = rm["ctx"].as_array().unwrap();
    let ctx = Ctx::new(c[0].as_str().unwrap(), c[1].as_u64().unwrap(), c[2].as_u64().unwrap());
    let wpath = dir.join(rm["witness"].as_str().unwrap());
    let w = Witness::load(&wpath);
    let raw: Value = serde_json::from_slice(&std::fs::read(&wpath).unwrap()).unwrap();
    let m = raw["M"].as_u64().unwrap() as usize;
    let ncls = raw["ncls"].as_u64().unwrap() as usize;
    let xm = raw["X"].as_array().unwrap();
    let x: Vec<u64> = (0..d).flat_map(|k| (0..m).map(move |t| (k, t))).map(|(k, t)| darkproof::field::from_i64(xm[k][t].as_i64().unwrap())).collect();
    let labels: Vec<usize> = raw["labels"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as usize).collect();
    let pol = Policy { x, labels, ncls, kc: 10, ignore_range: false };
    let prm = darkproof::step::StepParams { rc: rm["rc"].as_bool().unwrap_or(false), lb: rm["lb"].as_bool().unwrap_or(false), ..darkproof::step::StepParams::HARNESS };
    let rec = darkproof::step::replay_release(&w.public, d, m, prm, &pol.x, &pol.labels, ncls, 10).expect("replay");
    let nb = rec.proof_products() + darkproof::middle::beaver_count(rec.had.len());
    let mut dl = Dealer::from_state(&w.dealer_state, w.alpha_sh.clone());
    let mut tapes: Vec<Vec<Triple>> = vec![Vec::with_capacity(nb); 3];
    for _ in 0..nb {
        let av = dl.rng.randrange_u64(darkproof::field::p());
        let bv = dl.rng.randrange_u64(darkproof::field::p());
        let (a, b2, cc) = (dl.auth_all(av), dl.auth_all(bv), dl.auth_all(darkproof::field::mul(av, bv)));
        for i in 0..3 {
            tapes[i].push((a[i], b2[i], cc[i]));
        }
    }
    let ext = |name: &str, i: usize| -> Vec<darkproof::spdz::Sh> {
        raw["ext"][name].as_array().unwrap().iter().map(|e| (e[i][0].as_u64().unwrap(), e[i][1].as_u64().unwrap())).collect()
    };
    let nets = darkproof::net::Nets::new(darkproof::net::transport_from_env(), 3);
    let heads = carry.unwrap();
    let outs: Vec<Result<(Vec<u8>, f64), String>> = std::thread::scope(|s| {
        let hs: Vec<_> = tapes
            .into_iter()
            .zip(heads)
            .enumerate()
            .map(|(i, (tp, hd))| {
                let (nets, w, pr, lp, ctx, pol, det) = (&nets, &w, &pr, &lp, &ctx, &pol, det.clone());
                let mut wires = BTreeMap::new();
                wires.insert("W1".to_string(), w.wires[i]["W1"].clone());
                wires.insert("W2".to_string(), w.wires[i]["W2"].clone());
                wires.insert("z1".to_string(), ext("z1", i));
                wires.insert("h".to_string(), ext("h", i));
                s.spawn(move || {
                    let mut net = nets.take(i);
                    let st = PartyRelease { i, n: 3, d, alpha_i: w.alpha_sh[i], wires, public: w.public.clone(), atoms: w.atoms[i].clone(), triples: tp, det };
                    prove_release(pr, lp, prm, &mut *net, ctx, pol, st, hd)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap_or_else(|_| Err("party panicked".into()))).collect()
    });
    let blobs: Vec<Vec<u8>> = outs.into_iter().map(|o| o.expect("release proof").0).collect();
    let pyb = std::fs::read(dir.join(rm["blob"].as_str().unwrap())).unwrap();
    let eq = blobs[0] == pyb;
    let agree = blobs.iter().all(|b| b == &blobs[0]);
    println!(
        "{tag} release: native {} bytes sha256 {} | python {} bytes sha256 {} | {} | parties agree {agree}",
        blobs[0].len(), &sha(&blobs[0])[..16], pyb.len(), &sha(&pyb)[..16],
        if eq { "EQUAL".to_string() } else { format!("DIFFER at offset {:?}", first_diff(&blobs[0], &pyb)) }
    );
    std::fs::write(dir.join(format!("{tag}_rel.native.bin")), &blobs[0]).unwrap();
    let heads_r = roots_of(&rm["head_roots"]);
    let v = wire::verify_release(&pr, &lp, &pyb, &ctx, &heads_r, &pol.x, &pol.labels, prm, ncls, d, 10);
    println!("  native verify of the python release: {:?} (C = {} in the harness)", v, rm["C"]);
    let mut ok = eq && agree && v.as_ref().map(|r| r.1 == rm["C"].as_u64().unwrap()).unwrap_or(false);
    let mut bad = pyb.clone();
    let pos = bad.len() / 2;
    bad[pos] ^= 1;
    let v2 = wire::verify_release(&pr, &lp, &bad, &ctx, &heads_r, &pol.x, &pol.labels, prm, ncls, d, 10);
    println!("  one flipped byte at {pos}: {:?}", v2);
    ok &= v2.is_err();
    // the count's field element (the transcript's last value) claims one more correct example
    let off = 8 + 2 + ctx.model.len() + 18 + 4 + 8 * (w.public.len() - 1);
    let mut lie = pyb.clone();
    let cv = u64::from_be_bytes(lie[off..off + 8].try_into().unwrap());
    lie[off..off + 8].copy_from_slice(&(cv + 1).to_be_bytes());
    let v3 = wire::verify_release(&pr, &lp, &lie, &ctx, &heads_r, &pol.x, &pol.labels, prm, ncls, d, 10);
    println!("  the released count raised by one (C = {}): {:?}", cv + 1, v3);
    ok &= v3.is_err();
    let mut other = pol.labels.clone();
    other[0] = (other[0] + 1) % ncls;
    let v4 = wire::verify_release(&pr, &lp, &pyb, &ctx, &heads_r, &pol.x, &other, prm, ncls, d, 10);
    println!("  verified against another label set: {:?}", v4);
    ok &= v4.is_err();
    let mut wrong_head = heads_r.clone();
    wrong_head.insert("W1".into(), roots_of(&meta["genesis_roots"])["W1"].clone());
    let v5 = wire::verify_release(&pr, &lp, &pyb, &ctx, &wrong_head, &pol.x, &pol.labels, prm, ncls, d, 10);
    println!("  verified against the genesis W1 instead of the head's: {:?}", v5);
    ok &= v5.is_err();
    println!("{}", if ok { "REL-CHECK PASS" } else { "REL-CHECK FAIL" });
    std::process::exit(if ok { 0 } else { 1 });
}

/// The proof sections' triple counts for one step and for the release (DP_PROGRAM as ds-bench; M = 64, 10 classes).
fn counts(d: usize, prof: &str) {
    let pr = Profile::by_name(prof).unwrap();
    darkproof::field::set_p(wire::he_field(&pr).unwrap());
    let lp = pr.ligero();
    let prm = match std::env::var("DP_PROGRAM") {
        Ok(j) => program_of(&serde_json::json!({ "program": serde_json::from_str::<Value>(&j).unwrap() }), d).deployed(),
        Err(_) => darkproof::step::StepParams::for_width(d).deployed(),
    };
    let tables = darkproof::step::tables_for(prm.t_lo);
    for carried in [false, true] {
        let zeros = vec![0u64; prm.transcript_len(d, carried)];
        let rec = darkproof::step::replay(&zeros, d, prm, &tables, carried).unwrap();
        let nh = rec.had.len();
        let lig = darkproof::ligero::LigParty::tape_triples(&lp, darkproof::spine::LIG_SCALARS, 1) + darkproof::ligero::LigParty::tape_triples(&lp, darkproof::middle::LIG_SCALARS, 1);
        let gen5 = 4 * (nh.next_power_of_two() - 1);
        println!(
            "step (carried {carried}) {prm:?}: hadamard rows {nh} (range rows included), atoms {}, spine Beaver {}, range products {}, lookup products {}, zerocheck {} (gen 5 method: {gen5}), Ligero (unauthenticated) {lig}; section total {}",
            rec.n_prep(), darkproof::spine::beaver_count(d), rec.range_products(), rec.lookup_products(), darkproof::middle::beaver_count(nh), darkproof::run::step_section(&lp, d, prm, carried, &tables)
        );
    }
    let m = 64;
    let pol = darkproof::run::Policy { x: vec![0; d * m], labels: vec![0; m], ncls: 10, kc: 10, ignore_range: false };
    let zeros = vec![0u64; wire::release_len(d, m, prm, 10, 10)];
    let rec = darkproof::step::replay_release(&zeros, d, m, prm, &pol.x, &pol.labels, 10, 10).unwrap();
    let nh = rec.had.len();
    println!(
        "release M = 64: hadamard rows {nh}, atoms {}, range products {}, lookup products {}, zerocheck {} (gen 5 method: {}), section total {}",
        rec.n_prep(), rec.range_products(), rec.lookup_products(), darkproof::middle::beaver_count(nh), 4 * (nh.next_power_of_two() - 1), darkproof::run::release_section(&lp, d, m, prm, &pol)
    );
}

struct Rows {
    out: Vec<(String, String, String)>,
}
impl Rows {
    fn rec(&mut self, name: &str, r: Result<(), String>) {
        let (v, by) = match r {
            Ok(()) => ("ACCEPT".to_string(), "accept".to_string()),
            Err(e) => ("REFUSED".to_string(), e),
        };
        println!("{name:62} {v:8} {by}");
        self.out.push((name.into(), v, by));
    }
}

fn wit(dir: &Path, tag: &str, nm: &str) -> Witness {
    Witness::load(&dir.join(format!("{tag}_{nm}.json")))
}

/// The refusal rows of the decision doc (§16 forgeries, §18 tamper/replay/equivocation/rotation/restart and the
/// signed-input rows) against the native prover, verifier and ledger.
fn rows(dir: &Path, tag: &str) {
    use darkproof::ledger::{Genesis, Ledger};
    use darkproof::owner::{det_seed, Owner};
    use darkproof::witness::{clone_carry, owner_commit, with_max_lives, OwnerIn};
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let seed = meta["seed"].as_str().unwrap().to_string();
    let det = Det(Some(seed.clone()));
    let mut opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det, spine_attack: None, fs_public_attack: false, diagnose: true, transport: darkproof::net::transport_from_env(), prm: None };
    let model = "mind-0";
    let c = |e, s| Ctx::new(model, e, s);
    let tmp = std::env::temp_dir().join(format!("dl-native-ledger-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let mut rows = Rows { out: vec![] };
    let cust = |a: &[&str]| a.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    // ---------------------------------------------------------------- run_proofwire rows
    let (w1, w2, w3) = (wit(dir, tag, "r_pw1"), wit(dir, tag, "r_pw2"), wit(dir, tag, "r_pw3"));
    let s1 = make_bundle(&opts, w1.clone(), &c(0, 1), None, None).unwrap();
    let groots = s1.genesis_roots.clone().unwrap();
    let child1 = s1.child;
    let s2 = make_bundle(&opts, w2.clone(), &c(0, 2), Some(child1), None).unwrap();
    let (b1, b2) = (s1.blob.clone(), s2.blob.clone());
    let child1 = with_max_lives(s2.carried, 99);
    let s2b = make_bundle(&opts, w2.clone(), &c(0, 2), Some(child1), None).unwrap();
    let s3x = make_bundle(&opts, w2.clone(), &c(0, 3), Some(s2b.carried), None).unwrap();
    let child1 = with_max_lives(s3x.carried, pr.lives);
    let (b2b, b3) = (s2b.blob, s3x.blob);
    match make_bundle(&opts, w2.clone(), &c(0, 2), Some(child1), None) {
        Ok(_) => rows.rec("honest custodians asked to open step 1's child a third time", Ok(())),
        Err(e) => rows.rec("honest custodians asked to open step 1's child a third time", Err(e)),
    }
    let path = tmp.join("mind-0.ledger");
    let mut lg = Ledger::open(&path, model, &pr, Some(Genesis { d: w1.d, program: darkproof::step::StepParams::for_width(w1.d), owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: groots.clone() })).unwrap();
    let hdr = 8 + 2 + model.len();
    rows.rec("step 1, honest (parent = genesis record)", lg.accept(&lp, &b1, &tables));
    rows.rec("step 1 replayed", lg.accept(&lp, &b1, &tables));
    rows.rec("step 2 truncated by one byte", lg.accept(&lp, &b2[..b2.len() - 1], &tables));
    let mut t = b2.clone();
    t.push(0);
    rows.rec("step 2 with one trailing byte", lg.accept(&lp, &t, &tables));
    let ld = w1.d.trailing_zeros() as usize;
    let off = hdr + 16 + (13 + 4 * ld + 2) * 3 * 32;
    let mut t = b2.clone();
    t[off..off + 8].copy_from_slice(&darkproof::field::p().to_be_bytes());
    rows.rec("step 2 with a non-canonical field element", lg.accept(&lp, &t, &tables));
    for (what, pos) in [
        ("a byte in the header's model id", 10),
        ("a byte in a commitment root", hdr + 16 + 5),
        ("a byte in a field element (prox)", off + 7),
        ("a byte in the middle of the blob", b2.len() / 2),
        ("the last byte", b2.len() - 1),
    ] {
        let mut t = b2.clone();
        t[pos] ^= 1;
        rows.rec(&format!("step 2 with {what} flipped"), lg.accept(&lp, &t, &tables));
    }
    let mut t = b2[..10].to_vec();
    t.extend_from_slice(b"\xff\xfe\xfd\xfc\xfb\xfa");
    t.extend_from_slice(&b2[16..]);
    rows.rec("step 2 with a model id that is not UTF-8", lg.accept(&lp, &t, &tables));
    let mut t = b3.clone();
    t[hdr + 4..hdr + 12].copy_from_slice(&2u64.to_be_bytes());
    rows.rec("step 3's proof under a header patched to step 2", lg.accept(&lp, &t, &tables));
    let mut t = b2[..8].to_vec();
    t.extend_from_slice(&6u16.to_be_bytes());
    t.extend_from_slice(b"mind-1");
    t.extend_from_slice(&b2[hdr..]);
    rows.rec("step 2 claiming another model id", lg.accept(&lp, &t, &tables));
    // stale parent (§16): step 2 verified against the genesis roots instead of step 1's child
    rows.rec(
        "step 2 against a stale parent (genesis W, not step 1's child)",
        wire::verify_step(&pr, &lp, &b2, &c(0, 2), &groots, &tables, w1.d, darkproof::step::StepParams::for_width(w1.d), None, 0).map(|_| ()),
    );
    rows.rec("step 2, honest", lg.accept(&lp, &b2, &tables));
    rows.rec("a second valid proof of step 2 (equivocation)", lg.accept(&lp, &b2b, &tables));
    let lg2 = Ledger::open(&path, model, &pr, None).unwrap();
    let same = lg2.head() == lg.head();
    println!("{:62} {:8} {:?}", "restart reconstructs the head", if same { "OK" } else { "FAIL" }, lg2.head().0);
    rows.out.push(("restart reconstructs the head".into(), if same { "OK" } else { "FAIL" }.into(), format!("{:?}", lg2.head().0)));
    let s3 = make_bundle(&opts, w3.clone(), &c(1, 3), Some(s2.child), None).unwrap();
    let nc: BTreeMap<String, Vec<[u8; 32]>> = ["W1", "W2"]
        .iter()
        .map(|k| (k.to_string(), owner_commit(&pr, &w2.plain(&format!("{k}n")), k, 3, &opts.det).iter().map(|c| c.root).collect()))
        .collect();
    let mut lg2 = lg2;
    rows.rec(
        "rotation with no handover proof (empty bytes)",
        lg2.rotate(&cust(&["c3", "c4", "c5"]), &nc, b""),
    );
    rows.rec(
        "the OLD committee's step 3 against the new committee's roots",
        wire::verify_step(&pr, &lp, &s3.blob, &c(1, 3), &nc, &tables, w1.d, darkproof::step::StepParams::for_width(w1.d), None, 0).map(|_| ()),
    );
    let ledger_text = std::fs::read_to_string(&path).unwrap();
    std::fs::write(dir.join(format!("{tag}_native.ledger")), &ledger_text).unwrap();
    std::fs::remove_file(&path).unwrap();
    // ---------------------------------------------------------------- §16 spine forgeries (full collusion)
    for att in ["forge_W1n", "forge_z1", "forge_sumcheck", "lie_in_u"] {
        opts.spine_attack = Some(att);
        let b = make_bundle(&opts, w1.clone(), &c(0, 1), None, None).unwrap();
        opts.spine_attack = None;
        let p = tmp.join(format!("{att}.ledger"));
        let mut l = Ledger::open(&p, model, &pr, Some(Genesis { d: w1.d, program: darkproof::step::StepParams::for_width(w1.d), owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: b.genesis_roots.clone().unwrap() })).unwrap();
        let r = l.accept(&lp, &b.blob, &tables);
        rows.rec(&format!("spine forgery {att} (violates: {})", b.spine_violates.clone().unwrap_or_default()), r);
        std::fs::remove_file(&p).unwrap();
    }
    // ---------------------------------------------------------------- §16 middle forgeries
    for nm in ["trunc", "lookup", "bad_triple", "nonboolean_bit", "mask_out_of_range"] {
        let w = wit(dir, tag, &format!("r_g_{nm}"));
        let b = make_bundle(&opts, w.clone(), &c(0, 1), None, None).unwrap();
        let p = tmp.join(format!("{nm}.ledger"));
        let mut l = Ledger::open(&p, model, &pr, Some(Genesis { d: w.d, program: darkproof::step::StepParams::for_width(w.d), owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: b.genesis_roots.clone().unwrap() })).unwrap();
        let r = l.accept(&lp, &b.blob, &tables);
        let label = match nm {
            "trunc" => "forged trunc opening",
            "lookup" => "forged lookup opening",
            x => x,
        };
        rows.rec(&format!("middle forgery: {label} (violates: {})", b.middle_violates.clone().unwrap_or_default()), r);
        std::fs::remove_file(&p).unwrap();
    }
    // ---------------------------------------------------------------- §19 fs_public_falsifier
    {
        const DELTA: u64 = 12345;
        let mut wf = w1.clone();
        let xs = w1.plain("x");
        let d = w1.d;
        let v = &mut wf.wires[0].get_mut("d1").unwrap()[0];
        v.0 = darkproof::field::add(v.0, DELTA);
        for j in 0..d {
            let v = &mut wf.wires[0].get_mut("W1n").unwrap()[j];
            v.0 = darkproof::field::sub(v.0, darkproof::field::mul(DELTA, xs[j]));
        }
        opts.fs_public_attack = true;
        let b = make_bundle(&opts, wf.clone(), &c(0, 1), None, None).unwrap();
        opts.fs_public_attack = false;
        let p = tmp.join("fs.ledger");
        let mut l = Ledger::open(&p, model, &pr, Some(Genesis { d, program: darkproof::step::StepParams::for_width(d), owner_pk: None, custodians: cust(&["c0", "c1", "c2"]), roots: b.genesis_roots.clone().unwrap() })).unwrap();
        let r = l.accept(&lp, &b.blob, &tables);
        rows.rec(
            &format!(
                "fs_public: d1 steered by 12345, dead opening shifted after gamma (spine violates: {}, middle: {})",
                b.spine_violates.clone().unwrap_or("none".into()),
                b.middle_violates.clone().unwrap_or("none".into())
            ),
            r,
        );
        std::fs::remove_file(&p).unwrap();
    }
    // ---------------------------------------------------------------- signed-input rows
    let xy = &meta["rows_xy"];
    let v = |k: &str| xy[k].as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect::<Vec<u64>>();
    let (x1, y1, x2, y2, xb, yb) = (v("x1"), v("y1"), v("x2"), v("y2"), v("x_bad"), v("y_bad"));
    let h = pr.owner_h;
    let oseed = det_seed(&seed, 0);
    let mut owner = Owner::new(h, Some(oseed.clone()), None);
    let mut mallory = Owner::new(h, Some(det_seed(&seed, 1)), None);
    let (ws1, ws2, wsa, wsb, wsr) =
        (wit(dir, tag, "r_si1"), wit(dir, tag, "r_si2"), wit(dir, tag, "r_sa"), wit(dir, tag, "r_sb"), wit(dir, tag, "r_sr"));
    let t1 = make_bundle(&opts, ws1.clone(), &c(0, 1), None, Some(OwnerIn { owner: &mut owner, x: x1.clone(), y: y1.clone() })).unwrap();
    let sgen = t1.genesis_roots.clone().unwrap();
    let t2 = make_bundle(&opts, ws2.clone(), &c(0, 2), Some(t1.child), Some(OwnerIn { owner: &mut owner, x: x2, y: y2 })).unwrap();
    let mut gen = with_max_lives(t1.carried, 99);
    let schild = with_max_lives(t2.carried, 99);
    let mut twin = || Owner::new(h, Some(oseed.clone()), None);
    let mut tw = twin();
    let sa = make_bundle(&opts, wsa.clone(), &c(0, 1), Some(clone_carry(&gen)), Some(OwnerIn { owner: &mut tw, x: x1.clone(), y: y1.clone() })).unwrap();
    gen = with_max_lives(sa.carried, 99);
    let mut tw = twin();
    let sb = make_bundle(&opts, wsb.clone(), &c(0, 1), Some(clone_carry(&gen)), Some(OwnerIn { owner: &mut tw, x: x1.clone(), y: y1.clone() })).unwrap();
    gen = with_max_lives(sb.carried, 99);
    let sc = make_bundle(&opts, wsa.clone(), &c(0, 1), Some(gen), Some(OwnerIn { owner: &mut mallory, x: xb.clone(), y: y1.clone() })).unwrap();
    let old = make_bundle(&opts, wsr.clone(), &c(0, 1), Some(schild), Some(OwnerIn { owner: &mut owner, x: x1.clone(), y: y1.clone() })).unwrap();
    let mut fresh = Owner::new(h, Some(det_seed(&seed, 2)), None);
    let new = make_bundle(&opts, wsr.clone(), &c(0, 2), Some(with_max_lives(old.carried, 99)), Some(OwnerIn { owner: &mut fresh, x: x1.clone(), y: y1 })).unwrap();
    let l = darkproof::owner::sig_len(h);
    let mut sr = new.blob[..new.blob.len() - l].to_vec();
    sr.extend_from_slice(&old.blob[old.blob.len() - l..]);
    let _ = yb;
    let p = tmp.join("signed.ledger");
    let mut lg = Ledger::open(&p, model, &pr, Some(Genesis { d: ws1.d, program: darkproof::step::StepParams::for_width(ws1.d), owner_pk: Some(owner.pk), custodians: cust(&["c0", "c1", "c2"]), roots: sgen })).unwrap();
    rows.rec(&format!("custodians train on x' while presenting the owner's signed x (violates: {})", sa.spine_violates.clone().unwrap_or_default()), lg.accept(&lp, &sa.blob, &tables));
    rows.rec(&format!("custodians train on y' while presenting the owner's signed y (violates: {})", sb.middle_violates.clone().unwrap_or_default()), lg.accept(&lp, &sb.blob, &tables));
    rows.rec("custodians commit x' themselves and sign with their own key", lg.accept(&lp, &sc.blob, &tables));
    rows.rec("step 1, honest, owner-signed", lg.accept(&lp, &t1.blob, &tables));
    rows.rec("step 2 re-using the owner's step-1 signature (old batch, used leaf)", lg.accept(&lp, &sr, &tables));
    rows.rec("step 2, honest, owner-signed", lg.accept(&lp, &t2.blob, &tables));
    std::fs::remove_file(&p).unwrap();
    std::fs::remove_dir(&tmp).unwrap();
    let js: Vec<Value> = rows.out.iter().map(|(a, b, c)| serde_json::json!({"row": a, "verdict": b, "by": c})).collect();
    std::fs::write(dir.join(format!("{tag}_native_rows.json")), serde_json::to_string_pretty(&js).unwrap()).unwrap();
}

/// The native witness generator (live.rs) against the harness's dumped witness for step 1.
fn gen_check(dir: &Path, tag: &str) {
    let w = Witness::load(&dir.join(format!("{tag}_r_pw1.json")));
    let tables = darkproof::step::tables();
    let (w1, w2, x, y) = darkproof::live::harness_inputs(w.d);
    let g = darkproof::live::run_step(&w1, &w2, &x, &y, w.d, darkproof::step::StepParams::for_width(w.d), &tables);
    let mut ok = true;
    let mut cmp = |what: &str, a: bool| {
        println!("  {what}: {}", if a { "holds" } else { "FAILS" });
        ok &= a;
    };
    cmp("public transcript equal", g.public == w.public);
    cmp("middle atoms equal (every party's share and MAC share)", g.atoms == w.atoms);
    cmp("dealer MT state after the step equal", g.dealer_state == w.dealer_state);
    cmp("alpha shares equal", g.alpha_sh == w.alpha_sh);
    for k in w.wires[0].keys() {
        cmp(&format!("wire {k} equal"), (0..w.n).all(|i| g.wires[i].get(k) == w.wires[i].get(k)));
    }
    let mut bad = g.atoms.clone();
    bad[0][1].0 ^= 1;
    cmp("negative control: one flipped atom share compares unequal", bad != w.atoms);
    println!("{}", if ok { "GEN-CHECK PASS" } else { "GEN-CHECK FAIL" });
    std::process::exit(if ok { 0 } else { 1 });
}

/// Field elements, hashes and column indices of a proof (as cosnark_zk.measure counts them).
fn measure_spine(p: &darkproof::spine::SpineProof) -> (u64, u64, u64) {
    let (mut fe, mut hs, mut idx) = (0u64, 0u64, 0u64);
    for c in p.pcs_cols.values() {
        idx += c.j.len() as u64;
        for party in &c.open {
            for (col, path) in party {
                fe += col.len() as u64;
                hs += path.len() as u64;
            }
        }
    }
    fe += p.prox.values().map(|v| v.iter().map(|u| u.len() as u64).sum::<u64>()).sum::<u64>();
    hs += p.roots.values().map(|v| v.len() as u64).sum::<u64>();
    hs += p.round_roots.values().map(|v| v.iter().map(|r| r.len() as u64).sum::<u64>()).sum::<u64>();
    hs += (p.eval_roots.len() + p.mask_roots.len()) as u64;
    let (f2, h2) = measure_lig(&p.ligero);
    (fe + f2, hs + h2, idx)
}
fn measure_lig(l: &darkproof::ligero::LigProof) -> (u64, u64) {
    let mut fe = (l.w.len() + l.q.len() + l.pq.len()) as u64;
    let mut hs = 0;
    for g in &l.cols {
        for party in g {
            for (col, path) in party {
                fe += col.len() as u64;
                hs += path.len() as u64;
            }
        }
    }
    (fe, hs)
}
fn measure_middle(p: &darkproof::middle::MiddleProof) -> (u64, u64, u64) {
    let (mut fe, mut hs, mut idx) = (0u64, 0u64, 0u64);
    for c in p.pcs_cols.values() {
        idx += c.j.len() as u64;
        for party in &c.open {
            for (col, path) in party {
                fe += col.len() as u64;
                hs += path.len() as u64;
            }
        }
    }
    fe += p.prox.values().map(|v| v.iter().map(|u| u.len() as u64).sum::<u64>()).sum::<u64>();
    hs += p.roots.values().map(|v| v.len() as u64).sum::<u64>();
    hs += p.zc_roots.iter().chain(p.lsc_roots.iter()).map(|r| r.len() as u64).sum::<u64>();
    hs += (p.claims_root.len() + p.eval_roots.len() + p.mask_roots.len()) as u64;
    let (f2, h2) = measure_lig(&p.ligero);
    (fe + f2, hs + h2, idx)
}

/// Timing: the native witness generator, then step 1 (genesis) and step 2 (chained, the steady state), each
/// proved by three custodian threads and verified by the untrusted-input verifier.
fn bench(d: usize, prof: &str) {
    use darkproof::live;
    use darkproof::step::StepParams;
    let pr = Profile::by_name(prof).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let prm = StepParams::for_width(d);
    let opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det: Det(None), spine_attack: None, fs_public_attack: false, diagnose: false, transport: darkproof::net::transport_from_env(), prm: None };
    let t = std::time::Instant::now();
    let (w1, w2, x, y) = live::harness_inputs(d);
    let wit1 = live::run_step(&w1, &w2, &x, &y, d, prm, &tables);
    println!("d={d} profile={prof} params={prm:?} threads={}", rayon::current_num_threads());
    println!("witness step 1: {:.1}s, public transcript {} values, middle atoms {}", t.elapsed().as_secs_f64(), wit1.public.len(), wit1.atoms[0].len());
    let ctx1 = Ctx::new("mind-0", 0, 1);
    let w1n = wit1.plain("W1n");
    let w2n = wit1.plain("W2n");
    let carry_w: Vec<(Vec<darkproof::spdz::Sh>, Vec<darkproof::spdz::Sh>)> =
        wit1.wires.iter().map(|m| (m["W1n"].clone(), m["W2n"].clone())).collect();
    let b1 = make_bundle(&opts, wit1, &ctx1, None, None).expect("prove 1");
    let groots = b1.genesis_roots.clone().unwrap();
    println!("step 1 prove (3 custodian threads, incl. genesis commitment): {:.1}s, bundle {} bytes", b1.prove_secs, b1.blob.len());
    let t = std::time::Instant::now();
    let a1 = wire::verify_step(&pr, &lp, &b1.blob, &ctx1, &groots, &tables, d, prm, None, 0);
    println!("step 1 verify: {:.1}s {:?}", t.elapsed().as_secs_f64(), a1.as_ref().map(|_| "accept"));
    let t = std::time::Instant::now();
    let mut wit2 = live::run_step(&w1n, &w2n, &x, &y, d, prm, &tables);
    for (i, (a, b)) in carry_w.into_iter().enumerate() {
        wit2.wires[i].insert("W1".into(), a);
        wit2.wires[i].insert("W2".into(), b);
    }
    println!("witness step 2: {:.1}s", t.elapsed().as_secs_f64());
    let ctx2 = Ctx::new("mind-0", 0, 2);
    let public2 = wit2.public.clone();
    let b2 = make_bundle(&opts, wit2, &ctx2, Some(b1.child), None).expect("prove 2");
    println!("step 2 prove (chained, W1/W2 carried): {:.1}s, bundle {} bytes", b2.prove_secs, b2.blob.len());
    let t = std::time::Instant::now();
    let a2 = wire::verify_step(&pr, &lp, &b2.blob, &ctx2, &a1.as_ref().unwrap().child, &tables, d, prm, None, 0);
    println!("step 2 verify: {:.1}s {:?}", t.elapsed().as_secs_f64(), a2.as_ref().map(|_| "accept"));
    let mut bad = b2.blob.clone();
    let l = bad.len();
    bad[l / 3] ^= 1;
    let a3 = wire::verify_step(&pr, &lp, &bad, &ctx2, &a1.as_ref().unwrap().child, &tables, d, prm, None, 0);
    println!("step 2 with one flipped byte: {:?}", a3.as_ref().map(|_| "accept"));
    // sizes
    let mut r = 8 + 2 + 6 + 16;
    let blob = &b2.blob;
    let _ = &mut r;
    let n_public = public2.len();
    let rec = darkproof::step::replay(&public2, d, prm, &tables, false).unwrap();
    let mut rd = blob.clone();
    let _ = &mut rd;
    let sp = {
        let mut rr = darkproof::wire::R::new(&blob[32..]);
        darkproof::wire::read_spine(&mut rr, &pr, 3, d, true, false).unwrap()
    };
    let spine_bytes = {
        let mut w = darkproof::wire::W { b: vec![] };
        darkproof::wire::write_spine(&mut w, &pr, 3, d, true, false, &sp);
        w.b.len()
    };
    let mid_off = 32 + spine_bytes + 4 + 8 * n_public;
    let mp = {
        let mut rr = darkproof::wire::R::new(&blob[mid_off..]);
        darkproof::wire::read_middle(&mut rr, &pr, 3, d, rec.n_prep(), rec.had.len(), false).unwrap()
    };
    let (sf, sh, si) = measure_spine(&sp);
    let (mf, mh, mi) = measure_middle(&mp);
    println!("spine: {spine_bytes} bytes; {sf} field elements, {sh} hashes, {si} indices; {:.1} Mbit (61 fe + 256 h)", (61 * sf + 256 * sh) as f64 / 1e6);
    println!("middle: {} bytes; {} field elements (incl. {mi} indices), {mh} hashes; {:.1} Mbit", blob.len() - mid_off, mf + mi, (61 * (mf + mi) + 256 * mh) as f64 / 1e6);
    println!("public transcript: {} bytes", 4 + 8 * n_public);
    if let Ok(st) = std::fs::read_to_string("/proc/self/status") {
        for l in st.lines().filter(|l| l.starts_with("VmHWM")) {
            println!("peak RSS {l}");
        }
    }
    println!("bench rows: hadamard {} atoms {} spine stats {:?} middle stats {:?}", rec.had.len(), rec.n_prep(), b2.spine_stats, b2.middle_stats);
}
