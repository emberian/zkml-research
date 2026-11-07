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
    match args.get(1).map(|s| s.as_str()) {
        Some("check") => check(Path::new(&args[2]), &args[3]),
        Some("rows") => rows(Path::new(&args[2]), &args[3]),
        Some("gen-check") => gen_check(Path::new(&args[2]), &args[3]),
        Some("bench") => bench(args[2].parse().unwrap(), &args[3]),
        _ => eprintln!("usage: darkproof check VECDIR TAG"),
    }
}

fn check(dir: &Path, tag: &str) {
    let meta: Value = serde_json::from_slice(&std::fs::read(dir.join(format!("{tag}_meta.json"))).unwrap()).unwrap();
    let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
    let lp = pr.ligero();
    let tables = darkproof::step::tables();
    let det = Det(Some(meta["seed"].as_str().unwrap().to_string()));
    let opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det, spine_attack: None, fs_public_attack: false, diagnose: true, transport: darkproof::net::transport_from_env() };
    let mut ok_all = true;
    let groots = roots_of(&meta["genesis_roots"]);
    let mut carry = None;
    let mut parent = groots.clone();
    for name in ["pw1", "pw2"] {
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
        let v = wire::verify_step(&pr, &lp, &pyb, &ctx, &parent, &tables, w.d, darkproof::step::StepParams::for_width(w.d), None, 0);
        println!("  native verify of the python bundle: {:?} ({:.2}s)", v.as_ref().map(|_| "accept"), t.elapsed().as_secs_f64());
        ok_all &= v.is_ok();
        let mut bad = pyb.clone();
        let pos = bad.len() / 2;
        bad[pos] ^= 1;
        let v2 = wire::verify_step(&pr, &lp, &bad, &ctx, &parent, &tables, w.d, darkproof::step::StepParams::for_width(w.d), None, 0);
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
    let mut opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det, spine_attack: None, fs_public_attack: false, diagnose: true, transport: darkproof::net::transport_from_env() };
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
    t[off..off + 8].copy_from_slice(&darkproof::field::P.to_be_bytes());
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
    let opts = BundleOpts { pr: &pr, lp: &lp, tables: &tables, det: Det(None), spine_attack: None, fs_public_attack: false, diagnose: false, transport: darkproof::net::transport_from_env() };
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
    let rec = darkproof::step::replay(&public2, d, prm, &tables).unwrap();
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
