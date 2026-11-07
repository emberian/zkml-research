//! The native handover prover (six custodian party states over an in-process mesh) against handover.py's bytes.
//!
//!   cd research/dark_learning_2026_11_06
//!   DL_DETERMINISTIC=7 python3 handover_vectors.py <dir> <d> <demo|ledger>      (d = 4 and 16)
//!   HANDOVER_PROVER_VECTORS=<dir> cargo test --release -p darkproof --features test-det --test handover_prover_vs_python -- --nocapture
//!
//! Every vector in <dir>: the native proof bytes equal Python's, every party holds the same proof, the native
//! verifier accepts them; a third opening of the old child is refused; and (negative control) a proof for another
//! new custodian set differs from Python's bytes and is refused under the original context.
use darkproof::handover::{self, HandoverCtx};
use darkproof::net::mem_mesh;
use darkproof::pcs::PcsParty;
use darkproof::rng::Det;
use darkproof::Profile;
use serde_json::Value;
use std::collections::BTreeMap;
use std::path::PathBuf;

fn shares(v: &Value) -> Vec<Vec<u64>> {
    v.as_array().unwrap().iter().map(|s| s.as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect()).collect()
}

/// Runs the six parties; returns every party's encoded proof (or error) and the old parts after the run.
fn run(pr: &Profile, d: usize, ctx: &HandoverCtx, old: &BTreeMap<String, Vec<Vec<u64>>>, new: &BTreeMap<String, Vec<Vec<u64>>>,
       labels: &BTreeMap<String, String>, lives_spent: usize, det: &Det) -> Vec<Result<Vec<u8>, String>> {
    let lp = pr.ligero();
    let nets = mem_mesh(6);
    std::thread::scope(|s| {
        let hs: Vec<_> = nets
            .into_iter()
            .enumerate()
            .map(|(g, mut net)| {
                let lp = &lp;
                s.spawn(move || {
                    let mut mine = BTreeMap::new();
                    for k in ["W1", "W2"] {
                        let c = if g < 3 {
                            let mut c = PcsParty::commit(pr, &old[k][g], &labels[k], g, det);
                            c.opened_lives = lives_spent;
                            c
                        } else {
                            PcsParty::commit(pr, &new[k][g - 3], k, g - 3, det)
                        };
                        mine.insert(k.to_string(), c);
                    }
                    handover::prove(pr, lp, d, 3, 3, ctx, &mut mine, &mut net, det).map(|p| handover::encode(pr, d, &p))
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap_or_else(|_| Err("party thread ended: a peer refused".into()))).collect()
    })
}

#[test]
fn handover_prover_equals_python() {
    let dir = PathBuf::from(std::env::var("HANDOVER_PROVER_VECTORS").expect("set HANDOVER_PROVER_VECTORS (see the header)"));
    let det = Det(Some("7".into()));
    let mut done = 0;
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok()).map(|e| e.path())
        .filter(|p| p.extension().map(|x| x == "json").unwrap_or(false)).collect();
    names.sort();
    for path in names {
        let v: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        // the vector's field first: LigParams and every field operation after it use it
        darkproof::field::set_p(v["p"].as_u64().expect("vector records its field p"));
        let pr = Profile::by_name(v["profile"].as_str().unwrap()).unwrap();
        let d = v["d"].as_u64().unwrap() as usize;
        let strs = |x: &Value| x.as_array().unwrap().iter().map(|s| s.as_str().unwrap().to_string()).collect::<Vec<_>>();
        let ctx = HandoverCtx {
            model: v["model"].as_str().unwrap().into(),
            epoch_old: v["epoch_old"].as_u64().unwrap(),
            epoch_new: v["epoch_new"].as_u64().unwrap(),
            after_step: v["after_step"].as_u64().unwrap(),
            old_set: strs(&v["old_set"]),
            new_set: strs(&v["new_set"]),
        };
        let m = |x: &Value| ["W1", "W2"].iter().map(|k| (k.to_string(), shares(&x[*k]))).collect::<BTreeMap<_, _>>();
        let (old, new) = (m(&v["old"]), m(&v["new"]));
        let labels: BTreeMap<String, String> =
            ["W1", "W2"].iter().map(|k| (k.to_string(), v["old_labels"][*k].as_str().unwrap().to_string())).collect();
        let spent = v["old_lives_spent"].as_u64().unwrap() as usize;
        let py = std::fs::read(dir.join(v["bytes"].as_str().unwrap())).unwrap();
        // native resharing equals handover.reshare under random.Random(1234) (W1 then W2, as the vector script)
        let mut rs = vec![pycompat::PyRandom::from_u64(1234)];
        for k in ["W1", "W2"] {
            assert_eq!(handover::reshare(&old[k], 3, &mut rs).1, new[k], "resharing of {k} differs from Python's");
        }

        let t = std::time::Instant::now();
        let outs = run(&pr, d, &ctx, &old, &new, &labels, spent, &det);
        let secs = t.elapsed().as_secs_f64();
        let nb = outs[0].as_ref().expect("party 0 proves").clone();
        for (g, o) in outs.iter().enumerate() {
            assert_eq!(o.as_ref().unwrap(), &nb, "party {g} holds another proof");
        }
        let first = nb.iter().zip(&py).position(|(a, b)| a != b);
        assert!(nb == py, "d = {d} {}: native bytes differ from Python's (lengths {} / {}, first difference at {:?})",
                pr.name, nb.len(), py.len(), first);
        // the native verifier accepts them, against the old roots the proof names (the ledger head's in a run)
        let lp = pr.ligero();
        let parsed = handover::decode(&pr, &nb, d, 3, 3).unwrap();
        assert_eq!(nb.len(), handover::byte_len(&pr, d, &parsed), "the schema's length (byte_len) differs from the bytes'");
        let tv = std::time::Instant::now();
        handover::verify(&pr, &lp, d, 3, 3, &ctx, &parsed.old_roots, &nb).expect("native verifier accepts");
        let vsecs = tv.elapsed().as_secs_f64();
        println!("[{} d = {d}] native prove {secs:.3}s (6 parties, in-process), verify {vsecs:.3}s, {} bytes == Python",
                 pr.name, nb.len());
        // a third opening of the old child is refused by the custodians' counter
        let third = run(&pr, d, &ctx, &old, &new, &labels, 2, &det);
        for g in 0..3 {
            assert!(third[g].as_ref().unwrap_err().contains("LifeExhausted"), "third opening was not refused");
        }
        assert!(third.iter().all(|o| o.is_err()), "a party finished a proof whose old part refused");
        // negative control: another new custodian set gives other bytes, refused under the original context
        let mut other = ctx.clone();
        other.new_set[2] = "c9".into();
        let ob = run(&pr, d, &other, &old, &new, &labels, spent, &det)[0].clone().unwrap();
        assert_ne!(ob, py, "the comparison cannot tell contexts apart");
        let e = handover::verify(&pr, &lp, d, 3, 3, &ctx, &parsed.old_roots, &ob).unwrap_err();
        assert!(e.contains("column challenge mismatch"), "{e}");
        done += 1;
    }
    assert!(done >= 1, "no vectors in {}", dir.display());
}
