//! The native handover verifier and Ledger::rotate against the Python harness's bytes and verdicts.
//!
//!   cd research/dark_learning_2026_11_06
//!   DL_DETERMINISTIC=7 HANDOVER_DUMP=<dir> python3 run_handover.py 4 <demo|ledger>
//!   HANDOVER_VECTORS=<dir>[:<dir>...] cargo test --release -p darkproof --test handover_vs_python -- --nocapture
//!
//! Every rotation attempt of run_handover.py (the honest handover and each attack) is replayed on a copy of the
//! ledger file as Python had it before the attempt: the native verdict and reason must equal Python's, and the
//! ledger file afterwards must equal Python's byte for byte (the accepted record line included).
use darkproof::h::{unhex32, Hash};
use darkproof::handover;
use darkproof::ledger::Ledger;
use darkproof::Profile;
use serde_json::Value;
use std::collections::BTreeMap;
use std::path::PathBuf;

fn roots(v: &Value) -> BTreeMap<String, Vec<Hash>> {
    ["W1", "W2"]
        .iter()
        .map(|k| (k.to_string(), v[*k].as_array().unwrap().iter().map(|h| unhex32(h.as_str().unwrap()).unwrap()).collect()))
        .collect()
}

#[test]
fn handover_rotations_equal_python() {
    let dirs = std::env::var("HANDOVER_VECTORS")
        .expect("set HANDOVER_VECTORS to the HANDOVER_DUMP directories of run_handover.py (see the file header)");
    let mut checked = 0;
    for dir in dirs.split(':').map(PathBuf::from) {
        let meta: Value = serde_json::from_str(&std::fs::read_to_string(dir.join("rotations.json")).unwrap()).unwrap();
        let pr = Profile::by_name(meta["profile"].as_str().unwrap()).unwrap();
        let d = meta["d"].as_u64().unwrap() as usize;
        let model = meta["model"].as_str().unwrap();
        let tmp = std::env::temp_dir().join(format!("dl-handover-test-{}-{}", std::process::id(), pr.name));
        std::fs::create_dir_all(&tmp).unwrap();
        let mut honest: Option<(Vec<u8>, String)> = None;
        for (i, rot) in meta["rotations"].as_array().unwrap().iter().enumerate() {
            let name = rot["name"].as_str().unwrap();
            let path = tmp.join(format!("r{i}.ledger"));
            std::fs::write(&path, rot["ledger_before"].as_str().unwrap()).unwrap();
            let mut lg = Ledger::open(&path, model, &pr, None).unwrap();
            let cust: Vec<String> =
                rot["custodians"].as_array().unwrap().iter().map(|c| c.as_str().unwrap().to_string()).collect();
            let blob = match rot["bytes"].as_str() {
                Some(f) => std::fs::read(dir.join(f)).unwrap(),
                None => Vec::new(),
            };
            let t = std::time::Instant::now();
            let got = lg.rotate(&cust, &roots(&rot["new_roots"]), &blob);
            let secs = t.elapsed().as_secs_f64();
            let (ok, why) = match &got {
                Ok(()) => (true, "accept".to_string()),
                Err(e) => (false, e.clone()),
            };
            let py_ok = rot["ok"].as_bool().unwrap();
            let py_why = rot["why"].as_str().unwrap();
            println!(
                "[{}] {:58} native {:7} python {:7} {:.3}s  {}",
                pr.name,
                name,
                if ok { "ACCEPT" } else { "REFUSED" },
                if py_ok { "ACCEPT" } else { "REFUSED" },
                secs,
                why
            );
            assert_eq!((ok, why.as_str()), (py_ok, py_why), "{name}: native verdict differs from Python's");
            let after = std::fs::read_to_string(&path).unwrap();
            assert_eq!(after, rot["ledger_after"].as_str().unwrap(), "{name}: ledger file differs from Python's");
            if ok {
                assert_eq!(blob.len(), handover::byte_len(&pr, d, 3, 3), "schema length");
                honest = Some((blob, rot["ledger_before"].as_str().unwrap().to_string()));
            }
            std::fs::remove_file(&path).unwrap();
            checked += 1;
        }
        // negative controls on the comparison itself: the honest bytes are refused under a context the proof was not
        // made for (another epoch's ledger head) and with any single byte of the field-element region flipped
        let (hb, before) = honest.expect("an accepting rotation");
        let path = tmp.join("ctl.ledger");
        std::fs::write(&path, &before).unwrap();
        let lg = Ledger::open(&path, model, &pr, None).unwrap();
        let lp = pr.ligero();
        let cust: Vec<String> = ["c3", "c4", "c5"].iter().map(|s| s.to_string()).collect();
        let mut ctx = lg.handover_context(&cust);
        let t = std::time::Instant::now();
        let nr = handover::verify(&pr, &lp, d, 3, 3, &ctx, &lg.parent, &hb).expect("honest bytes accept");
        println!("[{}] native verify of the honest {} bytes: {:.3}s", pr.name, hb.len(), t.elapsed().as_secs_f64());
        ctx.epoch_new += 1;
        assert!(handover::verify(&pr, &lp, d, 3, 3, &ctx, &lg.parent, &hb).is_err(), "other context accepted");
        let mut other = lg.parent.clone();
        other.get_mut("W1").unwrap()[0][0] ^= 1;
        assert_eq!(
            handover::verify(&pr, &lp, d, 3, 3, &lg.handover_context(&cust), &other, &hb).unwrap_err(),
            "handover: old roots are not the ledger head's"
        );
        assert!(!nr.is_empty());
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_dir(&tmp).unwrap();
    }
    assert!(checked >= 12, "only {checked} rotations checked");
}
