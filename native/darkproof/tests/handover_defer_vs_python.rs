//! Cut E's handover (handover.prove_defer): the native prover over six in-process custodians against handover.py's
//! bytes, the native verifier's new pending claims against Python's, and the refusals.
//!
//!   cd research/dark_learning_2026_11_06
//!   DL_DETERMINISTIC=7 python3 handover_vectors.py <dir> 4 demo-x2de
//!   HANDOVER_DEFER_VECTORS=<dir> cargo test --release -p darkproof --features test-det --test handover_defer_vs_python -- --nocapture
//!
//! Per vector: every party holds the same proof, equal to Python's bytes; byte_len is the length; the verifier accepts
//! and returns Python's new pending (points r, carry roots cN) and the new parties' DeferIn carries those roots;
//! negative controls: the head's carries replaced by another's (the discharge fails), a final-head form of the proof
//! offered to the pending head, another new set, a flipped byte; a second opening of the old head is refused.
use darkproof::defer::Pending;
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

struct Vec_ {
    old: BTreeMap<String, Vec<Vec<u64>>>,
    new: BTreeMap<String, Vec<Vec<u64>>>,
    labels: BTreeMap<String, String>,
    carry: BTreeMap<String, Vec<Vec<u64>>>,
    carry_labels: BTreeMap<String, String>,
}

type Out = Result<(Vec<u8>, Option<darkproof::defer::DeferIn>), String>;

fn run(pr: &Profile, d: usize, ctx: &HandoverCtx, v: &Vec_, pend: Option<&Pending>, spent: usize, det: &Det) -> Vec<Out> {
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
                            let mut c = PcsParty::commit(&pr.w_life(), &v.old[k][g], &v.labels[k], g, det);
                            c.opened_lives = spent;
                            c
                        } else {
                            PcsParty::commit(&pr.w_life(), &v.new[k][g - 3], k, g - 3, det)
                        };
                        mine.insert(k.to_string(), c);
                    }
                    let mut oc: BTreeMap<String, PcsParty> = BTreeMap::new();
                    if g < 3 {
                        for k in ["c1p", "c2p"] {
                            let mut c = PcsParty::commit(pr, &v.carry[k][g], &v.carry_labels[k], g, det);
                            c.opened_lives = 1;
                            oc.insert(k.to_string(), c);
                        }
                    }
                    handover::prove_defer(pr, lp, d, 3, 3, ctx, &mut mine, pend, if g < 3 { Some(&mut oc) } else { None }, &mut net, det)
                        .map(|(p, dfr)| (handover::encode(pr, d, &p), dfr))
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap_or_else(|_| Err("party thread ended: a peer refused".into()))).collect()
    })
}

#[test]
fn handover_defer_equals_python() {
    let dir = PathBuf::from(std::env::var("HANDOVER_DEFER_VECTORS").expect("set HANDOVER_DEFER_VECTORS (see the header)"));
    let det = Det(Some("7".into()));
    let mut done = 0;
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok()).map(|e| e.path())
        .filter(|p| p.extension().map(|x| x == "json").unwrap_or(false)).collect();
    names.sort();
    for path in names {
        let v: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        if v["deferred"].is_null() {
            continue;
        }
        darkproof::field::set_p(v["p"].as_u64().unwrap());
        let pr = Profile::by_name(v["profile"].as_str().unwrap()).unwrap();
        assert!(pr.defer);
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
        let m = |x: &Value, ks: &[&str]| ks.iter().map(|k| (k.to_string(), shares(&x[*k]))).collect::<BTreeMap<_, _>>();
        let df = &v["deferred"];
        let vec_ = Vec_ {
            old: m(&v["old"], &["W1", "W2"]),
            new: m(&v["new"], &["W1", "W2"]),
            labels: ["W1", "W2"].iter().map(|k| (k.to_string(), v["old_labels"][*k].as_str().unwrap().to_string())).collect(),
            carry: m(&df["carry_shares"], &["c1p", "c2p"]),
            carry_labels: ["c1p", "c2p"].iter().map(|k| (k.to_string(), df["carry_labels"][*k].as_str().unwrap().to_string())).collect(),
        };
        let flat = |x: &Value| x.as_array().unwrap().iter().map(|a| a.as_u64().unwrap()).collect::<Vec<u64>>();
        // the head's pending claims as the ledger holds them: points, and the old carries' roots
        let croots = |labels: &BTreeMap<String, String>, sh: &BTreeMap<String, Vec<Vec<u64>>>| -> BTreeMap<String, Vec<[u8; 32]>> {
            ["c1p", "c2p"].iter().map(|k| (k.to_string(), (0..3).map(|g| PcsParty::commit(&pr, &sh[*k][g], &labels[*k], g, &det).root).collect())).collect()
        };
        let pend = Pending {
            points: ["W1", "W2"].iter().map(|k| (k.to_string(), flat(&df["points"][*k]))).collect(),
            carry_roots: croots(&vec_.carry_labels, &vec_.carry),
        };
        let py = std::fs::read(dir.join(v["bytes"].as_str().unwrap())).unwrap();
        let t = std::time::Instant::now();
        let outs = run(&pr, d, &ctx, &vec_, Some(&pend), 0, &det);
        let secs = t.elapsed().as_secs_f64();
        let nb = outs[0].as_ref().expect("party 0 proves").0.clone();
        for (g, o) in outs.iter().enumerate() {
            assert_eq!(o.as_ref().unwrap().0, nb, "party {g} holds another proof");
        }
        let first = nb.iter().zip(&py).position(|(a, b)| a != b);
        assert!(nb == py, "d = {d} {}: native bytes differ from Python's (lengths {} / {}, first difference at {:?})", pr.name, nb.len(), py.len(), first);
        let lp = pr.ligero();
        let parsed = handover::decode_defer(&pr, &nb, d, 3, 3, true).unwrap();
        assert_eq!(nb.len(), handover::byte_len(&pr, d, &parsed), "byte_len differs from the bytes' length");
        let head: BTreeMap<String, Vec<[u8; 32]>> = ["W1", "W2"].iter().map(|k| (k.to_string(), parsed.old_roots[*k].clone())).collect();
        let tv = std::time::Instant::now();
        let (nr, np) = handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, Some(&pend), &nb).expect("native verifier accepts");
        let vsecs = tv.elapsed().as_secs_f64();
        assert_eq!(nr, parsed.new_roots);
        // the new pending equals Python's (pending_json: flat points, hex roots)
        let want = &df["new_pending"];
        for k in ["W1", "W2"] {
            assert_eq!(np.points[k], flat(&want["points"][k]), "new pending point {k}");
        }
        for k in ["c1p", "c2p"] {
            let hx: Vec<String> = np.carry_roots[k].iter().map(|h| pycompat::repr::hex(h)).collect();
            let wh: Vec<String> = want["carry_roots"][k].as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect();
            assert_eq!(hx, wh, "new pending carry roots {k}");
        }
        // each new party's DeferIn: its carries are the recorded roots, its shares Python's
        for j in 0..3 {
            let dfr = outs[3 + j].as_ref().unwrap().1.as_ref().expect("a new party gets its DeferIn");
            assert_eq!(dfr.points, np.points);
            for k in ["c1p", "c2p"] {
                assert_eq!(dfr.carries[k].root, np.carry_roots[k][j]);
                let ws = shares(&df["new_carry_shares"][k]);
                assert_eq!(&dfr.carries[k].ext[..ws[j].len()], &ws[j][..], "new carry share {k} of party {j}");
            }
            assert!(outs[j].as_ref().unwrap().1.is_none());
        }
        println!("[{} d = {d}] native prove {secs:.3}s (6 parties), verify {vsecs:.3}s, {} bytes == Python; new pending == Python's", pr.name, nb.len());
        // refusals
        let mut flip = nb.clone();
        flip[nb.len() / 2] ^= 1;
        assert!(handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, Some(&pend), &flip).is_err(), "flipped byte accepted");
        let e = handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, None, &nb).unwrap_err();
        println!("  the pending head's proof offered as for a final head: {e}");
        let mut other_pend = pend.clone();
        other_pend.points.get_mut("W1").unwrap()[0] ^= 1;
        let e = handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, Some(&other_pend), &nb).unwrap_err();
        println!("  other pending points: {e}");
        assert!(e.contains("Ligero") || e.contains("mismatch"), "{e}");
        // a forged old carry (custodian 0's c1p + 1): the discharge W1(r_k) = c1p fails
        let mut bad = Vec_ { carry: vec_.carry.clone(), old: vec_.old.clone(), new: vec_.new.clone(), labels: vec_.labels.clone(), carry_labels: vec_.carry_labels.clone() };
        bad.carry.get_mut("c1p").unwrap()[0][0] = darkproof::field::add(bad.carry["c1p"][0][0], 1);
        let bpend = Pending { points: pend.points.clone(), carry_roots: croots(&bad.carry_labels, &bad.carry) };
        let bo = run(&pr, d, &ctx, &bad, Some(&bpend), 0, &det);
        let bb = bo[0].as_ref().unwrap().0.clone();
        let e = handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, Some(&bpend), &bb).unwrap_err();
        println!("  a forged old carry: {e}");
        assert!(e.contains("Ligero"), "{e}");
        // another new set: other bytes, refused under the original context
        let mut other = ctx.clone();
        other.new_set[2] = "c9".into();
        let ob = run(&pr, d, &other, &vec_, Some(&pend), 0, &det)[0].as_ref().unwrap().0.clone();
        assert_ne!(ob, py);
        assert!(handover::verify_defer(&pr, &lp, d, 3, 3, &ctx, &head, Some(&pend), &ob).is_err());
        // a second opening of the old head (its one life spent)
        let second = run(&pr, d, &ctx, &vec_, Some(&pend), 1, &det);
        for g in 0..3 {
            assert!(matches!(&second[g], Err(e) if e.contains("LifeExhausted")), "a second opening was not refused");
        }
        done += 1;
    }
    assert!(done >= 1, "no cut E vectors in {}", dir.display());
}
