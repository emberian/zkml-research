//! The production handover (no deterministic hook anywhere): two handovers of the SAME state (the same old and new
//! share vectors) give different commitments and different proof bytes, and both verify. A prover whose secret coins
//! came from public data would produce the same bytes twice; this fails then.
//!
//!   cargo test --release -p darkproof --test handover_production -- --nocapture
use darkproof::handover::{self, HandoverCtx};
use darkproof::net::mem_mesh;
use darkproof::pcs::PcsParty;
use darkproof::rng::Det;
use darkproof::{field, Profile};
use std::collections::BTreeMap;

type M = BTreeMap<String, Vec<Vec<u64>>>;

fn once(pr: &Profile, d: usize, ctx: &HandoverCtx, old: &M, new: &M) -> (Vec<u8>, BTreeMap<String, Vec<[u8; 32]>>) {
    let lp = pr.ligero();
    let det = Det(None);
    let outs: Vec<_> = std::thread::scope(|s| {
        let hs: Vec<_> = mem_mesh(6)
            .into_iter()
            .enumerate()
            .map(|(g, mut net)| {
                let (lp, det) = (&lp, &det);
                s.spawn(move || {
                    let mut mine: BTreeMap<String, PcsParty> = ["W1", "W2"]
                        .iter()
                        .map(|k| {
                            let c = if g < 3 {
                                let mut c = PcsParty::commit(pr, &old[*k][g], &format!("{k}n"), g, det);
                                c.opened_lives = 1;
                                c
                            } else {
                                PcsParty::commit(pr, &new[*k][g - 3], k, g - 3, det)
                            };
                            (k.to_string(), c)
                        })
                        .collect();
                    handover::prove(pr, lp, d, 3, 3, ctx, &mut mine, &mut net, det).unwrap()
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let b = handover::encode(pr, d, &outs[0]);
    handover::verify(pr, &lp, d, 3, 3, ctx, &outs[0].old_roots, &b).expect("verifies");
    (b, outs[0].old_roots.clone())
}

#[test]
fn two_production_handovers_differ_and_verify() {
    for name in ["demo", "ledger"] {
        let pr = Profile::by_name(name).unwrap();
        let d = 16;
        let p = field::p();
        let old: M = ["W1", "W2"].iter().map(|k| (k.to_string(), (0..3).map(|_| handover::os_field(d * d, p)).collect())).collect();
        // production resharing: two reshares of one share differ and both sum to it
        let a = handover::reshare_os(&old["W1"][0], 3);
        let b = handover::reshare_os(&old["W1"][0], 3);
        assert_ne!(a, b, "two reshares drew the same subshares");
        for parts in [&a, &b] {
            let sum = handover::combine(&parts.iter().map(|v| v.as_slice()).collect::<Vec<_>>());
            assert_eq!(sum, old["W1"][0]);
        }
        let new: M = old
            .iter()
            .map(|(k, v)| {
                let subs: Vec<Vec<Vec<u64>>> = v.iter().map(|s| handover::reshare_os(s, 3)).collect();
                (k.clone(), (0..3).map(|j| handover::combine(&subs.iter().map(|q| q[j].as_slice()).collect::<Vec<_>>())).collect())
            })
            .collect();
        let ctx = HandoverCtx {
            model: "mind-h".into(),
            epoch_old: 0,
            epoch_new: 1,
            after_step: 1,
            old_set: vec!["c0".into(), "c1".into(), "c2".into()],
            new_set: vec!["c3".into(), "c4".into(), "c5".into()],
        };
        let (b1, r1) = once(&pr, d, &ctx, &old, &new);
        let (b2, r2) = once(&pr, d, &ctx, &old, &new);
        assert_ne!(r1, r2, "{name}: the same shares committed to the same roots twice (tails or salts not secret)");
        assert_ne!(b1, b2, "{name}: two production handovers gave the same bytes");
        let same = b1.iter().zip(&b2).filter(|(x, y)| x == y).count();
        println!("[{name} d = {d}] two production handovers: {} bytes each, both verify, {:.4} of bytes equal", b1.len(), same as f64 / b1.len() as f64);
    }
}
