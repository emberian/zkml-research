//! The gated native step (ceremony keys + the ZKPoPK gate before every ptxct) equals native_ref_gated.py bit for bit:
//! the step digests (transcript, shares, sigma), the ceremony (seed, every registered b_j) and every batch proof
//! (sha256 per sender and call). Negative control: a sender whose first matvec batch is off the layout (forged
//! proof) is refused by both recipients with the reference's reason, before any product.
//!
//!   cargo test --release -p darkstep --features test-det --test vs_reference_gated -- --nocapture
use darkstep::node::{prof, run_local};

const SEED: &str = "g1";

fn reference(name: &str) -> serde_json::Value {
    let path = format!("{}/../../research/dark_learning_2026_11_06/native_ref_results/{name}.json", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

fn gated(n: usize, l: usize, f: u32, d: usize, t: usize) -> darkstep::node::Prof {
    let mut pf = prof(&[n.to_string(), l.to_string(), f.to_string(), d.to_string()]);
    pf.gate = Some(t);
    pf.det_seed = Some(SEED.into());
    pf
}

#[test]
fn gated_d64_n4096() {
    let r = reference("native_ref_gated_N4096_L3_F118_d64_T309");
    let (res, _) = run_local(&gated(4096, 3, 118, 64, 309), None);
    assert_eq!(res["verdict"], "ACCEPT");
    assert_eq!(res["refines_spec"], true);
    assert_eq!(res["transcript"], r["transcript"], "transcript digest");
    for i in 0..3 {
        assert_eq!(res["parties"][i], r["parties"][i.to_string()], "party {i} shares digest");
        assert_eq!(res["sigma"][i], r["sigma"][i.to_string()], "party {i} sigma");
        let g = &res["detail"][i]["gate"];
        assert_eq!(g["ceremony_seed"], r["gate"]["ceremony_seed"], "ceremony seed (party {i}'s view)");
        assert_eq!(g["key_b_sha256"], r["gate"]["key_b_sha256"], "registered keys (party {i}'s view)");
        assert_eq!(g["proofs"], r["gate"]["proofs"][i.to_string()], "party {i}'s batch proofs");
        println!("party {i}: {} batch proofs equal; prove {:.2} s, verify {:.2} s", g["proofs"].as_array().unwrap().len(), g["prove_seconds"], g["verify_seconds"]);
    }
    // the gate does not change the step: the digests are the ungated reference's too
    let u = reference("native_ref_N4096_L3_F118_d64");
    assert_eq!(res["transcript"], u["transcript"]);
}

#[test]
fn gated_off_layout_refused_before_any_product() {
    let r = reference("native_ref_gated_N4096_L3_F118_d64_T309_zk_off_layout0");
    let (res, _) = run_local(&gated(4096, 3, 118, 64, 309), Some(("zk_off_layout".into(), 0)));
    assert_eq!(res["verdict"], "REFUSED");
    assert_eq!(r["verdict"], "REFUSED");
    assert_eq!(r["gate"]["products"], 0);
    for i in 0..3 {
        assert_eq!(res["by"][i], r["by"], "party {i}'s abort reason");
        assert_eq!(res["detail"][i]["he_wire"]["mv"]["he_return"], 0, "party {i} made no matvec return");
    }
    println!("refused: {}", r["by"]);
}
