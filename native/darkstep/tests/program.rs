//! The three-custodian step under the pinned gen 6 program (step::Program::GEN6): at d = 64 on inputs_for's in-bound
//! inputs, the revealed MPC weights equal step_spec's step under GEN6 (refines_spec), and the program changes the
//! step (its transcript differs from HARNESS's). Negative control: custodians running GEN6 with floor instead of the
//! rounding constant (r3 = 0) do not refine the GEN6 plaintext step.
use darkstep::node::{prof, run_local};
use darkstep::step::{inputs_for, Program};

fn pf(prog: Program) -> darkstep::node::Prof {
    let mut p = prof(&["4096".into(), "3".into(), "118".into(), "64".into()]);
    p.program = prog;
    p
}

#[test]
fn gen6_refines_step_spec() {
    let pl = inputs_for(64, &Program::GEN6);
    let (n1, n2) = pl.step_prog(&Program::GEN6).unwrap();
    assert!(n1 != pl.w1 && n2 != pl.w2, "both layers update");
    let (res, _) = run_local(&pf(Program::GEN6), None);
    assert_eq!(res["verdict"], "ACCEPT");
    assert_eq!(res["refines_spec"], true);
    let (h, _) = run_local(&pf(Program::HARNESS), None);
    assert_ne!(res["transcript"], h["transcript"]);
}

#[test]
fn floor_d1_custodians_do_not_refine_gen6() {
    // the custodians run r3 = 0 on GEN6's inputs; the reference is the true GEN6 step
    let pl = inputs_for(64, &Program::GEN6);
    let mut floor = Program::GEN6;
    floor.r3 = 0;
    assert_ne!(pl.step_prog(&floor).unwrap().0, pl.step_prog(&Program::GEN6).unwrap().0, "the rounding matters here");
    // run_local checks each run against its own program, so compare the final shares of the two runs
    let (a, _) = run_local(&pf(Program::GEN6), None);
    let p = pf(floor);
    let (b, _) = run_local(&p, None);
    assert_eq!(b["refines_spec"], true, "floor is itself a consistent program");
    assert_ne!(a["parties"], b["parties"], "and its final shares differ from GEN6's");
}

/// darkstep under GEN6 equals the Python harness under GEN6 (`python3 native_ref.py 4096 3 118 64 --program GEN6`,
/// committed in native_ref_results/): public transcript, every party's final shares and MAC-check sigma, SPDZ wire.
#[test]
fn gen6_equals_native_ref() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../research/dark_learning_2026_11_06/native_ref_results/native_ref_N4096_L3_F118_d64_GEN6.json");
    let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    assert_eq!(r["verdict"], "ACCEPT");
    assert_eq!(r["refines_spec"], true);
    let (res, _) = run_local(&pf(Program::GEN6), None);
    assert_eq!(res["refines_spec"], true);
    assert_eq!(res["transcript"], r["transcript"], "transcript digest");
    for i in 0..3 {
        assert_eq!(res["parties"][i], r["parties"][i.to_string()], "party {i} shares digest");
        assert_eq!(res["sigma"][i], r["sigma"][i.to_string()], "party {i} sigma");
    }
    assert_eq!(res["detail"][0]["wire"], r["wire"], "SPDZ wire counts");
    // control: the HARNESS reference at the same size differs
    let h: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path.replace("_GEN6", "")).unwrap()).unwrap();
    assert_ne!(h["transcript"], r["transcript"]);
}
