//! Exact truncation (genesis "XT"; notes/dark-learning-gen6/xtrunc.md) in the verifier's replay: a truncation opening
//! in the wrap zone (c < 2^(K+1)) is refused by name (Rec::xt_refusal, called by wire::verify_step / verify_release and
//! by the custodians before proving); outside the zone, and without XT, the same replay passes. (The harness's plain
//! SPDZ step: the deployed step's replay also requires its he_outer_commit entries to be 0.)
use darkproof::step::{replay, tables_for, StepParams};

fn prm(xt: bool) -> StepParams {
    StepParams { rc: true, lb: true, rs: true, xt, ..StepParams::HARNESS }
}

#[test]
fn wrap_zone_refused_by_name_under_xt_only() {
    darkproof::field::set_p(2305843009212399617);
    let d = 4;
    let tables = tables_for(-128);
    let n = prm(true).transcript_len(d, false);
    let zeros = vec![0u64; n];
    // every truncation opening 0: inside the zone
    let r = replay(&zeros, d, prm(true), &tables, false).unwrap();
    let e = r.xt_refusal().unwrap_err();
    assert!(e.starts_with("XT: truncation opening in the wrap zone"), "{e}");
    // the same transcript without XT: no refusal (the statistical public check is the range rows')
    assert!(replay(&zeros, d, prm(false), &tables, false).unwrap().xt_refusal().is_ok());
    // every opening 2^20 >= 2^(K+1) for every K of the program: outside the zone
    let big = vec![1u64 << 20; n];
    assert!(replay(&big, d, prm(true), &tables, false).unwrap().xt_refusal().is_ok());
    // one opening just below 2^(K1+1) at the first truncation: refused, and the position is named
    let first = r.xt_zone.unwrap();
    assert_eq!(first, 2 * d * d + 2 * d + d * d + d, "the first truncation opening follows the inputs and the z1 matvec");
    let mut one = big.clone();
    one[first] = (1u64 << (StepParams::HARNESS.k1 + 1)) - 1;
    let e = replay(&one, d, prm(true), &tables, false).unwrap().xt_refusal().unwrap_err();
    assert!(e.contains(&format!("public entry {first}")), "{e}");
}
