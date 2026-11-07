//! The native three-custodian step equals the Python harness (native_ref.py) bit for bit: the public transcript, every
//! party's final authenticated shares, and every party's MAC-check sigma. Reference digests are the committed outputs
//! of `python3 native_ref.py N L F d` in research/dark_learning_2026_11_06/native_ref_results/.
use darkstep::node::{prof, run_local};

fn check(n: usize, l: usize, f: u32, d: usize) {
    let path = format!(
        "{}/../../research/dark_learning_2026_11_06/native_ref_results/native_ref_N{n}_L{l}_F{f}_d{d}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    let pf = prof(&[n.to_string(), l.to_string(), f.to_string(), d.to_string()]);
    let (res, _) = run_local(&pf, None);
    assert_eq!(res["verdict"], "ACCEPT");
    assert_eq!(res["refines_spec"], true);
    assert_eq!(res["transcript"], r["transcript"], "transcript digest");
    for i in 0..3 {
        assert_eq!(res["parties"][i], r["parties"][i.to_string()], "party {i} shares digest");
        assert_eq!(res["sigma"][i], r["sigma"][i.to_string()], "party {i} sigma");
    }
    assert_eq!(res["detail"][0]["wire"], r["wire"], "SPDZ wire counts");
}

#[test]
fn d8_n4096() {
    check(4096, 3, 118, 8);
}

#[test]
fn d64_n4096() {
    check(4096, 3, 118, 64);
}

#[test]
fn d64_n8192_demo_profile() {
    check(8192, 3, 118, 64);
}

/// Negative controls: the comparison can fail. A returner that shifts one matvec share is refused by the
/// Freivalds check; one that shifts an outer-product return is refused by the outer check.
#[test]
fn attacks_refused() {
    let pf = prof(&["4096".into(), "3".into(), "118".into(), "64".into()]);
    for (att, by) in [("mv_wrong_return", "HE matvec: Freivalds"), ("wrong_return", "HE outer: Freivalds")] {
        let (res, _) = run_local(&pf, Some((att.into(), 1)));
        assert_eq!(res["verdict"], "REFUSED", "{att}");
        assert!(res["by"][0].as_str().unwrap().starts_with(by), "{att}: {}", res["by"]);
    }
}
