//! The native three-custodian step equals the Python harness (native_ref.py) bit for bit: the public transcript, every
//! party's final authenticated shares, and every party's MAC-check sigma. Reference digests are the committed outputs
//! of `python3 native_ref.py N L F d` in research/dark_learning_2026_11_06/native_ref_results/.
use darkstep::node::{prof, run_local};

fn check(n: usize, l: usize, f: u32, d: usize) {
    check_with(n, l, f, d, 0);
}

fn check_with(n: usize, l: usize, f: u32, d: usize, ret_primes: usize) -> serde_json::Value {
    check_round(n, l, f, d, ret_primes, None)
}

fn check_round(n: usize, l: usize, f: u32, d: usize, ret_primes: usize, round: Option<(u32, u32)>) -> serde_json::Value {
    let path = format!(
        "{}/../../research/dark_learning_2026_11_06/native_ref_results/native_ref_N{n}_L{l}_F{f}_d{d}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let r: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    let mut pf = prof(&[n.to_string(), l.to_string(), f.to_string(), d.to_string()]);
    pf.ret_primes = ret_primes;
    pf.ret_round = round;
    let (res, _) = run_local(&pf, None);
    assert_eq!(res["verdict"], "ACCEPT");
    assert_eq!(res["refines_spec"], true);
    assert_eq!(res["transcript"], r["transcript"], "transcript digest");
    for i in 0..3 {
        assert_eq!(res["parties"][i], r["parties"][i.to_string()], "party {i} shares digest");
        assert_eq!(res["sigma"][i], r["sigma"][i.to_string()], "party {i} sigma");
    }
    assert_eq!(res["detail"][0]["wire"], r["wire"], "SPDZ wire counts");
    for i in 0..3 {
        let det = &res["detail"][i];
        let to = det["bytes_sent_to"].as_object().unwrap();
        assert_eq!(to.len(), 2, "party {i}: one entry per peer");
        assert!(!to.contains_key(&i.to_string()), "party {i}: no self link");
        for tag in ["open", "he_ct", "he_ret", "ctrl", "proof"] {
            let links: u64 = to.values().map(|l| l[tag].as_u64().unwrap()).sum();
            assert_eq!(links, det["bytes_sent"][tag].as_u64().unwrap(), "party {i} tag {tag}: links sum to the total");
        }
        assert!(to.values().all(|l| l["he_ct"].as_u64().unwrap() > 0), "party {i}: HE ciphertexts go to both peers");
    }
    res
}

/// HE returns modulus-switched to 2 primes, c0 only where the recipient decrypts: every decryption is still exact,
/// so the transcript, all shares and sigmas stay equal to the Python reference, on fewer bytes.
#[test]
fn compressed_returns_stay_bit_exact() {
    for (n, l, f) in [(4096, 3, 118), (16384, 4, 175)] {
        let full = check_with(n, l, f, 64, 0);
        let small = check_with(n, l, f, 64, 2);
        let ret = |r: &serde_json::Value| r["detail"][0]["bytes_sent"]["he_ret"].as_u64().unwrap();
        let ratio = ret(&small) as f64 / ret(&full) as f64;
        eprintln!("N = {n}, L = {l}: he_ret {} -> {} bytes per party ({ratio:.3})", ret(&full), ret(&small));
        assert!(ratio < 0.5 + 0.1 / l as f64, "ratio {ratio}");
    }
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

#[test]
fn d64_n16384_ledger_profile() {
    check(16384, 4, 175, 64);
}

/// Tapes that also carry the proof's truncation range bits (Tag::Trhb, cosnark_gates.RecEngine's stream) give the same
/// step, and the middle's atom count grows by exactly those bits: sum over truncations of K + 40 - s.
#[test]
fn proof_atoms_on_the_tape_leave_the_step_unchanged() {
    let pf = prof(&["4096".into(), "3".into(), "118".into(), "64".into()]);
    let (a, _) = darkstep::node::run_local_opts(&pf, None, false);
    let (b, _) = darkstep::node::run_local_opts(&pf, None, true);
    assert_eq!(a["transcript"], b["transcript"]);
    assert_eq!(a["parties"], b["parties"]);
    let d = 64u64;
    let bits = 2 * d * (13 + 40 - 5) + d * (8 + 40 - 4) + d * (13 + 40 - 8);
    let ma = a["detail"][0]["middle_atoms"].as_u64().unwrap();
    let mb = b["detail"][0]["middle_atoms"].as_u64().unwrap();
    assert_eq!(mb - ma, bits);
}

/// Control: one prime is too few (the switching rounding swamps Q_1 / 2t), so decryptions go wrong and the shares
/// no longer equal the reference; the comparison above can fail.
#[test]
#[should_panic]
fn compressed_to_one_prime_breaks_decryption() {
    check_with(16384, 4, 175, 64, 1);
}

#[test]
fn return_primes_needed_is_two_at_both_profiles() {
    for (n, l) in [(4096usize, 3usize), (16384, 4)] {
        let pf = prof(&[n.to_string(), l.to_string(), "118".into(), "8".into()]);
        let rns = darkstep::rns::Rns::new(pf.n, &pf.qs, pf.t);
        assert_eq!(darkstep::bfv::return_primes_needed(&rns), 2);
    }
}

/// The switched returns with their noise bits rounded away (bfv::round_bits): still bit-exact with the reference.
#[test]
fn rounded_returns_stay_bit_exact() {
    for (n, l, f) in [(4096, 3, 118), (16384, 4, 175)] {
        let pf = prof(&[n.to_string(), l.to_string(), f.to_string(), "64".into()]);
        let rb = darkstep::bfv::round_bits(&darkstep::rns::Rns::new(pf.n, &pf.qs, pf.t), f);
        let sw = check_with(n, l, f, 64, 2);
        let rd = check_round(n, l, f, 64, 2, Some(rb));
        let ret = |r: &serde_json::Value| r["detail"][0]["bytes_sent"]["he_ret"].as_u64().unwrap();
        eprintln!("N = {n}, L = {l}: round bits (c0, c1) = {rb:?}; he_ret {} -> {} ({:.3})", ret(&sw), ret(&rd), ret(&rd) as f64 / ret(&sw) as f64);
        assert!(ret(&rd) < ret(&sw));
    }
}

/// Control: rounding c1 nine bits past the bound (the bound is worst case; the typical |r1 s| is about
/// sqrt(2N/3) 2^(b1-1), seven bits below it) breaks decryption, so the comparison above can fail.
#[test]
#[should_panic]
fn rounding_past_the_bound_breaks_decryption() {
    let pf = prof(&["16384".into(), "4".into(), "175".into(), "64".into()]);
    let (b0, b1) = darkstep::bfv::round_bits(&darkstep::rns::Rns::new(pf.n, &pf.qs, pf.t), 175);
    check_round(16384, 4, 175, 64, 2, Some((b0, b1 + 9)));
}
