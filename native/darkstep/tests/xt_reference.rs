//! Exact truncation (genesis "XT"; notes/dark-learning-gen6/xtrunc.md): the native three-custodian step under XT equals
//! the Python harness bit for bit (native_ref.py ... --xt, committed in native_ref_results/*_XT.json), refines
//! step_spec, and differs from the statistical step. A wrap-zone opening makes every custodian stop with XT_REDO before
//! the MAC check (a redo, not a key-retiring abort).
use darkstep::node::{custodian, prof, run_local, Prof, DEALER_SEED, OWNER_SEED};
use darkstep::party::XT_REDO;
use darkstep::step::{inputs_for, Program};

fn reference(name: &str) -> serde_json::Value {
    let path = format!("{}/../../research/dark_learning_2026_11_06/native_ref_results/{name}.json", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

fn pf(n: usize, l: usize, f: u32, d: usize, prog: Program, xt: bool) -> Prof {
    let mut p = prof(&[n.to_string(), l.to_string(), f.to_string(), d.to_string()]);
    p.program = prog;
    p.xt = xt;
    p
}

fn equal_to(res: &serde_json::Value, r: &serde_json::Value) {
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
fn xt_d8_n4096_equals_python() {
    let (res, _) = run_local(&pf(4096, 3, 118, 8, Program::HARNESS, true), None);
    equal_to(&res, &reference("native_ref_N4096_L3_F118_d8_XT"));
    // negative control: the statistical reference is a different transcript (the comparison can fail)
    assert_ne!(res["transcript"], reference("native_ref_N4096_L3_F118_d8")["transcript"]);
}

#[test]
fn xt_gen6_d64_n4096_equals_python() {
    let (res, _) = run_local(&pf(4096, 3, 118, 64, Program::GEN6, true), None);
    equal_to(&res, &reference("native_ref_N4096_L3_F118_d64_GEN6_XT"));
}

/// The first truncation's mask is moved (consistently, with its MAC shares) so that its opening is c = 0: every
/// custodian stops with XT_REDO and no step output; the same tapes unmoved are accepted.
#[test]
fn wrap_zone_is_a_redo() {
    let p = pf(4096, 3, 118, 8, Program::HARNESS, true);
    let plain = inputs_for(p.d, &p.program);
    let (cs, dl) = darkstep::tape::deal_step_dealer_prog_xt(p.t, p.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(p.t), false, &p.program, false, true);
    let run = |tapes: Vec<darkstep::tape::Tape>| -> Vec<serde_json::Value> {
        let ls: Vec<std::net::TcpListener> = (0..3).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
        let addrs: Vec<std::net::SocketAddr> = ls.iter().map(|l| l.local_addr().unwrap()).collect();
        let hs: Vec<_> = ls
            .into_iter()
            .zip(tapes)
            .enumerate()
            .map(|(i, (l, tape))| {
                let (addrs, cs, mut p2) = (addrs.clone(), cs.clone(), p.clone());
                p2.colocated = true;
                std::thread::spawn(move || custodian(i, &p2, darkstep::net::Net::connect(i, l, &addrs), tape, &cs, None).0)
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    };
    let honest = run(dl.tapes.clone());
    assert!(honest.iter().all(|r| r["verdict"] == "ACCEPT"), "{honest:?}");
    // the first truncation's opening c, from the honest transcript's first trunc entry: shift r by -c on party 0
    let first_tr = dl.tapes[0].tags.iter().position(|&t| t == darkstep::tape::Tag::Tr as u8).unwrap();
    // the honest opening c = z1[0] + 2^K + r (no wrap): z1 = W1 x in the clear, r the sum of the dealt shares
    let z1_0: i64 = (0..p.d).map(|j| plain.w1[0][j] * plain.x[j]).sum();
    let r: u64 = (0..3).fold(0u64, |a, i| darkstep::arith::addmod(a, dl.tapes[i].sh[first_tr], p.t));
    let c0 = darkstep::arith::addmod(darkstep::arith::addmod(darkstep::arith::from_i64(z1_0, p.t), 1 << p.program.k1, p.t), r, p.t);
    assert!(c0 >= 1 << (p.program.k1 + 1), "the honest opening is outside the zone");
    let mut moved = dl.tapes.clone();
    let mv = |v: u64, by: u64| darkstep::arith::submod(v, by, p.t);
    moved[0].sh[first_tr] = mv(moved[0].sh[first_tr], c0);
    for i in 0..3 {
        // MAC shares of r - c0: party i subtracts alpha_i c0 (alpha = sum alpha_i)
        moved[i].mac[first_tr] = mv(moved[i].mac[first_tr], darkstep::arith::mulmod(dl.alpha_sh[i], c0, p.t));
    }
    let out = run(moved);
    for (i, r) in out.iter().enumerate() {
        assert_eq!(r["verdict"], "REFUSED", "party {i}");
        assert!(r["by"].as_str().unwrap().starts_with(XT_REDO), "party {i}: {}", r["by"]);
    }
}
