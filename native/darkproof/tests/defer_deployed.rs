//! Cut E (DEFER) in the deployed run: what a custodian process (dl-custodian) keeps and calls.
//! - The carry it checkpoints (StepProof.child; pcs::write_carry / read_carry) holds W1, W2 (one life) and, while the
//!   head is pending, its carries c1p, c2p; the points of the pending claims are the ledger replica's
//!   (Ledger.pending). run::carry_in joins the two and refuses a carry and a ledger that disagree.
//! - The discharging calls: run::prove_step_l (the next step), run::release_custodian_l (the release),
//!   run::close_custodian then Ledger::close (a halted run).
//! The end-to-end rows run the darkproof binary's ds-chain (three darkstep custodians over TCP on this host,
//! d = 16, demo-x2de, the harness shifts with R3 128, public genesis, the carry through its checkpoint after every
//! step):
//!   cargo test --release -p darkproof --features tcp --test defer_deployed
#![cfg(feature = "tcp")]
use darkproof::defer::{Pending, CARRY_IN};
use darkproof::pcs::{read_carry, write_carry, PcsParty};
use darkproof::rng::Det;
use std::collections::BTreeMap;

fn pr() -> darkproof::Profile {
    let pr = darkproof::Profile::by_name("demo-x2de").unwrap();
    darkproof::field::set_p(darkproof::wire::he_field(&pr).unwrap());
    pr
}

/// A party's carry as a DEFER step leaves it: W1, W2 committed with one life, the two carries with two (one spent).
fn carry(pr: &darkproof::Profile) -> BTreeMap<String, PcsParty> {
    let share: Vec<u64> = (0..256u64).map(|v| v * 7919 + 3).collect();
    let mut c = BTreeMap::new();
    for k in ["W1", "W2"] {
        c.insert(k.to_string(), PcsParty::commit(&pr.w_life(), &share, &format!("{k}n"), 0, &Det::off()));
    }
    for (k, lab) in [("c1p", "c1"), ("c2p", "c2")] {
        let mut p = PcsParty::commit(pr, &[5, 6], lab, 0, &Det::off());
        p.opened_lives = 1;
        c.insert(k.to_string(), p);
    }
    c
}

fn pending(c: &BTreeMap<String, PcsParty>) -> Pending {
    let mut points = BTreeMap::new();
    points.insert("W1".to_string(), vec![1u64; 16]);
    points.insert("W2".to_string(), vec![2u64; 16]);
    Pending { points, carry_roots: CARRY_IN.iter().map(|k| (k.to_string(), vec![c[*k].root; 3])).collect() }
}

#[test]
fn checkpoint_keeps_the_carries_and_carry_in_joins_the_ledger() {
    let pr = pr();
    let c = carry(&pr);
    let mut buf = Vec::new();
    write_carry(&c, &mut buf).unwrap();
    let mut back = read_carry(&mut buf.as_slice(), &pr).unwrap();
    assert_eq!(back.keys().collect::<Vec<_>>(), ["W1", "W2", "c1p", "c2p"]);
    for (k, x) in &c {
        let b = &back[k];
        assert_eq!((b.root, b.opened_lives, b.max_lives, b.shape.hide, b.shape.nmask), (x.root, x.opened_lives, x.max_lives, x.shape.hide, x.shape.nmask), "{k}");
    }
    // a W keeps its single life (hide T, EXT masks) through the checkpoint
    assert_eq!((back["W1"].max_lives, back["W1"].shape.hide, back["W1"].shape.nmask), (1, pr.t_cols, pr.ext));
    let pend = pending(&c);
    let dfr = darkproof::run::carry_in(&mut back, Some(&pend)).unwrap().unwrap();
    assert_eq!(back.keys().collect::<Vec<_>>(), ["W1", "W2"], "carry_in takes the carries out");
    assert_eq!(dfr.points, pend.points);
    assert_eq!(dfr.carries["c1p"].root, c["c1p"].root);
    // the head final and no carries: nothing to discharge
    assert!(darkproof::run::carry_in(&mut back, None).unwrap().is_none());
    // refused: the ledger's head pending but the carry without its carries; the reverse
    let e = darkproof::run::carry_in(&mut back, Some(&pend)).err().unwrap();
    assert!(e.contains("does not hold its carries"), "{e}");
    let mut c2 = carry(&pr);
    let e = darkproof::run::carry_in(&mut c2, None).err().unwrap();
    assert!(e.contains("the ledger's head is final"), "{e}");
}

/// The d = 16 program: the harness shifts with GEN6's rounding (R3 128), he, RC, LB (the train lane's consistent
/// pair for d = 16).
const PROGRAM: &str = r#"{"R3": 128, "RC": true, "LB": true}"#;

/// Its public-genesis cfg (darktrain's; the proof lane's cfg16 with the train lane's corrections). The intervals are
/// written from the program's own (StepParams::bound, what the proof proves), so the cfg's copy cannot drift.
fn cfg16() -> String {
    let p = darkproof::step::StepParams { r3: 128, rc: true, lb: true, he: true, ..darkproof::step::StepParams::HARNESS };
    let iv = |nm: &str| {
        let (a, b) = p.bound(nm, 10);
        format!("[{a}, {b}]")
    };
    format!(
        r#"{{"d": 16, "hid": 16, "reps": 1, "s1a": 5, "s1b": 5, "k1": 13, "s2": 4, "k2": 8, "s3": 8, "k3": 13, "rnd3": true, "t_lo": -128, "xenc": "mc", "tile": 0, "bias": true, "ypos": 128, "yneg": 0, "rnd2": true, "seed_init": 1, "a1": 7, "a2": 3, "eval_n": 4, "intervals": {{"step": {{"z1": {}, "z2": {}, "e": {}, "bg_plus_R3": {}}}, "release": {{"z1": {}, "z2_class": {}, "cmp": {}}}}}, "release": {{"M": 4, "examples": "t10k indices 0..3", "opened": "C", "KC": 10}}}}"#,
        iv("z1"), iv("z2"), iv("e"), iv("bg"), iv("z1"), iv("score"), iv("compare")
    )
}

fn ds_chain_run(steps: &str, env: &[(&str, &str)]) -> (bool, String) {
    let cfgp = std::env::temp_dir().join(format!("defer-deployed-cfg16-{}-{steps}-{}.json", std::process::id(), env.len()));
    std::fs::write(&cfgp, cfg16()).unwrap();
    let mut c = std::process::Command::new(env!("CARGO_BIN_EXE_darkproof"));
    c.args(["ds-chain", "16", "demo-x2de", steps, "4"]).env("DP_CARRY_RT", "1").env("DP_PG_CFG", &cfgp).env("DP_PROGRAM", PROGRAM);
    for (k, v) in env {
        c.env(k, v);
    }
    let out = c.output().unwrap();
    let _ = std::fs::remove_file(&cfgp);
    (out.status.success(), format!("{}\n{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)))
}

/// ds-chain's plaintext-twin lines: every release truncation's inputs against its proved interval.
fn twin(s: &str) -> Vec<&str> {
    s.lines().filter(|l| l.starts_with("plaintext twin: release truncation")).collect()
}

fn ds_chain(steps: &str, close: bool) -> String {
    let (ok, s) = ds_chain_run(steps, if close { &[("DP_CLOSE", "1")] } else { &[] });
    assert!(ok, "ds-chain failed:\n{s}");
    s
}

#[test]
fn three_steps_then_the_release_discharges_the_head() {
    let s = ds_chain("3", false);
    assert!(s.contains(r#"ledger status after the steps: {1: "final (step 2 opened its child)", 2: "final (step 3 opened its child)", 3: "pending"}"#), "{s}");
    assert!(s.contains(r#"3: "final (the release opened its child)""#), "{s}");
    assert_eq!(twin(&s).iter().filter(|l| l.ends_with(", 0 outside")).count(), 3, "the plaintext twin leaves a proved interval:\n{s}");
    assert!(s.contains("DS-CHAIN PASS"), "{s}");
}

/// The negative control: a release set outside the program's domain (x in [0, 10000], |x| <= 7 broken) drives z1 past
/// its proved interval; the range check refuses to prove it.
#[test]
fn an_out_of_domain_release_is_refused_in_proving() {
    let (ok, s) = ds_chain_run("3", &[("DP_XWIDE", "10000")]);
    assert!(!ok, "an out-of-domain release was proved:\n{s}");
    assert!(s.contains("truncation input outside its proved bound: z1"), "{s}");
    let z1 = twin(&s).into_iter().find(|l| l.contains("truncation z1:")).expect("the plaintext twin's z1 line");
    assert!(!z1.ends_with(", 0 outside"), "the plaintext twin is in bound, yet the proof refused:\n{s}");
}

#[test]
fn three_steps_then_the_closing_proof() {
    let s = ds_chain("3", true);
    assert!(s.contains(r#"{1: "final (step 2 opened its child)", 2: "final (step 3 opened its child)", 3: "final (closing proof)"}"#), "{s}");
    assert!(s.contains(r#"a second close: Err("the head is not pending: nothing to close")"#), "{s}");
    assert!(s.contains("a release after the close: Err"), "{s}");
    assert!(s.contains("DS-CHAIN CLOSE PASS"), "{s}");
}
