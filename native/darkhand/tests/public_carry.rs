//! side::carry_is_public: true for darkproof's public genesis commitment, false for a secret share's commitment
//! (the negative control: the same vector committed with secret coins).
//!   cargo test --release -p darkhand --test public_carry
#[test]
fn public_genesis_is_recognised_and_a_secret_commitment_is_not() {
    let pr = darkproof::Profile::by_name("demo").unwrap();
    let p = darkstep::node::prof(&["8192".into(), "3".into(), "118".into(), "16".into()]).t;
    darkproof::field::set_p(p);
    let d = 16;
    let w: Vec<i64> = (0..(d * d) as i64).map(|x| x % 7 - 3).collect();
    let (coms, _) = darkproof::run::public_genesis(&pr, d, 0, &w, &w, 3);
    assert!(darkhand::side::carry_is_public(&coms["W1"], p));
    let (coms1, _) = darkproof::run::public_genesis(&pr, d, 1, &w, &w, 3);
    assert!(darkhand::side::carry_is_public(&coms1["W2"], p), "party 1's zero commitment is public too");
    let share: Vec<u64> = w.iter().map(|&v| darkproof::field::from_i64(v)).collect();
    let secret = darkproof::pcs::PcsParty::commit(&pr, &share, "W1", 0, &darkproof::rng::Det(None));
    assert!(!darkhand::side::carry_is_public(&secret, p));
}
