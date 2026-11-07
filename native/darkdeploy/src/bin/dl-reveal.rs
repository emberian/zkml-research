//! dl-reveal (TEST ONLY: it reassembles the custodians' weight shares, which no deployed run does).
//!
//!   dl-reveal CFG.json STEPS DIR0 DIR1 DIR2
//! Sums shares_<i>.bin from DIRi (darkstep serve --test-keep-shares) and compares the weights with the plaintext
//! twin: darktrain's exact trainer from the same genesis cfg over the same STEPS examples (the owner's order).
//! Prints both weight digests (sha256(repr((W1, W2))), as `darktrain shadow`) and whether they are equal.
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let cfg_bytes = std::fs::read(&a[1]).expect("cfg");
    let c: darktrain::Cfg = serde_json::from_slice(&cfg_bytes).expect("cfg json");
    c.validate().unwrap();
    let steps: usize = a[2].parse().unwrap();
    let m = darktrain::data::load(std::path::Path::new(&c.data)).unwrap();
    let c = c.with_means(&m);
    let d = c.d;
    let pf = darkstep::node::prof(&["16384".into(), "4".into(), "175".into(), d.to_string()]);
    let p = pf.t;
    let shares: Vec<Vec<u64>> = (0..3)
        .map(|i| darkstep::net::bytes_to_u64s(&std::fs::read(std::path::Path::new(&a[3 + i]).join(format!("shares_{i}.bin"))).unwrap()))
        .collect();
    let cen = |v: u64| if v > p / 2 { v as i64 - p as i64 } else { v as i64 };
    let w: Vec<i64> = (0..2 * d * d).map(|k| cen(shares.iter().fold(0, |acc, s| darkstep::arith::addmod(acc, s[2 * k], p)))).collect();
    let (w1, w2) = w.split_at(d * d);
    // the twin
    let (mut t1, mut t2) = darktrain::init(&c);
    let ord = darktrain::order(c.seed_order, m.train.n);
    let mut bd = darktrain::Bounds::default();
    for k in 0..steps {
        let ex = ord[k % m.train.n];
        let (x, y) = darktrain::encode(&c, m.train.image(ex), m.train.lab[ex]);
        darktrain::fast_step(&c, &mut t1, &mut t2, &x, &y, &mut bd);
    }
    let got = darktrain::weights_digest(d, w1, w2);
    let want = darktrain::weights_digest(d, &t1, &t2);
    println!("{}", serde_json::json!({"steps": steps, "revealed_sha256": got, "twin_sha256": want, "equal": got == want,
        "twin_bound_violations": bd.violations()}));
}
