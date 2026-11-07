//! darktrain equals the Python data owner and step_spec (research/.../train_owner.py digest): the seeded init and
//! the weights after three MNIST steps under a gen-6-shaped program at d = 1024, as sha256(repr((W1, W2))).
//! Negative control: one step fewer gives a different digest.
use darktrain::*;

fn digest(d: usize, w1: &[i64], w2: &[i64]) -> String {
    weights_digest(d, w1, w2)
}

#[test]
fn equals_python_owner_and_step_spec() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../research/dark_learning_2026_11_06");
    let gj = r#"{"d":1024,"hid":1024,"s2":6,"s3":10,"rnd2":true,"rnd3":true,"a1":256,"a2":64,"ypos":128,"xenc":"mc","bias":true}"#;
    let gp = std::env::temp_dir().join(format!("darktrain_vs_python_{}.json", std::process::id()));
    std::fs::write(&gp, gj).unwrap();
    let out = std::process::Command::new("python3")
        .args(["-I", &format!("{dir}/train_owner.py"), "digest", gp.to_str().unwrap(), &format!("{dir}/data/mnist"), "3"])
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&gp);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let py: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    let c: Cfg = serde_json::from_str(gj).unwrap();
    let m = data::load(std::path::Path::new(&c.data)).unwrap();
    let c = c.with_means(&m);
    let (mut w1, mut w2) = init(&c);
    assert_eq!(digest(c.d, &w1, &w2), py["init"].as_str().unwrap(), "init");
    let ord = order(c.seed_order, m.train.n);
    let mut bd = Bounds::default();
    let mut before_last = String::new();
    for s in 0..3 {
        if s == 2 {
            before_last = digest(c.d, &w1, &w2);
        }
        let (x, y) = encode(&c, m.train.image(ord[s]), m.train.lab[ord[s]]);
        fast_step(&c, &mut w1, &mut w2, &x, &y, &mut bd);
    }
    assert_eq!(bd.violations(), 0);
    let after = digest(c.d, &w1, &w2);
    assert_eq!(after, py["after"].as_str().unwrap(), "after three steps");
    assert_ne!(before_last, after, "control: the last step changes the weights");
    // the custodians' evaluation: per-example strict correctness on test 0..20, and the released count
    let per: Vec<u64> = (0..20)
        .map(|t| {
            let ev = evaluate(&c, &w1, &w2, &TestOne(&m.test, t).split(), 1);
            ev.acc_o as u64
        })
        .collect();
    let want: Vec<u64> = py["per_example"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap()).collect();
    assert_eq!(per, want, "per-example correctness");
    assert_eq!(per.iter().sum::<u64>(), py["release"][1].as_u64().unwrap());
    assert!(per.iter().any(|&v| v == 1) && per.iter().any(|&v| v == 0), "control: both outcomes occur");
}

struct TestOne<'a>(&'a data::Split, usize);
impl TestOne<'_> {
    fn split(&self) -> data::Split {
        data::Split { img: self.0.image(self.1).to_vec(), lab: vec![self.0.lab[self.1]], n: 1 }
    }
}
