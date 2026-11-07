//! The fast trainer equals the scalar step (step_spec.step under the program) on random and MNIST cases, over
//! several consecutive steps (weights carried), including the rounding options; a perturbed fast step is caught.
use darktrain::*;
use pycompat::PyRandom;

fn same(c: &Cfg, w1: &[i64], w2: &[i64], xs: &[(Vec<i64>, Vec<i64>)]) -> bool {
    let (mut a1, mut a2, mut b1, mut b2) = (w1.to_vec(), w2.to_vec(), w1.to_vec(), w2.to_vec());
    let mut bd = Bounds::default();
    for (x, y) in xs {
        let ta = reference_step(c, &mut a1, &mut a2, x, y);
        let tb = fast_step(c, &mut b1, &mut b2, x, y, &mut bd);
        if ta.z2 != tb.z2 || ta.d1 != tb.d1 || ta.b != tb.b {
            return false;
        }
    }
    a1 == b1 && a2 == b2
}

#[test]
fn random_dense_cases() {
    for (d, rnd) in [(16usize, false), (64, false), (64, true)] {
        let mut c = Cfg { d, hid: d, reps: 1, s1a: 5, s1b: 5, s2: 4, s3: 8, rnd3: rnd, ..Default::default() };
        c.tile = 0;
        let mut r = PyRandom::from_u64(d as u64 + rnd as u64);
        let w1: Vec<i64> = (0..d * d).map(|_| r.randint_i64(-7, 7)).collect();
        let w2: Vec<i64> = (0..d * d).map(|_| r.randint_i64(-7, 7)).collect();
        let xs: Vec<(Vec<i64>, Vec<i64>)> =
            (0..5).map(|_| ((0..d).map(|_| r.randint_i64(-7, 7)).collect(), (0..d).map(|_| r.randint_i64(-7, 7)).collect())).collect();
        assert!(same(&c, &w1, &w2, &xs), "d = {d}");
        // negative control: a different program (s3 + 1) gives different weights, so the comparison can fail
        let mut w1b = w1.clone();
        let mut w2b = w2.clone();
        let mut bd = Bounds::default();
        let c2 = Cfg { s2: 3, ..c.clone() };
        for (x, y) in &xs {
            fast_step(&c2, &mut w1b, &mut w2b, x, y, &mut bd);
        }
        let (mut a1, mut a2) = (w1.clone(), w2.clone());
        for (x, y) in &xs {
            reference_step(&c, &mut a1, &mut a2, x, y);
        }
        assert!(a1 != w1b || a2 != w2b, "control: s2 must matter");
    }
}

#[test]
fn mnist_cases_d1024() {
    let c = Cfg { d: 1024, hid: 1024, s1a: 11, s1b: 11, a1: 64, a2: 4, ..Default::default() };
    let m = data::load(std::path::Path::new(&c.data)).unwrap();
    let (w1, w2) = init(&c);
    let xs: Vec<_> = (0..4).map(|k| encode(&c, m.train.image(k), m.train.lab[k])).collect();
    assert!(same(&c, &w1, &w2, &xs));
}

#[test]
fn order_is_python_shuffle() {
    // python3 -c "import random; v=list(range(10)); random.Random(2).shuffle(v); print(v)"
    assert_eq!(order(2, 10), vec![5, 9, 3, 4, 6, 7, 2, 8, 1, 0]);
    assert_ne!(order(3, 10), order(2, 10));
}

/// The committed genesis trains exactly darkstep's pinned program, and the fast step equals darkstep's
/// Plain::step_prog (step_spec under GEN6) on MNIST steps at d = 4096 from the genesis init.
#[test]
fn genesis_is_gen6_and_fast_step_equals_darkstep() {
    let g = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../research/dark_learning_2026_11_06/train_genesis_gen6.json")).unwrap();
    let c: Cfg = serde_json::from_str(&g).unwrap();
    assert_eq!(c.program().unwrap(), darkstep::step::Program::GEN6);
    let m = data::load(std::path::Path::new(&c.data)).unwrap();
    let c = c.with_means(&m);
    let d = c.d;
    let (mut w1, mut w2) = init(&c);
    let ord = order(c.seed_order, m.train.n);
    let mut bd = Bounds::default();
    for s in 0..2 {
        let (x, y) = encode(&c, m.train.image(ord[s]), m.train.lab[ord[s]]);
        let rows = |w: &[i64]| -> Vec<Vec<i64>> { w.chunks(d).map(|r| r.to_vec()).collect() };
        let pl = darkstep::step::Plain { w1: rows(&w1), w2: rows(&w2), x: x.clone(), y: y.clone() };
        let (e1, e2) = pl.step_prog(&darkstep::step::Program::GEN6).unwrap();
        fast_step(&c, &mut w1, &mut w2, &x, &y, &mut bd);
        assert!(rows(&w1) == e1 && rows(&w2) == e2, "step {s}");
        // control: floor instead of round in d1 (r3 = 0) is a different program
        let mut p0 = darkstep::step::Program::GEN6;
        p0.r3 = 0;
        if s == 1 {
            assert_ne!(pl.step_prog(&p0).unwrap().0, e1);
        }
    }
}
