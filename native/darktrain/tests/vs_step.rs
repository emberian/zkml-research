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
