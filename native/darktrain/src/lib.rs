//! Plaintext training of the dark-learning integer model (step_spec.step under a Program) on MNIST.
//!
//! The fast trainer computes exactly the scalar step (`reference_step`, which mirrors step_spec.step and
//! darkstep::step); tests/vs_step.rs checks equality on random and MNIST cases. Every step also records the MPC's
//! preconditions (|v| < 2^K at each truncation, u1 inside the table's domain), because a run that breaks one is not
//! a run the custodians can execute.
pub mod data;

use pycompat::PyRandom;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

pub fn sig(u: i64) -> i64 {
    u.div_euclid(4).clamp(-7, 7)
}
pub fn dsig(u: i64) -> i64 {
    if (-28..32).contains(&u) { 1 } else { 0 }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct Cfg {
    pub d: usize,
    /// active hidden units (rows of W1 / columns of W2 drawn at init; the rest are zero and stay zero)
    pub hid: usize,
    /// output rows per class (active outputs = 10 * reps; row i is class i % 10)
    pub reps: usize,
    /// truncation shifts: z1 >> s1a, z2 >> s1b (one S1 in the harness), e >> s2, bg >> s3
    pub s1a: u32,
    pub s1b: u32,
    pub s2: u32,
    pub s3: u32,
    /// truncation input bounds |v| < 2^K (the MPC's precondition)
    pub k1: u32,
    pub k2: u32,
    pub k3: u32,
    /// table domain [t_lo, t_lo + 256)
    pub t_lo: i64,
    /// PROGRAM option: add 2^(s3-1) to bg before its truncation (round half up instead of floor)
    pub rnd3: bool,
    /// ENCODER option: the owner subtracts 2^(s2-1) from active targets, so e >> s2 rounds instead of floors
    pub rnd2: bool,
    pub ypos: i64,
    pub yneg: i64,
    /// "pos": x = round(7 p / 255) in [0, 7]; "ctr": round(14 p / 255) - 7 in [-7, 7]
    pub xenc: String,
    /// copies of the 784 pixels laid side by side
    pub tile: usize,
    /// one constant input coordinate x = 7 after the pixels
    pub bias: bool,
    /// init ranges: W1, W2 entries uniform in [-a, a] (PyRandom randint, row-major, W1 then W2; a = 0: zeros)
    pub a1: i64,
    pub a2: i64,
    pub seed_init: u64,
    pub seed_order: u64,
    pub steps: usize,
    pub evals: Vec<usize>,
    /// test examples evaluated (the first eval_n of the official test split)
    pub eval_n: usize,
    pub data: String,
    /// float baseline only: learning-rate multiplier on the matched rates (both layers), and on layer 1 alone
    pub lrmul: f64,
    pub lr1mul: f64,
    /// float baseline only: > 0 replaces the squared error by softmax cross-entropy on logits o / ce_tau
    /// (error vector ypos * (softmax - onehot), so the rates stay comparable); reps must be 1
    pub ce_tau: f64,
    /// per-pixel training-split means, round half up (filled by `with_means`, not part of the JSON)
    #[serde(skip)]
    pub mu: Vec<u8>,
}

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            d: 4096,
            hid: 4096,
            reps: 1,
            s1a: 11,
            s1b: 11,
            s2: 4,
            s3: 14,
            k1: 19,
            k2: 8,
            k3: 19,
            t_lo: -128,
            rnd3: false,
            rnd2: false,
            ypos: 32,
            yneg: 0,
            xenc: "pos".into(),
            tile: 1,
            bias: false,
            a1: 64,
            a2: 0,
            seed_init: 1,
            seed_order: 2,
            steps: 1000,
            evals: vec![0, 25, 50, 100, 200, 300, 500, 750, 1000, 1500, 2000, 3000, 4000],
            eval_n: 10000,
            data: concat!(env!("CARGO_MANIFEST_DIR"), "/../../research/dark_learning_2026_11_06/data/mnist").into(),
            lrmul: 1.0,
            lr1mul: 1.0,
            ce_tau: 0.0,
            mu: vec![],
        }
    }
}

impl Cfg {
    /// The encoder's statistics from the training split: mu_k = floor((sum_k + n / 2) / n).
    pub fn with_means(mut self, m: &data::Mnist) -> Self {
        let n = m.train.n as u64;
        self.mu = (0..784).map(|k| ((0..m.train.n).map(|t| m.train.img[t * 784 + k] as u64).sum::<u64>() + n / 2).div_euclid(n) as u8).collect();
        self
    }
    pub fn nin(&self) -> usize {
        self.tile * 784 + self.bias as usize
    }
    pub fn nout(&self) -> usize {
        10 * self.reps
    }
    pub fn validate(&self) -> Result<(), String> {
        if self.nin() > self.d || self.nout() > self.d || self.hid > self.d {
            return Err("layout does not fit in d".into());
        }
        Ok(())
    }
}

/// The data owner's encoder: one MNIST image and label -> (x, y), both of length d.
pub fn encode(c: &Cfg, img: &[u8], label: u8) -> (Vec<i64>, Vec<i64>) {
    let mut x = vec![0i64; c.d];
    for t in 0..c.tile {
        for (k, &p) in img.iter().enumerate() {
            let p = p as i64;
            x[t * 784 + k] = match c.xenc.as_str() {
                "pos" => (7 * p + 127) / 255,
                "ctr" => (14 * p + 127) / 255 - 7,
                // mean-centred: round(m (p - mu_k) / 255) clamped to [-7, 7], mu_k the training split's pixel mean
                "mc" | "mc2" => {
                    let mm = if c.xenc == "mc" { 7 } else { 14 };
                    (2 * mm * (p - c.mu[k] as i64) + 255).div_euclid(510).clamp(-7, 7)
                }
                e => panic!("xenc {e}"),
            };
        }
    }
    if c.bias {
        x[c.tile * 784] = 7;
    }
    let off = if c.rnd2 && c.s2 > 0 { 1i64 << (c.s2 - 1) } else { 0 };
    let mut y = vec![0i64; c.d];
    for (i, yi) in y.iter_mut().enumerate().take(c.nout()) {
        *yi = if i % 10 == label as usize { c.ypos } else { c.yneg } - off;
    }
    (x, y)
}

/// Seeded init (Python: r = random.Random(seed_init); W1[j][k] = r.randint(-a1, a1) for j < hid, k < nin, row-major;
/// then W2[i][j] = r.randint(-a2, a2) for i < nout, j < hid; every other entry 0; a = 0 draws nothing).
pub fn init(c: &Cfg) -> (Vec<i64>, Vec<i64>) {
    let d = c.d;
    let mut r = PyRandom::from_u64(c.seed_init);
    let mut w1 = vec![0i64; d * d];
    let mut w2 = vec![0i64; d * d];
    if c.a1 > 0 {
        for j in 0..c.hid {
            for k in 0..c.nin() {
                w1[j * d + k] = r.randint_i64(-c.a1, c.a1);
            }
        }
    }
    if c.a2 > 0 {
        for i in 0..c.nout() {
            for j in 0..c.hid {
                w2[i * d + j] = r.randint_i64(-c.a2, c.a2);
            }
        }
    }
    (w1, w2)
}

/// Python random.Random(seed).shuffle(list(range(n))).
pub fn order(seed: u64, n: usize) -> Vec<usize> {
    let mut r = PyRandom::from_u64(seed);
    let mut v: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = r.randbelow_u64(i as u64 + 1) as usize;
        v.swap(i, j);
    }
    v
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Bounds {
    pub max_z1: i64,
    pub max_z2: i64,
    pub max_e: i64,
    pub max_bg: i64,
    pub max_w1: i64,
    pub max_w2: i64,
    /// violations of the MPC preconditions: u1 outside the table, |z1|, |z2| >= 2^k1, |e| >= 2^k2, |bg| >= 2^k3
    pub v_u1: u64,
    pub v_z1: u64,
    pub v_z2: u64,
    pub v_e: u64,
    pub v_bg: u64,
}

impl Bounds {
    pub fn violations(&self) -> u64 {
        self.v_u1 + self.v_z1 + self.v_z2 + self.v_e + self.v_bg
    }
}

pub struct Trace {
    pub z1: Vec<i64>,
    pub u1: Vec<i64>,
    pub h: Vec<i64>,
    pub g1: Vec<i64>,
    pub z2: Vec<i64>,
    pub e: Vec<i64>,
    pub d2: Vec<i64>,
    pub b: Vec<i64>,
    pub d1: Vec<i64>,
}

fn rnd3(c: &Cfg) -> i64 {
    if c.rnd3 && c.s3 > 0 { 1i64 << (c.s3 - 1) } else { 0 }
}

/// The scalar step, written exactly as step_spec.step (dense, no shortcuts). W updated in place.
pub fn reference_step(c: &Cfg, w1: &mut [i64], w2: &mut [i64], x: &[i64], y: &[i64]) -> Trace {
    let d = c.d;
    let z1: Vec<i64> = (0..d).map(|i| (0..d).map(|j| w1[i * d + j] * x[j]).sum()).collect();
    let u1: Vec<i64> = z1.iter().map(|z| z >> c.s1a).collect();
    let h: Vec<i64> = u1.iter().map(|&u| sig(u)).collect();
    let g1: Vec<i64> = u1.iter().map(|&u| dsig(u)).collect();
    let z2: Vec<i64> = (0..d).map(|i| (0..d).map(|j| w2[i * d + j] * h[j]).sum()).collect();
    let e: Vec<i64> = z2.iter().zip(y).map(|(z, yy)| (z >> c.s1b) - yy).collect();
    let d2: Vec<i64> = e.iter().map(|v| v >> c.s2).collect();
    let b: Vec<i64> = (0..d).map(|j| (0..d).map(|i| w2[i * d + j] * d2[i]).sum()).collect();
    let r3 = rnd3(c);
    let d1: Vec<i64> = b.iter().zip(&g1).map(|(bb, g)| (bb * g + r3) >> c.s3).collect();
    for i in 0..d {
        for j in 0..d {
            w2[i * d + j] -= d2[i] * h[j];
            w1[i * d + j] -= d1[i] * x[j];
        }
    }
    Trace { z1, u1, h, g1, z2, e, d2, b, d1 }
}

/// The same step, fast: sparse in x and in d2 / d1 (zero entries contribute exactly zero), rows in parallel.
pub fn fast_step(c: &Cfg, w1: &mut [i64], w2: &mut [i64], x: &[i64], y: &[i64], bd: &mut Bounds) -> Trace {
    let d = c.d;
    let nz: Vec<(usize, i64)> = x.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v)).collect();
    let z1: Vec<i64> = w1.par_chunks(d).map(|r| nz.iter().map(|&(k, v)| r[k] * v).sum()).collect();
    let u1: Vec<i64> = z1.iter().map(|z| z >> c.s1a).collect();
    let h: Vec<i64> = u1.iter().map(|&u| sig(u)).collect();
    let g1: Vec<i64> = u1.iter().map(|&u| dsig(u)).collect();
    let hz: Vec<(usize, i64)> = h.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v)).collect();
    let z2: Vec<i64> = w2.par_chunks(d).map(|r| hz.iter().map(|&(k, v)| r[k] * v).sum()).collect();
    let e: Vec<i64> = z2.iter().zip(y).map(|(z, yy)| (z >> c.s1b) - yy).collect();
    let d2: Vec<i64> = e.iter().map(|v| v >> c.s2).collect();
    let dz: Vec<(usize, i64)> = d2.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v)).collect();
    let mut b = vec![0i64; d];
    for &(i, v) in &dz {
        let r = &w2[i * d..(i + 1) * d];
        b.par_iter_mut().zip(r.par_iter()).for_each(|(bb, &w)| *bb += w * v);
    }
    let r3 = rnd3(c);
    let d1: Vec<i64> = b.iter().zip(&g1).map(|(bb, g)| (bb * g + r3) >> c.s3).collect();
    // bounds, before the update (they are the step's openings)
    let (lim1, lim2, lim3) = (1i64 << c.k1, 1i64 << c.k2, 1i64 << c.k3);
    for j in 0..d {
        let (a, u) = (z1[j].abs(), u1[j]);
        bd.max_z1 = bd.max_z1.max(a);
        bd.v_z1 += (a >= lim1) as u64;
        bd.v_u1 += !(c.t_lo..c.t_lo + 256).contains(&u) as u64;
        let a2 = z2[j].abs();
        bd.max_z2 = bd.max_z2.max(a2);
        bd.v_z2 += (a2 >= lim1) as u64;
        let ae = e[j].abs();
        bd.max_e = bd.max_e.max(ae);
        bd.v_e += (ae >= lim2) as u64;
        let ab = (b[j] * g1[j] + r3).abs();
        bd.max_bg = bd.max_bg.max(ab);
        bd.v_bg += (ab >= lim3) as u64;
    }
    w2.par_chunks_mut(d).zip(d2.par_iter()).filter(|(_, &v)| v != 0).for_each(|(r, &v)| {
        for &(k, hv) in &hz {
            r[k] -= v * hv;
        }
    });
    w1.par_chunks_mut(d).zip(d1.par_iter()).filter(|(_, &v)| v != 0).for_each(|(r, &v)| {
        for &(k, xv) in &nz {
            r[k] -= v * xv;
        }
    });
    Trace { z1, u1, h, g1, z2, e, d2, b, d1 }
}

/// Class scores from a forward pass: per class, the sum over its rows of o = z2 >> s1b (and of z2 itself).
pub fn scores(c: &Cfg, z2: &[i64]) -> ([i64; 10], [i64; 10]) {
    let mut so = [0i64; 10];
    let mut sz = [0i64; 10];
    for i in 0..c.nout() {
        so[i % 10] += z2[i] >> c.s1b;
        sz[i % 10] += z2[i];
    }
    (so, sz)
}

/// argmax with the custodians' tie rule: the true class must be strictly above every other score.
pub fn correct(s: &[i64; 10], label: u8) -> bool {
    let l = label as usize;
    (0..10).all(|k| k == l || s[l] > s[k])
}

pub fn argmax(s: &[i64; 10]) -> usize {
    let mut b = 0;
    for k in 1..10 {
        if s[k] > s[b] {
            b = k;
        }
    }
    b
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Eval {
    pub n: usize,
    /// strict: true class strictly above all others, on o = z2 >> s1b (what the custodians compute)
    pub acc_o: f64,
    /// strict, on z2 (finer)
    pub acc_z2: f64,
    /// argmax (lowest index wins ties) on o
    pub acc_o_argmax: f64,
    pub ties_o: f64,
    pub bounds: Bounds,
}

/// The forward half of the step on the first n test examples (the custodians' evaluation, in plaintext).
pub fn evaluate(c: &Cfg, w1: &[i64], w2: &[i64], m: &data::Split, n: usize) -> Eval {
    let d = c.d;
    let lim1 = 1i64 << c.k1;
    let res: Vec<(bool, bool, bool, bool, Bounds)> = (0..n)
        .into_par_iter()
        .map(|t| {
            let (x, _) = encode(c, m.image(t), m.lab[t]);
            let nz: Vec<(usize, i64)> = x.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v)).collect();
            let mut bd = Bounds::default();
            let mut h = vec![0i64; d];
            for j in 0..d {
                let r = &w1[j * d..(j + 1) * d];
                let z: i64 = nz.iter().map(|&(k, v)| r[k] * v).sum();
                let u = z >> c.s1a;
                bd.max_z1 = bd.max_z1.max(z.abs());
                bd.v_z1 += (z.abs() >= lim1) as u64;
                bd.v_u1 += !(c.t_lo..c.t_lo + 256).contains(&u) as u64;
                h[j] = sig(u);
            }
            let mut z2 = vec![0i64; d];
            for i in 0..c.nout() {
                let r = &w2[i * d..(i + 1) * d];
                z2[i] = r.iter().zip(&h).map(|(a, b)| a * b).sum();
                bd.max_z2 = bd.max_z2.max(z2[i].abs());
                bd.v_z2 += (z2[i].abs() >= lim1) as u64;
            }
            let (so, sz) = scores(c, &z2);
            let l = m.lab[t];
            let am = argmax(&so);
            let tie = (0..10).filter(|&k| so[k] == so[am]).count() > 1;
            (correct(&so, l), correct(&sz, l), am == l as usize, tie, bd)
        })
        .collect();
    let mut ev = Eval { n, ..Default::default() };
    for (a, b, cc, t, bd) in &res {
        ev.acc_o += *a as u8 as f64;
        ev.acc_z2 += *b as u8 as f64;
        ev.acc_o_argmax += *cc as u8 as f64;
        ev.ties_o += *t as u8 as f64;
        let e = &mut ev.bounds;
        e.max_z1 = e.max_z1.max(bd.max_z1);
        e.max_z2 = e.max_z2.max(bd.max_z2);
        e.v_u1 += bd.v_u1;
        e.v_z1 += bd.v_z1;
        e.v_z2 += bd.v_z2;
    }
    for v in [&mut ev.acc_o, &mut ev.acc_z2, &mut ev.acc_o_argmax, &mut ev.ties_o] {
        *v /= n as f64;
    }
    ev
}

pub fn maxabs(w: &[i64]) -> i64 {
    w.par_iter().map(|v| v.abs()).max().unwrap_or(0)
}

#[derive(Serialize)]
pub struct Point {
    pub step: usize,
    pub eval: Eval,
    /// online accuracy (strict, on o) of the training examples since the previous point, before their update
    pub online: f64,
    pub train_bounds: Bounds,
    pub secs: f64,
}

/// Train under cfg, evaluating at cfg.evals; returns the curve and the final weights.
pub fn train(c: &Cfg, m: &data::Mnist, mut on_point: impl FnMut(&Point)) -> (Vec<Point>, Vec<i64>, Vec<i64>) {
    let t0 = std::time::Instant::now();
    let (mut w1, mut w2) = init(c);
    let ord = order(c.seed_order, m.train.n);
    let mut pts = Vec::new();
    let mut bd = Bounds::default();
    let (mut ok, mut seen) = (0usize, 0usize);
    for s in 0..=c.steps {
        if c.evals.contains(&s) || s == c.steps {
            let mut ev = evaluate(c, &w1, &w2, &m.test, c.eval_n);
            ev.bounds.max_w1 = maxabs(&w1);
            ev.bounds.max_w2 = maxabs(&w2);
            let p = Point { step: s, eval: ev, online: if seen > 0 { ok as f64 / seen as f64 } else { 0.0 }, train_bounds: bd.clone(), secs: t0.elapsed().as_secs_f64() };
            on_point(&p);
            pts.push(p);
            ok = 0;
            seen = 0;
        }
        if s == c.steps {
            break;
        }
        let k = ord[s % m.train.n];
        let (x, y) = encode(c, m.train.image(k), m.train.lab[k]);
        let tr = fast_step(c, &mut w1, &mut w2, &x, &y, &mut bd);
        let (so, _) = scores(c, &tr.z2);
        ok += correct(&so, m.train.lab[k]) as usize;
        seen += 1;
    }
    (pts, w1, w2)
}

/// The float baseline: the same architecture, data order and init, in f64. u = v1 x (v1 = W1 / 2^s1a),
/// h = clamp(u / 4, -7, 7), g = [-28 <= u < 32], o = v2 h (v2 = W2 / 2^s1b), e = o - y,
/// v2 -= lr2 e h^T, v1 -= lr1 ((v2^T e) g / 4) x^T, with the integer program's matched rates times lrmul:
/// lr2 = 2^-(s1b + s2), lr1 = 4 * 2^(s1b - s1a - s2 - s3).
pub fn train_float(c: &Cfg, m: &data::Mnist, mut on_point: impl FnMut(usize, f64, f64)) -> Vec<(usize, f64)> {
    let d = c.d;
    let (w1i, w2i) = init(c);
    let (f1, f2) = (2f64.powi(-(c.s1a as i32)), 2f64.powi(-(c.s1b as i32)));
    let mut v1: Vec<f64> = w1i.iter().map(|&w| w as f64 * f1).collect();
    let mut v2: Vec<f64> = w2i.iter().map(|&w| w as f64 * f2).collect();
    let lr2 = c.lrmul * 2f64.powi(-((c.s1b + c.s2) as i32));
    let lr1 = c.lrmul * c.lr1mul * 4.0 * 2f64.powi(c.s1b as i32 - c.s1a as i32 - c.s2 as i32 - c.s3 as i32);
    let ord = order(c.seed_order, m.train.n);
    let no = c.nout();
    let fwd = |v1: &[f64], v2: &[f64], x: &[i64]| -> (Vec<f64>, Vec<f64>, Vec<f64>) {
        let nz: Vec<(usize, f64)> = x.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v as f64)).collect();
        let u: Vec<f64> = v1.par_chunks(d).map(|r| nz.iter().map(|&(k, v)| r[k] * v).sum()).collect();
        let h: Vec<f64> = u.iter().map(|&u| (u / 4.0).clamp(-7.0, 7.0)).collect();
        let o: Vec<f64> = v2[..no * d].par_chunks(d).map(|r| r.iter().zip(&h).map(|(a, b)| a * b).sum()).collect();
        (u, h, o)
    };
    let acc = |v1: &[f64], v2: &[f64]| -> f64 {
        let ok: usize = (0..c.eval_n)
            .into_par_iter()
            .map(|t| {
                let (x, _) = encode(c, m.test.image(t), m.test.lab[t]);
                let nz: Vec<(usize, f64)> = x.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v as f64)).collect();
                let h: Vec<f64> = v1.chunks(d).map(|r| (nz.iter().map(|&(k, v)| r[k] * v).sum::<f64>() / 4.0).clamp(-7.0, 7.0)).collect();
                let mut s = [0f64; 10];
                for i in 0..no {
                    s[i % 10] += v2[i * d..(i + 1) * d].iter().zip(&h).map(|(a, b)| a * b).sum::<f64>();
                }
                let l = m.test.lab[t] as usize;
                (0..10).all(|k| k == l || s[l] > s[k]) as usize
            })
            .sum();
        ok as f64 / c.eval_n as f64
    };
    let mut out = Vec::new();
    let t0 = std::time::Instant::now();
    for s in 0..=c.steps {
        if c.evals.contains(&s) || s == c.steps {
            let a = acc(&v1, &v2);
            on_point(s, a, t0.elapsed().as_secs_f64());
            out.push((s, a));
        }
        if s == c.steps {
            break;
        }
        let k = ord[s % m.train.n];
        let mut cc = c.clone();
        cc.rnd2 = false;
        let (x, y) = encode(&cc, m.train.image(k), m.train.lab[k]);
        let (u, h, o) = fwd(&v1, &v2, &x);
        let e: Vec<f64> = if c.ce_tau > 0.0 {
            let mx = o.iter().cloned().fold(f64::MIN, f64::max);
            let ex: Vec<f64> = o.iter().map(|v| ((v - mx) / c.ce_tau).exp()).collect();
            let z: f64 = ex.iter().sum();
            (0..no).map(|i| c.ypos as f64 * (ex[i] / z - (i % 10 == m.train.lab[k] as usize) as u8 as f64)).collect()
        } else {
            (0..no).map(|i| o[i] - y[i] as f64).collect()
        };
        let mut b = vec![0f64; d];
        for i in 0..no {
            let r = &v2[i * d..(i + 1) * d];
            b.par_iter_mut().zip(r.par_iter()).for_each(|(bb, &w)| *bb += w * e[i]);
        }
        v2[..no * d].par_chunks_mut(d).enumerate().for_each(|(i, r)| {
            for j in 0..d {
                r[j] -= lr2 * e[i] * h[j];
            }
        });
        let nz: Vec<(usize, f64)> = x.iter().enumerate().filter(|(_, &v)| v != 0).map(|(k, &v)| (k, v as f64)).collect();
        v1.par_chunks_mut(d).enumerate().for_each(|(j, r)| {
            let g = if (-28.0..32.0).contains(&u[j]) { 1.0 } else { 0.0 };
            let dj = lr1 * b[j] * g / 4.0;
            if dj != 0.0 {
                for &(k, xv) in &nz {
                    r[k] -= dj * xv;
                }
            }
        });
    }
    out
}

/// sha256(repr((W1, W2))) of the d x d weights as Python lists of lists (train_owner.py's digest).
pub fn weights_digest(d: usize, w1: &[i64], w2: &[i64]) -> String {
    let mut h = pycompat::ReprHasher::new();
    h.raw(b"(");
    for (z, w) in [w1, w2].iter().enumerate() {
        if z > 0 {
            h.sep();
        }
        h.raw(b"[");
        for i in 0..d {
            if i > 0 {
                h.sep();
            }
            h.raw(b"[");
            for j in 0..d {
                if j > 0 {
                    h.sep();
                }
                h.i64(w[i * d + j]);
            }
            h.raw(b"]");
        }
        h.raw(b"]");
    }
    h.raw(b")");
    h.finish_hex()
}
