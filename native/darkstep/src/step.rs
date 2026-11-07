//! The step program (mpc_fork.run_step with HEMatvec and HEOuter, then the MAC check) from one custodian's seat,
//! the reference integer learner (step_spec.step), the inputs native_ref.py draws, and the result digests.
use crate::arith::*;
use crate::he::He;
use crate::party::*;
use pycompat::{PyRandom, ReprHasher};
use std::time::Instant;

pub fn sig(u: i64) -> i64 {
    (u.div_euclid(4)).clamp(-7, 7)
}

pub fn dsig(u: i64) -> i64 {
    if (-28..32).contains(&u) { 1 } else { 0 }
}

/// mpc_fork.tables(p): SIG and DSIG interpolated over 0..256 (input code u - 128).
pub fn tables(p: u64) -> Vec<Vec<u64>> {
    let s: Vec<u64> = (0..256).map(|u| from_i64(sig(u - 128), p)).collect();
    let g: Vec<u64> = (0..256).map(|u| from_i64(dsig(u - 128), p)).collect();
    vec![interpolate(&s, p), interpolate(&g, p)]
}

pub struct Plain {
    pub w1: Vec<Vec<i64>>,
    pub w2: Vec<Vec<i64>>,
    pub x: Vec<i64>,
    pub y: Vec<i64>,
}

/// native_ref.run's inputs: random.Random(d), W1, W2 in [-wmax, wmax], x, y in [-7, 7]. wmax = 7 up to d = 64; wider
/// layers need smaller weights to keep u1 = z1 >> 5 inside the table's domain [-128, 128) (step_spec asserts it).
pub fn wmax_for(d: usize) -> i64 {
    if d <= 64 { 7 } else if d <= 256 { 2 } else { 1 }
}

pub fn inputs(d: usize) -> Plain {
    let wmax = wmax_for(d);
    let mut r = PyRandom::from_u64(d as u64);
    let mat = |r: &mut PyRandom| -> Vec<Vec<i64>> { (0..d).map(|_| (0..d).map(|_| r.randint_i64(-wmax, wmax)).collect()).collect() };
    let w1 = mat(&mut r);
    let w2 = mat(&mut r);
    let x = (0..d).map(|_| r.randint_i64(-7, 7)).collect();
    let y = (0..d).map(|_| r.randint_i64(-7, 7)).collect();
    Plain { w1, w2, x, y }
}

impl Plain {
    pub fn flat_mod(&self, p: u64) -> Vec<u64> {
        let mut v = Vec::new();
        for m in [&self.w1, &self.w2] {
            for r in m.iter() {
                v.extend(r.iter().map(|&x| from_i64(x, p)));
            }
        }
        v.extend(self.x.iter().map(|&x| from_i64(x, p)));
        v.extend(self.y.iter().map(|&x| from_i64(x, p)));
        v
    }

    /// step_spec.step: the new weights, or the bound step_spec would assert on.
    pub fn step(&self) -> Result<(Vec<Vec<i64>>, Vec<Vec<i64>>), String> {
        let d = self.x.len();
        let mv = |w: &Vec<Vec<i64>>, v: &[i64]| -> Vec<i64> { (0..d).map(|i| (0..d).map(|j| w[i][j] * v[j]).sum()).collect() };
        let z1 = mv(&self.w1, &self.x);
        let u1: Vec<i64> = z1.iter().map(|z| z >> 5).collect();
        if let Some(u) = u1.iter().find(|u| !(-128..128).contains(*u)) {
            return Err(format!("step_spec domain: u1 = {u} outside [-128, 128)"));
        }
        let h: Vec<i64> = u1.iter().map(|&u| sig(u)).collect();
        let g1: Vec<i64> = u1.iter().map(|&u| dsig(u)).collect();
        let z2 = mv(&self.w2, &h);
        let e: Vec<i64> = z2.iter().zip(&self.y).map(|(z, y)| (z >> 5) - y).collect();
        let d2: Vec<i64> = e.iter().map(|v| v >> 4).collect();
        let b: Vec<i64> = (0..d).map(|j| (0..d).map(|i| self.w2[i][j] * d2[i]).sum()).collect();
        let d1: Vec<i64> = b.iter().zip(&g1).map(|(bb, g)| (bb * g) >> 8).collect();
        let w2n = (0..d).map(|i| (0..d).map(|j| self.w2[i][j] - d2[i] * h[j]).collect()).collect();
        let w1n = (0..d).map(|i| (0..d).map(|j| self.w1[i][j] - d1[i] * self.x[j]).collect()).collect();
        Ok((w1n, w2n))
    }
}

pub struct StepOut {
    pub w1n: Vec<Vec<Sh>>,
    pub w2n: Vec<Vec<Sh>>,
    pub sigma: u64,
    pub phases: Vec<(&'static str, f64)>,
    pub record: ProofRecord,
}

/// What the collaborative proof needs from one custodian's step (the proof lane's spec): its MAC key share, its
/// shares of every wire, the public transcript values in order, and the tape entries the middle constrains
/// (truncations with their range bits, lookups, the b * g1 products) in creation order. `w1n`/`w2n` are in StepOut.
#[derive(Default)]
pub struct ProofRecord {
    pub alpha_i: u64,
    pub wires: std::collections::BTreeMap<&'static str, Vec<Sh>>,
    pub public: Vec<u64>,
    pub middle_atoms: Vec<Sh>,
    pub tape_cursor: usize,
}

pub fn run_step(pt: &mut Party, he: &mut He, cs: &[u64], d: usize, tab: &[Vec<u64>]) -> Result<StepOut, String> {
    let mut phases = Vec::new();
    let mut t = Instant::now();
    let lap = |name: &'static str, t: &mut Instant, ph: &mut Vec<(&'static str, f64)>| {
        ph.push((name, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    };
    let dd = d * d;
    let sw1 = pt.input_vec(&cs[..dd]);
    let sw2 = pt.input_vec(&cs[dd..2 * dd]);
    let sx = pt.input_vec(&cs[2 * dd..2 * dd + d]);
    let sy = pt.input_vec(&cs[2 * dd + d..]);
    let m1: Vec<Vec<Sh>> = sw1.chunks(d).map(|r| r.to_vec()).collect();
    let m2: Vec<Vec<Sh>> = sw2.chunks(d).map(|r| r.to_vec()).collect();
    drop(sw1);
    drop(sw2);
    lap("input", &mut t, &mut phases);
    let z1 = he.matvec(pt, &m1, &sx, false)?;
    lap("matvec_z1", &mut t, &mut phases);
    let u1 = pt.trunc_vec(&z1, 5, 13);
    let hg = pt.lookup_vec(&u1, 128, tab, 255);
    let h: Vec<Sh> = hg.iter().map(|v| v[0]).collect();
    let g1: Vec<Sh> = hg.iter().map(|v| v[1]).collect();
    lap("trunc_lookup", &mut t, &mut phases);
    let z2 = he.matvec(pt, &m2, &h, false)?;
    lap("matvec_z2", &mut t, &mut phases);
    let t2 = pt.trunc_vec(&z2, 5, 13);
    let e: Vec<Sh> = t2.iter().zip(&sy).map(|(a, b)| pt.sub(*a, *b)).collect();
    let d2 = pt.trunc_vec(&e, 4, 8);
    lap("trunc_e_d2", &mut t, &mut phases);
    let b = he.matvec(pt, &m2, &d2, true)?;
    lap("matvec_b", &mut t, &mut phases);
    pt.middle_mul = true;
    let bg = pt.mul_vec(&b, &g1);
    pt.middle_mul = false;
    let d1 = pt.trunc_vec(&bg, 8, 13);
    lap("mul_trunc_d1", &mut t, &mut phases);
    let g2 = he.outer(pt, &d2, &h)?;
    let w2n: Vec<Vec<Sh>> = (0..d).map(|i| (0..d).map(|j| pt.sub(m2[i][j], g2[i][j])).collect()).collect();
    let mut record = ProofRecord { alpha_i: pt.alpha(), ..Default::default() };
    for (k, v) in [("x", &sx), ("y", &sy), ("z1", &z1), ("h", &h), ("z2", &z2), ("d2", &d2), ("b", &b), ("g1", &g1), ("bg", &bg), ("d1", &d1)] {
        record.wires.insert(k, v.clone());
    }
    drop(g2);
    lap("outer_G2", &mut t, &mut phases);
    let g1o = he.outer(pt, &d1, &sx)?;
    let w1n: Vec<Vec<Sh>> = (0..d).map(|i| (0..d).map(|j| pt.sub(m1[i][j], g1o[i][j])).collect()).collect();
    drop(g1o);
    lap("outer_G1", &mut t, &mut phases);
    let sigma = pt.mac_check("he")?;
    lap("mac_check", &mut t, &mut phases);
    record.wires.insert("W1", m1.into_iter().flatten().collect());
    record.wires.insert("W2", m2.into_iter().flatten().collect());
    record.public = pt.tr.v.clone();
    record.middle_atoms = pt
        .atom_log
        .iter()
        .flat_map(|r| r.clone().map(|k| Sh { s: pt.tape.sh[k], m: pt.tape.mac[k] }))
        .collect();
    record.tape_cursor = pt.cur;
    Ok(StepOut { w1n, w2n, sigma, phases, record })
}

/// sha256(repr((W1n_i, W2n_i))) with entries (share, mac).
pub fn party_digest(w1n: &[Vec<Sh>], w2n: &[Vec<Sh>]) -> String {
    let mut h = ReprHasher::new();
    h.raw(b"(");
    for (z, m) in [w1n, w2n].iter().enumerate() {
        if z > 0 {
            h.sep();
        }
        h.raw(b"[");
        for (k, row) in m.iter().enumerate() {
            if k > 0 {
                h.sep();
            }
            h.raw(b"[");
            for (c, x) in row.iter().enumerate() {
                if c > 0 {
                    h.sep();
                }
                h.raw(b"(");
                h.u64(x.s);
                h.sep();
                h.u64(x.m);
                h.raw(b")");
            }
            h.raw(b"]");
        }
        h.raw(b"]");
    }
    h.raw(b")");
    h.finish_hex()
}

pub fn transcript_digest(tr: &Transcript) -> String {
    let mut h = ReprHasher::new();
    tr.repr_into(&mut h);
    h.finish_hex()
}
