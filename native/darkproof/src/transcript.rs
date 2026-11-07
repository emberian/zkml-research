//! cosnark.Transcript: state = H(state, *parts); chal = int(H(state, "c", i), 16) % p.
use crate::field;
use crate::h::{Hash, Py};

#[derive(Clone)]
pub struct Transcript {
    pub state: Hash,
}

impl Transcript {
    pub fn new(label: &str) -> Self {
        let mut h = Py::new();
        h.s("cosnark").s(label);
        Transcript { state: h.done() }
    }

    /// absorb(*parts): `f` writes the reprs of the parts after the state.
    pub fn absorb(&mut self, f: impl FnOnce(&mut Py)) {
        let mut h = Py::new();
        h.hx(&self.state);
        f(&mut h);
        self.state = h.done();
    }

    pub fn chal(&mut self, k: usize) -> Vec<u64> {
        (0..k).map(|i| self.chal1_i(i as u64)).collect()
    }

    /// The i-th draw of a chal(k) (a streamed chal: call with i = 0, 1, ... in order).
    #[inline]
    pub fn chal1_i(&mut self, i: u64) -> u64 {
        let mut h = Py::new();
        h.hx(&self.state).s("c").int(i);
        self.state = h.done();
        field::from_digest(&self.state)
    }

    pub fn chal1(&mut self) -> u64 {
        self.chal1_i(0)
    }

    /// cosnark.distinct_cols: T distinct column indices (a repeated draw is drawn again).
    pub fn distinct_cols(&mut self, t: usize, npts: usize) -> Vec<usize> {
        let want = t.min(npts);
        let mut out = Vec::with_capacity(want);
        let mut seen = vec![false; npts];
        while out.len() < want {
            let j = (self.chal1() % npts as u64) as usize;
            if !seen[j] {
                seen[j] = true;
                out.push(j);
            }
        }
        out
    }
}

/// A shapes-only transcript (proofwire._NullTr) is not needed: schedules take challenges as inputs.
pub fn eqv(r: &[u64]) -> Vec<u64> {
    let mut v = vec![1u64];
    for &rk in r {
        let om = field::one_minus(rk);
        let mut nv = Vec::with_capacity(v.len() * 2);
        nv.extend(v.iter().map(|&x| field::mul(x, om)));
        nv.extend(v.iter().map(|&x| field::mul(x, rk)));
        v = nv;
    }
    v
}

pub fn mle(vec: &[u64], r: &[u64]) -> u64 {
    let e = eqv(r);
    // zip semantics: the shorter length
    let n = vec.len().min(e.len());
    field::dot(&vec[..n], &e[..n])
}

/// cosnark_zk.lagc: Lagrange coefficients of nodes 0..deg at r.
pub fn lagc(deg: usize, r: u64) -> Vec<u64> {
    (0..=deg)
        .map(|i| {
            let mut num = 1u64;
            let mut den = 1u64;
            for j in 0..=deg {
                if j != i {
                    num = field::mul(num, field::sub(r, j as u64));
                    den = field::mul(den, field::from_i64(i as i64 - j as i64));
                }
            }
            field::mul(num, field::inv(den))
        })
        .collect()
}
