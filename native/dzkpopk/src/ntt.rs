//! Radix-2 NTT over F_P (natural order in and out: out[i] = a(w^i)), the Reed-Solomon code of zkpopk_ligero.Code,
//! and negacyclic products in F_P[X]/(X^N + 1).

use crate::field::{root_of, Fe, ONE, SHIFT};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

pub struct Plan {
    pub n: usize,
    /// tw[i] = w^i, i < n/2
    tw: Vec<Fe>,
    /// 1/n (for the inverse plan only; ONE otherwise)
    scale: Fe,
}

fn plans() -> &'static Mutex<HashMap<(usize, bool), Arc<Plan>>> {
    static C: OnceLock<Mutex<HashMap<(usize, bool), Arc<Plan>>>> = OnceLock::new();
    C.get_or_init(|| Mutex::new(HashMap::new()))
}

/// The plan for size n with root root_of(n) (inverse = false) or its inverse with the 1/n scale (inverse = true).
pub fn plan(n: usize, inverse: bool) -> Arc<Plan> {
    if let Some(p) = plans().lock().unwrap().get(&(n, inverse)) {
        return p.clone();
    }
    let mut w = root_of(n);
    if inverse {
        w = w.inv();
    }
    let mut tw = Vec::with_capacity((n / 2).max(1));
    let mut x = ONE;
    for _ in 0..(n / 2).max(1) {
        tw.push(x);
        x = x.mul(w);
    }
    let scale = if inverse { Fe::from_u64(n as u64).inv() } else { ONE };
    let p = Arc::new(Plan { n, tw, scale });
    plans().lock().unwrap().insert((n, inverse), p.clone());
    p
}

impl Plan {
    /// In place: a <- [a(w^i)] (times 1/n for an inverse plan).
    pub fn run(&self, a: &mut [Fe]) {
        let n = self.n;
        assert_eq!(a.len(), n);
        if n == 1 {
            a[0] = a[0].mul(self.scale);
            return;
        }
        let lg = n.trailing_zeros();
        for i in 0..n {
            let j = i.reverse_bits() >> (usize::BITS - lg);
            if i < j {
                a.swap(i, j);
            }
        }
        let mut m = 2;
        while m <= n {
            let h = m / 2;
            let step = n / m;
            for s in (0..n).step_by(m) {
                for i in 0..h {
                    let w = self.tw[i * step];
                    let x = a[s + i];
                    let y = a[s + h + i].mul(w);
                    a[s + i] = x.add(y);
                    a[s + h + i] = x.sub(y);
                }
            }
            m *= 2;
        }
        if self.scale != ONE {
            for x in a.iter_mut() {
                *x = x.mul(self.scale);
            }
        }
    }
}

/// zkpopk_ligero.Code: messages of length k on H = <w_k>; codewords on the coset D = SHIFT * <w_D>,
/// |D| = nD the least power of two >= 4 (k + th).
pub struct Code {
    pub k: usize,
    pub th: usize,
    pub n_d: usize,
    pub lg_d: usize,
    pk_inv: Arc<Plan>,
    pd: Arc<Plan>,
    pd_inv: Arc<Plan>,
    shpow: Vec<Fe>,
    ishpow: Vec<Fe>,
    /// pts[j] = SHIFT * w_D^j
    pub pts: Vec<Fe>,
    pub wk: Fe,
}

pub fn n_d_for(k: usize, th: usize) -> usize {
    let x = 4 * (k + th) - 1;
    1usize << (usize::BITS - x.leading_zeros())
}

impl Code {
    pub fn new(k: usize, th: usize) -> Code {
        assert!(k.is_power_of_two() && th >= 1);
        let n_d = n_d_for(k, th);
        let lg_d = n_d.trailing_zeros() as usize;
        let sh = Fe::from_u64(SHIFT);
        let ish = sh.inv();
        let mut shpow = vec![ONE; n_d];
        let mut ishpow = vec![ONE; n_d];
        for i in 1..n_d {
            shpow[i] = shpow[i - 1].mul(sh);
            ishpow[i] = ishpow[i - 1].mul(ish);
        }
        let wd = root_of(n_d);
        let mut pts = vec![sh; n_d];
        for i in 1..n_d {
            pts[i] = pts[i - 1].mul(wd);
        }
        Code {
            k,
            th,
            n_d,
            lg_d,
            pk_inv: plan(k, true),
            pd: plan(n_d, false),
            pd_inv: plan(n_d, true),
            shpow,
            ishpow,
            pts,
            wk: root_of(k),
        }
    }

    pub fn interp(&self, msg: &[Fe]) -> Vec<Fe> {
        let mut c = msg.to_vec();
        self.pk_inv.run(&mut c);
        c
    }

    pub fn eval_d(&self, coeffs: &[Fe]) -> Vec<Fe> {
        assert!(coeffs.len() <= self.n_d);
        let mut c = vec![Fe::ZERO; self.n_d];
        for (i, x) in coeffs.iter().enumerate() {
            c[i] = x.mul(self.shpow[i]);
        }
        self.pd.run(&mut c);
        c
    }

    pub fn coeffs_d(&self, evals: &[Fe]) -> Vec<Fe> {
        let mut c = evals.to_vec();
        self.pd_inv.run(&mut c);
        for (x, s) in c.iter_mut().zip(&self.ishpow) {
            *x = x.mul(*s);
        }
        c
    }

    /// interp(msg) + (X^k - 1) * rand(X), deg rand < th; draws th field elements from `rng` in order.
    pub fn row_poly(&self, msg: &[Fe], rng: &mut dyn crate::rng::Hiding) -> Vec<Fe> {
        let mut c = self.interp(msg);
        c.resize(self.k + self.th, Fe::ZERO);
        for l in 0..self.th {
            let r = rng.fe();
            c[l] = c[l].sub(r);
            c[self.k + l] = c[self.k + l].add(r);
        }
        c
    }
}

/// Products in F_P[X]/(X^N + 1) through the 2N-th root psi.
pub struct Nega {
    pub n: usize,
    psi: Vec<Fe>,
    ipsi: Vec<Fe>,
    fwd: Arc<Plan>,
    inv: Arc<Plan>,
}

impl Nega {
    pub fn new(n: usize) -> Nega {
        let psi1 = root_of(2 * n);
        let ipsi1 = psi1.inv();
        let mut psi = vec![ONE; n];
        let mut ipsi = vec![ONE; n];
        for i in 1..n {
            psi[i] = psi[i - 1].mul(psi1);
            ipsi[i] = ipsi[i - 1].mul(ipsi1);
        }
        Nega { n, psi, ipsi, fwd: plan(n, false), inv: plan(n, true) }
    }

    /// Forward transform of a coefficient vector.
    pub fn fwd(&self, a: &[Fe]) -> Vec<Fe> {
        let mut v: Vec<Fe> = a.iter().zip(&self.psi).map(|(x, p)| x.mul(*p)).collect();
        self.fwd.run(&mut v);
        v
    }

    pub fn inv(&self, mut v: Vec<Fe>) -> Vec<Fe> {
        self.inv.run(&mut v);
        for (x, p) in v.iter_mut().zip(&self.ipsi) {
            *x = x.mul(*p);
        }
        v
    }

    pub fn mul(&self, a: &[Fe], b: &[Fe]) -> Vec<Fe> {
        let fa = self.fwd(a);
        let fb = self.fwd(b);
        self.inv(fa.iter().zip(&fb).map(|(x, y)| x.mul(*y)).collect())
    }
}
