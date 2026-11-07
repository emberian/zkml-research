//! BFV as bfv_ref.BFV / he_matvec.OwnKey, over RNS: every draw from the key's random.Random in the reference order,
//! so keys, ciphertexts and decryptions are bit-identical to the harness.
use crate::arith::*;
use crate::rns::Rns;
use pycompat::PyRandom;
use std::sync::Arc;

/// A ciphertext in coefficient form: residues, limb-major (k * N + i).
#[derive(Clone)]
pub struct Ct {
    pub c0: Vec<u64>,
    pub c1: Vec<u64>,
}

/// The public half of a custodian's key, in NTT form (what other custodians need for Enc_pk_j(0)).
#[derive(Clone)]
pub struct PubKey {
    pub pk0_ntt: Vec<u64>,
    pub pk1_ntt: Vec<u64>,
}

pub struct OwnKey {
    pub rns: Arc<Rns>,
    pub rng: PyRandom,
    pub s: Vec<i64>,
    s_ntt: Vec<u64>,
    pub pk: PubKey,
}

/// bfv.uniform(): N draws randrange(Q), as residues.
fn uniform(rns: &Rns, rng: &mut PyRandom) -> Vec<u64> {
    let mut ql = [0u64; 5];
    for (k, x) in rns.q_big.to_u64_digits().into_iter().enumerate() {
        ql[k] = x;
    }
    let n = rns.n;
    let mut out = rns.zero();
    for i in 0..n {
        let v = rng.randbelow_arr::<5>(&ql);
        for k in 0..rns.l() {
            out[k * n + i] = rns.md[k].limbs5(&v);
        }
    }
    out
}

fn small_error(n: usize, rng: &mut PyRandom) -> Vec<i64> {
    (0..n).map(|_| rng.randint_i64(-8, 8)).collect()
}

impl OwnKey {
    /// he_matvec.OwnKey(N, Q, t, seed).
    pub fn new(rns: Arc<Rns>, seed: u64) -> Self {
        let n = rns.n;
        let mut rng = PyRandom::from_u64(seed);
        let s: Vec<i64> = (0..n).map(|_| rng.ternary()).collect();
        let mut s_ntt = rns.from_signed(&s);
        rns.fwd(&mut s_ntt);
        let a = uniform(&rns, &mut rng);
        let e = small_error(n, &mut rng);
        let mut a_ntt = a.clone();
        rns.fwd(&mut a_ntt);
        let mut as_ = rns.mul_pw(&a_ntt, &s_ntt);
        rns.inv(&mut as_);
        let mut pk0 = rns.zero();
        for (k, &q) in rns.qs.iter().enumerate() {
            for i in 0..n {
                pk0[k * n + i] = submod(0, addmod(as_[k * n + i], from_i64(e[i], q), q), q);
            }
        }
        rns.fwd(&mut pk0);
        OwnKey { rns, rng, s, s_ntt, pk: PubKey { pk0_ntt: pk0, pk1_ntt: a_ntt } }
    }

    /// bfv.encrypt_exact(m), m[i] in [0, t).
    pub fn encrypt_exact(&mut self, m: &[u64]) -> Ct {
        let rns = self.rns.clone();
        let n = rns.n;
        let a = uniform(&rns, &mut self.rng);
        let e = small_error(n, &mut self.rng);
        let mut a_ntt = a.clone();
        rns.fwd(&mut a_ntt);
        let mut as_ = rns.mul_pw(&a_ntt, &self.s_ntt);
        rns.inv(&mut as_);
        let mut c0 = rns.zero();
        let mut enc = [0u64; 8];
        for i in 0..n {
            rns.encode_round(m[i], &mut enc);
            for (k, &q) in rns.qs.iter().enumerate() {
                c0[k * n + i] = submod(enc[k], addmod(as_[k * n + i], from_i64(e[i], q), q), q);
            }
        }
        Ct { c0, c1: a }
    }

    /// bfv.decrypt((c0, c1)) at the given coefficients (all when idx is None).
    pub fn decrypt(&self, ct: &Ct, idx: Option<&[usize]>) -> Vec<u64> {
        let rns = &self.rns;
        let n = rns.n;
        let l = rns.l();
        let mut c1 = ct.c1.clone();
        rns.fwd(&mut c1);
        let mut x = rns.mul_pw(&c1, &self.s_ntt);
        rns.inv(&mut x);
        rns.add_assign(&mut x, &ct.c0);
        let mut res = [0u64; 8];
        let mut one = |i: usize| {
            for k in 0..l {
                res[k] = x[k * n + i];
            }
            rns.decrypt_round(&res[..l])
        };
        match idx {
            None => (0..n).map(&mut one).collect(),
            Some(ix) => ix.iter().map(|&i| one(i)).collect(),
        }
    }
}

/// The returner's reply (he_matvec / he_outer `_return`): acc + Enc_pk_j(0) + round(Q M / t) + flood, with every draw
/// from `rng` in the reference order: M (N x randrange(t)), u (N x choice), e0, e1 (N x randint(-8, 8) each), flood
/// (N x randint(-2^F, 2^F)). `acc` is (c0, c1) in NTT form. Returns the coefficient-form ciphertext and M.
pub fn make_return(rns: &Rns, pk: &PubKey, acc: (&[u64], &[u64]), rng: &mut PyRandom, f_bits: u32) -> (Ct, Vec<u64>) {
    let n = rns.n;
    let t = rns.t;
    let m: Vec<u64> = (0..n).map(|_| rng.randrange_u64(t)).collect();
    let u: Vec<i64> = (0..n).map(|_| rng.ternary()).collect();
    let e0 = small_error(n, rng);
    let e1 = small_error(n, rng);
    let mut u_ntt = rns.from_signed(&u);
    rns.fwd(&mut u_ntt);
    let mut c0 = acc.0.to_vec();
    rns.mul_acc(&mut c0, &pk.pk0_ntt, &u_ntt);
    let mut c1 = acc.1.to_vec();
    rns.mul_acc(&mut c1, &pk.pk1_ntt, &u_ntt);
    rns.inv(&mut c0);
    rns.inv(&mut c1);
    let mut enc = [0u64; 8];
    for i in 0..n {
        rns.encode_round(m[i], &mut enc);
        let (neg, mag) = rng.randint_sym_pow2_arr::<5>(f_bits);
        for (k, &q) in rns.qs.iter().enumerate() {
            let fl = rns.md[k].limbs5(&mag);
            let fl = if neg { submod(0, fl, q) } else { fl };
            let j = k * n + i;
            c0[j] = addmod(addmod(addmod(c0[j], from_i64(e0[i], q), q), enc[k], q), fl, q);
            c1[j] = addmod(c1[j], from_i64(e1[i], q), q);
        }
    }
    (Ct { c0, c1 }, m)
}
