//! BFV as bfv_ref.BFV / he_matvec.OwnKey, over RNS: every draw from the key's random.Random in the reference order,
//! so keys, ciphertexts and decryptions are bit-identical to the harness.
use crate::arith::*;
use crate::rns::Rns;
use crate::coins::{os_key, Coins, Prf};
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
    /// encryption coins: the reference stream (`new`, `from_ceremony`) or the OS-keyed PRF (`*_secure`)
    pub rng: Coins,
    /// the key for this custodian's HE-return coins; None = the public reference labels (test harness only)
    pub return_key: Option<[u8; 32]>,
    /// HE returns on the wire: None = (c0, c1) in full; Some = modulus-switched down to its first primes, c0 only at
    /// the coefficients the recipient decrypts (`set_return_primes`)
    pub compress: Option<Arc<Compress>>,
    pub s: Vec<i64>,
    s_ntt: Vec<u64>,
    pub pk: PubKey,
}

pub struct Compress {
    pub small: Arc<Rns>,
    s_ntt: Vec<u64>,
}

/// The fewest primes an HE return can be switched to with decryption still exact: the switching rounding term,
/// at most (1 + N)/2, must stay under Q_k / (4 t), with a factor-2 margin (the flood's ratio to Q is unchanged).
pub fn return_primes_needed(rns: &Rns) -> usize {
    let t = rns.t as f64;
    let mut q = 1f64;
    for (k, &qk) in rns.qs.iter().enumerate() {
        q *= qk as f64;
        if (1.0 + rns.n as f64) / 2.0 < q / (8.0 * t) {
            return k + 1;
        }
    }
    rns.l()
}

/// Modulus-switch a coefficient-form ciphertext from all of `rns`'s primes down to the first `k` (dropping the last
/// prime at a time: c <- (c - [c]_q) / q with [c]_q centered, i.e. round(c / q)), keeping c0 only at `coefs`.
/// Wire layout: c0 [k x |coefs|] then c1 [k x N], residue-major.
pub fn compress_return(rns: &Rns, ct: &Ct, k: usize, coefs: &[usize]) -> Vec<u64> {
    let n = rns.n;
    let l = rns.l();
    let drop = |c: &[u64], pos: &dyn Fn(usize) -> usize, cnt: usize| -> Vec<u64> {
        // c: residues limb-major over `cnt` coefficients (limb stride n, position pos(j))
        let mut cur: Vec<Vec<u64>> = (0..l).map(|kk| (0..cnt).map(|j| c[kk * n + pos(j)]).collect()).collect();
        for top in (k..l).rev() {
            let qt = rns.qs[top];
            let half = qt / 2;
            let last = cur.pop().unwrap();
            for (kk, row) in cur.iter_mut().enumerate() {
                let q = rns.qs[kk];
                let inv = invmod(qt % q, q);
                for (j, x) in row.iter_mut().enumerate() {
                    let r = last[j];
                    // centered remainder r in (-qt/2, qt/2]
                    let rq = if r > half { submod(0, (qt - r) % q, q) } else { r % q };
                    *x = mulmod(submod(*x, rq, q), inv, q);
                }
            }
            let _ = top;
        }
        cur.into_iter().flatten().collect()
    };
    let mut out = drop(&ct.c0, &|j| coefs[j], coefs.len());
    out.extend(drop(&ct.c1, &|j| j, n));
    out
}

/// A ciphertext's uniform half a from its 32-byte seed (the PRF stream "bfv-a" under the seed): seeded ciphertexts
/// travel as (c0, seed).
pub fn expand_a(rns: &Rns, seed: &[u8; 32]) -> Vec<u64> {
    uniform(rns, &mut Coins::Prf(Prf::new(seed, "bfv-a")))
}

/// bfv.uniform(): N draws randrange(Q), as residues.
fn uniform(rns: &Rns, rng: &mut Coins) -> Vec<u64> {
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

fn small_error(n: usize, rng: &mut Coins) -> Vec<i64> {
    (0..n).map(|_| rng.randint_i64(-8, 8)).collect()
}

impl OwnKey {
    /// he_matvec.OwnKey(N, Q, t, seed).
    pub fn new(rns: Arc<Rns>, seed: u64) -> Self {
        Self::keygen(rns, Coins::Py(PyRandom::from_u64(seed)), None)
    }

    /// A key with s, a, e and every later coin from OS randomness (a party process's ungated key).
    pub fn new_secure(rns: Arc<Rns>) -> Self {
        Self::keygen(rns, Coins::Prf(Prf::new(&os_key(), "ownkey")), Some(os_key()))
    }

    fn keygen(rns: Arc<Rns>, mut rng: Coins, return_key: Option<[u8; 32]>) -> Self {
        let n = rns.n;
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
        OwnKey { rns, rng, return_key, compress: None, s, s_ntt, pk: PubKey { pk0_ntt: pk0, pk1_ntt: a_ntt } }
    }

    /// keygen_ceremony.CeremonyKey(N, Q, t, cust, seed): the ceremony's (s, b, a); the encryption coins come from
    /// random.Random(seed), with no key draws.
    pub fn from_ceremony(rns: Arc<Rns>, seed: u64, s: &[i64], b: &[Vec<u64>], a: &[Vec<u64>]) -> Self {
        Self::from_ceremony_coins(rns, Coins::Py(PyRandom::from_u64(seed)), None, s, b, a)
    }

    /// The ceremony's key with encryption coins and HE-return coins from OS randomness (what a party process uses).
    pub fn from_ceremony_secure(rns: Arc<Rns>, s: &[i64], b: &[Vec<u64>], a: &[Vec<u64>]) -> Self {
        Self::from_ceremony_coins(rns, Coins::Prf(Prf::new(&os_key(), "ownkey")), Some(os_key()), s, b, a)
    }

    fn from_ceremony_coins(rns: Arc<Rns>, rng: Coins, return_key: Option<[u8; 32]>, s: &[i64], b: &[Vec<u64>], a: &[Vec<u64>]) -> Self {
        let mut s_ntt = rns.from_signed(s);
        rns.fwd(&mut s_ntt);
        let flat = |v: &[Vec<u64>]| {
            let mut x: Vec<u64> = v.iter().flatten().copied().collect();
            rns.fwd(&mut x);
            x
        };
        let pk = PubKey { pk0_ntt: flat(b), pk1_ntt: flat(a) };
        OwnKey { rns: rns.clone(), rng, return_key, compress: None, s: s.to_vec(), s_ntt, pk }
    }

    /// Send and receive HE returns modulus-switched to the first `k` primes (k < L), c0 only at the decrypted
    /// coefficients. Decryption stays exact while the return's noise relative to Q stays under 1/(2t): the 2^F flood
    /// keeps its ratio, and switching adds a rounding term of at most (1 + N)/2 per coefficient, so k = 2 suffices at
    /// the profiles here (`return_primes_needed`). Every custodian must use the same k.
    pub fn set_return_primes(&mut self, k: usize) {
        assert!(k >= 1 && k < self.rns.l());
        let small = Arc::new(Rns::new(self.rns.n, &self.rns.qs[..k], self.rns.t));
        let mut s_ntt = small.from_signed(&self.s);
        small.fwd(&mut s_ntt);
        self.compress = Some(Arc::new(Compress { small, s_ntt }));
    }

    /// Decrypt a compressed return (`compress_return`) at `coefs`.
    pub fn decrypt_compressed(&self, wire: &[u64], coefs: &[usize]) -> Vec<u64> {
        let c = self.compress.as_ref().expect("compressed returns not configured");
        let rns = &c.small;
        let (n, k) = (rns.n, rns.l());
        let m = coefs.len();
        assert_eq!(wire.len(), k * m + k * n, "compressed return length");
        let mut c1 = wire[k * m..].to_vec();
        rns.fwd(&mut c1);
        let mut x = rns.mul_pw(&c1, &c.s_ntt);
        rns.inv(&mut x);
        let mut res = [0u64; 8];
        coefs
            .iter()
            .enumerate()
            .map(|(j, &i)| {
                for kk in 0..k {
                    res[kk] = addmod(x[kk * n + i], wire[kk * m + j], rns.qs[kk]);
                }
                rns.decrypt_round(&res[..k])
            })
            .collect()
    }

    /// A fresh HE-return key (a secure key only; the reference key keeps its public labels). The loop calls it per step.
    pub fn refresh_return_key(&mut self) {
        if self.return_key.is_some() {
            self.return_key = Some(os_key());
        }
    }

    /// The coins for one HE return: random.Random(label) for the reference key, else the PRF under return_key.
    pub fn return_coins(&self, label: &str) -> Coins {
        Coins::for_label(self.return_key.as_ref(), label)
    }

    /// bfv.encrypt_exact(m), m[i] in [0, t).
    pub fn encrypt_exact(&mut self, m: &[u64]) -> Ct {
        self.encrypt_exact_w(m).0
    }

    /// encrypt_exact, also returning the error e (the sender's ZKPoPK witness).
    pub fn encrypt_exact_w(&mut self, m: &[u64]) -> (Ct, Vec<i64>) {
        let (ct, e, _) = self.encrypt_seeded(m);
        (ct, e)
    }

    /// encrypt_exact_w; with the OS-keyed coins (`*_secure` keys) a = expand_a(seed) for a fresh 32-byte seed, which
    /// is returned so the ciphertext can travel as (c0, seed). The reference coins draw a in full, as the harness.
    pub fn encrypt_seeded(&mut self, m: &[u64]) -> (Ct, Vec<i64>, Option<[u8; 32]>) {
        let rns = self.rns.clone();
        let n = rns.n;
        let (a, seed) = match &mut self.rng {
            Coins::Prf(r) => {
                let mut sd = [0u8; 32];
                for c in sd.chunks_mut(8) {
                    c.copy_from_slice(&r.next_u64().to_le_bytes());
                }
                (expand_a(&rns, &sd), Some(sd))
            }
            Coins::Py(_) => (uniform(&rns, &mut self.rng), None),
        };
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
        (Ct { c0, c1: a }, e, seed)
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
pub fn make_return(rns: &Rns, pk: &PubKey, acc: (&[u64], &[u64]), rng: &mut Coins, f_bits: u32) -> (Ct, Vec<u64>) {
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
