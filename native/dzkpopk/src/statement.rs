//! The public side: key registry, statements, the digit layout, quotient bounds and the proof shape
//! (zkpopk_ligero.KeyRegistry, Statement, layout, quotient_bounds, shape, proof_bytes, folds_for).

use crate::canon::Json;
use crate::field::{p_big, Fe};
use crate::ntt::Nega;
use crate::transcript::{shake256, DOMAIN};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::sync::{Arc, OnceLock};

pub const MIN_MODULUS_BITS: u32 = 60; // q, t in (2^60, 2^61)
pub const EB: usize = 32;
/// scholar_zkpopk.DOMAIN (public_a's domain).
pub const SCHOLAR_DOMAIN: &str = "scholar-bfv-stern-v1";

// ------------------------------------------------------------------------------------------- integers
/// N coefficients of nl little-endian u64 limbs each (an element of R_Q, or any vector of naturals).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigPoly {
    nl: usize,
    data: Vec<u64>,
}

fn limbs_of(x: &BigUint) -> Vec<u64> {
    let d = x.to_u64_digits();
    if d.is_empty() {
        vec![0]
    } else {
        d
    }
}

impl BigPoly {
    /// N coefficients of nl limbs each; refuses nl = 0 or a ragged length.
    pub fn from_limbs(nl: usize, data: Vec<u64>) -> Result<BigPoly, String> {
        if nl == 0 || data.len() % nl != 0 {
            return Err("BigPoly: limb layout".into());
        }
        Ok(BigPoly { nl, data })
    }
    pub fn nl(&self) -> usize {
        self.nl
    }
    pub fn data(&self) -> &[u64] {
        &self.data
    }
    pub fn len(&self) -> usize {
        self.data.len() / self.nl
    }
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    pub fn from_big(v: &[BigUint]) -> BigPoly {
        let nl = v.iter().map(|x| limbs_of(x).len()).max().unwrap_or(1).max(1);
        let mut data = vec![0u64; nl * v.len()];
        for (i, x) in v.iter().enumerate() {
            for (j, d) in x.to_u64_digits().iter().enumerate() {
                data[i * nl + j] = *d;
            }
        }
        BigPoly { nl, data }
    }
    /// From residues per prime (each < q_i) by CRT; the primes must be distinct primes.
    pub fn from_rns(res: &[Vec<u64>], primes: &[u64]) -> BigPoly {
        let n = res[0].len();
        let crt = Crt::new(primes);
        let v: Vec<BigUint> = (0..n).into_par_iter().map(|k| crt.combine(&res.iter().map(|r| r[k]).collect::<Vec<_>>())).collect();
        BigPoly::from_big(&v)
    }
    pub fn coeff(&self, i: usize) -> &[u64] {
        &self.data[i * self.nl..(i + 1) * self.nl]
    }
    pub fn coeff_big(&self, i: usize) -> BigUint {
        let c = self.coeff(i);
        let mut u = Vec::with_capacity(2 * c.len());
        for x in c {
            u.push(*x as u32);
            u.push((*x >> 32) as u32);
        }
        BigUint::from_slice(&u)
    }
    pub fn to_big(&self) -> Vec<BigUint> {
        (0..self.len()).map(|i| self.coeff_big(i)).collect()
    }
    pub fn residues(&self, q: u64) -> Vec<u64> {
        (0..self.len())
            .map(|i| {
                let mut r: u128 = 0;
                for x in self.coeff(i).iter().rev() {
                    r = ((r << 64) | *x as u128) % q as u128;
                }
                r as u64
            })
            .collect()
    }
    /// Every coefficient < m.
    pub fn all_below(&self, m: &BigUint) -> bool {
        let ml = limbs_of(m);
        (0..self.len()).all(|i| lt_limbs(self.coeff(i), &ml))
    }
    /// Coefficient i as wb big-endian bytes (it must fit).
    pub fn write_be(&self, i: usize, wb: usize, out: &mut Vec<u8>) {
        let c = self.coeff(i);
        for b in (0..wb).rev() {
            let limb = b / 8;
            out.push(if limb < c.len() { (c[limb] >> (8 * (b % 8))) as u8 } else { 0 });
        }
    }
}

fn lt_limbs(a: &[u64], b: &[u64]) -> bool {
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let x = a.get(i).copied().unwrap_or(0);
        let y = b.get(i).copied().unwrap_or(0);
        if x != y {
            return x < y;
        }
    }
    false
}

pub struct Crt {
    q: BigUint,
    terms: Vec<BigUint>, // (Q/q_i) * ((Q/q_i)^-1 mod q_i)
}

impl Crt {
    pub fn new(primes: &[u64]) -> Crt {
        let q: BigUint = primes.iter().map(|&p| BigUint::from(p)).product();
        let terms = primes
            .iter()
            .map(|&p| {
                let mq = &q / p;
                let r = (&mq % p).to_u64().unwrap();
                mq * BigUint::from(inv_mod_u64(r, p))
            })
            .collect();
        Crt { q, terms }
    }
    pub fn combine(&self, r: &[u64]) -> BigUint {
        let mut x = BigUint::zero();
        for (ri, t) in r.iter().zip(&self.terms) {
            x += t * *ri;
        }
        x % &self.q
    }
}

pub fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}
pub fn pow_mod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    a %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod(r, a, m);
        }
        a = mul_mod(a, a, m);
        e >>= 1;
    }
    r
}
pub fn inv_mod_u64(a: u64, p: u64) -> u64 {
    pow_mod(a, p - 2, p)
}

/// bfv_ref.is_probable_prime for n < 2^64 (deterministic Miller-Rabin; same answers).
pub fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    const SMALL: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    for p in SMALL {
        if n % p == 0 {
            return n == p;
        }
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'outer: for a in SMALL {
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 0..s - 1 {
            x = mul_mod(x, x, n);
            if x == n - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

/// bfv_ref.ntt_primes(bits, count, two_n): the largest primes below 2^bits with p = 1 mod 2N.
pub fn ntt_primes(bits: u32, count: usize, two_n: u64) -> Vec<u64> {
    let mut out = vec![];
    let mut p = ((1u64 << bits) - 1) / two_n * two_n + 1;
    while out.len() < count {
        if is_prime_u64(p) {
            out.push(p);
        }
        p -= two_n;
    }
    out
}

/// scholar_zkpopk.public_a(seed, N, Q): rejection sampling from SHAKE-256 over canonical([DOMAIN, "key-a", seed, ctr]).
pub fn public_a(seed: &str, n: usize, q: &BigUint) -> Vec<BigUint> {
    let width = ((q.bits() + 7) / 8) as usize;
    let limit = (BigUint::one() << (8 * width)) / q * q;
    let draw = |ctr: usize| -> Option<BigUint> {
        let c = Json::list(vec![Json::s(SCHOLAR_DOMAIN), Json::s("key-a"), Json::s(seed), Json::i(ctr as i64)]).canonical();
        let x = BigUint::from_bytes_be(&shake256(&[&c], width));
        if x < limit {
            Some(x % q)
        } else {
            None
        }
    };
    let mut out = Vec::with_capacity(n);
    let mut start = 0usize;
    while out.len() < n {
        let chunk = (n - out.len()) + 64;
        let got: Vec<Option<BigUint>> = (start..start + chunk).into_par_iter().map(draw).collect();
        for x in got.into_iter().flatten() {
            if out.len() < n {
                out.push(x);
            }
        }
        start += chunk;
    }
    out
}

// ------------------------------------------------------------------------------------------- registry
/// The pinned key record: a = public_a(seed), b registered. For a secret-key batch the sender's own key; for a
/// public-key batch the joint key.
pub struct KeyRegistry {
    pub n: usize,
    pub primes: Vec<u64>,
    pub t: u64,
    pub seed: String,
    pub key_id: String,
    pub q: BigUint,
    pub b: BigPoly,
    /// public_a(seed) at construction; kept as a field so a tampered a can be presented (and refused).
    pub a: BigPoly,
    res_b: OnceLock<Vec<Vec<u64>>>,
    res_a: OnceLock<Vec<Vec<u64>>>,
}

impl KeyRegistry {
    pub fn new(n: usize, primes: &[u64], t: u64, seed: &str, key_id: &str, b: BigPoly) -> KeyRegistry {
        let q: BigUint = primes.iter().map(|&p| BigUint::from(p)).product();
        let a = BigPoly::from_big(&public_a(seed, n, &q));
        KeyRegistry::with_a(n, primes, t, seed, key_id, b, a)
    }

    pub fn with_a(n: usize, primes: &[u64], t: u64, seed: &str, key_id: &str, b: BigPoly, a: BigPoly) -> KeyRegistry {
        let q: BigUint = primes.iter().map(|&p| BigUint::from(p)).product();
        KeyRegistry {
            n,
            primes: primes.to_vec(),
            t,
            seed: seed.into(),
            key_id: key_id.into(),
            q,
            b,
            a,
            res_b: OnceLock::new(),
            res_a: OnceLock::new(),
        }
    }

    /// The pinned profile (KeyRegistry.valid): N a power of two; distinct primes q_i and t in (2^60, 2^61), q_i = 1
    /// mod 2N, t odd and not a q_i; Q > 17 t (decryption margin); b canonical of length N.
    pub fn valid(&self) -> bool {
        let inr = |x: u64| x > (1u64 << MIN_MODULUS_BITS) && x < (1u64 << (MIN_MODULUS_BITS + 1));
        let mut ps = self.primes.clone();
        ps.sort_unstable();
        ps.dedup();
        self.n >= 2
            && self.n.is_power_of_two()
            && self.n <= 1 << 31
            && !self.primes.is_empty()
            && ps.len() == self.primes.len()
            && self.primes.iter().all(|&q| inr(q) && q % (2 * self.n as u64) == 1 && is_prime_u64(q))
            && inr(self.t)
            && self.t % 2 == 1
            && is_prime_u64(self.t)
            && !self.primes.contains(&self.t)
            && self.q > BigUint::from(17u32) * self.t
            && self.b.len() == self.n
            && self.b.all_below(&self.q)
    }

    pub fn public(&self) -> Vec<u8> {
        let b = Json::List(self.b.to_big().into_iter().map(|x| Json::Int(BigInt::from(x))).collect());
        Json::list(vec![
            Json::Int(BigInt::from(self.n)),
            Json::List(self.primes.iter().map(|&p| Json::Int(BigInt::from(p))).collect()),
            Json::Int(BigInt::from(self.t)),
            Json::s(&self.seed),
            Json::s(&self.key_id),
            b,
        ])
        .canonical()
    }

    pub fn b_res(&self) -> &Vec<Vec<u64>> {
        // no rayon inside a OnceLock initializer: a worker stealing a task that re-enters it would deadlock
        self.res_b.get_or_init(|| self.primes.iter().map(|&q| self.b.residues(q)).collect())
    }
    pub fn a_res(&self) -> &Vec<Vec<u64>> {
        self.res_a.get_or_init(|| self.primes.iter().map(|&q| self.a.residues(q)).collect())
    }
}

// ------------------------------------------------------------------------------------------- statement
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// a secret-key batch (the MPC helpers' sends), bound to the sender's registered key
    Sk,
    /// a public-key batch (FHE (b)'s masks) under the joint key
    Pk,
    /// the key relation alone (the ceremony)
    Key,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Sk => "sk",
            Kind::Pk => "pk",
            Kind::Key => "key",
        }
    }
    pub fn parse(s: &str) -> Result<Kind, String> {
        match s {
            "sk" => Ok(Kind::Sk),
            "pk" => Ok(Kind::Pk),
            "key" => Ok(Kind::Key),
            _ => Err("kind".into()),
        }
    }
    pub fn secret(self) -> bool {
        self != Kind::Pk
    }
}

/// Immutable once built: the digest and residue caches are computed from these fields, so they are private
/// (a statement whose context could be changed after `new` would keep a stale digest).
pub struct Statement {
    reg: Arc<KeyRegistry>,
    kind: Kind,
    /// (c0, c1) per ciphertext, canonical (< Q)
    cts: Vec<(BigPoly, BigPoly)>,
    /// per ciphertext the public slot set: sorted, distinct, < N
    slots: Vec<Vec<usize>>,
    context: Json,
    digest: [u8; 32],
    /// [prime][ct] -> (c0 mod q, c1 mod q)
    res: OnceLock<Vec<Vec<(Vec<u64>, Vec<u64>)>>>,
}

impl Statement {
    pub fn new(reg: Arc<KeyRegistry>, kind: Kind, cts: Vec<(BigPoly, BigPoly)>, slots: Vec<Vec<usize>>, context: Json) -> Result<Statement, String> {
        if (kind == Kind::Key) != cts.is_empty() || slots.len() != cts.len() {
            return Err("batch shape".into());
        }
        let n = reg.n;
        for ((c0, c1), s) in cts.iter().zip(&slots) {
            if c0.len() != n || c1.len() != n {
                return Err("ciphertext shape".into());
            }
            if !c0.all_below(&reg.q) || !c1.all_below(&reg.q) {
                return Err("noncanonical ciphertext".into());
            }
            if s.windows(2).any(|w| w[0] >= w[1]) || s.iter().any(|&k| k >= n) {
                return Err("slot layout".into());
            }
        }
        let mut st = Statement { reg, kind, cts, slots, context, digest: [0; 32], res: OnceLock::new() };
        st.digest = st.compute_digest();
        Ok(st)
    }

    fn compute_digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(DOMAIN);
        h.update(self.reg.public());
        let slots = Json::List(self.slots.iter().map(|s| Json::List(s.iter().map(|&k| Json::Int(BigInt::from(k))).collect())).collect());
        h.update(Json::list(vec![Json::s(self.kind.name()), self.context.clone(), slots]).canonical());
        let wb = ((self.reg.q.bits() + 7) / 8) as usize;
        for (c0, c1) in &self.cts {
            let mut buf = Vec::with_capacity(2 * c0.len() * wb);
            for p in [c0, c1] {
                for i in 0..p.len() {
                    p.write_be(i, wb, &mut buf);
                }
            }
            h.update(&buf);
        }
        h.finalize().into()
    }

    pub fn reg(&self) -> &Arc<KeyRegistry> {
        &self.reg
    }
    pub fn kind(&self) -> Kind {
        self.kind
    }
    pub fn cts(&self) -> &[(BigPoly, BigPoly)] {
        &self.cts
    }
    pub fn slots(&self) -> &[Vec<usize>] {
        &self.slots
    }
    pub fn context(&self) -> &Json {
        &self.context
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub fn ct_res(&self) -> &Vec<Vec<(Vec<u64>, Vec<u64>)>> {
        self.res.get_or_init(|| {
            self.reg.primes.iter().map(|&q| self.cts.iter().map(|(c0, c1)| (c0.residues(q), c1.residues(q))).collect()).collect()
        })
    }
}

// ------------------------------------------------------------------------------------------- layout and bounds
/// One witness group: `n` integers in [lo, hi], each written as digits with weights(hi - lo).
#[derive(Clone, Debug)]
pub struct Group {
    pub name: String,
    pub n: usize,
    pub lo: BigInt,
    pub hi: BigInt,
}

impl Group {
    fn small(name: String, n: usize, lo: i64, hi: i64) -> Group {
        Group { name, n, lo: BigInt::from(lo), hi: BigInt::from(hi) }
    }
    pub fn range(&self) -> BigUint {
        (&self.hi - &self.lo).to_biguint().unwrap()
    }
    pub fn ndig(&self) -> usize {
        weights(&self.range()).len()
    }
}

/// zkpopk_ligero.weights(U): 1, 2, 4, ..., and a top digit of adjusted weight so [0, U] is covered exactly.
pub fn weights(u: &BigUint) -> Vec<BigUint> {
    let w = u.bits() as usize;
    let mut out: Vec<BigUint> = (0..w.saturating_sub(1)).map(|j| BigUint::one() << j).collect();
    if w >= 1 {
        out.push(u - (BigUint::one() << (w - 1)) + 1u32);
    }
    out
}

/// zkpopk_ligero.folds_for(T).
pub fn folds_for(t: usize) -> usize {
    let bits = t as f64 * (4.0f64 / 3.0).log2();
    ((bits / 60.0).ceil() as usize).max(1)
}

/// zkpopk_ligero.quotient_bounds: |F_i| <= B_i for any in-range witness and any rho.
pub fn quotient_bounds(kind: Kind, n: usize, primes: &[u64], t: u64, m: usize) -> Result<Vec<BigUint>, String> {
    let mut out = vec![];
    let t = BigUint::from(t);
    for &q in primes {
        let q = BigUint::from(q);
        let ring = (&q - 1u32) * (n + 1) + 8u32;
        let ct0 = &t * &ring + (&t - 1u32) / 2u32;
        let b = if kind.secret() { (&q - 1u32) * n * (&ring + &ct0 * m) } else { (&q - 1u32) * n * m * (&ct0 + &ring) };
        if (&b * 2u32 + &q) >= *p_big() {
            return Err("field too small for this batch: the folded limb equation could wrap modulo P".into());
        }
        out.push(b);
    }
    Ok(out)
}

/// zkpopk_ligero.layout: round-1 groups in wire order, round-2 quotient groups (one per fold and prime).
pub fn layout(kind: Kind, n: usize, primes: &[u64], t: u64, slot_sizes: &[usize], f: usize) -> Result<(Vec<Group>, Vec<Group>), String> {
    let r = ((t - 1) / 2) as i64;
    let mut g1 = vec![];
    if kind.secret() {
        g1.push(Group::small("s".into(), n, -1, 1));
        g1.push(Group::small("e_pk".into(), n, -8, 8));
        for (j, &s) in slot_sizes.iter().enumerate() {
            g1.push(Group::small(format!("e{j}"), n, -8, 8));
            g1.push(Group::small(format!("r{j}"), s, -r, r));
        }
    } else {
        for (j, &s) in slot_sizes.iter().enumerate() {
            g1.push(Group::small(format!("u{j}"), n, -1, 1));
            g1.push(Group::small(format!("e0_{j}"), n, -8, 8));
            g1.push(Group::small(format!("e1_{j}"), n, -8, 8));
            g1.push(Group::small(format!("r{j}"), s, -r, r));
        }
    }
    let bs = quotient_bounds(kind, n, primes, t, slot_sizes.len())?;
    let mut g2 = vec![];
    for fi in 0..f {
        for (i, (b, &q)) in bs.iter().zip(primes).enumerate() {
            let kb = BigInt::from(b / q + 1u32);
            g2.push(Group { name: format!("K{fi}_{i}"), n: 1, lo: -kb.clone(), hi: kb });
        }
    }
    Ok((g1, g2))
}

pub fn nbits(groups: &[Group]) -> usize {
    groups.iter().map(|g| g.n * g.ndig()).sum()
}

/// zkpopk_ligero.proof_bytes.
pub fn proof_bytes(k: usize, th: usize, t: usize, m1: usize, m2: usize) -> usize {
    let lg_d = crate::ntt::n_d_for(k, th).trailing_zeros() as usize;
    let msgs = (k + th) + (2 * k + th - 1) + (2 * k + 2 * th - 1);
    let per_col = (m1 + 3) + 1 + lg_d + m2 + 1 + lg_d;
    EB * (2 + msgs + t * per_col)
}

#[derive(Clone, Debug)]
pub struct Shape {
    pub k: usize,
    pub th: usize,
    pub t: usize,
    pub f: usize,
    pub m1: usize,
    pub m2: usize,
    pub n1: usize,
    pub n2: usize,
    pub g1: Vec<Group>,
    pub g2: Vec<Group>,
}

/// zkpopk_ligero.shape: th = T, F = folds_for(T), and the k (16 .. 2^19) that minimizes the proof's bytes.
pub fn shape_of(kind: Kind, n: usize, primes: &[u64], t: u64, slot_sizes: &[usize], tcols: usize) -> Result<Shape, String> {
    let th = tcols;
    let f = folds_for(tcols);
    let (g1, g2) = layout(kind, n, primes, t, slot_sizes, f)?;
    let (n1, n2) = (nbits(&g1), nbits(&g2));
    let mut best: Option<(usize, usize, usize, usize)> = None;
    for lk in 4..20 {
        let k = 1usize << lk;
        let (m1, m2) = (n1.div_ceil(k), n2.div_ceil(k));
        let b = proof_bytes(k, th, tcols, m1, m2);
        if best.is_none() || b < best.unwrap().0 {
            best = Some((b, k, m1, m2));
        }
    }
    let (_, k, m1, m2) = best.unwrap();
    Ok(Shape { k, th, t: tcols, f, m1, m2, n1, n2, g1, g2 })
}

pub fn shape(st: &Statement, tcols: usize) -> Result<Shape, String> {
    let sizes: Vec<usize> = st.slots.iter().map(|s| s.len()).collect();
    shape_of(st.kind, st.reg.n, &st.reg.primes, st.reg.t, &sizes, tcols)
}

/// zkpopk_ligero.batch_proof_bits: (bits, shape) from the batch's shape alone.
pub fn batch_proof_bits(kind: Kind, n: usize, primes: &[u64], t: u64, slot_sizes: &[usize], tcols: usize) -> Result<(usize, Shape), String> {
    let sh = shape_of(kind, n, primes, t, slot_sizes, tcols)?;
    Ok((8 * proof_bytes(sh.k, sh.th, tcols, sh.m1, sh.m2), sh))
}

// ------------------------------------------------------------------------------------------- exact ring products
/// Exact a * v in Z[X]/(X^N + 1) for a with entries in [0, 2^61] and |v| small enough that N 2^61 max|v| < P/2,
/// computed in F_P and lifted centered. Returns None if the bound does not hold.
pub fn exact_nega(nega: &Nega, a: &[u64], v: &[i64]) -> Option<Vec<i128>> {
    let amax = a.iter().copied().max().unwrap_or(0) as f64;
    let vmax = v.iter().map(|x| x.unsigned_abs()).max().unwrap_or(0) as f64;
    if (a.len() as f64) * amax * vmax >= 2f64.powi(252) {
        return None;
    }
    let fa: Vec<Fe> = a.iter().map(|&x| Fe::from_u64(x)).collect();
    let fv: Vec<Fe> = v.iter().map(|&x| Fe::from_i64(x)).collect();
    nega.mul(&fa, &fv).into_iter().map(|x| x.to_i128_centered()).collect()
}
