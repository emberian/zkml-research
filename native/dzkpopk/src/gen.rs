//! Key generation and encryption with a caller's coins, draw-for-draw as zkpopk_ligero.keygen / encrypt_sk /
//! encrypt_pk (so a PyRandom with the harness's seed reproduces the harness's statements exactly).

use crate::ntt::Nega;
use crate::proof::{PkCt, SkCt};
use crate::statement::{exact_nega, public_a, BigPoly, KeyRegistry};
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};
use pycompat::PyRandom;
use rayon::prelude::*;

fn modq(x: i128, q: u64) -> u64 {
    x.rem_euclid(q as i128) as u64
}

/// zkpopk_ligero._round_scale: u = round(Q m / t) (ties up), r = t u - Q m.
pub fn round_scale(q: &BigUint, t: u64, m: u64) -> (BigUint, i64) {
    let u = (BigUint::from(2u32) * q * m + t) / (2 * t as u128);
    let r = BigInt::from(&u * t) - BigInt::from(q * m);
    (u, r.to_i64().expect("|r| <= (t-1)/2"))
}

/// zkpopk_ligero.keygen with the caller's coins: (registry, s, e).
pub fn keygen(n: usize, primes: &[u64], t: u64, seed: &str, key_id: &str, rng: &mut PyRandom) -> (KeyRegistry, Vec<i64>, Vec<i64>) {
    let s: Vec<i64> = (0..n).map(|_| rng.ternary()).collect();
    let e: Vec<i64> = (0..n).map(|_| rng.randint_i64(-8, 8)).collect();
    let b = key_b(n, primes, seed, &s, &e);
    (KeyRegistry::new(n, primes, t, seed, key_id, b), s, e)
}

/// b = -(a s + e) mod Q with a = public_a(seed).
pub fn key_b(n: usize, primes: &[u64], seed: &str, s: &[i64], e: &[i64]) -> BigPoly {
    let q: BigUint = primes.iter().map(|&p| BigUint::from(p)).product();
    let a = BigPoly::from_big(&public_a(seed, n, &q));
    let nega = Nega::new(n);
    let res: Vec<Vec<u64>> = primes
        .par_iter()
        .map(|&p| {
            let as_ = exact_nega(&nega, &a.residues(p), s).unwrap();
            (0..n).map(|k| modq(-as_[k] - e[k] as i128, p)).collect()
        })
        .collect();
    BigPoly::from_rns(&res, primes)
}

/// zkpopk_ligero.encrypt_sk: m (length N, reduced mod t) nonzero only at `slots`; draws a (N randrange(Q)) then e
/// (N randint(-8, 8)) unless e is given.
pub fn encrypt_sk(reg: &KeyRegistry, s: &[i64], m: &[u64], slots: &[usize], rng: &mut PyRandom, e: Option<Vec<i64>>) -> ((BigPoly, BigPoly), SkCt) {
    let (n, t) = (reg.n, reg.t);
    let m: Vec<u64> = m.iter().map(|x| x % t).collect();
    for k in 0..n {
        assert!(m[k] == 0 || slots.contains(&k), "plaintext off the layout");
    }
    let a: Vec<BigUint> = (0..n).map(|_| rng.randbelow_big(&reg.q)).collect();
    let e = e.unwrap_or_else(|| (0..n).map(|_| rng.randint_i64(-8, 8)).collect());
    let us: Vec<(BigUint, i64)> = m.iter().map(|&x| if x == 0 { (BigUint::zero(), 0) } else { round_scale(&reg.q, t, x) }).collect();
    let a = BigPoly::from_big(&a);
    let nega = Nega::new(n);
    let res: Vec<Vec<u64>> = reg
        .primes
        .par_iter()
        .map(|&p| {
            let as_ = exact_nega(&nega, &a.residues(p), s).unwrap();
            (0..n).map(|k| modq((&us[k].0 % p).to_u64().unwrap() as i128 - as_[k] - e[k] as i128, p)).collect()
        })
        .collect();
    let c0 = BigPoly::from_rns(&res, &reg.primes);
    let r = slots.iter().map(|&k| us[k].1).collect();
    ((c0, a), SkCt { e, r })
}

/// zkpopk_ligero.encrypt_pk under (b, a) of `reg`: draws u (ternary), e0 (unless given), e1.
pub fn encrypt_pk(reg: &KeyRegistry, m: &[u64], slots: &[usize], rng: &mut PyRandom, e0: Option<Vec<i64>>) -> ((BigPoly, BigPoly), PkCt) {
    let (n, t) = (reg.n, reg.t);
    let m: Vec<u64> = m.iter().map(|x| x % t).collect();
    for k in 0..n {
        assert!(m[k] == 0 || slots.contains(&k), "plaintext off the layout");
    }
    let u: Vec<i64> = (0..n).map(|_| rng.ternary()).collect();
    let e0 = e0.unwrap_or_else(|| (0..n).map(|_| rng.randint_i64(-8, 8)).collect());
    let e1: Vec<i64> = (0..n).map(|_| rng.randint_i64(-8, 8)).collect();
    let us: Vec<(BigUint, i64)> = m.iter().map(|&x| if x == 0 { (BigUint::zero(), 0) } else { round_scale(&reg.q, t, x) }).collect();
    let nega = Nega::new(n);
    let (r0, r1): (Vec<Vec<u64>>, Vec<Vec<u64>>) = reg
        .primes
        .par_iter()
        .enumerate()
        .map(|(i, &p)| {
            let bu = exact_nega(&nega, &reg.b_res()[i], &u).unwrap();
            let au = exact_nega(&nega, &reg.a_res()[i], &u).unwrap();
            let c0 = (0..n).map(|k| modq(bu[k] + e0[k] as i128 + (&us[k].0 % p).to_u64().unwrap() as i128, p)).collect();
            let c1 = (0..n).map(|k| modq(au[k] + e1[k] as i128, p)).collect();
            (c0, c1)
        })
        .unzip();
    let c0 = BigPoly::from_rns(&r0, &reg.primes);
    let c1 = BigPoly::from_rns(&r1, &reg.primes);
    let r = slots.iter().map(|&k| us[k].1).collect();
    ((c0, c1), PkCt { u, e0, e1, r })
}
