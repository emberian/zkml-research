//! zkpopk_ligero.Transcript, H, and the salted Merkle tree.

use crate::field::{p_big, Fe};
use num_bigint::BigUint;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Shake256;

pub const DOMAIN: &[u8] = b"dl-gen4-zkpopk-ligero-v1";

pub fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        Digest::update(&mut h, p);
    }
    h.finalize().into()
}

pub fn shake256(data: &[&[u8]], n: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    for d in data {
        h.update(d);
    }
    let mut out = vec![0u8; n];
    h.finalize_xof().read(&mut out);
    out
}

/// zkpopk_ligero.H: SHA-256 over (8-byte big-endian length, bytes) pairs.
pub fn hh(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        Digest::update(&mut h, &(p.len() as u64).to_be_bytes());
        Digest::update(&mut h, p);
    }
    h.finalize().into()
}

#[derive(Clone)]
pub struct Transcript {
    pub legacy: bool,
    pub state: [u8; 32],
}

/// Rejection-sampled draws below a modulus < 2^64 from one SHAKE stream (Transcript.ints' inner loop).
fn expand_u64(state: &[u8; 32], label: &str, count: usize, m: u64) -> Vec<u64> {
    let bl = 64 - m.leading_zeros() as usize;
    let nb = (bl + 7) / 8 + 8;
    assert!(nb <= 16);
    // lim = (2^(8 nb) // m) * m; at nb = 16 a power-of-two m divides 2^128 and every draw is accepted
    let all = nb == 16 && m.is_power_of_two();
    let lim: u128 = if nb == 16 { (u128::MAX / m as u128) * m as u128 } else { ((1u128 << (8 * nb)) / m as u128) * m as u128 };
    let mut out = Vec::with_capacity(count);
    let mut ctr: u64 = 0;
    while out.len() < count {
        let need = count - out.len();
        let raw = shake256(&[state, label.as_bytes(), &ctr.to_be_bytes()], nb * need);
        ctr += 1;
        for i in 0..need {
            let mut x: u128 = 0;
            for b in &raw[i * nb..(i + 1) * nb] {
                x = (x << 8) | *b as u128;
            }
            if all || x < lim {
                out.push((x % m as u128) as u64);
            }
        }
    }
    out
}

impl Transcript {
    pub fn new(statement_digest: &[u8; 32], legacy: bool) -> Transcript {
        Transcript { legacy, state: sha256(&[DOMAIN, b"|statement|", statement_digest]) }
    }

    pub fn absorb(&mut self, label: &str, data: &[u8]) {
        if self.legacy {
            return;
        }
        let d = sha256(&[data]);
        self.state = sha256(&[&self.state, label.as_bytes(), &d]);
    }

    fn advance(&mut self, label: &str) {
        self.state = sha256(&[&self.state, b"|drawn|", label.as_bytes()]);
    }

    /// Transcript.ints(label, count, mod) for mod < 2^64.
    pub fn ints_u64(&mut self, label: &str, count: usize, m: u64) -> Vec<u64> {
        let out = expand_u64(&self.state, label, count, m);
        self.advance(label);
        out
    }

    /// Many ints_u64 calls in order; the state chain does not depend on the outputs, so the expansions run in parallel.
    pub fn ints_u64_many(&mut self, calls: &[(String, usize, u64)]) -> Vec<Vec<u64>> {
        let mut states = Vec::with_capacity(calls.len());
        for (label, _, _) in calls {
            states.push(self.state);
            self.advance(label);
        }
        calls.par_iter().zip(states.par_iter()).map(|((l, c, m), s)| expand_u64(s, l, *c, *m)).collect()
    }

    /// Transcript.ints(label, count, P).
    pub fn ints_p(&mut self, label: &str, count: usize) -> Vec<Fe> {
        let p = p_big();
        let nb = (255 + 7) / 8 + 8;
        let lim = (BigUint::from(1u32) << (8 * nb)) / p * p;
        let mut out = Vec::with_capacity(count);
        let mut ctr: u64 = 0;
        while out.len() < count {
            let need = count - out.len();
            let raw = shake256(&[&self.state, label.as_bytes(), &ctr.to_be_bytes()], nb * need);
            ctr += 1;
            for i in 0..need {
                let x = BigUint::from_bytes_be(&raw[i * nb..(i + 1) * nb]);
                if x < lim {
                    out.push(Fe::from_biguint(&(x % p)));
                }
            }
        }
        self.advance(label);
        out
    }

    /// Transcript.distinct(label, T, n).
    pub fn distinct(&mut self, label: &str, t: usize, n: usize) -> Vec<usize> {
        let mut out = Vec::with_capacity(t);
        let mut seen = std::collections::HashSet::new();
        let mut ctr = 0;
        while out.len() < t {
            for j in self.ints_u64(&format!("{label}{ctr}"), t, n as u64) {
                if out.len() < t && seen.insert(j) {
                    out.push(j as usize);
                }
            }
            ctr += 1;
        }
        out
    }
}

/// The salted Merkle tree: levels[0] are the leaves H("leaf", salt, column bytes).
pub struct Merkle {
    pub levels: Vec<Vec<[u8; 32]>>,
}

impl Merkle {
    pub fn build(leaves: Vec<[u8; 32]>) -> Merkle {
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let l = levels.last().unwrap();
            let next: Vec<[u8; 32]> = l.par_chunks(2).map(|c| hh(&[&c[0], &c[1]])).collect();
            levels.push(next);
        }
        Merkle { levels }
    }
    pub fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }
    pub fn path(&self, mut j: usize) -> Vec<[u8; 32]> {
        let mut out = Vec::new();
        for l in &self.levels[..self.levels.len() - 1] {
            out.push(l[j ^ 1]);
            j /= 2;
        }
        out
    }
}

pub fn leaf(salt: &[u8], col: &[u8]) -> [u8; 32] {
    hh(&[b"leaf", salt, col])
}

pub fn mverify(root: &[u8], colb: &[u8], salt: &[u8], mut j: usize, path: &[&[u8]]) -> bool {
    let mut h = leaf(salt, colb);
    for sib in path {
        h = if j % 2 == 0 { hh(&[&h, sib]) } else { hh(&[sib, &h]) };
        j /= 2;
    }
    h[..] == *root
}
