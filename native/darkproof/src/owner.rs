//! owner_sig.py: the data owner's hash-based signature (Lamport one-time keys under a Merkle tree, durable leaf
//! counter) and the batch message it signs.
use crate::h::{Hash, Py};
use crate::Ctx;
use rayon::prelude::*;
use sha2::{Digest, Sha256};

fn h(parts: &[&[u8]]) -> Hash {
    let mut m = Sha256::new();
    for p in parts {
        m.update(p);
    }
    m.finalize().into()
}

pub struct Owner {
    pub h: usize,
    pub seed: Vec<u8>,
    tree: Vec<Vec<Hash>>,
    pub pk: Hash,
    pub next_leaf: u64,
    state_path: Option<std::path::PathBuf>,
}

impl Owner {
    /// seed None: 32 bytes from the OS; `det_seed(seed, k)` gives the harness's deterministic k-th owner.
    pub fn new(h_: usize, seed: Option<Vec<u8>>, state_path: Option<std::path::PathBuf>) -> Self {
        let seed = seed.unwrap_or_else(|| crate::rng::secret_bytes(32));
        let leaves: Vec<Hash> = (0..1u64 << h_).into_par_iter().map(|i| pkhash(&seed, i)).collect();
        let mut tree = vec![leaves];
        while tree.last().unwrap().len() > 1 {
            let l = tree.last().unwrap();
            let nx: Vec<Hash> = l.chunks(2).map(|c| h(&[&c[0], &c[1]])).collect();
            tree.push(nx);
        }
        let pk = tree.last().unwrap()[0];
        let mut next_leaf = 0;
        if let Some(p) = &state_path {
            if let Ok(s) = std::fs::read_to_string(p) {
                next_leaf = s.trim().parse().expect("owner state");
            }
        }
        Owner { h: h_, seed, tree, pk, next_leaf, state_path }
    }

    pub fn sign(&mut self, msg: &[u8]) -> Result<Vec<u8>, String> {
        let leaf = self.next_leaf;
        if leaf >= 1 << self.h {
            return Err("owner key tree exhausted: rotate the owner key (a ledger event)".into());
        }
        self.next_leaf = leaf + 1;
        if let Some(p) = &self.state_path {
            let tmp = p.with_extension("tmp");
            {
                use std::io::Write;
                let mut f = std::fs::File::create(&tmp).map_err(|e| e.to_string())?;
                f.write_all(self.next_leaf.to_string().as_bytes()).map_err(|e| e.to_string())?;
                f.sync_all().map_err(|e| e.to_string())?;
            }
            std::fs::rename(&tmp, p).map_err(|e| e.to_string())?;
        }
        let dig = h(&[msg]);
        let sk = sk(&self.seed, leaf);
        let mut out = (leaf as u32).to_be_bytes().to_vec();
        let bits: Vec<usize> = (0..256).map(|j| ((dig[j / 8] >> (7 - j % 8)) & 1) as usize).collect();
        for (j, &b) in bits.iter().enumerate() {
            out.extend_from_slice(&sk[b][j]);
        }
        for (j, &b) in bits.iter().enumerate() {
            out.extend_from_slice(&h(&[&sk[1 - b][j]]));
        }
        let mut k = leaf as usize;
        for lvl in &self.tree[..self.tree.len() - 1] {
            out.extend_from_slice(&lvl[k ^ 1]);
            k /= 2;
        }
        Ok(out)
    }
}

/// owner_sig._det_seed: sha256("dl-proof|<seed>|owner|<k>").
pub fn det_seed(seed: &str, k: u64) -> Vec<u8> {
    h(&[format!("dl-proof|{seed}|owner|{k}").as_bytes()]).to_vec()
}

fn sk(seed: &[u8], i: u64) -> [Vec<Hash>; 2] {
    let one = |b: u64| -> Vec<Hash> {
        (0..256u64)
            .map(|j| h(&[seed, i.to_string().as_bytes(), b.to_string().as_bytes(), j.to_string().as_bytes()]))
            .collect()
    };
    [one(0), one(1)]
}

fn pkhash(seed: &[u8], i: u64) -> Hash {
    let s = sk(seed, i);
    let mut m = Sha256::new();
    for b in 0..2 {
        for x in &s[b] {
            m.update(h(&[x]));
        }
    }
    m.finalize().into()
}

pub fn sig_len(h_: usize) -> usize {
    4 + 32 * (512 + h_)
}

pub fn sig_leaf(sig: &[u8]) -> u64 {
    u32::from_be_bytes(sig[..4].try_into().unwrap()) as u64
}

pub fn verify(pk: &Hash, h_: usize, min_leaf: u64, msg: &[u8], sig: &[u8]) -> bool {
    if sig.len() != sig_len(h_) {
        return false;
    }
    let leaf = sig_leaf(sig);
    if leaf < min_leaf || leaf >= 1 << h_ {
        return false;
    }
    let at = |j: usize| &sig[4 + 32 * j..36 + 32 * j];
    let dig = h(&[msg]);
    let mut node = Sha256::new();
    let mut halves: [Vec<Hash>; 2] = [vec![[0; 32]; 256], vec![[0; 32]; 256]];
    for j in 0..256 {
        let b = ((dig[j / 8] >> (7 - j % 8)) & 1) as usize;
        halves[b][j] = h(&[at(j)]);
        halves[1 - b][j].copy_from_slice(at(256 + j));
    }
    for b in 0..2 {
        for x in &halves[b] {
            node.update(x);
        }
    }
    let mut nd: Hash = node.finalize().into();
    let mut k = leaf;
    for j in 0..h_ {
        let sib = at(512 + j);
        nd = if k % 2 == 0 { h(&[&nd, sib]) } else { h(&[sib, &nd]) };
        k /= 2;
    }
    &nd == pk
}

/// batch_message: H("dark-learning batch", tuple(ctx), tuple(roots_x), tuple(roots_y)) as raw digest bytes.
pub fn batch_message(ctx: &Ctx, rx: &[Hash], ry: &[Hash]) -> Hash {
    let mut p = Py::new();
    p.s("dark-learning batch").ctx(ctx).tuple_hx(rx).tuple_hx(ry);
    p.done()
}
