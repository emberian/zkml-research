//! cosnark.SharePCS as cosnark_zk.ZKPCS uses it (layer-1 hiding: secret tails and one proximity mask row per life),
//! split per custodian: `PcsParty` is ONE custodian's part (its share rows, tails, mask rows, salts and Merkle
//! tree). `Shape` is cosnark_zk.PubShape: what the verifier may know. The codeword is never stored: a leaf is hashed
//! from its column, computed as dot products of the rows with the powers of the column's point, and an opened
//! column is recomputed the same way.
use crate::field;
use crate::h::{h_leaf, h_node, h_pad, Hash};
use crate::poly::powers;
use crate::rng::{salt, secret_rng, Det};
use crate::transcript::{eqv, Transcript};
use crate::Profile;
use rayon::prelude::*;

#[derive(Clone, Debug, PartialEq)]
pub struct Shape {
    pub m: usize,
    pub mr: usize,
    pub mc: usize,
    pub rd: usize,
    pub c: usize,
    pub nmask: usize,
    pub hide: usize,
    pub r: usize,
    pub block: usize,
    pub base: usize,
    pub w: usize,
    pub npts: usize,
}

impl Shape {
    pub fn new(pr: &Profile, m: usize, base: usize) -> Self {
        let (mr, mc) = (m / 2, m - m / 2);
        let (rd, c) = (1usize << mr, 1usize << mc);
        let nmask = pr.nmask;
        let w = c + pr.hide;
        Shape {
            m,
            mr,
            mc,
            rd,
            c,
            nmask,
            hide: pr.hide,
            r: rd + nmask,
            block: if nmask > 0 { nmask / pr.lives } else { 0 },
            base,
            w,
            npts: pr.blow * w,
        }
    }
    pub fn prox_row(&self) -> usize {
        self.rd + self.base + self.block - 1
    }
    pub fn prox_len(&self) -> usize {
        self.r - if self.nmask > 0 { 1 } else { 0 }
    }
    pub fn prox_weights(&self, gam: Vec<u64>) -> Vec<u64> {
        if self.nmask == 0 {
            return gam;
        }
        let mut g = gam;
        g.insert(self.prox_row(), 1);
        g
    }
    /// ZKPCS.eval_weights: eq(pt[mc:]) on the data rows, 0 on the mask rows.
    pub fn eval_weights(&self, pt: &[u64]) -> Vec<u64> {
        let mut a = eqv(&pt[self.mc..]);
        a.resize(a.len() + self.nmask, 0);
        a
    }
    /// path length: salt + (levels - 1) siblings.
    pub fn path_len(&self) -> usize {
        bitlen(self.npts - 1) + 1
    }
}

pub fn bitlen(x: usize) -> usize {
    (usize::BITS - x.leading_zeros()) as usize
}

pub type Opening = (Vec<u64>, Vec<Hash>);

pub struct PcsParty {
    pub label: String,
    pub shape: Shape,
    /// R x W, row-major: data rows (share + tails), then mask rows
    pub ext: Vec<u64>,
    pub salts: Vec<Hash>,
    pub tree: Vec<Vec<Hash>>,
    pub root: Hash,
    pub opened_lives: usize,
    pub max_lives: usize,
}

#[derive(Debug)]
pub struct LifeExhausted(pub String);

impl PcsParty {
    /// Party `i`'s part of a commitment to the vector whose share it holds (`share`, length 2^m).
    pub fn commit(pr: &Profile, share: &[u64], label: &str, i: usize, det: &Det) -> Self {
        let m = bitlen(share.len() - 1);
        assert_eq!(share.len(), 1 << m);
        let shape = Shape::new(pr, m, 0);
        let mut rng = match det.on() {
            true => det
                .rng(&[
                    "pcs",
                    label,
                    &i.to_string(),
                    &shape.hide.to_string(),
                    &shape.nmask.to_string(),
                    &crate::h::h_list_hex(share),
                ])
                .unwrap(),
            false => secret_rng(),
        };
        let (w, c) = (shape.w, shape.c);
        let mut ext = vec![0u64; shape.r * w];
        for r in 0..shape.rd {
            ext[r * w..r * w + c].copy_from_slice(&share[r * c..(r + 1) * c]);
            for k in c..w {
                ext[r * w + k] = rng.randrange_u64(field::p());
            }
        }
        for r in shape.rd..shape.r {
            for k in 0..w {
                ext[r * w + k] = rng.randrange_u64(field::p());
            }
        }
        let salts: Vec<Hash> =
            (0..shape.npts).map(|_| salt(if det.on() { Some(&mut rng) } else { None })).collect();
        let mut me = PcsParty {
            label: label.to_string(),
            shape,
            ext,
            salts,
            tree: Vec::new(),
            root: [0; 32],
            opened_lives: 0,
            max_lives: pr.lives,
        };
        me.build_tree();
        me
    }

    pub fn column(&self, j: usize) -> Vec<u64> {
        let s = &self.shape;
        let pw = powers((j + 1) as u64, s.w);
        (0..s.r).map(|r| field::dot(&self.ext[r * s.w..(r + 1) * s.w], &pw)).collect()
    }

    fn build_tree(&mut self) {
        let npts = self.shape.npts;
        let mut level: Vec<Hash> = (0..npts).into_par_iter().map(|j| h_leaf(&self.salts[j], &self.column(j))).collect();
        let full = 1usize << bitlen(npts - 1);
        for j in 0..full - npts {
            level.push(h_pad(j as u64));
        }
        self.tree = merkle_levels(level);
        self.root = self.tree.last().unwrap()[0];
    }

    pub fn open(&self, j: usize) -> Opening {
        (self.column(j), auth_path(&self.tree, &self.salts[j], j))
    }

    /// row_combo(i, a): sum_r a[r] ext[r] (length W).
    pub fn row_combo(&self, a: &[u64]) -> Vec<u64> {
        let s = &self.shape;
        let mut out = vec![0u64; s.w];
        out.par_chunks_mut(1024).enumerate().for_each(|(blk, o)| {
            for (cc, slot) in o.iter_mut().enumerate() {
                let c = blk * 1024 + cc;
                let mut acc = 0u64;
                let mut sacc = 0u128;
                for r in 0..s.r {
                    sacc += a[r] as u128 * self.ext[r * s.w + c] as u128;
                    if r % 32 == 31 {
                        acc = field::add(acc, field::red(sacc));
                        sacc = 0;
                    }
                }
                *slot = field::add(acc, field::red(sacc));
            }
        });
        out
    }

    /// The party's share of the evaluation row combination u_e at point pt, and of Y_e = <u_e[:C], eq(pt[:mc])>.
    pub fn eval_share(&self, pt: &[u64]) -> (Vec<u64>, u64) {
        let a = self.shape.eval_weights(pt);
        let u = self.row_combo(&a);
        let b = eqv(&pt[..self.shape.mc]);
        let y = field::dot(&u[..self.shape.c], &b);
        (u, y)
    }

    /// Counts one opening life; refuses beyond max_lives (cosnark.LifeExhausted).
    pub fn take_life(&mut self, key: &str, lives: usize) -> Result<(), LifeExhausted> {
        self.opened_lives += 1;
        if self.shape.hide > 0 && self.opened_lives > self.max_lives {
            return Err(LifeExhausted(format!(
                "commitment {key} already opened in {lives} proofs; a further opening reveals it"
            )));
        }
        Ok(())
    }
}

pub fn merkle_levels(leaves: Vec<Hash>) -> Vec<Vec<Hash>> {
    let mut tree = vec![leaves];
    while tree.last().unwrap().len() > 1 {
        let lvl = tree.last().unwrap();
        let next: Vec<Hash> = lvl.par_chunks(2).map(|c| h_node(&c[0], &c[1])).collect();
        tree.push(next);
    }
    tree
}

pub fn auth_path(tree: &[Vec<Hash>], salt: &Hash, j: usize) -> Vec<Hash> {
    let mut out = vec![*salt];
    let mut k = j;
    for lvl in &tree[..tree.len() - 1] {
        out.push(lvl[k ^ 1]);
        k /= 2;
    }
    out
}

/// cosnark.verify_path: path = [salt, sibling, ...].
pub fn verify_path(root: &Hash, col: &[u64], j: usize, path: &[Hash]) -> bool {
    if path.is_empty() {
        return false;
    }
    let mut h = h_leaf(&path[0], col);
    let mut k = j;
    for sib in &path[1..] {
        h = if k % 2 == 0 { h_node(&h, sib) } else { h_node(sib, &h) };
        k /= 2;
    }
    &h == root
}

/// The PCS part of a ZK proof (pcs_prove with no evaluations): per commitment, every party's proximity combination
/// and opened columns.
#[derive(Clone, Debug, PartialEq)]
pub struct PcsCols {
    pub j: Vec<usize>,
    /// per party, per opened column: (column, path)
    pub open: Vec<Vec<Opening>>,
}

/// pcs_verify(sh, roots, [], [], prox, cols, tr): replays the proximity challenges and column draws, checks every
/// Merkle opening and the proximity test at every opened column. Keys in sorted order.
pub fn verify(
    pr: &Profile,
    keys: &[String],
    shapes: &[Shape],
    roots: &[Vec<Hash>],
    prox: &[Vec<Vec<u64>>],
    cols: &[PcsCols],
    tr: &mut Transcript,
    n: usize,
) -> Result<(), String> {
    let mut gams = Vec::with_capacity(keys.len());
    for (ki, k) in keys.iter().enumerate() {
        let s = &shapes[ki];
        let g = s.prox_weights(tr.chal(s.prox_len()));
        gams.push(g);
        let px = &prox[ki];
        tr.absorb(|h| {
            h.s("g").s(k).list2(px);
        });
    }
    for (ki, k) in keys.iter().enumerate() {
        let s = &shapes[ki];
        let jj = tr.distinct_cols(pr.t_cols, s.npts);
        if jj != cols[ki].j {
            return Err("column challenge mismatch".into());
        }
        let gsum: Vec<u64> =
            (0..s.w).map(|c| prox[ki].iter().fold(0u64, |a, g| field::add(a, g[c]))).collect();
        let gam = &gams[ki];
        // check in column order, Merkle paths first per column, as cosnark.pcs_verify
        let fails: Vec<Option<String>> = jj
            .par_iter()
            .enumerate()
            .map(|(t, &j)| {
                let mut colsum = vec![0u64; s.r];
                for i in 0..n {
                    let (col, path) = &cols[ki].open[i][t];
                    if !verify_path(&roots[ki][i], col, j, path) {
                        return Some(format!("Merkle opening fails ({k}, custodian {i})"));
                    }
                    for (a, &b) in colsum.iter_mut().zip(col) {
                        *a = field::add(*a, b);
                    }
                }
                let lhs = field::dot(&gam[..s.r.min(gam.len())], &colsum[..s.r.min(gam.len())]);
                let rhs = crate::poly::peval(&gsum, (j + 1) as u64);
                if lhs != rhs {
                    return Some(format!("proximity test fails ({k})"));
                }
                None
            })
            .collect();
        if let Some(Some(e)) = fails.into_iter().find(|f| f.is_some()) {
            return Err(e);
        }
    }
    Ok(())
}

/// Column sums at the opened columns (what the constraints' right-hand sides use).
pub fn colsums(c: &PcsCols, r: usize) -> Vec<Vec<u64>> {
    (0..c.j.len())
        .map(|t| {
            let mut s = vec![0u64; r];
            for party in &c.open {
                for (a, &b) in s.iter_mut().zip(&party[t].0) {
                    *a = field::add(*a, b);
                }
            }
            s
        })
        .collect()
}
