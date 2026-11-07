//! cosnark.SharePCS as cosnark_zk.ZKPCS uses it (layer-1 hiding: secret tails and one proximity mask row per life),
//! split per custodian: `PcsParty` is ONE custodian's part (its share rows, tails, mask rows, salts and Merkle
//! tree). `Shape` is cosnark_zk.PubShape: what the verifier may know. The codeword is never stored: a leaf is hashed
//! from its column, computed as dot products of the rows with the powers of the column's point, and an opened
//! column is recomputed the same way.
use crate::field;
use crate::h::{h_leaf, h_node, h_pad, Hash};
use crate::poly::powers;
use crate::rng::{salt, Det};
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
    /// the evaluation points (cosnark.domain)
    pub dom: Dom,
}

/// cosnark.domain: x_j = j + 1, or x_j = z^t omega^i with (t, i) = (j >> k, j mod 2^k): T disjoint cosets of the
/// order-2^k subgroup, each in natural NTT order.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Dom {
    Int,
    Coset { k: u32, t: usize, omega: u64, z: u64 },
}

/// cosnark.coset_params: k minimising T (2^(k-1) k + w) (ties to the larger k), omega = h^((p-1)/2^k) for the least
/// non-residue h >= 2, z the least a >= 2 with a^t outside the subgroup for 0 < t < T.
pub fn coset_params(npts: usize, w: usize) -> Dom {
    let p = field::p();
    let s = (p - 1).trailing_zeros();
    let mut best: Option<(usize, u32, usize)> = None;
    for k in 1..=s {
        let t = npts.div_ceil(1usize << k);
        let cost = t * ((1usize << (k - 1)) * k as usize + w);
        if best.map_or(true, |b| cost <= b.0) {
            best = Some((cost, k, t));
        }
    }
    let (_, k, t) = best.unwrap();
    let mut h = 2u64;
    while field::pow(h, (p - 1) / 2) != p - 1 {
        h += 1;
    }
    let omega = field::pow(h, (p - 1) >> k);
    let mut z = 2u64;
    while (1..t).any(|tt| field::pow(z, (tt as u64) << k) == 1) {
        z += 1;
    }
    Dom::Coset { k, t, omega, z }
}

impl Dom {
    pub fn point(&self, j: usize) -> u64 {
        match *self {
            Dom::Int => (j + 1) as u64,
            Dom::Coset { k, omega, z, .. } => {
                field::mul(field::pow(z, (j >> k) as u64), field::pow(omega, (j & ((1usize << k) - 1)) as u64))
            }
        }
    }
}

/// In-place radix-2 NTT, natural order in and out: a[i] <- sum_c a[c] omega^(c i); tw[i] = omega^i for i < n / 2.
pub fn ntt(a: &mut [u64], tw: &[u64]) {
    let n = a.len();
    let lg = n.trailing_zeros();
    for i in 0..n {
        let r = i.reverse_bits() >> (usize::BITS - lg);
        if i < r {
            a.swap(i, r);
        }
    }
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let step = n / len;
        for st in (0..n).step_by(len) {
            for j in 0..half {
                let u = a[st + j];
                let v = field::mul(a[st + j + half], tw[j * step]);
                a[st + j] = field::add(u, v);
                a[st + j + half] = field::sub(u, v);
            }
        }
        len *= 2;
    }
}

/// cosnark.row_split: the row count exponent mr of a commitment to 2^m values. Square: m / 2. Balanced: the mr in 0..m
/// minimising T K (2^mr + nmask) + (2^(m - mr) + hide) (K + T) (an opening's column values, plus its proximity row and
/// one evaluation's Ligero rows, per custodian); ties to the smaller mr.
pub fn row_split(pr: &Profile, m: usize) -> usize {
    match pr.split {
        crate::Split::Square => m / 2,
        crate::Split::Balanced => {
            let (t, k) = (pr.t_cols as u128, pr.k_l as u128);
            (0..=m)
                .min_by_key(|&r| (t * k * ((1u128 << r) + pr.nmask as u128) + ((1u128 << (m - r)) + pr.hide as u128) * (k + t), r))
                .unwrap()
        }
    }
}

impl Shape {
    pub fn new(pr: &Profile, m: usize, base: usize) -> Self {
        let mr = row_split(pr, m);
        let mc = m - mr;
        let (rd, c) = (1usize << mr, 1usize << mc);
        let nmask = pr.nmask;
        let w = c + pr.hide;
        let npts = pr.blow * w;
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
            npts,
            dom: match pr.domain {
                crate::Domain::Int => Dom::Int,
                crate::Domain::Coset => coset_params(npts, w),
            },
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
    /// This life's proximity mask rows for F_{p^E} weights: the last E rows of its block, one per component
    /// (E = 1: [prox_row()]).
    pub fn prox_rows_e(&self, e: usize) -> Vec<usize> {
        (0..e).map(|k| self.rd + self.base + self.block - e + k).collect()
    }
    pub fn prox_len_e(&self, e: usize) -> usize {
        self.r - if self.nmask > 0 { e } else { 0 }
    }
    /// gam (prox_len_e elements) with this life's k-th proximity mask row given the unit u^k, so each component of
    /// the revealed combination is masked by its own uniform row.
    pub fn prox_weights_e<const E: usize>(&self, gam: Vec<[u64; E]>) -> Vec<[u64; E]> {
        let mut g = gam;
        if self.nmask > 0 {
            for (k, r) in self.prox_rows_e(E).into_iter().enumerate() {
                let mut u = [0u64; E];
                u[k] = 1;
                g.insert(r, u);
            }
        }
        g
    }
    /// ZKPCS.eval_weights_e: eq(pt[mc:]) on the data rows, 0 on the mask rows.
    pub fn eval_weights_e<const E: usize>(&self, pt: &[[u64; E]]) -> Vec<[u64; E]> {
        let mut a = crate::ext::eqv(&pt[self.mc..]);
        a.resize(a.len() + self.nmask, [0; E]);
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

#[derive(Clone)]
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
    /// the codeword, column-major (npts x R), kept for the coset domain (built by NTT; openings read it)
    pub cw: Vec<u64>,
}

#[derive(Debug)]
pub struct LifeExhausted(pub String);

impl PcsParty {
    /// Party `i`'s part of a commitment to the vector whose share it holds (`share`, length 2^m).
    pub fn commit(pr: &Profile, share: &[u64], label: &str, i: usize, det: &Det) -> Self {
        let m = bitlen(share.len() - 1);
        assert_eq!(share.len(), 1 << m);
        let shape = Shape::new(pr, m, 0);
        let rng = if det.on() {
            det.coins(&[
                "pcs",
                label,
                &i.to_string(),
                &shape.hide.to_string(),
                &shape.nmask.to_string(),
                &crate::h::h_list_hex(share),
            ])
        } else {
            crate::rng::secret_coins()
        };
        Self::commit_with(pr, share, label, rng)
    }

    /// A commitment to a PUBLIC share (the public genesis): its tails, mask rows and salts are public coins keyed by
    /// the share's hash alone, so anyone recomputes the root, and equal shares give equal commitments.
    pub fn commit_public(pr: &Profile, share: &[u64], label: &str) -> Self {
        let rng = crate::rng::public_coins(&["dl-public-genesis", &crate::h::h_list_hex(share)]);
        Self::commit_with(pr, share, label, rng)
    }

    fn commit_with(pr: &Profile, share: &[u64], label: &str, mut rng: crate::rng::Coins) -> Self {
        let m = bitlen(share.len() - 1);
        assert_eq!(share.len(), 1 << m);
        let shape = Shape::new(pr, m, 0);
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
            (0..shape.npts).map(|_| salt(&mut rng)).collect();
        let mut me = PcsParty {
            label: label.to_string(),
            shape,
            ext,
            salts,
            tree: Vec::new(),
            root: [0; 32],
            opened_lives: 0,
            max_lives: pr.lives,
            cw: Vec::new(),
        };
        me.build_tree();
        me
    }

    pub fn column(&self, j: usize) -> Vec<u64> {
        let s = &self.shape;
        if !self.cw.is_empty() {
            return self.cw[j * s.r..(j + 1) * s.r].to_vec();
        }
        let pw = powers(s.dom.point(j), s.w);
        (0..s.r).map(|r| field::dot(&self.ext[r * s.w..(r + 1) * s.w], &pw)).collect()
    }

    /// Every row's codeword on the coset domain by NTT, column-major (npts x R).
    fn encode_coset(&self) -> Vec<u64> {
        let s = &self.shape;
        let Dom::Coset { k, t, omega, z } = s.dom else { unreachable!() };
        let n = 1usize << k;
        let tw = powers(omega, n / 2);
        // per coset: the scaling c^c (c = z^tt) of the row's coefficients, shared by every row
        let scale: Vec<Vec<u64>> = (0..t).map(|tt| powers(field::pow(z, tt as u64), s.w)).collect();
        let (r, w, npts) = (s.r, s.w, s.npts);
        // blocks of 64 rows: each block's codewords are encoded into a small buffer, then written into its own
        // (disjoint) slots of the column-major codeword, so the only large allocation is the codeword itself
        const B: usize = 64;
        let mut cw = vec![0u64; npts * r];
        struct Out(*mut u64);
        unsafe impl Send for Out {}
        unsafe impl Sync for Out {}
        let out = Out(cw.as_mut_ptr());
        let out = &out;
        (0..r.div_ceil(B)).into_par_iter().for_each(|blk| {
            let r0 = blk * B;
            let nb = B.min(r - r0);
            let mut rows = vec![0u64; nb * npts];
            let mut buf = vec![0u64; n];
            for (dr, dst) in rows.chunks_mut(npts).enumerate() {
                let row = &self.ext[(r0 + dr) * w..(r0 + dr + 1) * w];
                for (tt, sc) in scale.iter().enumerate() {
                    buf.iter_mut().for_each(|x| *x = 0);
                    for (c, (&a, &f)) in row.iter().zip(sc).enumerate() {
                        let b = &mut buf[c & (n - 1)];
                        *b = field::add(*b, field::mul(a, f));
                    }
                    ntt(&mut buf, &tw);
                    let lo = tt * n;
                    if lo < npts {
                        let hi = (lo + n).min(npts);
                        dst[lo..hi].copy_from_slice(&buf[..hi - lo]);
                    }
                }
            }
            for j in 0..npts {
                for dr in 0..nb {
                    // SAFETY: entry (j, r0 + dr) belongs to this block alone, and cw outlives the loop
                    unsafe { *out.0.add(j * r + r0 + dr) = rows[dr * npts + j] };
                }
            }
        });
        cw
    }

    /// Rows r0..r0 + nb encoded on the coset domain, row-major (nb x npts).
    fn encode_rows(&self, r0: usize, nb: usize) -> Vec<u64> {
        let s = &self.shape;
        let Dom::Coset { k, t, omega, z } = s.dom else { unreachable!() };
        let n = 1usize << k;
        let tw = powers(omega, n / 2);
        let scale: Vec<Vec<u64>> = (0..t).map(|tt| powers(field::pow(z, tt as u64), s.w)).collect();
        let (w, npts) = (s.w, s.npts);
        let mut rows = vec![0u64; nb * npts];
        rows.par_chunks_mut(npts).enumerate().for_each(|(dr, dst)| {
            let row = &self.ext[(r0 + dr) * w..(r0 + dr + 1) * w];
            let mut buf = vec![0u64; n];
            for (tt, sc) in scale.iter().enumerate() {
                buf.iter_mut().for_each(|x| *x = 0);
                for (c, (&a, &f)) in row.iter().zip(sc).enumerate() {
                    let b = &mut buf[c & (n - 1)];
                    *b = field::add(*b, field::mul(a, f));
                }
                ntt(&mut buf, &tw);
                let lo = tt * n;
                if lo < npts {
                    let hi = (lo + n).min(npts);
                    dst[lo..hi].copy_from_slice(&buf[..hi - lo]);
                }
            }
        });
        rows
    }

    /// Hold the coset codeword (R npts words) from the commitment to its first opening only when it is at most
    /// DP_CW_HOLD_MB (default 1024) MiB; a larger one is streamed: the leaves are hashed block by block of rows, and
    /// an opening re-encodes the rows to read its columns. Same bytes either way.
    fn hold_cw(&self) -> bool {
        let lim: usize = std::env::var("DP_CW_HOLD_MB").ok().and_then(|v| v.parse().ok()).unwrap_or(1024);
        self.shape.r * self.shape.npts * 8 <= lim << 20
    }

    /// The leaves of the coset codeword, streamed over blocks of rows (h_leaf = H("leaf", salt, column) with the
    /// column fed in row order), never holding the codeword.
    fn stream_leaves(&self) -> Vec<Hash> {
        let (r, npts) = (self.shape.r, self.shape.npts);
        let b = stream_rows(npts);
        let mut st: Vec<crate::h::Py> = self
            .salts
            .iter()
            .map(|sa| {
                let mut h = crate::h::Py::new();
                h.s("leaf").hx(sa).raw(b"[");
                h
            })
            .collect();
        for r0 in (0..r).step_by(b) {
            let nb = b.min(r - r0);
            let rows = self.encode_rows(r0, nb);
            st.par_iter_mut().enumerate().for_each(|(j, h)| {
                for dr in 0..nb {
                    if r0 + dr > 0 {
                        h.raw(b", ");
                    }
                    h.int(rows[dr * npts + j]);
                }
            });
        }
        st.into_par_iter()
            .map(|mut h| {
                h.raw(b"]");
                h.done()
            })
            .collect()
    }

    /// The columns js of the coset codeword, streamed (re-encoding every row, holding only the chosen columns).
    fn stream_columns(&self, js: &[usize]) -> Vec<Vec<u64>> {
        let (r, npts) = (self.shape.r, self.shape.npts);
        let b = stream_rows(npts);
        let mut cols = vec![Vec::with_capacity(r); js.len()];
        for r0 in (0..r).step_by(b) {
            let nb = b.min(r - r0);
            let rows = self.encode_rows(r0, nb);
            cols.par_iter_mut().zip(js.par_iter()).for_each(|(c, &j)| {
                for dr in 0..nb {
                    c.push(rows[dr * npts + j]);
                }
            });
        }
        cols
    }

    fn build_tree(&mut self) {
        let npts = self.shape.npts;
        let coset = matches!(self.shape.dom, Dom::Coset { .. });
        let mut level: Vec<Hash> = if coset && !self.hold_cw() {
            self.cw = Vec::new();
            self.stream_leaves()
        } else {
            if coset {
                self.cw = self.encode_coset();
            }
            (0..npts).into_par_iter().map(|j| h_leaf(&self.salts[j], &self.column(j))).collect()
        };
        let full = 1usize << bitlen(npts - 1);
        for j in 0..full - npts {
            level.push(h_pad(j as u64));
        }
        self.tree = merkle_levels(level);
        self.root = self.tree.last().unwrap()[0];
    }

    /// The openings of columns js. On the coset domain the codeword is held from the commitment until its first
    /// opening and released after it (memory: R npts per commitment); a later life re-encodes it once.
    pub fn open_batch(&mut self, js: &[usize]) -> Vec<Opening> {
        if matches!(self.shape.dom, Dom::Coset { .. }) && self.cw.is_empty() && !self.hold_cw() {
            let cols = self.stream_columns(js);
            return cols.into_iter().zip(js).map(|(c, &j)| (c, auth_path(&self.tree, &self.salts[j], j))).collect();
        }
        if matches!(self.shape.dom, Dom::Coset { .. }) && self.cw.is_empty() {
            self.cw = self.encode_coset();
        }
        let out: Vec<Opening> = js.par_iter().map(|&j| self.open(j)).collect();
        self.cw = Vec::new();
        out
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

    /// row_combo_e: sum_r a_r row_r for F_{p^E} weights, as E component rows (each length W).
    pub fn row_combo_e<const E: usize>(&self, a: &[[u64; E]]) -> Vec<Vec<u64>> {
        (0..E).map(|k| self.row_combo(&a.iter().map(|w| w[k]).collect::<Vec<_>>())).collect()
    }

    /// The party's share of u_e at an F_{p^E} point (E component rows) and of Y_e = <u_e[:C], eq(pt[:mc])>.
    pub fn eval_share_e<const E: usize>(&self, pt: &[[u64; E]]) -> (Vec<Vec<u64>>, [u64; E]) {
        let a = self.shape.eval_weights_e(pt);
        let u = self.row_combo_e(&a);
        let b = crate::ext::eqv(&pt[..self.shape.mc]);
        let ue: Vec<[u64; E]> = (0..self.shape.c)
            .map(|c| {
                let mut v = [0u64; E];
                for k in 0..E {
                    v[k] = u[k][c];
                }
                v
            })
            .collect();
        (u, crate::ext::dot(&ue, &b))
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
                let rhs = crate::poly::peval(&gsum, s.dom.point(j));
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

/// pcs_verify with F_{p^E} proximity weights: each custodian's proximity row is the E components of its combination
/// concatenated (length E W); every component is tested at every opened column.
#[allow(clippy::too_many_arguments)]
pub fn verify_e<const E: usize>(
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
        let g = s.prox_weights_e::<E>(crate::ext::chal::<E>(tr, s.prox_len_e(E)));
        gams.push(g);
        let px = &prox[ki];
        if px.len() != n || px.iter().any(|g| g.len() != E * s.w) {
            return Err(format!("proximity combination of the wrong shape ({k})"));
        }
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
        let gsum: Vec<Vec<u64>> = (0..E)
            .map(|kk| (0..s.w).map(|c| prox[ki].iter().fold(0u64, |a, g| field::add(a, g[kk * s.w + c]))).collect())
            .collect();
        let gam: Vec<Vec<u64>> = (0..E).map(|kk| gams[ki].iter().map(|g| g[kk]).collect()).collect();
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
                let x = s.dom.point(j);
                for kk in 0..E {
                    let m = s.r.min(gam[kk].len());
                    if field::dot(&gam[kk][..m], &colsum[..m]) != crate::poly::peval(&gsum[kk], x) {
                        return Some(format!("proximity test fails ({k})"));
                    }
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

/// Rows per streamed block: a 64 MiB buffer of encoded rows (balanced shapes have few, long rows), at least one.
fn stream_rows(npts: usize) -> usize {
    ((64usize << 20) / (8 * npts)).max(1)
}

/// A carry checkpoint (secret: the share rows, tails, mask rows and salts): the child commitments a custodian carries
/// into its next step, written so a resumed custodian process can prove that step. Format: b"DLCARRY1", u32 LE count,
/// then per entry (in key order): key, label (u32 LE length + bytes each), m, base, opened_lives, max_lives (u32 LE),
/// ext (u64 LE count + u64 LE words), salts (u32 LE count + 32 bytes each), root (32 bytes). read_carry rebuilds each
/// tree (and the coset codeword) from ext and salts and refuses a root that differs.
pub fn write_carry(carry: &std::collections::BTreeMap<String, PcsParty>, out: &mut impl std::io::Write) -> std::io::Result<()> {
    let u32w = |o: &mut dyn std::io::Write, v: usize| o.write_all(&(v as u32).to_le_bytes());
    out.write_all(b"DLCARRY1")?;
    u32w(out, carry.len())?;
    for (k, c) in carry {
        for s in [k, &c.label] {
            u32w(out, s.len())?;
            out.write_all(s.as_bytes())?;
        }
        for v in [c.shape.m, c.shape.base, c.opened_lives, c.max_lives] {
            u32w(out, v)?;
        }
        out.write_all(&(c.ext.len() as u64).to_le_bytes())?;
        let mut buf = Vec::with_capacity(8 * c.ext.len());
        for x in &c.ext {
            buf.extend_from_slice(&x.to_le_bytes());
        }
        out.write_all(&buf)?;
        u32w(out, c.salts.len())?;
        for s in &c.salts {
            out.write_all(s)?;
        }
        out.write_all(&c.root)?;
    }
    out.flush()
}

/// Read a carry checkpoint (write_carry) under profile `pr`; every root is recomputed and must equal the stored one.
pub fn read_carry(inp: &mut impl std::io::Read, pr: &Profile) -> Result<std::collections::BTreeMap<String, PcsParty>, String> {
    let e = |x: std::io::Error| format!("carry checkpoint: {x}");
    let mut b4 = [0u8; 4];
    let mut rd32 = |i: &mut dyn std::io::Read| -> Result<usize, String> {
        i.read_exact(&mut b4).map_err(e)?;
        Ok(u32::from_le_bytes(b4) as usize)
    };
    let mut magic = [0u8; 8];
    inp.read_exact(&mut magic).map_err(e)?;
    if &magic != b"DLCARRY1" {
        return Err("carry checkpoint: bad magic".into());
    }
    let n = rd32(inp)?;
    let mut out = std::collections::BTreeMap::new();
    for _ in 0..n {
        let mut strs = Vec::new();
        for _ in 0..2 {
            let l = rd32(inp)?;
            if l > 64 {
                return Err("carry checkpoint: name too long".into());
            }
            let mut s = vec![0u8; l];
            inp.read_exact(&mut s).map_err(e)?;
            strs.push(String::from_utf8(s).map_err(|_| "carry checkpoint: name not utf-8")?);
        }
        let (m, base, opened_lives, max_lives) = (rd32(inp)?, rd32(inp)?, rd32(inp)?, rd32(inp)?);
        if m > 40 {
            return Err("carry checkpoint: m out of range".into());
        }
        // DEFER: a carried W (key W1, W2) has one life (Profile::w_life)
        let shape = if pr.defer && strs[0].starts_with('W') { Shape::new(&pr.w_life(), m, base) } else { Shape::new(pr, m, base) };
        let mut b8 = [0u8; 8];
        inp.read_exact(&mut b8).map_err(e)?;
        let ne = u64::from_le_bytes(b8) as usize;
        if ne != shape.r * shape.w {
            return Err(format!("carry checkpoint: {} holds {ne} words, its shape {}", strs[0], shape.r * shape.w));
        }
        let mut raw = vec![0u8; 8 * ne];
        inp.read_exact(&mut raw).map_err(e)?;
        let ext: Vec<u64> = raw.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        drop(raw);
        if ext.iter().any(|&x| x >= field::p()) {
            return Err("carry checkpoint: a word is not a field element".into());
        }
        let ns = rd32(inp)?;
        if ns != shape.npts {
            return Err("carry checkpoint: salt count differs from the shape".into());
        }
        let mut salts = vec![[0u8; 32]; ns];
        for s in salts.iter_mut() {
            inp.read_exact(s).map_err(e)?;
        }
        let mut root = [0u8; 32];
        inp.read_exact(&mut root).map_err(e)?;
        let mut c = PcsParty { label: strs[1].clone(), shape, ext, salts, tree: Vec::new(), root: [0; 32], opened_lives, max_lives, cw: Vec::new() };
        c.build_tree();
        if c.root != root {
            return Err(format!("carry checkpoint: {}'s recomputed root differs from the stored one", strs[0]));
        }
        out.insert(strs[0].clone(), c);
    }
    let mut rest = [0u8; 1];
    if inp.read(&mut rest).map_err(e)? != 0 {
        return Err("carry checkpoint: trailing bytes".into());
    }
    Ok(out)
}
