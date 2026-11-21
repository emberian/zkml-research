//! Multithreaded (`rayon`) Succinct Zero-Knowledge Coset-NTT Reed–Solomon / Ligero Matrix MLE PCS
//! over `BabyBear` (`p = 2013265921`) with `123.7`-bit `Ext4` (`X^4 - 11`) challenges and salted
//! `cSHAKE256` Merkle multiproofs (`>= 103.5` bits unconditional `[AHIV17]` `d/3` UD soundness;
//! `>= 108.7` bits `[BCIKS20]`/`2026/532` `(1 - rho)/2` UD soundness; perfect HVZK row & column masking).

use crate::ext4::{
    badd, bpow, build_eq_table_lsb_ext4, cshake256_32, intt_bb_in_place, merkle_node_cshake,
    ntt_bb_in_place, ntt_ext4_in_place, os_random_seed_32, precompute_twiddles_bb, ByteCursor,
    CShakeRng, CShakeTranscript, Ext4, G_PRIM, P, P_U32,
};
use rayon::prelude::*;

const PCS_LEAF_DOM: &[u8] = b"QW35-PCS-LEAF-V1";
const PCS_NODE_DOM: &[u8] = b"QW35-PCS-NODE-V1";

/// Parameters for the succinct `Ext4` Coset-RS Matrix MLE PCS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PcsParams {
    /// Reed–Solomon LDE blowup factor `B` (`rho = 1 / B`; default `8`).
    pub blowup: usize,
    /// Number of queried coset columns `t_cols` (default `208` -> `103.5`b AHIV17 UD, `141`b query / `109`b BCIKS20 UD).
    pub t_cols: usize,
    /// Enable zero-knowledge column tail hiding (`h_hide >= t_cols`), salted leaves, and `Ext4` eval/prox mask rows.
    pub zk: bool,
    /// Maximum number of distinct multilinear evaluation claims opened against this commitment (`1..=4`).
    pub max_evals: usize,
}

impl PcsParams {
    pub const fn default_zk(max_evals: usize) -> Self {
        Self {
            blowup: 8,
            t_cols: 208,
            zk: true,
            max_evals,
        }
    }

    pub const fn default_public(max_evals: usize) -> Self {
        Self {
            blowup: 8,
            t_cols: 208,
            zk: false,
            max_evals,
        }
    }
}

/// Public matrix & code geometry derived deterministically from `(num_vars, params)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PcsShape {
    pub m: usize,
    pub mc: usize,
    pub mr: usize,
    pub c_data: usize,
    pub r_data: usize,
    pub w_poly: usize,
    pub n_pts: usize,
    pub blowup: usize,
    pub t_cols: usize,
    pub zk: bool,
    pub max_evals: usize,
    /// Total rows per column: `r_data + (if zk { 4 * max_evals + 4 } else { 0 })`.
    pub r_total: usize,
}

impl PcsShape {
    pub fn new(m: usize, params: PcsParams) -> Self {
        assert!(params.blowup.is_power_of_two() && params.blowup >= 2);
        assert!(params.max_evals >= 1 && params.max_evals <= 8);

        // Choose `mc in 0..=m` minimizing proof bytes `t_cols * r_total * 4 + (max_evals + 1) * w_poly * 16`
        // while keeping `w_poly` a power of two with `w_poly - c_data >= t_cols` when `zk = true`.
        let mut best: Option<(usize, usize, usize)> = None;
        let mc_min = if m >= 4 { 4 } else { 0 };
        let mc_max = m.min(11);
        for mc in mc_min..=mc_max {
            let c_data = 1usize << mc;
            let r_data = 1usize << (m - mc);
            let w_poly = if params.zk {
                (c_data + params.t_cols).next_power_of_two().max(c_data * 2)
            } else {
                c_data.max(64)
            };
            let n_mask = if params.zk {
                4 * params.max_evals + 4
            } else {
                0
            };
            let r_total = r_data + n_mask;
            let wire_est = params.t_cols * r_total * 4 + (params.max_evals + 1) * w_poly * 16;
            if best.map_or(true, |b| wire_est < b.0) {
                best = Some((wire_est, mc, w_poly));
            }
        }
        let (_, mc, w_poly) = best.unwrap();
        let mr = m - mc;
        let c_data = 1usize << mc;
        let r_data = 1usize << mr;
        let n_pts = params.blowup * w_poly;
        let r_total = r_data + if params.zk { 4 * params.max_evals + 4 } else { 0 };

        Self {
            m,
            mc,
            mr,
            c_data,
            r_data,
            w_poly,
            n_pts,
            blowup: params.blowup,
            t_cols: params.t_cols.min(n_pts),
            zk: params.zk,
            max_evals: params.max_evals,
            r_total,
        }
    }

    #[inline]
    pub fn ev_mask_row_start(&self, eval_idx: usize) -> usize {
        debug_assert!(self.zk && eval_idx < self.max_evals);
        self.r_data + 4 * eval_idx
    }

    #[inline]
    pub fn prox_mask_row_start(&self) -> usize {
        debug_assert!(self.zk);
        self.r_data + 4 * self.max_evals
    }

    /// Returns `(ahiv17_d_over_3_ud_bits, bciks20_half_dist_ud_bits)` provable Unique-Decoding soundness bits
    /// over `BabyBear Ext4` (`|F| = P^4 ≈ 2^{123.69}`).
    pub fn provable_ud_soundness_bits(&self) -> (f64, f64) {
        let log_f = 4.0 * (P as f64).log2(); // 123.6907 bits
        let n = self.n_pts as f64;
        let w = self.w_poly as f64;
        let rho = w / n;

        // 1. Unconditional `[AHIV17]` Lemma 4.2 (`e = floor((n - w) / 3)` elementary unique decoding):
        let e = (self.n_pts - self.w_poly) / 3;
        let q_err_ahiv = 1.0 - ((e + 1) as f64) / n;
        let q_bits_ahiv = -(self.t_cols as f64) * q_err_ahiv.log2();
        let alg_bits_ahiv = log_f - ((e + 1) as f64).log2();
        let ahiv_bits = q_bits_ahiv.min(alg_bits_ahiv);

        // 2. Unconditional `[BCIKS20]` / `2026/532` Thm 28 (`theta = (1 - rho)/2 - eta` unique decoding):
        let half_gap = 0.5 * (1.0 - rho);
        let mut best_bciks = 0.0f64;
        for log_inv_eta in 3..=12 {
            let eta = 0.5f64.powi(log_inv_eta);
            if eta >= half_gap {
                continue;
            }
            let theta = half_gap - eta;
            let q_bits = -(self.t_cols as f64) * (1.0 - theta).log2();
            let alg_bits = log_f + eta.log2() - n.log2();
            best_bciks = best_bciks.max(q_bits.min(alg_bits));
        }

        (ahiv_bits, best_bciks)
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.m as u8);
        out.push(self.blowup.trailing_zeros() as u8);
        out.extend_from_slice(&(self.t_cols as u32).to_le_bytes());
        out.push(if self.zk { 1 } else { 0 });
        out.push(self.max_evals as u8);
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let m = cur.read_u8()? as usize;
        let lg_blow = cur.read_u8()? as u32;
        let t_cols = cur.read_u32()? as usize;
        let zk = cur.read_u8()? != 0;
        let max_evals = cur.read_u8()? as usize;
        if m > 26 || lg_blow < 1 || lg_blow > 6 || max_evals == 0 || max_evals > 8 || t_cols == 0 {
            return Err("invalid PcsShape parameters".to_string());
        }
        Ok(Self::new(
            m,
            PcsParams {
                blowup: 1usize << lg_blow,
                t_cols,
                zk,
                max_evals,
            },
        ))
    }
}

/// Deduplicated bottom-up `cSHAKE256` Merkle multiproof for sorted unique column indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleMultiProof {
    pub aux_hashes: Vec<[u8; 32]>,
}

impl MerkleMultiProof {
    pub fn build(tree_levels: &[Vec<[u8; 32]>], sorted_indices: &[usize]) -> Self {
        let mut cur_indices = sorted_indices.to_vec();
        let mut aux_hashes = Vec::new();
        for (lvl, nodes) in tree_levels.iter().take(tree_levels.len() - 1).enumerate() {
            let _ = lvl;
            let mut next_indices = Vec::with_capacity(cur_indices.len());
            let mut k = 0;
            while k < cur_indices.len() {
                let idx = cur_indices[k];
                let sib = idx ^ 1;
                if k + 1 < cur_indices.len() && cur_indices[k + 1] == sib {
                    k += 2;
                } else {
                    aux_hashes.push(nodes[sib]);
                    k += 1;
                }
                next_indices.push(idx >> 1);
            }
            cur_indices = next_indices;
        }
        Self { aux_hashes }
    }

    pub fn verify(
        &self,
        expected_root: &[u8; 32],
        n_leaves: usize,
        sorted_indices: &[usize],
        leaf_hashes: &[[u8; 32]],
    ) -> bool {
        if !n_leaves.is_power_of_two()
            || sorted_indices.is_empty()
            || sorted_indices.len() != leaf_hashes.len()
        {
            return false;
        }
        for w in sorted_indices.windows(2) {
            if w[0] >= w[1] {
                return false;
            }
        }
        if *sorted_indices.last().unwrap() >= n_leaves {
            return false;
        }

        let num_levels = n_leaves.trailing_zeros() as usize;
        let mut cur_nodes: Vec<(usize, [u8; 32])> = sorted_indices
            .iter()
            .copied()
            .zip(leaf_hashes.iter().copied())
            .collect();
        let mut aux_pos = 0usize;

        for level in 0..num_levels {
            let mut next_nodes = Vec::with_capacity((cur_nodes.len() + 1) / 2);
            let mut k = 0;
            while k < cur_nodes.len() {
                let (idx, hash) = cur_nodes[k];
                let sib = idx ^ 1;
                let (left, right) = if k + 1 < cur_nodes.len() && cur_nodes[k + 1].0 == sib {
                    let sib_hash = cur_nodes[k + 1].1;
                    k += 2;
                    (hash, sib_hash)
                } else {
                    if aux_pos >= self.aux_hashes.len() {
                        return false;
                    }
                    let sib_hash = self.aux_hashes[aux_pos];
                    aux_pos += 1;
                    k += 1;
                    if (idx & 1) == 0 {
                        (hash, sib_hash)
                    } else {
                        (sib_hash, hash)
                    }
                };
                let parent = merkle_node_cshake(PCS_NODE_DOM, level as u8, (idx >> 1) as u32, &left, &right);
                next_nodes.push((idx >> 1, parent));
            }
            cur_nodes = next_nodes;
        }

        aux_pos == self.aux_hashes.len() && cur_nodes.len() == 1 && &cur_nodes[0].1 == expected_root
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.aux_hashes.len() as u32).to_le_bytes());
        for h in &self.aux_hashes {
            out.extend_from_slice(h);
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let cnt = cur.read_u32()? as usize;
        if cnt > 200_000 {
            return Err(format!("excessive multiproof aux count {cnt}"));
        }
        let mut aux_hashes = Vec::with_capacity(cnt);
        for _ in 0..cnt {
            aux_hashes.push(cur.read_arr32()?);
        }
        Ok(Self { aux_hashes })
    }
}

/// Prover-side committed state for `SuccinctExt4Pcs`.
pub struct PcsProverState {
    pub shape: PcsShape,
    pub root: [u8; 32],
    /// `[r_total * w_poly]` row-major polynomial coefficients (`deg < w_poly`).
    pub row_polys: Vec<u32>,
    /// `[r_total * w_poly]` row-major evaluations on `H_0` (`|H_0| = w_poly`).
    pub row_evals_h0: Vec<u32>,
    /// `[n_pts * r_total]` column-major codeword evaluations on disjoint coset `D = G_PRIM * H_{n_pts}`.
    pub col_codewords: Vec<u32>,
    pub salts: Vec<[u8; 16]>,
    pub tree_levels: Vec<Vec<[u8; 32]>>,
}

/// Single multilinear evaluation claim `f_mle(point) == value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MleEvalClaim {
    pub point: Vec<Ext4>,
    pub value: Ext4,
}

/// Per-claim degree-`< w_poly` `Ext4` evaluation polynomial + optional ZK inner-product mask scalar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimEvalOpening {
    pub s_mask: Ext4,
    pub u_eval_coeffs: Vec<Ext4>,
}

/// Self-contained succinct PCS opening proof (`to_bytes` / `from_bytes`, zero witness access).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsOpeningProof {
    pub shape: PcsShape,
    pub claim_openings: Vec<ClaimEvalOpening>,
    pub u_prox_coeffs: Vec<Ext4>,
    pub opened_salts: Vec<[u8; 16]>,
    /// `[t_cols * r_total]` opened column entries (`col_k` contiguous of length `r_total`).
    pub opened_cols: Vec<u32>,
    pub multiproof: MerkleMultiProof,
}

impl PcsOpeningProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.write_to(&mut out);
        out
    }

    pub fn write_to(&self, out: &mut Vec<u8>) {
        self.shape.write_to(out);
        out.extend_from_slice(&(self.claim_openings.len() as u32).to_le_bytes());
        for co in &self.claim_openings {
            if self.shape.zk {
                out.extend_from_slice(&co.s_mask.to_bytes());
            }
            for &c in &co.u_eval_coeffs {
                out.extend_from_slice(&c.to_bytes());
            }
        }
        for &c in &self.u_prox_coeffs {
            out.extend_from_slice(&c.to_bytes());
        }
        if self.shape.zk {
            for s in &self.opened_salts {
                out.extend_from_slice(s);
            }
        }
        for &v in &self.opened_cols {
            out.extend_from_slice(&v.to_le_bytes());
        }
        self.multiproof.write_to(out);
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let shape = PcsShape::read_from(cur)?;
        let num_claims = cur.read_u32()? as usize;
        if num_claims == 0 || num_claims > shape.max_evals {
            return Err(format!("invalid num_claims {num_claims} > {}", shape.max_evals));
        }
        let mut claim_openings = Vec::with_capacity(num_claims);
        for _ in 0..num_claims {
            let s_mask = if shape.zk {
                cur.read_ext4()?
            } else {
                Ext4::ZERO
            };
            let mut u_eval_coeffs = Vec::with_capacity(shape.w_poly);
            for _ in 0..shape.w_poly {
                u_eval_coeffs.push(cur.read_ext4()?);
            }
            claim_openings.push(ClaimEvalOpening {
                s_mask,
                u_eval_coeffs,
            });
        }
        let mut u_prox_coeffs = Vec::with_capacity(shape.w_poly);
        for _ in 0..shape.w_poly {
            u_prox_coeffs.push(cur.read_ext4()?);
        }
        let mut opened_salts = Vec::with_capacity(shape.t_cols);
        if shape.zk {
            for _ in 0..shape.t_cols {
                opened_salts.push(cur.read_arr16()?);
            }
        } else {
            opened_salts.resize(shape.t_cols, [0u8; 16]);
        }
        let total_cells = shape.t_cols * shape.r_total;
        let mut opened_cols = Vec::with_capacity(total_cells);
        for _ in 0..total_cells {
            opened_cols.push(cur.read_bb()?);
        }
        let multiproof = MerkleMultiProof::read_from(cur)?;
        Ok(Self {
            shape,
            claim_openings,
            u_prox_coeffs,
            opened_salts,
            opened_cols,
            multiproof,
        })
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cur = ByteCursor::new(bytes);
        let pf = Self::read_from(&mut cur)?;
        if cur.remaining() != 0 {
            return Err(format!("trailing {} bytes in PcsOpeningProof", cur.remaining()));
        }
        Ok(pf)
    }
}

#[inline]
fn hash_pcs_column(j: usize, salt: &[u8; 16], col: &[u32]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(4 + 16 + col.len() * 4);
    buf.extend_from_slice(&(j as u32).to_le_bytes());
    buf.extend_from_slice(salt);
    for &v in col {
        buf.extend_from_slice(&v.to_le_bytes());
    }
    cshake256_32(PCS_LEAF_DOM, &buf)
}

/// Commit a `2^m` basefield `Bb` table via multithreaded (`rayon`) Coset-NTT LDE and `cSHAKE256` Merkle tree.
/// If `opt_det_seed` is `None` and `params.zk == true`, draws 32 bytes from `/dev/urandom`.
pub fn commit_table_pcs(
    table: &[u32],
    params: PcsParams,
    opt_det_seed: Option<&[u8]>,
) -> PcsProverState {
    assert!(!table.is_empty() && table.len().is_power_of_two());
    let m = table.len().trailing_zeros() as usize;
    let shape = PcsShape::new(m, params);

    let base_seed: [u8; 32] = if !shape.zk {
        [0u8; 32]
    } else if let Some(s) = opt_det_seed {
        cshake256_32(b"QW35-PCS-DET-SEED-V1", s)
    } else {
        os_random_seed_32()
    };

    // 1. Build `row_evals_h0` (`r_total * w_poly`):
    //    - Data rows `0..r_data`: `c_data` witness entries + `w_poly - c_data` random hiding entries.
    //    - Mask rows `r_data..r_total` (if `zk`): `w_poly` uniform random `Bb` entries.
    let mut row_evals_h0 = vec![0u32; shape.r_total * shape.w_poly];
    row_evals_h0
        .par_chunks_mut(shape.w_poly)
        .enumerate()
        .for_each(|(r, row_dst)| {
            let mut row_seed = [0u8; 36];
            row_seed[0..32].copy_from_slice(&base_seed);
            row_seed[32..36].copy_from_slice(&(r as u32).to_le_bytes());
            let mut rng = CShakeRng::from_seed(b"QW35-PCS-ROW-MASK-V1", &row_seed);

            if r < shape.r_data {
                let src = &table[r * shape.c_data..(r + 1) * shape.c_data];
                for (dst, &v) in row_dst[..shape.c_data].iter_mut().zip(src.iter()) {
                    *dst = v % P_U32;
                }
                if shape.zk {
                    for dst in &mut row_dst[shape.c_data..] {
                        *dst = rng.next_bb();
                    }
                }
            } else {
                for dst in row_dst.iter_mut() {
                    *dst = rng.next_bb();
                }
            }
        });

    // 2. Interpolate `row_polys` on `H_0` (`INTT` of length `w_poly`) and evaluate on disjoint coset
    //    `D = G_PRIM * H_{n_pts}` (`NTT` of length `n_pts`), in `rayon` parallel across all rows!
    let inv_tw_w = precompute_twiddles_bb(shape.w_poly, true);
    let fwd_tw_n = precompute_twiddles_bb(shape.n_pts, false);
    let zeta_pows: Vec<u32> = (0..shape.w_poly)
        .map(|k| bpow(G_PRIM, k as u64))
        .collect();

    let mut row_polys = row_evals_h0.clone();
    let row_ldes: Vec<Vec<u32>> = row_polys
        .par_chunks_mut(shape.w_poly)
        .map(|poly| {
            intt_bb_in_place(poly, &inv_tw_w);
            let mut lde = vec![0u32; shape.n_pts];
            for k in 0..shape.w_poly {
                lde[k] = ((poly[k] as u64 * zeta_pows[k] as u64) % P) as u32;
            }
            ntt_bb_in_place(&mut lde, &fwd_tw_n);
            lde
        })
        .collect();

    // 3. Transpose into column-major `col_codewords` (`[n_pts * r_total]`) and hash salted `cSHAKE256` leaves.
    let mut salts = vec![[0u8; 16]; shape.n_pts];
    if shape.zk {
        let mut salt_rng = CShakeRng::from_seed(b"QW35-PCS-COL-SALTS-V1", &base_seed);
        for s in &mut salts {
            salt_rng.fill_bytes(s);
        }
    }

    let mut col_codewords = vec![0u32; shape.n_pts * shape.r_total];
    let leaves: Vec<[u8; 32]> = col_codewords
        .par_chunks_mut(shape.r_total)
        .enumerate()
        .map(|(j, col_dst)| {
            for r in 0..shape.r_total {
                col_dst[r] = row_ldes[r][j];
            }
            hash_pcs_column(j, &salts[j], col_dst)
        })
        .collect();

    // 4. Build full `cSHAKE256` Merkle tree (`rayon` parallel per level).
    let mut tree_levels = Vec::with_capacity((shape.n_pts.trailing_zeros() as usize) + 1);
    tree_levels.push(leaves);
    let mut level = 0u8;
    while tree_levels.last().unwrap().len() > 1 {
        let prev = tree_levels.last().unwrap();
        let next: Vec<[u8; 32]> = prev
            .par_chunks_exact(2)
            .enumerate()
            .map(|(idx, pair)| {
                merkle_node_cshake(PCS_NODE_DOM, level, idx as u32, &pair[0], &pair[1])
            })
            .collect();
        tree_levels.push(next);
        level += 1;
    }
    let root = tree_levels.last().unwrap()[0];

    PcsProverState {
        shape,
        root,
        row_polys,
        row_evals_h0,
        col_codewords,
        salts,
        tree_levels,
    }
}

#[inline]
fn pack_4_bb_rows_as_ext4_poly(row_polys: &[u32], w_poly: usize, start_row: usize) -> Vec<Ext4> {
    (0..w_poly)
        .map(|k| {
            Ext4([
                row_polys[(start_row) * w_poly + k],
                row_polys[(start_row + 1) * w_poly + k],
                row_polys[(start_row + 2) * w_poly + k],
                row_polys[(start_row + 3) * w_poly + k],
            ])
        })
        .collect()
}

#[inline]
fn pack_4_bb_col_as_ext4(col: &[u32], start_row: usize) -> Ext4 {
    Ext4([
        col[start_row],
        col[start_row + 1],
        col[start_row + 2],
        col[start_row + 3],
    ])
}

/// Linear combination `sum_{r=0}^{weights.len()-1} weights[r] * row_polys[r]` in `rayon` parallel over coefficients.
fn combine_bb_rows_with_ext4_weights(
    row_polys: &[u32],
    w_poly: usize,
    weights: &[Ext4],
) -> Vec<Ext4> {
    (0..w_poly)
        .into_par_iter()
        .map(|k| {
            let mut acc = [0u128; 4];
            for (r, &w) in weights.iter().enumerate() {
                let pv = row_polys[r * w_poly + k] as u128;
                acc[0] += pv * (w.0[0] as u128);
                acc[1] += pv * (w.0[1] as u128);
                acc[2] += pv * (w.0[2] as u128);
                acc[3] += pv * (w.0[3] as u128);
                if (r & 15) == 15 {
                    acc[0] %= P as u128;
                    acc[1] %= P as u128;
                    acc[2] %= P as u128;
                    acc[3] %= P as u128;
                }
            }
            Ext4([
                (acc[0] % (P as u128)) as u32,
                (acc[1] % (P as u128)) as u32,
                (acc[2] % (P as u128)) as u32,
                (acc[3] % (P as u128)) as u32,
            ])
        })
        .collect()
}

/// Open `1..=max_evals` multilinear evaluation claims against `state`, sharing ONE set of `t_cols` column openings!
pub fn open_pcs_claims(
    state: &PcsProverState,
    claims: &[MleEvalClaim],
    tr: &mut CShakeTranscript,
) -> PcsOpeningProof {
    let shape = state.shape;
    assert!(!claims.is_empty() && claims.len() <= shape.max_evals);
    tr.absorb_root(b"pcs_open_root", &state.root);
    tr.absorb_u32(b"pcs_num_claims", claims.len() as u32);

    let mut claim_openings = Vec::with_capacity(claims.len());
    for (idx, claim) in claims.iter().enumerate() {
        assert_eq!(claim.point.len(), shape.m);
        tr.absorb_ext4_slice(b"pcs_claim_pt", &claim.point);
        tr.absorb_ext4(b"pcs_claim_val", claim.value);

        let eq_col = build_eq_table_lsb_ext4(&claim.point[..shape.mc]);
        let eq_row = build_eq_table_lsb_ext4(&claim.point[shape.mc..]);

        let (s_mask, beta_zk) = if shape.zk {
            let m_row = shape.ev_mask_row_start(idx);
            let mut sm = Ext4::ZERO;
            for c in 0..shape.c_data {
                let f_ev_c = Ext4([
                    state.row_evals_h0[m_row * shape.w_poly + c],
                    state.row_evals_h0[(m_row + 1) * shape.w_poly + c],
                    state.row_evals_h0[(m_row + 2) * shape.w_poly + c],
                    state.row_evals_h0[(m_row + 3) * shape.w_poly + c],
                ]);
                sm = sm.add(f_ev_c.mul(eq_col[c]));
            }
            tr.absorb_ext4(b"pcs_s_mask", sm);
            let beta = tr.squeeze_ext4(b"pcs_beta_zk", true);
            (sm, beta)
        } else {
            (Ext4::ZERO, Ext4::ZERO)
        };

        let mut u_eval_coeffs =
            combine_bb_rows_with_ext4_weights(&state.row_polys, shape.w_poly, &eq_row);
        if shape.zk {
            let f_ev_poly =
                pack_4_bb_rows_as_ext4_poly(&state.row_polys, shape.w_poly, shape.ev_mask_row_start(idx));
            for (dst, &m_c) in u_eval_coeffs.iter_mut().zip(f_ev_poly.iter()) {
                *dst = dst.add(beta_zk.mul(m_c));
            }
        }
        tr.absorb_ext4_slice(b"pcs_u_eval", &u_eval_coeffs);
        claim_openings.push(ClaimEvalOpening {
            s_mask,
            u_eval_coeffs,
        });
    }

    // Proximity RLC over all non-prox rows (`r_data + 4 * max_evals` if `zk`, else `r_data`).
    let non_prox_rows = if shape.zk {
        shape.prox_mask_row_start()
    } else {
        shape.r_data
    };
    let gammas = tr.squeeze_ext4_vec(b"pcs_prox_gamma", non_prox_rows, false);
    let mut u_prox_coeffs =
        combine_bb_rows_with_ext4_weights(&state.row_polys, shape.w_poly, &gammas);
    if shape.zk {
        let f_prox_poly =
            pack_4_bb_rows_as_ext4_poly(&state.row_polys, shape.w_poly, shape.prox_mask_row_start());
        for (dst, &mp) in u_prox_coeffs.iter_mut().zip(f_prox_poly.iter()) {
            *dst = dst.add(mp);
        }
    }
    tr.absorb_ext4_slice(b"pcs_u_prox", &u_prox_coeffs);

    // Squeeze `t_cols` distinct sorted column indices!
    let indices = tr.squeeze_distinct_indices(b"pcs_col_queries", shape.n_pts, shape.t_cols);
    let mut opened_salts = Vec::with_capacity(shape.t_cols);
    let mut opened_cols = Vec::with_capacity(shape.t_cols * shape.r_total);
    for &j in &indices {
        opened_salts.push(state.salts[j]);
        let col = &state.col_codewords[j * shape.r_total..(j + 1) * shape.r_total];
        opened_cols.extend_from_slice(col);
    }
    let multiproof = MerkleMultiProof::build(&state.tree_levels, &indices);

    PcsOpeningProof {
        shape,
        claim_openings,
        u_prox_coeffs,
        opened_salts,
        opened_cols,
        multiproof,
    }
}

/// Standalone succinct PCS verifier (`0` access to secret witness!).
pub fn verify_pcs_claims(
    expected_root: &[u8; 32],
    expected_shape: PcsShape,
    claims: &[MleEvalClaim],
    proof: &PcsOpeningProof,
    tr: &mut CShakeTranscript,
) -> Result<(), String> {
    if proof.shape != expected_shape {
        return Err("PCS shape mismatch".to_string());
    }
    let shape = proof.shape;
    if claims.is_empty()
        || claims.len() != proof.claim_openings.len()
        || claims.len() > shape.max_evals
    {
        return Err("PCS claim count mismatch".to_string());
    }
    if proof.u_prox_coeffs.len() != shape.w_poly
        || proof.opened_salts.len() != shape.t_cols
        || proof.opened_cols.len() != shape.t_cols * shape.r_total
    {
        return Err("PCS proof array length mismatch".to_string());
    }
    if proof.opened_cols.iter().any(|&v| v >= P_U32) {
        return Err("non-canonical BabyBear value in opened column".to_string());
    }

    tr.absorb_root(b"pcs_open_root", expected_root);
    tr.absorb_u32(b"pcs_num_claims", claims.len() as u32);

    let fwd_tw_w = precompute_twiddles_bb(shape.w_poly, false);
    let fwd_tw_n = precompute_twiddles_bb(shape.n_pts, false);
    let zeta_pows: Vec<u32> = (0..shape.w_poly)
        .map(|k| bpow(G_PRIM, k as u64))
        .collect();

    let mut eq_rows = Vec::with_capacity(claims.len());
    let mut betas_zk = Vec::with_capacity(claims.len());
    let mut u_eval_ldes = Vec::with_capacity(claims.len());

    // 1. Replay per-claim transcript & check subgroup `H_0` inner-product equation:
    //    `sum_{c < c_data} u_eval(H_0[c]) * eq(z_col, c) == claim.value + beta_zk * s_mask`.
    for (idx, (claim, co)) in claims.iter().zip(proof.claim_openings.iter()).enumerate() {
        let _ = idx;
        if claim.point.len() != shape.m || co.u_eval_coeffs.len() != shape.w_poly {
            return Err("PCS claim point/poly length mismatch".to_string());
        }
        tr.absorb_ext4_slice(b"pcs_claim_pt", &claim.point);
        tr.absorb_ext4(b"pcs_claim_val", claim.value);

        let beta = if shape.zk {
            tr.absorb_ext4(b"pcs_s_mask", co.s_mask);
            tr.squeeze_ext4(b"pcs_beta_zk", true)
        } else {
            Ext4::ZERO
        };
        tr.absorb_ext4_slice(b"pcs_u_eval", &co.u_eval_coeffs);

        // Evaluate `u_eval_coeffs` on `H_0` via 1 fast `w_poly`-point `Ext4` NTT!
        let mut eval_h0 = co.u_eval_coeffs.clone();
        ntt_ext4_in_place(&mut eval_h0, &fwd_tw_w);

        let eq_col = build_eq_table_lsb_ext4(&claim.point[..shape.mc]);
        let mut lhs = Ext4::ZERO;
        for c in 0..shape.c_data {
            lhs = lhs.add(eval_h0[c].mul(eq_col[c]));
        }
        let rhs = if shape.zk {
            claim.value.add(beta.mul(co.s_mask))
        } else {
            claim.value
        };
        if lhs != rhs {
            return Err("PCS H_0 multilinear evaluation sum mismatch".to_string());
        }

        // Evaluate `u_eval_coeffs` on coset `D` via 1 `n_pts`-point `Ext4` NTT!
        let mut lde = vec![Ext4::ZERO; shape.n_pts];
        for k in 0..shape.w_poly {
            lde[k] = co.u_eval_coeffs[k].scale_bb(zeta_pows[k]);
        }
        ntt_ext4_in_place(&mut lde, &fwd_tw_n);

        eq_rows.push(build_eq_table_lsb_ext4(&claim.point[shape.mc..]));
        betas_zk.push(beta);
        u_eval_ldes.push(lde);
    }

    // 2. Replay proximity challenge & evaluate `u_prox` on coset `D`.
    let non_prox_rows = if shape.zk {
        shape.prox_mask_row_start()
    } else {
        shape.r_data
    };
    let gammas = tr.squeeze_ext4_vec(b"pcs_prox_gamma", non_prox_rows, false);
    tr.absorb_ext4_slice(b"pcs_u_prox", &proof.u_prox_coeffs);

    let indices = tr.squeeze_distinct_indices(b"pcs_col_queries", shape.n_pts, shape.t_cols);

    let mut u_prox_lde = vec![Ext4::ZERO; shape.n_pts];
    for k in 0..shape.w_poly {
        u_prox_lde[k] = proof.u_prox_coeffs[k].scale_bb(zeta_pows[k]);
    }
    ntt_ext4_in_place(&mut u_prox_lde, &fwd_tw_n);

    // 3. Verify `cSHAKE256` Merkle multiproof of all `t_cols` queried columns against `expected_root`!
    let leaf_hashes: Vec<[u8; 32]> = (0..shape.t_cols)
        .map(|qi| {
            let j = indices[qi];
            let salt = if shape.zk {
                &proof.opened_salts[qi]
            } else {
                &[0u8; 16]
            };
            let col = &proof.opened_cols[qi * shape.r_total..(qi + 1) * shape.r_total];
            hash_pcs_column(j, salt, col)
        })
        .collect();
    if !proof
        .multiproof
        .verify(expected_root, shape.n_pts, &indices, &leaf_hashes)
    {
        return Err("PCS cSHAKE256 Merkle multiproof verification failed".to_string());
    }

    // 4. Check proximity & evaluation linear-combination consistency at all `t_cols` opened columns!
    for qi in 0..shape.t_cols {
        let j = indices[qi];
        let col = &proof.opened_cols[qi * shape.r_total..(qi + 1) * shape.r_total];

        // 4a. Proximity equation at column `j`
        let mut prox_acc = [0u128; 4];
        for r in 0..non_prox_rows {
            let cv = col[r] as u128;
            let g = gammas[r];
            prox_acc[0] += cv * (g.0[0] as u128);
            prox_acc[1] += cv * (g.0[1] as u128);
            prox_acc[2] += cv * (g.0[2] as u128);
            prox_acc[3] += cv * (g.0[3] as u128);
            if (r & 15) == 15 {
                prox_acc[0] %= P as u128;
                prox_acc[1] %= P as u128;
                prox_acc[2] %= P as u128;
                prox_acc[3] %= P as u128;
            }
        }
        let mut col_prox = Ext4([
            (prox_acc[0] % (P as u128)) as u32,
            (prox_acc[1] % (P as u128)) as u32,
            (prox_acc[2] % (P as u128)) as u32,
            (prox_acc[3] % (P as u128)) as u32,
        ]);
        if shape.zk {
            col_prox = col_prox.add(pack_4_bb_col_as_ext4(col, shape.prox_mask_row_start()));
        }
        if col_prox != u_prox_lde[j] {
            return Err(format!("PCS proximity column check failed at query {qi} (col {j})"));
        }

        // 4b. Evaluation equation(s) at column `j`
        for ci in 0..claims.len() {
            let eq_r = &eq_rows[ci];
            let mut ev_acc = [0u128; 4];
            for r in 0..shape.r_data {
                let cv = col[r] as u128;
                let w = eq_r[r];
                ev_acc[0] += cv * (w.0[0] as u128);
                ev_acc[1] += cv * (w.0[1] as u128);
                ev_acc[2] += cv * (w.0[2] as u128);
                ev_acc[3] += cv * (w.0[3] as u128);
                if (r & 15) == 15 {
                    ev_acc[0] %= P as u128;
                    ev_acc[1] %= P as u128;
                    ev_acc[2] %= P as u128;
                    ev_acc[3] %= P as u128;
                }
            }
            let mut col_ev = Ext4([
                (ev_acc[0] % (P as u128)) as u32,
                (ev_acc[1] % (P as u128)) as u32,
                (ev_acc[2] % (P as u128)) as u32,
                (ev_acc[3] % (P as u128)) as u32,
            ]);
            if shape.zk {
                let f_ev_j = pack_4_bb_col_as_ext4(col, shape.ev_mask_row_start(ci));
                col_ev = col_ev.add(betas_zk[ci].mul(f_ev_j));
            }
            if col_ev != u_eval_ldes[ci][j] {
                return Err(format!(
                    "PCS evaluation column check failed on claim {ci} at query {qi} (col {j})"
                ));
            }
        }
    }

    let _ = badd(0, 0);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ext4::mle_eval_bb_at_ext4;

    #[test]
    fn test_succinct_ext4_pcs_zk_roundtrip_and_tamper_rejection() {
        let m = 16usize; // 65,536 cells
        let table: Vec<u32> = (0..(1usize << m))
            .map(|i| (((i as u64) * 31337 + 19) % P) as u32)
            .collect();
        let params = PcsParams::default_zk(2);
        let state = commit_table_pcs(&table, params, Some(b"unit-test-seed"));
        let (ahiv_bits, bciks_bits) = state.shape.provable_ud_soundness_bits();
        assert!(ahiv_bits >= 100.0 && bciks_bits >= 105.0);

        let mut pt_tr = CShakeTranscript::new(b"pts");
        let pt0 = pt_tr.squeeze_ext4_vec(b"p0", m, true);
        let pt1 = pt_tr.squeeze_ext4_vec(b"p1", m, true);
        let val0 = mle_eval_bb_at_ext4(&table, &pt0);
        let val1 = mle_eval_bb_at_ext4(&table, &pt1);
        let claims = vec![
            MleEvalClaim {
                point: pt0,
                value: val0,
            },
            MleEvalClaim {
                point: pt1,
                value: val1,
            },
        ];

        let mut prv_tr = CShakeTranscript::new(b"pcs-test");
        let proof = open_pcs_claims(&state, &claims, &mut prv_tr);
        let bytes = proof.to_bytes();
        let decoded = PcsOpeningProof::from_bytes(&bytes).expect("decode proof");

        let mut ver_tr = CShakeTranscript::new(b"pcs-test");
        verify_pcs_claims(&state.root, state.shape, &claims, &decoded, &mut ver_tr)
            .expect("honest succinct ZK PCS proof must verify");

        // Falsifier 1: forged evaluation claim
        let mut bad_claims = claims.clone();
        bad_claims[0].value = bad_claims[0].value.add(Ext4::ONE);
        let mut ver_tr2 = CShakeTranscript::new(b"pcs-test");
        assert!(verify_pcs_claims(&state.root, state.shape, &bad_claims, &decoded, &mut ver_tr2).is_err());

        // Falsifier 2: forged opened column cell
        let mut bad_pf = decoded.clone();
        bad_pf.opened_cols[0] = (bad_pf.opened_cols[0] + 1) % P_U32;
        let mut ver_tr3 = CShakeTranscript::new(b"pcs-test");
        assert!(verify_pcs_claims(&state.root, state.shape, &claims, &bad_pf, &mut ver_tr3).is_err());

        // Falsifier 3: forged Merkle sibling hash
        let mut bad_mp = decoded;
        bad_mp.multiproof.aux_hashes[0][0] ^= 0x80;
        let mut ver_tr4 = CShakeTranscript::new(b"pcs-test");
        assert!(verify_pcs_claims(&state.root, state.shape, &claims, &bad_mp, &mut ver_tr4).is_err());
    }
}
