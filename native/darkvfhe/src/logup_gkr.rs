//! Native 61-Bit `D1b` LogUp-GKR Fraction-Tree Prover & Verifier + `ProveKit v2` Subdomain
//! Table Multiplicity Projection over `T = [0, 2^20)`.
//!
//! Implements helper-free projective fraction-tree LogUp-GKR (`Assurance/AirSumcheckCubic.lean`,
//! `notes/trace-packing-and-zk-whir.md` §2, `notes/vfhe-hoisted-certificate-breakthrough.md` §2.2):
//! - Counts exact lookup multiplicities `m[0..2^20]` in `rayon` parallel across all digit columns;
//! - Commits `m` once on the `2^20` subdomain (`ProveKit v2` `pi(x) = x^{2^{k_1 - 20}}`);
//! - Samples `c in {3, 4}` independent 61-bit basefield challenges `alpha_0..alpha_{c-1} in F_p`
//!   (`40.68` bits/chal at `2^18` chunked trees => `c = 3` gives `122.0` bits; `32.0+` bits/chal
//!   at monolithic `M <= 2^29` => `c = 4` gives `>= 128.0` bits);
//! - Evaluates projective binary fraction trees `(P, Q)` bottom-up in `rayon` parallel (`0` field
//!   inversions inside the tree!), deterministically checks non-zero root denominators (`Q_root != 0`,
//!   sealing poles), checks rational equality `sum_b P_{w,b}/Q_{w,b} == P_tab/Q_tab`, and proves every
//!   tree layer via degree-3 `cubicForm` GKR sumchecks (`E(x)*(A(x)*B(x) + C(x)*D(x))`), discharging
//!   `id(z_tab) = sum_{b=0}^{19} 2^b z_b` in `20` muls and `sel_{[0, M)}(z_w)` in `O(log M)` muls!

use crate::FastPrime61;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const TABLE_LOG2: usize = 20;
pub const TABLE_SIZE: usize = 1 << TABLE_LOG2; // 1,048,576

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LogUpConfig {
    /// Chunked `2^18`-leaf witness trees with `c = 3` challenges (`3 * 40.68 = 122.0` bits).
    BatchedC3 { chunk_log2: usize },
    /// Monolithic witness tree with `c = 4` challenges (`>= 128.0` bits up to `M = 2^29`).
    MonolithicC4,
}

impl LogUpConfig {
    pub fn num_challenges(&self) -> usize {
        match self {
            LogUpConfig::BatchedC3 { .. } => 3,
            LogUpConfig::MonolithicC4 => 4,
        }
    }
}

/// One layer of a multi-challenge GKR fraction-tree proof (`k >= 1` variables -> `k + 1` variables).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GkrLayerProof {
    /// Degree-3 sumcheck round polynomials `[k0, k1, k2, k3]` for each of the `k` variables.
    pub sumcheck_rounds: Vec<[u64; 4]>,
    /// Terminal child evaluations `(p_l, p_r, q_l, q_r)` per challenge `ell in 0..c`.
    pub child_evals: Vec<[u64; 4]>,
}

/// Complete GKR proof for one binary fraction tree of depth `depth` (`2^depth` leaves).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FractionTreeProof {
    pub depth: usize,
    pub active_len: usize,
    /// Root numerators & denominators `(P_0, Q_0)` per challenge `ell in 0..c`.
    pub roots: Vec<[u64; 2]>,
    /// Direct children `(P_L, P_R, Q_L, Q_R)` of the root (`0 -> 1` step) per challenge `ell in 0..c`.
    pub layer1_vals: Vec<[u64; 4]>,
    /// Degree-3 GKR sumchecks for layers `1 -> 2`, ..., `(depth - 1) -> depth`.
    pub layers: Vec<GkrLayerProof>,
    /// Final multilinear evaluation of the leaf payload (`f_pad(z_leaf)` for witness, `m(z_leaf)` for table).
    pub leaf_payload_eval: u64,
}

/// Complete `D1b` LogUp-GKR + `ProveKit v2` Subdomain Projection Proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LogUpGkrProof {
    pub config: LogUpConfig,
    pub total_lookups: usize,
    /// SHA-256 commitment root of the `2^20` subdomain-projected multiplicity vector `m[0..2^20]`.
    pub mult_commitment: [u8; 32],
    pub witness_trees: Vec<FractionTreeProof>,
    pub table_tree: FractionTreeProof,
}

impl LogUpGkrProof {
    /// Exact serialized proof byte size of the GKR + commitment transcript (excluding raw Stage-1 witness).
    pub fn succinct_bytes(&self) -> usize {
        let tree_bytes = |t: &FractionTreeProof| -> usize {
            let mut b = 16 + t.roots.len() * 16 + t.layer1_vals.len() * 32 + 8;
            for l in &t.layers {
                b += l.sumcheck_rounds.len() * 32 + l.child_evals.len() * 32;
            }
            b
        };
        32 + 16 + self.witness_trees.iter().map(tree_bytes).sum::<usize>() + tree_bytes(&self.table_tree)
    }
}

#[derive(Clone)]
struct FsTranscript {
    state: [u8; 32],
}

impl FsTranscript {
    fn new(domain_sep: &str, p: u64, context_digest: &[u8; 32]) -> Self {
        let mut h = Sha256::new();
        h.update(b"DARKVFHE_D1B_GKR|");
        h.update(domain_sep.as_bytes());
        h.update(&p.to_le_bytes());
        h.update(context_digest);
        FsTranscript {
            state: h.finalize().into(),
        }
    }

    fn absorb_bytes(&mut self, data: &[u8]) {
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(data);
        self.state = h.finalize().into();
    }

    fn absorb_u64s(&mut self, vals: &[u64]) {
        let mut h = Sha256::new();
        h.update(&self.state);
        for &v in vals {
            h.update(&v.to_le_bytes());
        }
        self.state = h.finalize().into();
    }

    fn squeeze_fp(&mut self, fp: &FastPrime61, tag: u64) -> u64 {
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(b"CHAL");
        h.update(&tag.to_le_bytes());
        let out: [u8; 32] = h.finalize().into();
        self.state = out;
        let lo = u128::from_le_bytes(out[0..16].try_into().unwrap());
        fp.red128(lo)
    }

    fn fork_sub(&self, label: &str, idx: u64) -> Self {
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(b"SUB|");
        h.update(label.as_bytes());
        h.update(&idx.to_le_bytes());
        FsTranscript {
            state: h.finalize().into(),
        }
    }
}

/// Compute `ProveKit v2` subdomain-projected commitment root of `mults[0..2^20]` in parallel.
pub fn commit_multiplicities(mults: &[u64]) -> [u8; 32] {
    assert_eq!(mults.len(), TABLE_SIZE);
    let chunk_hashes: Vec<[u8; 32]> = mults
        .par_chunks(4096)
        .enumerate()
        .map(|(idx, ch)| {
            let mut h = Sha256::new();
            h.update(b"PKV2_SUBDOMAIN_M20|");
            h.update(&(idx as u32).to_le_bytes());
            for &v in ch {
                h.update(&v.to_le_bytes());
            }
            h.finalize().into()
        })
        .collect();
    let mut root_h = Sha256::new();
    root_h.update(b"PKV2_ROOT|");
    for ch in &chunk_hashes {
        root_h.update(ch);
    }
    root_h.finalize().into()
}

/// Count exact multiplicities of `entries` in `[0, 2^20)` in `rayon` parallel.
/// Returns `Err` if an honest prover sees an out-of-range entry (cheating provers bypass via `prove_with_custom_mults`).
pub fn count_multiplicities_parallel(entries: &[u64]) -> Result<Vec<u64>, String> {
    if entries.is_empty() {
        return Ok(vec![0u64; TABLE_SIZE]);
    }
    let chunk_size = (entries.len() / rayon::current_num_threads().max(1)).max(65536);
    let partials: Result<Vec<Vec<u32>>, String> = entries
        .par_chunks(chunk_size)
        .map(|ch| {
            let mut hist = vec![0u32; TABLE_SIZE];
            for &v in ch {
                if v >= TABLE_SIZE as u64 {
                    return Err(format!("lookup entry {v} outside [0, 2^20)"));
                }
                hist[v as usize] += 1;
            }
            Ok(hist)
        })
        .collect();
    let partials = partials?;
    let mut total = vec![0u64; TABLE_SIZE];
    total.par_chunks_mut(16384).enumerate().for_each(|(blk, dst)| {
        let base = blk * 16384;
        for part in &partials {
            for (i, slot) in dst.iter_mut().enumerate() {
                *slot += part[base + i] as u64;
            }
        }
    });
    Ok(total)
}

/// Build `eq(z, x)` over `{0, 1}^k` in little-endian bit order (`i = sum_{b=0}^{k-1} 2^b x_b`):
/// variable `z[0]` corresponds to stride `1` (`x_0`), ..., `z[k-1]` to stride `2^{k-1}`.
fn build_eq_le(fp: &FastPrime61, z: &[u64]) -> Vec<u64> {
    let mut v = vec![1u64];
    for &zk in z.iter().rev() {
        let om = fp.sub(1, zk);
        let mut next = Vec::with_capacity(v.len() * 2);
        for &val in &v {
            next.push(fp.mul(val, om));
            next.push(fp.mul(val, zk));
        }
        v = next;
    }
    v
}

/// Evaluate `mle(vec, z)` in little-endian bit order in parallel.
pub fn eval_mle_le(fp: &FastPrime61, vec_padded: &[u64], z: &[u64]) -> u64 {
    assert_eq!(vec_padded.len(), 1usize << z.len());
    if z.is_empty() {
        return vec_padded[0] % fp.p;
    }
    if z.len() <= 14 {
        let eq = build_eq_le(fp, z);
        return fp.dot(vec_padded, &eq);
    }
    // Split high/low variables so memory stays tiny and parallelizes cleanly across cores!
    let lo_bits = z.len() / 2;
    let eq_lo = build_eq_le(fp, &z[..lo_bits]);
    let eq_hi = build_eq_le(fp, &z[lo_bits..]);
    let lo_len = 1usize << lo_bits;
    let hi_vals: Vec<u64> = vec_padded
        .par_chunks(lo_len)
        .map(|ch| fp.dot(ch, &eq_lo))
        .collect();
    fp.dot(&hi_vals, &eq_hi)
}

/// `O(d)` closed-form verifier evaluation of prefix indicator `sel_{[0, M)}(z_0..z_{d-1})`
/// under little-endian bit indexing `i = sum_{b=0}^{d-1} 2^b i_b`!
pub fn eval_prefix_selector_le(fp: &FastPrime61, active_len: usize, depth: usize, z: &[u64]) -> u64 {
    assert_eq!(z.len(), depth);
    if depth == 0 {
        return if active_len >= 1 { 1 } else { 0 };
    }
    let full = 1usize << depth;
    if active_len >= full {
        return 1;
    }
    if active_len == 0 {
        return 0;
    }
    // Precompute suffix matches `prod_{t = b+1}^{d-1} eq(z_t, M_t)`:
    let mut suf = vec![1u64; depth + 1];
    for b in (0..depth).rev() {
        let bit = (active_len >> b) & 1;
        let term = if bit == 1 { z[b] } else { fp.sub(1, z[b]) };
        suf[b] = fp.mul(suf[b + 1], term);
    }
    let mut acc = 0u64;
    for b in 0..depth {
        if ((active_len >> b) & 1) == 1 {
            // Fix bit b to 0, bits > b to M_t, bits < b free (sum to 1)!
            acc = fp.add(acc, fp.mul(fp.sub(1, z[b]), suf[b + 1]));
        }
    }
    acc
}

/// `O(20)` closed-form verifier evaluation of `id(z_0..z_{19}) = sum_{b=0}^{19} 2^b z_b mod p`.
pub fn eval_table_identity_le(fp: &FastPrime61, z: &[u64]) -> u64 {
    let mut acc = 0u64;
    let mut pw2 = 1u64;
    for &zb in z {
        acc = fp.add(acc, fp.mul(pw2, zb));
        pw2 = fp.add(pw2, pw2);
    }
    acc
}

/// Build all layers `0..=depth` of a `c`-challenge projective binary fraction tree in `rayon` parallel.
/// Layer `0` has length `1` (root); layer `depth` has length `2^depth` (leaves).
fn build_fraction_tree_layers(
    fp: &FastPrime61,
    leaf_p: Vec<Vec<u64>>,
    leaf_q: Vec<Vec<u64>>,
    depth: usize,
) -> (Vec<Vec<Vec<u64>>>, Vec<Vec<Vec<u64>>>) {
    let c = leaf_p.len();
    let mut p_layers = vec![Vec::new(); depth + 1];
    let mut q_layers = vec![Vec::new(); depth + 1];
    p_layers[depth] = leaf_p;
    q_layers[depth] = leaf_q;

    for lvl in (1..=depth).rev() {
        let half = 1usize << (lvl - 1);
        let mut next_p = Vec::with_capacity(c);
        let mut next_q = Vec::with_capacity(c);
        for ell in 0..c {
            let pl = &p_layers[lvl][ell];
            let ql = &q_layers[lvl][ell];
            if half >= 4096 {
                let (np, nq): (Vec<u64>, Vec<u64>) = (0..half)
                    .into_par_iter()
                    .map(|x| {
                        let (p0, p1) = (pl[2 * x], pl[2 * x + 1]);
                        let (q0, q1) = (ql[2 * x], ql[2 * x + 1]);
                        (
                            fp.red128(p0 as u128 * q1 as u128 + p1 as u128 * q0 as u128),
                            fp.mul(q0, q1),
                        )
                    })
                    .unzip();
                next_p.push(np);
                next_q.push(nq);
            } else {
                let mut np = Vec::with_capacity(half);
                let mut nq = Vec::with_capacity(half);
                for x in 0..half {
                    let (p0, p1) = (pl[2 * x], pl[2 * x + 1]);
                    let (q0, q1) = (ql[2 * x], ql[2 * x + 1]);
                    np.push(fp.red128(p0 as u128 * q1 as u128 + p1 as u128 * q0 as u128));
                    nq.push(fp.mul(q0, q1));
                }
                next_p.push(np);
                next_q.push(nq);
            }
        }
        p_layers[lvl - 1] = next_p;
        q_layers[lvl - 1] = next_q;
    }
    (p_layers, q_layers)
}

/// Prove a single `c`-challenge binary fraction tree using degree-3 GKR sumchecks (`AirSumcheckCubic`).
fn prove_single_tree(
    fp: &FastPrime61,
    tr: &mut FsTranscript,
    p_layers: &[Vec<Vec<u64>>],
    q_layers: &[Vec<Vec<u64>>],
    leaf_payload_padded: &[u64],
    active_len: usize,
    depth: usize,
) -> (FractionTreeProof, Vec<u64>) {
    let c = p_layers[0].len();
    let roots: Vec<[u64; 2]> = (0..c).map(|ell| [p_layers[0][ell][0], q_layers[0][ell][0]]).collect();
    for r in &roots {
        tr.absorb_u64s(r);
    }

    if depth == 0 {
        return (
            FractionTreeProof {
                depth: 0,
                active_len,
                roots,
                layer1_vals: Vec::new(),
                layers: Vec::new(),
                leaf_payload_eval: leaf_payload_padded[0] % fp.p,
            },
            Vec::new(),
        );
    }

    // Step 0 -> 1: send direct children at layer 1 (`2` nodes: index 0 and index 1):
    let layer1_vals: Vec<[u64; 4]> = (0..c)
        .map(|ell| {
            [
                p_layers[1][ell][0],
                p_layers[1][ell][1],
                q_layers[1][ell][0],
                q_layers[1][ell][1],
            ]
        })
        .collect();
    for v in &layer1_vals {
        tr.absorb_u64s(v);
    }
    let z0 = tr.squeeze_fp(fp, 1);
    let mut z_point = vec![z0];

    let mut layers_out = Vec::with_capacity(depth.saturating_sub(1));

    // Layers k = 1 .. depth - 1 (reducing k-var claim at layer k to (k+1)-var claim at layer k+1):
    // Note on indexing: in `build_fraction_tree_layers`, parent `x` has children `2*x` (child bit = 0,
    // which is the LEAST-significant bit `b = 0` of `2*x + bit`!) and `2*x + 1` (child bit = 1)!
    // Let's keep bit ordering 100% consistent:
    // At layer `k` (`2^k` nodes), node index `x in 0..2^k` has binary bits `(x_0, ..., x_{k-1})` (`x = sum 2^b x_b`).
    // Its children in layer `k + 1` are `2*x + child_bit` (`child_bit in {0, 1}`), which has binary bits
    // `(child_bit, x_0, ..., x_{k-1})`!
    // Therefore, folding `child_bit` at `r_child` prepends `r_child` at bit `0`: `z_next = [r_child, r_0, ..., r_{k-1}]`!
    for k in 1..depth {
        let m_len = 1usize << k;
        let lam_p: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, 100 + ell as u64)).collect();
        let lam_q: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, 200 + ell as u64)).collect();

        let mut eq_tbl = build_eq_le(fp, &z_point);
        let mut p_left: Vec<Vec<u64>> = Vec::with_capacity(c);
        let mut p_right: Vec<Vec<u64>> = Vec::with_capacity(c);
        let mut q_left: Vec<Vec<u64>> = Vec::with_capacity(c);
        let mut q_right: Vec<Vec<u64>> = Vec::with_capacity(c);

        for ell in 0..c {
            let pl_src = &p_layers[k + 1][ell];
            let ql_src = &q_layers[k + 1][ell];
            let mut pl = Vec::with_capacity(m_len);
            let mut pr = Vec::with_capacity(m_len);
            let mut ql = Vec::with_capacity(m_len);
            let mut qr = Vec::with_capacity(m_len);
            for x in 0..m_len {
                pl.push(pl_src[2 * x]);
                pr.push(pl_src[2 * x + 1]);
                ql.push(ql_src[2 * x]);
                qr.push(ql_src[2 * x + 1]);
            }
            p_left.push(pl);
            p_right.push(pr);
            q_left.push(ql);
            q_right.push(qr);
        }

        let mut sumcheck_rounds = Vec::with_capacity(k);
        let mut r_vars = Vec::with_capacity(k);
        let mut cur_len = m_len;

        // Fold variables b = 0 .. k - 1 (stride 1 at each step since pairs `(2*u, 2*u + 1)` vary in lowest remaining bit!):
        for round in 0..k {
            let half = cur_len / 2;
            // Compute exact cubic coefficients [k0, k1, k2, k3] over u in 0..half:
            let compute_pair = |u: usize| -> [u64; 4] {
                let e0 = eq_tbl[2 * u];
                let e1 = eq_tbl[2 * u + 1];
                let de = fp.sub(e1, e0);

                let mut s0 = 0u64;
                let mut s1 = 0u64;
                let mut s2 = 0u64;
                for ell in 0..c {
                    let (a0, a1) = (p_left[ell][2 * u], p_left[ell][2 * u + 1]);
                    let (b0, b1) = (q_right[ell][2 * u], q_right[ell][2 * u + 1]);
                    let (c0, c1) = (p_right[ell][2 * u], p_right[ell][2 * u + 1]);
                    let (d0, d1) = (q_left[ell][2 * u], q_left[ell][2 * u + 1]);
                    let da = fp.sub(a1, a0);
                    let db = fp.sub(b1, b0);
                    let dc_v = fp.sub(c1, c0);
                    let dd = fp.sub(d1, d0);

                    // P term: a*b + c*d
                    let p_c0 = fp.red128(a0 as u128 * b0 as u128 + c0 as u128 * d0 as u128);
                    let p_c1 = fp.red128(
                        a0 as u128 * db as u128
                            + da as u128 * b0 as u128
                            + c0 as u128 * dd as u128
                            + dc_v as u128 * d0 as u128,
                    );
                    let p_c2 = fp.red128(da as u128 * db as u128 + dc_v as u128 * dd as u128);

                    // Q term: q_left * q_right = d * b
                    let q_c0 = fp.mul(d0, b0);
                    let q_c1 = fp.red128(d0 as u128 * db as u128 + dd as u128 * b0 as u128);
                    let q_c2 = fp.mul(dd, db);

                    let lp = lam_p[ell] as u128;
                    let lq = lam_q[ell] as u128;
                    s0 = fp.add(s0, fp.red128(lp * p_c0 as u128 + lq * q_c0 as u128));
                    s1 = fp.add(s1, fp.red128(lp * p_c1 as u128 + lq * q_c1 as u128));
                    s2 = fp.add(s2, fp.red128(lp * p_c2 as u128 + lq * q_c2 as u128));
                }

                let k0 = fp.mul(e0, s0);
                let k1 = fp.red128(e0 as u128 * s1 as u128 + de as u128 * s0 as u128);
                let k2 = fp.red128(e0 as u128 * s2 as u128 + de as u128 * s1 as u128);
                let k3 = fp.mul(de, s2);
                [k0, k1, k2, k3]
            };

            let poly = if half >= 2048 {
                (0..half)
                    .into_par_iter()
                    .map(compute_pair)
                    .reduce(
                        || [0u64; 4],
                        |acc, x| [
                            fp.add(acc[0], x[0]),
                            fp.add(acc[1], x[1]),
                            fp.add(acc[2], x[2]),
                            fp.add(acc[3], x[3]),
                        ],
                    )
            } else {
                let mut acc = [0u64; 4];
                for u in 0..half {
                    let x = compute_pair(u);
                    for i in 0..4 {
                        acc[i] = fp.add(acc[i], x[i]);
                    }
                }
                acc
            };

            tr.absorb_u64s(&poly);
            let r_i = tr.squeeze_fp(fp, 1000 + round as u64);
            sumcheck_rounds.push(poly);
            r_vars.push(r_i);

            // Fold tables in-place at r_i: `f(r_i) = f0 + r_i * (f1 - f0)`
            let fold_vec = |v: &mut Vec<u64>| {
                if half >= 4096 {
                    let next: Vec<u64> = (0..half)
                        .into_par_iter()
                        .map(|u| {
                            let f0 = v[2 * u];
                            let f1 = v[2 * u + 1];
                            fp.add(f0, fp.mul(r_i, fp.sub(f1, f0)))
                        })
                        .collect();
                    *v = next;
                } else {
                    for u in 0..half {
                        let f0 = v[2 * u];
                        let f1 = v[2 * u + 1];
                        v[u] = fp.add(f0, fp.mul(r_i, fp.sub(f1, f0)));
                    }
                    v.truncate(half);
                }
            };
            fold_vec(&mut eq_tbl);
            for ell in 0..c {
                fold_vec(&mut p_left[ell]);
                fold_vec(&mut p_right[ell]);
                fold_vec(&mut q_left[ell]);
                fold_vec(&mut q_right[ell]);
            }
            cur_len = half;
        }

        let child_evals: Vec<[u64; 4]> = (0..c)
            .map(|ell| [p_left[ell][0], p_right[ell][0], q_left[ell][0], q_right[ell][0]])
            .collect();
        for ce in &child_evals {
            tr.absorb_u64s(ce);
        }
        let r_child = tr.squeeze_fp(fp, 2000 + k as u64);
        let mut z_next = Vec::with_capacity(k + 1);
        z_next.push(r_child);
        z_next.extend_from_slice(&r_vars);
        z_point = z_next;
        layers_out.push(GkrLayerProof {
            sumcheck_rounds,
            child_evals,
        });
    }

    let leaf_payload_eval = eval_mle_le(fp, leaf_payload_padded, &z_point);
    tr.absorb_u64s(&[leaf_payload_eval]);

    (
        FractionTreeProof {
            depth,
            active_len,
            roots,
            layer1_vals,
            layers: layers_out,
            leaf_payload_eval,
        },
        z_point,
    )
}

/// Verify a single `c`-challenge binary fraction tree proof and return `(z_leaf, p_leaf_claims, q_leaf_claims)`.
fn verify_single_tree(
    fp: &FastPrime61,
    tr: &mut FsTranscript,
    proof: &FractionTreeProof,
    c: usize,
) -> Result<(Vec<u64>, Vec<u64>, Vec<u64>), String> {
    if proof.roots.len() != c {
        return Err("FractionTreeProof root count mismatch".into());
    }
    for r in &proof.roots {
        if r[0] >= fp.p || r[1] >= fp.p {
            return Err("root field residue out of range".into());
        }
        if r[1] == 0 {
            return Err("LogUp-GKR root denominator Q_root == 0 (pole rejected)".into());
        }
        tr.absorb_u64s(r);
    }

    if proof.depth == 0 {
        let p_claims = proof.roots.iter().map(|r| r[0]).collect();
        let q_claims = proof.roots.iter().map(|r| r[1]).collect();
        return Ok((Vec::new(), p_claims, q_claims));
    }

    if proof.layer1_vals.len() != c || proof.layers.len() != proof.depth - 1 {
        return Err("FractionTreeProof layer shape mismatch".into());
    }
    for (ell, v) in proof.layer1_vals.iter().enumerate() {
        let [pl, pr, ql, qr] = *v;
        if pl >= fp.p || pr >= fp.p || ql >= fp.p || qr >= fp.p {
            return Err("layer1_vals residue out of range".into());
        }
        let want_p = fp.red128(pl as u128 * qr as u128 + pr as u128 * ql as u128);
        let want_q = fp.mul(ql, qr);
        if want_p != proof.roots[ell][0] || want_q != proof.roots[ell][1] {
            return Err(format!("GKR root 0->1 fraction check failed at challenge {ell}"));
        }
        tr.absorb_u64s(v);
    }
    let z0 = tr.squeeze_fp(fp, 1);
    let mut z_point = vec![z0];
    let mut cur_p: Vec<u64> = (0..c)
        .map(|ell| {
            let [pl, pr, _, _] = proof.layer1_vals[ell];
            fp.add(pl, fp.mul(z0, fp.sub(pr, pl)))
        })
        .collect();
    let mut cur_q: Vec<u64> = (0..c)
        .map(|ell| {
            let [_, _, ql, qr] = proof.layer1_vals[ell];
            fp.add(ql, fp.mul(z0, fp.sub(qr, ql)))
        })
        .collect();

    for (idx, layer) in proof.layers.iter().enumerate() {
        let k = idx + 1;
        if layer.sumcheck_rounds.len() != k || layer.child_evals.len() != c {
            return Err(format!("GKR layer {k} round/eval length mismatch"));
        }
        let lam_p: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, 100 + ell as u64)).collect();
        let lam_q: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, 200 + ell as u64)).collect();

        let mut running_claim = 0u64;
        for ell in 0..c {
            running_claim = fp.add(
                running_claim,
                fp.red128(
                    lam_p[ell] as u128 * cur_p[ell] as u128
                        + lam_q[ell] as u128 * cur_q[ell] as u128,
                ),
            );
        }

        let mut r_vars = Vec::with_capacity(k);
        for (round, poly) in layer.sumcheck_rounds.iter().enumerate() {
            if poly.iter().any(|&v| v >= fp.p) {
                return Err("sumcheck coefficient out of field range".into());
            }
            // g(0) = k0; g(1) = k0 + k1 + k2 + k3
            let g0 = poly[0];
            let g1 = fp.add(fp.add(poly[0], poly[1]), fp.add(poly[2], poly[3]));
            if fp.add(g0, g1) != running_claim {
                return Err(format!("GKR sumcheck round {round} at layer {k} failed g(0)+g(1)==claim"));
            }
            tr.absorb_u64s(poly);
            let r_i = tr.squeeze_fp(fp, 1000 + round as u64);
            r_vars.push(r_i);
            // Horner eval k0 + r*(k1 + r*(k2 + r*k3)):
            let mut ev = poly[3];
            ev = fp.add(poly[2], fp.mul(r_i, ev));
            ev = fp.add(poly[1], fp.mul(r_i, ev));
            ev = fp.add(poly[0], fp.mul(r_i, ev));
            running_claim = ev;
        }

        // Factored terminal check (`scChain_cubicHonest_final`):
        let mut eq_zr = 1u64;
        for (&zb, &rb) in z_point.iter().zip(r_vars.iter()) {
            // eq(zb, rb) = (1 - zb)(1 - rb) + zb * rb
            let t0 = fp.mul(fp.sub(1, zb), fp.sub(1, rb));
            let t1 = fp.mul(zb, rb);
            eq_zr = fp.mul(eq_zr, fp.add(t0, t1));
        }

        let mut inner_sum = 0u64;
        for ell in 0..c {
            let [pl, pr, ql, qr] = layer.child_evals[ell];
            if pl >= fp.p || pr >= fp.p || ql >= fp.p || qr >= fp.p {
                return Err("child_evals residue out of range".into());
            }
            let p_term = fp.red128(pl as u128 * qr as u128 + pr as u128 * ql as u128);
            let q_term = fp.mul(ql, qr);
            inner_sum = fp.add(
                inner_sum,
                fp.red128(lam_p[ell] as u128 * p_term as u128 + lam_q[ell] as u128 * q_term as u128),
            );
            tr.absorb_u64s(&layer.child_evals[ell]);
        }
        if running_claim != fp.mul(eq_zr, inner_sum) {
            return Err(format!("GKR layer {k} factored terminal check failed"));
        }

        let r_child = tr.squeeze_fp(fp, 2000 + k as u64);
        for ell in 0..c {
            let [pl, pr, ql, qr] = layer.child_evals[ell];
            cur_p[ell] = fp.add(pl, fp.mul(r_child, fp.sub(pr, pl)));
            cur_q[ell] = fp.add(ql, fp.mul(r_child, fp.sub(qr, ql)));
        }
        let mut z_next = Vec::with_capacity(k + 1);
        z_next.push(r_child);
        z_next.extend_from_slice(&r_vars);
        z_point = z_next;
    }

    if proof.leaf_payload_eval >= fp.p {
        return Err("leaf_payload_eval out of range".into());
    }
    tr.absorb_u64s(&[proof.leaf_payload_eval]);
    Ok((z_point, cur_p, cur_q))
}

/// Prove that every element in `lookup_entries` lies in `[0, 2^20)` via `D1b` LogUp-GKR + `ProveKit v2`
/// subdomain multiplicity commitment.
pub fn prove_logup_gkr(
    fp: &FastPrime61,
    lookup_entries: &[u64],
    config: LogUpConfig,
    context_digest: &[u8; 32],
) -> Result<(LogUpGkrProof, Vec<u64>), String> {
    let mults = count_multiplicities_parallel(lookup_entries)?;
    let proof = prove_logup_gkr_with_mults(fp, lookup_entries, &mults, config, context_digest);
    Ok((proof, mults))
}

/// Lower-level prover taking explicit `mults` (also used in adversarial falsifiers where a cheating
/// prover supplies arbitrary `mults` for out-of-range witness digits).
pub fn prove_logup_gkr_with_mults(
    fp: &FastPrime61,
    lookup_entries: &[u64],
    mults: &[u64],
    config: LogUpConfig,
    context_digest: &[u8; 32],
) -> LogUpGkrProof {
    assert_eq!(mults.len(), TABLE_SIZE);
    let c = config.num_challenges();
    let mult_commitment = commit_multiplicities(mults);

    let mut tr = FsTranscript::new("LOGUP_RANGE20", fp.p, context_digest);
    tr.absorb_u64s(&[lookup_entries.len() as u64, c as u64]);
    tr.absorb_bytes(&mult_commitment);

    let alphas: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, ell as u64)).collect();

    // Partition witness entries into chunks:
    let chunk_cap = match config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => lookup_entries.len().max(2).next_power_of_two(),
    };
    let chunks: Vec<&[u64]> = if lookup_entries.is_empty() {
        vec![&[]]
    } else {
        lookup_entries.chunks(chunk_cap).collect()
    };

    // Build AND prove each witness fraction tree in parallel on forked sub-transcripts,
    // immediately dropping per-tree layer buffers so peak RAM stays O(threads * chunk_cap)!
    let witness_trees: Vec<FractionTreeProof> = chunks
        .par_iter()
        .enumerate()
        .map(|(b_idx, ch)| {
            let active = ch.len();
            let padded_len = active.max(2).next_power_of_two();
            let depth = padded_len.trailing_zeros() as usize;
            let mut f_pad = vec![0u64; padded_len];
            for (i, &v) in ch.iter().enumerate() {
                f_pad[i] = v % fp.p;
            }
            let mut leaf_p = Vec::with_capacity(c);
            let mut leaf_q = Vec::with_capacity(c);
            for &alpha in &alphas {
                let mut lp = vec![0u64; padded_len];
                let mut lq = vec![1u64; padded_len];
                for i in 0..active {
                    lp[i] = 1;
                    lq[i] = fp.sub(alpha, f_pad[i]);
                }
                leaf_p.push(lp);
                leaf_q.push(lq);
            }
            let (p_layers, q_layers) = build_fraction_tree_layers(fp, leaf_p, leaf_q, depth);
            let mut sub_tr = tr.fork_sub("WIT_TREE", b_idx as u64);
            let (prf, _) = prove_single_tree(fp, &mut sub_tr, &p_layers, &q_layers, &f_pad, active, depth);
            prf
        })
        .collect();

    // Build and prove the single shared `2^20` Table Tree in parallel:
    let mut tab_leaf_p = Vec::with_capacity(c);
    let mut tab_leaf_q = Vec::with_capacity(c);
    let mults_mod_p: Vec<u64> = mults.iter().map(|&m| m % fp.p).collect();
    for &alpha in &alphas {
        let lp = mults_mod_p.clone();
        let lq: Vec<u64> = (0..TABLE_SIZE as u64).into_par_iter().map(|j| fp.sub(alpha, j)).collect();
        tab_leaf_p.push(lp);
        tab_leaf_q.push(lq);
    }
    let (tab_p_layers, tab_q_layers) = build_fraction_tree_layers(fp, tab_leaf_p, tab_leaf_q, TABLE_LOG2);
    let mut tab_tr = tr.fork_sub("TAB_TREE", 0);
    let (table_tree, _) = prove_single_tree(
        fp,
        &mut tab_tr,
        &tab_p_layers,
        &tab_q_layers,
        &mults_mod_p,
        TABLE_SIZE,
        TABLE_LOG2,
    );

    LogUpGkrProof {
        config,
        total_lookups: lookup_entries.len(),
        mult_commitment,
        witness_trees,
        table_tree,
    }
}

/// Verify a `D1b` LogUp-GKR proof.
/// - When `witness_and_mults` is `Some((lookup_entries, mults))`, also checks the commitment root
///   `mult_commitment == commit_multiplicities(mults)` and discharges the terminal MLE openings
///   `f_pad(z_w)` and `m(z_tab)` directly against the vectors.
/// - When `witness_and_mults` is `None` (succinct PCS-oracle verifier mode), verifies the entire
///   GKR sumcheck chain, pole guards, `O(log M)` prefix selectors, `O(20)` table identity MLE, and
///   root rational fraction balance in sub-millisecond time!
pub fn verify_logup_gkr(
    fp: &FastPrime61,
    proof: &LogUpGkrProof,
    context_digest: &[u8; 32],
    witness_and_mults: Option<(&[u64], &[u64])>,
) -> Result<(), String> {
    let c = proof.config.num_challenges();
    if let Some((entries, mults)) = witness_and_mults {
        if entries.len() != proof.total_lookups {
            return Err("total_lookups length mismatch vs witness".into());
        }
        if mults.len() != TABLE_SIZE {
            return Err("multiplicity table size != 2^20".into());
        }
        if commit_multiplicities(mults) != proof.mult_commitment {
            return Err("ProveKit v2 multiplicity commitment mismatch".into());
        }
    }

    let mut tr = FsTranscript::new("LOGUP_RANGE20", fp.p, context_digest);
    tr.absorb_u64s(&[proof.total_lookups as u64, c as u64]);
    tr.absorb_bytes(&proof.mult_commitment);
    let alphas: Vec<u64> = (0..c).map(|ell| tr.squeeze_fp(fp, ell as u64)).collect();

    let chunk_cap = match proof.config {
        LogUpConfig::BatchedC3 { chunk_log2 } => 1usize << chunk_log2,
        LogUpConfig::MonolithicC4 => proof.total_lookups.max(2).next_power_of_two(),
    };

    // 1. Verify all witness fraction trees in parallel and accumulate active count + root rational sums:
    let per_tree_res: Result<Vec<(usize, Vec<u64>)>, String> = proof
        .witness_trees
        .par_iter()
        .enumerate()
        .map(|(b_idx, w_prf)| {
            let mut sub_tr = tr.fork_sub("WIT_TREE", b_idx as u64);
            let (z_w, p_claims, q_claims) = verify_single_tree(fp, &mut sub_tr, w_prf, c)?;
            let sel_ev = eval_prefix_selector_le(fp, w_prf.active_len, w_prf.depth, &z_w);
            let mut fracs = vec![0u64; c];
            for ell in 0..c {
                if p_claims[ell] != sel_ev {
                    return Err(format!("witness tree {b_idx} leaf P_ell != sel_MLE"));
                }
                let want_q = fp.sub(
                    fp.add(fp.mul(fp.sub(alphas[ell], 1), sel_ev), 1),
                    w_prf.leaf_payload_eval,
                );
                if q_claims[ell] != want_q {
                    return Err(format!("witness tree {b_idx} leaf Q_ell != (alpha-1)*sel + 1 - f_MLE"));
                }
                fracs[ell] = fp.mul(w_prf.roots[ell][0], fp.inv(w_prf.roots[ell][1]));
            }
            if let Some((entries, _)) = witness_and_mults {
                let start = b_idx * chunk_cap;
                let end = (start + w_prf.active_len).min(entries.len());
                let slice = if entries.is_empty() { &[] } else { &entries[start..end] };
                let padded_len = 1usize << w_prf.depth;
                let mut f_pad = vec![0u64; padded_len];
                for (i, &v) in slice.iter().enumerate() {
                    f_pad[i] = v % fp.p;
                }
                let actual_f_ev = eval_mle_le(fp, &f_pad, &z_w);
                if actual_f_ev != w_prf.leaf_payload_eval {
                    return Err(format!("witness tree {b_idx} Stage-1 MLE opening mismatch"));
                }
            }
            Ok((w_prf.active_len, fracs))
        })
        .collect();
    let per_tree_res = per_tree_res?;

    let mut accounted_lookups = 0usize;
    let mut wit_rational_sum = vec![0u64; c];
    for (act, fracs) in per_tree_res {
        accounted_lookups += act;
        for ell in 0..c {
            wit_rational_sum[ell] = fp.add(wit_rational_sum[ell], fracs[ell]);
        }
    }

    if accounted_lookups != proof.total_lookups {
        return Err("witness tree active_len sum != total_lookups".into());
    }

    // 2. Verify the shared 2^20 Table Tree:
    if proof.table_tree.depth != TABLE_LOG2 || proof.table_tree.active_len != TABLE_SIZE {
        return Err("table tree depth/size != 2^20".into());
    }
    let mut tab_tr = tr.fork_sub("TAB_TREE", 0);
    let (z_tab, tab_p_claims, tab_q_claims) = verify_single_tree(fp, &mut tab_tr, &proof.table_tree, c)?;
    let id_ev = eval_table_identity_le(fp, &z_tab);
    for ell in 0..c {
        if tab_p_claims[ell] != proof.table_tree.leaf_payload_eval {
            return Err("table tree leaf P_ell != m(z_tab)".into());
        }
        let want_tab_q = fp.sub(alphas[ell], id_ev);
        if tab_q_claims[ell] != want_tab_q {
            return Err("table tree leaf Q_ell != alpha_ell - id(z_tab)".into());
        }
        let tab_frac = fp.mul(
            proof.table_tree.roots[ell][0],
            fp.inv(proof.table_tree.roots[ell][1]),
        );
        if wit_rational_sum[ell] != tab_frac {
            return Err(format!(
                "LogUp-GKR rational sum balance failed at challenge {ell} (out-of-range digit or bad multiplicity!)"
            ));
        }
    }

    if let Some((_, mults)) = witness_and_mults {
        let mults_mod_p: Vec<u64> = mults.iter().map(|&m| m % fp.p).collect();
        let actual_m_ev = eval_mle_le(fp, &mults_mod_p, &z_tab);
        if actual_m_ev != proof.table_tree.leaf_payload_eval {
            return Err("table tree multiplicity MLE opening mismatch".into());
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HoistedParams;

    #[test]
    fn logup_gkr_accepts_valid_and_rejects_out_of_range() {
        let params = HoistedParams::n8192();
        let fp = &params.fp[0];
        let ctx = [0x42u8; 32];
        let mut entries: Vec<u64> = (0..50_000).map(|i| ((i * 7919) % TABLE_SIZE) as u64).collect();
        entries.push(0);
        entries.push((TABLE_SIZE - 1) as u64);

        for cfg in [
            LogUpConfig::BatchedC3 { chunk_log2: 15 },
            LogUpConfig::MonolithicC4,
        ] {
            let (prf, mults) = prove_logup_gkr(fp, &entries, cfg, &ctx).expect("honest prove");
            verify_logup_gkr(fp, &prf, &ctx, Some((&entries, &mults))).expect("honest full verify");
            verify_logup_gkr(fp, &prf, &ctx, None).expect("honest succinct GKR verify");

            // Falsifier: forge one out-of-range entry `entries[10] = 1 << 20` (outside [0, 2^20))
            // with ANY multiplicity vector (even adjusting sum(m) == M):
            let mut bad_entries = entries.clone();
            bad_entries[10] = TABLE_SIZE as u64; // 2^20 is OUT OF RANGE!
            let bad_prf = prove_logup_gkr_with_mults(fp, &bad_entries, &mults, cfg, &ctx);
            assert!(
                verify_logup_gkr(fp, &bad_prf, &ctx, Some((&bad_entries, &mults))).is_err(),
                "D1b LogUp-GKR must reject out-of-range digit 2^20!"
            );
            assert!(
                verify_logup_gkr(fp, &bad_prf, &ctx, None).is_err(),
                "succinct D1b LogUp-GKR must reject out-of-range digit 2^20 at root balance!"
            );
        }
    }
}
