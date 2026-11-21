//! `124`-bit `BabyBear Ext4` (`X^4 - 11`) `Gruen` `{0, ∞}` Mode-2 `EinSumcheck` (`0` prover inversions!),
//! strict-lower-triangularity zerocheck `(1 - SLT) ⊙ L == 0`, helper-free `D1b` projective fraction-tree
//! LogUp-GKR (`ProveKit v2` §3.2 subdomain-lifted `[0, 4096)` WY remainder range proof), and delayed
//! block-bind (`b -> j -> k`, `l_0 = 5`) 7-bucket 0-mul E2M1 `MXFP4` Horner prover & verifier.

use crate::ext4::{
    badd, bsub, build_eq_suffix_tables_ext4, build_eq_table_lsb_ext4, eq_lin_ext4,
    eval_cubic_zero_one_two_inf_ext4, eval_quad_zero_one_inf_ext4, fold_bb_to_ext4, fold_ext4,
    ByteCursor, CShakeTranscript, Ext4, P, P_U32,
};
use rayon::prelude::*;

// ===========================================================================
// §1. `124`-Bit `Ext4` `Gruen` `{0, ∞}` Mode-2 `EinSumcheck` (`0` Prover Inversions)
// ===========================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GruenRoundExt4Msg {
    TwoPoint { q0: Ext4, q_inf: Ext4 },
    ZeroEqFallback { q0: Ext4, q_inf: Ext4, q1: Ext4 },
}

impl GruenRoundExt4Msg {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        match *self {
            Self::TwoPoint { q0, q_inf } => {
                out.push(0);
                out.extend_from_slice(&q0.to_bytes());
                out.extend_from_slice(&q_inf.to_bytes());
            }
            Self::ZeroEqFallback { q0, q_inf, q1 } => {
                out.push(1);
                out.extend_from_slice(&q0.to_bytes());
                out.extend_from_slice(&q_inf.to_bytes());
                out.extend_from_slice(&q1.to_bytes());
            }
        }
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        match cur.read_u8()? {
            0 => Ok(Self::TwoPoint {
                q0: cur.read_ext4()?,
                q_inf: cur.read_ext4()?,
            }),
            1 => Ok(Self::ZeroEqFallback {
                q0: cur.read_ext4()?,
                q_inf: cur.read_ext4()?,
                q1: cur.read_ext4()?,
            }),
            tag => Err(format!("invalid GruenRoundExt4Msg tag {tag}")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GruenMode2Ext4Proof {
    pub claim: Ext4,
    pub mu_s: usize,
    pub kappa: usize,
    pub rounds: Vec<GruenRoundExt4Msg>,
    pub terminal_openings: (Ext4, Ext4),
}

impl GruenMode2Ext4Proof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.claim.to_bytes());
        out.push(self.mu_s as u8);
        out.push(self.kappa as u8);
        for r in &self.rounds {
            r.write_to(out);
        }
        out.extend_from_slice(&self.terminal_openings.0.to_bytes());
        out.extend_from_slice(&self.terminal_openings.1.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let claim = cur.read_ext4()?;
        let mu_s = cur.read_u8()? as usize;
        let kappa = cur.read_u8()? as usize;
        if mu_s + kappa == 0 || mu_s + kappa > 30 {
            return Err("invalid GruenMode2Ext4Proof dimensions".to_string());
        }
        let m = mu_s + kappa;
        let mut rounds = Vec::with_capacity(m);
        for _ in 0..m {
            rounds.push(GruenRoundExt4Msg::read_from(cur)?);
        }
        let open_a = cur.read_ext4()?;
        let open_b = cur.read_ext4()?;
        Ok(Self {
            claim,
            mu_s,
            kappa,
            rounds,
            terminal_openings: (open_a, open_b),
        })
    }
}

fn gruen_f2_round_evals_ext4(
    left: &[Ext4],
    right: &[Ext4],
    suf_eq: &[Ext4],
    kappa: usize,
) -> (Ext4, Ext4, Ext4) {
    let rem_h_pairs = suf_eq.len();
    let nk = 1usize << kappa;
    let stride_p = rem_h_pairs * 2;
    let mut q0_by_h = vec![Ext4::ZERO; rem_h_pairs];
    let mut qinf_by_h = vec![Ext4::ZERO; rem_h_pairs];
    let mut q1_by_h = vec![Ext4::ZERO; rem_h_pairs];

    for q in 0..nk {
        let base = q * stride_p;
        for h_rem in 0..rem_h_pairs {
            let idx0 = base + 2 * h_rem;
            let a0 = left[idx0];
            let a1 = left[idx0 + 1];
            let b0 = right[idx0];
            let b1 = right[idx0 + 1];
            let da = a1.sub(a0);
            let db = b1.sub(b0);
            q0_by_h[h_rem] = q0_by_h[h_rem].add(a0.mul(b0));
            qinf_by_h[h_rem] = qinf_by_h[h_rem].add(da.mul(db));
            q1_by_h[h_rem] = q1_by_h[h_rem].add(a1.mul(b1));
        }
    }

    let mut q0 = Ext4::ZERO;
    let mut q_inf = Ext4::ZERO;
    let mut q1 = Ext4::ZERO;
    for h_rem in 0..rem_h_pairs {
        let w = suf_eq[h_rem];
        q0 = q0.add(w.mul(q0_by_h[h_rem]));
        q_inf = q_inf.add(w.mul(qinf_by_h[h_rem]));
        q1 = q1.add(w.mul(q1_by_h[h_rem]));
    }
    (q0, q_inf, q1)
}

/// Prove `claim = sum_{h, p} eq(z_s, h) * left[h, p] * right[h, p]` (`h` at low `mu_s` bits, `p` at high `kappa` bits)
/// over `124`-bit `Ext4` challenges using **zero prover inversions**! Returns `(proof, challenges)`.
pub fn prove_gruen_einsum_mode2_ext4(
    left_tab: &[Ext4],
    right_tab: &[Ext4],
    mu_s: usize,
    kappa: usize,
    z_s: &[Ext4],
    tr: &mut CShakeTranscript,
) -> (GruenMode2Ext4Proof, Vec<Ext4>) {
    let m = mu_s + kappa;
    assert_eq!(left_tab.len(), 1usize << m);
    assert_eq!(right_tab.len(), 1usize << m);
    assert_eq!(z_s.len(), mu_s);

    let ns = 1usize << mu_s;
    let nk = 1usize << kappa;
    let eq_h = build_eq_table_lsb_ext4(z_s);
    let mut claim = Ext4::ZERO;
    for q in 0..nk {
        let base = q << mu_s;
        for h in 0..ns {
            claim = claim.add(eq_h[h].mul(left_tab[base + h].mul(right_tab[base + h])));
        }
    }

    tr.absorb_ext4(b"gruen_claim", claim);
    tr.absorb_ext4_slice(b"gruen_zs", z_s);

    let suf_tables = build_eq_suffix_tables_ext4(z_s);
    let mut l_cur = left_tab.to_vec();
    let mut r_cur = right_tab.to_vec();
    let mut rounds = Vec::with_capacity(m);
    let mut challenges = Vec::with_capacity(m);

    for u in 0..mu_s {
        let suf = &suf_tables[mu_s - 1 - u];
        let (q0, q_inf, q1_dir) = gruen_f2_round_evals_ext4(&l_cur, &r_cur, suf, kappa);
        let msg = if z_s[u].is_zero() {
            tr.absorb_ext4(b"gruen_q0", q0);
            tr.absorb_ext4(b"gruen_qinf", q_inf);
            tr.absorb_ext4(b"gruen_q1_fb", q1_dir);
            GruenRoundExt4Msg::ZeroEqFallback {
                q0,
                q_inf,
                q1: q1_dir,
            }
        } else {
            tr.absorb_ext4(b"gruen_q0", q0);
            tr.absorb_ext4(b"gruen_qinf", q_inf);
            GruenRoundExt4Msg::TwoPoint { q0, q_inf }
        };
        rounds.push(msg);
        let ch = tr.squeeze_ext4(b"gruen_ch_s", true);
        challenges.push(ch);
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
    }

    for _v in 0..kappa {
        let half = l_cur.len() / 2;
        let mut q0 = Ext4::ZERO;
        let mut q_inf = Ext4::ZERO;
        for idx in 0..half {
            let a0 = l_cur[2 * idx];
            let a1 = l_cur[2 * idx + 1];
            let b0 = r_cur[2 * idx];
            let b1 = r_cur[2 * idx + 1];
            q0 = q0.add(a0.mul(b0));
            q_inf = q_inf.add(a1.sub(a0).mul(b1.sub(b0)));
        }
        tr.absorb_ext4(b"gruen_s_q0", q0);
        tr.absorb_ext4(b"gruen_s_qinf", q_inf);
        rounds.push(GruenRoundExt4Msg::TwoPoint { q0, q_inf });
        let ch = tr.squeeze_ext4(b"gruen_ch_k", true);
        challenges.push(ch);
        l_cur = fold_ext4(&l_cur, ch);
        r_cur = fold_ext4(&r_cur, ch);
    }

    let term = (l_cur[0], r_cur[0]);
    tr.absorb_ext4(b"gruen_term_a", term.0);
    tr.absorb_ext4(b"gruen_term_b", term.1);

    (
        GruenMode2Ext4Proof {
            claim,
            mu_s,
            kappa,
            rounds,
            terminal_openings: term,
        },
        challenges,
    )
}

/// Fail-closed `124`-bit `Ext4` Mode-2 `Gruen` `EinSumcheck` verifier. Returns recovered `challenges` on success.
pub fn verify_gruen_einsum_mode2_ext4(
    expected_claim: Ext4,
    z_s: &[Ext4],
    proof: &GruenMode2Ext4Proof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Ext4>, String> {
    let m = proof.mu_s + proof.kappa;
    if proof.claim != expected_claim {
        return Err("Gruen Mode-2 initial claim mismatch".to_string());
    }
    if z_s.len() != proof.mu_s || proof.rounds.len() != m {
        return Err("Gruen Mode-2 round/point length mismatch".to_string());
    }

    tr.absorb_ext4(b"gruen_claim", proof.claim);
    tr.absorb_ext4_slice(b"gruen_zs", z_s);

    let mut sigma = proof.claim;
    let mut challenges = Vec::with_capacity(m);

    for i in 0..m {
        if i < proof.mu_s {
            let r = z_s[i];
            if r.is_zero() {
                match proof.rounds[i] {
                    GruenRoundExt4Msg::ZeroEqFallback { q0, q_inf, q1 } => {
                        if q0 != sigma {
                            return Err(format!("Gruen ZeroEqFallback q0 != sigma at round {i}"));
                        }
                        tr.absorb_ext4(b"gruen_q0", q0);
                        tr.absorb_ext4(b"gruen_qinf", q_inf);
                        tr.absorb_ext4(b"gruen_q1_fb", q1);
                        let ch = tr.squeeze_ext4(b"gruen_ch_s", true);
                        challenges.push(ch);
                        sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
                    }
                    GruenRoundExt4Msg::TwoPoint { .. } => {
                        return Err(format!("expected ZeroEqFallback at round {i}"))
                    }
                }
            } else {
                match proof.rounds[i] {
                    GruenRoundExt4Msg::TwoPoint { q0, q_inf } => {
                        tr.absorb_ext4(b"gruen_q0", q0);
                        tr.absorb_ext4(b"gruen_qinf", q_inf);
                        let ch = tr.squeeze_ext4(b"gruen_ch_s", true);
                        challenges.push(ch);
                        let r_inv = r.inv().ok_or_else(|| "nonzero r failed inv".to_string())?;
                        let l0_q0 = Ext4::ONE.sub(r).mul(q0);
                        let q1 = r_inv.mul(sigma.sub(l0_q0));
                        sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
                    }
                    GruenRoundExt4Msg::ZeroEqFallback { .. } => {
                        return Err(format!("unexpected ZeroEqFallback at round {i}"))
                    }
                }
            }
        } else {
            match proof.rounds[i] {
                GruenRoundExt4Msg::TwoPoint { q0, q_inf } => {
                    tr.absorb_ext4(b"gruen_s_q0", q0);
                    tr.absorb_ext4(b"gruen_s_qinf", q_inf);
                    let ch = tr.squeeze_ext4(b"gruen_ch_k", true);
                    challenges.push(ch);
                    let q1 = sigma.sub(q0);
                    sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
                }
                GruenRoundExt4Msg::ZeroEqFallback { .. } => {
                    return Err(format!("unexpected ZeroEqFallback in S phase round {i}"))
                }
            }
        }
    }

    let (open_a, open_b) = proof.terminal_openings;
    tr.absorb_ext4(b"gruen_term_a", open_a);
    tr.absorb_ext4(b"gruen_term_b", open_b);

    if sigma != open_a.mul(open_b) {
        return Err("Gruen Mode-2 terminal sigma != open_a * open_b".to_string());
    }
    Ok(challenges)
}

// ===========================================================================
// §2. Strict-Lower-Triangularity Zerocheck `(1 - SLT(i, j)) * L[h, i, j] == 0`
// ===========================================================================

/// Public multilinear extension of `1 - SLT(i, j) = [i <= j]` on `{0,1}^{log_c} × {0,1}^{log_c}`
/// (`O(C^2)` = `4,096` ops at `C = 64`, `0` witness access!).
pub fn eval_upper_or_diag_indicator_mle(pt_i: &[Ext4], pt_j: &[Ext4]) -> Ext4 {
    assert_eq!(pt_i.len(), pt_j.len());
    let eq_i = build_eq_table_lsb_ext4(pt_i);
    let eq_j = build_eq_table_lsb_ext4(pt_j);
    let c = eq_i.len();
    let mut acc = Ext4::ZERO;
    for i in 0..c {
        let mut row_j = Ext4::ZERO;
        for j in i..c {
            row_j = row_j.add(eq_j[j]);
        }
        acc = acc.add(eq_i[i].mul(row_j));
    }
    acc
}

/// Prove `(1 - SLT(i, j)) * L[h, i, j] == 0` (`h` at bits `0..log_h`, `i` at `log_h..log_h+log_c`,
/// `j` at `log_h+log_c..log_h+2*log_c`) via 16-round `Ext4` Gruen Mode-2 zerocheck (`claim == 0`).
pub fn prove_strict_lower_tri_ext4(
    l_lsb_hij: &[u32],
    log_h: usize,
    log_c: usize,
    tr: &mut CShakeTranscript,
) -> (GruenMode2Ext4Proof, Vec<Ext4>) {
    let h_len = 1usize << log_h;
    let c_len = 1usize << log_c;
    let m = log_h + 2 * log_c;
    assert_eq!(l_lsb_hij.len(), 1usize << m);

    let z_s = tr.squeeze_ext4_vec(b"slt_zs", m, true);
    let mut ind_tab = vec![Ext4::ZERO; 1usize << m];
    let mut l_tab = vec![Ext4::ZERO; 1usize << m];
    for j in 0..c_len {
        for i in 0..c_len {
            let is_bad = if i <= j { Ext4::ONE } else { Ext4::ZERO };
            for h in 0..h_len {
                let idx = h + (i << log_h) + (j << (log_h + log_c));
                ind_tab[idx] = is_bad;
                l_tab[idx] = Ext4::from_bb(l_lsb_hij[idx]);
            }
        }
    }
    prove_gruen_einsum_mode2_ext4(&ind_tab, &l_tab, m, 0, &z_s, tr)
}

/// Verify `(1 - SLT) ⊙ L == 0` succinctly (`claim == 0` AND `open_a == eval_upper_or_diag_indicator_mle`)!
/// Returns `(point_hij, claimed_l_eval)` to be discharged against `L`'s `SuccinctExt4Pcs` commitment!
pub fn verify_strict_lower_tri_ext4(
    log_h: usize,
    log_c: usize,
    proof: &GruenMode2Ext4Proof,
    tr: &mut CShakeTranscript,
) -> Result<(Vec<Ext4>, Ext4), String> {
    let m = log_h + 2 * log_c;
    if proof.mu_s != m || proof.kappa != 0 || !proof.claim.is_zero() {
        return Err("strict-lower-triangularity zerocheck requires claim == 0".to_string());
    }
    let z_s = tr.squeeze_ext4_vec(b"slt_zs", m, true);
    let chals = verify_gruen_einsum_mode2_ext4(Ext4::ZERO, &z_s, proof, tr)?;
    let expected_ind =
        eval_upper_or_diag_indicator_mle(&chals[log_h..log_h + log_c], &chals[log_h + log_c..]);
    if proof.terminal_openings.0 != expected_ind {
        return Err("strict-lower-triangularity public indicator evaluation mismatch".to_string());
    }
    Ok((chals, proof.terminal_openings.1))
}

// ===========================================================================
// §3. Helper-Free `D1b` Projective Fraction-Tree LogUp-GKR (`ProveKit v2` §3.2 Subdomain Lifted)
// ===========================================================================

/// Per-round degree-3 `{p(0), p(1), p(2), p(∞)}` message in `Ext4` GKR layer sumcheck.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CubicExt4RoundMsg {
    pub p0: Ext4,
    pub p1: Ext4,
    pub p2: Ext4,
    pub p_inf: Ext4,
}

impl CubicExt4RoundMsg {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.p0.to_bytes());
        out.extend_from_slice(&self.p1.to_bytes());
        out.extend_from_slice(&self.p2.to_bytes());
        out.extend_from_slice(&self.p_inf.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        Ok(Self {
            p0: cur.read_ext4()?,
            p1: cur.read_ext4()?,
            p2: cur.read_ext4()?,
            p_inf: cur.read_ext4()?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct D1bLayerProof {
    pub rounds: Vec<CubicExt4RoundMsg>,
    pub p_lo: Ext4,
    pub p_hi: Ext4,
    pub q_lo: Ext4,
    pub q_hi: Ext4,
}

/// Complete `124`-bit `Ext4` Helper-Free `D1b` LogUp-GKR proof that all `2^m_wit` entries of `R_rem`
/// lie in `[0, 2^m_tab)` (`m_wit = 18 -> 262,144`, `m_tab = 12 -> 4,096`), using `ProveKit v2` §3.2
/// prefix subdomain lifting on the `2^m_tab` multiplicity commitment (`0` helper columns!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct D1bRangeExt4Proof {
    pub m_wit: usize,
    pub m_tab: usize,
    pub root_q: Ext4,
    pub layers: Vec<D1bLayerProof>,
    /// Terminal witness evaluation `R_rem_mle(z_leaf)` (verified against `R_rem`'s `SuccinctExt4Pcs`!).
    pub rem_leaf_eval: Ext4,
    /// Terminal multiplicity evaluation `mult_mle(z_leaf[..m_tab])` (verified against `mult`'s `4,096`-cell ZK PCS!).
    pub mult_leaf_eval: Ext4,
}

impl D1bRangeExt4Proof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.push(self.m_wit as u8);
        out.push(self.m_tab as u8);
        out.extend_from_slice(&self.root_q.to_bytes());
        out.extend_from_slice(&(self.layers.len() as u32).to_le_bytes());
        for lyr in &self.layers {
            out.extend_from_slice(&(lyr.rounds.len() as u32).to_le_bytes());
            for r in &lyr.rounds {
                r.write_to(out);
            }
            out.extend_from_slice(&lyr.p_lo.to_bytes());
            out.extend_from_slice(&lyr.p_hi.to_bytes());
            out.extend_from_slice(&lyr.q_lo.to_bytes());
            out.extend_from_slice(&lyr.q_hi.to_bytes());
        }
        out.extend_from_slice(&self.rem_leaf_eval.to_bytes());
        out.extend_from_slice(&self.mult_leaf_eval.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let m_wit = cur.read_u8()? as usize;
        let m_tab = cur.read_u8()? as usize;
        if m_wit == 0 || m_wit > 24 || m_tab == 0 || m_tab > m_wit {
            return Err("invalid D1bRangeExt4Proof dimensions".to_string());
        }
        let root_q = cur.read_ext4()?;
        let num_layers = cur.read_u32()? as usize;
        if num_layers != m_wit + 1 {
            return Err("D1b layer count mismatch".to_string());
        }
        let mut layers = Vec::with_capacity(num_layers);
        for _ in 0..num_layers {
            let n_rds = cur.read_u32()? as usize;
            if n_rds > m_wit {
                return Err("D1b round count overflow".to_string());
            }
            let mut rounds = Vec::with_capacity(n_rds);
            for _ in 0..n_rds {
                rounds.push(CubicExt4RoundMsg::read_from(cur)?);
            }
            layers.push(D1bLayerProof {
                rounds,
                p_lo: cur.read_ext4()?,
                p_hi: cur.read_ext4()?,
                q_lo: cur.read_ext4()?,
                q_hi: cur.read_ext4()?,
            });
        }
        let rem_leaf_eval = cur.read_ext4()?;
        let mult_leaf_eval = cur.read_ext4()?;
        Ok(Self {
            m_wit,
            m_tab,
            root_q,
            layers,
            rem_leaf_eval,
            mult_leaf_eval,
        })
    }
}

/// Histogram multiplicities of `rem_table` in `[0, 2^m_tab)`. Returns `Err` if any cell is out of range.
pub fn compute_d1b_multiplicities(rem_table: &[u32], m_tab: usize) -> Result<Vec<u32>, String> {
    let tab_len = 1usize << m_tab;
    let mut mult = vec![0u32; tab_len];
    for (idx, &v) in rem_table.iter().enumerate() {
        if (v as usize) >= tab_len {
            return Err(format!("R_rem[{idx}] = {v} out of range [0, {tab_len})"));
        }
        mult[v as usize] += 1;
    }
    Ok(mult)
}

/// Prove `forall k, rem_table[k] in [0, 2^m_tab)` via `124`-bit `Ext4` projective fraction-tree `D1b` LogUp-GKR!
/// Returns `(proof, leaf_point_m_wit)`.
///
/// Tree leaf layout (`2^{m_wit + 1}` leaves; `x` in `[0, 2^{m_wit})`, `side` in `{0, 1}` at MSB `bit m_wit`
/// so pair `(2*x, 2*x + 1)` combines at every tree layer):
/// Wait: pairing `(x, 0)` at `2*x` and `(x, 1)` at `2*x + 1` or `side` at MSB `x + side * 2^{m_wit}`?
/// With `side` at MSB (`index = x + (side << m_wit)`):
/// At each tree reduction layer `d`, node `y` combines `2*y` and `2*y + 1` (LSB pair!).
/// Thus the LAST tree reduction layer (`1` pair -> root) combines `side = 0` (witness sum) and `side = 1` (table sum)!
pub fn prove_d1b_range_ext4(
    rem_table: &[u32],
    mult_table: &[u32],
    m_wit: usize,
    m_tab: usize,
    tr: &mut CShakeTranscript,
) -> (D1bRangeExt4Proof, Vec<Ext4>) {
    let n_wit = 1usize << m_wit;
    let n_tab = 1usize << m_tab;
    assert_eq!(rem_table.len(), n_wit);
    assert_eq!(mult_table.len(), n_tab);

    let alpha = tr.squeeze_ext4(b"d1b_alpha", true);

    // Level 0 (`2^{m_wit + 1}` leaves):
    //   `0 .. n_wit`: `P = 1`, `Q = alpha - rem_table[x]`
    //   `n_wit .. 2*n_wit`:
    //     Under `ProveKit v2` §3.2 prefix subdomain lifting on high bits `m_tab .. m_wit` (`x_hi == 0` -> `x < n_tab`):
    //     For `x < n_tab`: `P = -mult_table[x]`, `Q = alpha - x`.
    //     For `x >= n_tab`: `P = 0`, `Q = alpha - (x & (n_tab - 1))` (non-zero everywhere since `alpha not in F_p`
    //     with prob `1 - p/p^4 = 1 - p^{-3} > 1 - 2^{-92}`, and publicly evaluable in `m_tab` ops!).
    let total_leaves = n_wit * 2;
    let mut p_zero_layers: Vec<Vec<Ext4>> = Vec::with_capacity(m_wit + 2);
    let mut q_zero_layers: Vec<Vec<Ext4>> = Vec::with_capacity(m_wit + 2);

    let mut p0 = vec![Ext4::ZERO; total_leaves];
    let mut q0 = vec![Ext4::ZERO; total_leaves];
    p0[..n_wit]
        .par_iter_mut()
        .zip(q0[..n_wit].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            *pd = Ext4::ONE;
            *qd = alpha.sub(Ext4::from_bb(rem_table[x] % P_U32));
        });
    let mask_tab = n_tab - 1;
    p0[n_wit..]
        .par_iter_mut()
        .zip(q0[n_wit..].par_iter_mut())
        .enumerate()
        .for_each(|(x, (pd, qd))| {
            if x < n_tab {
                let m_bb = mult_table[x] % P_U32;
                *pd = Ext4::from_bb(if m_bb == 0 { 0 } else { P_U32 - m_bb });
            } else {
                *pd = Ext4::ZERO;
            }
            *qd = alpha.sub(Ext4::from_bb((x & mask_tab) as u32));
        });

    p_zero_layers.push(p0);
    q_zero_layers.push(q0);

    // Build binary projective fraction tree (`m_wit + 1` reduction steps to 1 root pair `(root_P, root_Q)`).
    for _lvl in 0..=m_wit {
        let prev_p = p_zero_layers.last().unwrap();
        let prev_q = q_zero_layers.last().unwrap();
        let next_len = prev_p.len() / 2;
        let mut next_p = vec![Ext4::ZERO; next_len];
        let mut next_q = vec![Ext4::ZERO; next_len];
        next_p
            .par_iter_mut()
            .zip(next_q.par_iter_mut())
            .enumerate()
            .for_each(|(i, (np, nq))| {
                let pl = prev_p[2 * i];
                let pr = prev_p[2 * i + 1];
                let ql = prev_q[2 * i];
                let qr = prev_q[2 * i + 1];
                *np = pl.mul(qr).add(pr.mul(ql));
                *nq = ql.mul(qr);
            });
        p_zero_layers.push(next_p);
        q_zero_layers.push(next_q);
    }

    let root_p = p_zero_layers.last().unwrap()[0];
    let root_q = q_zero_layers.last().unwrap()[0];
    debug_assert!(root_p.is_zero() && !root_q.is_zero());

    tr.absorb_ext4(b"d1b_root_q", root_q);

    // Top-down GKR reduction from root (`lvl = m_wit`, `0` parent vars) down to leaves (`lvl = 0`, `m_wit` parent vars).
    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO;
    let mut cur_q_claim = root_q;
    let mut layer_proofs = Vec::with_capacity(m_wit + 1);

    for step in 0..=m_wit {
        let child_lvl = m_wit - step; // child has `step + 1` variables (`1` LSB pair bit + `step` parent vars)
        let child_p = &p_zero_layers[child_lvl];
        let child_q = &q_zero_layers[child_lvl];
        let num_vars = step; // `cur_pt.len() == step`

        let eta = tr.squeeze_ext4(b"d1b_eta", true);
        let _combined_claim = cur_p_claim.add(eta.mul(cur_q_claim));

        // Split child tables into even (`bit 0 = 0`, length `2^num_vars`) and odd (`bit 0 = 1`, length `2^num_vars`).
        let half = 1usize << num_vars;
        let mut pl_cur = Vec::with_capacity(half);
        let mut pr_cur = Vec::with_capacity(half);
        let mut ql_cur = Vec::with_capacity(half);
        let mut qr_cur = Vec::with_capacity(half);
        for i in 0..half {
            pl_cur.push(child_p[2 * i]);
            pr_cur.push(child_p[2 * i + 1]);
            ql_cur.push(child_q[2 * i]);
            qr_cur.push(child_q[2 * i + 1]);
        }

        let mut eq_cur = build_eq_table_lsb_ext4(&cur_pt);
        let mut rounds = Vec::with_capacity(num_vars);
        let mut sum_chals = Vec::with_capacity(num_vars);

        for _r in 0..num_vars {
            let h2 = eq_cur.len() / 2;
            let mut p0_acc = Ext4::ZERO;
            let mut p1_acc = Ext4::ZERO;
            let mut p2_acc = Ext4::ZERO;
            let mut pinf_acc = Ext4::ZERO;
            let two = Ext4::from_bb(2);

            for idx in 0..h2 {
                let e0 = eq_cur[2 * idx];
                let e1 = eq_cur[2 * idx + 1];
                let de = e1.sub(e0);
                let e2 = e0.add(two.mul(de));

                let pl0 = pl_cur[2 * idx];
                let pl1 = pl_cur[2 * idx + 1];
                let dpl = pl1.sub(pl0);
                let pl2 = pl0.add(two.mul(dpl));

                let pr0 = pr_cur[2 * idx];
                let pr1 = pr_cur[2 * idx + 1];
                let dpr = pr1.sub(pr0);
                let pr2 = pr0.add(two.mul(dpr));

                let ql0 = ql_cur[2 * idx];
                let ql1 = ql_cur[2 * idx + 1];
                let dql = ql1.sub(ql0);
                let ql2 = ql0.add(two.mul(dql));

                let qr0 = qr_cur[2 * idx];
                let qr1 = qr_cur[2 * idx + 1];
                let dqr = qr1.sub(qr0);
                let qr2 = qr0.add(two.mul(dqr));

                let num0 = pl0.mul(qr0).add(pr0.mul(ql0));
                let den0 = ql0.mul(qr0);
                p0_acc = p0_acc.add(e0.mul(num0.add(eta.mul(den0))));

                let num1 = pl1.mul(qr1).add(pr1.mul(ql1));
                let den1 = ql1.mul(qr1);
                p1_acc = p1_acc.add(e1.mul(num1.add(eta.mul(den1))));

                let num2 = pl2.mul(qr2).add(pr2.mul(ql2));
                let den2 = ql2.mul(qr2);
                p2_acc = p2_acc.add(e2.mul(num2.add(eta.mul(den2))));

                let num_inf = dpl.mul(dqr).add(dpr.mul(dql));
                let den_inf = dql.mul(dqr);
                pinf_acc = pinf_acc.add(de.mul(num_inf.add(eta.mul(den_inf))));
            }

            let msg = CubicExt4RoundMsg {
                p0: p0_acc,
                p1: p1_acc,
                p2: p2_acc,
                p_inf: pinf_acc,
            };
            tr.absorb_ext4(b"d1b_c0", msg.p0);
            tr.absorb_ext4(b"d1b_c1", msg.p1);
            tr.absorb_ext4(b"d1b_c2", msg.p2);
            tr.absorb_ext4(b"d1b_cinf", msg.p_inf);
            rounds.push(msg);

            let ch = tr.squeeze_ext4(b"d1b_ch", true);
            sum_chals.push(ch);
            eq_cur = fold_ext4(&eq_cur, ch);
            pl_cur = fold_ext4(&pl_cur, ch);
            pr_cur = fold_ext4(&pr_cur, ch);
            ql_cur = fold_ext4(&ql_cur, ch);
            qr_cur = fold_ext4(&qr_cur, ch);
        }

        let p_lo = pl_cur[0];
        let p_hi = pr_cur[0];
        let q_lo = ql_cur[0];
        let q_hi = qr_cur[0];
        tr.absorb_ext4(b"d1b_plo", p_lo);
        tr.absorb_ext4(b"d1b_phi", p_hi);
        tr.absorb_ext4(b"d1b_qlo", q_lo);
        tr.absorb_ext4(b"d1b_qhi", q_hi);

        let r_bit = tr.squeeze_ext4(b"d1b_rbit", true);
        cur_p_claim = p_lo.add(r_bit.mul(p_hi.sub(p_lo)));
        cur_q_claim = q_lo.add(r_bit.mul(q_hi.sub(q_lo)));

        let mut next_pt = Vec::with_capacity(num_vars + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;

        layer_proofs.push(D1bLayerProof {
            rounds,
            p_lo,
            p_hi,
            q_lo,
            q_hi,
        });
    }

    // `cur_pt` now has length `m_wit + 1`: `cur_pt[0..m_wit]` indexes `x in [0, 2^m_wit)` and `cur_pt[m_wit]`
    // indexes `side in {0, 1}`!
    let z_leaf = cur_pt[..m_wit].to_vec();
    let rem_leaf_eval = crate::ext4::mle_eval_bb_at_ext4(rem_table, &z_leaf);
    let mult_leaf_eval = crate::ext4::mle_eval_bb_at_ext4(mult_table, &z_leaf[..m_tab]);
    tr.absorb_ext4(b"d1b_rem_eval", rem_leaf_eval);
    tr.absorb_ext4(b"d1b_mult_eval", mult_leaf_eval);

    (
        D1bRangeExt4Proof {
            m_wit,
            m_tab,
            root_q,
            layers: layer_proofs,
            rem_leaf_eval,
            mult_leaf_eval,
        },
        z_leaf,
    )
}

/// Standalone `D1b` LogUp-GKR verifier! Returns `z_leaf` (`m_wit` `Ext4` coords) so the caller verifies
/// `proof.rem_leaf_eval == R_rem_pcs(z_leaf)` and `proof.mult_leaf_eval == mult_pcs(z_leaf[..m_tab])`!
pub fn verify_d1b_range_ext4(
    proof: &D1bRangeExt4Proof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Ext4>, String> {
    if proof.root_q.is_zero() {
        return Err("D1b root_q == 0 (denominator pole)".to_string());
    }
    if proof.layers.len() != proof.m_wit + 1 {
        return Err("D1b layer count mismatch".to_string());
    }
    let alpha = tr.squeeze_ext4(b"d1b_alpha", true);
    tr.absorb_ext4(b"d1b_root_q", proof.root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO; // `root_P == 0` enforced!
    let mut cur_q_claim = proof.root_q;

    for (step, lyr) in proof.layers.iter().enumerate() {
        if lyr.rounds.len() != step {
            return Err(format!("D1b step {step} round count mismatch"));
        }
        let eta = tr.squeeze_ext4(b"d1b_eta", true);
        let mut sigma = cur_p_claim.add(eta.mul(cur_q_claim));
        let mut sum_chals = Vec::with_capacity(step);

        for (r_idx, msg) in lyr.rounds.iter().enumerate() {
            if msg.p0.add(msg.p1) != sigma {
                return Err(format!("D1b cubic sumcheck failed at step {step} round {r_idx}"));
            }
            tr.absorb_ext4(b"d1b_c0", msg.p0);
            tr.absorb_ext4(b"d1b_c1", msg.p1);
            tr.absorb_ext4(b"d1b_c2", msg.p2);
            tr.absorb_ext4(b"d1b_cinf", msg.p_inf);
            let ch = tr.squeeze_ext4(b"d1b_ch", true);
            sum_chals.push(ch);
            sigma = eval_cubic_zero_one_two_inf_ext4(msg.p0, msg.p1, msg.p2, msg.p_inf, ch);
        }

        tr.absorb_ext4(b"d1b_plo", lyr.p_lo);
        tr.absorb_ext4(b"d1b_phi", lyr.p_hi);
        tr.absorb_ext4(b"d1b_qlo", lyr.q_lo);
        tr.absorb_ext4(b"d1b_qhi", lyr.q_hi);

        let eq_eval = crate::ext4::eq_mle_ext4(&cur_pt, &sum_chals);
        let num_val = lyr.p_lo.mul(lyr.q_hi).add(lyr.p_hi.mul(lyr.q_lo));
        let den_val = lyr.q_lo.mul(lyr.q_hi);
        let expected_sigma = eq_eval.mul(num_val.add(eta.mul(den_val)));
        if sigma != expected_sigma {
            return Err(format!("D1b terminal layer check failed at step {step}"));
        }

        let r_bit = tr.squeeze_ext4(b"d1b_rbit", true);
        cur_p_claim = lyr.p_lo.add(r_bit.mul(lyr.p_hi.sub(lyr.p_lo)));
        cur_q_claim = lyr.q_lo.add(r_bit.mul(lyr.q_hi.sub(lyr.q_lo)));

        let mut next_pt = Vec::with_capacity(step + 1);
        next_pt.push(r_bit);
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
    }

    tr.absorb_ext4(b"d1b_rem_eval", proof.rem_leaf_eval);
    tr.absorb_ext4(b"d1b_mult_eval", proof.mult_leaf_eval);

    // Leaf consistency check (`ProveKit v2` §3.2 prefix subdomain lift + public table `[0..2^m_tab)`):
    let z_leaf = &cur_pt[..proof.m_wit];
    let z_side = cur_pt[proof.m_wit];

    let p_wit = Ext4::ONE;
    let q_wit = alpha.sub(proof.rem_leaf_eval);

    let mut subdomain_zero_prefix = Ext4::ONE;
    for &zb in &z_leaf[proof.m_tab..] {
        subdomain_zero_prefix = subdomain_zero_prefix.mul(Ext4::ONE.sub(zb));
    }
    let p_tab = subdomain_zero_prefix.mul(proof.mult_leaf_eval).neg();

    let mut iota_tab = Ext4::ZERO;
    for (bit, &zb) in z_leaf[..proof.m_tab].iter().enumerate() {
        iota_tab = iota_tab.add(zb.scale_bb(1u32 << bit));
    }
    let q_tab = alpha.sub(iota_tab);

    let expected_p = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(p_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(p_tab));
    let expected_q = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(q_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(q_tab));

    if cur_p_claim != expected_p || cur_q_claim != expected_q {
        return Err("D1b leaf witness/table equation mismatch".to_string());
    }

    Ok(z_leaf.to_vec())
}

/// Prove `forall k in [0, 2^m_wit), wit_table[k] in pub_table[0..2^m_tab)` for an arbitrary public
/// lookup table `pub_table` (e.g., the 1,280-entry byte-DFA transition table `(q, b, delta(q, b))`)!
pub fn compute_d1b_public_table_multiplicities(
    wit_table: &[u32],
    pub_table: &[u32],
) -> Result<Vec<u32>, String> {
    assert!(pub_table.len().is_power_of_two());
    let mut val_to_slot = std::collections::HashMap::with_capacity(pub_table.len());
    for (slot, &tv) in pub_table.iter().enumerate() {
        val_to_slot.entry(tv).or_insert(slot);
    }
    let mut mult = vec![0u32; pub_table.len()];
    for (idx, &w) in wit_table.iter().enumerate() {
        let slot = val_to_slot
            .get(&w)
            .ok_or_else(|| format!("witness[{idx}] = {w} not in public table"))?;
        mult[*slot] += 1;
    }
    Ok(mult)
}

pub fn prove_d1b_public_table_ext4(
    wit_table: &[u32],
    pub_table: &[u32],
    mult_table: &[u32],
    tr: &mut CShakeTranscript,
) -> (D1bRangeExt4Proof, Vec<Ext4>) {
    let n_wit = wit_table.len();
    let n_tab = pub_table.len();
    assert!(n_wit.is_power_of_two() && n_tab.is_power_of_two() && n_tab == mult_table.len());
    let m_wit = n_wit.trailing_zeros() as usize;
    let m_tab = n_tab.trailing_zeros() as usize;
    assert!(m_tab <= m_wit, "pad wit_table so m_wit >= m_tab");

    let alpha = tr.squeeze_ext4(b"d1b_pub_alpha", true);
    let total_leaves = n_wit * 2;
    let mut p0 = vec![Ext4::ZERO; total_leaves];
    let mut q0 = vec![Ext4::ZERO; total_leaves];
    for x in 0..n_wit {
        p0[x] = Ext4::ONE;
        q0[x] = alpha.sub(Ext4::from_bb(wit_table[x] % P_U32));
    }
    let mask_tab = n_tab - 1;
    for x in 0..n_wit {
        p0[n_wit + x] = if x < n_tab {
            let m_bb = mult_table[x] % P_U32;
            Ext4::from_bb(if m_bb == 0 { 0 } else { P_U32 - m_bb })
        } else {
            Ext4::ZERO
        };
        q0[n_wit + x] = alpha.sub(Ext4::from_bb(pub_table[x & mask_tab] % P_U32));
    }

    let mut p_zero_layers = vec![p0];
    let mut q_zero_layers = vec![q0];
    for _lvl in 0..=m_wit {
        let prev_p = p_zero_layers.last().unwrap();
        let prev_q = q_zero_layers.last().unwrap();
        let next_len = prev_p.len() / 2;
        let mut next_p = vec![Ext4::ZERO; next_len];
        let mut next_q = vec![Ext4::ZERO; next_len];
        for i in 0..next_len {
            let pl = prev_p[2 * i];
            let pr = prev_p[2 * i + 1];
            let ql = prev_q[2 * i];
            let qr = prev_q[2 * i + 1];
            next_p[i] = pl.mul(qr).add(pr.mul(ql));
            next_q[i] = ql.mul(qr);
        }
        p_zero_layers.push(next_p);
        q_zero_layers.push(next_q);
    }

    let root_q = q_zero_layers.last().unwrap()[0];
    tr.absorb_ext4(b"d1b_pub_root_q", root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO;
    let mut cur_q_claim = root_q;
    let mut layer_proofs = Vec::with_capacity(m_wit + 1);
    let two = Ext4::from_bb(2);

    for step in 0..=m_wit {
        let child_lvl = m_wit - step;
        let child_p = &p_zero_layers[child_lvl];
        let child_q = &q_zero_layers[child_lvl];
        let eta = tr.squeeze_ext4(b"d1b_pub_eta", true);

        let half = 1usize << step;
        let mut pl_cur = (0..half).map(|i| child_p[2 * i]).collect::<Vec<_>>();
        let mut pr_cur = (0..half).map(|i| child_p[2 * i + 1]).collect::<Vec<_>>();
        let mut ql_cur = (0..half).map(|i| child_q[2 * i]).collect::<Vec<_>>();
        let mut qr_cur = (0..half).map(|i| child_q[2 * i + 1]).collect::<Vec<_>>();
        let mut eq_cur = build_eq_table_lsb_ext4(&cur_pt);

        let mut rounds = Vec::with_capacity(step);
        let mut sum_chals = Vec::with_capacity(step);
        for _r in 0..step {
            let h2 = eq_cur.len() / 2;
            let mut p0_acc = Ext4::ZERO;
            let mut p1_acc = Ext4::ZERO;
            let mut p2_acc = Ext4::ZERO;
            let mut pinf_acc = Ext4::ZERO;
            for idx in 0..h2 {
                let (e0, e1) = (eq_cur[2 * idx], eq_cur[2 * idx + 1]);
                let de = e1.sub(e0);
                let e2 = e0.add(two.mul(de));
                let (pl0, pl1) = (pl_cur[2 * idx], pl_cur[2 * idx + 1]);
                let dpl = pl1.sub(pl0);
                let pl2 = pl0.add(two.mul(dpl));
                let (pr0, pr1) = (pr_cur[2 * idx], pr_cur[2 * idx + 1]);
                let dpr = pr1.sub(pr0);
                let pr2 = pr0.add(two.mul(dpr));
                let (ql0, ql1) = (ql_cur[2 * idx], ql_cur[2 * idx + 1]);
                let dql = ql1.sub(ql0);
                let ql2 = ql0.add(two.mul(dql));
                let (qr0, qr1) = (qr_cur[2 * idx], qr_cur[2 * idx + 1]);
                let dqr = qr1.sub(qr0);
                let qr2 = qr0.add(two.mul(dqr));

                p0_acc = p0_acc.add(e0.mul(pl0.mul(qr0).add(pr0.mul(ql0)).add(eta.mul(ql0.mul(qr0)))));
                p1_acc = p1_acc.add(e1.mul(pl1.mul(qr1).add(pr1.mul(ql1)).add(eta.mul(ql1.mul(qr1)))));
                p2_acc = p2_acc.add(e2.mul(pl2.mul(qr2).add(pr2.mul(ql2)).add(eta.mul(ql2.mul(qr2)))));
                pinf_acc = pinf_acc
                    .add(de.mul(dpl.mul(dqr).add(dpr.mul(dql)).add(eta.mul(dql.mul(dqr)))));
            }
            let msg = CubicExt4RoundMsg {
                p0: p0_acc,
                p1: p1_acc,
                p2: p2_acc,
                p_inf: pinf_acc,
            };
            tr.absorb_ext4(b"d1b_pub_c0", msg.p0);
            tr.absorb_ext4(b"d1b_pub_c1", msg.p1);
            tr.absorb_ext4(b"d1b_pub_c2", msg.p2);
            tr.absorb_ext4(b"d1b_pub_cinf", msg.p_inf);
            rounds.push(msg);
            let ch = tr.squeeze_ext4(b"d1b_pub_ch", true);
            sum_chals.push(ch);
            eq_cur = fold_ext4(&eq_cur, ch);
            pl_cur = fold_ext4(&pl_cur, ch);
            pr_cur = fold_ext4(&pr_cur, ch);
            ql_cur = fold_ext4(&ql_cur, ch);
            qr_cur = fold_ext4(&qr_cur, ch);
        }

        let (p_lo, p_hi, q_lo, q_hi) = (pl_cur[0], pr_cur[0], ql_cur[0], qr_cur[0]);
        tr.absorb_ext4(b"d1b_pub_plo", p_lo);
        tr.absorb_ext4(b"d1b_pub_phi", p_hi);
        tr.absorb_ext4(b"d1b_pub_qlo", q_lo);
        tr.absorb_ext4(b"d1b_pub_qhi", q_hi);
        let r_bit = tr.squeeze_ext4(b"d1b_pub_rbit", true);
        cur_p_claim = p_lo.add(r_bit.mul(p_hi.sub(p_lo)));
        cur_q_claim = q_lo.add(r_bit.mul(q_hi.sub(q_lo)));

        let mut next_pt = vec![r_bit];
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
        layer_proofs.push(D1bLayerProof {
            rounds,
            p_lo,
            p_hi,
            q_lo,
            q_hi,
        });
    }
    let _ = cur_p_claim;
    let _ = cur_q_claim;
    let z_leaf = cur_pt[..m_wit].to_vec();
    let rem_leaf_eval = crate::ext4::mle_eval_bb_at_ext4(wit_table, &z_leaf);
    let mult_leaf_eval = crate::ext4::mle_eval_bb_at_ext4(mult_table, &z_leaf[..m_tab]);
    tr.absorb_ext4(b"d1b_pub_wit_ev", rem_leaf_eval);
    tr.absorb_ext4(b"d1b_pub_mult_ev", mult_leaf_eval);

    (
        D1bRangeExt4Proof {
            m_wit,
            m_tab,
            root_q,
            layers: layer_proofs,
            rem_leaf_eval,
            mult_leaf_eval,
        },
        z_leaf,
    )
}

pub fn verify_d1b_public_table_ext4(
    pub_table: &[u32],
    proof: &D1bRangeExt4Proof,
    tr: &mut CShakeTranscript,
) -> Result<Vec<Ext4>, String> {
    if !pub_table.len().is_power_of_two() || pub_table.len() != (1usize << proof.m_tab) {
        return Err("public table size mismatch".to_string());
    }
    if proof.root_q.is_zero() || proof.layers.len() != proof.m_wit + 1 {
        return Err("D1b public-table root_q == 0 or layer count mismatch".to_string());
    }
    let alpha = tr.squeeze_ext4(b"d1b_pub_alpha", true);
    tr.absorb_ext4(b"d1b_pub_root_q", proof.root_q);

    let mut cur_pt: Vec<Ext4> = Vec::new();
    let mut cur_p_claim = Ext4::ZERO;
    let mut cur_q_claim = proof.root_q;

    for (step, lyr) in proof.layers.iter().enumerate() {
        if lyr.rounds.len() != step {
            return Err("D1b public-table round count mismatch".to_string());
        }
        let eta = tr.squeeze_ext4(b"d1b_pub_eta", true);
        let mut sigma = cur_p_claim.add(eta.mul(cur_q_claim));
        let mut sum_chals = Vec::with_capacity(step);
        for msg in &lyr.rounds {
            if msg.p0.add(msg.p1) != sigma {
                return Err("D1b public-table sumcheck round mismatch".to_string());
            }
            tr.absorb_ext4(b"d1b_pub_c0", msg.p0);
            tr.absorb_ext4(b"d1b_pub_c1", msg.p1);
            tr.absorb_ext4(b"d1b_pub_c2", msg.p2);
            tr.absorb_ext4(b"d1b_pub_cinf", msg.p_inf);
            let ch = tr.squeeze_ext4(b"d1b_pub_ch", true);
            sum_chals.push(ch);
            sigma = eval_cubic_zero_one_two_inf_ext4(msg.p0, msg.p1, msg.p2, msg.p_inf, ch);
        }
        tr.absorb_ext4(b"d1b_pub_plo", lyr.p_lo);
        tr.absorb_ext4(b"d1b_pub_phi", lyr.p_hi);
        tr.absorb_ext4(b"d1b_pub_qlo", lyr.q_lo);
        tr.absorb_ext4(b"d1b_pub_qhi", lyr.q_hi);

        let eq_eval = crate::ext4::eq_mle_ext4(&cur_pt, &sum_chals);
        let num_val = lyr.p_lo.mul(lyr.q_hi).add(lyr.p_hi.mul(lyr.q_lo));
        let den_val = lyr.q_lo.mul(lyr.q_hi);
        if sigma != eq_eval.mul(num_val.add(eta.mul(den_val))) {
            return Err("D1b public-table terminal layer mismatch".to_string());
        }
        let r_bit = tr.squeeze_ext4(b"d1b_pub_rbit", true);
        cur_p_claim = lyr.p_lo.add(r_bit.mul(lyr.p_hi.sub(lyr.p_lo)));
        cur_q_claim = lyr.q_lo.add(r_bit.mul(lyr.q_hi.sub(lyr.q_lo)));
        let mut next_pt = vec![r_bit];
        next_pt.extend_from_slice(&sum_chals);
        cur_pt = next_pt;
    }

    tr.absorb_ext4(b"d1b_pub_wit_ev", proof.rem_leaf_eval);
    tr.absorb_ext4(b"d1b_pub_mult_ev", proof.mult_leaf_eval);

    let z_leaf = &cur_pt[..proof.m_wit];
    let z_side = cur_pt[proof.m_wit];
    let mut subdomain_zero_prefix = Ext4::ONE;
    for &zb in &z_leaf[proof.m_tab..] {
        subdomain_zero_prefix = subdomain_zero_prefix.mul(Ext4::ONE.sub(zb));
    }
    let p_tab = subdomain_zero_prefix.mul(proof.mult_leaf_eval).neg();
    let pub_tab_eval = crate::ext4::mle_eval_bb_at_ext4(pub_table, &z_leaf[..proof.m_tab]);
    let q_tab = alpha.sub(pub_tab_eval);
    let q_wit = alpha.sub(proof.rem_leaf_eval);

    let expected_p = eq_lin_ext4(z_side, Ext4::ZERO)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(p_tab));
    let expected_q = eq_lin_ext4(z_side, Ext4::ZERO)
        .mul(q_wit)
        .add(eq_lin_ext4(z_side, Ext4::ONE).mul(q_tab));
    if cur_p_claim != expected_p || cur_q_claim != expected_q {
        return Err("D1b public-table leaf check failed".to_string());
    }
    Ok(z_leaf.to_vec())
}

// ===========================================================================
// §4. `124`-Bit `Ext4` Delayed Block-Bind (`b -> j -> k`) + 7-Bucket 0-Mul E2M1 Horner
// ===========================================================================

/// Zero-multiplication 7-bucket E2M1 Horner dot product over `Ext4` (`pure additions & subtractions`, `0` muls!).
#[inline]
pub fn e2m1_horner_dot_ext4(q_nibbles: &[u8], vec: &[Ext4]) -> Ext4 {
    debug_assert_eq!(q_nibbles.len(), vec.len());
    let mut b = [Ext4::ZERO; 8];
    for (&nib, &v) in q_nibbles.iter().zip(vec.iter()) {
        let mag = (nib & 7) as usize;
        if mag != 0 {
            if (nib & 8) == 0 {
                b[mag] = b[mag].add(v);
            } else {
                b[mag] = b[mag].sub(v);
            }
        }
    }
    let c8 = b[6].add(b[7]);
    let c4 = b[4].add(b[5]).add(b[7]);
    let c2 = b[2].add(b[3]).add(b[5]);
    let c1 = b[1].add(b[3]);
    let d8 = c8.add(c8).add(c4);
    let d4 = d8.add(d8).add(c2);
    d4.add(d4).add(c1)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CubicZeroTwoInfExt4Msg {
    pub p0: Ext4,
    pub p2: Ext4,
    pub p_inf: Ext4,
}

impl CubicZeroTwoInfExt4Msg {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.p0.to_bytes());
        out.extend_from_slice(&self.p2.to_bytes());
        out.extend_from_slice(&self.p_inf.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        Ok(Self {
            p0: cur.read_ext4()?,
            p2: cur.read_ext4()?,
            p_inf: cur.read_ext4()?,
        })
    }
}

/// Complete `124`-bit `Ext4` transcript for `Y_raw[i, j] = sum_{k, b} X[i, k, b] · Q_e2m1[j, k, b] · S[j, k]`
/// (`b -> j -> k`, `l_0 = 5`, `0` multiplications on `Q_nibbles`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mxfp4DelayedBjkExt4Proof {
    pub claim: Ext4,
    pub log_j: usize,
    pub log_k: usize,
    pub b_rounds: [[Ext4; 2]; 5],
    pub j_rounds: Vec<GruenRoundExt4Msg>,
    pub k_rounds: Vec<CubicZeroTwoInfExt4Msg>,
    /// Terminal evaluations `(X̂(r_i, c_b, c_k), Q̂(c_b, c_j, c_k), Ŝ(c_j, c_k))`.
    pub finals: (Ext4, Ext4, Ext4),
}

impl Mxfp4DelayedBjkExt4Proof {
    pub fn write_to(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.claim.to_bytes());
        out.push(self.log_j as u8);
        out.push(self.log_k as u8);
        for br in &self.b_rounds {
            out.extend_from_slice(&br[0].to_bytes());
            out.extend_from_slice(&br[1].to_bytes());
        }
        for jr in &self.j_rounds {
            jr.write_to(out);
        }
        for kr in &self.k_rounds {
            kr.write_to(out);
        }
        out.extend_from_slice(&self.finals.0.to_bytes());
        out.extend_from_slice(&self.finals.1.to_bytes());
        out.extend_from_slice(&self.finals.2.to_bytes());
    }

    pub fn read_from(cur: &mut ByteCursor) -> Result<Self, String> {
        let claim = cur.read_ext4()?;
        let log_j = cur.read_u8()? as usize;
        let log_k = cur.read_u8()? as usize;
        if log_j == 0 || log_j > 20 || log_k == 0 || log_k > 16 {
            return Err("invalid Mxfp4DelayedBjkExt4Proof dimensions".to_string());
        }
        let mut b_rounds = [[Ext4::ZERO; 2]; 5];
        for br in &mut b_rounds {
            br[0] = cur.read_ext4()?;
            br[1] = cur.read_ext4()?;
        }
        let mut j_rounds = Vec::with_capacity(log_j);
        for _ in 0..log_j {
            j_rounds.push(GruenRoundExt4Msg::read_from(cur)?);
        }
        let mut k_rounds = Vec::with_capacity(log_k);
        for _ in 0..log_k {
            k_rounds.push(CubicZeroTwoInfExt4Msg::read_from(cur)?);
        }
        let fx = cur.read_ext4()?;
        let fq = cur.read_ext4()?;
        let fs = cur.read_ext4()?;
        Ok(Self {
            claim,
            log_j,
            log_k,
            b_rounds,
            j_rounds,
            k_rounds,
            finals: (fx, fq, fs),
        })
    }
}

pub struct Mxfp4SolvedChallenges {
    pub chals_b: [Ext4; 5],
    pub chals_j: Vec<Ext4>,
    pub chals_k: Vec<Ext4>,
}

/// Multithreaded (`rayon`) `124`-bit `Ext4` MXFP4 delayed-bind 0-mul E2M1 Horner prover (`b -> j -> k`).
pub fn prove_mxfp4_delayed_bjk_horner_ext4(
    x_ri: &[Ext4],
    q_nibbles: &[u8],
    s_scale: &[u32],
    log_j: usize,
    log_k: usize,
    r_j: &[Ext4],
    tr: &mut CShakeTranscript,
) -> (Mxfp4DelayedBjkExt4Proof, Mxfp4SolvedChallenges) {
    let j_len = 1usize << log_j;
    let k_len = 1usize << log_k;
    assert_eq!(x_ri.len(), k_len * 32);
    assert_eq!(q_nibbles.len(), j_len * k_len * 32);
    assert_eq!(s_scale.len(), j_len * k_len);
    assert_eq!(r_j.len(), log_j);

    // Step 1: `E_jk[j, k] = eq(r_j, j) · S[j, k]` (`4` base muls per `S[j, k]`, `32×` smaller than `Q`!)
    let eq_j = build_eq_table_lsb_ext4(r_j);
    let mut e_jk = vec![Ext4::ZERO; j_len * k_len];
    e_jk.par_chunks_mut(k_len)
        .enumerate()
        .for_each(|(j, row_dst)| {
            let ej = eq_j[j];
            let s_row = &s_scale[j * k_len..(j + 1) * k_len];
            for k in 0..k_len {
                row_dst[k] = ej.scale_bb(s_row[k]);
            }
        });

    // Step 2: Collapse `M[k, b] = sum_j E_jk[j, k] · Q[j, k, b]` via 7-bucket 0-mul E2M1 Horner in `rayon` parallel over `k`!
    let mut m_kb = vec![Ext4::ZERO; k_len * 32];
    m_kb.par_chunks_mut(32)
        .enumerate()
        .for_each(|(k, m_row)| {
            let mut buckets = [[Ext4::ZERO; 8]; 32];
            for j in 0..j_len {
                let ejk = e_jk[j * k_len + k];
                let q_blk = &q_nibbles[(j * k_len + k) * 32..(j * k_len + k + 1) * 32];
                for b in 0..32 {
                    let nib = q_blk[b];
                    let mag = (nib & 7) as usize;
                    if mag != 0 {
                        if (nib & 8) == 0 {
                            buckets[b][mag] = buckets[b][mag].add(ejk);
                        } else {
                            buckets[b][mag] = buckets[b][mag].sub(ejk);
                        }
                    }
                }
            }
            for b in 0..32 {
                let bk = &buckets[b];
                let c8 = bk[6].add(bk[7]);
                let c4 = bk[4].add(bk[5]).add(bk[7]);
                let c2 = bk[2].add(bk[3]).add(bk[5]);
                let c1 = bk[1].add(bk[3]);
                let d8 = c8.add(c8).add(c4);
                let d4 = d8.add(d8).add(c2);
                m_row[b] = d4.add(d4).add(c1);
            }
        });
    drop(e_jk);

    let mut claim = Ext4::ZERO;
    for idx in 0..(k_len * 32) {
        claim = claim.add(x_ri[idx].mul(m_kb[idx]));
    }
    tr.absorb_ext4(b"mxfp4_claim", claim);
    tr.absorb_ext4_slice(b"mxfp4_rj", r_j);

    // Step 3: 5 quadratic `b`-rounds on tiny `(K * 32)` `Ext4` buffers!
    let mut x_cur = x_ri.to_vec();
    let mut m_cur = m_kb;
    let mut b_rounds = [[Ext4::ZERO; 2]; 5];
    let mut chals_b = [Ext4::ZERO; 5];
    for r in 0..5 {
        let half = x_cur.len() / 2;
        let mut q0 = Ext4::ZERO;
        let mut q_inf = Ext4::ZERO;
        for idx in 0..half {
            let x0 = x_cur[2 * idx];
            let x1 = x_cur[2 * idx + 1];
            let m0 = m_cur[2 * idx];
            let m1 = m_cur[2 * idx + 1];
            q0 = q0.add(x0.mul(m0));
            q_inf = q_inf.add(x1.sub(x0).mul(m1.sub(m0)));
        }
        b_rounds[r] = [q0, q_inf];
        tr.absorb_ext4(b"mxfp4_b_q0", q0);
        tr.absorb_ext4(b"mxfp4_b_qinf", q_inf);
        let ch = tr.squeeze_ext4(b"mxfp4_ch_b", true);
        chals_b[r] = ch;
        x_cur = fold_ext4(&x_cur, ch);
        m_cur = fold_ext4(&m_cur, ch);
    }
    let x5 = x_cur; // length `k_len`

    // Step 4: Bind `Q^{(5)}[k, j]` (`j` at LSB stride 1, `k` at high bits) via 0-mul E2M1 Horner in `rayon` parallel!
    let eq_b = build_eq_table_lsb_ext4(&chals_b);
    let mut q_kj = vec![Ext4::ZERO; k_len * j_len];
    let mut s_kj = vec![Ext4::ZERO; k_len * j_len];
    q_kj.par_chunks_mut(j_len)
        .zip(s_kj.par_chunks_mut(j_len))
        .enumerate()
        .for_each(|(k, (q_row, s_row))| {
            for j in 0..j_len {
                let q_blk = &q_nibbles[(j * k_len + k) * 32..(j * k_len + k + 1) * 32];
                q_row[j] = e2m1_horner_dot_ext4(q_blk, &eq_b);
                s_row[j] = Ext4::from_bb(s_scale[j * k_len + k]);
            }
        });

    // Step 5: `log_j` Gruen Mode-2 quadratic rounds on `j` (`0` prover inversions!).
    let suf_j = build_eq_suffix_tables_ext4(r_j);
    let mut j_rounds = Vec::with_capacity(log_j);
    let mut chals_j = Vec::with_capacity(log_j);
    for u in 0..log_j {
        let suf = &suf_j[log_j - 1 - u];
        let rem_j = suf.len();
        let stride_k = rem_j * 2;
        let mut q0_by_j = vec![Ext4::ZERO; rem_j];
        let mut qinf_by_j = vec![Ext4::ZERO; rem_j];
        let mut q1_by_j = vec![Ext4::ZERO; rem_j];

        for k in 0..k_len {
            let xk = x5[k];
            let base = k * stride_k;
            for jr in 0..rem_j {
                let idx0 = base + 2 * jr;
                let qv0 = q_kj[idx0];
                let qv1 = q_kj[idx0 + 1];
                let sv0 = s_kj[idx0];
                let sv1 = s_kj[idx0 + 1];
                q0_by_j[jr] = q0_by_j[jr].add(xk.mul(qv0.mul(sv0)));
                qinf_by_j[jr] = qinf_by_j[jr].add(xk.mul(qv1.sub(qv0).mul(sv1.sub(sv0))));
                q1_by_j[jr] = q1_by_j[jr].add(xk.mul(qv1.mul(sv1)));
            }
        }
        let mut q0 = Ext4::ZERO;
        let mut q_inf = Ext4::ZERO;
        let mut q1 = Ext4::ZERO;
        for jr in 0..rem_j {
            let w = suf[jr];
            q0 = q0.add(w.mul(q0_by_j[jr]));
            q_inf = q_inf.add(w.mul(qinf_by_j[jr]));
            q1 = q1.add(w.mul(q1_by_j[jr]));
        }

        let msg = if r_j[u].is_zero() {
            tr.absorb_ext4(b"mxfp4_j_q0", q0);
            tr.absorb_ext4(b"mxfp4_j_qinf", q_inf);
            tr.absorb_ext4(b"mxfp4_j_q1fb", q1);
            GruenRoundExt4Msg::ZeroEqFallback { q0, q_inf, q1 }
        } else {
            tr.absorb_ext4(b"mxfp4_j_q0", q0);
            tr.absorb_ext4(b"mxfp4_j_qinf", q_inf);
            GruenRoundExt4Msg::TwoPoint { q0, q_inf }
        };
        j_rounds.push(msg);
        let ch = tr.squeeze_ext4(b"mxfp4_ch_j", true);
        chals_j.push(ch);
        q_kj = fold_ext4(&q_kj, ch);
        s_kj = fold_ext4(&s_kj, ch);
    }

    // Step 6: `log_k` cubic `{p(0), p(2), p(∞)}` rounds over `k` (`x5`, `q_kj`, `s_kj` each have length `k_len`!).
    let mut x_k = x5;
    let mut q_k = q_kj;
    let mut s_k = s_kj;
    let mut k_rounds = Vec::with_capacity(log_k);
    let mut chals_k = Vec::with_capacity(log_k);
    let two = Ext4::from_bb(2);

    for _v in 0..log_k {
        let half = x_k.len() / 2;
        let mut p0 = Ext4::ZERO;
        let mut p2 = Ext4::ZERO;
        let mut p_inf = Ext4::ZERO;
        for idx in 0..half {
            let x0 = x_k[2 * idx];
            let dx = x_k[2 * idx + 1].sub(x0);
            let x2 = x0.add(two.mul(dx));

            let q0 = q_k[2 * idx];
            let dq = q_k[2 * idx + 1].sub(q0);
            let q2 = q0.add(two.mul(dq));

            let s0 = s_k[2 * idx];
            let ds = s_k[2 * idx + 1].sub(s0);
            let s2 = s0.add(two.mul(ds));

            p0 = p0.add(x0.mul(q0).mul(s0));
            p2 = p2.add(x2.mul(q2).mul(s2));
            p_inf = p_inf.add(dx.mul(dq).mul(ds));
        }
        let msg = CubicZeroTwoInfExt4Msg { p0, p2, p_inf };
        tr.absorb_ext4(b"mxfp4_k_p0", msg.p0);
        tr.absorb_ext4(b"mxfp4_k_p2", msg.p2);
        tr.absorb_ext4(b"mxfp4_k_pinf", msg.p_inf);
        k_rounds.push(msg);

        let ch = tr.squeeze_ext4(b"mxfp4_ch_k", true);
        chals_k.push(ch);
        x_k = fold_ext4(&x_k, ch);
        q_k = fold_ext4(&q_k, ch);
        s_k = fold_ext4(&s_k, ch);
    }

    let finals = (x_k[0], q_k[0], s_k[0]);
    tr.absorb_ext4(b"mxfp4_fx", finals.0);
    tr.absorb_ext4(b"mxfp4_fq", finals.1);
    tr.absorb_ext4(b"mxfp4_fs", finals.2);

    (
        Mxfp4DelayedBjkExt4Proof {
            claim,
            log_j,
            log_k,
            b_rounds,
            j_rounds,
            k_rounds,
            finals,
        },
        Mxfp4SolvedChallenges {
            chals_b,
            chals_j,
            chals_k,
        },
    )
}

/// Fail-closed `124`-bit `Ext4` verifier for `Mxfp4DelayedBjkExt4Proof`.
pub fn verify_mxfp4_delayed_bjk_horner_ext4(
    expected_claim: Ext4,
    r_j: &[Ext4],
    proof: &Mxfp4DelayedBjkExt4Proof,
    tr: &mut CShakeTranscript,
) -> Result<Mxfp4SolvedChallenges, String> {
    if proof.claim != expected_claim {
        return Err("MXFP4 delayed-bind claim mismatch".to_string());
    }
    if r_j.len() != proof.log_j
        || proof.j_rounds.len() != proof.log_j
        || proof.k_rounds.len() != proof.log_k
    {
        return Err("MXFP4 delayed-bind round length mismatch".to_string());
    }

    tr.absorb_ext4(b"mxfp4_claim", proof.claim);
    tr.absorb_ext4_slice(b"mxfp4_rj", r_j);

    let mut sigma = proof.claim;
    let mut chals_b = [Ext4::ZERO; 5];
    for r in 0..5 {
        let [q0, q_inf] = proof.b_rounds[r];
        tr.absorb_ext4(b"mxfp4_b_q0", q0);
        tr.absorb_ext4(b"mxfp4_b_qinf", q_inf);
        let ch = tr.squeeze_ext4(b"mxfp4_ch_b", true);
        chals_b[r] = ch;
        let q1 = sigma.sub(q0);
        sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
    }

    let mut chals_j = Vec::with_capacity(proof.log_j);
    for u in 0..proof.log_j {
        let r = r_j[u];
        if r.is_zero() {
            match proof.j_rounds[u] {
                GruenRoundExt4Msg::ZeroEqFallback { q0, q_inf, q1 } => {
                    if q0 != sigma {
                        return Err(format!("MXFP4 j-round {u} ZeroEqFallback q0 != sigma"));
                    }
                    tr.absorb_ext4(b"mxfp4_j_q0", q0);
                    tr.absorb_ext4(b"mxfp4_j_qinf", q_inf);
                    tr.absorb_ext4(b"mxfp4_j_q1fb", q1);
                    let ch = tr.squeeze_ext4(b"mxfp4_ch_j", true);
                    chals_j.push(ch);
                    sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
                }
                GruenRoundExt4Msg::TwoPoint { .. } => {
                    return Err(format!("MXFP4 j-round {u} expected ZeroEqFallback"))
                }
            }
        } else {
            match proof.j_rounds[u] {
                GruenRoundExt4Msg::TwoPoint { q0, q_inf } => {
                    tr.absorb_ext4(b"mxfp4_j_q0", q0);
                    tr.absorb_ext4(b"mxfp4_j_qinf", q_inf);
                    let ch = tr.squeeze_ext4(b"mxfp4_ch_j", true);
                    chals_j.push(ch);
                    let r_inv = r.inv().ok_or_else(|| "nonzero r failed inv".to_string())?;
                    let q1 = r_inv.mul(sigma.sub(Ext4::ONE.sub(r).mul(q0)));
                    sigma = eval_quad_zero_one_inf_ext4(q0, q1, q_inf, ch);
                }
                GruenRoundExt4Msg::ZeroEqFallback { .. } => {
                    return Err(format!("MXFP4 j-round {u} unexpected ZeroEqFallback"))
                }
            }
        }
    }

    let mut chals_k = Vec::with_capacity(proof.log_k);
    for msg in &proof.k_rounds {
        tr.absorb_ext4(b"mxfp4_k_p0", msg.p0);
        tr.absorb_ext4(b"mxfp4_k_p2", msg.p2);
        tr.absorb_ext4(b"mxfp4_k_pinf", msg.p_inf);
        let ch = tr.squeeze_ext4(b"mxfp4_ch_k", true);
        chals_k.push(ch);
        let p1 = sigma.sub(msg.p0);
        sigma = eval_cubic_zero_one_two_inf_ext4(msg.p0, p1, msg.p2, msg.p_inf, ch);
    }

    let (fx, fq, fs) = proof.finals;
    tr.absorb_ext4(b"mxfp4_fx", fx);
    tr.absorb_ext4(b"mxfp4_fq", fq);
    tr.absorb_ext4(b"mxfp4_fs", fs);

    if sigma != fx.mul(fq).mul(fs) {
        return Err("MXFP4 delayed-bind terminal sigma != fx * fq * fs".to_string());
    }

    let _ = (badd(0, 0), bsub(0, 0), fold_bb_to_ext4, P);
    Ok(Mxfp4SolvedChallenges {
        chals_b,
        chals_j,
        chals_k,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ext4::mle_eval_bb_at_ext4;
    use crate::safetensors_mmap::decode_e2m1_x2_bb;

    #[test]
    fn test_d1b_range_and_mxfp4_horner_ext4() {
        // 1. Test D1b range proof on 2^10 witnesses in [0, 2^6)
        let m_wit = 10usize;
        let m_tab = 6usize;
        let rem: Vec<u32> = (0..(1usize << m_wit)).map(|i| (i * 13 + 7) as u32 & 63).collect();
        let mult = compute_d1b_multiplicities(&rem, m_tab).unwrap();

        let mut p_tr = CShakeTranscript::new(b"d1b-test");
        let (pf, z_leaf) = prove_d1b_range_ext4(&rem, &mult, m_wit, m_tab, &mut p_tr);
        let mut v_tr = CShakeTranscript::new(b"d1b-test");
        let z_ver = verify_d1b_range_ext4(&pf, &mut v_tr).expect("D1b verify");
        assert_eq!(z_leaf, z_ver);

        // 2. Test MXFP4 delayed-bind 0-mul E2M1 Horner with interior r_j[1] == 0 fallback!
        let log_j = 4usize;
        let log_k = 3usize;
        let j_len = 1usize << log_j;
        let k_len = 1usize << log_k;
        let mut rng_tr = CShakeTranscript::new(b"mxfp4-gen");
        let x_ri = rng_tr.squeeze_ext4_vec(b"x", k_len * 32, true);
        let q_nibbles: Vec<u8> = (0..(j_len * k_len * 32)).map(|i| ((i * 7 + 3) & 15) as u8).collect();
        let s_scale: Vec<u32> = (0..(j_len * k_len)).map(|i| ((i * 29 + 1) % 1024) as u32).collect();
        let mut r_j = rng_tr.squeeze_ext4_vec(b"rj", log_j, true);
        r_j[1] = Ext4::ZERO; // Force interior ZeroEqFallback!

        let mut p_tr2 = CShakeTranscript::new(b"mxfp4-test");
        let (mpf, solved) = prove_mxfp4_delayed_bjk_horner_ext4(
            &x_ri, &q_nibbles, &s_scale, log_j, log_k, &r_j, &mut p_tr2,
        );
        let mut v_tr2 = CShakeTranscript::new(b"mxfp4-test");
        let ver_solved =
            verify_mxfp4_delayed_bjk_horner_ext4(mpf.claim, &r_j, &mpf, &mut v_tr2).expect("mxfp4 verify");
        assert_eq!(solved.chals_b, ver_solved.chals_b);

        // Verify terminal Q̂(c_b, c_j, c_k) matches `to_bb_table_lsb_bjk` layout!
        let mut q_lsb_bjk = vec![0u32; j_len * k_len * 32];
        for j in 0..j_len {
            for k in 0..k_len {
                for b in 0..32 {
                    q_lsb_bjk[(k * j_len + j) * 32 + b] =
                        decode_e2m1_x2_bb(q_nibbles[(j * k_len + k) * 32 + b]);
                }
            }
        }
        let mut pt_q = Vec::new();
        pt_q.extend_from_slice(&solved.chals_b);
        pt_q.extend_from_slice(&solved.chals_j);
        pt_q.extend_from_slice(&solved.chals_k);
        assert_eq!(mpf.finals.1, mle_eval_bb_at_ext4(&q_lsb_bjk, &pt_q));
    }
}
