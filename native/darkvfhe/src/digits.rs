//! Canonical digit lift encodings for `HoistedB61`:
//! 1. **`Direct-20` (`DirectDigitSpec`)**:
//!    - `10` `w = 20`-bit unsigned limbs (`d_0..d_9`, narrowed top limb `d_9 < 2^3` checked via
//!      `2^17 * d_9 < 2^20` and `d_9 + (2^20 - 8) < 2^20`) for centered mod-`Q` inputs `u = x + floor(Q/2)`
//!      and BEHZ remainders `s in [0, Q)`.
//!    - `14` `w = 20`-bit unsigned limbs (`d_0..d_13`) for signed quotients `y + 2^{max_y_bits}`.
//! 2. **`Exact-Garner-15` (`ExactGarnerSpec`)**:
//!    - `15` `w = 20`-bit unsigned columns (`5` per prime limb `q_i`) enforcing `u in [0, Q - 1]`
//!      with **zero slack** (`Astra E4 / E7`) via `delta_i = 2^61 - q_i < 2^20`, boolean carry
//!      `c_i in {0, 1}`, and linear complement lookup `T_i in [0, 2^20)`.

use crate::bigint::{divrem_u576_by_u192, SignedU320};
use crate::HoistedParams;
use darkstep::arith::invmod;
use serde::{Deserialize, Serialize};

pub const W20_LIMIT: u32 = 1 << 20;
pub const W20_MASK: u64 = (1u64 << 20) - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LiftMode {
    Direct20,
    ExactGarner15,
}

impl LiftMode {
    pub fn as_str(&self) -> &'static str {
        match self {
            LiftMode::Direct20 => "direct",
            LiftMode::ExactGarner15 => "exact_garner",
        }
    }

    pub fn q_cols(&self) -> usize {
        match self {
            LiftMode::Direct20 => 10,
            LiftMode::ExactGarner15 => 15,
        }
    }
}

/// Column-major digit polynomial matrix (`num_cols` columns, each length `N`, entries in `[0, 2^20)`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DigitCols {
    pub cols: Vec<Vec<u32>>,
}

impl DigitCols {
    pub fn num_cols(&self) -> usize {
        self.cols.len()
    }
    pub fn n(&self) -> usize {
        self.cols.first().map_or(0, Vec::len)
    }
}

/// `Direct-20` canonical digit specification (`Lx = 10`, `Ly = 14`).
#[derive(Clone, Debug)]
pub struct DirectDigitSpec {
    pub w: u32,
    pub lx: usize,
    pub top_x_bits: u32,
    pub max_y_bits: u32,
    pub ly: usize,
    pub top_y_bits: u32,
}

impl DirectDigitSpec {
    pub fn new(params: &HoistedParams, max_y_bits: u32) -> Self {
        let q_bits = params.q_big.bits() as u32; // 183
        let w = 20u32;
        let lx = q_bits.div_ceil(w) as usize; // 10
        let top_x_bits = q_bits - w * (lx as u32 - 1); // 3
        let y_span_bits = max_y_bits + 1; // 263 -> covers (-2^262, 2^262)
        let ly = y_span_bits.div_ceil(w) as usize; // 14
        let top_y_bits = y_span_bits - w * (ly as u32 - 1); // 3 at max_y_bits=262
        DirectDigitSpec {
            w,
            lx,
            top_x_bits,
            max_y_bits,
            ly,
            top_y_bits,
        }
    }

    /// Encode `u_j in [0, 2^183)` (`[u64; 3]`) into `10` `w = 20`-bit digit columns.
    pub fn encode_u192(&self, us: &[[u64; 3]]) -> DigitCols {
        let n = us.len();
        let mut cols = vec![vec![0u32; n]; self.lx];
        let top_lim = 1u64 << self.top_x_bits;
        for (j, u) in us.iter().enumerate() {
            // u = u[0] + 2^64 u[1] + 2^128 u[2]: extract 10 x 20-bit chunks
            let d0 = u[0] & W20_MASK;
            let d1 = (u[0] >> 20) & W20_MASK;
            let d2 = (u[0] >> 40) & W20_MASK;
            let d3 = ((u[0] >> 60) | (u[1] << 4)) & W20_MASK;
            let d4 = (u[1] >> 16) & W20_MASK;
            let d5 = (u[1] >> 36) & W20_MASK;
            let d6 = ((u[1] >> 56) | (u[2] << 8)) & W20_MASK;
            let d7 = (u[2] >> 12) & W20_MASK;
            let d8 = (u[2] >> 32) & W20_MASK;
            let d9 = u[2] >> 52;
            assert!(d9 < top_lim, "top limb {d9} overflows 2^{}", self.top_x_bits);
            let ds = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9];
            for m in 0..10 {
                cols[m][j] = ds[m] as u32;
            }
        }
        DigitCols { cols }
    }

    /// Encode signed quotients `y_j` shifted by `+ 2^{max_y_bits}` into `14` `w = 20`-bit columns.
    pub fn encode_signed_y(&self, ys: &[SignedU320]) -> DigitCols {
        let n = ys.len();
        let mut cols = vec![vec![0u32; n]; self.ly];
        let top_lim = 1u64 << self.top_y_bits;
        for (j, y) in ys.iter().enumerate() {
            let mut rem = y.add_pow2(self.max_y_bits);
            for m in 0..(self.ly - 1) {
                cols[m][j] = (rem[0] & W20_MASK) as u32;
                // Shift [u64; 5] right by 20 bits:
                rem = [
                    (rem[0] >> 20) | (rem[1] << 44),
                    (rem[1] >> 20) | (rem[2] << 44),
                    (rem[2] >> 20) | (rem[3] << 44),
                    (rem[3] >> 20) | (rem[4] << 44),
                    rem[4] >> 20,
                ];
            }
            assert!(
                rem[0] < top_lim && rem[1] == 0 && rem[2] == 0 && rem[3] == 0 && rem[4] == 0,
                "y top limb {} overflows 2^{}",
                rem[0],
                self.top_y_bits
            );
            cols[self.ly - 1][j] = rem[0] as u32;
        }
        DigitCols { cols }
    }

    /// Deterministic verifier check on `num_limbs` `w = 20` columns with narrowed `top_bits`.
    pub fn check_digits(&self, dc: &DigitCols, num_limbs: usize, top_bits: u32) -> Result<(), String> {
        if dc.cols.len() != num_limbs {
            return Err(format!(
                "wrong number of digit limbs: got {}, expected {}",
                dc.cols.len(),
                num_limbs
            ));
        }
        let top_lim = 1u32 << top_bits;
        let shift = self.w - top_bits;
        for (m, col) in dc.cols.iter().enumerate() {
            let is_top = m + 1 == num_limbs;
            for &val in col {
                if val >= W20_LIMIT {
                    return Err(format!("digit limb {m} value {val} out of [0, 2^20)"));
                }
                if is_top && (val >= top_lim || (val << shift) >= W20_LIMIT) {
                    return Err(format!("top digit limb {m} value {val} overflows 2^{top_bits}"));
                }
            }
        }
        Ok(())
    }

    /// Emit all `[0, 2^20)` lookup queries into `out` (both raw limbs and narrowed-top complement
    /// `d_top + (2^20 - 2^top_bits)` so even arbitrary `F_p` elements cannot wrap mod `p`).
    pub fn append_lookups_fp(&self, dc: &DigitCols, top_bits: u32, p: u64, out: &mut Vec<u64>) {
        let num_limbs = dc.cols.len();
        let top_shift_offset = (W20_LIMIT - (1u32 << top_bits)) as u64;
        for (m, col) in dc.cols.iter().enumerate() {
            for &val in col {
                out.push((val as u64) % p);
            }
            if m + 1 == num_limbs && top_bits < 20 {
                for &val in col {
                    out.push(((val as u64) + top_shift_offset) % p);
                }
            }
        }
    }

    /// Shift-pack `10` `w = 20` digit columns into `(lo100, hi83)` `u128` pairs once (prime-independent!),
    /// cutting per-prime evaluation work by `10x` while preserving exact algebraic identity over `Z` and `F_p`.
    pub fn prepack_q10(dc: &DigitCols) -> Vec<(u128, u128)> {
        let n = dc.n();
        let c = &dc.cols;
        (0..n)
            .map(|j| {
                let lo = (c[0][j] as u128)
                    + ((c[1][j] as u128) << 20)
                    + ((c[2][j] as u128) << 40)
                    + ((c[3][j] as u128) << 60)
                    + ((c[4][j] as u128) << 80);
                let hi = (c[5][j] as u128)
                    + ((c[6][j] as u128) << 20)
                    + ((c[7][j] as u128) << 40)
                    + ((c[8][j] as u128) << 60)
                    + ((c[9][j] as u128) << 80);
                (lo, hi)
            })
            .collect()
    }

    /// Shift-pack `14` `w = 20` digit columns for `y` into `(lo100, mid100, hi80)` `u128` triples once!
    pub fn prepack_y14(dc: &DigitCols) -> Vec<(u128, u128, u128)> {
        let n = dc.n();
        let c = &dc.cols;
        (0..n)
            .map(|j| {
                let lo = (c[0][j] as u128)
                    + ((c[1][j] as u128) << 20)
                    + ((c[2][j] as u128) << 40)
                    + ((c[3][j] as u128) << 60)
                    + ((c[4][j] as u128) << 80);
                let mid = (c[5][j] as u128)
                    + ((c[6][j] as u128) << 20)
                    + ((c[7][j] as u128) << 40)
                    + ((c[8][j] as u128) << 60)
                    + ((c[9][j] as u128) << 80);
                let hi = (c[10][j] as u128)
                    + ((c[11][j] as u128) << 20)
                    + ((c[12][j] as u128) << 40)
                    + ((c[13][j] as u128) << 60);
                (lo, mid, hi)
            })
            .collect()
    }
}

/// Zero-slack non-power-of-two `[0, Q - 1]` canonical lift specification (`Exact-Garner-15`).
#[derive(Clone, Debug)]
pub struct ExactGarnerSpec {
    pub qp: [u64; 3],
    pub deltas: [u64; 3],
    pub inv2_20_mod_q: [u64; 3],
    pub q0_limbs: [u64; 3],
    pub q01_limbs: [u64; 3],
}

impl ExactGarnerSpec {
    pub fn new(params: &HoistedParams) -> Self {
        let qp = params.qp;
        let deltas = qp.map(|q| (1u64 << 61) - q);
        for &d in &deltas {
            assert!(d > 0 && d < (1u64 << 20), "Exact-Garner-15 requires 2^61 - q_i < 2^20");
        }
        let inv2_20_mod_q = qp.map(|q| invmod(1u64 << 20, q));
        let q0_limbs = [qp[0], 0, 0];
        let q01_limbs = [
            params.prefix_prods[2][0],
            params.prefix_prods[2][1],
            params.prefix_prods[2][2],
        ];
        ExactGarnerSpec {
            qp,
            deltas,
            inv2_20_mod_q,
            q0_limbs,
            q01_limbs,
        }
    }

    /// Encode `u_j in [0, Q - 1]` (`[u64; 3]`) into `15` `w = 20`-bit Garner columns (`5` per prime limb).
    pub fn encode_u_exact(&self, us: &[[u64; 3]]) -> DigitCols {
        let n = us.len();
        let mut cols = vec![vec![0u32; n]; 15];
        let [q0, q1, q2] = self.qp;

        // Divide u (192-bit) by q0 and q1 using u128 step-division!
        for (j, u) in us.iter().enumerate() {
            let (quo0, r0) = divrem_u192_by_u64(u, q0);
            let (quo1, r1) = divrem_u192_by_u64(&quo0, q1);
            assert!(quo1[1] == 0 && quo1[2] == 0 && quo1[0] < q2, "u outside [0, Q)");
            let r2 = quo1[0];

            for (idx, (ri, delta)) in [(r0, self.deltas[0]), (r1, self.deltas[1]), (r2, self.deltas[2])]
                .into_iter()
                .enumerate()
            {
                let d0 = ri & ((1u64 << 20) - 1);
                let d1 = (ri >> 20) & ((1u64 << 19) - 1);
                let d2 = (ri >> 39) & ((1u64 << 18) - 1);
                let d3 = ri >> 57;
                debug_assert!(d3 < 16);
                let s0 = d0 + delta;
                let v0 = s0 & ((1u64 << 20) - 1);
                let ci = s0 >> 20;
                debug_assert!(ci <= 1);
                let base = 5 * idx;
                cols[base][j] = d0 as u32;
                cols[base + 1][j] = d1 as u32;
                cols[base + 2][j] = d2 as u32;
                cols[base + 3][j] = d3 as u32;
                cols[base + 4][j] = v0 as u32;
            }
        }
        let _ = divrem_u576_by_u192;
        DigitCols { cols }
    }

    /// Deterministic verifier check proving every coefficient `u_j in [0, Q - 1]` with zero slack!
    pub fn check_u_exact(&self, dc: &DigitCols) -> Result<(), String> {
        if dc.cols.len() != 15 {
            return Err(format!("Exact-Garner-15 requires 15 columns, got {}", dc.cols.len()));
        }
        let n = dc.n();
        for idx in 0..3 {
            let q = self.qp[idx];
            let delta = self.deltas[idx];
            let inv2_20 = self.inv2_20_mod_q[idx];
            let d0s = &dc.cols[5 * idx];
            let d1s = &dc.cols[5 * idx + 1];
            let d2s = &dc.cols[5 * idx + 2];
            let d3s = &dc.cols[5 * idx + 3];
            let v0s = &dc.cols[5 * idx + 4];

            for j in 0..n {
                let (d0, d1, d2, d3, v0) = (
                    d0s[j] as u64,
                    d1s[j] as u64,
                    d2s[j] as u64,
                    d3s[j] as u64,
                    v0s[j] as u64,
                );
                if d0 >= W20_LIMIT as u64 || v0 >= W20_LIMIT as u64 {
                    return Err(format!("Garner limb {idx} d0/v0 out of [0, 2^20)"));
                }
                if (d1 << 1) >= W20_LIMIT as u64
                    || (d2 << 2) >= W20_LIMIT as u64
                    || (d3 << 16) >= W20_LIMIT as u64
                {
                    return Err(format!("narrowed Garner limb {idx} out of range"));
                }
                // Boolean carry c_i in F_q (lifts to Z because |d0 + delta - v0| < 2^21 << q):
                let diff = if d0 + delta >= v0 {
                    (d0 + delta - v0) % q
                } else {
                    q - ((v0 - d0 - delta) % q)
                };
                let ci = ((diff as u128 * inv2_20 as u128) % q as u128) as u64;
                if !(ci == 0 || ci == 1) {
                    return Err(format!("Garner carry c_{idx} not boolean"));
                }
                // Linear complement lookup T_i in [0, 2^20) (negative wraps to >= 2^60 in F_p, < 0 in i64):
                let ti = ((1i64 << 19) - 1 - d1 as i64)
                    + ((1i64 << 18) - 1 - d2 as i64)
                    + (15 - d3 as i64)
                    - (ci as i64);
                if !(0 <= ti && ti < W20_LIMIT as i64) {
                    return Err(format!(
                        "Garner limb r_{idx} >= q_{idx} (boundary overflow refused)"
                    ));
                }
            }
        }
        Ok(())
    }

    /// Emit all `[0, 2^20)` lookup queries for `D1b` LogUp-GKR in `F_p`, including narrowed-limb
    /// complements and the linear boundary complement `T_i mod p` (which becomes `p - 1 >= 2^60`
    /// if `r_i >= q_i`, deterministically failing the `[0, 2^20)` table lookup!).
    pub fn append_lookups_fp(&self, dc: &DigitCols, p: u64, out: &mut Vec<u64>) {
        let n = dc.n();
        let inv2_20_p = invmod(1u64 << 20, p);
        for idx in 0..3 {
            let delta = self.deltas[idx];
            let d0s = &dc.cols[5 * idx];
            let d1s = &dc.cols[5 * idx + 1];
            let d2s = &dc.cols[5 * idx + 2];
            let d3s = &dc.cols[5 * idx + 3];
            let v0s = &dc.cols[5 * idx + 4];
            for j in 0..n {
                let (d0, d1, d2, d3, v0) = (
                    d0s[j] as u64,
                    d1s[j] as u64,
                    d2s[j] as u64,
                    d3s[j] as u64,
                    v0s[j] as u64,
                );
                out.push(d0 % p);
                out.push(d1 % p);
                out.push((d1 + (1u64 << 19)) % p);
                out.push(d2 % p);
                out.push((d2 + 3 * (1u64 << 18)) % p);
                out.push(d3 % p);
                out.push((d3 + ((1u64 << 20) - 16)) % p);
                out.push(v0 % p);

                let diff = if d0 + delta >= v0 {
                    (d0 + delta - v0) % p
                } else {
                    p - ((v0 - d0 - delta) % p)
                };
                let ci = ((diff as u128 * inv2_20_p as u128) % p as u128) as u64;
                // Compute T_i in F_p:
                let pos_sum = (((1u64 << 19) - 1) + ((1u64 << 18) - 1) + 15) % p;
                let neg_sum = (d1 + d2 + d3 + ci) % p;
                let ti_mod_p = if pos_sum >= neg_sum {
                    pos_sum - neg_sum
                } else {
                    p + pos_sum - neg_sum
                };
                out.push(ti_mod_p);
            }
        }
    }

    /// Prepack the 3 Garner residues `(r0_j, r1_j, r2_j)` once per coefficient (prime-independent!).
    pub fn prepack_garner15(dc: &DigitCols) -> Vec<(u128, u128, u128)> {
        let n = dc.n();
        let c = &dc.cols;
        (0..n)
            .map(|j| {
                let r0 = (c[0][j] as u128)
                    + ((c[1][j] as u128) << 20)
                    + ((c[2][j] as u128) << 39)
                    + ((c[3][j] as u128) << 57);
                let r1 = (c[5][j] as u128)
                    + ((c[6][j] as u128) << 20)
                    + ((c[7][j] as u128) << 39)
                    + ((c[8][j] as u128) << 57);
                let r2 = (c[10][j] as u128)
                    + ((c[11][j] as u128) << 20)
                    + ((c[12][j] as u128) << 39)
                    + ((c[13][j] as u128) << 57);
                (r0, r1, r2)
            })
            .collect()
    }
}

#[inline]
fn divrem_u192_by_u64(u: &[u64; 3], d: u64) -> ([u64; 3], u64) {
    let d128 = d as u128;
    let q2 = (u[2] as u128) / d128;
    let r2 = (u[2] as u128) % d128;
    let cur1 = (r2 << 64) | (u[1] as u128);
    let q1 = cur1 / d128;
    let r1 = cur1 % d128;
    let cur0 = (r1 << 64) | (u[0] as u128);
    let q0 = cur0 / d128;
    let r0 = cur0 % d128;
    ([q0 as u64, q1 as u64, q2 as u64], r0 as u64)
}
