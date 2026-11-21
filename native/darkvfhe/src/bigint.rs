//! Zero-allocation fixed-width stack integer arithmetic (`[u64; 3]` = 192b, `[u64; 5]` = 320b,
//! `[u64; 9]` = 576b) for exact Garner CRT lifts, 8-limb `Q * B` tensor reconstruction, and
//! Euclidean BEHZ division `divmod(t * D + floor(Q/2), Q)` with zero heap allocations in hot loops.

use crate::HoistedParams;
use darkstep::arith::{mulmod, submod};
use num_bigint::BigUint;

pub fn biguint_to_limbs3(x: &BigUint) -> [u64; 3] {
    let d = x.to_u64_digits();
    assert!(d.len() <= 3, "BigUint exceeds 192 bits");
    let mut out = [0u64; 3];
    for (i, &v) in d.iter().enumerate() {
        out[i] = v;
    }
    out
}

pub fn biguint_to_limbs9(x: &BigUint) -> [u64; 9] {
    let d = x.to_u64_digits();
    assert!(d.len() <= 9, "BigUint exceeds 576 bits");
    let mut out = [0u64; 9];
    for (i, &v) in d.iter().enumerate() {
        out[i] = v;
    }
    out
}

pub fn biguint_mod_u64(x: &BigUint, m: u64) -> u64 {
    let mut r = 0u128;
    for &limb in x.to_u64_digits().iter().rev() {
        r = ((r << 64) | limb as u128) % m as u128;
    }
    r as u64
}

#[inline(always)]
pub fn gt_limbs<const N: usize>(a: &[u64; N], b: &[u64; N]) -> bool {
    for i in (0..N).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    false
}

#[inline(always)]
pub fn ge_limbs<const N: usize>(a: &[u64; N], b: &[u64; N]) -> bool {
    for i in (0..N).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

#[inline(always)]
pub fn add_limbs<const N: usize>(a: &[u64; N], b: &[u64; N]) -> [u64; N] {
    let mut out = [0u64; N];
    let mut carry = 0u128;
    for i in 0..N {
        let s = a[i] as u128 + b[i] as u128 + carry;
        out[i] = s as u64;
        carry = s >> 64;
    }
    debug_assert_eq!(carry, 0, "add_limbs overflow");
    out
}

#[inline(always)]
pub fn sub_limbs<const N: usize>(a: &[u64; N], b: &[u64; N]) -> [u64; N] {
    let mut out = [0u64; N];
    let mut borrow = 0u128;
    for i in 0..N {
        let ai = a[i] as u128;
        let bi = b[i] as u128 + borrow;
        if ai >= bi {
            out[i] = (ai - bi) as u64;
            borrow = 0;
        } else {
            out[i] = ((1u128 << 64) + ai - bi) as u64;
            borrow = 1;
        }
    }
    debug_assert_eq!(borrow, 0, "sub_limbs underflow");
    out
}

#[inline(always)]
pub fn add_mul_u64<const N: usize>(acc: &mut [u64; N], prod: &[u64; N], scalar: u64) {
    if scalar == 0 {
        return;
    }
    let mut carry = 0u128;
    let s = scalar as u128;
    for i in 0..N {
        let v = acc[i] as u128 + prod[i] as u128 * s + carry;
        acc[i] = v as u64;
        carry = v >> 64;
    }
    debug_assert_eq!(carry, 0, "add_mul_u64 overflow");
}

#[inline(always)]
pub fn mul_limbs9_u64(a: &[u64; 9], scalar: u64) -> [u64; 9] {
    let mut out = [0u64; 9];
    let mut carry = 0u128;
    let s = scalar as u128;
    for i in 0..9 {
        let v = a[i] as u128 * s + carry;
        out[i] = v as u64;
        carry = v >> 64;
    }
    debug_assert_eq!(carry, 0, "mul_limbs9_u64 overflow");
    out
}

/// Signed integer in `(-2^319, 2^319)` represented as `(neg, mag: [u64; 5])`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedU320 {
    pub neg: bool,
    pub mag: [u64; 5],
}

impl SignedU320 {
    /// Compute `self + (1 << shift_bits)` as an unsigned `[u64; 5]`, asserting `0 <= result < 2^320`.
    #[inline]
    pub fn add_pow2(&self, shift_bits: u32) -> [u64; 5] {
        let mut sh = [0u64; 5];
        sh[(shift_bits / 64) as usize] = 1u64 << (shift_bits % 64);
        if !self.neg {
            add_limbs(&self.mag, &sh)
        } else {
            assert!(ge_limbs(&sh, &self.mag), "SignedU320::add_pow2 negative overflow");
            sub_limbs(&sh, &self.mag)
        }
    }

    /// Reduce `self mod p` in `[0, p)`.
    #[inline]
    pub fn mod_p(&self, p: u64) -> u64 {
        let mut r = 0u128;
        for i in (0..5).rev() {
            r = ((r << 64) | self.mag[i] as u128) % p as u128;
        }
        let rem = r as u64;
        if self.neg && rem != 0 {
            p - rem
        } else {
            rem
        }
    }
}

/// Exact Knuth-D / base-`2^64` unsigned division of a 576-bit `[u64; 9]` dividend by a 3-limb
/// divisor `den` with `den[2] != 0` (such as `Q ~ 2^183`), returning `(quot: [u64; 7], rem: [u64; 3])`.
#[inline]
pub fn divrem_u576_by_u192(num: &[u64; 9], den: &[u64; 3]) -> ([u64; 7], [u64; 3]) {
    debug_assert!(den[2] != 0, "divisor top limb must be non-zero");
    let shift = den[2].leading_zeros();
    let d: [u64; 3] = if shift == 0 {
        *den
    } else {
        [
            den[0] << shift,
            (den[1] << shift) | (den[0] >> (64 - shift)),
            (den[2] << shift) | (den[1] >> (64 - shift)),
        ]
    };
    let mut u = [0u64; 10];
    if shift == 0 {
        u[..9].copy_from_slice(num);
    } else {
        u[0] = num[0] << shift;
        for i in 1..9 {
            u[i] = (num[i] << shift) | (num[i - 1] >> (64 - shift));
        }
        u[9] = num[8] >> (64 - shift);
    }

    let d2 = d[2] as u128;
    let d1 = d[1] as u128;
    let mut q = [0u64; 7];

    for j in (0..7).rev() {
        let u_hi = u[j + 3] as u128;
        let u_mid = u[j + 2] as u128;
        let u_lo = u[j + 1] as u128;
        let top2 = (u_hi << 64) | u_mid;
        let (mut qhat, mut rhat) = if u_hi == d2 {
            (u64::MAX as u128, u_mid + d2)
        } else {
            (top2 / d2, top2 % d2)
        };
        while qhat >= (1u128 << 64) || (rhat < (1u128 << 64) && qhat * d1 > ((rhat << 64) | u_lo)) {
            qhat -= 1;
            rhat += d2;
            if rhat >= (1u128 << 64) {
                break;
            }
        }

        // Multiply and subtract qhat * d from u[j..=j+3]:
        let mut borrow = 0i128;
        let mut prod_carry = 0u128;
        for i in 0..3 {
            let p = qhat * (d[i] as u128) + prod_carry;
            prod_carry = p >> 64;
            let p_lo = (p as u64) as i128;
            let diff = (u[j + i] as i128) - p_lo - borrow;
            u[j + i] = diff as u64;
            borrow = if diff < 0 { 1 } else { 0 };
        }
        let diff_top = (u[j + 3] as i128) - (prod_carry as i128) - borrow;
        if diff_top < 0 {
            // qhat was 1 too large (probability < 2 / 2^64): add d back once
            qhat -= 1;
            let mut c = 0u128;
            for i in 0..3 {
                let s = (u[j + i] as u128) + (d[i] as u128) + c;
                u[j + i] = s as u64;
                c = s >> 64;
            }
            u[j + 3] = (diff_top + c as i128) as u64;
        } else {
            u[j + 3] = diff_top as u64;
        }
        q[j] = qhat as u64;
    }

    let rem = if shift == 0 {
        [u[0], u[1], u[2]]
    } else {
        [
            (u[0] >> shift) | (u[1] << (64 - shift)),
            (u[1] >> shift) | (u[2] << (64 - shift)),
            u[2] >> shift,
        ]
    };
    (q, rem)
}

/// Exact 3-limb centered lift + base extension `Qp -> Qp union Bp`:
/// Given `(r0, r1, r2)` mod `(q0, q1, q2)`:
/// - Computes `z in [0, Q)` via Garner mixed radix,
/// - Computes `u = centered(z, Q) + floor(Q/2) in [0, Q - 1]` as `[u64; 3]`,
/// - Computes `centered(z, Q) mod p_l` across all 8 primes `Qp union Bp`.
#[inline]
pub fn lift_q_to_8limbs_and_u(
    params: &HoistedParams,
    r0: u64,
    r1: u64,
    r2: u64,
) -> ([u64; 8], [u64; 3]) {
    let [q0, q1, q2] = params.qp;
    let g0 = r0;
    let g1 = mulmod(submod(r1, g0 % q1, q1), params.inv_prefix_mod[1], q1);
    let c01_mod_q2 = params.fp[2].add(g0 % q2, params.fp[2].mul(g1 % q2, q0 % q2));
    let g2 = mulmod(submod(r2, c01_mod_q2, q2), params.inv_prefix_mod[2], q2);

    // Reconstruct z = g0 + q0*g1 + (q0*q1)*g2 in [u64; 3]:
    let mut z = [g0, 0, 0];
    let q0_arr = [q0, 0, 0];
    let q01_arr = [
        params.prefix_prods[2][0],
        params.prefix_prods[2][1],
        params.prefix_prods[2][2],
    ];
    add_mul_u64(&mut z, &q0_arr, g1);
    add_mul_u64(&mut z, &q01_arr, g2);

    let is_neg = gt_limbs(&z, &params.half_q_limbs);
    // u = centered(z, Q) + floor(Q/2):
    // If z <= floor(Q/2): centered = z => u = z + floor(Q/2).
    // If z > floor(Q/2):  centered = z - Q => u = z - (Q - floor(Q/2)).
    let u = if !is_neg {
        add_limbs(&z, &params.half_q_limbs)
    } else {
        sub_limbs(&z, &params.q_minus_half_q_limbs)
    };

    let mut out8 = [r0, r1, r2, 0, 0, 0, 0, 0];
    for m in 3..8 {
        let fpm = &params.fp[m];
        let z_mod_pm = fpm.red128(
            g0 as u128
                + (g1 as u128) * (params.prefix_mod[m][1] as u128)
                + (g2 as u128) * (params.prefix_mod[m][2] as u128),
        );
        out8[m] = if is_neg {
            fpm.sub(z_mod_pm, params.q_mod_p[m])
        } else {
            z_mod_pm
        };
    }
    (out8, u)
}

/// Exact 3-limb unsigned Garner reconstruction `z in [0, Q)` from `(r0, r1, r2)` mod `Qp`.
#[inline]
pub fn crt3_unsigned(params: &HoistedParams, r0: u64, r1: u64, r2: u64) -> [u64; 3] {
    let [q0, q1, q2] = params.qp;
    let g0 = r0;
    let g1 = mulmod(submod(r1, g0 % q1, q1), params.inv_prefix_mod[1], q1);
    let c01_mod_q2 = params.fp[2].add(g0 % q2, params.fp[2].mul(g1 % q2, q0 % q2));
    let g2 = mulmod(submod(r2, c01_mod_q2, q2), params.inv_prefix_mod[2], q2);
    let mut z = [g0, 0, 0];
    let q0_arr = [q0, 0, 0];
    let q01_arr = [
        params.prefix_prods[2][0],
        params.prefix_prods[2][1],
        params.prefix_prods[2][2],
    ];
    add_mul_u64(&mut z, &q0_arr, g1);
    add_mul_u64(&mut z, &q01_arr, g2);
    z
}

/// Exact 8-limb Garner reconstruction of `D in (-M_QB/2, M_QB/2]` followed by exact BEHZ Euclidean
/// division `t * D + floor(Q/2) = Q * y + s` with `0 <= s < Q`, returning `(y_signed, s_limbs, y_mod_qp)`.
#[inline]
pub fn behz_rescale_from_8limbs(
    params: &HoistedParams,
    res: &[u64; 8],
) -> (SignedU320, [u64; 3], [u64; 3]) {
    let mut g = [0u64; 8];
    g[0] = res[0];
    for m in 1..8 {
        let fpm = &params.fp[m];
        let mut s = g[0] as u128;
        for i in 1..m {
            s += (g[i] as u128) * (params.prefix_mod[m][i] as u128);
        }
        let cur = fpm.red128(s);
        g[m] = mulmod(submod(res[m], cur, fpm.p), params.inv_prefix_mod[m], fpm.p);
    }

    let mut z = [0u64; 9];
    z[0] = g[0];
    for m in 1..8 {
        add_mul_u64(&mut z, &params.prefix_prods[m], g[m]);
    }

    let d_neg = gt_limbs(&z, &params.half_mqb_limbs);
    let d_mag = if !d_neg {
        z
    } else {
        sub_limbs(&params.mqb_limbs, &z)
    };

    // Compute signed `num = t * D + floor(Q/2)`:
    let td_mag = mul_limbs9_u64(&d_mag, params.t);
    let mut hq9 = [0u64; 9];
    hq9[..3].copy_from_slice(&params.half_q_limbs);

    let (num_neg, num_mag) = if !d_neg {
        (false, add_limbs(&td_mag, &hq9))
    } else if gt_limbs(&td_mag, &hq9) {
        (true, sub_limbs(&td_mag, &hq9))
    } else {
        (false, sub_limbs(&hq9, &td_mag))
    };

    let (q_abs, rem_abs) = divrem_u576_by_u192(&num_mag, &params.q_limbs);
    debug_assert_eq!(q_abs[5], 0);
    debug_assert_eq!(q_abs[6], 0);
    let mut q5 = [q_abs[0], q_abs[1], q_abs[2], q_abs[3], q_abs[4]];

    let (y_signed, s_limbs) = if !num_neg {
        (SignedU320 { neg: false, mag: q5 }, rem_abs)
    } else if rem_abs == [0, 0, 0] {
        let is_zero = q5 == [0, 0, 0, 0, 0];
        (SignedU320 { neg: !is_zero, mag: q5 }, [0, 0, 0])
    } else {
        let one5 = [1u64, 0, 0, 0, 0];
        q5 = add_limbs(&q5, &one5);
        let s = sub_limbs(&params.q_limbs, &rem_abs);
        (SignedU320 { neg: true, mag: q5 }, s)
    };

    let y_mod_qp = [
        y_signed.mod_p(params.qp[0]),
        y_signed.mod_p(params.qp[1]),
        y_signed.mod_p(params.qp[2]),
    ];
    (y_signed, s_limbs, y_mod_qp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_integer::Integer;

    #[test]
    fn divrem_and_behz_match_bigint_exact() {
        let params = HoistedParams::n8192();
        let q_bi = BigInt::from(params.q_big.clone());
        let hq_bi = &q_bi >> 1usize;
        let t_bi = BigInt::from(params.t);

        let mut rng_state = 0x1234_5678_9abc_def0u64;
        for case in 0..2000 {
            rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let neg = (case % 2 == 1) && (case > 0);
            let d_bi: BigInt = if case == 0 {
                BigInt::from(0)
            } else if case < 10 {
                let small = BigInt::from((case as i64 - 5) * 17);
                small
            } else {
                let mut mag = BigUint::from(0u32);
                for _ in 0..6 {
                    rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    mag = (mag << 64usize) | BigUint::from(rng_state);
                }
                // Up to 384 bits (deployed K=64 bound)
                let bi = BigInt::from(mag);
                if neg { -bi } else { bi }
            };

            let mut res = [0u64; 8];
            for l in 0..8 {
                let p_bi = BigInt::from(params.all_primes[l]);
                let r_bi = d_bi.mod_floor(&p_bi);
                res[l] = r_bi.to_u64_digits().1.first().copied().unwrap_or(0);
            }

            let (y_got, s_got, y_qp_got) = behz_rescale_from_8limbs(&params, &res);
            let num_bi = &t_bi * &d_bi + &hq_bi;
            let (y_want, s_want) = num_bi.div_mod_floor(&q_bi);

            let s_want_u = s_want.to_biguint().unwrap();
            assert_eq!(s_got, biguint_to_limbs3(&s_want_u), "s mismatch at case {case}");

            let (y_sign, y_digits) = y_want.to_u64_digits();
            let want_neg = y_sign == num_bigint::Sign::Minus;
            let mut want_mag = [0u64; 5];
            for (i, &v) in y_digits.iter().enumerate() {
                want_mag[i] = v;
            }
            assert_eq!(y_got.neg, want_neg, "y sign mismatch at case {case}");
            assert_eq!(y_got.mag, want_mag, "y mag mismatch at case {case}");

            for k in 0..3 {
                let pk = BigInt::from(params.qp[k]);
                let yk = y_want.mod_floor(&pk).to_u64_digits().1.first().copied().unwrap_or(0);
                assert_eq!(y_qp_got[k], yk);
            }
        }
    }
}
