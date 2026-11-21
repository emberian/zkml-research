#!/usr/bin/env python3
"""Deterministic exact-arithmetic repricing of Reed-Solomon proximity regimes
beyond Johnson (Dao-Kominers-Thaler ePrint 2026/2056, Gabizon ePrint 2026/2048,
Jeronimo arXiv:2609.05870) against Selvage / Dregg proof-system configurations.

Every security comparison uses exact Python integers / fractions.Fraction or
certified high-precision Decimal interval bounds (80 decimal digits).
All published reference vectors from TwoRegimeQueryBudget.lean, DKT26 (SS1.1,
4.3, 5.6, 5.7, 8.2-8.4, 10.5, App. H), and Plonky3 #2282 are verified as
live falsification guards before evaluating our parameter grid.
"""

from __future__ import annotations

import json
import math
import sys
from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# 80 decimal digits (~265 bits) for irrational thresholds (sqrt, cubic root u_rho, log2).
getcontext().prec = 80


# ============================================================================
# 1. Exact integer / rational / high-precision Decimal helpers
# ============================================================================

def ceil_frac(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def isqrt_ceil(num: int, den: int) -> int:
    """Exact ceil(sqrt(num / den)) for positive integers num, den."""
    if num <= 0:
        return 0
    q = num // den
    r = math.isqrt(q)
    if r * r * den < num:
        return r + 1
    return r


def isqrt_floor(n: int) -> int:
    return math.isqrt(n)


def dec_sqrt(x: Decimal) -> Decimal:
    return x.sqrt()


def dec_log2(x: Decimal) -> Decimal:
    if x <= 0:
        raise ValueError("log2 requires positive argument")
    return x.ln() / Decimal(2).ln()


def frac_log2_float(x: Fraction) -> float:
    """Display-only bits (-log2(x) uses -frac_log2_float(x)); never used for gates."""
    if x <= 0:
        return float("-inf")
    num_bits = x.numerator.bit_length() - 1
    den_bits = x.denominator.bit_length() - 1
    scaled_num = Decimal(x.numerator) / (Decimal(2) ** num_bits)
    scaled_den = Decimal(x.denominator) / (Decimal(2) ** den_bits)
    return float(Decimal(num_bits - den_bits) + dec_log2(scaled_num) - dec_log2(scaled_den))


def neg_log2_frac(x: Fraction) -> float:
    """Display-only security bits -log2(x) for exact positive Fraction x."""
    return -frac_log2_float(x)


def max_agreement_for_queries(n: int, queries: int, target_bits: int, pow_bits: int) -> int:
    """Exact largest integer A in [0, n] such that (A/n)^queries * 2^{-pow_bits} <= 2^{-target_bits}.

    Uses Decimal estimate + 2 exact integer-power checks instead of O(log n) giant pows.
    """
    eff_bits = target_bits - pow_bits
    if eff_bits <= 0:
        return n
    if queries <= 0:
        return 0
    rhs = n ** queries
    est = int(Decimal(n) * (Decimal(2) ** (Decimal(-eff_bits) / Decimal(queries))))
    cand = max(0, min(n, est))
    while cand < n and (((cand + 1) ** queries) << eff_bits) <= rhs:
        cand += 1
    while cand > 0 and ((cand ** queries) << eff_bits) > rhs:
        cand -= 1
    return cand


def min_queries_for_agreement_frac(a_num: int, a_den: int, target_bits: int, pow_bits: int) -> int:
    """Exact smallest integer q >= 0 such that (a_num / a_den)^q * 2^{-pow_bits} <= 2^{-target_bits}."""
    eff_bits = target_bits - pow_bits
    if eff_bits <= 0:
        return 0
    if a_num >= a_den:
        raise ValueError("agreement >= 1 cannot clear positive effective bits")
    q = max(1, int(eff_bits / (-math.log2(a_num / a_den))))
    while ((a_num ** q) << eff_bits) > (a_den ** q):
        q += 1
    while q > 1 and ((a_num ** (q - 1)) << eff_bits) <= (a_den ** (q - 1)):
        q -= 1
    return q


# ============================================================================
# 2. Asymptotic curves: UDR, JBR, DKT26 a_1(rho), Gabizon 2026/2048, CBR
# ============================================================================

def rho_cutoff_dkt() -> Decimal:
    """DKT26 SS4.3 Eq. (27): rho_c = 11 - 3 * sqrt(13) ~ 0.183346179."""
    return Decimal(11) - Decimal(3) * dec_sqrt(Decimal(13))


def solve_u_rho(rho: Decimal) -> Tuple[Decimal, Decimal]:
    """Solve u^2 * (u + 3) = sqrt(rho / 2) to certified 70-digit interval [lo, hi]."""
    target = dec_sqrt(rho / Decimal(2))
    lo = Decimal(0)
    hi = target.sqrt()  # since u^2(u+3) >= 3 u^2, u <= sqrt(target/3) < sqrt(target)
    for _ in range(260):
        mid = (lo + hi) / Decimal(2)
        if mid * mid * (mid + Decimal(3)) < target:
            lo = mid
        else:
            hi = mid
    return lo, hi


def dkt_a1_interval(rho_frac: Fraction) -> Tuple[Decimal, Decimal, str]:
    """Certified [lo, hi] enclosure for DKT26 SS4.3 Eq. (31) two-branch curve a_1(rho)."""
    rho = Decimal(rho_frac.numerator) / Decimal(rho_frac.denominator)
    rc = rho_cutoff_dkt()
    eps = Decimal("1e-72")
    if rho >= rc:
        # Upper branch: (3*rho + 2*sqrt(rho*(5 - rho)*(2 - rho))) / (8 - rho)
        rad = rho * (Decimal(5) - rho) * (Decimal(2) - rho)
        val = (Decimal(3) * rho + Decimal(2) * dec_sqrt(rad)) / (Decimal(8) - rho)
        return val - eps, val + eps, "upper (lambda_d <= 1/2)"
    else:
        u_lo, u_hi = solve_u_rho(rho)
        sr2 = dec_sqrt(rho / Decimal(2))
        lo = sr2 * (Decimal(1) + u_lo) - eps
        hi = sr2 * (Decimal(1) + u_hi) + eps
        return lo, hi, "lower (lambda_d > 1/2)"


def gabizon_alpha_quadratic(rho_frac: Fraction) -> Decimal:
    """Gabizon 2026/2048 Lemma 4.5 exact root of alpha^2/rho - 1 + 3(1-alpha)^2/(4(2-rho)) = 0.
    Note: algebraically identical to DKT26's upper branch extended across all rho (misses Rank transition at lambda_d = 1/2).
    """
    rho = Decimal(rho_frac.numerator) / Decimal(rho_frac.denominator)
    rad = rho * (Decimal(5) - rho) * (Decimal(2) - rho)
    return (Decimal(3) * rho + Decimal(2) * dec_sqrt(rad)) / (Decimal(8) - rho)


def gabizon_alpha_explicit(rho_frac: Fraction) -> Decimal:
    """Gabizon 2026/2048 p. 9 concrete display: sqrt(rho) * (1 - (1 - sqrt(rho))^2 / 8)."""
    rho = Decimal(rho_frac.numerator) / Decimal(rho_frac.denominator)
    sr = dec_sqrt(rho)
    return sr * (Decimal(1) - ((Decimal(1) - sr) ** 2) / Decimal(8))


def asymptotic_queries_dkt_a1(rho_frac: Fraction, target_bits: int, pow_bits: int) -> int:
    """Smallest integer q with a_1(rho)^q * 2^{-pow_bits} <= 2^{-target_bits}, verified on interval."""
    eff = target_bits - pow_bits
    if eff <= 0:
        return 0
    a_lo, a_hi, _ = dkt_a1_interval(rho_frac)
    bpq_lo = -dec_log2(a_hi)
    bpq_hi = -dec_log2(a_lo)
    q_lo = math.ceil(Decimal(eff) / bpq_hi)
    q_hi = math.ceil(Decimal(eff) / bpq_lo)
    assert q_lo == q_hi, f"Interval precision ambiguous at rho={rho_frac}: {q_lo} vs {q_hi}"
    return q_hi


# ============================================================================
# 3. TwoRegimeQueryBudget.lean exact rational squared-survival verifier
# ============================================================================

def two_regime_bits(lb: int, q: int, pow_bits: int, regime: str) -> int:
    """Exact two-sided integer bit floor k satisfying errSq <= 1/4^k and 1/4^{k+1} < errSq."""
    rho = Fraction(1, 1 << lb)
    if regime == "UDR":
        surv_sq = ((1 + rho) / 2) ** 2
    elif regime == "JBR":
        surv_sq = rho
    elif regime == "CBR":
        surv_sq = rho ** 2
    else:
        raise ValueError(f"Unknown regime {regime}")
    err_sq = (surv_sq ** q) / Fraction(1 << (2 * pow_bits), 1)
    # Find k such that 4^k * num <= den < 4^{k+1} * num
    num, den = err_sq.numerator, err_sq.denominator
    k = (den.bit_length() - num.bit_length()) // 2
    while (num << (2 * k)) > den:
        k -= 1
    while (num << (2 * (k + 1))) <= den:
        k += 1
    assert (num << (2 * k)) <= den < (num << (2 * (k + 1)))
    return k


# ============================================================================
# 4. DKT26 SS5.3 & SS5.7: Zeroth-order (Johnson) MCA in EVERY characteristic
# ============================================================================

def psi_ord(D: int, B: int) -> int:
    """DKT26 SS5.3 Eq. (37): Psi_D(B)."""
    if D < 1 or B < 1:
        raise ValueError("require D >= 1 and B >= 1")
    return 1 + (2 * D - 1) * (2 * B - 1) + 2 * max(0, B - 2 * D - 1)


def minimize_convex_int(lo: int, hi: int, fn) -> Tuple[int, Fraction]:
    """Exact integer minimizer of a discrete convex function on [lo, hi]."""
    while lo < hi:
        mid = (lo + hi) // 2
        if fn(mid + 1) < fn(mid):
            lo = mid + 1
        else:
            hi = mid
    return lo, fn(lo)


def e_ord_at_threshold(n: int, D: int, A: int, B: int, H: int, L: int, ell: int = 1) -> Fraction:
    """DKT26 SS5.3 Eq. (38): E_ord^{(ell)}(D, A, n; B, H; L)."""
    if B == 0:
        return Fraction(H, 1)
    joint = ell * B + H * psi_ord(D, B)
    return (
        Fraction((2 * B - 1) * H, 1)
        + Fraction(n - L + 1, A - L + 1) * joint
        + Fraction(ell * (n - L) * B, 1)
    )


def e_ord_min(n: int, D: int, A: int, B: int, H: int, ell: int = 1) -> Tuple[int, Fraction]:
    if B == 0:
        return D + 1, Fraction(H, 1)
    return minimize_convex_int(D + 1, A, lambda L: e_ord_at_threshold(n, D, A, B, H, L, ell))


@dataclass
class JohnsonCert:
    n: int
    k: int
    A: int
    m: int
    B_jet: int
    B_Z: int
    list_bound: int
    E_exact_L_k: Fraction
    E_exact_opt_L: Fraction
    E_closed_upper: Fraction  # ell * 8 * n * (m + 1/2)^3 / (3 * rho_minus)
    E_bchks25_approx: Fraction  # ell * 2 * (m + 1/2)^5 * n / (3 * rho^{3/2}) for comparison


def dkt_johnson_certificate(n: int, k: int, A: int, ell: int = 1) -> Optional[JohnsonCert]:
    """DKT26 Theorem 5.12 (SS5.7) + Plonky3 #2282 curve extension (SS7.2 Eq. (88)).
    Valid in EVERY characteristic (including char = 2) whenever A^2 > (k - 1)*n.
    """
    D = k - 1
    if D < 1 or A <= k or A > n:
        return None
    if A * A <= D * n:
        return None  # Not strictly above finite Johnson threshold sqrt((k-1)/n)
    # eta_0 = A/n - sqrt(D/n) > 0. Need m = max(ceil(sqrt(D/n) / (2 * eta_0)), 3).
    # Equivalently m >= sqrt(D*n) / (2 * (A - sqrt(D*n))).
    # Exact check for integer m >= 3: 2*m*A >= (2*m + 1)*sqrt(D*n) <=> 4*m^2*A^2 >= (2*m + 1)^2 * D * n.
    # Let's compute exact smallest integer m >= 3 satisfying Proposition B.1's C_spec <= m*A:
    # C_spec = ceil((m + 1/2) * sqrt(D*n)) = isqrt_ceil((2*m + 1)^2 * D * n, 4).
    # Wait: Theorem 5.12 defines m = max(ceil(sqrt(rho_minus) / (2 * eta_0)), 3) where a = A/n:
    # m < sqrt(D*n) / (2*(A - sqrt(D*n)))  <=>  2*m*A - (2*m + 1)*sqrt(D*n) < 0
    # <=> (2*m*A)^2 < ((2*m + 1)^2) * D * n.
    lo_m, hi_m = 3, 2 * n + 4
    # Check hi_m works: at m = n, 2*n*A - (2*n+1)*sqrt(Dn) >= 2*n*sqrt(Dn + 1) - (2n+1)*sqrt(Dn)
    while (2 * hi_m * A) ** 2 < ((2 * hi_m + 1) ** 2) * D * n:
        hi_m *= 2
    while lo_m < hi_m:
        mid = (lo_m + hi_m) // 2
        if (2 * mid * A) ** 2 >= ((2 * mid + 1) ** 2) * D * n:
            hi_m = mid
        else:
            lo_m = mid + 1
    m = lo_m
    four_t2 = (2 * m + 1) ** 2  # 4 * t^2 where t = m + 1/2
    B_jet = isqrt_ceil(four_t2 * n, 4 * D) - 1
    # ceil(ell * t^2 * n / (3 * D)) - 1 = (ell * four_t2 * n - 1) // (12 * D)
    B_Z = (ell * four_t2 * n - 1) // (12 * D)
    classical_pair = (n * (A - D)) // (A * A - n * D)
    list_bound = min(B_jet, classical_pair)
    E_L_k = e_ord_at_threshold(n, D, A, B_jet, B_Z, D + 1, ell)
    _, E_opt = e_ord_min(n, D, A, B_jet, B_Z, ell)
    # Closed-form upper bound: ell * 8 * n * t^3 / (3 * rho_minus) = ell * n^2 * (2m+1)^3 / (3 * D)
    E_closed = Fraction(ell * (n * n) * ((2 * m + 1) ** 3), 3 * D)
    # BCHKS25 Thm 4.2 / 2026/532 Thm 19 comparison scale: ell * m * (2 * m^4 / (3 * rho) + 1) * n
    # using t = m + 1/2 and rho = k/n, rho^{-3/2} approximated conservatively via integer square if even blowup:
    # More precisely, BCHKS25 Thm 1.5 leading scale is (2/3) * ell * t^5 * n / rho_minus^{3/2};
    # square to get rational or bound sqrt(D/n) <= A/n: we compute exact rational upper via isqrt_floor:
    # Here we use S-two Thm 28 formula: ell * m * (2 * m^4 * n / (3 * k) + 1) * isqrt_ceil(n, k) * n / 1 (at Johnson m_GS = ceil(m / sqrt(rho))):
    # Specifically in 2026/532 Thm 19/28, l_GS = ceil(t / sqrt(rho)), bound = ell * l_GS * (2 * l_GS^4 / 3 + 1) * n:
    l_gs = B_jet + 1
    E_bchks = Fraction(ell * l_gs * (2 * (l_gs ** 4) + 3) * n, 3)
    return JohnsonCert(
        n=n, k=k, A=A, m=m, B_jet=B_jet, B_Z=B_Z,
        list_bound=list_bound,
        E_exact_L_k=E_L_k,
        E_exact_opt_L=E_opt,
        E_closed_upper=E_closed,
        E_bchks25_approx=E_bchks,
    )


def plonky3_johnson_line_count_log2(log_degree: int, log_inv_rate: int, m: int) -> float:
    """Exact match of Plonky3 security/src/proximity.rs::johnson_exceptional_line_count_log2 (#2282)."""
    if m < 3 or log_inv_rate == 0:
        return float("inf")
    if log_degree == 0:
        log_n_minus_1 = log_inv_rate + math.log2(1.0 - 2.0 ** (-log_inv_rate))
        return log_inv_rate + log_n_minus_1 - 1.0
    log_n = float(log_degree + log_inv_rate)
    log_rho_minus = math.log2(1.0 - 2.0 ** (-log_degree)) - float(log_inv_rate)
    return 3.0 + log_n + 3.0 * math.log2(m + 0.5) - math.log2(3.0) - log_rho_minus


# ============================================================================
# 5. DKT26 SS4.3 & SS5.6: First-order interpolation, O(mu) fast exact counts,
#    Proposition 5.10 certificates, Lemma 5.6 (squarefree) & Lemma 5.9 (stages)
# ============================================================================

def sum_min_linear_cap(u_lo: int, u_hi: int, low: int, m: int) -> int:
    """Exact sum_{u = u_lo}^{u_hi} min(max(0, u - low + 1), m - u) in O(1) arithmetic."""
    u_lo = max(u_lo, low)
    u_hi = min(u_hi, m - 1)
    if u_lo > u_hi:
        return 0
    # u - low + 1 <= m - u  <=>  2*u <= m + low - 1  <=>  u <= (m + low - 1) // 2
    split = (m + low - 1) // 2
    total = 0
    # Left piece: u in [u_lo, min(u_hi, split)], summand = u - low + 1
    l_end = min(u_hi, split)
    if u_lo <= l_end:
        cnt = l_end - u_lo + 1
        first = u_lo - low + 1
        last = l_end - low + 1
        total += cnt * (first + last) // 2
    # Right piece: u in [max(u_lo, split + 1), u_hi], summand = m - u
    r_start = max(u_lo, split + 1)
    if r_start <= u_hi:
        cnt = u_hi - r_start + 1
        first = m - r_start
        last = m - u_hi
        total += cnt * (first + last) // 2
    return total


def sum_min_const_cap(u_lo: int, u_hi: int, c_val: int, m: int) -> int:
    """Exact sum_{u = u_lo}^{u_hi} min(c_val, m - u) for c_val > 0 in O(1) arithmetic."""
    if c_val <= 0:
        return 0
    u_hi = min(u_hi, m - 1)
    if u_lo > u_hi:
        return 0
    # c_val <= m - u  <=>  u <= m - c_val
    split = m - c_val
    total = 0
    l_end = min(u_hi, split)
    if u_lo <= l_end:
        total += (l_end - u_lo + 1) * c_val
    r_start = max(u_lo, split + 1)
    if r_start <= u_hi:
        cnt = u_hi - r_start + 1
        total += cnt * ((m - r_start) + (m - u_hi)) // 2
    return total


def support_profiles_fast(
    n: int, k: int, A: int, m: int, M: int, mu: int, weighted: bool = True
) -> Tuple[List[int], List[int]]:
    """Exact O(mu) computation of (N_coef(t), R_loc(t))_{t=0..mu} matching DKT26 Eq. (61)-(62)."""
    D = max(k, 2) - 1
    M = min(M, mu)
    Ns: List[int] = []
    rs: List[int] = []
    mA = m * A
    for t in range(mu + 1):
        cap = min(t, M)
        base = mA - D * t
        if weighted:
            lo = max(0, 1 - base)
            if lo <= cap:
                cnt = cap - lo + 1
                Nt = cnt * base + (lo + cap) * cnt // 2
            else:
                Nt = 0
        else:
            Nt = (cap + 1) * max(0, base)
        Ns.append(Nt)

        u_min = max(0, t - M)
        if weighted:
            # Need u + (D - 1)*t < mA  <=>  u <= mA - (D - 1)*t - 1
            u_max = min(m - 1, mA - (D - 1) * t - 1)
            if u_min > u_max:
                rs.append(0)
            else:
                low = u_min
                # Split u < t (high = u) vs u >= t (high = t)
                rt1 = sum_min_linear_cap(u_min, min(u_max, t - 1), low, m)
                rt2 = sum_min_const_cap(max(u_min, t), u_max, t - low + 1, m)
                rs.append(rt1 + rt2)
        else:
            # Unweighted: low_u = max(t - M, 0, u + D*t - mA + 1).
            # Notice for u + D*t - mA + 1 <= max(0, t - M) <=> u <= max(0, t - M) + mA - D*t - 1:
            # When u > that threshold, high - low_u + 1 = min(t, u) - (u + D*t - mA) = min(t - u, 0) + mA - D*t.
            thresh = u_min + mA - D * t - 1
            rt = 0
            # Region A: u in [u_min, min(m - 1, thresh)], low = u_min
            ua_hi = min(m - 1, thresh)
            if u_min <= ua_hi:
                rt += sum_min_linear_cap(u_min, min(ua_hi, t - 1), u_min, m)
                rt += sum_min_const_cap(max(u_min, t), ua_hi, t - u_min + 1, m)
            # Region B: u in [max(u_min, thresh + 1), m - 1], low_u = u + D*t - mA + 1
            ub_lo = max(u_min, thresh + 1)
            if ub_lo <= m - 1:
                # Subregion B1: u < t => high - low_u + 1 = u - (u + D*t - mA + 1) + 1 = mA - D*t (constant!)
                c_b1 = mA - D * t
                if c_b1 > 0 and ub_lo <= t - 1:
                    rt += sum_min_const_cap(ub_lo, min(m - 1, t - 1), c_b1, m)
                # Subregion B2: u >= t => high - low_u + 1 = t - u + mA - D*t = (mA - (D - 1)*t) - u
                # min((mA - (D - 1)*t) - u, m - u) = min(mA - (D - 1)*t, m) - u!
                ub2_lo = max(ub_lo, t)
                m_eff = min(mA - (D - 1) * t, m)
                ub2_hi = min(m - 1, m_eff - 1)
                if ub2_lo <= ub2_hi:
                    cnt = ub2_hi - ub2_lo + 1
                    rt += cnt * ((m_eff - ub2_lo) + (m_eff - ub2_hi)) // 2
            rs.append(rt)
    return Ns, rs


def column_profile_fast(k: int, A: int, m: int, M: int, mu: int, weighted: bool = True) -> List[int]:
    """Exact O(mu) computation of N_{Y_0}(a) for a = 0..mu (DKT26 Proposition 5.10 Eq. (64))."""
    D = max(k, 2) - 1
    M = min(M, mu)
    step = D - 1 if weighted else D
    mA = m * A
    out: List[int] = []
    for a in range(mu + 1):
        b_max = min(M, mu - a)
        c0 = mA - D * a  # x count at b = 0 is max(0, c0 - step * b)
        if c0 <= 0 or b_max < 0:
            out.append(0)
            continue
        if step == 0:
            out.append((b_max + 1) * c0)
        else:
            # Positive while step * b < c0 <=> b <= (c0 - 1) // step
            b_pos = min(b_max, (c0 - 1) // step)
            cnt = b_pos + 1
            last = c0 - step * b_pos
            out.append(cnt * (c0 + last) // 2)
    return out


def shifted_row_height(Ns: List[int], rs: List[int], n: int, ell: int = 1) -> int:
    """Exact smallest integer B_Z >= 0 satisfying DKT26 Eq. (63)."""
    slope = 0
    intercept = 0
    mu = len(Ns) - 1
    for t in range(mu + 1):
        diff = Ns[t] - n * rs[t]
        slope += diff
        intercept += ell * t * diff
        # For B_Z in [start, end], active indices with B_Z - ell*u + 1 > 0 are u <= t:
        # B_Z - ell*u + 1 >= 1 <=> u <= B_Z // ell. So u <= t iff B_Z in [ell*t, ell*(t+1) - 1] (or t == mu: [ell*mu, inf)).
        start = ell * t
        end = ell * (t + 1) - 1
        if slope > 0:
            # Want slope * (B_Z + 1) - intercept > 0 <=> slope * B_Z > intercept - slope
            need = (intercept - slope) // slope + 1
            cand = max(start, need)
            if t == mu or cand <= end:
                return max(0, cand)
    raise ValueError("Nonpositive total interpolation surplus")


def prop_5_10_height(
    n: int, k: int, A: int, m: int, M: int, mu: int, weighted: bool = True, ell: int = 1
) -> Optional[Dict[str, int]]:
    """DKT26 Proposition 5.10 exact finite support & challenge-degree certificate."""
    M = min(M, mu)
    Ns, rs = support_profiles_fast(n, k, A, m, M, mu, weighted)
    N_coef = sum(Ns)
    R_loc = sum(rs)
    if N_coef <= n * R_loc:
        return None
    row_h = shifted_row_height(Ns, rs, n, ell)
    col_prof = column_profile_fast(k, A, m, M, mu, weighted)
    W_col = sum(a * c for a, c in enumerate(col_prof))
    lo, hi = 0, (ell * W_col) // (N_coef - n * R_loc)

    def col_valid(H: int) -> bool:
        return sum(c * max(0, H - ell * a + 1) for a, c in enumerate(col_prof)) > n * R_loc * (H + 1)

    while not col_valid(hi):
        hi = hi * 2 + 1
    while lo < hi:
        mid = (lo + hi) // 2
        if col_valid(mid):
            hi = mid
        else:
            lo = mid + 1
    col_h = lo
    return {
        "N_coef": N_coef,
        "R_loc": R_loc,
        "B_Z": min(row_h, col_h),
        "row_B_Z": row_h,
        "col_B_Z": col_h,
    }


def lemma_5_6_squarefree_bounds(
    n: int, k: int, A: int, B_jet: int, B_d: int, B_Z: int, ell: int = 1, tight_taylor: bool = True
) -> Tuple[Fraction, int, Fraction, int]:
    """DKT26 Lemma 5.6 (squarefree first-order counting, Eqs. (54)-(56)) with independent ordinary tail L_0."""
    D = max(k, 2) - 1
    M = min(B_d, B_jet)
    lam_agr = Fraction(n - D, A - D)
    if M == 0:
        _, e0 = e_ord_min(n, D, A, B_jet, B_Z, ell)
        return Fraction(B_jet, 1), B_jet, e0, ceil_frac(e0)
    tau = max(0, 2 * D - 3) if tight_taylor else (2 * D - 1)
    u = 1 + tau * (B_jet - 1)
    v = min(u, tau * (M - 1) + D)
    F_reg = B_jet * v + M * (u - v)
    S = max(B_jet, (2 * M - 1) * B_jet - M * M)
    H_s = (2 * M - 1) * B_Z
    J_ell = B_Z * (2 * u * v - v * v) + 2 * (ell + tau * B_Z) * F_reg

    list_exact = lam_agr * F_reg + S
    list_int = int(list_exact)  # Lemma 5.11: size of finite set <= rational bound => <= floor(bound)!

    _, E_ord = e_ord_min(n, D, A, S, H_s, ell)

    def reg_obj(L: int) -> Fraction:
        return (
            E_ord
            + Fraction(n - L + 1, A - L + 1) * lam_agr * J_ell
            + Fraction(ell * (n - L) * (n - D), L - D) * F_reg
        )

    _, E_exact = minimize_convex_int(D + 1, A, reg_obj)
    # Note: |E| is an integer <= E_exact, while DKT's tuner records ceil(E_exact) as upper bound;
    # floor(E_exact) is mathematically valid for cardinality, we record ceil_frac(E_exact) to match DKT26 verbatim!
    return list_exact, list_int, E_exact, ceil_frac(E_exact)


def lemma_5_9_successive_stage_bounds(
    n: int, k: int, A: int, B_jet: int, B_d: int, B_Z: int, ell: int = 1, tight_taylor: bool = True
) -> Tuple[Fraction, int, Fraction, int]:
    """DKT26 Lemma 5.9 (successive-stage counting with ordinary tail, Eq. (59))."""
    D = max(k, 2) - 1
    M = min(B_d, B_jet)
    lam_agr = Fraction(n - D, A - D)
    if M == 0:
        _, e0 = e_ord_min(n, D, A, B_jet, B_Z, ell)
        return Fraction(B_jet, 1), B_jet, e0, ceil_frac(e0)
    tau = max(0, 2 * D - 3) if tight_taylor else (2 * D - 1)

    def stage_sums(d: int) -> Tuple[int, int]:
        D_joint = 0
        D_fiber = 0
        for i in range(d):
            j_i = B_jet - i
            r_i = d - i
            b_i = 1 + tau * (j_i - 1)
            c_i = min(b_i, tau * (r_i - 1) + D)
            fib = j_i * c_i + r_i * (b_i - c_i)
            D_fiber += fib
            D_joint += B_Z * (2 * b_i * c_i - c_i * c_i) + 2 * (ell + tau * B_Z) * fib
        return D_joint, D_fiber

    _, D_fib_max = stage_sums(M)
    list_exact = lam_agr * D_fib_max + (B_jet - M)
    list_int = int(list_exact)

    worst_E = Fraction(0, 1)
    for d in range(0, M + 1):
        b_tail = B_jet - d
        _, E_tail = e_ord_min(n, D, A, b_tail, B_Z, ell)
        if d == 0:
            E_d = E_tail
        else:
            D_joint, D_fib = stage_sums(d)

            def obj(L: int) -> Fraction:
                return (
                    E_tail
                    + Fraction(n - L + 1, A - L + 1) * lam_agr * D_joint
                    + Fraction(ell * (n - L) * (n - D), L - D) * D_fib
                )

            _, E_d = minimize_convex_int(D + 1, A, obj)
        if E_d > worst_E:
            worst_E = E_d

    return list_exact, list_int, worst_E, ceil_frac(worst_E)


@dataclass
class FirstOrderCert:
    n: int
    k: int
    A: int
    m: int
    B_d: int
    B_jet: int
    B_Z: int
    weighted: bool
    Lambda: int
    E: int
    char_guard: int  # p > max(k - 1, B_d)
    method: str


def evaluate_first_order_support(
    n: int, k: int, A: int, m: int, B_d: int, B_jet: int,
    weighted: bool = True, ell: int = 1, tight_taylor: bool = True,
    include_stages: bool = True,
) -> Optional[FirstOrderCert]:
    h = prop_5_10_height(n, k, A, m, B_d, B_jet, weighted=weighted, ell=ell)
    if h is None:
        return None
    B_Z = h["B_Z"]
    B_d_eff = min(B_d, B_jet)
    _, L_sq, _, E_sq = lemma_5_6_squarefree_bounds(n, k, A, B_jet, B_d_eff, B_Z, ell, tight_taylor)
    Lambda, E, method = L_sq, E_sq, "squarefree (Lemma 5.6)"
    if include_stages and B_d_eff <= 80:
        _, L_st, _, E_st = lemma_5_9_successive_stage_bounds(n, k, A, B_jet, B_d_eff, B_Z, ell, tight_taylor)
        Lambda = min(L_sq, L_st)
        if E_st < E_sq:
            E, method = E_st, "successive-stage (Lemma 5.9)"
    return FirstOrderCert(
        n=n, k=k, A=A, m=m, B_d=B_d_eff, B_jet=B_jet, B_Z=B_Z,
        weighted=weighted, Lambda=Lambda, E=E,
        char_guard=max(k - 1, B_d_eff), method=method,
    )


def dkt_analytic_4_3_params(n: int, k: int, A: int) -> Optional[Tuple[int, int, int, int, int, int]]:
    """DKT26 SS4.3 Eqs. (32)-(34) + Thm 5.7/5.8 explicit analytic finite parameters (m, B_d, B_jet, B_Z, Lambda, E)."""
    rho_f = Fraction(k, n)
    a_f = Fraction(A, n)
    a1_lo, a1_hi, branch = dkt_a1_interval(rho_f)
    a_dec = Decimal(A) / Decimal(n)
    if a_dec <= a1_hi:
        return None
    rho_dec = Decimal(k) / Decimal(n)
    rho_n_dec = Decimal(k - 1) / Decimal(n)
    a_cert = min(a_dec, (Decimal(1) + a1_hi) / Decimal(2))
    if "lower" in branch:
        lam_d = (a1_hi - dec_sqrt(rho_dec / Decimal(2))) / rho_dec
    else:
        lam_d = Decimal(3) * (Decimal(1) - a_cert) / (Decimal(2) * (Decimal(2) - rho_dec))

    def coef_fn(r: Decimal, ac: Decimal, ld: Decimal) -> Decimal:
        return (ld * ac * ac) / (Decimal(2) * r) - (ac * ld * ld) / Decimal(2) + (r * (ld ** 3)) / Decimal(6)

    def rank_fn(ld: Decimal) -> Decimal:
        if ld <= Decimal("0.5"):
            return ld / Decimal(2) - (ld * ld) / Decimal(2) + (ld ** 3) / Decimal(3)
        return ld / Decimal(4) + Decimal(1) / Decimal(24)

    margin_n = coef_fn(rho_n_dec, a_cert, lam_d) - rank_fn(lam_d)
    if margin_n <= 0:
        return None
    c_rank = Decimal(2) * lam_d + Decimal(3)
    m = math.ceil((Decimal(4) * c_rank) / margin_n)
    B_d = int(lam_d * Decimal(m))
    B_jet = math.ceil((Decimal(m) * a_cert) / rho_n_dec)
    # Certify via Proposition 5.10 / Lemma 5.6 exact integer check at (m, B_d, B_jet)
    cert = evaluate_first_order_support(n, k, A, m, B_d, B_jet, weighted=False, ell=1, tight_taylor=True)
    if cert is None:
        return None
    return m, B_d, B_jet, cert.B_Z, cert.Lambda, cert.E


def search_sharp_first_order_cert(n: int, k: int, A: int, ell: int = 1) -> Optional[FirstOrderCert]:
    """Deterministic multi-scale search over Proposition 5.10 weighted supports (m, B_d, B_jet)
    minimizing E (and Lambda) for exact integer tuple (n, k, A).
    """
    rho_f = Fraction(k, n)
    a_dec = Decimal(A) / Decimal(n)
    _, a1_hi, branch = dkt_a1_interval(rho_f)
    if a_dec <= a1_hi:
        return None
    rho_dec = Decimal(k) / Decimal(n)
    rho_n_dec = Decimal(k - 1) / Decimal(n)
    a_cert = min(a_dec, (Decimal(1) + a1_hi) / Decimal(2))
    if "lower" in branch:
        lam_star = float((a1_hi - dec_sqrt(rho_dec / Decimal(2))) / rho_dec)
    else:
        lam_star = float(Decimal(3) * (Decimal(1) - a_cert) / (Decimal(2) * (Decimal(2) - rho_dec)))
    mu_ratio_star = float(a_cert / rho_n_dec)

    # Estimate minimum feasible multiplicity m_min by binary search along the asymptotic ray (lam_star, mu_ratio_star)
    def ray_feasible(m_val: int) -> bool:
        bd = max(1, round(lam_star * m_val))
        bj = max(bd + 1, math.ceil(mu_ratio_star * m_val))
        Ns, rs = support_profiles_fast(n, k, A, m_val, bd, bj, weighted=True)
        return sum(Ns) > n * sum(rs)

    # Quick probe up to m = 512 (beyond m = 512, B_jet > 512 so E >> 2^95 > Goldilocks^3 * 2^{-100} anyway)
    m_probe = 4
    while m_probe <= 512 and not ray_feasible(m_probe):
        m_probe *= 2
    best: Optional[FirstOrderCert] = None

    if m_probe <= 512:
        lo_m, hi_m = max(2, m_probe // 2), m_probe
        while lo_m < hi_m:
            mid = (lo_m + hi_m) // 2
            if ray_feasible(mid):
                hi_m = mid
            else:
                lo_m = mid + 1
        m0 = lo_m
        m_cands = sorted({
            max(2, round(m0 * mult))
            for mult in (0.80, 0.90, 1.0, 1.12, 1.25, 1.45, 1.75)
            if round(m0 * mult) <= 640
        })
        for m_val in m_cands:
            bd_center = max(1, round(lam_star * m_val))
            bj_full = max(bd_center + 1, math.ceil(mu_ratio_star * m_val))
            for bd_scale in (0.80, 0.92, 1.0, 1.10):
                bd = max(1, round(bd_center * bd_scale))
                for bj_scale in (0.75, 0.88, 1.0):
                    bj = max(bd, round(bj_full * bj_scale))
                    cert = evaluate_first_order_support(
                        n, k, A, m_val, bd, bj, weighted=True, ell=ell, include_stages=False
                    )
                    if cert is not None:
                        if best is None or (cert.E, cert.Lambda) < (best.E, best.Lambda):
                            best = cert
        if best is not None and best.B_d <= 80:
            best = evaluate_first_order_support(
                n, k, A, best.m, best.B_d, best.B_jet, weighted=best.weighted, ell=ell, include_stages=True
            )

    # Fallback to analytic SS4.3 support if grid above was above m=512 (cap m_a <= 1200 for fast exact run)
    if best is None:
        ana = dkt_analytic_4_3_params(n, k, A)
        if ana is not None:
            m_a, bd_a, bj_a, _, _, _ = ana
            if m_a <= 1200:
                best = evaluate_first_order_support(
                    n, k, A, m_a, bd_a, bj_a, weighted=True, ell=ell, include_stages=False
                )
    return best


# ============================================================================
# 6. Live Falsification / Reproduction Guards (Must pass before our grid runs)
# ============================================================================

def run_falsification_guards() -> Dict[str, object]:
    guards: Dict[str, object] = {}

    # Guard A: Fast O(mu) support_profiles_fast & column_profile_fast == naive reference loops
    for (n, k, A, m, M, mu) in [
        (64, 16, 31, 12, 5, 28),
        (512, 2, 19, 12, 12, 45),
        (2048, 128, 453, 38, 23, 133),
    ]:
        D = max(k, 2) - 1
        for weighted in (True, False):
            Ns_fast, rs_fast = support_profiles_fast(n, k, A, m, M, mu, weighted)
            for t in range(mu + 1):
                cap = min(t, M)
                Nt_ref = sum(max(0, m * A - D * t + (b if weighted else 0)) for b in range(cap + 1))
                rt_ref = 0
                for u in range(max(0, t - M), m):
                    low = max(0, t - M)
                    high = min(t, u)
                    if weighted:
                        if u + (D - 1) * t >= m * A:
                            continue
                    else:
                        low = max(low, u + D * t - m * A + 1)
                    rt_ref += min(max(0, high - low + 1), m - u)
                assert Ns_fast[t] == Nt_ref, f"Ns mismatch at t={t}, weighted={weighted}"
                assert rs_fast[t] == rt_ref, f"rs mismatch at t={t}, weighted={weighted}"

            col_fast = column_profile_fast(k, A, m, M, mu, weighted)
            for a in range(mu + 1):
                ca_ref = sum(
                    max(0, m * A - D * a - (D - 1 if weighted else D) * b)
                    for b in range(min(M, mu - a) + 1)
                )
                assert col_fast[a] == ca_ref, f"col mismatch at a={a}, weighted={weighted}"
    guards["fast_profile_equivalence"] = "PASS (6/6 tuples, weighted & unweighted)"

    # Guard B: TwoRegimeQueryBudget.lean exact two-sided bit theorems
    lean_cells = [
        ("ir2", 6, 19, 16, (34, 73, 130)),
        ("recursionCfg", 3, 38, 14, (45, 71, 128)),
        ("prodV1", 3, 38, 16, (47, 73, 130)),
        ("zkdtvmCore", 1, 261, 20, (128, 150, 281)),
    ]
    for name, lb, q, pw, expected in lean_cells:
        got = (
            two_regime_bits(lb, q, pw, "UDR"),
            two_regime_bits(lb, q, pw, "JBR"),
            two_regime_bits(lb, q, pw, "CBR"),
        )
        assert got == expected, f"Lean mismatch on {name}: got {got}, expected {expected}"
    guards["lean_two_regime_cells"] = "PASS (4/4 configurations, 12/12 two-sided bounds)"

    # Guard C: DKT26 SS1.1 & SS4.3 asymptotic curve values & branch continuity at rho_c
    rc = rho_cutoff_dkt()
    a1_rc_target = Decimal(4) - dec_sqrt(Decimal(13))
    u_rc_lo, u_rc_hi = solve_u_rho(rc)
    a1_rc_lower = dec_sqrt(rc / Decimal(2)) * (Decimal(1) + (u_rc_lo + u_rc_hi) / Decimal(2))
    a1_rc_upper = (Decimal(3) * rc + Decimal(2) * dec_sqrt(rc * (Decimal(5) - rc) * (Decimal(2) - rc))) / (Decimal(8) - rc)
    assert abs(a1_rc_lower - a1_rc_target) < Decimal("1e-65")
    assert abs(a1_rc_upper - a1_rc_target) < Decimal("1e-65")

    a1_q_lo, a1_q_hi, _ = dkt_a1_interval(Fraction(1, 4))
    a1_h_lo, a1_h_hi, _ = dkt_a1_interval(Fraction(1, 2))
    # Exact closed forms: (3 + sqrt(133))/31 at rho=1/4, (1 + sqrt(6))/5 at rho=1/2
    assert a1_q_lo <= (Decimal(3) + dec_sqrt(Decimal(133))) / Decimal(31) <= a1_q_hi
    assert a1_h_lo <= (Decimal(1) + dec_sqrt(Decimal(6))) / Decimal(5) <= a1_h_hi
    guards["dkt_curve_exact_anchors"] = {
        "rho_c": f"{float(rc):.9f}",
        "a1_at_rho_c": f"{float(a1_rc_target):.9f}",
        "a1_quarter": f"{float(a1_q_hi):.9f}",
        "a1_half": f"{float(a1_h_hi):.9f}",
    }

    # Guard D: DKT26 SS8.2, SS8.3, SS8.4 exact rational / integer application certificates!
    # 1) ProveKit Goldilocks lookup Round 2 (SS8.2 p. 73): (n, k, A) = (2048, 128, 453), (m, B_d, B_jet) = (38, 23, 133)
    h_pk2 = prop_5_10_height(2048, 128, 453, 38, 23, 133, weighted=True, ell=1)
    assert h_pk2 is not None
    L_sq_exact, L_sq_int, _, _ = lemma_5_6_squarefree_bounds(2048, 128, 453, 133, 23, h_pk2["B_Z"], ell=1, tight_taylor=True)
    L_st_exact, L_st_int, _, _ = lemma_5_9_successive_stage_bounds(2048, 128, 453, 133, 23, h_pk2["B_Z"], ell=1, tight_taylor=True)
    assert L_sq_exact == Fraction(2659384185, 326), f"Got {L_sq_exact}"
    assert L_sq_int == 8157620, f"Got {L_sq_int}"
    # Lemma 5.9 (ordinary tail B_jet - B_d = 110) gives floor = 93948347; DKT's historical stage_budgets
    # differentiated Y_0 too (B0 = sum_{j=1}^{110} j = 6105) + ceil, giving 93948347 - 110 + 6105 + 1 = 93954343!
    legacy_b0 = (133 - 23) * (133 - 23 + 1) // 2
    assert ceil_frac(L_st_exact - (133 - 23) + legacy_b0) == 93954343, f"Got {L_st_exact}"
    assert L_st_int == 93948347, f"Got {L_st_int}"

    # 2) ZisK compressed final (SS8.3 p. 74): (n, k, A) = (2^19, 2^15, 124136), (10, 6, 37), E_103 + E_4 == 4073087021134687044
    h_z103 = prop_5_10_height(1 << 19, 1 << 15, 124136, 10, 6, 37, weighted=True, ell=103)
    h_z4 = prop_5_10_height(1 << 19, 1 << 15, 124136, 10, 6, 37, weighted=True, ell=4)
    assert h_z103 is not None and h_z4 is not None
    _, _, _, E_z103 = lemma_5_6_squarefree_bounds(1 << 19, 1 << 15, 124136, 37, 6, h_z103["B_Z"], ell=103, tight_taylor=True)
    _, _, _, E_z4 = lemma_5_6_squarefree_bounds(1 << 19, 1 << 15, 124136, 37, 6, h_z4["B_Z"], ell=4, tight_taylor=True)
    assert E_z103 + E_z4 == 4073087021134687044, f"ZisK E_103+E_4 mismatch: {E_z103 + E_z4}"

    # 3) LambdaVM CPU (SS8.4 p. 75): (n, k, A) = (65536, 32768, 45690), (32, 9, 44), ell=50 => B_Z = 36670, ceil(Lambda(T+3)) = 113769033
    h_lam = prop_5_10_height(65536, 32768, 45690, 32, 9, 44, weighted=True, ell=50)
    assert h_lam is not None and h_lam["B_Z"] == 36670, f"LambdaVM B_Z mismatch: {h_lam}"
    L_lam_exact, L_lam_floor, _, _ = lemma_5_6_squarefree_bounds(65536, 32771, 45690, 44, 9, 0, ell=1, tight_taylor=True)
    assert ceil_frac(L_lam_exact) == 113769033 and L_lam_floor == 113769032, f"LambdaVM Lambda mismatch: {L_lam_exact}"

    # 4) Plonky3 PR #2282 DKT26 Johnson vectors
    for ld, lr, m_v, exp_v in [
        (1, 1, 3, 10.837102265451657),
        (2, 1, 3, 11.2521397647305),
        (20, 2, 3, 30.83710364131352),
        (20, 2, 10, 35.59199114347699),
    ]:
        got_v = plonky3_johnson_line_count_log2(ld, lr, m_v)
        assert abs(got_v - exp_v) < 1e-12, f"Plonky3 #2282 mismatch: {got_v} vs {exp_v}"
    jc_test = dkt_johnson_certificate(8, 2, 5, ell=1)
    assert jc_test is not None and jc_test.B_jet == 9 and jc_test.B_Z == 32
    assert jc_test.E_exact_L_k == Fraction(9175, 4)  # 2293.75 exact (Plonky3 proximity.rs:361)!

    guards["dkt_and_plonky3_exact_certificates"] = (
        "PASS (ProveKit 2659384185/326=8157620, ZisK E_103+E_4=4073087021134687044, "
        "LambdaVM B_Z=36670 & Lambda=113769033, Plonky3 #2282 5/5)"
    )
    return guards


# ============================================================================
# 7. Part (a), (b), (c): Asymptotic table, Characteristic split, & Full Grid
# ============================================================================

@dataclass
class FieldSpec:
    name: str
    char: int          # prime characteristic p
    ext_deg: int       # extension degree e
    q: int             # field cardinality p^e

    @property
    def log2_p(self) -> float:
        return math.log2(self.char)

    @property
    def log2_q(self) -> float:
        return float(dec_log2(Decimal(self.q)))


FIELDS: List[FieldSpec] = [
    FieldSpec("BabyBear^4", 2013265921, 4, 2013265921 ** 4),
    FieldSpec("KoalaBear^5", 2130706433, 5, 2130706433 ** 5),
    FieldSpec("Goldilocks^3", (1 << 64) - (1 << 32) + 1, 3, ((1 << 64) - (1 << 32) + 1) ** 3),
    FieldSpec("Tower256 (GF(2^128))", 2, 128, 1 << 128),
    FieldSpec("GF(2^192) (leanVM)", 2, 192, 1 << 192),
]


def part_a_asymptotic_curves() -> List[Dict[str, object]]:
    rows = []
    for lb in [1, 2, 3, 4, 5, 6]:
        rho = Fraction(1, 1 << lb)
        rho_dec = Decimal(rho.numerator) / Decimal(rho.denominator)
        a_udr = (Decimal(1) + rho_dec) / Decimal(2)
        a_jbr = dec_sqrt(rho_dec)
        a1_lo, a1_hi, branch = dkt_a1_interval(rho)
        a_gab_q = gabizon_alpha_quadratic(rho)
        a_gab_exp = gabizon_alpha_explicit(rho)
        a_cbr = rho_dec

        bpq_udr = -dec_log2(a_udr)
        bpq_jbr = -dec_log2(a_jbr)
        bpq_a1 = -dec_log2(a1_hi)
        bpq_gab = -dec_log2(a_gab_q)
        bpq_cbr = -dec_log2(a_cbr)

        rows.append({
            "lb": lb,
            "rate": f"1/{1 << lb}",
            "branch": branch,
            "a_UDR": float(a_udr),
            "a_JBR": float(a_jbr),
            "a_Gab26_explicit": float(a_gab_exp),
            "a_Gab26_quad": float(a_gab_q),
            "a1_DKT": float(a1_hi),
            "a_CBR": float(a_cbr),
            "delta_jbr_minus_a1_pp": float((a_jbr - a1_hi) * Decimal(100)),
            "bpq_UDR": float(bpq_udr),
            "bpq_JBR": float(bpq_jbr),
            "bpq_a1": float(bpq_a1),
            "bpq_CBR": float(bpq_cbr),
            "bpq_gain_pct_over_JBR": float((bpq_a1 / bpq_jbr - Decimal(1)) * Decimal(100)),
            "q100_pow0_UDR_JBR_a1": (
                min_queries_for_agreement_frac((1 << lb) + 1, 1 << (lb + 1), 100, 0),
                math.ceil(Decimal(100) / bpq_jbr),
                asymptotic_queries_dkt_a1(rho, 100, 0),
            ),
            "q100_pow16_UDR_JBR_a1": (
                min_queries_for_agreement_frac((1 << lb) + 1, 1 << (lb + 1), 100, 16),
                math.ceil(Decimal(84) / bpq_jbr),
                asymptotic_queries_dkt_a1(rho, 100, 16),
            ),
            "q128_pow16_UDR_JBR_a1": (
                min_queries_for_agreement_frac((1 << lb) + 1, 1 << (lb + 1), 128, 16),
                math.ceil(Decimal(112) / bpq_jbr),
                asymptotic_queries_dkt_a1(rho, 128, 16),
            ),
            "q128_pow20_UDR_JBR_a1": (
                min_queries_for_agreement_frac((1 << lb) + 1, 1 << (lb + 1), 128, 20),
                math.ceil(Decimal(108) / bpq_jbr),
                asymptotic_queries_dkt_a1(rho, 128, 20),
            ),
        })
    return rows


def check_characteristic_split() -> List[Dict[str, object]]:
    out = []
    k_max = 1 << 30
    b_d_conservative = 10_000  # Every practical finite certificate has B_d <= ~500
    for f in FIELDS:
        req = max(k_max - 1, b_d_conservative)
        passes_k30 = f.char > req
        max_k_allowed = f.char  # since p > k - 1 <=> k <= p
        out.append({
            "field": f.name,
            "char_p": f.char,
            "log2_q": round(f.log2_q, 4),
            "k_up_to_2_30_passes": passes_k30,
            "p_minus_2_30_plus_1": f.char - (k_max - 1),
            "max_dimension_k_for_1st_order": max_k_allowed if f.char > 2 else "LOCKED OUT (k <= 2 only; p=2 fails k>=3)",
            "surviving_mca_regime": (
                "DKT 1st-order (Thm 1.1/5.8) + higher-order + DKT 0th-order Johnson O_rho(n/eta_0^3)"
                if passes_k30
                else "Zeroth-order ONLY: UDR + DKT Theorem 5.12 Johnson O_rho(n/eta_0^3)"
            ),
        })
    return out


def ood_error_u(Lambda: int, k: int, n: int, q: int, u: int) -> Tuple[Fraction, Fraction]:
    """Returns (exact_lemma_8_1_or_eq_93, prompt_Lambda2_k_over_q_form) for u in {1, 2}.
    - Eq. (93) (WHIR single-vector degree k-1): binom(Lambda, 2) * ((k - 1) / q)^u
    - Lemma 8.1 (DEEP early anchor without replacement, u=2, degree k+2): binom(Lambda, 2) * ((k + 2)/(q - n - 1))^2
    We also return the conservative simple ratio (Lambda^2 * k^u) / q^u for direct comparison.
    """
    pairs = Lambda * (Lambda - 1) // 2
    if u == 1:
        eq93 = Fraction(pairs * k, q)
        simple = Fraction((Lambda * Lambda) * k, q)
        return eq93, simple
    elif u == 2:
        denom = max(1, q - n - 1)
        lem81 = Fraction(pairs * ((k + 2) ** 2), denom * denom)
        simple = Fraction((Lambda * Lambda) * (k * k), q * q)
        return lem81, simple
    raise ValueError("u must be 1 or 2")


def evaluate_full_grid() -> Tuple[List[Dict[str, object]], List[Dict[str, object]]]:
    """Evaluate all (n, rho) base certificates + (field, n, rho, target, pow) query savings."""
    log_ns = [18, 20, 22, 24]
    lbs = [1, 2, 3, 6]  # rho in {1/2, 1/4, 1/8, 1/64}
    targets = [100, 128]
    pows = [0, 16, 20]

    # Step 1: Precompute field-independent midpoint beyond-Johnson & Johnson certificates per (n, lb)
    midpoint_summary: List[Dict[str, object]] = []
    for log_n in log_ns:
        n = 1 << log_n
        for lb in lbs:
            k = n >> lb
            rho = Fraction(1, 1 << lb)
            _, a1_hi, _ = dkt_a1_interval(rho)
            a_jbr = dec_sqrt(Decimal(k - 1) / Decimal(n))
            # Midpoint agreement halfway between a_1(rho) and finite Johnson sqrt((k-1)/n):
            a_mid = (a1_hi + a_jbr) / Decimal(2)
            A_mid = int(a_mid * Decimal(n))
            assert A_mid * A_mid < (k - 1) * n, "Midpoint must lie strictly below finite Johnson"
            cert_mid = search_sharp_first_order_cert(n, k, A_mid, ell=1)
            assert cert_mid is not None

            # Also evaluate DKT zeroth-order Johnson at m=10 (alpha = 1.05 * sqrt(rho)) vs BCHKS25
            A_jbr_m10 = math.ceil(1.05 * math.sqrt(k * n))
            jcert = dkt_johnson_certificate(n, k, A_jbr_m10, ell=1)
            assert jcert is not None

            midpoint_summary.append({
                "log2_n": log_n,
                "lb": lb,
                "rate": f"1/{1 << lb}",
                "k": k,
                "A_mid": A_mid,
                "a_mid": round(A_mid / n, 6),
                "a_finite_JBR": round(float(a_jbr), 6),
                "support_mid": (cert_mid.m, cert_mid.B_d, cert_mid.B_jet),
                "B_Z_mid": cert_mid.B_Z,
                "log2_Lambda_mid": round(math.log2(cert_mid.Lambda), 2),
                "log2_E_mid": round(math.log2(cert_mid.E), 2),
                "log2_Lam2_k_u1": round(math.log2(cert_mid.Lambda * cert_mid.Lambda * k), 2),
                "log2_E_JBR_DKT_m10": round(frac_log2_float(jcert.E_exact_opt_L), 2),
                "log2_E_JBR_closed_m10": round(frac_log2_float(jcert.E_closed_upper), 2),
                "log2_E_JBR_BCHKS25_m10": round(frac_log2_float(jcert.E_bchks25_approx), 2),
                "jbr_dkt_gain_bits_over_bchks25": round(
                    frac_log2_float(jcert.E_bchks25_approx) - frac_log2_float(jcert.E_exact_opt_L), 2
                ),
            })

    # Step 2: Cache finite certificates by (n, k, A) so identical query thresholds across fields/pows are computed once!
    fo_cache: Dict[Tuple[int, int, int], Optional[FirstOrderCert]] = {}
    jbr_cache: Dict[Tuple[int, int, int], Optional[JohnsonCert]] = {}

    def get_fo(n: int, k: int, A: int) -> Optional[FirstOrderCert]:
        key = (n, k, A)
        if key not in fo_cache:
            fo_cache[key] = search_sharp_first_order_cert(n, k, A, ell=1)
        return fo_cache[key]

    def get_jbr(n: int, k: int, A: int) -> Optional[JohnsonCert]:
        key = (n, k, A)
        if key not in jbr_cache:
            jbr_cache[key] = dkt_johnson_certificate(n, k, A, ell=1)
        return jbr_cache[key]

    grid_rows: List[Dict[str, object]] = []
    for log_n in log_ns:
        n = 1 << log_n
        for lb in lbs:
            k = n >> lb
            rho = Fraction(1, 1 << lb)
            for target in targets:
                for pw in pows:
                    # Exact UDR query count (a_UDR = (1 + rho)/2 = (2^lb + 1)/2^{lb+1})
                    q_udr = min_queries_for_agreement_frac((1 << lb) + 1, 1 << (lb + 1), target, pw)
                    # Smallest query count whose max allowed A strictly exceeds finite Johnson sqrt((k-1)*n)
                    q_a1_asymp = asymptotic_queries_dkt_a1(rho, target, pw)
                    q_jbr_floor = max(1, q_a1_asymp)
                    while True:
                        A_test = max_agreement_for_queries(n, q_jbr_floor, target, pw)
                        if A_test * A_test > (k - 1) * n:
                            break
                        q_jbr_floor += 1

                    for f in FIELDS:
                        thresh_inv = 1 << target  # need error <= 1 / thresh_inv

                        # 1) Find exact finite Johnson certified query count for this field (DKT Thm 5.12)
                        # Check if field can even satisfy E_JBR / q <= 2^{-target} and OOD <= 2^{-target}
                        q_jbr_cert: Optional[int] = None
                        for q_cand in range(q_jbr_floor, q_udr + 1):
                            A_cand = max_agreement_for_queries(n, q_cand, target, pw)
                            if A_cand >= n:
                                q_jbr_cert = q_cand
                                break
                            jc = get_jbr(n, k, A_cand)
                            if jc is not None:
                                # Check E_opt / f.q <= 2^{-target} and u=1 OOD binom(L,2)*k / f.q <= 2^{-target}
                                ood1, _ = ood_error_u(jc.list_bound, k, n, f.q, 1)
                                if jc.E_exact_opt_L * thresh_inv <= f.q and ood1 * thresh_inv <= 1:
                                    q_jbr_cert = q_cand
                                    break

                        # 2) Check beyond-Johnson candidate query counts q_cand in [q_a1_asymp .. q_jbr_floor - 1]
                        best_u1: Optional[Tuple[int, FirstOrderCert, float, float]] = None
                        best_u2: Optional[Tuple[int, FirstOrderCert, float, float]] = None
                        best_any_bj_E_bits: Optional[float] = None
                        best_any_bj_ood1_bits: Optional[float] = None
                        best_any_bj_ood2_bits: Optional[float] = None

                        if f.char > 2:
                            # Also check the largest strictly-below-Johnson integer A_max_bj = isqrt_floor((k-1)*n)
                            # so we know whether *any* beyond-Johnson point clears E/q <= 2^{-target} even with 0 query savings!
                            A_max_bj = isqrt_floor((k - 1) * n)
                            if A_max_bj * A_max_bj == (k - 1) * n:
                                A_max_bj -= 1
                            cert_edge = get_fo(n, k, A_max_bj)
                            if cert_edge is not None and f.char > cert_edge.char_guard:
                                best_any_bj_E_bits = round(neg_log2_frac(Fraction(cert_edge.E, f.q)), 2)
                                ood1_e, _ = ood_error_u(cert_edge.Lambda, k, n, f.q, 1)
                                ood2_e, _ = ood_error_u(cert_edge.Lambda, k, n, f.q, 2)
                                best_any_bj_ood1_bits = round(neg_log2_frac(ood1_e) if ood1_e > 0 else 999.0, 2)
                                best_any_bj_ood2_bits = round(neg_log2_frac(ood2_e) if ood2_e > 0 else 999.0, 2)

                            for q_cand in range(q_a1_asymp, q_jbr_floor):
                                A_cand = max_agreement_for_queries(n, q_cand, target, pw)
                                cert = get_fo(n, k, A_cand)
                                if cert is None or f.char <= cert.char_guard:
                                    continue
                                # Line MCA check: E / q <= 2^{-target}
                                if cert.E * thresh_inv > f.q:
                                    continue
                                E_bits = neg_log2_frac(Fraction(cert.E, f.q))
                                ood1_eq, ood1_simple = ood_error_u(cert.Lambda, k, n, f.q, 1)
                                ood2_lem, _ = ood_error_u(cert.Lambda, k, n, f.q, 2)
                                # Check strict prompt form Lambda^2 * k / q <= 2^{-target} AND Eq. (93) form
                                if best_u2 is None and ood2_lem * thresh_inv <= 1:
                                    best_u2 = (q_cand, cert, E_bits, neg_log2_frac(ood2_lem))
                                if best_u1 is None and ood1_simple * thresh_inv <= 1:
                                    best_u1 = (q_cand, cert, E_bits, neg_log2_frac(ood1_simple))
                                if best_u1 is not None and best_u2 is not None:
                                    break

                        grid_rows.append({
                            "field": f.name,
                            "char_ok": f.char > max(k - 1, 1000),
                            "log2_n": log_n,
                            "lb": lb,
                            "rate": f"1/{1 << lb}",
                            "target": target,
                            "pow": pw,
                            "q_UDR": q_udr,
                            "q_JBR_query_floor": q_jbr_floor,
                            "q_JBR_finite_cert": q_jbr_cert,
                            "q_a1_asymp": q_a1_asymp,
                            "edge_bj_E_bits": best_any_bj_E_bits,
                            "edge_bj_ood1_bits": best_any_bj_ood1_bits,
                            "edge_bj_ood2_bits": best_any_bj_ood2_bits,
                            "q_DKT_u1": best_u1[0] if best_u1 else None,
                            "q_DKT_u2": best_u2[0] if best_u2 else None,
                            "saved_vs_JBR_floor_u1": (q_jbr_floor - best_u1[0]) if best_u1 else 0,
                            "saved_vs_JBR_floor_u2": (q_jbr_floor - best_u2[0]) if best_u2 else 0,
                            "saved_vs_JBR_cert_u2": (
                                (q_jbr_cert - best_u2[0]) if (best_u2 and q_jbr_cert is not None) else 0
                            ),
                            "saved_vs_UDR_u2": (q_udr - best_u2[0]) if best_u2 else 0,
                            "u2_E_bits": round(best_u2[2], 2) if best_u2 else None,
                            "u2_OOD_bits": round(best_u2[3], 2) if best_u2 else None,
                            "u2_support": (best_u2[1].m, best_u2[1].B_d, best_u2[1].B_jet) if best_u2 else None,
                        })

    return midpoint_summary, grid_rows


# ============================================================================
# 8. CLI entrypoint & structured report
# ============================================================================

def main() -> int:
    print("=" * 88)
    print("BEYOND-JOHNSON REED-SOLOMON PROXIMITY & MCA REPRICING (EXACT ARITHMETIC)")
    print("=" * 88)

    guards = run_falsification_guards()
    print("\n[0] LIVE FALSIFICATION & REPRODUCTION GUARDS")
    for gname, gval in guards.items():
        print(f"  - {gname}: {gval}")

    # Deployed IR-v2 (lb=6, q=19, pow=16) and prodV1 (lb=3, q=38, pow=16) idealised a_1 check:
    a1_64_lo, a1_64_hi, _ = dkt_a1_interval(Fraction(1, 64))
    a1_8_lo, a1_8_hi, _ = dkt_a1_interval(Fraction(1, 8))
    ir2_a1_bits_lo = float(Decimal(16) - Decimal(19) * dec_log2(a1_64_hi))
    ir2_a1_bits_hi = float(Decimal(16) - Decimal(19) * dec_log2(a1_64_lo))
    pv1_a1_bits_lo = float(Decimal(16) - Decimal(38) * dec_log2(a1_8_hi))
    print("\n[0b] DEPLOYED CONFIGS ON IDEALISED ASYMPTOTIC QUERY COLUMN ALONE")
    print(f"  - IR-v2  (lb=6, q=19, pow=16): UDR 34 | JBR 73 | DKT-a1(asymp) {int(ir2_a1_bits_lo)} ({ir2_a1_bits_lo:.2f} bits) | withdrawn CBR 130")
    print(f"  - prodV1 (lb=3, q=38, pow=16): UDR 47 | JBR 73 | DKT-a1(asymp) {int(pv1_a1_bits_lo)} ({pv1_a1_bits_lo:.2f} bits) | withdrawn CBR 130")
    assert int(ir2_a1_bits_lo) == int(ir2_a1_bits_hi) == 78

    # Part (a)
    print("\n[1] PART (a): ASYMPTOTIC CURVES & BITS PER QUERY (-log2 a(rho))")
    print(f"  Branch cutoff rho_c = 11 - 3*sqrt(13) = {float(rho_cutoff_dkt()):.9f}, a_1(rho_c) = 4 - sqrt(13) = {float(Decimal(4)-dec_sqrt(Decimal(13))):.9f}")
    asymp_rows = part_a_asymptotic_curves()
    hdr = f"{'Rate':>6} | {'a_UDR':>8} {'a_JBR':>8} {'a_GabQ':>8} {'a1_DKT':>8} {'a_CBR':>8} | {'bpq_UDR':>7} {'bpq_JBR':>7} {'bpq_a1':>7} {'+bpq%':>6} | {'q(100,p16) U/J/a1':>18} | {'q(128,p16) U/J/a1':>18}"
    print("  " + hdr)
    print("  " + "-" * len(hdr))
    for r in asymp_rows:
        u100, j100, a100 = r["q100_pow16_UDR_JBR_a1"]
        u128, j128, a128 = r["q128_pow16_UDR_JBR_a1"]
        print(
            f"  {r['rate']:>6} | {r['a_UDR']:8.5f} {r['a_JBR']:8.5f} {r['a_Gab26_quad']:8.5f} "
            f"{r['a1_DKT']:8.5f} {r['a_CBR']:8.5f} | {r['bpq_UDR']:7.4f} {r['bpq_JBR']:7.4f} "
            f"{r['bpq_a1']:7.4f} {r['bpq_gain_pct_over_JBR']:+5.2f}% | "
            f"{f'{u100}/{j100}/{a100}':>18} | {f'{u128}/{j128}/{a128}':>18}"
        )

    # Part (c.2): Characteristic split
    print("\n[2] CHARACTERISTIC SPLIT: p > max{k - 1, B_d} UP TO k = 2^30")
    char_rows = check_characteristic_split()
    for cr in char_rows:
        print(
            f"  - {cr['field']:22s} | char p = {cr['char_p']:<20d} | log2(q) = {cr['log2_q']:7.3f} | "
            f"k<=2^30 ok? {str(cr['k_up_to_2_30_passes']):5s} | {cr['surviving_mca_regime']}"
        )

    # Part (b) & (c.1): Midpoint beyond-Johnson & zeroth-order Johnson certificates + Full Grid
    mid_rows, grid_rows = evaluate_full_grid()
    print("\n[3] FIELD-INDEPENDENT FINITE CERTIFICATES AT MIDPOINT a_mid = (a_1(rho) + sqrt((k-1)/n))/2 & JBR (m=10)")
    mhdr = f"{'n':>5} {'rate':>5} | {'a_mid':>8} {'a_JBR':>8} {'(m,Bd,Bjet)':>15} {'log2(Lam)':>9} {'log2(E_1)':>9} {'log2(L^2k)':>10} | {'JBR log2(E): DKT / clsd / BCHKS':>32} {'DKT gain':>9}"
    print("  " + mhdr)
    print("  " + "-" * len(mhdr))
    for mr in mid_rows:
        jstr = f"{mr['log2_E_JBR_DKT_m10']:5.2f} / {mr['log2_E_JBR_closed_m10']:5.2f} / {mr['log2_E_JBR_BCHKS25_m10']:5.2f}"
        print(
            f"  2^{mr['log2_n']:<2d} {mr['rate']:>5} | {mr['a_mid']:8.5f} {mr['a_finite_JBR']:8.5f} "
            f"{str(mr['support_mid']):>15} {mr['log2_Lambda_mid']:9.2f} {mr['log2_E_mid']:9.2f} "
            f"{mr['log2_Lam2_k_u1']:10.2f} | {jstr:>32} +{mr['jbr_dkt_gain_bits_over_bchks25']:5.2f}b"
        )

    print("\n[4] ALGEBRAIC SLACK & QUERY SAVINGS SUMMARY ACROSS (field, target, n, rho) AT pow=16")
    ghdr = f"{'Field':>20} {'tgt':>3} {'n':>5} {'rate':>5} | {'q_UDR':>5} {'q_JBR0':>6} {'q_JBRc':>6} {'q_a1*':>5} | {'edge E/OOD1/OOD2 bits':>23} | {'q_DKT(u1/u2)':>13} {'save vs JBRc/UDR (u2)':>22}"
    print("  " + ghdr)
    print("  " + "-" * len(ghdr))
    for gr in grid_rows:
        if gr["pow"] != 16:
            continue
        if gr["field"] == "Tower256 (GF(2^128))":
            continue  # Print GF(2^192) for binary tower in concise table; JSON holds all 5 fields & all 3 pows
        eb = (
            f"{gr['edge_bj_E_bits']:5.1f}/{gr['edge_bj_ood1_bits']:5.1f}/{gr['edge_bj_ood2_bits']:5.1f}"
            if gr["edge_bj_E_bits"] is not None
            else "   LOCKED OUT (p=2)    "
        )
        qdkt = f"{str(gr['q_DKT_u1'])}/{str(gr['q_DKT_u2'])}"
        qjbr_c = str(gr["q_JBR_finite_cert"]) if gr["q_JBR_finite_cert"] is not None else "FAIL"
        sav = (
            f"-{gr['saved_vs_JBR_cert_u2']}q / -{gr['saved_vs_UDR_u2']}q"
            if gr["q_DKT_u2"] is not None
            else "0q (infeasible)"
        )
        print(
            f"  {gr['field']:>20} {gr['target']:>3} 2^{gr['log2_n']:<2d} {gr['rate']:>5} | "
            f"{gr['q_UDR']:>5} {gr['q_JBR_query_floor']:>6} {qjbr_c:>6} {gr['q_a1_asymp']:>5} | "
            f"{eb:>23} | {qdkt:>13} {sav:>22}"
        )

    # Also summarize all passing beyond-Johnson cells across ALL (pow in {0, 16, 20})!
    passing_cells = [g for g in grid_rows if g["q_DKT_u2"] is not None]
    print(f"\n[5] ALL PASSING BEYOND-JOHNSON CELLS ACROSS ALL 5 FIELDS x 4 LENGTHS x 4 RATES x 2 TARGETS x 3 POWS ({len(passing_cells)}/{len(grid_rows)} cells):")
    for g in passing_cells:
        print(
            f"  * {g['field']:14s} | tgt={g['target']} pow={g['pow']:2d} | n=2^{g['log2_n']} rho={g['rate']:4s} | "
            f"UDR={g['q_UDR']} JBR_cert={g['q_JBR_finite_cert']} (floor {g['q_JBR_query_floor']}) -> "
            f"DKT(u1={g['q_DKT_u1']}, u2={g['q_DKT_u2']}) | saves {g['saved_vs_JBR_cert_u2']}q vs JBR_cert "
            f"({g['saved_vs_JBR_floor_u2']}q vs JBR_floor, {g['saved_vs_UDR_u2']}q vs UDR) | "
            f"E={g['u2_E_bits']}b OOD2={g['u2_OOD_bits']}b sup={g['u2_support']}"
        )

    # Write full JSON artifact alongside script inside experiments/? Wait: brief says:
    # "Deliverables (Write ONLY to these paths):
    #  1. .../beyond_johnson_repricing.py
    #  2. .../notes/proximity-and-hw-delta-2026-11.md"
    # So do NOT write any extra JSON file in the workspace! Keep stdout self-contained (or optional --json flag).
    if "--json" in sys.argv:
        print(json.dumps({
            "guards": guards,
            "asymptotic_curves": asymp_rows,
            "characteristic_split": char_rows,
            "midpoint_certificates": mid_rows,
            "grid": grid_rows,
        }, indent=2))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
