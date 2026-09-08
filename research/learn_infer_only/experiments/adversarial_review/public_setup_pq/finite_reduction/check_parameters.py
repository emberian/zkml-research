#!/usr/bin/env python3
"""Public integer/rational parameter inequalities only; no cryptography or sampling."""
from fractions import Fraction
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def clog2(value):
    assert isinstance(value, int) and value >= 1
    return (value - 1).bit_length()


def csqrt(value):
    root = isqrt(value)
    return root if root * root == value else root + 1


def two_power(exponent):
    return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)


def audit(row, kappa):
    n, d, m_left, m_right = row['n'], row['d'], row['M'], row['L']
    total_m = m_left + m_right
    s1 = 1 << row['sigma1_pow2']
    s2 = 1 << row['sigma2_pow2']
    ln, lm, ll, ls = map(clog2, (n, m_left, m_right, s1))
    q1 = s1 * csqrt(n * lm)
    q2 = 2 * csqrt(30 * n * (ls + ln))
    a_upper = csqrt(m_left) * q1
    b_upper = max((1 + q1 * q2) * csqrt(lm + ll + kappa + 3), csqrt(lm + 4))
    k_upper = (1 + a_upper) * (1 + s2 * q2 * csqrt(m_left * m_right))
    xi_min_pow2 = clog2(2 * k_upper)
    xi_pow2 = row.get('xi_pow2', xi_min_pow2)
    xi = 1 << xi_pow2
    noise_pow2 = row['encryption_error_width_pow2'] - xi_pow2 - 1
    base_width = two_power(noise_pow2)
    q = row['p'] ** row['k']
    checks = {
        'n_at_least_100_and_kappa': n >= max(100, kappa),
        'n_minus_d_at_least_kappa': n - d >= kappa,
        'L_ge_M_gt_n': m_right >= m_left > n,
        'AR_sigma1': s1*s1 >= 81*(kappa+ln+2),
        'AR_strict_M': m_left > 30*n*(ls+ln),
        'Gaussian_image_sigma2': s2 >= a_upper*b_upper,
        'gadget_norm_tail': m_left >= kappa+ll+1,
        'operator_norm_xi': xi >= 2*k_upper,
        'discrete_continuous_smoothing': base_width**2 >= 2*(kappa+clog2(total_m-d)+2),
        'final_discretizer_smoothing': 2*base_width**2*xi**2 >= kappa+clog2(total_m)+2,
        'alpha_between_zero_and_one': (1 << row['encryption_error_width_pow2']) < q,
    }
    regularity = []
    for columns in (n, n+1):
        regularity.append({
            'columns': columns,
            'row_count': m_left >= columns*clog2(q)+kappa+1,
            'width': s1*s1 >= lm+kappa+2,
        })
    # Size ratios only: no model timings or arithmetic-throughput assumptions.
    result = {
        'name': row['name'],
        'origin': row['origin'],
        'n': n, 'd': d, 'source_LWE_secret_dimension': n-d,
        'M': m_left, 'L': m_right, 'm': total_m,
        'q_representation': f"{row['p']}^{row['k']}", 'q_bits': q.bit_length(),
        'sigma1_pow2': row['sigma1_pow2'], 'sigma2_pow2': row['sigma2_pow2'],
        'encryption_error_width_pow2': row['encryption_error_width_pow2'],
        'least_integer_certificate_xi_pow2': xi_min_pow2,
        'used_xi_pow2': xi_pow2,
        'base_LWE_error_width_pow2': noise_pow2,
        'AR_M_strict_floor': 30*n*(ls+ln),
        'least_integer_certificate_sigma2_pow2': clog2(a_upper*b_upper),
        'clog2_Q1': clog2(q1), 'clog2_Q2': clog2(q2), 'clog2_A': clog2(a_upper),
        'checks': checks,
        'finite_distribution_certificate_pass': all(checks.values()),
        'regularity': regularity,
        'sampler_discrepancy_requirement': f'per-world total variation <= 2^-{kappa}',
        'sampler_implementation_status': 'not implemented or certified',
    }
    return result


def main():
    raw = (HERE/'INPUTS.json').read_bytes()
    inputs = json.loads(raw)
    rows = [audit(row, inputs['kappa']) for row in inputs['profiles']]
    expected = inputs['expected_pass']
    assert {row['name']: row['finite_distribution_certificate_pass'] for row in rows} == expected
    assert all(all(r['row_count'] and r['width'] for r in row['regularity']) for row in rows)
    d, r, count = inputs['d'], inputs['r'], inputs['T']
    ledger = {}
    for coalition in (0, r):
        regularity = 8*(d-r) + 8*count*(d-coalition)
        reduction = 68*count
        total = regularity + reduction
        assert total < (1 << 21)
        ledger[str(coalition)] = {
            'regularity_numerator_over_2_pow_kappa': regularity,
            'reduction_numerator_over_2_pow_kappa': reduction,
            'total_numerator_over_2_pow_kappa': total,
            'statistical_bound_if_sampler_requirement_met': f'< 2^-{inputs["kappa"]-21}',
            'LWE_advantage_multiplier': 2*count,
        }
    result = {
        'scope': 'exact public integer and rational inequalities; no key, ciphertext, Gaussian or attack execution',
        'kappa': inputs['kappa'],
        'inputs_sha256': sha256(raw).hexdigest(),
        'profiles': rows,
        'privacy_ledger': ledger,
        'status': 'PASS: expected original/adjusted classifications and all regularity certificates',
    }
    output = json.dumps(result, indent=2)+'\n'
    (HERE/'RESULTS.json').write_text(output)
    print(output)


if __name__ == '__main__':
    main()
