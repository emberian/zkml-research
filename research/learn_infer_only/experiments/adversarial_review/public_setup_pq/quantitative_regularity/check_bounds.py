#!/usr/bin/env python3
"""Exact public integer bounds and additive-group counts only.

No keys, ciphertexts, Gaussian draws, cryptographic library or private inputs.
"""

from collections import Counter
from fractions import Fraction
from functools import reduce
import hashlib
from itertools import product
import json
from math import gcd, isqrt
from pathlib import Path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ceil_log2(value):
    assert value > 0
    return (value - 1).bit_length()


def is_prime(value):
    if value < 2:
        return False
    return all(value % div for div in range(2, isqrt(value) + 1))


def dyadic(numerator, exponent):
    value = Fraction(numerator, 1 << exponent)
    return {
        'numerator_over_2_pow_kappa': numerator,
        'kappa': exponent,
        'reduced_numerator': value.numerator,
        'reduced_denominator': value.denominator,
    }


def group_count_controls():
    cases = 0
    vectors = 0
    for p in (2, 3):
        for k in (1, 2, 3):
            q = p ** k
            for n in (2, 3):
                observed = Counter()
                for vector in product(range(q), repeat=n):
                    order = q // reduce(gcd, vector, q)
                    observed[order] += 1
                    vectors += 1
                expected = {1: 1}
                expected.update({p ** i: p ** (i*n) - p ** ((i-1)*n) for i in range(1, k+1)})
                assert dict(observed) == expected
                assert sum(expected.values()) == q ** n
                cases += 1
    return {'parameter_cases': cases, 'public_vectors_counted': vectors, 'result': 'PASS'}


def certificate(profile, columns, kappa):
    p, k, M = profile['p'], profile['k'], profile['M']
    assert is_prime(p) and k >= 1 and M >= columns >= 2
    q = p ** k
    sigma_sq = 1 << (2 * profile['sigma1_pow2'])
    matrix_required = columns * ceil_log2(q) + kappa + 1
    width_sq_required = ceil_log2(M) + kappa + 2
    checks = {
        'prime_power_hypotheses': True,
        'matrix_rows_sufficient': M >= matrix_required,
        'gaussian_width_sufficient': sigma_sq >= width_sq_required,
    }
    assert all(checks.values())
    return {
        'columns': columns,
        'q_bits': ceil_log2(q),
        'matrix_rows': M,
        'matrix_rows_required': matrix_required,
        'matrix_row_margin': M - matrix_required,
        'sigma_squared_representation': f"2^{2 * profile['sigma1_pow2']}",
        'sigma_squared_required': width_sq_required,
        'checks': checks,
    }


def main():
    root = Path(__file__).resolve().parent
    inputs = json.loads((root / 'INPUTS.json').read_text())
    kappa = inputs['kappa']
    profiles = []
    for profile in inputs['profiles']:
        n, d, r, T = (profile[field] for field in ('n', 'd', 'r', 'T'))
        setup = certificate(profile, n, kappa)
        augmented = certificate(profile, n + 1, kappa)
        coalition_bounds = []
        for j in (0, r):
            setup_num = 4 * (d-r)
            mask_num = 4 * (d-j)
            whole_num = 2 * setup_num + 2*T*mask_num
            assert Fraction(whole_num, 1 << kappa) < Fraction(1, 1 << 139)
            coalition_bounds.append({
                'coalition_size': j,
                'setup_joint_bound': dyadic(setup_num, kappa),
                'augmented_joint_bound': dyadic(mask_num, kappa),
                'regularity_terms_in_acceptance_gap': dyadic(whole_num, kappa),
                'regularity_terms_below_2_minus_139': True,
            })
        profiles.append({
            'label': profile['label'],
            'n': n,
            'classification': 'Regularity arithmetic only; no computational security certification',
            'setup_certificate': setup,
            'augmented_certificate': augmented,
            'coalition_bounds': coalition_bounds,
        })
    result = {
        'scope': 'Exact public integer bound checks and p-adic additive-group counting only',
        'result': 'PASS',
        'input_sha256': sha256(root / 'INPUTS.json'),
        'script_sha256': sha256(Path(__file__)),
        'additive_group_controls': group_count_controls(),
        'profiles': profiles,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
