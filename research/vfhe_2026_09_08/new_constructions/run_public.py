"""One reproducible, public arithmetic experiment; no cryptographic launch."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import statistics
import sys
import time

from fused_ring_matvec import (P, Plan, duplicate_baseline, evaluate, evaluate_poly,
                               preprocess, prime_by_trial_division, schoolbook)

HERE = Path(__file__).resolve().parent


def encode(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest(value):
    return hashlib.sha256(encode(value)).hexdigest()


def fixture(r, m, k, n):
    # Nonconstant, deterministic public vectors; no sampling or seed selection.
    A = [[[(17 * (i + 1) + 31 * (j + 1) + (t + 1) ** 3 + 19 * j * t) % P
           for t in range(n)] for j in range(m)] for i in range(r)]
    C = [[[(29 * (j + 1) + 11 * (c + 1) + (t + 2) ** 2 + 23 * c * t + P // 3) % P
           for t in range(n)] for c in range(k)] for j in range(m)]
    return A, C


def relation_checks(A, C, Y, Q):
    r, m, k, n = len(A), len(C), len(C[0]), len(A[0][0])
    checks = 0
    for alpha in (0, 1, 2, 7, P - 1):
        ae = [[evaluate_poly(a, alpha) for a in row] for row in A]
        ce = [[evaluate_poly(c, alpha) for c in row] for row in C]
        for i in range(r):
            for c in range(k):
                lhs = sum(ae[i][j] * ce[j][c] for j in range(m)) % P
                rhs = (evaluate_poly(Y[i][c], alpha) + (pow(alpha, n, P) + 1) * evaluate_poly(Q[i][c], alpha)) % P
                assert lhs == rhs
                checks += 1
    return checks


def plan_description(cache):
    return [{'n': p.n, 'negacyclic': p.negacyclic, 'modulus': p.p, 'omega': p.omega,
             'psi': p.psi, 'input_coefficients': 'ascending', 'output_frequencies': 'natural',
             'normalization': 'inverse only', 'bit_reversal_sha256': digest(p.reverse)} for p in cache.plans]


assert prime_by_trial_division(P)
controls = []
for n in (1, 2, 4, 8):
    for a_degree in range(n):
        for b_degree in range(n):
            a, b = [0] * n, [0] * n
            a[a_degree] = b[b_degree] = 1
            A, C = [[a]], [[b]]
            expected = schoolbook(A, C)
            long = evaluate(preprocess(A, 'long'), C)
            split = evaluate(preprocess(A, 'split'), C)
            assert (long[0], long[1]) == (split[0], split[1]) == expected
            controls.append({'n': n, 'a_degree': a_degree, 'b_degree': b_degree, 'Y': split[0], 'Q': split[1]})

small_fixtures = []
for n in (8, 16, 32, 64):
    A, C = fixture(3, 4, 2, n)
    expected = schoolbook(A, C)
    baseline = duplicate_baseline(A, C)
    long = evaluate(preprocess(A, 'long'), C)
    split = evaluate(preprocess(A, 'split'), C)
    assert (baseline[0], baseline[1]) == (long[0], long[1]) == (split[0], split[1]) == expected
    small_fixtures.append({'n': n, 'shape': [3, 4, 2], 'A': A, 'C': C, 'Y': split[0], 'Q': split[1],
                           'exact_schoolbook_match': True, 'polynomial_evaluation_checks': relation_checks(A, C, *expected)})

benchmark = []
for n, repeats in ((64, 3), (256, 3), (1024, 3), (4096, 1)):
    A, C = fixture(3, 4, 2, n)
    records = {}
    answers = {}
    for mode in ('duplicate', 'long', 'split'):
        setup_start = time.perf_counter_ns()
        cache = preprocess(A, mode) if mode != 'duplicate' else None
        baseline_plans = (Plan(n, True), Plan(2 * n, True)) if mode == 'duplicate' else None
        preprocessing_ns = time.perf_counter_ns() - setup_start
        times = []
        for _ in range(repeats):
            start = time.perf_counter_ns()
            result = evaluate(cache, C) if cache else duplicate_baseline(A, C, plans=baseline_plans)
            times.append(time.perf_counter_ns() - start)
        answers[mode] = result[:2]
        records[mode] = {'online_ns': times, 'online_median_ns': statistics.median(times),
                         'preprocessing_ns': preprocessing_ns,
                         'online_counts': result[2], 'preprocessing_counts': cache.preprocessing_counts if cache else {},
                         'plans': plan_description(cache) if cache else [],
                         'cached_matrix_field_elements': 3 * 4 * 2 * n if cache else 0}
    assert answers['duplicate'] == answers['long'] == answers['split']
    evaluation_count = relation_checks(A, C, *answers['split'])
    assert records['duplicate']['online_counts'][f'forward_{2 * n}'] == 48
    assert records['duplicate']['online_counts'][f'inverse_{2 * n}'] == 24
    assert records['duplicate']['online_counts'][f'forward_{n}'] == 48
    assert records['duplicate']['online_counts'][f'inverse_{n}'] == 24
    assert records['long']['online_counts'][f'forward_{2 * n}'] == 8
    assert records['long']['online_counts'][f'inverse_{2 * n}'] == 6
    assert records['split']['online_counts'][f'forward_{n}'] == 16
    assert records['split']['online_counts'][f'inverse_{n}'] == 12
    benchmark.append({'n': n, 'rows': 3, 'inner': 4, 'components': 2, 'repeats': repeats,
                      'input_sha256': digest({'A': A, 'C': C}), 'output_Y_Q_sha256': digest(answers['split']),
                      'all_three_algorithms_equal': True, 'polynomial_evaluation_checks': evaluation_count,
                      'implementations': records})

# Direct NTT evaluation pins actual domains on a positive nonconstant vector.
domain_checks = []
for n in (1, 2, 8, 32):
    values = [(i + 2) ** 2 % P for i in range(n)]
    for negative in (False, True):
        plan = Plan(n, negative)
        transformed = plan.transform(values)
        points = [plan.psi * pow(plan.omega, j, P) % P for j in range(n)]
        assert transformed == [evaluate_poly(values, z) for z in points]
        assert plan.transform(transformed, True) == values
        domain_checks.append({'n': n, 'negacyclic': negative, 'omega': plan.omega, 'psi': plan.psi,
                              'direct_evaluation_match': True, 'inverse_match': True})

result = {'status': 'PASS', 'environment': {'python': sys.version, 'platform': platform.platform(),
          'processor': platform.processor()}, 'prime': P, 'prime_verified_by_trial_division': True,
          'controls': {'monomial_pairs': len(controls), 'schoolbook_matvec_shapes': len(small_fixtures),
                       'direct_domain_checks': len(domain_checks)},
          'benchmark': benchmark,
          'scope': 'Public arithmetic prototype; duplicate is our model of source call pattern, not measured Rust/FHE/PCS',
          'timing_caveat': 'Unoptimized Python, fixed order, short local samples; all plans created before online timers. Public matrix spectra cached only by long/split. Compare operation counts first.'}
(HERE / 'positive_fixtures.json').write_text(json.dumps({'monomials': controls, 'small_matvec': small_fixtures,
                                                       'domain_checks': domain_checks}, indent=2) + '\n')
(HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'monomial_pairs': len(controls), 'schoolbook_matvec_shapes': len(small_fixtures),
                  'direct_domain_checks': len(domain_checks),
                  'timings_ms': [{'n': row['n'], **{mode: round(rec['online_median_ns'] / 1e6, 3)
                     for mode, rec in row['implementations'].items()}} for row in benchmark]}, indent=2))
