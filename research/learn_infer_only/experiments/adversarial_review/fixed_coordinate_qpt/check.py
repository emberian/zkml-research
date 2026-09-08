#!/usr/bin/env python3
"""Public probability/linear-algebra controls; no cryptographic implementation."""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
PINS = {
    'research/learn_infer_only/experiments/adversarial_review/public_setup_pq/FIXED_COORDINATE_QPT.md': '4c43bce409495edf9c9d5b8e4ada0581af5be0ecf6ff949fbd99fdbfd3da62fe',
    'research/learn_infer_only/experiments/private_construction/public_setup_pq/notes/AUDIT.md': '2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007',
    '/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf': 'a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0',
    str(BASE / 'extracts/2015-608.txt'): 'a1170661edc061a9b011367d43b9b75ed6dfc073cfd0aa477459c20f14d1ecdd',
}


def multiply(row, matrix, p):
    return tuple(sum(row[i] * matrix[i][j] for i in range(len(row))) % p
                 for j in range(len(matrix[0])))


def stat_distance(counter, uniform_domain_size, sample_count):
    return sum(abs(Fraction(count, sample_count) - Fraction(1, uniform_domain_size))
               for count in counter.values()) / 2 + Fraction(
                   uniform_domain_size - len(counter), 2 * uniform_domain_size)


def probability_control(p):
    """A finite uniform-row analogue, not the Gaussian regularity theorem."""
    vectors = list(product(range(p), repeat=2))
    one, two, matrices, shifted = Fraction(0), Fraction(0), 0, 0
    for entries in product(range(p), repeat=4):
        matrix = (entries[:2], entries[2:])
        distribution = Counter(multiply(row, matrix, p) for row in vectors)
        sd = stat_distance(distribution, p**2, p**2)
        double = Counter({(a, b): ca * cb for a, ca in distribution.items()
                          for b, cb in distribution.items()})
        sd2 = stat_distance(double, p**4, p**4)
        assert sd2 <= 2 * sd
        # Revealing an independent row and its deterministic products keeps
        # the original output: its total variation distance is unchanged.
        exposed = Counter({(a, row, multiply(row, matrix, p)): count
                           for a, count in distribution.items() for row in vectors})
        # The comparison has support {(uniform_a,row,row*matrix)} only.
        exposed_sd = sum(abs(Fraction(exposed.get((a, row, multiply(row, matrix, p)), 0), p**4)
                             - Fraction(1, p**4)) for a in vectors for row in vectors) / 2
        assert exposed_sd == sd
        for shift in vectors:
            translated = Counter({tuple((a[i] + shift[i]) % p for i in range(2)): count
                                  for a, count in distribution.items()})
            assert stat_distance(translated, p**2, p**2) == sd
            shifted += 1
        one += sd; two += sd2; matrices += 1
    one /= matrices; two /= matrices
    zero_seed_distance = Fraction(p**2 - 1, p**2)
    assert zero_seed_distance > one and two <= 2 * one
    return {'modulus': p, 'matrices': matrices, 'translation_checks': shifted,
            'joint_one_row_SD': str(one), 'joint_two_rows_SD': str(two),
            'conditioned_zero_matrix_SD': str(zero_seed_distance),
            'independent_exposed_row_preserves_SD': True}


def nonvacuity():
    basis = ((1, 0, 1), (0, 1, 1), (0, 0, 1))
    h = (-1, -1, 1)
    tested, restricted = 0, 0
    # Column-vector convention B*x.
    apply = lambda x, p: tuple(sum(a*b for a, b in zip(row, x)) % p for row in basis)
    for p in [2, 3, 5]:
        assert apply(h, p) == (0, 0, 1)
        for x in product(range(p), repeat=3):
            other = tuple((x[i] + h[i]) % p for i in range(3))
            a, b = apply(x, p), apply(other, p)
            assert a[:2] == b[:2] and a[2] != b[2] and x != other
            assert ((a[0]-a[2]) % p, (a[1]-a[2]) % p, a[2]) == x
            tested += 1
        image = [apply((x, y, 0), p)[:2] for x, y in product(range(p), repeat=2)]
        assert len(set(image)) == len(image)
        restricted += len(image)
    return {'whole_coalition_equal_output_distinct_state_pairs': tested,
            'injective_restricted_image_control_points': restricted}


def parameters():
    """Exact arithmetic on an explicit asymptotic family, without sampling."""
    rows = []
    for k in [16, 32, 64]:
        n, C, p = 2**k, 128, 2
        q, M = n**30, C*n*k
        m, s1, s2, xi = 2*M, n**2, n**8, n**10
        # All logarithms in these controls use base 2. Ceilings are computed
        # exactly and only strengthen the source lower bounds.
        ceil_log = lambda x: (x-1).bit_length()
        ratios = {
            'sigma1_squared_over_M_n_ceillogM': Fraction(s1*s1, M*n*ceil_log(M)),
            'M_over_n_ceillog_sigma1n': Fraction(M, n*ceil_log(s1*n)),
            'sigma2_squared_over_n5_M_sigma1fourth_ceillogcubed': Fraction(s2*s2, n**5*M*s1**4*ceil_log(M*s1)**3),
            'xi_squared_over_n_M_sigma2_squared': Fraction(xi*xi, n*M*s2*s2),
            'sigma1_squared_over_nplus1_ceillogM': Fraction(s1*s1, n+1+ceil_log(M)),
            'betaq_squared_over_n': Fraction(n**10, 4*n),
            'inverse_alpha_over_correctness_sufficient_RHS': Fraction(n**15, 2*p*n**2*k*(1+s2*m*k+m)),
        }
        assert q == p**(30*k) and M >= 2*(n+1)*(30*k)
        assert all(ratio > 1 for ratio in ratios.values())
        rows.append({'log2_n': k, 'C': C, 'augmented_width_passes': True,
                     'unit_constant_only_ratios': {key: str(value) for key, value in ratios.items()}})
    return {'scope': 'Ratios for explicit unit-constant controls; unknown source constants and hardness are not certified',
            'rows': rows}


def main():
    for name, expected in PINS.items():
        path = ROOT / name
        assert '.private' not in path.parts
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
    result = {'claim_kind': 'EXECUTED', 'source_pins': PINS,
              'finite_probability_controls': [probability_control(p) for p in [2, 3]],
              'nonvacuity': nonvacuity(), 'parameter_controls': parameters(),
              'scope': 'Public mathematical controls only; no Gaussian sampling, key generation, ciphertexts, crypto/runtime imports, private data or attack experiment',
              'network_queries': 0}
    (BASE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ['finite_probability_controls', 'nonvacuity']}, indent=2))
    print('Parameter unit-constant controls passed for log2(n)=16,32,64; not concrete security points.')


if __name__ == '__main__':
    main()
