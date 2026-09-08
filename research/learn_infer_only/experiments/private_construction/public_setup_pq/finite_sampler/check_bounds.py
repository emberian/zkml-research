#!/usr/bin/env python3
"""Deterministic rational inequalities and resource counts; no random sampler."""
from fractions import Fraction as F
from hashlib import sha256
from math import factorial
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
PUBLIC = HERE.parent
SPEC_HASH = '2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def ceil_frac(x):
    return -((-x.numerator) // x.denominator)


assert digest(HERE / 'SPEC.md') == SPEC_HASH
ring_path = PUBLIC / 'ring_candidate/hardness/GRID.json'
scalar_path = PUBLIC / 'alternatives/hardness/REBUILT.json'
ring = next(p for p in json.loads(ring_path.read_text())['points']
            if p['label'] == 'ring_joint_repair_16384')
scalar = next(p for p in json.loads(scalar_path.read_text())['rows'] if p['n'] == 16384)
assert ring['N'] == scalar['n'] == 16384
assert ring['w_ring_samples'] == 64 and scalar['l'] == 262144
assert ring['sigma_K_width_pow2'] == 25 and scalar['sigma_K_width'] == 2**32
assert ring['sigma_e_width_pow2'] == 10 and scalar['sigma_e_width'] == 2**10

# Public Machin rational certificate. No candidate exponent or Gaussian output is evaluated.
intervals = {}
for c in [5, 239]:
    lower = sum((F((-1)**j, (2*j+1)*c**(2*j+1)) for j in range(80)), F(0))
    error = F(1, 161*c**161)
    intervals[c] = (lower, lower+error)
pi_lower = 16*intervals[5][0] - 4*intervals[239][1]
pi_upper = 16*intervals[5][1] - 4*intervals[239][0]
assert F(3) < pi_lower < pi_upper < F(4)
assert pi_upper - pi_lower < F(1, 2**360)
Q = 2**320
pL = (pi_lower*Q).numerator // (pi_lower*Q).denominator
pU = ceil_frac(pi_upper*Q)
assert pU - pL <= 3
assert factorial(81) > Q
assert sum((F(7,10)**j / factorial(j) for j in range(5)), F(0)) > 2

term_width = F(0)
widths = []
for j in range(1,81):
    term_width = (term_width+4)/j+2
    assert term_width <= 8
    widths.append(str(term_width))
final_width = 641
for step in range(8):
    final_width = 2*final_width+2
assert final_width < 2**19

delta = F(1, 2**256)
tail = 3*delta
rounded = F(16)*2*delta/(1-tail)
assert rounded < 64*delta
acceptance_lower = (1-tail)/16-2*delta
assert acceptance_lower > F(1,17)
assert 17**16 > 2*16**16
assert F(16,17)**4096 < delta
nu = 68*delta
assert nu < F(1, 2**249)

workloads = []
gaussian_ledger = uniform_ledger = 0
for label, dimension, key_exp, public_coefficients, secret_coefficients, q, flood_exp in [
    ('ring_repair', ring['N']*64, 25, (64+561)*ring['N'], ring['N'], int(ring['q']), 247),
    ('scalar_repair', scalar['l'], 32, (scalar['l']+561)*scalar['n'], scalar['n'], int(scalar['q_selected']), 248),
]:
    d, r, T = 577, 16, 384
    actual_keys = r*dimension
    errors = T*dimension
    proof_keys = d*dimension
    actual = actual_keys+errors
    proof = proof_keys+errors
    coefficient = 2*actual+4*T*proof
    gaussian_ledger += coefficient
    actual_uniform = public_coefficients+T*secret_coefficients+T*d
    # Charge each reduction for the same entire uniform workload, despite no need
    # to resample its externally supplied challenge matrix.
    uniform_coefficient = (2+4*T)*actual_uniform
    uniform_ledger += uniform_coefficient
    key_word, error_word = key_exp+4+256, 10+4+256
    expected_bits = 17*(actual_keys*key_word+errors*error_word)
    capped_bits = 4096*(actual_keys*key_word+errors*error_word)
    assert F(coefficient)*nu < F(1,2**192)
    workloads.append({
        'label': label, 'coefficients_per_row_or_error_vector': dimension,
        'key_sigma_pow2': key_exp, 'error_sigma_pow2': 10,
        'actual_key_draws': actual_keys, 'actual_encryption_error_draws': errors,
        'actual_Gaussian_draws': actual, 'proof_only_full_row_draws': proof_keys,
        'one_reduction_Gaussian_allowance': proof,
        'Gaussian_loss_coefficient_2Qactual_plus_4TQred': coefficient,
        'actual_uniform_output_count': actual_uniform,
        'conservative_uniform_loss_coefficient': uniform_coefficient,
        'reference_expected_proposal_upper': 17*actual,
        'reference_worst_proposal_cap': 4096*actual,
        'reference_expected_integer_product_upper': 179*17*actual,
        'reference_worst_integer_product_upper': 179*4096*actual,
        'reference_expected_random_bit_upper': expected_bits,
        'reference_expected_bit_equivalent_bytes_upper': (expected_bits+7)//8,
        'reference_worst_random_bit_upper': capped_bits,
        'reference_worst_bit_equivalent_bytes_upper': (capped_bits+7)//8,
        'threshold_table_error_bytes': (16*2**10-1)*32,
        'threshold_table_key_bytes': (16*2**key_exp-1)*32,
        'table_zero_entry': 'The known k=0 index is interpreted as full acceptance; its 2^256 threshold is implicit.',
        'q_bits': q.bit_length(), 'flood_uniform_proposal_bits': (2*2**flood_exp).bit_length(),
    })
assert gaussian_ledger < 2**41
assert uniform_ledger < 2**45
gaussian_loss = gaussian_ledger*nu
uniform_loss = F(uniform_ledger, 2**512)
assert gaussian_loss < F(1, 2**208)
assert uniform_loss < F(1, 2**467)
assert gaussian_loss+uniform_loss < F(1, 2**207)
assert gaussian_loss+uniform_loss < F(1, 2**192)

input_paths = [
    ring_path, scalar_path,
    PUBLIC / 'ring_candidate/hardness/MANIFEST.json',
    PUBLIC / 'ring_candidate/hardness/MODEL_AND_GRID.md',
    PUBLIC / 'alternatives/hardness/MANIFEST.json',
    PUBLIC / 'alternatives/hardness/AUDIT.md',
    PUBLIC / 'ring_candidate/CANDIDATE.md',
    PUBLIC / 'alternatives/SMUDGED_FIXED_COORDINATE.md',
]
sources = {
    'scope': 'Exact repaired parameter artifacts and primary algorithm orientation',
    'public_input_files': [{'path': str(path), 'sha256': digest(path)} for path in input_paths],
    'web_sources': [
        {'url': 'https://arxiv.org/html/1303.6257',
         'seen': 'Karney 1303.6257v2, section4 AlgorithmD and rational standard-deviation condition; not a frozen strict-cap implementation'},
        {'url': 'https://falcon-sign.info/impl/sign.c.html',
         'seen': 'Reference source comments1090-1092 (1.8205,72-bit half-Gaussian),1348-1353 (standard-deviation range1..2), BerExp finite-precision source; no runtime'},
    ],
    'queries': [
        'Karney "Sampling exactly from the normal distribution" discrete normal algorithm D (domain arxiv.org)',
        'Falcon reference sampler Gaussian sampler.c official (domain falcon-sign.info)',
    ],
    'meter': {'web_search_queries': 2, 'web_page_open_calls': 3,
              'distinct_opened_pages': 2, 'in_page_find_calls': 2,
              'scry_sql_calls': 0, 'scry_schema_calls': 0, 'pdf_downloads': 0},
    'scope_limit': 'Two targeted primary leads only; no absence claim or inherited practical sampler/security guarantee',
}
(HERE / 'SOURCES.json').write_text(json.dumps(sources, indent=2)+'\n')
result = {
    'scope': 'Deterministic public rational/integer inequalities only; no sampler implementation or random/crypto/estimator execution',
    'status': 'PASS', 'frozen_spec_sha256': SPEC_HASH,
    'pi_certificate': {'method': 'Exact Machin80 rational sums followed by one outward fixed-point rounding',
                       'P': 320, 'lower_scaled_integer': str(pL), 'upper_scaled_integer': str(pU),
                       'scaled_width': pU-pL, 'exact_rational_width_below_2_minus_360': True},
    'factorial_81_gt_2_pow320': True,
    'term_width_bound': 8, 'post_8_squaring_width_grid_units': final_width,
    'rounding_TV_upper': '64*2^-256', 'cutoff_TV_upper': '3*2^-256',
    'cap_TV_upper': '2^-256', 'per_Gaussian_TV_upper': '68*2^-256',
    'workloads': workloads,
    'combined_Gaussian_loss_coefficient': gaussian_ledger,
    'combined_uniform_loss_coefficient': uniform_ledger,
    'combined_Gaussian_loss_bound': '<2^-208', 'combined_uniform_loss_bound': '<2^-467',
    'combined_independent_bit_sampling_loss_bound': '<2^-207',
    'declared_budget_met': '<2^-192',
    'CSPRNG_substitution': 'No statistical claim; requires separately charged computational PRG assumption',
}
(HERE / 'RESULTS.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
