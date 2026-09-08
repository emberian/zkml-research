#!/usr/bin/env python3
"""Public arithmetic and local source hashes only; zero estimator calls."""
from fractions import Fraction
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
RING = HERE.parent
EXPERIMENTS = RING.parents[2]
SCALAR = RING.parent / 'alternatives/hardness'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def packed(count, bits):
    return (count * bits + 7) // 8


source_manifest = json.loads((SCALAR / 'MANIFEST.json').read_text())
for item in source_manifest['source_files']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
cert_path = RING / 'searches/prime_certificate.json'
cert = json.loads(cert_path.read_text())
q = int(cert['q'])
assert q == 4294967767 * 2**256 + 1
assert pow(3, (q - 1) // 2, q) == q - 1
assert 2**256 + 1 > isqrt(q)
p, d, r, window, inputs, w = 28439893, 577, 16, 32, 384, 64
assert all(p % a for a in range(2, isqrt(p) + 1))
x = (p - 1) // 2
denominator = d * x
scale = q // denominator
delta = Fraction(1, 2**192)
points = []
for label, n, key_bits, flood_bits in [
    ('ring_baseline_4096', 4096, 24, 244),
    ('ring_joint_repair_16384', 16384, 25, 247),
]:
    dim, sigma_key, sigma_error = n * w, 2**key_bits, 2**10
    b_key, b_error, flood = 8 * sigma_key, 8 * sigma_error, 2**flood_bits
    root = pow(3, (q - 1) // (2 * n), q)
    assert (q - 1) % (2 * n) == 0
    assert pow(root, n, q) == q - 1 and pow(root, 2 * n, q) == 1
    log_upper = 192 + (dim - 1).bit_length() + 2
    assert sigma_key**64 >= (n * log_upper)**32 * q**3
    assert q**122 >= n**64
    regularity = []
    for k in (1, 2):
        short_exponent = n * 3 * (3 - k) // 64
        assert n * 3 * (3 - k) % 64 == 0
        short = Fraction(2**n, q**short_exponent)
        rank = n * sum((Fraction(1, q**(w-i)) for i in range(k)), Fraction(0))
        assert rank + short < delta
        regularity.append({'k': k, 'short_bound': f'2^{n}/q^{short_exponent}',
                           'rank_plus_short_below_2_minus_192': True,
                           'joint_h_rows': '(2h+1)*2^-192 for h>=1'})
    shift = dim * b_key * b_error
    tau_key = Fraction(3 * d * dim * sigma_key, 2**256)
    tau_error = Fraction(3 * dim * sigma_error, 2**256)
    smudge = Fraction(d * shift, 2 * flood + 1) + tau_key + tau_error
    assert denominator >= 2 * window * x + 1
    assert scale > 2 * window * (flood + shift)
    for coalition in range(r + 1):
        setup = (2 * (d-r) + 1) * delta
        mask = (2 * (d-coalition) + 1) * delta
        assert 2 * setup + 2 * inputs * (smudge + mask) < Fraction(1, 2**168)
    correctness_bits = 203 if n == 4096 else 200
    assert tau_key + inputs * tau_error < Fraction(1, 2**correctness_bits)
    unit_failure_upper = Fraction(n, q)
    unit_failure_bits = 276 if n == 4096 else 274
    assert unit_failure_upper < Fraction(1, 2**unit_failure_bits)
    key_coefficient_bits = key_bits + 4
    points.append({
        'label': label, 'N': n, 'w_ring_samples': w,
        'q': str(q), 'q_bits': q.bit_length(),
        'primitive_2N_root': str(root), 'sigma_e_width_pow2': 10,
        'sigma_K_width_pow2': key_bits, 'flood_radius_pow2': flood_bits,
        'BK_pow2': key_bits+3, 'BE_pow2': 13, 'shift_bound_pow2': shift.bit_length()-1,
        'theta': '3/64', 'smoothing_log_upper': log_upper,
        'regularity': regularity, 'all_17_coalitions_privacy_statistical_bound': '<2^-168',
        'correctness_failure_bound': f'<2^-{correctness_bits}',
        'unit_failure_upper': f'N/q < 2^-{unit_failure_bits}',
        'raw_scalar_proxy': {'n': n, 'm': dim, 'secret': 'UniformMod(q)'},
        'normalized_scalar_proxy': {'n': n, 'm': dim-n,
                                    'secret_and_error': 'DiscreteGaussianAlpha(QQ(1024)/q,q)'},
        'costs': {
            'ciphertext_coefficients': dim+d,
            'ciphertext_bytes': packed(dim+d, q.bit_length()),
            'public_A_and_P_bytes': packed((w+d)*n, q.bit_length()),
            'recipient_key_bits_per_coefficient_strict_tail': key_coefficient_bits,
            'one_recipient_key_bytes_strict_tail': packed(dim, key_coefficient_bits),
            'all_recipient_keys_bytes_strict_tail': r*packed(dim, key_coefficient_bits),
            'fresh_encode_full_ring_products': w,
            'fresh_encode_scalar_coefficient_multiplications': d*n,
            'fresh_encode_gaussian_coefficients': dim,
            'read_coefficient_multiplications': dim,
            'add_or_expire_residue_operations': dim+d,
        },
    })

result = {
    'scope': '[EXECUTED] Public integer/Fraction arithmetic and source provenance; zero estimator calls',
    'status': 'PASS', 'shared': {'d': d, 'r': r, 'W': window, 'T': inputs, 'p': p,
                              'X': x, 'encoding_denominator': denominator},
    'points': points,
    'proposed_calls': {'points': 2, 'paths': ['usvp', 'bdd', 'dual'],
        'models': ['MATZOV_classical', 'ADPS16_classical',
                   'ADPS16_quantum_core_svp', 'MATZOV_quantum_depth_width'],
        'count': 24, 'max_seconds_per_call': 45, 'all_paths_receive_explicit_normalized_input': True},
    'estimator_archive_commit': source_manifest['estimator_commit'],
    'source_hashes_checked': len(source_manifest['source_files']),
    'source_manifest_path': str(SCALAR / 'MANIFEST.json'),
    'source_manifest_sha256': digest(SCALAR / 'MANIFEST.json'),
    'prime_certificate_path': str(cert_path), 'prime_certificate_sha256': digest(cert_path),
    'frozen_ring_sources': {name: digest(RING/name) for name in
        ['CANDIDATE.md', 'RING_REGULARITY.md', 'PARAMETERS.md', 'MANIFEST.json']},
    'calls_executed_this_lane': 0,
    'new_network_meter': {'web_search_queries': 0, 'scry_sql_calls': 0, 'pdf_downloads': 0},
}
(HERE / 'GRID.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
