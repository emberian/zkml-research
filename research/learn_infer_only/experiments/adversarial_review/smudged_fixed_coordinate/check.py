"""Independent public integer/distribution controls. No crypto or sampling.

Reads the frozen public author artifacts; never imports or runs their code.
The finite controls exercise identities, not the cryptographic theorem.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/public_setup_pq/alternatives'
EXPECTED = {
    'SMUDGED_FIXED_COORDINATE.md': 'a7f98b9f17b0e9b37537ca763697f7a9235df498364df4e0dd774f293d9b9327',
    'AUDIT.md': '593faaffcd84f2bade468d9e570a3e2dd3d11eafc76b46ec71b046d22d884307',
    'results.json': '75d69f3c18d502a2761a9b4acab3924c0d18bbd38ca16375ee98dab3b63aae54',
    'MANIFEST.json': '0bf70a6a12442a02f3fced956a456722985d8279ee651e299a501fdff3741654',
}


def read_public(path):
    path = Path(path).resolve()
    forbidden = {'.private', 'private', 'runtime', 'signer_route', 'verified_route'}
    assert not forbidden.intersection(path.parts), str(path)
    allowed = (ROOT, Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror'))
    assert any(path.is_relative_to(base) for base in allowed), str(path)
    return path.read_bytes()


def pin(path):
    data = read_public(path)
    return {'path': str(Path(path).resolve()), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}


subject_pins = []
for name, expected in EXPECTED.items():
    record = pin(AUTHOR / name)
    assert record['sha256'] == expected
    subject_pins.append(record)
manifest = json.loads(read_public(AUTHOR / 'MANIFEST.json'))
linked_pins = []
for section in ['source_pdfs', 'reused_frozen_public_inputs', 'owned_artifacts']:
    for expected in manifest[section]:
        actual = pin(expected['path'])
        assert actual == expected, (section, expected['path'])
        linked_pins.append(actual)
assert read_public(AUTHOR / 'results.json') == read_public(AUTHOR / 'public_arithmetic.stdout.json')

# Exact overlap of two equal-length integer intervals.
scalar_cases = 0
for radius in range(1, 9):
    base = set(range(-radius, radius + 1))
    size = len(base)
    for shift in range(-20, 21):
        moved = {x + shift for x in base}
        exact = F(len(base ^ moved), 2 * size)
        claimed = min(F(1), F(abs(shift), size))
        assert exact == claimed
        scalar_cases += 1
cube_cases = 0
for radius in range(1, 4):
    base = set(product(range(-radius, radius + 1), repeat=2))
    side = 2 * radius + 1
    for shifts in product(range(-5, 6), repeat=2):
        moved = {tuple(x + s for x, s in zip(point, shifts)) for point in base}
        exact = F(len(base ^ moved), 2 * len(base))
        overlap = 1
        for s in shifts:
            overlap *= max(0, side - abs(s))
        assert exact == 1 - F(overlap, side**2)
        assert exact <= min(F(1), sum((F(abs(s), side) for s in shifts), F()))
        cube_cases += 1

# Cyclic decoding grid, independent of any encryption construction.
def circular_distance(a, b, modulus):
    d = (a - b) % modulus
    return min(d, modulus - d)


grid_cases = 0
decoded_points = 0
for q in [17, 31, 67, 97, 127]:
    for denominator in range(3, min(21, q)):
        delta = q // denominator
        for radius in range(1, (denominator - 1) // 2 + 1):
            assert denominator >= 2 * radius + 1
            points = [(delta * z) % q for z in range(-radius, radius + 1)]
            gaps = [b - a for a, b in zip(sorted(points), sorted(points)[1:])]
            gaps.append(q + min(points) - max(points))
            assert min(gaps) >= delta
            for error_bound in range((delta - 1) // 2 + 1):
                assert delta > 2 * error_bound
                for z in range(-radius, radius + 1):
                    for noise in range(-error_bound, error_bound + 1):
                        received = (delta * z + noise) % q
                        distances = {v: circular_distance(received, delta * v, q)
                                     for v in range(-radius, radius + 1)}
                        best = min(distances.values())
                        assert [v for v, dist in distances.items() if dist == best] == [z]
                        decoded_points += 1
                grid_cases += 1
# Printed source's broader [-D,D] interval needs an additional range argument.
source_endpoint = {'q': 97, 'D': 10, 'delta': 9, 'received': 8,
                   'distinct_integers': [-10, 1], 'errors': [1, -1]}
assert all((9 * z + error) % 97 == 8 for z, error in zip([-10, 1], [1, -1]))
assert 4 * 1 <= 9

# Public parameter arithmetic: dyadic upper bounds avoid enormous Gaussian sums.
d, r, n, height, p, W, T = 577, 16, 1024, 16384, 28439893, 32, 384
assert all(p % k for k in range(2, isqrt(p) + 1))
X = (p - 1) // 2
D = d * X
qlo, qhi = 1 << 288, 1 << 289
BK, BL, flood = 1 << 35, 1 << 13, 1 << 244
delta_lo = qlo // D
phase = flood + height * BK * BL
assert D >= 2 * W * X + 1 and delta_lo > 2 * W * phase
# For every q>qlo: Delta<=q/D, so this sufficient centered-phase inequality
# handles Delta's dependence on q (testing just Delta_lo would not suffice).
assert F(2 * W * X, D) + F(2 * W * phase, qlo) < 1
assert height * BK * BL == 1 << 62
eps0 = F(1, 1 << 192)
assert (height - 1).bit_length() + 194 < 4 * 64  # etaZ<8 using 4 ln2<pi
regularity = {}
for columns in [n, n + 1]:
    exponent = 289 * columns - 29 * height
    sup_S = F(1, 1 << (-exponent))
    sup_R = eps0 + (1 + eps0) * sup_S
    # Prime q>2^288 and negative exponent, with q-1>1.
    sup_rank = F(1, 1 << (288 * (height - columns)))
    assert sup_R < F(1, 1 << 191)
    assert sup_rank < F(1, 1 << 192)
    for hidden_rows in [1, d-r, d]:
        assert sup_rank + 2 * hidden_rows * sup_R < F(hidden_rows, 1 << 189)
    regularity[str(columns)] = {'S_exponent_upper': exponent,
                                'rank_exponent_upper': -288 * (height-columns)}
reg_num = 2 * (d-r) + 2*T*d
reg_bound = F(reg_num, 1 << 189)
smudge_num = 2*T*d
smudge_bound = F(smudge_num, 1 << 183)
tail_K = F(3*d*height, 1 << 224)
tail_e = F(3*height, 1 << 246)
assert reg_bound < F(1, 1 << 170)
assert smudge_bound < F(1, 1 << 164)
assert tail_K < F(1, 1 << 199) and tail_e < F(1, 1 << 230)
assert 2*T*tail_K < F(1, 1 << 189) and 2*T*tail_e < F(1, 1 << 220)
total_stat = reg_bound + smudge_bound + 2*T*(tail_K+tail_e)
assert total_stat < F(1, 1 << 163)
# A separate correctness union pays the key event once and T error vectors.
correctness_failure = tail_K + T*tail_e
assert correctness_failure < F(1, 1 << 198)
assert (2*BK - 2).bit_length() == 36  # strict interval has 2*BK-1 possibilities
assert (2*BK).bit_length() == 37      # inclusive interval has 2*BK+1 possibilities


def packed(count, width):
    return (count*width + 7)//8


expected_derived = {
    'n': n, 'l': height, 'q_prime_interval_exponents': [288, 289],
    'q_bit_upper': 289, 'sigma_K_exponent': 32, 'sigma_LWE_exponent': 10,
    'flood_exponent': 244, 'key_tail_cut': 8, 'error_tail_cut': 8,
    'BK': BK, 'BL': BL, 'delta_lower': delta_lo,
    'individual_phase_error_bound': phase, 'correctness_2WE_less_delta': True,
    'regularity_S_exponent_upper': {k: v['S_exponent_upper'] for k,v in regularity.items()},
    'regularity_total_numerator_over_2pow189': reg_num,
    'smudge_total_numerator': smudge_num, 'smudge_total_denominator_power': 183,
    'statistical_total_less_2pow_minus163': True, 'LWE_advantage_multiplier': 2*T,
    'ciphertext_entries': height+d, 'public_key_entries': (height+d)*n,
    'ciphertext_byte_upper': packed(height+d, 289),
    'public_key_byte_upper': packed((height+d)*n, 289),
    'recipient_key_high_probability_bytes': packed(height, 36),
    'all_recipient_keys_high_probability_bytes': packed(r*height, 36),
    'encryption_modular_products': (height+d)*n,
    'decryption_modular_products_per_coordinate': height,
    'scalar_add_residue_additions': height+d,
    'live_66_ciphertexts_byte_upper': 66*packed(height+d, 289),
    'T384_ciphertexts_byte_upper': T*packed(height+d, 289),
}
author_results = json.loads(read_public(AUTHOR / 'results.json'))
assert expected_derived == author_results['derived']
assert author_results['fixture'] == {'d': d, 'r': r, 'window': W, 'issued_inputs': T,
    'p': p, 'centered_coordinate_bound': X, 'window_centered_sum_bound': W*X,
    'scale_denominator': D}
profiles = []
for s in [16, 32, 155]:
    lam = s*s
    nn, ll, lp, bits = 11*lam, lam**2, lam**2-2*lam, 7*s+1
    profiles.append({'sqrt_lambda': s, 'lambda': lam, 'n': nn, 'l': ll, 'l_prime': lp,
        'theorem3_required_l_prime_lower': 2*nn*(bits-1), 'q_bit_upper': bits,
        'theorem3_required_l_prime_upper': 2*nn*bits,
        'theorem3_sufficient_check': lp >= 2*nn*bits,
        'single_block_ciphertext_byte_upper': packed(ll+d, bits),
        'single_block_public_key_byte_upper': packed((ll+d)*nn, bits),
        'single_block_encrypt_products': (ll+d)*nn})
assert profiles == author_results['source_table_mechanical_profiles_not_security_parameters']
naive128_lp = 128**2 - 2*128
naive128_rhs_lower = 2*(11*128)*(7*isqrt(128))
assert naive128_lp < naive128_rhs_lower

# Nonzero ambient witness from the exact public policy matrix. These are plain
# finite-field vectors, not keys, ciphertexts, or learner-encoder-image claims.
rows_path = ROOT / 'research/learn_infer_only/experiments/private_construction/designated_span/crypto/rows.json'
Y = json.loads(read_public(rows_path))
assert len(Y) == r and all(len(row) == d for row in Y)
augmented = [[value % p for value in row[:r]] + [(-row[r]) % p] for row in Y]
for col in range(r):
    pivot = next(idx for idx in range(col, r) if augmented[idx][col])
    augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
    inverse = pow(augmented[col][col], -1, p)
    augmented[col] = [(v*inverse) % p for v in augmented[col]]
    for idx in range(r):
        if idx != col:
            coefficient = augmented[idx][col]
            augmented[idx] = [(a-coefficient*b) % p for a,b in zip(augmented[idx], augmented[col])]
h = [row[-1] for row in augmented] + [1] + [0]*(d-r-1)
assert any(h) and all(sum(a*b for a,b in zip(row, h)) % p == 0 for row in Y)

# Check the subjects again after all pure arithmetic and record only public data.
assert all(pin(AUTHOR / name)['sha256'] == value for name,value in EXPECTED.items())
output = {
    'status': 'PASS',
    'scope': 'Independent exact public arithmetic; no keys, ciphertexts, Gaussian/flood samples, crypto or estimator execution.',
    'subject_pins': subject_pins, 'author_linked_pins_verified': len(linked_pins),
    'linked_pins_by_section': {name: len(manifest[name]) for name in ['source_pdfs', 'reused_frozen_public_inputs', 'owned_artifacts']},
    'interval_TV_cases': scalar_cases, 'product_interval_TV_cases': cube_cases,
    'decoder_grid_cases': grid_cases, 'decoded_integer_points': decoded_points,
    'source_generic_endpoint_control': source_endpoint,
    'regularity_exponents': regularity,
    'regularity_total_numerator_over_2pow189': reg_num,
    'smudge_total_numerator_over_2pow183': smudge_num,
    'statistical_total_less_2pow_minus163': True,
    'correctness_all_T_upper_less_2pow_minus198': True,
    'author_derived_fields_matched': len(expected_derived),
    'author_source_table_fields_matched': sum(len(v) for v in profiles),
    'naive_source_lambda128': {'l_prime': naive128_lp, 'required_lower_bound': naive128_rhs_lower, 'fails_height': True},
    'ambient_kernel_witness': {'p': p, 'nonzero_first_17_coordinates': h[:17],
                               'remaining_coordinates_zero': d-17,
                               'all_16_policy_products_zero': True,
                               'semantic_encoder_image_claim': False},
    'searches': {'remote': 0, 'local_PDF_downloads': 0, 'new_source_discovery': 0},
    'author_files_unchanged_after_check': True,
}
text = json.dumps(output, indent=2) + '\n'
(HERE / 'results.json').write_text(text)
print(text, end='')
