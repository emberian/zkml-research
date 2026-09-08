"""Independent public-source, saved-output and exact-arithmetic review.

No author-code import, Sage/estimator invocation, Gaussian draw, or protocol.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
import math
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_candidate/hardness'
RING = AUTHOR.parent
EST = ROOT / 'research/learn_infer_only/experiments/he_closure_costs/estimator'
SNAP = EST / 'runtime/pinned-estimator'
COMMIT = '53da5982597709ba0fdf94ea37a84d822310fd84'
EXPECTED = {
    'MANIFEST.json': '2f90bee88437465514066d879eddbc3918ab1af6d0c8d6592e63b0750adeef53',
    'AUDIT.md': '84e3180ba5f6409dea7e590bbdd40c449a58a1d325efc773ef63ea11d35951ae',
    'MODEL_AND_GRID.md': 'a3b0e6db5cc15d52fb1eee75ae580045391d7d73dd1ee6ac36797486d7eef7c8',
}
frozen = {}


def read_public(path):
    path = Path(path).resolve()
    assert path.is_relative_to(ROOT)
    assert not {'.private', 'private', 'signer_route', 'verified_route'}.intersection(path.parts)
    if 'runtime' in path.parts:
        assert path.is_relative_to(SNAP) or path == EST / 'runtime/estimator-src.tar'
    data = path.read_bytes()
    entry = {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}
    if str(path) in frozen:
        assert frozen[str(path)] == entry
    frozen[str(path)] = entry
    return data


def digest(path):
    return sha256(read_public(path)).hexdigest()


def load(path):
    return json.loads(read_public(path))


for name, value in EXPECTED.items():
    assert digest(AUTHOR / name) == value
manifest = load(AUTHOR / 'MANIFEST.json')
grid = load(AUTHOR / 'GRID.json')
run = load(AUTHOR / 'estimates.manifest.json')
summary = load(AUTHOR / 'SUMMARY.json')
seal = load(AUTHOR / 'SEAL.json')
for name, expected in manifest['artifacts'].items():
    assert digest(AUTHOR / name) == expected
assert seal['manifest_sha256'] == EXPECTED['MANIFEST.json']
assert seal['audit_sha256'] == EXPECTED['AUDIT.md']
assert seal['mapping_sha256'] == EXPECTED['MODEL_AND_GRID.md']
assert seal['summary_sha256'] == digest(AUTHOR / 'SUMMARY.json')
assert seal['entries_validated'] == 24 and seal['source_hashes_unchanged'] == 27
for name, expected in grid['frozen_ring_sources'].items():
    assert manifest['frozen_ring_sources'][name] == expected
    assert digest(RING / name) == expected
assert digest(Path(grid['source_manifest_path'])) == grid['source_manifest_sha256']
scalar_manifest = load(Path(grid['source_manifest_path']))
assert scalar_manifest['source_files'] == manifest['source_files'] == run['source_files']
for entry in run['source_files']:
    assert digest(entry['path']) == entry['sha256']
    assert len(read_public(entry['path'])) == entry['bytes']
assert len(run['source_files']) == 27
assert run['estimator_archive_commit'] == grid['estimator_archive_commit'] == COMMIT
provenance = load(EST / 'environment-final-provenance.json')
archive_path = EST / 'runtime/estimator-src.tar'
assert digest(archive_path) == provenance['estimator_archive_sha256']
with tarfile.open(archive_path) as archive:
    assert archive.pax_headers['comment'] == COMMIT
    for entry in run['source_files']:
        relative = Path(entry['path']).relative_to(SNAP)
        assert archive.extractfile(str(relative)).read() == read_public(entry['path'])
# The earlier independent proof review is evidence of its own scoped result,
# not substituted for this review's mapping or finite arithmetic.
proof_review = HERE.parent / 'ring_fixed_coordinate'
proof_manifest = load(proof_review / 'manifest.json')
proof_report = next(e for e in proof_manifest['files'] if e['path'] == 'REPORT.md')
assert digest(proof_review / 'REPORT.md') == proof_report['sha256']

assert run['source_path'] == str(SNAP) and run['sage_version'] == '10.8'
assert run['primal_shape_model'] == 'gsa' and run['per_entry_seconds_limit'] == 45
for field, name in [('predeclared_grid_sha256', 'GRID.json'),
                    ('predeclared_mapping_sha256', 'MODEL_AND_GRID.md'),
                    ('driver_sha256', 'run_estimates.py'),
                    ('output_sha256', 'estimates.jsonl')]:
    assert run[field] == digest(AUTHOR / name)
models = ['MATZOV_classical', 'ADPS16_classical',
          'ADPS16_quantum_core_svp', 'MATZOV_quantum_depth_width']
paths = ['usvp', 'bdd', 'dual']
assert run['models'] == grid['proposed_calls']['models'] == models
assert run['paths'] == grid['proposed_calls']['paths'] == paths
rows = [json.loads(s) for s in read_public(AUTHOR / 'estimates.jsonl').decode().splitlines()]
assert run['planned_entries'] == run['attempts_completed'] == run['estimator_entries'] == len(rows) == 24
assert [r['attempt'] for r in rows] == list(range(1, 25))
assert Counter(r['status'] for r in rows) == {'EXECUTED': 24}
expected_order = list(product([p['label'] for p in grid['points']], models, paths))
assert [(r['point'], r['model'], r['path']) for r in rows] == expected_order
log = read_public(AUTHOR / 'estimates.log').decode().splitlines()
assert len(log) == 49 and log[-1] == 'FINISHED 24 24'
assert read_public(AUTHOR / 'estimates.stderr.log') == b''
log_fields_checked = 0
for row in rows:
    n = row['N_secret']
    assert row['estimator_entered'] is True
    assert row['ring_samples_raw'] == 64 and row['ring_samples_normalized'] == 63
    assert row['scalar_proxy_raw_n'] == row['scalar_proxy_normalized_n'] == n
    assert row['scalar_proxy_raw_m'] == 64*n and row['scalar_proxy_normalized_m'] == 63*n
    assert row['error_width_exact'] == '1024'
    assert math.isclose(float(row['error_stddev_estimator']), 1024/math.sqrt(2*math.pi), rel_tol=0, abs_tol=1e-10)
    assert f"n={n}, q={row['q_exact']}" in row['raw_repr']
    assert f'm={64*n}, tag=None' in row['raw_repr']
    assert f"n={n}, q={row['q_exact']}" in row['normalized_repr']
    assert 'Xs=D(σ=408.52), Xe=D(σ=408.52)' in row['normalized_repr']
    assert f'm={63*n}, tag=None' in row['normalized_repr']
    assert 0 < row['seconds_estimator_not_attack'] < 45
    assert row['fields']['tag'] == row['path']
    for key, value in row['fields'].items():
        if key != 'tag':
            assert math.isfinite(float(value)) and float(value) > 0
    for key, value in row['log2_fields'].items():
        assert math.isfinite(value)
        assert math.isclose(math.log2(float(row['fields'][key])), value, abs_tol=1e-10)
        log_fields_checked += 1
    beta, dimension = int(row['fields']['beta']), int(row['fields']['d'])
    assert 40 < beta <= 1024 and beta <= dimension <= 64*n+1
    if 'eta' in row['fields']:
        assert 2 < int(row['fields']['eta']) <= 1024
    if row['path'] == 'usvp':
        assert row['fields']['rop'] == row['fields']['red']
    if row['path'] == 'bdd':
        assert math.isclose(float(row['fields']['rop']),
                            float(row['fields']['red']) + float(row['fields']['svp']), rel_tol=1e-12)
    if row['path'] == 'dual':
        assert 1 <= int(row['fields']['m']) <= 63*n
        assert dimension == int(row['fields']['m']) + n
        assert row['fields']['repetitions'] == '1'
    if row['model'].startswith('ADPS16') and row['path'] != 'dual':
        slope = .292 if row['model'] == 'ADPS16_classical' else .265
        assert math.isclose(row['log2_fields']['red'], slope*beta, abs_tol=1e-10)
    j = row['attempt'] - 1
    assert log[2*j] == f"START {j+1} {row['point']} {row['model']} {row['path']}"
    assert log[2*j+1] == f"RESULT {j+1} EXECUTED {row['log2_fields']} {beta}"

minima = []
for point, advertised in zip(grid['points'], summary['points']):
    assert advertised['point'] == point['label']
    assert advertised['joint_finite_parameters_and_costs'] == point
    selected = {}
    for model in models:
        choices = [r for r in rows if r['point'] == point['label'] and r['model'] == model]
        winner = min(choices, key=lambda r: r['log2_fields']['rop'])
        rebuilt = {'log2_modeled_cost': winner['log2_fields']['rop'], 'path': winner['path'],
                   'beta': int(winner['fields']['beta']), 'lattice_dimension': int(winner['fields']['d'])}
        assert advertised['minima'][model] == rebuilt
        assert next(r for r in choices if r['path'] == 'dual')['log2_fields']['rop'] > rebuilt['log2_modeled_cost']
        selected[model] = rebuilt
    minima.append({'point': point['label'], 'minima': selected})
assert summary['attempts'] == summary['entries'] == 24
assert summary['errors'] == summary['timeouts'] == summary['infinity_outputs'] == 0
assert summary['block_size_range'] == [60, 632]
assert summary['total_estimator_calculation_seconds_not_attack_time'] == sum(r['seconds_estimator_not_attack'] for r in rows)

cert_path = Path(grid['prime_certificate_path'])
assert digest(cert_path) == grid['prime_certificate_sha256']
cert = load(cert_path)
q = int(cert['q'])
assert q == 4294967767 * 2**256 + 1 and 4294967767 % 2 == 1
assert pow(3, (q-1)//2, q) == q-1 and pow(3, q-1, q) == 1
assert (2**256+1)**2 > q and 2**288 < q < 2**289
assert Q(1, 2**279) < Q(1024, q) < Q(1, 2**278)
p, d, recipients, window, inputs, w = 28439893, 577, 16, 32, 384, 64
assert all(p % k for k in range(2, math.isqrt(p)+1))
x, denominator = (p-1)//2, d*((p-1)//2)
assert grid['shared'] == {'d': d, 'r': recipients, 'W': window, 'T': inputs,
                          'p': p, 'X': x, 'encoding_denominator': denominator}
scale, delta = q//denominator, Q(1, 2**192)
finite = []
fields_checked = 0
for point, (n, key_bits, flood_bits) in zip(grid['points'], [(4096, 24, 244), (16384, 25, 247)]):
    assert point['N'] == n and point['q'] == str(q) and point['w_ring_samples'] == w
    dimension, sigma, error, flood = n*w, 2**key_bits, 1024, 2**flood_bits
    bk, be = 8*sigma, 8*error
    root = pow(3, (q-1)//(2*n), q)
    assert (q-1) % (2*n) == 0 and pow(root, n, q) == q-1 and pow(root, 2*n, q) == 1
    assert str(root) == point['primitive_2N_root']
    # These integer-powered checks imply the actual sufficient real inequalities.
    log_upper = 192 + (dimension-1).bit_length() + 2
    assert sigma**64 >= (n*log_upper)**32 * q**3
    assert q**122 >= n**64  # B=q^(61/64)/sqrt(N) >= 1.
    assert n >= 16  # In particular 2B<q since sqrt(N)>=4, q^theta>1.
    assert point['theta'] == '3/64'
    for k, bound in zip((1, 2), point['regularity']):
        theta, gamma = Q(3, 64), 3-k
        assert Q(k, w) < theta < 1 and gamma > 0
        exponent = n*theta*gamma
        assert exponent.denominator == 1
        short = Q(2**n, q**exponent.numerator)
        rank = n*sum((Q(1, q**(w-i)) for i in range(k)), Q(0))
        assert rank+short < delta
        assert bound['short_bound'] == f'2^{n}/q^{exponent.numerator}'
        assert bound['rank_plus_short_below_2_minus_192'] is True
    c = dimension*bk*be
    tau_key = Q(3*d*dimension*sigma, 2**256)
    tau_error = Q(3*dimension*error, 2**256)
    smudge = Q(d*c, 2*flood+1) + tau_key + tau_error
    setup = (2*(d-recipients)+1)*delta
    ledgers = []
    for j in range(recipients+1):
        masking = (2*(d-j)+1)*delta
        ledger = 2*setup + 2*inputs*(smudge+masking)
        assert ledger < Q(1, 2**168)
        ledgers.append(ledger)
    correctness = tau_key + inputs*tau_error
    correctness_bits = 203 if n == 4096 else 200
    assert correctness < Q(1, 2**correctness_bits)
    assert point['all_17_coalitions_privacy_statistical_bound'] == '<2^-168'
    assert point['correctness_failure_bound'] == f'<2^-{correctness_bits}'
    assert denominator >= 2*window*x+1 and scale > 2*window*(flood+c)
    # The circular endpoint separation is a distinct necessary decoder check.
    assert q-2*window*x*scale >= scale
    unit_bits = 276 if n == 4096 else 274
    assert Q(n, q) < Q(1, 2**unit_bits)
    assert point['unit_failure_upper'] == f'N/q < 2^-{unit_bits}'
    packed = lambda count, bits: (count*bits+7)//8
    costs = {'ciphertext_coefficients': dimension+d,
             'ciphertext_bytes': packed(dimension+d, 289),
             'public_A_and_P_bytes': packed((w+d)*n, 289),
             'recipient_key_bits_per_coefficient_strict_tail': key_bits+4,
             'one_recipient_key_bytes_strict_tail': packed(dimension, key_bits+4),
             'all_recipient_keys_bytes_strict_tail': recipients*packed(dimension, key_bits+4),
             'fresh_encode_full_ring_products': w,
             'fresh_encode_scalar_coefficient_multiplications': d*n,
             'fresh_encode_gaussian_coefficients': dimension,
             'read_coefficient_multiplications': dimension,
             'add_or_expire_residue_operations': dimension+d}
    assert point['costs'] == costs
    assert point['smoothing_log_upper'] == log_upper and point['shift_bound_pow2'] == c.bit_length()-1
    assert point['sigma_K_width_pow2'] == key_bits and point['flood_radius_pow2'] == flood_bits
    assert point['sigma_e_width_pow2'] == 10 and point['BK_pow2'] == key_bits+3 and point['BE_pow2'] == 13
    assert point['q_bits'] == q.bit_length() == 289
    assert point['raw_scalar_proxy'] == {'n': n, 'm': 64*n, 'secret': 'UniformMod(q)'}
    assert point['normalized_scalar_proxy'] == {'n': n, 'm': 63*n,
        'secret_and_error': 'DiscreteGaussianAlpha(QQ(1024)/q,q)'}
    fields_checked += len(costs) + 12
    finite.append({'N': n, 'root_order': 2*n, 'C_pow2': c.bit_length()-1,
                   'regularity_k_values_pass': [1, 2], 'coalitions_checked': len(ledgers),
                   'max_privacy_statistical_log2_informational': math.log2(max(ledgers).numerator)-math.log2(max(ledgers).denominator),
                   'correctness_log2_informational': math.log2(correctness.numerator)-math.log2(correctness.denominator),
                   'decoder_scale': str(scale), 'decoder_noise_margin': str(scale-2*window*(flood+c)),
                   'extra_message_scale_products_excluded_from_dN': d,
                   'uniform_secret_coefficients': n, 'scalar_flood_draws': d,
                   'costs': costs})

# Exhaustive tiny public ring-map controls, with no random or cryptographic state.
# F5[X]/(X^2+1): CRT roots ±2; 16/25 units and 9/25 nonunits.
elements = list(product(range(5), repeat=2))
mul = lambda a,b: ((a[0]*b[0]-a[1]*b[1])%5, (a[0]*b[1]+a[1]*b[0])%5)
add = lambda a,b: ((a[0]+b[0])%5, (a[1]+b[1])%5)
neg = lambda a: ((-a[0])%5, (-a[1])%5)
one = (1,0)
units = [a for a in elements if ((a[0]+2*a[1])%5)*((a[0]-2*a[1])%5)%5 != 0]
assert len(units) == 16 and Q(25-len(units), 25) == 1-Q(4,5)**2 <= Q(2,5)
affine_permutations = inverse_identities = 0
for a in units:
    inv = next(b for b in elements if mul(a,b) == one)
    assert len({neg(mul(b,inv)) for b in elements}) == 25
    for offset in elements:
        assert len({add(mul(a,t),offset) for t in elements}) == 25
        affine_permutations += 1
        for b in elements:
            b_prime = neg(mul(b,inv))
            assert neg(mul(b_prime,a)) == b
            # Inverse of y' = y + b' v is y = y' - b' v.
            for v in [(0,0),(1,0),(0,1),(4,4)]:
                forward = add(offset, mul(b_prime,v))
                assert add(forward, neg(mul(b_prime,v))) == offset
                inverse_identities += 1

inputs_record = {'scope': 'Named frozen public sources and saved estimator records only; no private state or protocol runtime.',
                 'frozen_public_files': sorted(frozen.values(), key=lambda e: e['path'])}
(HERE / 'INPUTS.json').write_text(json.dumps(inputs_record, indent=2)+'\n')
for entry in list(frozen.values()):
    assert digest(entry['path']) == entry['sha256']
result = {'status': 'PASS', 'scope': 'Pure arithmetic/source and retained estimator-output audit. No Sage, estimator, Gaussian sampling or crypto execution.',
          'author_manifest_sha256': EXPECTED['MANIFEST.json'],
          'frozen_public_files_unchanged': len(frozen), 'estimator_archive_commit': COMMIT,
          'archive_source_files_matching': 27, 'saved_attempts': 24, 'saved_estimator_entries': 24,
          'errors': 0, 'timeouts': 0, 'Infinity_or_nonfinite_fields': 0,
          'saved_log2_fields_recomputed': log_fields_checked, 'minima': minima,
          'joint_parameter_and_cost_fields_compared': fields_checked, 'finite_points': finite,
          'ring_map_controls': {'ring': 'F5[X]/(X^2+1)', 'elements': 25, 'units': 16,
                                'affine_permutations': affine_permutations, 'inverse_identities': inverse_identities},
          'new_estimator_calls': 0, 'new_sage_calls': 0, 'new_crypto_calls': 0,
          'new_web_queries': 0, 'new_scry_queries': 0, 'new_PDF_downloads': 0}
text = json.dumps(result, indent=2)+'\n'
(HERE / 'results.json').write_text(text)
print(text, end='')
