#!/usr/bin/env python3
"""Finite predicate/update audit; no secure encryption implementation.

Checks an ideal threshold interface, KSW's masked-exponent aggregation identity,
and a deliberately insecure equation witness for the proposed GSW bit-encoding
repair helper. Source algorithms are not claimed implemented in full.
"""
import hashlib
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def matmul(a, b):
    return [[dot(row, col) for col in zip(*b)] for row in a]


def transpose_mv(a, s):
    return [dot(col, s) for col in zip(*a)]


def sign_recovery(initial):
    lo, hi = -128, 127
    offset, state = 0, initial
    trace = []
    while lo < hi:
        threshold = (lo + hi + 1) // 2
        next_offset = -threshold
        command = next_offset - offset
        state += command
        offset = next_offset
        assert state == initial - threshold and -255 <= state <= 255
        bit = int(state >= 0)
        trace.append({'learn': command, 'threshold': threshold, 'infer': bit})
        if bit:
            lo = threshold
        else:
            hi = threshold - 1
    assert lo == initial
    return trace


def aggregate_blinders():
    # KSW pairing product exponent: (alpha*f1+beta*f2)*<v,x> mod q.
    q, f1, f2 = 101, 5, 7
    alpha1, beta1, alpha2, beta2 = 1, 3, 2, 4
    sigma1 = (alpha1 * f1 + beta1 * f2) % q
    sigma2 = (alpha2 * f1 + beta2 * f2) % q
    score1, score2 = 1, -1
    product_phase = (sigma1 * score1 + sigma2 * score2) % q
    assert score1 + score2 == 0 and product_phase != 0
    # For two fixed nonzero scores, independent uniform effective masks give
    # cancellation probability 1/q, rather than exact sum-zero correctness.
    identities = sum((a * score1 + b * score2) % q == 0
                     for a in range(q) for b in range(q))
    assert identities == q
    # An alignment helper supplies a base T for this same projection. A bounded
    # magnitude can then be decoded by candidate testing from T and T^score.
    modulus, generator = 607, pow(2, 6, 607)
    assert pow(generator, q, modulus) == 1 and generator != 1
    base = pow(generator, sigma1, modulus)
    count = 0
    for score in range(-20, 21):
        value = pow(base, score, modulus)
        guesses = [candidate for candidate in range(-20, 21)
                   if pow(base, candidate, modulus) == value]
        assert guesses == [score]
        count += 1
    return {'classification': 'EXECUTED toy exponent/group identities, not pairing encryption',
            'q': q, 'scores': [score1, score2], 'clear_sum_zero': True,
            'effective_masks': [sigma1, sigma2], 'aggregate_phase': product_phase,
            'aggregate_zero_test': product_phase == 0,
            'uniform_mask_pairs': q * q, 'zero_pairs': identities,
            'alignment_helper_bounded_projection_decodes': count}


def natural_outer_repair():
    rng = random.Random(2026090602)
    q, n, bits = 257, 2, 9
    m = (n + 1) * bits
    gadget = [[(1 << (j % bits)) if j // bits == i else 0 for j in range(m)]
              for i in range(n + 1)]
    Gbar = gadget[:n]
    B = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    secret = [17, 29]
    error = [-1, 0, 1] * (m // 3)
    beta0 = [(x + e) % q for x, e in zip(transpose_mv(B, secret), error, strict=True)]
    A = B + [beta0]
    attributes = [1, 0, 1, 1, 0, 0]
    inner = []
    for bit in attributes:
        R = [[rng.randrange(2) for _ in range(m)] for _ in range(m)]
        AR = matmul(A, R)
        Psi = [[(a + bit * g) % q for a, g in zip(row, grow, strict=True)]
               for row, grow in zip(AR, gadget, strict=True)]
        inner.append(Psi)
    # Natural helper needed for c_j -> c_j+(psi'_j-psi_j)*Gbar^T*s.
    helper = [x % q for x in transpose_mv(Gbar, secret)]
    recovered_secret = [helper[i * bits] for i in range(n)]
    assert recovered_secret == secret
    # The last gadget block has a q/2-sized coefficient at weight128. Thus
    # (s,-1)*Psi separates zero/one despite the small chosen witness errors.
    selected_column = n * bits + 7
    recovered = []
    phase_values = []
    for Psi in inner:
        phase = (Psi[-1][selected_column]
                 - dot(recovered_secret, [row[selected_column] for row in Psi[:n]])) % q
        centered = phase if phase <= q // 2 else phase - q
        recovered.append(int(abs(centered) > q // 4))
        phase_values.append(centered)
    assert recovered == attributes
    # Show why merely changing a publicly visible inner-ciphertext bit does not
    # update the corresponding outer encoding, and why the helper would fix it.
    Bj = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    W = [[rng.choice([-1, 1]) for _ in range(m)] for _ in range(m)]
    we = transpose_mv(W, error)
    old = [(v + e) % q for v, e in zip(transpose_mv(Bj, secret), we, strict=True)]
    new_matrix = [[b + g for b, g in zip(row, grow, strict=True)]
                  for row, grow in zip(Bj, Gbar, strict=True)]
    required = [(v + e) % q for v, e in zip(transpose_mv(new_matrix, secret), we, strict=True)]
    repaired = [(c + h) % q for c, h in zip(old, helper, strict=True)]
    assert old != required and repaired == required
    return {'classification': 'EXECUTED deliberately insecure GSW/outer-encoding equation witness',
            'q': q, 'n': n, 'gadget_bits': bits, 'm': m,
            'outer_encoding_stale_after_inner_bit_change': old != required,
            'helper_repairs_outer_encoding': repaired == required,
            'helper_exposes_entire_inner_secret': recovered_secret == secret,
            'original_attribute_bits': attributes, 'recovered_attribute_bits': recovered,
            'decryption_centered_phases': phase_values,
            'scope': 'refutes publishing exact Gbar^T*s; no general PE update impossibility'}


def source_record(path, title, access, url):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'title': title, 'access': access, 'url': url}


def main():
    traces = [sign_recovery(s) for s in range(-128, 128)]
    assert {len(t) for t in traces} == {8}
    # Positive control: parity equivalence is a congruence under every addition.
    parity_checks = sum((a + u) % 2 == (b + u) % 2
                        for a in range(16) for b in range(16) if a % 2 == b % 2
                        for u in range(16))
    assert parity_checks == 2048
    before = [int(x >= 0) for x in (1, 2)]
    after = [int(x - 2 >= 0) for x in (1, 2)]
    assert before == [1, 1] and after == [0, 1]
    sources = [
        source_record(MIRROR / '2007/404.pdf', 'KSW predicate-only inner-product PE',
                      'Def2.2 pp3-4; section4.2 full algorithms/correctness pp7-8 read; no full reduction audit',
                      'https://eprint.iacr.org/2007/404'),
        source_record(HERE / 'sources/1302-1192.pdf', 'Homomorphic Encryption with Access Policies',
                      'arXivv2 PDF pp5-8: HPE syntax/game, Eq3.3, aggregation; main XOR-IBE only overview read',
                      'https://arxiv.org/abs/1302.1192v2'),
        source_record(MIRROR / '2016/691.pdf', 'Targeted Homomorphic Attribute Based Encryption',
                      'Def2.1-2.3 pp7-8, single-target construction pp11-13, security statement p15 read; no full reduction audit',
                      'https://eprint.iacr.org/2016/691'),
        source_record(MIRROR / '2015/029.pdf', 'Predicate Encryption for Circuits from LWE',
                      'section1.3 p5 and section4.1 pp21-22 plus weak/full security discussion read; no full reduction audit',
                      'https://eprint.iacr.org/2015/029'),
        source_record(MIRROR / '2025/361.pdf', 'Predicate Encryption from Lattices: Enhanced Compactness and Refined Functionality',
                      'Def2 pp13-14, Lemma2.8 pp10-11, Construction1/Theorem3.1 pp14-16 read; proof not fully audited; constant-payload0 avoids printed Dec-step3 ambiguity',
                      'https://eprint.iacr.org/2025/361'),
    ]
    query_names = ('scry_predicate_homomorphic.json', 'scry_predicate_fhe.json',
                   'scry_predicate_lattices.json', 'scry_predicate_inner_lwe.json')
    queries = []
    for name in query_names:
        path = HERE / 'sources' / name
        record = json.loads(path.read_text())
        queries.append({'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'record_id': record.get('record_id'), 'row_count': record.get('row_count'),
                        'spend_nanodollars': record.get('spend_nanodollars')})
    report = {
        'classification': 'Finite semantic and equation witnesses, no secure PE implementation',
        'ordinary_full_attribute_hiding_translation_counterexample':
            {'states': [1, 2], 'initial_predicates': before, 'update': -2, 'post_predicates': after},
        'sign_interface': {'initial_domain': [-128, 127], 'state_witness_range': [-255, 255],
                           'states_recovered': len(traces), 'inference_calls_per_state': 8,
                           'learn_calls_per_state': 8, 'forks_needed': False,
                           'sample_trace_for_37': traces[37 + 128]},
        'parity_congruence_positive_checks': parity_checks,
        'ksw_aggregation': aggregate_blinders(),
        'gsw_outer_repair': natural_outer_repair(),
        'source_records': sources,
        'search_accounting': {'new_scry_sql_queries': 4, 'new_schema_calls': 0,
                              'cumulative_scry_sql_queries': 7, 'cumulative_schema_calls': 1,
                              'new_web_search_queries': 15, 'cumulative_web_search_queries': 26,
                              'kagi_queries': 0, 'queries': queries,
                              'non_eprint_pdf_downloads': ['https://arxiv.org/pdf/1302.1192v2'],
                              'eprint_pdf_downloads': 0},
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python': sys.version,
    }
    (HERE / 'results/predicate_closure_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('ordinary_full_attribute_hiding_translation_counterexample',
                     'sign_interface', 'parity_congruence_positive_checks', 'ksw_aggregation', 'gsw_outer_repair')}, indent=2))


if __name__ == '__main__':
    main()
