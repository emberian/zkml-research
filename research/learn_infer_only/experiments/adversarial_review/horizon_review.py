#!/usr/bin/env python3
"""Independent finite-channel telescoping and source/provenance controls.

The channel below is deliberately insecure and transparent. It tests the exact
reduction wiring, correlated full packages, and orientations; no encryption or
primitive security advantage is implemented or measured.
"""
from collections import Counter
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
LANE = HERE.parent / 'private_construction'
PDF = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mean(values):
    values = list(values)
    return sum(values, F(0)) / len(values)


def paths(b, h):
    yield ()
    if h:
        for c in range(b):
            for tail in paths(b, h-1):
                yield (c,) + tail


def step(x, c):
    return (x + 1) % 256 if c == 0 else (2*x) % 256


def follow(x, path):
    for c in path:
        x = step(x, c)
    return x


def encrypt(pk, message, nonce):
    # All fields are public: this is intentionally NOT encryption.
    return ('ct', message ^ pk ^ nonce, nonce)


def real_packages(i, horizon):
    futures = [None] if i == horizon else list(real_packages(i+1, horizon))
    for future, pk in itertools.product(futures, (0, 1)):
        # Every current key carries the next public key. The entire correlated
        # future package is retained, not replaced by a separate fresh sample.
        next_pk = None if future is None else future[1]
        count = 1 if i == horizon else 2
        keys = tuple(('real-key', pk, c, next_pk) for c in range(count))
        yield (i, pk, keys, future)


def host(package, ciphertext):
    # Nonlinear public test consumes all ancestor/future keys and ciphertext.
    encoded = repr((package, ciphertext)).encode()
    return hashlib.sha256(encoded).digest()[0] & 1


def simulated_package(i, pk, future, outputs):
    keys = tuple(('sim-key', pk, c, y) for c, y in enumerate(outputs))
    return (i, pk, keys, future)


def ancestor_wrapper(parent, i, left, right, child):
    def wrapped(future, challenge):
        values = []
        for pk, zero_nonce, sibling_nonce in itertools.product((0, 1), repeat=3):
            outputs = []
            for c in range(2):
                candidate = right if c < child else left
                child_ct = challenge if c == child else encrypt(
                    future[1], step(candidate, c), sibling_nonce)
                outputs.append((child_ct, 'ACK'))
            package = simulated_package(i, pk, future, outputs)
            values.append(parent(package, encrypt(pk, 0, zero_nonce)))
        return mean(values)
    return wrapped


def node_test(path):
    test, left, right = host, 0, 1
    for i, child in enumerate(path):
        test = ancestor_wrapper(test, i, left, right, child)
        left, right = step(left, child), step(right, child)
    return test, left, right


def real_probability(i, horizon, message, test):
    return mean(test(package, encrypt(package[1], message, nonce))
                for package in real_packages(i, horizon) for nonce in (0, 1))


def ideal_probability(i, horizon, message, test):
    futures = [None] if i == horizon else list(real_packages(i+1, horizon))
    values = []
    for future, pk, zero_nonce in itertools.product(futures, (0, 1), (0, 1)):
        if future is None:
            vectors = [(message >> 7,)]
        else:
            vectors = [tuple((encrypt(future[1], step(message, c), coins[c]), 'ACK')
                             for c in range(2))
                       for coins in itertools.product((0, 1), repeat=2)]
        for outputs in vectors:
            package = simulated_package(i, pk, future, outputs)
            values.append(test(package, encrypt(pk, 0, zero_nonce)))
    return mean(values)


def finite_channel_control(horizon):
    sides = []
    for path in paths(2, horizon):
        test, left, right = node_test(path)
        for side, message, orientation in [('left', left, 1), ('right', right, -1)]:
            gap = real_probability(len(path), horizon, message, test) - ideal_probability(
                len(path), horizon, message, test)
            sides.append({'path': list(path), 'side': side,
                          'real_minus_ideal': str(gap), 'oriented_gap': str(orientation*gap)})
    root = real_probability(0, horizon, 0, host) - real_probability(0, horizon, 1, host)
    total = sum((F(row['oriented_gap']) for row in sides), F(0))
    assert total == root
    k = len(sides)
    padded = 1 << (k-1).bit_length()
    assert k <= padded < 2*k
    # The extra ranks use the same one-message source game with no key queries
    # and a constant final bit, giving exactly zero Real-minus-Ideal gap.
    padded_gap = mean([F(row['oriented_gap']) for row in sides] + [F(0)]*(padded-k))
    assert padded_gap == root/padded
    uncomplemented = sum((F(row['real_minus_ideal']) for row in sides), F(0))
    return {'horizon': horizon, 'root_gap': str(root), 'sides': sides,
            'uniform_mathematical_gap': str(root/k), 'strict_fair_coin_choices': padded,
            'dummy_choices': padded-k, 'exact_padded_gap': str(padded_gap),
            'sum_without_right_complement': str(uncomplemented),
            'right_complement_is_load_bearing': uncomplemented != root}


def main():
    inputs = [Path(__file__).resolve(), PDF, LANE/'FINITE_LADDER.md',
              LANE/'finite_ladder.py', LANE/'horizon/HORIZON.md',
              LANE/'horizon/audit.py', LANE/'horizon/results.json']
    before = {str(p): digest(p) for p in inputs}
    spec = importlib.util.spec_from_file_location('owner_horizon_audit', LANE/'horizon/audit.py')
    owner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(owner)
    saved = json.loads((LANE/'horizon/results.json').read_text())
    replay = {
        'uniform_hybrid': owner.uniform_hybrid_control(),
        'horizon_accounting': owner.horizon_accounting(),
        'uniformity_controls': owner.uniformity_and_negligibility_controls(),
        'nonvacuity': owner.nonvacuity(),
    }
    assert all(saved[k] == v for k, v in replay.items())
    # Independent labels, not the owner's recursive unranking implementation.
    ranked_cases = 0
    for b in (1, 2, 3, 4):
        for h in range(5):
            expected = {(p, side, sign) for p in paths(b, h)
                        for side, sign in [('left', 1), ('right', -1)]}
            found = {owner.unrank_one_sim(b, h, j) for j in range(len(expected))}
            assert found == expected
            ranked_cases += len(expected)
    # Full exposed auxiliary correlation is indispensable: a uniform hidden
    # pad makes each ciphertext marginal uniform, but exposing that same pad
    # recovers the bit with certainty. Independent resampling loses the joint law.
    marginal = [Counter(k ^ b for k in (0, 1)) for b in (0, 1)]
    joint = [Counter((k, k ^ b) for k in (0, 1)) for b in (0, 1)]
    assert marginal[0] == marginal[1] and joint[0] != joint[1]
    channels = [finite_channel_control(h) for h in range(3)]
    assert any(row['root_gap'] != '0' for row in channels)
    assert all(row['right_complement_is_load_bearing'] for row in channels)
    # Fixed finite fair-coin samplers have dyadic atom probabilities. Uniform
    # 26-choice sampling cannot be exact, while padded32 is exact in five bits.
    assert F(1, 26).denominator & (F(1, 26).denominator-1)
    report = {
        'label': 'EXECUTED exact reduction-wiring controls; deliberately insecure finite channel',
        'command': [sys.executable, str(Path(__file__).resolve())], 'inputs': before,
        'inputs_unchanged': all(before[str(p)] == digest(p) for p in inputs),
        'paper_extraction_command': ['pdftotext', '-layout', str(PDF), str(HERE/'2013_729_review.txt')],
        'full_extract_is_ignored_scratch': True,
        'owner_function_outputs_match_saved': True, 'independent_rank_cases': ranked_cases,
        'finite_channel_wrappers': channels,
        'auxiliary_pad_control': {'ciphertext_marginals_equal': True,
                                  'full_exposed_joint_worlds_distinct': True},
        'strict_sampling_repair': 'M=2^ceil(log2(2N)); dummy one-message, zero-key, constant-output ranks; exact Delta/M',
        'scope': 'No primitive theorem, encrypted execution, measured cryptographic advantage, or full source reduction formalization.'}
    assert report['inputs_unchanged']
    (HERE/'horizon_review.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
