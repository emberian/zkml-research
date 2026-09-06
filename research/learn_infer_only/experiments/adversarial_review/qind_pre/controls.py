#!/usr/bin/env python3
"""Independent premise controls for QIND_pre review, not quantum cryptography."""
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[2]
TARGET = RESEARCH / 'experiments/pq_composition/qind_pre/QIND_PRE_LIFT.md'
PDF = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf')
EXPECTED_TARGET_SHA = '78b5140be6fd2b2cd7d15706eabad4ee2da476b437ef310f1feb77ec5d3dbd66'


def qualified_gap_control():
    grid = [Fraction(i, 4) for i in range(5)]
    count = 0
    for bad, good0, good1, bad0, bad1 in itertools.product(grid, repeat=5):
        qualified = abs((1 - bad) * (good0 - good1))
        total = abs((1 - bad) * good0 + bad * bad0 -
                    ((1 - bad) * good1 + bad * bad1))
        assert total <= qualified + bad
        count += 1
    # If E depends on the challenge bit, using one world's zero bad probability
    # is invalid. The proposed game prevents this by sampling circuits before b.
    challenge_dependent_E_counterexample = {'qualified_gap': 0,
                                            'world0_bad_probability': 0,
                                            'actual_gap': 1}
    assert (challenge_dependent_E_counterexample['actual_gap'] >
            challenge_dependent_E_counterexample['qualified_gap'] +
            challenge_dependent_E_counterexample['world0_bad_probability'])
    return {'exact_rational_cases': count,
            'bound': 'total_gap <= qualified_gap + common_prechallenge_bad_probability',
            'challenge_dependent_event_falsifier': challenge_dependent_E_counterexample}


def add_matrices(a, b):
    return [[x + y for x, y in zip(row_a, row_b, strict=True)]
            for row_a, row_b in zip(a, b, strict=True)]


def scale_matrix(scale, a):
    return [[scale * value for value in row] for row in a]


def inner_matrix_trace(a, b):
    return sum((a[i][j] * b[j][i] for i in range(len(a))
                for j in range(len(a))), Fraction(0))


def bell_projector(sign):
    rho = [[Fraction(0) for _ in range(4)] for _ in range(4)]
    rho[0][0] = rho[3][3] = Fraction(1, 2)
    rho[0][3] = rho[3][0] = Fraction(sign, 2)
    return rho


def joint_quantum_advice_control():
    plus, minus = bell_projector(1), bell_projector(-1)
    assert inner_matrix_trace(plus, plus) == 1
    assert inner_matrix_trace(plus, minus) == 0
    # V0: y0->Phi+, y1->Phi-. V1 swaps these. Both marginal laws agree.
    v0, v1 = (plus, minus), (minus, plus)
    marginal0 = scale_matrix(Fraction(1, 2), add_matrices(*v0))
    marginal1 = scale_matrix(Fraction(1, 2), add_matrices(*v1))
    assert marginal0 == marginal1
    # One Bell-sign measurement, then compare its classical outcome with y.
    accept0 = sum((Fraction(1, 2) * inner_matrix_trace((plus, minus)[y], v0[y])
                   for y in range(2)), Fraction(0))
    accept1 = sum((Fraction(1, 2) * inner_matrix_trace((plus, minus)[y], v1[y])
                   for y in range(2)), Fraction(0))
    assert accept0 == 1 and accept1 == 0
    return {'classification': 'exact 4x4 rational density matrices, no quantum FE implementation',
            'classical_Y_marginals_equal': True, 'quantum_R_marginals_equal': True,
            'joint_accept_probabilities': [str(accept0), str(accept1)],
            'one_copy_measurement_joint_gap': str(accept0 - accept1),
            'lesson': 'separate Y and R marginals cannot replace joint compatibility'}


def delayed_signature_control():
    pair = ('c1_star|c2_star|proof_star', 'valid_signature_star')
    delayed_signed_pairs = set()
    eager_signed_pairs = {pair}
    delayed_forgery = pair not in delayed_signed_pairs
    eager_forgery = pair not in eager_signed_pairs
    assert delayed_forgery and not eager_forgery
    # This is transcript accounting: no signature algorithm is implemented.
    return {'classification': 'symbolic signing-query transcript control only',
            'exact_future_challenge_query_is_allowed_before_release': True,
            'same_query_is_new_pair_with_delayed_signing': delayed_forgery,
            'same_query_is_new_pair_after_eager_signing': eager_forgery,
            'minimal_simulated_key_constants': ['t_star', 'Y_f', 'MPK', 'PKE_secret', 'punctured_PRF_key', 'f'],
            'unreleased_signature_literal_present': False,
            'lesson': 'minimal simulated code and delayed signature justify the zero-query forgery reduction'}


def bad_history_control():
    # Same good substate, arbitrary bad substates of equal trace p: any binary
    # measurement gap is at most p, not necessarily 2p. Orthogonal bad states
    # attain p. Matrix form keeps a genuinely quantum common good component.
    plus, minus = bell_projector(1), bell_projector(-1)
    rows = []
    for p in (Fraction(0), Fraction(1, 8), Fraction(1, 2), Fraction(1)):
        common = scale_matrix(1 - p, plus)
        left = add_matrices(common, scale_matrix(p, plus))
        right = add_matrices(common, scale_matrix(p, minus))
        gap = abs(inner_matrix_trace(plus, left) - inner_matrix_trace(plus, right))
        assert gap == p
        rows.append({'bad_probability': str(p), 'attained_measurement_gap': str(gap)})
    return {'cases': rows, 'no_physical_state_copy_is_performed': True}


def main():
    target_sha = hashlib.sha256(TARGET.read_bytes()).hexdigest()
    assert target_sha == EXPECTED_TARGET_SHA, 'review target changed; rereview required'
    result = {'classification': 'independent finite premise controls, not a cryptographic theorem checker',
              'reviewed_target': {'path': str(TARGET), 'sha256': target_sha},
              'primary_source': {'path': str(PDF), 'sha256': hashlib.sha256(PDF.read_bytes()).hexdigest(),
                                 'access': 'Def2.4 p8; source algorithms/11hybrids pp13-17; AppendixA pp19-24 and AppendixC p25 read'},
              'qualified_QIO': qualified_gap_control(),
              'joint_quantum_advice': joint_quantum_advice_control(),
              'delayed_signature': delayed_signature_control(),
              'bad_history': bad_history_control(),
              'new_queries': {'SQL': 0, 'schema': 0, 'web': 0, 'Kagi': 0},
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'python': sys.version}
    (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
