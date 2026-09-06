#!/usr/bin/env python3
"""Size and admissibility controls for encrypted-output randomized FE.

No FE or PKE implementation is claimed. Finite tables model only the disjoint
message supports supplied by perfectly correct PKE, and an explicit public
random-tape equality test. Fractions are exact; size recurrences are labeled
illustrative models, not instantiated cryptographic costs.
"""
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def fraction_record(value):
    return {'numerator': value.numerator, 'denominator': value.denominator}


def distribution(message, lam, collision_mode=False):
    # Labels stand for disjoint ciphertext supports. The plaintext in the label
    # makes this deliberately insecure, not an encryption prototype. Ignoring
    # coins is a correctness-preserving collision control, not CPA security.
    counts = Counter()
    for r0 in range(1 << lam):
        for r1 in range(1 << lam):
            c0 = (message, 0 if collision_mode else r0)
            c1 = (message, 0 if collision_mode else r1)
            counts[(c0, c1)] += 1
    return {ct: Fraction(count, 1 << (2 * lam)) for ct, count in counts.items()}


def statistical_distance(left, right):
    return sum((abs(left.get(x, 0) - right.get(x, 0))
                for x in left.keys() | right.keys()), Fraction(0)) / 2


def equality_event(dist, target_first_component):
    return sum((prob for ct, prob in dist.items()
                if ct[0] == target_first_component), Fraction(0))


def compatibility_controls():
    rows = []
    for lam in range(1, 7):
        # Two distinct one-bit messages plus lambda random bits fit s=lambda+1.
        # The general inequality below needs only s>0, not s>=lambda.
        s = lam + 1
        left, right = distribution(0, lam), distribution(1, lam)
        event_left = equality_event(left, (0, 0))
        event_right = equality_event(right, (0, 0))
        epsilon = Fraction(1, 1 << (2 * s + lam))
        assert statistical_distance(left, right) == 1
        assert event_left == Fraction(1, 1 << lam) and event_right == 0
        assert event_left - event_right > epsilon
        # If Step merges the private states, their encrypted-output laws agree.
        merged = distribution(0, lam)
        assert statistical_distance(left, merged) == 0
        # Collisions within a correct message support only increase event mass.
        collision_mass = equality_event(distribution(0, lam, True), (0, 0))
        assert collision_mass == 1 and collision_mass >= event_left
        rows.append({'lambda': lam, 's': s, 'coin_pairs_per_message': 1 << (2 * lam),
                     'statistical_distance': 1,
                     'first_component_event_left': fraction_record(event_left),
                     'first_component_event_right': fraction_record(event_right),
                     'theorem_epsilon': fraction_record(epsilon),
                     'gap_over_epsilon': int((event_left - event_right) / epsilon),
                     'same_next_state_distance': 0,
                     'within_message_collision_event': fraction_record(collision_mass)})
    inequalities = 0
    for lam in range(1, 257):
        for s in range(1, 257):
            # Compare exponents exactly, avoiding enormous floating-point tails.
            assert lam < 2 * s + lam
            inequalities += 1
    return {'finite_disjoint_support_tables': rows,
            'general_exponent_inequalities_checked': inequalities,
            'symbolic_claim': '2^(-lambda) > 2^(-2*s-lambda) for every s>0',
            'ordinary_security_attack_claimed': False}


def size_controls():
    # Faithful qualitative model of separate ciphertext copies per output bit.
    # b is illustrative base ciphertext bits; no scheme parameter is inferred.
    b, answer_bits, terminal = 8, 1, 8
    widths = [terminal]
    for _ in range(6):
        widths.append(b * (widths[-1] + answer_bits))
    rejected = 0
    for base in range(2, 17):
        for ct_bits in range(1, 1025):
            assert ct_bits < base * (ct_bits + answer_bits)
            rejected += 1
    # Compact source syntax: Enc consumes fixed-width plaintext, not last CT as
    # plaintext, and does not contain the function or issued function-key code.
    # Numbers below are an illustrative type shape, not bytes/cycles/security.
    compact_ct_bits = 3 * 16
    compact_rounds = [compact_ct_bits for _ in range(7)]
    assert len(set(compact_rounds)) == 1
    return {'classification': 'illustrative exact size/type controls only',
            'per_output_copy_model': {'base_bits': b, 'answer_bits': answer_bits,
                                      'terminal_bits': terminal, 'backward_widths': widths,
                                      'same_format_inequalities_rejected': rejected,
                                      'necessary_condition': 'L >= b*(L+a), impossible for b>1 and L>0'},
            'compact_model': {'ciphertext_widths': compact_rounds,
                              'dependency_dag': ['parameters -> public Enc code',
                                                 '(public Enc code, Step) -> F_cmd',
                                                 '(F_cmd, erased raw master) -> issued key'],
                              'function_to_encryptor_back_edge': False}}


def step(state, command):
    # A continuing private representation with a meaningful visible bit.
    # The hidden coordinate is observationally irrelevant for this interface.
    visible, hidden = state
    if command == 'learn':
        return ((visible + 1) % 4, hidden ^ 1), 'ACK'
    if command == 'infer':
        return state, visible & 1
    raise ValueError(command)


def continuing_interface():
    left, right = (0, 0), (0, 1)
    traces = [[], []]
    states = [[left], [right]]
    for command in ('learn', 'learn', 'infer', 'learn', 'infer'):
        left, out0 = step(left, command)
        right, out1 = step(right, command)
        assert out0 == out1 and left != right
        traces[0].append(out0)
        traces[1].append(out1)
        states[0].append(left)
        states[1].append(right)
    assert step((0, 0), 'infer')[1] != step((1, 0), 'infer')[1]
    # Restore is allowed and returns a different permitted old-state answer.
    restored = step(states[0][0], 'infer')[1]
    current = step(states[0][-1], 'infer')[1]
    assert restored == 0 and current == 1
    # Verify the hidden-coordinate relation is closed over this entire toy.
    checks = 0
    for v in range(4):
        for command in ('learn', 'infer'):
            a, oa = step((v, 0), command)
            b, ob = step((v, 1), command)
            assert a[0] == b[0] and oa == ob
            checks += 1
    return {'classification': 'executed ideal interface, no encrypted state implementation',
            'states': states, 'outward_traces': traces,
            'distinct_next_states_with_equal_all_future_outward_behavior': True,
            'closed_relation_checks': checks,
            'different_visible_states_have_different_permitted_answers': True,
            'restored_answer': restored, 'current_answer': current,
            'privacy_kind': 'behavioral quotient; hidden coordinate has no future authorized influence'}


def source(path, title, access):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'title': title, 'access': access,
            'url': 'https://eprint.iacr.org/' + str(path.relative_to(MIRROR)).removesuffix('.pdf')}


def main():
    sources = [
        source(MIRROR / '2012/733.pdf', 'Reusable Garbled Circuits and Succinct Functional Encryption',
               'Remark3.6 p22, Remark3.7 and section3.1 opening p23 read; product-per-output scope, not a field-wide bound'),
        source(MIRROR / '2013/451.pdf', 'Candidate Indistinguishability Obfuscation and Functional Encryption for all circuits',
               'section6 definitions/game pp22-23 and section6.1 algorithms pp23-24 read; no full reduction or candidate obfuscation audit'),
        source(MIRROR / '2013/729.pdf', 'Functional Encryption for Randomized Functionalities',
               'Def2.1-2.6 pp5-9, Remark2.8 p9, construction pp12-14 and Theorem4.1 p14 read; no full reduction audit'),
        source(MIRROR / '2025/330.pdf', '(Multi-Input) FE for Randomized Functionalities, Revisited',
               'Def3.8 p18 perfect PKE correctness, Def4.1-4.4 pp21-23, Def5.1 p28 footnote, section6.1/Construction2 pp48-49, Theorem6.1 p50; no full reduction or QPT audit'),
    ]
    query_path = HERE / 'sources/scry_rfe_recurrence.json'
    query = json.loads(query_path.read_text())
    report = {'classification': 'exact symbolic/finite controls, no FE/PKE implementation',
              'compatibility': compatibility_controls(), 'sizes': size_controls(),
              'continuing_interface': continuing_interface(), 'sources': sources,
              'search_accounting': {'new_scry_sql_queries': 1, 'new_schema_calls': 0,
                                    'cumulative_scry_sql_queries': 8, 'cumulative_schema_calls': 1,
                                    'new_web_search_queries': 2, 'cumulative_web_search_queries': 28,
                                    'kagi_queries': 0, 'eprint_pdf_downloads': 0,
                                    'query': {'path': str(query_path),
                                              'sha256': hashlib.sha256(query_path.read_bytes()).hexdigest(),
                                              'record_id': query.get('record_id'),
                                              'rows': query.get('row_count'),
                                              'spend_nanodollars': query.get('spend_nanodollars')}},
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'python': sys.version}
    (HERE / 'results/rfe_recurrence_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('classification', 'compatibility', 'sizes',
                                                 'continuing_interface', 'search_accounting')}, indent=2))


if __name__ == '__main__':
    main()
