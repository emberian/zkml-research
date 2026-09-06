#!/usr/bin/env python3
"""Finite checks of program-equivalence premises, not cryptographic primitives."""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    # A finite plaintext-bearing model deliberately has no encryption security.
    # c=(plaintext,coin) models only perfect PKE decoding and distinct supports.
    cts = list(product(range(2), range(2)))
    tags = list(product(cts, cts, range(2)))
    t_star = ((1, 0), (0, 1), 1)
    y_star = 7

    def valid(tag, proof, signature):
        c0, c1, _ = tag
        true_statement = c0[0] == c1[0] or tag == t_star
        return proof and signature and true_statement

    def sim(side, tag, proof, signature, sound=True):
        if not signature or not proof:
            return None
        if sound and not valid(tag, proof, signature):
            return None
        if tag == t_star:
            return y_star
        return tag[side][0]

    rows = []
    for tag, proof, signature in product(tags, [False, True], [False, True]):
        lhs, rhs = sim(0, tag, proof, signature), sim(1, tag, proof, signature)
        assert lhs == rhs
        rows.append((tag, proof, signature, lhs))

    bad_tag = ((0, 0), (1, 0), 0)
    assert bad_tag != t_star
    bad_pair = [sim(0, bad_tag, True, True, sound=False),
                sim(1, bad_tag, True, True, sound=False)]
    assert bad_pair == [0, 1]

    # The unhooked oracle programs disagree on an accepted t_star when its two
    # PKE components encrypt different messages. Valid-signature exclusion matters.
    special_plain_outputs = [t_star[0][0], t_star[1][0]]
    assert special_plain_outputs == [1, 0]

    # Source Figure 1 typo versus the intended Verify=0 rejection semantics.
    honest_signature_valid = True
    source_literal_rejects = bool(honest_signature_valid)
    normalized_rejects = not honest_signature_valid
    assert source_literal_rejects and not normalized_rejects

    # Why pointwise average correctness is weaker than a uniform all-input event:
    # a sampled program is wrong at one explicitly encoded location.
    size = 16
    pointwise_error = [Fraction(sum(bad == x for bad in range(size)), size)
                       for x in range(size)]
    all_input_failure = Fraction(sum(any(bad == x for x in range(size))
                                     for bad in range(size)), size)
    adaptive_code_reader_failure = Fraction(sum(bad == bad for bad in range(size)), size)
    assert set(pointwise_error) == {Fraction(1, size)}
    assert all_input_failure == adaptive_code_reader_failure == 1

    # Sum the eleven transition entries for a one-world hybrid path. The
    # coefficient d is the public indicator that qD is positive.
    def ledger(qk, qd):
        d = int(qd > 0)
        return [
            {'IO': qk}, {'PPRF': qk}, {'COM': 1}, {'WI': 1}, {'PKE': 1},
            {'IO': qk, 'NIWI_BAD': qk},
            {'SUF': d, 'NIWI_BAD': d, 'IO_CORR': 2 * qd},
            {'PKE': 1},
            {'SUF': d, 'NIWI_BAD': d, 'IO_CORR': 2 * qd},
            {'IO': qk, 'NIWI_BAD': qk},
            {'PPRF': qd, 'IO_CORR': qd},
        ]

    ledger_checks = 0
    for qk, qd in product(range(17), range(17)):
        total = {key: sum(row.get(key, 0) for row in ledger(qk, qd))
                 for key in ['IO', 'PPRF', 'COM', 'WI', 'PKE', 'SUF', 'NIWI_BAD', 'IO_CORR']}
        expected = {'IO': 3 * qk, 'PPRF': qk + qd, 'COM': 1, 'WI': 1,
                    'PKE': 2, 'SUF': 2 * int(qd > 0),
                    'NIWI_BAD': 2 * qk + 2 * int(qd > 0), 'IO_CORR': 5 * qd}
        assert total == expected
        ledger_checks += 1

    result = {
        'label': 'EXECUTED',
        'scope': 'Finite program-premise and coefficient checks only. '
                 'No real encryption, obfuscation, quantum game or PQ instantiation.',
        'simulated_key_equivalence_cases': len(rows),
        'soundness_removed_counterexample': {'tag': bad_tag, 'outputs': bad_pair},
        'accepted_special_tag_oracle_outputs': special_plain_outputs,
        'honest_signature_source_literal_rejects': source_literal_rejects,
        'honest_signature_normalized_rejects': normalized_rejects,
        'pointwise_correctness_control': {'domain_size': size,
             'each_fixed_input_error': str(pointwise_error[0]),
             'all_input_failure_probability': str(all_input_failure),
             'adaptive_code_reader_failure_probability': str(adaptive_code_reader_failure)},
        'eleven_transition_coefficient_checks': ledger_checks,
        'zero_decryption_ledger_at_qk_3': ledger(3, 0),
    }
    (HERE / 'functional_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
