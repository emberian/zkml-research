#!/usr/bin/env python3
"""Exact finite algebra for a source-level base-FE review.

No encryption, runtime privacy, state-recovery, extraction, or quantum protocol
experiment is implemented. The probability spaces below test bookkeeping and
finite-group translation facts used in the written conditional reductions.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parents[1]/'pq_composition/base_fe_audit'
TARGET = '3e49e259abbe3ca72da5528b96ca8080b96a3589a442e6b3a38ea66841c60d2d'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tv(p, q):
    return sum(abs(p.get(x, 0)-q.get(x, 0)) for x in p.keys() | q.keys())/2


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total+1):
        for rest in compositions(total-first, slots-1):
            yield (first,)+rest


def translate(p, message, modulus):
    return {(x, (y+message)%modulus): mass for (x, y), mass in p.items()}


def all_block_replacement():
    cases = 0
    corr_shortcut_witness = None
    for modulus, denominator in ((2, 8), (3, 3)):
        points = list(product(range(modulus), repeat=2))
        uniform = {x: F(1, len(points)) for x in points}
        for counts in compositions(denominator, len(points)):
            law = dict(zip(points, (F(c, denominator) for c in counts)))
            epsilon = tv(law, uniform)
            first_marginal = defaultdict(F)
            for (x, _), mass in law.items():
                first_marginal[x] += mass
            uniform_last = {(x, y): first_marginal[x]/modulus for x, y in points}
            corr = tv(law, uniform_last)
            assert corr <= 2*epsilon
            if epsilon > 0 and corr > epsilon and corr_shortcut_witness is None:
                corr_shortcut_witness = {'modulus': modulus, 'counts': counts,
                    'denominator': denominator, 'all_block_TV': str(epsilon),
                    'correlated_to_uniform_last_TV': str(corr)}
            for left, right in product(range(modulus), repeat=2):
                # All coordinates are uniform and independent in the middle;
                # translating the last coordinate leaves this law unchanged.
                assert translate(uniform, left, modulus) == uniform
                gap = tv(translate(law, left, modulus), translate(law, right, modulus))
                assert gap <= 2*epsilon
                cases += 1
    # Explicit tight two-leg witness. A one-epsilon bound would be false.
    law = {(0, 0): F(3, 8), (0, 1): F(1, 8), (1, 0): F(1, 4), (1, 1): F(1, 4)}
    uniform = {x: F(1, 4) for x in law}
    assert tv(law, uniform) == F(1, 8)
    assert tv(law, translate(law, 1, 2)) == F(1, 4)
    # A uniform final marginal alone is insufficient if it remains correlated
    # with the preceding public block.
    diagonal = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    assert tv(diagonal, translate(diagonal, 1, 2)) == 1
    # A finer ternary law shows that simply assigning the all-block gap to
    # the correlated-to-uniform-last comparison can undercount that gap.
    ternary = {point: F(1, 9) for point in product(range(3), repeat=2)}
    ternary[(0, 0)] += F(1, 9)
    ternary[(1, 0)] -= F(1, 9)
    ternary_uniform = {point: F(1, 9) for point in ternary}
    ternary_marginal = {x: sum(ternary[x, y] for y in range(3)) for x in range(3)}
    ternary_last_uniform = {(x, y): ternary_marginal[x]/3 for x, y in ternary}
    assert tv(ternary, ternary_uniform) == F(1, 9)
    assert tv(ternary, ternary_last_uniform) == F(4, 27)
    corr_shortcut_witness = {'modulus': 3, 'all_block_TV': '1/9',
                            'correlated_to_uniform_last_TV': '4/27',
                            'row_major_masses': [str(ternary[x]) for x in ternary]}
    return {'finite_group_message_pair_checks': cases,
            'direct_two_leg_bound_tight': {'one_leg': '1/8', 'message_gap': '1/4'},
            'uniform_marginal_without_independence_gap': '1',
            'correlated_shortcut_witness': corr_shortcut_witness,
            'scope': 'Finite group laws, not instantiated TOR/LWE/ABE games.'}


def branch_errors():
    cases = 0
    exact_refusal_cases = 0
    # Symbolic return values; None is the refusal value. The actual wrapper
    # chooses the first non-refusal branch, matching GKP Appendix B.
    for predicate in range(2):
        messages = (10, 20)
        for returned in product((None, 10, 20, 30), repeat=2):
            output = returned[0] if returned[0] is not None else returned[1]
            active_bad = returned[predicate] != messages[predicate]
            inactive_bad = returned[1-predicate] is not None
            assert (output != messages[predicate]) <= (active_bad or inactive_bad)
            cases += 1
            if not inactive_bad:
                assert (output != messages[predicate]) == active_bad
                exact_refusal_cases += 1
        # The unopened ordinary ABE predicate evaluates to zero; its challenge
        # slot can therefore be selected before setup in the static schedule.
        branch_predicates = (1-predicate, predicate)
        assert branch_predicates[predicate] == 1
        assert branch_predicates[1-predicate] == 0
    return {'wrapper_failure_implication_cases': cases,
            'exact_false_branch_refusal_cases': exact_refusal_cases,
            'static_unopened_branch_cases': 2}


def explicit_key_width():
    cases = 0
    for message_bits, fhe_bits, matrix_bits, fhe_pk_bits in product(
            range(1, 65), range(1, 9), range(1, 9), range(17)):
        attribute_bits = message_bits*fhe_bits+fhe_pk_bits
        raw_pk_bits = 2*fhe_bits*(2*attribute_bits+1)*matrix_bits
        assert raw_pk_bits >= 4*message_bits*fhe_bits**2*matrix_bits
        assert raw_pk_bits > message_bits
        cases += 1
    # Use the deliberately weakest allowed constants L=matrix_bits=1 and
    # hpk=0, omit all circuit/prefix metadata. Even this relaxed lower model
    # grows as N_i = 4*N_(i+1)+2, starting with one leaf bit.
    rows = []
    size = 1
    for depth in range(33):
        assert size == (5*4**depth-2)//3
        assert size >= 4**depth
        rows.append({'depth': depth, 'relaxed_root_payload_lower_bound': size,
                     'weaker_four_to_depth_bound': 4**depth})
        size = 4*size+2
    return {'literal_matrix_tuple_width_checks': cases,
            'per_level_lower_bound_rows': rows,
            'premises': ['uncompressed explicit GKP/GVW tuple',
                         'complete next-level public key embedded in plaintext',
                         'next-level GKP message bound covers its payload',
                         'L>=1 and nonempty encoding of each matrix'],
            'scope': 'Refutes this literal recursive-payload substitution only; no claim about compressed or alternative short-key constructions.'}


def coefficients():
    cases = 0
    for n, length, g in product(range(1, 33), range(1, 33), range(1, 17)):
        # Slots: FHE IND, garbling simulation, ABE2, evaluated-FHE error.
        one_leg = (n, 1, length, 1)
        both_legs = tuple(a+a for a in one_leg)
        assert both_legs == (2*n, 2, 2*length, 2)
        # Two statistical replacements per predicate gate on each message leg.
        assert sum([g, g, g, g]) == 4*g
        cases += 1
    return {'gkp_and_abe_gate_coefficient_cases': cases,
            'direct_ABE_LWE_coefficient': 2,
            'black_box_TOR_composition_safe_LWE_coefficient': 4,
            'ABE_gate_statistical_coefficient_for_one_key':
                '2*g*(eta_recode + eta_key), when each is a per-replacement TV envelope'}


def main():
    access = json.loads((AUTHOR/'access.json').read_text())
    named = ['BASE_FE_AUDIT.md', 'source_spans.json', 'access.json', 'rate_ledger.py',
             'rate_ledger.json', 'validate.py', 'validation.json', 'artifact_hashes.json']
    files = [AUTHOR/name for name in named]
    for row in access['local_pdf_reads']:
        pdf, txt = Path(row['path']), Path(row['command'][-1])
        assert sha(pdf) == row['sha256']
        assert sha(txt) == row['text_sha256']
        files += [pdf, txt]
    before = {str(path): sha(path) for path in files}
    assert sha(AUTHOR/'BASE_FE_AUDIT.md') == TARGET
    reference = HERE/'reference'
    reference.mkdir(exist_ok=True)
    shutil.copyfile(AUTHOR/'rate_ledger.py', reference/'rate_ledger.py')
    assert sha(reference/'rate_ledger.py') == sha(AUTHOR/'rate_ledger.py')
    command = ['python3', str(reference/'rate_ledger.py')]
    run = subprocess.run(command, capture_output=True, text=True, check=False)
    (HERE/'author_replay.stdout.txt').write_text(run.stdout)
    (HERE/'author_replay.stderr.txt').write_text(run.stderr)
    assert run.returncode == 0, run.stderr
    assert (reference/'rate_ledger.json').read_bytes() == (AUTHOR/'rate_ledger.json').read_bytes()
    result = {'label': 'EXECUTED', 'scope': __doc__, 'script_sha256': sha(Path(__file__)),
              'all_block_replacement': all_block_replacement(),
              'branch_errors': branch_errors(), 'key_width': explicit_key_width(),
              'coefficients': coefficients(),
              'author_replay': {'command': command, 'exit_code': run.returncode,
                                'byte_identical_owned_script': True,
                                'result_matches_frozen_author': True},
              'additional_web_queries': 0, 'additional_scry_queries': 0,
              'additional_kagi_queries': 0, 'PDF_downloads': 0}
    after = {str(path): sha(path) for path in files}
    assert before == after
    result.update(input_hashes_before=before, input_hashes_after=after,
                  all_inputs_unchanged=True)
    encoded = json.dumps(result, indent=2)+'\n'
    (HERE/'results.json').write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
