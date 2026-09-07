#!/usr/bin/env python3
"""Independent arity, source-monomial and ordinary clocked-program checks.

No encryption, quantum adversary, privacy or protected-state experiment is run.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parents[1] / 'pq_composition/base_fe_audit/depth_interface'
TARGET = 'f7a380764376f5292a65e8b0a0ebe9917f90594fc4f5e99875f28a4f080b088a'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pins():
    entries = json.loads((AUTHOR / 'inputs.json').read_text())['inputs']
    result = {item['path']: item['sha256'] for item in entries}
    artifacts = json.loads((AUTHOR / 'artifact_hashes.json').read_text())['files']
    result.update({str(AUTHOR / item['path']): item['sha256'] for item in artifacts})
    result[str(AUTHOR / 'artifact_hashes.json')] = sha(AUTHOR / 'artifact_hashes.json')
    assert result[str(AUTHOR / 'DEPTH_INTERFACE.md')] == TARGET
    for path, digest in result.items():
        assert sha(Path(path)) == digest, path
    return result


def query_incidence():
    checks = 0
    for q_external, m in product(range(1, 9), range(1, 17)):
        # One vector backend instance gets Q vector queries. Bit splitting
        # sends all Q*M predicates to one Boolean instance.
        vector = Counter({0: q_external})
        split = Counter(instance for _ in range(q_external)
                        for _ in range(m) for instance in (0,))
        # AJ instead uses M separately addressed Boolean instances; each sees
        # Q queries. This says nothing about independence of real PRF tapes.
        separate = Counter(i for _ in range(q_external) for i in range(m))
        assert vector[0] == q_external
        assert split[0] == q_external * m
        assert len(separate) == m and set(separate.values()) == {q_external}
        assert sum(split.values()) == sum(separate.values())
        checks += 1
    return {'parameter_pairs': checks, 'one_instance_split_bound': 'Q*M',
            'AJ_separately_addressed_instance_bound': 'Q per instance; M instances',
            'direct_vector_bound': 'Q'}


def monomials():
    checks = 0
    for kappa, degree, q_external, m in product((1, 7, 32, 128),
                                               (1, 3, 16), range(1, 6), range(1, 33)):
        q_internal = q_external * m
        # Unit coefficients represent normalized monomials only.
        t = kappa * q_internal**2
        instances = degree**2 * q_internal**2 * t
        masks = kappa * q_internal**2
        assert instances == kappa * degree**2 * q_external**4 * m**4
        assert masks == kappa * q_external**2 * m**2
        assert instances == (kappa * degree**2 * q_external**4) * m**4
        assert masks == (kappa * q_external**2) * m**2
        checks += 1
    chunks = 0
    for m, width in product(range(1, 129), range(1, 65)):
        count = (m + width - 1) // width
        assert width * count >= m
        assert width * (count - 1) < m
        chunks += 1
    return {'normalized_monomial_checks': checks, 'chunk_cover_checks': chunks,
            'warning': 'No hidden Theta constants, measured cost ratios or optimality claim.'}


def run_program(program, bit):
    accumulator = bit
    output = None
    steps = 0
    for instruction in program:
        steps += 1
        if instruction == 'flip':
            accumulator ^= 1
        elif instruction == 'emit':
            output = accumulator
        elif instruction == 'halt':
            return output, steps
        else:
            assert instruction == 'noop'
    raise AssertionError('program did not halt')


def clocked(program, bit, bound):
    output, steps = run_program(program, bit)
    assert steps <= bound
    # This explicitly accounts for dummy execution after halt. A common
    # upper-bound label without these dummy steps would leave unequal times.
    dummy_steps = bound - steps
    return output, steps + dummy_steps


def clock_controls():
    equalities = 0
    unequal_actual_times = 0
    different_output_controls = 0
    for flips, left_noops, right_noops, bit in product(range(8), range(8), range(8), range(2)):
        left = ['flip'] * flips + ['emit'] + ['noop'] * left_noops + ['halt']
        right = ['noop'] * right_noops + ['flip'] * flips + ['emit', 'halt']
        width = max(len(left), len(right)) + 3
        # Equal serialized widths alone do not equalize the halt times.
        left += ['noop'] * (width - len(left))
        right += ['noop'] * (width - len(right))
        yl, tl = run_program(left, bit)
        yr, tr = run_program(right, bit)
        assert yl == yr and tl <= width and tr <= width
        unequal_actual_times += tl != tr
        assert clocked(left, bit, width) == clocked(right, bit, width)
        equalities += 1
        assert clocked(left, bit ^ 1, width)[0] != clocked(right, bit, width)[0]
        different_output_controls += 1
    return {'clocked_equalities': equalities,
            'same_width_same_upper_bound_but_unequal_actual_time': unequal_actual_times,
            'clocking_does_not_equalize_distinct_outputs': different_output_controls,
            'scope': 'Ordinary finite instruction interpreter, not randomized encoding.'}


def author_replay():
    dest = HERE / 'reference'
    dest.mkdir(exist_ok=True)
    source = AUTHOR / 'arity_substitution.py'
    shutil.copy2(source, dest / source.name)
    assert sha(source) == sha(dest / source.name)
    process = subprocess.run([sys.executable, str(dest / source.name)],
                             capture_output=True, text=True)
    (HERE / 'author_replay.stdout.txt').write_text(process.stdout)
    (HERE / 'author_replay.stderr.txt').write_text(process.stderr)
    assert process.returncode == 0 and not process.stderr
    generated = dest / 'arity_substitution.json'
    assert generated.read_bytes() == (AUTHOR / generated.name).read_bytes()
    return {'exit_code': process.returncode, 'byte_identical_script': True,
            'JSON_reproduced_exactly': True,
            'author_counts': json.loads(process.stdout)}


before = pins()
result = {'label': 'EXECUTED', 'scope': __doc__, 'script_sha256': sha(Path(__file__)),
          'query_incidence': query_incidence(), 'monomials': monomials(),
          'clock_controls': clock_controls(), 'author_replay': author_replay()}
after = pins()
assert before == after
result.update(input_hashes_before=before, input_hashes_after=after,
              all_inputs_unchanged=True)
encoded = json.dumps(result, indent=2) + '\n'
(HERE / 'results.json').write_text(encoded)
print(encoded, end='')
