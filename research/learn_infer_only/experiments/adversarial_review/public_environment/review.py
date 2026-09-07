#!/usr/bin/env python3
"""Independent Boolean, dependency-graph and integer-bound controls.

This is not encryption, cryptographic privacy validation, state recovery, a
quantum protocol run, or a compiler implementation for the source FE schemes.
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
AUTHOR = HERE.parents[1]/'pq_composition/base_fe_audit/public_environment'
TARGET = '0293ce75968387ca33b49691274ffb91777f78a31f724dd6a71f76ca2d012ca8'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def evaluate(gates, outputs, key, message, coins):
    values = {'k': key, 'm': message, 'r': coins, 'g': []}
    for op, left, right in gates:
        a, b = (values[ref[0]][ref[1]] for ref in (left, right))
        values['g'].append((a ^ b) if op == 'xor' else (a & b))
    return tuple(values[kind][i] for kind, i in outputs)


def project(gates, outputs):
    used = sorted({i for _, a, b in gates for kind, i in (a, b) if kind == 'k'} |
                  {i for kind, i in outputs if kind == 'k'})
    indices = {index: j for j, index in enumerate(used)}
    def wire(ref):
        kind, index = ref
        return (kind, indices[index] if kind == 'k' else index)
    return used, [(op, wire(a), wire(b)) for op, a, b in gates], [wire(x) for x in outputs]


def projection_controls():
    comparisons = 0
    nonzero = 0
    circuits = 0
    for gates_count, seed in product(range(5), range(8)):
        refs = [('k', i) for i in range(5)] + [('m', i) for i in range(2)] + [('r', 0)]
        gates = []
        for j in range(gates_count):
            a = refs[(3*seed+5*j)%len(refs)]
            b = refs[(7*seed+2*j+1)%len(refs)]
            gates.append(('xor' if (seed+j)%2 else 'and', a, b))
            refs.append(('g', j))
        outputs = [('g', gates_count-1) if gates_count else ('k', seed%5),
                   ('k', (seed+1)%5), ('m', seed%2)]
        used, small_gates, small_outputs = project(gates, outputs)
        assert len(used) <= 2*gates_count+len(outputs)
        for bits in product(range(2), repeat=8):
            key, message, coins = bits[:5], bits[5:7], bits[7:]
            full = evaluate(gates, outputs, key, message, coins)
            reduced = evaluate(small_gates, small_outputs, tuple(key[i] for i in used), message, coins)
            assert full == reduced
            comparisons += 1
            nonzero += any(full)
        circuits += 1
    direct_outputs = []
    for width in (1, 2, 8, 64, 1024):
        used, _, _ = project([], [('k', j) for j in range(width)])
        assert len(used) == width
        direct_outputs.append({'gates': 0, 'outputs': width, 'needed_key_bits': len(used)})
    return {'circuits': circuits, 'exhaustive_projection_equalities': comparisons,
            'nonzero_output_cases': nonzero, 'zero_gate_passthrough': direct_outputs}


def tv(p, q):
    return sum(abs(p.get(x, 0)-q.get(x, 0)) for x in p.keys() | q.keys())/2


def environment_channels():
    cases = []
    # Tagged finite records model only the dependency of a regenerated outer
    # package on the supplied key. No security property of these records is
    # asserted. A stale tag and a fresh tag have disjoint consistency support.
    for seam in ('inner_to_outer', 'child_to_parent'):
        correct = defaultdict(F)
        stale = defaultdict(F)
        for key, child_data, sibling_data, fresh_outer_coin in product(range(4), repeat=4):
            changed_key = key ^ 1
            common = (seam, changed_key, child_data, (changed_key, sibling_data), fresh_outer_coin)
            correct[common+(changed_key,)] += F(1, 256)
            stale[common+(key,)] += F(1, 256)
        assert sum(correct.values()) == sum(stale.values()) == 1
        assert all(record[1] == record[-1] == record[3][0] for record in correct)
        assert all(record[1] != record[-1] for record in stale)
        assert tv(dict(correct), dict(stale)) == 1
        cases.append({'seam': seam, 'correct_support': len(correct),
                      'stale_environment_TV': '1'})
    # A later-sampled parent record depending on the child key must not be
    # conditioned on when invoking fresh child-setup correctness.
    joint = {(key, key): F(1, 4) for key in range(4)}
    marginal_bad = sum(p for (key, _), p in joint.items() if key == 0)
    parent_zero = sum(p for (_, parent), p in joint.items() if parent == 0)
    conditional_bad = sum(p for (key, parent), p in joint.items() if key == parent == 0)/parent_zero
    assert marginal_bad == F(1, 4) and conditional_bad == 1
    return {'regeneration_seams': cases,
            'conditioning_scope_control': {'fresh_key_event': str(marginal_bad),
                'same_event_conditioned_on_parent_record': str(conditional_bad)}}


def setup_order():
    checks = 0
    for depth in range(33):
        order = [(kind, i) for i in range(depth, -1, -1) for kind in ('W', 'S')]
        at = {stage: i for i, stage in enumerate(order)}
        for i in range(depth+1):
            assert at['W', i] < at['S', i]
            if i < depth:
                assert at['S', i+1] < at['W', i]
            checks += 1
        assert len(order) == 2*(depth+1)
    return {'level_dependency_checks': checks, 'depths_checked': 33,
            'scope': 'Exact ordering constraints only, not verification of a probabilistic setup implementation.'}


def full_parameter_examples():
    # One intentionally loose fixed polynomial toy satisfying simultaneous
    # S, key, ciphertext, output-padding and time inequalities. These functions
    # are declared model bounds, not numerical costs of a cryptosystem.
    rows = []
    for log_u in range(1, 13):
        u = 2**log_u
        t = (2*u)**256
        log_t = 256*(1+log_u)
        s = (2*(u+t))**8
        log_s = s.bit_length()  # safe integer upper bound
        n = 4*(u+log_t+2)
        key = 8*n*(log_s+1)**2
        tape_b = n
        gate_b = key+n+tape_b+1
        output_b = 2*n
        assert key <= 2*gate_b+output_b
        # Specializing the function and compiling the weak encoder must fit S.
        specialized_size = (u+t+key+1)**6
        assert specialized_size <= s
        raw_xio_size = 4*(gate_b+1)**2
        ct_weak = (2*u)**128 * raw_xio_size**2
        enc_composed_work = ct_weak*(gate_b+tape_b+output_b)
        # Choose common output padding from the sublinear upper bound, rather
        # than forcing all nodes to write T bits of padding.
        output_bound = 2*enc_composed_work+1
        node_work = 4*enc_composed_work*(log_t+1)**2+output_bound+u**3
        assert output_bound <= t
        assert node_work <= t
        assert key > n
        rows.append({'U': u, 'log2_T': log_t, 'log2_S_upper': log_s,
                     'N': n, 'K': key, 'K_exceeds_N': True,
                     'specialized_size_fits_S': True, 'output_padding_fits_T': True,
                     'node_work_fits_T': True,
                     'node_work_bit_length': node_work.bit_length(),
                     'output_bound_bit_length': output_bound.bit_length()})
    return {'scope': full_parameter_examples.__doc__ or 'Declared integer model bounds only.',
            'rows': rows, 'fixed_time_polynomial': 'T=(2U)^256',
            'fixed_size_polynomial': 'S=(2(U+T))^8'}


def coefficients():
    checks = 0
    for n in range(25):
        privacy = (2, 0)
        for _ in range(n):
            privacy = (2+2*privacy[0], 2+2*privacy[1])
        assert privacy == (2**(n+2)-2, 2**(n+1)-2)
        nodes = sum(2**d for d in range(n+1))
        depths = sum(d*2**d for d in range(n+1))
        for output_positions, inner_width in product(range(1, 17), repeat=2):
            bound = max(output_positions, inner_width)
            assert nodes*(inner_width+output_positions) <= nodes*2*bound
            assert nodes*output_positions <= nodes*bound
            assert nodes+depths == n*2**(n+1)+1
            checks += 1
    return {'unchanged_privacy_and_correctness_coefficient_cases': checks}


def main():
    inputs = json.loads((AUTHOR/'inputs.json').read_text())['inputs']
    artifacts = json.loads((AUTHOR/'artifact_hashes.json').read_text())['files']
    files = []
    for row in inputs:
        p = Path(row['path'])
        assert sha(p) == row['sha256']
        files.append(p)
    for row in artifacts:
        p = AUTHOR/row['path']
        assert sha(p) == row['sha256']
        files.append(p)
    files.append(AUTHOR/'artifact_hashes.json')
    assert sha(AUTHOR/'PUBLIC_ENVIRONMENT.md') == TARGET
    before = {str(p): sha(p) for p in files}
    reference = HERE/'reference'
    reference.mkdir(exist_ok=True)
    shutil.copyfile(AUTHOR/'circuit_dependency.py', reference/'circuit_dependency.py')
    assert sha(reference/'circuit_dependency.py') == sha(AUTHOR/'circuit_dependency.py')
    command = ['python3', str(reference/'circuit_dependency.py')]
    replay = subprocess.run(command, capture_output=True, text=True, check=False)
    (HERE/'author_replay.stdout.txt').write_text(replay.stdout)
    (HERE/'author_replay.stderr.txt').write_text(replay.stderr)
    assert replay.returncode == 0, replay.stderr
    assert (reference/'circuit_dependency.json').read_bytes() == (AUTHOR/'circuit_dependency.json').read_bytes()
    result = {'label': 'EXECUTED', 'scope': __doc__, 'script_sha256': sha(Path(__file__)),
              'projection': projection_controls(), 'channels': environment_channels(),
              'setup_order': setup_order(), 'parameter_examples': full_parameter_examples(),
              'coefficients': coefficients(),
              'author_replay': {'command': command, 'exit_code': replay.returncode,
                                'byte_identical_script_and_result': True},
              'new_queries': {'web': 0, 'scry': 0, 'kagi': 0}, 'PDF_downloads': 0}
    after = {str(p): sha(p) for p in files}
    assert before == after
    result.update(input_hashes_before=before, input_hashes_after=after,
                  all_inputs_unchanged=True)
    text = json.dumps(result, indent=2)+'\n'
    (HERE/'results.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
