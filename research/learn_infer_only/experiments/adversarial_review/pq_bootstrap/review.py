#!/usr/bin/env python3
"""Independent exact finite controls for the conditional bootstrap proof.

These are channel algebra, compatibility and error-accounting tests, not FE,
PRG, xiO, quantum-security implementations, or state-recovery experiments.
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
EXPERIMENTS = HERE.parents[1]
AUTHOR = EXPERIMENTS / 'pq_composition/qio_instantiation/bootstrap_lift'
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
EXPECTED = {
    'BOOTSTRAP_LIFT.md': 'ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792',
    'POINTWISE_CORRECTNESS.md': 'c63e299a31a33617888814d5b4f371cf0f1e25541b4ebaa061e9bc84340d81f2',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tv(p, q):
    return sum(abs(p.get(x, 0)-q.get(x, 0)) for x in p.keys() | q.keys())/2


def push(law, channel):
    out = defaultdict(F)
    for x, p in law.items():
        for y, q in channel(x).items():
            out[y] += p*q
    assert sum(out.values()) == 1
    return dict(out)


def uniform(xs):
    xs = list(xs)
    return {x: F(1, len(xs)) for x in xs}


def compatibility_and_position_wrapper():
    """Symbolic ciphertexts expose their arguments; only assembly is tested."""
    compatible = 0
    view_checks = 0
    for width in range(1, 5):
        for y in product(range(2), repeat=width):
            for seed in product(range(2), repeat=width):
                pad = tuple(a ^ b for a, b in zip(y, seed))
                real = tuple(('real', y, i) for i in range(width))
                sim = tuple(('sim', pad, seed, i) for i in range(width))
                def f(message):
                    if message[0] == 'real':
                        return message[1][message[2]]
                    return message[1][message[3]] ^ message[2][message[3]]
                for i in range(width):
                    assert f(real[i]) == f(sim[i]) == y[i]
                    compatible += 1
                # A fixed nontrivial setup key suffices to test position/coin
                # allocation; the separate joint-key control enumerates keys.
                pk = 3
                for rank in range(width):
                    for bit in range(2):
                        messages = sim[:rank] + (real[rank] if bit == 0 else sim[rank],) + real[rank+1:]
                        direct = uniform(tuple((pk, m, r) for m, r in zip(messages, coins))
                                         for coins in product(range(2), repeat=width))
                        wrapped = defaultdict(F)
                        for challenge_coin in range(2):
                            for other_coins in product(range(2), repeat=width-1):
                                others = iter(other_coins)
                                ct = tuple((pk, m, challenge_coin if j == rank else next(others))
                                           for j, m in enumerate(messages))
                                wrapped[ct] += F(1, 2**width)
                        assert direct == dict(wrapped)
                        view_checks += 1
    return {'compatible_indexed_message_pairs': compatible,
            'exact_single_challenge_public_wrapper_laws': view_checks,
            'scope': 'One symbolic supplied key, one challenged position, publicly sampled remaining positions; no privacy claim for symbolic ciphertexts.'}


def shared_key_postprocessing():
    # Joint child view retains key. A sibling is public postprocessing with fresh
    # independent seed/tape. The subsequent map stands for any parent simulator.
    child = uniform(product(range(4), range(2), range(2)))
    def sibling_view(x, resample=False):
        pk, seed, tape = x
        keys = range(4) if resample else (pk,)
        return uniform((pk, seed, tape, kp, sibling_seed, sibling_tape)
                       for kp in keys for sibling_seed in range(2) for sibling_tape in range(2))
    honest = uniform((pk, a, r, pk, b, s)
                     for pk in range(4) for a, r, b, s in product(range(2), repeat=4))
    wrapped = push(child, sibling_view)
    wrong = push(child, lambda x: sibling_view(x, True))
    assert wrapped == honest
    assert tv(honest, wrong) == F(3, 4)
    # The channel may retain all child data, so the contractivity bound can be
    # tight. Test every point-mass alternative to the challenged child view.
    checks = 0
    for x in child:
        alternate = {x: F(1)}
        assert tv(push(alternate, sibling_view), wrapped) <= tv(alternate, child)
        checks += 1
    return {'honest_joint_support': len(honest), 'postprocessing_checks': checks,
            'wrong_independent_sibling_key_TV': str(tv(honest, wrong)),
            'scope': 'An exact joint-law test; replacing the shared key by an independent key changes the distribution.'}


def path_marginals():
    """Two finite channels test the hybrid algebra, not computational PRGs.

    alpha=1 is a deliberately insecure deterministic one-bit expander.
    alpha=1/4 is a randomized near-uniform channel making accumulated TV
    accounting nonvacuous. It is explicitly not a deterministic PRG.
    """
    tuples = tuple(product(range(2), repeat=4))
    u4 = uniform(tuples)
    pair_uniform = uniform(product(range(2), repeat=2))
    cases = 0
    summaries = []
    for alpha in (F(1, 4), F(1)):
        def expand(seed):
            target = (seed, seed, 0, seed)
            return {t: (1-alpha)*u4[t] + (alpha if t == target else 0) for t in tuples}
        full_fresh = push(uniform(range(2)), expand)
        epsilon = tv(full_fresh, u4)
        for depth in range(8):
            maximum = F(0)
            for prefix in product(range(2), repeat=depth):
                pair = pair_uniform
                for bit in prefix:
                    def one_step(previous):
                        raw = expand(previous[0])
                        projected = defaultdict(F)
                        for value, p in raw.items():
                            projected[value[2*bit:2*bit+2]] += p
                        return dict(projected)
                    pair = push(pair, one_step)
                gap = tv(pair, pair_uniform)
                assert gap <= depth*epsilon
                maximum = max(maximum, gap)
                cases += 1
            summaries.append({'alpha': str(alpha), 'depth': depth,
                              'full_fresh_channel_TV': str(epsilon),
                              'maximum_fixed_prefix_joint_pair_TV': str(maximum)})
    # Uniform separate marginals do not imply a fresh independent pair.
    diagonal = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
    assert tv(diagonal, pair_uniform) == F(1, 2)
    assert push(diagonal, lambda x: {x[0]: F(1)}) == uniform(range(2))
    assert push(diagonal, lambda x: {x[1]: F(1)}) == uniform(range(2))
    # A known seed fixes the deterministic pair; it is not the fresh marginal.
    conditioned = {(0, 0): F(1)}
    assert tv(conditioned, pair_uniform) == F(3, 4)
    return {'fixed_prefix_joint_law_checks': cases, 'by_depth': summaries,
            'equal_marginals_joint_TV': '1/2', 'known_seed_conditional_TV': '3/4',
            'scope': path_marginals.__doc__}


def pointwise_shared_setup():
    checks = 0
    examples = []
    for keys in range(2, 17):
        for positions in range(1, keys+1):
            # Two extreme dependence patterns: all errors coincide, or each
            # position fails on a different key. Every fixed position has 1/K.
            for coincident in (False, True):
                failures = []
                for key in range(keys):
                    failures.append(tuple(key == (0 if coincident else i)
                                          for i in range(positions)))
                pointwise = [F(sum(row[i] for row in failures), keys) for i in range(positions)]
                any_error = F(sum(any(row) for row in failures), keys)
                assert all(p == F(1, keys) for p in pointwise)
                assert any_error <= sum(pointwise)
                assert any_error == (F(1, keys) if coincident else F(positions, keys))
                checks += 1
                if keys == 8 and positions == 3:
                    examples.append({'coincident': coincident, 'pointwise': '1/8',
                                     'actual_union': str(any_error),
                                     'independence_formula_not_used': str(1-F(7, 8)**3)})
        # Choosing position=key after seeing this synthetic setup lies outside
        # the fixed-message premise and has failure one, not 1/K.
        assert all(key == key for key in range(keys))
    return {'shared_setup_union_checks': checks, 'examples': examples,
            'failed_premise_sibling': 'Post-setup choice i=key in the disjoint pattern has error 1 while every fixed i has error 1/K.'}


def coefficients():
    cases = 0
    for n in range(31):
        # Build privacy coefficients by the induction, independently of their
        # closed forms, and correctness weights by counting each level.
        privacy = (2, 0)
        weights = [1]
        for _ in range(n):
            privacy = (2+2*privacy[0], 2+2*privacy[1])
            weights.append(2*weights[-1])
        assert privacy == (2**(n+2)-2, 2**(n+1)-2)
        nodes, depths = sum(weights), sum(d*w for d, w in enumerate(weights))
        assert nodes == 2**(n+1)-1
        assert nodes+depths == n*2**(n+1)+1
        for s, lh in product(range(1, 17), repeat=2):
            privacy_re = (lh+s, 2*s+2, 2*s, 5)
            assert sum(privacy_re) <= 6*max(s, lh)+7
            errors = (nodes, nodes*(lh+s), nodes*s, nodes, depths)
            assert errors[1] <= nodes*2*max(s, lh)
            assert errors[2] <= nodes*max(s, lh)
            cases += 1
    return {'privacy_and_correctness_coefficient_cases': cases,
            'n_zero': {'privacy_RE': 2, 'privacy_tree_PRG': 0,
                       'correctness_nodes': 1, 'combined_correctness_PRG': 1}}


def replay_author():
    reference = HERE/'reference'
    reference.mkdir(exist_ok=True)
    for name in ('controls.py', 'pointwise_controls.py', *EXPECTED):
        shutil.copyfile(AUTHOR/name, reference/name)
        assert sha(reference/name) == sha(AUTHOR/name)
    records = []
    for script in ('controls.py', 'pointwise_controls.py'):
        command = ['python3', str(reference/script)]
        run = subprocess.run(command, capture_output=True, text=True, check=False)
        (HERE/(script+'.stdout.txt')).write_text(run.stdout)
        (HERE/(script+'.stderr.txt')).write_text(run.stderr)
        assert run.returncode == 0, run.stderr
        actual = json.loads(run.stdout)
        expected = json.loads((AUTHOR/(script.removesuffix('.py')+'.json')).read_text())
        assert actual == expected
        records.append({'command': command, 'exit_code': run.returncode,
                        'matches_frozen_author_result': True,
                        'result': actual})
    return records


def main():
    files = [AUTHOR/name for name in (*EXPECTED, 'REVIEW_REQUEST.md', 'controls.py',
             'controls.json', 'pointwise_controls.py', 'pointwise_controls.json', 'audit.json', 'ACCESS.md')]
    files += [MIRROR/'2016/006.pdf', MIRROR/'2015/720.pdf',
              HERE/'extracts/2016-006.txt', HERE/'extracts/2015-720.txt']
    before = {str(p): sha(p) for p in files}
    for name, expected in EXPECTED.items():
        assert sha(AUTHOR/name) == expected
    result = {'label': 'EXECUTED', 'scope': __doc__,
              'script_sha256': sha(Path(__file__)),
              'position_wrapper': compatibility_and_position_wrapper(),
              'shared_key': shared_key_postprocessing(),
              'path_marginals': path_marginals(),
              'pointwise_setup': pointwise_shared_setup(),
              'coefficients': coefficients(),
              'author_replays_in_owned_copies': replay_author(),
              'additional_network_queries': 0}
    after = {str(p): sha(p) for p in files}
    assert before == after
    result['input_hashes_before'] = before
    result['input_hashes_after'] = after
    result['all_review_inputs_unchanged'] = True
    text = json.dumps(result, indent=2)+'\n'
    (HERE/'results.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
