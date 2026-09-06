#!/usr/bin/env python3
"""Exact proof-tree/resource arithmetic, not cryptographic execution or estimates."""
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SOURCE = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf')


def nodes(branches, horizon):
    return sum(branches ** j for j in range(horizon + 1))


def sim_edges(keys):
    # No external decryption-oracle queries. This counts computational switch
    # obligations; statistical equivalence/correctness events are separate.
    return (['iO'] * (3 * keys) + ['punctured_PRF'] * keys +
            ['commitment', 'NIWI_WI', 'PKE', 'PKE'])


def edge_count(branches, horizon):
    leaves = branches ** horizon
    internal = horizon if branches == 1 else (leaves - 1) // (branches - 1)
    return 2 * len(sim_edges(branches)) * internal + 2 * len(sim_edges(1)) * leaves


def unrank_edge(branches, horizon, rank, path=()):
    """Unrank a uniformly chosen global hybrid edge without listing the tree.

    Ordering is left SIM path, child paths, reversed right SIM path. The walk
    visits at most horizon+1 frames with polynomial-bit integers, even when the edge count is
    exponential; then the distinguishing loss, not enumeration, is prohibitive.
    """
    assert 0 <= rank < edge_count(branches, horizon)
    frame = sim_edges(1 if horizon == 0 else branches)
    if rank < len(frame):
        return path, 'left', rank, frame[rank], 1
    rank -= len(frame)
    if horizon:
        child_edges = edge_count(branches, horizon - 1)
        if rank < branches * child_edges:
            child, child_rank = divmod(rank, child_edges)
            return unrank_edge(branches, horizon - 1, child_rank, path + (child,))
        rank -= branches * child_edges
    reversed_index = len(frame) - 1 - rank
    return path, 'right', reversed_index, frame[reversed_index], -1


def floor_log(base, value):
    exponent, power = 0, 1
    while power * base <= value:
        exponent, power = exponent + 1, power * base
    return exponent


def unrank_one_sim(branches, horizon, rank, path=()):
    assert 0 <= rank < 2 * nodes(branches, horizon)
    if rank == 0:
        return path, 'left', 1
    rank -= 1
    if horizon:
        child_count = 2 * nodes(branches, horizon - 1)
        if rank < branches * child_count:
            child, child_rank = divmod(rank, child_count)
            return unrank_one_sim(branches, horizon - 1, child_rank, path + (child,))
        rank -= branches * child_count
    assert rank == 0
    return path, 'right', -1


def uniform_hybrid_control():
    branches, horizon = 3, 2
    count = edge_count(branches, horizon)
    labels = [unrank_edge(branches, horizon, rank) for rank in range(count)]
    assert len(set(labels)) == count == 272
    types = Counter(label[3] for label in labels)
    assert types == {'iO': 126, 'punctured_PRF': 42,
                     'commitment': 26, 'NIWI_WI': 26, 'PKE': 52}
    assert max(len(label[0]) for label in labels) == horizon
    # An illustrative probability path. These are synthetic distributions, not
    # source primitive advantages. Reversing a right-side primitive experiment
    # is represented explicitly by the orientation in each label.
    probabilities = [Fraction(rank, 2 * count) for rank in range(count + 1)]
    signed_gaps = [probabilities[rank + 1] - probabilities[rank] for rank in range(count)]
    root_gap = probabilities[-1] - probabilities[0]
    average_gap = sum(signed_gaps) / count
    assert sum(signed_gaps) == root_gap == Fraction(1, 2)
    assert average_gap == root_gap / count
    sim_count = 2 * nodes(branches, horizon)
    sim_labels = [unrank_one_sim(branches, horizon, rank) for rank in range(sim_count)]
    assert len(set(sim_labels)) == sim_count == 26
    # Strict bounded-time fair-coin selector: pad to a power of two. Dummy
    # ranks run a valid zero-message, zero-key SIM experiment and output0.
    selector_bits = (sim_count - 1).bit_length()
    selector_domain = 1 << selector_bits
    assert sim_count <= selector_domain < 2 * sim_count
    selected = [unrank_one_sim(branches, horizon, rank) if rank < sim_count
                else ('valid_zero_message_zero_keys', 'constant_output', 0)
                for rank in range(selector_domain)]
    assert sum(item[-1] == 0 for item in selected) == selector_domain - sim_count
    padded_gap = root_gap / selector_domain
    return {'branches': branches, 'horizon': horizon, 'local_SIM_pair_nodes': nodes(branches, horizon),
            'one_SIM_sides': sim_count, 'one_SIM_ranked_choices_unique': True,
            'ideal_uniform_finite_choice_gap': str(root_gap / sim_count),
            'strict_PPT_selector_bits': selector_bits,
            'strict_PPT_selector_domain_M': selector_domain,
            'strict_PPT_dummy_ranks': selector_domain - sim_count,
            'dummy_experiment': 'valid zero message, no key queries, constant output',
            'strict_PPT_synthetic_one_SIM_gap': str(padded_gap),
            'computational_hybrid_edges': count, 'edge_types': dict(types),
            'all_ranked_edges_unique': True, 'maximum_wrapper_depth': horizon,
            'right_edges_have_known_reversed_orientation': True,
            'synthetic_root_gap': str(root_gap), 'synthetic_uniform_edge_gap': str(average_gap),
            'no_actual_primitive_advantages_measured': True}


def horizon_accounting():
    rows = []
    for lam in (16, 32, 64, 128, 256, 512, 1024, 4096):
        h = floor_log(3, lam)
        total = nodes(3, h)
        assert total <= Fraction(3, 2) * lam
        rows.append({'lambda': lam, 'H_floor_log3_lambda': h,
                     'FE_public_key_objects': h + 1, 'FE_function_key_objects': 3 * h + 1,
                     'proof_nodes': total, 'computational_edges': edge_count(3, h)})
    one_branch = []
    for h in (2, 8, 32, 128, 512):
        assert nodes(1, h) == h + 1
        # Closed form avoids recursion depth becoming an accidental script bound.
        one_branch.append({'H': h, 'proof_nodes': h + 1,
                           'computational_edges': 16 * (h + 1)})
    return {'branching_log_horizon': rows, 'one_command_polynomial_horizon_shape': one_branch}


def uniformity_and_negligibility_controls():
    # Every fixed-horizon family vanishes eventually, while its diagonal is1.
    fixed_family = lambda lam, h: int(lam <= (1 << h))
    fixed_checks = 0
    for h in range(1, 17):
        for lam in ((1 << h) + 1, 1 << (h + 1)):
            assert fixed_family(lam, h) == 0
            fixed_checks += 1
    diagonals = []
    for lam in (16, 32, 64, 128, 256, 512, 1024):
        h = (lam - 1).bit_length()
        assert fixed_family(lam, h) == 1
        diagonals.append({'lambda': lam, 'H_ceil_log2_lambda': h, 'diagonal_value': 1})
    # exp(-sqrt(lambda)) is negligible, but exponential branching can overwhelm
    # it. This is a proof-bound control, not a break of any cryptographic scheme.
    amplification = []
    for root in (8, 16, 32, 64, 128):
        lam, h = root * root, root
        base_error = Fraction(1, 1 << root)
        product = nodes(2, h) * base_error
        assert product >= 1
        amplification.append({'lambda': lam, 'H_sqrt_lambda': h,
                              'illustrative_base_error': str(base_error),
                              'tree_weighted_bound': str(product)})
    return {'fixed_family_eventually_zero_checks': fixed_checks,
            'fixed_horizon_negligibility_does_not_prove_diagonal': diagonals,
            'negligible_error_times_superpolynomial_branch_count': amplification}


def nonvacuity():
    rows = []
    for width in (8, 16, 32, 64, 128, 256):
        horizon = floor_log(3, width)
        assert horizon + 1 < width - 1
        path_checks = 0
        for commands in itertools.product(('add_one', 'double', 'infer'), repeat=horizon):
            states = [0, 1]
            outputs = [[], []]
            for command in commands:
                for index, state in enumerate(states):
                    if command == 'add_one':
                        states[index] = (state + 1) % (1 << width)
                        outputs[index].append('ACK')
                    elif command == 'double':
                        states[index] = (2 * state) % (1 << width)
                        outputs[index].append('ACK')
                    else:
                        outputs[index].append(state >> (width - 1))
            for index, state in enumerate(states):
                outputs[index].append(state >> (width - 1))
            assert outputs[0] == outputs[1] and states[0] != states[1]
            path_checks += 1
        critical = (1 << (width - 2)) - 1
        left, right = 2 * (critical + 1), 2 * critical + 1
        assert left >> (width - 1) == 1 and right >> (width - 1) == 0
        rows.append({'state_bits': width, 'horizon': horizon,
                     'private_challenge_pair': [0, 1], 'complete_paths_checked': path_checks,
                     'all_outward_traces_equal': True, 'raw_final_states_remain_distinct': True,
                     'noncommuting_two_step_terminal_bits': [1, 0],
                     'two_step_order_witness_within_horizon': horizon >= 2,
                     'immediate_infer_is_nonconstant': True})
    return rows


def main():
    report = {'classification': 'exact proof/resource and ideal-interface controls, no cryptographic implementation',
              'uniform_corollary_premises': ['uniform PPT host',
                                             'uniform PPT pre-setup initial-pair and Step-description sampler',
                                             'setup-independent initial pair and Step',
                                             'uniform polynomial primitive/circuit/resource bounds'],
              'uniform_hybrid': uniform_hybrid_control(), 'horizon_accounting': horizon_accounting(),
              'uniformity_controls': uniformity_and_negligibility_controls(),
              'nonvacuity': nonvacuity(),
              'source': {'path': str(SOURCE), 'sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                         'url': 'https://eprint.iacr.org/2013/729',
                         'access': 'Def2.3-2.4 pp6-8; Def3.1-3.4 pp10-12; simulator/11hybrids pp14-17; AppendixA pp19-24; AppendixC p25 footnote8 read. No exact concrete security parameters supplied by source.'},
              'search_accounting': {'new_SQL': 0, 'new_schema': 0, 'new_web': 0,
                                    'cumulative_SQL': 8, 'cumulative_schema': 1, 'cumulative_web': 28,
                                    'Kagi': 0, 'eprint_pdf_downloads': 0},
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'python': sys.version}
    (HERE / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
