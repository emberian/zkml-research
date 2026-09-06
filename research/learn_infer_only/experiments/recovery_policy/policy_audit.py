#!/usr/bin/env python3
"""Finite functionality/capability audit; no encryption or authenticated service."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import hashlib
import json
import sys


def partition(states, views):
    groups = defaultdict(list)
    for state in states:
        groups[tuple(view(state) for view in views)].append(state)
    return list(groups.values())


def summary(groups):
    return {'classes': len(groups), 'class_sizes': sorted(map(len, groups))}


def visible(state):
    version, pair = state
    return version, pair[version]


def transition(state, command, safe=True):
    version, pair = state
    if command == 'learn':
        updated = list(pair)
        updated[version] = 1 - updated[version]
        return version, tuple(updated)
    if command == 'migrate':
        return 1 - version, pair[::-1] if safe else pair
    raise ValueError(command)


def trace(state, commands, safe=True):
    seen = [visible(state)]
    for command in commands:
        state = transition(state, command, safe)
        seen.append(visible(state))
    return seen


def audit():
    states = list(product(range(5), repeat=2))
    old = lambda s: s[0]
    new = lambda s: s[1]
    compatible = lambda s: (2 * s[0] + 1) % 5
    old_groups = partition(states, [old])
    new_groups = partition(states, [new])
    joint_groups = partition(states, [old, new])
    compatible_groups = partition(states, [old, compatible])
    assert len(old_groups) == len(new_groups) == len(compatible_groups) == 5
    assert all(len(g) == 5 for g in old_groups + new_groups + compatible_groups)
    assert len(joint_groups) == 25 and all(len(g) == 1 for g in joint_groups)
    # Deleting an old policy from admission does not delete a saved answer/key.
    for state in states:
        retained_old_answer = old(state)
        new_answer = new(state)
        assert (retained_old_answer, new_answer) == state

    # All command strings through length 8: exhaustive nonadaptive paths. The
    # general adaptive theorem is a separate Lean artifact, not inferred from this.
    model_states = list(product(range(2), product(range(2), repeat=2)))
    related = [(s, t) for s in model_states for t in model_states
               if visible(s) == visible(t)]
    path_checks = 0
    for length in range(9):
        for commands in product(('learn', 'migrate'), repeat=length):
            for s, t in related:
                assert trace(s, commands) == trace(t, commands)
                path_checks += 1
    left, right = (0, (0, 1)), (0, (0, 0))
    safe_trace = trace(left, ('learn', 'migrate', 'learn', 'migrate'))
    assert safe_trace == trace(right, ('learn', 'migrate', 'learn', 'migrate'))
    assert transition(left, 'migrate') != left
    assert trace(left, ('migrate',), False) != trace(right, ('migrate',), False)

    # Distinguishing private initial states can never be hidden if recovery
    # explicitly exports that state, regardless of the name of the credential.
    recover_export = lambda s: s
    assert len(partition(states, [old, recover_export])) == 25
    # A keyless manifest is a public reference. Equal references alone prove no
    # private storage implementation and grant no state-opening method in this toy.
    manifests = {s: ('genesis', 'slot-0') for s in states}
    assert len(partition(states, [old, lambda s: manifests[s]])) == 5
    return {
        'scope': 'exhaustive finite functionality, no encryption implementation',
        'field': 5, 'states': len(states),
        'old_policy': summary(old_groups), 'new_policy': summary(new_groups),
        'retained_old_plus_new': summary(joint_groups),
        'retained_old_plus_compatible': summary(compatible_groups),
        'revocation_erases_saved_information': False,
        'migration': {'model_states': len(model_states), 'related_ordered_pairs': len(related),
                      'max_commands': 8, 'path_pair_checks': path_checks,
                      'representation_changing_trace': safe_trace,
                      'unsafe_left_trace': trace(left, ('migrate',), False),
                      'unsafe_right_trace': trace(right, ('migrate',), False)},
        'export_recovery_classes': 25, 'public_manifest_classes': 5,
        'all_assertions_passed': True,
    }


if __name__ == '__main__':
    result = audit()
    result['command'] = [sys.executable, str(Path(__file__).resolve())]
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output = Path(__file__).with_name('policy_audit.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
