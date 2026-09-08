#!/usr/bin/env python3
"""Independent bounded finite-log controls; no Lean or cryptographic execution."""
import itertools
import json
from pathlib import Path


def recompute(table, value, bits, path):
    if not bits:
        return table[('L', value)] if not path else None
    if not path:
        return None
    child = recompute(table, value, bits[1:], path[1:])
    if child is None:
        return None
    q = ('N', path[0], child) if bits[0] else ('N', child, path[0])
    return table[q]


def path_log(table, value, bits, path):
    if not bits or not path:
        return []
    child = recompute(table, value, bits[1:], path[1:])
    if child is None:
        return []
    q = ('N', path[0], child) if bits[0] else ('N', child, path[0])
    return path_log(table, value, bits[1:], path[1:]) + [(q, table[q])]


def opening_log(table, value, bits, path):
    return [(('L', value), table[('L', value)])] + path_log(table, value, bits, path)


def extract(prefix, root, bits, default=0):
    query = next((q for q, answer in prefix if answer == root), None)
    if not bits:
        return query[1] if query and query[0] == 'L' else default
    if query is None or query[0] != 'N':
        return default
    return extract(prefix, query[1 + bits[0]], bits[1:], default)


def bad(prefix, log, root):
    response_collision = any(a == b and q != r for q, a in log for r, b in log)
    targets = {root}
    for q, _ in prefix:
        if q[0] == 'N':
            targets.update(q[1:])
    late = any(entry not in prefix and entry[1] in targets for entry in log)
    return response_collision, late


def main():
    keys = [('L', 0), ('L', 1)] + [('N', a, b) for a in range(2) for b in range(2)]
    entries = list(itertools.product(keys, range(2)))
    # Deliberately admit arbitrary/inconsistent prefixes: the deterministic theorem does.
    prefixes = [()] + [(entry,) for entry in entries] + list(itertools.product(entries, repeat=2))
    counts = dict(cases=0, accepted=0, good_accepted=0, mismatches=0, good_mismatches=0)
    for responses in itertools.product(range(2), repeat=6):
        table = dict(zip(keys, responses))
        middles = [()] + [((key, table[key]),) for key in keys]
        for prefix_tuple in prefixes:
            prefix = list(prefix_tuple)
            for middle in middles:
                for depth in (0, 1):
                    for index in range(1 << depth):
                        bits = [(index >> j) & 1 for j in range(depth)]
                        for value in range(2):
                            for path_tuple in itertools.product(range(2), repeat=depth):
                                path = list(path_tuple)
                                got = recompute(table, value, bits, path)
                                trace = opening_log(table, value, bits, path)
                                assert len(trace) == depth + 1
                                for root in range(2):
                                    counts['cases'] += 1
                                    if got != root:
                                        continue
                                    counts['accepted'] += 1
                                    failure = any(bad(prefix, prefix + list(middle) + trace, root))
                                    mismatch = value != extract(prefix, root, bits)
                                    counts['good_accepted'] += not failure
                                    counts['mismatches'] += mismatch
                                    counts['good_mismatches'] += mismatch and not failure
                                    assert failure or not mismatch
    # Concrete nondegenerate source-shaped hash, only as a finite dictionary.
    table = {('L', 0): 10, ('L', 1): 11, ('N', 10, 11): 2011, ('N', 10, 10): 2010}
    prefix = [(('L', 0), 10), (('L', 1), 11), (('N', 10, 11), 2011)]
    trace = opening_log(table, 1, [1], [10])
    assert recompute(table, 1, [1], [10]) == 2011
    assert bad(prefix, prefix + trace, 2011) == (False, False)
    assert [extract(prefix, 2011, [i]) for i in range(2)] == [0, 1]
    # Child-target tooth: root query old, leaf query new, no late root or collision.
    child_prefix = [(('N', 10, 11), 2011)]
    child_full = child_prefix + trace
    assert bad(child_prefix, child_full, 2011) == (False, True)
    assert not any(e not in child_prefix and e[1] == 2011 for e in child_full)
    assert extract(child_prefix, 2011, [1]) == 0 != 1
    # Acceptance is necessary even when the finite Bad condition is absent.
    wrong_trace = opening_log(table, 0, [1], [10])
    assert recompute(table, 0, [1], [10]) != 2011
    assert bad(prefix, prefix + wrong_trace, 2011) == (False, False)
    assert extract(prefix, 2011, [1]) == 1 != 0
    # Exact path length rejects both directions at depth zero/one.
    malformed = 0
    for bits, paths in (([], [[10], [10, 10]]), ([1], [[], [10, 10]])):
        for path in paths:
            assert recompute(table, 1, bits, path) is None
            malformed += 1
    # First-response selection makes a cross-type collision relevant as well.
    cross = [(('L', 0), 2011)] + prefix
    assert bad(cross, cross + trace, 2011)[0]
    assert extract(cross, 2011, [1]) == 0 != 1
    result = dict(scope='Pure finite tuple/log arithmetic only; no probability or implementation refinement.',
                  counts=counts, arbitrary_prefixes=len(prefixes), oracle_tables=64,
                  child_target_falsifier=True, acceptance_premise_falsifier=True,
                  cross_type_response_collision_falsifier=True,
                  malformed_path_controls=malformed,
                  checkpoint_word=[0, 1], bottom_code_distance='1/2', radius='2/5',
                  all_checks_passed=True)
    text = json.dumps(result, indent=2) + '\n'
    Path(__file__).with_name('CONTROLS.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
