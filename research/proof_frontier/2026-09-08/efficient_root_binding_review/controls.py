#!/usr/bin/env python3
"""Independent finite mathematics only: no Lean, cryptography, or author imports."""
import itertools
import json
from fractions import Fraction
from pathlib import Path


def semantic_counts(n):
    fixed = either = total = 0
    for leaf in itertools.product(range(n), repeat=2):
        a, b = leaf
        for node in itertools.product(range(n), repeat=n * n):
            total += 1
            root = node[a * n + a]
            left = any(node[b * n + s] == root for s in range(n))
            right = any(node[s * n + b] == root for s in range(n))
            fixed += left
            either += left or right
    fixed_p, either_p = Fraction(fixed, total), Fraction(either, total)
    assert fixed_p == 1 - Fraction(n - 1, n) ** (n + 1)
    assert either_p == 1 - Fraction(n - 1, n) ** (2 * n)
    return dict(n=n, tables=total, fixed_index_tables=fixed,
                full_double_opening_tables=either,
                fixed_index_probability=str(fixed_p),
                full_double_opening_probability=str(either_p),
                observed_conflicts=0)


def extracted(log, root, bits, default=0):
    digest = root
    for bit in bits:
        match = next((key for key, out in log if key[0] == 'N' and out == digest), None)
        if match is None:
            return default
        digest = match[1 + bit]
    match = next((key for key, out in log if key[0] == 'L' and out == digest), None)
    return default if match is None else match[1]


def query(oracle, key, log, roots, flagged):
    if any(old == key for old, _ in log):
        return oracle[key], flagged
    targets = set(roots)
    targets.update(out for _, out in log)
    for old, _ in log:
        if old[0] == 'N':
            targets.update(old[1:])
    if key[0] == 'N':
        targets.update(key[1:])
    out = oracle[key]
    flagged = flagged or out in targets
    log.append((key, out))
    return out, flagged


def prefix_controls():
    keys = [('L', 0), ('L', 1)] + [('N', x, y) for x in range(2) for y in range(2)]
    prefixes = [()] + list(itertools.product(keys, repeat=1)) + list(itertools.product(keys, repeat=2))
    counts = dict(cases=0, accepted=0, mismatches=0, unflagged_accepted=0,
                  unflagged_mismatches=0, by_depth={str(k): 0 for k in range(3)})
    for table in itertools.product(range(2), repeat=len(keys)):
        oracle = dict(zip(keys, table))
        for prefix in prefixes:
            prefix_log, prefix_bad = [], False
            for key in prefix:
                _, prefix_bad = query(oracle, key, prefix_log, (), prefix_bad)
            checkpoint = tuple(prefix_log)
            for root in range(2):
                for late_query in [None] + keys:
                    before_log, before_bad = list(checkpoint), prefix_bad
                    if late_query is not None:
                        _, before_bad = query(oracle, late_query, before_log, (root,), before_bad)
                    for depth in range(3):
                        for index in range(2 ** depth):
                            bits = tuple((index >> j) & 1 for j in range(depth))
                            expected = extracted(checkpoint, root, bits)
                            for value in range(2):
                                for siblings in itertools.product(range(2), repeat=depth):
                                    counts['cases'] += 1
                                    log, bad = list(before_log), before_bad
                                    digest, bad = query(oracle, ('L', value), log, (root,), bad)
                                    # BinaryMerkle paths are top-down, recomputation is bottom-up.
                                    for bit, sibling in reversed(tuple(zip(bits, siblings))):
                                        children = (digest, sibling) if bit == 0 else (sibling, digest)
                                        digest, bad = query(oracle, ('N', *children), log, (root,), bad)
                                    if digest == root:
                                        mismatch = value != expected
                                        counts['accepted'] += 1
                                        counts['by_depth'][str(depth)] += 1
                                        counts['mismatches'] += mismatch
                                        counts['unflagged_accepted'] += not bad
                                        counts['unflagged_mismatches'] += mismatch and not bad
                                        assert not mismatch or bad
    return counts


def nonvacuity():
    # Different implementation/log than the author's finite-control script.
    log = [(('L', 1), 101), (('L', 4), 104),
           (('N', 101, 104), 201), (('N', 104, 101), 202),
           (('N', 201, 202), 301)]
    oracle = dict(log)
    checked, bad = [], False
    for key, _ in log:
        _, bad = query(oracle, key, checked, (), bad)
    assert not bad
    word = [extracted(log, 301, (i & 1, (i >> 1) & 1)) for i in range(4)]
    assert word == [1, 4, 4, 1]
    distances = [sum(v != (a * x + b) % 5 for x, v in zip(range(1, 5), word))
                 for a in range(5) for b in range(5)]
    distance = Fraction(min(distances), 4)
    assert distance == Fraction(1, 2) > Fraction(2, 5)
    # For w(x)=x^2 on F5*, folding the +/-x pair gives x^2 for every challenge.
    # A pre-query constant terminal word 1 agrees at squared coordinate 1 only.
    accepted = 0
    for challenge in range(5):
        for x in (1, 2):
            v, neg_v = x * x % 5, (-x) * (-x) % 5
            folded = ((v + neg_v) * 3 + challenge * (v - neg_v) * pow(2 * x, -1, 5)) % 5
            accepted += folded == 1
    assert accepted == 5
    return dict(word=word, unflagged=True, affine_words=25,
                minimum_distance=str(distance), accepting_challenge_query_pairs=accepted,
                challenge_query_pairs=10)


def main():
    integer_checks = 0
    for q in range(65):
        for roots in range(33):
            assert sum(3 * t - 1 + roots for t in range(1, q + 1)) == (3 * q * q + q) // 2 + roots * q
            integer_checks += 1
    result = dict(scope='Pure finite mathematics; no cryptographic evaluation or Lean build.',
                  semantic=[semantic_counts(2), semantic_counts(3)],
                  prefix=prefix_controls(), budget_integer_checks=integer_checks,
                  nonvacuity=nonvacuity())
    rendered = json.dumps(result, indent=2) + '\n'
    Path(__file__).with_name('RESULTS.json').write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
