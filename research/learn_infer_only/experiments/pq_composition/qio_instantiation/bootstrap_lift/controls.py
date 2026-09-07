#!/usr/bin/env python3
"""Finite algebra and plaintext function controls; not a cryptographic proof checker."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    counts = {}
    # Mock pad values merely enumerate possible values of a PRG output. Nothing
    # here instantiates FE or asserts that the mock generator is pseudorandom.
    cases = 0
    for width in range(1, 8):
        for y in range(1 << width):
            for pad in range(1 << width):
                c = y ^ pad
                for position in range(width):
                    real = (y >> position) & 1
                    fake = ((c ^ pad) >> position) & 1
                    assert real == fake
                    cases += 1
    counts['single_boolean_key_per_position_compatibility_cases'] = cases

    cases = 0
    for n in range(25):
        for r in (Fraction(0), Fraction(1, 997), Fraction(3, 83)):
            for g in (Fraction(0), Fraction(1, 1193), Fraction(2, 137)):
                recurrence = 2*r
                for _ in range(n):
                    recurrence = 2*r + 2*g + 2*recurrence
                closed = ((1 << (n+2))-2)*r + ((1 << (n+1))-2)*g
                assert recurrence == closed
                cases += 1
        nodes = sum(1 << d for d in range(n+1))
        depth_sum = sum(d*(1 << d) for d in range(n+1))
        assert nodes == (1 << (n+1))-1
        assert depth_sum == (n-1)*(1 << (n+1))+2
        assert nodes+depth_sum == n*(1 << (n+1))+1
    counts['privacy_recurrence_rational_cases'] = cases
    counts['all_node_depth_coefficient_cases'] = 25

    cases = 0
    for s in range(1, 65):
        for lh in range(1, 65):
            # Four base primitive coefficients, ordered B, X, P, G.
            rs = (lh, 0, 0, 2)
            mid = (0, 0, 0, 1)
            rw = (s, 2*s+2, 2*s, 2)
            actual = tuple(sum(v[i] for v in (rs, mid, rw)) for i in range(4))
            assert actual == (lh+s, 2*s+2, 2*s, 5)
            assert sum(actual) == lh+5*s+7
            assert sum(actual) <= 6*max(s,lh)+7
            cases += 1
    counts['encoding_composition_coefficient_cases'] = cases

    # Finite conditional all-node implication, all failure masks for depth <=3.
    # A mock failing decoder signals failure on every path through that node.
    cases = 0
    for n in range(4):
        node_count = (1 << (n+1))-1
        paths = []
        for x in range(1 << n):
            path = [0]
            index = 0
            for depth in range(n):
                bit = (x >> (n-depth-1)) & 1
                index = 2*index+1+bit
                path.append(index)
            paths.append(path)
        for mask in range(1 << node_count):
            any_path_fails = any(any(mask & (1 << node) for node in p) for p in paths)
            any_node_fails = mask != 0
            assert any_path_fails == any_node_fails
            cases += 1
    counts['latent_tree_failure_mask_cases'] = cases

    # Integer fixed-point example beta=1/2: T >= (2A)^2 and 2B.
    cases = 0
    for a in range(1, 33):
        for b in range(0, 33):
            root = max(2*a, b+1)
            time_bound = root*root
            assert a*root+b <= time_bound
            cases += 1
    counts['compactness_fixed_point_cases'] = cases

    # Deliberately insecure generator: three seed bits embedded in eight output
    # bits. A bad-range predicate is rare under uniform tapes, certain under G.
    bad_range = set(range(8))
    uniform_failure = Fraction(len(bad_range), 256)
    generated_failure = Fraction(1)
    prg_gap = generated_failure-uniform_failure
    assert uniform_failure == Fraction(1,32)
    assert generated_failure == uniform_failure+prg_gap
    assert generated_failure > uniform_failure
    countercontrol = {
        'label': 'REFUTED: replacing generated tapes by uniform correctness with no PRG term',
        'uniform_failure': str(uniform_failure),
        'generated_failure': str(generated_failure),
        'efficient_bad_range_PRG_gap': str(prg_gap),
        'scope': 'Deliberately insecure finite generator, not an attack on an assumed secure PRG.'
    }
    result = {'label': 'EXECUTED', 'scope': __doc__, 'counts': counts,
              'pseudorandom_tape_countercontrol': countercontrol,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'controls.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
