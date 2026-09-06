#!/usr/bin/env python3
"""Finite ideal-interface distributions; no cryptography or private inputs."""
from collections import Counter
from itertools import product, combinations
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent


def world(secret, seed):
    return seed, seed ^ secret


def advance(state, action):
    x, y = state
    if action == 0:
        return 1 - x, y
    if action == 1:
        return x, 1 - y
    if action == 2:
        return y, x
    raise ValueError(action)


def run(state, actions):
    for action in actions:
        state = advance(state, action)
    return state


def main():
    policies = observations = event_checks = 0
    per_length = []
    postprocessors = list(product((0, 1), repeat=2))
    for length in range(6):
        length_count = 0
        for actions in product(range(3), repeat=length):
            for coordinate in range(2):
                for post in postprocessors:
                    outcomes = [Counter(post[run(world(secret, seed), actions)[coordinate]]
                                        for seed in range(2)) for secret in range(2)]
                    assert outcomes[0] == outcomes[1] == Counter(post)
                    for event in postprocessors:
                        masses = [sum(n for value, n in distribution.items() if event[value])
                                  for distribution in outcomes]
                        assert masses[0] == masses[1]
                        event_checks += 1
                    policies += 1
                    length_count += 1
                    observations += 4
        per_length.append({"public_updates": length, "policies": length_count})

    supports = [{world(secret, seed) for seed in range(2)} for secret in range(2)]
    assert supports[0].isdisjoint(supports[1])
    for secret in range(2):
        assert all((x ^ y) == secret for x, y in supports[secret])
    separators = []
    for left, right in combinations(product(range(2), repeat=2), 2):
        coordinate = next(i for i in range(2) if left[i] != right[i])
        separators.append({"left": left, "right": right, "coordinate": coordinate})
    two_read = [[world(secret, seed)[0] ^ world(secret, seed)[1] for seed in range(2)]
                for secret in range(2)]
    assert two_read == [[0, 0], [1, 1]]
    report = {
        "label": "EXECUTED finite distributional nonvacuity control",
        "command": [sys.executable, str(Path(__file__).resolve())],
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "contract": "Public flips/swaps, one coordinate observation, arbitrary Boolean postprocessing; fair seed; no other leakage",
        "checked_public_update_lengths": [0, 1, 2, 3, 4, 5],
        "policies": policies,
        "sampled_transcripts": observations,
        "equal_event_count_checks": event_checks,
        "per_length": per_length,
        "disjoint_supports": [sorted(s) for s in supports],
        "every_distinct_point_pair_separable": separators,
        "two_read_secret_outputs": two_read,
        "not_claimed": ["encryption implementation", "arbitrary hidden side channels", "one-read privacy with two reads", "statistical equality merely from point-pair tests"],
    }
    (HERE / "distribution_audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["label", "policies", "sampled_transcripts", "equal_event_count_checks", "two_read_secret_outputs"]}, indent=2))


if __name__ == "__main__":
    main()
