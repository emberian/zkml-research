#!/usr/bin/env python3
"""Independent finite-interface review; no cryptography or source theorem proof."""

import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
COMMANDS = ("add", "double", "infer")


def step(state, command):
    if command == "add":
        return (state + 1) % 256, None
    if command == "double":
        return 2 * state % 256, None
    assert command == "infer"
    return state, state // 128


def relation(left, right, remaining):
    if remaining == 0:
        return left // 128 == right // 128
    for command in COMMANDS:
        next_left, answer_left = step(left, command)
        next_right, answer_right = step(right, command)
        if answer_left != answer_right or not relation(
            next_left, next_right, remaining - 1
        ):
            return False
    return True


def policies():
    # After an update only the ack is observed; after infer there are two branches.
    for first in COMMANDS[:2]:
        for second in COMMANDS:
            yield first, {None: second}
    for zero, one in itertools.product(COMMANDS, repeat=2):
        yield "infer", {0: zero, 1: one}


def trace(state, policy):
    first, continuation = policy
    middle, answer_first = step(state, first)
    second = continuation[answer_first]
    final, answer_second = step(middle, second)
    return first, answer_first, second, answer_second, final // 128


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    all_policies = list(policies())
    assert len(all_policies) == 15
    signatures = {
        state: tuple(trace(state, policy) for policy in all_policies)
        for state in range(256)
    }
    equivalent_pairs = separating_pairs = 0
    for left, right in itertools.combinations(range(256), 2):
        equivalent = signatures[left] == signatures[right]
        assert equivalent == relation(left, right, 2)
        if equivalent:
            equivalent_pairs += 1
        else:
            separating_pairs += 1
            assert any(
                trace(left, policy) != trace(right, policy)
                for policy in all_policies
            )
    classes = {}
    for state, signature in signatures.items():
        classes.setdefault(signature, []).append(state)
    assert len(classes) == 14
    assert classes[signatures[0]] == list(range(32))
    assert signatures[0] == signatures[1]
    # Simultaneously releasing every fork's trace adds no distinction within R0.
    assert all(
        signatures[group[0]] == signatures[state]
        for group in classes.values()
        for state in group
    )
    extra_horizon = next(h for h in range(3, 9) if not relation(0, 1, h))
    assert extra_horizon == 7
    assert trace(63, ("add", {None: "double"}))[-1] == 1
    assert trace(63, ("double", {None: "add"}))[-1] == 0

    lane = ROOT / "experiments/private_construction"
    reported = json.loads((lane / "results/finite_ladder_results.json").read_text())
    assert reported["finite_witness"]["behavioral_classes"] == len(classes)
    assert reported["finite_witness"]["class_containing_zero"] == list(range(32))
    source = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror/2013/729.pdf")
    assert digest(source) == reported["source"]["sha256"]
    output = {
        "classification": "EXECUTED independent exhaustive finite-interface review; not encryption or a proof of the source reduction",
        "adaptive_two_step_policies": len(all_policies),
        "policy_state_transcripts": 256 * len(all_policies),
        "unordered_state_pairs": equivalent_pairs + separating_pairs,
        "equivalent_distinct_pairs": equivalent_pairs,
        "separating_pairs": separating_pairs,
        "classes": list(classes.values()),
        "relation_matches_all_adaptive_and_full_fork_observations": True,
        "pair_0_1_first_separable_horizon": extra_horizon,
        "noncommuting_terminal_bits": [1, 0],
        "source": {
            "path": str(source),
            "sha256": digest(source),
            "root_read": "Definition2.4/Remark2.5 printedp8; section4pp12-14; AppendixCpp24-25 and footnote8",
            "derived_review": [
                "Joint compatibility must retain the shared future package and all issued future keys.",
                "Current MPK/MSK are independently generated after A1; AppendixC footnote8 uses this independence.",
                "All child challenge pairs are computed from setup-independent Step/states before future setup.",
                "Public encryption supplies known-message ciphertexts under the same package in each hybrid.",
                "The conclusion is classical IND-style fixed-horizon privacy under the cited primitive; no concrete encryption was run.",
            ],
            "literal_source_issue": "Figure1 step2 has a signature-test polarity discrepancy; the PQ source audit visually checks it against ObservationA.2. Use the stated theorem/intended reject-on-invalid semantics, not that literal line as runnable code.",
        },
        "reviewed_artifacts": {
            str(path.relative_to(ROOT)): digest(path)
            for path in [
                lane / "FINITE_LADDER.md",
                lane / "finite_ladder.py",
                lane / "finite_ladder.stdout.txt",
                lane / "results/finite_ladder_results.json",
            ]
        },
        "script_sha256": digest(Path(__file__)),
        "searches": {"scry_sql": 0, "schema": 0, "web": 0, "pdf_downloads": 0},
    }
    (HERE / "finite_ladder_review.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: output[k] for k in [
        "adaptive_two_step_policies", "policy_state_transcripts",
        "unordered_state_pairs", "equivalent_distinct_pairs", "separating_pairs",
        "pair_0_1_first_separable_horizon",
    ]}, indent=2))


if __name__ == "__main__":
    main()
