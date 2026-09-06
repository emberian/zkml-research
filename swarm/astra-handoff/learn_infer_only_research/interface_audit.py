#!/usr/bin/env python3
"""Finite-state audits of a 'learn and infer only' interface.

This is NOT encryption, an FE implementation, or an attack on a neural model.
It checks what the specified *ideal interface itself* reveals. A cryptographic
implementation cannot hide information already recoverable from that interface.
Python 3.10+, standard library only. Run: python interface_audit.py
"""
from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path
from typing import Iterable

MODULUS = 256


def infer(state: int) -> int:
    """Return only the most significant bit of an eight-bit state."""
    if not 0 <= state < MODULUS:
        raise ValueError("state must be an unsigned byte")
    return state >> 7


def learn(state: int, offset: int) -> int:
    """An update that returns no observation; use its resulting state internally."""
    return (state + offset) % MODULUS


def canonical_labels(signatures: Iterable[object]) -> list[int]:
    ids: dict[object, int] = {}
    result = []
    for signature in signatures:
        if signature not in ids:
            ids[signature] = len(ids)
        result.append(ids[signature])
    return result


def behavior_partition(allowed_offsets: tuple[int, ...]) -> dict[str, object]:
    """Greatest deterministic observational equivalence on this finite machine.

    Start with states that have equal inference output. Refine until every
    allowed learning action preserves each equivalence class. The fixed point
    gives indistinguishability under *all finite* action sequences, including
    adaptive choices (identical past outputs induce identical choices).
    """
    labels = canonical_labels(infer(s) for s in range(MODULUS))
    refinements = 0
    while True:
        signatures = (
            (infer(s), *(labels[learn(s, a)] for a in allowed_offsets))
            for s in range(MODULUS)
        )
        next_labels = canonical_labels(signatures)
        if next_labels == labels:
            sizes = sorted(Counter(labels).values())
            return {
                "allowed_offsets": list(allowed_offsets),
                "equivalence_classes": len(sizes),
                "class_size_histogram": dict(sorted(Counter(sizes).items())),
                "strict_refinement_iterations": refinements,
            }
        labels = next_labels
        refinements += 1
        if refinements >= MODULUS:
            raise AssertionError("finite partition refinement failed to converge")


def recover_original(initial: int) -> tuple[int, list[dict[str, object]]]:
    """Adaptive chosen-update attack using only learn(a) and infer()."""
    candidates = list(range(MODULUS))
    actual = initial
    cumulative_offset = 0
    trace: list[dict[str, object]] = []
    while len(candidates) > 1:
        # Select the total shift with the most even next-output partition.
        target_offset = min(
            range(MODULUS),
            key=lambda r: abs(
                2 * sum(infer(learn(c, r)) for c in candidates) - len(candidates)
            ),
        )
        update = (target_offset - cumulative_offset) % MODULUS
        actual = learn(actual, update)
        cumulative_offset = target_offset
        observed = infer(actual)
        candidates = [
            c for c in candidates
            if infer(learn(c, cumulative_offset)) == observed
        ]
        trace.append({
            "learn_argument": update,
            "cumulative_offset": cumulative_offset,
            "infer_output": observed,
            "remaining_original_states": len(candidates),
        })
        if len(trace) > 16:
            raise AssertionError("recovery did not converge as expected")
    return candidates[0], trace


def output_routing_checks() -> int:
    """Algebraic check for the unrestricted-evaluation/restricted-release trap.

    With a release oracle O(s)=MSB(s), an unrestricted evaluator can route any
    chosen state bit j into the public output: H_j(s)=128*bit_j(s). This is a
    plaintext check of a reduction. No cryptographic evaluation is implemented.
    """
    total = 0
    for state in range(MODULUS):
        for bit in range(8):
            chosen_bit = (state >> bit) & 1
            routed_state = 128 * chosen_bit
            assert infer(routed_state) == chosen_bit
            total += 1
    return total


def execute(initial: int, history: list[tuple[str, int]]) -> tuple[int, list[int]]:
    state = initial
    outputs: list[int] = []
    for operation, argument in history:
        if operation == "learn":
            state = learn(state, argument)
        elif operation == "infer":
            outputs.append(infer(state))
        elif operation != "noop":
            raise ValueError(f"unknown operation: {operation!r}")
    return state, outputs


def bounded_history_correctness(seed: int = 91703) -> int:
    """Compare online execution with a fixed-horizon history circuit.

    Only functional correctness is checked, NOT an FE security reduction.
    """
    rng = random.Random(seed)
    checks = 0
    for _ in range(30):
        initial = rng.randrange(MODULUS)
        history = [
            ("learn", rng.randrange(MODULUS)) if rng.randrange(3)
            else ("infer", 0)
            for _ in range(32)
        ]
        for prefix_length in range(33):
            prefix = history[:prefix_length]
            padded = prefix + [("noop", 0)] * (32 - prefix_length)
            assert execute(initial, prefix) == execute(initial, padded)
            checks += 1
    return checks


def main() -> None:
    partitions = {
        "infer_only": behavior_partition(()),
        "learn_flip_half": behavior_partition((128,)),
        "learn_increment_one": behavior_partition((1,)),
    }
    assert partitions["infer_only"]["equivalence_classes"] == 2
    assert partitions["learn_flip_half"]["equivalence_classes"] == 2
    assert partitions["learn_increment_one"]["equivalence_classes"] == 256

    lengths = Counter()
    for initial in range(MODULUS):
        recovered, trace = recover_original(initial)
        assert recovered == initial
        lengths[len(trace)] += 1
    assert lengths == {8: 256}
    _, example_trace = recover_original(173)

    results = {
        "scope": "Finite ideal-interface checks; no cryptography or neural model",
        "state_space_size": MODULUS,
        "partitions": partitions,
        "chosen_update_recovery": {
            "tested_initial_states": MODULUS,
            "all_recovered": True,
            "inference_query_count_histogram": dict(lengths),
            "example_original_state": 173,
            "example_trace": example_trace,
        },
        "restricted_release_routing_checks": output_routing_checks(),
        "bounded_history_prefix_checks": bounded_history_correctness(),
        "all_assertions_passed": True,
    }
    path = Path(__file__).resolve().parent / "results.json"
    path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
