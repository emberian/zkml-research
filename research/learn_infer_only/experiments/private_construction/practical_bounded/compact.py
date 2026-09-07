#!/usr/bin/env python3
"""Compact visible observational abstraction, not encrypted raw model state."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

COMMANDS = ("learn_0_negative", "learn_0_positive", "learn_1_negative",
            "learn_1_positive", "infer_0", "infer_1")
FORMAT = "bounded-mistake-learner-compact-quotient-v1"


def normalize(scores: tuple[int, int], remaining: int) -> tuple[int, int]:
    if remaining == 0:
        return (0, 0)
    return tuple(max(-remaining, min(remaining - 1, score)) for score in scores)


def initialize(scores: tuple[int, int], horizon: int) -> dict:
    if type(horizon) is not int or not 0 <= horizon <= 12:
        raise ValueError("supported horizon is 0..12")
    if len(scores) != 2 or any(type(w) is not int or not -8 <= w <= 8 for w in scores):
        raise ValueError("initial scores must be integers -8..8")
    return {"format": FORMAT, "remaining": horizon, "scores": list(normalize(scores, horizon))}


def advance(capability: dict, command: int) -> tuple[dict, int]:
    if capability["format"] != FORMAT:
        raise ValueError("invalid program")
    remaining = capability["remaining"]
    if type(remaining) is not int or not 1 <= remaining <= 12:
        raise ValueError("horizon exhausted or invalid")
    scores = capability["scores"]
    if len(scores) != 2 or any(type(w) is not int for w in scores):
        raise ValueError("invalid public representative")
    if tuple(scores) != normalize(tuple(scores), remaining):
        raise ValueError("representative is not normalized")
    if type(command) is not int or not 0 <= command < 6:
        raise ValueError("invalid public command")
    scores = list(scores)
    if command < 4:
        context, label = command // 2, 2 * (command % 2) - 1
        if (1 if scores[context] >= 0 else -1) != label:
            scores[context] += label
        answer = 255
    else:
        answer = int(scores[command - 4] >= 0)
    return {"format": FORMAT, "remaining": remaining - 1,
            "scores": list(normalize(tuple(scores), remaining - 1))}, answer


def wire(value: dict) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def audit() -> dict:
    # Audit-only dependencies. Neither initialization nor runtime imports them.
    from compiler import STATES, make_catalog, step
    from audit import histories, oracle
    here = Path(__file__).resolve().parent
    algebra = 0
    for remaining in range(1, 13):
        for initial in STATES:
            current = initialize(initial, remaining)
            for command in range(6):
                successor, answer = advance(current, command)
                raw_next, raw_answer = step(initial, command)
                assert answer == raw_answer
                assert successor == initialize(raw_next, remaining - 1)
                algebra += 1
    _, class_ids = make_catalog(4)
    equivalence_checks = 0
    for left in STATES:
        for right in STATES:
            assert (initialize(left, 4) == initialize(right, 4)) == (class_ids[left] == class_ids[right])
            equivalence_checks += 1
    paths = histories(4)
    runtime_edges = 0
    start = time.perf_counter_ns()
    for initial in STATES:
        capabilities = [initialize(initial, 4)]
        for child, history in enumerate(paths[1:], start=1):
            parent, command = (child - 1) // 6, (child - 1) % 6
            nxt, answer = advance(capabilities[parent], command)
            capabilities.append(nxt)
            assert answer == oracle(initial, history)[-1]
            runtime_edges += 1
    elapsed = time.perf_counter_ns() - start
    assert runtime_edges == 449106
    assert initialize((-8, -2), 4) == initialize((-7, -2), 4)
    extension_outputs = []
    for initial in ((-8, -2), (-7, -2)):
        current = initialize(initial, 8)
        for command in [1] * 7 + [4]:
            current, answer = advance(current, command)
        extension_outputs.append(answer)
    assert extension_outputs == [0, 1]
    forged_extension = initialize((-8, -2), 4)
    forged_extension["remaining"] = 8
    for command in [1] * 7 + [4]:
        forged_extension, answer = advance(forged_extension, command)
    assert answer == 1  # The lost initial confidence cannot be recovered by a counter edit.
    resident_path = here / "results" / "compact_resident.json"
    initializer_command = [sys.executable, "-I", "-B", str(Path(__file__).resolve()), "initialize",
                           "--horizon", "4", "--output", str(resident_path)]
    initialized = subprocess.run(initializer_command, input=json.dumps({"state": [-8, -2]}),
                                 text=True, capture_output=True, check=True)
    assert not initialized.stdout and not initialized.stderr
    evaluator_command = [sys.executable, "-I", "-B", str(Path(__file__).resolve()), "run",
                         "--resident", str(resident_path), "--commands",
                         "infer_1,learn_1_positive,learn_1_positive,infer_1"]
    evaluated = subprocess.run(evaluator_command, text=True, capture_output=True, check=True)
    assert not evaluated.stderr
    assert json.loads(evaluated.stdout)["outputs"] == [0, "ack", "ack", 1]
    report = {"status": "PASS", "local_transition_commutation_cases": algebra,
              "horizons_checked": list(range(1, 13)), "initial_states": 289,
              "ordered_H4_pair_equivalence_checks": equivalence_checks,
              "H4_direct_oracle_runtime_edges": runtime_edges,
              "full_runtime_edge_audit_ns": elapsed,
              "H4_classes": 64, "minimum_fixed_initial_class_bits": 6,
              "actual_json_resident_bytes": resident_path.stat().st_size,
              "public_runtime_source_bytes": Path(__file__).stat().st_size,
              "resident": json.loads(resident_path.read_bytes()),
              "outside_H4_legitimate_H8_pair_outputs": extension_outputs,
              "naive_H4_to_H8_counter_extension_wrong_output": answer,
              "initializer_command": initializer_command, "evaluator_command": evaluator_command,
              "evaluator_stdout": evaluated.stdout,
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "erasure_verified": False,
              "no_encryption_or_hidden_original_scores": True,
              "search_queries": 0}
    (here / "results" / "compact_results.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    sub.add_parser("audit")
    initialize_parser = sub.add_parser("initialize")
    initialize_parser.add_argument("--horizon", type=int, required=True)
    initialize_parser.add_argument("--output", type=Path, required=True)
    runtime_parser = sub.add_parser("run")
    runtime_parser.add_argument("--resident", type=Path, required=True)
    runtime_parser.add_argument("--commands", required=True)
    args = parser.parse_args()
    if args.mode == "audit":
        print(json.dumps(audit(), indent=2))
    elif args.mode == "initialize":
        args.output.write_bytes(wire(initialize(tuple(json.load(sys.stdin)["state"]), args.horizon)))
    else:
        current = json.loads(args.resident.read_bytes())
        answers = []
        for name in args.commands.split(","):
            command = int(name) if name.isdecimal() else COMMANDS.index(name)
            current, answer = advance(current, command)
            answers.append("ack" if answer == 255 else answer)
        print(json.dumps({"outputs": answers, "remaining": current["remaining"]}, sort_keys=True))


if __name__ == "__main__":
    main()
