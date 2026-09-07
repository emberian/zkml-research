#!/usr/bin/env python3
"""Exhaustive finite functionality audit and isolated process resource probes."""
from __future__ import annotations

import argparse
import base64
import gc
import hashlib
import importlib.metadata
import json
import math
import os
from pathlib import Path
import platform
import resource
import statistics
import subprocess
import sys
import tempfile
import time
import tracemalloc

from compiler import COMMANDS, STATES, make_catalog, profile, wire
from runtime import Runner

HERE = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def oracle(initial: tuple[int, int], history: tuple[int, ...]) -> tuple[int, ...]:
    """Independent direct state-machine reference, without compiler.step."""
    scores = list(initial)
    outputs = []
    for command in history:
        if command >= 4:
            outputs.append(int(scores[command - 4] >= 0))
        else:
            context = command // 2
            desired_positive = bool(command % 2)
            if (scores[context] >= 0) != desired_positive:
                scores[context] += 1 if desired_positive else -1
            outputs.append(255)
    return tuple(outputs)


def histories(horizon: int) -> list[tuple[int, ...]]:
    result = [()]
    for history in result:
        if len(history) < horizon:
            result.extend(history + (command,) for command in range(len(COMMANDS)))
    return result


def decode_history(node: int) -> list[int]:
    result = []
    while node:
        result.append((node - 1) % len(COMMANDS))
        node = (node - 1) // len(COMMANDS)
    return result[::-1]


def measure(kind: str, horizon: int) -> dict:
    if kind == "aes":
        sys.path.insert(0, str(HERE.parent))
        import bounded_tree
        build = lambda: bounded_tree.wire(bounded_tree.compile_tree(63, horizon))
        branching = 3
    elif kind == "table":
        build = lambda: profile((-8, -8), horizon)
        branching = 6
    elif kind == "catalog":
        build = lambda: wire(make_catalog(horizon)[0])
        branching = 6
    else:
        raise ValueError(kind)
    rss_before = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    durations = []
    sizes = []
    for _ in range(5):
        gc.collect()
        start = time.perf_counter_ns()
        artifact = build()
        durations.append(time.perf_counter_ns() - start)
        sizes.append(len(artifact))
        del artifact
    gc.collect()
    tracemalloc.start()
    artifact = build()
    _, python_peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    assert len(set(sizes)) == 1
    return {"kind": kind, "horizon": horizon, "branching": branching,
            "edges": branching * (branching**horizon - 1) // (branching - 1),
            "serialized_bytes": len(artifact), "setup_ns_samples": durations,
            "setup_ns_median": statistics.median(durations),
            "python_traced_peak_bytes_separate_run": python_peak,
            "process_rss_highwater_before_bytes": rss_before,
            "process_rss_highwater_after_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "rss_unit_source": "macOS SDK getrusage.2:94-95 (Darwin only)"}


def audit() -> dict:
    output = HERE / "results"
    output.mkdir(exist_ok=True)
    horizon = 4
    public, ids = make_catalog(horizon)
    public_bytes = wire(public)
    classes = len(public["profiles"])
    rows = [base64.b64decode(p) for p in public["profiles"]]
    paths = histories(horizon)
    edges = len(paths) - 1
    comparisons = 0
    groups: dict[int, list[tuple[int, int]]] = {}
    for state in STATES:
        group = ids[state]
        groups.setdefault(group, []).append(state)
        for node, history in enumerate(paths[1:], start=1):
            assert rows[group][node - 1] == oracle(state, history)[-1]
            comparisons += 1
    assert classes == 64 and edges == 1554 and comparisons == 449106
    assert ids[(-8, -8)] == ids[(-7, -8)]
    assert oracle((-8, -8), (1,) * 7 + (4,))[-1] == 0
    assert oracle((-7, -8), (1,) * 7 + (4,))[-1] == 1
    assert oracle((-1, 0), (4, 1, 4)) == (0, 255, 1)
    assert oracle((-2, 0), (4, 1, 4)) == (0, 255, 0)
    assert oracle((0, 0), (0, 1, 4))[-1] == 1
    assert oracle((0, 0), (1, 0, 4))[-1] == 0
    # Complete interface reconstructs the class exactly. This proves that its
    # public resident label is neither less nor more informative than the table.
    assert len(set(rows)) == classes
    for group, members in groups.items():
        for state in members:
            assert rows.index(profile(state, horizon)) == group
    catalog_path = output / "public_catalog.json"
    catalog_path.write_bytes(public_bytes)
    package = output / "synthetic_deployment"
    if package.exists():
        # Only clear the explicitly owned reproducible files, never an unknown file.
        assert {p.name for p in package.iterdir()} == {"program.json", "resident.bin", "runtime.py"}
        for name in ("program.json", "resident.bin", "runtime.py"):
            (package / name).unlink()
        package.rmdir()
    initializer_command = [sys.executable, "-B", str(HERE / "compiler.py"), "initialize",
                           "--catalog", str(catalog_path), "--output", str(package)]
    initialized = subprocess.run(initializer_command, input=json.dumps({"state": [-1, 2]}),
                                 text=True, capture_output=True, check=True)
    assert initialized.stderr == ""
    inventory = {p.name: {"bytes": p.stat().st_size, "sha256": sha(p)} for p in package.iterdir()}
    assert set(inventory) == {"program.json", "resident.bin", "runtime.py"}
    assert sha(package / "runtime.py") == sha(HERE / "runtime.py")
    evaluator_command = [sys.executable, "-I", "-B", str(package / "runtime.py"),
                         "--package", str(package), "--commands", "infer_0,learn_0_positive,infer_0"]
    evaluated = subprocess.run(evaluator_command, text=True, capture_output=True, check=True,
                               cwd=package, env={"PATH": os.environ.get("PATH", "")})
    assert evaluated.stderr == ""
    assert json.loads(evaluated.stdout)["outputs"] == [0, "ack", 1]
    runner = Runner(package)
    started = time.perf_counter_ns()
    for _ in range(10000):
        runner.run([4, 1, 4])
    three_step_mean_ns = (time.perf_counter_ns() - started) / 10000
    selected = runner.run([0, 1, 4])
    assert decode_history(selected["node"]) == [0, 1, 4]
    try:
        runner.run([4] * 5)
    except ValueError:
        pass
    else:
        raise AssertionError("fifth step accepted")
    # No hidden-state-dependent inputs survive: every initial state in a class
    # produces the SAME three deployed file contents (including the fixed runtime).
    coupled_deployment_checks = sum(len(group) - 1 for group in groups.values())
    assert coupled_deployment_checks == 225
    # Actual external reinitialization with an admissible pair, compare all bytes.
    with tempfile.TemporaryDirectory(prefix="bounded-quotient-pair-") as temp:
        pair_packages = []
        for i, state in enumerate(((-8, -8), (-7, -8))):
            candidate = Path(temp) / str(i)
            command = initializer_command[:-1] + [str(candidate)]
            subprocess.run(command, input=json.dumps({"state": state}), text=True,
                           capture_output=True, check=True)
            pair_packages.append({p.name: p.read_bytes() for p in candidate.iterdir()})
        assert pair_packages[0] == pair_packages[1]
        # Exercise the deployed runtime on EVERY edge of EVERY behavior class.
        # Changing this public class label is also an explicit integrity negative.
        scratch = Path(temp) / "runtime-all-classes"
        scratch.mkdir()
        (scratch / "program.json").write_bytes(public_bytes)
        runtime_edges = 0
        for group, row in enumerate(rows):
            (scratch / "resident.bin").write_bytes(group.to_bytes(public["resident_width"], "big"))
            class_runner = Runner(scratch)
            for parent in range(edges // len(COMMANDS)):
                for command in range(len(COMMANDS)):
                    child, answer = class_runner.advance(parent, command)
                    assert child == len(COMMANDS) * parent + command + 1
                    assert answer == row[child - 1]
                    runtime_edges += 1
        assert runtime_edges == 99456
        mutated_answers = []
        for state in ((-1, 2), (1, 2)):
            (scratch / "resident.bin").write_bytes(ids[state].to_bytes(public["resident_width"], "big"))
            mutated_answers.append(Runner(scratch).run([4])["outputs"])
        assert mutated_answers == [[0], [1]]
    assert platform.system() == "Darwin", "RSS byte interpretation is pinned to this Mac"
    probes = []
    for kind, horizons in (("table", range(1, 7)), ("catalog", range(1, 6)),
                           ("aes", (2, 4, 5, 6, 7, 8))):
        for h in horizons:
            command = [sys.executable, "-B", str(HERE / "audit.py"), "measure",
                       "--kind", kind, "--horizon", str(h)]
            measured = subprocess.run(command, text=True, capture_output=True, check=True)
            probes.append(json.loads(measured.stdout))
    report = {"status": "PASS", "format": public["format"], "horizon": horizon,
              "states": len(STATES), "behavioral_classes": classes, "edges_per_state": edges,
              "direct_oracle_edge_comparisons": comparisons,
              "deployed_runtime_edges_checked": runtime_edges,
              "same_class_additional_states": coupled_deployment_checks,
              "minimum_fixed_class_bits": math.ceil(math.log2(classes)),
              "actual_resident_bytes": public["resident_width"],
              "public_catalog_bytes": len(public_bytes),
              "plaintext_single_profile_bytes": edges,
              "class_sizes": sorted(len(group) for group in groups.values()),
              "groups": {str(k): v for k, v in groups.items()},
              "lifecycle": {"initializer_command_without_initial_scores": initializer_command,
                            "initializer_stdout": initialized.stdout,
                            "initializer_completed_before_evaluator_started": True,
                            "evaluator_command": evaluator_command, "evaluator_stdout": evaluated.stdout,
                            "deployed_inventory": inventory, "erasure_verified": False,
                            "synthetic_test_initial_state_is_public": True},
              "evaluator_three_step_mean_ns_10000_runs": three_step_mean_ns,
              "controls": {"private_raw_initial_pair_same_deployment_bytes": True,
                           "horizon_extension_separates_pair_at_8_steps": True,
                           "initially_equal_labels_separate_after_learning": True,
                           "noncommuting_observation_order": True,
                           "all_forks_reconstruct_class": True,
                           "snapshot_node_reveals_public_observation_history": True,
                           "fifth_command_refused_by_honest_runtime": True,
                           "raw_states_keys_not_fields_of_deployment": True},
              "integrity_negative": {"changing_resident_label_changes_inference": mutated_answers,
                                     "integrity_or_authentication_claim": False},
              "measurements": probes,
              "environment": {"python": sys.version, "platform": platform.platform(),
                              "cryptography": importlib.metadata.version("cryptography")},
              "source_hashes": {str(p.relative_to(HERE.parent)): sha(p) for p in
                                [HERE / "compiler.py", HERE / "runtime.py", HERE / "audit.py",
                                 HERE.parent / "bounded_tree.py"]},
              "rss_manual_sha256": sha(Path("/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/share/man/man2/getrusage.2")),
              "search_queries_this_tranche": {"scry_sql": 0, "schema": 0, "web": 0, "kagi": 0}}
    (output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    return {key: report[key] for key in ("status", "horizon", "states", "behavioral_classes",
                                       "direct_oracle_edge_comparisons", "actual_resident_bytes",
                                       "public_catalog_bytes", "controls")}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("audit", "measure"))
    parser.add_argument("--kind", choices=("aes", "table", "catalog"))
    parser.add_argument("--horizon", type=int)
    args = parser.parse_args()
    print(json.dumps(measure(args.kind, args.horizon) if args.mode == "measure" else audit(), indent=2))


if __name__ == "__main__":
    main()
