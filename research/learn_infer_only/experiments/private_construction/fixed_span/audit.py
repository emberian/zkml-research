#!/usr/bin/env python3
"""Positive fixed-span correctness, equivalence and deployment audit only."""
from __future__ import annotations

from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import tempfile

from span import CT_BYTES, INPUT_BOUND, OUTPUT_BOUND, WINDOW, Y, ip

HERE = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_trace(rows):
    result = []
    for end in range(1, len(rows) + 1):
        window = rows[max(0, end - WINDOW):end]
        total = tuple(sum(row[i] for row in window) for i in range(3))
        scores = [sum(a * b for a, b in zip(total, y)) for y in Y]
        assert all(-OUTPUT_BOUND <= score <= OUTPUT_BOUND for score in scores)
        result.append({"step": end, "window_items": len(window), "scores": scores,
                       "class": int(scores[1] > scores[0])})
    return result


def main():
    results_dir = HERE / "results"
    results_dir.mkdir(exist_ok=True)
    states = tuple(itertools.product(range(-INPUT_BOUND, INPUT_BOUND + 1), repeat=3))
    groups = defaultdict(list)
    for state in states:
        groups[tuple(sum(a * b for a, b in zip(state, y)) for y in Y)].append(state)
    equivalence_checks = 0
    equivalent_ordered_pairs = 0
    for left in states:
        for right in states:
            difference = tuple(b - a for a, b in zip(left, right))
            same_outputs = all(sum(d * y for d, y in zip(difference, vector)) == 0 for vector in Y)
            in_kernel = difference == (difference[0], -difference[0], difference[0])
            assert same_outputs == in_kernel
            equivalence_checks += 1
            equivalent_ordered_pairs += int(same_outputs)
    rows_left = [[t % 3 - 1, 1 + t % 2, 1 - t % 3] for t in range(12)]
    rows_right = [[a + 1, b - 1, c + 1] for a, b, c in rows_left]
    reference = expected_trace(rows_left)
    assert reference == expected_trace(rows_right)
    assert len({tuple(row["scores"]) for row in reference}) > 1
    assert {row["class"] for row in reference} == {0, 1}
    commands = []
    process_logs = []
    source = HERE / "span.py"
    with tempfile.TemporaryDirectory(prefix="fixed-span-positive-") as temp:
        root = Path(temp)
        setup_dir = root / "setup"
        command = [sys.executable, "-I", "-B", str(source), "setup", "--output", str(setup_dir)]
        process = subprocess.run(command, text=True, capture_output=True, check=True)
        assert not process.stdout and not process.stderr
        commands.append(command)
        assert {p.name for p in setup_dir.iterdir()} == {"public.bin", "projection_keys.bin"}
        assert (setup_dir / "public.bin").stat().st_size == 768
        assert (setup_dir / "projection_keys.bin").stat().st_size == 512
        setup_inventory = {p.name: {"bytes": p.stat().st_size, "sha256": sha(p)} for p in setup_dir.iterdir()}
        all_traces = []
        issue_samples = []
        checkpoint_sizes = []
        ciphertext_bytes = 0
        for label, rows in (("left", rows_left), ("right", rows_right)):
            combined = []
            checkpoint = None
            for phase in range(2):
                stream = root / f"{label}-{phase}.ct"
                private_benchmark = root / f"{label}-{phase}-private-benchmark.json"
                command = [sys.executable, "-I", "-B", str(source), "issue",
                           "--public", str(setup_dir / "public.bin"), "--output", str(stream),
                           "--benchmark-log", str(private_benchmark)]
                process = subprocess.run(command, input=json.dumps({"rows": rows[6 * phase:6 * phase + 6]}),
                                         text=True, capture_output=True, check=True)
                assert not process.stderr
                issue_log = json.loads(process.stdout)
                assert issue_log["records"] == 6 and issue_log["bytes"] == 6 * CT_BYTES
                assert set(issue_log) == {"records", "bytes"}
                issue_samples.extend(json.loads(private_benchmark.read_text())["encryption_ns_samples"])
                ciphertext_bytes += issue_log["bytes"]
                commands.append(command)
                process_logs.append({"role": "public-only issuer", "label": label, "phase": phase,
                                     "stdout": issue_log})
                output = root / f"{label}-{phase}.window"
                command = [sys.executable, "-I", "-B", str(source), "run",
                           "--keys", str(setup_dir / "projection_keys.bin"), "--input", str(stream),
                           "--output", str(output)]
                if checkpoint is not None:
                    command += ["--checkpoint", str(checkpoint)]
                process = subprocess.run(command, text=True, capture_output=True, check=True)
                assert not process.stderr
                run_log = json.loads(process.stdout)
                assert run_log["checkpoint_bytes"] == 5140
                combined.extend(run_log["trace"])
                checkpoint_sizes.append(run_log["checkpoint_bytes"])
                commands.append(command)
                process_logs.append({"role": "fixed-key evaluator", "label": label, "phase": phase,
                                     "stdout": run_log})
                checkpoint = output
            visible = [{key: row[key] for key in ("step", "window_items", "scores", "class")} for row in combined]
            assert visible == reference
            assert sum(row["expired_exact_old_ciphertext"] for row in combined) == 8
            assert all(row["aggregate_bytes_equal_current_queue_product"] for row in combined)
            all_traces.append(combined)
        # These are disposable synthetic deployment bytes, not retained real-user
        # credentials. Save a replayable positive fixture from the second stream.
        for name in ("public.bin", "projection_keys.bin"):
            (results_dir / name).write_bytes((setup_dir / name).read_bytes())
        (results_dir / "synthetic_final.window").write_bytes(checkpoint.read_bytes())
    measurements = {"public_encryption_ns_median": statistics.median(issue_samples)}
    for metric in ("validation_ns", "update_ns", "two_read_ns"):
        measurements[metric + "_median"] = statistics.median(row[metric] for trace in all_traces for row in trace)
    pdf = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/017.pdf")
    report = {"status": "PASS", "scope": "positive fixed-span reference; no recovery/extraction experiments",
              "dimension": 3, "projection_vectors": Y, "rank": 2, "kernel_generator": [1, -1, 1],
              "input_coordinate_interval": [-INPUT_BOUND, INPUT_BOUND], "window": WINDOW,
              "integer_readout_interval": [-OUTPUT_BOUND, OUTPUT_BOUND],
              "bounded_input_states": len(states), "observable_classes": len(groups),
              "ordered_equivalence_checks": equivalence_checks,
              "equivalent_ordered_pairs_including_diagonal": equivalent_ordered_pairs,
              "synthetic_left_history": rows_left, "synthetic_right_history": rows_right,
              "expected_visible_trace_both_histories": reference,
              "actual_fixed_projection_outputs_compared": 48,
              "exact_queue_product_checks": 24, "normal_checkpoint_continuations": 2,
              "exact_old_ciphertext_expirations": 16, "ciphertext_traffic_both_histories_bytes": ciphertext_bytes,
              "active_window_ciphertext_bytes": WINDOW * CT_BYTES,
              "aggregate_ciphertext_bytes": CT_BYTES, "framed_checkpoint_bytes": checkpoint_sizes[0],
              "setup_export_inventory": setup_inventory,
              "initializer_finished_before_public_issuer": True,
              "public_issuer_has_no_projection_keys_or_master_argument": True,
              "private_issuer_timing_diagnostics_not_deployed": True,
              "master_or_input_coin_erasure_verified": False,
              "measurements": measurements, "process_commands": commands, "process_logs": process_logs,
              "environment": {"python": sys.version, "platform": platform.platform()},
              "source_manifest": {"paper_path": str(pdf), "paper_sha256": sha(pdf),
                                  "paper_access": "Fig2 pp6-7; Constr3.1/Thm3.2 pp7-9 and generic-proof norm remark inspected",
                                  "approved_control_sha256": sha(HERE.parent / "additive_ipfe.py"),
                                  "span_source_sha256": sha(source), "audit_source_sha256": sha(Path(__file__))},
              "search_queries": 0}
    (results_dir / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("status", "bounded_input_states", "observable_classes",
                                                  "ordered_equivalence_checks", "actual_fixed_projection_outputs_compared",
                                                  "exact_queue_product_checks", "exact_old_ciphertext_expirations",
                                                  "framed_checkpoint_bytes", "measurements")}, indent=2))


if __name__ == "__main__":
    main()
