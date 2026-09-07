#!/usr/bin/env python3
"""Independent finite backward partition, without the compiler's table routine."""
import hashlib
import importlib.util
import itertools
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "private_construction/practical_bounded"


def raw_step(state, command):
    values = list(state)
    if command >= 4:
        return state, int(values[command - 4] >= 0)
    index = command // 2
    positive = command % 2 == 1
    if positive and values[index] < 0:
        values[index] += 1
    if not positive and values[index] >= 0:
        values[index] -= 1
    return tuple(values), 255


def main():
    spec = importlib.util.spec_from_file_location("reviewed_compact", SOURCE / "compact.py")
    compact = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(compact)
    states = list(itertools.product(range(-8, 9), repeat=2))
    partition = {state: 0 for state in states}
    counts = [1]
    checks = 0
    for horizon in range(1, 13):
        keys = {}
        next_partition = {}
        for state in states:
            signature = tuple((answer, partition[successor]) for successor, answer in
                              (raw_step(state, command) for command in range(6)))
            next_partition[state] = keys.setdefault(signature, len(keys))
        correspondence = {}
        inverse = {}
        for state in states:
            normalized = compact.initialize(state, horizon)
            rep = tuple(normalized["scores"])
            cid = next_partition[state]
            assert correspondence.setdefault(rep, cid) == cid
            assert inverse.setdefault(cid, rep) == rep
            for command in range(6):
                raw_next, expected = raw_step(state, command)
                actual_next, actual = compact.advance(normalized, command)
                assert actual == expected
                assert actual_next == compact.initialize(raw_next, horizon - 1)
                checks += 1
        counts.append(len(keys))
        partition = next_partition
    assert counts == [1, 4, 16, 36, 64, 100, 144, 196, 256, 289, 289, 289, 289]
    runtime = HERE / "runtime/compact_review_001"
    runtime.mkdir(parents=True, exist_ok=False)
    commands = []
    outputs = []
    for i, state in enumerate(([-8, -2], [-7, -2])):
        resident = runtime / f"resident_{i}.json"
        argv = [sys.executable, "-I", "-B", str(SOURCE / "compact.py"), "initialize", "--horizon", "4", "--output", str(resident)]
        done = subprocess.run(argv, input=json.dumps({"state": state}), text=True, capture_output=True, check=True)
        assert not done.stdout and not done.stderr
        commands.append(argv)
        argv = [sys.executable, "-I", "-B", str(SOURCE / "compact.py"), "run", "--resident", str(resident), "--commands", "infer_1,learn_1_positive,learn_1_positive,infer_1"]
        done = subprocess.run(argv, text=True, capture_output=True, check=True)
        outputs.append(json.loads(done.stdout))
        commands.append(argv)
    assert (runtime / "resident_0.json").read_bytes() == (runtime / "resident_1.json").read_bytes()
    assert outputs == [{"outputs": [0, "ack", "ack", 1], "remaining": 0}] * 2
    # Same visible representative, no integrity: changing it changes permitted output.
    resident = compact.initialize((-8, -2), 4)
    resident["scores"][1] = 0
    _, altered_answer = compact.advance(resident, 5)
    assert altered_answer == 1
    report = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "review_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "reviewed_source_sha256": hashlib.sha256((SOURCE / "compact.py").read_bytes()).hexdigest(),
        "reviewed_note_sha256": hashlib.sha256((SOURCE / "COMPACT.md").read_bytes()).hexdigest(),
        "independent_method": "Backward partition refinement by output/successor signatures; does not import compiler.py, catalog, histories or author's oracle.",
        "horizons": list(range(13)), "class_counts": counts,
        "raw_states": len(states), "local_runtime_checks": checks,
        "external_commands": commands, "external_outputs": outputs,
        "admissible_pair_resident_bytes_identical": True,
        "visible_representative_tamper_changes_answer": True,
        "classification": "EXECUTED finite quotient equivalence and real subprocess functionality",
        "scope": "Plaintext functionality-specific bounded quotient, honest private initialization and erasure assumed. No encryption, live hidden raw state, fresh private ingress, integrity or unbounded extension is proved.",
        "passed": True,
    }
    out = HERE / "compact_quotient_review_001.json"
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"record": str(out), "passed": True, "class_counts": counts, "local_runtime_checks": checks}))


if __name__ == "__main__":
    main()
