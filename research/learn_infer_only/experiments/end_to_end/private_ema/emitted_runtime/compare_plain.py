#!/usr/bin/env python3
"""[DERIVED] Independent integer-oracle checks of the emitted Rust schedule loop.

No cryptographic execution. Fixture inputs are public synthetic research data.
Full interpreter stdout is retained losslessly compressed under reports/plain.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[3]
FORMAL = RESEARCH / "formal/private_address_ema/emitted_schedule"
BINARY = HERE / "target/release/resident-emitted-bool-runtime"
TRANSITIONS = HERE.parent / "utility/transitions.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def bits(value, width=8):
    return [bool((value >> i) & 1) for i in range(width)]


def state_bits(state):
    return [bit for value in state for bit in bits(value)]


def signed(byte):
    return ((byte + 128) % 256) - 128


def invoke(name, argv, report):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    process = subprocess.run([str(x) for x in argv], capture_output=True, cwd=HERE)
    (report / f"{name}.stdout.json.gz").write_bytes(gzip.compress(process.stdout, mtime=0))
    (report / f"{name}.stderr.txt").write_bytes(process.stderr)
    metadata = {"claim": "EXECUTED", "argv": [str(x) for x in argv], "cwd": str(HERE),
                "started_utc": start, "returncode": process.returncode,
                "stdout_sha256": digest(process.stdout), "stdout_bytes": len(process.stdout),
                "stderr_sha256": digest(process.stderr)}
    (report / f"{name}.command.json").write_text(json.dumps(metadata, indent=2) + "\n")
    if process.returncode:
        raise RuntimeError(f"{name} failed; see saved stderr and command")
    return json.loads(process.stdout)


def main():
    report = HERE / "reports/plain"
    scratch = HERE / "runs/plain"
    report.mkdir(parents=True, exist_ok=False)
    scratch.mkdir(parents=True, exist_ok=False)
    schedules = {op: FORMAL / f"artifacts/{op}.json" for op in ["learn", "infer"]}
    source_pins = {str(p): digest(p.read_bytes()) for p in [Path(__file__), BINARY, TRANSITIONS, *schedules.values()]}
    validation = {op: invoke(f"validate_{op}", [BINARY, "validate", path], report)
                  for op, path in schedules.items()}
    transitions = json.loads(TRANSITIONS.read_text())
    learn_rows, learn_expected, groups = [], [], {}
    infer_rows, infer_expected = [], []

    def learn(state, address, label):
        expected = state.copy()
        expected[address] = (7 * state[address] + label) // 8
        assert all(-128 <= value <= 127 for value in expected)
        learn_rows.append(state_bits(state) + bits(address, 2) + bits(label))
        learn_expected.append(state_bits(expected))
        return expected

    for transition in transitions:
        route = transition["route"]
        expected = learn(transition["state_before"][route], transition["bin"], transition["u"])
        assert expected == transition["state_after"][route], "saved fixture differs from integer oracle"
        for address in range(4):
            infer_rows.append(state_bits(expected) + bits(address, 2))
            infer_expected.append([expected[address] < 0])
    groups["saved_utility_transitions"] = len(transitions)

    start = len(learn_rows)
    for selected in range(-128, 128):
        for address in range(4):
            state = [signed(selected + 73 * j) for j in range(4)]
            state[address] = selected
            for label in [-120, 120]:
                learn(state, address, label)
    groups["all_selected_signed_byte_states_x_two_labels_x_four_addresses"] = len(learn_rows) - start

    start = len(learn_rows)
    selected_edges = [-128, -127, -121, -120, -1, 0, 1, 119, 120, 126, 127]
    for selected in selected_edges:
        for address in range(4):
            state = [signed(selected + 73 * j) for j in range(4)]
            state[address] = selected
            for label in range(-128, 128):
                learn(state, address, label)
    groups["eleven_selected_boundary_states_x_all_signed_byte_labels_x_four_addresses"] = len(learn_rows) - start

    results = {}
    for op, rows, expected in [("learn", learn_rows, learn_expected), ("infer", infer_rows, infer_expected)]:
        path = scratch / f"{op}_inputs.json"
        payload = json.dumps(rows, separators=(",", ":")).encode() + b"\n"
        path.write_bytes(payload)
        actual = invoke(op, [BINARY, "clear", schedules[op], path], report)
        got = actual["outputs"]
        mismatch = [i for i, (a, b) in enumerate(zip(got, expected)) if a != b]
        match = len(got) == len(expected) and not mismatch
        results[op] = {"rows": len(rows), "output_bits_per_row": len(expected[0]),
                       "matched": match, "first_mismatch_indices": mismatch[:20],
                       "output_rows": len(got), "input_sha256": digest(payload),
                       "input_bytes": len(payload),
                       "expected_sha256": digest(json.dumps(expected, separators=(",", ":")).encode())}
    summary = {"claim": "EXECUTED", "scope": "public plain Boolean interpreter vs independent Python signed-integer oracle",
               "source_pins": source_pins, "validation": validation, "learn_groups": groups,
               "infer_group": "all four addresses for each saved selected-route post-transition state",
               "results": results, "cryptographic_execution": False,
               "all_matched": all(r["matched"] for r in results.values()),
               "universal_rust_or_tfhe_proof": False}
    (report / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if not summary["all_matched"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
