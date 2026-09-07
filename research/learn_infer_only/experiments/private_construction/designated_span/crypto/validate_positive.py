#!/usr/bin/env python3
"""Read-only normal-artifact validation; private comparison emits only booleans."""
from pathlib import Path
import argparse
import hashlib
import json
import struct
import sys

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, default=HERE / "runtime/positive_001")
    parser.add_argument("--reports", type=Path, default=HERE / "reports/positive_001")
    args = parser.parse_args()
    runtime, reports = args.runtime.resolve(), args.reports.resolve()
    report = json.loads((reports / "report.json").read_text())
    pre = json.loads((reports / "predeclared.json").read_text())
    rows = json.loads((runtime / "source/rows.json").read_text())
    answers = json.loads((runtime / "private/reader_records.json").read_text())
    source_pins = {name: sha(runtime / "source" / name) for name in report["source_sha256"]}
    assert source_pins == report["source_sha256"] == pre["source_sha256"]
    assert source_pins == {name: sha(HERE / name) for name in source_pins}
    assert report["predeclared_sha256"] == sha(reports / "predeclared.json")
    assert report["commands_sha256"] == sha(reports / "commands.jsonl")
    assert sha(report["native_library"]) == report["native_library_sha256"]
    inputs = [json.loads((runtime / "private" / f"input{i:02d}.json").read_text()) for i in range(33)]
    assert all(len(x) == 577 and all(type(v) is int and -127 <= v <= 127 for v in x) for x in inputs)
    checks = []
    header = struct.Struct(">8sB32s32sH32s32s32sQ")
    for record, admissions in zip(answers, (0, 1, 32, 33), strict=True):
        row = int(pre["reads_after_admissions"][str(admissions)])
        # Reconstruct coordinates first, then dot once; this is independent of
        # the driver's per-input score summation and the ciphertext arithmetic.
        current = [sum(x[j] for x in inputs[max(0, admissions - 32):admissions]) for j in range(577)]
        exact = sum(current[j] * rows[row][j] for j in range(577))
        answer = record["result"]
        assert answer["signed_score"] == exact and answer["row_id"] == row
        assert answer["sign"] == (exact > 0) - (exact < 0)
        assert abs(exact) <= 32 * 127 * sum(map(abs, rows[row]))
        output = runtime / "public" / f"read{admissions:02d}.ct"
        raw = output.read_bytes()
        fields = header.unpack(raw[:header.size])
        assert fields[0] == b"RSDDH001" and fields[1] == 2 and fields[4] == row
        assert len(raw) == 691 and fields[-1] == 512
        assert fields[3].hex() == report["context_sha256"]
        assert sha(output) == answer["ciphertext_sha256"]
        state = runtime / "public" / ("zero.ct" if admissions == 0 else f"acc{admissions:02d}.ct")
        assert state.read_bytes()[179:435] == raw[179:435]
        checks.append({"after_admissions": admissions, "row_id": row, "direct_integer_match": True,
                       "designated_output_identity": True, "aggregate_randomizer_retained": True})
    assert (runtime / "public/acc33.ct").read_bytes() == (runtime / "public/final.replayed.ct").read_bytes()
    recipients = runtime / "private/recipients"
    assert sorted(p.name for p in recipients.iterdir()) == [f"r{i:02d}.key" for i in range(16)]
    assert recipients.stat().st_mode & 0o777 == 0o700
    assert all(p.stat().st_size == 435 and p.stat().st_mode & 0o777 == 0o600 for p in recipients.iterdir())
    assert all((runtime / "private" / f"input{i:02d}.json").stat().st_mode & 0o777 == 0o600 for i in range(33))
    commands = [json.loads(line) for line in (reports / "commands.jsonl").read_text().splitlines()]
    assert sum(r["command"][1] == "issuer-encrypt" for r in commands) == 33
    assert sum(r["command"][1] == "host-learn" for r in commands) == 34  # includes exact normal replay
    assert sum(r["command"][1] == "reader-decrypt" for r in commands) == 4
    for record in commands:
        command = record["command"][1]
        if record["role"].startswith("public_"):
            assert "--vector" not in record["command"] or command == "encode-query"
            assert "--sk" not in record["command"]
        if command == "reader-decrypt":
            assert record["stdout"] is None and record["elapsed_ns"] is None
            assert record["private_output_and_timing_omitted"] is True
        else:
            assert "signed_score" not in record["stdout"]
    validation = json.loads((reports / "validated_context.json").read_text())
    assert validation["validated"] is True and validation["context_id"] == sha(runtime / "public/context.json")
    assert validation["source_sha256"] == source_pins
    assert validation["counts"]["context_consistency_rows"] == 16
    assert validation["counts"]["subgroup_checks"] == 593
    result = {"passed": True, "classification": "EXECUTED independent normal-artifact/private-integer validation",
              "validator_sha256": sha(__file__), "report_sha256": sha(reports / "report.json"),
              "checks": checks, "exact_public_transition_replay": True,
              "private_files_mode_and_final_recipient_inventory": True,
              "public_host_commands_have_no_plaintext_or_recipient_key_inputs": True,
              "recipient_outputs_and_private_timings_omitted_from_public_commands": True,
              "full_validation_and_runtime_source_pins_match": True,
              "private_values_and_private_file_hashes_omitted": True,
              "scope": "normal retained artifacts only; no adversarial, malformed, routing or extraction experiment",
              "python": sys.version}
    target = reports / "validation.json"
    assert not target.exists()
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"passed": True, "exact_private_integer_matches": len(checks), "public_transition_replay_equal": True}))


if __name__ == "__main__":
    main()
