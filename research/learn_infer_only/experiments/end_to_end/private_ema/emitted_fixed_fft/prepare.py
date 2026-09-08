#!/usr/bin/env python3
"""Materialize only the authorized public input tuples; no old output reads."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "emitted_runtime"
FORMAL = HERE.parents[3] / "formal/private_address_ema/emitted_schedule"


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def metadata(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha(path)}


def main():
    previous_report = PRIOR / "reports/smoke/results.json"
    previous = json.loads(previous_report.read_text())
    assert previous["success"] is True
    cases = []
    for name in ["learn_001", "infer_001", "learn_002", "infer_002"]:
        operation = next(o for o in previous["operations"] if o["name"] == name)
        op, tag = name.split("_")
        pair = next(p for p in previous["replays"] if p["operation"] == op and p["step"] == tag)
        paths = operation["argv"][2:6]
        assert len(paths) == 4
        reads = [metadata(p) for p in paths]
        assert all(r["sha256"] == pair["input_hashes"][r["path"]] for r in reads)
        cases.append({"case": f"prior_emitted_{name}", "operation": op,
                      "source_record": str(previous_report), "read_inputs": reads})
    failure_report = HERE.parent / "encrypted_successor/reports/run001/public_failure_audit.json"
    failure = json.loads(failure_report.read_text())["failed_pair"]
    assert failure["event_id"] == "h0-e0014" and failure["inputs_equal_across_invocations"] is True
    # Import only the recorded read inputs, never the failed primary/replay output paths.
    reads = [metadata(FORMAL / "artifacts/learn.json")]
    for entry in failure["public_read_inputs"]:
        actual = metadata(entry["path"])
        assert actual == entry
        reads.append(actual)
    assert len(reads) == 4
    cases.append({"case": "old_fourteenth_learn_public_inputs", "operation": "learn",
                  "source_record": str(failure_report), "read_inputs": reads})
    document = {"schema": "fixed-fft-public-control-inputs-v1", "claim": "EXECUTED",
                "source_records": [metadata(previous_report), metadata(failure_report)],
                "cases": cases, "host_pairs": len(cases), "old_failed_output_files_opened": False,
                "private_files_opened": False, "new_chained_trajectory": False}
    with (HERE / "inputs.json").open("x") as stream:
        stream.write(json.dumps(document, indent=2) + "\n")
    print(json.dumps({"claim":"EXECUTED", "cases":len(cases), "inputs_sha256":sha(HERE / "inputs.json"),
                      "private_files_opened":False, "old_failed_output_files_opened":False}))


if __name__ == "__main__":
    main()
