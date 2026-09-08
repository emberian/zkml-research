#!/usr/bin/env python3
"""Collect completed public evidence; never open private keys or audit contents."""
from pathlib import Path
import csv
import hashlib
import json
import shutil
import statistics

HERE = Path(__file__).resolve().parent


def main():
    report = HERE / "reports/smoke"
    data = json.loads((report / "results.json").read_text())
    plain = json.loads((HERE / "reports/plain/summary.json").read_text())
    if data["success"] is not True or data["error"] is not None:
        raise RuntimeError("smoke did not finish successfully; do not collect as success")
    output_dir = report / "artifacts"
    output_dir.mkdir(exist_ok=False)
    artifacts = []
    for pair in data["replays"]:
        for role in ["first", "replay"]:
            source = Path(pair[f"{role}_path"])
            # These are only new host-produced public ciphertexts from the passed smoke.
            destination = output_dir / source.name
            shutil.copyfile(source, destination)
            raw = destination.read_bytes()
            actual_hash = hashlib.sha256(raw).hexdigest()
            if actual_hash != pair[f"{role}_sha256"]:
                raise RuntimeError("public ciphertext archival copy differs from executed hash")
            artifacts.append({"path": str(destination.relative_to(HERE)), "bytes": len(raw), "sha256": actual_hash})
    rows = []
    for operation in data["operations"]:
        record = operation["reported"]
        row = {"name": operation["name"], "role": record["role"], "operation": record["operation"],
               "wall_seconds": operation["wall_ns"] / 1e9,
               "work_seconds": record["work_ns"] / 1e9,
               "peak_rss_bytes": operation.get("peak_rss_bytes", ""),
               "evaluate_seconds": record.get("evaluate_ns", 0) / 1e9,
               "serialized_bytes": record.get("serialized_bytes", ""),
               "xor_api_calls": record.get("gate_api_calls", {}).get("xor", ""),
               "and_api_calls": record.get("gate_api_calls", {}).get("and", ""),
               "trivial_encrypt_api_calls": record.get("gate_api_calls", {}).get("trivial_encrypt", ""),
               "bootstrap_count_instrumented": record.get("bootstrap_count_instrumented", ""),
               "rayon_num_threads": data["rayon_num_threads"]}
        rows.append(row)
    with (HERE / "costs.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    ranges = {}
    for op in ["learn", "infer"]:
        group = [r for r in rows if r["role"] == "generic-schedule-host" and r["operation"] == op]
        ranges[op] = {"processes": len(group), "wall_seconds_min": min(r["wall_seconds"] for r in group),
                      "wall_seconds_max": max(r["wall_seconds"] for r in group),
                      "wall_seconds_median": statistics.median(r["wall_seconds"] for r in group),
                      "evaluate_seconds_min": min(r["evaluate_seconds"] for r in group),
                      "evaluate_seconds_max": max(r["evaluate_seconds"] for r in group),
                      "peak_rss_bytes_max": max(r["peak_rss_bytes"] for r in group)}
    summary = {"claim": "EXECUTED", "success": data["success"], "freeze_sha256": data["freeze_sha256"],
               "logical_learn": 2, "logical_infer": 2, "exact_byte_replay_pairs": len(data["replays"]),
               "all_replay_pairs_equal": all(p["complete_serialized_bytes_equal"] for p in data["replays"]),
               "private_oracle_audits": data["private_audits"], "public_artifacts": artifacts,
               "plain_rows": {op: plain["results"][op]["rows"] for op in ["learn", "infer"]},
               "wall_and_evaluate_ranges": ranges,
               "timing_limit": "contended single-host-process sample; concurrent workloads changed during execution",
               "private_audit_timing": "all prerequisite public operations/replays/result checks completed first; one additional final frozen-file integrity recheck occurred after private audit",
               "contract_wording_deviation": "frozen contract said all frozen-file hash checks precede private audit; driver also performs a final read-only integrity recheck after it",
               "no_universal_rust_tfhe_or_replay_claim": True}
    (HERE / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
