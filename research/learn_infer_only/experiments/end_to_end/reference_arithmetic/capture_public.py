#!/usr/bin/env python3
"""Capture an allowlisted subset of an explicitly public synthetic fixture.

Reads only public report metadata and SHA256-named ciphertext/query CAS files.
Never opens fixture vectors, a public/secret key, a database, or reader state.
"""
import gzip
import json
from pathlib import Path
import re
from reference import decode_ct, decode_query, require, sha

HERE = Path(__file__).resolve().parent
E2E = HERE.parent
REPORTS = E2E / "host_runtime/results/run_001"
CAS = E2E / "host_runtime/runtime/run_001/journal/host_cas"
EVENTS = {f"learn-{i:03d}" for i in (1, 2, 16, 32, 33, 34, 39, 40)} | {f"infer-{i:03d}" for i in (1, 16, 33, 40)}


def main():
    out = HERE / "fixtures"
    out.mkdir(exist_ok=True)
    # Public status is established by benchmark.py:181-191 and its fixed
    # retained report. We do not need to open the public vectors themselves.
    report = json.loads((REPORTS / "report.json").read_bytes())
    require(report["ok"] and report["events"] == 44 and report["expiries"] == 8, "known public fixture report")
    pairs = [json.loads(line) for line in (REPORTS / "pairs.jsonl").read_text().splitlines()]
    selected = {p["result_ct"]: p for p in pairs if p["event_id"] in EVENTS}
    commands = [json.loads(line) for line in gzip.open(REPORTS / "commands.jsonl.gz", "rt")]
    records, blobs = {}, {}
    for entry in commands:
        argv = entry["command"]
        if entry["role"] != "host" or argv[1] not in ("host-learn", "host-infer"):
            continue
        require(entry["exit_code"] == 0, "captured host success")
        result = json.loads(entry["stdout"])
        if result["sha256"] not in selected:
            continue
        pair = selected[result["sha256"]]
        if pair["event_id"] in records:
            continue
        hashes = {"acc": result["acc_sha256"], "result": result["sha256"]}
        if argv[1] == "host-learn":
            hashes["fresh"] = result["fresh_sha256"]
            if result["old_sha256"]:
                hashes["old"] = result["old_sha256"]
            require(result["old_sha256"] == pair["expired_ct"], "expiry metadata agrees")
        else:
            hashes["query"] = result["query_sha256"]
        for role, identity in hashes.items():
            require(re.fullmatch("[0-9a-f]{64}", identity), "CAS hash only")
            data = (CAS / identity).read_bytes()
            require(sha(data) == identity, "CAS content identity")
            kind = "public_query" if role == "query" else "public_ciphertext"
            (decode_query if role == "query" else decode_ct)(data)
            compressed = gzip.compress(data, mtime=0)
            path = out / (identity + ".gz")
            if path.exists():
                require(gzip.decompress(path.read_bytes()) == data, "retained fixture unchanged")
            else:
                path.write_bytes(compressed)
            blobs[identity] = {"kind": kind, "bytes": len(data), "path": str(path.relative_to(HERE)), "gzip_sha256": sha(path.read_bytes())}
        records[pair["event_id"]] = {"event_id": pair["event_id"], "kind": pair["kind"], "hashes": hashes,
                                     "command_log_entry_sha256": sha(json.dumps(entry, sort_keys=True, separators=(",", ":")).encode()),
                                     "historical_binary_path": argv[0]}
    require(set(records) == EVENTS, "all selected events captured")
    manifest = {"schema": "independent-public-arithmetic-fixtures-v1", "scope": "Only public synthetic fixture ciphertexts and authorized public queries; no keys, ingress vectors or decrypted values",
                "events": [records[p["event_id"]] for p in pairs if p["event_id"] in records], "blobs": blobs,
                "provenance": {str(p): sha(p.read_bytes()) for p in [REPORTS / "report.json", REPORTS / "pairs.jsonl", REPORTS / "commands.jsonl.gz", E2E / "host_runtime/benchmark.py", E2E / "host_runtime/source_pins.json"]}}
    (HERE / "fixtures.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"ok": True, "events": len(records), "ciphertexts": sum(b["kind"] == "public_ciphertext" for b in blobs.values()), "queries": sum(b["kind"] == "public_query" for b in blobs.values()), "retained_bytes": sum(b["bytes"] for b in blobs.values())}))


if __name__ == "__main__":
    main()
