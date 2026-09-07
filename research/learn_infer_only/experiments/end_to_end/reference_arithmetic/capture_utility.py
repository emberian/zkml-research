#!/usr/bin/env python3
"""Retain one existing public, dense utility Infer; never rerun the workload."""
import gzip
import json
from pathlib import Path
from reference import decode_ct, decode_query, require, sha

HERE = Path(__file__).resolve().parent
UTILITY = HERE.parent / "journal/results/utility_002"


def main():
    target = HERE / "utility-fixtures.json"
    require(not target.exists(), "utility fixture already frozen")
    public = UTILITY / "public_evidence"
    packets = json.loads((public / "representative_finalized_infer.json").read_bytes())
    packet = packets[0]
    action = packet["payload"]["request"]["action"]
    require(action["request_id"] == "h0-e0065" and action["kind"] == "Infer", "representative honest utility Infer")
    require(json.loads((UTILITY / "history_0/report.json").read_bytes())["kind"] == "public_fixed_utility_history", "public utility history")
    expected_hash = packet["payload"]["output_ct"]
    selected = None
    for line in (UTILITY / "history_0/commands.jsonl").open():
        entry = json.loads(line)
        if entry["role"] == "host" and entry["command"][1] == "host-infer" and entry["exit_code"] == 0:
            meta = json.loads(entry["stdout"])
            if meta["sha256"] == expected_hash:
                selected = entry, meta
                break
    require(selected is not None, "captured successful host command")
    entry, meta = selected
    require(meta["query_sha256"] == action["query_ct"], "finalized query identity")
    hashes = {"acc": meta["acc_sha256"], "query": meta["query_sha256"], "result": expected_hash}
    inventory = {x["path"]: x for x in json.loads((public / "runtime_hash_inventory.json").read_bytes())}
    out = HERE / "utility_fixtures"
    out.mkdir(exist_ok=True)
    blobs = {}
    for role, identity in hashes.items():
        source = f"history_0/authority/cas/{identity}"
        record = inventory[source]
        require(record["sha256"] == identity, "public inventory membership")
        data = (UTILITY / source).read_bytes()
        require(sha(data) == identity and len(data) == record["bytes"], "exact retained public object")
        if role == "query":
            q = decode_query(data)
            require(sum(x > 0 for x in q) == 270 and sum(x < 0 for x in q) == 269, "dense signed public utility query")
            require(q[0] != 0 and q[-1] != 0, "both query endpoints exercised")
        else:
            ct = decode_ct(data)
            require(any(x for poly in ct.components for limb in poly for x in limb), "nonzero public ciphertext")
        path = out / (identity + ".gz")
        path.write_bytes(gzip.compress(data, mtime=0))
        blobs[identity] = {"kind": "public_query" if role == "query" else "public_ciphertext", "bytes": len(data), "path": str(path.relative_to(HERE)), "gzip_sha256": sha(path.read_bytes())}
    envelope = HERE / "utility_finalization.json"
    envelope.write_text(json.dumps(packet, indent=2) + "\n")
    manifest = {"schema": "independent-public-arithmetic-fixtures-v1", "suite": "utility_002_dense_h0_e0065",
                "scope": "One already-finalized public utility Infer; accumulator/query/output bytes only; no keys, private vectors, decryption or workload rerun",
                "events": [{"event_id": "utility-h0-e0065", "kind": "Infer", "hashes": hashes,
                            "command_log_entry_sha256": sha(json.dumps(entry, sort_keys=True, separators=(",", ":")).encode()), "historical_binary_path": entry["command"][0]}],
                "blobs": blobs, "retained_public_finalization_sha256": sha(envelope.read_bytes()),
                "provenance": {str(p): sha(p.read_bytes()) for p in [UTILITY / "history_0/report.json", UTILITY / "history_0/commands.jsonl", public / "representative_finalized_infer.json", public / "runtime_hash_inventory.json"]}}
    target.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"ok": True, "event_id": "utility-h0-e0065", "query_nonzero": 539, "query_positive": 270, "query_negative": 269, "ciphertexts": 2, "query": hashes["query"], "honest_result": expected_hash}))


if __name__ == "__main__":
    main()
