#!/usr/bin/env python3
"""Read saved normal-run evidence; do not invoke crypto or trusted roles."""
from pathlib import Path
import collections
import gzip
import hashlib
import json
import statistics

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results/run_001"
RUNTIME = HERE / "runtime/run_001/journal"
sha = lambda b: hashlib.sha256(b).hexdigest()
canon = lambda x: json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode()
load = lambda p: json.loads(p.read_bytes())
report = load(RESULTS / "report.json")
pairs = [json.loads(line) for line in (RESULTS / "pairs.jsonl").read_bytes().splitlines()]
assert len(pairs) == report["events"] == 44
assert sum(p["kind"] == "Learn" for p in pairs) == 40
assert sum(p["expired_ct"] is not None for p in pairs) == 8
actual_ct_comparisons = 0
for pair in pairs:
    event = RUNTIME / "work" / pair["event_id"]
    b, p = (event / "request.json").read_bytes(), (event / "peer-request.json").read_bytes()
    assert b == p and sha(b) == pair["request_sha256"]
    request = json.loads(b)
    assert b == canon(request) + b"\n" and sha(canon(request)) == pair["request_digest"]
    h = pair["result_ct"]
    ct1, ct2 = (RUNTIME / "host_cas" / h).read_bytes(), (RUNTIME / "peer_cas" / h).read_bytes()
    assert ct1 == ct2 and sha(ct1) == h
    actual_ct_comparisons += 1
    for field in ("cas_get_calls", "full_blob_sha256_calls", "full_blob_sha256_bytes"):
        assert pair["baseline"]["request_stats"][field] == pair["persistent"]["request_stats"][field]
    assert pair["baseline"]["request_stats"]["cas_get_calls"] == pair["baseline"]["request_stats"]["full_blob_sha256_calls"]

def read_gzip_lines(name):
    return [json.loads(line) for line in gzip.decompress((RESULTS / name).read_bytes()).splitlines()]

commands = read_gzip_lines("commands.jsonl.gz")
peer_commands = read_gzip_lines("peer_commands.jsonl.gz")
normal_host_commands = [c for c in commands if c["role"] == "host"]
first_count = sum(pairs[0]["baseline"]["request_stats"]["crypto_calls"].values())
direct_control = normal_host_commands[first_count:2 * first_count]
baseline_commands = normal_host_commands[:first_count] + normal_host_commands[2 * first_count:]
command_checks = {}
for label, rows in [("baseline", baseline_commands), ("persistent", peer_commands)]:
    counted = collections.Counter(c["command"][1] for c in rows)
    assert dict(counted) == report[label]["crypto_calls"]
    assert len(rows) == report[label]["crypto_subprocesses"]
    for row in rows:
        assert row["exit_code"] == 0
        assert row["command"][1] in ("inspect", "host-learn", "host-infer")
        assert not {"--sk", "--vector", "--pk"}.intersection(row["command"])
    command_checks[label] = {"commands": len(rows), "by_command": dict(counted),
        "cli_elapsed_ns": sum(r["elapsed_ns"] for r in rows)}
assert len(direct_control) == first_count == 3
assert dict(collections.Counter(c["command"][1] for c in direct_control)) == pairs[0]["baseline"]["request_stats"]["crypto_calls"]
for command in commands:
    if command["role"] == "reader" and command["command"][1] == "reader-decrypt":
        assert command["stdout"] is None and command["stderr"] is None and command["private_output_omitted"]

cache = {json.loads(c["stdout"])["sha256"]: json.loads(c["stdout"]) for c in peer_commands if c["command"][1] == "inspect"}
assert len(cache) == report["persistent"]["final_cache_entries"] == 84
groups = {}
for label, selected in [("baseline_first", [p for p in pairs if p["order"] == "baseline-first"]),
                        ("persistent_first", [p for p in pairs if p["order"] == "persistent-first"]),
                        ("expiry_events", [p for p in pairs if p["expired_ct"] is not None])]:
    before = sum(p["baseline_caller_ns"] for p in selected)
    after = sum(p["persistent_caller_ns"] for p in selected)
    groups[label] = {"events": len(selected), "baseline_ns": before, "persistent_ns": after,
                     "ratio_excludes_startup": before / after}

pins = load(HERE / "source_pins.json")
for name, pin in pins["core"].items():
    assert sha((HERE / "frozen_core" / name).read_bytes()) == pin["sha256"]
assert sha((HERE / "runtime/run_001/resident-crypto").read_bytes()) == pins["crypto_binary_sha256"]
for source in (HERE / "host.py", HERE / "benchmark.py"):
    assert "controls" not in source.read_text() and "signing.key" not in source.read_text()

out = {"ok": True, "paired_saved_request_and_ciphertext_comparisons": actual_ct_comparisons,
    "all_recorded_full_blob_hash_counts_and_bytes_equal": True,
    "command_audit": command_checks, "direct_original_cli_control_commands_excluded": len(direct_control),
    "all_keyless_host_commands": True, "reader_plaintext_not_in_public_command_logs": True,
    "cache_entries": len(cache), "cache_canonical_json_bytes": len(canon(cache)),
    "cache_bytes_scope": "serialized metadata proxy; Python heap/RSS not measured",
    "timing_groups": groups, "core_and_binary_pins_rechecked": True,
    "scope": "Saved normal-workload evidence inspection only; no new cryptographic calls or adversarial tests"}
(RESULTS / "audit.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
