"""Postrun read-only integrity collection; no private path traversal or crypto."""
from pathlib import Path
from collections import Counter
import hashlib
import json

HERE = Path(__file__).resolve().parent
RUN = HERE / "reports/normal_001"
PUBLIC = RUN / "public"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


pins_path = HERE / "SOURCE_PINS.json"
pins = json.loads(pins_path.read_text())
assert sha(pins_path) == "be861661892f52e52068d88361fc1519989ae6103a4945a3c6c7e41a8ffc5fac"
assert all(sha(HERE/name) == expected for name, expected in pins["source_sha256"].items())
assert all(sha(Path(path)) == expected for path, expected in pins["reviewed_mathematics"].items())
assert all(sha(HERE/copy) == record["sha256"] == sha(Path(record["original"]))
           for copy, record in pins["copied_predecessors"].items())
assert sha(Path(pins["native_dependency"]["path"])) == pins["native_dependency"]["sha256"]
gate = json.loads((HERE/"PRELAUNCH_REVIEW.json").read_text())
assert gate["source_pins_sha256"] == sha(pins_path) and gate["disposition"] == "accepted"
assert gate["root_notified"] and sha(Path(gate["review_report_path"])) == gate["review_report_sha256"]
seal = json.loads((PUBLIC/"PUBLIC_COMPLETE.json").read_text())
assert seal["private_decryptions_so_far"] == 0 and seal["all_public_children_exited"]
for rel, info in seal["files"].items():
    path = PUBLIC / rel
    assert path.resolve().is_relative_to(PUBLIC.resolve())
    assert path.stat().st_size == info["bytes"] and sha(path) == info["sha256"]
actual_files = {str(p.relative_to(PUBLIC)) for p in PUBLIC.rglob("*") if p.is_file()}
assert actual_files == set(seal["files"]) | {"PUBLIC_COMPLETE.json"}
commands = [json.loads(line) for line in (PUBLIC/"commands.jsonl").read_text().splitlines()]
assert [r["ordinal"] for r in commands] == list(range(len(commands)))
assert all(r["exit_code"] == 0 and "signed_score" not in r["result"] for r in commands)
counts = Counter(r["command"] or "public-reference" for r in commands)
expected = {"auth-init": 1, "recipient-init": 16, "public-build": 1, "verify-public": 2,
            "validate-context": 1, "recipient-finalize": 16, "issuer-encrypt": 33,
            "host-learn": 33, "encode-query": 4, "host-infer": 4, "public-reference": 1}
assert dict(counts) == expected
learns = [r for r in commands if r["command"] == "host-learn"]
expiry = [r for r in learns if "--old" in r["argv"]]
assert len(expiry) == 1 and expiry[0] == learns[-1]
assert expiry[0]["argv"][expiry[0]["argv"].index("--old")+1] == str(PUBLIC/"ciphertexts/c01.ct")
tr = json.loads((PUBLIC/"transcript.json").read_text())
assert len(tr["complete_domain"]["complete_registry"]) == 16
assert len(tr["derivation"]["tau"]) == 16 and len(tr["derivation"]["U"]) == 561
assert len(tr["derivation"]["tapes"]) == 577
assert tr["source_identity"]["manifest_sha256"] == sha(pins_path)
accepted_counts = Counter(t["accepted_counter"] for t in tr["derivation"]["tapes"])
result = json.loads((RUN/"RESEARCH_RESULT.json").read_text())
assert result["ok"] and result["all_four_integer_comparisons_match"]
assert result["learns"] == 33 and result["infers"] == 4 and result["exact_expiries"] == 1
assert result["public_evidence_closed_before_first_private_decode"] and result["private_decode_processes"] == 4
stdout = [json.loads(line) for line in (HERE/"reports/normal_001.stdout.log").read_text().splitlines()]
assert stdout[-1]["ok"] and stdout[-1]["all_match"]
closure = next(r for r in stdout if r.get("stage") == "public_evidence_closed_before_private_drain")
assert closure == stdout[-2]
assert (HERE/"reports/normal_001.stderr.log").stat().st_size == 0
native_counts = Counter()
for record in commands:
    if record["command"] is not None:
        native_counts.update(record["result"].get("counts", {}))
out = {
    "ok": True, "scope": "postrun public integrity collection; no private path traversed or crypto rerun",
    "closed_public_files_including_seal": len(actual_files),
    "closed_public_bytes_including_seal": sum((PUBLIC/p).stat().st_size for p in actual_files),
    "source_files_rechecked": len(pins["source_sha256"]), "source_manifest_sha256": sha(pins_path),
    "context_id": tr["context_id"], "transcript_sha256": sha(PUBLIC/"transcript.json"),
    "transcript_bytes": (PUBLIC/"transcript.json").stat().st_size,
    "complete_domain_sha256_inventory_only": tr["domain_sha256_for_inventory_only"],
    "public_closure_sha256": sha(PUBLIC/"PUBLIC_COMPLETE.json"),
    "public_commands": len(commands), "command_counts": dict(sorted(counts.items())),
    "reported_native_counts_in_public_phase_logs": dict(native_counts),
    "public_reference_counts": next(r["result"]["counts"] for r in commands if r["command"] is None),
    "accepted_counter_histogram": dict(accepted_counts),
    "context_bytes": (PUBLIC/"context.json").stat().st_size,
    "state_bytes": (PUBLIC/"states/a33.ct").stat().st_size,
    "recipient_output_bytes": (PUBLIC/"outputs/o03.ct").stat().st_size,
    "hash_words": sum(len(t["raw_words_hex"]) for t in tr["derivation"]["tapes"]),
    "setup_ns": result["setup_ns"], "public_work_timer_ns": result["public_phase_ns"],
    "public_closure_checkpoint_ns": closure["elapsed_ns"], "total_ns": result["total_ns"],
    "integer_comparisons": "four matches, attributed to saved aggregate research result; private answers unread",
    "stderr_bytes": 0,
}
print(json.dumps(out, indent=2, sort_keys=True))
