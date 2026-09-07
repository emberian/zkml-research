#!/usr/bin/env python3
"""Independent targeted regression and semantic checks of the repaired wrapper."""
import base64
import concurrent.futures
import copy
import hashlib
import json
import shutil
import socket
import sys
import threading
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "end_to_end"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    snapshot = HERE / "snapshots/journal_repaired"
    snapshot.mkdir(parents=True, exist_ok=False)
    hashes = {}
    for name in ("common.py", "model.py", "roles.py", "authority.py", "reader.py", "run.py", "client.py"):
        src = SOURCE / "journal" / name
        shutil.copy2(src, snapshot / name)
        hashes[name] = sha(src)
    (snapshot / "manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
    sys.path.insert(0, str(snapshot))
    from run import Run
    import authority
    from common import atomic_write, canonical, rpc, write_json
    runtime = HERE / "runtime/journal_repair_001"
    runtime.mkdir(parents=True, exist_ok=False)
    binary = HERE / "runtime/journal_alias_001/resident-crypto"
    vector, query, queries = [runtime / name for name in ("vector.json", "query.json", "queries.json")]
    write_json(vector, [1] + [0] * 576)
    write_json(query, [1] + [0] * 576)
    write_json(queries, [{"route": 0, "path": str(query)}])
    execution = Run(runtime / "roles", queries, binary)
    checks = []
    release_second_read = threading.Event()

    def refused(name, response):
        assert response.get("ok") is False, (name, response)
        checks.append({"name": name, "refused": True, "reason": response.get("reason")})

    try:
        first = execution.prepare("Learn", 0, "first", vector=vector)
        accepted_first = execution.accepted(first)
        infer = execution.prepare("Infer", 0, "selected-infer", query_index=0)
        for field, value, name in [
            ("program_version", True, "boolean_program_version"),
            ("program_version", 1.0, "float_program_version"),
            ("parent_revision", True, "boolean_parent_revision"),
            ("parent_revision", 1.0, "float_parent_revision"),
            ("route", False, "boolean_route"),
            ("route", 0.0, "float_route"),
            ("recipient", "other-recipient", "changed_recipient"),
            ("genesis", "0" * 64, "changed_genesis"),
            ("program_id", "0" * 64, "changed_program"),
            ("key_id", "0" * 64, "changed_key"),
        ]:
            bad = copy.deepcopy(infer)
            bad["action"][field] = value
            refused(name, execution.submit(bad))
        bad = copy.deepcopy(infer)
        bad["proposal"]["result_ct"] = execution.g["zero_ct_sha256"]
        refused("canonical_wrong_result_real_recomputation", execution.submit(bad))
        bad = copy.deepcopy(infer)
        signature = bad["authorization"]["signature"]
        bad["authorization"]["signature"] = ("A" if signature[0] != "A" else "B") + signature[1:]
        refused("forged_request_signature", execution.submit(bad))
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
            client.connect(execution.acfg["socket"])
            client.sendall(b'{"op":"head","op":"head"}\n')
            with client.makefile("rb") as stream:
                response = json.loads(stream.readline())
            refused("duplicate_network_json_field", response)
        accepted_infer = execution.accepted(infer)
        assert execution.answers() == {"selected-infer": 1}
        refused("genuine_learn_receipt_at_reader", rpc(execution.rcfg["socket"], {
            "op": "receive", "envelope": accepted_first["envelope"], "ciphertext": ""}))
        bad_envelope = copy.deepcopy(accepted_infer["envelope"])
        bad_envelope["payload"]["output_ct"] = execution.g["zero_ct_sha256"]
        refused("altered_finalization_signature", rpc(execution.rcfg["socket"], {
            "op": "receive", "envelope": bad_envelope, "ciphertext": ""}))
        second = execution.prepare("Learn", 0, "second", vector=vector)
        bad = copy.deepcopy(second)
        bad["action"]["range_assertion"] = [-127.0, 127.0]
        refused("float_signed_range_assertion", execution.submit(bad))
        fresh = Path(execution.acfg["cas"]) / second["action"]["fresh_ct"]
        original_bytes = fresh.read_bytes()
        saved = fresh.with_name("review-held-fresh")
        fresh.rename(saved)
        try:
            refused("missing_committed_candidate_blob", execution.submit(second))
        finally:
            saved.rename(fresh)
        corrupt = bytearray(original_bytes)
        corrupt[-1] ^= 1
        atomic_write(fresh, bytes(corrupt))
        try:
            refused("mutated_previously_inspected_blob", execution.submit(second))
        finally:
            atomic_write(fresh, original_bytes)
        execution.accepted(second)
        assert execution.accepted(first)["envelope"] == accepted_first["envelope"]
        third = execution.prepare("Learn", 0, "third", vector=vector)
        before = execution.head()["revision"]
        local_reader = authority.Authority(execution.acfg)
        original_connect = authority.connect
        reached_second_read = threading.Event()
        statements = []

        def trace(sql):
            text = sql.lower()
            if text.startswith("select") and ("from journal" in text or "from meta" in text):
                statements.append(sql)
                if len(statements) == 2:
                    reached_second_read.set()
                    release_second_read.wait(30)

        def traced_connect(path):
            connection = original_connect(path)
            connection.set_trace_callback(trace)
            return connection

        authority.connect = traced_connect
        try:
            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
                future = pool.submit(local_reader.handle, {"op": "export"})
                assert reached_second_read.wait(30), statements
                committed = execution.accepted(third)
                assert committed["envelope"]["payload"]["revision"] == before + 1
                release_second_read.set()
                exported = future.result(timeout=30)
        finally:
            release_second_read.set()
            authority.connect = original_connect
        journal_last = exported["journal"][-1]["envelope"]["payload"]["revision"]
        assert journal_last == exported["head"]["revision"] == before
        assert execution.head()["revision"] == before + 1
        historical_infer = execution.accepted(infer)
        assert historical_infer["status"] == "replayed"
        assert historical_infer["envelope"] == accepted_infer["envelope"]
        assert historical_infer["delivery"]["reader"]["status"] == "replayed"
        replay = execution.replay(True)
        report = {
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "classification": "EXECUTED independent repaired-wrapper checks",
            "review_script_sha256": sha(Path(__file__)), "sources": hashes,
            "binary_sha256": sha(binary), "negative_checks": checks,
            "positive_learns": 3, "positive_infers": 1,
            "honest_public_test_vector_score": 1,
            "historical_learn_and_infer_retry_exact": True,
            "historical_reader_retry_deduplicated": True,
            "concurrent_export": {"traced_selects": statements, "journal_last": journal_last,
                                  "head_revision": exported["head"]["revision"],
                                  "concurrent_committed_revision": before + 1},
            "quiescent_full_replay": replay,
            "scope": "Targeted actual BFV/Ed25519/SQLite/reader regressions, no full window rerun, confidentiality theorem or masterless claim.",
            "passed": True,
        }
        out = HERE / "journal_repair_review_001.json"
        out.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"record": str(out), "passed": True, "negative_checks": len(checks), "consistent_concurrent_export": True}))
    finally:
        release_second_read.set()
        execution.close()


if __name__ == "__main__":
    main()
