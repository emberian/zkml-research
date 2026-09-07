#!/usr/bin/env python3
"""Schedule sync between the verified reader's two status SELECTs over real RPC."""
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import shutil
import socketserver
import sys
import threading
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "end_to_end"
EXPECTED = "f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    snapshot = HERE / "snapshots/verified_status"
    snapshot.mkdir(parents=True, exist_ok=False)
    shutil.copytree(HERE / "snapshots/journal_repaired", snapshot / "journal")
    (snapshot / "verified_reader").mkdir()
    source = SOURCE / "verified_reader/service.py"
    assert sha(source) == EXPECTED
    saved = snapshot / "verified_reader/service.py"
    shutil.copy2(source, saved)
    spec = importlib.util.spec_from_file_location("reviewed_verified_service", saved)
    service = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(service)
    from common import read_json, rpc, write_json
    runtime = HERE / "runtime/verified_status_001"
    runtime.mkdir(parents=True, exist_ok=False)
    original_root = HERE / "runtime/journal_repair_001/roles"
    config = read_json(original_root / ".private/reader/config.json")
    config.update(db=str(runtime / "reader.sqlite3"), cas=str(runtime / "cas"),
                  command_log=str(runtime / "public_commands.jsonl"),
                  verified_reader_source_sha256=EXPECTED)
    address = "/tmp/rs-review-status-" + os.urandom(6).hex() + ".sock"
    config["socket"] = address
    write_json(runtime / "config.json", config, True)
    role = service.VerifiedReader(config)
    first_event = json.loads((original_root / "events.jsonl").read_text().splitlines()[0])
    envelope = first_event["reply"]["envelope"]
    assert envelope["payload"]["revision"] == 1
    fresh_hash = envelope["payload"]["request"]["action"]["fresh_ct"]
    role.cas.import_file(original_root / "zero.ct")
    role.cas.import_file(original_root / "host_cas" / fresh_hash)
    selected = threading.Event()
    release_count = threading.Event()
    original_connect = service.connect
    status_thread = [None]
    statements = []

    def trace(sql):
        lowered = sql.lower()
        if "select revision,state_digest from verified_head" in lowered:
            status_thread[0] = threading.get_ident()
            statements.append(sql)
        if "select count(*) from verified_journal" in lowered and threading.get_ident() == status_thread[0]:
            statements.append(sql)
            selected.set()
            release_count.wait(30)

    def traced_connect(path):
        connection = original_connect(path)
        connection.set_trace_callback(trace)
        return connection

    service.connect = traced_connect
    server = socketserver.ThreadingUnixStreamServer(address, service.Handler)
    server.daemon_threads = True
    server.role = role
    os.chmod(address, 0o600)
    worker = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.05}, daemon=True)
    worker.start()
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
            future = pool.submit(rpc, address, {"op": "verified_status"})
            assert selected.wait(30)
            synced = rpc(address, {"op": "sync", "envelope": envelope})
            assert synced.get("ok") is True and synced["revision"] == 1
            release_count.set()
            old_status = future.result(timeout=30)
        assert old_status["revision"] == old_status["verified_records"] == 0
        new_status = rpc(address, {"op": "verified_status"})
        assert new_status["revision"] == new_status["verified_records"] == 1
        result = {
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "classification": "EXECUTED targeted independent concurrent verified-reader status check",
            "review_script_sha256": sha(Path(__file__)),
            "service_sha256": sha(saved),
            "journal_snapshot_manifest": read_json(snapshot / "journal/manifest.json"),
            "schedule": ["status reads head at revision0", "status pauses before count SELECT", "separate RPC sync verifies real signed BFV Learn and commits revision1", "status resumes count SELECT in original read transaction"],
            "traced_status_selects": statements,
            "concurrent_sync": synced,
            "status_during_commit": old_status,
            "status_after_commit": new_status,
            "passed": True,
            "scope": "Actual strict RPC handler, Ed25519, BFV recomputation and SQLite WAL. A trace callback only schedules the SELECT interleaving. This one-history status check does not replace the owner's mixed-history/crash/release suite or establish masterless security.",
        }
        out = HERE / "verified_status_review_001.json"
        out.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({"record": str(out), "passed": True, "during": [old_status["revision"], old_status["verified_records"]], "after": [new_status["revision"], new_status["verified_records"]]}))
    finally:
        release_count.set()
        service.connect = original_connect
        server.shutdown()
        server.server_close()
        worker.join(timeout=5)
        Path(address).unlink(missing_ok=True)


if __name__ == "__main__":
    main()
