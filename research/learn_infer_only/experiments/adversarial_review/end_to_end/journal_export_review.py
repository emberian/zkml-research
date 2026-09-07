#!/usr/bin/env python3
"""Schedule a real concurrent commit in the export's separate-read seam."""
import concurrent.futures
import hashlib
import json
import sys
import threading
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SNAPSHOT = HERE / "snapshots/journal_initial"
sys.path.insert(0, str(SNAPSHOT))
from run import Run
from authority import Authority
from common import write_json


def main():
    runtime = HERE / "runtime/journal_export_001"
    runtime.mkdir(parents=True, exist_ok=False)
    binary = HERE / "runtime/journal_alias_001/resident-crypto"
    vector = runtime / "vector.json"
    query = runtime / "query.json"
    queries = runtime / "queries.json"
    write_json(vector, [1] + [0] * 576)
    write_json(query, [1] + [0] * 576)
    write_json(queries, [{"route": 0, "path": str(query)}])
    execution = Run(runtime / "roles", queries, binary)
    release_head = threading.Event()
    try:
        first = execution.prepare("Learn", 0, "first", vector=vector)
        execution.accepted(first)
        second = execution.prepare("Learn", 0, "second", vector=vector)
        local_reader = Authority(execution.acfg)
        original_head = local_reader.head
        reached_head = threading.Event()

        def scheduled_head():
            reached_head.set()
            if not release_head.wait(30):
                raise RuntimeError("scheduled commit did not finish")
            return original_head()

        # This hook schedules an ordinary possible interleaving. The original
        # export still performs both database reads and constructs its result.
        local_reader.head = scheduled_head
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(local_reader.handle, {"op": "export"})
            assert reached_head.wait(30)
            committed = execution.accepted(second)
            assert committed["envelope"]["payload"]["revision"] == 2
            release_head.set()
            exported = future.result(timeout=30)
        journal_revisions = [row["envelope"]["payload"]["revision"] for row in exported["journal"]]
        assert journal_revisions == [1]
        assert exported["head"]["revision"] == 2
        # Ordinary quiescent export/replay after the same commits still works.
        replay = execution.replay(True)
        assert replay["revision"] == 2
        report = {
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "classification": "EXECUTED scheduled interleaving counterexample to atomic journal/head export",
            "review_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "snapshot_manifest": json.loads((SNAPSHOT / "manifest.json").read_bytes()),
            "schedule": ["export reads journal at revision1", "export enters delayed head method", "real separate authority process accepts and commits revision2", "export executes original head read"],
            "exported_journal_revisions": journal_revisions,
            "exported_head_revision": exported["head"]["revision"],
            "quiescent_full_public_replay": replay,
            "counterexample_observed": True,
            "scope": "No bad transition or signature is accepted. Concurrent export is an inconsistent snapshot; quiescent replay remains valid. Only an audit-owned instance's head method is delayed, without changing any read/result logic or author-owned files.",
        }
        path = HERE / "journal_export_review_001.json"
        path.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"record": str(path), "journal_revision": 1, "head_revision": 2, "quiescent_replay_passes": True}))
    finally:
        release_head.set()
        execution.close()


if __name__ == "__main__":
    main()
