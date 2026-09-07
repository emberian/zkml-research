#!/usr/bin/env python3
"""Exercise real signed-action aliases through an isolated journal/reader run."""
import hashlib
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "end_to_end"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    snapshot = HERE / "snapshots/journal_initial"
    snapshot.mkdir(parents=True, exist_ok=False)
    source_hashes = {}
    for name in ("common.py", "model.py", "roles.py", "authority.py", "reader.py", "run.py", "client.py"):
        src = SOURCE / "journal" / name
        shutil.copy2(src, snapshot / name)
        source_hashes[name] = sha(src)
    runtime = HERE / "runtime/journal_alias_001"
    runtime.mkdir(parents=True, exist_ok=False)
    binary = runtime / "resident-crypto"
    shutil.copy2(SOURCE / "crypto/target/release/resident-crypto", binary)
    binary.chmod(0o755)
    source_hashes["crypto/src/main.rs"] = sha(SOURCE / "crypto/src/main.rs")
    (snapshot / "manifest.json").write_text(json.dumps(source_hashes, indent=2) + "\n")
    sys.path.insert(0, str(snapshot))
    import run as implementation
    from common import canonical, write_json
    vector = runtime / "vector.json"
    query = runtime / "query.json"
    queries = runtime / "queries.json"
    write_json(vector, [1] + [0] * 576)
    write_json(query, [1] + [0] * 576)
    write_json(queries, [{"route": 0, "path": str(query)}])
    execution = implementation.Run(runtime / "roles", queries, binary)
    controls = []
    try:
        baseline = execution.prepare("Learn", 0, "honest-learn", vector=vector)
        honest = execution.accepted(baseline)
        controls.append({"name": "honest_learn", "ok": honest["ok"], "status": honest["status"]})
        cases = [
            ("Infer", "boolean-program-version", lambda a: a.update(program_version=True)),
            ("Learn", "float-program-version", lambda a: a.update(program_version=1.0)),
            ("Learn", "float-range-assertion", lambda a: a.update(range_assertion=[-127.0, 127.0])),
        ]
        for kind, name, mutate in cases:
            kwargs = {"query_index": 0} if kind == "Infer" else {"vector": vector}
            req = execution.prepare(kind, 0, name, **kwargs)
            signed_bytes = canonical(req["authorization"])
            mutate(req["action"])
            canonical_different = canonical(req["action"]) != canonical(req["authorization"]["payload"])
            signature_unchanged = canonical(req["authorization"]) == signed_bytes
            reply = execution.submit(req)
            controls.append({
                "name": name,
                "signed_authorization_unchanged": signature_unchanged,
                "action_differs_from_signed_canonical_payload": canonical_different,
                "accepted": reply.get("ok") is True,
                "status": reply.get("status"),
                "delivery": reply.get("delivery"),
                "reason": reply.get("reason"),
            })
            assert canonical_different and signature_unchanged and reply.get("ok") is True
        answers = execution.answers()
        assert answers == {"boolean-program-version": 1}
        result = {
            "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "classification": "EXECUTED counterexamples to exact canonical signed-action binding",
            "review_script_sha256": sha(Path(__file__)),
            "sources": source_hashes,
            "binary_sha256": sha(binary),
            "controls": controls,
            "private_test_oracle_public_vector_answers": answers,
            "final_revision": execution.head()["revision"],
            "all_alias_witnesses_observed": True,
            "scope": "Actual isolated authority and reader RPCs, real signatures and BFV. Numerical meanings match, but canonical signed context differs. No plaintext authorization bypass or masterless-security claim.",
        }
        out = HERE / "journal_alias_review_001.json"
        out.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({"record": str(out), "alias_witnesses": 3, "reader_accepts_boolean_alias": answers == {"boolean-program-version": 1}}))
    finally:
        execution.close()


if __name__ == "__main__":
    main()
