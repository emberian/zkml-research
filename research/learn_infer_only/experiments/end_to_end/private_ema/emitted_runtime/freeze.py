#!/usr/bin/env python3
"""Freeze the public program, interpreter and prior public fixture before crypto."""
from pathlib import Path
import datetime
import hashlib
import json

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parents[3] / "formal/private_address_ema/emitted_schedule"
PRIOR = HERE.parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def frozen_files():
    own = ["Cargo.toml", "Cargo.lock", "CONTRACT.md", "build_pins.json", "build.log", "test.log",
           "compare_plain.py", "freeze.py", "run_smoke.py", "reports/plain/summary.json",
           "target/release/resident-emitted-bool-runtime"]
    files = [HERE / name for name in own] + sorted((HERE / "src").rglob("*.rs"))
    files += [FORMAL / name for name in ["SCHEMA.md", "artifacts/learn.json", "artifacts/infer.json"]]
    files += [PRIOR / name for name in ["CONTRACT.md", "Cargo.toml", "Cargo.lock", "source_manifest.json",
                                       "target/release/reader", "src/bin/reader.rs", "src/lib.rs",
                                       "runs/run_001/public/keys/server_key.bin",
                                       "runs/run_001/public/state_000.ct",
                                       "runs/run_001/public/input_001.ct", "runs/run_001/public/input_002.ct",
                                       "runs/run_001/public/query_001.ct"]]
    return files


def main():
    report = json.loads((HERE / "reports/plain/summary.json").read_text())
    if report["all_matched"] is not True or report["cryptographic_execution"] is not False:
        raise RuntimeError("plain comparison prerequisite did not pass")
    for path, expected in report["source_pins"].items():
        if sha(Path(path)) != expected:
            raise RuntimeError(f"plain comparison input changed: {path}")
    # The retained prior manifest identifies its original reader binary.
    prior_manifest = json.loads((PRIOR / "source_manifest.json").read_text())
    if sha(PRIOR / "target/release/reader") != prior_manifest["binary_hashes"]["reader"]:
        raise RuntimeError("prior reader binary changed")
    files = [{"path": str(p), "bytes": p.stat().st_size, "sha256": sha(p)} for p in frozen_files()]
    document = {"schema": "emitted-bool-runtime-positive-smoke-freeze-v1", "claim": "EXECUTED",
                "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "files": files, "private_key_read_or_hashed": False,
                "planned_logical_learn": 2, "planned_logical_infer": 2,
                "replays_per_operation": 1, "host_concurrency": 1,
                "private_audit_after_all_public_evaluations_replays_and_hash_checks": True,
                "contention": "root reports existing one-thread long EMA utility and short setup/journal work; wall timings are contended"}
    path = HERE / "freeze.json"
    with path.open("x") as stream:
        stream.write(json.dumps(document, indent=2) + "\n")
    print(json.dumps({"freeze": str(path), "sha256": sha(path), "frozen_public_files": len(files)}))


if __name__ == "__main__":
    main()
