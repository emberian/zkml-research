#!/usr/bin/env python3
"""Recheck source pins and exact bookkeeping; never tests cryptographic security."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / ".git").exists())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    completed = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    row = {"argv": args, "exit_code": completed.returncode,
           "stdout": completed.stdout, "stderr": completed.stderr}
    assert completed.returncode == 0, row
    return row


access = json.loads((HERE / "access.json").read_text())
checked = []
for source in access["local_pdf_reads"]:
    pdf = Path(source["path"])
    extracted = ROOT / source["command"][-1]
    assert digest(pdf) == source["sha256"], pdf
    assert digest(extracted) == source["text_sha256"], extracted
    checked.append({"pdf": str(pdf), "sha256": source["sha256"],
                    "text_sha256": source["text_sha256"]})

spans = json.loads((HERE / "source_spans.json").read_text())
assert {s["local_pdf"] for s in spans["sources"]} == {
    s["path"] for s in access["local_pdf_reads"]}
assert access["web_queries"] == len(access["web_query_log"]) == 4
assert access["metered_searches"] == 0

commands = [run([sys.executable, str(HERE / "rate_ledger.py")]),
            run([sys.executable, "-m", "py_compile", str(HERE / "rate_ledger.py"),
                 str(HERE / "validate.py")]),
            run(["git", "check-ignore", str(HERE / "texts" / "2012_733.txt"),
                 importlib.util.cache_from_source(str(HERE / "validate.py"))])]

bootstrap = HERE.parent / "qio_instantiation" / "bootstrap_lift" / "BOOTSTRAP_LIFT.md"
bootstrap_hash = "ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792"
assert digest(bootstrap) == bootstrap_hash, "Frozen bootstrap changed; review contract"
validation = {
    "schema": "base-fe-audit-validation-v1",
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Source hashes, local-ignore rules, exact scalar bookkeeping and compilation of Python only. No encryption run or quantum-security proof validation.",
    "source_pins": checked,
    "frozen_bootstrap": {"path": str(bootstrap), "sha256": bootstrap_hash},
    "commands": commands,
    "source_rows": len(spans["sources"]),
    "search_counts": {"web": 4, "scry": 0, "kagi": 0},
    "network_pdf_downloads": 0,
}
(HERE / "validation.json").write_text(json.dumps(validation, indent=2) + "\n")
names = [".gitignore", "BASE_FE_AUDIT.md", "access.json", "source_spans.json",
         "rate_ledger.py", "rate_ledger.json", "validate.py", "validation.json"]
manifest = {"schema": "base-fe-audit-artifacts-v1", "files": [
    {"path": name, "sha256": digest(HERE / name), "bytes": (HERE / name).stat().st_size}
    for name in names]}
(HERE / "artifact_hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"sources_verified": len(checked), "artifacts_pinned": len(names),
                  "report_sha256": digest(HERE / "BASE_FE_AUDIT.md"),
                  "manifest_sha256": digest(HERE / "artifact_hashes.json")}, indent=2))
