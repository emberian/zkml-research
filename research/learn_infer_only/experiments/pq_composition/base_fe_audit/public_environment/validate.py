#!/usr/bin/env python3
"""Provenance and finite witness checks, not a cryptographic theorem checker."""
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


inputs = json.loads((HERE / "inputs.json").read_text())
for item in inputs["inputs"]:
    assert digest(Path(item["path"])) == item["sha256"], item["path"]
commands = [run([sys.executable, str(HERE / "circuit_dependency.py")]),
            run([sys.executable, "-m", "py_compile", str(HERE / "circuit_dependency.py"),
                 str(HERE / "validate.py")]),
            run(["git", "check-ignore",
                 importlib.util.cache_from_source(str(HERE / "validate.py"))])]
witness = json.loads((HERE / "circuit_dependency.json").read_text())
assert witness["exhaustive_equalities"] == 32768
assert witness["nonzero_output_cases"] == 28672
assert witness["retained_positions"] == [2, 5, 9, 11]
assert len(witness["after_log_absorption_closure_examples"]) == 8
assert all(row["node_work_upper_bound"] <= row["T"]
           for row in witness["after_log_absorption_closure_examples"])
validation = {
    "schema": "public-environment-validation-v1",
    "time_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Verifies unchanged frozen/source inputs and finite ordinary-circuit/integer witnesses. Does not verify the mathematical security or asymptotic parameter proof.",
    "read_only_inputs_verified": len(inputs["inputs"]),
    "commands": commands,
    "new_queries": inputs["new_queries"],
    "new_pdf_downloads": 0,
}
(HERE / "validation.json").write_text(json.dumps(validation, indent=2) + "\n")
names = [".gitignore", "PUBLIC_ENVIRONMENT.md", "inputs.json", "circuit_dependency.py",
         "circuit_dependency.json", "validate.py", "validation.json"]
manifest = {"schema": "public-environment-artifacts-v1", "files": [
    {"path": name, "sha256": digest(HERE / name), "bytes": (HERE / name).stat().st_size}
    for name in names]}
(HERE / "artifact_hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"read_only_inputs_verified": len(inputs["inputs"]),
                  "artifacts_pinned": len(names),
                  "report_sha256": digest(HERE / "PUBLIC_ENVIRONMENT.md"),
                  "manifest_sha256": digest(HERE / "artifact_hashes.json")}, indent=2))
