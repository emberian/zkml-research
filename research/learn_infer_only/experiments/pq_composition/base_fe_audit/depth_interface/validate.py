#!/usr/bin/env python3
"""Source pins and parameter bookkeeping only; no cryptographic runtime tests."""
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
    r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    row = {"argv": args, "exit_code": r.returncode, "stdout": r.stdout, "stderr": r.stderr}
    assert r.returncode == 0, row
    return row


inputs = json.loads((HERE / "inputs.json").read_text())
for item in inputs["inputs"]:
    assert digest(Path(item["path"])) == item["sha256"], item["path"]
commands = [run([sys.executable, str(HERE / "arity_substitution.py")]),
            run([sys.executable, "-m", "py_compile", str(HERE / "arity_substitution.py"),
                 str(HERE / "validate.py")]),
            run(["git", "check-ignore", importlib.util.cache_from_source(str(HERE / "validate.py"))])]
ledger = json.loads((HERE / "arity_substitution.json").read_text())
assert len(ledger["arity_rows"]) == 12 and len(ledger["chunk_rows"]) == 36
for row in ledger["arity_rows"]:
    q, m = row["external_function_keys_Q"], row["randomized_encoding_output_bits_M"]
    assert row["bit_split_underlying_boolean_keys"] == q * m
    assert row["normalized_N_q4_multiplier_vs_q_Q"] == m**4
    assert row["normalized_share_q2_multiplier_vs_q_Q"] == m**2
record = {
    "schema": "depth-interface-validation-v1", "utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Unchanged source/frozen inputs and combinatorial/normalized-monomial bookkeeping. No validation of cryptographic security or a complete compact-FE implementation.",
    "read_only_inputs_verified": len(inputs["inputs"]), "commands": commands,
    "new_queries": inputs["new_queries"], "new_pdf_downloads": 0,
}
(HERE / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
names = [".gitignore", "DEPTH_INTERFACE.md", "inputs.json", "arity_substitution.py",
         "arity_substitution.json", "validate.py", "validation.json"]
manifest = {"schema": "depth-interface-artifacts-v1", "files": [
    {"path": name, "sha256": digest(HERE / name), "bytes": (HERE / name).stat().st_size}
    for name in names]}
(HERE / "artifact_hashes.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"read_only_inputs_verified": len(inputs["inputs"]), "artifacts_pinned": len(names),
                  "report_sha256": digest(HERE / "DEPTH_INTERFACE.md"),
                  "manifest_sha256": digest(HERE / "artifact_hashes.json")}, indent=2))
