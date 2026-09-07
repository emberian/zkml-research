#!/usr/bin/env python3
"""Hash retained source and public evidence; exclude all runtime state."""
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = [p for p in HERE.rglob("*") if p.is_file() and "runtime" not in p.relative_to(HERE).parts
         and "__pycache__" not in p.relative_to(HERE).parts and p.name != "artifact_manifest.json"]
for source in HERE.glob("*.py"):
    compile(source.read_text(), str(source), "exec")
pins = json.loads((HERE / "source_pins.json").read_text())
for name, entry in pins["core"].items():
    assert sha(HERE / "frozen_core" / name) == entry["sha256"]
result = json.loads((HERE / "results/run_001/report.json").read_text())
audit = json.loads((HERE / "results/run_001/audit.json").read_text())
assert result["ok"] and audit["ok"]
ignored = subprocess.run(["git", "check-ignore", str(HERE / "runtime/run_001/journal/.private/reader/bfv_secret.bin")],
                         cwd=HERE, capture_output=True, text=True)
assert ignored.returncode == 0
manifest = {str(p.relative_to(HERE)): {"sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(files)}
(HERE / "artifact_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"retained_files": len(manifest), "runtime_locally_ignored": True,
                  "report_sha256": sha(HERE / "results/run_001/report.json"),
                  "audit_sha256": sha(HERE / "results/run_001/audit.json"),
                  "host_adapter_sha256": sha(HERE / "host.py")}, indent=2))
