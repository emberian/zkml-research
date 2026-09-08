#!/usr/bin/env python3
"""Single-file Lean checks, preserving each attempt without companion writes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
ENV = json.loads((RESULTS / "environment.json").read_text())
SOURCE = HERE / "Theory/PrivateAddressEma.lean"
index = 1
while (RESULTS / f"lean_{index:03d}.json").exists():
    index += 1
command = [ENV["lean"], str(SOURCE)]
start = time.monotonic()
p = subprocess.run(command, cwd=HERE, env=dict(os.environ, LEAN_PATH=ENV["lean_path"]),
                   text=True, capture_output=True)
record = {"command": command, "cwd": str(HERE), "exit_code": p.returncode,
          "elapsed_seconds": time.monotonic() - start,
          "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          "stdout": p.stdout, "stderr": p.stderr}
(RESULTS / f"lean_{index:03d}.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
raise SystemExit(p.returncode)
