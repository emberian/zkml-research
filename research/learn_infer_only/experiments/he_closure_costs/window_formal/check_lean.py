#!/usr/bin/env python3
"""Compile only owned proposed modules; companion sources/builds are read-only."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
FORMAL = ROOT / "formal/he_closure_costs"
BUILD = FORMAL / "build"
HERE = Path(__file__).resolve().parent
LEAN = Path("/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean")
environment = json.loads((ROOT / "experiments/results/environment.json").read_text())
paths = next(x["stdout"].strip() for x in environment["checks"]
             if x["command"] == ["lake", "env", "printenv", "LEAN_PATH"])
# Lean resolves a top-level module directory from the first matching path.
# Merge dependency oleans with read-only symlinks; never output through one.
for base in [ROOT / "formal/durable_integration/bfv_window/build", Path("/Users/ember/dev/minidregg/.lake/build/lib/lean")]:
    for artifact in base.rglob("*.olean"):
        relative = artifact.relative_to(base)
        if relative.parts[0] not in ("Theory", "Assurance", "Kernel"):
            continue
        target = BUILD / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
env = dict(os.environ, LEAN_PATH=str(BUILD) + ":" + str(ROOT / "formal/durable_integration/bfv_window/build") + ":" + paths)
modules = sys.argv[1:] or ["Theory/IntegerWindowNoise", "Theory/CiphertextWindowNoise", "Assurance/ResidentBfvWindowNoise", "Assurance/ResidentBfvWindowPhase"]
for module in modules:
    source = FORMAL / (module + ".lean")
    output = BUILD / (module + ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    assert not output.is_symlink()
    command = [str(LEAN), "-o", str(output), str(source)]
    start = time.monotonic()
    run = subprocess.run(command, cwd=FORMAL, env=env, capture_output=True, text=True)
    record = dict(command=command, cwd=str(FORMAL), lean_path=env["LEAN_PATH"],
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr,
                  elapsed_seconds=time.monotonic() - start)
    if run.returncode == 0:
        record["olean_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
    stem = source.stem
    serial = len(list(HERE.glob("lean_" + stem + "_*.json"))) + 1
    (HERE / f"lean_{stem}_{serial:02d}.json").write_text(json.dumps(record, indent=2) + "\n")
    print(stem, run.returncode, run.stdout, run.stderr, flush=True)
    if run.returncode:
        sys.exit(run.returncode)
