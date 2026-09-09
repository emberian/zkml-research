#!/usr/bin/env python3
"""Record three acceptances and the update-button rejection in Node/WASM."""
from pathlib import Path
import datetime, hashlib, json, subprocess, time

root = Path(__file__).resolve().parent
out, err = root/'results/verify-node.json', root/'results/verify-node.stderr'
assert not out.exists() and not err.exists(), 'refuse to replace a retained run'
start = time.monotonic()
record = {'argv': ['node', 'verify.mjs'], 'cwd': str(root),
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
with out.open('x') as stdout, err.open('x') as stderr:
    p = subprocess.run(record['argv'], cwd=root, stdout=stdout, stderr=stderr, timeout=180)
record.update(returncode=p.returncode, elapsed_seconds=time.monotonic()-start,
              finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              stdout_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),
              stderr_sha256=hashlib.sha256(err.read_bytes()).hexdigest())
with (root/'results/node-command.json').open('x') as f:
    json.dump(record, f, indent=2); f.write('\n')
print(json.dumps(record, indent=2))
raise SystemExit(p.returncode)
