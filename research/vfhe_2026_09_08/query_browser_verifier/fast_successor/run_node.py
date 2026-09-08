#!/usr/bin/env python3
"""One bounded replay of saved public proofs through the exported WASM consumer."""
from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)
if (OUT / 'node-command.json').exists() or (OUT / 'verify-node.json').exists():
    raise SystemExit('Retained execution exists; this runner will not overwrite it.')
sha = lambda data: hashlib.sha256(data).hexdigest()
inputs = [ROOT / 'package_bundle.py', ROOT / 'run_node.py', ROOT / 'query-case.json',
          ROOT / 'source_provenance.json']
inputs += sorted(path for folder in ('web', 'fixtures') for path in (ROOT / folder).rglob('*') if path.is_file())
pins = {str(path.relative_to(ROOT)): {'bytes': path.stat().st_size, 'sha256': sha(path.read_bytes())} for path in inputs}
(ROOT / 'SOURCE_PINS.json').write_text(json.dumps(pins, indent=2) + '\n')
command = [shutil.which('node'), 'web/verify-recorded-query.mjs']
record = {'argv': command, 'cwd': str(ROOT), 'timeout_seconds': 180,
          'source_pins_sha256': sha((ROOT / 'SOURCE_PINS.json').read_bytes()),
          'start_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
started = time.perf_counter()
try:
    with (OUT / 'verify-node.json').open('wb') as stdout, (OUT / 'verify-node.stderr').open('wb') as stderr:
        result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr, timeout=180, check=False)
    record['exit_code'] = result.returncode
except subprocess.TimeoutExpired:
    record['timeout'] = True
    record['exit_code'] = None
record['elapsed_seconds'] = time.perf_counter() - started
record['end_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['inputs_unchanged'] = all(sha((ROOT / rel).read_bytes()) == pin['sha256'] for rel, pin in pins.items())
record['stdout_sha256'] = sha((OUT / 'verify-node.json').read_bytes())
record['stderr_sha256'] = sha((OUT / 'verify-node.stderr').read_bytes())
(OUT / 'node-command.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(0 if record['exit_code'] == 0 and record['inputs_unchanged'] else 1)
