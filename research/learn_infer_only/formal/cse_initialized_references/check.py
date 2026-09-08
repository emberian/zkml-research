#!/usr/bin/env python3
"""Isolated output overlay; frozen dependencies are read and compiled, never changed."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
RESULTS = HERE / 'results'
base = json.loads((HERE.parent / 'private_address_ema/results/environment.json').read_text())
config_path = RESULTS / 'environment.json'
if not config_path.exists():
    scratch = Path(tempfile.mkdtemp(prefix='cse_initialized_'))
    overlay = scratch / 'olean'
    existing = Path('/Users/ember/dev/minidregg/.lake/build/lib/lean')
    for current, dirs, files in os.walk(existing):
        target = overlay / Path(current).relative_to(existing)
        target.mkdir(parents=True, exist_ok=True)
        for name in files:
            (target / name).symlink_to(Path(current) / name)
    env = dict(os.environ, LEAN_PATH=str(overlay) + ':' + base['lean_path'])
    records = []
    dependencies = [
        ('private_address_ema', 'Theory/PrivateAddressEma'),
        ('private_address_ema/emitted_schedule', 'Compiler/PrivateAddressEmaSchedule'),
        ('emitted_schedule_execution', 'Compiler/EmittedScheduleExecution'),
        ('cse_structure', 'Compiler/CseStructure'),
    ]
    for package, module in dependencies:
        source = HERE.parent / package / (module + '.lean')
        output = overlay / (module + '.olean')
        if output.is_symlink():
            output.unlink()
        command = [base['lean'], '-o', str(output), str(source)]
        started = time.monotonic()
        p = subprocess.run(command, cwd=source.parent.parent, env=env, text=True, capture_output=True)
        records.append(dict(command=command, cwd=str(source.parent.parent),
            sha256=hashlib.sha256(source.read_bytes()).hexdigest(), exit_code=p.returncode,
            stdout=p.stdout, stderr=p.stderr, seconds=time.monotonic()-started))
        assert p.returncode == 0, records[-1]
    config_path.write_text(json.dumps(dict(lean=base['lean'], lean_path=env['LEAN_PATH'],
        overlay=str(overlay), dependencies=records), indent=2) + '\n')
config = json.loads(config_path.read_text())
source = HERE / 'Compiler/CseInitializedReferences.lean'
index = 1
while (RESULTS / f'lean_{index:03d}.json').exists():
    index += 1
command = [config['lean'], '-o', str(Path(config['overlay']) / 'Compiler/CseInitializedReferences.olean'), str(source)]
before = hashlib.sha256(source.read_bytes()).hexdigest()
started = time.monotonic()
p = subprocess.run(command, cwd=HERE, env=dict(os.environ, LEAN_PATH=config['lean_path']), text=True, capture_output=True)
after = hashlib.sha256(source.read_bytes()).hexdigest()
record = dict(command=command, cwd=str(HERE), exit_code=p.returncode,
    source_sha256=before, source_sha256_after=after, source_unchanged=before==after,
    stdout=p.stdout, stderr=p.stderr, seconds=time.monotonic()-started)
(RESULTS / f'lean_{index:03d}.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(p.returncode if before == after else 2)
