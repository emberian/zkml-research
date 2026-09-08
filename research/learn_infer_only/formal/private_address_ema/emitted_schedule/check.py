#!/usr/bin/env python3
"""Read-only dependency overlay; only this proposal's artifacts are compiled."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
RESULTS = HERE/'results'
base = json.loads((HERE.parent/'results/environment.json').read_text())
cfg = RESULTS/'environment.json'
if not cfg.exists():
    scratch = Path(tempfile.mkdtemp(prefix='ema_schedule_'))
    overlay = scratch/'olean'
    existing = Path('/Users/ember/dev/minidregg/.lake/build/lib/lean')
    for current, dirs, files in os.walk(existing):
        target = overlay/Path(current).relative_to(existing)
        target.mkdir(parents=True,exist_ok=True)
        for name in files:
            (target/name).symlink_to(Path(current)/name)
    env = dict(os.environ,LEAN_PATH=str(overlay)+':'+base['lean_path'])
    dep = HERE.parent/'Theory/PrivateAddressEma.lean'
    output = overlay/'Theory/PrivateAddressEma.olean'
    command=[base['lean'],'-o',str(output),str(dep)]
    p=subprocess.run(command,cwd=HERE.parent,env=env,text=True,capture_output=True)
    assert p.returncode==0,(p.stdout,p.stderr)
    cfg.write_text(json.dumps(dict(lean=base['lean'],lean_path=env['LEAN_PATH'],
        overlay=str(overlay),dependency_command=command,dependency_sha256=hashlib.sha256(dep.read_bytes()).hexdigest(),
        dependency_stdout=p.stdout,dependency_stderr=p.stderr),indent=2)+'\n')
config=json.loads(cfg.read_text())
source=HERE/'Compiler/PrivateAddressEmaSchedule.lean'
index=1
while (RESULTS/f'lean_{index:03d}.json').exists(): index+=1
command=[config['lean'],'-o',str(Path(config['overlay'])/'Compiler/PrivateAddressEmaSchedule.olean'),str(source)]
before_hash=hashlib.sha256(source.read_bytes()).hexdigest()
p=subprocess.run(command,cwd=HERE,env=dict(os.environ,LEAN_PATH=config['lean_path']),text=True,capture_output=True)
after_hash=hashlib.sha256(source.read_bytes()).hexdigest()
record=dict(command=command,cwd=str(HERE),exit_code=p.returncode,source_sha256=before_hash,
    source_sha256_after=after_hash,source_unchanged=before_hash==after_hash,stdout=p.stdout,stderr=p.stderr)
(RESULTS/f'lean_{index:03d}.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
raise SystemExit(p.returncode if before_hash==after_hash else 2)
