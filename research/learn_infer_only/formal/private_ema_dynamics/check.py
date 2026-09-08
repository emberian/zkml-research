import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parent
RESULTS=ROOT/'results'
ENV=json.loads((RESULTS/'environment.json').read_text())
source=ROOT/'Theory/PrivateEmaDynamics.lean'
index=1
while (RESULTS/f'lean_{index:03d}.json').exists():index+=1
command=[ENV['lean'],str(source)]
t=time.monotonic();p=subprocess.run(command,cwd=ROOT,env=dict(os.environ,LEAN_PATH=ENV['lean_path']),text=True,capture_output=True)
r={'command':command,'cwd':str(ROOT),'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-t,
   'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'stdout':p.stdout,'stderr':p.stderr}
(RESULTS/f'lean_{index:03d}.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2));raise SystemExit(p.returncode)
