"""Single-module Lean checks in the owned isolated checkout."""
from pathlib import Path
import subprocess, sys, json, time, hashlib

HERE=Path(__file__).resolve().parent
REPO=Path('/tmp/minidregg-efficient-root-opening-20260908')
module,tag=sys.argv[1:3]
dest=REPO/'.lake/build/lib/lean'/Path(module).with_suffix('.olean')
dest.parent.mkdir(parents=True,exist_ok=True)
log=HERE/'logs'/f'{tag}.log';log.parent.mkdir(parents=True,exist_ok=True)
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=digest(REPO/module)
cmd=['lake','env','lean','-o',str(dest),module]
started=time.monotonic()
result=subprocess.run(cmd,cwd=REPO,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log.write_text(result.stdout)
record={'command':cmd,'cwd':str(REPO),'exit_code':result.returncode,
        'source_sha256':before,'source_unchanged':before==digest(REPO/module),
        'elapsed_s':time.monotonic()-started,'log':str(log)}
log.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
if result.returncode: print(result.stdout)
sys.exit(result.returncode)
