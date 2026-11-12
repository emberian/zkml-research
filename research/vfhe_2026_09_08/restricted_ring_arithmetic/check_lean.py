#!/usr/bin/env python3
"""Focused Lean checks using retained predecessor oleans; never a full build."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
MAIN=Path('/Users/ember/dev/minidregg')
LEAN=Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean')
source,tag=sys.argv[1:3]
out=ROOT/'results'/tag
assert not out.with_suffix('.json').exists(), 'Do not overwrite retained checks'
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=MAIN,text=True).strip()
overlays=[ROOT/'build',ROOT.parent/'query_native_emitter/build',ROOT.parent/'compiler_cost_successor/build',ROOT.parent/'arithmetic_coverage/build']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,overlays))+':'+base
src=ROOT/source
command=[str(LEAN),'-o',str(ROOT/'build'/Path(source).with_suffix('.olean')),source]
if len(sys.argv)>3 and sys.argv[3]=='--run':
 command=[str(LEAN),'--run',source]+sys.argv[4:]
record={'argv':command,'cwd':str(ROOT),'LEAN_PATH':env['LEAN_PATH'],'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
 'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'timeout_seconds':180}
t=time.perf_counter()
with out.with_suffix('.stdout').open('wb') as stdout,out.with_suffix('.stderr').open('wb') as stderr:
 try:
  p=subprocess.run(command,cwd=ROOT,env=env,stdout=stdout,stderr=stderr,timeout=180)
  record['exit_code']=p.returncode
 except subprocess.TimeoutExpired:
  record['exit_code']=None;record['timeout']=True
record['elapsed_seconds']=time.perf_counter()-t
out.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
print(out.with_suffix('.stdout').read_text())
print(out.with_suffix('.stderr').read_text())
raise SystemExit(0 if record['exit_code']==0 else 1)
