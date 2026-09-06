#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time
E=Path(__file__).parent;R=E.parents[2];F=R/'formal/durable_integration/bfv_window'
rec=json.loads(sorted(E.glob('lean_CiphertextWindowWitness_*.json'))[-1].read_text())
env=dict(os.environ,LEAN_PATH=rec['lean_path']);src=E/'InspectWindow.lean';cmd=[rec['command'][0],str(src.resolve())];digest=hashlib.sha256(src.read_bytes()).hexdigest();t=time.time()
deps={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in F.glob('*/*.lean')}
try:
 p=subprocess.run(cmd,cwd=E,env=env,capture_output=True,text=True,timeout=60)
except subprocess.TimeoutExpired as ex:
 p=subprocess.CompletedProcess(cmd,124,(ex.stdout or b'').decode() if isinstance(ex.stdout,bytes) else (ex.stdout or ''),(ex.stderr or b'').decode() if isinstance(ex.stderr,bytes) else (ex.stderr or ''))
out=dict(command=cmd,cwd=str(E.resolve()),lean_path=env['LEAN_PATH'],exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t,source_sha256=digest,dependency_source_sha256=deps,dependencies_unchanged=all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in deps.items()),inputs_unchanged=digest==hashlib.sha256(src.read_bytes()).hexdigest())
n=len(list(E.glob('inspect_*.json')))+1;(E/f'inspect_{n:02}.json').write_text(json.dumps(out,indent=2)+'\n');(E/'inspect.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));raise SystemExit(p.returncode)
