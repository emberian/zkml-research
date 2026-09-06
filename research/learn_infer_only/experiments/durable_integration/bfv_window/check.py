#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time,sys
R=Path(__file__).resolve().parents[3]
F=R/'formal/durable_integration/bfv_window'; B=F/'build'; E=Path(__file__).parent
lean='/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
envrec=json.loads((R/'experiments/results/environment.json').read_text())
paths=next(x['stdout'].strip() for x in envrec['checks'] if x['command']==['lake','env','printenv','LEAN_PATH'])
for ns in ['Theory','Assurance']:
 (B/ns).mkdir(parents=True,exist_ok=True)
 for a in (Path('/Users/ember/dev/minidregg/.lake/build/lib/lean')/ns).iterdir():
  d=B/ns/a.name
  if not d.exists() and not d.is_symlink():d.symlink_to(a)
for a in (R/'formal/durable_integration/build/Assurance').iterdir():
 d=B/'Assurance'/a.name
 if not d.exists() and not d.is_symlink():d.symlink_to(a)
env=dict(os.environ,LEAN_PATH=str(B)+':'+str(R/'formal/durable_integration/build')+':'+paths)
for arg in sys.argv[1:]:
 s=F/arg;t=B/Path(arg).with_suffix('.olean')
 if t.is_symlink():raise RuntimeError('refusing symlink output')
 digest=hashlib.sha256(s.read_bytes()).hexdigest();start=time.time()
 p=subprocess.run([lean,'-o',str(t),str(s)],cwd=F,env=env,capture_output=True,text=True)
 rec=dict(source=str(s),source_sha256=digest,inputs_unchanged=digest==hashlib.sha256(s.read_bytes()).hexdigest(),command=[lean,'-o',str(t),str(s)],cwd=str(F),lean_path=env['LEAN_PATH'],exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-start)
 if p.returncode==0:rec['olean_sha256']=hashlib.sha256(t.read_bytes()).hexdigest()
 n=len(list(E.glob('lean_'+s.stem+'_*.json')))+1
 (E/f'lean_{s.stem}_{n:02}.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(s.stem,p.returncode,p.stdout,p.stderr,flush=True)
 if p.returncode:sys.exit(p.returncode)
