#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time,sys
R=Path(__file__).resolve().parents[3];E=Path(__file__).parent;F=R/'formal/durable_integration/window_frame';B=F/'build'
ref=json.loads((R/'experiments/durable_integration/bfv_window/lean_CiphertextWindowWitness_06.json').read_text());old=R/'formal/durable_integration/bfv_window/build'
for ns in ['Theory','Assurance']:
 (B/ns).mkdir(parents=True,exist_ok=True)
 for p in (old/ns).iterdir():
  dest=B/ns/p.name
  if not dest.exists() and not dest.is_symlink():dest.symlink_to(p)
env=dict(os.environ,LEAN_PATH=str(B)+':'+ref['lean_path'])
for rel in sys.argv[1:]:
 p=F/rel;dest=B/Path(rel).with_suffix('.olean');assert not dest.is_symlink()
 h=hashlib.sha256(p.read_bytes()).hexdigest();cmd=[ref['command'][0],'-o',str(dest),str(p)];t=time.time()
 out=subprocess.run(cmd,cwd=F,env=env,capture_output=True,text=True)
 rec=dict(command=cmd,cwd=str(F),lean_path=env['LEAN_PATH'],source_sha256=h,inputs_unchanged=h==hashlib.sha256(p.read_bytes()).hexdigest(),exit_code=out.returncode,stdout=out.stdout,stderr=out.stderr,elapsed_seconds=time.time()-t)
 if out.returncode==0:rec['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
 n=len(list(E.glob('lean_'+p.stem+'_*.json')))+1;(E/f'lean_{p.stem}_{n:02}.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(p.stem,out.returncode,out.stdout,out.stderr,flush=True)
 if out.returncode:raise SystemExit(out.returncode)
