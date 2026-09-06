#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time
E=Path(__file__).parent;R=E.parents[2];F=R/'formal/durable_integration'
rec=json.loads(sorted(E.glob('lean_ResidentEmaWitness_*.json'))[-1].read_text())
env=dict(os.environ,LEAN_PATH=rec['lean_path']);src=E/'InspectEma.lean'
cmd=[rec['command'][0],str(src.resolve())];t=time.time()
p=subprocess.run(cmd,cwd=E,env=env,capture_output=True,text=True)
sources={}
for rel in ['Compiler/ResidentEmaCertificate.lean','Assurance/ResidentEmaCell.lean','Assurance/ResidentEmaRelease.lean','Assurance/ResidentEmaWitness.lean']:
 f=F/rel;check=json.loads(sorted(E.glob('lean_'+f.stem+'_*.json'))[-1].read_text());h=hashlib.sha256(f.read_bytes()).hexdigest()
 assert check['exit_code']==0 and check['source_sha256']==h and check['inputs_unchanged'];sources[rel]=h
out=dict(command=cmd,cwd=str(E.resolve()),lean_path=env['LEAN_PATH'],exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),module_sha256=sources)
if (E/'inspect.json').exists() and not list(E.glob('inspect_*.json')):(E/'inspect_01.json').write_bytes((E/'inspect.json').read_bytes())
n=len(list(E.glob('inspect_*.json')))+1;(E/f'inspect_{n:02}.json').write_text(json.dumps(out,indent=2)+'\n');(E/'inspect.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));raise SystemExit(p.returncode)
