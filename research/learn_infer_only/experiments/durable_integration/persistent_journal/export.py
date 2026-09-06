#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time
E=Path(__file__).resolve().parent;R=E.parents[2];F=R/'formal/durable_integration';B=F/'build'
ref=json.loads((R/'experiments/durable_integration/bfv_window/lean_CiphertextWindowWitness_06.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=E/'ExportFixture.lean';dependencies=[F/'Assurance/ResidentDurableIntegration.lean',R/'formal/Assurance/ResidentReleaseContext.lean']
inputs={str(p):sha(p) for p in [source,*dependencies]};cmd=[ref['command'][0],str(source)];t=time.time()
p=subprocess.run(cmd,cwd=E,env=dict(os.environ,LEAN_PATH=ref['lean_path']),capture_output=True,text=True,timeout=60)
record=dict(command=cmd,cwd=str(E),lean_path=ref['lean_path'],exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t,source_sha256=inputs,inputs_unchanged=all(sha(Path(p))==h for p,h in inputs.items()))
n=len(list(E.glob('export_*.json')))+1;(E/f'export_{n:02}.json').write_text(json.dumps(record,indent=2)+'\n')
print(p.returncode,p.stdout,p.stderr)
if p.returncode==0:
 fixture=json.loads(p.stdout);assert all(fixture['checked'].values());(E/'fixture.json').write_text(json.dumps(fixture,indent=2)+'\n')
raise SystemExit(p.returncode)
