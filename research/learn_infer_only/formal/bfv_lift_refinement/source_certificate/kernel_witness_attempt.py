#!/usr/bin/env python3
import json,os,subprocess,time
from pathlib import Path
root=Path(__file__).resolve().parent;build=root/'.build';env=os.environ.copy();env['LEAN_PATH']=str(build)+':'+env['LEAN_PATH']
cmd=['lean','-o',str(build/'Compiler/FheSourceCertificateKernelWitness.olean'),str(build/'Compiler/FheSourceCertificateKernelWitness.lean')];start=time.monotonic()
try:
 r=subprocess.run(cmd,cwd=build,env=env,capture_output=True,text=True,timeout=60);record=dict(command=cmd,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr)
except subprocess.TimeoutExpired as e:
 record=dict(command=cmd,exit_code='timeout',timeout_seconds=60,stdout=(e.stdout or b'').decode(),stderr=(e.stderr or b'').decode())
record['elapsed_seconds']=time.monotonic()-start;(root/'kernel-witness-attempt.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
