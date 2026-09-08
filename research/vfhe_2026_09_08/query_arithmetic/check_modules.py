#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,time
P=Path(__file__).resolve().parent
rows=[]
for name in ['BfvQueryMul','BfvQueryRow','BfvQueryWitness','BfvQueryTeeth']:
 cmd=['lake','env','bash','-c','LEAN_PATH="$1/build:$LEAN_PATH" lean --root="$1" -o "$1/build/Compiler/$2.olean" "$1/Compiler/$2.lean"','check',str(P),name]
 start=time.monotonic()
 with (P/f'results/final-{name}.log').open('w') as log:r=subprocess.run(cmd,cwd='/Users/ember/dev/minidregg',stdout=log,stderr=subprocess.STDOUT)
 rows.append({'module':'Compiler.'+name,'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start})
 (P/'results/validation.json').write_text(json.dumps(rows,indent=2)+'\n')
 if r.returncode:raise SystemExit(r.returncode)
 print(name,'PASS',flush=True)
