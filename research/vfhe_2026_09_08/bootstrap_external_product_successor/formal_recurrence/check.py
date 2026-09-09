#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,time
ROOT=Path(__file__).resolve().parent
modules=list(json.loads((ROOT/'declarations.json').read_text()))
results=[]
for i,m in enumerate(modules):
    out=ROOT/'build'/Path(m).with_suffix('.olean')
    cmd=['lake','env','bash','-c','LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$3" "$4"','lean-check',str(ROOT/'build'),str(ROOT),str(out),str(ROOT/m)]
    start=time.monotonic()
    with (ROOT/'results'/f'final-{i+1}.log').open('w') as log:
        r=subprocess.run(cmd,cwd='/Users/ember/dev/minidregg',stdout=log,stderr=subprocess.STDOUT)
    results.append({'module':m,'exit':r.returncode,'seconds':time.monotonic()-start})
    print(m,r.returncode,flush=True)
    if r.returncode:break
(ROOT/'results'/'validation.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(0 if len(results)==len(modules) and all(x['exit']==0 for x in results) else 1)
