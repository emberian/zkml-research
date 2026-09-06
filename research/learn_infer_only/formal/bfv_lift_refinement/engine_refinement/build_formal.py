#!/usr/bin/env python3
import os,subprocess,json,time
from pathlib import Path
root=Path(__file__).resolve().parent;companion=Path('/Users/ember/dev/minidregg');build=root/'.build';(build/'Compiler').mkdir(parents=True,exist_ok=True)
for obj in (companion/'.lake/build/lib/lean/Compiler').iterdir():
    target=build/'Compiler'/obj.name
    if not target.exists():target.symlink_to(obj)
env=os.environ.copy();env['LEAN_PATH']=str(build)+':'+env['LEAN_PATH']
records=[];index=1
while (root/f'build-{index:03}.json').exists():index+=1
steps=[]
if not (build/'Compiler/BFVScaleLiftRefinement.olean').exists():steps.append((root.parent,root.parent/'Compiler/BFVScaleLiftRefinement.lean',build/'Compiler/BFVScaleLiftRefinement.olean'))
steps.append((root,root/'Compiler/FheRnsScaleDecomposition.lean',build/'Compiler/FheRnsScaleDecomposition.olean'))
for cwd,source,out in steps:
    command=['lean','-o',str(out),str(source)];start=time.monotonic();r=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True)
    records.append(dict(command=command,cwd=str(cwd),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,elapsed_seconds=time.monotonic()-start));(root/f'build-{index:03}.json').write_text(json.dumps(records,indent=2)+'\n');print(r.stdout+r.stderr)
    if r.returncode:raise SystemExit(r.returncode)
