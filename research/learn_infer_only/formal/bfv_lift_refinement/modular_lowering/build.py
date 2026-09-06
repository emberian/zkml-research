#!/usr/bin/env python3
import json,os,subprocess,time,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;COMP=Path('/Users/ember/dev/minidregg');BUILD=ROOT/'.build';(BUILD/'Compiler').mkdir(parents=True,exist_ok=True)
for base in [ROOT.parent/'target_projection/.build/Compiler',ROOT.parent/'source_certificate/.build/Compiler',COMP/'.lake/build/lib/lean/Compiler',ROOT.parent/'engine_refinement/.build/Compiler',ROOT.parent.parent/'integer_certificate_emission/build/Compiler',ROOT.parent.parent/'integer_certificate_emission/optimization/build/Compiler']:
 for p in base.iterdir():
  target=BUILD/'Compiler'/p.name
  if not target.exists():target.symlink_to(p)
env=os.environ.copy();env['LEAN_PATH']=str(BUILD)+':'+env['LEAN_PATH'];records=[];i=1
while True:
 try:
  with (ROOT/f'build-{i:03}.json').open('x') as reserve:reserve.write('[]\n')
  break
 except FileExistsError:i+=1
for name in sys.argv[1:] or ['FheShoupWord']:
 src=ROOT/f'Compiler/{name}.lean';out=BUILD/f'Compiler/{name}.olean'
 if out.is_symlink():out.unlink()
 cmd=['lean','-o',str(out),str(src)];start=time.monotonic();r=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,text=True)
 records.append(dict(command=cmd,cwd=str(ROOT),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,elapsed_seconds=time.monotonic()-start));(ROOT/f'build-{i:03}.json').write_text(json.dumps(records,indent=2)+'\n');print(r.stdout+r.stderr)
 if r.returncode:raise SystemExit(r.returncode)
