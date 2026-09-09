from pathlib import Path
import os,sys,json,subprocess,time,hashlib
p=Path(__file__).resolve().parent
prior=json.loads((p.parent.parent/'nonlinear_performance/formal/results/RangeKeyswitchInfer_003.json').read_text())
env=dict(os.environ,LEAN_PATH=str(p/'build')+':'+str(p.parent.parent/'nonlinear_performance/backend/build')+':'+prior['LEAN_PATH'])
for srcdir in [p.parent.parent/'nonlinear_performance/formal/build/Compiler',p.parent.parent/'nonlinear_performance/backend/build/Compiler']:
 for f in srcdir.glob('*.olean'):
  dst=p/'build/Compiler'/f.name
  dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists(): dst.symlink_to(f.resolve())
(p/'checks').mkdir(exist_ok=True)
name=sys.argv[1]; number=len(list((p/'checks').glob(name+'*.json')))+1
cmd=[prior['command'][0],'-o','build/Compiler/'+name+'.olean','Compiler/'+name+'.lean'];start=time.perf_counter()
r=subprocess.run(cmd,cwd=p,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
f=p/'checks'/f'{name}_{number:03d}'
f.with_suffix('.log').write_text(r.stdout)
f.with_suffix('.json').write_text(json.dumps(dict(command=cmd,cwd=str(p),LEAN_PATH=env['LEAN_PATH'],exit=r.returncode,seconds=time.perf_counter()-start,source_sha256=hashlib.sha256((p/'Compiler'/f'{name}.lean').read_bytes()).hexdigest()),indent=2)+'\n')
print(r.stdout);print('exit',r.returncode);sys.exit(r.returncode)
