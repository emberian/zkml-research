from pathlib import Path
import os,subprocess,sys,json,time,hashlib
repo=Path('/tmp/minidregg-polynomial-gluing-20260908')
root=Path(__file__).resolve().parent
module=sys.argv[1] if len(sys.argv)>1 else 'Selvage/FullUDSamplingBudget.lean'
tag=sys.argv[2] if len(sys.argv)>2 else 'check'
out=repo/'.lake/build/lib/lean'/Path(module).with_suffix('.olean')
out.parent.mkdir(parents=True,exist_ok=True)
env=os.environ.copy()
path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
env['LEAN_PATH']='/tmp/minidregg-full-ud-babybear-20260908/.lake/build/lib/lean:'+path
cmd=['lean','-o',str(out),module]
source_sha256=hashlib.sha256((repo/module).read_bytes()).hexdigest()
started=time.time()
r=subprocess.run(cmd,cwd=repo,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/'logs'/f'{tag}.log').write_text(r.stdout)
record={'command':cmd,'cwd':str(repo),'lean_path':env['LEAN_PATH'],'exit_code':r.returncode,'source_sha256':source_sha256,'source_unchanged':source_sha256==hashlib.sha256((repo/module).read_bytes()).hexdigest(),'elapsed_s':time.time()-started,'log':str(root/'logs'/f'{tag}.log')}
(root/'logs'/f'{tag}.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
print(r.stdout[-14000:])
sys.exit(r.returncode)
