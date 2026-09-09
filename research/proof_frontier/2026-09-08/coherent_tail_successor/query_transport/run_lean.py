from pathlib import Path
import subprocess,sys,json,time,hashlib
repo=Path('/tmp/minidregg-coherent-query-transport-20260908')
module=sys.argv[1]
tag=sys.argv[2]
root=Path(__file__).resolve().parent
out=repo/'.lake/build/lib/lean'/Path(module).with_suffix('.olean')
out.parent.mkdir(parents=True,exist_ok=True)
cmd=['lake','env','lean','-o',str(out),module]
source_sha256=hashlib.sha256((repo/module).read_bytes()).hexdigest()
started=time.time()
r=subprocess.run(cmd,cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/'checks'/f'{tag}.log').write_text(r.stdout)
record={'command':cmd,'cwd':str(repo),'exit_code':r.returncode,'source_sha256':source_sha256,'source_unchanged':source_sha256==hashlib.sha256((repo/module).read_bytes()).hexdigest(),'elapsed_s':time.time()-started,'log':str(root/'checks'/f'{tag}.log')}
(root/'checks'/f'{tag}.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
if r.returncode:print(r.stdout[-14000:])
sys.exit(r.returncode)
