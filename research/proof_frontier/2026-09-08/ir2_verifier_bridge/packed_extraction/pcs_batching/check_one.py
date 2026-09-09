from pathlib import Path
import subprocess,sys,time,json,shutil
root=Path(__file__).resolve().parent
isolate=Path('/tmp/minidregg-pcs-batching-20260908')
name,run=sys.argv[1:3]
src=root/'Selvage'/f'{name}.lean'
shutil.copyfile(src,isolate/'Selvage'/src.name)
cmd=['lake','env','lean','-o',str(isolate/'.lake/build/lib/lean/Selvage'/f'{name}.olean'),f'Selvage/{name}.lean']
t=time.time();r=subprocess.run(cmd,cwd=isolate,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(root/'checks'/f'{run}.log').write_text(r.stdout)
(root/'checks'/f'{run}.json').write_text(json.dumps(dict(command=cmd,cwd=str(isolate),exit=r.returncode,seconds=time.time()-t),indent=2)+'\n')
print(r.returncode);print(r.stdout)
sys.exit(r.returncode)
