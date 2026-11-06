from pathlib import Path
import shutil
import subprocess, os, hashlib, json
root=Path('/Users/ember/dev/minidregg')
base=Path(__file__).resolve().parent
print(subprocess.check_output(['df','-h','/System/Volumes/Data'],text=True),flush=True)
if shutil.disk_usage('/System/Volumes/Data').free < 30 * 2**30:
 raise SystemExit('Disk below 30 GiB; paused')
paths=[root/'.lake/build/lib/lean']+list((root/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ, LEAN_PATH=':'.join(map(str,paths)))
cmd=['/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean','-o',str(base/'build/Selvage/BindingGame.olean'),str(base/'source/Selvage/BindingGame.lean')]
source_hash=hashlib.sha256((base/'source/Selvage/BindingGame.lean').read_bytes()).hexdigest()
p=subprocess.Popen(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(base/'build-core.pid').write_text(str(p.pid)+'\n')
output,_=p.communicate()
(base/'build-core.log').write_text('COMMAND '+repr(cmd)+'\n'+output+'\nEXIT '+str(p.returncode)+'\n')
if p.returncode == 0:
 assert source_hash==hashlib.sha256((base/'source/Selvage/BindingGame.lean').read_bytes()).hexdigest(), 'Core changed during compilation'
 (base/'core-build-manifest.json').write_text(json.dumps({'source_sha256':source_hash,'olean_sha256':hashlib.sha256((base/'build/Selvage/BindingGame.olean').read_bytes()).hexdigest()},indent=2)+'\n')
print(output);print('exit',p.returncode)
raise SystemExit(p.returncode)
