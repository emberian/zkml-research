"""Run the project's actual boundary gate on a read-only source overlay."""
from pathlib import Path
import shutil
import subprocess, os, shutil
root=Path('/Users/ember/dev/minidregg')
base=Path(__file__).resolve().parent
print(subprocess.check_output(['df','-h','/System/Volumes/Data'],text=True),flush=True)
if shutil.disk_usage('/System/Volumes/Data').free < 30 * 2**30:
 raise SystemExit('Disk below 30 GiB; paused')
snapshot=base/'build/boundary-overlay'; snapshot.mkdir(exist_ok=True)
files=subprocess.check_output(['git','-C',str(root),'ls-files','-z','--','*.lean']).decode().split('\0')
files=[f for f in files if f]
for f in files:
 p=snapshot/f;p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists():p.symlink_to(root/f)
for p in (base/'source/Selvage').glob('*.lean'):
 dest=snapshot/'Selvage'/p.name
 if dest.is_symlink():dest.unlink() # Only a symlink this script created, never its target.
 shutil.copy2(p,dest)
for f in ['scripts/check-import-boundary.sh','scripts/lean_imports.py']:
 p=snapshot/f;p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists():p.symlink_to(root/f)
if not (snapshot/'.git').exists():subprocess.run(['git','init','-q',str(snapshot)],check=True)
allfiles=files+[str(p.relative_to(base/'source')) for p in (base/'source/Selvage').glob('*.lean')]
for i in range(0,len(allfiles),200):
 subprocess.run(['git','-C',str(snapshot),'add','--']+allfiles[i:i+200],check=True)
cmd=['bash',str(snapshot/'scripts/check-import-boundary.sh')]
r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
(base/'import-boundary.log').write_text('COMMAND '+repr(cmd)+'\n'+r.stdout+'\nEXIT '+str(r.returncode)+'\n')
print(r.stdout);raise SystemExit(r.returncode)
