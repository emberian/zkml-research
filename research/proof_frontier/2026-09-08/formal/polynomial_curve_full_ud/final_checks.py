from pathlib import Path
import subprocess,sys,json
out=Path(__file__).resolve().parent
mods=json.loads((out/'declaration-names.json').read_text())
for i,mod in enumerate(mods,1):
 p=mod.replace('.','/')+'.lean'
 r=subprocess.run([sys.executable,str(out/'run_lean.py'),p,f'freeze-{i:02d}'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(mod,r.returncode,flush=True)
 if r.returncode:print(r.stdout,flush=True);sys.exit(r.returncode)
 assert not (out/'checks'/f'freeze-{i:02d}.log').read_text(),mod
