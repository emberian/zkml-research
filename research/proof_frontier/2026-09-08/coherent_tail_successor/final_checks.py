from pathlib import Path
import json,subprocess,sys,hashlib
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-coherent-tail-successor-20260908')
mods=json.loads((out/'declaration-names.json').read_text())
for i,mod in enumerate(mods,1):
 rel=mod.replace('.','/')+'.lean'
 p=repo/rel
 cpath=out/'checks'/f'final-{i:02d}.json'
 if cpath.exists():
  c=json.loads(cpath.read_text())
  if c['exit_code']==0 and c['source_unchanged'] and c['source_sha256']==hashlib.sha256(p.read_bytes()).hexdigest() and Path(c['log']).read_bytes()==b'':
   print('retained exact green check',mod,flush=True)
   continue
 r=subprocess.run([sys.executable,str(out/'run_lean.py'),rel,f'final-{i:02d}'])
 if r.returncode:sys.exit(r.returncode)
 assert (out/'checks'/f'final-{i:02d}.log').read_bytes()==b''
