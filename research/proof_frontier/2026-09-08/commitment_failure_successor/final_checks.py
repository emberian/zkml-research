from pathlib import Path
import json,subprocess,sys
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-commitment-failure-successor-20260908')
mods=json.loads((out/'declaration-names.json').read_text())
for i,mod in enumerate(mods,1):
 rel=mod.replace('.','/')+'.lean'
 p=repo/rel
 p.write_text(p.read_text().rstrip()+'\n')
 r=subprocess.run([sys.executable,str(out/'run_lean.py'),rel,f'final-{i:02d}'])
 if r.returncode:sys.exit(r.returncode)
 assert (out/'checks'/f'final-{i:02d}.log').read_bytes()==b''
