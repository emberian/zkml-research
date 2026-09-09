#!/usr/bin/env python3
"""Inventory the completed public package; no crypto, compiler, or secret reads."""
from pathlib import Path
import hashlib,json,subprocess
root=Path(__file__).resolve().parent
names=subprocess.check_output(['rg','--files','--hidden','-g','!.git'],cwd=root,text=True).splitlines()
files=[]
for name in sorted(names):
 if name=='MANIFEST.json':continue
 p=root/name;b=p.read_bytes();files.append({'path':name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
result={'schema':'selected-exact-external-product-completion-v1','scope':'Complete selected sparse first external product, fresh public GGSW key identity; full PBS held/unlaunched.','proof_sha256':'89ee3f4e6d61ec11bb3c9fec0404bb2b32ced48a42efb117622bbb627a8dd8c7','file_count':len(files),'public_source_bytes':sum(f['bytes'] for f in files),'files':files,'ignored_trace_and_binaries':'Exact paths and hashes retained in proof_pins.json; source and public proof are inventoried here.'}
p=root/'MANIFEST.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'manifest_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'file_count':len(files),'bytes':result['public_source_bytes']}))
