import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent
UTILITY=PRIOR/'utility'
RUNTIME=ROOT/'runtime/run001'
REPORTS=ROOT/'reports/run001'
BIN=PRIOR/'target/release'
load=lambda p:json.loads(Path(p).read_text())

def save(p,obj):
    p=Path(p)
    temporary=p.with_suffix(p.suffix+'.tmp')
    temporary.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    temporary.replace(p)

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def meta(p):
    p=Path(p)
    return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}

def verify_freeze():
    f=load(ROOT/'freeze.json')
    for p,row in f['files'].items():assert meta(p)==row,p
    return f

def lines(p):
    return [json.loads(s) for s in Path(p).read_text().splitlines()]
