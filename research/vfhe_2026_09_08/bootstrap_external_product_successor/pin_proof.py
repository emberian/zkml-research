#!/usr/bin/env python3
"""Pin the generated relation and consumer before their single joined proof."""
from pathlib import Path
import datetime, hashlib, json
root=Path(__file__).resolve().parent
assert not (root/'results/proof001').exists(), 'must pin before proof output creation'
def pin(p):
 p=p.resolve(); b=p.read_bytes()
 return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
old=json.loads((root/'capture_pins.json').read_text())
for item in old['files']:
 assert pin(Path(item['path']))==item, item['path']
files=[root/x for x in ['pin_proof.py','run_record.py','capture_pins.json','consumer/Cargo.toml','consumer/Cargo.lock','consumer/target/release/tfhe-external-product-proof','Compiler/TfheCrtRange.lean','build/Compiler/TfheCrtRange.olean']]
files+=list((root/'consumer/src').rglob('*.rs'))
files+=list((root/'fixtures/normal_001').iterdir())
formal=root/'formal_recurrence'
assert (formal/'SOURCE_PINS.json').exists(), 'await formal owner freeze'
files+=[formal/'SOURCE_PINS.json']
for rel,expected in json.loads((formal/'SOURCE_PINS.json').read_text()).items():
 assert pin(formal/rel)['sha256']==expected, rel
for pattern in ['Compiler/*.lean','Theory/*.lean','EmitTfheSparse.lean','build/Compiler/TfheSparse*.olean','build/Theory/*.olean','artifacts/*']:
 files+=list(formal.glob(pattern))
items=[pin(p) for p in sorted(set(files)) if p.is_file()]
result={'schema':'tfhe-selected-external-product-proof-pins-v1','recorded_before_proof_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'capture_pins_rechecked':len(old['files']),'files':items}
p=root/'proof_pins.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'proof_pins':pin(p),'files':len(items),'capture_pins_unchanged':len(old['files'])}))
