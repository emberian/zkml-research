"""Seal only this review and rehash the explicitly enumerated public inputs."""
import datetime
import hashlib
import json
from pathlib import Path

here=Path(__file__).resolve().parent
results=json.loads((here/'results.json').read_text())
for row in results['inputs']:
    p=Path(row['path'])
    assert 'private' not in p.parts and p.name!='client_key.bin'
    if 'runtime' in p.parts:
        assert p.parent.as_posix().endswith('/emitted_long_run/runtime/run001/public')
    data=p.read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
names=['REPORT.md','SOURCES.md','STATUS.md','NEXT.md','check_public.py','check.stdout.json','check.stderr.txt','results.json','seal_review.py']
files=[]
for name in names:
    data=(here/name).read_bytes()
    files.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
manifest={'claim':'EXECUTED independent public review seal','sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'disposition':'accepted within finite public execution scope; private matches attributed',
    'input_files_rehashed_unchanged':len(results['inputs']),'new_crypto_invocations':0,'private_files_read':0,
    'files':files}
payload=json.dumps(manifest,indent=2,sort_keys=True)+'\n'
(here/'MANIFEST.json').write_text(payload)
print(payload,end='')
