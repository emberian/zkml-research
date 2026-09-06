#!/usr/bin/env python3
"""Capture exact local source spans and hashes, without fetching or editing code."""
from pathlib import Path
import hashlib
import json
HERE = Path(__file__).resolve().parent
base = Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv')
spans = {
 'keys/public_key.rs': [(24,36), (46,102)],
 'keys/secret_key.rs': [(40,52), (101,145), (198,262)],
 'plaintext.rs': [(51,64)],
 'parameters.rs': [(417,447)],
 'ops/mod.rs': [(15,68), (110,164), (229,246)],
}
records = []
for relative, ranges in spans.items():
    p = base / relative
    data = p.read_bytes()
    lines = data.decode().splitlines()
    records.append(dict(path=str(p), sha256=hashlib.sha256(data).hexdigest(),
                        spans=[dict(start=a,end=b,text='\n'.join(lines[a-1:b])) for a,b in ranges]))
(HERE/'source_spans.json').write_text(json.dumps(records, indent=2)+'\n')
print(json.dumps({r['path']:r['sha256'] for r in records}, indent=2))
