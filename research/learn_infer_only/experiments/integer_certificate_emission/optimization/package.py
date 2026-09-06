#!/usr/bin/env python3
"""Package only this optimization tranche; verify the preserved predecessor."""
from pathlib import Path
import gzip
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
FORMAL=ROOT/'formal/integer_certificate_emission/optimization'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    old=json.loads((ROOT/'experiments/integer_certificate_emission/artifact_hashes.json').read_text())
    assert all(sha(ROOT/p)==h for p,h in old['artifacts'].items())
    compressed={}
    for name in ['large_simplified_descriptor.json','large_simplified_CSE_descriptor.json']:
        source=HERE/name;packed=HERE/(name+'.gz')
        raw=source.read_bytes();data=gzip.compress(raw,mtime=0);packed.write_bytes(data)
        assert gzip.decompress(data)==raw
        compressed[name]=dict(raw_sha256=sha(source),gzip_sha256=sha(packed),
                              raw_bytes=len(raw),gzip_bytes=len(data))
    files=[FORMAL/'OPTIMIZATION.md']+sorted((FORMAL/'Compiler').glob('*.lean'))
    files+=sorted(FORMAL.glob('*.patch'))+sorted(HERE.glob('*.py'))
    files+=[HERE/n for n in ['results.json','review_01.json','small_simplified_descriptor.json','small_simplified_CSE_descriptor.json']]
    record=dict(first_tranche_unchanged=True,compressed=compressed,
                artifacts={str(p.relative_to(ROOT)):sha(p) for p in files})
    (HERE/'artifact_hashes.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(compressed,indent=2))

if __name__=='__main__':main()
