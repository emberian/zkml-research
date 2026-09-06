#!/usr/bin/env python3
"""Keep deterministic compact copies of large emissions and pin delivered artifacts."""
from pathlib import Path
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    emissions = {}
    for name in ['large_descriptor.json', 'large_shared_descriptor.json']:
        raw = (HERE/name).read_bytes()
        packed = gzip.compress(raw, mtime=0)
        (HERE/(name+'.gz')).write_bytes(packed)
        assert gzip.decompress(packed) == raw
        emissions[name] = dict(raw_sha256=sha(raw),gzip_sha256=sha(packed),
                               raw_bytes=len(raw),gzip_bytes=len(packed))
    files = [ROOT/'INTEGER_CERTIFICATE_EMISSION.md']
    files += sorted((ROOT/'formal/integer_certificate_emission/Compiler').glob('*.lean'))
    files += sorted((ROOT/'formal/integer_certificate_emission').glob('*.patch'))
    files += sorted(HERE.glob('*.py'))
    files += [HERE/name for name in ['checker_results.json','checker_vectors.json','descriptor.json',
                                    'large_results.json','large_CSE_costs.json','review_01.json']]
    evidence = dict(emissions=emissions, artifacts={str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in files})
    (HERE/'artifact_hashes.json').write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(emissions,indent=2))

if __name__=='__main__':
    main()
