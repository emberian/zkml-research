#!/usr/bin/env python3
"""Pin executable backend inputs for the one shared journal/service run."""
import hashlib
import json
from pathlib import Path
import transport as t

HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    origins=json.loads((HERE/'ORIGINS.json').read_text())
    paths=['transport.py','basis.py','registry.json','fixture.json','expansion/__init__.py','expansion/public_expander.py']
    paths += [p for p in origins if p.startswith('source/fast/') or p.startswith('codec/')]
    paths=sorted(set(paths))
    p=t.params('candidate_full')
    out={'owned':{rel:sha(HERE/rel) for rel in paths},'profile':'candidate_full','parameters':p.__dict__,
         'delta':p.delta,'seed_policy':t.SEED_POLICY,'seed_bits':t.SEED_BITS,'magic':t.MAGIC.decode(),
         'format_version':t.FORMAT_VERSION,
         'python':str(HERE.parent/'ring_implementation/.venv/bin/python'),
         'byte_identical_copied_origins':{rel:row for rel,row in origins.items() if rel in paths and rel!='transport.py'},
         'scope':'Prelaunch executable inputs; one fresh shared journal run only; no Gaussian/expansion/setup execution by this pin script'}
    (HERE/'SOURCE_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'source_files':len(paths),'transport_sha256':out['owned']['transport.py'],
                      'source_pins_sha256':sha(HERE/'SOURCE_PINS.json')}))

if __name__=='__main__':main()
