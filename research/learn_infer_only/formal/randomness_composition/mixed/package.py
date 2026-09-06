#!/usr/bin/env python3
"""Package two frozen proposed modules; companion inputs are read-only."""
from pathlib import Path
import difflib,hashlib,json
HERE=Path(__file__).resolve().parent
COMPANION=Path('/Users/ember/dev/minidregg')
MODULES=['Compiler/DisjointOraclePhases.lean','Assurance/ResidentMixedPhases.lean']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    patch=[]
    for rel in MODULES:
        patch.extend(difflib.unified_diff([], (HERE/rel).read_text().splitlines(keepends=True),
            fromfile='/dev/null',tofile='b/'+rel))
    for ns,module,comment in [('Compiler','DisjointOraclePhases','one-cache coupling for disjoint two-phase query strategies'),
                             ('Assurance','ResidentMixedPhases','actual Stage0/EMA shared-cache soundness with exact phase budgets')]:
        before=(COMPANION/(ns+'.lean')).read_text()
        after=before+f'import {ns}.{module} -- {comment}\n'
        patch.extend(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),
            fromfile='a/'+ns+'.lean',tofile='b/'+ns+'.lean'))
    p=HERE/'minidregg-mixed-oracle-phases.patch';p.write_text(''.join(patch))
    sources={rel:sha(HERE/rel) for rel in MODULES}
    (HERE/'results/source_hashes.json').write_text(json.dumps(dict(sources=sources,patch=p.name,patch_sha256=sha(p)),indent=2)+'\n')
    print(json.dumps(dict(sources=sources,patch_sha256=sha(p))))

if __name__=='__main__':main()
