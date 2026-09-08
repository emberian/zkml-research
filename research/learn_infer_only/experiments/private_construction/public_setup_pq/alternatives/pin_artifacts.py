"""Pin named public sources and this lane's review artifacts."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
sources = [MIRROR / f'{x}.pdf' for x in
           ['2015/017','2025/1613','2025/2232','2011/501','2007/432','2015/608']]
reuse = [
    HERE.parent/'notes/AUDIT.md', HERE.parent/'costs/FEASIBILITY.md',
    HERE.parent/'costs/results.json',
    HERE.parents[1]/'designated_span/crypto/rows.json',
    HERE.parents[2]/'adversarial_review/public_setup_pq/quantitative_regularity/BOUND.md',
]
owned = [HERE/x for x in ['AUDIT.md','SMUDGED_FIXED_COORDINATE.md','SOURCES.md',
                         'CHECKPOINT.md','public_arithmetic.py','results.json',
                         'public_arithmetic.stdout.json','pin_artifacts.py','.gitignore']]
owned += sorted((HERE/'searches').glob('*.json'))
out = {'source_pdfs': [pin(x) for x in sources],
       'reused_frozen_public_inputs': [pin(x) for x in reuse],
       'owned_artifacts': [pin(x) for x in owned],
       'scope': 'Source/math/public arithmetic only; no cryptographic execution.'}
assert (HERE/'results.json').read_bytes() == (HERE/'public_arithmetic.stdout.json').read_bytes()
text = json.dumps(out, indent=2)+'\n'
(HERE/'MANIFEST.json').write_text(text)
print(text,end='')
