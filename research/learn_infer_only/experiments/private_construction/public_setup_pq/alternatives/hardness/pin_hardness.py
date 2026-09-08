"""Hash retained public research artifacts; no crypto or estimator invocation."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
EXPERIMENTS = HERE.parents[3]
OLD = EXPERIMENTS / 'he_closure_costs/estimator'
ESTIMATOR = OLD / 'runtime/pinned-estimator'

def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

frozen = json.loads((HERE.parent / 'MANIFEST.json').read_text())
checked_frozen = []
for category in ['source_pdfs', 'reused_frozen_public_inputs', 'owned_artifacts']:
    for record in frozen[category]:
        current = pin(Path(record['path']))
        assert current == record, (record['path'], current)
        checked_frozen.append(current)

source_files = sorted((ESTIMATOR / 'estimator').glob('*.py'))
source_files += [ESTIMATOR / name for name in ['README.rst', 'pyproject.toml']
                 if (ESTIMATOR / name).is_file()]
source_pins = [pin(path) for path in source_files]
run_manifests = sorted(HERE.glob('*.manifest.json'))
for path in run_manifests:
    record = json.loads(path.read_text())
    for name, expected in record['source_hashes'].items():
        assert pin(ESTIMATOR / 'estimator' / name)['sha256'] == expected

excluded = {'MANIFEST.json', 'pin_hardness.stdout.json'}
owned = [pin(path) for path in sorted(HERE.iterdir())
         if path.is_file() and path.name not in excluded]
reused = [pin(HERE.parent / 'MANIFEST.json')]
reused += [pin(OLD / name) for name in ['AUDIT.md', 'run_estimates.py']
           if (OLD / name).is_file()]
out = {
    'scope': 'Public parameter arithmetic and bounded estimator records only; no cryptographic execution.',
    'estimator_commit': '53da5982597709ba0fdf94ea37a84d822310fd84',
    'source_files': source_pins,
    'checked_frozen_parent_artifacts': checked_frozen,
    'reused_provenance': reused,
    'owned_artifacts': owned,
    'search_accounting': {
        'web_search_queries': 0, 'scry_sql_attempts': 0,
        'primary_web_pages_opened': [
            'https://lattice-estimator.readthedocs.io/en/latest/',
            'https://doc.sagemath.org/html/en/reference/rings_standard/sage/rings/integer.html#sage.rings.integer.Integer.is_prime'
        ],
        'pdf_downloads': 0
    }
}
rendered = json.dumps(out, indent=2) + '\n'
(HERE / 'MANIFEST.json').write_text(rendered)
print(rendered, end='')
