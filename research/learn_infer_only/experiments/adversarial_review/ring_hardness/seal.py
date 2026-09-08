"""Seal only named public review sources and outputs; no estimator invocation."""
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
EST = ROOT / 'research/learn_infer_only/experiments/he_closure_costs/estimator'
SNAP = EST / 'runtime/pinned-estimator'


def pin(path):
    path = Path(path).resolve()
    assert path.is_relative_to(ROOT)
    assert not {'.private', 'private', 'signer_route', 'verified_route'}.intersection(path.parts)
    if 'runtime' in path.parts:
        assert path.is_relative_to(SNAP) or path == EST / 'runtime/estimator-src.tar'
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}


inputs = json.loads((HERE / 'INPUTS.json').read_text())
results = json.loads((HERE / 'results.json').read_text())
assert results['status'] == 'PASS'
assert (HERE / 'stdout.txt').read_bytes() == (HERE / 'results.json').read_bytes()
assert (HERE / 'stderr.txt').read_bytes() == b''
for entry in inputs['frozen_public_files']:
    assert pin(entry['path']) == entry
owned = ['.gitignore', 'REPORT.md', 'check.py', 'INPUTS.json', 'results.json',
         'stdout.txt', 'stderr.txt', 'seal.py']
manifest = {
    'scope': 'Independent exact ring normal-form and Gaussian map, saved 24-call generic cost model records, and coupled finite arithmetic. No computational security certification.',
    'frozen_public_files': inputs['frozen_public_files'],
    'owned_artifacts': [pin(HERE / f) for f in owned],
    'author_artifacts_unchanged': True,
    'new_estimator_calls': 0, 'new_sage_calls': 0, 'new_crypto_calls': 0,
    'sampler_QPT_obligations': 'Separate lane; not closed by this ideal-model/cost audit.',
    'command': 'python3 research/learn_infer_only/experiments/adversarial_review/ring_hardness/seal.py',
}
(HERE / 'review_manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'report': pin(HERE / 'REPORT.md'),
                  'review_manifest': pin(HERE / 'review_manifest.json'),
                  'frozen_public_files_unchanged': len(inputs['frozen_public_files'])}, indent=2))
