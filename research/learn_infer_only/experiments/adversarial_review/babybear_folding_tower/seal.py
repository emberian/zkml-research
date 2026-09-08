"""Seal the bounded public-source/math review; execute no Lean or protocol."""
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ALLOWED = [ROOT, Path('/Users/ember/dev/minidregg'),
           Path('/tmp/minidregg-babybear-folding-tower-20260908'),
           Path('/Users/ember/dev/breadstuffs'),
           Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7')]


def pin(path):
    path = Path(path).absolute()
    assert not {'.private', 'private', 'runtime', 'signer_route', 'verified_route'}.intersection(path.parts)
    assert any(path.is_relative_to(base) for base in ALLOWED)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}


inputs = json.loads((HERE / 'INPUTS.json').read_text())
results = json.loads((HERE / 'results.json').read_text())
assert results['status'] == 'PASS'
assert (HERE / 'stdout.txt').read_bytes() == (HERE / 'results.json').read_bytes()
assert (HERE / 'stderr.txt').read_bytes() == b''
for expected in inputs['frozen_public_files']:
    assert pin(expected['path']) == expected
owned = ['.gitignore', 'REPORT.md', 'INPUTS.json', 'check.py', 'results.json',
         'stdout.txt', 'stderr.txt', 'seal.py']
manifest = {
    'scope': 'Independent source/axiom/patch census, saved isolated Lean evidence, and pure modular/rational arithmetic. No new Lean or protocol execution.',
    'frozen_public_files': inputs['frozen_public_files'],
    'owned_artifacts': [pin(HERE / name) for name in owned],
    'author_artifacts_unchanged': True,
    'new_lean_builds': 0,
    'new_crypto_executions': 0,
    'combined_closure_build': 'Separate root-owned integration result; not repeated by this reviewer.',
    'command': 'python3 research/learn_infer_only/experiments/adversarial_review/babybear_folding_tower/seal.py',
}
(HERE / 'review_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'report': pin(HERE / 'REPORT.md'),
                  'review_manifest': pin(HERE / 'review_manifest.json'),
                  'frozen_public_files_unchanged': len(inputs['frozen_public_files'])}, indent=2))
