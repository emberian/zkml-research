#!/usr/bin/env python3
"""Verify frozen spec/source/results provenance only; no sampler execution."""
from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


results = json.loads((HERE / 'RESULTS.json').read_text())
sources = json.loads((HERE / 'SOURCES.json').read_text())
assert results['status'] == 'PASS'
assert digest(HERE / 'SPEC.md') == results['frozen_spec_sha256']
for item in sources['public_input_files']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
assert results['combined_Gaussian_loss_coefficient'] < 2**41
assert results['combined_uniform_loss_coefficient'] < 2**45
artifacts = ['SPEC.md', 'AUDIT.md', 'STATUS.md', 'NEXT.md',
             'check_bounds.py', 'RESULTS.json', 'SOURCES.json', 'seal.py']
manifest = {
    'scope': 'Frozen bounded sampler specification and deterministic probability/resource certificate; no sampler implementation or random outputs',
    'status': 'PASS',
    'frozen_spec_before_implementation_sha256': results['frozen_spec_sha256'],
    'public_input_files': sources['public_input_files'],
    'primary_web_sources': sources['web_sources'],
    'artifacts': {name: digest(HERE / name) for name in artifacts},
    'meter': sources['meter'],
    'execution': {'deterministic_probability_arithmetic_helper': 'PASS',
                  'sampler_implementation': False, 'random_outputs': 0,
                  'keygen': 0, 'encryption': 0, 'estimator': 0, 'lattice_attack': 0},
    'review_status': 'Assigned independent reviewer reports no correction needed; awaiting sealed final report',
}
(HERE / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
seal_result = {'status': 'PASS', 'spec_sha256': digest(HERE / 'SPEC.md'),
               'audit_sha256': digest(HERE / 'AUDIT.md'),
               'results_sha256': digest(HERE / 'RESULTS.json'),
               'manifest_sha256': digest(HERE / 'MANIFEST.json'),
               'public_input_hashes': len(sources['public_input_files']),
               'artifact_hashes': len(artifacts)}
(HERE / 'SEAL.json').write_text(json.dumps(seal_result, indent=2)+'\n')
print(json.dumps(seal_result, indent=2))
