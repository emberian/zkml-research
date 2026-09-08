#!/usr/bin/env python3
"""Pin only named public review artifacts and their source bytes."""

import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path(__file__).resolve().parents[1]
    repo = root.parents[4]
    source = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf')
    candidate = repo / 'research/learn_infer_only/experiments/private_construction/public_setup_pq/notes/AUDIT.md'
    expected = {
        source: 'a7d5c231b70961ea59ca544c91b2392fb35c166c88e42b898640cfdc7dbb94d0',
        candidate: '2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007',
        root / 'extracts/2015-608.txt': 'a1170661edc061a9b011367d43b9b75ed6dfc073cfd0aa477459c20f14d1ecdd',
    }
    pins = []
    for path, expected_hash in expected.items():
        actual = digest(path)
        assert actual == expected_hash, f'Changed frozen input: {path}'
        pins.append({'path': str(path), 'sha256': actual, 'matched': True})

    result = json.loads((root / 'checks/public_algebra_output.json').read_text())
    assert result['result'] == 'PASS'
    assert result['script_sha256'] == digest(root / 'checks/public_algebra.py')
    named = [
        'REVIEW.md',
        'FIXED_COORDINATE_QPT.md',
        'checks/public_algebra.py',
        'checks/public_algebra_output.json',
        'checks/seal_review.py',
        'extracts/page18.png',
        'extracts/page21.png',
    ]
    artifacts = []
    for name in named:
        path = root / name
        artifacts.append({'path': name, 'bytes': path.stat().st_size, 'sha256': digest(path)})
        if path.suffix in {'.md', '.py'}:
            for number, line in enumerate(path.read_text().splitlines(), 1):
                assert line == line.rstrip(), f'Trailing whitespace: {path}:{number}'
    manifest = {
        'scope': 'Independent public-source and mathematical review; no crypto or private-state execution',
        'frozen_inputs': pins,
        'artifacts': artifacts,
        'source_queries': {'web_open': 1, 'web_search': 0, 'scry_sql': 0, 'scry_schema': 0, 'kagi': 0, 'pdf_download': 0},
        'public_algebra_result': result['result'],
    }
    (root / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'result': 'PASS', 'frozen_input_pins': len(pins), 'review_artifacts': len(artifacts), 'manifest_sha256': digest(root / 'MANIFEST.json')}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
