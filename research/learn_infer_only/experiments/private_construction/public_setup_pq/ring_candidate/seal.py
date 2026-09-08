#!/usr/bin/env python3
"""Verify local source/proposal provenance; no cryptographic runtime."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


sources = json.loads((HERE / 'SOURCES.json').read_text())
checked = []
for source in sources['sources']:
    pdf, extract = Path(source['pdf_path']), Path(source['extract_path'])
    assert digest(pdf) == source['pdf_sha256'], pdf
    assert digest(extract) == source['extract_sha256'], extract
    with tempfile.TemporaryDirectory(prefix='source-recheck-', dir=HERE) as temp:
        generated = Path(temp) / 'paper.txt'
        extraction = subprocess.run(
            ['pdftotext', '-layout', str(pdf), str(generated)],
            check=True, capture_output=True, text=True)
        assert digest(generated) == digest(extract), source['name']
        warning_count = len(extraction.stderr.splitlines())
    checked.append({
        'name': source['name'],
        'pdf_sha256': digest(pdf),
        'extract_sha256': digest(extract),
        'fresh_layout_extraction_matches': True,
        'fresh_extraction_stderr_line_count': warning_count,
    })

frozen = {
    'CANDIDATE.md': '5010b72b024aa7154504a7c0dd0de306fe0068b3af3b33b5026b444c510a0dc2',
    'RING_REGULARITY.md': '2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85',
    'PARAMETERS.md': 'c23732e366fe5966ddf971c0f69fdf51cec41bee134d0bf3e4da19367631b78d',
    'RESULTS.json': 'e034b208095cbb82cf852abe0137aac7c1be1dd03f8df16844edc8bdb299b693',
}
for name, expected in frozen.items():
    assert digest(HERE / name) == expected, name
scalar = sources['frozen_scalar_math_reference']
assert digest(Path(scalar['path'])) == scalar['sha256']
results = json.loads((HERE / 'RESULTS.json').read_text())
assert results['status'] == 'PASS'
assert digest(HERE / 'searches/prime_certificate.json') == results['prime_certificate_sha256']

artifacts = [
    'CANDIDATE.md', 'RING_REGULARITY.md', 'PARAMETERS.md',
    'STATUS.md', 'NEXT.md', 'RESULTS.json', 'SOURCES.json',
    'check_public_math.py', 'seal.py',
    'searches/prime_certificate.json', 'searches/scry_1.json',
    'searches/scry_1_retry.json',
]
renders = sorted(path for path in HERE.rglob('*.png') if path.is_file())
manifest = {
    'scope': '[EXECUTED] Local-source and artifact provenance only; no crypto, estimator, Gaussian or attack execution',
    'status': 'PASS',
    'fresh_source_extractions': checked,
    'frozen_notes_and_math_results': frozen,
    'frozen_scalar_math_reference': scalar,
    'artifacts': {name: digest(HERE / name) for name in artifacts},
    'visual_source_renders': {str(path.relative_to(HERE)): digest(path) for path in renders},
    'query_meter': sources['query_meter'],
    'review_status_at_seal': 'Independent source/math review assigned; proposal hashes frozen pending review',
}
(HERE / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
seal_result = {
    'status': 'PASS', 'source_extractions': len(checked),
    'frozen_notes_and_math_results': len(frozen),
    'artifacts': len(artifacts), 'visual_source_renders': len(renders),
    'manifest_sha256': digest(HERE / 'MANIFEST.json'),
}
(HERE / 'SEAL.json').write_text(json.dumps(seal_result, indent=2) + '\n')
print(json.dumps(seal_result, indent=2))
