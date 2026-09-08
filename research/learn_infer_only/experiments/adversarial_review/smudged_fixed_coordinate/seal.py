"""Hash only the named public artifacts; no imported author code or runtime."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/public_setup_pq/alternatives'


def record(path):
    path = Path(path).resolve()
    assert not {'.private', 'private', 'runtime', 'signer_route', 'verified_route'}.intersection(path.parts)
    assert path.is_relative_to(ROOT) or path.is_relative_to('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


results = json.loads((HERE/'results.json').read_text())
assert results['status'] == 'PASS'
assert (HERE/'stdout.txt').read_bytes() == (HERE/'results.json').read_bytes()
assert (HERE/'stderr.txt').read_bytes() == b''
for expected in results['subject_pins']:
    assert record(expected['path']) == expected
author_manifest = json.loads((AUTHOR/'MANIFEST.json').read_text())
all_author_pins = []
for section in ['source_pdfs', 'reused_frozen_public_inputs', 'owned_artifacts']:
    for expected in author_manifest[section]:
        actual = record(expected['path'])
        assert actual == expected
        all_author_pins.append(actual)
visual = {
    'scope': 'Local primary PDF text and rendered pages read by reviewer; previous MP/GPV page reads reused.',
    'HYL_PDF': record('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/1613.pdf'),
    'HYL_text': record(HERE/'extracts/2025-1613.txt'),
    'HYL_pages_visually_read': [
        {'printed_page': page, 'render': record(HERE/f'renders/hyl-{page}.png')}
        for page in [24, 27, 28, 29]
    ],
    'prior_MP_GPV_visual_record': record(HERE.parent/'pq_finite_costs/visual_access.json'),
    'prior_MP_GPV_review': record(HERE.parent/'pq_finite_costs/REPORT.md'),
    'reused_MP_GPV_extracts': [
        record(HERE.parent/'public_setup_pq/quantitative_regularity/extracts'/name)
        for name in ['2011-501.txt', '2007-432.txt']
    ],
}
(HERE/'visual_access.json').write_text(json.dumps(visual, indent=2)+'\n')
owned = ['.gitignore', 'REPORT.md', 'check.py', 'results.json', 'stdout.txt',
         'stderr.txt', 'seal.py', 'visual_access.json']
manifest = {
    'scope': 'Independent source/math review. Named public artifacts only; no crypto, estimator or private-data execution.',
    'frozen_subjects': results['subject_pins'],
    'all_author_manifest_links_rechecked': all_author_pins,
    'owned_artifacts': [record(HERE/name) for name in owned],
    'author_artifacts_unchanged': True,
    'command': 'python3 research/learn_infer_only/experiments/adversarial_review/smudged_fixed_coordinate/seal.py',
}
(HERE/'review_manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'report': record(HERE/'REPORT.md'),
                  'review_manifest': record(HERE/'review_manifest.json'),
                  'author_links_unchanged': len(all_author_pins)}, indent=2))
