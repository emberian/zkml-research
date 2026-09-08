#!/usr/bin/env python3
"""Source/extraction/hash verification only. No cryptographic runtime."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = Path('/Users/ember/dev/zkml-research')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


sources = json.loads((HERE/'SOURCES.json').read_text())
checked = []
for source in sources['sources']:
    pdf, extract = Path(source['pdf_path']), Path(source['extract_path'])
    assert digest(pdf) == source['pdf_sha256'], pdf
    assert digest(extract) == source['extract_sha256'], extract
    with tempfile.TemporaryDirectory(prefix='source-recheck-', dir=HERE) as temp:
        generated = Path(temp)/'paper.txt'
        subprocess.run(['pdftotext', '-layout', str(pdf), str(generated)], check=True)
        assert digest(generated) == digest(extract), source['name']
    checked.append({'name': source['name'], 'pdf_sha256': digest(pdf), 'extract_sha256': digest(extract), 'fresh_layout_extraction_matches': True})

frozen = {
    ROOT/'research/learn_infer_only/experiments/private_construction/public_setup_pq/notes/AUDIT.md': '2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007',
    HERE.parent/'FIXED_COORDINATE_QPT.md': '4c43bce409495edf9c9d5b8e4ada0581af5be0ecf6ff949fbd99fdbfd3da62fe',
    HERE.parent/'quantitative_regularity/BOUND.md': 'b07d7714ca6078a63bf1281ad8edbd07dc39094d91f6808e1c3868a3503dc2e5',
    HERE/'FINITE_THEOREM.md': '7ae20bc50552283e4688466b966c7e2d1265613f4fb8a49c2909aaeb77bd7bd4',
}
for path, expected in frozen.items():
    assert digest(path) == expected, path
inputs = json.loads((HERE/'INPUTS.json').read_text())
assert digest(Path(inputs['source_path'])) == inputs['source_sha256']
results = json.loads((HERE/'RESULTS.json').read_text())
assert results['inputs_sha256'] == digest(HERE/'INPUTS.json')

artifacts = ['FINITE_THEOREM.md', 'PARAMETERS.md', 'STATUS.md', 'NEXT.md', 'INPUTS.json', 'RESULTS.json', 'SOURCES.json', 'check_parameters.py', 'seal.py']
manifest = {
    'scope': '[EXECUTED] Provenance only; no crypto, estimator, Gaussian or attack execution',
    'status': 'PASS',
    'four_fresh_source_extractions_match': checked,
    'frozen_note_inputs': {str(path): expected for path, expected in frozen.items()},
    'parameter_source': {'path': inputs['source_path'], 'sha256': inputs['source_sha256']},
    'artifacts': {name: digest(HERE/name) for name in artifacts},
    'network_meter': sources['network_counts_this_finite_task'],
}
(HERE/'MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
result = {'status': 'PASS', 'source_extractions': len(checked), 'frozen_notes': len(frozen), 'artifacts': len(artifacts), 'manifest_sha256': digest(HERE/'MANIFEST.json')}
(HERE/'SEAL.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
