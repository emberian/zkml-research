#!/usr/bin/env python3
"""Copy only the saved fast001 public query proofs into the frozen consumer."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent
LANES = PRIOR.parent
SOURCE = LANES / 'proved_journal/fast_live_successor/results/fast001'
sha = lambda data: hashlib.sha256(data).hexdigest()
prior = json.loads((PRIOR / 'BROWSER_PACKAGE.json').read_text())
assert sha((PRIOR / 'BROWSER_PACKAGE.json').read_bytes()) == 'c766e339ce5a35629eab6bc4b298c9aa27ad1c62f6c364b6769e55d99236b0ff'
pins = {entry['path']: entry for entry in prior['files']}
copied = {}

def copy(source, relative, expected=None):
    data = source.read_bytes()
    digest = sha(data)
    if expected is not None:
        assert digest == expected, (str(source), 'pin mismatch')
    target = ROOT / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    copied[relative] = {'bytes': len(data), 'sha256': digest,
        'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'source': str(source.resolve())}

reused = ['web/package.json', 'web/verifier.js', 'web/query-consumer.js',
          'web/query-worker.js', 'web/shared-query-worker.js', 'run_node.py']
reused += sorted(path for path in pins if path.startswith('web/pkg/'))
for path in reused:
    copy(PRIOR / path, path, pins[path]['sha256'])

accepted = json.loads((SOURCE / 'public_acceptance.json').read_text())
envelope = json.loads((SOURCE / 'request.json').read_text())
request = envelope['request']
assert request == accepted['request']
assert accepted['all_active_classes_verified'] is True
assert request['active_classes'] == ['card_arrival', 'cash_withdrawal_charge']
assert request['template_sha256'] == prior['template_sha256']
copy(LANES / 'query_arithmetic/artifacts/template_ir2.json', 'fixtures/template.json', request['template_sha256'])
copy(SOURCE / 'request.json', 'fixtures/request.json')
cases = []
for index, label in enumerate(request['active_classes']):
    folder = SOURCE / f'class{index}'
    metadata = json.loads((folder / 'proof/proof.json').read_text())
    selected = request['classes'][label]
    assert metadata['backend'] == prior['backend']
    assert metadata['template_sha256'] == request['template_sha256']
    assert metadata['public_rows_sha256'] == selected['rows_sha256']
    assert metadata['proof_sha256'] == selected['proof_sha256']
    assert accepted['native_acceptances'][label]['proof_sha256'] == selected['proof_sha256']
    rows_path = f'fixtures/class{index}/public_rows.json'
    proof_path = f'fixtures/class{index}/proof.bin'
    copy(folder / 'case/public_rows.json', rows_path, metadata['public_rows_sha256'])
    copy(folder / 'proof/proof.bin', proof_path, metadata['proof_sha256'])
    rows = json.loads((ROOT / rows_path).read_text())
    assert len(rows) == 8192 and all(len(row) == 57 and row[0] == i for i, row in enumerate(rows))
    assert copied[proof_path]['bytes'] == metadata['proof_bytes']
    cases.append({'label': label, 'publicRowsPath': rows_path, 'proofPath': proof_path,
        'rows': 8192, 'publicWidth': 57, 'accumulatorSha256': selected['acc_sha256'],
        'outputCiphertextSha256': selected['out_sha256']})

case = {'schema': 'recorded-two-class-query-wasm-v1', 'id': 'fast001-new-two-class-query',
    'requestId': request['request_id'], 'expectedBackend': prior['backend'],
    'expectedTemplateSha256': request['template_sha256'],
    'templatePath': 'fixtures/template.json', 'requestPath': 'fixtures/request.json',
    'wasmPath': 'web/pkg/vfhe_browser_verifier_bg.wasm',
    'publicQuerySha256': request['query_sha256'], 'recordedModelRoot': request['model_root'],
    'recordedRevision': request['revision'],
    'scope': 'Both recorded class ciphertext query computations: two signed products and subtraction. No encoder, decryption or authorization proof.',
    'cases': cases,
    'files': {path: {key: value for key, value in info.items() if key in ['bytes', 'sha256']}
        for path, info in copied.items() if path.startswith('fixtures/') or path in pins and
        (path in ['web/package.json', 'web/verifier.js'] or path.startswith('web/pkg/'))}}
(ROOT / 'query-case.json').write_text(json.dumps(case, indent=2) + '\n')
(ROOT / 'web/query-case.js').write_text('// Application-selected transport pins for this exact retained public case.\n'
    'const freeze = value => { if (value && typeof value === "object") { for (const item of Object.values(value)) freeze(item); Object.freeze(value); } return value; };\n'
    'export const QUERY_CASE = freeze(' + json.dumps(case, indent=2) + ');\n')
provenance = {'source_run': str(SOURCE.resolve()), 'source_run_id': 'fast001',
    'predecessor_package_sha256': sha((PRIOR / 'BROWSER_PACKAGE.json').read_bytes()),
    'source_public_request_sha256': sha((SOURCE / 'request.json').read_bytes()),
    'source_public_acceptance_sha256': sha((SOURCE / 'public_acceptance.json').read_bytes()),
    'source_command_sha256': sha((SOURCE / 'command.json').read_bytes()),
    'copied_files': copied, 'wasm_rebuilt': False, 'new_proof_generated': False,
    'private_files_read': 0, 'original_gated001_preserved': True}
(ROOT / 'source_provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'case_id': case['id'], 'copied_files': len(copied),
    'query_case_script_sha256': sha((ROOT / 'web/query-case.js').read_bytes()),
    'proof_bytes': [copied[item['proofPath']]['bytes'] for item in cases]}, indent=2))
