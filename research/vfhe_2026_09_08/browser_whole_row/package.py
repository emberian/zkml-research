#!/usr/bin/env python3
"""Package all-row replacement public assets, preserving every predecessor."""
from pathlib import Path
import gzip, hashlib, json, shutil

ROOT = Path(__file__).resolve().parent
LANES = ROOT.parent
PRIOR = LANES / 'query_browser_verifier/fast_successor'
BASE = LANES / 'browser_verifier'

def digest(data): return hashlib.sha256(data).hexdigest()
def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')

copied = {}
def copy(source, relative, expected=None):
    data = source.read_bytes()
    if expected is not None:
        assert digest(data) == expected, str(source)
    target = ROOT / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as f: f.write(data)
    copied[relative] = {'source': str(source.resolve()), 'sha256': digest(data),
                       'bytes': len(data), 'gzip9_bytes': len(gzip.compress(data, mtime=0))}
    return copied[relative]

def main():
    prior = json.loads((PRIOR / 'query-case.json').read_text())
    for name in ['package.json', 'verifier.js', 'query-consumer.js', 'shared-query-worker.js']:
        copy(PRIOR / 'web' / name, 'web/' + name)
    for source in sorted((PRIOR / 'web/pkg').iterdir()):
        if source.is_file(): copy(source, 'web/pkg/' + source.name)
    assert copied['web/pkg/vfhe_browser_verifier_bg.wasm']['sha256'] == '96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908'
    # Update fixture retains its actual public tuple file byte for byte.
    update = 'update/fixtures/learner-expiry/'
    copy(ROOT / 'templates/expiry/template_ir2.json', update + 'template.json')
    copy(BASE / 'fixtures/learner-expiry/public_rows.json', update + 'public_rows.json',
         '125fdd7d2bc8739898559c3275a8d572cbb0ea693e2d8b9cbb1b8d2cc944c8b1')
    copy(ROOT / 'proofs/learner-expiry/proof.bin', update + 'proof.bin')
    save(ROOT / (update + 'fixture.json'), {
        'schema': 'whole-row-public-update-fixture-v1',
        'claim': '[SOURCE] Re-proved event 65 public acc+fresh-old coefficient rows with all-row arithmetic gates.',
        'backend': prior['expectedBackend'], 'public_table_id': 11,
        'files': {name: copied[update+name] for name in ['template.json', 'public_rows.json', 'proof.bin']},
        'scope': 'All physical rows under the application-selected coefficient relation. No proof of FIFO authorization, encoder, ciphertext-key membership, decryption, or universal native verifier soundness.',
        'original_fixture_preserved': str(BASE / 'fixtures/learner-expiry')})
    copy(ROOT / 'templates/query/template_ir2.json', 'query/fixtures/template.json')
    copy(PRIOR / 'fixtures/request.json', 'query/original_request.json')
    case = dict(prior)
    case['id'] = 'fast001-all-row-reproof-two-class-query'
    case['expectedTemplateSha256'] = copied['query/fixtures/template.json']['sha256']
    case['scope'] = 'Both recorded fast001 class ciphertext query computations, newly proved with arithmetic gates on all 8192 physical rows. No encoder, decryption, authorization, or universal native verifier soundness proof.'
    case['files'] = {}
    for path, info in copied.items():
        if path.startswith('web/pkg/') or path in ['web/package.json', 'web/verifier.js']:
            case['files'][path] = {key: info[key] for key in ['bytes', 'sha256']}
    for i, item in enumerate(case['cases']):
        relative = f'query/fixtures/class{i}/'
        copy(PRIOR / f'fixtures/class{i}/public_rows.json', relative + 'public_rows.json',
             prior['files'][item['publicRowsPath']]['sha256'])
        metadata = json.loads((ROOT / f'proofs/class{i}/proof.json').read_text())
        assert metadata['backend'] == case['expectedBackend'] and metadata['verified'] is True
        assert metadata['template_sha256'] == case['expectedTemplateSha256']
        copy(ROOT / f'proofs/class{i}/proof.bin', relative + 'proof.bin', metadata['proof_sha256'])
    # The source journal's historical request is preserved separately. This
    # replacement envelope identifies this public reproof and is not a newly
    # authorized request or a claim that the historical receipt changed.
    original = json.loads((PRIOR / 'fixtures/request.json').read_text())
    request = {
        'schema': 'public-whole-row-reproof-context-v1', 'case_id': case['id'],
        'original_request_sha256': copied['query/original_request.json']['sha256'],
        'original_request': original,
        'replacement_template_sha256': case['expectedTemplateSha256'],
        'replacement_proofs': {item['label']: copied[f'query/fixtures/class{i}/proof.bin']['sha256']
                               for i, item in enumerate(case['cases'])},
        'scope': 'Historical context plus replacement arithmetic proof identities; not an authorization or live model-head attestation.'}
    save(ROOT / 'query/fixtures/request.json', request)
    request_bytes = (ROOT / 'query/fixtures/request.json').read_bytes()
    copied['query/fixtures/request.json'] = {
        'source': 'generated from preserved public request and new proof identities',
        'bytes': len(request_bytes), 'sha256': digest(request_bytes),
        'gzip9_bytes': len(gzip.compress(request_bytes, mtime=0))}
    for path, info in copied.items():
        if path.startswith('query/fixtures/'):
            case['files'][path.removeprefix('query/')] = {key: info[key] for key in ['bytes', 'sha256']}
    save(ROOT / 'query-case.json', case)
    script = '// Application-selected pins for the all-row reproof of the saved fast001 public cases.\n' + \
        'const freeze = value => { if (value && typeof value === "object") { for (const item of Object.values(value)) freeze(item); Object.freeze(value); } return value; };\n' + \
        'export const QUERY_CASE = freeze(' + json.dumps(case, indent=2) + ');\n'
    with (ROOT / 'web/query-case.js').open('x') as f: f.write(script)
    save(ROOT / 'ASSET_MAP.json', {
        'schema': 'whole-row-microsite-asset-replacements-v1',
        'owner': 'root; this package does not modify or publish a website',
        'replace': [
            {'source': 'web/query-case.js', 'site_destination': 'proof/query-case.js'},
            {'source': 'query/fixtures/', 'site_destination': 'query-bundle/fixtures/', 'recursive': True},
            {'source': update, 'site_destination': 'learner-bundle/fixtures/learner-expiry/',
             'recursive': True, 'destination_note': 'Use the existing site update-fixture directory; this is a suggested bundle name.'}],
        'reuse_unchanged': [path for path in copied if path.startswith('web/')],
        'required_case_id': case['id'],
        'update_template_sha256': copied[update+'template.json']['sha256'],
        'query_template_sha256': case['expectedTemplateSha256'],
        'integration_note': 'Update every application-selected update fixture pin and require the new query case ID. Preserve archived old fixtures but remove their status as corrected current examples. The unchanged shared worker accepts the existing bundleBaseUrl ending in a slash.'})
    save(ROOT / 'source_provenance.json', {
        'classification': 'EXECUTED', 'copied_files': copied,
        'wasm_rebuilt': False, 'new_proofs_generated': 3, 'private_files_read': 0,
        'old_fixtures_changed': False, 'old_request_preserved': True,
        'search_queries': {'web': 0, 'scry': 0}})
    print(json.dumps({'status': 'PASS', 'new_case_id': case['id'],
                      'update_template_sha256': copied[update+'template.json']['sha256'],
                      'query_template_sha256': case['expectedTemplateSha256']}, indent=2))

if __name__ == '__main__': main()
