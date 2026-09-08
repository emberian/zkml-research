#!/usr/bin/env python3
"""Record the public runtime assets, download estimates and additive handoff files."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
case = json.loads((ROOT / 'query-case.json').read_text())
result = json.loads((ROOT / 'results/verify-node.json').read_text())
assert result['status'] == 'PASS' and result['genuine']['verified']
assert result['changedPublicOutput']['actualProofBackendRefused']
pins = json.loads((ROOT / 'SOURCE_PINS.json').read_text())
assert all(sha((ROOT / rel).read_bytes()) == pin['sha256'] for rel, pin in pins.items())

fixtures = [case['templatePath'], case['requestPath']]
for entry in case['cases']:
    fixtures += [entry['publicRowsPath'], entry['proofPath']]
shared_existing = ['web/verifier.js', 'web/pkg/vfhe_browser_verifier.js', case['wasmPath']]
shared_new = ['web/query-consumer.js', 'web/query-case.js', 'web/shared-query-worker.js'] + fixtures
standalone = ['web/query-consumer.js', 'web/query-case.js', 'web/query-worker.js'] + shared_existing + fixtures
def fileinfo(rel):
    data = (ROOT / rel).read_bytes()
    return {'path': rel, 'bytes': len(data), 'sha256': sha(data),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0))}
def total(paths):
    files = [fileinfo(path) for path in paths]
    return {'files': files, 'uncompressed_bytes': sum(v['bytes'] for v in files),
            'estimated_gzip9_bytes': sum(v['gzip9_bytes'] for v in files)}
downloads = {
    'method': 'Exact raw byte counts; sum of independent gzip level-9 streams with mtime=0. This is an estimate of HTTP transfer, not observed browser/network traffic.',
    'standalone_first_load': total(standalone),
    'shared_existing_assets': total(shared_existing),
    'shared_incremental_assets': total(shared_new),
    'shared_first_load_without_cache': total(shared_existing + shared_new),
    'public_fixture_data': total(fixtures),
    'excluded_from_runtime_transfer': ['Node runner', 'package.json', 'TypeScript declarations', 'reports and evidence files'],
}
(ROOT / 'DOWNLOADS.json').write_text(json.dumps(downloads, indent=2) + '\n')
files = sorted(path for path in ROOT.rglob('*') if path.is_file() and path.name != 'BROWSER_PACKAGE.json')
manifest = {
    'schema': 'recorded-two-class-query-browser-package-v1',
    'backend': case['expectedBackend'],
    'case_id': case['id'],
    'template_sha256': case['expectedTemplateSha256'],
    'wasm_sha256': case['files'][case['wasmPath']]['sha256'],
    'execution_result_sha256': sha((ROOT / 'results/verify-node.json').read_bytes()),
    'execution_scope': 'Node WebAssembly, two genuine proofs and one changed-output backend refusal; shared worker source syntax checked only.',
    'browser_execution_performed': False,
    'wasm_rebuilt': False,
    'new_proof_generated': False,
    'files': [fileinfo(str(path.relative_to(ROOT))) for path in files],
}
(ROOT / 'BROWSER_PACKAGE.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({
    'status': 'PASS', 'files': len(files),
    'manifest_sha256': sha((ROOT / 'BROWSER_PACKAGE.json').read_bytes()),
    'execution_result_sha256': manifest['execution_result_sha256'],
    'standalone_first_load_bytes': downloads['standalone_first_load']['uncompressed_bytes'],
    'standalone_estimated_gzip9_bytes': downloads['standalone_first_load']['estimated_gzip9_bytes'],
    'shared_incremental_bytes': downloads['shared_incremental_assets']['uncompressed_bytes'],
    'shared_incremental_estimated_gzip9_bytes': downloads['shared_incremental_assets']['estimated_gzip9_bytes'],
}, indent=2))
