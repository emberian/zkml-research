#!/usr/bin/env python3
"""Seal the fast001 public dataset and the already-executed unchanged consumer."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
case = json.loads((ROOT / 'query-case.json').read_text())
result = json.loads((ROOT / 'results/verify-node.json').read_text())
assert result['status'] == 'PASS' and result['genuine']['verified']
assert result['actualProofVerifications'] == 2
assert result['genuine']['caseId'] == 'fast001-new-two-class-query'
pins = json.loads((ROOT / 'SOURCE_PINS.json').read_text())
assert all(sha((ROOT / name).read_bytes()) == info['sha256'] for name, info in pins.items())
assert sha((ROOT.parent / 'BROWSER_PACKAGE.json').read_bytes()) == 'c766e339ce5a35629eab6bc4b298c9aa27ad1c62f6c364b6769e55d99236b0ff'

fixtures = [case['templatePath'], case['requestPath']]
fixtures += [item[key] for item in case['cases'] for key in ['publicRowsPath', 'proofPath']]
replacement = ['web/query-case.js'] + fixtures
changed = [path for path in replacement if path != case['templatePath']]
standalone = ['web/query-consumer.js', 'web/query-case.js', 'web/query-worker.js',
              'web/verifier.js', 'web/pkg/vfhe_browser_verifier.js', case['wasmPath']] + fixtures
def info(path):
    data = (ROOT / path).read_bytes()
    return {'path': path, 'bytes': len(data), 'sha256': sha(data),
            'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0))}
def total(paths):
    files = [info(path) for path in paths]
    return {'files': files, 'uncompressed_bytes': sum(item['bytes'] for item in files),
            'estimated_gzip9_bytes': sum(item['gzip9_bytes'] for item in files)}
downloads = {'method': 'Exact raw bytes; gzip estimates are sums of independent gzip level-9 streams with mtime=0, not observed network traffic.',
    'replacement_dataset': total(replacement), 'changed_files_template_cached': total(changed),
    'standalone_first_load': total(standalone)}
(ROOT / 'DOWNLOADS.json').write_text(json.dumps(downloads, indent=2) + '\n')
paths = sorted(str(path.relative_to(ROOT)) for path in ROOT.rglob('*') if path.is_file() and path.name != 'BROWSER_PACKAGE.json')
manifest = {'schema': 'fast001-two-class-query-browser-package-v1', 'case_id': case['id'],
    'backend': case['expectedBackend'], 'template_sha256': case['expectedTemplateSha256'],
    'wasm_sha256': case['files'][case['wasmPath']]['sha256'],
    'execution_result_sha256': sha((ROOT / 'results/verify-node.json').read_bytes()),
    'execution_scope': 'Exactly two saved proofs verified in Node WebAssembly through unchanged existing consumer.',
    'browser_execution_performed': False, 'wasm_rebuilt': False, 'new_proof_generated': False,
    'files': [info(path) for path in paths]}
(ROOT / 'BROWSER_PACKAGE.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(paths),
    'manifest_sha256': sha((ROOT / 'BROWSER_PACKAGE.json').read_bytes()),
    'query_case_script_sha256': sha((ROOT / 'web/query-case.js').read_bytes()),
    'execution_result_sha256': manifest['execution_result_sha256'],
    'replacement_raw_bytes': downloads['replacement_dataset']['uncompressed_bytes'],
    'replacement_estimated_gzip_bytes': downloads['replacement_dataset']['estimated_gzip9_bytes']}, indent=2))
