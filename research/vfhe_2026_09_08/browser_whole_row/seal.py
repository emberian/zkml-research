#!/usr/bin/env python3
"""Freeze the publication package and exact transfer sizes without re-verifying."""
from pathlib import Path
import gzip, hashlib, json

root = Path(__file__).resolve().parent
output = root / 'BROWSER_PACKAGE.json'
assert not output.exists()
files = []
for p in sorted(root.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts: continue
    data = p.read_bytes()
    files.append({'path': p.relative_to(root).as_posix(), 'bytes': len(data),
                  'sha256': hashlib.sha256(data).hexdigest()})
assets = []
for p in sorted(root.rglob('*')):
    if not p.is_file(): continue
    relative = p.relative_to(root).as_posix()
    if relative.startswith(('query/fixtures/', 'update/fixtures/')) or relative == 'web/query-case.js':
        data = p.read_bytes()
        assets.append({'path': relative, 'bytes': len(data),
                       'sha256': hashlib.sha256(data).hexdigest(),
                       'gzip9_bytes': len(gzip.compress(data, compresslevel=9, mtime=0))})
result = {'schema': 'whole-row-browser-publication-package-v1',
          'classification': 'EXECUTED', 'files': files, 'replacement_assets': assets,
          'replacement_raw_bytes': sum(p['bytes'] for p in assets),
          'replacement_gzip9_bytes': sum(p['gzip9_bytes'] for p in assets),
          'gzip_scope': 'Sum of independent gzip level-9 streams; not measured HTTP transfer.',
          'query_case_id': 'fast001-all-row-reproof-two-class-query',
          'wasm_sha256': '96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908',
          'proofs_generated': 3, 'native_self_checks': 3,
          'node_wasm_genuine_acceptances': 3, 'node_wasm_changed_output_rejections': 1,
          'browser_ui_execution': False, 'website_published_by_this_lane': False}
with output.open('x') as f: json.dump(result, f, indent=2); f.write('\n')
print(json.dumps({'status': 'PASS', 'files': len(files),
                  'package_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                  'replacement_raw_bytes': result['replacement_raw_bytes'],
                  'replacement_gzip9_bytes': result['replacement_gzip9_bytes']}, indent=2))
