"""Seal owned artifacts; no compiler, companion write, or cryptographic call."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
verification = json.loads((root / 'results/verification.json').read_text())
assert verification['all_passed']
assert verification['source_sha256'] == sha(root / 'Theory/PrivateEmaDynamics.lean')
assert verification['patch_sha256'] == sha(root / 'minidregg-private-ema-dynamics.patch')
entries = []
for path in sorted(root.rglob('*')):
    if not path.is_file():
        continue
    relative = path.relative_to(root)
    if '.build' in relative.parts or '__pycache__' in relative.parts or relative.as_posix() == 'manifest.json':
        continue
    entries.append({'path': relative.as_posix(), 'bytes': path.stat().st_size, 'sha256': sha(path)})
manifest = {'scope': 'isolated checked dynamics extension; no whole-tree integration', 'entries': entries}
target = root / 'manifest.json'
target.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
for entry in entries:
    assert sha(root / entry['path']) == entry['sha256']
print(json.dumps({'entries': len(entries), 'manifest_sha256': sha(target),
                  'source_sha256': verification['source_sha256'],
                  'patch_sha256': verification['patch_sha256']}, indent=2))
