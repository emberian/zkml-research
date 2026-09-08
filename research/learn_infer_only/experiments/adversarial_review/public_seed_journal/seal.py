"""Seal the bounded unexecuted source snapshot, not a launch authorization."""
from hashlib import sha256
import json
from pathlib import Path
import stat

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def pin(path):
    path = Path(path).resolve()
    assert path.is_relative_to(ROOT)
    assert not {'runtime', '.private', 'private', 'signer_route', 'verified_route'}.intersection(path.parts)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest(),
            'mode': oct(stat.S_IMODE(path.stat().st_mode))}


result = json.loads((HERE/'source_results.json').read_text())
assert result['status'] == 'PASS_SOURCE_SNAPSHOT_ONLY'
assert result['launch_authorized'] is False and result['prelaunch_acceptance_issued'] is False
assert (HERE/'source_check.log').read_bytes() == (HERE/'source_results.json').read_bytes()
assert (HERE/'source_check.stderr').read_bytes() == b''
for entry in result['frozen_predecessor_records']:
    assert pin(entry['path']) == entry
for entry in result['author_source_snapshot']:
    captured = pin(HERE/'source_snapshot'/Path(entry['path']).name)
    assert captured['sha256'] == entry['sha256'] and captured['bytes'] == entry['bytes']
owned = ['REPORT.md','STATUS.md','NEXT.md','check_source.py','source_results.json',
         'source_check.log','source_check.stderr','seal.py']
manifest = {'status': 'UNEXECUTED_SOURCE_HANDOFF', 'launch_authorized': False,
            'prelaunch_acceptance_issued': False,
            'scope': 'Captured preparation source and unchanged predecessor identities; final launcher/public closure/preparation gate remain unreviewed.',
            'owned_files': [pin(HERE/name) for name in owned] + [pin(p) for p in sorted((HERE/'source_snapshot').iterdir())],
            'author_preparation_may_continue': True,
            'frozen_predecessor_records': result['frozen_predecessor_records'],
            'new_crypto_calls': 0, 'new_private_reads': 0}
(HERE/'review_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status': 'UNEXECUTED_SOURCE_HANDOFF', 'launch_authorized': False,
                  'report_sha256': pin(HERE/'REPORT.md')['sha256'],
                  'manifest_sha256': pin(HERE/'review_manifest.json')['sha256']},indent=2))
