#!/usr/bin/env python3
"""Read-only companion dependencies; isolated output; keep each compiler result."""
from pathlib import Path
import hashlib
import difflib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / 'formal/recovery_policy'
RESULTS = Path(__file__).resolve().parent
COMPANION = Path('/Users/ember/dev/minidregg')
LEAN = Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean')

environment = json.loads((ROOT / 'experiments/results/environment.json').read_text())
paths = next(x['stdout'].strip() for x in environment['checks']
             if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
overlay = FORMAL / 'build/Theory'
overlay.mkdir(parents=True, exist_ok=True)
for artifact in (COMPANION / '.lake/build/lib/lean/Theory').iterdir():
    target = overlay / artifact.name
    if not target.exists() and not target.is_symlink():
        target.symlink_to(artifact)
source = FORMAL / 'Theory/PrivatePolicyEvolution.lean'
output = overlay / 'PrivatePolicyEvolution.olean'
if output.is_symlink():
    raise RuntimeError('Refusing output through a companion symlink')
env = dict(os.environ, LEAN_PATH=str(FORMAL / 'build') + ':' + paths)
args = [str(LEAN), '-o', str(output), str(source)]
p = subprocess.run(args, cwd=FORMAL, env=env, text=True, capture_output=True)
record = {'command': args, 'cwd': str(FORMAL), 'lean_path': env['LEAN_PATH'],
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'exit_code': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}
index = len(list(RESULTS.glob('lean_policy_*.json'))) + 1
(RESULTS / f'lean_policy_{index:02d}.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
if p.returncode or '--review' not in sys.argv:
    raise SystemExit(p.returncode)

original = (COMPANION / 'Theory.lean').read_text()
staged = original + '\nimport Theory.PrivatePolicyEvolution\n'
umbrella = FORMAL / 'build/Theory.lean'
umbrella.write_text(staged)
(overlay / 'PrivatePolicyEvolution.lean').write_text(source.read_text())
script = FORMAL / 'build/scripts/check-import-boundary.sh'
script.parent.mkdir(exist_ok=True)
script.write_text((COMPANION / 'scripts/check-import-boundary.sh').read_text())
patch = ''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
    fromfile='a/Theory.lean', tofile='b/Theory.lean'))
patch += ('diff --git a/Theory/PrivatePolicyEvolution.lean b/Theory/PrivatePolicyEvolution.lean\n'
          'new file mode 100644\n')
patch += ''.join(difflib.unified_diff([], source.read_text().splitlines(True),
    fromfile='/dev/null', tofile='b/Theory/PrivatePolicyEvolution.lean'))
patch_file = FORMAL / 'minidregg-private-policy-evolution.patch'
patch_file.write_text(patch)
review = {'scope': 'isolated module/umbrella against existing oleans, not a full clean build',
          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'patch_sha256': hashlib.sha256(patch_file.read_bytes()).hexdigest(),
          'base_umbrella_sha256': hashlib.sha256((COMPANION / 'Theory.lean').read_bytes()).hexdigest(),
          'checks': []}
for label, command, cwd in [
    ('umbrella', [str(LEAN), '-o', str(FORMAL / 'build/Theory.olean'), str(umbrella)], FORMAL / 'build'),
    ('boundary_staged', ['bash', str(script)], FORMAL / 'build'),
    ('boundary_existing', ['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION),
    ('patch', ['git', 'apply', '--check', str(patch_file)], COMPANION),
]:
    output_path = FORMAL / 'build/Theory.olean'
    if output_path.is_symlink():
        raise RuntimeError('Refuse umbrella write through a symlink')
    run = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
    review['checks'].append({'label': label, 'command': command, 'cwd': str(cwd),
                            'exit_code': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr})
    if run.returncode:
        break
review['all_passed'] = len(review['checks']) == 4 and all(x['exit_code'] == 0 for x in review['checks'])
index = len(list(RESULTS.glob('review_policy_*.json'))) + 1
(RESULTS / f'review_policy_{index:02d}.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review, indent=2))
raise SystemExit(0 if review['all_passed'] else 1)
