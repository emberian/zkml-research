#!/usr/bin/env python3
"""Read-only companion build overlay; logs failed and successful attempts."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
RESIDENT = HERE.parents[1]
COMPANION = Path('/Users/ember/dev/minidregg')
BUILD = HERE / 'build'
RESULTS = HERE / 'results'
LEAN = '/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, command, cwd, env=None, source=None):
    p = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
    result = {'command': command, 'cwd': str(cwd), 'exit_code': p.returncode,
              'stdout': p.stdout, 'stderr': p.stderr}
    if source is not None:
        result['source_sha256'] = digest(source)
    i = len(list(RESULTS.glob(label + '_*.json'))) + 1
    (RESULTS / f'{label}_{i:02}.json').write_text(json.dumps(result, indent=2) + '\n')
    print(label, p.returncode, p.stdout, p.stderr, flush=True)
    return p.returncode == 0


def main():
    RESULTS.mkdir(exist_ok=True)
    BUILD.mkdir(exist_ok=True)
    prior = json.loads((RESIDENT / 'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in prior['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    overlay = BUILD / 'Selvage'
    overlay.mkdir(exist_ok=True)
    for artifact in (COMPANION / '.lake/build/lib/lean/Selvage').iterdir():
        target = overlay / artifact.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
    env = dict(os.environ, LEAN_PATH=str(BUILD) + ':' + paths)
    source = HERE / 'Selvage/RandomnessSelection.lean'
    output = overlay / 'RandomnessSelection.olean'
    if output.is_symlink():
        raise RuntimeError('Refuse output through a companion symlink')
    if not run('lean', [LEAN, '-o', str(output), str(source)], HERE, env, source):
        return 1
    if '--review' not in sys.argv:
        return 0
    original = (COMPANION / 'Selvage.lean').read_text()
    staged = original + '\nimport Selvage.RandomnessSelection\n'
    umbrella = BUILD / 'Selvage.lean'
    umbrella.write_text(staged)
    umbrella_output = BUILD / 'Selvage.olean'
    if umbrella_output.is_symlink():
        raise RuntimeError('Refuse umbrella output through a symlink')
    if not run('umbrella', [LEAN, '-o', str(umbrella_output), str(umbrella)], BUILD, env, umbrella):
        return 1
    boundary = (COMPANION / 'scripts/check-import-boundary.sh').read_text()
    # The actual boundary script checks its own root. Run a byte-identical copy
    # over only this lane's staged tree, then run the original read-only too.
    scripts = BUILD / 'scripts'
    scripts.mkdir(exist_ok=True)
    (scripts / 'check-import-boundary.sh').write_text(boundary)
    (BUILD / 'Theory.lean').write_text('')
    (BUILD / 'Theory').mkdir(exist_ok=True)
    # Add the new source to the overlay; all existing linked files are oleans.
    (overlay / 'RandomnessSelection.lean').write_text(source.read_text())
    for label, command, cwd in (
        ('boundary_staged', ['bash', str(scripts / 'check-import-boundary.sh')], BUILD),
        ('boundary_existing', ['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION),
    ):
        if not run(label, command, cwd):
            return 1
    patch = ''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
                                        fromfile='a/Selvage.lean', tofile='b/Selvage.lean'))
    patch += ''.join(difflib.unified_diff([], source.read_text().splitlines(True),
                                        fromfile='/dev/null', tofile='b/Selvage/RandomnessSelection.lean'))
    patch_path = HERE / 'minidregg-randomness-selection.patch'
    patch_path.write_text(patch)
    if not run('patch_check', ['git', 'apply', '--check', str(patch_path)], COMPANION):
        return 1
    manifest = {'source_sha256': digest(source), 'patch_sha256': digest(patch_path),
                'base_umbrella_sha256': digest(COMPANION / 'Selvage.lean'),
                'scope': 'staged file and umbrella elaboration against read-only companion oleans; not clean full build',
                'companion_modified': False}
    (RESULTS / 'review_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
