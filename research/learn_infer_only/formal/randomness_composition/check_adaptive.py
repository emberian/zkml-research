#!/usr/bin/env python3
"""Check the dependent adaptive-context extension, preserving first green lane."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import sys
from check import HERE, BUILD, RESULTS, RESIDENT, COMPANION, LEAN, run


def main():
    theory = BUILD / 'Theory'
    theory.mkdir(parents=True, exist_ok=True)
    for artifact in (COMPANION / '.lake/build/lib/lean/Theory').iterdir():
        target = theory / artifact.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
    overlay = BUILD / 'Assurance'
    overlay.mkdir(parents=True, exist_ok=True)
    # First-tranche proposed modules take precedence; original companion oleans
    # fill the rest. Every output remains under this lane's own build directory.
    for directory in (RESIDENT / 'formal/build/Assurance', COMPANION / '.lake/build/lib/lean/Assurance'):
        for artifact in directory.iterdir():
            target = overlay / artifact.name
            if not target.exists() and not target.is_symlink():
                target.symlink_to(artifact)
    prior = json.loads((RESIDENT / 'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in prior['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(BUILD) + ':' + paths)
    source = HERE / 'Assurance/ResidentAdaptiveContext.lean'
    output = overlay / 'ResidentAdaptiveContext.olean'
    if output.is_symlink():
        raise RuntimeError('Refuse output through a companion symlink')
    if not run('adaptive_lean', [LEAN, '-o', str(output), str(source)], HERE, env, source):
        return 1
    if '--review' not in sys.argv:
        return 0
    # This patch DEPENDS on the first-tranche context patch. Check it against
    # that exact already-staged umbrella, not a guessed future companion tree.
    base_path = RESIDENT / 'formal/Assurance.lean'
    original = base_path.read_text()
    staged = original + '\nimport Assurance.ResidentAdaptiveContext\n'
    umbrella = BUILD / 'Assurance.lean'
    umbrella.write_text(staged)
    umbrella_output = BUILD / 'Assurance.olean'
    if umbrella_output.is_symlink():
        raise RuntimeError('Refuse umbrella output through a symlink')
    if not run('adaptive_umbrella', [LEAN, '-o', str(umbrella_output), str(umbrella)], BUILD, env, umbrella):
        return 1
    patch = ''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
                                        fromfile='a/Assurance.lean', tofile='b/Assurance.lean'))
    patch += ''.join(difflib.unified_diff([], source.read_text().splitlines(True),
                                        fromfile='/dev/null', tofile='b/Assurance/ResidentAdaptiveContext.lean'))
    patch_path = HERE / 'minidregg-adaptive-context.patch'
    patch_path.write_text(patch)
    isolated = BUILD / 'adaptive_patch_check'
    isolated.mkdir(exist_ok=True)
    (isolated / 'Assurance.lean').write_text(original)
    if not run('adaptive_patch_init', ['git', 'init', '-q'], isolated):
        return 1
    if not run('adaptive_patch_check', ['git', 'apply', '--check', str(patch_path)], isolated):
        return 1
    if not run('adaptive_boundary', ['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION):
        return 1
    manifest = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'patch_sha256': hashlib.sha256(patch_path.read_bytes()).hexdigest(),
                'base_umbrella_sha256': hashlib.sha256(base_path.read_bytes()).hexdigest(),
                'required_prior_patch': str(RESIDENT / 'formal/minidregg-resident-release.patch'),
                'scope': 'one global context-bearing full-word ROM reduction; one final output; staged umbrella; no full clean build',
                'companion_modified': False}
    (RESULTS / 'adaptive_review_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
