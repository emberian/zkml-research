#!/usr/bin/env python3
"""Compile only the multi-output extension against its checked dependencies."""
import difflib
import hashlib
import json
import os
import sys
from check import HERE, BUILD, RESIDENT, RESULTS, COMPANION, LEAN, run


def main():
    dependency = json.loads((RESULTS / 'adaptive_review_manifest.json').read_text())
    dependency_source = HERE / 'Assurance/ResidentAdaptiveContext.lean'
    if hashlib.sha256(dependency_source.read_bytes()).hexdigest() != dependency['source_sha256']:
        raise RuntimeError('Adaptive dependency changed since its successful review')
    prior = json.loads((RESIDENT / 'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in prior['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(BUILD) + ':' + paths)
    source = HERE / 'Assurance/ResidentMultiReceiptSchedule.lean'
    output = BUILD / 'Assurance/ResidentMultiReceiptSchedule.olean'
    if output.is_symlink():
        raise RuntimeError('Refuse companion output symlink')
    if not run('schedule_lean', [LEAN, '-o', str(output), str(source)], HERE, env, source):
        return 1
    if '--review' not in sys.argv:
        return 0
    original = (RESIDENT / 'formal/Assurance.lean').read_text() + '\nimport Assurance.ResidentAdaptiveContext\n'
    staged = original + '\nimport Assurance.ResidentMultiReceiptSchedule\n'
    umbrella = BUILD / 'Assurance.lean'
    umbrella.write_text(staged)
    umbrella_output = BUILD / 'Assurance.olean'
    if umbrella_output.is_symlink():
        raise RuntimeError('Refuse umbrella output symlink')
    if not run('schedule_umbrella', [LEAN, '-o', str(umbrella_output), str(umbrella)], BUILD, env, umbrella):
        return 1
    patch = ''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
                                        fromfile='a/Assurance.lean', tofile='b/Assurance.lean'))
    patch += ''.join(difflib.unified_diff([], source.read_text().splitlines(True),
                                        fromfile='/dev/null', tofile='b/Assurance/ResidentMultiReceiptSchedule.lean'))
    patch_path = HERE / 'minidregg-multi-receipt-schedule.patch'
    patch_path.write_text(patch)
    isolated = BUILD / 'schedule_patch_check'
    isolated.mkdir(exist_ok=True)
    (isolated / 'Assurance.lean').write_text(original)
    if not run('schedule_patch_init', ['git', 'init', '-q'], isolated):
        return 1
    if not run('schedule_patch_check', ['git', 'apply', '--check', str(patch_path)], isolated):
        return 1
    if not run('schedule_boundary', ['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION):
        return 1
    manifest = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'patch_sha256': hashlib.sha256(patch_path.read_bytes()).hexdigest(),
                'base_umbrella_sha256': hashlib.sha256(original.encode()).hexdigest(),
                'required_prior_patches': [str(RESIDENT / 'formal/minidregg-resident-release.patch'),
                                           str(HERE / 'minidregg-adaptive-context.patch')],
                'dependency_source_sha256': dependency['source_sha256'],
                'scope': 'query-complete shared-log schedule; public full-word badness selection; total prover+verifier queries; uniform-field classical ROM',
                'companion_modified': False}
    (RESULTS / 'schedule_review_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
