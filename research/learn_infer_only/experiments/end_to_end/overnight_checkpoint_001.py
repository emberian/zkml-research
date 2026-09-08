#!/usr/bin/env python3
"""Collect the first completed overnight artifacts without executing crypto."""
from pathlib import Path
import datetime
import json
import subprocess
from collect_interrupted_run import HERE, REPO, SEEN, pin, read, check_manifest


def main():
    review = HERE.parent / 'adversarial_review'
    counts = {}
    for name in ('direct_multioutput', 'compact_tmre'):
        m = read(review / name / 'review_manifest.json')
        for item in m['artifacts']:
            pin(REPO / item['path'], item['sha256'])
        counts[name] = len(m['artifacts'])
    utility = HERE / 'private_ema/utility'
    counts['utility'] = check_manifest(utility / 'manifest.json')
    formal = REPO / 'research/learn_infer_only/formal/private_address_ema'
    checked = read(formal / 'results/verification.json')
    assert checked['all_passed']
    assert checked['census']['theorem_count'] == checked['census']['pin_count'] == 28
    for name, digest in checked['inputs'].items():
        pin(REPO / name, digest)
    counts['private_address_ema_pins'] = 28
    capsule = HERE.parent / 'private_construction/receipt_key_capsule'
    cm = read(capsule / 'notes/SOURCE_MANIFEST.json')
    for item in cm['source_rows']:
        pin(item['pdf_absolute_path'], item['pdf_sha256'])
        pin(capsule / item['text_relative_path'], item['text_sha256'])
    for name, digest in cm['artifact_hashes'].items():
        pin(capsule / name, digest)
    counts['capsule_sources'] = len(cm['source_rows'])
    pin(capsule / 'notes/AUDIT.md', '3a52157a95fd416cbc09f690482e01293cc8b35dbc3031a09b1f4f690d8f1b95')
    pin(review / 'receipt_key_capsule/REPORT.md')
    frontier = REPO / 'research/proof_frontier/2026-09-08'
    fm = read(frontier / 'SOURCES.json')
    for name, digest in fm['evidence_sha256'].items():
        pin(frontier / name, digest)
    counts['frontier_evidence'] = len(fm['evidence_sha256'])
    kernel = frontier / 'formal/polynomial_kernel'
    km = read(kernel / 'provenance.json')
    pin(kernel / 'PolynomialMatrixKernel.lean', km['files_sha256']['Theory/PolynomialMatrixKernel.lean'])
    pin(kernel / 'ArkLib-Apache-2.0.txt', km['files_sha256']['LICENSES/ArkLib-Apache-2.0.txt'])
    pin(kernel / 'polynomial-kernel.patch', km['patch_sha256'])
    counts['polynomial_kernel_pins'] = 8
    baseline = read(HERE / 'overnight_2026-09-08_baseline.json')
    companion_checks = {}
    for name in ('minidregg', 'breadstuffs'):
        item = baseline['repositories'][name]
        root = Path(item['path'])
        head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
        status = subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain=v1', '--untracked-files=all'], text=True)
        assert head == item['head'], name
        assert status == item['status'], name
        for relative, recorded in item['preexisting_dirty_content'].items():
            assert len(pin(root / relative, recorded['sha256'])) == recorded['bytes']
        companion_checks[name] = {'head_unchanged': True, 'status_unchanged': True,
                                 'preexisting_dirty_content_unchanged': True}
    out = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'scope': 'Saved public source/evidence collection; no new cryptography or Lean execution',
           'counts': counts, 'companions': companion_checks, 'files': SEEN,
           'all_passed': True}
    (HERE / 'overnight_checkpoint_001.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({'all_passed': True, 'counts': counts, 'hashed_files': len(SEEN)}))


if __name__ == '__main__':
    main()
