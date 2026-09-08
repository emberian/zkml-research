#!/usr/bin/env python3
"""Rehash completed public evidence; do not execute crypto or read private state."""
from pathlib import Path
import datetime
import json
import subprocess
from collect_interrupted_run import HERE, REPO, SEEN, pin, read

R = REPO / 'research/learn_infer_only'
COUNTS = {}


def public_pin(path, expected=None):
    path = Path(path)
    assert 'private' not in path.parts and path.name not in ('client_key.bin', 'secret_key.bin'), path
    return pin(path, expected)


def items(base, rows):
    count = 0
    if isinstance(rows, dict):
        rows = [dict(path=p, sha256=v if isinstance(v, str) else v['sha256']) for p, v in rows.items()]
    for row in rows:
        data = public_pin(base / row['path'], row['sha256'])
        if 'bytes' in row:
            assert len(data) == row['bytes']
        count += 1
    return count


def manifest(relative, key, root=None):
    p = R / relative
    d = read(p)
    base = p.parent if root is None else root
    COUNTS[relative] = items(base, d[key])
    return d


def main():
    for name in ('public_setup_journal', 'fixed_coordinate_qpt'):
        manifest('experiments/adversarial_review/' + name + '/review_manifest.json', 'artifacts', REPO)
    manifest('experiments/adversarial_review/emitted_ema/review_manifest.json', 'outputs_sha256')
    manifest('experiments/adversarial_review/public_setup_pq/MANIFEST.json', 'artifacts')
    manifest('experiments/adversarial_review/public_setup_pq/quantitative_regularity/MANIFEST.json', 'artifacts')
    manifest('formal/private_ema_dynamics/manifest.json', 'entries')
    failed = manifest('experiments/end_to_end/private_ema/encrypted_successor/manifest.json', 'files')
    assert not failed['cryptographic_workload_completed']
    for name in ('emitted_runtime', 'emitted_fixed_fft'):
        manifest('experiments/end_to_end/private_ema/' + name + '/freeze.json', 'files', Path('/'))
        public_pin(HERE / 'private_ema' / name / 'summary.json')
    journal = 'experiments/private_construction/designated_span/public_coin_setup/'
    manifest(journal + 'journal/FINAL_MANIFEST.json', 'files')
    public_pin(R / (journal + 'adapter/FINAL_MANIFEST.json'))
    pq = R / 'experiments/private_construction/public_setup_pq'
    sources = read(pq / 'notes/SOURCE_MANIFEST.json')
    assert sources['all_source_extractions_match']
    for row in sources['source_rows']:
        public_pin(row['pdf_absolute_path'], row['pdf_sha256'])
        public_pin(pq / row['text_relative_path'], row['text_sha256'])
    items(pq, sources['artifact_hashes'])
    cm = read(pq / 'costs/COST_MANIFEST.json')
    assert cm['all_recorded_input_hashes_match'] and cm['frozen_audit_unchanged']
    for key in ('additional_sources_sha256', 'artifact_sha256'):
        if key in cm:
            items(pq / 'costs', cm[key])
    for name in ('private_address_ema', 'private_address_ema/emitted_schedule'):
        v = read(R / 'formal' / name / 'results/verification.json')
        assert v['all_passed']
        for p, digest in v.get('inputs', {}).items():
            public_pin(REPO / p, digest)
    frontier = REPO / 'research/proof_frontier/2026-09-08'
    fm = read(frontier / 'formal/full_ud/manifest.json')
    assert fm['exact_byte_checks_complete'] and fm['all_pins_standard_only']
    public_pin(frontier / 'formal/full_ud/full-ud.patch', fm['patch_sha256'])
    owned = [row for row in fm['modules'] if row['owned']]
    for row in owned:
        public_pin(frontier / 'formal/full_ud/src' / row['path'], row['sha256'])
    assert sum(len(row['pins']) for row in owned) == 38
    public_pin(frontier / 'formal/polynomial_kernel/all_pins_successor/PolynomialMatrixKernel.lean', '6c2aa5d0be03d7c00c3aca459eff2532570f205f6af604210f2cf033aaaec5dd')
    public_pin(frontier / 'formal/polynomial_kernel/all_pins_successor/polynomial-kernel.patch', '83b4a44a855109efbbcc2b467f4531c52faf1374e5a83718c884277b8c275ae4')
    for name, digest in {
        'PolynomialGluing.lean': '898da7979dd4f3ed387c8a83d9e2a19dd1e70f6dcb82b09098f7c18c7a0b7f41',
        'PolynomialGluingStatement.lean': '8f7fb82b2d8003cc034ca1a0035495b38a104f4bbb4c91e62b11b962f0ab4cf0',
        'PolynomialBivariate.lean': 'fef487127bd25f43775a238add6bdb3d7becbdd6745af393fd2bd834daa18dd0'
    }.items():
        public_pin(frontier / 'formal/polynomial_gluing/universe_successor' / name, digest)
    for name in ('ema_byte_determinism/REPORT.md', 'private_address_ema/REPORT.md'):
        public_pin(R / 'experiments/adversarial_review' / name)
    baseline = read(HERE / 'overnight_2026-09-08_baseline.json')
    companions = {}
    for name in ('minidregg', 'breadstuffs'):
        b = baseline['repositories'][name]
        root = Path(b['path'])
        assert subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip() == b['head']
        assert subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain=v1', '--untracked-files=all'], text=True) == b['status']
        for p, row in b['preexisting_dirty_content'].items():
            assert len(public_pin(root / p, row['sha256'])) == row['bytes']
        companions[name] = dict(head_unchanged=True, status_unchanged=True, dirty_file_bytes_unchanged=True)
    out = dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), all_passed=True,
        scope='Public saved-evidence and source hash verification only; no crypto, private-state inspection or new Lean execution. Manifest booleans are checked records, not independently rerun claims.',
        counts=COUNTS, files=SEEN, companions=companions)
    (HERE / 'overnight_checkpoint_002.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(dict(all_passed=True, files_hashed=len(SEEN), inventories=len(COUNTS))))


if __name__ == '__main__':
    main()
