#!/usr/bin/env python3
"""Seal this bounded review using public bytes only; execute no author program."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/journal'
EXPECTED = '1d5901a81cb0056f94878878af3737865bb804bf3cd16533e9a3582bb7d676a9'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    subject = AUTHOR / 'FINAL_MANIFEST.json'
    raw_manifest = subject.read_bytes()
    assert sha(raw_manifest) == EXPECTED
    author_manifest = json.loads(raw_manifest)
    assert len(author_manifest['files']) == 110
    for name, item in author_manifest['files'].items():
        path = AUTHOR / name
        assert path.resolve().is_relative_to(AUTHOR.resolve())
        assert not set(path.parts).intersection(['.private', 'runtime', '__pycache__'])
        data = path.read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], name

    source = json.loads((BASE / 'source_review.json').read_bytes())
    records = json.loads((BASE / 'record_review.json').read_bytes())
    for name, digest in source['source_file_hashes'].items():
        assert author_manifest['files'][name]['sha256'] == digest
    for name, digest in records['public_artifacts_sha256'].items():
        assert author_manifest['files']['reports/normal_002/' + name]['sha256'] == digest
    assert source['public_root'] == str(AUTHOR / 'reports/normal_002')
    for name in ['source_review.stderr.txt', 'record_review.stderr.txt']:
        assert (BASE / name).read_bytes() == b''

    files = [p for p in sorted(BASE.iterdir()) if p.is_file() and p.name != 'review_manifest.json']
    for path in files:
        text = path.read_text()
        assert all(line.rstrip() == line for line in text.splitlines()), path.name
        if path.suffix == '.py':
            compile(text, str(path), 'exec')
    assert len((BASE / 'REPORT.md').read_text().splitlines()) < 400
    result = {
        'schema': 'independent-public-setup-journal-review-v1',
        'claim_kind': 'EXECUTED',
        'reviewer': '/root/independent_review',
        'as_of_date_utc': '2026-09-08',
        'subject': str(subject.relative_to(ROOT)),
        'subject_sha256': EXPECTED,
        'verdict': 'Accept source-level public setup join and normal integration; no extension of accepted-value DDH to timing-bearing genesis or full instrumented view',
        'checks': {
            'author_public_files_unchanged': len(author_manifest['files']),
            'launch_sources_match_final_manifest': len(source['source_file_hashes']),
            'reviewed_public_records_match_final_manifest': len(records['public_artifacts_sha256']),
            'review_scripts_compile': True,
            'review_stderr_empty': True,
            'review_whitespace': True,
            'report_under_400_lines': True,
        },
        'activity': {
            'author_program_invocations': 0,
            'group_or_signature_verification': 0,
            'private_file_reads_or_hashes': 0,
            'network_queries': 0,
            'author_file_edits': 0,
            'commits': 0,
        },
        'artifacts': [{'path': str(p.relative_to(ROOT)), 'sha256': sha(p.read_bytes())}
                      for p in files],
    }
    (BASE / 'review_manifest.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['checks'], indent=2))


if __name__ == '__main__':
    main()
