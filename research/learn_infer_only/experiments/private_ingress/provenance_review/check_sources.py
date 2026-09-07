#!/usr/bin/env python3
"""Pin/reread local PDFs; verify frozen predecessor artifacts without edits."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
INGRESS = HERE.parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    previous = json.loads((INGRESS / 'source_manifest.json').read_text())
    provenance = json.loads((INGRESS / 'provenance/source_manifest.json').read_text())
    expected = {Path(s['path']).parts[-2] + '/' + Path(s['path']).stem: s['sha256']
                for s in previous['sources']}
    expected.update({s['id']: s['pdf_sha256'] for s in provenance['sources']})
    extract_expected = {s['id']: s['extract_sha256'] for s in provenance['sources']}
    scopes = {
        '2025/330': ('Definitions 3.8,4.1-4.4; Construction 2; section 6.1; Theorem 6.1 and early proof hybrids',
                     'printed/PDF 18,21-23,48-51',
                     ['Definition 3.8', 'Definition 4.3', 'Theorem 6.1.']),
        '2020/137': ('Figures 14-15; Theorem 6.2; Lemmas 6.3-6.4; base-key return and privacy switch',
                     'printed 28-32; PDF 30-34',
                     ['Theorem 6.2.', 'Lemma 6.3', 'Lemma 6.4']),
        '2016/629': ('Appendix D Definitions 12-14; Appendix G Definition 15 and Theorem 8',
                     'printed/PDF 35-37,53-56',
                     ['Definition 13.', 'Definition 15.', 'Theorem 8.']),
        '2013/729': ('Definition 2.4; Remark 2.5; Lemma 2.9; Theorem 4.1; source theorem assumed, not full reduction reproof',
                     'printed/PDF 7-9,14',
                     ['Definition 2.4', 'Lemma 2.9.', 'Theorem 4.1.'])}
    entries = []
    for paper, (scope, pages, anchors) in scopes.items():
        pdf = MIRROR / f'{paper}.pdf'
        actual = digest(pdf)
        assert actual == expected[paper], (paper, 'PDF changed')
        cmd = ['pdftotext', '-layout', str(pdf), '-']
        proc = subprocess.run(cmd, capture_output=True, check=True)
        extracted = sha256(proc.stdout).hexdigest()
        retained = INGRESS / ('sources' if paper in ('2025/330', '2013/729')
                              else 'provenance/sources') / (paper.replace('/', '-') + '.txt')
        assert extracted == digest(retained), (paper, 'retained extract differs')
        if paper in extract_expected:
            assert extracted == extract_expected[paper], (paper, 'frozen extract changed')
        page_texts = proc.stdout.decode().split('\f')
        positions = {a: [i + 1 for i, page in enumerate(page_texts) if a in page]
                     for a in anchors}
        entries.append({'id': paper, 'url': f'https://eprint.iacr.org/{paper}',
                        'pdf_path': str(pdf), 'pdf_sha256': actual,
                        'matches_frozen_pdf_hash': True,
                        'retained_extract_path': str(retained), 'extract_sha256': extracted,
                        'fresh_extract_matches_retained': True,
                        'access': scope, 'location': pages,
                        'anchor_PDF_pages_1_based': positions,
                        'extraction_command': cmd, 'exit_code': proc.returncode,
                        'stderr': proc.stderr.decode()})

    paths = [INGRESS.parent.parent / 'PRIVATE_INGRESS.md']
    paths += [p for p in INGRESS.iterdir() if p.is_file()]
    paths += [p for p in (INGRESS / 'provenance').iterdir() if p.is_file()]
    hashes = [{'path': str(p), 'sha256': digest(p)} for p in sorted(paths)]
    frozen_path = HERE / 'frozen_hashes.json'
    if frozen_path.exists():
        assert json.loads(frozen_path.read_text())['files'] == hashes, 'Frozen predecessor changed'
    else:
        frozen_path.write_text(json.dumps({'classification': 'EXECUTED read-only snapshot of frozen predecessors',
                                          'files': hashes}, indent=2) + '\n')
    manifest = {'classification': 'EXECUTED local source reproduction and predecessor-hash checks',
                'sources': entries,
                'accounting': {'scry_sql': 0, 'scry_schema': 0, 'kagi': 0,
                               'web_search_queries': 0, 'web_HTML_opens': 4,
                               'PDF_downloads': 0},
                'web_HTML_only': [f'https://eprint.iacr.org/{p}' for p in scopes],
                'frozen_predecessor_files': len(hashes)}
    dest = HERE / 'source_manifest.json'
    if dest.exists():
        assert json.loads(dest.read_text()) == manifest, 'Source manifest changed'
    else:
        dest.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'all_four_PDF_hashes_match_frozen_manifests': True,
                      'all_four_reproduced_extracts_match': True,
                      'frozen_predecessor_files_unchanged': len(hashes),
                      'anchors': {s['id']: s['anchor_PDF_pages_1_based'] for s in entries}}, indent=2))


if __name__ == '__main__':
    main()
