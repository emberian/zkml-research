#!/usr/bin/env python3
"""Source/frozen-input verification only. No cryptography or attack runtime."""
from hashlib import sha256
from pathlib import Path
import json
import platform


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def checked(path, expected):
    actual = digest(path)
    assert actual == expected, (str(path), expected, actual)
    return {'path': str(path), 'sha256': actual}


def main():
    here = Path(__file__).resolve().parent
    review = here.parent
    ingress = review.parent
    specifications = [
        {
            'id': '2025/330',
            'url': 'https://eprint.iacr.org/2025/330',
            'pdf': Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/330.pdf'),
            'pdf_sha': 'b7133ad8161f287b2a4b4d1a15664c4ace47fbce451d5f569a6d795261108fd2',
            'extract': ingress/'sources/2025-330.txt',
            'extract_sha': '88e4fa7f4120767c0724bf37d757e0ea1ed24ca0d6eefa9ea181148fa2249e54',
            'access': 'Notation p15; PKE/iO definitions p18; NIZK p21; Defs4.1-4.4 pp21-23; recalled older definition and footnote6 pp28-29; section6.1/Construction2 pp48-49; Thm6.1 and hybrids pp50-63; Lemmas6.2-6.8 and final sum pp64-67. Retained text read with rg/sed; no new extraction.',
            'anchors': ['Throughout, we will use', 'Definition 4.3', 'Definition 4.4',
                        'all non-uniform PPT adversaries A',
                        'The original definition in [GJKS15] considers non-uniform attackers',
                        'Lemma 6.2.', 'Lemma 6.8.'],
            'quantifier_search_terms': ['non-uniform', 'nonuniform', 'auxiliary',
                'auxilliary', 'compatible', 'compatibility', 'generator',
                'coin tosses', 'randomness of', 'probability is over'],
        },
        {
            'id': '2007/155',
            'url': 'https://eprint.iacr.org/2007/155',
            'pdf': Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2007/155.pdf'),
            'pdf_sha': '45358698cdd4007dddbabf74f7e32e7762d963637c8e3bfae5be2235df64868e',
            'extract': review/'dual_mode_sources/2007-155.txt',
            'extract_sha': '0c4b2fc7fa3d22f1e85277cb8b2189052be1d69d966c465efaa46be25ac9d2f5',
            'access': 'Defs4-5 pp9-10; scalar commitments, source CRS and SXDH instantiation pp24-28; section11 construction/Theorem18 and proof pp34-36. Retained text read with rg/sed; no new extraction.',
            'anchors': ['Definition 4 (Composable', 'Definition 5 (Composable',
                        'Theorem 15', 'Theorem 18'],
        },
    ]
    sources = []
    for spec in specifications:
        pdf = checked(spec['pdf'], spec['pdf_sha'])
        extract = checked(spec['extract'], spec['extract_sha'])
        pages = spec['extract'].read_text().split('\f')
        locations = {term: [i+1 for i, page in enumerate(pages) if term in page]
                     for term in spec['anchors']}
        assert all(locations.values())
        source = {'id': spec['id'], 'url': spec['url'], 'pdf': pdf,
                  'retained_extract': extract, 'access': spec['access'],
                  'anchor_PDF_pages_1_based': locations}
        if 'quantifier_search_terms' in spec:
            source['quantifier_search_terms'] = spec['quantifier_search_terms']
        sources.append(source)

    frozen_checks = []
    for name in ['review_hashes.json', 'dual_mode_hashes.json']:
        path = review/name
        manifest = json.loads(path.read_text())
        records = [checked(Path(item['path']), item['sha256'])
                   for item in manifest['files']]
        frozen_checks.append({'manifest': {'path': str(path), 'sha256': digest(path)},
                              'verified_files': records})
    completion_path = review/'parameter_review_completion.json'
    completion = json.loads(completion_path.read_text())
    parameter_records = []
    for item in completion['identities']:
        for category in ['preserved_copy', 'current']:
            record = item[category]
            parameter_records.append(checked(Path(record['path']), record['sha256']))
    for key in ['historical_manifest', 'historical_manifest_archive',
                'completion_note', 'verification', 'independent_review',
                'independent_review_manifest']:
        record = completion[key]
        parameter_records.append(checked(Path(record['path']), record['sha256']))
    frozen_checks.append({'manifest': {'path': str(completion_path),
                                      'sha256': digest(completion_path)},
                          'verified_files': parameter_records})
    note = here/'TERMINAL_JOINT.md'
    assert all(line == line.rstrip() for line in note.read_text().splitlines())
    result = {
        'classification': 'EXECUTED primary-source identities and frozen-input verification only',
        'command': f'python3 {Path(__file__).resolve()}',
        'python': platform.python_version(),
        'verifier_sha256': digest(Path(__file__).resolve()),
        'note': {'path': str(note), 'sha256': digest(note)},
        'sources': sources,
        'frozen_checks': frozen_checks,
        'all_expected_identities_match': True,
        'note_trailing_whitespace_check': True,
        'accounting': {'web_search_queries': 0, 'web_HTML_opens': 2,
                       'scry_sql': 0, 'scry_schema': 0, 'kagi': 0,
                       'new_PDF_extracts': 0, 'PDF_downloads': 0,
                       'attack_recovery_or_extraction_runtimes': 0},
        'web_scope': 'Primary eprint HTML publication/version metadata only; theorem/game evidence is the pinned local full text.',
    }
    data = json.dumps(result, indent=2)+'\n'
    (here/'sources.json').write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
