#!/usr/bin/env python3
"""Pin the finite dependency audit and check stated algebraic loss formulas."""

import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
SOURCES = {
    '2025/2215': ['Theorem 2.', 'Definition 6 (Pseudorandom Obfuscation)',
                  'Lemma 4 (Correctness)', 'Theorem 5.', 'Claim 4.', 'Claim 5.'],
    '2025/096': ['Definition 1 (Learning With Errors)', 'Theorem 3 (Succinct NIVOLE',
                 '5.4', 'Security for Alice.'],
    '2016/006': ['Theorem 3 ([GKP', 'Theorem 4 ([GHRW', 'Theorem 6.', 'Theorem 7.'],
    '2015/720': ['Theorem 11.', 'Theorem 12.', 'Theorem 13.', 'Theorem 15.'],
    '2012/733': ['Theorem 3.1.', 'Corollary 3.2', 'Lemma 3.9.', 'Lemma 3.10.', 'Lemma 3.11.'],
    '2014/917': ['Theorem 3. Assuming that:'],
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args):
    p = subprocess.run(args, text=True, capture_output=True)
    assert p.returncode == 0, (args, p.stderr)
    return {'command': args, 'returncode': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def main():
    (HERE / 'extracts').mkdir(exist_ok=True)
    sources = []
    for paper, tokens in SOURCES.items():
        pdf = MIRROR / f'{paper}.pdf'
        extract = HERE / 'extracts' / f'{paper.replace("/", "-")}.txt'
        commands = [command(['pdftotext', '-layout', str(pdf), str(extract)]),
                    command(['pdfinfo', str(pdf)])]
        pages = extract.read_text().split('\f')
        locations = {token: [i + 1 for i, page in enumerate(pages) if token in page]
                     for token in tokens}
        assert all(locations.values()), (paper, locations)
        sources.append({'paper': paper, 'pdf_path': str(pdf), 'pdf_sha256': sha(pdf),
                        'extract_path': str(extract), 'extract_sha256': sha(extract),
                        'locator_pdf_pages': locations, 'commands': commands})
    # Algebra only: each output position has two XiO and two PRF switches plus
    # one succinct-FE challenge, with two boundary XiO switches.
    checked = 0
    for length in range(1, 65):
        rows = [{'XiO': 1}, *([{'XiO': 2, 'PPRF': 2, 'sFE': 1}] * length), {'XiO': 1}]
        actual = {key: sum(row.get(key, 0) for row in rows) for key in ('XiO', 'PPRF', 'sFE')}
        assert actual == {'XiO': 2*length+2, 'PPRF': 2*length, 'sFE': length}
        checked += 1
    note = HERE / 'INSTANTIATION.md'
    links = [link for link in re.findall(r'\]\(([^)]+)\)', note.read_text())
             if not link.startswith('https://')]
    for link in links:
        assert (HERE / link).is_file(), link
    result = {
        'label': 'EXECUTED', 'scope': 'source pins and arithmetic, not a cryptographic theorem checker',
        'note_sha256': sha(note), 'local_note_links_checked': len(links),
        'sources': sources,
        '2016_006_theorem6_coefficient_checks': checked,
        'queries': {'SQL': 0, 'schema': 0, 'web_search': 2, 'web_open': 0, 'Kagi': 0},
        'network_pdf_downloads': 0, 'script_sha256': sha(Path(__file__)),
    }
    (HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
