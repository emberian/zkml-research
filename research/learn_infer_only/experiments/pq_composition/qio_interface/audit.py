#!/usr/bin/env python3
"""Local source pins and finite quantifier controls, not a cryptographic implementation."""

from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command):
    p = subprocess.run(command, text=True, capture_output=True)
    assert p.returncode == 0, (command, p.stderr)
    return {'command': command, 'returncode': p.returncode,
            'stdout': p.stdout, 'stderr': p.stderr}


def main():
    (HERE / 'extracts').mkdir(exist_ok=True)
    sources = []
    for paper, locators in [
        ('2023/265', ['A non-uniform quantum polynomial-time',
                      'Definition 4.3 (Indistinguishability obfuscation)',
                      'Definition 4.6 (Differing Inputs Circuits)']),
        ('2025/2215', ['Theorem 2.', 'Definition 3 (Indistinguishability obfuscation',
                       'Definition 6 (Pseudorandom Obfuscation)']),
    ]:
        pdf = MIRROR / f'{paper}.pdf'
        extract = HERE / 'extracts' / f'{paper.replace("/", "-")}.txt'
        commands = [run(['pdftotext', '-layout', str(pdf), str(extract)]),
                    run(['pdfinfo', str(pdf)])]
        pages = extract.read_text().split('\f')
        locations = {locator: [i + 1 for i, page in enumerate(pages) if locator in page]
                     for locator in locators}
        assert all(locations.values()), locations
        sources.append({'paper': paper, 'pdf_path': str(pdf), 'pdf_sha256': digest(pdf),
                        'extract_path': str(extract), 'extract_sha256': digest(extract),
                        'locator_pdf_pages': locations, 'commands': commands})

    # Scalar block controls for the cq averaging proof. Each delta is a conditional
    # acceptance-probability difference bounded by eps on good blocks. This is not
    # a proof over quantum channels: that proof is the linearity argument in the note.
    grid = [Fraction(i, 4) for i in range(5)]
    cases = 0
    for p, eps, d0, d1 in itertools.product(grid, grid, grid, grid):
        for signs in itertools.product((-1, 1), repeat=2):
            delta0, delta1 = signs[0] * eps * d0, signs[1] * eps * d1
            for mask in ((0, 0), (0, 1), (1, 0), (1, 1)):
                lhs = abs(p * mask[0] * delta0 + (1 - p) * mask[1] * delta1)
                good_mass = p * mask[0] + (1 - p) * mask[1]
                assert lhs <= good_mass * eps
                cases += 1
    # Unqualified average cancellation gives no zero-loss qualified guarantee.
    p = Fraction(1, 2)
    acceptance0, acceptance1 = (0, 1), (1, 0)
    total_gap = abs(p * sum(acceptance0) - p * sum(acceptance1))
    qualified_gap = abs(p * acceptance0[0] - p * acceptance1[0])
    assert total_gap == 0 and qualified_gap == Fraction(1, 2)
    # Each fixed k has one exceptional lambda; a moving k=lambda defeats uniformity.
    moving = [max(int(k == lam) for k in range(1, 33)) for lam in range(1, 33)]
    assert moving == [1] * 32
    note = HERE / 'QIO_INTERFACE.md'
    local_links = [target for target in re.findall(r'\]\(([^)]+)\)', note.read_text())
                   if not target.startswith('https://')]
    for target in local_links:
        assert (HERE / target).is_file(), target
    result = {
        'label': 'EXECUTED', 'scope': 'source provenance and finite scalar controls only',
        'note_sha256': digest(note), 'local_note_links_checked': len(local_links),
        'sources': sources,
        'averaging_bound_cases': cases,
        'unqualified_cancellation_countermodel': {
            'common_good_probability': '1/2', 'unqualified_gap': str(total_gap),
            'qualified_gap': str(qualified_gap),
            'scope': 'refutes inference from one unqualified mixed experiment; not a separation of complete iO definitions'},
        'moving_index_control': {'tested_lambdas': 32, 'supremum_gap_at_each': 1,
            'scope': 'illustrates the distinction between fixed labels and arbitrary lambda-indexed sequences'},
        'queries': {'SQL': 0, 'schema': 0, 'web_search': 3, 'web_HTML_open': 1, 'Kagi': 0},
        'network_pdf_downloads': 0,
        'script_sha256': digest(Path(__file__)),
    }
    (HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
