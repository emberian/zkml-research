#!/usr/bin/env python3
"""Read-only local-paper provenance census. No network calls, no cryptographic test."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
SOURCES = [
    ('2025/2215', 'Obfuscating Pseudorandom Functions is Post-Quantum Complete',
     ['Theorem 2.', 'Definition 3 (Indistinguishability', 'Lemma 1.', 'Definition 6',
      'Lemma 4 (Correctness)', 'Theorem 5.', 'Post-condition reduction.', 'A.1       SMS']),
    ('2013/729', 'Functional Encryption for Randomized Functionalities',
     ['Definition 2.4', 'Lemma 2.9.', 'Definition 3.1.', 'Theorem 4.1.',
      'S3 simulates the decryption oracle', 'Claim A.4.', 'Lemma A.13.', 'C      SIM security']),
    ('2025/330', '(Multi-Input) FE for Randomized Functionalities, Revisited',
     ['Definition 3.9', 'Definition 4.3', '6.1    Parameters', 'Theorem 6.1.', 'Lemma 6.8.']),
    ('2016/006', 'Indistinguishability Obfuscation with Non-trivial Efficiency',
     ['Theorem 1.', 'Theorem 6.', 'Theorem 7.']),
    ('2013/650', 'On Extractability (a.k.a. Differing-Inputs) Obfuscation',
     ['Definition 6.1', 'Theorem 6.2.', 'Figure 2: Recursion algorithm']),
    ('2015/1113', 'Multi-Input Functional Encryption with Unbounded-Message Security',
     ['2.4    (d,', 'Definition 3.', 'Theorem 1.', 'Figure 8: Extractor',
      'We finally run the extractor']),
    ('2025/096', 'Simultaneous-Message and Succinct Secure Computation',
     ['Definition 4 (Simultaneous-Message', 'Security for Bob.', 'superpolynomial modulus-to-noise ratio']),
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv: list[str]) -> dict:
    result = subprocess.run(argv, text=True, capture_output=True, check=False)
    record = {'command': argv, 'returncode': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr}
    if result.returncode:
        raise RuntimeError(record)
    return record


def main() -> None:
    (ROOT / 'extracts').mkdir(exist_ok=True)
    records = []
    commands = []
    for identifier, title, locators in SOURCES:
        pdf = MIRROR / f'{identifier}.pdf'
        extract = ROOT / 'extracts' / f'{identifier.replace("/", "-")}.txt'
        commands.append(run(['pdftotext', '-layout', str(pdf), str(extract)]))
        info = run(['pdfinfo', str(pdf)])
        commands.append(info)
        content = extract.read_text()
        pages = content.split('\f')
        if not pages[-1].strip():
            pages.pop()
        matches = []
        for locator in locators:
            matches.append({'locator': locator, 'pdf_pages_1_based':
                            [i + 1 for i, page in enumerate(pages) if locator in page]})
        tokens = {}
        for term in ['quantum', 'QPT', 'auxiliary', 'sub-exponential', 'extractor']:
            tokens[term] = {'occurrences_case_insensitive': len(re.findall(re.escape(term), content, re.I)),
                            'pdf_pages_1_based': [i + 1 for i, page in enumerate(pages)
                                                 if re.search(re.escape(term), page, re.I)]}
        records.append({'id': identifier, 'title': title,
                        'url': f'https://eprint.iacr.org/{identifier}',
                        'pdf_path': str(pdf), 'pdf_sha256': digest(pdf),
                        'pdf_bytes': pdf.stat().st_size,
                        'extract_path': str(extract), 'extract_sha256': digest(extract),
                        'pdf_page_count': len(pages),
                        'locator_matches': matches, 'literal_token_census': tokens})
    output = {
        'label': 'EXECUTED', 'generated_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Seven named local PDFs only; pdftotext -layout literal-token and locator census. '
                 'No literature-absence or security conclusion follows from token counts.',
        'script_sha256': digest(Path(__file__)), 'sources': records,
        'commands': commands,
        'query_accounting': {'scry_sql': 0, 'scry_schema': 0, 'kagi': 0,
                             'web_search_queries': 4, 'web_open_urls': 3,
                             'pdf_downloads': 0},
    }
    (ROOT / 'source_manifest.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({
        'label': 'EXECUTED', 'sources': len(records),
        'source_manifest': str(ROOT / 'source_manifest.json'),
        'local_pdf_pages': sum(record['pdf_page_count'] for record in records),
        'all_pdf_commands_returned_zero': all(c['returncode'] == 0 for c in commands),
        'scope': output['scope'], 'query_accounting': output['query_accounting'],
    }, indent=2))


if __name__ == '__main__':
    main()
