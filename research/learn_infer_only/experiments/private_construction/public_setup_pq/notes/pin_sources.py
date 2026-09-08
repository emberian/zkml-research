#!/usr/bin/env python3
"""Local source provenance only: hash/re-extract documents; no crypto protocol/network."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
SOURCES = {
    '2015-608': '2015/608.pdf',
    '2021-046': '2021/46.pdf',
    '2023-395': '2023/395.pdf',
    '2025-044': '2025/044.pdf',
    '2024-1572': '2024/1572.pdf',
    '2025-836': '2025/836.pdf',
    '2025-967': '2025/967.pdf',
    '2025-1039': '2025/1039.pdf',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

out = {'scope': 'local primary-source provenance only; no crypto execution',
       'source_rows': [], 'artifact_hashes': {}}
for ident, relative in SOURCES.items():
    pdf = MIRROR / relative
    txt = ROOT / 'extracts' / (ident + '.txt')
    saved = txt.read_bytes()
    command = ['pdftotext', '-layout', str(pdf), '-']
    p = subprocess.run(command, check=True, capture_output=True)
    assert p.stdout == saved, ident + ' saved extraction mismatch'
    out['source_rows'].append({
        'id': ident.replace('-', '/'), 'pdf_absolute_path': str(pdf),
        'pdf_sha256': sha(pdf.read_bytes()),
        'text_relative_path': str(txt.relative_to(ROOT)),
        'text_sha256': sha(saved),
        'command': command, 'exit_code': p.returncode,
        'matches_saved_text': True, 'stderr': p.stderr.decode(),
    })
for p in sorted([*ROOT.glob('notes/*.md'), *ROOT.glob('searches/*.json'),
                 Path(__file__)]):
    out['artifact_hashes'][str(p.relative_to(ROOT))] = sha(p.read_bytes())
out['all_source_extractions_match'] = True
(ROOT / 'notes' / 'SOURCE_MANIFEST.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
