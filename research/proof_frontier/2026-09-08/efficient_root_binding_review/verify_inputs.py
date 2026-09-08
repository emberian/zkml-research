#!/usr/bin/env python3
"""Validate the author's frozen input claims; writes only the review directory."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'efficient_root_binding'
EXPECTED = {
    'AUDIT.md': '98fb3d92058fee53698ff4af191f70b12ac9e243b3c09e822c774de4e4f40d44',
    'RESULTS.json': 'dd4069f3028ef502471610f2e928744772e8bbf0ed4bda52d7483e934e6d99c6',
    'MANIFEST.json': '036da50e4a76d36581ea7d867096292008db6691661f0721471b3c71c63aa118',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for name, expected in EXPECTED.items():
        assert sha(AUTHOR / name) == expected, name
    manifest = json.loads((AUTHOR / 'MANIFEST.json').read_text())
    checked = []
    for group in ('checked_frozen_inputs', 'primary_sources', 'owned_artifacts'):
        for entry in manifest[group]:
            path = Path(entry['path'])
            assert path.stat().st_size == entry['bytes'], str(path)
            assert sha(path) == entry['sha256'], str(path)
            checked.append(dict(group=group, **entry))
    extra = []
    base = Path('/Users/ember/src/VCV-io-2026-09/VCVio/CryptoFoundations/MerkleTree')
    for relative in ('ExtractionKernel.lean', 'MultiExtractability/ResourceBounds.lean'):
        path = base / relative
        extra.append(dict(path=str(path), bytes=path.stat().st_size, sha256=sha(path)))
    links = 0
    for target in re.findall(r'\]\(([^)]+)\)', (HERE / 'REPORT.md').read_text()):
        if target.startswith('https://'):
            continue
        path = Path(re.sub(r':\d+$', '', target))
        if not path.is_absolute():
            path = HERE / path
        # This output is generated after link validation.
        assert path.name == 'INPUTS.json' or path.exists(), target
        links += 1
    result = dict(freeze=EXPECTED, author_manifest_entries_checked=len(checked),
                  checked=checked, additional_reviewed_sources=extra,
                  local_report_links_checked=links, all_match=True)
    (HERE / 'INPUTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(author_manifest_entries_checked=len(checked),
                          additional_source_pins=len(extra), local_links=links, all_match=True)))


if __name__ == '__main__':
    main()
