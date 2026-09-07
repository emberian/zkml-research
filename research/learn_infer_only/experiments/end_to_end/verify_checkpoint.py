#!/usr/bin/env python3
"""Read-only rehash of a saved root collection inventory and companion state."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('inventory', type=Path)
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    count = 0
    for group in inventory['groups']:
        assert digest(group['manifest']) == group['sha256'], group['manifest']
        for entry in group['checked']:
            path = Path(entry['path'])
            assert path.stat().st_size == entry['bytes'], str(path)
            assert digest(path) == entry['sha256'], str(path)
            count += 1
    baseline = json.loads((Path(__file__).parent / 'baseline.json').read_text())
    for entry in baseline['companions'].values():
        path = entry['path']
        head = subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD'], text=True).strip()
        status = subprocess.check_output(['git', '-C', path, 'status', '--porcelain=v1', '--untracked-files=all'], text=True)
        assert head == entry['head'] and status == entry['status'], path
        assert inventory['companions_observed'][path] == {'head': head, 'status': status}, path
    assert count == inventory['file_links_checked']
    print(json.dumps({'passed': True, 'manifest_count': len(inventory['groups']),
                      'file_links_checked': count, 'companions_unchanged_from_baseline': True,
                      'inventory_sha256': digest(args.inventory),
                      'verifier_sha256': digest(__file__)}))


if __name__ == '__main__':
    main()
