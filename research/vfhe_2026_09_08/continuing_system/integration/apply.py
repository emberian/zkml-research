#!/usr/bin/env python3
"""Check the pinned proposal; apply only with --apply after the active run ends."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'MANIFEST.json').read_text())
    for name, expected in manifest['base'].items():
        if sha(ROOT / name) != expected:
            raise SystemExit('Base changed; review/rebase the proposal: ' + name)
    patch = HERE / 'APPLY-LATER.patch'
    if sha(patch) != manifest['patch_sha256']:
        raise SystemExit('Patch differs from reviewed manifest')
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=ROOT, check=True)
    if args.apply:
        subprocess.run(['git', 'apply', str(patch)], cwd=ROOT, check=True)
        for name, expected in manifest['new_files'].items():
            if sha(ROOT / name) != expected:
                raise SystemExit('Applied file differs from proposal: ' + name)
    print(json.dumps({'patch_applicable': True, 'applied': args.apply,
                      'patch_sha256': manifest['patch_sha256']}))


if __name__ == '__main__':
    main()
