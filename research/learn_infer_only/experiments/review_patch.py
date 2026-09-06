#!/usr/bin/env python3
"""Generate/review the companion patch; never apply it to the companion tree.

Checks the staged Assurance umbrella against existing dependency oleans, the
companion import-boundary script, patch applicability, and local evidence schemas.
"""
from pathlib import Path
import csv
import difflib
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
RESULTS = ROOT / 'experiments/results'
COMPANION = Path('/Users/ember/dev/minidregg')


def main():
    modules = ['ResidentReleaseContext', 'ResidentRestoreFinality']
    base = (COMPANION / 'Assurance.lean').read_text()
    staged = base.rstrip() + '\n' + ''.join('import Assurance.' + n + '\n' for n in modules)
    pieces = []
    for name in modules:
        rel = 'Assurance/' + name + '.lean'
        contents = (FORMAL / rel).read_text()
        checks = sorted(RESULTS.glob('lean_' + name + '_*.json'))
        latest = json.loads(checks[-1].read_text())
        if latest['exit_code'] != 0 or latest['source_sha256'] != hashlib.sha256(contents.encode()).hexdigest():
            raise RuntimeError('No successful source-matching Lean check for ' + rel)
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|^#guard\s', contents, re.M):
            raise RuntimeError('Forbidden proof shortcut in ' + rel)
        # Every theorem must have one observed exact-output axiom pin.
        theorems = len(re.findall(r'^theorem ', contents, re.M))
        pins = len(re.findall(r'^#guard_msgs .* in #print axioms ', contents, re.M))
        if theorems != pins:
            raise RuntimeError(f'{rel}: {theorems} theorems but {pins} pins')
        pieces.append('diff --git a/' + rel + ' b/' + rel + '\n')
        pieces.append('new file mode 100644\n')
        pieces.extend(difflib.unified_diff([], contents.splitlines(keepends=True),
                                         fromfile='/dev/null', tofile='b/' + rel))
    pieces.append('diff --git a/Assurance.lean b/Assurance.lean\n')
    pieces.extend(difflib.unified_diff(base.splitlines(keepends=True), staged.splitlines(keepends=True),
                                     fromfile='a/Assurance.lean', tofile='b/Assurance.lean'))
    patch = FORMAL / 'minidregg-resident-release.patch'
    patch.write_text(''.join(pieces))
    # Generated staging copy, ignored; no write into minidregg.
    umbrella = FORMAL / 'Assurance.lean'
    umbrella.write_text(staged)
    environment = json.loads((RESULTS / 'environment.json').read_text())
    paths = next(x['stdout'].strip() for x in environment['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(FORMAL / 'build') + ':' + paths)
    lean = '/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
    checks = [
        ([lean, '-o', str(FORMAL / 'build/Assurance.olean'), str(umbrella)], FORMAL),
        (['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION),
        (['git', 'apply', '--check', str(patch)], COMPANION),
    ]
    results = []
    for args, cwd in checks:
        if args[0] == lean and (FORMAL / 'build/Assurance.olean').is_symlink():
            raise RuntimeError('Refusing to write through an umbrella symlink')
        p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
        results.append(dict(command=args, cwd=str(cwd), exit_code=p.returncode,
                            stdout=p.stdout, stderr=p.stderr))
        print(f'{args[0]}: exit {p.returncode}\n{p.stdout}{p.stderr}', flush=True)
    for name in ('CREDENTIALS.csv', 'COSTS.csv'):
        with (ROOT / name).open(newline='') as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            assert rows and all(None not in row and all(v is not None for v in row.values())
                                for row in rows), name
        results.append(dict(check=name + ' rectangular schema', rows=len(rows), exit_code=0))
    result = dict(patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),
                  original_umbrella_sha256=hashlib.sha256(base.encode()).hexdigest(),
                  staged_umbrella_sha256=hashlib.sha256(staged.encode()).hexdigest(), checks=results)
    current = RESULTS / 'patch_review.json'
    if current.exists():
        index = len(list(RESULTS.glob('patch_review_previous_*.json'))) + 1
        (RESULTS / f'patch_review_previous_{index:02d}.json').write_text(current.read_text())
    current.write_text(json.dumps(result, indent=2)+'\n')
    return 0 if all(c['exit_code'] == 0 for c in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
