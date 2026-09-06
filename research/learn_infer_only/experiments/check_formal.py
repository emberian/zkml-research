#!/usr/bin/env python3
"""Check staged patch files against read-only companion oleans; retain failures."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
RESULTS = ROOT / 'experiments/results'
LEAN = Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean')


def main():
    environment = json.loads((RESULTS / 'environment.json').read_text())
    paths = next(x['stdout'].strip() for x in environment['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(FORMAL / 'build') + ':' + paths)
    # Lean resolves a namespace directory at the first search root, so overlay
    # the existing Assurance artifacts here without changing the companion.
    overlay = FORMAL / 'build/Assurance'
    overlay.mkdir(parents=True, exist_ok=True)
    for artifact in Path('/Users/ember/dev/minidregg/.lake/build/lib/lean/Assurance').iterdir():
        target = overlay / artifact.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
    names = sys.argv[1:] or ['ResidentReleaseContext', 'ResidentRestoreFinality']
    good = True
    for name in names:
        source = FORMAL / 'Assurance' / (name + '.lean')
        output = FORMAL / 'build/Assurance' / (name + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.is_symlink():
            raise RuntimeError(f'Refusing to write through companion symlink: {output}')
        args = [str(LEAN), '-o', str(output), str(source)]
        p = subprocess.run(args, cwd=FORMAL, env=env, text=True, capture_output=True)
        result = dict(command=args, cwd=str(FORMAL), lean_path=env['LEAN_PATH'],
                      source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr)
        index = len(list(RESULTS.glob(f'lean_{name}_*.json'))) + 1
        (RESULTS / f'lean_{name}_{index:02d}.json').write_text(json.dumps(result, indent=2)+'\n')
        print(f'{name}: exit {p.returncode}\n{p.stdout}{p.stderr}', flush=True)
        good &= p.returncode == 0
        if not good:
            return 1  # A dependent check must never consume a stale staged olean.
    return 0 if good else 1


if __name__ == '__main__':
    raise SystemExit(main())
