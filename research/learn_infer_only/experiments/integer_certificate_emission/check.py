#!/usr/bin/env python3
"""Compile the isolated proposal, retaining every command, result and source hash."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FORMAL = ROOT / 'formal/integer_certificate_emission'
COMPANION = Path('/Users/ember/dev/minidregg')
LEAN = '/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'

def main():
    envlog = json.loads((ROOT / 'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in envlog['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    overlay = FORMAL / 'build/Compiler'
    overlay.mkdir(parents=True, exist_ok=True)
    for source in (COMPANION / '.lake/build/lib/lean/Compiler').iterdir():
        target = overlay / source.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(source)
    env = dict(os.environ, LEAN_PATH=str(FORMAL / 'build') + ':' + paths)
    name = sys.argv[1] if len(sys.argv) > 1 else 'IntegerCertificateEmission'
    source = FORMAL / 'Compiler' / (name + '.lean')
    output = overlay / (name + '.olean')
    if output.is_symlink():
        raise RuntimeError('Refusing companion symlink output')
    cmd = [LEAN, '-o', str(output), str(source)]
    process = subprocess.run(cmd, cwd=FORMAL, env=env, capture_output=True, text=True)
    record = dict(command=cmd, cwd=str(FORMAL), lean_path=env['LEAN_PATH'],
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  exit_code=process.returncode, stdout=process.stdout, stderr=process.stderr)
    index = len(list(HERE.glob('compile_' + name + '_*.json'))) + 1
    (HERE / f'compile_{name}_{index:02}.json').write_text(json.dumps(record, indent=2)+'\n')
    print(process.stdout + process.stderr)
    return process.returncode

if __name__ == '__main__':
    raise SystemExit(main())
