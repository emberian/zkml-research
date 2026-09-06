#!/usr/bin/env python3
"""Run the two new audits and the unchanged seed; retain exact commands/output."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'experiments/results'


def run(source, cwd=None):
    args = [sys.executable, str(source)]
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    result = dict(command=args, cwd=str(cwd) if cwd else None,
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr)
    (RESULTS / (source.stem + '_run.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(f'{source.name}: exit {p.returncode}', flush=True)
    if p.returncode:
        print(p.stdout, p.stderr)
        raise SystemExit(p.returncode)
    return p.stdout


def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    for name in ('writer_recovery', 'restore_release'):
        stdout = run(ROOT / 'experiments' / (name + '.py'))
        (RESULTS / (name + '.json')).write_text(json.dumps(json.loads(stdout), indent=2)+'\n')
    original = ROOT.parents[1] / 'swarm/astra-handoff/learn_infer_only_research/interface_audit.py'
    with tempfile.TemporaryDirectory(prefix='resident-seed-') as tmp:
        copied = Path(tmp) / original.name
        shutil.copyfile(original, copied)
        run(copied, Path(tmp))
        shutil.copyfile(Path(tmp) / 'results.json', RESULTS / 'interface_audit.json')
    print('All audit results retained under experiments/results.')


if __name__ == '__main__':
    main()
