#!/usr/bin/env python3
"""Run one fresh two-class native-witness service and retain total process cost."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PYTHON = REPO / 'research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', default='fast001')
    args = parser.parse_args()
    if not args.run.isalnum(): parser.error('run ID must be alphanumeric')
    directory = HERE / 'launches' / args.run
    if directory.exists() or (HERE / 'runtime' / args.run).exists() or (HERE / 'results' / args.run).exists():
        parser.error('run ID already exists; no overwrite or retry')
    directory.mkdir(parents=True)
    argv = [str(PYTHON), '-B', str(HERE / 'run_demo.py'), '--run', args.run]
    report = {'schema': 'fast-live-total-command-v1', 'argv': argv,
        'launcher_argv': [sys.executable, '-B', str(Path(__file__)), '--run', args.run],
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'source_pins': {name: sha(HERE / name) for name in ('run.py', 'run_demo.py', 'live.py', 'gate.py', 'PIPELINES.json')},
        'timeout_seconds': 900}
    started = time.monotonic_ns()
    with (directory / 'stdout').open('xb') as out, (directory / 'stderr').open('xb') as err:
        process = subprocess.Popen(argv, stdout=out, stderr=err, start_new_session=True,
            cwd=REPO, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
        timed_out = False
        try:
            code = process.wait(timeout=900)
        except subprocess.TimeoutExpired:
            timed_out = True
            try: os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError: pass
            try: process.wait(timeout=5)
            except subprocess.TimeoutExpired: pass
            try: os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            code = process.wait(timeout=10)
    try:
        os.killpg(process.pid, 0)
        absent = False
    except ProcessLookupError:
        absent = True
    if not absent:
        try: os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError: pass
    report.update(exit_code=code, timed_out=timed_out, command_process_group_absent=absent,
        elapsed_ns=time.monotonic_ns() - started, finished_utc=datetime.now(timezone.utc).isoformat(),
        sources_unchanged=all(sha(HERE / p) == h for p, h in report['source_pins'].items()))
    result_path = HERE / 'results' / args.run / 'RESULT.json'
    if result_path.exists(): report['result_sha256'] = sha(result_path)
    (directory / 'command.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0 if code == 0 and absent and not timed_out and report['sources_unchanged'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
