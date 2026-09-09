#!/usr/bin/env python3
"""One entry point for the continuing learner research application."""
import argparse
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = next(p for p in HERE.parents if (p / 'AGENTS.md').is_file())
PYTHON = REPO / 'research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['serve', 'prepare', 'evaluate', 'resume', 'check', 'build'])
    args, rest = parser.parse_known_args()
    if not PYTHON.is_file():
        raise SystemExit('The retained encoder environment is missing: ' + str(PYTHON))
    if args.action == 'serve':
        target, argv = 'server.py', rest
    elif args.action in ('prepare', 'evaluate', 'resume'):
        target = 'workload.py'
        argv = [{'prepare': '--prepare', 'evaluate': '--run', 'resume': '--resume'}[args.action], *rest]
    else:
        target, argv = 'bootstrap.py', ['--' + args.action, *rest]
    os.environ.setdefault('RAYON_NUM_THREADS', '4')
    os.environ.setdefault('PYTHONDONTWRITEBYTECODE', '1')
    os.execv(str(PYTHON), [str(PYTHON), '-B', str(HERE / target), *argv])


if __name__ == '__main__':
    main()
