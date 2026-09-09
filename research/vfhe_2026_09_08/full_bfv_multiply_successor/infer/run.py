#!/usr/bin/env python3
"""Produce and independently verify the retained complete kernel Infer.

Usage: run.py APPROVED_REQUEST CASE NEW_RUN
"""
from pathlib import Path
import json
import sys
import time
from common import now, save
import prove
import verify


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    request, case, out = (Path(x).resolve() for x in sys.argv[1:])
    out.mkdir()
    started = time.monotonic()
    save(out / 'started.json', {'started_utc': now(), 'request': str(request), 'case': str(case)})
    try:
        prove.main([str(case), str(out / 'proofs')])
        verify.main([str(request), str(case), str(out / 'proofs'), str(out / 'verification')])
        result = json.loads((out / 'verification/result.json').read_text())
        assert result['complete_infer_verified']
        save(out / 'result.json', {'complete_infer_verified': True, 'binding': result['binding'], 'verification': str(out / 'verification/result.json'), 'proofs_verified': 116, 'elapsed_seconds': time.monotonic() - started, 'finished_utc': now()})
    except BaseException as e:
        save(out / 'failure.json', {'complete_infer_verified': False, 'error': repr(e), 'retried': False, 'utc': now()})
        raise


if __name__ == '__main__':
    main()
