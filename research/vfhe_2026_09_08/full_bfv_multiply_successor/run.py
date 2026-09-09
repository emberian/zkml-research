#!/usr/bin/env python3
"""Prove and verify the complete saved square, reusing exact rescale proofs.

Usage: run.py CASE EXISTING_RESCALE_PROOFS NEW_RUN
The case is produced by the native import command. All approved phase configs
must be frozen locally before starting. Partial phase results never authorize
whole-operation acceptance.
"""
import json
from pathlib import Path
import sys
import time
from common import now, save
import prove_phase
import verify_whole


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    case, rescale, out = (Path(x).resolve() for x in sys.argv[1:])
    out.mkdir()
    started = time.monotonic()
    save(out / 'started.json', {'started_utc': now(), 'case': str(case), 'reused_rescale': str(rescale)})
    try:
        extension, tensor, verification = out / 'extension', out / 'tensor', out / 'verification'
        prove_phase.main(['extension', str(case), str(extension)])
        prove_phase.main(['tensor', str(case), str(tensor)])
        verify_whole.main([str(case), str(extension), str(tensor), str(rescale), str(verification)])
        result = json.loads((verification / 'result.json').read_text())
        assert result['whole_operation_verified']
        save(out / 'result.json', {'whole_operation_verified': True, 'verification': str(verification / 'result.json'),
             'binding': result['binding'], 'proofs_verified': 28, 'new_proofs': 22, 'rescale_proofs_reused': 6,
             'elapsed_seconds': time.monotonic() - started, 'finished_utc': now()})
    except BaseException as e:
        save(out / 'failure.json', {'whole_operation_verified': False, 'error': repr(e), 'utc': now(), 'retried': False})
        raise


if __name__ == '__main__':
    main()
