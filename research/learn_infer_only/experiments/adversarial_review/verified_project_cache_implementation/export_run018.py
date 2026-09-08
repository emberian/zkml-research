#!/usr/bin/env python3
"""Explicit authorized post-success export; no Lean/build/model execution."""
import datetime
import importlib.util
import json
from pathlib import Path
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
INTEGRATION = HERE.parents[1] / 'integration'
spec = importlib.util.spec_from_file_location('verified_project_cache', INTEGRATION / 'verified_project_cache.py')
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


def main():
    started = time.monotonic()
    record = {'schema': 'authorized-run018-observed-export-command-v1',
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'argv': sys.orig_argv, 'helper_pin_before': cache.file_pin(INTEGRATION / 'verified_project_cache.py'),
              'policy_pin': cache.file_pin(HERE / 'compiler_policy.json'),
              'scope': 'New post-success observation, not historical external or ambient environment attestation. No Lean/build/model/crypto or overlay installation.'}
    try:
        record['result'] = cache.export_completed_run(
            run_dir=INTEGRATION / 'results/run_018', build_dir=INTEGRATION / 'build/run_018',
            metadata_dir=HERE / 'run018_observed_001',
            object_dir=INTEGRATION / 'build/verified_project_cache/run018_observed_001',
            compiler_policy=json.loads((HERE / 'compiler_policy.json').read_text()),
            expected_report_sha256='75c1d3921998fdf7fd5377af07be6887304ebe004369eab09c28effc75ec5b39',
            expected_harness_sha256='563b52272d913d00eb5751588befbbe7f7b226d83016d1c53f917dececff57ff')
        record['exit_code'] = 0
    except Exception:
        record.update(exit_code=1, traceback=traceback.format_exc())
    record['helper_pin_after'] = cache.file_pin(INTEGRATION / 'verified_project_cache.py')
    record['elapsed_seconds'] = time.monotonic() - started
    attempts = list(HERE.glob('export_attempt_*.json'))
    target = HERE / f'export_attempt_{len(attempts)+1:03}.json'
    with target.open('x') as stream:
        json.dump(record, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(record, indent=2, sort_keys=True))
    return record['exit_code']


if __name__ == '__main__':
    sys.exit(main())
