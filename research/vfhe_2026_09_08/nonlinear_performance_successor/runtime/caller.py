#!/usr/bin/env python3
"""Caller-selected whole-operation proof worker. Run in its own subprocess.

caller.py produce-update SOURCE NEW_OUTPUT
caller.py verify-update EXPECTED_JSON PRODUCED NEW_OUTPUT
caller.py produce-infer MODEL QUERY EVALUATION_KEY CAPTURE NEW_OUTPUT
caller.py verify-infer EXPECTED_JSON PRODUCED NEW_OUTPUT
caller.py config

Every operation writes NEW_OUTPUT/result.json. No saved workload is selected.
Optional leading --profile PATH selects another approved PIPELINE.json.
"""
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent.parent / 'nonlinear_performance/runtime'
sys.path.insert(0, str(PRIOR))
import pipeline
import consumer
from common import check_pins


def configure(profile_path):
    profile_path = Path(profile_path).resolve()
    if profile_path.name != 'PIPELINE.json':
        raise RuntimeError('Profile filename must be PIPELINE.json')

    def config():
        if not __debug__:
            raise RuntimeError('Assertions must remain enabled')
        c = pipeline.read(profile_path)
        assert c['schema'] == 'caller-selected-profiled-kernel-v1'
        check_pins(c['pins'])
        return c

    pipeline.ROOT = profile_path.parent
    pipeline.config = config
    pipeline.check_record = consumer.check_record
    return config


def main():
    args = sys.argv[1:]
    if not args or args == ['--help'] or args == ['-h']:
        print(__doc__)
        return
    profile = HERE / 'caller/PIPELINE.json'
    if args[0] == '--profile':
        if len(args) < 3:
            raise SystemExit(__doc__)
        profile = Path(args[1])
        args = args[2:]
    config = configure(profile)
    action, *args = args
    if action == 'config' and not args:
        print(json.dumps(config(), indent=2))
        return
    if action == 'produce-update' and len(args) == 2:
        result = pipeline.produce_update(*args)
    elif action == 'verify-update' and len(args) == 3:
        result = pipeline.verify_update(pipeline.read(args[0]), *args[1:])
    elif action == 'produce-infer' and len(args) == 5:
        result = pipeline.produce_infer(*args)
    elif action == 'verify-infer' and len(args) == 3:
        result = pipeline.verify_infer(pipeline.read(args[0]), *args[1:])
    else:
        raise SystemExit(__doc__)
    print(json.dumps({'action': action, 'result': str(Path(args[-1]).resolve() / 'result.json'),
                      **{key: result[key] for key in ('verified', 'complete_infer_verified',
                         'proofs_generated', 'fresh_proofs', 'proofs_verified') if key in result}}))


if __name__ == '__main__':
    main()
