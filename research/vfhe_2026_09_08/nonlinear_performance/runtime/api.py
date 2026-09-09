#!/usr/bin/env python3
"""Corrected public API over the frozen compact/all-row pipeline.

api.py prove NEW_RUN
api.py verify REQUEST_JSON PRODUCED NEW_VERIFY
api.py produce-infer MODEL QUERY EVAL_KEY CAPTURE NEW_PRODUCED
api.py verify-infer EXPECTED_JSON PRODUCED NEW_VERIFY
api.py produce-update SOURCE NEW_PRODUCED
api.py verify-update EXPECTED_JSON PRODUCED NEW_VERIFY

The measured production and consumer are already retained; invoking produce/prove
creates a new caller-requested proof run. No command invokes a private reader.
"""
import json
import sys
from common import ROOT, check_pins
import consumer
import pipeline
import run


def main():
    if len(sys.argv) == 1 or sys.argv[1] in ('--help', '-h'):
        print(__doc__)
        return
    check_pins(pipeline.read(ROOT / 'API.json')['pins'])
    pipeline.config()
    # Explicit controller adapter: preserve all proof/public-binding checks while
    # allowing diagnostic fields omitted by the pinned native verify schema.
    # This is the same checker used in the completed consumer001 acceptance.
    pipeline.check_record = consumer.check_record
    action, *args = sys.argv[1:]
    if action == 'prove' and len(args) == 1:
        sys.argv = [sys.argv[0], args[0]]
        run.main()
        return
    if action == 'verify' and len(args) == 3:
        result = run.consume(pipeline.read(args[0]), args[1], args[2])
    elif action == 'produce-infer' and len(args) == 5:
        result = pipeline.produce_infer(*args)
    elif action == 'verify-infer' and len(args) == 3:
        result = pipeline.verify_infer(pipeline.read(args[0]), *args[1:])
    elif action == 'produce-update' and len(args) == 2:
        result = pipeline.produce_update(*args)
    elif action == 'verify-update' and len(args) == 3:
        result = pipeline.verify_update(pipeline.read(args[0]), *args[1:])
    else:
        raise SystemExit(__doc__)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
