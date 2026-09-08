#!/usr/bin/env python3
"""Bounded kernel reduction probe of the existing computed CSE descriptors.

This never substitutes a compiled Boolean answer for a Lean proof. The cap applies
only to the fresh Lean process spawned here, not to any co-running job.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
config = json.loads((HERE/'results/environment.json').read_text())
operation = sys.argv[1]
assert operation in ('infer', 'learn', 'baseline')
profile = sys.argv[2] if len(sys.argv) > 2 else '1g'
assert profile in ('1g', '3g')
assert operation != 'baseline' or profile == '1g'
seconds_cap = 120 if operation == 'learn' or profile == '3g' else 45
rss_cap_kib = (3 if profile == '3g' else 1) * 1024 * 1024
suffix = '_3g' if profile == '3g' else ''
stem = HERE / 'results' / f'kernel_{operation}{suffix}'
source = stem.with_suffix('.lean')
assert not source.exists(), 'Retain each prior probe; choose a new named probe for retries.'
header = '''import Compiler.EmittedScheduleExecution
open Minidregg.Compiler.PrivateAddressEmaSchedule
open Minidregg.Compiler.EmittedScheduleExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
'''
body = '' if operation == 'baseline' else f'''theorem {operation}_valid_kernel : validCheck {operation}Schedule = true := by
  decide +kernel
#print axioms {operation}_valid_kernel
'''
source.write_text(header + body)
cmd = [config['lean'], str(source)]
started = time.monotonic()
samples = []
reason = None
with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
    p = subprocess.Popen(cmd, cwd=HERE, env=dict(os.environ, LEAN_PATH=config['lean_path']), stdout=out, stderr=err)
    while p.poll() is None:
        elapsed = time.monotonic() - started
        rss_text = subprocess.run(['ps', '-o', 'rss=', '-p', str(p.pid)], text=True, capture_output=True).stdout.strip()
        rss = int(rss_text) if rss_text else 0
        samples.append({'seconds': elapsed, 'rss_kib': rss})
        if elapsed >= seconds_cap or rss > rss_cap_kib:
            reason = 'time_cap' if elapsed >= seconds_cap else 'rss_cap'
            p.terminate()
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait()
            break
        time.sleep(1)
record = dict(command=cmd, cwd=str(HERE), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    exit_code=p.returncode, seconds=time.monotonic()-started, stopped_by=reason,
    seconds_cap=seconds_cap, rss_cap_kib=rss_cap_kib, max_sampled_rss_kib=max(s['rss_kib'] for s in samples),
    samples=samples, stdout=stem.with_suffix('.stdout').read_text(), stderr=stem.with_suffix('.stderr').read_text())
stem.with_suffix('.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='samples'}, indent=2))
