"""Owned command/pin helpers; no arithmetic or proof implementation."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def _terminate(signum, frame):
    raise SystemExit(128 + signum)


signal.signal(signal.SIGTERM, _terminate)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, obj):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2) + '\n')
    tmp.replace(path)


def check_pins(pins):
    for path, digest in pins.items():
        if sha(path) != digest:
            raise RuntimeError('frozen input changed: ' + path)


def command(run, label, argv, timeout, env):
    record = {'argv': [str(x) for x in argv], 'started_utc': now(),
              'cwd': str(ROOT), 'timeout_seconds': timeout}
    started = time.monotonic()
    with (run / (label + '.stdout')).open('xb') as out, (run / (label + '.stderr')).open('xb') as err:
        p = subprocess.Popen(record['argv'], cwd=ROOT, env=env,
                             stdout=out, stderr=err, start_new_session=True)
        record['pid'] = p.pid
        save(run / (label + '.command.json'), record)
        timed_out = False
        try:
            while True:
                pid, status, usage = os.wait4(p.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() - started > timeout:
                    timed_out = True
                    os.killpg(p.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(p.pid, 0)
                    break
                time.sleep(0.05)
        except BaseException as e:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                _, status, usage = os.wait4(p.pid, 0)
            except ChildProcessError:
                pass
            p.returncode = os.waitstatus_to_exitcode(status)
            record.update(returncode=p.returncode, interrupted=repr(e), finished_utc=now())
            save(run / (label + '.command.json'), record)
            raise
        p.returncode = os.waitstatus_to_exitcode(status)
    record.update(returncode=p.returncode, timed_out=timed_out,
                  finished_utc=now(), elapsed_seconds=time.monotonic() - started,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  max_rss_bytes=usage.ru_maxrss if sys.platform == 'darwin' else usage.ru_maxrss * 1024)
    save(run / (label + '.command.json'), record)
    if p.returncode or timed_out:
        raise RuntimeError('step failed; no retry: ' + label)
    return record
