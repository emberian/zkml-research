"""Pinned subprocess boundary for the continuing learner's real proof backend.

Frozen drivers execute in their own Python process. Their `common`, `pipeline`,
and signal-handler globals never enter the HTTP server or another caller.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
WORKER = RESEARCH / 'nonlinear_performance_successor/runtime/caller.py'
PROFILE = WORKER.parent / 'caller/PIPELINE.json'
HELPER = RESEARCH / 'proved_journal/live_nonlinear/fixture_builder/helper.py'
ENV = dict(os.environ, RAYON_NUM_THREADS='4', PYTHONDONTWRITEBYTECODE='1')


def install_signal_handlers():
    import threading
    if threading.current_thread() is threading.main_thread():
        def interrupted(signum, frame):
            raise SystemExit(128 + signum)
        signal.signal(signal.SIGTERM, interrupted)


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp = tempfile.mkstemp(prefix='.backend-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(value, f, sort_keys=True, allow_nan=False)
            f.write('\n'); f.flush(); os.fsync(f.fileno())
        os.replace(temp, path)
        fd = os.open(path.parent, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
    finally:
        if os.path.exists(temp): os.unlink(temp)


def read(path):
    return json.loads(Path(path).read_text())


def helper():
    spec = importlib.util.spec_from_file_location('continuing_system_frozen_issuer', HELPER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def process_alive(record):
    """Check a concrete retained process handle, including PID reuse when pinned."""
    if not record.get('pid') or record.get('returncode') is not None:
        return False
    p = subprocess.run(['/bin/ps', '-p', str(record['pid']), '-o', 'lstart=,stat=,command='],
                       text=True, capture_output=True)
    if p.returncode or not p.stdout.strip():
        return False
    fields = p.stdout.strip().split(None, 6)
    if len(fields) < 7 or fields[5].startswith('Z'):
        return False
    stamp = ' '.join(fields[:5])
    if record.get('process_start') and record['process_start'] != stamp:
        return False
    argv = record.get('argv', [])
    return bool(argv and str(argv[0]) in fields[6])


def live_processes(directory):
    live = []
    for path in Path(directory).rglob('*.command.json'):
        try:
            record = read(path)
            if process_alive(record):
                live.append({'record': str(path), 'pid': record['pid'], 'argv': record['argv']})
        except (ValueError, OSError, KeyError):
            continue
    return live


def run(directory, label, argv, timeout=14400):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=True)
    record_path = directory / (label + '.command.json')
    record = {'argv': [str(x) for x in argv], 'cwd': str(HERE),
              'started_utc': now(), 'timeout_seconds': timeout}
    start = time.monotonic()
    with (directory / (label + '.stdout')).open('xb') as out, (directory / (label + '.stderr')).open('xb') as err:
        child = subprocess.Popen(record['argv'], cwd=HERE, env=ENV, stdout=out, stderr=err,
                                 start_new_session=True)
        record['pid'] = child.pid
        stamp = subprocess.run(['/bin/ps', '-p', str(child.pid), '-o', 'lstart='], text=True, capture_output=True)
        record['process_start'] = ' '.join(stamp.stdout.split())
        save(record_path, record)
        try:
            code = child.wait(timeout=timeout)
        except BaseException as exc:
            try: os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError: pass
            try: child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL); child.wait()
            record.update(returncode=child.returncode, error=repr(exc), finished_utc=now(),
                          elapsed_seconds=time.monotonic() - start)
            save(record_path, record)
            raise
    record.update(returncode=code, elapsed_seconds=time.monotonic() - start, finished_utc=now())
    save(record_path, record)
    if code:
        raise RuntimeError(f'backend phase {label} failed (exit {code}); see {directory / (label + ".stderr")}')
    return record


class Backend:
    def __init__(self, descriptor=None):
        if descriptor is None:
            profile = Path(os.environ.get('CONTINUING_SYSTEM_PROFILE', PROFILE)).resolve()
            worker = Path(os.environ.get('CONTINUING_SYSTEM_WORKER', WORKER)).resolve()
            descriptor = {'worker': str(worker), 'worker_sha256': sha(worker),
                          'profile': str(profile), 'profile_sha256': sha(profile),
                          'issuer_helper': str(HELPER), 'issuer_helper_sha256': sha(HELPER)}
        self.descriptor = dict(descriptor)
        self.check()

    def check(self):
        d = self.descriptor
        for key in ('worker', 'profile', 'issuer_helper'):
            if sha(d[key]) != d[key + '_sha256']:
                raise RuntimeError('approved backend changed: ' + key)
        config = read(d['profile'])
        if config['schema'] != 'caller-selected-profiled-kernel-v1':
            raise RuntimeError('unsupported continuing backend profile')
        for path, expected in config['pins'].items():
            if sha(path) != expected:
                raise RuntimeError('approved backend dependency changed: ' + path)
        self.config = config
        return config

    @property
    def profile_sha256(self):
        return self.descriptor['profile_sha256']

    def native(self, operation, directory, **kwargs):
        h = helper()
        run(directory, operation, h.native_argv(operation, **kwargs), 300)
        return read(Path(directory) / (operation + '.stdout'))

    def capture(self, issuer, model, query, out, revision, label, directory):
        run(directory, 'capture', [sys.executable, HELPER, 'capture', '--issuer', issuer,
            '--model-ct', model, '--query', query, '--out', out, '--revision', revision, '--label', label], 300)
        return read(Path(out) / 'capture.json')

    def call(self, action, arguments, out, directory):
        self.check()
        d = self.descriptor
        run(directory, action, [sys.executable, d['worker'], '--profile', d['profile'],
                                action, *arguments, out])
        return read(Path(out) / 'result.json')

    def produce_update(self, source, out, directory):
        return self.call('produce-update', [source], out, directory)

    def verify_update(self, expected, produced, out, directory):
        path = Path(directory) / 'expected.json'; save(path, expected)
        return self.call('verify-update', [path, produced], out, directory)

    def produce_infer(self, model, query, key, capture, out, directory):
        return self.call('produce-infer', [model, query, key, capture], out, directory)

    def verify_infer(self, expected, produced, out, directory):
        path = Path(directory) / 'expected.json'; save(path, expected)
        return self.call('verify-infer', [path, produced], out, directory)
