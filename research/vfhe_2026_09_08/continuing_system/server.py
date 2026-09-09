#!/usr/bin/env python3
"""Local continuing learner application. Jobs and model state survive restarts.

Run with the existing encoder environment:
  python server.py --state runtime/local --port 8765

The native prover runs in the background; HTTP requests never wait for a proof.
This research service retains a full reader. It provides no remote authentication.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
import os
from pathlib import Path
import re
import signal
import sqlite3
import subprocess
import sys
import threading
import time
import traceback
from urllib.parse import unquote, urlparse

HERE = Path(__file__).resolve().parent
TERMINAL = {'completed', 'failed', 'interrupted'}


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def progress_description(directory, progress, raw):
    relative = str(progress.parent.relative_to(directory))
    phase = raw.get('phase', '')
    if progress.parent == directory:
        match = re.fullmatch(r'(class|bank)(\d+)-(prove|verify|capture|read)', phase)
        if match:
            action = {'prove': 'Proving the encrypted computation',
                      'verify': 'Independently verifying the complete proof batch',
                      'capture': 'Computing the encrypted answer',
                      'read': 'Reading the verified answer'}[match[3]]
            return f'{match[1].capitalize()} {int(match[2]) + 1}: {action}'
        return {'issue': 'Encrypting the new teaching example',
                'learn': 'Updating encrypted memory', 'prove': 'Proving the model update',
                'verify': 'Verifying the model update', 'complete': 'Complete'}.get(phase, phase.replace('_', ' ').capitalize())
    match = re.search(r'class(\d+)', relative)
    prefix = f'Class {int(match[1]) + 1}: ' if match else ''
    kind = raw.get('kind') or progress.parent.name
    part = {'infer': 'encrypted dot product', 'extension': 'basis extension',
            'tensor': 'ciphertext square', 'rescale': 'rescaling',
            'update': 'model update'}.get(kind, 'computation')
    action = {'emit': 'Building witness for', 'prove': 'Proving',
              'complete': 'Finished'}.get(phase, 'Verifying')
    detail = f" · chunk {raw['index'] + 1}" if isinstance(raw.get('index'), int) else ''
    return prefix + action + ' ' + part + detail


class Jobs:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True, mode=0o700)
        self.model = self.root / 'resident'
        self.database = self.root / 'jobs.sqlite'
        self.wake = threading.Event()
        self.stop = threading.Event()
        with self.db() as db:
            db.execute('PRAGMA journal_mode=WAL')
            db.execute('''CREATE TABLE IF NOT EXISTS jobs (
                id TEXT PRIMARY KEY, kind TEXT NOT NULL, payload TEXT NOT NULL,
                payload_sha256 TEXT NOT NULL, status TEXT NOT NULL,
                phase TEXT NOT NULL, result TEXT, error TEXT,
                created_utc TEXT NOT NULL, updated_utc TEXT NOT NULL,
                attempts INTEGER NOT NULL DEFAULT 0)''')
            db.execute("UPDATE jobs SET status='interrupted', phase='Interrupted by service restart; resume to continue', updated_utc=? WHERE status='running'", (now(),))

    @contextlib.contextmanager
    def db(self):
        db = sqlite3.connect(self.database, timeout=30)
        db.row_factory = sqlite3.Row
        try:
            yield db
            db.commit()
        except BaseException:
            db.rollback()
            raise
        finally:
            db.close()

    @staticmethod
    def public(row):
        result = dict(row)
        result.pop('payload', None)
        result.pop('payload_sha256', None)
        for key in ('result',):
            if result[key] is not None:
                result[key] = json.loads(result[key])
        return result

    def get(self, identifier):
        with self.db() as db:
            row = db.execute('SELECT * FROM jobs WHERE id=?', (identifier,)).fetchone()
        if row is None:
            raise KeyError(identifier)
        return self.public(row)

    def list(self):
        with self.db() as db:
            return [self.public(r) for r in db.execute('SELECT * FROM jobs ORDER BY created_utc DESC, rowid DESC LIMIT 100')]

    def submit(self, kind, payload):
        if self.evaluation().get('running'):
            raise ValueError('The fixed lifecycle evaluation is using this learner. Teaching and queries reopen when it finishes.')
        if kind == 'init':
            labels = payload.get('classes')
            if (not isinstance(labels, list) or not 1 <= len(labels) <= 1024
                    or not all(isinstance(c, str) and c.strip() and len(c) <= 256 for c in labels)
                    or len(set(labels)) != len(labels)):
                raise ValueError('Provide distinct nonempty class labels (at most 1024).')
            body = {'classes': labels}
            score = payload.get('score', 'squared')
            proof_backend = payload.get('proof_backend', 'compact')
            layout = payload.get('layout', 'examples')
            if (score, proof_backend) not in (('squared', 'compact'), ('linear', 'compact'), ('linear', 'matched')):
                raise ValueError('Choose squared/compact, linear/compact, or linear/matched.')
            if layout not in ('examples', 'classes') or (layout == 'classes' and (score, proof_backend) != ('linear', 'matched')):
                raise ValueError('Packed classes require linear scoring with matched proofs.')
            # Preserve existing initialization request identities for the default.
            if (score, proof_backend) != ('squared', 'compact'):
                body.update(score=score, proof_backend=proof_backend)
            if layout == 'classes':
                body['layout'] = layout
            identifier = 'init'
        else:
            request_id = payload.get('request_id')
            text = payload.get('text')
            if not isinstance(request_id, str) or not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', request_id):
                raise ValueError('request_id must contain 1–80 letters, digits, underscores or hyphens.')
            if not isinstance(text, str) or not text.strip() or len(text) > 16384:
                raise ValueError('Supply nonempty text of at most 16384 characters.')
            body = {'request_id': request_id, 'text': text}
            if kind == 'teach':
                label = payload.get('label')
                if not isinstance(label, str) or not label.strip() or len(label) > 256:
                    raise ValueError('Supply the teaching class label.')
                body['label'] = label
            identifier = kind + '-' + request_id
        encoded = canonical(body)
        digest = hashlib.sha256(encoded.encode()).hexdigest()
        with self.db() as db:
            db.execute('BEGIN IMMEDIATE')
            previous = db.execute('SELECT * FROM jobs WHERE id=?', (identifier,)).fetchone()
            if previous is not None:
                if previous['payload_sha256'] != digest:
                    raise ValueError('This request ID already belongs to different input; choose a new ID.')
                return self.public(previous)
            if kind != 'init' and not (self.model / 'journal/genesis.json').exists():
                raise ValueError('Initialize the learner before teaching or querying.')
            if kind == 'init' and self.model.exists():
                raise ValueError('A resident already exists in this state directory.')
            stamp = now()
            db.execute('INSERT INTO jobs(id,kind,payload,payload_sha256,status,phase,created_utc,updated_utc) VALUES(?,?,?,?,?,?,?,?)',
                       (identifier, kind, encoded, digest, 'queued', 'Waiting for the prover', stamp, stamp))
        self.wake.set()
        return self.get(identifier)

    def retry(self, identifier):
        if self.evaluation().get('running'):
            raise ValueError('The fixed lifecycle evaluation is using this learner; resume jobs after it finishes.')
        with self.db() as db:
            db.execute('BEGIN IMMEDIATE')
            row = db.execute('SELECT * FROM jobs WHERE id=?', (identifier,)).fetchone()
            if row is None:
                raise KeyError(identifier)
            if row['status'] not in {'failed', 'interrupted'}:
                raise ValueError('Only failed or interrupted jobs can be resumed.')
            db.execute("UPDATE jobs SET status='queued', phase='Queued to resume', error=NULL, updated_utc=? WHERE id=?", (now(), identifier))
        self.wake.set()
        return self.get(identifier)

    def phase(self, identifier, value):
        with self.db() as db:
            db.execute("UPDATE jobs SET phase=?, updated_utc=? WHERE id=? AND status='running' AND phase<>?", (value, now(), identifier, value))

    def state(self):
        result = {'initialized': False, 'jobs': self.list(), 'fifo_capacity': 8,
                  'scope': 'Local research learner; whole-row arithmetic proofs; full reader retained.'}
        database = self.model / 'journal/state.sqlite'
        # Frozen journal helpers use journal.sqlite3 in some generations. Select
        # an existing database by its head table, without creating another file.
        candidates = ([database] if database.exists() else []) + sorted((self.model / 'journal').glob('*.sqlite*'))
        for path in dict.fromkeys(candidates):
            if path.name.endswith(('-wal', '-shm')):
                continue
            try:
                with sqlite3.connect(path.as_uri() + '?mode=ro', uri=True, timeout=1) as db:
                    row = db.execute('SELECT state FROM head WHERE singleton=1').fetchone()
                if row:
                    result.update(initialized=True, head=json.loads(row[0]))
                    break
            except sqlite3.Error:
                continue
        answers = sorted((self.model / 'queries').glob('*/answer.json'),
                         key=lambda p: p.stat().st_mtime_ns, reverse=True)[:10]
        result['recent_answers'] = []
        for path in answers:
            try:
                result['recent_answers'].append({'request_id': path.parent.name,
                                                 'result': json.loads(path.read_text())})
            except (OSError, ValueError):
                continue
        result['evaluation'] = self.evaluation()
        genesis_path = self.model / 'journal/genesis.json'
        if result['initialized'] and (HERE / 'engines.py').exists():
            import engines
            genesis = json.loads(genesis_path.read_text())
            packed = genesis['schema'] == 'packed-class-centroid-genesis-v1'
            descriptor = genesis['backend']['proof_engine'] if packed else genesis.get('engine')
            result['engine'] = engines.metadata(descriptor)
            if packed:
                info = result['engine']
                info.update(layout='classes', classes_per_bank=genesis['policy']['classes_per_bank'],
                            bank_count=len(genesis['initial_banks']), score_formula='class_sum / count',
                            infer_proofs_per_bank=info.pop('infer_proofs_per_class'))
                info.pop('lane_values_key', None)
        return result

    def evaluation(self):
        controller = self.model.with_name(self.model.name + '.workload')
        lock_path = controller / 'driver.lock'
        if not lock_path.exists():
            return {'running': False}
        import fcntl
        with lock_path.open('r') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                running = False
                fcntl.flock(lock, fcntl.LOCK_UN)
            except BlockingIOError:
                running = True
        genesis_path = self.model / 'journal/genesis.json'
        packed = genesis_path.exists() and json.loads(genesis_path.read_text())['schema'] == 'packed-class-centroid-genesis-v1'
        corpus = HERE / 'packed/workload/corpus.json' if packed else HERE / 'workload.json'
        operations = json.loads(corpus.read_text())['operations']
        done = [op for op in operations if (controller / 'steps' / op['id'] / 'completed.json').is_file()]
        current = next((op for op in operations if op not in done), None)
        value = {'running': running, 'completed_operations': len(done),
                 'total_operations': len(operations), 'current_step': current['id'] if current else None,
                 'phase': 'Complete' if current is None else 'Starting the next operation'}
        if current:
            kind = 'teaching' if current['kind'] == 'teach' else 'queries'
            directory = self.model / kind / current['id']
            progress = max(directory.rglob('progress.json'), key=lambda p: p.stat().st_mtime_ns, default=None)
            if progress:
                try:
                    raw = json.loads(progress.read_text())
                    value['phase'] = progress_description(directory, progress, raw)
                except (OSError, ValueError):
                    pass
        if (controller / 'RESULT.json').exists():
            value['summary'] = json.loads((controller / 'RESULT.json').read_text())
        return value

    def worker(self, core):
        live = None
        while not self.stop.is_set():
            with self.db() as db:
                db.execute('BEGIN IMMEDIATE')
                row = db.execute("SELECT * FROM jobs WHERE status='queued' ORDER BY created_utc,rowid LIMIT 1").fetchone()
                if row:
                    db.execute("UPDATE jobs SET status='running',phase='Starting',attempts=attempts+1,updated_utc=? WHERE id=?", (now(), row['id']))
            if row is None:
                self.wake.wait(0.5)
                self.wake.clear()
                continue
            payload = json.loads(row['payload'])
            monitor_stop = threading.Event()
            monitor = threading.Thread(target=self.monitor, args=(row, payload, monitor_stop), daemon=True)
            monitor.start()
            try:
                selected_core = core
                genesis_path = self.model / 'journal/genesis.json'
                packed = payload.get('layout') == 'classes'
                if genesis_path.exists():
                    packed = json.loads(genesis_path.read_text())['schema'] == 'packed-class-centroid-genesis-v1'
                if packed:
                    from packed import core as selected_core
                if row['kind'] == 'init':
                    self.phase(row['id'], 'Creating encryption keys and the initial journal')
                    selection = {key: payload[key] for key in ('score', 'proof_backend') if key in payload}
                    result = selected_core.initialize(self.model, payload['classes'], **({} if packed else selection))
                    live = selected_core.Live(self.model)
                else:
                    if live is None:
                        live = selected_core.Live(self.model)
                    self.phase(row['id'], 'Encoding supplied text and preparing encrypted computation')
                    if row['kind'] == 'teach':
                        result = live.teach(payload['label'], payload['text'], payload['request_id'])
                    else:
                        result = live.query(payload['text'], payload['request_id'])
                with self.db() as db:
                    db.execute("UPDATE jobs SET status='completed',phase='Complete',result=?,error=NULL,updated_utc=? WHERE id=?", (canonical(result), now(), row['id']))
            except BaseException as error:
                live = None
                detail = ''.join(traceback.format_exception(error))
                (self.root / (row['id'] + '.error.log')).write_text(detail)
                with self.db() as db:
                    db.execute("UPDATE jobs SET status='failed',phase='Stopped; no partial result accepted',error=?,updated_utc=? WHERE id=?", (str(error), now(), row['id']))
                if isinstance(error, (SystemExit, KeyboardInterrupt)):
                    raise
            finally:
                monitor_stop.set()
                monitor.join(timeout=3)

    def monitor(self, row, payload, stop):
        if row['kind'] == 'init':
            return
        request = self.model / ('teaching' if row['kind'] == 'teach' else 'queries') / payload['request_id']
        newest = 0
        while not stop.wait(2):
            try:
                progress = max(request.rglob('progress.json'), key=lambda p: p.stat().st_mtime_ns, default=None)
                if progress is None or progress.stat().st_mtime_ns <= newest:
                    continue
                raw = json.loads(progress.read_text())
                newest = progress.stat().st_mtime_ns
                self.phase(row['id'], progress_description(request, progress, raw))
            except (OSError, ValueError):
                continue


class Handler(BaseHTTPRequestHandler):
    server_version = 'ContinuingLearner/1'

    def local_host(self):
        return self.headers.get('Host') in {
            f'127.0.0.1:{self.server.server_port}',
            f'localhost:{self.server.server_port}',
        }

    def reply(self, status, value):
        body = (json.dumps(value, ensure_ascii=False) + '\n').encode()
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if not self.local_host():
            return self.reply(403, {'error': 'Use the local application address.'})
        path = urlparse(self.path).path
        try:
            if path == '/api/state':
                state = self.server.jobs.state()
                state['worker_running'] = self.server.worker.poll() is None
                if not state['worker_running']:
                    state['service_error'] = 'The worker stopped. Restart the local service; retained jobs and model state will reopen.'
                return self.reply(200, state)
            if path.startswith('/api/jobs/'):
                return self.reply(200, self.server.jobs.get(unquote(path.removeprefix('/api/jobs/'))))
            relative = unquote(path).lstrip('/') or 'index.html'
            target = (HERE / 'web' / relative).resolve()
            if not target.is_relative_to(HERE / 'web') or not target.is_file():
                return self.reply(404, {'error': 'Not found'})
            body = target.read_bytes()
            self.send_response(200)
            self.send_header('Content-Type', mimetypes.guess_type(target)[0] or 'application/octet-stream')
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Cache-Control', 'no-cache')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.end_headers()
            self.wfile.write(body)
        except KeyError:
            self.reply(404, {'error': 'Unknown job'})
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_POST(self):
        if not self.local_host():
            return self.reply(403, {'error': 'Use the local application address.'})
        if self.server.worker.poll() is not None:
            return self.reply(503, {'error': 'The worker stopped; restart the local service.'})
        origin = self.headers.get('Origin')
        if origin and origin != 'http://' + self.headers.get('Host', ''):
            return self.reply(403, {'error': 'Use the local application origin.'})
        if self.headers.get('Content-Type', '').split(';')[0].strip() != 'application/json':
            return self.reply(415, {'error': 'Send application/json.'})
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if not 0 < size <= 262144:
                return self.reply(413, {'error': 'Request body is empty or too large.'})
            value = json.loads(self.rfile.read(size))
            if not isinstance(value, dict):
                raise ValueError('Expected a JSON object.')
            path = urlparse(self.path).path
            if path in ('/api/init', '/api/teach', '/api/query'):
                result = self.server.jobs.submit(path.rsplit('/', 1)[1], value)
            elif path.startswith('/api/jobs/') and path.endswith('/retry'):
                result = self.server.jobs.retry(unquote(path[len('/api/jobs/'):-len('/retry')]))
            else:
                return self.reply(404, {'error': 'Not found'})
            self.reply(202, result)
        except KeyError:
            self.reply(404, {'error': 'Unknown job'})
        except (ValueError, TypeError) as error:
            self.reply(400, {'error': str(error)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', type=Path, default=HERE / 'runtime/local')
    parser.add_argument('--port', type=int, default=8765)
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    # Import native wrappers on the main thread: some frozen helpers register
    # signal handlers at import time. Encoder/model initialization remains lazy.
    if args.worker:
        import core
        import backend
        backend.install_signal_handlers()
        Jobs(args.state).worker(core)
        return
    # One service process owns a state directory, including startup recovery.
    import fcntl
    root = args.state.resolve()
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    lock = (root / 'service.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit('A service already owns this state directory.')
    jobs = Jobs(root)
    server = ThreadingHTTPServer(('127.0.0.1', args.port), Handler)
    server.jobs = jobs
    worker_log = (root / 'worker.log').open('ab', buffering=0)
    worker = subprocess.Popen([sys.executable, '-B', str(Path(__file__).resolve()),
                               '--state', str(root), '--worker'],
                              stdout=worker_log, stderr=worker_log, start_new_session=True)
    server.worker = worker
    def stop_service(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop_service)
    print(json.dumps({'url': f'http://127.0.0.1:{server.server_port}', 'state': str(jobs.root), 'pid': os.getpid()}), flush=True)
    try:
        server.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        pass
    finally:
        jobs.stop.set()
        jobs.wake.set()
        server.server_close()
        if worker.poll() is None:
            worker.terminate()
            try:
                worker.wait(timeout=15)
            except subprocess.TimeoutExpired:
                worker.kill()
                worker.wait()
        worker_log.close()
        lock.close()


if __name__ == '__main__':
    main()
