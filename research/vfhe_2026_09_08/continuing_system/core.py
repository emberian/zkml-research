"""Durable continuing BFV learner over the corrected, caller-selected proof backend.

The full local reader, encoding, key validity, journal policy, SQLite and native
implementation remain explicit TCB. Only whole completed proof phases can advance
an accepted model or permit the local private receive phase.
"""
from __future__ import annotations
import argparse
import contextlib
from fractions import Fraction
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import threading
import time

HERE = Path(__file__).resolve().parent

def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

backend = _load('continuing_system_backend', HERE / 'backend.py')
j = _load('continuing_system_journal_primitives', HERE.parent / 'proved_journal/multiclass_successor/service.py')
Refused = j.Refused
CAPACITY = 8
POLICY = {
    'schema': 'continuing-proof-learner-policy-v1', 'capacity': CAPACITY,
    'update': 'out=acc+fresh-old; fixed cyclic SIMD lane, FIFO expiry after eight examples per class',
    'query': 'All active classes require complete fresh corrected kernel proofs before private receive',
    'features': {'dimension': 576, 'coordinate_bound': 32, 'squared_norm_bound': 20000},
    'reader': 'Surviving full BFV reader; this local acceptance sequence is not cryptographic decryption restriction',
    'scope': 'Public encoder, setup/key validity, FIFO/request/recipient policy, parser/NTT/controller and proof backend TCB',
}


def state_root(classes):
    return j.digest({'schema': 'continuing-class-map-v1', 'classes': classes})


def _request_id(value):
    j.need(isinstance(value, str) and re.fullmatch(r'[A-Za-z0-9_-]{1,80}', value), 'request_id')
    return value


def _vector(value):
    if hasattr(value, 'tolist'): value = value.tolist()
    j.need(isinstance(value, (list, tuple)) and len(value) == 576, 'feature_dimension')
    value = list(value)
    j.need(all(type(x) is int and -32 <= x <= 32 for x in value), 'feature_integer_domain')
    j.need(sum(x*x for x in value) <= 20000, 'feature_norm_domain')
    return value


def _schema(db):
    db.execute('CREATE TABLE IF NOT EXISTS head(singleton INTEGER PRIMARY KEY CHECK(singleton=1),state TEXT NOT NULL,state_sha256 TEXT NOT NULL)')
    db.execute('CREATE TABLE IF NOT EXISTS journal(revision INTEGER PRIMARY KEY,request_id TEXT UNIQUE NOT NULL,request_sha256 TEXT NOT NULL,receipt TEXT NOT NULL,receipt_sha256 TEXT NOT NULL)')
    db.execute('CREATE TABLE IF NOT EXISTS requests(request_id TEXT PRIMARY KEY,kind TEXT NOT NULL,input_sha256 TEXT NOT NULL,input_json TEXT NOT NULL,status TEXT NOT NULL,phase TEXT NOT NULL,result_json TEXT,error_json TEXT,created_utc TEXT NOT NULL,updated_utc TEXT NOT NULL)')


def _empty_failed_setup(attempt):
    """Only the observed pre-keygen failure is retryable: terminal failure and logs alone."""
    attempt = Path(attempt)
    allowed = {'keygen.command.json', 'keygen.stdout', 'keygen.stderr'}
    if not attempt.is_dir() or attempt.is_symlink(): return False
    entries = list(attempt.iterdir())
    if any(not p.is_file() or p.is_symlink() or p.name not in allowed for p in entries): return False
    record_path = attempt / 'keygen.command.json'
    if not record_path.exists(): return False
    try: record = j.read(record_path)
    except (OSError, ValueError): return False
    code = record.get('returncode'); argv = record.get('argv', [])
    return (type(code) is int and code != 0 and len(argv) == 4 and argv[1:3] == ['keygen', '--dir']
            and argv[3] == str(attempt / 'issuer') and not (attempt / 'issuer').exists())


def initialize(root, classes):
    """Fresh keygen once; matching initialization retries recover its durable phase."""
    backend.install_signal_handlers()
    root = Path(root).expanduser().resolve()
    j.need(isinstance(classes, (list, tuple)) and 1 <= len(classes) <= 1024, 'class_count')
    j.need(all(isinstance(x, str) and 0 < len(x) <= 256 for x in classes), 'class_labels')
    j.need(len(classes) == len(set(classes)), 'unique_classes')
    classes = sorted(classes)
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    import fcntl
    with (root / 'adapter.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if (root / 'journal/genesis.json').exists() and (root / 'initialized.json').exists():
            result = j.read(root / 'initialized.json')
            j.need(sorted(result['head']['classes']) == classes, 'initialization_class_conflict')
            backend.Backend(j.read(root / 'journal/genesis.json')['backend'])
            return result
        init_path = root / 'initializing.json'
        if init_path.exists():
            request = j.read(init_path)
            j.need(request['classes'] == classes, 'initialization_class_conflict')
            engine = backend.Backend(request['backend'])
        else:
            j.need(not any(p.name not in ('adapter.lock',) for p in root.iterdir()), 'fresh_instance_directory')
            engine = backend.Backend()
            request = {'classes': classes, 'backend': engine.descriptor, 'started_utc': backend.now()}
            j.write_json(init_path, request)
        issuer = root / 'issuer'
        if not (issuer / '.setup_complete.json').exists():
            attempts = root / 'setup_attempts'; attempts.mkdir(exist_ok=True)
            live = backend.live_processes(attempts)
            j.need(not live, 'setup_process_still_running', live)
            recovered = next((p / 'issuer' for p in sorted(attempts.glob('attempt*'))
                              if (p / 'issuer/.setup_complete.json').exists()), None)
            if recovered is None:
                attempt = attempts / f'attempt{len(list(attempts.iterdir())):03}'
                # Retry only a recorded failure containing logs alone: no issuer/key files can exist.
                j.need(all(_empty_failed_setup(p) for p in attempts.iterdir()), 'incomplete_setup_preserved',
                       {'path': str(attempts), 'action': 'Inspect the retained keygen attempt; resume its completed setup or choose a new instance root.'})
                attempt.mkdir(); (attempt / 'issuer').mkdir(mode=0o700)
                engine.native('keygen', attempt, dir=attempt / 'issuer')
                recovered = attempt / 'issuer'
                files = ('public.key', 'evaluation.key', 'parameters.json', 'zero.ct', '.private/reader.key')
                pins = {name: backend.sha(recovered / name) for name in files}
                j.write_json(recovered / '.setup_complete.json', {'files': pins, 'finished_utc': backend.now()})
            j.need(not issuer.exists(), 'incomplete_issuer_requires_recovery')
            os.replace(recovered, issuer); j.sync_directory(root)
        setup = j.read(issuer / '.setup_complete.json')
        for name, digest in setup['files'].items():
            j.need(backend.sha(issuer / name) == digest, 'setup_artifact_changed')
        journal = root / 'journal'; journal.mkdir(exist_ok=True)
        zero = (issuer / 'zero.ct').read_bytes(); zero_hash = j.sha(zero)
        j.write(journal / 'cas' / zero_hash, zero)
        initial = {label: {'acc_sha256': zero_hash, 'teaches': 0, 'queue': []} for label in classes}
        genesis_path = journal / 'genesis.json'
        if genesis_path.exists():
            genesis = j.read(genesis_path)
            j.need(genesis['classes'] == classes and genesis['backend'] == engine.descriptor, 'genesis_initialization_conflict')
        else:
            genesis = {'schema': 'continuing-proof-learner-genesis-v1', 'classes': classes,
                'backend': engine.descriptor, 'profile_sha256': engine.profile_sha256, 'policy': POLICY,
                'recipient_id': backend.sha(issuer / 'public.key'),
                'evaluation_key_sha256': backend.sha(issuer / 'evaluation.key'),
                'initial_classes': initial, 'zero_sha256': zero_hash, 'created_utc': backend.now()}
            j.write_json(genesis_path, genesis)
        gid = j.digest(genesis)
        state = {'genesis': gid, 'revision': 0, 'classes': initial, 'model_root': state_root(initial), 'last_receipt_sha256': None}
        db = j.connection(journal)
        try:
            db.execute('BEGIN IMMEDIATE'); _schema(db)
            row = db.execute('SELECT state FROM head WHERE singleton=1').fetchone()
            if row is None:
                db.execute('INSERT INTO head VALUES(1,?,?)', (j.canonical(state).decode(), j.digest(state)))
            else: j.need(j.parse(row['state']) == state, 'initial_head_conflict')
            db.execute('COMMIT')
        finally:
            if db.in_transaction: db.execute('ROLLBACK')
            db.close()
        result = {'initialized': True, 'genesis': gid, 'head': state, 'recipient_id': genesis['recipient_id'],
                  'full_reader_key': True, 'fifo_capacity': CAPACITY}
        j.write_json(root / 'initialized.json', result)
        return result


class Live:
    def __init__(self, root):
        backend.install_signal_handlers()
        self.root = Path(root).expanduser().resolve(); self.journal = self.root / 'journal'
        self.genesis = j.read(self.journal / 'genesis.json'); self.gid = j.digest(self.genesis)
        self.backend = backend.Backend(self.genesis['backend'])
        self.encoder = None; self._thread_lock = threading.RLock()
        self.check(); self.reopen()

    def check(self):
        j.need(j.read(self.journal / 'genesis.json') == self.genesis and self.genesis['policy'] == POLICY, 'genesis_policy_changed')
        self.backend.check()
        j.need(backend.sha(self.root / 'issuer/public.key') == self.genesis['recipient_id'] and
               backend.sha(self.root / 'issuer/evaluation.key') == self.genesis['evaluation_key_sha256'], 'public_key_identity')

    @contextlib.contextmanager
    def locked(self):
        import fcntl
        with self._thread_lock, (self.root / 'adapter.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            try:
                self.check(); yield
            finally: fcntl.flock(lock, fcntl.LOCK_UN)

    def head(self, db=None):
        own = db is None; db = db or j.connection(self.journal)
        try:
            row = db.execute('SELECT state,state_sha256 FROM head WHERE singleton=1').fetchone()
            j.need(row is not None, 'initialized_head')
            state = j.parse(row['state'])
            j.need(j.digest(state) == row['state_sha256'] and state['genesis'] == self.gid and
                   state['model_root'] == state_root(state['classes']), 'head_identity')
            return state
        finally:
            if own: db.close()

    def cas(self, digest):
        j.need(isinstance(digest, str) and re.fullmatch('[a-f0-9]{64}', digest), 'cas_identifier')
        raw = j.regular_bytes(self.journal / 'cas' / digest)
        j.need(j.sha(raw) == digest, 'cas_identity'); return raw

    def parent(self, state, req):
        j.need(req['label'] in state['classes'], 'declared_class')
        entry = state['classes'][req['label']]
        j.need(req['genesis'] == self.gid and req['recipient_id'] == self.genesis['recipient_id'], 'request_genesis_recipient')
        j.need(req['parent_sha256'] == j.digest(state) and req['revision'] == state['revision'] + 1 and
               req['parent_model_root'] == state['model_root'], 'current_model_parent')
        old = entry['queue'][0]['sha256'] if len(entry['queue']) == CAPACITY else self.genesis['zero_sha256']
        j.need(req['payloads']['acc_sha256'] == entry['acc_sha256'] and req['payloads']['old_sha256'] == old and
               req['lane'] == entry['teaches'] % CAPACITY, 'current_class_lane_fifo')
        j.need(req['profile_sha256'] == self.genesis['profile_sha256'], 'request_profile')

    def advance(self, state, req, receipt_sha):
        classes = dict(state['classes']); entry = classes[req['label']]; queue = list(entry['queue'])
        if len(queue) == CAPACITY: queue.pop(0)
        queue.append({'sha256': req['payloads']['fresh_sha256'], 'lane': req['lane']})
        classes[req['label']] = {'acc_sha256': req['payloads']['out_sha256'], 'teaches': entry['teaches'] + 1, 'queue': queue}
        return {'genesis': self.gid, 'revision': state['revision'] + 1, 'classes': classes,
                'model_root': state_root(classes), 'last_receipt_sha256': receipt_sha}

    def reopen(self):
        state = {'genesis': self.gid, 'revision': 0, 'classes': self.genesis['initial_classes'],
                 'model_root': state_root(self.genesis['initial_classes']), 'last_receipt_sha256': None}
        db = j.connection(self.journal)
        try:
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                receipt = j.parse(row['receipt']); req = receipt['request']
                j.need(j.digest(receipt) == row['receipt_sha256'] and j.digest(req) == row['request_sha256'], 'receipt_identity')
                self.parent(state, req)
                accepted = receipt['proof_acceptance']
                j.need(accepted['verified'] and accepted['proofs_verified'] == 8 and accepted['binding'] == req['payloads'], 'retained_update_acceptance')
                for digest in req['payloads'].values(): self.cas(digest)
                state = self.advance(state, req, row['receipt_sha256'])
            j.need(state == self.head(db), 'reopened_committed_chain')
        finally: db.close()

    def directory(self, kind, request_id):
        return self.root / kind / _request_id(request_id)

    def vector(self, text):
        j.need(isinstance(text, str) and text.strip(), 'supplied_text')
        if self.encoder is None: self.encoder = backend.helper().TextEncoder(self.root / 'encoder_cache')
        return _vector(self.encoder.encode([text])[0])

    def _request(self, kind, request_id, inputs):
        _request_id(request_id)
        out = self.directory('teaching' if kind == 'teach' else 'queries', request_id)
        digest = j.digest(inputs); db = j.connection(self.journal)
        try:
            db.execute('BEGIN IMMEDIATE')
            row = db.execute('SELECT * FROM requests WHERE request_id=?', (request_id,)).fetchone()
            if row:
                j.need(row['kind'] == kind and row['input_sha256'] == digest, 'request_id_input_conflict')
                db.execute('COMMIT')
                out.mkdir(parents=True, exist_ok=True)
                if not (out / 'input.json').exists(): j.write_json(out / 'input.json', inputs)
                return out, j.parse(row['result_json']) if row['result_json'] else None
            stamp = backend.now()
            db.execute('INSERT INTO requests VALUES(?,?,?,?,?,?,?,?,?,?)',
                (request_id, kind, digest, j.canonical(inputs).decode(), 'incomplete', 'requested', None, None, stamp, stamp))
            db.execute('COMMIT')
        finally:
            if db.in_transaction: db.execute('ROLLBACK')
            db.close()
        out.mkdir(parents=True, exist_ok=True)
        j.write_json(out / 'input.json', inputs)
        return out, None

    def _status(self, out, phase, status='running', **extra):
        record = {'request_id': out.name, 'phase': phase, 'status': status, 'utc': backend.now(), **extra}
        j.write_json(out / 'progress.json', record)
        db = j.connection(self.journal)
        try:
            db.execute('UPDATE requests SET status=?,phase=?,updated_utc=?,error_json=? WHERE request_id=? AND result_json IS NULL',
                (status, phase, record['utc'], j.canonical(extra).decode() if status == 'failed' else None, out.name))
        finally: db.close()

    def _phase(self, out, name, build, recover=None):
        phases = out / 'phases'; phases.mkdir(exist_ok=True)
        checkpoint = phases / (name + '.json')
        if checkpoint.exists():
            record = j.read(checkpoint)
            j.need(record['result_sha256'] == j.digest(record['result']), 'phase_checkpoint_identity')
            return record
        attempts = sorted(phases.glob(name + '-attempt*'))
        for attempt in attempts:
            live = backend.live_processes(attempt)
            j.need(not live, 'phase_process_still_running', live)
            if (attempt / 'completed.json').exists():
                record = j.read(attempt / 'completed.json')
                j.need(record['result_sha256'] == j.digest(record['result']), 'phase_checkpoint_identity')
                j.write_json(checkpoint, record); return record
            if recover is not None:
                result = recover(attempt)
                if result is not None:
                    record = {'phase': name, 'attempt': str(attempt), 'result': result,
                        'result_sha256': j.digest(result), 'elapsed_seconds': None, 'recovered_complete_phase': True,
                        'finished_utc': backend.now()}
                    j.write_json(attempt / 'completed.json', record); j.write_json(checkpoint, record)
                    return record
        attempt = phases / f'{name}-attempt{len(attempts):03}'; attempt.mkdir()
        self._status(out, name, attempt=str(attempt), resumed=bool(attempts))
        start = time.monotonic()
        try:
            result = build(attempt)
            record = {'phase': name, 'attempt': str(attempt), 'result': result,
                'result_sha256': j.digest(result), 'elapsed_seconds': time.monotonic()-start, 'finished_utc': backend.now()}
            j.write_json(attempt / 'completed.json', record); j.write_json(checkpoint, record)
            return record
        except BaseException as exc:
            j.write_json(attempt / 'failed.json', {'error': repr(exc), 'phase': name, 'utc': backend.now(), 'elapsed_seconds': time.monotonic()-start})
            self._status(out, name, 'failed', error=str(exc), attempt=str(attempt), resumable=True)
            raise

    @staticmethod
    def _recover_result(attempt, name, flag, count=None):
        path = attempt / name / 'result.json'
        if not path.exists(): return None
        value = j.read(path)
        j.need(value.get(flag) is True, 'incomplete_backend_result')
        if count is not None:
            key = 'proofs_verified' if 'proofs_verified' in value else 'fresh_proofs'
            j.need(value.get(key) == count, 'complete_backend_proof_count')
        return {'path': str(attempt / name), 'value': value}

    def _metrics(self, out, accepted, operation):
        entries = accepted['verifications'] if operation == 'teach' else [v for c in accepted.values() for v in c['verifications']]
        phases = [j.read(p) for p in (out / 'phases').glob('*.json')]
        generated = []
        for proof in (out / 'phases').rglob('proof.bin'):
            report = proof.with_name('proof.json')
            if report.exists() and j.read(report).get('verified') is True:
                generated.append(proof)
        result = {'proofs_generated': len(generated), 'accepted_fresh_proofs': len(entries),
            'proofs_verified': len(entries), 'discarded_phase_attempts': len(list((out / 'phases').rglob('failed.json'))),
            'proof_bytes': sum(v['proof_bytes'] for v in entries),
            'phase_elapsed_seconds': {p['phase']: p['elapsed_seconds'] for p in phases},
            'committed_updates': int(operation == 'teach'), 'answered_queries': int(operation == 'query'),
            'private_reads': 0 if operation == 'teach' else len(accepted)}
        j.write_json(out / 'metrics.json', result)
        return result

    def teach_vector(self, label, vector, text, request_id):
        vector = _vector(vector); j.need(isinstance(text, str), 'text_metadata')
        inputs = {'kind': 'teach', 'label': label, 'text': text, 'vector': vector}
        with self.locked():
            out, completed = self._request('teach', request_id, inputs)
            if completed is not None: return completed
            head = self.head(); j.need(label in head['classes'], 'declared_class')
            context_path = out / 'context.json'
            if context_path.exists():
                context = j.read(context_path)
                j.need(context['head'] == head, 'stale_incomplete_teach_parent')
            else:
                context = {'head': head}; j.write_json(context_path, context)
            entry = head['classes'][label]; lane = entry['teaches'] % CAPACITY
            old = entry['queue'][0]['sha256'] if len(entry['queue']) == CAPACITY else self.genesis['zero_sha256']
            vector_path = out / 'vector.json'
            if not vector_path.exists(): j.write_json(vector_path, vector)
            j.need(j.read(vector_path) == vector, 'retained_feature_identity')
            def issue(attempt):
                self.backend.native('issue', attempt, dir=self.root / 'issuer', vector=vector_path, lane=lane, out=attempt / 'fresh.ct')
                return {'path': str(attempt / 'fresh.ct'), 'sha256': backend.sha(attempt / 'fresh.ct')}
            issued = self._phase(out, 'issue', issue)['result']
            j.need(backend.sha(issued['path']) == issued['sha256'], 'issued_ciphertext_identity')
            def learn(attempt):
                case = attempt / 'case'; case.mkdir()
                j.write(case / 'acc.ct', self.cas(entry['acc_sha256'])); j.write(case / 'old.ct', self.cas(old))
                j.write(case / 'fresh.ct', Path(issued['path']).read_bytes())
                self.backend.native('learn', attempt, acc=case / 'acc.ct', fresh=case / 'fresh.ct', old=case / 'old.ct', out=case / 'out.ct')
                return {'path': str(case), 'binding': {role + '_sha256': backend.sha(case / (role + '.ct')) for role in ('acc', 'fresh', 'old', 'out')}}
            candidate = self._phase(out, 'learn', learn)['result']; case = Path(candidate['path'])
            req = {'schema': 'continuing-update-v1', 'request_id': request_id, 'genesis': self.gid,
                'recipient_id': self.genesis['recipient_id'], 'revision': head['revision'] + 1,
                'parent_sha256': j.digest(head), 'parent_model_root': head['model_root'], 'label': label, 'lane': lane,
                'text_sha256': j.sha(text.encode()), 'feature_sha256': backend.sha(vector_path),
                'payloads': candidate['binding'], 'profile_sha256': self.genesis['profile_sha256']}
            self.parent(head, req); j.write_json(out / 'request.json', req)
            def prove(attempt):
                value = self.backend.produce_update(case, attempt / 'produced', attempt)
                return {'path': str(attempt / 'produced'), 'value': value}
            produced = self._phase(out, 'prove', prove,
                lambda a: self._recover_result(a, 'produced', 'proofs_generated', 8))['result']
            j.need(produced['value']['binding'] == req['payloads'] and produced['value']['fresh_proofs'] == 8, 'complete_update_production')
            def verify(attempt):
                value = self.backend.verify_update(req['payloads'], produced['path'], attempt / 'verified', attempt)
                return {'path': str(attempt / 'verified'), 'value': value}
            accepted = self._phase(out, 'verify', verify,
                lambda a: self._recover_result(a, 'verified', 'verified', 8))['result']['value']
            j.need(accepted['verified'] and accepted['proofs_verified'] == 8 and accepted['binding'] == req['payloads'], 'complete_update_acceptance')
            metrics = self._metrics(out, accepted, 'teach'); self.check()
            db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); self.parent(self.head(db), req)
                for role, digest in req['payloads'].items():
                    raw = (case / (role.removesuffix('_sha256') + '.ct')).read_bytes()
                    j.need(j.sha(raw) == digest, 'verified_update_bytes')
                    path = self.journal / 'cas' / digest
                    if path.exists(): j.need(self.cas(digest) == raw, 'immutable_cas_conflict')
                    else: j.write(path, raw)
                receipt = {'schema': 'continuing-teach-receipt-v1', 'request': req, 'proof_acceptance': accepted,
                           'parent_checked_inside_commit': True, 'accepted_utc': backend.now()}
                digest = j.digest(receipt); new = self.advance(head, req, digest)
                result = {'committed': True, 'head': new, 'receipt_sha256': digest, 'request': req,
                          'private_reads': 0, 'metrics': metrics, 'fifo_capacity': CAPACITY}
                db.execute('INSERT INTO journal VALUES(?,?,?,?,?)', (new['revision'], request_id, j.digest(req), j.canonical(receipt).decode(), digest))
                db.execute('UPDATE head SET state=?,state_sha256=? WHERE singleton=1', (j.canonical(new).decode(), j.digest(new)))
                db.execute('UPDATE requests SET status=?,phase=?,result_json=?,error_json=NULL,updated_utc=? WHERE request_id=?',
                    ('complete', 'committed', j.canonical(result).decode(), backend.now(), request_id))
                db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            j.write_json(out / 'committed.json', result); self._status(out, 'committed', 'complete')
            return result

    def teach(self, label, text, request_id):
        return self.teach_vector(label, self.vector(text), text, request_id)

    def prepare_query(self, vector, text, request_id):
        vector = _vector(vector); j.need(isinstance(text, str), 'text_metadata')
        inputs = {'kind': 'query', 'text': text, 'vector': vector}
        with self.locked():
            out, completed = self._request('query', request_id, inputs)
            if completed is not None: return j.read(out / 'request.json')
            if (out / 'prepared.json').exists():
                req = j.read(out / 'request.json'); self.query_binding(self.head(), req); return req
            head = self.head(); active = sorted(c for c, e in head['classes'].items() if e['queue'])
            j.need(active, 'active_classes')
            context = out / 'context.json'
            if context.exists(): j.need(j.read(context)['head'] == head, 'stale_incomplete_query_parent')
            else: j.write_json(context, {'head': head})
            query_path = out / 'query.json'
            if not query_path.exists(): j.write_json(query_path, vector)
            j.need(j.read(query_path) == vector, 'retained_feature_identity')
            req = {'schema': 'continuing-query-v1', 'request_id': request_id, 'genesis': self.gid,
                'recipient_id': self.genesis['recipient_id'], 'revision': head['revision'], 'head_sha256': j.digest(head),
                'model_root': head['model_root'], 'profile_sha256': self.genesis['profile_sha256'],
                'evaluation_key_sha256': self.genesis['evaluation_key_sha256'], 'query_sha256': backend.sha(query_path),
                'text_sha256': j.sha(text.encode()), 'active_classes': active, 'classes': {}}
            for index, label in enumerate(active):
                acc = head['classes'][label]['acc_sha256']; self.cas(acc)
                def capture(attempt):
                    value = self.backend.capture(self.root / 'issuer', self.journal / 'cas' / acc, query_path,
                        attempt / 'capture', head['revision'], label, attempt)
                    return {'path': str(attempt / 'capture'), 'value': value}
                captured = self._phase(out, f'class{index:03}-capture', capture)['result']
                def prove(attempt):
                    value = self.backend.produce_infer(self.journal / 'cas' / acc, query_path,
                        self.root / 'issuer/evaluation.key', captured['path'], attempt / 'produced', attempt)
                    return {'path': str(attempt / 'produced'), 'value': value}
                produced = self._phase(out, f'class{index:03}-prove', prove,
                    lambda a: self._recover_result(a, 'produced', 'proofs_generated', 116))['result']
                j.need(produced['value']['fresh_proofs'] == 116 and produced['value'].get('reused_proofs', 0) == 0, 'complete_fresh_kernel_production')
                binding = produced['value']['binding']
                j.need(binding['model_ciphertext_sha256'] == acc and binding['query_sha256'] == req['query_sha256'] and
                       binding['evaluation_key_sha256'] == req['evaluation_key_sha256'], 'query_production_binding')
                req['classes'][label] = {'model_ciphertext_sha256': acc,
                    'kernel_ciphertext_sha256': binding['kernel_ciphertext_sha256'],
                    'count': len(head['classes'][label]['queue']), 'produced': produced['path'], 'index': index}
                j.write_json(out / 'request.json', req)
            self.query_binding(self.head(), req)
            j.write_json(out / 'prepared.json', {'prepared': True, 'private_reads': 0,
                'request_sha256': j.digest(req), 'finished_utc': backend.now()})
            self._status(out, 'prepared', 'prepared', classes_completed=len(active))
            return req

    def query_binding(self, head, req):
        active = sorted(c for c, e in head['classes'].items() if e['queue'])
        j.need(req['genesis'] == self.gid and req['recipient_id'] == self.genesis['recipient_id'] and
               req['profile_sha256'] == self.genesis['profile_sha256'], 'query_genesis_profile')
        j.need(req['revision'] == head['revision'] and req['head_sha256'] == j.digest(head) and
               req['model_root'] == head['model_root'], 'query_current_revision')
        j.need(req['active_classes'] == active and set(req['classes']) == set(active), 'all_active_classes_required')
        j.need(req['evaluation_key_sha256'] == self.genesis['evaluation_key_sha256'], 'query_evaluation_key')
        for label, entry in req['classes'].items():
            j.need(entry['model_ciphertext_sha256'] == head['classes'][label]['acc_sha256'] and
                   entry['count'] == len(head['classes'][label]['queue']), 'query_class_current_model')

    def accept_query(self, request_id):
        with self.locked():
            out = self.directory('queries', request_id); req = j.read(out / 'request.json')
            j.need((out / 'prepared.json').exists() and j.read(out / 'prepared.json')['request_sha256'] == j.digest(req), 'complete_query_preparation')
            self.query_binding(self.head(), req)
            path = out / 'public_acceptance.json'
            if path.exists():
                accepted = j.read(path); j.need(accepted['request_sha256'] == j.digest(req), 'retained_query_acceptance_identity')
                return accepted
            checks = {}; outputs = {}
            for label, entry in req['classes'].items():
                expected = {k: entry[k] for k in ('model_ciphertext_sha256', 'kernel_ciphertext_sha256')}
                expected.update(query_sha256=req['query_sha256'], evaluation_key_sha256=req['evaluation_key_sha256'])
                def verify(attempt):
                    value = self.backend.verify_infer(expected, entry['produced'], attempt / 'verified', attempt)
                    return {'path': str(attempt / 'verified'), 'value': value}
                accepted = self._phase(out, f'class{entry["index"]:03}-verify', verify,
                    lambda a: self._recover_result(a, 'verified', 'complete_infer_verified', 116))['result']['value']
                j.need(accepted['complete_infer_verified'] and accepted['proofs_verified'] == 116 and
                       all(accepted['binding'][k] == v for k, v in expected.items()), 'complete_kernel_acceptance')
                checks[label] = accepted
                outputs[label] = str(Path(entry['produced']) / 'infer_case/expected_kernel.ct')
            self.check(); db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); head = self.head(db); self.query_binding(head, req)
                acceptance = {'all_active_classes_verified': True, 'head': head, 'request': req,
                    'request_sha256': j.digest(req), 'profile_sha256': self.genesis['profile_sha256'],
                    'checks': checks, 'outputs': outputs, 'private_reads': 0,
                    'public_phase_complete_utc': backend.now(), 'head_checked_under_write_lock': True}
                j.write_json(path, acceptance); db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            self._status(out, 'publicly-accepted', 'accepted', classes_verified=len(checks))
            return acceptance

    def receive(self, request_id):
        with self.locked():
            out = self.directory('queries', request_id)
            db = j.connection(self.journal)
            try:
                row = db.execute('SELECT result_json FROM requests WHERE request_id=? AND kind=?', (request_id, 'query')).fetchone()
                if row and row['result_json']: return j.parse(row['result_json'])
            finally: db.close()
            req = j.read(out / 'request.json'); self.query_binding(self.head(), req)
            acceptance = j.read(out / 'public_acceptance.json')
            j.need(acceptance['all_active_classes_verified'] and acceptance['head_checked_under_write_lock'] and
                   acceptance['request_sha256'] == j.digest(req) and acceptance['request'] == req and
                   set(acceptance['checks']) == set(req['active_classes']), 'all_proofs_before_private_receive')
            for label, path in acceptance['outputs'].items():
                j.need(backend.sha(path) == req['classes'][label]['kernel_ciphertext_sha256'] and
                       acceptance['checks'][label]['complete_infer_verified'] and
                       acceptance['checks'][label]['proofs_verified'] == 116, 'accepted_reader_output')
            if not (out / 'receive_started.json').exists():
                j.write_json(out / 'receive_started.json', {'utc': backend.now(),
                    'public_acceptance_sha256': backend.sha(out / 'public_acceptance.json')})
            answers = {}
            for index, label in enumerate(req['active_classes']):
                def read(attempt):
                    value = self.backend.native('read', attempt, dir=self.root / 'issuer', ct=acceptance['outputs'][label])
                    return {'value': value}
                answers[label] = self._phase(out, f'class{index:03}-read', read)['result']['value']
            order = sorted(answers, key=lambda c: (-Fraction(answers[c]['sum_kernel'], req['classes'][c]['count']), c))
            metrics = self._metrics(out, acceptance['checks'], 'query')
            result = {'answered': True, 'prediction': order[0], 'winner': order[0], 'ranking': order,
                'classes': answers, 'counts': {c: req['classes'][c]['count'] for c in answers},
                'class_scores': [{'label': c, 'sum_kernel': answers[c]['sum_kernel'], 'count': req['classes'][c]['count'],
                    'mean_numerator': answers[c]['sum_kernel'], 'mean_denominator': req['classes'][c]['count']} for c in order],
                'revision': req['revision'], 'model_root': req['model_root'], 'public_accepted': True,
                'public_acceptance_sha256': backend.sha(out / 'public_acceptance.json'),
                'private_reads': len(answers), 'finished_utc': backend.now(), 'full_reader': True, 'metrics': metrics}
            db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); self.query_binding(self.head(db), req)
                db.execute('UPDATE requests SET status=?,phase=?,result_json=?,error_json=NULL,updated_utc=? WHERE request_id=?',
                    ('complete', 'answered', j.canonical(result).decode(), backend.now(), request_id))
                db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            j.write_json(out / 'answer.json', result); self._status(out, 'answered', 'complete')
            return result

    def query_vector(self, vector, text, request_id):
        vector = _vector(vector)
        # Completed response survives later model revisions; request identity is checked first.
        with self.locked():
            _, completed = self._request('query', request_id, {'kind': 'query', 'text': text, 'vector': vector})
            if completed is not None: return completed
        self.prepare_query(vector, text, request_id); self.accept_query(request_id)
        return self.receive(request_id)

    def query(self, text, request_id):
        return self.query_vector(self.vector(text), text, request_id)


def get_progress(root, request_id):
    root = Path(root).expanduser().resolve(); _request_id(request_id)
    for kind in ('teaching', 'queries'):
        out = root / kind / request_id; path = out / 'progress.json'
        if path.exists():
            result = j.read(path)
            attempt = result.get('attempt')
            if attempt and result['status'] == 'running':
                candidates = list(Path(attempt).rglob('progress.json'))
                if candidates:
                    latest = max(candidates, key=lambda p: p.stat().st_mtime)
                    result['backend_progress'] = j.read(latest)
            return result
    return {'request_id': request_id, 'status': 'unknown', 'phase': None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    init = sub.add_parser('init'); init.add_argument('root'); init.add_argument('--class', dest='classes', action='append', required=True)
    for name in ('teach', 'query', 'status'):
        p = sub.add_parser(name); p.add_argument('root')
        if name != 'status':
            p.add_argument('--text', required=True); p.add_argument('--request-id', required=True); p.add_argument('--vector-json')
        if name == 'teach': p.add_argument('--label', required=True)
    args = parser.parse_args()
    if args.action == 'init': result = initialize(args.root, args.classes)
    else:
        live = Live(args.root)
        if args.action == 'status': result = live.head()
        elif args.action == 'teach':
            result = live.teach_vector(args.label, j.read(args.vector_json), args.text, args.request_id) if args.vector_json else live.teach(args.label, args.text, args.request_id)
        else: result = live.query_vector(j.read(args.vector_json), args.text, args.request_id) if args.vector_json else live.query(args.text, args.request_id)
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
