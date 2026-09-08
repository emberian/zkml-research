#!/usr/bin/env python3
"""Local durable multiclass BFV model gate over the native emitted-relation verifier.

Proof checks ciphertext arithmetic. Parser, request policy, parent CAS, SQLite,
local caller authorization and recipient metadata are explicit protocol TCB.
This process has no BFV secret key; the existing full learner reader survives.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import socketserver
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve().parent
NAMES = ('acc', 'fresh', 'old', 'out')
PARAMS_ID = 'fb16ccd74dd4b7bedb6673b369b56475af06f9415a4faf4645d411d3c7d0cda3'
RANDOMNESS_RULE = {
    'arithmetic': 'deterministic canonical BFV acc+fresh-old; no new arithmetic randomness or rerandomization',
    'fresh_ciphertext': 'external trusted learner encryption; randomness quality is not proved by this relation',
    'proof': 'portable public preprocessing; witness hiding commitments generated with OS randomness by the prover; freshness not certified by verification',
}


class Refused(Exception):
    def __init__(self, code, evidence=None):
        super().__init__(code)
        self.code, self.evidence = code, evidence


def need(condition, code, evidence=None):
    if not condition:
        raise Refused(code, evidence)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(value):
    return sha(canonical(value))


def model_root(classes):
    return digest({'schema': 'proved-class-model-map-v1', 'classes': classes})


def replace_class(classes, req):
    updated = dict(classes)
    updated[req['learner_class']] = {'acc_sha256': req['payloads']['out'], 'learner_event': req['learner_event']}
    return updated


def parse(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate_json_key')
            result[key] = value
        return result
    def constant(_):
        raise Refused('nonfinite_json_number')
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=constant)


def read(path):
    return parse(Path(path).read_bytes())


def regular_bytes(path, cap=16_000_000):
    path = Path(path)
    need(path.is_absolute() and path.resolve() == path and path.is_file() and not path.is_symlink(), 'regular_canonical_artifact_path')
    need(path.stat().st_size <= cap, 'artifact_size_limit')
    return path.read_bytes()


def sync_directory(path):
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def write(path, raw, mode=0o600):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    fd, name = tempfile.mkstemp(prefix='.write-', dir=path.parent)
    try:
        os.fchmod(fd, mode)
        with os.fdopen(fd, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
        sync_directory(path.parent)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def write_json(path, value):
    write(path, canonical(value) + b'\n')


def connection(root):
    db = sqlite3.connect(Path(root) / 'journal.sqlite3', timeout=30, isolation_level=None)
    db.row_factory = sqlite3.Row
    db.execute('PRAGMA journal_mode=WAL')
    db.execute('PRAGMA synchronous=FULL')
    return db


def header(raw, key_id=None):
    need(len(raw) == 85103 and raw[:8] == b'RSBFV001' and raw[8] == 1, 'ciphertext_envelope_format')
    need(raw[9:41].hex() == PARAMS_ID and int.from_bytes(raw[73:81], 'little') == 85022, 'ciphertext_parameters')
    if key_id is not None:
        need(raw[41:73].hex() == key_id, 'declared_key_id')
    return raw[41:73].hex()


def initialize(root, binary, template, checkpoint_path, initial_files_path, recipient,
               expected_binary_sha256, expected_template_sha256):
    root = Path(root)
    need(root.is_absolute() and root.resolve() == root and not root.exists(), 'fresh_canonical_service_root')
    native = regular_bytes(binary, 200_000_000)
    relation = regular_bytes(template)
    need(sha(native) == expected_binary_sha256 and sha(relation) == expected_template_sha256, 'approved_executable_and_template_pins')
    checkpoint_bytes = regular_bytes(checkpoint_path)
    checkpoint, initial_files = parse(checkpoint_bytes), read(initial_files_path)
    need(set(checkpoint) == {'schema', 'global_learner_event', 'classes', 'provenance'}
         and checkpoint['schema'] == 'proved-model-checkpoint-v1', 'checkpoint_schema')
    learner_event, classes = checkpoint['global_learner_event'], checkpoint['classes']
    need(isinstance(recipient, str) and recipient and type(learner_event) is int and learner_event >= 0, 'initial_policy')
    need(isinstance(classes, dict) and 0 < len(classes) <= 1024 and set(initial_files) == set(classes), 'initial_model_classes')
    initial_objects, key_id = {}, None
    for label, entry in classes.items():
        need(isinstance(label, str) and 0 < len(label) <= 256 and set(entry) == {'acc_sha256', 'learner_event'}
             and type(entry['learner_event']) is int and 0 <= entry['learner_event'] <= learner_event, 'initial_class_entry')
        raw = regular_bytes(initial_files[label])
        actual_key = header(raw, key_id)
        key_id = actual_key if key_id is None else key_id
        need(sha(raw) == entry['acc_sha256'], 'checkpoint_accumulator_hash')
        initial_objects[sha(raw)] = raw
    root.mkdir(parents=True, mode=0o700)
    write(root / 'approved/verifier', native, 0o500)
    write(root / 'approved/template.json', relation)
    write(root / 'cas' / sha(checkpoint_bytes), checkpoint_bytes)
    for h, raw in initial_objects.items():
        write(root / 'cas' / h, raw)
    genesis = {'schema': 'proved-multiclass-update-genesis-v1',
        'service_source_sha256': sha(Path(__file__).read_bytes()),
        'native_verifier_sha256': sha(native), 'approved_template_sha256': sha(relation),
        'relation': 'Lean-generated canonical NTT BFV acc+fresh-old; 8192 rows, 57 columns, 16384 RNS equations',
        'params_id': PARAMS_ID, 'declared_key_id': key_id, 'recipient_id': recipient,
        'checkpoint_sha256': sha(checkpoint_bytes), 'initial_checkpoint': checkpoint,
        'initial_model_root': model_root(classes),
        'global_event_rule': 'Consecutive admitted events after the imported checkpoint; fixed class set; exactly one class replacement per commit.',
        'randomness_rule': RANDOMNESS_RULE,
        'reader_scope': 'Existing full BFV reader survives. Declared keyID/recipient equality is protocol metadata, not ciphertext key-membership proof or restricted release.',
        'protocol_scope': 'Local caller authorization and genesis selection, ciphertext/descriptor parsers, native verifier adapter and durable parent/commit logic are TCB. No confidentiality or hostile-OS claim.'}
    write_json(root / 'genesis.json', genesis)
    gid = digest(genesis)
    state = {'genesis': gid, 'revision': 0, 'classes': classes, 'model_root': model_root(classes), 'learner_event': learner_event,
             'recipient_id': recipient, 'last_receipt_sha256': None}
    db = connection(root)
    try:
        db.execute('BEGIN IMMEDIATE')
        db.execute('CREATE TABLE head (singleton INTEGER PRIMARY KEY CHECK(singleton=1), state TEXT NOT NULL, state_sha256 TEXT NOT NULL)')
        db.execute('CREATE TABLE journal (revision INTEGER PRIMARY KEY, request_id TEXT UNIQUE NOT NULL, request_sha256 TEXT NOT NULL, receipt TEXT NOT NULL, receipt_sha256 TEXT NOT NULL)')
        db.execute('INSERT INTO head VALUES(1,?,?)', (canonical(state).decode(), digest(state)))
        db.execute('COMMIT')
    finally:
        db.close()
    sync_directory(root)
    return {'ok': True, 'genesis': gid, 'head': state, 'head_sha256': digest(state)}


class Service:
    def __init__(self, root):
        self.root = Path(root)
        self.genesis = read(self.root / 'genesis.json')
        self.gid = digest(self.genesis)
        self.binary = self.root / 'approved/verifier'
        self.template = self.root / 'approved/template.json'
        self.check_assets()
        self.audit_reopen()

    def check_assets(self):
        need(read(self.root / 'genesis.json') == self.genesis, 'genesis_changed')
        need(sha(Path(__file__).read_bytes()) == self.genesis['service_source_sha256'], 'service_source_changed')
        need(sha(regular_bytes(self.binary, 200_000_000)) == self.genesis['native_verifier_sha256'], 'native_verifier_changed')
        need(sha(regular_bytes(self.template)) == self.genesis['approved_template_sha256'], 'approved_template_changed')

    def cas(self, h):
        need(isinstance(h, str) and len(h) == 64 and all(c in '0123456789abcdef' for c in h), 'cas_identifier')
        raw = regular_bytes(self.root / 'cas' / h)
        need(sha(raw) == h, 'cas_byte_identity')
        return raw

    def head(self, db=None):
        owned = db is None
        db = db or connection(self.root)
        try:
            row = db.execute('SELECT state,state_sha256 FROM head WHERE singleton=1').fetchone()
            state = parse(row['state'])
            need(digest(state) == row['state_sha256'] and state['genesis'] == self.gid, 'installed_head_identity')
            return {'ok': True, 'genesis': self.gid, 'head': state, 'head_sha256': row['state_sha256']}
        finally:
            if owned:
                db.close()

    def audit_reopen(self):
        """Reopen checks retained receipts/CAS and head consistency, not new proof execution."""
        checkpoint = self.genesis['initial_checkpoint']
        need(parse(self.cas(self.genesis['checkpoint_sha256'])) == checkpoint, 'retained_checkpoint_identity')
        state = {'genesis': self.gid, 'revision': 0, 'classes': checkpoint['classes'],
                 'model_root': model_root(checkpoint['classes']), 'learner_event': checkpoint['global_learner_event'],
                 'recipient_id': self.genesis['recipient_id'], 'last_receipt_sha256': None}
        need(state['model_root'] == self.genesis['initial_model_root'], 'retained_initial_model_root')
        for entry in state['classes'].values():
            self.cas(entry['acc_sha256'])
        db = connection(self.root)
        try:
            db.execute('BEGIN')
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                receipt = parse(row['receipt'])
                request = receipt['request']
                need(digest(receipt) == row['receipt_sha256'] and digest(request) == row['request_sha256']
                     and request['request_id'] == row['request_id'], 'retained_receipt_identity')
                need(receipt['revision'] == row['revision'] == state['revision'] + 1
                     and request['parent_revision'] == state['revision']
                     and request['parent_sha256'] == digest(state), 'retained_parent_chain')
                self.policy(request)
                self.current_parent(state, request)
                for h in [*request['payloads'].values(), request['proof_sha256'], request['public_rows_sha256'], request['source_event_sha256']]:
                    self.cas(h)
                need(receipt['proof_acceptance']['verified'] is True
                     and receipt['proof_acceptance']['proof_sha256'] == request['proof_sha256']
                     and receipt['binding_sha256'] == digest(request), 'retained_proof_acceptance')
                need(receipt['previous_model_root'] == state['model_root']
                     and receipt['changed_class'] == request['learner_class'], 'retained_model_transition')
                state = self.next_state(state, request, row['receipt_sha256'])
                need(receipt['next_acc_sha256'] == state['classes'][request['learner_class']]['acc_sha256']
                     and receipt['next_model_root'] == state['model_root'] == request['next_model_root'], 'retained_output_identity')
            need(self.head(db)['head'] == state, 'reopened_exact_head')
            db.execute('COMMIT')
        finally:
            db.close()

    def policy(self, req):
        fields = {'schema', 'request_id', 'genesis', 'parent_revision', 'parent_sha256', 'recipient_id',
                  'template_sha256', 'randomness_rule_sha256', 'payloads', 'public_rows_sha256', 'proof_sha256',
                  'source_event_sha256', 'learner_class', 'parent_learner_event', 'learner_event', 'parent_model_root', 'next_model_root'}
        need(set(req) == fields and req['schema'] == 'proved-multiclass-expiry-request-v1', 'request_schema')
        need(isinstance(req['request_id'], str) and 0 < len(req['request_id']) <= 128, 'request_id')
        need(req['genesis'] == self.gid and req['recipient_id'] == self.genesis['recipient_id'], 'genesis_or_recipient')
        need(req['template_sha256'] == self.genesis['approved_template_sha256'], 'approved_template_only')
        need(req['randomness_rule_sha256'] == digest(self.genesis['randomness_rule']), 'declared_randomness_rule')
        need(req['learner_class'] in self.genesis['initial_checkpoint']['classes'], 'learner_class')
        need(type(req['parent_revision']) is int and req['parent_revision'] >= 0
             and type(req['parent_learner_event']) is int and type(req['learner_event']) is int
             and req['learner_event'] > req['parent_learner_event'], 'revision_types_and_order')
        need(set(req['payloads']) == set(NAMES), 'ciphertext_payload_roles')
        hashes = [req[k] for k in ('genesis', 'parent_sha256', 'template_sha256', 'randomness_rule_sha256',
                  'public_rows_sha256', 'proof_sha256', 'source_event_sha256', 'parent_model_root', 'next_model_root')] + list(req['payloads'].values())
        need(all(isinstance(h, str) and len(h) == 64 and all(c in '0123456789abcdef' for c in h) for h in hashes), 'hash_identifiers')

    def current_parent(self, state, req):
        need(req['parent_revision'] == state['revision'] and req['parent_sha256'] == digest(state), 'stale_parent')
        need(state['model_root'] == model_root(state['classes']) == req['parent_model_root'], 'current_model_root')
        entry = state['classes'][req['learner_class']]
        need(req['payloads']['acc'] == entry['acc_sha256'] and req['parent_learner_event'] == entry['learner_event'], 'current_class_accumulator')
        need(req['learner_event'] == state['learner_event'] + 1, 'consecutive_global_event')
        need(req['next_model_root'] == model_root(replace_class(state['classes'], req)), 'proposed_model_root')

    def next_state(self, state, req, receipt_hash):
        classes = replace_class(state['classes'], req)
        return {'genesis': self.gid, 'revision': state['revision'] + 1, 'classes': classes, 'model_root': model_root(classes),
                'learner_event': req['learner_event'], 'recipient_id': req['recipient_id'], 'last_receipt_sha256': receipt_hash}

    def prior(self, db, req):
        row = db.execute('SELECT request_sha256,receipt,receipt_sha256 FROM journal WHERE request_id=?', (req['request_id'],)).fetchone()
        if row is not None:
            need(row['request_sha256'] == digest(req), 'request_id_conflict')
            return {'ok': True, 'status': 'replayed', 'receipt': parse(row['receipt']), 'receipt_sha256': row['receipt_sha256'], 'proof_reexecuted': False}

    def native(self, args, cwd, code):
        env = dict(os.environ, RAYON_NUM_THREADS='4')
        started = time.monotonic_ns()
        proc = subprocess.run([str(self.binary), *args], cwd=cwd, env=env, capture_output=True, timeout=30)
        record = {'argv': [str(self.binary), *args], 'exit_code': proc.returncode,
                  'elapsed_ns': time.monotonic_ns() - started, 'stdout': proc.stdout.decode(), 'stderr': proc.stderr.decode()}
        need(proc.returncode == 0, code, record)
        return parse(proc.stdout), record

    def submit(self, bundle_path):
        self.check_assets()
        bundle = read(bundle_path)
        need(set(bundle) == {'request', 'files'}, 'bundle_schema')
        req, files = bundle['request'], bundle['files']
        self.policy(req)
        need(set(files) == {*NAMES, 'proof', 'rows', 'source_event'}, 'bundle_artifact_roles')
        db = connection(self.root)
        try:
            old = self.prior(db, req)
            if old is not None:
                return old
            self.current_parent(self.head(db)['head'], req)
        finally:
            db.close()
        self.root.joinpath('staging').mkdir(exist_ok=True, mode=0o700)
        with tempfile.TemporaryDirectory(prefix='update-', dir=self.root / 'staging') as temporary:
            stage = Path(temporary)
            pinned = {}
            for name in NAMES:
                raw = regular_bytes(files[name])
                header(raw, self.genesis['declared_key_id'])
                need(sha(raw) == req['payloads'][name], 'ciphertext_payload_hash')
                write(stage / f'{name}.ct', raw)
                pinned[req['payloads'][name]] = raw
            for name, field, target in [('proof', 'proof_sha256', 'proof.bin'), ('rows', 'public_rows_sha256', 'submitted_rows.json'),
                                         ('source_event', 'source_event_sha256', 'source_event.json')]:
                raw = regular_bytes(files[name])
                need(sha(raw) == req[field], 'submitted_artifact_hash:' + name)
                write(stage / target, raw)
                pinned[req[field]] = raw
            origin = read(stage / 'source_event.json')
            need(origin['schema'] == 'useful-prototype-expiry-proof-join-v1'
                 and origin['event'] == req['learner_event'] and origin['prior_state_event'] == req['parent_learner_event']
                 and origin['class'] == req['learner_class'], 'learner_event_binding')
            need(all(origin['files'][name]['sha256'] == req['payloads'][name] for name in NAMES), 'learner_event_payload_binding')
            generated, export_record = self.native(['export-update-ntt', str(stage)], stage, 'native_ciphertext_reader_refused')
            rows = regular_bytes(stage / 'public_ntt_rows.json')
            need(generated['rows'] == 8192 and generated['public_tuple_width'] == 57 and generated['basis_conversion'] is False,
                 'native_public_row_shape')
            need(sha(rows) == generated['public_rows_sha256'] == req['public_rows_sha256']
                 and rows == pinned[req['public_rows_sha256']], 'ciphertext_to_public_rows_binding')
            accepted, proof_record = self.native(['verify-update', str(self.template), str(stage), str(stage / 'proof.bin')],
                                                  stage, 'native_proof_rejected')
            need(accepted['verified'] is True and accepted['changed_output_claim_rejected'] is False
                 and accepted['proof_sha256'] == req['proof_sha256'], 'actual_native_proof_acceptance')
            self.check_assets()
            for name in NAMES:
                need(sha(regular_bytes(stage / f'{name}.ct')) == req['payloads'][name], 'staged_payload_changed')
            need(sha(regular_bytes(stage / 'proof.bin')) == req['proof_sha256'] and sha(regular_bytes(stage / 'public_ntt_rows.json')) == req['public_rows_sha256'], 'staged_statement_changed')
            db = connection(self.root)
            try:
                db.execute('BEGIN IMMEDIATE')
                old = self.prior(db, req)
                if old is not None:
                    db.execute('ROLLBACK')
                    return old
                state = self.head(db)['head']
                self.current_parent(state, req)  # Authoritative check after proof, under write lock.
                for h, raw in pinned.items():
                    path = self.root / 'cas' / h
                    if path.exists():
                        need(self.cas(h) == raw, 'immutable_cas_conflict')
                    else:
                        write(path, raw)
                receipt = {'schema': 'proved-multiclass-expiry-receipt-v1', 'revision': state['revision'] + 1,
                           'request': req, 'binding_sha256': digest(req), 'next_acc_sha256': req['payloads']['out'],
                           'changed_class': req['learner_class'], 'previous_model_root': state['model_root'],
                           'next_model_root': model_root(replace_class(state['classes'], req)),
                           'proof_acceptance': accepted, 'public_rows_reader': generated,
                           'native_verifier_sha256': self.genesis['native_verifier_sha256'],
                           'native_commands': [export_record, proof_record], 'parent_checked_inside_commit': True}
                receipt_hash = digest(receipt)
                new = self.next_state(state, req, receipt_hash)
                db.execute('INSERT INTO journal VALUES(?,?,?,?,?)', (new['revision'], req['request_id'], digest(req), canonical(receipt).decode(), receipt_hash))
                db.execute('UPDATE head SET state=?,state_sha256=? WHERE singleton=1', (canonical(new).decode(), digest(new)))
                db.execute('COMMIT')
                return {'ok': True, 'status': 'accepted', 'receipt': receipt, 'receipt_sha256': receipt_hash, 'proof_reexecuted': True}
            except BaseException:
                if db.in_transaction:
                    db.execute('ROLLBACK')
                raise
            finally:
                db.close()

    def dispatch(self, request):
        self.check_assets()
        need(isinstance(request, dict), 'rpc_object')
        if set(request) == {'op'} and request['op'] == 'head':
            return self.head()
        if set(request) == {'op'} and request['op'] == 'history':
            db = connection(self.root)
            try:
                return {'ok': True, 'genesis': self.gid, 'receipts': [parse(row[0]) for row in db.execute('SELECT receipt FROM journal ORDER BY revision')]}
            finally:
                db.close()
        if set(request) == {'op', 'bundle'} and request['op'] == 'submit':
            return self.submit(request['bundle'])
        raise Refused('unknown_rpc_operation')


def request_bundle(root, case, proof, request_id, output):
    service = Service(root)
    head = service.head()
    origin = read(Path(case) / 'source_event.json')
    files = {name: str((Path(case) / f'{name}.ct').resolve()) for name in NAMES}
    files.update(proof=str(Path(proof).resolve()), rows=str((Path(case) / 'public_ntt_rows.json').resolve()),
                 source_event=str((Path(case) / 'source_event.json').resolve()))
    request = {'schema': 'proved-multiclass-expiry-request-v1', 'request_id': request_id, 'genesis': service.gid,
               'parent_revision': head['head']['revision'], 'parent_sha256': head['head_sha256'],
               'recipient_id': service.genesis['recipient_id'], 'template_sha256': service.genesis['approved_template_sha256'],
               'randomness_rule_sha256': digest(service.genesis['randomness_rule']),
               'payloads': {name: sha(regular_bytes(files[name])) for name in NAMES},
               'public_rows_sha256': sha(regular_bytes(files['rows'])), 'proof_sha256': sha(regular_bytes(files['proof'])),
               'source_event_sha256': sha(regular_bytes(files['source_event'])), 'learner_class': origin['class'],
               'parent_learner_event': origin['prior_state_event'], 'learner_event': origin['event'],
               'parent_model_root': head['head']['model_root']}
    request['next_model_root'] = model_root(replace_class(head['head']['classes'], request))
    service.policy(request)
    write_json(output, {'request': request, 'files': files})
    return {'ok': True, 'bundle': str(output), 'request_sha256': digest(request)}


def rpc(address, request):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
        client.settimeout(90)
        client.connect(str(address))
        client.sendall(canonical(request) + b'\n')
        with client.makefile('rb') as stream:
            return parse(stream.readline(4_000_001))


def serve(root, address):
    service = Service(root)
    class Handler(socketserver.StreamRequestHandler):
        def handle(self):
            try:
                self.connection.settimeout(35)
                raw = self.rfile.readline(1_000_001)
                need(len(raw) <= 1_000_000 and raw.endswith(b'\n'), 'rpc_frame')
                result = service.dispatch(parse(raw))
            except Refused as error:
                result = {'ok': False, 'code': error.code, 'evidence': error.evidence}
            except Exception as error:
                result = {'ok': False, 'code': 'invalid_request_or_io', 'error_type': type(error).__name__}
            self.wfile.write(canonical(result) + b'\n')
    class Server(socketserver.ThreadingUnixStreamServer):
        daemon_threads = False
    need(not Path(address).exists(), 'fresh_socket_path')
    stop = threading.Event()
    signal.signal(signal.SIGTERM, lambda *_: stop.set())
    signal.signal(signal.SIGINT, lambda *_: stop.set())
    with Server(str(address), Handler) as server:
        server.timeout = 0.25
        os.chmod(address, 0o600)
        print(json.dumps({'ok': True, 'ready': True, 'genesis': service.gid}), flush=True)
        try:
            while not stop.is_set():
                server.handle_request()
        finally:
            Path(address).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    init = sub.add_parser('init')
    for name in ('root', 'binary', 'template', 'checkpoint', 'initial-files'):
        init.add_argument('--' + name, type=Path, required=True)
    for name in ('recipient', 'expected-binary-sha256', 'expected-template-sha256'):
        init.add_argument('--' + name, required=True)
    for name in ('head', 'history', 'submit', 'serve', 'request'):
        command = sub.add_parser(name)
        command.add_argument('--root', type=Path, required=True)
        if name == 'submit':
            command.add_argument('--bundle', type=Path, required=True)
        if name == 'serve':
            command.add_argument('--socket', required=True)
        if name == 'request':
            for flag in ('case', 'proof', 'out'):
                command.add_argument('--' + flag, type=Path, required=True)
            command.add_argument('--request-id', required=True)
    call = sub.add_parser('rpc')
    call.add_argument('--socket', required=True)
    call.add_argument('--request', type=Path, required=True)
    args = parser.parse_args()
    if args.command == 'init':
        result = initialize(args.root, args.binary, args.template, args.checkpoint, args.initial_files, args.recipient,
                            args.expected_binary_sha256, args.expected_template_sha256)
    elif args.command == 'request':
        result = request_bundle(args.root, args.case, args.proof, args.request_id, args.out)
    elif args.command == 'serve':
        return serve(args.root, args.socket)
    elif args.command == 'rpc':
        result = rpc(args.socket, read(args.request))
    else:
        request = {'op': args.command}
        if args.command == 'submit':
            request['bundle'] = str(args.bundle.resolve())
        result = Service(args.root).dispatch(request)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Refused as error:
        print(json.dumps({'ok': False, 'code': error.code, 'evidence': error.evidence}, sort_keys=True))
        sys.exit(2)
