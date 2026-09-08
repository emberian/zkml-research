#!/usr/bin/env python3
"""Durable restricted-ring model; COMPLETE deterministic candidate recomputation.

This is not a succinct/compiler proof. Recipient keys remain usable outside the
journal on retained inputs; local integrity/visibility is protocol TCB.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
BACKEND = REPO / 'research/learn_infer_only/experiments/end_to_end/restricted_query_learner_2026_09_08'
PROFILE = 'candidate_full'


class Refused(Exception):
    def __init__(self, code, evidence=None):
        super().__init__(code); self.code, self.evidence = code, evidence


def need(ok, code, evidence=None):
    if not ok: raise Refused(code, evidence)


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode('ascii')


def digest(x): return hashlib.sha256(canonical(x)).hexdigest()


def sha(path):
    with Path(path).open('rb') as f:
        h = hashlib.sha256()
        for chunk in iter(lambda: f.read(1 << 20), b''): h.update(chunk)
        return h.hexdigest()


def parse(raw):
    def pairs(items):
        out = {}
        for k, v in items:
            need(k not in out, 'duplicate_json_key'); out[k] = v
        return out
    return json.loads(raw, object_pairs_hook=pairs)


def read(path): return parse(Path(path).read_bytes())


def sync_dir(path):
    fd = os.open(path, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)


def write(path, value):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.atomic-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(canonical(value) + b'\n'); f.flush(); os.fsync(f.fileno())
        os.replace(temporary, path); sync_dir(path.parent)
    finally: Path(temporary).unlink(missing_ok=True)


def header(path, private=False):
    with Path(path).open('rb') as f:
        need(f.read(8) == b'RINGSEM1', 'ring_magic')
        size = int.from_bytes(f.read(4), 'big'); need(0 < size <= 16384, 'ring_header_size')
        raw = f.read(size); h = parse(raw)
    need(canonical(h) == raw and h['format_version'] == 2 and h['profile'] == PROFILE, 'canonical_ring_header')
    need(private or h['kind'] != 'key', 'orchestrator_does_not_read_keys')
    return h


def connection(root):
    db = sqlite3.connect(Path(root) / 'journal.sqlite3', isolation_level=None, timeout=30)
    db.row_factory = sqlite3.Row
    db.execute('PRAGMA journal_mode=WAL'); db.execute('PRAGMA synchronous=FULL')
    return db


def source_pins():
    saved = read(BACKEND / 'SOURCE_PINS.json')['owned']
    need(all(sha(BACKEND / p) == h for p, h in saved.items()), 'frozen_backend_source_pins')
    return {str(HERE / 'ring_service.py'): sha(HERE / 'ring_service.py'),
            **{str(BACKEND / p): h for p, h in saved.items()}}


def actor(root, name, role, arguments, deadline=None, sandbox=True):
    root = Path(root); logs = root / 'logs'; logs.mkdir(exist_ok=True)
    receipt = logs / (name + '.json')
    need(not receipt.exists(), 'fresh_actor_record')
    argv = [sys.executable, '-B', str(BACKEND / 'transport.py'), '--registry', str(root / 'registry.json'),
            '--receipt', str(receipt), *map(str, arguments)]
    if sandbox: argv = ['/usr/bin/sandbox-exec', '-f', str(root / 'profiles' / (role + '.sb')), *argv]
    limit = 180 if deadline is None else min(180, deadline - time.monotonic())
    need(limit > 0, 'bounded_run_deadline')
    started = time.monotonic_ns()
    p = subprocess.run(argv, cwd=root / 'public', capture_output=True, timeout=limit)
    (logs / (name + '.stdout')).write_bytes(p.stdout); (logs / (name + '.stderr')).write_bytes(p.stderr)
    command = {'argv': argv, 'role': role, 'exit_code': p.returncode, 'elapsed_ns': time.monotonic_ns() - started}
    write(logs / (name + '.command.json'), command)
    need(p.returncode == 0, 'ring_actor_failed', command)
    result = read(receipt)
    need(result['status'] == 'PASS' and result['registry_sha256'] == sha(root / 'registry.json'), 'ring_actor_receipt')
    private_reads = [r for r in result['artifact_reads'] if r['private']]
    private_writes = [r for r in result['artifact_writes'] if r['private']]
    if role == 'public': need(not private_reads and not private_writes, 'public_actor_private_artifact_access')
    else:
        own = root / 'private' / role
        need(all(Path(r['path']).is_relative_to(own) for r in private_reads + private_writes), 'recipient_own_private_artifacts_only')
    print(json.dumps({'actor': name, 'role': role, 'elapsed_ns': command['elapsed_ns']}), file=sys.stderr, flush=True)
    return result


def model_root(classes): return digest({'schema': 'restricted-ring-model-map-v1', 'classes': classes})


def create(root, deadline=None):
    root = Path(root).resolve(); need(not root.exists(), 'fresh_restricted_ring_instance')
    pins = source_pins(); registry = read(BACKEND / 'registry.json')
    root.mkdir(parents=True, mode=0o700)
    for name in ('public', 'private', 'profiles', 'logs', 'cas', 'proposals'): (root / name).mkdir(mode=0o700)
    shutil.copyfile(BACKEND / 'registry.json', root / 'registry.json')
    recipients = []
    for i in range(16):
        directory = root / 'private' / ('recipient_%02d' % i); directory.mkdir(mode=0o700); recipients.append(directory)
    for role in ['public'] + [d.name for d in recipients]:
        denied = [root / 'private'] if role == 'public' else [d for d in recipients if d.name != role]
        profile = '(version 1)\n(allow default)\n(deny network*)\n'
        for path in denied: profile += '(deny file-read* file-write* (subpath ' + json.dumps(str(path)) + '))\n'
        (root / 'profiles' / (role + '.sb')).write_text(profile)
    public = root / 'public'
    actor(root, 'setup_init', 'public', ['init', '--profile', PROFILE, '--out', public / 'a.ring'], deadline)
    registrations = []
    for i, directory in enumerate(recipients):
        path = public / ('registration_%02d.ring' % i)
        actor(root, 'setup_register_%02d' % i, directory.name, ['register', '--public-a', public / 'a.ring',
            '--coordinate', i, '--key-out', directory / 'key.ring', '--registration-out', path], deadline)
        h = header(path); need(h['coordinate'] == i and h['registry_sha256'] == sha(root / 'registry.json'), 'registered_coordinate')
        registrations.append({'coordinate': i, 'registration_sha256': sha(path),
            'query_sha256': digest(registry['queries'][i]), 'recipient_id': directory.name})
    arguments = ['finalize', '--public-a', public / 'a.ring', '--out', public / 'public.ring']
    for i in range(16): arguments += ['--registration', public / ('registration_%02d.ring' % i)]
    finalized = actor(root, 'setup_finalize', 'public', arguments, deadline)
    need(finalized['result']['missing_public_rows_generated_directly'] == 561 and finalized['result']['actual_private_rows_generated'] == 0, 'direct_missing_rows_no_reader')
    ph = header(public / 'public.ring')
    genesis = {'schema': 'restricted-ring-journal-genesis-v1', 'source_pins': pins, 'registry_sha256': sha(root / 'registry.json'),
        'setup_id': ph['setup_id'], 'parameters': ph['parameters'], 'profile': PROFILE,
        'a_sha256': sha(public / 'a.ring'), 'public_sha256': sha(public / 'public.ring'),
        'registrations': registrations, 'recipient_set_sha256': digest(registrations),
        'classes': registry['classes'], 'capacity': 2,
        'verification': 'Full deterministic canonical byte recomputation of acc+fresh-old in this exact ring backend; no succinct/compiler proof.',
        'randomness': 'Fresh honest recipient-local keys, honest Gaussian issuer sampling, and directly ideal-uniform missing public rows; no setup from a public seed.',
        'scope': 'Local continuity/integrity and accepted-state visibility; fixed recipient keys expose their per-input projection/span outside this journal. No cryptographic history-bound release.'}
    need(ph['a_sha256'] == genesis['a_sha256'], 'setup_A_binding')
    write(root / 'genesis.json', genesis)
    classes = {c: {'state_sha256': None, 'queue': []} for c in genesis['classes']}
    head = {'genesis': digest(genesis), 'revision': 0, 'classes': classes, 'model_root': model_root(classes), 'last_receipt_sha256': None}
    db = connection(root)
    try:
        db.execute('BEGIN IMMEDIATE')
        db.execute('CREATE TABLE head (id INTEGER PRIMARY KEY CHECK(id=1), body TEXT NOT NULL, sha256 TEXT NOT NULL)')
        db.execute('CREATE TABLE journal (revision INTEGER PRIMARY KEY, request_id TEXT UNIQUE NOT NULL, request_sha256 TEXT NOT NULL, receipt TEXT NOT NULL, receipt_sha256 TEXT NOT NULL)')
        db.execute('INSERT INTO head VALUES(1,?,?)', (canonical(head).decode(), digest(head)))
        db.execute('COMMIT')
    finally: db.close()
    return {'ok': True, 'genesis': digest(genesis), 'head': head, 'head_sha256': digest(head)}


class Service:
    def __init__(self, root, deadline=None, audit=False):
        self.root = Path(root).resolve(); self.genesis = read(self.root / 'genesis.json'); self.gid = digest(self.genesis); self.deadline = deadline
        self.check_assets()
        if audit: self.audit()

    def check_assets(self):
        need(read(self.root / 'genesis.json') == self.genesis and sha(self.root / 'registry.json') == self.genesis['registry_sha256'], 'genesis_or_registry_changed')
        need(all(sha(Path(p)) == h for p, h in self.genesis['source_pins'].items()), 'source_pin_changed')

    def head(self, db=None):
        owned = db is None; db = db or connection(self.root)
        try:
            row = db.execute('SELECT body,sha256 FROM head WHERE id=1').fetchone(); head = parse(row['body'])
            need(digest(head) == row['sha256'] and head['genesis'] == self.gid and head['model_root'] == model_root(head['classes']), 'installed_model_head')
            return {'ok': True, 'genesis': self.gid, 'head': head, 'head_sha256': row['sha256']}
        finally:
            if owned: db.close()

    def cas(self, h):
        need(isinstance(h, str) and re.fullmatch('[0-9a-f]{64}', h), 'cas_digest')
        path = self.root / 'cas' / h; need(path.is_file() and not path.is_symlink() and sha(path) == h, 'cas_object_hash')
        return path

    def install(self, source, h):
        dest = self.root / 'cas' / h
        if dest.exists(): self.cas(h); return
        fd, temporary = tempfile.mkstemp(prefix='.cas-', dir=dest.parent)
        try:
            with os.fdopen(fd, 'wb') as out, Path(source).open('rb') as inp:
                shutil.copyfileobj(inp, out, 1 << 20); out.flush(); os.fsync(out.fileno())
            need(sha(temporary) == h, 'cas_source_changed')
            os.link(temporary, dest); sync_dir(dest.parent)
        finally: Path(temporary).unlink(missing_ok=True)

    def directory(self, request_id):
        need(isinstance(request_id, str) and re.fullmatch('[A-Za-z0-9_-]{1,80}', request_id), 'request_id')
        return self.root / 'proposals' / request_id

    def next_classes(self, state, req):
        classes = {c: {'state_sha256': e['state_sha256'], 'queue': list(e['queue'])} for c, e in state['classes'].items()}
        entry = classes[req['class']]
        if len(entry['queue']) == 2: entry['queue'].pop(0)
        entry['queue'].append({'input_id': req['input_id'], 'input_sha256': req['input_sha256'], 'fresh_sha256': req['fresh_sha256'], 'revision': state['revision'] + 1})
        entry['state_sha256'] = req['candidate_sha256']
        return classes

    def binding(self, state, req):
        fields = {'schema', 'request_id', 'genesis', 'registry_sha256', 'setup_id', 'a_sha256', 'public_sha256',
                  'recipient_set_sha256', 'parent_revision', 'parent_sha256', 'parent_model_root', 'class', 'input_id',
                  'input_sha256', 'acc_sha256', 'fresh_sha256', 'expired_sha256', 'candidate_sha256', 'next_model_root'}
        need(set(req) == fields and req['schema'] == 'restricted-ring-update-request-v1', 'request_schema')
        self.directory(req['request_id'])
        need(req['genesis'] == self.gid and all(req[k] == self.genesis[k] for k in ('registry_sha256', 'setup_id', 'a_sha256', 'public_sha256', 'recipient_set_sha256')), 'setup_registry_recipient_binding')
        need(type(req['parent_revision']) is int and req['parent_revision'] == state['revision'] and req['parent_sha256'] == digest(state)
             and req['parent_model_root'] == state['model_root'], 'stale_parent')
        need(req['class'] in state['classes'] and isinstance(req['input_id'], str) and req['input_id'], 'class_input_identity')
        entry = state['classes'][req['class']]; expected_expired = entry['queue'][0]['fresh_sha256'] if len(entry['queue']) == 2 else None
        need(req['acc_sha256'] == entry['state_sha256'] and req['expired_sha256'] == expected_expired, 'class_accumulator_fifo_binding')
        hashes = [req[k] for k in ('input_sha256', 'fresh_sha256', 'candidate_sha256', 'next_model_root')]
        need(all(isinstance(h, str) and re.fullmatch('[0-9a-f]{64}', h) for h in hashes), 'request_hashes')
        need(req['next_model_root'] == model_root(self.next_classes(state, req)), 'next_model_root')

    def prepare(self, label, input_path, input_id, request_id):
        self.check_assets(); current = self.head(); state = current['head']; need(label in state['classes'], 'class')
        directory = self.directory(request_id); need(not directory.exists(), 'fresh_proposal'); directory.mkdir()
        shutil.copyfile(input_path, directory / 'input.json'); input_path = directory / 'input.json'
        fresh, candidate = directory / 'fresh.ring', directory / 'candidate.ring'
        actor(self.root, request_id + '_encode', 'public', ['encode', '--public', self.root / 'public/public.ring', '--input', input_path, '--out', fresh], self.deadline)
        fh = header(fresh)
        need(fh['kind'] == 'ciphertext' and fh['terms'] is None and all(fh[k] == self.genesis[k] for k in ('registry_sha256', 'setup_id', 'a_sha256', 'public_sha256')), 'fresh_input_context')
        entry = state['classes'][label]; expired = entry['queue'][0]['fresh_sha256'] if len(entry['queue']) == 2 else None
        arguments = ['window', '--add', fresh, '--capacity', 2, '--out', candidate]
        if entry['state_sha256']: arguments += ['--state', self.cas(entry['state_sha256'])]
        if expired: arguments += ['--expire', self.cas(expired)]
        actor(self.root, request_id + '_candidate', 'public', arguments, self.deadline)
        req = {'schema': 'restricted-ring-update-request-v1', 'request_id': request_id, 'genesis': self.gid,
               **{k: self.genesis[k] for k in ('registry_sha256', 'setup_id', 'a_sha256', 'public_sha256', 'recipient_set_sha256')},
               'parent_revision': state['revision'], 'parent_sha256': current['head_sha256'], 'parent_model_root': state['model_root'],
               'class': label, 'input_id': input_id, 'input_sha256': sha(input_path), 'acc_sha256': entry['state_sha256'],
               'fresh_sha256': sha(fresh), 'expired_sha256': expired, 'candidate_sha256': sha(candidate)}
        req['next_model_root'] = model_root(self.next_classes(state, req)); self.binding(state, req)
        bundle = {'request': req, 'files': {'input': str(input_path), 'fresh': str(fresh), 'candidate': str(candidate)}}
        write(directory / 'request.json', bundle)
        need(self.head() == current, 'parent_changed_while_preparing')
        return {'status': 'prepared_not_committed', 'bundle': str(directory / 'request.json'), 'request': req}

    def prior(self, db, req):
        row = db.execute('SELECT * FROM journal WHERE request_id=?', (req['request_id'],)).fetchone()
        if row:
            need(row['request_sha256'] == digest(req), 'request_id_conflict')
            return {'ok': True, 'status': 'replayed', 'receipt': parse(row['receipt']), 'receipt_sha256': row['receipt_sha256']}

    def submit(self, bundle_path):
        self.check_assets(); bundle = read(bundle_path); need(set(bundle) == {'request', 'files'}, 'bundle_schema'); req, files = bundle['request'], bundle['files']
        need(set(files) == {'input', 'fresh', 'candidate'}, 'artifact_roles')
        db = connection(self.root)
        try:
            old = self.prior(db, req)
            if old: return old
            state = self.head(db)['head']; self.binding(state, req)
            need(not any(parse(row[0])['request']['input_id'] == req['input_id'] for row in db.execute('SELECT receipt FROM journal')), 'input_id_already_issued')
        finally: db.close()
        for name, field in [('input', 'input_sha256'), ('fresh', 'fresh_sha256'), ('candidate', 'candidate_sha256')]:
            need(sha(files[name]) == req[field], 'submitted_artifact_hash')
        fh = header(files['fresh']); need(fh['terms'] is None and all(fh[k] == req[k] for k in ('registry_sha256', 'setup_id', 'a_sha256', 'public_sha256')), 'fresh_context')
        directory = self.directory(req['request_id']); directory.mkdir(exist_ok=True)
        recomputed = directory / 'verification.ring'; arguments = ['combine', '--out', recomputed]
        if req['acc_sha256']: arguments += ['--term', 1, self.cas(req['acc_sha256'])]
        arguments += ['--term', 1, files['fresh']]
        if req['expired_sha256']: arguments += ['--term', -1, self.cas(req['expired_sha256'])]
        receipt = actor(self.root, req['request_id'] + '_recompute', 'public', arguments, self.deadline)
        compared = 0
        with Path(files['candidate']).open('rb') as got, recomputed.open('rb') as expected:
            while True:
                a, b = got.read(1 << 20), expected.read(1 << 20); compared += len(b)
                need(a == b, 'complete_candidate_recomputation_mismatch', {'compared_bytes_through_mismatch': compared, 'expected_sha256': sha(recomputed), 'candidate_sha256': req['candidate_sha256']})
                if not b: break
        need(compared == Path(files['candidate']).stat().st_size and sha(recomputed) == req['candidate_sha256'], 'full_file_comparison')
        self.check_assets(); db = connection(self.root)
        try:
            db.execute('BEGIN IMMEDIATE'); old = self.prior(db, req)
            if old: db.execute('ROLLBACK'); return old
            state = self.head(db)['head']; self.binding(state, req)
            need(not any(parse(row[0])['request']['input_id'] == req['input_id'] for row in db.execute('SELECT receipt FROM journal')), 'input_id_already_issued')
            for name, field in [('input', 'input_sha256'), ('fresh', 'fresh_sha256'), ('candidate', 'candidate_sha256')]: self.install(files[name], req[field])
            record = {'schema': 'restricted-ring-update-receipt-v1', 'revision': state['revision'] + 1, 'request': req,
                'request_sha256': digest(req), 'changed_class': req['class'], 'previous_model_root': state['model_root'],
                'next_model_root': req['next_model_root'], 'verification': 'complete deterministic public recomputation; not a succinct/compiler proof',
                'all_candidate_bytes_equal': True, 'bytes_compared': compared, 'recomputation_receipt_sha256': sha(self.root / 'logs' / (req['request_id'] + '_recompute.json')),
                'parent_checked_inside_commit': True, 'public_actor_private_artifact_reads': 0}
            rh = digest(record); classes = self.next_classes(state, req)
            new = {'genesis': self.gid, 'revision': state['revision'] + 1, 'classes': classes, 'model_root': model_root(classes), 'last_receipt_sha256': rh}
            db.execute('INSERT INTO journal VALUES(?,?,?,?,?)', (new['revision'], req['request_id'], digest(req), canonical(record).decode(), rh))
            db.execute('UPDATE head SET body=?,sha256=? WHERE id=1', (canonical(new).decode(), digest(new))); db.execute('COMMIT')
            return {'ok': True, 'status': 'accepted', 'receipt': record, 'receipt_sha256': rh}
        except BaseException:
            if db.in_transaction: db.execute('ROLLBACK')
            raise
        finally: db.close()

    def audit(self):
        classes = {c: {'state_sha256': None, 'queue': []} for c in self.genesis['classes']}
        state = {'genesis': self.gid, 'revision': 0, 'classes': classes, 'model_root': model_root(classes), 'last_receipt_sha256': None}
        db = connection(self.root)
        try:
            db.execute('BEGIN')
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                receipt = parse(row['receipt']); req = receipt['request']
                need(digest(receipt) == row['receipt_sha256'] and digest(req) == row['request_sha256'], 'retained_receipt_identity')
                self.binding(state, req)
                need(receipt['revision'] == row['revision'] == state['revision'] + 1 and receipt['all_candidate_bytes_equal'] is True, 'retained_verified_transition')
                for field in ('input_sha256', 'fresh_sha256', 'candidate_sha256'): self.cas(req[field])
                classes = self.next_classes(state, req)
                state = {'genesis': self.gid, 'revision': state['revision'] + 1, 'classes': classes, 'model_root': model_root(classes), 'last_receipt_sha256': row['receipt_sha256']}
            need(self.head(db)['head'] == state, 'reopened_exact_model_head'); db.execute('COMMIT')
        finally: db.close()

    def publish(self):
        self.check_assets(); current = self.head(); state = current['head']
        need(all(e['state_sha256'] and 1 <= len(e['queue']) <= 2 for e in state['classes'].values()), 'populated_accepted_classes')
        models = {'registry_sha256': self.genesis['registry_sha256'], 'capacity': 2,
            'snapshots': [{'revision': state['revision'], 'classes': {c: {'path': str(self.cas(e['state_sha256'])), 'sha256': e['state_sha256'], 'count': len(e['queue'])} for c, e in state['classes'].items()}}],
            'service_binding': {'genesis': self.gid, 'head_sha256': current['head_sha256'], 'model_root': state['model_root'], 'recipient_set_sha256': self.genesis['recipient_set_sha256']}}
        path = self.root / 'public' / ('accepted_model_%06d.json' % state['revision']); need(not path.exists(), 'fresh_published_model')
        write(path, models); need(self.head() == current, 'head_changed_before_publication')
        return {'ok': True, 'head': current, 'models': str(path), 'models_sha256': sha(path)}


def recipient(root, coordinate, models_path, output):
    service = Service(root); current = service.head(); models = read(models_path); g = service.genesis
    need(type(coordinate) is int and 0 <= coordinate < 16, 'registered_recipient_coordinate')
    registration = g['registrations'][coordinate]
    need(registration['coordinate'] == coordinate, 'registered_recipient_identity')
    path = service.root / 'public' / ('registration_%02d.ring' % coordinate)
    need(sha(path) == registration['registration_sha256'], 'retained_registration')
    need(models['service_binding'] == {'genesis': service.gid, 'head_sha256': current['head_sha256'], 'model_root': current['head']['model_root'], 'recipient_set_sha256': g['recipient_set_sha256']}, 'recipient_current_accepted_head')
    snap = models['snapshots']; need(len(snap) == 1 and snap[0]['revision'] == current['head']['revision'], 'accepted_snapshot_revision')
    expected = {c: {'path': str(service.root / 'cas' / e['state_sha256']), 'sha256': e['state_sha256'], 'count': len(e['queue'])} for c, e in current['head']['classes'].items()}
    need(snap[0]['classes'] == expected, 'recipient_exact_accepted_class_states')
    role = 'recipient_%02d' % coordinate; key = service.root / 'private' / role / 'key.ring'
    kh = header(key, private=True)
    need(kh['coordinate'] == coordinate and all(kh[k] == g[k] for k in ('setup_id', 'registry_sha256', 'a_sha256')), 'recipient_own_registered_key_context')
    result = actor(service.root, role + '_query_transport', role, ['query', '--key', key, '--models', models_path], sandbox=False)
    need(result['result']['recipient_coordinate'] == coordinate, 'recipient_query_coordinate')
    record = {'ok': True, 'recipient_id': role, 'coordinate': coordinate, 'registration_sha256': registration['registration_sha256'],
        'genesis': service.gid, 'accepted_head_sha256': current['head_sha256'], 'models_sha256': sha(models_path),
        'registry_sha256': g['registry_sha256'], 'private_rows_read': result['result']['private_rows_read'],
        'query_results': result['result']['query_results'],
        'scope': 'Service delivered only its current accepted model. This fixed key also works on retained inputs outside the service; no cryptographic history-bound release.'}
    write(output, record); return record


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='command', required=True)
    for name in ('init', 'head', 'audit', 'prepare', 'submit', 'publish', 'receive'):
        cmd = sub.add_parser(name); cmd.add_argument('--root', type=Path, required=True)
        if name == 'prepare':
            cmd.add_argument('--class', dest='label', required=True); cmd.add_argument('--input', type=Path, required=True)
            cmd.add_argument('--input-id', required=True); cmd.add_argument('--request-id', required=True)
        if name == 'submit': cmd.add_argument('--bundle', type=Path, required=True)
        if name == 'receive':
            cmd.add_argument('--coordinate', type=int, required=True); cmd.add_argument('--models', type=Path, required=True); cmd.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    if a.command == 'init': result = create(a.root)
    elif a.command == 'receive': result = recipient(a.root, a.coordinate, a.models, a.out)
    else:
        service = Service(a.root, audit=a.command == 'audit')
        if a.command in ('head', 'audit'): result = service.head()
        elif a.command == 'prepare': result = service.prepare(a.label, a.input, a.input_id, a.request_id)
        elif a.command == 'submit': result = service.submit(a.bundle)
        else: result = service.publish()
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try: main()
    except Refused as e:
        print(json.dumps({'ok': False, 'code': e.code, 'evidence': e.evidence}), file=sys.stderr); raise SystemExit(2)
