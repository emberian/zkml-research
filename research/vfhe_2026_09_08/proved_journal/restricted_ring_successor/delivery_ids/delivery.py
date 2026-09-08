#!/usr/bin/env python3
"""Additive request/delivery IDs over the frozen accepted-ring model service."""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import ring_service as s

def identifier(value):
    s.need(type(value) is str and re.fullmatch('[A-Za-z0-9_-]{1,80}', value), 'delivery_identifier')
    return value

def once(path, value):
    path = Path(path)
    with path.open('xb') as stream:
        stream.write(s.canonical(value) + b'\n'); stream.flush(); os.fsync(stream.fileno())
    s.sync_dir(path.parent)

def head_readonly(root):
    db = sqlite3.connect((Path(root).resolve() / 'journal.sqlite3').as_uri() + '?mode=ro', uri=True)
    try:
        row = db.execute('SELECT body,sha256 FROM head WHERE id=1').fetchone()
        head = s.parse(row[0]); s.need(s.digest(head) == row[1], 'delivery_head_hash')
        return {'ok': True, 'genesis': head['genesis'], 'head': head, 'head_sha256': row[1]}
    finally: db.close()

def connection(root):
    directory = Path(root) / 'deliveries'; directory.mkdir(exist_ok=True)
    db = sqlite3.connect(directory / 'deliveries.sqlite3', isolation_level=None, timeout=30)
    db.row_factory = sqlite3.Row
    db.execute('PRAGMA journal_mode=WAL'); db.execute('PRAGMA synchronous=FULL')
    db.execute('''CREATE TABLE IF NOT EXISTS deliveries (
        request_id TEXT PRIMARY KEY, delivery_id TEXT UNIQUE NOT NULL,
        request_sha256 TEXT NOT NULL, request TEXT NOT NULL,
        status TEXT NOT NULL, receipt TEXT, receipt_sha256 TEXT)''')
    return db

def make_request(root, coordinate, request_id, delivery_id, models_path):
    service = s.Service(root); current = head_readonly(root)
    s.need(type(coordinate) is int and 0 <= coordinate < 16, 'registered_recipient_coordinate')
    registration = service.genesis['registrations'][coordinate]
    request = {'schema': 'restricted-ring-delivery-request-v1',
        'request_id': identifier(request_id), 'delivery_id': identifier(delivery_id),
        'coordinate': coordinate, 'genesis': service.gid,
        'registry_sha256': service.genesis['registry_sha256'],
        'recipient_set_sha256': service.genesis['recipient_set_sha256'],
        'registration_sha256': registration['registration_sha256'],
        'query_sha256': registration['query_sha256'],
        'accepted_revision': current['head']['revision'],
        'accepted_head_sha256': current['head_sha256'],
        'model_root': current['head']['model_root'],
        'models_path': str(Path(models_path).resolve()), 'models_sha256': s.sha(models_path)}
    validate_request(service, request)
    return request

FIELDS = {'schema','request_id','delivery_id','coordinate','genesis','registry_sha256',
          'recipient_set_sha256','registration_sha256','query_sha256','accepted_revision',
          'accepted_head_sha256','model_root','models_path','models_sha256'}

def validate_identity(service, request):
    s.need(set(request) == FIELDS and request['schema'] == 'restricted-ring-delivery-request-v1', 'delivery_request_schema')
    identifier(request['request_id']); identifier(request['delivery_id'])
    coordinate = request['coordinate']; g = service.genesis
    s.need(type(coordinate) is int and 0 <= coordinate < 16, 'registered_recipient_coordinate')
    s.need(request['genesis'] == service.gid and all(request[k] == g[k] for k in ('registry_sha256','recipient_set_sha256')), 'delivery_genesis_registry')
    registration = g['registrations'][coordinate]
    s.need(registration['coordinate'] == coordinate and all(request[k] == registration[k] for k in ('registration_sha256','query_sha256')), 'delivery_registered_policy')
    s.need(type(request['accepted_revision']) is int and request['accepted_revision'] > 0, 'delivery_revision')
    for key in ('accepted_head_sha256','model_root','models_sha256'):
        s.need(type(request[key]) is str and re.fullmatch('[0-9a-f]{64}', request[key]), 'delivery_digest')
    s.need(type(request['models_path']) is str and Path(request['models_path']).is_absolute(), 'delivery_models_path')
    return coordinate, registration

def validate_request(service, request):
    coordinate, registration = validate_identity(service, request)
    current = head_readonly(service.root); g = service.genesis
    s.need(current['head']['genesis'] == service.gid and current['head']['model_root'] == s.model_root(current['head']['classes']), 'delivery_installed_head')
    s.need(request['accepted_revision'] == current['head']['revision'] and request['accepted_head_sha256'] == current['head_sha256']
           and request['model_root'] == current['head']['model_root'], 'delivery_not_current_head')
    path = service.root / 'public' / ('registration_%02d.ring' % coordinate)
    s.need(s.sha(path) == registration['registration_sha256'], 'delivery_retained_registration')
    models_path = Path(request['models_path'])
    s.need(s.sha(models_path) == request['models_sha256'], 'delivery_models_changed')
    models = s.read(models_path)
    s.need(set(models) == {'registry_sha256','capacity','snapshots','service_binding'}, 'delivery_models_schema')
    s.need(models['registry_sha256'] == g['registry_sha256'] and models['capacity'] == g['capacity'], 'delivery_models_registry')
    s.need(models['service_binding'] == {'genesis': service.gid, 'head_sha256': current['head_sha256'],
        'model_root': current['head']['model_root'], 'recipient_set_sha256': g['recipient_set_sha256']}, 'delivery_model_head_binding')
    expected = {c: {'path': str(service.cas(e['state_sha256'])), 'sha256': e['state_sha256'], 'count': len(e['queue'])}
                for c,e in current['head']['classes'].items()}
    s.need(models['snapshots'] == [{'revision': current['head']['revision'], 'classes': expected}], 'delivery_exact_accepted_classes')
    return current

def recipient_worker(root, request_path, outdir):
    # This function executes ONLY in the recipient's existing sandbox profile.
    # Its only private file is that recipient's existing registered key.
    service = s.Service(root); request = s.read(request_path)
    current = validate_request(service, request)
    config = s.read(service.root / 'delivery_credentials.json')
    s.need(config['genesis'] == service.gid, 'delivery_credential_genesis')
    coordinate = request['coordinate']; role = 'recipient_%02d' % coordinate
    credential_root = Path(config['credential_root']).resolve()
    key = credential_root / 'private' / role / 'key.ring'
    kh = s.header(key, private=True)
    s.need(kh['coordinate'] == coordinate and all(kh[k] == service.genesis[k] for k in ('setup_id','registry_sha256','a_sha256')), 'delivery_own_key_context')
    outdir = Path(outdir)
    actor_receipt = outdir / 'transport.json'
    s.need(not actor_receipt.exists(), 'fresh_delivery_actor_record')
    argv = [sys.executable, '-B', str(s.BACKEND / 'transport.py'), '--registry', str(service.root / 'registry.json'),
            '--receipt', str(actor_receipt), 'query', '--key', str(key), '--models', request['models_path']]
    started = time.monotonic_ns()
    proc = subprocess.run(argv, capture_output=True, timeout=180)
    (outdir / 'transport.stdout').write_bytes(proc.stdout); (outdir / 'transport.stderr').write_bytes(proc.stderr)
    once(outdir / 'transport.command.json', {'argv': argv, 'exit_code': proc.returncode,
         'elapsed_ns': time.monotonic_ns() - started, 'role': role})
    s.need(proc.returncode == 0, 'delivery_transport_failed')
    receipt = s.read(actor_receipt)
    s.need(receipt['status'] == 'PASS' and receipt['registry_sha256'] == service.genesis['registry_sha256'], 'delivery_actor_receipt')
    private_reads = [r for r in receipt['artifact_reads'] if r['private']]
    s.need(len(private_reads) == 1 and Path(private_reads[0]['path']) == key, 'delivery_own_key_only')
    s.need(not any(r['private'] for r in receipt['artifact_writes']), 'delivery_no_private_writes')
    s.need(receipt['result']['recipient_coordinate'] == coordinate and receipt['result']['private_rows_read'] == 1, 'delivery_coordinate_output')
    s.need(head_readonly(root) == current, 'delivery_head_changed_during_read')
    result = {'schema': 'restricted-ring-delivery-receipt-v1', 'request': request,
        'request_sha256': s.digest(request), 'delivery_id': request['delivery_id'],
        'recipient_id': role, 'coordinate': coordinate, 'accepted_head_sha256': current['head_sha256'],
        'accepted_revision': current['head']['revision'], 'actor_receipt_sha256': s.sha(actor_receipt),
        'private_rows_read': 1, 'query_results': receipt['result']['query_results'],
        'scope': 'Current accepted-head delivery by local service; fixed key remains usable on retained inputs outside it.'}
    once(outdir / 'recipient.json', result)
    return result

def deliver(root, request):
    service = s.Service(root); validate_identity(service, request)
    db = connection(root)
    journal = s.connection(root)
    try:
        # Hold the original journal writer lock across validation and recipient
        # execution. Cooperative submit/import commits cannot change the head.
        journal.execute('BEGIN IMMEDIATE')
        db.execute('BEGIN IMMEDIATE')
        by_request = db.execute('SELECT * FROM deliveries WHERE request_id=?', (request['request_id'],)).fetchone()
        by_delivery = db.execute('SELECT * FROM deliveries WHERE delivery_id=?', (request['delivery_id'],)).fetchone()
        if by_request or by_delivery:
            old = by_request or by_delivery
            s.need(old['request_sha256'] == s.digest(request) and old['request'] == s.canonical(request).decode(), 'delivery_id_or_request_conflict')
            s.need(old['status'] == 'complete', 'delivery_incomplete_no_automatic_reexecution', {'status': old['status']})
            result = s.parse(old['receipt']); s.need(s.digest(result) == old['receipt_sha256'], 'retained_delivery_receipt_hash')
            db.execute('COMMIT'); journal.execute('ROLLBACK')
            return {'status': 'replayed', 'receipt': result, 'receipt_sha256': old['receipt_sha256'], 'new_private_actor_invocations': 0}
        current = validate_request(service, request)
        outdir = service.root / 'deliveries' / request['delivery_id']
        s.need(not outdir.exists(), 'fresh_delivery_directory'); outdir.mkdir()
        once(outdir / 'request.json', request)
        once(outdir / 'PUBLIC_VALIDATED.json', {'request_sha256': s.digest(request), 'current_head': current,
             'private_artifact_reads': 0, 'recipient_started': False, 'monotonic_ns': time.monotonic_ns(), 'pid': os.getpid()})
        db.execute('INSERT INTO deliveries VALUES(?,?,?,?,?,?,?)', (request['request_id'], request['delivery_id'],
            s.digest(request), s.canonical(request).decode(), 'running', None, None))
        db.execute('COMMIT')
        config = s.read(service.root / 'delivery_credentials.json'); s.need(config['genesis'] == service.gid, 'delivery_credential_genesis')
        role = 'recipient_%02d' % request['coordinate']
        profile = Path(config['credential_root']) / 'profiles' / (role + '.sb')
        argv = ['/usr/bin/sandbox-exec', '-f', str(profile), sys.executable, '-B', str(Path(__file__).resolve()),
                'worker', '--root', str(service.root), '--request', str(outdir / 'request.json'), '--outdir', str(outdir)]
        started = time.monotonic_ns()
        process = subprocess.run(argv, capture_output=True, timeout=180)
        (outdir / 'worker.stdout').write_bytes(process.stdout); (outdir / 'worker.stderr').write_bytes(process.stderr)
        once(outdir / 'worker.command.json', {'argv': argv, 'exit_code': process.returncode, 'elapsed_ns': time.monotonic_ns()-started})
        s.need(process.returncode == 0, 'delivery_recipient_worker_failed')
        result = s.read(outdir / 'recipient.json')
        s.need(result['request'] == request and result['request_sha256'] == s.digest(request), 'delivery_worker_request_binding')
        s.need(head_readonly(root) == current, 'delivery_head_changed_before_retention')
        once(outdir / 'receipt.json', result)
        db.execute('BEGIN IMMEDIATE')
        db.execute('UPDATE deliveries SET status=?,receipt=?,receipt_sha256=? WHERE request_id=? AND status=?',
                   ('complete', s.canonical(result).decode(), s.digest(result), request['request_id'], 'running'))
        db.execute('COMMIT'); journal.execute('ROLLBACK')
        return {'status': 'delivered', 'receipt': result, 'receipt_sha256': s.digest(result), 'new_private_actor_invocations': 1}
    finally:
        if db.in_transaction: db.execute('ROLLBACK')
        if journal.in_transaction: journal.execute('ROLLBACK')
        db.close(); journal.close()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('request', 'deliver', 'worker'):
        cmd = sub.add_parser(name); cmd.add_argument('--root', type=Path, required=True)
        if name == 'request':
            cmd.add_argument('--coordinate', type=int, required=True); cmd.add_argument('--request-id', required=True)
            cmd.add_argument('--delivery-id', required=True); cmd.add_argument('--models', type=Path, required=True)
        else: cmd.add_argument('--request', type=Path, required=True)
        if name == 'worker': cmd.add_argument('--outdir', type=Path, required=True)
    args = parser.parse_args()
    if args.command == 'request': result = make_request(args.root, args.coordinate, args.request_id, args.delivery_id, args.models)
    elif args.command == 'deliver': result = deliver(args.root, s.read(args.request))
    else: result = recipient_worker(args.root, args.request, args.outdir)
    print(s.canonical(result).decode())

if __name__ == '__main__':
    try: main()
    except s.Refused as error:
        print(s.canonical({'ok': False, 'code': error.code, 'evidence': error.evidence}).decode(), file=sys.stderr)
        raise SystemExit(2)
