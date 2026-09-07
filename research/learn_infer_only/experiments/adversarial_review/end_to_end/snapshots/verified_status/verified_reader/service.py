#!/usr/bin/env python3
"""Benchmark R: public-history verification before trusted scalar release.

The full BFV reader secret still exists. This service changes which authority
claims it trusts; it does not instantiate a masterless decryption capability.
"""
from __future__ import annotations
import argparse
import base64
import json
import os
from pathlib import Path
import socketserver
import sys

HERE = Path(__file__).resolve().parent
JOURNAL = HERE.parent / 'journal'
sys.path.insert(0, str(JOURNAL))
from common import (CAS, Refusal, canonical, digest, exact_keys, initial_state,
                    integer, read_json, require, sha, validate_state, verify)
from authority import connect
from model import check_request, transition
from reader import Reader


def equal_bytes(left, right, reason):
    require(canonical(left) == canonical(right), reason)


def strict_message(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicateJSONKey')
            result[key] = value
        return result

    def no_float(value):
        raise Refusal('nonIntegerJSONNumber')

    return json.loads(raw, object_pairs_hook=pairs, parse_float=no_float,
                      parse_constant=no_float)


class VerifiedReader(Reader):
    def __init__(self, config):
        require(config.get('verified_reader_source_sha256') ==
                sha(Path(__file__).read_bytes()), 'verifiedReaderSourcePin')
        super().__init__(config)
        with connect(self.cfg['db']) as db:
            db.execute('''CREATE TABLE IF NOT EXISTS verified_head (
                singleton INTEGER PRIMARY KEY CHECK(singleton=1),
                genesis TEXT NOT NULL, revision INTEGER NOT NULL,
                state TEXT NOT NULL, state_digest TEXT NOT NULL)''')
            db.execute('''CREATE TABLE IF NOT EXISTS verified_journal (
                revision INTEGER PRIMARY KEY, request_id TEXT UNIQUE NOT NULL,
                nonce TEXT UNIQUE NOT NULL, record_id TEXT UNIQUE,
                kind TEXT NOT NULL, envelope TEXT NOT NULL,
                envelope_sha256 TEXT NOT NULL)''')
            row = db.execute('SELECT * FROM verified_head').fetchone()
            if row is None:
                state = initial_state(self.g)
                db.execute('INSERT INTO verified_head VALUES(1,?,?,?,?)',
                           (digest(self.g), 0, canonical(state).decode(), digest(state)))
            else:
                require(row['genesis'] == digest(self.g), 'verifiedReaderGenesis')

    def sync(self, envelope):
        payload = verify(envelope, self.g['authority_vk'],
                         'resident-authority-finalization-v1')
        exact_keys(payload, ['schema', 'request', 'request_sha256', 'revision',
                            'parent_state', 'next_state', 'delta', 'output_ct'],
                   'finalizationFields')
        require(payload['schema'] == 'resident-finalized-v1', 'finalizationSchema')
        request = payload['request']
        exact_keys(request, ['schema', 'action', 'authorization', 'proposal'],
                   'requestFields')
        action = request['action']
        require(isinstance(action, dict) and
                isinstance(action.get('request_id'), str), 'requestIdentifier')
        encoded = canonical(envelope).decode()
        db = connect(self.cfg['db'])
        try:
            db.execute('BEGIN IMMEDIATE')
            prior = db.execute('SELECT * FROM verified_journal WHERE request_id=?',
                               (action['request_id'],)).fetchone()
            if prior is not None:
                require(prior['envelope'] == encoded, 'verifiedRequestConflict')
                db.execute('COMMIT')
                return {'ok': True, 'status': 'verifiedReplay',
                        'revision': prior['revision'],
                        'envelope_sha256': prior['envelope_sha256']}

            check_request(request, self.g, self.cas)
            # Bind exact signed JSON, independently of Python numeric aliases.
            equal_bytes(request['authorization']['payload'], action,
                        'exactSignedAction')
            require(integer(action['program_version']) and
                    action['program_version'] == 1, 'programVersionType')
            if action['kind'] == 'Learn':
                equal_bytes(action['range_assertion'], [-127, 127], 'rangeAssertionType')
            require(integer(payload['revision']), 'finalizedRevisionType')
            head = db.execute('SELECT * FROM verified_head').fetchone()
            require(action['parent_revision'] == head['revision'] and
                    action['parent_state'] == head['state_digest'], 'verifiedStaleParent')
            require(payload['revision'] == head['revision'] + 1, 'verifiedRevision')
            require(payload['parent_state'] == head['state_digest'], 'verifiedParentState')
            require(payload['request_sha256'] == digest(request), 'verifiedRequestDigest')
            require(db.execute('SELECT 1 FROM verified_journal WHERE nonce=?',
                               (action['nonce'],)).fetchone() is None,
                    'verifiedNonceConsumed')
            if action['kind'] == 'Learn':
                require(db.execute('SELECT 1 FROM verified_journal WHERE record_id=?',
                                   (action['record_id'],)).fetchone() is None,
                        'verifiedInputConsumed')
            state = json.loads(head['state'])
            require(validate_state(state, self.g, self.cas) == head['state_digest'],
                    'verifiedStoredStateDigest')
            new, delta, proposal = transition(state, action, self.g, self.cas)
            equal_bytes(request['proposal'], proposal, 'verifiedArithmeticProposal')
            equal_bytes(payload['delta'], delta, 'verifiedArithmeticDelta')
            require(payload['next_state'] == digest(new), 'verifiedNextState')
            output = proposal['result_ct'] if action['kind'] == 'Infer' else None
            require(payload['output_ct'] == output, 'verifiedSelectedOutput')
            db.execute('''INSERT INTO verified_journal VALUES(?,?,?,?,?,?,?)''',
                       (payload['revision'], action['request_id'], action['nonce'],
                        action.get('record_id'), action['kind'], encoded, digest(envelope)))
            db.execute('UPDATE verified_head SET revision=?,state=?,state_digest=? WHERE singleton=1',
                       (payload['revision'], canonical(new).decode(), digest(new)))
            db.execute('COMMIT')
            return {'ok': True, 'status': 'verified', 'revision': payload['revision'],
                    'state_digest': digest(new), 'envelope_sha256': digest(envelope)}
        finally:
            if db.in_transaction:
                db.execute('ROLLBACK')
            db.close()

    def receive(self, envelope, raw):
        # A stored accepted record is immutable under the reader persistence
        # assumption. Later commits do not invalidate this exact release.
        encoded = canonical(envelope).decode()
        with connect(self.cfg['db']) as db:
            row = db.execute('SELECT kind,envelope FROM verified_journal WHERE envelope_sha256=?',
                             (digest(envelope),)).fetchone()
        require(row is not None and row['envelope'] == encoded, 'unverifiedFinalization')
        require(row['kind'] == 'Infer', 'verifiedReaderOnlyInfer')
        return super().receive(envelope, raw)

    def handle(self, message):
        require(isinstance(message, dict), 'messageObject')
        op = message.get('op')
        if op == 'put':
            exact_keys(message, ['op', 'kind', 'sha256', 'data'])
            raw = base64.b64decode(message['data'], validate=True)
            return {'ok': True, 'sha256': self.cas.put(raw, message['kind'], message['sha256'])}
        if op == 'sync':
            exact_keys(message, ['op', 'envelope'])
            return self.sync(message['envelope'])
        if op == 'verified_status':
            exact_keys(message, ['op'])
            with connect(self.cfg['db']) as db:
                db.execute('BEGIN')
                head = db.execute('SELECT revision,state_digest FROM verified_head').fetchone()
                count = db.execute('SELECT count(*) FROM verified_journal').fetchone()[0]
                db.execute('COMMIT')
            return {'ok': True, 'revision': head['revision'],
                    'state_digest': head['state_digest'], 'verified_records': count}
        return super().handle(message)


class Handler(socketserver.StreamRequestHandler):
    def handle(self):
        try:
            raw = self.rfile.readline(2_000_001)
            require(len(raw) <= 2_000_000, 'requestSize')
            reply = self.server.role.handle(strict_message(raw))
        except Refusal as exc:
            reply = {'ok': False, 'reason': str(exc)}
        except Exception as exc:
            reply = {'ok': False, 'reason': 'malformed:' + type(exc).__name__}
        self.wfile.write(canonical(reply) + b'\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', required=True)
    args = parser.parse_args()
    config = read_json(args.config)
    role = VerifiedReader(config)
    address = Path(config['socket'])
    address.unlink(missing_ok=True)
    with socketserver.ThreadingUnixStreamServer(str(address), Handler) as server:
        server.daemon_threads = True
        server.role = role
        os.chmod(address, 0o600)
        server.serve_forever(poll_interval=0.1)


if __name__ == '__main__':
    main()
