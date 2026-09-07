#!/usr/bin/env python3
"""One-command real-BFV verified-reader experiment; all secrets stay in runtime/.

The outer process freezes the imported source tree before launching this same
driver from the snapshot. No shared source is edited by an experiment.
"""
from __future__ import annotations
import argparse
import base64
import collections
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import sqlite3
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
MODULES = ['common.py', 'model.py', 'roles.py', 'authority.py', 'reader.py', 'run.py']


def hexdigest(raw):
    return hashlib.sha256(raw).hexdigest()


def freeze(args):
    runtime = Path(args.runtime).resolve()
    report = Path(args.report).resolve()
    runtime.mkdir(parents=True, exist_ok=False)
    os.chmod(runtime, 0o700)
    report.mkdir(parents=True, exist_ok=False)
    stage = runtime / 'e2e'
    for name in ['journal', 'verified_reader']:
        (stage / name).mkdir(parents=True)
    pins = {}
    for name in MODULES:
        src = HERE.parent / 'journal' / name
        raw = src.read_bytes()
        (stage / 'journal' / name).write_bytes(raw)
        pins['journal/' + name] = hexdigest(raw)
    for name in ['service.py', 'test_driver.py']:
        raw = (HERE / name).read_bytes()
        (stage / 'verified_reader' / name).write_bytes(raw)
        pins['verified_reader/' + name] = hexdigest(raw)
    # Pin a binary copy too: another lane cannot change a running experiment.
    binary = stage / 'resident-crypto'
    shutil.copyfile(Path(args.binary).resolve(), binary)
    os.chmod(binary, 0o755)
    pins['resident-crypto'] = hexdigest(binary.read_bytes())
    (report / 'source_pins.json').write_text(json.dumps(pins, sort_keys=True, indent=2) + '\n')
    with tarfile.open(report / 'source_snapshot.tar.gz', 'w:gz') as archive:
        for name in sorted(pins):
            if name != 'resident-crypto':
                archive.add(stage / name, arcname=name)
    command = [sys.executable, str(stage / 'verified_reader' / 'test_driver.py'),
               '--worker', '--runtime', str(runtime), '--report', str(report),
               '--binary', str(binary)]
    with (report / 'execution.log').open('wb') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    print(json.dumps({'ok': result.returncode == 0, 'report': str(report),
                      'exit_code': result.returncode}))
    raise SystemExit(result.returncode)


def worker(args):
    sys.path.insert(0, str(HERE.parent / 'journal'))
    from run import Run
    from common import (canonical, digest, read_json, require, rpc, sha, sign,
                        write_json, Crypto)

    root = Path(args.runtime).resolve()
    reportdir = Path(args.report).resolve()
    began = time.perf_counter_ns()
    controls = []
    timings = []
    socket_paths = []
    private = root / 'oracle'
    private.mkdir(mode=0o700)
    # Fixed query selection, before outcomes: coordinate zero and a sparse dot
    # product. These are bounded benchmark queries, not a privacy-safe policy.
    queries = [[1] + [0] * 576, [2, -1, 3] + [0] * 574]
    for i, query in enumerate(queries):
        write_json(root / f'query-input-{i}.json', query)
    policy = root / 'query-policy.json'
    write_json(policy, [{'route': 0, 'path': str(root / f'query-input-{i}.json')}
                        for i in range(len(queries))])
    run = Run(root / 'run', policy, binary=Path(args.binary))
    extras = []
    verified_config = None

    def timed_rpc(address, message, label, raw=None):
        started = time.perf_counter_ns()
        sent = raw if raw is not None else canonical(message) + b'\n'
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
            client.settimeout(120)
            client.connect(str(address))
            client.sendall(sent)
            with client.makefile('rb') as source:
                received = source.readline(2_000_001)
        require(bool(received), 'emptyReply:' + label)
        result = json.loads(received)
        item = {'label': label, 'operation': message.get('op'),
                'server': 'verified_reader' if address == verified_config['socket'] else 'baseline_control_reader',
                'elapsed_ns': time.perf_counter_ns() - started,
                'request_bytes': len(sent), 'response_bytes': len(received),
                'request_sha256': sha(sent), 'response': result}
        timings.append(item)
        with (root / 'rpc.jsonl').open('ab') as sink:
            sink.write(canonical(item) + b'\n')
        return result

    def start_service(config, name='verified'):
        cfg = read_json(config)
        address = cfg['socket']
        socket_paths.append(address)
        Path(address).unlink(missing_ok=True)
        script = HERE / 'service.py' if name == 'verified' else HERE.parent / 'journal' / 'reader.py'
        log = (root / (name + '-server.log')).open('ab')
        proc = subprocess.Popen([sys.executable, str(script), '--config', str(config)],
                                stdout=log, stderr=log)
        log.close()
        extras.append(proc)
        started = time.monotonic()
        while not Path(address).exists():
            require(proc.poll() is None, 'readerServerExited:' + name)
            require(time.monotonic() - started < 30, 'readerServerStartup:' + name)
            time.sleep(.02)
        return proc

    def clone_reader(name, verified=False):
        folder = root / name
        folder.mkdir(mode=0o700)
        cfg = copy.deepcopy(run.rcfg)
        cfg.update(db=str(folder / 'answers.sqlite3'), cas=str(folder / 'cas'),
                   socket='/tmp/rsv-' + os.urandom(6).hex() + '.sock',
                   command_log=str(root / (name + '-commands.jsonl')))
        if verified:
            cfg['verified_reader_source_sha256'] = sha((HERE / 'service.py').read_bytes())
        path = folder / 'config.json'
        write_json(path, cfg, True)
        return cfg, path, start_service(path, 'verified' if verified else name)

    def status():
        return timed_rpc(verified_config['socket'], {'op': 'verified_status'}, 'verified_status')

    def refuse(message, label, reason=None, raw=None):
        before = status()
        result = timed_rpc(verified_config['socket'], message, label, raw)
        require(result.get('ok') is False, 'expectedRefusal:' + label)
        if reason:
            require(result['reason'] == reason, 'wrongRefusal:' + label + ':' + result['reason'])
        after = status()
        require(before == after, 'rejectionChangedHead:' + label)
        item = {'label': label, 'reason': result['reason'], 'head_unchanged': True,
                'revision': before['revision'], 'state_digest': before['state_digest']}
        controls.append(item)
        return result

    def put(path, kind='ct'):
        raw = Path(path).read_bytes()
        result = timed_rpc(verified_config['socket'],
                          {'op': 'put', 'kind': kind, 'sha256': sha(raw),
                           'data': base64.b64encode(raw).decode()}, 'put_' + kind)
        require(result.get('ok') and result['sha256'] == sha(raw), 'verifiedUpload')

    def sync(envelope):
        result = timed_rpc(verified_config['socket'], {'op': 'sync', 'envelope': envelope}, 'sync')
        require(result.get('ok'), 'syncRejected:' + str(result))
        return result

    def register(cfg, request, label='register'):
        raw = run.host_cas.get(request['action']['query_ct'], 'query').read_bytes()
        result = timed_rpc(cfg['socket'], {'op': 'register', 'authorization': request['authorization'],
                          'query': base64.b64encode(raw).decode()}, label)
        require(result.get('ok'), 'registerRejected:' + str(result))
        return result

    def receive(cfg, envelope, ciphertext, label='receive'):
        return timed_rpc(cfg['socket'], {'op': 'receive', 'envelope': envelope,
                         'ciphertext': base64.b64encode(ciphertext).decode()}, label)

    def scalar(cfg, request_id):
        # Test oracle only. No score, vector, state or key bytes are logged.
        with sqlite3.connect(cfg['db']) as db:
            row = db.execute('SELECT answer FROM received WHERE request_id=?', (request_id,)).fetchone()
        require(row is not None, 'missingPrivateOracleAnswer')
        return json.loads(row[0])['signed_score']

    def signed_variant(envelope, mutate, resign_action=False):
        bad = copy.deepcopy(envelope)
        mutate(bad['payload'])
        req = bad['payload']['request']
        if resign_action:
            kind = req['action']['kind']
            cfg = read_json(run.root / '.private' / ('issuer' if kind == 'Learn' else 'command') / 'config.json')
            domain = 'resident-issuer-v1' if kind == 'Learn' else 'resident-query-authorization-v1'
            req['authorization'] = sign(req['action'], cfg['signing_key'], domain)
        bad['payload']['request_sha256'] = digest(req)
        return sign(bad['payload'], run.acfg['signing_key'], 'resident-authority-finalization-v1')

    try:
        verified_config, vpath, vproc = clone_reader('verified', True)
        put(run.root / 'zero.ct')
        for q in sorted((run.root / 'queries').glob('*.json')):
            put(q, 'query')
        initial_head = run.head()
        authority_snapshot = root / 'authority-at-genesis.sqlite3'
        with sqlite3.connect(run.acfg['db']) as source, sqlite3.connect(authority_snapshot) as destination:
            source.backup(destination)
        require(status()['revision'] == 0, 'initialVerifiedHead')
        queue = collections.deque()
        oracle = [0] * 577
        accepted = []
        infer_records = []
        expiries = 0
        oracle_checks = 0
        genuine_infer_before_ticket = False
        first_vector = None

        for n in range(1, 41):
            vector_path = private / f'input-{n:02d}.json'
            Crypto(run.hcfg, 'trusted_private_input_generator', run.root / 'commands.jsonl').run(
                'issuer-private-vector', out=vector_path)
            vector = read_json(vector_path)
            if first_vector is None:
                first_vector = vector_path
            queue.append(vector)
            oracle = [a + b for a, b in zip(oracle, vector)]
            if len(queue) > 32:
                old = queue.popleft()
                oracle = [a - b for a, b in zip(oracle, old)]
                expiries += 1
            parent_at_expiry = run.head() if n == 33 else None
            req = run.prepare('Learn', 0, f'learn-{n:02d}', vector=vector_path)
            reply = run.accepted(req)
            envelope = reply['envelope']
            accepted.append((req, envelope))
            put(run.host_cas.get(req['action']['fresh_ct']))
            if n == 1:
                # The reader has neither receipt yet, while the authority advances.
                continue
            if n == 2:
                refuse({'op': 'sync', 'envelope': envelope}, 'second_learn_before_first', 'verifiedStaleParent')
                sync(accepted[0][1])
                sync(envelope)
                refuse({'op': 'receive', 'envelope': accepted[0][1],
                        'ciphertext': base64.b64encode(run.host_cas.get(accepted[0][0]['proposal']['result_ct']).read_bytes()).decode()},
                       'verified_learn_cannot_release', 'verifiedReaderOnlyInfer')
            else:
                if n == 33:
                    # A concrete wrong-old arithmetic computation, using a
                    # different original ciphertext from the live queue.
                    parent_route = parent_at_expiry['state']['routes']['0']
                    wrong_old = parent_route['queue'][1]['ct_sha256']
                    wrong_path = run.host_cas.fresh_output()
                    run.host_cas.crypto.run('host-learn',
                        acc=run.host_cas.get(parent_route['acc_ct']),
                        fresh=run.host_cas.get(req['action']['fresh_ct']),
                        old=run.host_cas.get(wrong_old), out=wrong_path)
                    wrong_result = run.host_cas.finish_output(wrong_path)
                    require(wrong_result != req['proposal']['result_ct'], 'wrongOldActuallyChangesBytes')
                    bad = signed_variant(envelope, lambda p: p['request']['proposal'].update(
                        result_ct=wrong_result, expired_ct=wrong_old))
                    refuse({'op': 'sync', 'envelope': bad}, 'wrong_original_expiry_actual_arithmetic',
                           'verifiedArithmeticProposal')
                    bad = signed_variant(envelope, lambda p: p['delta'].__setitem__(
                        'expired', parent_route['queue'][1]))
                    refuse({'op': 'sync', 'envelope': bad}, 'wrong_expiry_delta', 'verifiedArithmeticDelta')
                sync(envelope)

            if n not in [10, 20, 33, 40]:
                continue
            qindex = [10, 20, 33, 40].index(n) % 2
            expected = sum(a * b for a, b in zip(oracle, queries[qindex]))
            req = run.prepare('Infer', 0, f'infer-{n:02d}', query_index=qindex)

            if n == 10:
                # The same legitimately selected ticket goes to an isolated
                # baseline clone and the verifier. Only the authority signer is
                # corrupted; issuer and command signatures remain authentic.
                register(verified_config, req)
                baseline, bpath, bproc = clone_reader('baseline-control')
                register(baseline, req, 'baseline_register')
                # Fixed before private outcomes: scalar8128 =127*2^6 exceeds
                # the first query's possible magnitude10*127, while remaining
                # inside the reader's global score bound. Public encryption and
                # six doublings supply a real well-formed wrong-output Ct.
                public_unit = root / 'public-control-unit.json'
                write_json(public_unit, [0] * 576 + [127])
                wrong_path = root / 'public-control-unit.ct'
                public_crypto = Crypto(run.hcfg, 'public_falsifier', run.root / 'commands.jsonl')
                public_crypto.run('issuer-encrypt', pk=run.root / 'public_key.bin',
                                  vector=public_unit, out=wrong_path)
                for exponent in range(1, 7):
                    doubled = root / f'public-control-double-{exponent}.ct'
                    public_crypto.run('host-learn', acc=wrong_path, fresh=wrong_path, out=doubled)
                    wrong_path = doubled
                wrong_hash = run.host_cas.import_file(wrong_path)
                badreq = copy.deepcopy(req)
                badreq['proposal']['result_ct'] = wrong_hash
                forged_payload = {'schema': 'resident-finalized-v1', 'request': badreq,
                    'request_sha256': digest(badreq), 'revision': req['action']['parent_revision'] + 1,
                    'parent_state': req['action']['parent_state'], 'next_state': req['action']['parent_state'],
                    'delta': {'kind': 'Infer', 'route': 0, 'query_ct': req['action']['query_ct'], 'output_ct': wrong_hash},
                    'output_ct': wrong_hash}
                forged = sign(forged_payload, run.acfg['signing_key'], 'resident-authority-finalization-v1')
                wrong_raw = run.host_cas.get(wrong_hash).read_bytes()
                baseline_reply = receive(baseline, forged, wrong_raw, 'baseline_signed_substitution')
                require(baseline_reply.get('ok') and scalar(baseline, req['action']['request_id']) == 8128
                        and abs(expected) <= 10 * 127,
                        'baselineBoundaryWitness')
                require(run.head()['revision'] == 10, 'forgeryNotAuthorityCommitted')
                refuse({'op': 'sync', 'envelope': forged}, 'signed_output_substitution', 'verifiedArithmeticProposal')
                refuse({'op': 'receive', 'envelope': forged, 'ciphertext': base64.b64encode(wrong_raw).decode()},
                       'signed_unverified_output_cannot_release', 'unverifiedFinalization')
                write_json(reportdir / 'signed_substitution.json', {'envelope': forged,
                    'baseline_accepted': True, 'private_oracle_mismatch': True,
                    'verified_sync_refused': True, 'verified_receive_refused': True})

            reply = run.accepted(req)
            envelope = reply['envelope']
            raw = run.host_cas.get(req['proposal']['result_ct']).read_bytes()
            # Fresh/query/zero only are uploaded to the verifier. It must create
            # the result ciphertext through its own public transition.
            sync(envelope)
            if n == 20:
                refuse({'op': 'receive', 'envelope': envelope, 'ciphertext': base64.b64encode(raw).decode()},
                       'verified_infer_without_independent_ticket', 'unselectedQueryTicket')
                genuine_infer_before_ticket = True
            if n != 10:
                register(verified_config, req)
            answer = receive(verified_config, envelope, raw)
            require(answer.get('ok') and answer['status'] == 'received', 'verifiedPositiveRead')
            require(scalar(verified_config, req['action']['request_id']) == expected, 'verifiedPrivateOracle')
            require(scalar(run.rcfg, req['action']['request_id']) == expected, 'baselinePrivateOracle')
            oracle_checks += 2
            infer_records.append((req, envelope, raw))
            accepted.append((req, envelope))
            print(json.dumps({'checkpoint_learns': n, 'verified_revision': status()['revision'],
                              'private_oracle_match': True}), flush=True)

        require(status()['revision'] == 44 and expiries == 8, 'finalCounts')
        current = status()
        original_req, original_envelope = accepted[0]
        historical = sync(original_envelope)
        require(historical['status'] == 'verifiedReplay' and historical['revision'] == 1 and status() == current,
                'historicalSyncRetry')
        ir, ie, raw = infer_records[0]
        replay = receive(verified_config, ie, raw, 'historical_receive')
        require(replay.get('ok') and replay['status'] == 'replayed', 'historicalReceiveRetry')

        # Reject exact-context mutations even when the malicious authority signs.
        bad = signed_variant(ie, lambda p: p['request']['action'].__setitem__('recipient', 'wrong-recipient'))
        refuse({'op': 'sync', 'envelope': bad}, 'changed_historical_recipient', 'verifiedRequestConflict')
        refuse({'op': 'receive', 'envelope': bad, 'ciphertext': base64.b64encode(raw).decode()},
               'wrong_recipient_receive', 'unverifiedFinalization')
        bad = signed_variant(ie, lambda p: p['request']['action'].__setitem__('query_ct', run.g['query_policy'][1]['query_ct']))
        refuse({'op': 'receive', 'envelope': bad, 'ciphertext': base64.b64encode(raw).decode()},
               'wrong_query_receive', 'unverifiedFinalization')
        refuse({'op': 'receive', 'envelope': ie, 'ciphertext': base64.b64encode(run.host_cas.get(run.g['zero_ct_sha256']).read_bytes()).decode()},
               'wrong_ciphertext_for_verified_infer', 'uploadDigestMismatch')

        # Genuine current-head actions allow type refusals before staleness or
        # historical request-id branches can mask the field being checked.
        probe = run.prepare('Infer', 0, 'type-probe', query_index=0)
        probe_payload = {'schema': 'resident-finalized-v1', 'request': probe,
            'request_sha256': digest(probe), 'revision': 45,
            'parent_state': probe['action']['parent_state'], 'next_state': probe['proposal']['next_state'],
            'delta': {'kind': 'Infer', 'route': 0, 'query_ct': probe['action']['query_ct'], 'output_ct': probe['proposal']['result_ct']},
            'output_ct': probe['proposal']['result_ct']}
        probe_env = sign(probe_payload, run.acfg['signing_key'], 'resident-authority-finalization-v1')
        bad = signed_variant(probe_env, lambda p: p['request']['action'].__setitem__('recipient', 'wrong-recipient'), True)
        refuse({'op': 'sync', 'envelope': bad}, 'current_signed_wrong_recipient', 'recipient')
        bad = signed_variant(probe_env, lambda p: p['request']['action'].__setitem__('query_ct', run.g['query_policy'][1]['query_ct']))
        refuse({'op': 'sync', 'envelope': bad}, 'current_unsigned_query_substitution', 'authorizationContext')
        for field in ['program_version', 'route', 'parent_revision']:
            bad = signed_variant(probe_env, lambda p, field=field: p['request']['action'].__setitem__(field, True), True)
            refuse({'op': 'sync', 'envelope': bad}, 'boolean_' + field)
        bad = signed_variant(probe_env, lambda p: p.__setitem__('revision', True))
        refuse({'op': 'sync', 'envelope': bad}, 'boolean_finalized_revision', 'finalizedRevisionType')
        bad = signed_variant(probe_env, lambda p: p['request']['action'].__setitem__('program_version', 1.0), True)
        refuse({'op': 'sync', 'envelope': bad}, 'float_program_version', 'nonIntegerJSONNumber')
        msg = {'op': 'sync', 'envelope': probe_env}
        encoded = canonical(msg)
        require(b'"program_version":1' in encoded, 'duplicateFieldFixture')
        refuse(msg, 'duplicate_nested_json_key', 'duplicateJSONKey',
               encoded.replace(b'"program_version":1', b'"program_version":1,"program_version":1') + b'\n')
        refuse({'op': 'verified_status'}, 'duplicate_top_level_json_key', 'duplicateJSONKey',
               b'{"op":"verified_status","op":"verified_status"}\n')
        refuse({'op': 'verified_status'}, 'nan_json', 'nonIntegerJSONNumber',
               b'{"op":"verified_status","extra":NaN}\n')
        # An unsigned action alias must not match the original integer signature.
        bad = signed_variant(probe_env, lambda p: p['request']['action'].__setitem__('program_version', True))
        refuse({'op': 'sync', 'envelope': bad}, 'unsigned_boolean_alias')

        before_status = status()
        before_inbox = timed_rpc(verified_config['socket'], {'op': 'status'}, 'inbox_before_SIGKILL')
        old_pid = vproc.pid
        vproc.kill()
        require(vproc.wait(timeout=10) == -signal.SIGKILL, 'actualReaderSIGKILL')
        vproc = start_service(vpath)
        require(vproc.pid != old_pid and status() == before_status, 'readerHeadSurvivesRestart')
        after_inbox = timed_rpc(verified_config['socket'], {'op': 'status'}, 'inbox_after_SIGKILL')
        require(before_inbox == after_inbox and after_inbox['received'] == 4, 'readerInboxSurvivesRestart')
        require(sync(original_envelope)['status'] == 'verifiedReplay', 'restartHistoricalSync')
        require(receive(verified_config, ie, raw, 'restart_historical_receive')['status'] == 'replayed', 'restartHistoricalReceive')

        # Start a separate authority process from a true genesis database copy.
        # Its valid alternate-branch signature cannot rewind the verifier.
        rollback_cfg = copy.deepcopy(run.acfg)
        rollback_cfg['db'] = str(authority_snapshot)
        rollback_cfg['socket'] = '/tmp/rsv-old-authority-' + os.urandom(5).hex() + '.sock'
        rollback_cfg_path = root / 'rollback-authority.json'
        write_json(rollback_cfg_path, rollback_cfg, True)
        socket_paths.append(rollback_cfg['socket'])
        old_authority = run.start('authority', rollback_cfg_path)
        alternate = run.prepare('Learn', 0, 'alternate-genesis-branch', vector=first_vector, head=initial_head)
        alt_reply = run.submit(alternate, rollback_cfg['socket'])
        require(alt_reply.get('ok') and alt_reply['envelope']['payload']['revision'] == 1, 'copiedAuthorityActuallyAccepted')
        put(run.host_cas.get(alternate['action']['fresh_ct']))
        refuse({'op': 'sync', 'envelope': alt_reply['envelope']}, 'copied_authority_old_parent', 'verifiedStaleParent')
        write_json(reportdir / 'rollback_envelopes.json', {'original': original_envelope,
                    'alternate': alt_reply['envelope'], 'same_parent_revision': True,
                    'retained_verified_revision': status()['revision']})

        require(run.head()['revision'] == 44 and status()['revision'] == 44, 'controlsDidNotAdvanceMainHistory')
        verified_db = sqlite3.connect(verified_config['db'])
        try:
            finalstate = json.loads(verified_db.execute('SELECT state FROM verified_head').fetchone()[0])
            rows = verified_db.execute('SELECT envelope FROM verified_journal ORDER BY revision').fetchall()
            private_answer_count = verified_db.execute('SELECT count(*) FROM received').fetchone()[0]
        finally:
            verified_db.close()
        require(finalstate == run.head()['state'], 'independentlyRecomputedFinalState')
        require([json.loads(row[0]) for row in rows] == [env for _, env in accepted], 'sameExactOrderedJournal')
        write_json(reportdir / 'accepted_envelopes.json', [env for _, env in accepted])
        crypto_records = []
        for path in [run.root / 'commands.jsonl', root / 'verified-commands.jsonl', root / 'baseline-control-commands.jsonl']:
            records = [json.loads(line) for line in path.read_bytes().splitlines()]
            for record in records:
                record['process_instance'] = ('verified_reader' if path.name == 'verified-commands.jsonl'
                    else 'baseline_control_reader' if path.name == 'baseline-control-commands.jsonl'
                    else 'main_pipeline')
                command = record['command'][1]
                if command == 'reader-decrypt':
                    require(record['private_output_omitted'] and record['stdout'] is None and record['stderr'] is None,
                            'privateReaderLogOmission')
                if record['role'] in ['host', 'authority', 'public_transport']:
                    require('--sk' not in record['command'] and '--vector' not in record['command'], 'keylessHostInputs')
                crypto_records.append(record)
        own_commands = [json.loads(line) for line in (root / 'verified-commands.jsonl').read_bytes().splitlines()]
        require(sum(x['command'][1] == 'reader-decrypt' for x in own_commands) == 4, 'exactlyFourVerifiedDecrypts')
        require(all(x['command'][1] in ['inspect', 'host-learn', 'host-infer', 'reader-decrypt'] for x in own_commands),
                'verifiedReaderCommandDomain')
        costs = {}
        for record in crypto_records:
            key = record['process_instance'] + ':' + record['role'] + ':' + record['command'][1]
            costs.setdefault(key, []).append(record['elapsed_ns'])
        priced = {}
        for key, values in sorted(costs.items()):
            ordered = sorted(values)
            priced[key] = {'count': len(values), 'sum_ns': sum(values),
                           'median_ns': ordered[len(ordered) // 2],
                           'p95_ns': ordered[min(len(ordered) - 1, (95 * len(ordered) + 99) // 100 - 1)]}
        live = [r['acc_ct'] for r in finalstate['routes'].values()]
        live += [entry['ct_sha256'] for r in finalstate['routes'].values() for entry in r['queue']]
        cas_files = [p for p in Path(verified_config['cas']).iterdir() if p.is_file() and len(p.name) == 64]
        rpc_costs = {}
        for row in timings:
            key = row['server'] + ':' + str(row['operation'])
            bucket = rpc_costs.setdefault(key, {'count': 0, 'sum_ns': 0, 'request_bytes': 0, 'response_bytes': 0})
            bucket['count'] += 1
            for field in ['request_bytes', 'response_bytes']:
                bucket[field] += row[field]
            bucket['sum_ns'] += row['elapsed_ns']
        report = {'ok': True, 'schema': 'verified-reader-real-bfv-driver-v1',
            'source_pins': read_json(reportdir / 'source_pins.json'),
            'genesis_sha256': digest(run.g), 'params_id': run.g['crypto']['params_id'],
            'program_id': run.g['crypto']['program_id'],
            'history': {'main_learns': 40, 'main_infers': 4, 'revision': 44, 'expiries': expiries,
                        'route_admissions': {k: v['admissions'] for k, v in finalstate['routes'].items()},
                        'route_queue_lengths': {k: len(v['queue']) for k, v in finalstate['routes'].items()},
                        'distinct_fresh_ciphertexts': len({req['action']['fresh_ct'] for req, _ in accepted if req['action']['kind'] == 'Learn'}),
                        'infer_after_learns': [10, 20, 33, 40], 'query_indices': [0, 1, 0, 1],
                        'extra_rollback_branch_learns': 1, 'uncommitted_type_probe_infers': 1},
            'private_oracle': {'scalar_comparisons': oracle_checks, 'all_match': True,
                               'baseline_signed_substitution_mismatch': True,
                               'private_values_in_public_reports': False},
            'controls': controls,
            'positive_controls': {'exact_historical_sync': True, 'exact_historical_receive': True,
                'reader_actual_SIGKILL_restart': True, 'head_and_inbox_retained': True,
                'same_journal_and_state_as_authority': True, 'copied_authority_did_finalize_other_branch': True,
                'genuine_verified_infer_needs_ticket': genuine_infer_before_ticket,
                'verified_decrypt_calls_including_retries': 4, 'logical_verified_answers': private_answer_count,
                'no_outputs_uploaded_before_sync': True},
            'public_falsifier': {'selection_independent_of_private_oracle': True,
                'known_public_scalar': 8128, 'first_query_score_magnitude_bound': 1270,
                'issuer_encrypt_calls': 1, 'public_doubling_calls': 6,
                'not_a_private_resident_score': True},
            'bytes': {'wrapped_ciphertext': (run.root / 'zero.ct').stat().st_size,
                      'logical_live_ciphertexts': len(live),
                      'logical_live_ciphertext_bytes': sum(run.host_cas.get(h).stat().st_size for h in live),
                      'verified_cas_files_including_queries_and_failed_proposal_artifacts': len(cas_files),
                      'verified_cas_total_bytes': sum(p.stat().st_size for p in cas_files),
                      'verified_and_control_rpc_request_bytes_including_uploads': sum(x['request_bytes'] for x in timings),
                      'verified_and_control_rpc_response_bytes': sum(x['response_bytes'] for x in timings)},
            'crypto_process_costs': priced, 'rpc_costs': rpc_costs,
            'role_process_costs': {role: {'count': sum(x['role_process'] == role for x in run.calls),
                'sum_ns': sum(x['elapsed_ns'] for x in run.calls if x['role_process'] == role)}
                for role in sorted({x['role_process'] for x in run.calls})},
            'elapsed_ns': time.perf_counter_ns() - began,
            'scope': ['benchmark R: a full BFV key is retained by trusted readers',
                      'same-machine process/file role separation, not OS isolation',
                      'no restricted-decryption or no-master-read claim',
                      'public query policy can disclose coordinates; privacy safety is not established',
                      'issuer range/feature/key provenance and independent command authorization are trusted',
                      'authority may deny or stall service; reader persistence must resist rollback',
                      'Ed25519 role authentication is classical; no end-to-end post-quantum claim',
                      'tests cover returned sync then SIGKILL, not every instruction-level crash interleaving']}
        write_json(reportdir / 'report.json', report)
        # Public logs omit reader stdout and include only paths to private inputs.
        evidence = [root / 'rpc.jsonl', run.root / 'commands.jsonl', run.root / 'events.jsonl',
                    run.root / 'role_calls.jsonl', root / 'verified-commands.jsonl',
                    root / 'baseline-control-commands.jsonl', run.root / 'genesis.json']
        for i, path in enumerate(evidence):
            with gzip.open(reportdir / (f'{i:02d}-' + path.name + '.gz'), 'wb') as out:
                out.write(path.read_bytes())
        manifest = {p.name: {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
                    for p in sorted(reportdir.iterdir()) if p.is_file() and p.name not in ['execution.log', 'manifest.json']}
        write_json(reportdir / 'manifest.json', manifest)
        print(json.dumps({'ok': True, 'main_learns': 40, 'main_infers': 4, 'expiries': 8,
                          'refusal_controls': len(controls), 'report': str(reportdir / 'report.json')}), flush=True)
    finally:
        for proc in extras:
            if proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=10)
        run.close()
        for path in socket_paths:
            Path(path).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--runtime', default=str(HERE / 'runtime' / 'run_001'))
    parser.add_argument('--report', default=str(HERE / 'reports' / 'run_001'))
    parser.add_argument('--binary', default=str(HERE.parent / 'crypto' / 'target' / 'release' / 'resident-crypto'))
    args = parser.parse_args()
    if args.worker:
        worker(args)
    else:
        freeze(args)


if __name__ == '__main__':
    main()
