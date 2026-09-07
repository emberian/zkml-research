#!/usr/bin/env python3
"""Complete frozen utility histories through independently verified BFV release.

Honest integration only. No adversarial or routing-control code is imported.
The issuer/test-oracle fixture is copied into ignored runtime before execution.
"""
from __future__ import annotations
import argparse
import base64
import collections
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import sqlite3
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
MODULES = ['common.py', 'model.py', 'roles.py', 'authority.py', 'reader.py', 'run.py']


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n')


def stage(args):
    runtime, reports = Path(args.runtime).resolve(), Path(args.reports).resolve()
    runtime.mkdir(parents=True, exist_ok=False)
    os.chmod(runtime, 0o700)
    reports.mkdir(parents=True, exist_ok=False)
    e2e = runtime / 'e2e'
    for name in ['journal', 'verified_reader', 'utility/issuer_oracle', 'utility/public_queries']:
        (e2e / name).mkdir(parents=True)
    os.chmod(e2e / 'utility/issuer_oracle', 0o700)
    pins = {}
    for name in MODULES:
        raw = (HERE.parent / 'journal' / name).read_bytes()
        (e2e / 'journal' / name).write_bytes(raw)
        pins['journal/' + name] = sha(raw)
    for name in ['service.py', 'utility_driver.py']:
        raw = (HERE / name).read_bytes()
        (e2e / 'verified_reader' / name).write_bytes(raw)
        pins['verified_reader/' + name] = sha(raw)
    binary = e2e / 'resident-crypto'
    shutil.copyfile(Path(args.binary).resolve(), binary)
    os.chmod(binary, 0o755)
    pins['resident-crypto'] = sha(binary.read_bytes())
    utility = HERE.parent / 'utility'
    manifest = json.loads((utility / 'materialized_inputs_manifest.json').read_bytes())
    index_path = utility / 'issuer_oracle/input_index.json'
    oracle_path = utility / 'issuer_oracle/expected_scalars.json'
    assert sha(index_path.read_bytes()) == manifest['private_index_sha256']
    assert sha(oracle_path.read_bytes()) == manifest['oracle_sha256']
    index = json.loads(index_path.read_bytes())
    assert len(index['events']) == 480
    frozen_files = {}
    for event in index['events']:
        field = 'issuer_vector_path' if event['kind'] == 'Learn' else 'public_query_vector_path'
        path = Path(event[field])
        raw = path.read_bytes()
        assert sha(raw) == manifest['files_sha256'][str(path)]
        dest = e2e / 'utility' / ('issuer_oracle' if event['kind'] == 'Learn' else 'public_queries') / path.name
        dest.write_bytes(raw)
        os.chmod(dest, 0o600 if event['kind'] == 'Learn' else 0o644)
        event[field] = str(dest)
        frozen_files[str(dest.relative_to(e2e))] = sha(raw)
    dump(e2e / 'utility/issuer_oracle/input_index.json', index)
    os.chmod(e2e / 'utility/issuer_oracle/input_index.json', 0o600)
    (e2e / 'utility/issuer_oracle/expected_scalars.json').write_bytes(oracle_path.read_bytes())
    os.chmod(e2e / 'utility/issuer_oracle/expected_scalars.json', 0o600)
    provenance = {'materialized_inputs_manifest_sha256': sha((utility / 'materialized_inputs_manifest.json').read_bytes()),
        'original_index_sha256': manifest['private_index_sha256'], 'oracle_sha256': manifest['oracle_sha256'],
        'copied_index_sha256': sha((e2e / 'utility/issuer_oracle/input_index.json').read_bytes()),
        'mapping_sha256': manifest['mapping_sha256'], 'frozen_vector_files': frozen_files,
        'source_utility_report_sha256': sha((HERE.parent / 'journal/results/utility_002/report.json').read_bytes()),
        'source_live_text_report_sha256': sha((HERE.parent / 'journal/results/live_text_002/report.json').read_bytes()),
        'issuer_vectors': 384, 'public_queries': 16, 'expected_outputs': 96,
        'exposure': 'Previously public frozen utility fixture; copied issuer/oracle data is never a host/authority input.'}
    dump(reports / 'source_pins.json', pins)
    dump(reports / 'fixture_pins.json', provenance)
    with tarfile.open(reports / 'source_snapshot.tar.gz', 'w:gz') as archive:
        for name in sorted(pins):
            if name != 'resident-crypto':
                archive.add(e2e / name, arcname=name)
    command = [sys.executable, str(e2e / 'verified_reader/utility_driver.py'), '--worker',
               '--runtime', str(runtime), '--reports', str(reports), '--binary', str(binary)]
    dump(reports / 'command.json', {'argv': command})
    with (reports / 'execution.log').open('wb') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    print(json.dumps({'ok': result.returncode == 0, 'exit_code': result.returncode,
                      'report': str(reports / 'report.json')}))
    raise SystemExit(result.returncode)


def worker(args):
    sys.path.insert(0, str(HERE.parent / 'journal'))
    from run import Run
    from common import canonical, digest, read_json, require, write_json

    runtime, reports = Path(args.runtime).resolve(), Path(args.reports).resolve()
    utility = HERE.parent / 'utility'
    events = read_json(utility / 'issuer_oracle/input_index.json')['events']
    oracle = read_json(utility / 'issuer_oracle/expected_scalars.json')['queries']
    policy = runtime / 'query_policy.json'
    write_json(policy, [{'route': 0 if i < 8 else 1,
                        'path': str(utility / 'public_queries' / f'q{i:02d}.json')}
                       for i in range(16)])
    histories = []
    total_start = time.perf_counter_ns()

    for history in [0, 1]:
        reportdir = reports / f'history_{history}'
        reportdir.mkdir()
        run = Run(runtime / f'history_{history}', policy, binary=Path(args.binary))
        proc = None
        calls = []
        expected_events = [event for event in events if event['event_id'].startswith(f'h{history}-')]
        require(len(expected_events) == 240, 'fixedHistoryCount')

        def vrpc(message):
            encoded = canonical(message) + b'\n'
            start = time.perf_counter_ns()
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                client.settimeout(120)
                client.connect(cfg['socket'])
                client.sendall(encoded)
                with client.makefile('rb') as stream:
                    received = stream.readline(2_000_001)
            require(bool(received), 'emptyVerifiedReply')
            reply = json.loads(received)
            item = {'operation': message['op'], 'request_sha256': sha(encoded),
                    'request_bytes': len(encoded), 'response_bytes': len(received),
                    'elapsed_ns': time.perf_counter_ns() - start, 'reply': reply}
            calls.append(item)
            with (run.root / 'verified_rpc.jsonl').open('ab') as sink:
                sink.write(canonical(item) + b'\n')
            require(reply.get('ok'), 'verifiedRejected:' + str(reply))
            return reply

        def put(path, kind='ct'):
            raw = Path(path).read_bytes()
            return vrpc({'op': 'put', 'kind': kind, 'sha256': sha(raw),
                         'data': base64.b64encode(raw).decode()})

        try:
            # Replace the automatically started baseline receiver at the same
            # public delivery socket. The new reader has its own DB and CAS.
            run.stop(run.reader)
            original = run.rcfg
            private_reader = run.root / '.private/verified_reader'
            private_reader.mkdir(mode=0o700)
            cfg = {**original, 'db': str(private_reader / 'answers.sqlite3'),
                   'cas': str(run.root / 'verified_cas'),
                   'command_log': str(run.root / 'verified_commands.jsonl'),
                   'verified_reader_source_sha256': sha((HERE / 'service.py').read_bytes())}
            cfg_path = private_reader / 'config.json'
            write_json(cfg_path, cfg, True)
            Path(cfg['socket']).unlink(missing_ok=True)
            with (run.root / 'verified_server.log').open('ab') as log:
                proc = subprocess.Popen([sys.executable, str(HERE / 'service.py'), '--config', str(cfg_path)],
                                        stdout=log, stderr=log)
            started = time.monotonic()
            while not Path(cfg['socket']).exists():
                require(proc.poll() is None, 'verifiedServerExited')
                require(time.monotonic() - started < 30, 'verifiedServerTimeout')
                time.sleep(.02)
            run.rcfg = cfg  # Run.prepare now registers the independent ticket here.
            put(run.root / 'zero.ct')
            for query in sorted((run.root / 'queries').glob('*.json')):
                put(query, 'query')

            accepted = []
            fresh = []
            query_ids = []
            expiry = 0
            phase_counts = {}
            normal_pending = 0
            transition_rows = []
            for ordinal, event in enumerate(expected_events, 1):
                begin = time.perf_counter_ns()
                kwargs = {'vector': event['issuer_vector_path']} if event['kind'] == 'Learn' else {
                    'query_index': int(Path(event['public_query_vector_path']).stem[1:])}
                request = run.prepare(event['kind'], event['route'], event['event_id'], **kwargs)
                if event['kind'] == 'Learn':
                    put(run.host_cas.get(request['action']['fresh_ct']))
                reply = run.submit(request)
                require(reply.get('ok') and reply['status'] == 'accepted', 'authorityAcceptedNewCommand')
                envelope = reply['envelope']
                require(envelope['payload']['revision'] == ordinal, 'orderedRevision')
                if event['kind'] == 'Infer':
                    require(reply['delivery']['status'] == 'pending', 'waitForIndependentVerification')
                    normal_pending += 1
                verified = vrpc({'op': 'sync', 'envelope': envelope})
                require(verified['status'] == 'verified' and verified['revision'] == ordinal,
                        'verifiedInstalledNewCommand')
                if event['kind'] == 'Infer':
                    delivered = run.accepted(request)
                    require(delivered['status'] == 'replayed' and delivered['envelope'] == envelope,
                            'sameFinalizationAfterVerification')
                    require(delivered['delivery']['reader']['status'] == 'received', 'newVerifiedRelease')
                    query_ids.append(event['event_id'])
                    # Test oracle only: the worker never forwards this integer
                    # to host/authority or writes it in retained output logs.
                    actual = run.answers()[event['event_id']]
                    expected = oracle[event['event_id']]
                    require(actual == expected['expected_scalar'], 'exactFrozenIntegerScore')
                    actual_sign = 1 if actual >= 0 else -1
                    require(actual_sign == expected['sign'], 'frozenSignConvention')
                    correct = actual_sign == expected['target_label']
                    require(correct == expected['correct'], 'frozenUtilityCorrectness')
                    phase = (ordinal - 1) // 80 + 1
                    key = f'phase_{phase}_route_{event["route"]}'
                    tally = phase_counts.setdefault(key, {'queries': 0, 'correct': 0, 'known_empty': 0})
                    tally['queries'] += 1
                    tally['correct'] += int(correct)
                    tally['known_empty'] += int(expected['public_structural_zero'])
                else:
                    fresh.append(request['action']['fresh_ct'])
                    expiry += request['proposal']['expired_ct'] is not None
                accepted.append(envelope)
                timing = {'event_id': event['event_id'], 'kind': event['kind'], 'route': event['route'],
                          'revision': ordinal, 'elapsed_ns': time.perf_counter_ns() - begin,
                          'verified_envelope_sha256': digest(envelope)}
                transition_rows.append(timing)
                with (run.root / 'transitions.jsonl').open('ab') as sink:
                    sink.write(canonical(timing) + b'\n')
                if ordinal % 20 == 0:
                    print(json.dumps({'history': history, 'events_completed': ordinal,
                                      'verified_outputs': len(query_ids), 'all_oracle_matches': True}), flush=True)

            final = vrpc({'op': 'verified_status'})
            require(final['revision'] == final['verified_records'] == 240, 'finalVerifiedCount')
            with sqlite3.connect(cfg['db']) as db:
                vstate = json.loads(db.execute('SELECT state FROM verified_head').fetchone()[0])
                journal = [json.loads(row[0]) for row in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
                answer_count = db.execute('SELECT count(*) FROM received').fetchone()[0]
            require(journal == accepted and vstate == run.head()['state'], 'exactFinalHistoryAndState')
            require(answer_count == 48 and set(run.answers()) == set(query_ids), 'completeVerifiedAnswerSet')
            require(len(fresh) == len(set(fresh)) == 192 and expiry == 128, 'completeLearnExpirySet')
            with sqlite3.connect(original['db']) as db:
                require(db.execute('SELECT count(*) FROM received').fetchone()[0] == 0, 'baselineReaderNeverDecrypted')

            def summarize(values):
                ordered = sorted(values)
                return {'count': len(values), 'sum_ns': sum(values),
                        'median_ns': ordered[len(ordered) // 2],
                        'p95_ns': ordered[min(len(ordered) - 1, (95 * len(ordered) + 99) // 100 - 1)]}

            costs = collections.defaultdict(list)
            command_count = 0
            verifier_decrypts = 0
            for instance, path in [('main_pipeline', run.root / 'commands.jsonl'),
                                   ('verified_reader', run.root / 'verified_commands.jsonl')]:
                for line in path.read_bytes().splitlines():
                    row = json.loads(line)
                    command, role = row['command'][1], row['role']
                    require(row['exit_code'] == 0, 'cryptoCommandSucceeded')
                    command_count += 1
                    if role in ['host', 'authority', 'public_transport']:
                        require(command in ['inspect', 'host-learn', 'host-infer'], 'publicRoleCommandBoundary')
                        require('--sk' not in row['command'] and '--vector' not in row['command'], 'keylessRoleInputs')
                    if instance == 'verified_reader':
                        require(command in ['inspect', 'host-learn', 'host-infer', 'reader-decrypt'], 'verifiedCommandBoundary')
                    if command == 'reader-decrypt':
                        require(instance == 'verified_reader', 'allOutputsUseVerifiedReader')
                        require(row['stdout'] is None and row['stderr'] is None and row['private_output_omitted'],
                                'readerPlaintextOutputOmitted')
                        verifier_decrypts += 1
                    costs[f'{instance}:{role}:{command}'].append(row['elapsed_ns'])
            require(verifier_decrypts == 48, 'oneDecryptionPerVerifiedAnswer')
            blobs = [p for p in Path(cfg['cas']).iterdir() if p.is_file() and len(p.name) == 64]
            live = [route['acc_ct'] for route in vstate['routes'].values()]
            live += [entry['ct_sha256'] for route in vstate['routes'].values() for entry in route['queue']]
            report = {'ok': True, 'history': history, 'events': 240, 'learns': 192, 'infers': 48,
                'expiries': expiry, 'fresh_ciphertexts_distinct': True,
                'oracle_comparisons': 48, 'all_oracle_matches': True,
                'known_empty_outputs': sum(oracle[k]['public_structural_zero'] for k in query_ids),
                'nonempty_outputs': sum(not oracle[k]['public_structural_zero'] for k in query_ids),
                'phase_route_counts': phase_counts, 'initial_pending_publications': normal_pending,
                'acknowledged_after_verification': 48, 'verified_decrypt_calls': verifier_decrypts,
                'baseline_decrypt_calls': 0, 'genesis_sha256': digest(run.g),
                'final_verified_revision': 240, 'final_state_digest': final['state_digest'],
                'exact_same_journal_and_state_as_authority': True,
                'query_tickets_registered_at_verified_reader': True,
                'only_fresh_query_zero_uploaded_to_verifier': True,
                'queue_lengths': {k: len(v['queue']) for k, v in vstate['routes'].items()},
                'route_admissions': {k: v['admissions'] for k, v in vstate['routes'].items()},
                'bytes': {'logical_live_ciphertexts': len(live),
                          'logical_live_ciphertext_bytes': sum(run.host_cas.get(h).stat().st_size for h in live),
                          'retained_verified_cas_files': len(blobs),
                          'retained_verified_cas_bytes': sum(p.stat().st_size for p in blobs),
                          'verified_state_manifest': len(canonical(vstate)),
                          'driver_to_verifier_request_bytes': sum(c['request_bytes'] for c in calls),
                          'driver_to_verifier_response_bytes': sum(c['response_bytes'] for c in calls)},
                'crypto_process_costs': {k: summarize(v) for k, v in sorted(costs.items())},
                'transition_wall_costs': {kind: summarize([x['elapsed_ns'] for x in transition_rows if x['kind'] == kind])
                                          for kind in ['Learn', 'Infer']},
                'driver_rpc_costs': {op: summarize([x['elapsed_ns'] for x in calls if x['operation'] == op])
                                      for op in sorted({x['operation'] for x in calls})},
                'command_count': command_count, 'elapsed_ns': time.perf_counter_ns() - run.started}
            write_json(reportdir / 'report.json', report)
            write_json(reportdir / 'accepted_envelopes.json', accepted)
            public_logs = ['commands.jsonl', 'verified_commands.jsonl', 'events.jsonl', 'role_calls.jsonl',
                           'verified_rpc.jsonl', 'transitions.jsonl', 'genesis.json']
            for name in public_logs:
                with gzip.open(reportdir / (name + '.gz'), 'wb') as output:
                    output.write((run.root / name).read_bytes())
            # Full keys never enter the retained artifact set, including source
            # snapshots and decompressed logs. Scalar stdout omission is checked
            # structurally above; no reader DB or role configuration is copied.
            public = b'\n'.join(p.read_bytes() if not p.name.endswith('.gz') else gzip.decompress(p.read_bytes())
                                 for p in reportdir.iterdir() if p.is_file())
            keyfiles = list((run.root / '.private').glob('*/signing.key')) + [Path(cfg['bfv_secret_key'])]
            require(len(keyfiles) == 4, 'fourSetupSecretFiles')
            for path in keyfiles:
                key = path.read_bytes()
                for rawkey in ([key, key[81:]] if path.name == 'bfv_secret.bin' else [key]):
                    require(rawkey not in public and rawkey.hex().encode() not in public and
                            base64.b64encode(rawkey) not in public, 'secretAbsentFromPublicArtifacts')
            write_json(reportdir / 'privacy_validation.json', {'ok': True, 'full_secret_files_scanned': 4,
                'reader_outputs_omitted': True, 'baseline_reader_decryptions': 0,
                'scope': 'Previously public fixture; log/argv and full-key omission audit, not OS isolation or information-flow proof.'})
            histories.append(report)
            write_json(reports / 'progress.json', {'histories_complete': len(histories), 'histories': histories})
        finally:
            if proc is not None and proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=10)
            run.close()

    correct = sum(t['correct'] for h in histories for t in h['phase_route_counts'].values())
    nonempty_correct = sum(t['correct'] for h in histories for t in h['phase_route_counts'].values() if not t['known_empty'])
    report = {'ok': True, 'schema': 'complete-utility-verified-bfv-release-v1',
        'histories': histories, 'events': 480, 'learns': 384, 'infers': 96, 'expiries': 256,
        'oracle_comparisons': 96, 'all_oracle_matches': True, 'known_empty_outputs': 16,
        'nonempty_outputs': 80, 'verified_decrypt_calls': 96, 'baseline_decrypt_calls': 0,
        'utility_counts': {'all_checkpoints_correct': correct, 'all_checkpoints_total': 96,
            'nonempty_correct': nonempty_correct, 'nonempty_total': 80,
            'final_checkpoint_correct': sum(t['correct'] for h in histories for k, t in h['phase_route_counts'].items() if k.startswith('phase_3')),
            'final_checkpoint_total': 32},
        'source_pins': read_json(reports / 'source_pins.json'),
        'fixture_pins_sha256': sha((reports / 'fixture_pins.json').read_bytes()),
        'elapsed_ns': time.perf_counter_ns() - total_start,
        'scope': ['Both complete predeclared public fixture histories; no new model runs/training/downloads or utility reselection.',
                  'Actual BFV, trusted plaintext issuer, public queries, independent public recomputation and finalized release.',
                  'Benchmark R: trusted full-key reader; no restricted-decryption or no-master-read construction.',
                  'Public fixture is known-state utility evidence, not private-ingress confidentiality evidence.',
                  'Classical Ed25519 authorization; no end-to-end post-quantum claim.',
                  'Issuer provenance, independent command policy, reader persistence and process/file separation remain assumptions; no OS isolation.',
                  'No adversarial controls executed by this honest-workload driver.']}
    require(correct == 52 and nonempty_correct == 44, 'sameFrozenUtilityDenominator')
    require(report['utility_counts']['final_checkpoint_correct'] == 18, 'sameFrozenFinalSubset')
    write_json(reports / 'report.json', report)
    print(json.dumps({'ok': True, 'events': 480, 'verified_outputs': 96,
                      'all_oracle_matches': True, 'report': str(reports / 'report.json')}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--runtime', default=str(HERE / 'runtime/utility_001'))
    parser.add_argument('--reports', default=str(HERE / 'reports/utility_001'))
    parser.add_argument('--binary', default=str(HERE.parent / 'crypto/target/release/resident-crypto'))
    args = parser.parse_args()
    worker(args) if args.worker else stage(args)


if __name__ == '__main__':
    main()
