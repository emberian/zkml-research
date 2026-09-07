#!/usr/bin/env python3
"""Private live text -> signed BFV Learn -> independently verified scalar release.

Normal three-command interface demonstration, not an accuracy benchmark. Text,
features, scalar results and their hashes stay in ignored private runtime.
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
import select
import shutil
import socket
import sqlite3
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, value, private=False):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')
    if private:
        os.chmod(path, 0o600)


def stage(args):
    runtime, reports = Path(args.runtime).resolve(), Path(args.reports).resolve()
    runtime.mkdir(parents=True, exist_ok=False)
    os.chmod(runtime, 0o700)
    reports.mkdir(parents=True, exist_ok=False)
    secret = runtime / '.private'
    secret.mkdir(mode=0o700)
    data = load(args.input)
    if set(data) != {'text', 'route', 'label'} or not isinstance(data['text'], str):
        raise ValueError('input requires text, route and label')
    if type(data['route']) is not int or data['route'] not in [0, 1]:
        raise ValueError('route must be integer zero or one')
    if type(data['label']) is not int or data['label'] not in [-1, 1]:
        raise ValueError('label must be integer minus or plus one')
    dump(secret / 'input.json', data, True)
    e2e = runtime / 'e2e'
    for name in ['journal', 'verified_reader', 'host_runtime/frozen_core']:
        (e2e / name).mkdir(parents=True)
    pins = {}
    host = HERE.parent / 'host_runtime'
    core_pins = load(host / 'source_pins.json')
    for name, entry in core_pins['core'].items():
        raw = (host / 'frozen_core' / name).read_bytes()
        assert sha(raw) == entry['sha256']
        assert raw == (HERE.parent / 'journal' / name).read_bytes()
        for relative in ['journal/' + name, 'host_runtime/frozen_core/' + name]:
            (e2e / relative).write_bytes(raw)
            pins[relative] = sha(raw)
    for name in ['host.py', 'source_pins.json']:
        raw = (host / name).read_bytes()
        (e2e / 'host_runtime' / name).write_bytes(raw)
        pins['host_runtime/' + name] = sha(raw)
    for name in ['service.py', 'live_driver.py']:
        raw = (HERE / name).read_bytes()
        (e2e / 'verified_reader' / name).write_bytes(raw)
        pins['verified_reader/' + name] = sha(raw)
    binary = e2e / 'resident-crypto'
    shutil.copyfile(Path(args.binary).resolve(), binary)
    os.chmod(binary, 0o755)
    assert sha(binary.read_bytes()) == core_pins['crypto_binary_sha256']
    pins['resident-crypto'] = sha(binary.read_bytes())
    utility = HERE.parent / 'utility'
    dependencies = [utility / 'live_encoder/issue_text.py', utility / 'issuer_encode_prepared.py',
                    utility / 'encoder_policy.json', utility / 'encoder_feasibility.json',
                    utility / 'build_mapping.py', utility / 'live_encoder/results/run_001/report.json']
    dependencies += [HERE.parent / 'journal' / name for name in core_pins['core']]
    dep_pins = {str(path): sha(path.read_bytes()) for path in dependencies}
    # The tested frontend uses original absolute evidence keys and model paths.
    # Invoke those unchanged files, checking their bytes before and after. The
    # public runtime roles instead execute the copied core/service sources.
    dump(reports / 'frontend_dependencies.json', dep_pins)
    dump(reports / 'source_pins.json', pins)
    query_dir = runtime / 'public_query_inputs'
    query_dir.mkdir()
    query_pins = {}
    policy = []
    manifest = load(utility / 'materialized_inputs_manifest.json')
    for i in range(16):
        source = utility / 'public_queries' / f'q{i:02d}.json'
        raw = source.read_bytes()
        assert sha(raw) == manifest['files_sha256'][str(source)]
        dest = query_dir / source.name
        dest.write_bytes(raw)
        query_pins[source.name] = sha(raw)
        policy.append({'route': 0 if i < 8 else 1, 'path': str(dest)})
    dump(runtime / 'query_policy.json', policy)
    dump(reports / 'public_query_pins.json', query_pins)
    metadata = {'frontend_path': str(utility / 'live_encoder/issue_text.py'),
                'encoder_inventory': str(utility / 'encoder_feasibility.json'),
                'source_snapshot_scope': 'Public roles frozen; original live frontend/encoder sources pinned and checked before and after.',
                'input_path_and_input_hash_omitted': True}
    dump(reports / 'frontend_metadata.json', metadata)
    with tarfile.open(reports / 'source_snapshot.tar.gz', 'w:gz') as archive:
        for name in sorted(pins):
            if name != 'resident-crypto':
                archive.add(e2e / name, arcname=name)
        for i, path in enumerate(dependencies):
            archive.add(path, arcname=f'original_frontend_dependencies/{i:02d}-{path.name}')
    command = [sys.executable, str(e2e / 'verified_reader/live_driver.py'), '--worker',
               '--input', str(secret / 'input.json'), '--runtime', str(runtime), '--reports', str(reports),
               '--binary', str(binary)]
    dump(reports / 'command.json', {'argv': command, 'input_is_ignored_generic_runtime_copy': True})
    with (reports / 'execution.log').open('wb') as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    print(json.dumps({'ok': result.returncode == 0, 'exit_code': result.returncode,
                      'report': str(reports / 'report.json')}))
    raise SystemExit(result.returncode)


def worker(args):
    sys.path.insert(0, str(HERE.parent / 'journal'))
    from run import Run
    from common import canonical, digest, require, write_json
    runtime, reports = Path(args.runtime).resolve(), Path(args.reports).resolve()
    dep_pins = load(reports / 'frontend_dependencies.json')

    def check_dependencies():
        for path, expected in dep_pins.items():
            require(sha(Path(path).read_bytes()) == expected, 'liveFrontendDependencyChanged')

    class LiveRun(Run):
        def __init__(self, *positional, **named):
            self.host_worker = None
            self.worker_rows = []
            super().__init__(*positional, **named)
            self.worker_argv = [sys.executable, str(HERE.parent / 'host_runtime/host.py'), 'serve',
                                '--config', str(self.root / 'host_config.json'), '--cas', str(self.host_cas.root)]
            self.worker_log = (self.root / 'host_worker.stderr').open('wb')
            self.worker_started = time.perf_counter_ns()
            self.host_worker = subprocess.Popen(self.worker_argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                                 stderr=self.worker_log)
            require(select.select([self.host_worker.stdout], [], [], 30)[0], 'hostStartupTimeout')
            require(json.loads(self.host_worker.stdout.readline()) == {'ok': True, 'ready': True}, 'hostReady')
            self.worker_startup_ns = time.perf_counter_ns() - self.worker_started

        def role(self, command, **kwargs):
            if command != 'propose':
                return super().role(command, **kwargs)
            require(set(kwargs) == {'config', 'head', 'authorization', 'cas', 'out'}, 'publicProposalFields')
            require(Path(kwargs['config']).resolve() == self.root / 'host_config.json', 'fixedHostConfig')
            require(Path(kwargs['cas']).resolve() == self.host_cas.root.resolve(), 'fixedHostCAS')
            message = {k: str(kwargs[k]) for k in ['head', 'authorization', 'out']}
            start = time.perf_counter_ns()
            self.host_worker.stdin.write(canonical(message) + b'\n')
            self.host_worker.stdin.flush()
            require(select.select([self.host_worker.stdout], [], [], 180)[0], 'hostReplyTimeout')
            reply = json.loads(self.host_worker.stdout.readline())
            require(reply.get('ok'), 'hostProposalFailed')
            row = {'request': message, 'reply': reply, 'caller_ns': time.perf_counter_ns() - start}
            self.worker_rows.append(row)
            with (self.root / 'host_worker.jsonl').open('ab') as sink:
                sink.write(canonical(row) + b'\n')
            return reply['result']

        def close(self):
            if self.host_worker is not None:
                self.host_worker.stdin.close()
                self.host_worker.wait(timeout=30)
                self.worker_log.close()
            super().close()

    check_dependencies()
    started = time.perf_counter_ns()
    run = LiveRun(runtime / 'run', runtime / 'query_policy.json', binary=Path(args.binary))
    verifier = None
    rpc_rows = []
    accepted = []
    phase_costs = {}

    def vrpc(message):
        raw = canonical(message) + b'\n'
        begin = time.perf_counter_ns()
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
            client.settimeout(120)
            client.connect(cfg['socket'])
            client.sendall(raw)
            with client.makefile('rb') as stream:
                response = stream.readline(2_000_001)
        reply = json.loads(response)
        require(reply.get('ok'), 'verifiedOperationFailed')
        rpc_rows.append({'op': message['op'], 'elapsed_ns': time.perf_counter_ns() - begin,
                         'request_bytes': len(raw), 'response_bytes': len(response), 'reply': reply})
        return reply

    def put(path, kind='ct'):
        raw = Path(path).read_bytes()
        return vrpc({'op': 'put', 'kind': kind, 'sha256': sha(raw), 'data': base64.b64encode(raw).decode()})

    def admit(request):
        first = run.submit(request)
        require(first.get('ok') and first['status'] == 'accepted', 'newAuthorityAdmission')
        envelope = first['envelope']
        if request['action']['kind'] == 'Infer':
            require(first['delivery']['status'] == 'pending', 'publicationWaitsForVerification')
        synced = vrpc({'op': 'sync', 'envelope': envelope})
        require(synced['status'] == 'verified', 'independentVerification')
        if request['action']['kind'] == 'Infer':
            released = run.accepted(request)
            require(released['status'] == 'replayed' and released['envelope'] == envelope, 'sameFinalizedRelease')
            require(released['delivery']['reader']['status'] == 'received', 'verifiedDelivery')
        accepted.append(envelope)
        return envelope

    try:
        run.stop(run.reader)
        baseline_cfg = run.rcfg
        private_reader = run.root / '.private/verified_reader'
        private_reader.mkdir(mode=0o700)
        cfg = {**baseline_cfg, 'db': str(private_reader / 'answers.sqlite3'),
               'cas': str(run.root / 'verified_cas'),
               'command_log': str(run.root / 'verified_commands.jsonl'),
               'verified_reader_source_sha256': sha((HERE / 'service.py').read_bytes())}
        cfg_path = private_reader / 'config.json'
        write_json(cfg_path, cfg, True)
        Path(cfg['socket']).unlink(missing_ok=True)
        with (run.root / 'verified_server.log').open('wb') as log:
            verifier = subprocess.Popen([sys.executable, str(HERE / 'service.py'), '--config', str(cfg_path)],
                                        stdout=log, stderr=log)
        tick = time.monotonic()
        while not Path(cfg['socket']).exists():
            require(verifier.poll() is None and time.monotonic() - tick < 30, 'verifiedStartup')
            time.sleep(.02)
        run.rcfg = cfg
        put(run.root / 'zero.ct')
        for query in sorted((run.root / 'queries').glob('*.json')):
            put(query, 'query')
        private_input = load(args.input)
        route = private_input['route']
        query_index = route * 8

        begin = time.perf_counter_ns()
        before = run.prepare('Infer', route, 'before-live-observation', query_index=query_index)
        admit(before)
        phase_costs['before_infer_ns'] = time.perf_counter_ns() - begin

        begin = time.perf_counter_ns()
        folder = run.work / 'live-learn'
        folder.mkdir()
        write_json(folder / 'head.json', run.head())
        private_work = run.root / '.private/issuer/live_encoder'
        metadata = load(reports / 'frontend_metadata.json')
        frontend_command = [sys.executable, metadata['frontend_path'], '--input', str(Path(args.input).resolve()),
            '--issuer-config', str(run.root / '.private/issuer/config.json'), '--head', str(folder / 'head.json'),
            '--private-workdir', str(private_work), '--out', str(folder / 'issued'),
            '--request-id', 'live-learn', '--nonce', 'nonce-live-learn', '--record-id', 'opaque-live-observation-1']
        check_dependencies()
        encoder_begin = time.perf_counter_ns()
        frontend = subprocess.run(frontend_command, capture_output=True, timeout=300)
        encoder_elapsed = time.perf_counter_ns() - encoder_begin
        # All diagnostics stay private, including any failure from model code.
        dump(runtime / '.private/frontend_process.json', {'argv': frontend_command,
            'exit_code': frontend.returncode, 'stdout': frontend.stdout.decode(), 'stderr': frontend.stderr.decode()}, True)
        require(frontend.returncode == 0, 'liveFrontendFailedSeePrivateDiagnostics')
        frontend_result = json.loads(frontend.stdout)
        require(frontend_result['ok'] and frontend_result['dimension'] == 577, 'liveFrontendOutput')
        check_dependencies()
        auth = folder / 'issued/authorization.json'
        ciphertext = folder / 'issued/fresh.ct'
        run.host_cas.import_file(ciphertext)
        run.upload(ciphertext)
        put(ciphertext)
        run.role('propose', config=run.root / 'host_config.json', head=folder / 'head.json',
                 authorization=auth, cas=run.root / 'host_cas', out=folder / 'request.json')
        learned = load(folder / 'request.json')
        run.upload(run.host_cas.get(learned['proposal']['result_ct']))
        admit(learned)
        phase_costs['live_encoder_and_learn_ns'] = time.perf_counter_ns() - begin

        begin = time.perf_counter_ns()
        after = run.prepare('Infer', route, 'after-live-observation', query_index=query_index)
        admit(after)
        phase_costs['after_infer_ns'] = time.perf_counter_ns() - begin
        answers = run.answers()
        vector = load(private_work / 'vector.json')
        query = load(run.root / 'queries' / f'q{query_index:02d}.json')['coefficients']
        exact = sum(x * y for x, y in zip(vector, query))
        require(set(answers) == {'before-live-observation', 'after-live-observation'}, 'exactAnswerSet')
        require(answers['before-live-observation'] == 0 and answers['after-live-observation'] == exact,
                'privateDirectIntegerComparison')
        check_dependencies()
        status = vrpc({'op': 'verified_status'})
        require(status['revision'] == status['verified_records'] == 3, 'threeVerifiedCommands')
        with sqlite3.connect(cfg['db']) as db:
            state = json.loads(db.execute('SELECT state FROM verified_head').fetchone()[0])
            journal = [json.loads(x[0]) for x in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
        require(journal == accepted and state == run.head()['state'], 'sameActualJournalAndState')
        with sqlite3.connect(baseline_cfg['db']) as db:
            require(db.execute('SELECT count(*) FROM received').fetchone()[0] == 0, 'baselineNoDecryptions')
        costs = collections.defaultdict(list)
        decrypts = 0
        for instance, path in [('main_pipeline', run.root / 'commands.jsonl'),
                               ('verified_reader', run.root / 'verified_commands.jsonl')]:
            for line in path.read_bytes().splitlines():
                row = json.loads(line)
                command = row['command'][1]
                require(row['exit_code'] == 0, 'cryptoSucceeded')
                if row['role'] in ['host', 'authority', 'public_transport']:
                    require(command in ['inspect', 'host-learn', 'host-infer'] and '--sk' not in row['command']
                            and '--vector' not in row['command'], 'publicRoleInputs')
                if command == 'reader-decrypt':
                    require(instance == 'verified_reader' and row['stdout'] is None and row['stderr'] is None
                            and row['private_output_omitted'], 'privateVerifiedReaderOnly')
                    decrypts += 1
                costs[f'{instance}:{row["role"]}:{command}'].append(row['elapsed_ns'])
        require(decrypts == 2, 'exactlyTwoVerifiedDecrypts')
        inner = load(private_work / 'report.json')['live_encoder_result']
        require(inner['cached_quantized_comparison'] is False, 'actualNewTextForward')
        host_stats = run.worker_rows[-1]['reply']['cumulative_stats']
        require(host_stats['requests'] == 3 and host_stats['cas_get_calls'] == host_stats['full_blob_sha256_calls'],
                'persistentHostFullReads')
        inventory = load(metadata['encoder_inventory'])
        report = {'ok': True, 'schema': 'live-text-independent-verified-release-v1',
            'live_text_encoder_executed': True, 'cached_feature_substitution': False,
            'learns': 1, 'infers': 2, 'verified_revision': 3, 'expiries': 0,
            'oracle_comparisons': 2, 'all_oracle_matches': True,
            'output_changed_after_learning': exact != 0, 'utility_accuracy_claim': False,
            'verified_decrypt_calls': 2, 'baseline_decrypt_calls': 0,
            'same_signed_ticket_query_before_after': before['action']['query_ct'] == after['action']['query_ct'],
            'independently_registered_tickets': 2, 'only_verified_finalizations_released': True,
            'same_actual_authority_and_verified_journal_state': True,
            'only_fresh_query_zero_uploaded_to_verifier': True,
            'source_pins': load(reports / 'source_pins.json'),
            'frontend_dependency_pins_before_after_match': True,
            'frontend_dependencies_sha256': sha((reports / 'frontend_dependencies.json').read_bytes()),
            'model_revision': inventory['revision'],
            'encoder_frontend_wall_ns': encoder_elapsed,
            'encoder_subprocess_wall_ns': frontend_result['encoder_wall_ns'],
            'encrypted_signed_issuer_subprocess_wall_ns': frontend_result['issuer_wall_ns'],
            'encoder_model_load_seconds': inner['load_seconds'], 'encoder_feature_seconds': inner['feature_seconds'],
            'whole_path_elapsed_ns': time.perf_counter_ns() - started,
            'phase_wall_costs': phase_costs,
            'host_worker': {'processes': 1, 'startup_ns': run.worker_startup_ns,
                            'cache_entries': run.worker_rows[-1]['reply']['inspection_cache_entries'],
                            'stats': host_stats, 'proposal_caller_ns': sum(x['caller_ns'] for x in run.worker_rows)},
            'crypto_process_costs': {k: {'count': len(v), 'sum_ns': sum(v)} for k, v in sorted(costs.items())},
            'current_state_manifest_bytes': len(canonical(state)),
            'genesis_sha256': digest(run.g), 'final_state_digest': status['state_digest'],
            'scope': ['One private illustrative text through the already-tested plaintext SmolLM issuer frontend; no new utility estimate.',
                      'Same public query policy, source/range attestation, full-key benchmark-R reader and classical role authentication.',
                      'Source/policy hashes are public; text/vector/private scalar contents and their hashes are omitted.',
                      'Frozen public-role snapshots; unchanged original frontend files checked before and after invocation.',
                      'No OS isolation, hidden-encoder provenance proof, master-key-absence or end-to-end post-quantum claim.',
                      'Timing subdivisions overlap; whole-path elapsed includes setup, model work, issuance, public verification and release but excludes staging and report packaging.']}
        dump(reports / 'report.json', report)
        dump(reports / 'accepted_envelopes.json', accepted)
        dump(reports / 'verified_rpc.json', rpc_rows)
        for name in ['commands.jsonl', 'verified_commands.jsonl', 'events.jsonl', 'role_calls.jsonl', 'host_worker.jsonl', 'genesis.json']:
            with gzip.open(reports / (name + '.gz'), 'wb') as sink:
                sink.write((run.root / name).read_bytes())
        print(json.dumps({'ok': True, 'learns': 1, 'verified_outputs': 2,
                          'all_oracle_matches': True, 'output_changed_after_learning': exact != 0}), flush=True)
    finally:
        if verifier is not None and verifier.poll() is None:
            verifier.terminate()
            verifier.wait(timeout=10)
        run.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', required=True, help='Private JSON containing text, route (0/1) and label (-1/+1).')
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--runtime', default=str(HERE / 'runtime/live_001'))
    parser.add_argument('--reports', default=str(HERE / 'reports/live_001'))
    parser.add_argument('--binary', default=str(HERE.parent / 'crypto/target/release/resident-crypto'))
    args = parser.parse_args()
    worker(args) if args.worker else stage(args)


if __name__ == '__main__':
    main()
