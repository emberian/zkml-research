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
        accepted.append(envelope)
        return envelope

    try:
        run.stop(run.reader)
        baseline_cfg = run.rcfg
        private_reader = run.root / '.private/verified_reader'
        private_reader.mkdir(mode=0o700)
        cfg = {**baseline_cfg, 'db': str(run.root / 'verified_state.sqlite3'),
               'socket': baseline_cfg['socket'] + '-verify',
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
        require(route == 0, 'predeclaredPublicRoute')
        query_index = 1  # q01 fixed before any text encoding

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
        check_dependencies()
        replay = run.replay(True)
        status = vrpc({'op': 'verified_status'})
        require(status['revision'] == status['verified_records'] == 3, 'threeVerifiedCommands')
        with sqlite3.connect(cfg['db']) as db:
            state = json.loads(db.execute('SELECT state FROM verified_head').fetchone()[0])
            journal = [json.loads(x[0]) for x in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
            received = db.execute('SELECT count(*) FROM received').fetchone()[0]
            selected = db.execute('SELECT count(*) FROM expected').fetchone()[0]
        require(journal == accepted and state == run.head()['state'], 'sameActualJournalAndState')
        require(received == 0 and selected == 2, 'deferredPrivateRelease')
        with sqlite3.connect(baseline_cfg['db']) as db:
            require(db.execute('SELECT count(*) FROM received').fetchone()[0] == 0, 'baselineNoDecryptions')
        for path in [run.root / 'commands.jsonl', run.root / 'verified_commands.jsonl']:
            for line in path.read_bytes().splitlines():
                row = json.loads(line)
                require(row['exit_code'] == 0 and row['command'][1] != 'reader-decrypt', 'noPublicPhaseDecryptions')
        host_stats = run.worker_rows[-1]['reply']['cumulative_stats']
        require(host_stats['requests'] == 3 and host_stats['cas_get_calls'] == host_stats['full_blob_sha256_calls'],
                'persistentHostFullReads')
        public = {'ok': True, 'schema': 'semantic-live-deferred-public-v1', 'learns': 1, 'infers': 2,
                  'expiries': 0, 'events': 3, 'registered_tickets': selected, 'reader_decryptions': 0,
                  'received_before_private_phase': received, 'verified_revision': status['revision'],
                  'same_actual_authority_and_verified_journal_state': True,
                  'fixed_query_index': query_index,
                  'same_query_before_after': before['action']['query_ct'] == after['action']['query_ct'],
                  'authority_outbox_pending_by_deliberate_transport_withholding': True,
                  'public_replay': replay, 'phase_wall_costs': phase_costs,
                  'encoder_frontend_wall_ns': encoder_elapsed,
                  'encoder_subprocess_wall_ns': frontend_result['encoder_wall_ns'],
                  'issuer_subprocess_wall_ns': frontend_result['issuer_wall_ns'],
                  'host_worker': {'processes': 1, 'startup_ns': run.worker_startup_ns, 'stats': host_stats},
                  'services': [{'pid': p.pid, 'role': role} for p, role in
                               [(run.reader, 'baseline_reader'), (run.authority, 'authority'),
                                (run.host_worker, 'host'), (verifier, 'verifier')]]}
        dump(reports / 'accepted_envelopes.json', accepted)
        dump(reports / 'verified_rpc.json', rpc_rows)
        dump(reports / 'public_storage.json', {'verified_journal': journal, 'verified_state': state,
             'verified_records': 3, 'registered_tickets': selected, 'received': received})
        for name in ['commands.jsonl', 'verified_commands.jsonl', 'events.jsonl', 'role_calls.jsonl',
                     'host_worker.jsonl', 'genesis.json', 'replay.json']:
            with gzip.open(reports / (name + '.gz'), 'wb') as sink:
                sink.write((run.root / name).read_bytes())
    finally:
        if verifier is not None and verifier.poll() is None:
            verifier.terminate()
            verifier.wait(timeout=10)
        run.close()
    require(all(p.poll() is not None for p in [run.reader, run.authority, run.host_worker, verifier]), 'allServicesClosed')
    public['all_services_closed'] = True
    public['public_phase_wall_ns'] = time.perf_counter_ns() - started
    dump(reports / 'public_phase.json', public)
    print(json.dumps({'ok': True, 'events': 3, 'public_replay': True, 'all_services_closed': True,
                      'reader_decryptions': 0}), flush=True)

def main():
    parser=argparse.ArgumentParser()
    for name in ['input','runtime','reports','binary']:parser.add_argument('--'+name,required=True)
    parser.add_argument('--worker',action='store_true')
    args=parser.parse_args();assert args.worker
    worker(args)
if __name__=='__main__':main()
