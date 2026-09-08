#!/usr/bin/env python3
"""Prove every active class query before any full-reader receive operation."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
LIVE = HERE
sys.path.insert(0, str(LIVE))
import live
from live import j

PIPELINE = BASE / 'query_native_emitter/run.py'
NATIVE = BASE / 'query_runtime/target/release/vfhe-query-runtime'
TEMPLATE = BASE / 'query_arithmetic/artifacts/template_ir2.json'
NATIVE_SHA = '9566638eef8f0dce7c5d3edd351f1e29da6301164ccbe1d8451ce642874c8c2c'
TEMPLATE_SHA = 'f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d'
POLICY = {'schema': 'all-active-class-query-gate-v1',
    'coverage': 'Every and only class with a nonempty committed FIFO must have one accepted joined query proof for the common query and committed model snapshot.',
    'binding': 'Bind request ID, gate/model genesis, current global head/revision/model root, recipient, exact counts and every accumulator/query/output/proof/rows hash.',
    'private_order': 'Fresh native verification for every active class and authoritative current-head check, durable public acceptance, then full-reader receive.',
    'scope': 'Plaintext encoder, query/NTT parser, protocol binding, FIFO/counts, BFV decoder and shared OS are TCB; the full reader survives.'}


def source_pins():
    selected = j.read(HERE / 'PIPELINES.json')
    j.need(selected['schema'] == 'fast-live-explicit-pipelines-v1'
           and selected['query_pipeline'] == str(PIPELINE), 'explicit_native_query_pipeline')
    j.need(all(j.sha(Path(p).read_bytes()) == h for p, h in selected['source_pins'].items()), 'native_pipeline_pins')
    paths = [Path(__file__), LIVE / 'live.py', HERE / 'PIPELINES.json', PIPELINE, PIPELINE.parent / 'PIPELINE.json', NATIVE, TEMPLATE]
    return {**selected['source_pins'], **{str(p): j.sha(p.read_bytes()) for p in paths}}


def create(root, classes):
    root = Path(root).resolve()
    j.need(not root.exists(), 'fresh_query_gate_instance')
    pins = source_pins()
    j.need(pins[str(NATIVE)] == NATIVE_SHA and pins[str(TEMPLATE)] == TEMPLATE_SHA, 'approved_query_runtime_and_template')
    root.mkdir(parents=True, mode=0o700)
    initial = live.initialize(root / 'model', classes)
    genesis = {'schema': 'proved-query-gate-genesis-v1', 'source_pins': pins, 'policy': POLICY,
        'model_genesis': initial['head']['genesis'], 'native_sha256': NATIVE_SHA, 'template_sha256': TEMPLATE_SHA,
        'recipient_id': initial['head']['head']['recipient_id']}
    j.write_json(root / 'query_genesis.json', genesis)
    return {'ok': True, 'root': str(root), 'query_genesis': j.digest(genesis), 'model': initial}


class QueryGate:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.genesis = j.read(self.root / 'query_genesis.json')
        self.gid = j.digest(self.genesis)
        self.check_pins()
        self.model = live.Live(self.root / 'model')
        j.need(self.model.service.gid == self.genesis['model_genesis'], 'bound_model_genesis')

    def check_pins(self):
        j.need(j.read(self.root / 'query_genesis.json') == self.genesis and self.genesis['policy'] == POLICY, 'query_gate_genesis_changed')
        j.need(all(j.sha(Path(p).read_bytes()) == h for p, h in self.genesis['source_pins'].items()), 'query_gate_source_or_runtime_changed')

    def directory(self, request_id):
        self.model.proposal(request_id)  # Reuse the frozen bounded identifier parser.
        return self.root / 'queries' / request_id

    def command(self, argv, directory, label, timeout):
        before = time.monotonic_ns()
        with (directory / (label + '.stdout')).open('wb') as stdout, (directory / (label + '.stderr')).open('wb') as stderr:
            p = subprocess.Popen([str(x) for x in argv], stdout=stdout, stderr=stderr, start_new_session=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', RAYON_NUM_THREADS='4'))
            timed_out = False
            try:
                code = p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                try:
                    os.killpg(p.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    p.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                code = p.wait(timeout=10)
        try:
            os.killpg(p.pid, 0)
            absent = False
        except ProcessLookupError:
            absent = True
        if not absent:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        record = {'argv': [str(x) for x in argv], 'exit_code': code, 'elapsed_ns': time.monotonic_ns() - before,
                  'timed_out': timed_out, 'public_process_group_absent': absent}
        j.write_json(directory / (label + '.command.json'), record)
        j.need(code == 0 and not timed_out and absent, 'public_query_command_failed', record)
        return record

    def prepare(self, text, request_id):
        with self.model.locked():
            self.check_pins()
            directory = self.directory(request_id)
            j.need(not directory.exists(), 'fresh_query_request_id')
            head, queues = self.model.snapshot()
            active = sorted(c for c, q in queues.items() if q)
            j.need(active, 'no_active_classes')
            directory.mkdir(parents=True)
            j.write_json(directory / 'intent.json', {'request_id': request_id, 'text_sha256': j.sha(text.encode()),
                         'head': head, 'active_classes': active, 'status': 'public_query_preparation_no_receive'})
            vector = self.model.vector(text)
            j.write_json(directory / 'vector.json', vector)
            self.model.issuer.crypto('encode-query', vector=directory / 'vector.json', out=directory / 'query.json')
            qh = j.sha((directory / 'query.json').read_bytes())
            entries, files, pipeline_records = {}, {}, {}
            for index, label in enumerate(active):
                acc_sha = head['head']['classes'][label]['acc_sha256']
                acc = self.model.root / 'journal/cas' / acc_sha
                self.model.service.cas(acc_sha)
                out = directory / (str(index) + '.ct')
                host = self.model.issuer.crypto('host-infer', acc=acc, query=directory / 'query.json', out=out)
                j.need(host['acc_sha256'] == acc_sha and host['query_sha256'] == qh, 'actual_host_query_binding')
                job = directory / ('proof' + str(index))
                print(json.dumps({'phase': 'prove-query-class', 'class': label, 'active_classes': len(active)}), file=sys.stderr, flush=True)
                self.command([sys.executable, '-B', PIPELINE, acc, directory / 'query.json', out, job],
                             directory, 'pipeline' + str(index), 1800)
                result = j.read(job / 'result.json')
                j.need(result['verified'] is True and result['template_sha256'] == TEMPLATE_SHA
                       and result['native_sha256'] == NATIVE_SHA, 'query_pipeline_verified')
                case, proof = job / 'case', job / 'proof/proof.bin'
                entries[label] = {'acc_sha256': acc_sha, 'out_sha256': j.sha(out.read_bytes()),
                    'proof_sha256': j.sha(proof.read_bytes()), 'rows_sha256': j.sha((case / 'public_rows.json').read_bytes())}
                j.need(j.sha((case / 'acc.ct').read_bytes()) == acc_sha
                       and j.sha((case / 'query.json').read_bytes()) == qh
                       and j.sha((case / 'out.ct').read_bytes()) == entries[label]['out_sha256'], 'pipeline_exact_query_case')
                files[label] = {'case': str(case), 'proof': str(proof)}
                pipeline_records[label] = {'job': str(job), 'result_sha256': j.sha((job / 'result.json').read_bytes()), 'host_result': host}
            req = {'schema': 'all-active-class-query-request-v1', 'request_id': request_id, 'gate_genesis': self.gid,
                'model_genesis': self.model.service.gid, 'head_sha256': head['head_sha256'],
                'revision': head['head']['revision'], 'model_root': head['head']['model_root'],
                'recipient_id': self.genesis['recipient_id'], 'template_sha256': TEMPLATE_SHA,
                'query_sha256': qh, 'active_classes': active, 'counts': {c: len(queues[c]) for c in active}, 'classes': entries}
            self.binding(req, files)
            j.write_json(directory / 'request.json', {'request': req, 'files': files})
            staged = {'status': 'prepared_not_received', 'request': req, 'request_sha256': j.digest(req),
                      'bundle': str(directory / 'request.json'), 'pipeline_records': pipeline_records,
                      'private_receive_calls': 0}
            j.write_json(directory / 'prepared.json', staged)
            return staged

    def binding(self, req, files):
        expected = {'schema', 'request_id', 'gate_genesis', 'model_genesis', 'head_sha256', 'revision', 'model_root',
                    'recipient_id', 'template_sha256', 'query_sha256', 'active_classes', 'counts', 'classes'}
        j.need(set(req) == expected and req['schema'] == 'all-active-class-query-request-v1', 'query_request_schema')
        self.directory(req['request_id'])
        j.need(req['gate_genesis'] == self.gid and req['model_genesis'] == self.model.service.gid
               and req['recipient_id'] == self.genesis['recipient_id'] and req['template_sha256'] == TEMPLATE_SHA, 'query_genesis_template_recipient')
        head, queues = self.model.snapshot()
        active = sorted(c for c, q in queues.items() if q)
        j.need(req['active_classes'] == active and active and set(req['classes']) == set(active)
               and set(files) == set(active) and req['counts'] == {c: len(queues[c]) for c in active}, 'active_class_coverage')
        j.need(type(req['revision']) is int and req['revision'] == head['head']['revision']
               and req['head_sha256'] == head['head_sha256'] and req['model_root'] == head['head']['model_root'], 'current_accepted_query_head')
        for label, entry in req['classes'].items():
            j.need(set(entry) == {'acc_sha256', 'out_sha256', 'proof_sha256', 'rows_sha256'}
                   and entry['acc_sha256'] == head['head']['classes'][label]['acc_sha256']
                   and set(files[label]) == {'case', 'proof'}, 'query_class_accumulator')
        hashes = [req['query_sha256'], *[h for entry in req['classes'].values() for h in entry.values()]]
        j.need(all(isinstance(h, str) and len(h) == 64 and all(c in '0123456789abcdef' for c in h) for h in hashes), 'query_hash_identifiers')
        return head

    def accept(self, bundle_path):
        with self.model.locked():
            self.check_pins()
            bundle = j.read(bundle_path)
            j.need(set(bundle) == {'request', 'files'}, 'query_bundle_schema')
            req, files = bundle['request'], bundle['files']
            head = self.binding(req, files)
            directory = self.directory(req['request_id'])
            acceptance_path = directory / 'public_acceptance.json'
            if acceptance_path.exists():
                saved = j.read(acceptance_path)
                j.need(saved['request_sha256'] == j.digest(req), 'query_request_id_conflict')
                return saved
            staging = directory / 'verified'
            j.need(not staging.exists(), 'fresh_query_verification_stage')
            staging.mkdir(parents=True)
            checks, outputs = {}, {}
            for index, label in enumerate(req['active_classes']):
                entry, paths = req['classes'][label], files[label]
                supplied = Path(paths['case'])
                expected = {'acc.ct': entry['acc_sha256'], 'query.json': req['query_sha256'], 'out.ct': entry['out_sha256']}
                for name, h in expected.items():
                    j.need(j.sha(j.regular_bytes(supplied / name)) == h, 'query_payload_hash')
                proof_bytes = j.regular_bytes(paths['proof'])
                j.need(j.sha(proof_bytes) == entry['proof_sha256'], 'query_proof_hash')
                stage = staging / str(index)
                self.command([NATIVE, 'export', supplied / 'acc.ct', supplied / 'query.json', supplied / 'out.ct', stage],
                             directory, 'gate_export' + str(index), 60)
                for name, h in expected.items():
                    j.need(j.sha((stage / name).read_bytes()) == h, 'staged_query_payload_hash')
                j.need(j.sha((stage / 'public_rows.json').read_bytes()) == entry['rows_sha256'], 'reconstructed_query_rows')
                j.write(stage / 'proof.bin', proof_bytes)
                self.command([NATIVE, 'verify', TEMPLATE, stage, stage / 'proof.bin'], directory, 'gate_verify' + str(index), 60)
                accepted = j.read(directory / ('gate_verify' + str(index) + '.stdout'))
                j.need(accepted['verified'] is True and accepted['changed_output_rejected'] is False
                       and accepted['acc_sha256'] == entry['acc_sha256'] and accepted['out_sha256'] == entry['out_sha256']
                       and accepted['query_sha256'] == req['query_sha256'] and accepted['proof_sha256'] == entry['proof_sha256'], 'actual_joined_query_acceptance')
                checks[label] = accepted
                outputs[label] = str(stage / 'out.ct')
            self.check_pins()
            # Authoritative current-head check after every proof acceptance.
            db = j.connection(self.model.root / 'journal')
            try:
                db.execute('BEGIN IMMEDIATE')
                j.need(self.model.service.head(db) == head, 'query_head_changed_during_verification')
                acceptance = {'schema': 'all-active-class-public-acceptance-v1', 'request': req,
                    'request_sha256': j.digest(req), 'head': head, 'native_acceptances': checks,
                    'query_gate_genesis': self.gid, 'all_active_classes_verified': True,
                    'head_checked_under_journal_write_lock': True, 'public_process_groups_absent': True,
                    'private_receive_calls': 0, 'ticket': {'revision': head['head']['learner_event'],
                        'counts': req['counts'], 'outputs': outputs}}
                j.write_json(acceptance_path, acceptance)
                db.execute('COMMIT')
            finally:
                db.close()
            return acceptance

    def receive(self, request_id):
        with self.model.locked():
            self.check_pins()
            directory = self.directory(request_id)
            acceptance = j.read(directory / 'public_acceptance.json')
            bundle = j.read(directory / 'request.json')
            req, files = bundle['request'], bundle['files']
            head = self.binding(req, files)
            j.need(acceptance['request_sha256'] == j.digest(req) and acceptance['request'] == req
                   and acceptance['head'] == head and acceptance['all_active_classes_verified'] is True
                   and acceptance['query_gate_genesis'] == self.gid
                   and acceptance['head_checked_under_journal_write_lock'] is True
                   and set(acceptance['native_acceptances']) == set(req['active_classes']), 'accepted_query_before_receive')
            for label, path in acceptance['ticket']['outputs'].items():
                j.need(j.sha(j.regular_bytes(path)) == req['classes'][label]['out_sha256'], 'accepted_answer_ciphertext')
                check = acceptance['native_acceptances'][label]
                j.need(check['verified'] is True and check['changed_output_rejected'] is False
                       and check['acc_sha256'] == req['classes'][label]['acc_sha256']
                       and check['out_sha256'] == req['classes'][label]['out_sha256']
                       and check['proof_sha256'] == req['classes'][label]['proof_sha256']
                       and check['query_sha256'] == req['query_sha256'], 'retained_query_proof_acceptance')
            j.need(set(acceptance['ticket']['outputs']) == set(req['active_classes'])
                   and acceptance['ticket']['counts'] == req['counts']
                   and acceptance['ticket']['revision'] == head['head']['learner_event'], 'complete_reader_ticket')
            # This is the first and only private operation on this new query path.
            answer = self.model.issuer.receive(acceptance['ticket'])
            result = {'ok': True, 'status': 'answered_after_all_active_query_proofs', 'request_id': request_id,
                'head': head, 'answer': answer, 'public_acceptance_sha256': j.sha((directory / 'public_acceptance.json').read_bytes()),
                'scope': 'Actual full BFV reader after public proof gate; no decryption restriction claim.'}
            j.write_json(directory / 'answer.json', result)
            return result

    def query(self, text, request_id):
        self.prepare(text, request_id)
        self.accept(self.directory(request_id) / 'request.json')
        return self.receive(request_id)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    init = sub.add_parser('init'); init.add_argument('directory', type=Path); init.add_argument('--class', dest='classes', action='append', required=True)
    for name in ('teach', 'query', 'status'):
        cmd = sub.add_parser(name); cmd.add_argument('directory', type=Path)
        if name != 'status':
            cmd.add_argument('--text', required=True); cmd.add_argument('--request-id', required=True)
        if name == 'teach': cmd.add_argument('--label', required=True)
    args = p.parse_args()
    if args.command == 'init': result = create(args.directory, args.classes)
    else:
        gate = QueryGate(args.directory)
        if args.command == 'teach': result = gate.model.teach(args.label, args.text, args.request_id)
        elif args.command == 'query': result = gate.query(args.text, args.request_id)
        else: result = gate.model.status()
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'ok': False, 'error': str(error), 'error_type': type(error).__name__}), file=sys.stderr)
        raise SystemExit(2)
