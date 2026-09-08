#!/usr/bin/env python3
"""Live text -> staged BFV update -> generated proof -> journal commit -> query.

Run with the useful learner's existing ML Python environment. The plaintext
encoder, local adapter/FIFO policy and full BFV reader remain explicit TCB.
"""
from __future__ import annotations
import argparse
import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
REPO = BASE.parent.parent
JOURNAL = HERE.parent / 'multiclass_successor'
LEARNER = REPO / 'research/learn_infer_only/experiments/end_to_end/useful_learner_2026_09_08'
PIPELINE = BASE / 'update_native_emitter/run.py'
NATIVE = BASE / 'proved_operation/target/release/vfhe-proved-operation'
TEMPLATE = BASE / 'arithmetic_coverage/artifacts_expiry/template_ir2.json'
NATIVE_SHA = 'dd41ec2eac52bf35ff8a9c6e736fa4dcb7cb4ae41cec6bace5cf593a3cf87cc6'
TEMPLATE_SHA = '1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7'
sys.path.insert(0, str(JOURNAL))
import service as j
sys.path.insert(0, str(LEARNER))
from learner import Learner, BINARY, BINARY_SHA
from encoder import Encoder

POLICY = {'schema': 'live-proved-fifo-policy-v1', 'capacity': 8,
    'initial': 'Fresh native keygen produces canonical zero ciphertext. All declared classes start empty at event0.',
    'update': 'Use installed class accumulator; old is canonical zero while count<8, otherwise oldest committed input; fresh input is issued from new plaintext text encoding.',
    'visibility': 'Only journal-committed class heads and receipt-derived queues are queryable; staged candidates never supply a successful teach/query result.',
    'scope': 'Plaintext E5 encoder, local authorization/FIFO/adapter and full BFV reader are trusted. Native proof covers ciphertext arithmetic, not these application semantics.'}


def pins():
    selected = j.read(HERE / 'PIPELINES.json')
    j.need(selected['schema'] == 'fast-live-explicit-pipelines-v1'
           and selected['update_pipeline'] == str(PIPELINE), 'explicit_native_update_pipeline')
    j.need(all(j.sha(Path(p).read_bytes()) == h for p, h in selected['source_pins'].items()), 'native_pipeline_pins')
    paths = [Path(__file__), HERE / 'gate.py', HERE / 'run_demo.py', HERE / 'run.py', HERE / 'PIPELINES.json',
             JOURNAL / 'service.py', LEARNER / 'learner.py', LEARNER / 'encoder.py',
             LEARNER / 'config.json', PIPELINE, BINARY, NATIVE, TEMPLATE]
    return {**selected['source_pins'], **{str(p): j.sha(p.read_bytes()) for p in paths}}


def initialize(root, classes):
    root = Path(root).resolve()
    j.need(not root.exists() and len(classes) == len(set(classes)) and 1 <= len(classes) <= 1024
           and all(isinstance(c, str) and c.strip() for c in classes), 'fresh_live_instance_and_classes')
    source_pins = pins()
    j.need(source_pins[str(BINARY)] == BINARY_SHA and source_pins[str(NATIVE)] == NATIVE_SHA
           and source_pins[str(TEMPLATE)] == TEMPLATE_SHA, 'approved_runtime_pins')
    root.mkdir(parents=True, mode=0o700)
    learner = Learner.create(root / 'issuer', 'bfv', capacity=8)
    zero = root / 'issuer/zero.ct'
    zero_sha = j.sha(zero.read_bytes())
    checkpoint = {'schema': 'proved-model-checkpoint-v1', 'global_learner_event': 0,
        'classes': {label: {'acc_sha256': zero_sha, 'learner_event': 0} for label in sorted(classes)},
        'provenance': {'schema': 'fresh-zero-model-import-v1', 'adapter_policy': POLICY,
            'adapter_policy_sha256': j.digest(POLICY), 'live_source_sha256': source_pins[str(Path(__file__))],
            'source_pins_sha256': j.digest(source_pins),
            'zero_scope': 'Native keygen canonical difference fresh-fresh; initial zero checkpoint is trusted application setup, not a proved old model history.'}}
    j.write_json(root / 'checkpoint.json', checkpoint)
    j.write_json(root / 'initial_files.json', {label: str(zero) for label in classes})
    info = j.initialize(root / 'journal', NATIVE, TEMPLATE, root / 'checkpoint.json', root / 'initial_files.json',
                        'fresh-instance-full-bfv-reader', NATIVE_SHA, TEMPLATE_SHA)
    j.write_json(root / 'config.json', {'schema': 'live-proved-learner-v1', 'source_pins': source_pins,
        'policy': POLICY, 'zero_sha256': zero_sha, 'genesis': info['genesis'],
        'key_id': j.header(zero.read_bytes()), 'classes': sorted(classes)})
    return {'ok': True, 'status': 'initialized', 'root': str(root), 'head': info,
            'reader_scope': 'Fresh full BFV reader key exists in this instance only.'}


class Live:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.config = j.read(self.root / 'config.json')
        self.check_pins()
        self.issuer = Learner(self.root / 'issuer')
        # Separate cache, no writes into the frozen learner feature cache.
        self.encoder = Encoder(cache=self.root / 'issuer/.private/features')
        self.service = j.Service(self.root / 'journal')
        j.need(self.service.gid == self.config['genesis'], 'live_genesis')
        provenance = self.service.genesis['initial_checkpoint']['provenance']
        j.need(provenance['adapter_policy'] == POLICY == self.config['policy']
               and provenance['source_pins_sha256'] == j.digest(self.config['source_pins']), 'live_policy_genesis_binding')

    def check_pins(self):
        j.need(all(j.sha(Path(p).read_bytes()) == h for p, h in self.config['source_pins'].items()), 'live_source_or_runtime_changed')

    @contextlib.contextmanager
    def locked(self):
        with (self.root / 'adapter.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            try:
                self.check_pins()
                yield
            finally:
                fcntl.flock(lock, fcntl.LOCK_UN)

    def snapshot(self):
        db = j.connection(self.root / 'journal')
        try:
            db.execute('BEGIN')
            head = self.service.head(db)
            receipts = [j.parse(row[0]) for row in db.execute('SELECT receipt FROM journal ORDER BY revision')]
            db.execute('COMMIT')
        finally:
            db.close()
        queues = {label: [] for label in self.config['classes']}
        for receipt in receipts:
            req = receipt['request']
            origin = j.parse(self.service.cas(req['source_event_sha256']))
            queue = queues[req['learner_class']]
            old = queue[0] if len(queue) == 8 else self.config['zero_sha256']
            j.need(origin['adapter_policy_sha256'] == j.digest(POLICY) and req['payloads']['old'] == old,
                   'committed_fifo_policy')
            if len(queue) == 8:
                queue.pop(0)
            queue.append(req['payloads']['fresh'])
        j.need(len(receipts) == head['head']['revision'] == head['head']['learner_event'], 'live_receipt_count')
        return head, queues

    def vector(self, text):
        with contextlib.redirect_stdout(sys.stderr):
            vector = self.encoder.encode([text])[0].tolist()
        return vector

    def proposal(self, request_id):
        j.need(isinstance(request_id, str) and re.fullmatch(r'[A-Za-z0-9_-]{1,80}', request_id) is not None, 'request_id_format')
        return self.root / 'proposals' / request_id

    def pipeline(self, case, output, proposal):
        argv = [sys.executable, '-B', str(PIPELINE), str(case), str(output), '--threads', '4', '--step-timeout', '300']
        started = time.monotonic_ns()
        with (proposal / 'pipeline.stdout').open('wb') as stdout, (proposal / 'pipeline.stderr').open('wb') as stderr:
            proc = subprocess.Popen(argv, stdout=stdout, stderr=stderr, start_new_session=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
            timed_out = False
            try:
                code = proc.wait(timeout=900)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    pass
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                code = proc.wait(timeout=10)
        try:
            os.killpg(proc.pid, 0)
            group_absent = False
        except ProcessLookupError:
            group_absent = True
        if not group_absent:
            # No downstream private read if any descendant outlived the runner.
            for sig in (signal.SIGTERM, signal.SIGKILL):
                try:
                    os.killpg(proc.pid, sig)
                except ProcessLookupError:
                    break
                until = time.monotonic() + 5
                while time.monotonic() < until:
                    try:
                        os.killpg(proc.pid, 0)
                    except ProcessLookupError:
                        break
                    time.sleep(0.05)
            j.write_json(proposal / 'pipeline_command.json', {'argv': argv, 'exit_code': code,
                         'timed_out': timed_out, 'public_descendant_outlived_pipeline': True})
            raise j.Refused('public_descendant_outlived_pipeline')
        record = {'argv': argv, 'exit_code': code, 'elapsed_ns': time.monotonic_ns() - started,
                  'timed_out': timed_out, 'public_process_group_absent': group_absent}
        j.write_json(proposal / 'pipeline_command.json', record)
        j.need(code == 0 and not timed_out, 'proof_pipeline_failed', record)
        result = j.read(output / 'result.json')
        j.need(result['verified'] is True and result['approved_template_sha256'] == TEMPLATE_SHA
               and result['runtime_sha256'] == NATIVE_SHA
               and result['proof']['proof_sha256'] == j.sha((output / 'proof/proof.bin').read_bytes()), 'fresh_generated_proof')
        self.check_pins()
        return result

    def stage(self, label, text, request_id):
        with self.locked():
            j.need(label in self.config['classes'] and isinstance(text, str) and text.strip(), 'live_class_and_text')
            proposal = self.proposal(request_id)
            if proposal.exists():
                meta = j.read(proposal / 'proposal.json')
                j.need(meta['label'] == label and meta['text_sha256'] == j.sha(text.encode()), 'proposal_id_conflict')
                j.need((proposal / 'staged.json').exists(), 'incomplete_existing_proposal_use_new_id')
                return j.read(proposal / 'staged.json')
            head, queues = self.snapshot()
            event = head['head']['learner_event'] + 1
            entry, queue = head['head']['classes'][label], queues[label]
            old_sha = queue[0] if len(queue) == 8 else self.config['zero_sha256']
            proposal.mkdir(parents=True)
            case = proposal / 'candidate'
            case.mkdir()
            meta = {'schema': 'live-text-proposal-v1', 'request_id': request_id, 'label': label,
                'text_sha256': j.sha(text.encode()), 'parent': head, 'event': event,
                'visibility': 'tentative; not queryable or a successful teach response'}
            j.write_json(proposal / 'proposal.json', meta)
            vector = self.vector(text)
            private_vector = self.root / 'issuer/.private' / (request_id + '.json')
            j.write_json(private_vector, vector)
            try:
                self.issuer.crypto('issuer-encrypt', pk=self.root / 'issuer/public.key', vector=private_vector, out=case / 'fresh.ct')
            finally:
                private_vector.unlink(missing_ok=True)
            j.write(case / 'acc.ct', self.service.cas(entry['acc_sha256']))
            j.write(case / 'old.ct', self.service.cas(old_sha))
            operation = self.issuer.crypto('host-learn', acc=case / 'acc.ct', fresh=case / 'fresh.ct',
                                           old=case / 'old.ct', out=case / 'out.ct')
            source_event = {'schema': 'useful-prototype-expiry-proof-join-v1', 'event': event,
                'class': label, 'prior_state_event': entry['learner_event'], 'operation': 'out=acc+fresh-old',
                'adapter_policy_sha256': j.digest(POLICY), 'text_sha256': j.sha(text.encode()),
                'fifo_capacity': 8, 'class_count_before': len(queue), 'class_count_after': min(8, len(queue) + 1),
                'zero_outgoing': len(queue) < 8, 'files': {n: {'sha256': j.sha((case / (n + '.ct')).read_bytes()),
                    'bytes': (case / (n + '.ct')).stat().st_size} for n in j.NAMES},
                'actual_host_result': operation,
                'scope': 'New live plaintext-encoded text and actual staged BFV arithmetic. Encoder/FIFO authorization remains adapter TCB.'}
            j.write_json(case / 'source_event.json', source_event)
            proof_result = self.pipeline(case, proposal / 'proved', proposal)
            j.request_bundle(self.root / 'journal', proposal / 'proved/case', proposal / 'proved/proof/proof.bin',
                             request_id, proposal / 'request.json')
            # Staging may be long. Bind to the original state even if an external
            # journal writer bypassed this adapter's single-writer lock.
            req = j.read(proposal / 'request.json')['request']
            j.need(req['parent_sha256'] == head['head_sha256'], 'parent_changed_while_proving')
            staged = {'status': 'staged', 'committed': False, 'visible_to_query': False,
                'request_id': request_id, 'label': label, 'event': event,
                'proof_sha256': proof_result['proof']['proof_sha256'], 'pipeline_seconds': proof_result['elapsed_seconds'],
                'parent_sha256': head['head_sha256'], 'bundle': str(proposal / 'request.json')}
            j.write_json(proposal / 'staged.json', staged)
            return staged

    def commit(self, request_id):
        with self.locked():
            proposal = self.proposal(request_id)
            j.need((proposal / 'staged.json').exists(), 'proposal_not_proved')
            staged = j.read(proposal / 'staged.json')
            req = j.read(proposal / 'request.json')['request']
            db = j.connection(self.root / 'journal')
            try:
                prior = self.service.prior(db, req)
            finally:
                db.close()
            if prior is None:
                head, queues = self.snapshot()
                queue = queues[req['learner_class']]
                expected_old = queue[0] if len(queue) == 8 else self.config['zero_sha256']
                j.need(req['parent_sha256'] == head['head_sha256'] and req['payloads']['old'] == expected_old,
                       'current_live_parent_and_fifo')
            # The frozen journal executes native verification again, then checks
            # the class and global parent under its authoritative write lock.
            result = self.service.submit(proposal / 'request.json')
            j.need(result['ok'] is True and result['status'] in ('accepted', 'replayed'), 'journal_commit_required')
            head, queues = self.snapshot()
            response = {'ok': True, 'status': 'committed', 'request_id': request_id, 'label': staged['label'],
                'accepted_event': result['receipt']['request']['learner_event'], 'receipt_sha256': result['receipt_sha256'],
                'proof_sha256': staged['proof_sha256'], 'head': head,
                'counts': {c: len(q) for c, q in queues.items()}, 'idempotent_retry': result['status'] == 'replayed'}
            j.write_json(proposal / 'committed.json', response)
            return response

    def teach(self, label, text, request_id):
        self.stage(label, text, request_id)
        return self.commit(request_id)

    def query(self, text):
        with self.locked():
            head, queues = self.snapshot()
            vector = self.vector(text)
            directory = self.root / 'queries' / uuid.uuid4().hex
            directory.mkdir(parents=True)
            j.write_json(directory / 'vector.json', vector)
            self.issuer.crypto('encode-query', vector=directory / 'vector.json', out=directory / 'query.json')
            outputs, host_results = {}, {}
            for index, label in enumerate(sorted(head['head']['classes'])):
                path = directory / (str(index) + '.ct')
                acc_sha = head['head']['classes'][label]['acc_sha256']
                self.service.cas(acc_sha)
                host_results[label] = self.issuer.crypto('host-infer', acc=self.root / 'journal/cas' / acc_sha,
                    query=directory / 'query.json', out=path)
                j.need(host_results[label]['acc_sha256'] == acc_sha, 'query_accepted_accumulator')
                outputs[label] = str(path)
            ticket = {'revision': head['head']['learner_event'], 'outputs': outputs, 'counts': {c: len(q) for c, q in queues.items()}}
            public_complete = {'schema': 'accepted-model-public-query-v1', 'head': head, 'ticket': ticket,
                'host_results': host_results, 'all_public_host_processes_closed': True,
                'private_receive_started': False, 'scope': 'Ciphertexts evaluated only from this journal-committed model snapshot.'}
            j.write_json(directory / 'public_complete.json', public_complete)
            self.check_pins()
            # All public proof/commit/query subprocesses are complete before this
            # surviving full-key reader receives answers.
            answer = self.issuer.receive(ticket)
            response = {'ok': True, 'status': 'answered_from_committed_model', 'head': head,
                'answer': answer, 'public_query_record': str(directory / 'public_complete.json'),
                'public_query_record_sha256': j.sha((directory / 'public_complete.json').read_bytes()),
                'reader_scope': 'Actual surviving full BFV reader; no restricted-release/confidentiality claim.'}
            j.write_json(directory / 'answer.json', response)
            return response

    def status(self):
        with self.locked():
            head, queues = self.snapshot()
            return {'ok': True, 'head': head, 'counts': {c: len(q) for c, q in queues.items()}}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    init = sub.add_parser('init')
    init.add_argument('directory', type=Path)
    init.add_argument('--class', dest='classes', action='append', required=True)
    for name in ('stage', 'commit', 'teach', 'query', 'teach-query', 'status'):
        cmd = sub.add_parser(name)
        cmd.add_argument('directory', type=Path)
        if name in ('stage', 'teach', 'teach-query'):
            cmd.add_argument('--label', required=True)
            cmd.add_argument('--text', required=True)
        if name in ('stage', 'commit', 'teach', 'teach-query'):
            cmd.add_argument('--request-id', required=True)
        if name == 'query':
            cmd.add_argument('--text', required=True)
        if name == 'teach-query':
            cmd.add_argument('--query-text', required=True)
    args = p.parse_args()
    if args.command == 'init':
        result = initialize(args.directory, args.classes)
    else:
        model = Live(args.directory)
        if args.command == 'status':
            result = model.status()
        elif args.command == 'query':
            result = model.query(args.text)
        elif args.command == 'commit':
            result = model.commit(args.request_id)
        elif args.command == 'stage':
            result = model.stage(args.label, args.text, args.request_id)
        else:
            result = model.teach(args.label, args.text, args.request_id)
            if args.command == 'teach-query':
                result = {'ok': True, 'teach': result, 'query': model.query(args.query_text)}
        result['encoder_stats'] = model.encoder.stats
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'ok': False, 'error': str(error), 'error_type': type(error).__name__}), file=sys.stderr)
        raise SystemExit(2)
