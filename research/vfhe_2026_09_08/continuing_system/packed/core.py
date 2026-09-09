"""Durable FIFO8 class centroids: eight independent classes per encrypted bank.

This is a separate genesis and journal. It does not convert the example-lane
learner. The full reader, known encoder/inputs and native implementation remain
explicit assumptions; local acceptance order does not remove reader custody.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import importlib.util
import json
import os
from pathlib import Path
import threading

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('packed_backend', HERE / 'backend.py')
packed_backend = importlib.util.module_from_spec(spec); spec.loader.exec_module(packed_backend)
base = packed_backend.base
backend, j, Refused = base.backend, base.j, base.Refused
CAPACITY = 8
POLICY = {'schema': 'packed-class-centroid-policy-v1', 'capacity': 8, 'classes_per_bank': 8,
    'layout': 'Supplied class order fixes bank=index//8 and lane=index%8 at genesis',
    'update': 'Bank out=acc+fresh-old; each class uses its fixed lane; subtract its exact oldest contribution after eight live examples',
    'query': 'All occupied banks require fresh complete matched linear proofs before any private receive; each lane is one class sum',
    'features': {'dimension': 576, 'coordinate_bound': 32, 'squared_norm_bound': 20000},
    'class_sum_bound': 160000, 'score': 'signed class sum / current class count; label-order ties',
    'reader': 'Surviving full BFV reader; software acceptance is not cryptographic decryption restriction',
    'scope': 'Public encoder, inputs, setup/key validity, exact class/count/FIFO policy, parser/NTT/controller/SQLite and proof backend TCB'}


def state_root(classes, banks):
    return j.digest({'schema': 'packed-class-bank-map-v1', 'classes': classes, 'banks': banks})


def metadata(root=None):
    value = {'schema': 'packed-class-sum-display-v1', 'score_kind': 'linear', 'proof_backend': 'matched',
        'score_formula': 'class_sum / count', 'score_signed': True, 'classes_per_bank': 8,
        'fifo_capacity': 8, 'update_proofs': 32, 'infer_proofs_per_bank': 352,
        'layout': 'fixed class lanes', 'sum_key': 'sum_dot'}
    if root is not None:
        g = j.read(Path(root).expanduser().resolve() / 'journal/genesis.json')
        j.need(g['schema'] == 'packed-class-centroid-genesis-v1', 'packed_genesis_required')
        value['class_layout'] = g['layout']
        value['bank_count'] = len(g['initial_banks'])
    return value


def initialize(root, classes):
    backend.install_signal_handlers()
    root = Path(root).expanduser().resolve()
    j.need(isinstance(classes, (list, tuple)) and 1 <= len(classes) <= 1024, 'class_count')
    j.need(all(isinstance(x, str) and 0 < len(x) <= 256 for x in classes), 'class_labels')
    classes = list(classes); j.need(len(set(classes)) == len(classes), 'unique_classes')
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    import fcntl
    with (root / 'adapter.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if (root / 'initialized.json').exists():
            g = j.read(root / 'journal/genesis.json')
            j.need(g['schema'] == 'packed-class-centroid-genesis-v1' and g['classes'] == classes, 'initialization_layout_conflict')
            packed_backend.Backend(g['backend'])
            return j.read(root / 'initialized.json')
        request_path = root / 'initializing.json'
        if request_path.exists():
            request = j.read(request_path)
            j.need(request['schema'] == 'packed-class-initialization-v1' and request['classes'] == classes, 'initialization_layout_conflict')
            engine = packed_backend.Backend(request['backend'])
        else:
            j.need(not any(p.name != 'adapter.lock' for p in root.iterdir()), 'fresh_packed_instance_required')
            engine = packed_backend.Backend()
            j.write_json(request_path, {'schema': 'packed-class-initialization-v1', 'classes': classes,
                                       'backend': engine.descriptor, 'started_utc': backend.now()})
        issuer = root / 'issuer'
        if not (issuer / '.setup_complete.json').exists():
            attempts = root / 'setup_attempts'; attempts.mkdir(exist_ok=True)
            live = backend.live_processes(attempts); j.need(not live, 'setup_process_still_running', live)
            recovered = next((p / 'issuer' for p in sorted(attempts.glob('attempt*'))
                              if (p / 'issuer/.setup_complete.json').exists()), None)
            if recovered is None:
                j.need(all(base._empty_failed_setup(p) for p in attempts.iterdir()), 'incomplete_setup_preserved')
                attempt = attempts / f'attempt{len(list(attempts.iterdir())):03}'
                attempt.mkdir(); (attempt / 'issuer').mkdir(mode=0o700)
                engine.issuer.native('keygen', attempt, dir=attempt / 'issuer')
                recovered = attempt / 'issuer'
                names = ('public.key', 'evaluation.key', 'parameters.json', 'zero.ct', '.private/reader.key')
                j.write_json(recovered / '.setup_complete.json', {'files': {n: backend.sha(recovered / n) for n in names}, 'finished_utc': backend.now()})
            j.need(not issuer.exists(), 'incomplete_issuer_requires_recovery')
            os.replace(recovered, issuer); j.sync_directory(root)
        for name, digest in j.read(issuer / '.setup_complete.json')['files'].items():
            j.need(backend.sha(issuer / name) == digest, 'setup_artifact_changed')
        journal = root / 'journal'; journal.mkdir(exist_ok=True)
        zero = (issuer / 'zero.ct').read_bytes(); zero_hash = j.sha(zero)
        j.write(journal / 'cas' / zero_hash, zero)
        layout = {c: {'bank': str(i // 8), 'lane': i % 8} for i, c in enumerate(classes)}
        initial = {c: {**layout[c], 'teaches': 0, 'queue': []} for c in classes}
        banks = {str(i): {'acc_sha256': zero_hash} for i in range((len(classes) + 7) // 8)}
        genesis_path = journal / 'genesis.json'
        if genesis_path.exists():
            genesis = j.read(genesis_path)
            j.need(genesis['schema'] == 'packed-class-centroid-genesis-v1' and genesis['classes'] == classes
                   and genesis['backend'] == engine.descriptor, 'genesis_initialization_conflict')
        else:
            genesis = {'schema': 'packed-class-centroid-genesis-v1', 'classes': classes, 'layout': layout,
                'backend': engine.descriptor, 'policy': POLICY,
                'recipient_id': backend.sha(issuer / 'public.key'), 'evaluation_key_sha256': backend.sha(issuer / 'evaluation.key'),
                'initial_classes': initial, 'initial_banks': banks, 'zero_sha256': zero_hash, 'created_utc': backend.now()}
            j.write_json(genesis_path, genesis)
        gid = j.digest(genesis)
        state = {'genesis': gid, 'revision': 0, 'classes': initial, 'banks': banks,
                 'model_root': state_root(initial, banks), 'last_receipt_sha256': None}
        db = j.connection(journal)
        try:
            db.execute('BEGIN IMMEDIATE'); base._schema(db)
            row = db.execute('SELECT state FROM head WHERE singleton=1').fetchone()
            if row is None: db.execute('INSERT INTO head VALUES(1,?,?)', (j.canonical(state).decode(), j.digest(state)))
            else: j.need(j.parse(row['state']) == state, 'initial_head_conflict')
            db.execute('COMMIT')
        finally:
            if db.in_transaction: db.execute('ROLLBACK')
            db.close()
        result = {'initialized': True, 'genesis': gid, 'head': state, 'recipient_id': genesis['recipient_id'],
                  'full_reader_key': True, **metadata(root)}
        j.write_json(root / 'initialized.json', result)
        return result


class Live(base.Live):
    """Reuse durable request/phase primitives; all bank semantics are defined here."""
    def __init__(self, root):
        backend.install_signal_handlers()
        self.root = Path(root).expanduser().resolve(); self.journal = self.root / 'journal'
        self.genesis = j.read(self.journal / 'genesis.json'); self.gid = j.digest(self.genesis)
        j.need(self.genesis['schema'] == 'packed-class-centroid-genesis-v1', 'packed_genesis_required')
        self.engine = packed_backend.Backend(self.genesis['backend']); self.backend = self.engine.issuer
        self.encoder = None; self._thread_lock = threading.RLock()
        self.check(); self.reopen()

    def check(self):
        j.need(j.read(self.journal / 'genesis.json') == self.genesis and self.genesis['policy'] == POLICY, 'genesis_policy_changed')
        self.engine.check()
        j.need(backend.sha(self.root / 'issuer/public.key') == self.genesis['recipient_id'] and
               backend.sha(self.root / 'issuer/evaluation.key') == self.genesis['evaluation_key_sha256'], 'public_key_identity')

    def metadata(self): return metadata(self.root)

    def head(self, db=None):
        own = db is None; db = db or j.connection(self.journal)
        try:
            row = db.execute('SELECT state,state_sha256 FROM head WHERE singleton=1').fetchone()
            j.need(row is not None, 'initialized_head'); state = j.parse(row['state'])
            j.need(j.digest(state) == row['state_sha256'] and state['genesis'] == self.gid and
                   state['model_root'] == state_root(state['classes'], state['banks']), 'head_identity')
            return state
        finally:
            if own: db.close()

    def parent(self, state, req):
        j.need(req['label'] in state['classes'], 'declared_class')
        entry = state['classes'][req['label']]
        j.need(req['genesis'] == self.gid and req['recipient_id'] == self.genesis['recipient_id'] and
               req['backend_sha256'] == j.digest(self.engine.descriptor), 'request_genesis_recipient_backend')
        j.need(req['parent_sha256'] == j.digest(state) and req['revision'] == state['revision'] + 1 and
               req['parent_model_root'] == state['model_root'], 'current_model_parent')
        old = entry['queue'][0]['sha256'] if len(entry['queue']) == CAPACITY else self.genesis['zero_sha256']
        j.need(req['bank'] == entry['bank'] and req['lane'] == entry['lane'] and
               req['payloads']['acc_sha256'] == state['banks'][entry['bank']]['acc_sha256'] and
               req['payloads']['old_sha256'] == old, 'current_bank_class_fifo')

    def advance(self, state, req, receipt_sha):
        classes, banks = dict(state['classes']), dict(state['banks'])
        entry = classes[req['label']]; queue = list(entry['queue'])
        if len(queue) == CAPACITY: queue.pop(0)
        queue.append({'sha256': req['payloads']['fresh_sha256'], 'lane': req['lane']})
        classes[req['label']] = {**entry, 'teaches': entry['teaches'] + 1, 'queue': queue}
        banks[req['bank']] = {'acc_sha256': req['payloads']['out_sha256']}
        return {'genesis': self.gid, 'revision': state['revision'] + 1, 'classes': classes, 'banks': banks,
                'model_root': state_root(classes, banks), 'last_receipt_sha256': receipt_sha}

    def reopen(self):
        initial, banks = self.genesis['initial_classes'], self.genesis['initial_banks']
        state = {'genesis': self.gid, 'revision': 0, 'classes': initial, 'banks': banks,
                 'model_root': state_root(initial, banks), 'last_receipt_sha256': None}
        db = j.connection(self.journal)
        try:
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                receipt = j.parse(row['receipt']); req = receipt['request']; accepted = receipt['proof_acceptance']
                j.need(j.digest(receipt) == row['receipt_sha256'] and j.digest(req) == row['request_sha256'], 'receipt_identity')
                self.parent(state, req)
                j.need(accepted['verified'] and accepted['proofs_verified'] == 32 and accepted['binding'] == req['payloads'], 'retained_update_acceptance')
                for digest in req['payloads'].values(): self.cas(digest)
                state = self.advance(state, req, row['receipt_sha256'])
            j.need(state == self.head(db), 'reopened_committed_bank_chain')
        finally: db.close()

    def teach_vector(self, label, vector, text, request_id):
        vector = base._vector(vector); j.need(isinstance(text, str), 'text_metadata')
        with self.locked():
            out, completed = self._request('teach', request_id, {'kind': 'teach', 'label': label, 'text': text, 'vector': vector})
            if completed is not None: return completed
            head = self.head(); j.need(label in head['classes'], 'declared_class')
            context = out / 'context.json'
            if context.exists(): j.need(j.read(context)['head'] == head, 'stale_incomplete_teach_parent')
            else: j.write_json(context, {'head': head})
            entry = head['classes'][label]; bank, lane = entry['bank'], entry['lane']
            old = entry['queue'][0]['sha256'] if len(entry['queue']) == 8 else self.genesis['zero_sha256']
            vector_path = out / 'vector.json'
            if not vector_path.exists(): j.write_json(vector_path, vector)
            j.need(j.read(vector_path) == vector, 'retained_feature_identity')
            def issue(attempt):
                self.backend.native('issue', attempt, dir=self.root / 'issuer', vector=vector_path, lane=lane, out=attempt / 'fresh.ct')
                return {'path': str(attempt / 'fresh.ct'), 'sha256': backend.sha(attempt / 'fresh.ct')}
            issued = self._phase(out, 'issue', issue)['result']
            j.need(backend.sha(issued['path']) == issued['sha256'], 'issued_ciphertext_identity')
            def learn(attempt):
                case = attempt / 'case'; case.mkdir()
                j.write(case / 'acc.ct', self.cas(head['banks'][bank]['acc_sha256'])); j.write(case / 'old.ct', self.cas(old))
                j.write(case / 'fresh.ct', Path(issued['path']).read_bytes())
                self.backend.native('learn', attempt, acc=case / 'acc.ct', fresh=case / 'fresh.ct', old=case / 'old.ct', out=case / 'out.ct')
                return {'path': str(case), 'binding': {r + '_sha256': backend.sha(case / (r + '.ct')) for r in ('acc', 'fresh', 'old', 'out')}}
            candidate = self._phase(out, 'learn', learn)['result']; case = Path(candidate['path'])
            req = {'schema': 'packed-class-update-v1', 'request_id': request_id, 'genesis': self.gid,
                'recipient_id': self.genesis['recipient_id'], 'backend_sha256': j.digest(self.engine.descriptor),
                'revision': head['revision'] + 1, 'parent_sha256': j.digest(head), 'parent_model_root': head['model_root'],
                'label': label, 'bank': bank, 'lane': lane, 'text_sha256': j.sha(text.encode()),
                'feature_sha256': backend.sha(vector_path), 'payloads': candidate['binding']}
            self.parent(head, req); j.write_json(out / 'request.json', req)
            def prove(attempt):
                value = self.engine.produce_update(case, attempt / 'produced', attempt)
                return {'path': str(attempt / 'produced'), 'value': value}
            produced = self._phase(out, 'prove', prove, lambda a: self._recover_result(a, 'produced', 'proofs_generated', 32))['result']
            j.need(produced['value']['binding'] == req['payloads'] and produced['value']['fresh_proofs'] == 32, 'complete_update_production')
            def verify(attempt):
                value = self.engine.verify_update(req['payloads'], produced['path'], attempt / 'verified', attempt)
                return {'path': str(attempt / 'verified'), 'value': value}
            accepted = self._phase(out, 'verify', verify, lambda a: self._recover_result(a, 'verified', 'verified', 32))['result']['value']
            j.need(accepted['verified'] and accepted['proofs_verified'] == 32 and accepted['binding'] == req['payloads'], 'complete_update_acceptance')
            metrics = self._metrics(out, accepted, 'teach'); self.check(); db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); self.parent(self.head(db), req)
                for role, digest in req['payloads'].items():
                    raw = (case / (role.removesuffix('_sha256') + '.ct')).read_bytes()
                    j.need(j.sha(raw) == digest, 'verified_update_bytes')
                    path = self.journal / 'cas' / digest
                    if path.exists(): j.need(self.cas(digest) == raw, 'immutable_cas_conflict')
                    else: j.write(path, raw)
                receipt = {'schema': 'packed-class-teach-receipt-v1', 'request': req, 'proof_acceptance': accepted,
                           'parent_checked_inside_commit': True, 'accepted_utc': backend.now()}
                digest = j.digest(receipt); new = self.advance(head, req, digest)
                result = {'committed': True, 'head': new, 'receipt_sha256': digest, 'request': req,
                          'private_reads': 0, 'metrics': metrics, **self.metadata()}
                db.execute('INSERT INTO journal VALUES(?,?,?,?,?)', (new['revision'], request_id, j.digest(req), j.canonical(receipt).decode(), digest))
                db.execute('UPDATE head SET state=?,state_sha256=? WHERE singleton=1', (j.canonical(new).decode(), j.digest(new)))
                db.execute('UPDATE requests SET status=?,phase=?,result_json=?,error_json=NULL,updated_utc=? WHERE request_id=?',
                    ('complete', 'committed', j.canonical(result).decode(), backend.now(), request_id))
                db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            j.write_json(out / 'committed.json', result); self._status(out, 'committed', 'complete')
            return result

    def bank_context(self, head):
        active = sorted(c for c, e in head['classes'].items() if e['queue'])
        occupied = sorted({head['classes'][c]['bank'] for c in active}, key=int)
        classes = {c: {'bank': head['classes'][c]['bank'], 'lane': head['classes'][c]['lane'],
                       'count': len(head['classes'][c]['queue'])} for c in active}
        counts = {b: [0] * 8 for b in occupied}
        for c in classes.values(): counts[c['bank']][c['lane']] = c['count']
        return active, occupied, classes, counts

    def prepare_query(self, vector, text, request_id):
        vector = base._vector(vector); j.need(isinstance(text, str), 'text_metadata')
        with self.locked():
            out, completed = self._request('query', request_id, {'kind': 'query', 'text': text, 'vector': vector})
            if completed is not None: return j.read(out / 'request.json')
            if (out / 'prepared.json').exists():
                req = j.read(out / 'request.json'); self.query_binding(self.head(), req); return req
            head = self.head(); active, occupied, classes, counts = self.bank_context(head)
            j.need(active, 'active_classes')
            context = out / 'context.json'
            if context.exists(): j.need(j.read(context)['head'] == head, 'stale_incomplete_query_parent')
            else: j.write_json(context, {'head': head})
            query = out / 'query.json'
            if not query.exists(): j.write_json(query, vector)
            j.need(j.read(query) == vector, 'retained_feature_identity')
            req = {'schema': 'packed-class-query-v1', 'request_id': request_id, 'genesis': self.gid,
                'recipient_id': self.genesis['recipient_id'], 'backend_sha256': j.digest(self.engine.descriptor),
                'revision': head['revision'], 'head_sha256': j.digest(head), 'model_root': head['model_root'],
                'evaluation_key_sha256': self.genesis['evaluation_key_sha256'], 'query_sha256': backend.sha(query),
                'text_sha256': j.sha(text.encode()), 'active_classes': active, 'occupied_banks': occupied,
                'classes': classes, 'banks': {}}
            for bank in occupied:
                acc = head['banks'][bank]['acc_sha256']; self.cas(acc)
                def prove(attempt):
                    value = self.engine.produce_infer(self.journal / 'cas' / acc, query,
                        self.root / 'issuer/evaluation.key', attempt / 'produced', attempt)
                    return {'path': str(attempt / 'produced'), 'value': value}
                produced = self._phase(out, f'bank{int(bank):03}-prove', prove,
                    lambda a: self._recover_result(a, 'produced', 'proofs_generated', 352))['result']
                value = produced['value']; binding = value['binding']
                j.need(value['fresh_proofs'] == 352 and value.get('reused_proofs', 0) == 0, 'complete_fresh_bank_production')
                j.need(binding['model_ciphertext_sha256'] == acc and binding['query_sha256'] == req['query_sha256']
                       and binding['evaluation_key_sha256'] == req['evaluation_key_sha256'], 'bank_production_binding')
                req['banks'][bank] = {'model_ciphertext_sha256': acc, 'dot_ciphertext_sha256': binding['dot_ciphertext_sha256'],
                                      'counts': counts[bank], 'produced': produced['path']}
                j.write_json(out / 'request.json', req)
            self.query_binding(self.head(), req)
            j.write_json(out / 'prepared.json', {'prepared': True, 'private_reads': 0, 'request_sha256': j.digest(req)})
            self._status(out, 'prepared', 'prepared', banks_completed=len(occupied), classes_covered=len(active))
            return req

    def query_binding(self, head, req):
        active, occupied, classes, counts = self.bank_context(head)
        j.need(req['genesis'] == self.gid and req['recipient_id'] == self.genesis['recipient_id'] and
               req['backend_sha256'] == j.digest(self.engine.descriptor), 'query_genesis_backend')
        j.need(req['revision'] == head['revision'] and req['head_sha256'] == j.digest(head) and
               req['model_root'] == head['model_root'], 'query_current_revision')
        j.need(req['active_classes'] == active and req['classes'] == classes and req['occupied_banks'] == occupied
               and set(req['banks']) == set(occupied), 'all_occupied_banks_required')
        j.need(req['evaluation_key_sha256'] == self.genesis['evaluation_key_sha256'], 'query_evaluation_key')
        for bank, entry in req['banks'].items():
            j.need(entry['model_ciphertext_sha256'] == head['banks'][bank]['acc_sha256'] and
                   entry['counts'] == counts[bank], 'query_bank_current_model_counts')

    def accept_query(self, request_id):
        with self.locked():
            out = self.directory('queries', request_id); req = j.read(out / 'request.json')
            j.need(j.read(out / 'prepared.json')['request_sha256'] == j.digest(req), 'complete_query_preparation')
            self.query_binding(self.head(), req); path = out / 'public_acceptance.json'
            if path.exists():
                accepted = j.read(path); j.need(accepted['request_sha256'] == j.digest(req), 'retained_query_acceptance_identity')
                return accepted
            checks, outputs = {}, {}
            for bank, entry in req['banks'].items():
                expected = {k: entry[k] for k in ('model_ciphertext_sha256', 'dot_ciphertext_sha256')}
                expected.update(query_sha256=req['query_sha256'], evaluation_key_sha256=req['evaluation_key_sha256'])
                def verify(attempt):
                    value = self.engine.verify_infer(expected, entry['produced'], attempt / 'verified', attempt)
                    return {'path': str(attempt / 'verified'), 'value': value}
                accepted = self._phase(out, f'bank{int(bank):03}-verify', verify,
                    lambda a: self._recover_result(a, 'verified', 'complete_linear_verified', 352))['result']['value']
                j.need(accepted['complete_linear_verified'] and accepted['proofs_verified'] == 352 and
                       all(accepted['binding'][k] == v for k, v in expected.items()), 'complete_bank_acceptance')
                checks[bank] = accepted; outputs[bank] = str(Path(entry['produced']) / 'case/expected_dot.ct')
            self.check(); db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); head = self.head(db); self.query_binding(head, req)
                acceptance = {'accepted_all_banks': True, 'head': head, 'request': req, 'request_sha256': j.digest(req),
                    'checks': checks, 'outputs': outputs, 'private_reads': 0,
                    'public_phase_complete_utc': backend.now(), 'head_checked_under_write_lock': True}
                j.write_json(path, acceptance); db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            self._status(out, 'publicly-accepted', 'accepted', banks_verified=len(checks))
            return acceptance

    def receive(self, request_id):
        with self.locked():
            out = self.directory('queries', request_id); db = j.connection(self.journal)
            try:
                row = db.execute('SELECT result_json FROM requests WHERE request_id=? AND kind=?', (request_id, 'query')).fetchone()
                if row and row['result_json']: return j.parse(row['result_json'])
            finally: db.close()
            req = j.read(out / 'request.json'); self.query_binding(self.head(), req)
            accepted = j.read(out / 'public_acceptance.json')
            j.need(accepted['accepted_all_banks'] and accepted['head_checked_under_write_lock'] and
                accepted['request_sha256'] == j.digest(req) and accepted['request'] == req and
                set(accepted['checks']) == set(req['occupied_banks']) == set(accepted['outputs']), 'all_bank_proofs_before_private_receive')
            for bank, path in accepted['outputs'].items():
                check = accepted['checks'][bank]
                j.need(backend.sha(path) == req['banks'][bank]['dot_ciphertext_sha256'] and
                       check['complete_linear_verified'] and check['proofs_verified'] == 352, 'accepted_reader_output')
            if not (out / 'receive_started.json').exists():
                j.write_json(out / 'receive_started.json', {'utc': backend.now(), 'public_acceptance_sha256': backend.sha(out / 'public_acceptance.json')})
            banks = {}
            for bank in req['occupied_banks']:
                def read(attempt):
                    value = self.engine.receive(self.root / 'issuer', accepted['outputs'][bank],
                        accepted['checks'][bank]['binding'], req['banks'][bank]['counts'], attempt)
                    return {'value': value}
                banks[bank] = self._phase(out, f'bank{int(bank):03}-read', read)['result']['value']
            classes = {}
            for label, entry in req['classes'].items():
                total = banks[entry['bank']]['class_sums'][entry['lane']]
                classes[label] = {**entry, 'sum_dot': total, 'sum_score': total,
                                  'mean_numerator': total, 'mean_denominator': entry['count']}
            order = sorted(classes, key=lambda c: (-Fraction(classes[c]['sum_dot'], classes[c]['count']), c))
            metrics = self._metrics(out, accepted['checks'], 'query')
            metrics.update(classes_answered=len(classes), occupied_banks=len(banks))
            j.write_json(out / 'metrics.json', metrics)
            result = {'answered': True, 'prediction': order[0], 'winner': order[0], 'ranking': order,
                'classes': classes, 'counts': {c: e['count'] for c, e in classes.items()}, 'banks': banks,
                'class_scores': [{'label': c, **classes[c]} for c in order], 'revision': req['revision'],
                'model_root': req['model_root'], 'public_accepted': True, 'accepted_all_banks': True,
                'public_acceptance_sha256': backend.sha(out / 'public_acceptance.json'), 'private_reads': len(banks),
                'finished_utc': backend.now(), 'full_reader': True, 'metrics': metrics, **self.metadata()}
            db = j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE'); self.query_binding(self.head(db), req)
                db.execute('UPDATE requests SET status=?,phase=?,result_json=?,error_json=NULL,updated_utc=? WHERE request_id=?',
                    ('complete', 'answered', j.canonical(result).decode(), backend.now(), request_id)); db.execute('COMMIT')
            finally:
                if db.in_transaction: db.execute('ROLLBACK')
                db.close()
            j.write_json(out / 'answer.json', result); self._status(out, 'answered', 'complete')
            return result


get_progress = base.get_progress


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    init = sub.add_parser('init'); init.add_argument('root'); init.add_argument('--class', dest='classes', action='append', required=True)
    for name in ('teach', 'query', 'status'):
        command = sub.add_parser(name); command.add_argument('root')
        if name != 'status':
            command.add_argument('--text', required=True); command.add_argument('--request-id', required=True); command.add_argument('--vector-json')
        if name == 'teach': command.add_argument('--label', required=True)
    args = p.parse_args()
    if args.action == 'init': result = initialize(args.root, args.classes)
    else:
        live = Live(args.root)
        if args.action == 'status': result = {'head': live.head(), **live.metadata()}
        elif args.action == 'teach':
            result = live.teach_vector(args.label, j.read(args.vector_json), args.text, args.request_id) if args.vector_json else live.teach(args.label, args.text, args.request_id)
        else:
            result = live.query_vector(j.read(args.vector_json), args.text, args.request_id) if args.vector_json else live.query(args.text, args.request_id)
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
