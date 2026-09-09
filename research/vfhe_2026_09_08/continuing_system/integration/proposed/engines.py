"""Genesis-bound proof and score engines for the durable continuing learner.

The BFV issuer, FIFO update and encoder remain shared. Each proof caller runs in
its own process. A linear reader is invoked only by core's accepted receive phase;
it keeps the same explicit full-reader custody boundary as the squared engine.
"""
from pathlib import Path
import os
import sys

HERE = Path(__file__).resolve().parent
SCHEMA = 'continuing-score-engine-v1'


def metadata(descriptor=None):
    score = descriptor['score_kind'] if descriptor else 'squared'
    proof = descriptor['proof_backend'] if descriptor else 'compact'
    if (score, proof) not in (('squared', 'compact'), ('linear', 'compact'), ('linear', 'matched')):
        raise ValueError('supported engines: squared/compact, linear/compact, linear/matched')
    return {'score_kind': score, 'proof_backend': proof,
            'score_formula': 'mean(dot^2)' if score == 'squared' else 'mean(dot)',
            'score_signed': score == 'linear',
            'update_proofs_per_class': 32 if proof == 'matched' else 8,
            'infer_proofs_per_class': 116 if score == 'squared' else (352 if proof == 'matched' else 88),
            'lane_values_key': 'kernel_values' if score == 'squared' else 'dot_values',
            'sum_key': 'sum_kernel' if score == 'squared' else 'sum_dot'}


def policy(legacy, descriptor=None):
    if descriptor is None:
        return legacy
    return {**legacy, 'schema': 'continuing-proof-learner-policy-v2',
            'query': 'All active classes require complete fresh proofs of the genesis-bound score before private receive',
            'score_engine': metadata(descriptor)}


class Engine:
    def __init__(self, io, issuer, descriptor=None):
        self.issuer = issuer
        self.io = io
        self.sha, self.read_json, self.save, self.run = io.sha, io.read, io.save, io.run
        self.descriptor = descriptor
        self.info = metadata(descriptor)
        self.update_count = self.info['update_proofs_per_class']
        self.infer_count = self.info['infer_proofs_per_class']
        self.linear = self.info['score_kind'] == 'linear'
        self.matched = self.info['proof_backend'] == 'matched'
        self.needs_capture = not self.linear
        self.output_key = 'dot_ciphertext_sha256' if self.linear else 'kernel_ciphertext_sha256'
        self.infer_flag = 'complete_linear_verified' if self.linear else 'complete_infer_verified'
        self.check()

    @classmethod
    def new(cls, io, issuer, score='squared', proof_backend='compact'):
        selected = metadata({'score_kind': score, 'proof_backend': proof_backend})
        if score == 'squared':
            return cls(io, issuer)  # Preserve the original genesis, policy and backend descriptor.
        sha, read = io.sha, io.read
        where = HERE / 'linear' if proof_backend == 'compact' else HERE.parent / 'matched_field'
        prefix = 'CONTINUING_SYSTEM_LINEAR' if proof_backend == 'compact' else 'CONTINUING_SYSTEM_MATCHED'
        worker = Path(os.environ.get(prefix + '_WORKER', where / 'caller.py')).resolve()
        profile = Path(os.environ.get(prefix + '_PROFILE', where / 'PIPELINE.json')).resolve()
        reader_profile = Path(os.environ.get('CONTINUING_SYSTEM_LINEAR_PROFILE', HERE / 'linear/PIPELINE.json')).resolve()
        reader = Path(read(reader_profile)['native']['infer']).resolve()
        descriptor = {'schema': SCHEMA, 'id': score + '-' + proof_backend, **selected,
            'query_runner': {'worker': str(worker), 'worker_sha256': sha(worker),
                             'profile': str(profile), 'profile_sha256': sha(profile)},
            'reader': {'native': str(reader), 'native_sha256': sha(reader),
                       'profile': str(reader_profile), 'profile_sha256': sha(reader_profile)}}
        return cls(io, issuer, descriptor)

    def _profile(self, runner, schema):
        for key in ('worker', 'profile'):
            if self.sha(runner[key]) != runner[key + '_sha256']:
                raise RuntimeError('genesis-bound engine changed: ' + key)
        config = self.read_json(runner['profile'])
        if config['schema'] != schema:
            raise RuntimeError('wrong score engine profile schema')
        if schema == 'matched-field-linear-profile-v1':
            for key in ('native', 'linear_plan'):
                if self.sha(config[key]) != config[key + '_sha256']:
                    raise RuntimeError('matched-field dependency changed: ' + key)
            if config['caller_sha256'] != runner['worker_sha256']:
                raise RuntimeError('matched-field caller changed')
        else:
            for path, expected in config['pins'].items():
                if self.sha(path) != expected:
                    raise RuntimeError('score engine dependency changed: ' + path)
        return config

    def check(self):
        self.issuer.check()
        d = self.descriptor
        if d is None:
            return
        if (d['schema'] != SCHEMA or d['id'] != self.info['score_kind'] + '-' + self.info['proof_backend']
                or any(d[k] != value for k, value in self.info.items()) or not self.linear):
            raise RuntimeError('unsupported or changed genesis score engine')
        config = self._profile(d['query_runner'], 'matched-field-linear-profile-v1' if self.matched else 'caller-selected-linear-profile-v1')
        reader = d['reader']
        for key in ('native', 'profile'):
            if self.sha(reader[key]) != reader[key + '_sha256']:
                raise RuntimeError('genesis-bound linear reader changed: ' + key)
        reader_config = self.read_json(reader['profile'])
        if (reader_config['schema'] != 'caller-selected-linear-profile-v1'
                or reader_config['native']['infer'] != reader['native']
                or reader_config['linear_plan_sha256'] != config['linear_plan_sha256']):
            raise RuntimeError('linear reader and proof engine disagree on profile')

    def call(self, action, arguments, out, directory):
        self.check()
        runner = self.descriptor['query_runner']
        self.run(directory, action, [sys.executable, runner['worker'], '--profile', runner['profile'], action, *arguments, out])
        return self.read_json(Path(out) / 'result.json')

    def produce_update(self, source, out, directory):
        if not self.matched:
            return self.issuer.produce_update(source, out, directory)
        return self.call('produce-update', [Path(source) / (k + '.ct') for k in ('acc', 'fresh', 'old')], out, directory)

    def verify_update(self, expected, produced, out, directory):
        if not self.matched:
            return self.issuer.verify_update(expected, produced, out, directory)
        path = Path(directory) / 'expected.json'; self.save(path, expected)
        return self.call('verify-update', [path, produced], out, directory)

    def capture(self, *args):
        return self.issuer.capture(*args)

    def produce_infer(self, model, query, key, capture, out, directory):
        if not self.linear:
            return self.issuer.produce_infer(model, query, key, capture, out, directory)
        return self.call('produce-linear', [model, query, key], out, directory)

    def verify_infer(self, expected, produced, out, directory):
        if not self.linear:
            return self.issuer.verify_infer(expected, produced, out, directory)
        path = Path(directory) / 'expected.json'; self.save(path, expected)
        return self.call('verify-linear', [path, produced], out, directory)

    def output_path(self, produced):
        return Path(produced) / ('case/expected_dot.ct' if self.linear else 'infer_case/expected_kernel.ct')

    def receive(self, issuer, ciphertext, binding, directory):
        self.check()
        if self.sha(ciphertext) != binding[self.output_key]:
            raise RuntimeError('reader ciphertext differs from accepted output')
        if not self.linear:
            return self.issuer.native('read', directory, dir=issuer, ct=ciphertext)
        self.run(directory, 'read', [self.descriptor['reader']['native'], 'read', issuer, ciphertext,
                                    binding[self.output_key], binding['evaluation_key_sha256']], 300)
        value = self.read_json(Path(directory) / 'read.stdout')
        lanes = value['dot_values']
        if (value['dot_ciphertext_sha256'] != binding[self.output_key]
                or value['evaluation_key_sha256'] != binding['evaluation_key_sha256']
                or len(lanes) != 8 or any(type(x) is not int or abs(x) > 20000 for x in lanes)
                or value['sum_dot'] != sum(lanes) or value['signed_bound'] != 20000
                or value['all8192_slots_repeat8'] is not True or value['full_reader_key'] is not True):
            raise RuntimeError('linear reader output contract')
        return value

    def score(self, answer):
        return answer[self.info['sum_key']]

    def verification_entries(self, accepted):
        if not self.matched:
            return accepted['verifications']
        return [{**record, 'proof_bytes': record['timing']['proof_bytes']} for record in accepted['chunk_records']]

    def generated_proofs(self, phases):
        generated = set()
        for proof in Path(phases).rglob('proof.bin'):
            report = proof.with_name('proof.json')
            if report.exists() and self.read_json(report).get('verified') is True:
                generated.add(proof)
        if self.matched:
            for path in Path(phases).rglob('proofs/result.json'):
                report = self.read_json(path)
                if report.get('self_verification_only') is not True:
                    continue
                for record in report.get('chunk_records', []):
                    proof = path.parent / record['file']
                    if proof.is_file() and self.sha(proof) == record['proof_sha256']:
                        generated.add(proof)
        return len(generated)

    def decorate_result(self, result):
        if not self.linear:
            return result  # Legacy result objects remain byte-for-byte compatible.
        result.update(self.info)
        for answer in result.get('classes', {}).values():
            answer.update(score_values=answer['dot_values'], sum_score=answer['sum_dot'])
        return result
