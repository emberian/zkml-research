"""Pinned shared public prover and dedicated packed-class sum reader."""
from pathlib import Path
import importlib.util
import json
import os

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


base = load('packed_shared_durable_core', HERE.parent / 'core.py')
io = base.backend


class Backend:
    def __init__(self, descriptor=None):
        if descriptor is None:
            issuer = io.Backend()
            proof = base.engines.Engine.new(io, issuer, 'linear', 'matched')
            reader = Path(os.environ.get('CONTINUING_PACKED_READER', HERE / 'reader/native/target/release/vfhe-packed-class-reader')).resolve()
            profile = Path(os.environ.get('CONTINUING_PACKED_READER_PROFILE', HERE / 'reader/PROFILE.json')).resolve()
            sources = [HERE / 'backend.py', HERE / 'core.py', HERE.parent / 'core.py',
                       HERE.parent / 'backend.py', HERE.parent / 'engines.py']
            descriptor = {'schema': 'packed-class-sum-backend-v1', 'issuer': issuer.descriptor,
                'proof_engine': proof.descriptor, 'reader': {'native': str(reader), 'native_sha256': io.sha(reader),
                'profile': str(profile), 'profile_sha256': io.sha(profile)},
                'source_pins': {str(p): io.sha(p) for p in sources}}
        self.descriptor = descriptor
        self.issuer = io.Backend(descriptor['issuer'])
        self.proofs = base.engines.Engine(io, self.issuer, descriptor['proof_engine'])
        self.update_count, self.infer_count = 32, 352
        self.check()

    def check(self):
        d = self.descriptor
        if d['schema'] != 'packed-class-sum-backend-v1' or not self.proofs.matched or not self.proofs.linear:
            raise RuntimeError('unsupported packed learner backend')
        for path, expected in d['source_pins'].items():
            if io.sha(path) != expected: raise RuntimeError('packed learner source changed: ' + path)
        for key in ('native', 'profile'):
            if io.sha(d['reader'][key]) != d['reader'][key + '_sha256']:
                raise RuntimeError('packed class reader changed: ' + key)
        reader = io.read(d['reader']['profile'])
        if (reader['schema'] != 'packed-class-reader-profile-v1'
                or reader['native'] != d['reader']['native']
                or reader['maximum_class_count'] != 8 or reader['maximum_class_sum_bound'] != 160000):
            raise RuntimeError('unsupported packed reader profile')
        for path, expected in reader['pins'].items():
            if io.sha(path) != expected: raise RuntimeError('packed reader dependency changed: ' + path)
        self.proofs.check()

    def produce_update(self, *args): return self.proofs.produce_update(*args)
    def verify_update(self, *args): return self.proofs.verify_update(*args)
    def produce_infer(self, model, query, key, out, directory):
        return self.proofs.produce_infer(model, query, key, None, out, directory)
    def verify_infer(self, *args): return self.proofs.verify_infer(*args)
    def verification_entries(self, accepted): return self.proofs.verification_entries(accepted)
    def generated_proofs(self, phases): return self.proofs.generated_proofs(phases)

    def receive(self, issuer, ciphertext, binding, counts, directory):
        self.check()
        if (len(counts) != 8 or any(type(c) is not int or not 0 <= c <= 8 for c in counts)
                or io.sha(ciphertext) != binding['dot_ciphertext_sha256']):
            raise RuntimeError('packed receive binding/counts')
        io.run(directory, 'read', [self.descriptor['reader']['native'], 'read', issuer, ciphertext,
            binding['dot_ciphertext_sha256'], binding['evaluation_key_sha256'], json.dumps(counts, separators=(',', ':'))], 300)
        value = io.read(Path(directory) / 'read.stdout')
        sums = value['class_sums']
        if (len(sums) != 8 or any(type(v) is not int or abs(v) > 20000*c for v, c in zip(sums, counts))
                or value['counts'] != counts or value['sum_values'] != sums
                or value['signed_sum'] != sum(sums) or value['per_class_signed_bounds'] != [20000*c for c in counts]
                or value['dot_ciphertext_sha256'] != binding['dot_ciphertext_sha256']
                or value['evaluation_key_sha256'] != binding['evaluation_key_sha256']
                or value['all8192_slots_repeat8'] is not True or value['zero_empty_lanes'] is not True
                or value['full_reader_key'] is not True):
            raise RuntimeError('packed reader output contract')
        return value
