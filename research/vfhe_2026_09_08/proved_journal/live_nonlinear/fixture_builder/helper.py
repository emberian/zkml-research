#!/usr/bin/env python3
"""Fresh fixed semantic issuance and public native query capture. No implicit reads."""
import argparse
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = next(p for p in HERE.parents if (p / 'AGENTS.md').is_file())
OLD = REPO / 'research/learn_infer_only/experiments/end_to_end/useful_learner_2026_09_08'
NONLINEAR = OLD.parent / 'nonlinear_successor_2026_09_08'
NATIVE = NONLINEAR / 'crypto/target/release/kernel-crypto'
BASE = [1125899906826241,1125899906629633,1125899905744897,1125899905351681]
EXTENDED = BASE + [4611686018427322369,4611686018427289601,4611686018426454017,4611686018426257409,4611686018425815041]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def write_new(path, value):
    with Path(path).open('x') as f:
        f.write(json.dumps(value, indent=2) + '\n')


def check_pins(model=False):
    pins = json.loads((HERE / 'SOURCE_PINS.json').read_text())
    entries = pins['sources'] + (pins['model'] if model else [])
    for row in entries:
        if sha(row['path']) != row['sha256']:
            raise RuntimeError('frozen input changed: ' + row['path'])


def native_argv(operation, **kwargs):
    """Build a pinned command; caller owns phase order, launch and evidence.

    read is intentionally explicit and must be called by the shared driver only
    after complete accepted model/query proofs. This is a full reader interface.
    """
    check_pins()
    required = {
        'keygen': {'dir'}, 'issue': {'dir','vector','lane','out'},
        'learn': {'acc','fresh','out'}, 'read': {'dir','ct'},
        'infer': {'dir','acc','query','out','trace'},
    }
    if operation not in required:
        raise ValueError('unsupported native operation')
    allowed = required[operation] | ({'old'} if operation == 'learn' else set())
    if not required[operation] <= kwargs.keys() or not kwargs.keys() <= allowed:
        raise ValueError('wrong native argument set')
    result = [str(NATIVE), operation]
    for name, value in kwargs.items():
        result += ['--' + name, str(value)]
    return result


class TextEncoder:
    """Persistent exact frozen E5 issuer for later user-supplied teaching/query texts.

    Cache is caller-owned and may persist across restarts. This class performs no
    encryption, state update, proof, prediction selection or reader operation.
    """
    def __init__(self, cache):
        check_pins(model=True)
        spec = importlib.util.spec_from_file_location('live_frozen_e5_issuer', OLD / 'encoder.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self._encoder = module.Encoder(cache=Path(cache))

    @property
    def stats(self):
        return dict(self._encoder.stats)

    def encode(self, texts):
        check_pins(model=True)
        import numpy as np
        if isinstance(texts, (str,bytes)):
            raise ValueError('texts must be a sequence of strings, not one string')
        texts = list(texts)
        if not texts or any(not isinstance(text,str) or not text.strip() for text in texts):
            raise ValueError('one or more nonempty text strings required')
        with contextlib.redirect_stdout(sys.stderr):
            raw = self._encoder.encode(texts)
        vectors = np.rint(np.asarray(raw, dtype=np.float64)[:, :576] / 4).astype(np.int64)
        if (vectors.shape != (len(texts),576) or np.max(abs(vectors)) > 32 or
                np.any(np.sum(vectors*vectors,axis=1) > 20000)):
            raise RuntimeError('fixed feature domain failed; no retuning or retry')
        check_pins(model=True)
        return vectors.tolist()


def encode(out):
    """Initial fixed demonstration: fresh cache, exactly one batch of three texts."""
    check_pins(model=True)
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    fixture = json.loads((HERE / 'fixture.json').read_text())
    entries = fixture['teaching'] + [fixture['query']]
    encoder = TextEncoder(cache=out / 'encoder_cache')
    vectors = encoder.encode([entry['text'] for entry in entries])
    stats = encoder.stats
    if stats['forward_batches'] != 1 or stats['encoded_texts'] != 3 or stats['cached_texts'] != 0:
        raise RuntimeError('expected exactly one fresh batch of three texts')
    rows = []
    for entry, vector in zip(entries, vectors):
        path = out / (entry['id'] + '.json')
        write_new(path, vector)
        rows.append({'id':entry['id'], 'vector_path':str(path), 'sha256':sha(path),
                     'coordinate_max_abs':max(abs(x) for x in vector),
                     'norm_squared':sum(x*x for x in vector)})
    record = {'fixture_sha256':sha(HERE/'fixture.json'), 'encoder_stats':stats,
              'features':rows, 'plaintext_trusted_issuer':True,
              'public_fixture_features':True, 'new_model_batch_count':1,
              'full_reader_key_remains':True}
    write_new(out / 'issuance.json', record)
    check_pins(model=True)
    return record


def capture(issuer, model_ct, query, out, revision, label):
    """Public model→packed dot→square; exact old consumer filenames, fresh bytes.

    The shared driver selects an accepted model ciphertext/revision before this
    call. This producer does not accept revisions or decrypt ciphertexts.
    """
    check_pins()
    issuer, model_ct, query, out = [Path(p).resolve() for p in (issuer, model_ct, query, out)]
    out.mkdir(parents=True, exist_ok=False)
    parameters = json.loads((issuer / 'parameters.json').read_text())
    if parameters['N'] != 8192 or parameters['t'] != 4294475777 or parameters['q'] != BASE:
        raise RuntimeError('issuer does not use the frozen nonlinear profile')
    argv = native_argv('infer', dir=issuer, acc=model_ct, query=query,
                       out=out/'basic-000.ct', trace=out/'basic')
    # Reuse the enclosing driver's process-group/timeout/evidence implementation.
    spec = importlib.util.spec_from_file_location('live_nonlinear_commands', HERE.parent/'common.py')
    common = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(common)
    command = common.command(out, 'native_infer', argv, 120, dict(os.environ))
    native = json.loads((out/'native_infer.stdout').read_text())
    trace = json.loads((out/'basic.json').read_text())
    if (trace['N'],trace['t'],trace['components'],trace['base'],trace['extended_base']) != (8192,4294475777,3,BASE,EXTENDED):
        raise RuntimeError('native capture parameter mismatch')
    if not trace['native_multiplicator_bytes_equal']:
        raise RuntimeError('actual native multiplication comparison failed')
    if sha(out/'basic.dot.ct') != trace['input_dot_sha256'] or sha(out/'basic-000.ct') != trace['output_sha256'] or native['sha256'] != trace['output_sha256']:
        raise RuntimeError('native capture output binding failed')
    files = {}
    for name, filename in [('trace','basic.json'),('dot_ciphertext','basic.dot.ct'),('output_ciphertext','basic-000.ct')]:
        path = out / filename
        files[name] = {'path':str(path), 'bytes':path.stat().st_size, 'sha256':sha(path)}
    descriptor = {'instance':'fresh live nonlinear query capture', 'files':files,
                  'N':8192,'t':4294475777,'base':BASE,'extended_base':EXTENDED,'components':3,
                  'native_multiplicator_bytes_equal':True,
                  'source_sha256':sha(NONLINEAR/'crypto/src/main.rs'),
                  'binary_sha256':sha(NATIVE), 'cargo_lock_sha256':sha(NONLINEAR/'crypto/Cargo.lock'),
                  'captured':'Actual native pre-/post-directed-scaler PowerBasis arrays; public dot ciphertext and actual square output.',
                  'model_binding':{'caller_revision':revision,'label':label,'model_ciphertext_path':str(model_ct),
                                   'model_ciphertext_sha256':sha(model_ct),'query_path':str(query),'query_sha256':sha(query),
                                   'evaluation_key_path':str(issuer/'evaluation.key'),'evaluation_key_sha256':sha(issuer/'evaluation.key')},
                  'scope':'Public producer capture; accepted revision selection and proof checks belong to the shared journal driver. Full reader remains; no private read occurs here.'}
    write_new(out/'descriptor.json', descriptor)
    record = {'descriptor_path':str(out/'descriptor.json'),'descriptor_sha256':sha(out/'descriptor.json'),
              'native_command':command,'native_result':native,'private_reads':0}
    write_new(out/'capture.json', record)
    check_pins()
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    e = sub.add_parser('encode');e.add_argument('--out', required=True)
    c = sub.add_parser('capture')
    for name in ['issuer','model-ct','query','out','label']:
        c.add_argument('--'+name, required=True)
    c.add_argument('--revision',type=int,required=True)
    a = p.parse_args()
    if a.command == 'encode':result = encode(a.out)
    else:result = capture(a.issuer,a.model_ct,a.query,a.out,a.revision,a.label)
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
