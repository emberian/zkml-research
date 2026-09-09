#!/usr/bin/env python3
"""Standalone caller-selected linear backend; run in a separate Python process.

produce-linear MODEL QUERY EVALUATION_KEY NEW_OUTPUT
reuse-linear MODEL QUERY EVALUATION_KEY QUADRATIC_PRODUCED NEW_OUTPUT
verify-linear EXPECTED_JSON PRODUCED NEW_OUTPUT
receive-linear ISSUER EXPECTED_JSON PRODUCED NEW_OUTPUT
config

Optional leading --profile PATH/PIPELINE.json. Every operation creates a new
directory and writes result.json. EXPECTED_JSON must pin model_ciphertext_sha256,
query_sha256 and evaluation_key_sha256; dot_ciphertext_sha256 is optional.
receive-linear freshly verifies all 88 proofs before invoking the full reader.
"""
from pathlib import Path
import json
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent.parent / 'nonlinear_performance/runtime'
sys.path.insert(0, str(PRIOR))
import pipeline
from common import check_pins, command, now, save, sha

FIELDS = {'linear_plan_sha256', 'model_ciphertext_sha256', 'query_sha256',
          'evaluation_key_sha256', 'dot_ciphertext_sha256'}
INPUTS = {'model_ciphertext_sha256', 'query_sha256', 'evaluation_key_sha256'}
LEGACY_EXTRA = {'kernel_ciphertext_sha256'}
SCHEMA = 'caller-selected-linear-bundle-v1'


def read(path):
    return json.loads(Path(path).read_text())


def projected(binding):
    assert FIELDS <= set(binding) <= FIELDS | LEGACY_EXTRA
    return {k: binding[k] for k in sorted(FIELDS)}


def record_binding(kind, case, record):
    assert kind == 'infer'
    assert set(record['binding']) == FIELDS
    assert record['binding'] == projected(read(case / 'operation.json')['binding'])


def check_record(config, kind, index, case, record, proof):
    assert kind == 'infer'
    if 'backend' in record:
        assert record['backend'] == config['backend_id']
    assert record['verified'] is True and record['rows'] == 4096
    assert record['index'] == index
    assert record['first_row'] == index * 4096
    assert record['end_row_exclusive'] == (index + 1) * 4096
    assert record['proof_sha256'] == sha(proof)
    assert record['template_sha256'] == pipeline.profile(config, kind, index)['template_sha256']
    assert record['stage'] == index // 8 and record['prime_index'] == (index % 8) // 2
    record_binding(kind, case, record)


def configure(profile_path):
    profile_path = Path(profile_path).resolve()
    assert profile_path.name == 'PIPELINE.json'

    def config():
        if not __debug__:
            raise RuntimeError('Assertions must remain enabled')
        c = read(profile_path)
        assert c['schema'] == 'caller-selected-linear-profile-v1'
        check_pins(c['pins'])
        assert sha(c['linear_plan']) == c['linear_plan_sha256']
        assert len(c['profiles']['mac']) == 4 and set(c['native']) == {'infer'}
        return c

    pipeline.ROOT = profile_path.parent
    pipeline.config = config
    pipeline.record_binding = record_binding
    pipeline.check_record = check_record
    return config


def input_binding(model, query, key):
    return dict(zip(('model_ciphertext_sha256', 'query_sha256', 'evaluation_key_sha256'),
                    (sha(p) for p in (model, query, key))))


def approve(expected, binding, config):
    assert INPUTS <= set(expected) <= INPUTS | {'dot_ciphertext_sha256'}
    assert all(binding[k] == v for k, v in expected.items())
    assert binding['linear_plan_sha256'] == config['linear_plan_sha256']


def required_pins(case, proofs):
    # Native verification reconstructs every public row from these objects; it
    # does not trust the producer's exported rows or self-verification reports.
    files = [case / name for name in ('operation.json', 'model.ct', 'query.json',
                                     'evaluation.key', 'expected_dot.ct')]
    files += [case / f'steps/{i:02}.ct' for i in range(11)]
    files += [proofs / f'chunk{i:03}/proof.bin' for i in range(88)]
    return {str(p): sha(p) for p in files}


def bundle(case, proofs, binding, fresh, reused):
    return {'schema': SCHEMA, 'statement_kind': 'packed-linear-dot',
            'case': str(case), 'proofs': str(proofs), 'binding': binding,
            'dot_ciphertext': str(case / 'expected_dot.ct'),
            'proofs_generated': fresh == 88, 'fresh_proofs': fresh,
            'reused_proofs': reused, 'fresh_consumer_verified': False,
            'private_files_read': 0, 'finished_utc': now()}


def produce_linear(model, query, key, out):
    c = pipeline.config()
    model, query, key, out = (Path(p).resolve() for p in (model, query, key, out))
    expected = input_binding(model, query, key)
    out.mkdir()
    started = time.monotonic()
    command(out, 'import', [c['native']['infer'], 'import', c['linear_plan'],
                           model, query, key, out / 'case'], 120, pipeline.ENV)
    binding = projected(read(out / 'case/operation.json')['binding'])
    approve(expected, binding, c)
    pipeline.generate('infer', out / 'case', out / 'proofs')
    assert input_binding(model, query, key) == expected
    pipeline.config()
    result = bundle(out / 'case', out / 'proofs', binding, 88, 0)
    result.update(elapsed_seconds=time.monotonic() - started,
                  profile_sha256=sha(pipeline.ROOT / 'PIPELINE.json'))
    save(out / 'result.json', result)
    return result


def reuse_linear(model, query, key, quadratic_produced, out):
    """Reference an explicit complete-kernel producer's MAC prefix, without proving."""
    c = pipeline.config()
    source, out = Path(quadratic_produced).resolve(), Path(out).resolve()
    case, proofs = source / 'infer_case', source / 'infer'
    binding = projected(read(case / 'operation.json')['binding'])
    expected = input_binding(model, query, key)
    approve(expected, binding, c)
    # This is provenance, never acceptance. verify-linear must still consume88.
    pins = required_pins(case, proofs)
    out.mkdir()
    result = bundle(case, proofs, binding, 0, 88)
    result.update(reused_from=str(source), referenced_pins=pins,
                  profile_sha256=sha(pipeline.ROOT / 'PIPELINE.json'))
    save(out / 'result.json', result)
    return result


def verify_linear(expected, produced, out):
    c = pipeline.config()
    produced, out = Path(produced).resolve(), Path(out).resolve()
    supplied = read(produced / 'result.json')
    assert supplied['schema'] == SCHEMA and supplied['statement_kind'] == 'packed-linear-dot'
    case, proofs = Path(supplied['case']).resolve(), Path(supplied['proofs']).resolve()
    binding = projected(read(case / 'operation.json')['binding'])
    assert supplied['binding'] == binding
    approve(expected, binding, c)
    assert sha(case / 'expected_dot.ct') == binding['dot_ciphertext_sha256']
    frozen = required_pins(case, proofs)
    if 'referenced_pins' in supplied:
        assert supplied['referenced_pins'] == frozen
    out.mkdir()
    started = time.monotonic()
    save(out / 'started.json', {'expected': expected, 'binding': binding,
                              'profile_sha256': sha(pipeline.ROOT / 'PIPELINE.json'),
                              'input_pins': frozen, 'started_utc': now()})
    checks = pipeline.verify_phase(c, 'infer', case, proofs, out)
    assert len(checks) == 88
    check_pins(frozen)
    pipeline.config()
    result = {'complete_linear_verified': True, 'verified': True,
              'statement': 'Caller-approved model, query and evaluation key yield the bound dot ciphertext through all 11 stages of the fixed packed linear plan, under the parser/NTT/controller/backend TCB.',
              'statement_kind': 'packed-linear-dot', 'binding': binding,
              'dot_ciphertext': str(case / 'expected_dot.ct'),
              'proofs_verified': 88, 'proofs_generated_this_call': 0,
              'verifications': checks, 'proof_bytes': sum(x['proof_bytes'] for x in checks),
              'private_files_read': 0, 'elapsed_seconds': time.monotonic() - started,
              'profile_sha256': sha(pipeline.ROOT / 'PIPELINE.json'), 'finished_utc': now()}
    save(out / 'result.json', result)
    save(out / 'progress.json', {'phase': 'complete', 'completed': 88, 'utc': now()})
    return result


def receive_linear(issuer, expected, produced, out):
    """Controller-ordered verify then full-key read; receipt JSON is not a key gate."""
    out = Path(out).resolve()
    out.mkdir()
    verified = verify_linear(expected, produced, out / 'verify')
    c = pipeline.config()
    binding = verified['binding']
    command(out, 'read', [c['native']['infer'], 'read', Path(issuer).resolve(),
                         verified['dot_ciphertext'], binding['dot_ciphertext_sha256'],
                         binding['evaluation_key_sha256']], 120, pipeline.ENV)
    decoded = read(out / 'read.stdout')
    assert decoded['dot_ciphertext_sha256'] == binding['dot_ciphertext_sha256']
    assert decoded['evaluation_key_sha256'] == binding['evaluation_key_sha256']
    assert len(decoded['dot_values']) == 8 and decoded['all8192_slots_repeat8'] is True
    pipeline.config()
    result = {'complete_linear_verified': True, 'binding': binding,
              'proofs_verified': 88, 'dot_values': decoded['dot_values'],
              'sum_dot': decoded['sum_dot'], 'signed_bound': decoded['signed_bound'],
              'full_reader_key': True, 'private_files_read': 1,
              'verification_result': str(out / 'verify/result.json'),
              'verification_sha256': sha(out / 'verify/result.json'),
              'read_result': str(out / 'read.stdout'), 'finished_utc': now(),
              'scope': 'Software controller verifies before full-reader decryption. Reader custody and correct bounded-model initialization remain external.'}
    save(out / 'result.json', result)
    return result


def main():
    args = sys.argv[1:]
    if not args or args in (['--help'], ['-h']):
        print(__doc__)
        return
    profile = HERE / 'PIPELINE.json'
    if args[0] == '--profile':
        if len(args) < 3:
            raise SystemExit(__doc__)
        profile, args = Path(args[1]), args[2:]
    config = configure(profile)
    action, *args = args
    if action == 'config' and not args:
        print(json.dumps(config(), indent=2))
        return
    if action == 'produce-linear' and len(args) == 4:
        result = produce_linear(*args)
    elif action == 'reuse-linear' and len(args) == 5:
        result = reuse_linear(*args)
    elif action == 'verify-linear' and len(args) == 3:
        result = verify_linear(read(args[0]), *args[1:])
    elif action == 'receive-linear' and len(args) == 4:
        result = receive_linear(args[0], read(args[1]), *args[2:])
    else:
        raise SystemExit(__doc__)
    print(json.dumps({'action': action, 'result': str(Path(args[-1]).resolve() / 'result.json'),
                      **{k: result[k] for k in ('complete_linear_verified', 'fresh_proofs',
                         'reused_proofs', 'proofs_verified', 'dot_values', 'sum_dot') if k in result}}))


if __name__ == '__main__':
    main()
