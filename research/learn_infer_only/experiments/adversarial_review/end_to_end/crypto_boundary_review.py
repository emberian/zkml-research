#!/usr/bin/env python3
"""Small independent actual-BFV boundary tests; not the durable release gate.

All keys and ciphertexts are generated for this review in ignored runtime/.
Vectors are deliberately public test data. A saved raw reader helper is used
only as a trusted arithmetic oracle, never as evidence of restricted release.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
WIDTH = 577


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def varint(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def readvar(data, at):
    n, shift = 0, 0
    while True:
        if at >= len(data) or shift >= 70:
            raise ValueError('invalid protobuf varint in review parser')
        b = data[at]
        at += 1
        n |= (b & 127) << shift
        if not b & 128:
            return n, at
        shift += 7


def fields(data):
    out, at = [], 0
    while at < len(data):
        tag, at = readvar(data, at)
        number, wire = tag >> 3, tag & 7
        if wire == 0:
            value, at = readvar(data, at)
        elif wire == 2:
            n, at = readvar(data, at)
            value = data[at:at+n]
            if len(value) != n:
                raise ValueError('truncated protobuf')
            at += n
        else:
            raise ValueError('unexpected wire type in the reviewed codec')
        out.append((number, wire, value))
    return out


def pack(rows):
    out = bytearray()
    for number, wire, value in rows:
        out.extend(varint(number*8+wire))
        if wire == 0:
            out.extend(varint(value))
        else:
            out.extend(varint(len(value)))
            out.extend(value)
    return bytes(out)


def payload_blob(original, payload):
    return original[:73] + len(payload).to_bytes(8, 'little') + payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', required=True, type=Path)
    parser.add_argument('--source', required=True, type=Path)
    args = parser.parse_args()
    run_number = 1 + len(list((HERE/'runtime').glob('run_*'))) if (HERE/'runtime').exists() else 1
    run_dir = HERE/'runtime'/f'run_{run_number:03}'
    run_dir.mkdir(parents=True)
    binary = run_dir/'resident-crypto'
    shutil.copy2(args.binary, binary)
    source = args.source.read_bytes()
    (run_dir/'main.rs').write_bytes(source)
    records, checks = [], {}

    def invoke(name, command, expected=0):
        argv = [str(binary.resolve()), command[0]]
        for k, v in command[1:]:
            argv.extend([k, str(v)])
        start = time.monotonic()
        p = subprocess.run(argv, capture_output=True, text=True, timeout=30)
        record = {'name': name, 'argv': argv, 'exit': p.returncode,
                  'elapsed_seconds': time.monotonic()-start,
                  'stdout': p.stdout, 'stderr': p.stderr}
        records.append(record)
        if expected is not None:
            assert p.returncode == expected, (name, p.returncode, p.stdout, p.stderr)
        if not p.returncode:
            return json.loads(p.stdout)
        return record

    def file(name, value):
        path = run_dir/name
        path.write_bytes(value if isinstance(value, bytes) else canonical(value))
        return path

    params = invoke('source_identity', ['params'])
    assert params['source_sha256'] == sha(source), 'saved binary does not match supplied source'
    checks['binary_source_identity'] = True
    for label in ('a', 'b'):
        invoke('keygen_'+label, ['keygen', ('--pk', run_dir/f'{label}.pk'),
               ('--sk', run_dir/f'{label}.sk'), ('--zero', run_dir/f'{label}.zero')])
    va = [(i % 7)-3 for i in range(WIDTH)]
    vb = [((i*3) % 5)-2 for i in range(WIDTH)]
    q = [((i*5) % 7)-3 for i in range(WIDTH)]
    ap, bp, qp = file('public_a.json', va), file('public_b.json', vb), file('public_q.json', q)
    for name, key, vec in [('a1', 'a', ap), ('a2', 'a', ap), ('a3', 'a', bp), ('b1', 'b', ap)]:
        invoke('encrypt_'+name, ['issuer-encrypt', ('--pk', run_dir/f'{key}.pk'),
               ('--vector', vec), ('--out', run_dir/f'{name}.ct')])
    assert (run_dir/'a1.ct').read_bytes() != (run_dir/'a2.ct').read_bytes()
    checks['OS_random_repeated_encryption_bytes_differ'] = True
    invoke('first_add', ['host-learn', ('--acc', run_dir/'a.zero'),
           ('--fresh', run_dir/'a1.ct'), ('--out', run_dir/'state1.ct')])
    assert (run_dir/'state1.ct').read_bytes() == (run_dir/'a1.ct').read_bytes()
    invoke('second_add', ['host-learn', ('--acc', run_dir/'state1.ct'),
           ('--fresh', run_dir/'a3.ct'), ('--out', run_dir/'state2.ct')])
    invoke('exact_old_algebra', ['host-learn', ('--acc', run_dir/'state1.ct'),
           ('--fresh', run_dir/'a3.ct'), ('--old', run_dir/'a1.ct'),
           ('--out', run_dir/'expired.ct')])
    assert (run_dir/'expired.ct').read_bytes() == (run_dir/'a3.ct').read_bytes()
    checks['exact_original_expiry_algebra'] = True
    invoke('encode_query', ['encode-query', ('--vector', qp), ('--out', run_dir/'query.json')])
    infer = invoke('actual_infer', ['host-infer', ('--acc', run_dir/'state2.ct'),
                   ('--query', run_dir/'query.json'), ('--out', run_dir/'answer.ct')])
    read = invoke('trusted_oracle_score', ['reader-decrypt', ('--sk', run_dir/'a.sk'),
                  ('--ct', run_dir/'answer.ct')])
    expected_score = sum((x+y)*z for x, y, z in zip(va, vb, q))
    assert read['signed_score'] == expected_score
    assert read['ciphertext_sha256'] == infer['sha256']
    checks['actual_signed_score'] = expected_score

    honest = (run_dir/'a1.ct').read_bytes()
    ct_fields = fields(honest[81:])
    assert pack(ct_fields) == honest[81:]
    mutations = {
        'wrong_magic': b'BADMAGIC'+honest[8:],
        'wrong_kind': honest[:8]+bytes([2])+honest[9:],
        'wrong_params': honest[:9]+bytes([honest[9]^1])+honest[10:],
        'trailing_byte': honest+b'x',
        'truncated': honest[:-1],
        'over_cap': honest+b'x'*200_001,
        'extra_component': payload_blob(honest, pack(ct_fields+[ct_fields[0]])),
        'wrong_level': payload_blob(honest, pack([row for row in ct_fields if row[0] != 3]+[(3, 0, 1)])),
        'unknown_proto_field': payload_blob(honest, honest[81:]+varint(99*8)+varint(1)),
    }
    for representation in (1, 3):
        altered = []
        for n, w, poly in ct_fields:
            if n == 1:
                poly = pack([(rn, rw, representation if rn == 1 else rv)
                             for rn, rw, rv in fields(poly)])
            altered.append((n, w, poly))
        mutations[f'representation_{representation}'] = payload_blob(honest, pack(altered))
    for name, content in mutations.items():
        path = file(name+'.ct', content)
        invoke(name, ['inspect', ('--ct', path)], expected=2)
    checks['strict_ciphertext_mutations_refused'] = list(mutations)

    # An honest ciphertext under another key is rejected by declared labels.
    invoke('different_key_label', ['host-learn', ('--acc', run_dir/'a.zero'),
           ('--fresh', run_dir/'b1.ct'), ('--out', run_dir/'bad-key.ct')], expected=2)
    # Relabeling valid foreign-key payload remains syntactically canonical. This
    # explicitly demonstrates the documented absence of cryptographic key-ID proof.
    foreign = (run_dir/'b1.ct').read_bytes()
    relabelled = file('foreign_relabelled.ct', foreign[:41]+honest[41:73]+foreign[73:])
    declared = invoke('metadata_is_not_key_proof', ['inspect', ('--ct', relabelled)])
    assert declared['key_id'] == honest[41:73].hex()
    checks['relabelled_foreign_payload_passes_syntax_only'] = True

    for name, value in [('boolean', True), ('float', 1.0), ('range128', 128),
                        ('negative128', -128), ('overflow', 1 << 80)]:
        bad = va.copy()
        bad[0] = value
        path = file('bad_vector_'+name+'.json', bad)
        invoke('vector_'+name, ['encode-query', ('--vector', path),
               ('--out', run_dir/f'bad_query_{name}.json')], expected=2)
    for name, bad in [('short', va[:-1]), ('long', va+[0])]:
        invoke('vector_'+name, ['encode-query', ('--vector', file(name+'.json', bad)),
               ('--out', run_dir/(name+'_query.json'))], expected=2)
    query = (run_dir/'query.json').read_bytes()
    for name, bad in [('query_whitespace', query+b'\n'),
                      ('query_duplicate_field', query[:-1]+b',"schema":"resident-public-query-v1"}')]:
        invoke(name, ['host-infer', ('--acc', run_dir/'state1.ct'),
               ('--query', file(name+'.json', bad)), ('--out', run_dir/(name+'.ct'))], expected=2)
    invoke('host_rejects_secret_argument', ['host-learn', ('--acc', run_dir/'a.zero'),
           ('--fresh', run_dir/'a1.ct'), ('--out', run_dir/'unexpected.ct'),
           ('--sk', run_dir/'a.sk')], expected=2)
    checks['strict_query_and_role_argument_refusals'] = True

    report = {
        'classification': 'EXECUTED actual BFV component boundary review; no finalized journal/release claim',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'script_sha256': sha(Path(__file__).read_bytes()),
        'source_path': str(args.source.resolve()), 'source_sha256': sha(source),
        'binary_path': str(args.binary.resolve()), 'snapshot_binary_sha256': sha(binary.read_bytes()),
        'params': params, 'checks': checks, 'commands': records,
        'secret_keys_generated_for_test_only': True,
        'runtime_and_secret_keys_gitignored': True,
        'scope': 'Public test vectors; OS-random keys/coins; raw full-key helper only a trusted oracle. Exact expiry test is the arithmetic atom, not a W32 scheduler test. Key labels require separate authenticated issuer provenance.'}
    (HERE/f'crypto_boundary_review_{run_number:03}.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'run': run_number, 'commands': len(records), 'checks': checks}, indent=2))


if __name__ == '__main__':
    main()
