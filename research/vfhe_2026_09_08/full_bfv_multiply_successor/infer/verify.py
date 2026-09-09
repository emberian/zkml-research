#!/usr/bin/env python3
"""One fresh verifier for the full committed-input kernel Infer.

Usage: verify.py APPROVED_REQUEST CASE MAC_PROOFS NEW_OUT
The approved request selects model/query/evaluation-key content hashes.
The local pinned configuration selects relation profiles and square proofs.
"""
import json
import os
from pathlib import Path
import sys
import time
from common import ROOT, check_pins, command, now, save, sha


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 4:
        raise SystemExit(__doc__)
    request_path, case, proofs, out = (Path(x).resolve() for x in argv)
    request = json.loads(request_path.read_text())
    assert request['schema'] == 'approved-kernel-infer-input-v1'
    config = json.loads((ROOT / 'PIPELINE.json').read_text())
    squares = {k: json.loads(Path(v).read_text()) for k, v in config['square']['config_paths'].items()}
    pins = {config['native']: config['source_pins'][config['native']], config['linear_plan']: config['linear_plan_sha256']}
    for c in [config, *squares.values()]:
        pins[c['native']] = c['source_pins'][c['native']]
        for p in c['profiles']:
            pins[p['template']] = p['template_sha256']
    check_pins(pins)
    case_pins = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    expected = {'model_ciphertext_sha256': sha(case / 'model.ct'), 'query_sha256': sha(case / 'query.json'), 'evaluation_key_sha256': sha(case / 'evaluation.key')}
    assert all(request[k] == digest for k, digest in expected.items())
    out.mkdir()
    request_sha = sha(request_path)
    save(out / 'inputs.json', {'approved_request': request, 'approved_request_sha256': request_sha, 'approved_pins': pins, 'case_pins': case_pins, 'started_utc': now()})
    env = dict(os.environ, RAYON_NUM_THREADS='4')
    results = []
    binding = None
    square_binding = None
    started = time.monotonic()
    try:
        for i in range(88):
            profile = config['profiles'][(i % 8) // 2]
            proof = proofs / f'chunk{i:03}' / 'proof.bin'
            label = f'mac{i:03}'
            save(out / 'progress.json', {'phase': 'mac', 'index': i, 'completed': len(results), 'utc': now()})
            cost = command(out, label, [config['native'], 'verify', config['linear_plan'], i, profile['template'], case, proof], 300, env)
            r = json.loads((out / (label + '.stdout')).read_text())
            assert r['verified'] and r['index'] == i and r['stage'] == i // 8 and r['prime_index'] == (i % 8) // 2
            assert r['rows'] == 4096 and r['first_row'] == i * 4096 and r['end_row_exclusive'] == (i + 1) * 4096
            assert r['template_sha256'] == profile['template_sha256'] and r['proof_sha256'] == sha(proof)
            if binding is None:
                binding = r['binding']
                assert all(binding[k] == v for k, v in expected.items())
                assert binding['linear_plan_sha256'] == config['linear_plan_sha256']
            assert r['binding'] == binding
            results.append({'phase': 'mac', 'index': i, 'verification': r, 'proof_bytes': proof.stat().st_size, 'costs': cost})
        square_case = Path(config['square']['case'])
        for kind, count in [('extension', 4), ('tensor', 18), ('rescale', 6)]:
            c = squares[kind]
            for i in range(count):
                profile = c['profiles'][i // 2 if kind == 'tensor' else 0]
                proof = Path(config['square']['proof_paths'][kind]) / f'chunk{i:03}' / 'proof.bin'
                label = f'{kind}{i:03}'
                argv = ([c['native'], 'verify', profile['template'], square_case, i, proof] if kind == 'rescale' else [c['native'], 'verify', kind, i, profile['template'], square_case, proof])
                save(out / 'progress.json', {'phase': kind, 'index': i, 'completed': len(results), 'utc': now()})
                cost = command(out, label, argv, 300, env)
                r = json.loads((out / (label + '.stdout')).read_text())
                assert r['verified'] and r['rows'] == 4096 and r['proof_sha256'] == sha(proof)
                if kind == 'rescale':
                    assert r['chunk'] == i and r['first_global_row'] == i * 4096 and r['end_global_row_exclusive'] == (i + 1) * 4096
                    assert r['source_trace_sha256'] == square_binding['source_trace_sha256']
                    assert r['output_ciphertext_sha256'] == binding['kernel_ciphertext_sha256']
                else:
                    assert r['kind'] == kind and r['index'] == i and r['first_row'] == i * 4096 and r['end_row_exclusive'] == (i + 1) * 4096
                    assert r['template_sha256'] == profile['template_sha256']
                    if square_binding is None:
                        square_binding = r['binding']
                        assert square_binding['input_ciphertext_sha256'] == binding['dot_ciphertext_sha256']
                        assert square_binding['output_ciphertext_sha256'] == binding['kernel_ciphertext_sha256']
                    assert r['binding'] == square_binding
                results.append({'phase': kind, 'index': i, 'verification': r, 'proof_bytes': proof.stat().st_size, 'costs': cost})
        check_pins(pins)
        check_pins(case_pins)
        assert sha(request_path) == request_sha
        save(out / 'result.json', {'complete_infer_verified': True, 'statement': 'Infer(explicit committed model ciphertext, public query, approved public evaluation key) returns the verified kernel ciphertext',
             'approved_request_sha256': request_sha, 'binding': binding, 'square_binding': square_binding,
             'stages': 11, 'mac_tuple_rows': 360448, 'mac_output_residues': 720896, 'proofs_verified': 116,
             'new_mac_proofs': 88, 'reused_square_proofs': 28, 'square_reproved': False,
             'proof_bytes': sum(x['proof_bytes'] for x in results), 'verifications': results,
             'elapsed_seconds': time.monotonic() - started, 'finished_utc': now(), 'private_files_read': 0,
             'tcb': 'Public SIMD encoding, ciphertext/key decoding and public seed expansion, canonical residue lift and NTT transforms, application-approved Lean linear-plan interpretation, affine additions, IR2 adapter/proof backend, fixed phase/row binding controller.',
             'history_boundary': 'The committed input is the explicit approved model digest. The old saved revision9 workload had no proof-gated journal; its prior teaching/history is not proved here.',
             'scope': 'Complete retained one-class kernel Infer arithmetic for the saved workload under the stated TCB; no claim of shipped system, BFV noise/security/key correctness, text-encoder correctness, restricted-key custody or journal authorization.'})
        save(out / 'progress.json', {'phase': 'complete', 'completed': 116, 'utc': now()})
    except BaseException as e:
        save(out / 'failure.json', {'complete_infer_verified': False, 'completed': len(results), 'error': repr(e), 'utc': now()})
        raise


if __name__ == '__main__':
    main()
