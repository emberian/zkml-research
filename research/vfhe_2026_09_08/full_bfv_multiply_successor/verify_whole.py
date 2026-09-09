#!/usr/bin/env python3
"""Fresh-verify the complete saved square using new phases and reused rescale.

Usage: verify_whole.py CASE EXTENSION_PROOFS TENSOR_PROOFS RESCALE_PROOFS NEW_OUT
The application approves extension.json, tensor.json and rescale.json locally.
No witness, private key, decryption or scaler/product execution is needed.
"""
import json
import os
from pathlib import Path
import sys
import time
from common import ROOT, check_pins, command, now, save, sha


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 5:
        raise SystemExit(__doc__)
    case, extension, tensor, rescale, out = (Path(x).resolve() for x in argv)
    configs = {kind: json.loads((ROOT / (kind + '.json')).read_text()) for kind in ('extension', 'tensor', 'rescale')}
    pins = {}
    for config in configs.values():
        pins[config['native']] = config['source_pins'][config['native']]
        for profile in config['profiles']:
            pins[profile['template']] = profile['template_sha256']
    check_pins(pins)
    case_pins = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    out.mkdir()
    save(out / 'inputs.json', {'case_pins': case_pins, 'approved_pins': pins,
         'config_sha256': {k: sha(ROOT / (k + '.json')) for k in configs}, 'started_utc': now()})
    env = dict(os.environ, RAYON_NUM_THREADS='4')
    results = []
    binding = None
    started = time.monotonic()
    try:
        for kind, proofs, count in [('extension', extension, 4), ('tensor', tensor, 18), ('rescale', rescale, 6)]:
            config = configs[kind]
            for i in range(count):
                profile = config['profiles'][i // 2 if kind == 'tensor' else 0]
                proof = proofs / f'chunk{i:03}' / 'proof.bin'
                label = f'{kind}{i:03}'
                argv = ([config['native'], 'verify', profile['template'], case, i, proof] if kind == 'rescale'
                        else [config['native'], 'verify', kind, i, profile['template'], case, proof])
                save(out / 'progress.json', {'kind': kind, 'index': i, 'completed': len(results), 'utc': now()})
                cost = command(out, label, argv, 300, env)
                r = json.loads((out / (label + '.stdout')).read_text())
                assert r['verified'] and r['rows'] == 4096 and r['proof_sha256'] == sha(proof)
                if kind == 'rescale':
                    assert r['chunk'] == i and r['first_global_row'] == i * 4096 and r['end_global_row_exclusive'] == (i + 1) * 4096
                    assert r['source_trace_sha256'] == binding['source_trace_sha256']
                    assert r['output_ciphertext_sha256'] == binding['output_ciphertext_sha256']
                else:
                    assert r['kind'] == kind and r['index'] == i
                    assert r['first_row'] == i * 4096 and r['end_row_exclusive'] == (i + 1) * 4096
                    assert r['template_sha256'] == profile['template_sha256']
                    if binding is None:
                        binding = r['binding']
                    assert r['binding'] == binding
                results.append({'kind': kind, 'index': i, 'proof': str(proof), 'proof_bytes': proof.stat().st_size,
                                'verification': r, 'costs': cost})
        check_pins(pins)
        check_pins(case_pins)
        save(out / 'result.json', {'whole_operation_verified': True, 'statement': 'Saved raw degree8192 two-component ciphertext squared to the saved raw three-component ciphertext',
             'binding': binding, 'extension_positions': 16384, 'extension_output_residues': 147456,
             'tensor_rows': 73728, 'tensor_output_residues': 221184, 'rescale_positions': 24576,
             'rescale_output_residues': 98304, 'proofs_verified': 28, 'new_proofs': 22, 'rescale_proofs_reused': 6,
             'exact_coverage_no_padding': True, 'proof_bytes': sum(x['proof_bytes'] for x in results),
             'verifications': results, 'elapsed_seconds': time.monotonic() - started, 'finished_utc': now(),
             'private_files_read': 0, 'rescale_reproved': False,
             'tcb': 'Public parser/serializer, linear NTT transforms/copy checks, relation loading, proof backend and this fixed phase/index binding controller. No claim of Lean refinement for these implementation layers.',
             'scope': 'Complete saved ciphertext square arithmetic under the stated verifier TCB; not the preceding encrypted dot-product/rotation query, BFV security/noise, key custody or authorization protocol.'})
        save(out / 'progress.json', {'phase': 'complete', 'completed': 28, 'utc': now()})
    except BaseException as e:
        save(out / 'failure.json', {'whole_operation_verified': False, 'error': repr(e), 'completed': len(results), 'utc': now()})
        raise


if __name__ == '__main__':
    main()
