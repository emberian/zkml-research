#!/usr/bin/env python3
"""Verify all six rescale chunk proofs against the complete public case.

Usage: verify_all.py CASE PROOF_RUN NEW_VERIFICATION_DIR
No witness or private file is required. The application's approved PIPELINE.json
selects the template/backend; a proof-supplied template is never selected.
"""
import json
import os
from pathlib import Path
import sys
from run import ROOT, check_pins, command, now, save, sha


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    case, proofs, out = (Path(x).resolve() for x in sys.argv[1:])
    config = json.loads((ROOT / 'PIPELINE.json').read_text())
    pins = {p: config['source_pins'][p] for p in (config['native'], config['template'])}
    check_pins(pins)
    out.mkdir()
    env = dict(os.environ, RAYON_NUM_THREADS=str(config['rayon_threads']))
    accepted = []
    try:
        for i in range(6):
            label = f'chunk{i:03}'
            proof = proofs / label / 'proof.bin'
            costs = command(out, label, [config['native'], 'verify', config['template'], case, i, proof], 300, env)
            result = json.loads((out / (label + '.stdout')).read_text())
            assert result['verified'] and result['chunk'] == i and result['rows'] == 4096
            assert result['first_global_row'] == i * 4096
            assert result['end_global_row_exclusive'] == (i + 1) * 4096
            assert result['proof_sha256'] == sha(proof)
            if accepted:
                for key in ('source_trace_sha256', 'output_ciphertext_sha256'):
                    assert result[key] == accepted[0]['verification'][key]
            accepted.append({'verification': result, 'costs': costs})
        check_pins(pins)
        save(out / 'result.json', {'verified': True, 'chunks': accepted,
             'total_positions': 24576, 'output_residues': 98304,
             'exact_coverage_no_padding': True, 'template_sha256': config['template_sha256'],
             'native_sha256': pins[config['native']], 'finished_utc': now(),
             'scope': 'Complete captured rescale; public parser/NTT/provenance remain TCB.'})
    except BaseException as e:
        save(out / 'failure.json', {'verified': False, 'error': repr(e), 'utc': now()})
        raise


if __name__ == '__main__':
    main()
