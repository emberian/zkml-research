#!/usr/bin/env python3
"""Freshly consume the frozen proof production after a diagnostic-field wrapper fix.
No proof production, arithmetic, backend configuration, or private read occurs.
Usage: consumer.py NEW_VERIFY
"""
from pathlib import Path
import json
import sys
import time
from common import ROOT, save, sha, check_pins, command, now
import pipeline
from run import cases, phase_cost


def check_record(config, kind, index, case, record, proof):
    # Native `prove` emits BACKEND_ID; native `verify` omits that diagnostic.
    # The approved executable hash is checked by pipeline.config() regardless.
    if 'backend' in record:
        assert record['backend'] == config['backend_id']
    assert record['verified'] is True and record['rows'] == 4096
    assert record.get('index', record.get('chunk')) == index
    assert record.get('first_row', record.get('first_global_row')) == index * 4096
    assert record.get('end_row_exclusive', record.get('end_global_row_exclusive')) == (index + 1) * 4096
    assert record['proof_sha256'] == sha(proof)
    if 'template_sha256' in record:
        assert record['template_sha256'] == pipeline.profile(config, kind, index)['template_sha256']
    if kind == 'infer':
        assert record['stage'] == index // 8 and record['prime_index'] == (index % 8) // 2
    if kind in ('extension', 'tensor'):
        assert record['kind'] == kind
    pipeline.record_binding(kind, case, record)


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    contract = pipeline.read(ROOT / 'CONSUMER.json')
    check_pins(contract['pins'])
    config = pipeline.config()
    request = pipeline.read(ROOT / 'REQUEST.json')
    produced = ROOT / 'run001'
    out = Path(sys.argv[1]).resolve()
    out.mkdir()
    started = time.monotonic()
    save(out / 'started.json', {'started_utc': now(), 'consumer_sha256': sha(ROOT / 'CONSUMER.json'),
                              'profile_sha256': sha(ROOT / 'PIPELINE.json'), 'request': request})
    try:
        case = cases(request)
        ib = pipeline.read(case['infer'] / 'operation.json')['binding']
        sb = pipeline.read(case['extension'] / 'operation.json')['binding']
        rb = pipeline.read(case['rescale'] / 'operation.json')
        expected = request['expected']
        assert set(expected) == {'model_ciphertext_sha256', 'query_sha256', 'evaluation_key_sha256', 'kernel_ciphertext_sha256'}
        assert all(ib[k] == value for k, value in expected.items())
        assert ib['linear_plan_sha256'] == config['linear_plan_sha256']
        assert sb['input_ciphertext_sha256'] == ib['dot_ciphertext_sha256']
        assert sb['output_ciphertext_sha256'] == ib['kernel_ciphertext_sha256'] == rb['output_ciphertext_sha256']
        assert sb['source_trace_sha256'] == rb['source_trace_sha256']
        frozen = {str(p): sha(p) for directory in set(case.values()) for p in directory.rglob('*') if p.is_file()}
        checks = []
        generated = {}
        for kind in case:
            phase = pipeline.read(produced / kind / 'result.json')
            assert phase['proofs_generated'] and len(phase['chunks']) == pipeline.COUNT[kind]
            generated[kind] = phase
            for index in range(pipeline.COUNT[kind]):
                proof = produced / kind / f'chunk{index:03}' / 'proof.bin'
                assert sha(proof) == phase['chunks'][index]['proof']['proof_sha256']
                label = f'{kind}{index:03}'
                cost = command(out, label, pipeline.invoke(config, kind, 'verify', index, case[kind], proof), 300, pipeline.ENV)
                record = pipeline.read(out / (label + '.stdout'))
                check_record(config, kind, index, case[kind], record, proof)
                checks.append({'kind': kind, 'index': index, 'verification': record,
                               'proof_bytes': proof.stat().st_size, 'costs': cost})
                save(out / 'progress.json', {'phase': kind, 'completed_total': len(checks), 'utc': now()})
        assert len(checks) == 116
        check_pins(frozen)
        check_pins(contract['pins'])
        pipeline.config()
        baseline = pipeline.read(ROOT.parent / 'BASELINE.json')
        old = {x['phase']: x for x in baseline['phases']}
        costs = {kind: phase_cost(value) for kind, value in generated.items()}
        byte_count = sum(x['proof_bytes'] for x in checks)
        result = {
            'complete_class_verified': True, 'expected': expected, 'binding': ib, 'square_binding': sb,
            'new_proof_objects': 116, 'prover_self_checks': 116, 'fresh_consumer_checks': 116,
            'prior_native_acceptances_before_wrapper_error': 1, 'total_native_verification_calls': 233,
            'reused_proofs': 0, 'proof_production_repeated': False, 'phases': costs,
            'new_mac_proof_bytes': costs['infer']['proof_bytes'],
            'baseline_mac_proof_bytes': old['infer']['proof_bytes'],
            'mac_proof_byte_reduction': 1 - costs['infer']['proof_bytes'] / old['infer']['proof_bytes'],
            'new_mac_prove_seconds': costs['infer']['prove_seconds'],
            'baseline_mac_prove_seconds': old['infer']['prove_seconds'],
            'mac_prove_time_reduction': 1 - costs['infer']['prove_seconds'] / old['infer']['prove_seconds'],
            'whole_class_proof_bytes': byte_count,
            'baseline_whole_class_proof_bytes': baseline['complete_class_proof_bytes'],
            'whole_class_proof_byte_reduction': 1 - byte_count / baseline['complete_class_proof_bytes'],
            'whole_class_prove_seconds': sum(x['prove_seconds'] for x in costs.values()),
            'baseline_whole_class_prove_seconds': sum(x['prove_seconds'] for x in old.values()),
            'proof_phase_seconds': sum(x['phase_seconds'] for x in costs.values()),
            'baseline_proof_phase_seconds': sum(x['phase_seconds'] for x in old.values()),
            'whole_class_fresh_consumer_seconds': time.monotonic() - started,
            'baseline_whole_class_fresh_consumer_seconds': baseline['complete_class_fresh_verify_seconds'],
            'whole_class_peak_rss_bytes': max(x['peak_rss_bytes'] for x in costs.values()),
            'private_files_read': 0, 'verifications': checks, 'finished_utc': now(),
            'controller_correction': 'Original fresh native check accepted; frozen wrapper then raised KeyError for optional backend diagnostic. This separately frozen consumer uses the pinned binary identity and conditionally checks the diagnostic when present. Original failed attempt preserved; no proofs regenerated.',
            'comparison_scope': 'One corrected same-public-case class. All arithmetic now holds on the final row; historical baseline skipped it. Compact MAC uses ranges and fixed-four grouped lookups. Historical timing is not a controlled same-relation benchmark, and old numerical PCS pricing is not inherited.'}
        save(out / 'RESULT.json', result)
        save(out / 'progress.json', {'phase': 'complete', 'completed_total': 116, 'utc': now()})
        print(json.dumps({key: value for key, value in result.items() if key != 'verifications'}, indent=2))
    except BaseException as error:
        save(out / 'failure.json', {'complete_class_verified': False, 'error': repr(error), 'retried': False, 'utc': now()})
        raise


if __name__ == '__main__':
    main()
