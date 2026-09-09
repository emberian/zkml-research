#!/usr/bin/env python3
"""Produce ten changed full-coverage chunks, then consume the entire class.

Usage: run.py NEW_RUN | run.py verify APPROVED_REQUEST PRODUCED NEW_VERIFY
Arithmetic/proving and native invocation reuse the frozen predecessor pipeline.
The 106 unchanged proofs are pinned external inputs, not regenerated.
"""
from pathlib import Path
import json
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent.parent / 'nonlinear_performance/runtime'
sys.path.insert(0, str(PRIOR))
import pipeline
import consumer
from common import check_pins, now, save, sha
from run import cases, phase_cost

KINDS = ('infer', 'extension', 'tensor', 'rescale')
CHANGED = ('extension', 'rescale')


def config():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    c = pipeline.read(ROOT / 'PIPELINE.json')
    assert c['schema'] == 'profiled-range-complete-class-v1'
    check_pins(c['pins'])
    return c


# Reuse the same execution engine and the exact exercised diagnostic checker.
# These assignments redirect output/profile selection, not source arithmetic.
pipeline.ROOT = ROOT
pipeline.config = config
pipeline.check_record = consumer.check_record


def proof_dir(request, produced, kind):
    return Path(produced) / kind if kind in CHANGED else Path(request['reused_produced']) / kind


def consume(request, produced, out):
    c = config()
    out = Path(out).resolve()
    out.mkdir()
    case = cases(request)
    expected = request['expected']
    ib = pipeline.read(case['infer'] / 'operation.json')['binding']
    sb = pipeline.read(case['extension'] / 'operation.json')['binding']
    rb = pipeline.read(case['rescale'] / 'operation.json')
    assert set(expected) == {'model_ciphertext_sha256', 'query_sha256', 'evaluation_key_sha256', 'kernel_ciphertext_sha256'}
    assert all(ib[k] == value for k, value in expected.items())
    assert ib['linear_plan_sha256'] == c['linear_plan_sha256']
    assert sb['input_ciphertext_sha256'] == ib['dot_ciphertext_sha256']
    assert sb['output_ciphertext_sha256'] == ib['kernel_ciphertext_sha256'] == rb['output_ciphertext_sha256']
    assert sb['source_trace_sha256'] == rb['source_trace_sha256']
    frozen = {str(p): sha(p) for directory in set(case.values()) for p in directory.rglob('*') if p.is_file()}
    started = time.monotonic()
    checks = []
    for kind in KINDS:
        location = proof_dir(request, produced, kind)
        phase = pipeline.read(location / 'result.json')
        assert phase['proofs_generated'] and len(phase['chunks']) == pipeline.COUNT[kind]
        for index, chunk in enumerate(phase['chunks']):
            assert chunk['index'] == index
            assert sha(location / f'chunk{index:03}' / 'proof.bin') == chunk['proof']['proof_sha256']
        accepted = pipeline.verify_phase(c, kind, case[kind], location, out)
        for item in accepted:
            item['new_proof'] = kind in CHANGED
        checks.extend(accepted)
    assert len(checks) == 116
    check_pins(frozen)
    config()
    result = {
        'complete_class_verified': True, 'expected': expected, 'binding': ib, 'square_binding': sb,
        'new_proof_objects': 10, 'reused_proof_objects': 106, 'fresh_consumer_checks': 116,
        'whole_class_proof_bytes': sum(x['proof_bytes'] for x in checks),
        'verifications': checks, 'elapsed_seconds': time.monotonic() - started,
        'private_files_read': 0, 'finished_utc': now(),
        'scope': 'Complete same-public-case class kernel. All arithmetic is asserted on every row. The ten extension/rescale proofs use range-completed source; 106 corrected predecessor MAC/tensor proofs are reused exactly. This does not re-prove historical teaching, eliminate reader credentials, or supply a new numerical PCS/FRI/Fiat-Shamir theorem.'}
    save(out / 'RESULT.json', result)
    return result


def main():
    if len(sys.argv) == 2 and sys.argv[1] in ('--help', '-h'):
        print(__doc__)
        return
    if len(sys.argv) == 5 and sys.argv[1] == 'verify':
        result = consume(pipeline.read(sys.argv[2]), Path(sys.argv[3]).resolve(), sys.argv[4])
        print(json.dumps({k: v for k, v in result.items() if k != 'verifications'}, indent=2))
        return
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    out = Path(sys.argv[1]).resolve()
    out.mkdir()
    request = pipeline.read(ROOT / 'REQUEST.json')
    config()
    started = time.monotonic()
    save(out / 'started.json', {'started_utc': now(), 'request_sha256': sha(ROOT / 'REQUEST.json'),
                              'profile_sha256': sha(ROOT / 'PIPELINE.json'), 'request': request})
    try:
        case = cases(request)
        generated = {kind: pipeline.generate(kind, case[kind], out / kind) for kind in CHANGED}
        verified = consume(request, out, out / 'verification')
        prior = pipeline.read(PRIOR / 'consumer001/RESULT.json')
        recorded_costs = dict(prior['phases'])
        fresh_costs = {kind: phase_cost(value) for kind, value in generated.items()}
        recorded_costs.update(fresh_costs)
        total_bytes = verified['whole_class_proof_bytes']
        result = {
            'complete_class_verified': True, 'new_proof_objects': 10, 'reused_proof_objects': 106,
            'prover_self_checks': 10, 'fresh_consumer_checks': 116, 'total_native_verification_calls': 126,
            'new_phases': fresh_costs, 'composed_phases': recorded_costs,
            'whole_class_proof_bytes': total_bytes,
            'baseline_whole_class_proof_bytes': prior['whole_class_proof_bytes'],
            'whole_class_proof_byte_reduction': 1 - total_bytes / prior['whole_class_proof_bytes'],
            'new_only_prove_seconds': sum(x['prove_seconds'] for x in fresh_costs.values()),
            'composed_class_prove_seconds': sum(x['prove_seconds'] for x in recorded_costs.values()),
            'baseline_class_prove_seconds': prior['whole_class_prove_seconds'],
            'composed_class_peak_rss_bytes': max(x['peak_rss_bytes'] for x in recorded_costs.values()),
            'baseline_class_peak_rss_bytes': prior['whole_class_peak_rss_bytes'],
            'fresh_complete_consumer_seconds': verified['elapsed_seconds'],
            'new_production_and_complete_consumption_seconds': time.monotonic() - started,
            'finished_utc': now(), 'private_files_read': 0, 'baseline_reproved': False,
            'verification_record': str(out / 'verification/RESULT.json'),
            'comparison_scope': 'Two replacement full-coverage stages measured once on identical public rows. Complete proof bytes and complete consumption are measured directly. Composed proving/peak costs combine newly measured extension/rescale with retained unchanged MAC/tensor measurements; they are not a fresh whole-class production latency. No timing distribution or numerical proof-security claim.'}
        save(out / 'RESULT.json', result)
        print(json.dumps(result, indent=2))
    except BaseException as error:
        save(out / 'failure.json', {'complete_class_verified': False, 'error': repr(error), 'utc': now()})
        raise


if __name__ == '__main__':
    main()
