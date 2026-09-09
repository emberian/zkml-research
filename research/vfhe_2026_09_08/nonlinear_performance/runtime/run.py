#!/usr/bin/env python3
"""Produce and consume one corrected class proof bundle using saved PUBLIC cases.
Usage: run.py NEW_RUN | run.py verify REQUEST_JSON PRODUCED NEW_VERIFY.
No key, encoder, encryption, or private read is invoked.
"""
from pathlib import Path
import json
import sys
import time
from common import ROOT, save, now, sha, check_pins
import pipeline

KINDS = ('infer', 'extension', 'tensor', 'rescale')


def cases(request):
    old = Path(request['baseline_produced'])
    return {kind: old / ('infer_case' if kind == 'infer' else 'rescale_case' if kind == 'rescale' else 'square_case') for kind in KINDS}


def consume(request, produced, out):
    c = pipeline.config()
    expected = request['expected']
    out = Path(out).resolve()
    out.mkdir()
    case = cases(request)
    ib = pipeline.read(case['infer'] / 'operation.json')['binding']
    sb = pipeline.read(case['extension'] / 'operation.json')['binding']
    rb = pipeline.read(case['rescale'] / 'operation.json')
    assert set(expected) == {'model_ciphertext_sha256', 'query_sha256', 'evaluation_key_sha256', 'kernel_ciphertext_sha256'}
    assert all(ib[k] == v for k, v in expected.items())
    assert ib['linear_plan_sha256'] == c['linear_plan_sha256']
    assert sb['input_ciphertext_sha256'] == ib['dot_ciphertext_sha256']
    assert sb['output_ciphertext_sha256'] == ib['kernel_ciphertext_sha256'] == rb['output_ciphertext_sha256']
    assert sb['source_trace_sha256'] == rb['source_trace_sha256']
    frozen = {str(p): sha(p) for d in set(case.values()) for p in d.rglob('*') if p.is_file()}
    start = time.monotonic()
    checks = []
    for kind in KINDS:
        checks.extend(pipeline.verify_phase(c, kind, case[kind], Path(produced) / kind, out))
    check_pins(frozen)
    pipeline.config()
    assert len(checks) == 116
    result = {
        'complete_class_verified': True, 'expected': expected, 'binding': ib,
        'square_binding': sb, 'new_proofs': 116, 'reused_proofs': 0,
        'fresh_consumer_checks': len(checks),
        'proof_bytes': sum(x['proof_bytes'] for x in checks),
        'verifications': checks, 'elapsed_seconds': time.monotonic() - start,
        'private_files_read': 0, 'finished_utc': now(),
        'scope': 'One complete retained class kernel arithmetic with all-row assertions, compact MAC ranges and grouped lookup interactions. Parser, encoding, NTT, controller, and proof backend boundaries remain explicit; no classifier-wide or private-read claim.'}
    save(out / 'result.json', result)
    return result


def phase_cost(result):
    chunks = result['chunks']
    return {
        'proofs': len(chunks),
        'proof_bytes': sum(x['proof']['proof_bytes'] for x in chunks),
        'prove_seconds': sum(x['proof']['prove_ns'] for x in chunks) / 1e9,
        'self_verify_seconds': sum(x['proof']['self_verify_ns'] for x in chunks) / 1e9,
        'emission_seconds': sum(x['costs']['emit']['elapsed_seconds'] for x in chunks),
        'phase_seconds': result['elapsed_seconds'],
        'peak_rss_bytes': max(x['costs']['prove']['max_rss_bytes'] for x in chunks)}


def main():
    if len(sys.argv) == 5 and sys.argv[1] == 'verify':
        result = consume(pipeline.read(sys.argv[2]), Path(sys.argv[3]).resolve(), sys.argv[4])
        print(json.dumps(result, indent=2))
        return
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    out = Path(sys.argv[1]).resolve()
    out.mkdir()
    request = pipeline.read(ROOT / 'REQUEST.json')
    pipeline.config()
    start = time.monotonic()
    save(out / 'started.json', {'started_utc': now(), 'request_sha256': sha(ROOT / 'REQUEST.json'),
                              'profile_sha256': sha(ROOT / 'PIPELINE.json'), 'request': request})
    try:
        generated = {}
        for kind, case in cases(request).items():
            generated[kind] = pipeline.generate(kind, case, out / kind)
        verified = consume(request, out, out / 'verification')
        baseline = pipeline.read(ROOT.parent / 'BASELINE.json')
        old = {x['phase']: x for x in baseline['phases']}
        costs = {kind: phase_cost(value) for kind, value in generated.items()}
        result = {
            'complete_class_verified': True, 'new_proof_objects': 116,
            'prover_self_checks': 116, 'fresh_consumer_checks': 116, 'reused_proofs': 0,
            'baseline_reproved': False, 'phases': costs,
            'new_mac_proof_bytes': costs['infer']['proof_bytes'],
            'baseline_mac_proof_bytes': old['infer']['proof_bytes'],
            'mac_proof_byte_reduction': 1 - costs['infer']['proof_bytes'] / old['infer']['proof_bytes'],
            'new_mac_prove_seconds': costs['infer']['prove_seconds'],
            'baseline_mac_prove_seconds': old['infer']['prove_seconds'],
            'mac_prove_time_reduction': 1 - costs['infer']['prove_seconds'] / old['infer']['prove_seconds'],
            'whole_class_proof_bytes': verified['proof_bytes'],
            'baseline_whole_class_proof_bytes': baseline['complete_class_proof_bytes'],
            'whole_class_proof_byte_reduction': 1 - verified['proof_bytes'] / baseline['complete_class_proof_bytes'],
            'whole_class_prove_seconds': sum(x['prove_seconds'] for x in costs.values()),
            'baseline_whole_class_prove_seconds': sum(x['prove_seconds'] for x in old.values()),
            'whole_class_fresh_consumer_seconds': verified['elapsed_seconds'],
            'baseline_whole_class_fresh_consumer_seconds': baseline['complete_class_fresh_verify_seconds'],
            'elapsed_seconds': time.monotonic() - start, 'finished_utc': now(),
            'private_files_read': 0, 'verification_record': str(out / 'verification/result.json'),
            'comparison_scope': 'One new same-public-case class production and fresh consumption. All phases now assert arithmetic on the final row; historical baseline skipped it. MAC also uses compact ranges and fixed-four grouped lookups. Recorded historical timings are not a controlled same-semantics benchmark; no baseline reproof, parameter sweep, fresh encryption, or private read.'}
        save(out / 'RESULT.json', result)
        print(json.dumps(result, indent=2))
    except BaseException as error:
        save(out / 'failure.json', {'complete_class_verified': False, 'error': repr(error), 'retried': False, 'utc': now()})
        raise


if __name__ == '__main__':
    main()
