#!/usr/bin/env python3
"""Approve the two emitted profiles and unchanged proof/backend inputs once."""
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent.parent / 'nonlinear_performance/runtime'
sys.path.insert(0, str(PRIOR))
from common import check_pins, command, save, sha
import pipeline


def read(path):
    return json.loads(Path(path).read_text())


def main():
    if (ROOT / 'PIPELINE.json').exists():
        raise RuntimeError('An approved profile already exists')
    formal = ROOT.parent / 'formal'
    artifact_manifest = formal / 'artifacts/PROFILES.json'
    if not artifact_manifest.exists():
        artifact_manifest = formal / 'READY.json'
    ready = read(artifact_manifest)
    c = read(PRIOR / 'PIPELINE.json')
    check_pins(c['pins'])
    c['schema'] = 'profiled-range-complete-class-v1'
    c['profiles'].update({kind: ready['profiles'][kind] for kind in ('extension', 'rescale')})
    required = [ROOT / 'REQUEST.json', ROOT / 'run.py', ROOT / 'prepare.py',
                ROOT.parent / 'CONTRACT.md', artifact_manifest,
                PRIOR / 'consumer.py', PRIOR / 'consumer001/RESULT.json']
    shape = ROOT.parent / 'shape'
    shape.mkdir(exist_ok=True)
    probe = PRIOR.parent / 'backend/shape-probe/target/release/ir2-grouped-shape'
    required.append(probe)
    shape_records = {}
    for kind in ('extension', 'rescale'):
        profiles = c['profiles'][kind]
        assert len(profiles) == 1
        p = profiles[0]
        for key in ('template', 'plan', 'executor'):
            path = Path(p[key]).resolve()
            p[key] = str(path)
            digest = sha(path)
            if key + '_sha256' in p:
                assert p[key + '_sha256'] == digest
            p[key + '_sha256'] = digest
            required.append(path)
        template = read(p['template'])
        assert template['trace_width'] == p['width']
        assert p['public_arity'] == (84 if kind == 'extension' else 88)
        assert template['challenges'] == 0
        assert all(item['t'] == 'lookup' or
                   (item['t'] == 'window_gate' and item['on_transition'] is False)
                   for item in template['constraints'])
        identity = {'template_sha256': p['template_sha256'], 'probe_sha256': sha(probe)}
        if (shape / (kind + '.input.json')).exists():
            assert read(shape / (kind + '.input.json')) == identity
            cost = read(shape / (kind + '.command.json'))
            assert cost['returncode'] == 0
        else:
            cost = command(shape, kind, [probe, p['template']], 120, pipeline.ENV)
            save(shape / (kind + '.input.json'), identity)
        record = read(shape / (kind + '.stdout'))
        assert record['flattened_interactions_exact'] is True
        assert record['prover_or_preprocessing_executed'] is False
        shape_records[kind] = {'record': record, 'command': cost}
        required.extend([shape / (kind + suffix) for suffix in ('.stdout', '.stderr', '.command.json', '.input.json')])
    request = read(ROOT / 'REQUEST.json')
    assert sha(request['baseline_acceptance']) == request['baseline_acceptance_sha256']
    for kind in ('infer', 'tensor'):
        directory = Path(request['reused_produced']) / kind
        phase = read(directory / 'result.json')
        required.append(directory / 'result.json')
        assert len(phase['chunks']) == pipeline.COUNT[kind]
        for index, item in enumerate(phase['chunks']):
            proof = directory / f'chunk{index:03}' / 'proof.bin'
            assert sha(proof) == item['proof']['proof_sha256']
            required.append(proof)
    c['pins'].update(ready.get('pins', {}))
    for source in ready.get('sources', []):
        assert sha(source['path']) == source['sha256']
        c['pins'][source['path']] = source['sha256']
    for path in required:
        c['pins'][str(path.resolve())] = sha(path)
    c.pop('source_completion_ready', None)
    c['source_profile_artifacts'] = str(artifact_manifest)
    c['native_shapes'] = shape_records
    c['freshness'] = 'Ten new extension/rescale proofs,106 unchanged corrected MAC/tensor proofs; fresh complete116-proof consumption on the same saved public case.'
    c['soundness_scope'] = 'Range-completed profiled signed-matrix source under all-row arithmetic. Actual new lookup/PCS dimensions are recorded. Existing native backend identity and all cryptographic parameters remain pinned; no new numerical soundness bound is asserted.'
    c.pop('native_shape', None)
    check_pins(c['pins'])
    save(ROOT / 'PIPELINE.json', c)
    print(json.dumps({'profile_sha256': sha(ROOT / 'PIPELINE.json'),
                      'native_shapes': {kind: value['record'] for kind, value in shape_records.items()},
                      'pinned_files': len(c['pins'])}, indent=2))


if __name__ == '__main__':
    main()
