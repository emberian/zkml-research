#!/usr/bin/env python3
"""Seal one approved corrected/grouped profile after formal and native artifacts exist."""
from pathlib import Path
import json
import re
import sys
from common import ROOT, save, sha, check_pins

sys.setrecursionlimit(20000)
BASE = ROOT.parent.parent


def read(path):
    return json.loads(Path(path).read_text())


def main():
    if (ROOT / 'PIPELINE.json').exists():
        raise RuntimeError('approved profile already exists')
    formal = ROOT.parent / 'formal'
    ready = read(formal / 'READY.json')
    baseline = read(BASE / 'proved_journal/live_nonlinear/PIPELINE.json')
    config = dict(baseline)
    config['schema'] = 'nonlinear-range-approved-profile-v1'
    config['profiles'] = read(ROOT.parent / 'templates/PROFILES.json')['profiles']
    executor = BASE / 'rescale_native_emitter/native/target/release/lean-bigint-witness'
    config['profiles']['mac'] = []
    for index, prime in enumerate(config['base_primes']):
        path = formal / f'artifacts/prime{index}'
        config['profiles']['mac'].append({
            'prime_index': index, 'prime': str(prime), 'template': str(path / 'template_ir2.json'),
            'template_sha256': sha(path / 'template_ir2.json'), 'plan': str(path / 'witness_plan.json'),
            'plan_sha256': sha(path / 'witness_plan.json'), 'width': 349, 'public_arity': 97,
            'executor': str(executor), 'executor_sha256': sha(executor)})
    builds = {x['name']: x for x in read(ROOT / 'build001/BUILD.json')['builds']}
    for role in config['native']:
        name = 'square' if role in ('extension', 'tensor') else role
        config['native'][role] = builds[name]['binary']
    adapter = ROOT / 'native/adapter/src/lib.rs'
    config['backend_id'] = re.search(r'const BACKEND_ID[^=]*=\s*"([^"]+)"', adapter.read_text())[1]
    config['source_completion_ready'] = str(formal / 'READY.json')
    config['native_shape'] = str(ROOT.parent / 'backend/checks/010-compact-shape.json')
    config['soundness_scope'] = 'New three-instance compact-range/grouped-lookup profile. Source range completion and whole-row arithmetic are distinct from the explicit Rust/PCS/LogUp/FRI backend boundary. No inherited numerical pricing from the old query layout.'
    config['freshness'] = 'Caller-selected same-profile public cases. All116 measured class proofs are newly produced with all-row arithmetic; no old proof reuse and no private phase.'
    pins = {}
    required = [ROOT / 'REQUEST.json', ROOT.parent / 'CONTRACT.md', ROOT.parent / 'BASELINE.json',
                formal / 'READY.json', ROOT.parent / 'templates/PROFILES.json', Path(config['linear_plan']),
                Path(config['native_shape']), ROOT / 'build001/BUILD.json', Path(config['zstd'])]
    for name in ('common.py', 'pipeline.py', 'run.py', 'prepare_profile.py'):
        required.append(ROOT / name)
    required.extend(Path(p) for p in config['native'].values())
    for profiles in config['profiles'].values():
        for profile in profiles:
            for key in ('template', 'plan', 'executor'):
                required.append(Path(profile[key]))
            template = read(profile['template'])
            assert template['trace_width'] == profile['width']
            assert template['challenges'] == 0
            for constraint in template['constraints']:
                if constraint['t'] == 'window_gate':
                    assert constraint['on_transition'] is False
                else:
                    assert constraint['t'] == 'lookup'
    for path in (ROOT / 'native').rglob('*'):
        if path.is_file() and 'target' not in path.parts and path.suffix in ('.rs', '.toml', '.lock', '.json'):
            required.append(path)
    for sub in ('formal/Compiler', 'backend/p3-lookup-grouped/src'):
        required.extend(path for path in (ROOT.parent / sub).rglob('*') if path.is_file())
    required.extend([formal / 'EmitRangeKeyswitch.lean', ROOT.parent / 'backend/p3-lookup-grouped/Cargo.toml'])
    for path in required:
        pins[str(path.resolve())] = sha(path)
    config['pins'] = pins
    check_pins(pins)
    save(ROOT / 'PIPELINE.json', config)
    print(json.dumps({'profile_sha256': sha(ROOT / 'PIPELINE.json'), 'pinned_files': len(pins), 'backend_id': config['backend_id']}))


if __name__ == '__main__':
    main()
