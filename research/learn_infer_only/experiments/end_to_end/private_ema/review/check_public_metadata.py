#!/usr/bin/env python3
"""Read public code, binaries and normal-run metadata only; execute no crypto.

Does not open key files, ciphertext artifacts, private requests or audit files.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MANIFEST_HASH = '2dd31102c7ed58a974814f48102ec2a1f9228b984c766c5b5c47ec5d695b2339'
RESULT_HASH = 'a5e3e6f0d7c19d0b5951a5379cf422353a72824c1418f3197bcb6270d7d0f76c'


def sha(path):
    path = path.resolve()
    assert '/runs/run_001/private/' not in str(path)
    assert path.suffix != '.ct'
    assert '/public/keys/' not in str(path)
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest_path = ROOT / 'source_manifest.json'
result_path = ROOT / 'runs/run_001/results.json'
assert sha(manifest_path) == MANIFEST_HASH
assert sha(result_path) == RESULT_HASH
manifest = json.loads(manifest_path.read_text())
result = json.loads(result_path.read_text())
inputs = {str(manifest_path): MANIFEST_HASH, str(result_path): RESULT_HASH}
for group in ('own_sources', 'prior_probe', 'tfhe_source_locations'):
    for item in manifest[group]:
        path = Path(item['path'])
        assert sha(path) == item['sha256']
        inputs[str(path)] = item['sha256']
for field in ('build_log', 'result_file'):
    item = manifest[field]
    assert sha(Path(item['path'])) == item['sha256']
    inputs[item['path']] = item['sha256']
assert result['source_hashes_before'] == result['source_hashes_after']
for name, digest in result['source_hashes_after'].items():
    assert sha(ROOT / name) == digest
for name, digest in result['binary_hashes'].items():
    assert name in ('setup', 'issuer', 'host', 'reader')
    assert sha(ROOT / 'target/release' / name) == digest
assert result['binary_hashes'] == manifest['binary_hashes']
assert not result['errors'] and result['logical_learn_count'] == 2
assert result['completed_prespecified_two_step_run']
assert result['all_correctness_checks_passed'] and result['all_tested_byte_replays_match']

host_rows = []
log_pins = {}
expected_learn = {'and': 180, 'xor': 264, 'not': 46, 'mux': 32, 'trivial_encrypt': 20}
expected_infer = {'and': 0, 'xor': 0, 'not': 0, 'mux': 3, 'trivial_encrypt': 0}
for operation in result['operations']:
    assert operation['exit_code'] == 0
    for field in ('stdout_path', 'stderr_path', 'resource_log'):
        path = (ROOT / operation[field]).resolve()
        assert path.is_relative_to((ROOT / 'runs/run_001/logs').resolve())
        log_pins[str(path)] = sha(path)
    assert not (ROOT / operation['stderr_path']).read_bytes()
    assert json.loads((ROOT / operation['stdout_path']).read_text()) == operation['reported']
    report = operation['reported']
    if report['role'] == 'host':
        learn = report['operation'] == 'learn'
        assert report['gate_api_calls'] == (expected_learn if learn else expected_infer)
        assert report['output_bits'] == (32 if learn else 1)
        assert not report['client_key_read'] and not report['bootstrap_count_instrumented']
        assert all('/private/' not in arg for arg in operation['command'])
        host_rows.append({'name': operation['name'],
            'evaluate_seconds': report['evaluate_ns'] / 10**9,
            'read_seconds': report['read_ns'] / 10**9,
            'wall_seconds': operation['subprocess_wall_ns'] / 10**9,
            'serialized_bytes': report['serialized_bytes']})
assert len(host_rows) == 8
assert len(result['replay_pairs']) == 4
for pair in result['replay_pairs']:
    assert pair['equal_complete_serialized_bytes']
    assert pair['first']['sha256'] == pair['replay']['sha256']
    assert pair['first']['bytes'] == pair['replay']['bytes']
    assert len(set(pair['separate_wrapper_pids'])) == 2
    assert pair['same_serialized_read_inputs']

for path, digest in inputs.items():
    assert sha(Path(path)) == digest
out = {'label': 'EXECUTED public metadata consistency only',
       'script_sha256': sha(Path(__file__)), 'source_input_hashes': inputs,
       'binary_hashes_rechecked': result['binary_hashes'], 'public_log_hashes': log_pins,
       'source_inputs_unchanged': True, 'public_operation_records_checked': len(result['operations']),
       'reported_logical_learns': result['logical_learn_count'], 'reported_replay_pairs': 4,
       'host_timing_rows': host_rows, 'cryptographic_runs': 0, 'private_artifact_reads': 0,
       'ciphertext_or_key_file_reads': 0,
       'scope': 'Checks source/binary/log pins and internal public-record consistency, not reader plaintexts or ciphertext bytes. Same-input assertion is path comparison in the frozen driver.'}
encoded = json.dumps(out, indent=2) + '\n'
(HERE / 'public_checks.json').write_text(encoded)
print(encoded, end='')
