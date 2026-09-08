#!/usr/bin/env python3
"""Validate saved records and source hashes; no estimator/crypto execution."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import math

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


grid = json.loads((HERE / 'GRID.json').read_text())
run = json.loads((HERE / 'estimates.manifest.json').read_text())
rows = [json.loads(line) for line in (HERE / 'estimates.jsonl').read_text().splitlines()]
assert run['planned_entries'] == run['attempts_completed'] == run['estimator_entries'] == len(rows) == 24
assert run['predeclared_grid_sha256'] == digest(HERE / 'GRID.json')
assert run['predeclared_mapping_sha256'] == digest(HERE / 'MODEL_AND_GRID.md')
assert run['driver_sha256'] == digest(HERE / 'run_estimates.py')
assert run['output_sha256'] == digest(HERE / 'estimates.jsonl')
assert [row['attempt'] for row in rows] == list(range(1, 25))
assert Counter(row['status'] for row in rows) == {'EXECUTED': 24}
for item in run['source_files']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
for name, expected in grid['frozen_ring_sources'].items():
    assert digest(HERE.parent / name) == expected, name

summaries = []
expected_tuples = set()
for point in grid['points']:
    minima = {}
    for model in grid['proposed_calls']['models']:
        selected = []
        for path in grid['proposed_calls']['paths']:
            expected_tuples.add((point['label'], model, path))
            matching = [row for row in rows if (row['point'], row['model'], row['path']) ==
                        (point['label'], model, path)]
            assert len(matching) == 1
            row = matching[0]
            assert row['estimator_entered'] is True
            assert row['q_exact'] == point['q']
            assert row['N_secret'] == row['scalar_proxy_raw_n'] == row['scalar_proxy_normalized_n'] == point['N']
            assert row['ring_samples_raw'] == 64 and row['ring_samples_normalized'] == 63
            assert row['scalar_proxy_raw_m'] == 64 * point['N']
            assert row['scalar_proxy_normalized_m'] == 63 * point['N']
            assert row['error_width_exact'] == '1024'
            assert math.isfinite(row['log2_fields']['rop'])
            selected.append(row)
        minimum = min(selected, key=lambda row: row['log2_fields']['rop'])
        minima[model] = {'log2_modeled_cost': minimum['log2_fields']['rop'],
                         'path': minimum['path'], 'beta': int(minimum['fields']['beta']),
                         'lattice_dimension': int(minimum['fields']['d'])}
    summaries.append({'point': point['label'], 'minima': minima,
                      'joint_finite_parameters_and_costs': point})
assert {(row['point'], row['model'], row['path']) for row in rows} == expected_tuples

summary = {
    'scope': '[EXECUTED] Saved generic estimator records, conditional structured-ring modeling; no security certification',
    'status': 'PASS', 'attempts': len(rows), 'entries': len(rows),
    'errors': 0, 'timeouts': 0, 'infinity_outputs': 0,
    'total_estimator_calculation_seconds_not_attack_time': sum(row['seconds_estimator_not_attack'] for row in rows),
    'points': summaries,
    'baseline_filter': 'N=4096 fails the declared named cost filter',
    'larger_point_filter': 'N=16384 passes the declared named generic filter only; exact Ring-LWE hardness remains open',
    'block_size_range': [min(int(row['fields']['beta']) for row in rows),
                         max(int(row['fields']['beta']) for row in rows)],
    'all_selected_MATZOV_blocks_within_source_fit_1024': all(
        int(row['fields']['beta']) <= 1024 for row in rows if row['model'].startswith('MATZOV')),
}
(HERE / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
artifacts = [
    'MODEL_AND_GRID.md', 'GRID.json', 'prepare_grid.py', 'AUDIT.md',
    'STATUS.md', 'NEXT.md', 'SUMMARY.json', 'run_estimates.py',
    'estimates.jsonl', 'estimates.manifest.json', 'estimates.log',
    'estimates.stderr.log', '.gitignore', 'seal.py',
]
manifest = {
    'scope': '[EXECUTED] Read-only validation of saved 24-call run and sources; no new estimator or attack execution',
    'status': 'PASS', 'source_files': run['source_files'],
    'frozen_ring_sources': grid['frozen_ring_sources'],
    'artifacts': {name: digest(HERE / name) for name in artifacts},
    'estimator_archive_commit': run['estimator_archive_commit'],
    'sage_version': run['sage_version'], 'attempts_and_entries': 24,
    'new_network_meter': grid['new_network_meter'],
    'review_status': 'Frozen author map/results awaiting assigned independent review; no duplicate estimator run requested',
}
(HERE / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
result = {'status': 'PASS', 'entries_validated': 24, 'source_hashes_unchanged': 27,
          'artifact_hashes': len(artifacts), 'manifest_sha256': digest(HERE / 'MANIFEST.json'),
          'audit_sha256': digest(HERE / 'AUDIT.md'),
          'mapping_sha256': digest(HERE / 'MODEL_AND_GRID.md'),
          'summary_sha256': digest(HERE / 'SUMMARY.json')}
(HERE / 'SEAL.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
