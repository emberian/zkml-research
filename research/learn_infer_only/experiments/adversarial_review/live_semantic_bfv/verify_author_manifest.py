"""Independent public closeout hashes and cost transcription, no author runtime imports."""
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIVE = HERE.parents[1] / 'end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor'
reads = {}

def read(path):
    path = Path(path)
    assert '.private' not in path.parts and not path.name.endswith('.sqlite3')
    raw = path.read_bytes()
    reads[str(path)] = hashlib.sha256(raw).hexdigest()
    return raw

def sha(path):
    read(path)
    return reads[str(Path(path))]

def load(path):
    return json.loads(read(path))

def main():
    manifest = load(LIVE / 'manifest.json')
    for name, row in manifest['files'].items():
        rel = Path(name)
        assert not rel.is_absolute() and '..' not in rel.parts
        assert sha(LIVE / rel) == row['sha256'], name
        if 'bytes' in row:
            assert (LIVE / rel).stat().st_size == row['bytes']
    freeze = load(LIVE / 'freeze.json')
    parents = {}
    for directory, count in freeze['parent_entries_preserved'].items():
        base = Path(directory)
        entries = load(base / 'manifest.json')['files']
        assert len(entries) == count
        for name, row in entries.items():
            assert sha(base / name) == row['sha256'], (directory, name)
        parents[directory] = len(entries)
    command = load(LIVE / 'run.command.json')
    report = load(LIVE / 'reports/run001/report.json')
    expected = {r['phase']: r['wall_ns'] / 1e9 for r in command['phases']}
    expected['total'] = command['wall_ns'] / 1e9
    for k in ['children_user_cpu_seconds', 'children_system_cpu_seconds', 'maximum_child_rss_bytes_macos']:
        expected[k] = command[k]
    expected.update({'model:' + k: v for k, v in report['model_cost'].items() if type(v) in [int, float]})
    costs = list(csv.DictReader(io.StringIO(read(LIVE / 'costs.csv').decode())))
    assert {row['component'] for row in costs} == set(expected)
    for row in costs:
        assert float(row['value']) == expected[row['component']], row['component']
    crypto_costs = load(LIVE / 'crypto_costs.json')
    groups = {}
    total_public = total_private = decryptions = 0
    for name, expected_hash in crypto_costs['log_sha256'].items():
        path = LIVE / 'reports/run001' / name
        assert sha(path) == expected_hash
        raw = read(path)
        if name.endswith('.gz'):
            raw = gzip.decompress(raw)
        for row in map(json.loads, raw.splitlines()):
            key = ':'.join([name, row['role'], row['command'][1]])
            group = groups.setdefault(key, {'count': 0, 'sum_ns': 0})
            group['count'] += 1; group['sum_ns'] += row['elapsed_ns']
            if name == 'private_receive_commands.jsonl.gz':
                total_private += 1; decryptions += row['command'][1] == 'reader-decrypt'
            else:
                total_public += 1
                assert row['command'][1] != 'reader-decrypt'
    assert groups == crypto_costs['by_component_role_command']
    assert total_public == crypto_costs['public_cli_rows'] == 52
    assert total_private == crypto_costs['later_private_receive_cli_rows'] == 4
    assert decryptions == crypto_costs['later_decryptions'] == 2 and crypto_costs['public_decryptions'] == 0
    result = {'schema': 'live-semantic-independent-author-closeout-v1', 'ok': True,
              'author_manifest_sha256': sha(LIVE / 'manifest.json'),
              'author_manifest_files': len(manifest['files']), 'cost_rows': len(costs),
              'crypto_cost_groups': len(groups), 'crypto_cost_rows': total_public + total_private,
              'parent_entries_unchanged_after_run': parents, 'author_report_sha256': sha(LIVE / 'REPORT.md'),
              'private_file_reads': 0, 'model_or_crypto_imports': 0,
              'source_sha256': sha(__file__), 'public_file_sha256': reads}
    (HERE / 'manifest_check.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'public_file_sha256'}, sort_keys=True))

if __name__ == '__main__':
    main()
