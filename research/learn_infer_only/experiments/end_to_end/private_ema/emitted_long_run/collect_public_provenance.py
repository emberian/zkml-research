"""Post-completion public provenance collection. No crypto or private-file reads."""
import csv
import datetime
import hashlib
import json
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parent
REPORTS = ROOT / 'reports/run001'
PUBLIC = ROOT / 'runtime/run001/public'


def meta(path):
    p = Path(path)
    assert 'private' not in p.parts
    assert '/encrypted_successor/runtime/' not in str(p)
    digest = hashlib.sha256()
    with p.open('rb') as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': digest.hexdigest()}


def load(path):
    assert 'private' not in Path(path).parts
    return json.loads(Path(path).read_text())


def check(row):
    assert meta(row['path']) == row


def main():
    frozen = load(ROOT / 'freeze.json')
    freeze_meta = meta(ROOT / 'freeze.json')
    assert freeze_meta['sha256'] == '6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8'
    assert len(frozen['files']) == 39
    for row in frozen['files'].values():
        check(row)
    summary = load(ROOT / 'summary.json')
    pipeline = load(ROOT / 'pipeline.json')
    phase = load(REPORTS / 'public_phase.json')
    verified = load(REPORTS / 'public_verification.json')
    seal = load(REPORTS / 'public_seal.json')
    drain = load(REPORTS / 'private_drain.json')
    assert summary['success'] and pipeline['completed']
    assert [r['stage'] for r in pipeline['stages']] == ['run_public', 'verify_public', 'drain', 'seal']
    assert all(r['returncode'] == 0 for r in pipeline['stages'])
    assert not (REPORTS / 'failure.json').exists()
    assert phase['completed'] and verified['passed'] and seal['public_complete_and_verified']
    assert drain['passed'] and drain['all_match'] and drain['reader_invocations'] == 484
    assert len(drain['initial_checks']) == 4 and all(r['matches'] for r in drain['initial_checks'])
    assert len(drain['event_checks']) == 480 and all(r['matches_frozen_oracle'] for r in drain['event_checks'])
    assert drain['independent_replay_plaintext_checks'] == 0
    assert phase['reader_invocations'] == verified['reader_invocations'] == seal['reader_invocations'] == 0
    dates = [phase['closed_utc'], verified['verified_utc'], seal['sealed_utc'],
             drain['started_utc'], drain['finished_utc'], summary['sealed_utc']]
    parsed = [datetime.datetime.fromisoformat(s) for s in dates]
    assert parsed == sorted(parsed) and parsed[2] < parsed[3]
    assert meta(REPORTS / 'public_seal.json')['sha256'] == summary['public_seal_sha256'] == drain['public_seal_sha256_before_drain']
    assert meta(REPORTS / 'public_phase.json')['sha256'] == verified['public_phase_sha256']
    for row in seal['records'] + summary['records'] + [summary['costs']]:
        check(row)
    storage = load(REPORTS / 'public_storage.json')
    assert storage['artifact_count'] == len(storage['artifacts']) == 1364
    for row in storage['artifacts']:
        assert Path(row['path']).parent == PUBLIC
        check(row)
    assert {str(p) for p in PUBLIC.iterdir()} == {r['path'] for r in storage['artifacts']}
    pairs = [json.loads(s) for s in (REPORTS / 'replays.jsonl').read_text().splitlines()]
    assert len(pairs) == 480
    for pair in pairs:
        assert pair['complete_output_bytes_equal'] and pair['inputs_equal_across_invocations'] and pair['same_observed_plan']
        a, b = Path(pair['primary']['path']), Path(pair['replay']['path'])
        assert a.parent == b.parent == PUBLIC
        assert a.read_bytes() == b.read_bytes()
    with (ROOT / 'costs.csv').open() as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 1848
    costs = []
    for role, operation in sorted({(r['role'], r['operation']) for r in rows}):
        group = [r for r in rows if (r['role'], r['operation']) == (role, operation)]
        wall = [float(r['wall_seconds']) for r in group]
        rss = [int(r['peak_rss_bytes']) for r in group if r['peak_rss_bytes']]
        costs.append({'role': role, 'operation': operation, 'processes': len(group),
                      'wall_seconds_min': min(wall), 'wall_seconds_median': statistics.median(wall),
                      'wall_seconds_max': max(wall), 'wall_seconds_sum': sum(wall),
                      'maximum_recorded_rss_bytes': max(rss) if rss else None})
    result = {'claim': 'EXECUTED public-only post-completion provenance collection',
              'collected_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'success': True, 'new_crypto_invocations': 0, 'private_files_read': False,
              'old_failed_runtime_files_read': False, 'original_seals_modified': False,
              'frozen_files_match': 39, 'public_artifacts_match': 1364,
              'public_artifact_bytes': sum(r['bytes'] for r in storage['artifacts']),
              'public_replay_pairs_recompared_as_bytes': 480,
              'phase_order_verified': True, 'phase_timestamps_utc': dates,
              'counts': summary['counts'], 'authorized_primary_opens_match': 484,
              'replay_plaintext_independent_opens': 0,
              'public_wall_seconds': summary['public_wall_seconds'],
              'private_drain_wall_seconds': summary['private_drain_wall_seconds'],
              'final_correct': summary['final_correct'], 'final_queries': summary['final_queries'],
              'all_checkpoint_correct': summary['all_checkpoint_correct'],
              'all_checkpoint_queries': summary['all_checkpoint_queries'],
              'xor_api_calls_all_hosts': sum(int(r['xor_api_calls']) for r in rows if r['xor_api_calls']),
              'and_api_calls_all_hosts': sum(int(r['and_api_calls']) for r in rows if r['and_api_calls']),
              'cost_groups': costs,
              'records': [meta(ROOT / name) for name in ['freeze.json', 'summary.json', 'pipeline.json', 'costs.csv', 'contention.json', 'collect_public_provenance.py']]
                         + [meta(REPORTS / name) for name in ['public_phase.json', 'public_verification.json', 'public_seal.json', 'public_storage.json', 'private_drain.json', 'reader_operations.jsonl']]}
    with (ROOT / 'collection.json').open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
