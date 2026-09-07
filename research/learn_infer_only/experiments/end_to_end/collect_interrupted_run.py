#!/usr/bin/env python3
"""Verify saved public evidence after interruption; never execute cryptography."""
from pathlib import Path
import collections
import datetime
import gzip
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
EXP = HERE.parent
SEEN = {}


def pin(path, expected=None):
    path = Path(path).resolve()
    assert not any(x in path.parts for x in ('.private', '.private_fixture'))
    assert not any(x in str(path) for x in ('signer_route', 'verified_route'))
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if expected is not None:
        assert digest == expected, str(path)
    SEEN[str(path)] = {'sha256': digest, 'bytes': len(raw)}
    return raw


def read(path):
    path = Path(path)
    raw = pin(path)
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def check_manifest(path):
    manifest = read(path)
    files = manifest['files']
    records = files if isinstance(files, list) else [dict(path=k, **v) for k, v in files.items()]
    for item in records:
        target = Path(item['path'])
        if not target.is_absolute():
            target = Path(path).parent / target
        data = pin(target, item['sha256'])
        assert len(data) == item['bytes']
    return len(records)


def main():
    prior = read(HERE / 'checkpoint_004.json')
    for group in prior['groups']:
        pin(group['manifest'], group['sha256'])
        for entry in group['checked']:
            assert len(pin(entry['path'], entry['sha256'])) == entry['bytes']
    base = EXP / 'private_construction/designated_span'
    full = base / 'full_utility'
    static_count = check_manifest(full / 'artifact_manifest.json')
    report = read(full / 'reports/full_003/report.json')
    complete = read(full / 'reports/full_003/public_complete.json')
    expected = dict(events=480, learns=384, infers=96, expiries=256)
    for key, value in expected.items():
        assert report[key] == complete[key] == value
    assert report['ok'] and report['all_96_exact_integer_matches']
    assert report['public_completion_precedes_any_private_drain']
    assert complete['all_public_workers_and_services_closed']
    assert complete['all_public_replay_status_history_checks_before_any_private_drain']
    outcomes = report['event_outcomes']
    assert len(outcomes) == 96
    assert all(x['direct_and_frozen_integer_match'] for x in outcomes)
    assert sum(x['original_utility_correct'] for x in outcomes) == 52
    assert sum(x['public_structural_zero'] for x in outcomes) == 16
    assert sum(x['original_utility_correct'] for x in outcomes if x['phase'] == 3) == 18
    histories = []
    for index in (0, 1):
        folder = full / f'reports/full_003/history_{index}'
        public = read(folder / 'public_report.json')
        replay = read(folder / 'replay.json.gz')
        envelopes = read(folder / 'accepted_envelopes.json')
        assert len(envelopes) == replay['revision'] == public['events'] == 240
        counts = collections.Counter()
        queues = {0: [], 1: []}
        previous = None
        for revision, envelope in enumerate(envelopes, 1):
            item = envelope['payload']
            assert item['revision'] == revision
            if previous is not None:
                assert item['parent_state'] == previous
            previous = item['next_state']
            delta = item['delta']
            counts[delta['kind']] += 1
            if delta['kind'] == 'Learn':
                queue = queues[delta['route']]
                if len(queue) == 32:
                    assert delta['expired'] == queue.pop(0)
                    counts['expiry'] += 1
                else:
                    assert delta['expired'] is None
                queue.append(delta['fresh'])
        assert dict(counts) == {'Learn': 192, 'Infer': 48, 'expiry': 128}
        assert previous == replay['state_digest']
        for route in (0, 1):
            assert queues[route] == replay['head']['state']['routes'][str(route)]['queue']
        assert public['exact_authority_verified_journal_and_state']
        assert public['private_answer_db_absent_through_public_checks']
        assert public['public_services_closed_before_private_drain']
        histories.append({'history': index, 'ordered_envelopes': len(envelopes),
                          'counts': dict(counts), 'all_exact_fifo_expiries': True,
                          'parent_digest_chain_and_final_queue_match': True})
    adapter = base / 'public_coin_setup/adapter'
    adapter_report = read(adapter / 'reports/positive_001/report.json')
    assert adapter_report['ok'] and adapter_report['all_match']
    assert (adapter_report['learns'], adapter_report['infers'],
            adapter_report['exact_original_expiries']) == (33, 4, 1)
    assert not adapter_report['scalar_master_computed_in_executed_setup_path']
    assert not adapter_report['projection_key_delivery_computed_in_executed_setup_path']
    source = read(adapter / 'reports/positive_001/execution_pins.json')
    for path, digest in source['source_sha256'].items():
        pin(adapter / path, digest)
    pin(source['native_dependency']['path'], source['native_dependency']['sha256'])
    ema = read(HERE / 'private_ema/source_manifest.json')
    for item in ema['own_sources'] + [ema['build_log'], ema['result_file']]:
        pin(item['path'], item['sha256'])
    ema_review = read(HERE / 'private_ema/review/public_checks.json')
    for field in ('source_input_hashes', 'public_log_hashes'):
        for path, digest in ema_review[field].items():
            pin(path, digest)
    baseline = read(HERE / 'baseline.json')
    for entry in baseline['companions'].values():
        path = entry['path']
        head = subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD'], text=True).strip()
        status = subprocess.check_output(['git', '-C', path, 'status', '--porcelain=v1', '--untracked-files=all'], text=True)
        assert (head, status) == (entry['head'], entry['status'])
    result = {'label': 'EXECUTED saved public evidence collection only',
              'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'passed': True, 'prior_manifest_count': len(prior['groups']),
              'prior_file_links': prior['file_links_checked'],
              'full_run_static_manifest_files': static_count,
              'full_designated_run': {**expected, 'all_96_matches_reported': True,
                  'public_phase_seconds': report['whole_public_phase_ns'] / 1e9,
                  'histories': histories},
              'public_coin_positive_source_pins_unchanged': True,
              'private_ema_source_and_public_review_pins_unchanged': True,
              'companions_unchanged': True,
              'limits': ['No new cryptography, signature verification, model or theorem run.',
                         'Private integer comparisons attributed to saved executed reports; private answers not opened.',
                         'Public-coin implementation review remains unfinished at interruption.',
                         'No stopped-task artifact or private key/input/audit file read.'],
              'files': SEEN}
    destination = HERE / 'recovery_2026-09-07.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'files'}))


if __name__ == '__main__':
    main()
