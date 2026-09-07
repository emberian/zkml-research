#!/usr/bin/env python3
"""Independent exact integer replay and evidence audit for an honest utility run."""
import argparse
import base64
import collections
import gzip
import hashlib
import json
from pathlib import Path
import platform
import sqlite3
import subprocess
import tarfile


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(Path(path).read_bytes())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', required=True)
    args = parser.parse_args()
    reports = Path(__file__).resolve().parent / args.run
    runtime = reports.parent.parent / 'runtime' / args.run
    report = load(reports / 'report.json')
    assert report['ok'] and report['oracle_comparisons'] == 96
    pins = load(reports / 'source_pins.json')
    for name, expected in pins.items():
        assert sha((runtime / 'e2e' / name).read_bytes()) == expected
    for name in ['service.py', 'utility_driver.py']:
        assert sha((reports.parent.parent / name).read_bytes()) == pins['verified_reader/' + name]
    fixture = load(reports / 'fixture_pins.json')
    for name, expected in fixture['frozen_vector_files'].items():
        assert sha((runtime / 'e2e' / name).read_bytes()) == expected
    inputs = runtime / 'e2e/utility/issuer_oracle'
    assert sha((inputs / 'input_index.json').read_bytes()) == fixture['copied_index_sha256']
    assert sha((inputs / 'expected_scalars.json').read_bytes()) == fixture['oracle_sha256']
    events = load(inputs / 'input_index.json')['events']
    frozen = load(inputs / 'expected_scalars.json')['queries']
    comparisons = 0
    history_results = []
    for history in [0, 1]:
        root = runtime / f'history_{history}'
        cfg = load(root / '.private/verified_reader/config.json')
        with sqlite3.connect(cfg['db']) as db:
            answers = {rid: json.loads(answer)['signed_score'] for rid, answer in
                       db.execute('SELECT request_id,answer FROM received')}
            verified_count = db.execute('SELECT count(*) FROM verified_journal').fetchone()[0]
            verified_head = db.execute('SELECT revision,state_digest FROM verified_head').fetchone()
        queues = {0: collections.deque(), 1: collections.deque()}
        count, learned, expired, correct = 0, 0, 0, 0
        query_ids = set()
        for event in events:
            if not event['event_id'].startswith(f'h{history}-'):
                continue
            queue = queues[event['route']]
            if event['kind'] == 'Learn':
                vector = load(event['issuer_vector_path'])
                assert len(vector) == 577 and all(type(x) is int and -127 <= x <= 127 for x in vector)
                queue.append(vector)
                learned += 1
                if len(queue) > 32:
                    queue.popleft()
                    expired += 1
            else:
                query = load(event['public_query_vector_path'])
                assert len(query) == 577
                # Direct mathematical window definition, recomputed at each
                # query; this does not reuse the crypto/accumulator implementation.
                integer_reference = sum(sum(v * q for v, q in zip(vector, query)) for vector in queue)
                assert answers[event['event_id']] == integer_reference
                assert frozen[event['event_id']]['expected_scalar'] == integer_reference
                correct += (1 if integer_reference >= 0 else -1) == frozen[event['event_id']]['target_label']
                query_ids.add(event['event_id'])
                count += 1
        assert set(answers) == query_ids and count == 48 and learned == 192 and expired == 128
        assert verified_count == verified_head[0] == 240
        command_rows = [load_line for line in (root / 'verified_commands.jsonl').read_bytes().splitlines()
                        if (load_line := json.loads(line))['command'][1] == 'reader-decrypt']
        assert len(command_rows) == 48
        assert all(row['stdout'] is None and row['stderr'] is None and row['private_output_omitted']
                   for row in command_rows)
        sizes = {}
        for role, dbpath in [('verified_reader', Path(cfg['db'])),
                             ('authority', Path(load(root / '.private/authority/config.json')['db']))]:
            sizes[role] = {suffix or 'database': Path(str(dbpath) + suffix).stat().st_size
                           for suffix in ['', '-wal', '-shm'] if Path(str(dbpath) + suffix).exists()}
        history_results.append({'history': history, 'integer_queries_recomputed': count,
                                'all_actual_outputs_equal_direct_integer_reference': True,
                                'all_frozen_oracle_values_equal_direct_integer_reference': True,
                                'learns': learned, 'expiries': expired, 'correct': correct,
                                'verified_journal_records': verified_count,
                                'database_bytes_after_services_closed': sizes})
        comparisons += count
    assert comparisons == 96

    public = []
    for path in reports.rglob('*'):
        if not path.is_file():
            continue
        if path.name.endswith('.tar.gz'):
            with tarfile.open(path) as archive:
                public.extend(archive.extractfile(item).read() for item in archive.getmembers() if item.isfile())
        elif path.name.endswith('.gz'):
            public.append(gzip.decompress(path.read_bytes()))
        else:
            public.append(path.read_bytes())
    all_public = b'\n'.join(public)
    keys = []
    for history in [0, 1]:
        root = runtime / f'history_{history}'
        keys.extend((root / '.private').glob('*/signing.key'))
        keys.append(root / '.private/reader/bfv_secret.bin')
    assert len(keys) == 8
    for path in keys:
        key = path.read_bytes()
        for value in ([key, key[81:]] if path.name == 'bfv_secret.bin' else [key]):
            assert value not in all_public and value.hex().encode() not in all_public
            assert base64.b64encode(value) not in all_public
    ignored = subprocess.run(['git', 'check-ignore', str(keys[0]), str(keys[-1]), str(inputs / 'input_index.json')],
                             capture_output=True, text=True)
    assert ignored.returncode == 0 and len(ignored.stdout.splitlines()) == 3
    result = {'ok': True, 'source_binary_and_fixture_pins_match': True,
              'independent_integer_comparisons': comparisons, 'all_match': True,
              'histories': history_results, 'secret_files_scanned_raw_hex_base64': len(keys),
              'bfv_inner_secret_payloads_scanned': True, 'reader_plaintext_stdout_omitted': True,
              'runtime_gitignored': True, 'python': platform.python_version(), 'platform': platform.platform(),
              'validator_sha256': sha(Path(__file__).read_bytes()),
              'command': ['python3', str(Path(__file__).resolve()), '--run', args.run],
              'scope': 'Exact mathematical replay of this public fixture and artifact omission audit; not an OS-isolation or information-flow proof.'}
    (reports / 'validation.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    manifest = {str(path.relative_to(reports)): {'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
                for path in sorted(reports.rglob('*')) if path.is_file() and path.name != 'manifest.json'}
    (reports / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'ok': True, 'independent_integer_comparisons': comparisons,
                      'all_match': True, 'secret_files_scanned': len(keys)}))


if __name__ == '__main__':
    main()
