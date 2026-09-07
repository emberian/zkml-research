#!/usr/bin/env python3
"""Private oracle and artifact audit for the normal live text demonstration."""
import argparse
import base64
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
    home = Path(__file__).resolve().parent.parent
    reports, runtime = home / 'reports' / args.run, home / 'runtime' / args.run
    report = load(reports / 'report.json')
    assert report['ok'] and report['verified_revision'] == 3 and report['oracle_comparisons'] == 2
    for name, expected in load(reports / 'source_pins.json').items():
        assert sha((runtime / 'e2e' / name).read_bytes()) == expected
    assert sha((home / 'live_driver.py').read_bytes()) == report['source_pins']['verified_reader/live_driver.py']
    assert sha((home / 'service.py').read_bytes()) == report['source_pins']['verified_reader/service.py']
    for path, expected in load(reports / 'frontend_dependencies.json').items():
        assert sha(Path(path).read_bytes()) == expected
    private = runtime / 'run/.private'
    encoder = private / 'issuer/live_encoder'
    data, vector = load(encoder / 'input.json'), load(encoder / 'vector.json')
    assert len(vector) == 577 and all(type(x) is int and -127 <= x <= 127 for x in vector)
    query = load(runtime / 'run/queries' / f'q{data["route"] * 8:02d}.json')['coefficients']
    reference = sum(x * y for x, y in zip(vector, query))
    cfg = load(private / 'verified_reader/config.json')
    with sqlite3.connect(cfg['db']) as db:
        answers = {rid: json.loads(answer)['signed_score'] for rid, answer in
                   db.execute('SELECT request_id,answer FROM received')}
        selected = db.execute('SELECT count(*) FROM expected').fetchone()[0]
        rows = [json.loads(x[0]) for x in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
    assert selected == 2 and answers == {'before-live-observation': 0, 'after-live-observation': reference}
    assert [x['payload']['request']['action']['kind'] for x in rows] == ['Infer', 'Learn', 'Infer']
    first, last = rows[0]['payload']['request'], rows[2]['payload']['request']
    assert first['action']['query_ct'] == last['action']['query_ct']
    assert first['authorization'] != last['authorization'] and first['action']['nonce'] != last['action']['nonce']
    assert first['action']['parent_revision'] == 0 and last['action']['parent_revision'] == 2
    assert rows == load(reports / 'accepted_envelopes.json')
    with sqlite3.connect(private / 'reader/answers.sqlite3') as db:
        assert db.execute('SELECT count(*) FROM received').fetchone()[0] == 0
    processes = load(encoder / 'processes.json')
    assert len(processes) == 2 and all(x['exit_code'] == 0 for x in processes)
    assert '--expect-record-id' not in processes[0]['command']
    assert json.loads(processes[0]['stdout'])['cached_quantized_comparison'] is False

    public = []
    for path in reports.iterdir():
        if not path.is_file():
            continue
        if path.name.endswith('.tar.gz'):
            with tarfile.open(path) as archive:
                public.extend(archive.extractfile(member).read() for member in archive.getmembers() if member.isfile())
        elif path.name.endswith('.gz'):
            public.append(gzip.decompress(path.read_bytes()))
        else:
            public.append(path.read_bytes())
    all_public = b'\n'.join(public)
    assert data['text'].encode() not in all_public
    assert json.dumps(data['text']).encode() not in all_public
    for value in [vector, data]:
        for separators in [None, (',', ':')]:
            assert json.dumps(value, separators=separators).encode() not in all_public
    private_report = load(encoder / 'report.json')
    for key in ['input_sha256', 'vector_sha256']:
        assert private_report[key].encode() not in all_public
    for path in [encoder / 'input.json', encoder / 'vector.json', runtime / '.private/input.json']:
        assert sha(path.read_bytes()).encode() not in all_public
    keys = list(private.glob('*/signing.key')) + [private / 'reader/bfv_secret.bin']
    assert len(keys) == 4
    for path in keys:
        key = path.read_bytes()
        for value in ([key, key[81:]] if path.name == 'bfv_secret.bin' else [key]):
            assert value not in all_public and value.hex().encode() not in all_public
            assert base64.b64encode(value) not in all_public
    decrypt_rows = []
    for name in ['commands.jsonl.gz', 'verified_commands.jsonl.gz']:
        for line in gzip.decompress((reports / name).read_bytes()).splitlines():
            row = json.loads(line)
            if row['command'][1] == 'reader-decrypt':
                assert name == 'verified_commands.jsonl.gz'
                assert row['stdout'] is None and row['stderr'] is None and row['private_output_omitted']
                decrypt_rows.append(row)
    assert len(decrypt_rows) == 2
    ignored = subprocess.run(['git', 'check-ignore', str(encoder / 'input.json'), str(keys[-1])],
                             capture_output=True, text=True)
    assert ignored.returncode == 0 and len(ignored.stdout.splitlines()) == 2
    result = {'ok': True, 'direct_integer_comparisons': 2, 'all_match': True,
              'two_distinct_signed_tickets_same_public_query': True,
              'ticket_parent_revisions': [0, 2], 'verified_history_kinds': ['Infer', 'Learn', 'Infer'],
              'actual_live_forward_without_cached_record_substitution': True,
              'baseline_decryptions': 0, 'verified_decryptions': 2,
              'source_binary_and_frontend_pins_match': True,
              'private_text_vector_and_their_hashes_absent_from_expanded_public_artifacts': True,
              'secret_files_scanned_raw_hex_base64': 4, 'bfv_inner_secret_payload_scanned': True,
              'reader_scalar_output_omission_checked': True, 'runtime_gitignored': True,
              'python': platform.python_version(), 'platform': platform.platform(),
              'validator_sha256': sha(Path(__file__).read_bytes()),
              'command': ['python3', str(Path(__file__).resolve()), '--run', args.run],
              'scope': 'One illustrative text and concrete artifact checks, not an accuracy estimate or information-flow/OS-isolation proof.'}
    (reports / 'validation.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    manifest = {path.name: {'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
                for path in sorted(reports.iterdir()) if path.is_file() and path.name != 'manifest.json'}
    (reports / 'manifest.json').write_text(json.dumps(manifest, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'ok': True, 'direct_integer_comparisons': 2, 'all_match': True,
                      'text_vector_and_hashes_omitted': True, 'secret_files_scanned': 4}))


if __name__ == '__main__':
    main()
