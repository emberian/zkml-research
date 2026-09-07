#!/usr/bin/env python3
"""Validate source pins and whole-secret omission without printing private data."""
import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import tarfile


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', required=True)
    args = parser.parse_args()
    reports = Path(__file__).resolve().parent
    report = reports / args.run
    runtime = reports.parent / 'runtime' / args.run
    pins = json.loads((report / 'source_pins.json').read_bytes())
    for name, expected in pins.items():
        assert sha((runtime / 'e2e' / name).read_bytes()) == expected
    assert sha((reports.parent / 'test_driver.py').read_bytes()) == pins['verified_reader/test_driver.py']
    assert sha((reports.parent / 'service.py').read_bytes()) == pins['verified_reader/service.py']
    public = []
    for path in report.iterdir():
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
    vectors = list((runtime / 'oracle').glob('input-*.json'))
    assert len(vectors) == 40
    for path in vectors:
        vector = json.loads(path.read_bytes())
        assert json.dumps(vector, separators=(',', ':')).encode() not in all_public
        assert json.dumps(vector).encode() not in all_public
    keys = list((runtime / 'run/.private').glob('*/signing.key'))
    keys.append(runtime / 'run/.private/reader/bfv_secret.bin')
    assert len(keys) == 4
    for path in keys:
        raw = path.read_bytes()
        for data in [raw, raw[81:]] if path.name == 'bfv_secret.bin' else [raw]:
            assert data not in all_public
            assert data.hex().encode() not in all_public
            assert base64.b64encode(data) not in all_public
    for name in ['01-commands.jsonl.gz', '04-verified-commands.jsonl.gz',
                 '05-baseline-control-commands.jsonl.gz']:
        for line in gzip.decompress((report / name).read_bytes()).splitlines():
            row = json.loads(line)
            if row['command'][1] == 'reader-decrypt':
                assert row['private_output_omitted'] and row['stdout'] is None and row['stderr'] is None
    ignored = subprocess.run(['git', 'check-ignore', str(vectors[0]), str(keys[-1])],
                             capture_output=True, text=True)
    assert ignored.returncode == 0 and len(ignored.stdout.splitlines()) == 2
    result = {'ok': True, 'source_and_binary_pins_match': True,
              'current_driver_and_service_match_snapshot': True,
              'private_vectors_scanned_full_encodings': len(vectors),
              'secret_files_scanned_raw_hex_base64': len(keys),
              'bfv_inner_secret_payload_scanned': True,
              'compressed_public_artifacts_expanded_before_scan': True,
              'all_reader_decrypt_outputs_omitted': True, 'private_runtime_gitignored': True,
              'python': platform.python_version(), 'platform': platform.platform(),
              'validator_sha256': sha(Path(__file__).read_bytes()),
              'command': ['python3', str(Path(__file__).resolve()), '--run', args.run],
              'scope': 'Whole-vector/key scan plus typed command-log omission; not an information-flow proof.'}
    (report / 'privacy_validation.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    manifest = {path.name: {'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
                for path in sorted(report.iterdir()) if path.is_file() and path.name != 'manifest.json'}
    (report / 'manifest.json').write_text(json.dumps(manifest, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'ok': True, 'private_vectors_scanned': len(vectors),
                      'secret_files_scanned': len(keys), 'public_report': str(report)}))


if __name__ == '__main__':
    main()
