"""Shared paths, public metadata, atomic/fsynced records and immutable freeze."""
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent
FIXED = PRIOR / 'emitted_fixed_fft'
FORMAL = ROOT.parents[3] / 'formal/private_address_ema/emitted_schedule'
FIXTURE = PRIOR / 'utility/materialized_fixture.json'
RUNTIME = ROOT / 'runtime/run001'
REPORTS = ROOT / 'reports/run001'
HOST = FIXED / 'target/release/resident-emitted-bool-runtime'
ISSUER = PRIOR / 'target/release/issuer'
READER = PRIOR / 'target/release/reader'
PK = PRIOR / 'runs/run_001/public/keys/public_key.bin'
SK = PRIOR / 'runs/run_001/public/keys/server_key.bin'
CK = PRIOR / 'runs/run_001/private/reader/client_key.bin'
EXPECTED_PLAN = 'Plan { base_algo: Dif4, base_size: 512, fft_size: 512 }'
load = lambda p: json.loads(Path(p).read_text())


def sync_dir(path):
    descriptor = os.open(path, os.O_RDONLY)
    try: os.fsync(descriptor)
    finally: os.close(descriptor)


def save(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as stream:
        stream.write(json.dumps(value, indent=2, sort_keys=True) + '\n')
        stream.flush(); os.fsync(stream.fileno())
    temporary.replace(path); sync_dir(path.parent)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''): h.update(chunk)
    return h.hexdigest()


def meta(path):
    path = Path(path)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)}


def append(stream, value):
    stream.write(json.dumps(value, sort_keys=True) + '\n')
    stream.flush(); os.fsync(stream.fileno())


def lines(path):
    return [json.loads(row) for row in Path(path).read_text().splitlines()]


def verify_freeze():
    frozen = load(ROOT / 'freeze.json')
    for path, expected in frozen['files'].items():
        assert meta(path) == expected, f'frozen public/source file changed: {path}'
    return frozen


def envelope_check(path, kind, count):
    raw = Path(path).read_bytes()
    assert len(raw) >= 25 and raw[:8] == b'PEMA0001' and raw[8] == kind
    assert int.from_bytes(raw[9:17], 'little') == len(raw) - 17
    assert int.from_bytes(raw[17:25], 'little') == count
    return {'bytes': len(raw), 'kind': kind, 'bits': count}
