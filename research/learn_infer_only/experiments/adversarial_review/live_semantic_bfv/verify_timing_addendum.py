"""Check the separate public timing correction and preservation of both prior seals."""
import hashlib
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
    assert sha(LIVE / 'manifest.json') == '9e04634c8e7346697035372e363de4fb6a1abd5efd92e552eef6e1e6f86dce9f'
    assert sha(HERE / 'manifest.json') == '5857158dba63a63a0a15e0fcb0dc965658c5be07b6f362ffab28aa9d602e6140'
    for base in [LIVE, HERE]:
        for name, row in load(base / 'manifest.json')['files'].items():
            assert sha(base / name) == row['sha256'], (base, name)
    correction = load(LIVE / 'timing_addendum.json')
    seal = load(LIVE / 'timing_addendum_manifest.json')
    assert sha(LIVE / 'timing_addendum_manifest.json') == 'f1226c40feeab45bdf51554200c9a70f5da4c5ac20410efcef7b6e4c1edf0453'
    assert correction['original_manifest_sha256'] == seal['original_manifest_sha256'] == sha(LIVE / 'manifest.json')
    for name, row in seal['files'].items():
        assert sha(LIVE / name) == row['sha256']
    assert sha(correction['source_path']) == correction['source_sha256'] == '670f57b16ae146116cdf751b226b87962d621ff677331104445c47fae6b71bf4'
    source = load(correction['source_path'])
    by_event = {row['completed_events']: row for row in source['public_stdout_checkpoints']}
    assert correction['last_infer_event'] == by_event[80]
    assert correction['following_learn_event'] == by_event[81]
    assert by_event[80]['updated_utc'] == '2026-09-08T05:56:25.935979+00:00'
    assert by_event[81]['updated_utc'] == '2026-09-08T05:56:46.718959+00:00'
    assert correction['actual_live_start_utc'] == load(LIVE / 'run_started.json')['started_utc'] == '2026-09-08T05:56:48Z'
    assert correction['live_outer_wall_ns'] == load(LIVE / 'run.command.json')['wall_ns'] == 27504062000
    assert sha(source['source']['path']) == source['source']['sha256']
    result = {'ok': True, 'schema': 'live-semantic-independent-timing-addendum-v1',
              'original_author_manifest_files_preserved': 67, 'original_review_manifest_files_preserved': 17,
              'author_timing_addendum_manifest_sha256': sha(LIVE / 'timing_addendum_manifest.json'),
              'last_infer_checkpoint_utc': by_event[80]['updated_utc'],
              'following_learn81_checkpoint_utc': by_event[81]['updated_utc'],
              'live_start_utc': correction['actual_live_start_utc'], 'live_outer_wall_ns': correction['live_outer_wall_ns'],
              'timing_scope': 'Public checkpoint consistency only; TFHE runtime not re-executed. Learn overlap and shared-load timing remain explicit.',
              'prior_integration_acceptance_unchanged': True, 'private_file_reads': 0, 'model_or_crypto_imports': 0,
              'source_sha256': sha(__file__), 'public_file_sha256': reads}
    (HERE / 'timing_check.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'public_file_sha256'}, sort_keys=True))

if __name__ == '__main__':
    main()
